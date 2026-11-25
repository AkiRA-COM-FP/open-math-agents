-- Parity with pequalnp: credits (owner + agent + model), points, reductions into sub-steps, calendar,
-- filtered feed, windowed leaderboard. Additive only: functions used by older deployments keep working.

alter table oma_solutions add column if not exists agent text;
alter table oma_solutions add column if not exists model text;
alter table oma_solutions add column if not exists points int not null default 0;
alter table oma_solutions add column if not exists contributors json;
alter table oma_leases add column if not exists points int not null default 0;

-- A reduction: a merged Lean file proving  H1 → … → Hk → target. Each Hk becomes a step.
create table if not exists oma_reductions (
  id          text primary key,              -- "<problem>.R<n>"
  problem_id  text not null,
  handle      text not null,
  pr_url      text not null unique,
  hyps        int not null check (hyps between 2 and 4),
  module      text not null,                 -- Lean module the steps import
  created_at  timestamptz not null default now()
);
create table if not exists oma_steps (
  id          text primary key,              -- "<problem>.R<n>.H<k>"
  reduction   text not null references oma_reductions(id),
  parent      text not null,                 -- the problem (or step) the reduction targets
  k           int not null,
  statement   text not null,                 -- Lean text of Hk
  module      text not null,
  points      int not null default 1,
  created_at  timestamptz not null default now()
);
create index if not exists oma_steps_parent on oma_steps (parent);
alter table oma_reductions enable row level security;
alter table oma_steps enable row level security;
revoke all on oma_reductions, oma_steps from anon, authenticated;

create or replace function oma_claim2(p_problem text, p_handle text, p_agent text, p_ip_hash text, p_points int)
returns json language plpgsql security definer set search_path = public, pg_temp as $$
declare r json;
begin
  r := oma_claim(p_problem, p_handle, p_agent, p_ip_hash);
  if r->>'lease' is not null then
    update oma_leases set points = coalesce(p_points, 0) where id = (r->>'lease')::uuid and points = 0;
  end if;
  return r;
end $$;

-- Record a verdict with credits. When the last step of a reduction is proved, the parent is solved too,
-- credited to the reduction's author with every step solver listed as contributor.
create or replace function oma_verdict2(p_problem text, p_handle text, p_pr text, p_verdict text, p_polarity text,
                                        p_agent text, p_model text, p_points int)
returns json language plpgsql security definer set search_path = public, pg_temp as $$
declare
  v_step oma_steps;
  v_red oma_reductions;
  v_left int;
  v_contrib json;
  v_parent_points int;
begin
  insert into oma_solutions (problem_id, handle, pr_url, verdict, polarity, agent, model, points)
    values (p_problem, p_handle, p_pr, p_verdict, coalesce(p_polarity, 'proof'), left(p_agent, 80), left(p_model, 80), coalesce(p_points, 0))
  on conflict (pr_url) do update set verdict = excluded.verdict, agent = excluded.agent, model = excluded.model, points = excluded.points;
  insert into oma_events (kind, problem_id, handle, detail) values (p_verdict, p_problem, p_handle, p_pr);
  if p_verdict <> 'accepted' then return json_build_object('ok', true); end if;
  update oma_leases set status = 'settled', ended_at = now() where problem_id = p_problem and status = 'active';

  -- climb: a closed step may close its parent, which may itself be a step
  select * into v_step from oma_steps where id = p_problem;
  while found loop
    select * into v_red from oma_reductions where id = v_step.reduction;
    select count(*) into v_left from oma_steps s
      where s.reduction = v_red.id
        and not exists (select 1 from oma_solutions o where o.problem_id = s.id and o.verdict = 'accepted');
    exit when v_left > 0;
    if exists (select 1 from oma_solutions where problem_id = v_red.problem_id and verdict = 'accepted') then exit; end if;
    select json_agg(distinct o.handle) into v_contrib from oma_solutions o
      join oma_steps s on s.id = o.problem_id where s.reduction = v_red.id and o.verdict = 'accepted';
    select coalesce(sum(s.points), 0) into v_parent_points from oma_steps s where s.reduction = v_red.id;
    insert into oma_solutions (problem_id, handle, pr_url, verdict, polarity, agent, model, points, contributors)
      values (v_red.problem_id, v_red.handle, v_red.pr_url || '#closed', 'accepted', 'proof', 'reduction', null,
              greatest(1, v_parent_points / 10), v_contrib)
      on conflict (pr_url) do nothing;
    insert into oma_events (kind, problem_id, handle, detail) values ('accepted', v_red.problem_id, v_red.handle, 'closed by reduction ' || v_red.id);
    update oma_leases set status = 'settled', ended_at = now() where problem_id = v_red.problem_id and status = 'active';
    select * into v_step from oma_steps where id = v_red.problem_id;
  end loop;
  return json_build_object('ok', true);
end $$;

create or replace function oma_register_reduction(p_id text, p_problem text, p_handle text, p_pr text, p_module text,
                                                  p_statements json, p_points int)
returns json language plpgsql security definer set search_path = public, pg_temp as $$
declare
  n int := json_array_length(p_statements);
  k int;
begin
  if n < 2 or n > 4 then return json_build_object('error', 'hyps_out_of_range'); end if;
  if (select count(*) from oma_reductions where problem_id = p_problem) >= 3 then
    return json_build_object('error', 'too_many_reductions');
  end if;
  insert into oma_reductions (id, problem_id, handle, pr_url, hyps, module) values (p_id, p_problem, p_handle, p_pr, n, p_module)
    on conflict (id) do nothing;
  for k in 1..n loop
    insert into oma_steps (id, reduction, parent, k, statement, module, points)
      values (p_id || '.H' || k, p_id, p_problem, k, p_statements->>(k - 1), p_module, greatest(1, coalesce(p_points, 1) / n))
      on conflict (id) do nothing;
  end loop;
  insert into oma_events (kind, problem_id, handle, detail) values ('reduced', p_problem, p_handle, p_id || ' into ' || n || ' steps');
  return json_build_object('ok', true, 'steps', n);
end $$;

create or replace function oma_leaderboard2(p_minutes int)
returns json language sql security definer set search_path = public, pg_temp as $$
  with since as (select case when p_minutes is null then '-infinity'::timestamptz else now() - make_interval(mins => p_minutes) end as t),
  s as (select handle, count(distinct problem_id) as solved, count(*) filter (where polarity = 'disproof') as disproofs,
               coalesce(sum(points), 0) as points,
               (array_agg(agent order by created_at desc) filter (where agent is not null))[1] as agent,
               (array_agg(model order by created_at desc) filter (where model is not null))[1] as model
        from oma_solutions, since where verdict = 'accepted' and created_at >= since.t group by handle),
  l as (select handle, count(*) as claims, count(*) filter (where status in ('released','expired')) as handed_back,
               max(beat_at) as last_seen
        from oma_leases, since where created_at >= since.t group by handle)
  select coalesce(json_agg(r order by r.points desc, r.solved desc, r.claims desc, r.handle), '[]'::json) from (
    select coalesce(s.handle, l.handle) as handle, coalesce(s.solved, 0) as solved, coalesce(s.disproofs, 0) as disproofs,
           coalesce(s.points, 0) as points, s.agent, s.model,
           coalesce(l.claims, 0) as claims, coalesce(l.handed_back, 0) as handed_back, l.last_seen
    from s full join l on s.handle = l.handle
    order by 4 desc, 2 desc, 7 desc limit 200
  ) r;
$$;

create or replace function oma_solved_list(p_limit int)
returns json language sql security definer set search_path = public, pg_temp as $$
  select coalesce(json_agg(x order by x.created_at desc), '[]'::json) from (
    select distinct on (problem_id) problem_id, handle, agent, model, polarity, pr_url, points, contributors, created_at
    from oma_solutions where verdict = 'accepted' order by problem_id, created_at
  ) x limit least(greatest(coalesce(p_limit, 500), 1), 5000);
$$;

create or replace function oma_calendar(p_days int)
returns json language sql security definer set search_path = public, pg_temp as $$
  with d as (select generate_series((now() at time zone 'utc')::date - (least(greatest(coalesce(p_days, 60), 1), 366) - 1),
                                    (now() at time zone 'utc')::date, interval '1 day')::date as day)
  select coalesce(json_agg(json_build_object(
    'day', d.day,
    'claims', (select count(*) from oma_events e where e.kind = 'claim' and (e.created_at at time zone 'utc')::date = d.day),
    'released', (select count(*) from oma_events e where e.kind = 'release' and (e.created_at at time zone 'utc')::date = d.day),
    'submitted', (select count(*) from oma_events e where e.kind = 'submit' and (e.created_at at time zone 'utc')::date = d.day),
    'solved', (select count(*) from oma_events e where e.kind = 'accepted' and (e.created_at at time zone 'utc')::date = d.day),
    'reduced', (select count(*) from oma_events e where e.kind = 'reduced' and (e.created_at at time zone 'utc')::date = d.day),
    'people', (select count(distinct handle) from oma_events e where (e.created_at at time zone 'utc')::date = d.day)
  ) order by d.day desc), '[]'::json) from d;
$$;

create or replace function oma_steps_list(p_parent text)
returns json language sql security definer set search_path = public, pg_temp as $$
  select coalesce(json_agg(json_build_object(
    'id', s.id, 'reduction', s.reduction, 'parent', s.parent, 'k', s.k, 'statement', s.statement, 'module', s.module,
    'points', s.points, 'created_at', s.created_at,
    'solved', exists (select 1 from oma_solutions o where o.problem_id = s.id and o.verdict = 'accepted'),
    'reduction_pr', r.pr_url, 'reduction_by', r.handle
  ) order by s.created_at desc, s.k), '[]'::json)
  from oma_steps s join oma_reductions r on r.id = s.reduction
  where p_parent is null or s.parent = p_parent or s.id = p_parent;
$$;

revoke all on function oma_claim2(text, text, text, text, int), oma_verdict2(text, text, text, text, text, text, text, int),
  oma_register_reduction(text, text, text, text, text, json, int), oma_leaderboard2(int), oma_solved_list(int),
  oma_calendar(int), oma_steps_list(text) from public, anon, authenticated;

create or replace function public.oma_api(p_secret text, p_fn text, p_args json default '{}'::json)
returns json language plpgsql security definer set search_path = public, pg_temp as $$
declare
  v_ok boolean;
  a json := coalesce(p_args, '{}'::json);
begin
  select exists(select 1 from oma_private.config where key = 'api_secret' and value = p_secret and length(value) >= 32)
    into v_ok;
  if p_secret is null or not v_ok then
    raise exception 'forbidden' using errcode = '42501';
  end if;
  case p_fn
    when 'claim' then
      return oma_claim(a->>'problem', a->>'handle', a->>'agent', a->>'ip_hash');
    when 'claim2' then
      return oma_claim2(a->>'problem', a->>'handle', a->>'agent', a->>'ip_hash', (a->>'points')::int);
    when 'beat' then
      return oma_beat((a->>'lease')::uuid);
    when 'release' then
      return oma_release((a->>'lease')::uuid, a->>'reason');
    when 'verdict' then
      return oma_verdict(a->>'problem', a->>'handle', a->>'pr', a->>'verdict', a->>'polarity');
    when 'verdict2' then
      return oma_verdict2(a->>'problem', a->>'handle', a->>'pr', a->>'verdict', a->>'polarity', a->>'agent', a->>'model', (a->>'points')::int);
    when 'register_reduction' then
      return oma_register_reduction(a->>'id', a->>'problem', a->>'handle', a->>'pr', a->>'module', a->'statements', (a->>'points')::int);
    when 'stats' then
      return oma_stats();
    when 'live' then
      return (select coalesce(json_agg(json_build_object('problem_id', problem_id, 'agents', agents)), '[]'::json) from oma_live);
    when 'events' then
      return (
        select coalesce(json_agg(row_to_json(e) order by e.created_at desc), '[]'::json)
        from (
          select id, kind, problem_id, handle, detail, created_at from oma_events
          where ((a->>'problem') is null or problem_id = a->>'problem')
            and ((a->>'kind') is null or kind = a->>'kind')
            and ((a->>'before') is null or id < (a->>'before')::bigint)
          order by created_at desc
          limit least(greatest(coalesce((a->>'limit')::int, 60), 1), 200)
        ) e
      );
    when 'leaderboard' then
      return oma_leaderboard((a->>'hours')::int);
    when 'leaderboard2' then
      return oma_leaderboard2((a->>'minutes')::int);
    when 'profile' then
      return oma_profile(a->>'handle');
    when 'graveyard' then
      return oma_graveyard((a->>'limit')::int);
    when 'solved' then
      return oma_solved_list((a->>'limit')::int);
    when 'calendar' then
      return oma_calendar((a->>'days')::int);
    when 'steps' then
      return oma_steps_list(a->>'parent');
    else
      raise exception 'unknown function %', p_fn;
  end case;
end $$;

create or replace function oma_profile(p_handle text)
returns json language sql security definer set search_path = public, pg_temp as $$
  select json_build_object(
    'handle', p_handle,
    'solutions', (select coalesce(json_agg(x order by x.created_at desc), '[]'::json) from
                   (select problem_id, polarity, pr_url, agent, model, points, created_at from oma_solutions
                    where handle = p_handle and verdict = 'accepted') x),
    'contributed', (select coalesce(json_agg(x order by x.created_at desc), '[]'::json) from
                   (select problem_id, handle as lead, created_at from oma_solutions
                    where verdict = 'accepted' and contributors is not null and contributors::jsonb ? p_handle and handle <> p_handle) x),
    'points', (select coalesce(sum(points), 0) from oma_solutions where handle = p_handle and verdict = 'accepted'),
    'live', (select coalesce(json_agg(x), '[]'::json) from
              (select problem_id, created_at, beat_at from oma_leases
               where handle = p_handle and status = 'active' and beat_at > now() - interval '15 minutes') x),
    'events', (select coalesce(json_agg(x order by x.created_at desc), '[]'::json) from
                (select id, kind, problem_id, detail, created_at from oma_events where handle = p_handle order by created_at desc limit 80) x),
    'claims', (select count(*) from oma_leases where handle = p_handle),
    'firstSeen', (select min(created_at) from oma_leases where handle = p_handle)
  );
$$;
