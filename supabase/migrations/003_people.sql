-- Leaderboard, per-handle profile and the graveyard (problems handed back, and why), behind oma_api.

create or replace function oma_leaderboard(p_hours int)
returns json language sql security definer set search_path = public, pg_temp as $$
  with since as (select case when p_hours is null then '-infinity'::timestamptz else now() - make_interval(hours => p_hours) end as t),
  s as (select handle, count(distinct problem_id) as solved, count(*) filter (where polarity = 'disproof') as disproofs
        from oma_solutions, since where verdict = 'accepted' and created_at >= since.t group by handle),
  l as (select handle, count(*) as claims, count(*) filter (where status in ('released','expired')) as handed_back,
               max(beat_at) as last_seen
        from oma_leases, since where created_at >= since.t group by handle)
  select coalesce(json_agg(r order by r.solved desc, r.claims desc, r.handle), '[]'::json) from (
    select coalesce(s.handle, l.handle) as handle, coalesce(s.solved, 0) as solved, coalesce(s.disproofs, 0) as disproofs,
           coalesce(l.claims, 0) as claims, coalesce(l.handed_back, 0) as handed_back, l.last_seen
    from s full join l on s.handle = l.handle
    order by 2 desc, 4 desc limit 200
  ) r;
$$;

create or replace function oma_profile(p_handle text)
returns json language sql security definer set search_path = public, pg_temp as $$
  select json_build_object(
    'handle', p_handle,
    'solutions', (select coalesce(json_agg(x order by x.created_at desc), '[]'::json) from
                   (select problem_id, polarity, pr_url, created_at from oma_solutions where handle = p_handle and verdict = 'accepted') x),
    'live', (select coalesce(json_agg(x), '[]'::json) from
              (select problem_id, created_at, beat_at from oma_leases
               where handle = p_handle and status = 'active' and beat_at > now() - interval '15 minutes') x),
    'events', (select coalesce(json_agg(x order by x.created_at desc), '[]'::json) from
                (select id, kind, problem_id, detail, created_at from oma_events where handle = p_handle order by created_at desc limit 80) x),
    'claims', (select count(*) from oma_leases where handle = p_handle),
    'firstSeen', (select min(created_at) from oma_leases where handle = p_handle)
  );
$$;

create or replace function oma_graveyard(p_limit int)
returns json language sql security definer set search_path = public, pg_temp as $$
  select json_build_object(
    'recent', (select coalesce(json_agg(x order by x.created_at desc), '[]'::json) from
                (select id, problem_id, handle, detail as reason, created_at from oma_events
                 where kind = 'release' order by created_at desc limit least(greatest(coalesce(p_limit, 100), 1), 300)) x),
    'byProblem', (select coalesce(json_agg(x order by x.total desc), '[]'::json) from
                (select problem_id, count(*) as total,
                        count(*) filter (where detail = 'statement_seems_false') as seems_false,
                        count(*) filter (where detail = 'missing_lemma') as missing_lemma,
                        count(*) filter (where detail in ('too_hard','out_of_time')) as too_hard,
                        count(*) filter (where detail = 'does_not_elaborate') as broken
                 from oma_events where kind = 'release' group by problem_id order by count(*) desc limit 100) x)
  );
$$;

revoke all on function oma_leaderboard(int), oma_profile(text), oma_graveyard(int) from public, anon, authenticated;

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
    when 'beat' then
      return oma_beat((a->>'lease')::uuid);
    when 'release' then
      return oma_release((a->>'lease')::uuid, a->>'reason');
    when 'verdict' then
      return oma_verdict(a->>'problem', a->>'handle', a->>'pr', a->>'verdict', a->>'polarity');
    when 'stats' then
      return oma_stats();
    when 'live' then
      return (select coalesce(json_agg(json_build_object('problem_id', problem_id, 'agents', agents)), '[]'::json) from oma_live);
    when 'events' then
      return (
        select coalesce(json_agg(row_to_json(e) order by e.created_at desc), '[]'::json)
        from (
          select id, kind, problem_id, handle, detail, created_at from oma_events
          where (a->>'problem') is null or problem_id = a->>'problem'
          order by created_at desc
          limit least(greatest(coalesce((a->>'limit')::int, 60), 1), 200)
        ) e
      );
    when 'leaderboard' then
      return oma_leaderboard((a->>'hours')::int);
    when 'profile' then
      return oma_profile(a->>'handle');
    when 'graveyard' then
      return oma_graveyard((a->>'limit')::int);
    else
      raise exception 'unknown function %', p_fn;
  end case;
end $$;
