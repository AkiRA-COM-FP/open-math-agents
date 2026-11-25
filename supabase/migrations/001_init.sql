-- Open Math Agents: coordination desk.
-- Run once in the Supabase SQL editor (or `supabase db push`). Everything lives in schema oma_*
-- tables of public, reachable only with the service role key (RLS on, no policies).

create extension if not exists pgcrypto;

create table if not exists oma_leases (
  id          uuid primary key default gen_random_uuid(),
  problem_id  text not null,
  handle      text not null,              -- GitHub handle the agent works for (claimed, verified at PR time)
  agent       text,                       -- free label: "claude-code", "codex", ...
  ip_hash     text,
  status      text not null default 'active'
              check (status in ('active','released','submitted','expired','settled')),
  reason      text,
  created_at  timestamptz not null default now(),
  beat_at     timestamptz not null default now(),
  ended_at    timestamptz
);
create index if not exists oma_leases_active on oma_leases (problem_id) where status = 'active';
create index if not exists oma_leases_handle on oma_leases (handle) where status = 'active';
create index if not exists oma_leases_created on oma_leases (created_at desc);

create table if not exists oma_solutions (
  id          uuid primary key default gen_random_uuid(),
  problem_id  text not null,
  handle      text not null,
  pr_url      text not null unique,
  verdict     text not null check (verdict in ('accepted','rejected','fault')),
  polarity    text not null default 'proof' check (polarity in ('proof','disproof')),
  created_at  timestamptz not null default now()
);
create index if not exists oma_solutions_problem on oma_solutions (problem_id) where verdict = 'accepted';

create table if not exists oma_events (
  id          bigserial primary key,
  kind        text not null,              -- claim | release | submit | accepted | rejected
  problem_id  text not null,
  handle      text,
  detail      text,
  created_at  timestamptz not null default now()
);
create index if not exists oma_events_created on oma_events (created_at desc);

alter table oma_leases enable row level security;
alter table oma_solutions enable row level security;
alter table oma_events enable row level security;

-- A lease is live while it has beaten in the last 15 minutes.
create or replace view oma_live as
  select problem_id, count(*)::int as agents, max(beat_at) as last_beat
  from oma_leases
  where status = 'active' and beat_at > now() - interval '15 minutes'
  group by problem_id;

-- Claim a problem. Caps: 5 live leases per handle, 3 claims per minute per ip.
create or replace function oma_claim(p_problem text, p_handle text, p_agent text, p_ip_hash text)
returns json language plpgsql security definer as $$
declare
  v_live int;
  v_recent int;
  v_id uuid;
  v_solved boolean;
begin
  if p_handle !~ '^[A-Za-z0-9](?:[A-Za-z0-9-]{0,38})$' then
    return json_build_object('error', 'bad_handle');
  end if;
  select exists(select 1 from oma_solutions where problem_id = p_problem and verdict = 'accepted') into v_solved;
  if v_solved then
    return json_build_object('error', 'already_solved');
  end if;
  -- expire stale leases of this handle first
  update oma_leases set status = 'expired', ended_at = now()
   where handle = p_handle and status = 'active' and beat_at < now() - interval '15 minutes';
  select count(*) into v_live from oma_leases where handle = p_handle and status = 'active';
  if v_live >= 5 then
    return json_build_object('error', 'too_many_leases', 'limit', 5);
  end if;
  if p_ip_hash is not null then
    select count(*) into v_recent from oma_leases where ip_hash = p_ip_hash and created_at > now() - interval '1 minute';
    if v_recent >= 3 then
      return json_build_object('error', 'rate_limited');
    end if;
  end if;
  -- one live lease per handle per problem: reuse it
  select id into v_id from oma_leases where handle = p_handle and problem_id = p_problem and status = 'active' limit 1;
  if v_id is null then
    insert into oma_leases (problem_id, handle, agent, ip_hash) values (p_problem, p_handle, left(p_agent, 64), p_ip_hash)
      returning id into v_id;
    insert into oma_events (kind, problem_id, handle, detail) values ('claim', p_problem, p_handle, left(p_agent, 64));
  else
    update oma_leases set beat_at = now() where id = v_id;
  end if;
  return json_build_object('lease', v_id);
end $$;

create or replace function oma_beat(p_lease uuid)
returns json language plpgsql security definer as $$
declare v_row oma_leases;
begin
  select * into v_row from oma_leases where id = p_lease;
  if not found then return json_build_object('error', 'unknown_lease'); end if;
  if v_row.status <> 'active' then return json_build_object('stop', true, 'status', v_row.status); end if;
  if exists(select 1 from oma_solutions where problem_id = v_row.problem_id and verdict = 'accepted') then
    update oma_leases set status = 'settled', ended_at = now() where id = p_lease;
    return json_build_object('stop', true, 'status', 'settled');
  end if;
  if v_row.beat_at < now() - interval '15 minutes' then
    update oma_leases set status = 'expired', ended_at = now() where id = p_lease;
    return json_build_object('stop', true, 'status', 'expired');
  end if;
  update oma_leases set beat_at = now() where id = p_lease;
  return json_build_object('ok', true);
end $$;

create or replace function oma_release(p_lease uuid, p_reason text)
returns json language plpgsql security definer as $$
declare v_row oma_leases;
begin
  update oma_leases
     set status = case when p_reason = 'submitted' then 'submitted' else 'released' end,
         reason = left(p_reason, 40), ended_at = now()
   where id = p_lease and status = 'active'
  returning * into v_row;
  if not found then return json_build_object('error', 'not_active'); end if;
  insert into oma_events (kind, problem_id, handle, detail)
    values (case when p_reason = 'submitted' then 'submit' else 'release' end, v_row.problem_id, v_row.handle, left(p_reason, 40));
  return json_build_object('ok', true);
end $$;

-- Called by the trusted verdict workflow (through /api/verdict).
create or replace function oma_verdict(p_problem text, p_handle text, p_pr text, p_verdict text, p_polarity text)
returns json language plpgsql security definer as $$
begin
  insert into oma_solutions (problem_id, handle, pr_url, verdict, polarity)
    values (p_problem, p_handle, p_pr, p_verdict, coalesce(p_polarity, 'proof'))
  on conflict (pr_url) do update set verdict = excluded.verdict;
  insert into oma_events (kind, problem_id, handle, detail) values (p_verdict, p_problem, p_handle, p_pr);
  if p_verdict = 'accepted' then
    update oma_leases set status = 'settled', ended_at = now() where problem_id = p_problem and status = 'active';
  end if;
  return json_build_object('ok', true);
end $$;

create or replace function oma_stats()
returns json language sql security definer as $$
  select json_build_object(
    'liveAgents',   (select coalesce(sum(agents), 0) from oma_live),
    'liveProblems', (select count(*) from oma_live),
    'top',          (select coalesce(json_agg(t), '[]') from (select problem_id, agents from oma_live order by agents desc, last_beat desc limit 12) t),
    'solved',       (select coalesce(json_agg(s), '[]') from (select distinct on (problem_id) problem_id, handle, polarity, pr_url, created_at from oma_solutions where verdict = 'accepted' order by problem_id, created_at) s),
    'solvedToday',  (select count(distinct problem_id) from oma_solutions where verdict = 'accepted' and created_at > now() - interval '24 hours'),
    'claimsToday',  (select count(*) from oma_leases where created_at > now() - interval '24 hours'),
    'contributors', (select count(distinct handle) from oma_leases)
  );
$$;

revoke all on function oma_claim, oma_beat, oma_release, oma_verdict, oma_stats from public, anon, authenticated;
