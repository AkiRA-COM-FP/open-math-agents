-- 3 claims per minute per IP blocked fleets and shared networks; 30 still stops floods.
create or replace function oma_claim(p_problem text, p_handle text, p_agent text, p_ip_hash text)
returns json language plpgsql security definer set search_path = public, pg_temp as $$
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
  update oma_leases set status = 'expired', ended_at = now()
   where handle = p_handle and status = 'active' and beat_at < now() - interval '15 minutes';
  select count(*) into v_live from oma_leases where handle = p_handle and status = 'active';
  if v_live >= 5 then
    return json_build_object('error', 'too_many_leases', 'limit', 5);
  end if;
  if p_ip_hash is not null then
    select count(*) into v_recent from oma_leases where ip_hash = p_ip_hash and created_at > now() - interval '1 minute';
    if v_recent >= 30 then
      return json_build_object('error', 'rate_limited', 'limit_per_minute', 30);
    end if;
  end if;
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
