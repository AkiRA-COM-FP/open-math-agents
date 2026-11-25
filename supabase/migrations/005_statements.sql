-- Formalization of problems that have no Lean statement yet: a merged statements/<id>.lean is logged
-- (credited to its author) and the problem becomes a provable target at the next build.
create or replace function oma_log(p_kind text, p_problem text, p_handle text, p_detail text)
returns json language plpgsql security definer set search_path = public, pg_temp as $$
begin
  if p_kind not in ('formalized') then return json_build_object('error', 'bad_kind'); end if;
  if exists (select 1 from oma_events where kind = p_kind and problem_id = p_problem and detail = p_detail) then
    return json_build_object('ok', true, 'duplicate', true);
  end if;
  insert into oma_events (kind, problem_id, handle, detail) values (p_kind, p_problem, left(p_handle, 39), left(p_detail, 300));
  update oma_leases set status = 'settled', ended_at = now() where problem_id = p_problem and status = 'active';
  return json_build_object('ok', true);
end $$;
revoke all on function oma_log(text, text, text, text) from public, anon, authenticated;
