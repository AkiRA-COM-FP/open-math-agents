-- Single entry point gated by a server-side secret, so the app can run with the publishable key.
-- The secret lives in schema oma_private (not exposed by PostgREST). Set it once, outside git:
--   insert into oma_private.config (key, value) values ('api_secret', '<random>')
--   on conflict (key) do update set value = excluded.value;
-- and put the same value in Vercel as OMA_DB_SECRET.

create schema if not exists oma_private;
revoke all on schema oma_private from public, anon, authenticated;
create table if not exists oma_private.config (key text primary key, value text not null);
revoke all on oma_private.config from public, anon, authenticated;

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
    else
      raise exception 'unknown function %', p_fn;
  end case;
end $$;

revoke all on function public.oma_api(text, text, json) from public;
grant execute on function public.oma_api(text, text, json) to anon, authenticated, service_role;
