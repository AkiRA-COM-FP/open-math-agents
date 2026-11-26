-- Secret rotation without downtime: rotate (old secret) adds api_secret_next; promote (new secret) revokes the old one.
create or replace function public.oma_api(p_secret text, p_fn text, p_args json default '{}'::json)
returns json language plpgsql security definer set search_path = public, pg_temp as $$
declare
  v_ok boolean;
  a json := coalesce(p_args, '{}'::json);
begin
  -- two secrets are accepted only while a rotation is in progress (api_secret_next is set)
  select exists(select 1 from oma_private.config where key in ('api_secret', 'api_secret_next') and value = p_secret and length(value) >= 32)
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
    when 'log' then
      return oma_log(a->>'kind', a->>'problem', a->>'handle', a->>'detail');
    when 'rotate' then
      if length(coalesce(a->>'new', '')) < 40 then return json_build_object('error', 'too_short'); end if;
      insert into oma_private.config (key, value) values ('api_secret_next', a->>'new')
        on conflict (key) do update set value = excluded.value;
      return json_build_object('ok', true, 'step', 'next secret accepted; deploy it, then call promote with it');
    when 'promote' then
      if not exists (select 1 from oma_private.config where key = 'api_secret_next' and value = p_secret) then
        return json_build_object('error', 'call promote with the new secret');
      end if;
      update oma_private.config set value = p_secret where key = 'api_secret';
      delete from oma_private.config where key = 'api_secret_next';
      return json_build_object('ok', true, 'step', 'old secret revoked');
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
