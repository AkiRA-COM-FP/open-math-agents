-- Who contributed what to an accepted solution, as shares summing to 1 (used for signed certificates).
-- Direct proof: 100% to its author. Closed through a reduction: the reduction's author counts as one average step,
-- each step weighs its points; a step that was itself closed through a reduction is split again the same way.
create or replace function oma_contrib_rec(p_problem text, p_weight numeric, p_depth int)
returns jsonb language plpgsql stable security definer set search_path = public, pg_temp as $$
declare
  sol record; red record; st record;
  total numeric; avgp numeric; acc jsonb := '{}'::jsonb; sub jsonb; k text;
  add_share jsonb;
begin
  if p_depth > 8 then return acc; end if;
  select * into sol from oma_solutions where problem_id = p_problem and verdict = 'accepted' order by created_at limit 1;
  if not found then return acc; end if;
  if coalesce(sol.agent, '') <> 'reduction' then
    return jsonb_build_object(sol.handle, jsonb_build_object('share', p_weight, 'roles', jsonb_build_array(
      jsonb_build_object('role', case when p_depth = 0 then 'proof' else 'step' end, 'item', p_problem, 'pr', sol.pr_url, 'agent', sol.agent, 'model', sol.model))));
  end if;
  select * into red from oma_reductions where pr_url || '#closed' = sol.pr_url limit 1;
  if not found then
    return jsonb_build_object(sol.handle, jsonb_build_object('share', p_weight, 'roles', jsonb_build_array(jsonb_build_object('role', 'reduction', 'item', p_problem, 'pr', sol.pr_url))));
  end if;
  select coalesce(sum(points), 0), coalesce(avg(points), 0) into total, avgp from oma_steps where reduction = red.id;
  total := total + avgp;
  if total <= 0 then return acc; end if;
  acc := jsonb_build_object(red.handle, jsonb_build_object('share', p_weight * avgp / total, 'roles', jsonb_build_array(
    jsonb_build_object('role', 'reduction', 'item', red.id, 'pr', red.pr_url))));
  for st in select * from oma_steps where reduction = red.id order by k loop
    sub := oma_contrib_rec(st.id, p_weight * st.points / total, p_depth + 1);
    for k in select jsonb_object_keys(sub) loop
      if acc ? k then
        acc := jsonb_set(acc, array[k], jsonb_build_object(
          'share', (acc->k->>'share')::numeric + (sub->k->>'share')::numeric,
          'roles', (acc->k->'roles') || (sub->k->'roles')));
      else
        acc := acc || jsonb_build_object(k, sub->k);
      end if;
    end loop;
  end loop;
  return acc;
end $$;

create or replace function oma_contributions(p_problem text)
returns json language sql stable security definer set search_path = public, pg_temp as $$
  select coalesce(json_agg(json_build_object('handle', key, 'share', round((value->>'share')::numeric, 6), 'roles', value->'roles')
                           order by (value->>'share')::numeric desc, key), '[]'::json)
  from jsonb_each(oma_contrib_rec(p_problem, 1, 0));
$$;

revoke all on function oma_contrib_rec(text, numeric, int), oma_contributions(text) from public, anon, authenticated;

-- expose through the gated API
do $mig$
declare d text;
begin
  select pg_get_functiondef('public.oma_api(text,text,json)'::regprocedure) into d;
  if position('''contributions''' in d) = 0 then
    d := replace(d, $a$  case p_fn
$a$, $b$  case p_fn
    when 'contributions' then
      return oma_contributions(a->>'problem');
$b$);
    execute d;
  end if;
end
$mig$;
