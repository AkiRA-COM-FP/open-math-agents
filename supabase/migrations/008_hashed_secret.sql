-- Accept a secret whose SHA-256 is stored (key 'api_secret_sha256'), so a new deployment's secret never has to be
-- written in clear anywhere but the deployment itself. The plain-text keys keep working as before.
do $mig$
declare d text;
begin
  select pg_get_functiondef('public.oma_api(text,text,json)'::regprocedure) into d;
  if position('api_secret_sha256' in d) = 0 then
    d := replace(d,
      $a$key in ('api_secret', 'api_secret_next') and value = p_secret and length(value) >= 32)$a$,
      $b$key in ('api_secret', 'api_secret_next') and value = p_secret and length(value) >= 32)
    or exists(select 1 from oma_private.config where key = 'api_secret_sha256' and length(p_secret) >= 32
              and value = encode(sha256(convert_to(p_secret, 'UTF8')), 'hex'))$b$);
    execute d;
  end if;
end
$mig$;
