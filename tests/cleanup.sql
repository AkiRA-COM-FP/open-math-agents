-- Remove everything the integration tests created.
delete from oma_solutions where handle like 'oma-test-%' or pr_url like 'https://github.com/oma-test/%';
delete from oma_events where handle like 'oma-test-%';
delete from oma_leases where handle like 'oma-test-%';
delete from oma_steps where reduction like '%.OMATEST%' or reduction in (select id from oma_reductions where handle like 'oma-test-%');
delete from oma_reductions where handle like 'oma-test-%';
