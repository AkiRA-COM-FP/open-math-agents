-- Load before tests/api.test.mjs (with TEST_REDUCTION_PARENT=Erdos3.erdos_3.variants.green_tao); remove with tests/cleanup.sql.
select oma_register_reduction('Erdos3.erdos_3.variants.green_tao.R77', 'Erdos3.erdos_3.variants.green_tao', 'oma-test-fixture',
  'https://github.com/oma-test/x/pull/77', 'OMAReductions.R_Erdos3_erdos_3_variants_green_tao_R77', '["2 = 2","3 = 3"]'::json, 40);
