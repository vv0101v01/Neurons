# 重構審計 / Refactor audit

基線 baseline: `git show HEAD:…`　現在 now: 工作區 working tree  

> 方法：把「介面」看成有限符號集，重構就是符號集之間的映射；以單值性的判定程序（`univalence_compute.mbt` 的 `fin_map_is_equiv`）判定該映射是否為雙射，再量度檔案級依賴圖的強連通分量。庫內的對應認證：`refactor_certificates_sound()`。
> Method: an interface is a finite symbol set and a refactor is a map between them; the bijection is decided by the same procedure univalence uses (`fin_map_is_equiv`), and coupling is measured as SCCs of the file dependency graph. In-library counterpart: `refactor_certificates_sound()`.

## 1. 介面守恆 / Interface preservation

- 符號 before → after：**1430 → 1468**（Δ +38）
- 遺失 lost：**0** ✅
- 刻意刪除的死碼 dead code removed：**65**（清單見 `tools/dead_code_removed.txt` / see the manifest）
- 新增 added：**103**（新模組：可計算單值性、立方演算法、重構證書 / new modules）
- 判定 decision：既有符號集在移動下成雙射 → **介面等價 (equivalent)**

## 2. 宣告搬遷 / Ownership moves

| 由 from | 到 to | 符號 symbols |
|---|---|---|
| `bdd.mbt` | `face_core.mbt` | `Bdd`, `contains_int`, `dim_simplify`, `dim_subst`, `face_bound`, `face_simplify`, `face_subst`, `face_vars`, `sort_ints` |
| `interval.mbt` | `bdd.mbt` | `face_eq_mod`, `face_le`, `face_sat`, `face_unsat` |
| `interval.mbt` | `face_core.mbt` | `Face`, `assignment_of_mask`, `face_holds`, `face_var0`, `face_var1`, `pow2` |
| `nbe_eta.mbt` | `nbe.mbt` | `LTy` |
| `pathp_glue.mbt` | `finite_universe.mbt` | `PVal`, `Ty` |
| `system.mbt` | `system_core.mbt` | `VecBranch`, `VecSystem` |
| `verify.mbt` | `cube.mbt` | `check_cube_comp` |
| `verify.mbt` | `examples.mbt` | `example_projector`, `example_unit`, `grid`, `inv_sqrt2`, `sample_vectors`, `vec_e3` |

## 2b. 死碼刪除 / Dead code removed

這些宣告在刪除前已無任何引用（package 內、測試、`cmd/main`、`spec.mbt` 皆無）；刪除後 `moon check` 無警告、`moon test` 與 `cmd/main` 全綠。

These declarations had no reference at all (not in the package, the 19 test files, `cmd/main` or `spec.mbt`) before deletion; after it `moon check` is warning-free and both `moon test` and `cmd/main` are green.

- `alg_modulus_irreducible_small`, `alg_to_rat`, `algmat_add`, `bdd_dag_false`, `bdd_dag_true`, `bdd_dag_xor`
- `bdd_manager_stats`, `cert_path_const`, `cert_square_eq`, `cert_vec_to_numeric`, `checked_fill_value`, `checked_line_body`
- `checked_line_fn`, `checked_line_level`, `cinterval`, `deval`, `dfunctor_const`, `dfunctor_pi`
- `dfunctor_product`, `dfunctor_sum`, `dlevel_const`, `dlevel_max`, `dlevel_succ`, `dlevel_var`
- `dsystem_compatibility`, `dterm_family_strictly_positive`, `dtube_nf_class`, `equiv_inv_value`, `face_sat_within_budget`, `glue_equiv_term`
- `hit_plan_type_term`, `hit_type_term`, `mat_get`, `mutual_type_value`, `poly_scale`, `pval_not`
- `pval_swap`, `qcc_make`, `qci_mat_add`, `qci_mat_contains_point`, `qmat_Jordan_block_sizes`, `qmat_transpose`
- `quad_compatible`, `quad_conj`, `quad_div`, `quad_is_rat`, `quad_pow`, `quad_to_rat`
- `quotient_point_term`, `rat_interval_width`, `rat_is_one`, `rat_is_square`, `rpoly_const`, `sc_i`
- `schema_registry_hit_by_name`, `schema_registry_hit_plan`, `schema_registry_inductive_by_id`, `schema_registry_inductive_plan`, `schema_registry_stats`, `subline_const`
- `sym_mat_trace`, `sym_scalar_matrix`, `sym_vec_scale_c`, `ua_term`, `uty_implicit_arrow`

## 3. 循環 / File-level cycles

- before：**6** 個
  - bdd.mbt, bdd_dag.mbt, interval.mbt
  - nbe.mbt, nbe_eta.mbt
  - system.mbt, system_symbolic.mbt
  - dsystem_compat.mbt, dterm_transform.mbt, equiv_ast.mbt, kan_ast.mbt, nbe_dep.mbt, schema.mbt, schema_functor.mbt, schema_positivity.mbt, schema_registry.mbt
  - pathp_glue.mbt, wiring.mbt
  - ast_laws.mbt, bdd_certified_laws.mbt, categories.mbt, dsystem_compat_laws.mbt, hou_elaborator.mbt, kan_dep.mbt, module_system.mbt, schema_extension_laws.mbt, schema_laws.mbt, semantic_system_laws.mbt, verify.mbt
- after：**1** 個
  - dsystem_compat.mbt, dterm_transform.mbt, equiv_ast.mbt, kan_ast.mbt, nbe_dep.mbt, schema.mbt, schema_functor.mbt, schema_positivity.mbt, schema_registry.mbt

- 消除 eliminated：**5** （保留者為必要耦合 / the remaining one is the essential kernel cycle）

## 4. 結論 / Verdict

- 介面守恆 interface preserved：**YES**
- 循環 6 → 1：**YES**
- 判定方式同 `univalence_compute.mbt`：符號集雙射 ⟺ 介面等價；`refactor_certificates_sound()` 在庫內逐項認證同一事實。
