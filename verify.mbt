///|
// The theorem registry: every requirement, as an executable check.
//
// Each entry returns a boolean computed from concrete instances, using
// only the public operations of the layers below.  Where the model is
// finite (face formulas, finite types) checks are exhaustive; where it
// is continuous (vectors, cubes) checks are equalities of explicit
// formulas verified on sample grids — the formulas themselves are the
// constructions (Kan filler, projector pruning), so the sample checks
// test the constructions' defining equations.

///|
pub struct CheckResult {
  name : String
  ok : Bool
}

///|
/// 1/√2 to double precision.
pub fn inv_sqrt2() -> Double {
  0.7071067811865476
}

///|
/// Unit vector spanning the example eigenspace: v = (1, i, 0)/√2.
pub fn example_unit() -> CVec {
  [cx(inv_sqrt2(), 0.0), cx(0.0, inv_sqrt2()), cx_zero()]
}

///|
/// The example Hermitian idempotent: P = v·v†.
pub fn example_projector() -> CMat {
  outer(example_unit())
}

///|
pub fn vec_e3() -> CVec {
  [cx_zero(), cx_zero(), cx_real(1.0)]
}

///|
pub fn sample_vectors() -> Array[CVec] {
  [
    [cx_real(1.0), cx(0.0, 1.0), cx(2.0, -1.0)],
    [cx_zero(), cx_zero(), cx_zero()],
    [cx(-1.0, 2.0), cx(0.5, 0.25), cx(0.0, -3.0)],
    example_unit(),
    vec_e3(),
  ]
}

///|
pub fn grid() -> Array[Double] {
  [0.0, 0.25, 0.5, 0.75, 1.0]
}

///|
pub fn check_projector() -> Bool {
  let p = example_projector()
  is_hermitian(p) &&
  is_idempotent(p) &&
  is_projector(p) &&
  (mat_trace_re(p) - 1.0).abs() < 0.000001
}

///|
pub fn check_eigenspace() -> Bool {
  let p = example_projector()
  eigenspace_well_formed(p, sample_vectors()) &&
  pruning_is_retraction(p, sample_vectors()) &&
  is_projector(complement(p))
}

///|
pub fn check_commuting() -> Bool {
  let p = example_projector()
  let q = outer(vec_e3()) // orthogonal range: PQ = 0 = QP
  let r = outer([cx(inv_sqrt2(), 0.0), cx_zero(), cx(inv_sqrt2(), 0.0)])
  commuting_projectors_compatible(p, q) &&
  commuting_projectors_compatible(p, complement(p)) &&
  !mat_commutes(p, r) // non-commuting pair is detected as such
}

///|
pub fn check_interval_faces() -> Bool {
  let i0 = face_var0(0)
  let i1 = face_var1(0)
  let j0 = face_var0(1)
  interval_laws_hold(grid()) &&
  eval_dim(DZero, [0.5]) == 0.0 &&
  face_unsat(FBot, 2) &&
  face_eq_mod(FOr(i0, i0), i0, 2) &&
  face_unsat(FAnd(i0, i1), 2) &&
  face_le(FAnd(i0, j0), i0, 2) &&
  !face_le(i0, j0, 2) &&
  face_eq_mod(FAnd(FTop, i0), i0, 2)
}

///|
pub fn check_systems() -> Bool {
  let v1 : CVec = [cx_real(1.0), cx_zero(), cx_zero()]
  let v2 = vec_e3()
  let i0 = face_var0(0)
  let i1 = face_var1(0)
  let sys = system_of([
    branch(i0, v1),
    branch(i1, v2),
    branch(FAnd(i0, face_var0(1)), v1), // subsumed by branch 1
    branch(FAnd(i0, i1), v2), // unsatisfiable face
  ])
  let bad = system_of([branch(FTop, v1), branch(i0, v2)])
  let a = system_of([branch(i0, v1)])
  let b = system_of([branch(i1, v2)])
  let ext_ok = match system_extend_top(a, v1, 2) {
    Some(_) => true
    None => false
  }
  let ext_bad = match system_extend_top(a, v2, 2) {
    Some(_) => false
    None => true
  }
  system_compatible(sys, 2) &&
  !system_compatible(bad, 2) &&
  pruning_respects_quotient(sys, 2) &&
  prune_system(sys, 2).branches.length() == 2 &&
  union_commutes_mod(a, b, 2) &&
  compatibility_respects_quotient(sys, b, 2) &&
  ext_ok &&
  ext_bad
}

///|
pub fn check_cube_comp() -> Bool {
  let p = example_projector()
  let u = example_unit()
  let u2 = vec_scale(2.0, u)
  let u3 = vec_scale_c(cx(0.0, 1.0), u) // i·u, still in im P
  let u4 = vec_scale(3.0, u)
  let bottom = path_line(u, u2)
  let left = path_line(u, u3)
  let right = path_line(u2, u4)
  let filler = square_fill(bottom, left, right)
  open_box_wf(bottom, left, right) &&
  filler_respects_box(filler, bottom, left, right, grid()) &&
  face_maps_commute(filler, 0.0, 1.0) &&
  face_maps_commute(filler, 1.0, 0.0) &&
  eigenspace_kan_sound(p, bottom, left, right, grid()) &&
  path_trans_endpoints(bottom, path_line(u2, u3)) &&
  vec_approx_eq(path_start(path_sym(bottom)), u2) &&
  vec_approx_eq(path_end(path_sym(bottom)), u)
}

///|
pub fn check_kan_pruning() -> Bool {
  let p = example_projector()
  let u = example_unit()
  let bottom = path_line(u, vec_scale(2.0, u))
  let left = path_line(u, vec_scale_c(cx(0.0, 1.0), u))
  let right = path_line(vec_scale(2.0, u), vec_scale(3.0, u))
  pruning_repairs_filler(p, bottom, left, right, vec_e3(), grid())
}

///|
pub fn sample_terms() -> Array[Term] {
  [
    tm_id(),
    tm_const(),
    tm_swap(),
    TmApp(tm_id(), TmBool(true)),
    TmApp(TmApp(tm_const(), TmBool(true)), TmBool(false)),
    TmApp(tm_swap(), TmPair(TmBool(true), TmUnit)),
    TmCoeRefl,
    TmCoeUaSwap,
    TmApp(TmCoeUaSwap, TmPair(TmUnit, TmBool(false))),
    TmPair(TmFst(TmPair(TmBool(false), TmUnit)), TmUnit),
  ]
}

///|
pub fn check_nbe() -> Bool {
  let beta = TmApp(TmApp(tm_const(), TmBool(true)), TmBool(false))
  let open_term = TmPair(TmSnd(TmVar(0)), TmFst(TmVar(0)))
  nbe_single_valued(sample_terms(), 0) &&
  nbe_single_valued([open_term], 1) &&
  nf(beta, 0) == TmBool(true) &&
  def_eq(TmApp(tm_id(), TmBool(false)), TmBool(false), 0) &&
  nf(tm_swap(), 0) == tm_swap()
}

///|
pub fn check_coe_definitional() -> Bool {
  coe_rules_definitional() && swap_involutive_on_element()
}

///|
pub fn check_hoas() -> Bool {
  let terms = sample_terms()
  for i in 0..<terms.length() {
    if !hoas_roundtrip_term(terms[i], 0) {
      return false
    }
  }
  let beta_in_hoas = happ(hoas_swap_example(), HPair(HBool(true), HUnit))
  hoas_roundtrip_hoas(hoas_swap_example(), 0) &&
  hoas_roundtrip_hoas(hoas_const_example(), 0) &&
  hoas_to_term(0, hoas_swap_example()) == tm_swap() &&
  hoas_to_term(0, beta_in_hoas) == TmPair(TmUnit, TmBool(true))
}

///|
pub fn check_ua_coe() -> Bool {
  let iso = iso_swap(TyBool, TyUnit)
  let p = iso_to_path(iso)
  let x = PVPair(PVBool(true), PVUnit)
  iso_wf(iso) &&
  upath_left(p) == TyProd(TyBool, TyUnit) &&
  upath_right(p) == TyProd(TyUnit, TyBool) &&
  coe_computes(p) &&
  coe_upath(p, 0, 1, x) == PVPair(PVUnit, PVBool(true)) &&
  coe_computes(ua(equiv_bool_not())) &&
  equiv_wf(equiv_prod(equiv_bool_not(), equiv_swap(TyBool, TyUnit)))
}

///|
pub fn check_pathp_exchange() -> Bool {
  let e1 = equiv_bool_not()
  let e2 = equiv_id(TyUnit)
  let pp = pathp_prod(
    pathp_canonical(ua(e1), PVBool(true)),
    pathp_canonical(ua(e2), PVUnit),
  )
  swap_naturality(e1, e2) &&
  pathp_wf(pp) &&
  pp.at1 == PVPair(PVBool(false), PVUnit) &&
  pathp_prod_exchange_roundtrip(pp, e1, e2)
}

///|
pub fn check_glue() -> Bool {
  let g = GlueData::{
    base_ty: TyBool,
    partial_ty: TyBool,
    equiv: equiv_bool_not(),
    face: face_var0(0),
  }
  // not(true) = false: compatible on the face (i = 0).
  let good = make_glue(g, PVBool(true), PVBool(false), 1)
  let bad = make_glue(g, PVBool(true), PVBool(true), 1)
  let good_ok = match good {
    Some(e) => glue_sound(g, e, 1) && unglue(e) == PVBool(false)
    None => false
  }
  let bad_rejected = match bad {
    Some(_) => false
    None => true
  }
  // On the empty face there is no constraint: Glue[⊥ ↦ …] A behaves as A.
  let g_bot = GlueData::{
    base_ty: TyBool,
    partial_ty: TyBool,
    equiv: equiv_bool_not(),
    face: FAnd(face_var0(0), face_var1(0)),
  }
  let bot_ok = match make_glue(g_bot, PVBool(true), PVBool(true), 1) {
    Some(e) => glue_sound(g_bot, e, 1)
    None => false
  }
  good_ok && bad_rejected && bot_ok
}

///|
pub fn check_j() -> Bool {
  let fam = Family::{ fiber: _x => TyBool, }
  let p = refl_path(TyBool, PVBool(true))
  let ill = DiscPath::{
    ty: TyBool,
    lo: PVBool(true),
    hi: PVBool(false),
    point: _t => PVBool(true),
  }
  let ill_rejected = match j_elim_disc(fam, PVBool(false), ill) {
    Some(_) => false
    None => true
  }
  j_roundtrip(fam, PVBool(false), p) && ill_rejected
}

///|
/// Transport in a constant family respects, and is respected by, the
/// orthogonal eigenspace decomposition: decompose, transport each
/// component (identity, in a constant family), recompose — the round-trip
/// is the identity and the two directions stay orthogonal throughout.
pub fn check_orthogonal_roundtrip() -> Bool {
  let p = example_projector()
  let samples = sample_vectors()
  for s in 0..<samples.length() {
    let v = samples[s]
    let (v1, v0) = decompose(p, v)
    if !vec_orthogonal(v1, v0) {
      return false
    }
    // forth: split; back: recompose.  Each component is a fixed point of
    // its own projector, so the round-trip cannot drift between summands.
    let back = vec_add(mat_vec(p, v1), mat_vec(complement(p), v0))
    if !vec_approx_eq(back, v) {
      return false
    }
    if !vec_approx_eq(mat_vec(p, v0), vec_zero(v.length())) {
      return false
    }
  }
  true
}

///|
pub fn run_all_checks() -> Array[CheckResult] {
  [
    CheckResult::{
      name: "幂等 Hermitian 矩陣 P²=P, P†=P（正交投影）",
      ok: check_projector(),
    },
    CheckResult::{
      name: "特徵空間良構性 Cⁿ=im(P)⊕ker(P)，特徵值 1/0，正交分解",
      ok: check_eigenspace(),
    },
    CheckResult::{
      name: "可交換投影相容性 PQ=QP ⇒ PQ 為投影（不交換者被檢出）",
      ok: check_commuting(),
    },
    CheckResult::{
      name: "區間 De Morgan 律與面公式商（蘊含／等價可判定）",
      ok: check_interval_faces(),
    },
    CheckResult::{
      name: "系統商：剪枝保商、聯集可交換、相容性保商、擴張可行性判定",
      ok: check_systems(),
    },
    CheckResult::{
      name: "立方體在區間上 comp：開盒填充邊界方程、面映射交換、路徑傳遞",
      ok: check_cube_comp(),
    },
    CheckResult::{
      name: "特徵空間 Kan 纖維化剪枝：P∘fill 保持邊界並落入 im(P)",
      ok: check_kan_pruning(),
    },
    CheckResult::{
      name: "NbE 單值性：nf(nf t)=nf t，定義相等由正規形判定",
      ok: check_nbe(),
    },
    CheckResult::{
      name: "coe 定義相等：coe^refl ≡ id，coe^(ua swap) ≡ swap（NbE）",
      ok: check_coe_definitional(),
    },
    CheckResult::{
      name: "HOAS 同構：往返一周 = NbE 正規形，正規形上嚴格相等",
      ok: check_hoas(),
    },
    CheckResult::{
      name: "同構即相等 ua：Iso→Equiv→Path，coe 計得 equivFun（wiring 符號驗證）",
      ok: check_ua_coe(),
    },
    CheckResult::{
      name: "PathP 積交換：swap∘(e₁×e₂)=(e₂×e₁)∘swap；PathP 積分解往返",
      ok: check_pathp_exchange(),
    },
    CheckResult::{
      name: "Glue 可靠性：φ ⊢ equivFun(partial)=unglue；不相容 glue 被拒",
      ok: check_glue(),
    },
    CheckResult::{
      name: "J 計算規則與往返：J(refl)=d 且沿 p、sym p 往返回 d",
      ok: check_j(),
    },
    CheckResult::{
      name: "往返正交：常值族 transport 在 im(P)⊕ker(P) 分量正交且往返恆等",
      ok: check_orthogonal_roundtrip(),
    },
    CheckResult::{
      name: "NbE 加 η：函數/積/單位 η 長正規形，swap∘swap ≡ id（函數層面）",
      ok: check_eta_all(),
    },
    CheckResult::{
      name: "符號判定：面公式 ROBDD 規範形（sat/≤/≡ 不再枚舉 2ⁿ）",
      ok: check_bdd_canonical(),
    },
    CheckResult::{
      name: "符號判定：有限等價 wiring 規範形（置換性、合成、逆，範疇＋相干性）",
      ok: check_wiring_category() && check_wiring_coherence(),
    },
    CheckResult::{
      name: "一般 Glue comp：有限等價線端點算法＋子空間線開盒 hcomp 校正",
      ok: check_glue_comp_all(),
    },
    CheckResult::{
      name: "範疇化：Karoubi／面偏序／立方體範疇／句法笛卡兒閉範疇律",
      ok: check_categories_all(),
    },
    CheckResult::{
      name: "規格登記健全：逐條範形/範疇/判定齊備，名稱與符號不重複",
      ok: spec_registry_sound(),
    },
    CheckResult::{
      name: "依賴 NbE：Π/Σ 與累積宇宙 Typeᵢ，依賴代入與型別導向轉換/η",
      ok: check_dep_all(),
    },
    CheckResult::{
      name: "Kan 結構全型別化：Π/Σ/Universe 的 coe/comp 遞迴，連同 LTy/Ty/子空間/Glue",
      ok: check_kan_all_types(),
    },
    CheckResult::{
      name: "完全符號代數：特徵多項式、譜投影 Lagrange 公式恆等、仿射唯一填充恆等",
      ok: check_symbolic_algebra_all(),
    },
    CheckResult::{
      name: "立方 AST：PathP、Nat/List 與 Circle/Torus 的語法、檢查、NbE 及依賴消去",
      ok: check_ast_paths() && check_ast_data() && check_ast_hits(),
    },
    CheckResult::{
      name: "Kan 項構造子：coe/comp/hcomp/hfill 與多分支系統在 AST 中計算，hcompU 產生 Glue",
      ok: check_ast_kan_terms(),
    },
    CheckResult::{
      name: "hcomp 按型別化簡：Π 反變、Σ 沿填充、Path 端點分支、資料構造子、HIT 形式點與 Universe",
      ok: check_ast_kan_types(),
    },
    CheckResult::{
      name: "語義系統重構：持久共享環境、惰性求值、語義快取、DSystem 按值合併排序與多分支 Glue",
      ok: check_phase5_semantic_systems(),
    },
    CheckResult::{
      name: "通用歸納族生成器：telescope、嚴格正性、Nat/Bool/List/Vec/Fin/Tree/W 的檢查、消去與 comp",
      ok: check_generated_inductive_schemas(),
    },
    CheckResult::{
      name: "通用 HIT 生成器：0/1/2 維 cells、face 化簡、巢狀 PathP 消去、Circle/Segment/Torus 與同 cell comp",
      ok: check_generated_hit_schemas(),
    },
    CheckResult::{
      name: "Schema 擴展：結構化正性、容器函子巢狀/互歸納/歸納遞迴、商 HIT、宇宙多態與任意維 cells",
      ok: check_schema_extensions(),
    },
    CheckResult::{
      name: "原始 DSystem：面相對轉換判定相容性，first-match 系統有精確不交範形",
      ok: check_dsystem_compatibility() && check_dsystem_first_match_nf(),
    },
    CheckResult::{
      name: "AST 一等 Equiv：Equiv/ua/GlueEquiv 的檢查、轉換、引文與 Kan 計算",
      ok: check_equiv_ast(),
    },
    CheckResult::{
      name: "受檢查型別線與 schema 註冊：維度代換封閉、驗證與 telescope elaboration 快取",
      ok: check_phase6_infrastructure(),
    },
    CheckResult::{
      name: "精確代數擴展：廣義特徵空間、Jordan 分解、代數數與根式範形",
      ok: check_algebraic_extensions_and_Jordan(),
    },
    CheckResult::{
      name: "BDD DAG 與認證數值：hash-consing/預算/DPLL，精確投影與多項式填充證書",
      ok: check_bdd_and_certified_numeric(),
    },
    CheckResult::{
      name: "球面 S³：S¹ 兩次懸掛 HIT，meridian 端點、依賴消去與 hcomp",
      ok: check_sphere3(),
    },
    CheckResult::{
      name: "Jacobi 譜迭代：每次酉旋轉的符號區間包含證書與 Gershgorin 特徵區間",
      ok: check_Jacobi_interval(),
    },
    CheckResult::{
      name: "高階合一 elaborator：Miller pattern 求解隱含引數與 Nat motive，核心編譯至 DTerm",
      ok: check_hou_elaborator(),
    },
    CheckResult::{
      name: "參數化模組：函子實例化抽象整段宣告，import/open/alias/rename 與歧義拒絕",
      ok: check_module_system(),
    },
  ]
}

///|
pub fn all_checks_pass() -> Bool {
  let results = run_all_checks()
  for i in 0..<results.length() {
    if !results[i].ok {
      return false
    }
  }
  true
}

///|
pub fn print_report() -> Bool {
  let results = run_all_checks()
  let mut passed = 0
  println("cubical-hermitian — 定理登記表")
  for i in 0..<results.length() {
    let r = results[i]
    if r.ok {
      passed = passed + 1
      println("[PASS] \{r.name}")
    } else {
      println("[FAIL] \{r.name}")
    }
  }
  println("passed \{passed}/\{results.length()}")
  passed == results.length()
}
