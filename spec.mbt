///|
// The specification registry (規範形式與範疇化登記).
//
// Every type, operator, structure and specification in this project is
// registered here with three pieces of data:
//   canonical   — its normal / canonical form (規範形式): the chosen
//                 representative by which equality is decided;
//   categorical — its categorification (範疇化): the categorical structure
//                 it is an object / morphism / functor / law of;
//   decision    — how its governing equalities & predicates are decided.
// SPEC.md contains the same registry in document form, with an appendix
// listing every public symbol in the generated interface, grouped under
// these entries; tools/audit_spec.py checks the appendix is exhaustive.

///|
pub enum SpecKind {
  SpecType
  SpecOperator
  SpecStructure
  SpecTheorem
} derive(Debug, Eq)

///|
pub extend SpecKind with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend SpecKind with Eq::{not_equal, equal}

///|
pub struct SpecEntry {
  name : String
  kind : SpecKind
  symbols : Array[String]
  canonical : String
  categorical : String
  decision : String
}

///|
fn entry(
  name : String,
  kind : SpecKind,
  symbols : Array[String],
  canonical : String,
  categorical : String,
  decision : String,
) -> SpecEntry {
  SpecEntry::{ name, kind, symbols, canonical, categorical, decision, }
}

///|
pub fn spec_registry() -> Array[SpecEntry] {
  [
    entry(
      "複數標量",
      SpecType,
      ["Complex", "cx", "cx_add", "cx_mul", "cx_conj", "cx_approx_eq"],
      "(re, im) 有序對；相等以 eps 容差判定",
      "交換環 C 的元素；共軛是對合 (involution)",
      "分量比較",
    ),
    entry(
      "複向量與內積",
      SpecStructure,
      ["CVec", "vec_add", "vec_scale", "inner", "vec_orthogonal"],
      "分量表列；相等以 eps 逐分量判定",
      "有限維 Hilbert 空間 Hilb 的物件；內積給出對偶 v ↦ ⟨v, −⟩",
      "分量計算",
    ),
    entry(
      "複方陣與伴隨",
      SpecStructure,
      ["CMat", "mat_mul", "mat_adjoint", "mat_identity", "mat_vec", "outer2"],
      "列 (rows) 的表列",
      "Hilb 中的態射；伴隨 † 是 dagger 函子（反變、對合）",
      "矩陣運算",
    ),
    entry(
      "Hermitian／冪等／投影謂詞",
      SpecOperator,
      ["is_hermitian", "is_idempotent", "is_projector", "mat_commutes"],
      "P†=P 與 P²=P 兩方程的合取；規範形為 Σ vₖvₖ† (ONB 外積和)",
      "dagger 範疇中自伴冪等態射；其分裂即 Karoubi 包絡的物件",
      "eps 容差下矩陣方程",
    ),
    entry(
      "特徵空間分解",
      SpecTheorem,
      [
        "outer", "projector_from_orthonormal", "complement", "decompose", "in_image",
        "in_kernel", "eigenspace_well_formed", "prune_to_eigenspace", "pruning_is_retraction",
      ],
      "v 分解為 (Pv, (I−P)v) 的有序正交對",
      "冪等態射在 Hilb 中分裂：im(P) 是 retract，Cⁿ ≅ im(P) ⊕ ker(P) 是雙積 (biproduct)",
      "特徵值方程＋正交性＋tr(P) 整數性",
    ),
    entry(
      "可交換投影格",
      SpecTheorem,
      ["commuting_product", "commuting_projectors_compatible"],
      "交換族的乘積 PQ（交特徵空間的投影）",
      "投影偏序集 (P ≤ Q ⇔ QP=P) 中交換者的下確界 (meet)",
      "PQ=QP 方程",
    ),
    entry(
      "Karoubi 包絡",
      SpecStructure,
      ["karoubi_morphism", "karoubi_wrap", "karoubi_id", "karoubi_comp"],
      "物件：Hermitian 冪等 P；態射：被 (Q,P) 夾緊的矩陣 QAP=A",
      "冪等分裂完備化；恒等態射是 P 本身；† 給出 dagger 結構",
      "QAP=A 方程＋合成律抽樣驗證",
    ),
    entry(
      "Cubical 區間",
      SpecType,
      ["Dim", "eval_dim", "eval_dim_bool", "interval_laws_hold"],
      "De Morgan 代數表達式；端點語義化為布林公式",
      "區間物件 I 是 De Morgan 代數（有界分配格＋對合 ¬）",
      "端點求值＋dim_simplify 重寫",
    ),
    entry(
      "面公式（餘纖維）",
      SpecType,
      [
        "Face", "face_holds", "face_var0", "face_var1", "face_sat", "face_le", "face_eq_mod",
      ],
      "ROBDD（見下）",
      "餘纖維在面格中：子物件分類子的 cofibration 部分",
      "BDD 符號判定",
    ),
    entry(
      "面公式的 ROBDD 規範形式",
      SpecStructure,
      [
        "Bdd", "bdd_of_face", "bdd_not", "bdd_and", "bdd_or", "bdd_sat_face", "bdd_face_le",
        "bdd_face_eq", "face_witness", "dim_simplify", "face_simplify", "face_vars",
      ],
      "變量遞增序、等子節點消去的約化有序 BDD；結構相等即商相等",
      "自由有界分配格在生成元 Dim 變量上的規範代表；∧/∨ 即 BDD apply",
      "Shannon 展開＋常數簡化剪枝",
    ),
    entry(
      "面偏序範疇",
      SpecStructure,
      [
        "face_meet_universal", "face_join_universal", "check_face_poset_category",
      ],
      "物件為 BDD 等價類",
      "偏序範疇：∧=積，∨=餘積，⊤ 終物件，⊥ 始物件；態射存在性即 ≤",
      "bdd_face_le",
    ),
    entry(
      "系統（偏元素）與剪枝",
      SpecStructure,
      [
        "VecBranch", "VecSystem", "system_lookup", "system_compatible", "prune_system",
        "system_union", "union_commutes_mod", "system_extend_top",
      ],
      "符號規範形：以有效區域 BDD 分割端點立方體的值類別（system_normal_form）",
      "面上 presheaf 的偏元素；聯集是餘積式拼接，商由區域分割給出",
      "BDD 區域代數",
    ),
    entry(
      "系統符號規範形",
      SpecOperator,
      [
        "SymRegion", "SystemNF", "system_normal_form", "system_eq_mod_sym", "system_domain_bdd",
      ],
      "不交 BDD 區域＋值標籤，按值字典序排列，另加未定義區域",
      "偏元素到面格切片範疇中的像分解 (image factorisation)",
      "有效區域 φᵢ ∧ ¬(前覆蓋) 以 bdd_and/bdd_not/bdd_or 計算",
    ),
    entry(
      "立方體與路徑",
      SpecType,
      [
        "Cube", "cube_const", "path_line", "path_refl", "path_sym", "restrict_face",
        "degenerate_cube", "cube_ext_eq", "face_maps_commute",
      ],
      "函數 Iⁿ→Cᵐ 本身（語義立方體）；路徑範形為直線 path_line",
      "立方體範疇 □ 上的 cubical set 在 Cᵐ 中的實現；面/退化生成 □ 的態射",
      "樣本網格外延相等",
    ),
    entry(
      "Kan 填充與 comp（向量／特徵空間）",
      SpecOperator,
      [
        "open_box_wf", "square_fill", "kan_comp_path", "path_trans", "prune_cube",
        "kan_fill_eigenspace", "kan_comp_eigenspace", "eigenspace_kan_sound", "pruning_repairs_filler",
      ],
      "F(i,j)=b(i)+(1−i)(l(j)−b(0))+i(r(j)−b(1))，特徵空間版繼以 P 剪枝",
      "retract 的 Kan 纖維化結構：填充提升性質在 retraction 下封閉；comp 是帽子面",
      "邊界方程於樣本網格驗證",
    ),
    entry(
      "項語法與未型別 NbE",
      SpecStructure,
      [
        "Term", "Neutral", "Value", "eval", "quote", "nf", "def_eq", "nbe_single_valued",
        "coe_rules_definitional",
      ],
      "βπ-正規形（quote∘eval）",
      "λ× 句法範疇到指稱語義函子的單位/餘單位式分解；正規形是商的代表",
      "正規形結構相等",
    ),
    entry(
      "HOAS語法",
      SpecType,
      ["HTm", "happ", "term_to_hoas", "hoas_to_term", "hoas_roundtrip_term"],
      "reify 到 de Bruijn 正規形",
      "高階抽象語法作為函子範疇中的綁定；與一階語法互逆（模定義相等）即範疇等價",
      "reify/reflect 往返與 nf 比較",
    ),
    entry(
      "型別導向 NbE 與 η",
      SpecStructure,
      [
        "LTy", "TValue", "TNeutral", "ty_check", "ty_infer", "eval_check_t", "eval_infer_t",
        "quote_eta", "nf_eta", "def_eq_eta", "eta_single_valued_on",
      ],
      "η-長 βπ-正規形：函數 η 展開 λx.f x，積 η 展開 (fst p,snd p)，單位塌陷 ()",
      "自由笛卡兒閉範疇 (自由 CCC) 中態射的規範代表；quote 是按型別的反思 (reflection)",
      "雙向型別檢查＋按型別 quote＋結構比較",
    ),
    entry(
      "句法笛卡兒閉範疇",
      SpecStructure,
      [
        "tm_shift", "tm_comp_closed", "tm_comp_at", "tm_id_at", "check_syntactic_category",
      ],
      "箭頭：帶註記閉項，範形為其 nf_eta",
      "物件 LTy，態射為項模 βπη；積與指數由 λ/配對給出萬有性",
      "def_eq_eta 判定結合律／恒等律／逆律",
    ),
    entry(
      "Finite universe 型別與值",
      SpecType,
      ["Ty", "PVal", "elems_of", "in_ty", "leaves_of_ty", "flatten_pval"],
      "型別樹的葉序 (leaf sequence)；值樹展平為葉值列",
      "有限集合範疇中的物件，由 Bool/Unit 以積生成",
      "樹遞迴",
    ),
    entry(
      "Wiring 符號等價",
      SpecStructure,
      [
        "LeafKind", "LeafMap", "Wiring", "wiring_id", "wiring_not", "wiring_swap",
        "wiring_prod", "wiring_comp", "wiring_inv", "wiring_assoc", "wiring_left_unitor",
        "wiring_right_unitor", "wiring_wf", "wiring_eq", "wiring_apply",
      ],
      "帶號置換：每輸出葉的 (源索引, 否定旗)；Unit 輸出規範為 (−1,false)",
      "自由對稱冪冪範疇在 Bool(帶對合)/Unit 生成元上的態射；⊗ 與換位子 (braiding)",
      "置換性判定 O(#葉)；合成＝替換＋XOR；相等＝結構相等",
    ),
    entry(
      "同構／等價／ua／coe",
      SpecStructure,
      [
        "Iso", "Equiv", "UPath", "iso_of_wiring", "equiv_of_wiring", "iso_to_equiv",
        "equiv_prod", "equiv_comp", "equiv_inv", "equiv_wf", "equiv_ext_eq", "ua",
        "iso_to_path", "coe_upath", "coe_computes", "upath_eq", "swap_naturality",
      ],
      "wiring 規範形；coe 按端點分情況計算為 equivFun/equivInv/id",
      "ua 是 (A≃B)≃(A=B) 在此有限宇宙的迭代；swap 自然性方塊是交換圖",
      "wiring_eq 與 w;w⁻¹=id 的 wiring 等式",
    ),
    entry(
      "PathP 與離散路徑、J",
      SpecStructure,
      [
        "PathPVal", "pathp_canonical", "pathp_wf", "pathp_prod", "pathp_fst", "pathp_snd",
        "pathp_prod_exchange_roundtrip", "DiscPath", "refl_path", "disc_path_sym",
        "Family", "j_elim_disc", "j_roundtrip",
      ],
      "PathP 規範元：遠端 = coe 之像；離散路徑規範形為常值",
      "路徑物件與依賴路徑 (PathP)；J 是常值線上 coe 的恒等性陳述",
      "端點型別＋點值檢驗",
    ),
    entry(
      "有限 Glue（形成／可靠）",
      SpecStructure,
      [
        "GlueData", "GlueElem", "glue_wf", "make_glue", "unglue", "glue_restrict",
        "glue_from_base", "glue_sound",
      ],
      "(partial, base) 對；由 base 造的規範元 glue_from_base",
      "Glue 是沿等價把偏型別 T 黏到 A 的 (餘)極限式構造；unglue 是投影到 A 的纖維化",
      "φ 的 BDD 可滿足性＋相容方程",
    ),
    entry(
      "一般 Glue comp（有限線）",
      SpecOperator,
      [
        "GlueLineFinite", "glue_data_at0", "glue_data_at1", "glue_line_coherent",
        "glue_comp_finite", "glue_comp_finite_correct",
      ],
      "輸出 base 是校正後的 e₁(t₁)（當 φ₁ 成立）",
      "等價線 = 箭頭範疇 (arrow category) 中的態射；comp 是箭頭範疇中沿線的合成",
      "自然性方塊以 wiring_eq 判定；拒絕不相干線數據",
    ),
    entry(
      "特徵子空間線上的 Glue comp",
      SpecOperator,
      [
        "SubLine", "LinEquivLine", "GlueLineVec", "VecBox", "GlueCompVecResult",
        "prune_cube_subline", "fill_subline", "glue_box_compatible", "glue_comp_vec",
        "glue_comp_vec_sound",
      ],
      "校正方塊 (i,k)↦(1−k)·a_cap(i)+k·U(1)(t_cap(i)) 的 k=1 邊",
      "retract 線族上的 Kan 填充；校正即 A(1) 中的 hcomp 提升",
      "邊界/帽子/落點方程於網格驗證",
    ),
    entry(
      "依賴型別 NbE（Π/Σ/宇宙）",
      SpecStructure,
      [
        "DTerm", "DValue", "DNeutral", "DInfer", "d_infer", "d_check", "d_as_type",
        "conv_at", "conv_ty", "quote_at", "quote_ty", "dep_check_closed", "dep_nf_closed",
        "dep_type_of_closed", "lty_to_dterm", "check_dep_all",
      ],
      "按型別 quote 的 η 長依賴正規形；Π/Σ 的第二分量是語義閉包族，宇宙為累積層級 Typeᵢ:Typeᵢ₊₁",
      "帶族範疇 (categories with families) 的句法模型：脈絡延伸、依賴代入是閉包施用；單純片斷嵌入為非依賴 Π/Σ",
      "雙向 elaboration ＋ 型別導向 conversion；相等為範形結構相等",
    ),
    entry(
      "依賴 Kan 線 coe/comp",
      SpecStructure,
      [
        "DLine", "dline_at", "dcoe", "dfill", "dcomp", "dline_const", "dline_pi",
        "dline_sigma", "dline_univ", "dline_of_lty", "dline_of_ty", "dline_of_upath",
        "check_kan_all_types",
      ],
      "DLine{at, coe_fn, fill_fn}；Π 的 coe 在定義域反向、Σ 的第二分量沿第一分量路徑傳輸；comp=fill(1)",
      "型別即 Kan 纖維化結構；依賴族呈現為 (A 中的路徑)→DLine；連同特徵子空間與 Glue 覆蓋全專案型別族",
      "對型別構造子遞迴求值；coe(r,r) 由 wrapper 定義地恆等",
    ),
    entry(
      "精確符號代數",
      SpecStructure,
      [
        "Rat", "Poly", "PolyTerm", "SymFrac", "SymC", "SymMat", "UPoly", "poly_add",
        "poly_mul", "frac_eq", "sym_det", "charpoly_sym", "sym_projector_rank_one",
      ],
      "Q 上多變量多項式規範形（合併、去零、字典序）；分式以交叉相乘判定相等；複量為實符號有序對",
      "多項式戒與其分式體提供矩陣的代數語義；特徵多項式是 det(XI−A) 的精確展開",
      "多項式恆等（無 eps、無抽樣）",
    ),
    entry(
      "譜投影與仿射唯一填充的符號恆等",
      SpecTheorem,
      [
        "RPoly", "RPolyDiv", "spectral_q", "spectral_minpoly", "spectral_denominator",
        "spectral_projector_sym", "rpoly_divisible_by", "sym_square_fill", "sym_bilinear_from_corners",
        "sym_bilinear_ansatz", "check_symbolic_algebra_all",
      ],
      "譜投影 Pₖ=qₖ(A)/qₖ(λₖ)；仿射填充是四角的雙線性插值，繫數由角值唯一解出",
      "譜分解給出單位分解 ΣPₖ=I 與 ΣλₖPₖ=A；雙線性插值是張量積意義下兩個仿射方向的唯一黏合",
      "首一多項式整除（模最小多項式）及在座標原子 i,j 上的多項式恆等",
    ),
    entry(
      "立方 AST、PathP 與維度 NbE",
      SpecStructure,
      [
        "DTubeTerm", "d_tube", "DPathParts", "DGlueParts", "deval_dim", "eval_dim_expr",
        "dim_quote", "face_eval_env", "face_quote", "dapp_dim", "eval_tube_terms",
        "quote_tube_branches", "dep_def_eq_closed", "check_ast_paths",
      ],
      "同一 DTerm 以分離的項/維度 de Bruijn 索引表示型別線、tube 系統與路徑；範形由帶維度層級的 quote 給出，HIT 點在端點正規化",
      "帶區間脈絡的 cubical CwF 句法模型：PathP 是沿 I 的依賴路徑物件，維度代換即 denv 求值；Glue 值以 (單分支 raw 或多分支 DVPartial partial, base) 對表示",
      "雙向 elaboration；Dim/Face 以 dim_simplify、face_simplify 與 ROBDD 語義謂詞判定",
    ),
    entry(
      "AST Kan 運算 comp/hcomp/hfill/coe",
      SpecOperator,
      [
        "comp_value", "hcomp_value", "fill_value", "hfill_value", "coe_value", "comp_pi_value",
        "comp_sigma_value", "comp_path_value", "comp_glue_value", "comp_univ_value",
        "hcomp_univ_value", "check_ast_kan_terms", "check_ast_kan_types", "check_ast_kan_all",
      ],
      "在一般維度取樣型別線後按頭構造子派遣：Π 沿反向定義域填充、Σ 沿第一分量填充、PathP 加端點分支、Universe 產生保留完整 DSystem 的 Glue；coe/fill 由 comp 的線段限制得到",
      "每個型別構造子保存 Kan 纖維化結構；系統分支是餘纖維上的偏路徑，形式 DNComp/DNHComp 是未化簡合成的中性見證",
      "系統以 base 相容與分支重疊相容檢查；頂面分支取帽、底面分支消去；其餘由型別遞迴或形式中性項判定",
    ),
    entry(
      "資料型別與高階歸納型別消去",
      SpecStructure,
      [
        "d_nat_lit", "dv_nat_lit", "eval_bool_elim", "eval_nat_elim", "eval_list_elim",
        "circle_point", "torus_point", "eval_circle_elim", "eval_torus_elim", "comp_bool_value",
        "comp_nat_value", "comp_list_value", "comp_circle_value", "comp_torus_value",
        "check_ast_data", "check_ast_hits",
      ],
      "Nat/List 以建構子遞迴；Circle 點為 loop@r（端點為 base），Torus 點為 square@(i,j) 且對邊等同；非平凡 HIT 系統保留形式 hcomp 點",
      "Nat/List 是依賴消去的初始代數；Circle/Torus 是帶路徑/方塊生成元的 HIT，消去子是 motive 的截面並與形式 composition 交換",
      "構造子模式遞迴、HIT 點座標的 Dim 語義相等，以及在 motive 中 composition 的消去交換律",
    ),
    entry(
      "持久環境、惰性與語義快取",
      SpecStructure,
      [
        "DEnv", "DDimEnv", "DThunk", "denv_cons", "ddim_cons", "denv_extend", "lazy_value",
        "force_value", "lazy_deval", "memo_dim_line", "memo_family", "check_persistent_env_lazy_cache",
      ],
      "帶長度的持久連結串列：cons 以 O(1) 共享尾部，陣列版環境只在公開邊界轉換一次；DVThunk 強制後保存值且最多計算一次；維度線以簡化 Dim 鍵、型別族以引文項鍵 memoize",
      "CwF 的脈絡延伸與弱化由共享環境尾部實現；惰性語義值是 call-by-need 值，快取是外延函數圖的有限延伸而不改變其指稱",
      "de Bruijn 索引查找、force_count 觀察與穩定 Debug 快取鍵相等",
    ),
    entry(
      "依賴語義系統與 partial 值",
      SpecStructure,
      [
        "DTubeBranch", "tube_branch", "DSystem", "dsystem_of", "dsystem_canonical",
        "DFaceTerm", "DPartialValue", "partial_normal_form", "DSystemNF", "partial_eq_at",
        "glue_partial_values", "glue_store_partial", "check_phase5_semantic_systems",
      ],
      "DSystem 先去底面並簡化面；沿型別線的規範形把可轉換 body 以面聯集合併並按引文排序。partial 值的範形是 BDD 有效區域值類別加未定義區域；DVGlue 保存全部 partial type 分支",
      "面格切片中的偏元素：系統是餘纖維上的偏路徑/偏元素，多分支 Glue 是 partial type 系統與 base type 的配對極限表示",
      "有效區域以 BDD and/not/or 計算；分支合併與排序以型別導向轉換及引文鍵判定",
    ),
    entry(
      "通用歸納族 schema",
      SpecStructure,
      [
        "DArgKind", "DTelescopeEntry", "DConstructorArg", "DConstructorSpec", "DInductiveSpec",
        "dinductive_spec", "inductive_schema_validate", "inductive_case_type", "eval_inductive_elim",
        "infer_inductive_elim", "comp_inductive_value", "nat_schema", "vec_schema",
        "w_schema", "check_generated_inductive_schemas",
      ],
      "有限描述子：參數/索引 telescopes、外部/直接遞迴/函數遞迴引數與結果索引；值範形為引文的 DIntro， 中性消去按生成 motive/case 型別引文",
      "嚴格正性依賴多項式函子的初始代數；依賴消去是 motive 的截面，Kan comp 沿先前引數 filler 逐引數遞迴，函數遞迴引數以 Π comp 處理",
      "描述子結構相等；telescope 與引數/索引由雙向檢查驗證；外部型別與函數定義域以同名族掃描拒絕非嚴格正性出現",
    ),
    entry(
      "通用 HIT schema",
      SpecStructure,
      [
        "DHitFaceExpr", "DHitCellSpec", "DHitSpec", "dhit_spec", "hit_schema_validate",
        "hit_cell_value", "hit_case_type", "eval_hit_elim", "infer_hit_elim", "comp_hit_value",
        "circle_schema", "segment_schema", "torus_schema", "check_generated_hit_schemas",
      ],
      "0/1/2 維 cells：DVHitCell 的維度先簡化，任一端點即代入對應 face expression 遞迴化簡；消去 case 型別為逐維巢狀 PathP，端點是較低維 face 的消去值",
      "帶 face 映射的胞腔高階初始代數；依賴消去把 point/path/square cells 送到 motive 的截面與其路徑/方塊，comp 只在同 cell 同維度時逐引數計算，其餘保留形式合成",
      "face 的目標 cell、引數型別與結果索引由檢查器驗證；2-cell 以兩種維度化簡次序在四角轉換相等驗證相容性",
    ),
    entry(
      "Schema 擴展：函子正性、互歸納、商與宇宙多態",
      SpecStructure,
      [
        "DPositiveFunctor", "DConstructorConstraint", "DMutualFamily", "DLevelExpr",
        "dpositivity_report", "positive_functor_map", "compile_mutual_inductive",
        "instantiate_inductive_level_scheme", "quotient_schema", "decode_term", "check_schema_extensions",
      ],
      "遞迴引數以完整型別或 DPositiveFunctor 解碼，IH 依函子結構生成；互歸納編譯為 Sum-indexed 單一 schema；商是帶等式 cell 的 HIT，任意有限維 cells 逐維以 face expression 化簡",
      "正性函子與互歸納族的初始代數、Tarski 解碼的歸納—遞迴對，以及宇宙層級指派下的 schema 族",
      "別名展開後以極性遞迴判定嚴格正性；構造子 Path 約束、層級 scheme 求值與多維 face 相干性均由檢查器驗證",
    ),
    entry(
      "原始 DSystem 相容性與 first-match 範形",
      SpecStructure,
      [
        "DSystemCompatibility", "DTubeNF", "conv_at_under_face", "dsystem_checked",
        "dsystem_compatibility_report", "dsystem_first_match_normal_form", "check_dsystem_compatibility",
        "check_dsystem_first_match_nf",
      ],
      "相容原始系統經 checked 入口化為通常的型別導向 DSystem 範形；任意 first-match 系統化為互不交疊的有效區域與值路徑類別",
      "面切片中的原始偏元素到 composition 偏元素的相容性反射；first-match 是優先序區域分解",
      "將面轉成 BDD cubes 並在局部維度脈絡下逐 cube 轉換比較 base 與兩兩分支，首個衝突精確回報",
    ),
    entry(
      "AST 一等 Equiv、ua 與 GlueEquiv",
      SpecStructure,
      [
        "DEquivParts", "DGlueEquivParts", "as_equiv_type", "mk_equiv_term", "infer_ua",
        "comp_equiv_value", "comp_glue_equiv_value", "check_equiv_ast",
      ],
      "Equiv 值由正向函數、反向函數與 section/retraction Path 證明組成；GlueEquiv 分支保存完整 partial type 與其指向 base 的一等等價",
      "AST 內帶同倫逆的等價範疇；ua 把等價送入宇宙路徑，GlueEquiv 是沿偏等價系統黏合的型別",
      "雙向檢查 Equiv 四分量，conversion/quote 遞迴至各分量；沿 ua 的 coe 直接計算為 fwd 或 bwd",
    ),
    entry(
      "受檢查型別線與 schema 註冊快取",
      SpecStructure,
      [
        "DCheckedTypeLine", "DSchemaRegistry", "DInductivePlan", "checked_type_line",
        "checked_comp_value", "schema_registry_register_inductive", "schema_registry_validate_hit",
        "default_schema_registry", "check_phase6_infrastructure",
      ],
      "受檢查線保存已驗證的開放型別 body 與環境而不保存任意宿主函數；schema 以穩定鍵 intern 為 plan，telescope 保存完整前綴鏈",
      "由句法 body 表示的型別線與維度代換自然交換；註冊表是 schema elaboration 函數的有限共享圖",
      "在新鮮維度下檢查線 body 的宇宙層級；registry 以鍵命中驗證及語義 telescope，計數器使重用可觀察",
    ),
    entry(
      "精確單變量多項式與有理矩陣",
      SpecStructure,
      [
        "QPoly", "QMat", "QRref", "qpoly_normalize", "qpoly_gcd", "qpoly_extgcd",
        "qpoly_factor_rational_roots", "qmat_charpoly", "qmat_minimal_polynomial",
        "qmat_inverse",
      ],
      "QPoly 為去除尾零的升冪有理係數列，QMat 為有理列之列，線性子空間以 RREF 自由變量基底表示",
      "歐氏環 Q[x] 與有限維有理線性範疇；矩陣多項式求值給出 Q[x] 模結構",
      "primitive pseudo-remainder gcd/extgcd、Yun squarefree 分解、有理根枚舉、Faddeev–LeVerrier 與精確 RREF",
    ),
    entry(
      "代數擴張、廣義特徵空間與 Jordan 理論",
      SpecStructure,
      [
        "QuadNum", "AlgNum", "AlgMat", "QGeneralizedEigenspace", "QJordanDecomposition",
        "quad_denested_sqrt", "alg_rebase_to_minimal", "qmat_generalized_projector",
        "qmat_Jordan_decomposition", "algmat_Jordan_decomposition", "check_algebraic_extensions_and_Jordan",
      ],
      "QuadNum 為 a+b√d 的無平方因數範式，AlgNum 為模極小多項式的餘式；Jordan 分解由廣義核鏈的塊大小與鏈基底給出",
      "有限代數擴張體上的線性代數；主分解來自互質多項式因子的單位分解，Jordan 型刻畫分裂時的相似類",
      "以特徵多項式重數、(A−λI) 冪次 nullity 與鏈提升精確計算；Q 上未分裂部分保留殘餘因子並可在 AlgMat 擴張上處理",
    ),
    entry(
      "BDD DAG、預算搜尋與認證數值影子",
      SpecStructure,
      [
        "BddManager", "FaceDecision", "FaceSatDecision", "bdd_dag_of_face_best",
        "face_eq_within_budget", "face_sat_dpll", "QuadC", "CertMat", "CertPath",
        "ProjectorCertificate", "certify_numeric_projector", "check_bdd_and_certified_numeric",
      ],
      "面在 manager 中以 hash-consed root 表示，大小為 reachable DAG 節點；數值矩陣的精確影子由 QuadC 矩陣與多項式係數立方體給出",
      "布林函數的共享 ROBDD 圖與精確複二次矩陣代數；Double 層是影子的近似觀察而非等式來源",
      "同 manager root 相等判定面等式，節點預算或 DPLL 處理不可行建構；投影與填充恆等以精確結構相等驗證，浮點只量偏差與 residual",
    ),
    entry(
      "容器函子巢狀遞迴、互歸納與歸納遞迴宣告面",
      SpecStructure,
      [
        "dfunctor_container", "container_tree_schema", "check_container_functor_tree",
        "check_mutual_inductives", "check_tarski_induction_recursion",
      ],
      "DFunctorContainer(shape, positions, index) 表示 Sigma(s:Shape), Positions(s)->X(index s p)，與既有正性函子、互歸納編譯和 DDecode 共用生成器",
      "任意有限依賴多項式/container 函子的初始代數；互歸納是標籤索引和，歸納—遞迴是碼族與解碼的同時初始結構",
      "形狀與位置型別不得提及本族，遞迴索引在 shape/position 兩綁定子下檢查；IH 是對所有 positions 的 Pi 型",
    ),
    entry(
      "懸掛球面與 S³",
      SpecStructure,
      [
        "suspension_schema", "sphere_schema", "sphere2_schema", "sphere3_schema",
        "sphere3_meridian_term", "sphere3_meridian_value", "check_sphere3",
      ],
      "Susp(X) 由 north、south 與每點一條 meridian 生成；S² 與 S³ 分別是圓的一次與兩次懸掛，端點在 hit_cell_value 中化簡",
      "把 X×I 的上下端各塌縮成一點的 HIT；消去子由南北兩點的值和所有 meridian 上的依賴路徑組成",
      "基底 HIT 須無索引且先驗證；端點、恆等消去與固定 meridian 的 hcomp 以轉換與引文範形判定",
    ),
    entry(
      "Jacobi 酉旋轉的符號區間證書",
      SpecStructure,
      [
        "RatInterval", "CInterval", "QCpxMat", "QCIntervalMat", "JacobiCoefficients",
        "JacobiRotationCertificate", "JacobiCertificate", "jacobi_coefficients",
        "jacobi_unitary_interval", "jacobi_interval_eigen", "jacobi_certificate_sound",
        "check_Jacobi_interval",
      ],
      "精確 Hermitian 點矩陣的複矩形區間包絡；每次旋轉保存 before/after、累積變換與有理 c/s/phase 包絡，矩陣以 dyadic 外向捨入保持有界分母",
      "酉相似變換在區間矩陣格上的包含單調提升；最終 Hermitian 包絡的 Gershgorin 圓盤依重疊分簇並計重數",
      "sqrt 以整數二分和精確平方比較包絡；逐旋轉重算係數包含、J†J-I 含零、after 包 J†AJ 與 transform 包 VJ",
    ),
    entry(
      "Miller pattern 高階合一與雙向 elaborator",
      SpecStructure,
      [
        "UTerm", "Unifier", "STerm", "Elaborator", "ElabResult", "hou_fresh_meta",
        "hou_unify", "hou_semantic_optimize", "elab_infer", "elab_check", "elab_result_to_dterm",
        "check_hou_elaborator",
      ],
      "表面命名項解析為 de Bruijn UTerm；metavariable 以作用域變量的 pattern spine 表示，zonked 核心經 beta/投影/Nat 語義簡化後譯至 DTerm",
      "Miller pattern 是高階合一的可判定片斷；雙向 elaboration 將隱含型別引數與 dependent motive 化為同一類 flex-rigid 問題",
      "WHNF、eta、rigid 分解、不同綁定變量 spine 的抽象、occurs/scope 檢查；未解 metavariable 不得進入 DTerm，結果再由依賴檢查器驗收",
    ),
    entry(
      "參數化模組、import/open 與名字空間",
      SpecStructure,
      [
        "ModuleDef", "ModuleImport", "ModuleDecl", "ModuleEnv", "ModuleSignature",
        "ModuleInstance", "module_signature", "module_validate", "module_resolve",
        "module_ref", "module_instantiate", "module_instance_find", "check_module_system",
      ],
      "模組是參數、imports、本地宣告組成的 telescope；bindings 把限定名、別名與 opened/renamed 名映射到 telescope ordinal，實例是同時代換的閉合宣告列",
      "參數化模組是函子，import 是遞迴函子套用後內聯，open 是名字投影而非複製宣告；opaque export 在邊界後成為中性常數",
      "模組循環與重複路徑拒絕，參數引數與每條映射宣告以 d_check 驗證，only/hiding/rename 的歧義名字拒絕，閉合實例逐條 dep_check",
    ),
    entry(
      "定理登記表與範例",
      SpecTheorem,
      [
        "CheckResult", "run_all_checks", "all_checks_pass", "print_report", "example_projector",
        "sample_terms", "check_projector", "check_eigenspace", "check_cube_comp",
        "check_nbe", "check_eta_all", "check_bdd_canonical", "check_glue_comp_all",
        "check_categories_all",
      ],
      "條目 (名稱, Bool)；全表 PASS 為總驗收範式",
      "每一條目是一條可判定命題在具體見證上的實現",
      "moon test 與 moon run cmd/main",
    ),
    entry(
      "規格登記自身",
      SpecStructure,
      [
        "SpecKind", "SpecEntry", "spec_registry", "spec_registry_sound", "spec_covers",
        "spec_count",
      ],
      "條目本身即 (名稱, 類別, 符號, 範形, 範疇, 判定) 六元組",
      "登記是「規格的規格」；完備性由 SPEC.md 附錄以產生介面核對",
      "tools/audit_spec.py 逐符號審計",
    ),
  ]
}

///|
fn spec_symbol_count(reg : Array[SpecEntry], sym : String) -> Int32 {
  let mut count = 0
  for i in 0..<reg.length() {
    for k in 0..<reg[i].symbols.length() {
      if reg[i].symbols[k] == sym {
        count = count + 1
      }
    }
  }
  count
}

///|
/// The registry is sound: every entry fully specified, names unique, and
/// no symbol claimed by two entries.
pub fn spec_registry_sound() -> Bool {
  let reg = spec_registry()
  for i in 0..<reg.length() {
    let e = reg[i]
    if e.name == "" ||
      e.canonical == "" ||
      e.categorical == "" ||
      e.decision == "" ||
      e.symbols.length() == 0 {
      return false
    }
    for j in 0..<reg.length() {
      if i != j && reg[j].name == e.name {
        return false
      }
    }
    for k in 0..<e.symbols.length() {
      if spec_symbol_count(reg, e.symbols[k]) != 1 {
        return false
      }
    }
  }
  true
}

///|
pub fn spec_covers(sym : String) -> Bool {
  spec_symbol_count(spec_registry(), sym) >= 1
}

///|
pub fn spec_count() -> Int32 {
  spec_registry().length()
}
