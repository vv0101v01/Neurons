# 流水簿 / Worklog

> 每回合（turn）續記：環境、聯網研讀、完成事項、待辦去向。待辦清單的正典在
> `SPEC.md` §四（編號 1–10 穩定，「第 N 條」以該編號為準）；本簿只記流水。
>
> Every round is appended below. The canonical todo list is SPEC.md §4
> (items 1–10, stable numbering); this file is the running ledger only.

---

## 2026-10-21 — 回合 1（Round 1）

### 環境與版本 / Environment

| 項目 | 版本 |
|---|---|
| 專案 | <https://github.com/vv0101v01/Neurons>（已 clone 至工作區） |
| moon | `0.1.20261020 (2284bd2 2026-10-20)` — 最新穩定版（install/unix.sh） |
| moonc | `v0.10.16+b1a0e846e (2026-10-16)` — 最新穩定版 |
| feature flags | `rr_moon_mod, rr_moon_pkg`（`moon.pkg` 新 DSL） |

### 聯網研讀 / Online study

**MoonBit 最新語法（至 v0.10.16）**：

- v0.10.14（2026-09-21）：`T::_` suberror 型別匹配、`for ... in` 支援模式解構、
  enum `#non_exhaustive`＋`TypeName::..`、`a[i:j]` 改為安全 clamped view
  （舊語義改名 `exact_view`）、pipeline 右側 lambda 可呼叫 async、
  未用 import 警告、JS FFI 邊界棄用 `Array`（改 `FixedArray`）、
  隱式 `impl`→method 提升警告默認開啟（改用 `extend Type with Trait::{...}`）。
- 本專案採用的穩健寫法已按上述語法核對（`derive(Debug, Eq)`＋
  `pub extend X with @moonbitlang/core/debug.Debug::{to_repr}` 重導出、
  `let mut`＋while、Int64 字面量 `L` 後綴、`Option` 部分轉換）。
- v0.10.x 為 1.0 前關鍵系列（原目標 2026 Q3，仍在收尾）；1.0 前
  pre-1.0 版本相容解析、`moon.pkg` DSL、`moon search/view/deprecate` 工具已可用。

**單值性定理與立方體（cubical）演算法論文**：

- Cohen, Coquand, Huber, Mörtberg — *Cubical Type Theory: a constructive
  interpretation of the univalence axiom*（TYPES 2015 / arXiv:1611.02108）：
  立方體集合模型、直接操縱 n 維立方體、`Glue`/`unglue` 與 univalence 的
  可計算內容（本專案 `glue_comp.mbt`、`ua` 計算律的理論出處）。
- Coquand, Huber, Mörtberg — *The Univalence Axiom in Cubical Sets*（2018）：
  Bezem–Coquand–Huber 模型中 univalence 的構造性證明。
- Angiuli, Brunerie, Coquand, Harper, Hou (Favonia), Licata — *Syntax and
  Models of Cartesian Cubical Type Theory*（MSCS 2019）：笛卡兒立方體範疇
  （faces/degeneracies/symmetries/diagonals、無 connections），Π/Σ/path/identity/
  Glue 的語法與模型（對應本專案無 connection 的面格設定）。
- Cavallo, Mörtberg — *Unifying Cubical Models of Univalent Type Theory*
  （CSL 2020）：統一的立方模型，不依賴對角 cofibration/connections。
- Coquand, Huber, Sattler, Vezzosi 等 — Cubical Agda（arXiv 系列）：
  `ua`/`uaβ` 的可計算單值性、HIT 的定義性計算規則（對應 §1.11 與 schema/HIT 層）。
- 立方體算法（face lattice 上的容斥/Möbius 和、Kan 填充）在本專案的實作
  見 `cube_algorithm.mbt`（`nfill`/`ncomp`）；本回合不改動該模組。

### 本回合完成 / Done this round

**SPEC §四 第 9 條「可計算單值性」✅**（詳見 SPEC §1.11(a) 與 §四第 9 條）：

1. 新增 `bignat.mbt`：精確自然數 `BigNat`（base-10⁹ limbs，規範形），
   `add/mul/pow/fact/cmp/to_string/divmod_small` 全精確；到 `Int64`/`Int32`
   的**部分轉換**溢出時回 `None`，絕不回繞。含白箱測試（13!、16!、20!、
   25!、100!、2^64、溢出邊界）。
2. `univalence_compute.mbt` 計數公式全部改 `BigNat`：
   `fin_map_count = |B|^|A|`、`fact = n!`、`fin_equiv_count`、
   `univalence_path_count`。**溢位根除**：舊 `Int32` 在 13! 起回繞、
   16 元素 `16^16 ≡ 0 (mod 2^32)` 令 `fin_map_count` 歸零、判定變空洞；
   現 `fact(16) = 20922789888000`、`16^16 = 18446744073709551616` 精確。
3. `fin_equiv_search` 改**單射前綴剪枝搜尋**（n! 雙射搜索樹，非 `|B|^|A|`
   表掃描；字典序與舊編碼升序一致，回傳同一首表），任何大小即時判定
   「A ≃ B」；`fin_map_of_code_big` 提供精確編碼解碼（`fin_map_of_code`
   保留機器整數版供小空間）。
4. `fin_equiv_count` 在 n ≤ 18 由同一搜索樹的**記憶化枚舉**（used 位罩 DP）
   算出，與閉式 n! 交叉驗證；`univalence_decides` 在 16 元素型上真確運算
   （存在性剪枝搜尋、個數 DP 決定、比較閉式 n!）。
5. `ua_section_all`/`ua_retraction_all` 改**預算窮舉＋三值 `LawVerdict`**
   （`LawHolds`/`LawFails(反例表)`/`LawUndecided`）：小空間逐表窮舉
   （連非等價表一併檢查——對舊行為的嚴格加強），退一級逐等價窮舉
   （表預算 65,536；節點預算 150,000，恰覆蓋 8 元素搜索樹 109,601 節點）；
   超預算誠實回報 `LawUndecided`，絕不抽樣（與 BDD 節點預算同一慣例）。
6. 測試 55 → **65** 全綠（新增 16 元素穩健性、字典序回歸、溢位邊界、
   `LawFails` 反例路徑、BigNat 算術）；`moon run cmd/main` 43/43；
   `moon info && moon fmt` 已跑，`pkg.generated.mbti` +29 符號（2339 → 2368）；
   `tools/audit_spec.py` 新增規格族「精確自然數計數」，`--check` 通過。

**文件同步**：SPEC §1.11(a)（中英）、SPEC §四改**編號待辦清單**（1–10，
含本條完成紀錄與剩餘待辦）、GUIDE 第八期、README（徽章與計數）、
`spec.mbt` 登記條目（新增 `BigNat`/`LawVerdict`/`fin_map_of_code_big`
與新決策文）。

### 進行中 / In progress

**SPEC §四 第 1 條（Schema 片斷 / scheme）🔄** —— 本回合開始。細項待辦
（詳見 §四第 1 條）：(a) AST 一等宇宙多態宣告/抽象語法；(b) 原始互歸納
宣告；(c) 正性涵蓋更廣的間接用法；(d) 非均勻巢狀型別（Bush）；
(e) 不透明中性型別算子應用策略；(f) HIT 移動維度 comp 更廣化簡；
(g) 歸納—遞迴超出 Tarski `DDecode`。

### 待辦去向 / Pending

- §四第 1 條細項 (a)–(g)：下回合繼續（讀 `schema.mbt`/`schema_functor.mbt`/
  `schema_positivity.mbt`/`schema_extensions.mbt` 後逐細項實作＋測試）。
- §四第 9 條剩餘：逆律 >8 元素 `LawUndecided`（組合不可行，可加符號化
  論證層）；n ≤ 18 枚舉閾值；`BigNat` 移植至第 5/7 條 `Int32` 有理層。
- 其餘 §四條目（2,3,4,5,6,7,8,10）維持 ⏳，敘述與待辦已記入 §四。

---

---

## 第一期（續）· 第 2 段：§四第 1 條 schema（2026-10-21）

**範圍**：把 §四第 1 條 schema 完成至可完成的邊界。本段落地 (a)(b) 兩個子項，
(c)(e) 完成設計定案，(d)(f)(g) 記為 remaining。

**程式面（新增/擴充）**：

- `dterm_transform.mbt` 尾段新增 level 位置映射層：`dterm_map_levels`
  （覆蓋全部 payload 形狀，含嵌入 spec 的遞迴）、`dfunctor/arg/constraint/
  ctor/telescope/inductive_spec/hit_spec_map_levels`——把 body 裡的 level
  位置換進換出，是範本編碼的基礎。
- `schema_extensions.mbt` 尾段新增 **宇宙多態宣告**：
  `dlevel_var(i) = -1-i` 以 body 位置編碼 level 池入；`dlevel_unwrap`、
  `dlevel_expr_wf`、`dlevel_identity_pool`、`dlevel_pool_eval`；
  `DUnivPolyDecl`/`DUnivPolyHitDecl`（名稱 + level-arity + `DLevelExpr` 池 +
  結果 level + 脫離參數鏈的 template，derive(Eq,Debug) 可比較資料）；
  `duniv_poly_validate`（名稱/層級引用良構）、`duniv_poly_instantiate`
  （`dlevel_pool_eval`+`dlevel_eval` 算全 level 後經既有 schema 驗證）；
  一致律 `duniv_poly_agrees_with_scheme`（HIT 版同）；
  樣板 `list_univ_poly_decl`/`circle_univ_poly_decl`。
- `schema_extensions.mbt` 尾段新增 **原始互宣告** `DMutualDecl` +
  `dmutual_decl`/`dmutual_decl_validate`（`compile_mutual_inductive` 的
  格式前提提煉為宣告時驗證）/`dmutual_decl_compile`/
  `dmutual_decl_matches_family`（編譯與宣告同義後證）。
- 測試 `univ_poly_wbtest.mbt`（8 例）：pool 編碼、ListU/CircleU 與宿主
  level-scheme 全 level 一致、Eq 可判定、錯 arity/負 level/越界引用/名稱
  不符之拒絕、複合 level（部分多態 `BoundedU` 在 max(1,ℓ) 下實例化）、
  EvenOdd/TreeForest 互宣告編譯與 family 同義、Ill-formed 塊拒絕。

**設計決策**：
- **Pool 設計**取代單純哨兵：body 位置編碼 `-1-i` 指向宣告的 level 池，
  複合 level 表式（max/succ）可出現在宣告資料裡；結果 level 維持一般
  `DLevelExpr` 每次實例化時檢查。
- **變異性證書**（(c)+(e) 待實作設計已定）：`DVariance`（嚴格正/正/負）以
  顯式 registry 登記中性算子各參數位；正性判定對持證應用按證書判定，
  取代保守 unknown 拒絕；證書為顯式信任邊界，驗證快取鍵需含證書。
- (d) Bush 統一 `NestedTree`、(f) HIT 移動維度 comp 更廣化簡、(g) IR 超出
  Tarski `DDecode`：標明 remaining（(d) 需函子語義一般化、(f) 化簡點在
  schema.mbt hit comp 分派、(g) 設計研究）。

**狀態**：`moon test` 73/73（65+8 新例）全綠、`moon check` 乾淨；
審計 2413 顆粒（fn 1540/let 2/struct 141/field 458/enum 28/constructor 237/
type 7）`--check` 綠；spec.mbt「Schema 擴展」項更新（新增
DUnivPolyDecl/DUnivPolyHitDecl/DMutualDecl 等名）。SPEC §1.9.1 與
§四第 1 條已改寫為「現況＋剩餘待辦」。

---

## 第一期（續）· 第 3 段：§四第 1 條 (c)+(e) 證書 registry + 第 9 條再強化 + 找錯去重減債清死碼（2026-10-21）

**範圍**：按使用者指示——接納 (c)+(e) 設計並實作；第 9 條持續是重點攻堅
對象，持續改善優化其內容；完成後進行找錯、去重、減債、清死碼。

**(c)+(e) 變異性證書 registry（§四第 1 條完成到此）**：

- `schema_positivity.mbt` 新增 `DVariance`（`VarianceStrict`/
  `VariancePositive`/`VarianceNegative`）、`DPositivityCert`（算子名 +
  逐位變異性）、`DPositivityCerts`（登記表：空／加入或覆寫／按名查詢，
  `dpositivity_cert_strict`/`_positive`/`_negative` 單位證書捷徑）。
- 正性走訪全面升級處理**應用脊**（`app_spine` 拆 `DApp` 鏈為根+引數）：
  多引數透明別名（`DLam` 根）一次性歸約到底，不再逐引數假設單一 beta；
  `DInductive`/`DHitType`/`DDecode` 當作算子頭時遞迴頭部另走引數；
  `DTVar(k)` 根據 de Bruijn 索引解回脈絡名稱（`names`/`depth` 貫穿整個
  走訪），若在 registry 內有證書則逐位依變異性判定（嚴格位保持強度，
  正/負位轉非嚴格並視需要翻轉極性），否則回報保守 `unknown`。
  `dterm_family_positivity_with(t, name, names, certs)` 是新頂層入口，
  `dterm_family_positivity`（名稱不變、行為不變）委派給它（`names=[]`、
  `certs=空`），向後相容。
- `schema.mbt`：`schema_arg_type_for_validation`/`schema_validate_args`/
  `inductive_schema_validate_uncached`/`hit_schema_validate_uncached`
  新增 `certs` 參數，外部引數與函數定義域在證書非空時改走證書判定
  （`schema_positivity_accepts`：僅全嚴格正、無 unknown、無負極性視為
  接受）；既有無證書呼叫點傳空表，行為不變。
- `schema_registry.mbt`：`DSchemaRegistry` 新增 `cert_validations` 快取欄；
  `DCertValidationEntry{certs, inductive, hit, valid}` 以 `(descriptor,
  certs)` 為鍵；新入口 `inductive_schema_validate_with_certs`/
  `hit_schema_validate_with_certs`（空證書精確委派既有保守入口）。
- 測試 `positivity_certs_wbtest.mbt`（7 例）：算子式參數使用證成嚴格正、
  持證中性算子三種變異性判定、多引數/binder 深度/arity 溢位/未登記算子
  邊界、registry add/replace/lookup、持證驗證接受 vs 保守拒絕、快取鍵
  不互相污染、函數定義域仍禁出現、HIT 版本同。

**第 9 條再強化（持續優化）**：

- 新增路徑群胚定律：`cpath_comp_left_unit`/`_right_unit`（單位元）、
  `cpath_sym_involutive`（對合）、`cpath_sym_refl`（`¬refl=refl`）、
  `cpath_sym_comp`（反同態 `¬(p∙q)=¬q∘¬p`）、`cpath_comp_assoc`（結合律）、
  `transport_comp_computes`（複合輸運計算 `coe(p∙q)=coe q∘coe p` 雙向）、
  `transport_refl_identity`；全部併入 `univalence_compute_all` 電池與新
  whitebox 測試（含端點不合時的拒絕核對）。
- 優化：`bijection_count_enum`/`bijection_recurse` 改為預計算位元遮罩
  陣列 + 自由位走訪（`free = full - used` 逐位剝離），免每次呼叫
  `int_pow` 重算冪次，狀態成本降為剩餘自由位數；新增 `fin_map_inv_at`
  抽出單點逆元語義（與 `fin_map_inv` 共用、去重複代碼），`cpath_coe_index`
  改呼叫它，免每次 `coe 1→0` 配置整張逆表。全套測試由約 35 秒降到約
  28 秒（含新測試）。

**找錯、去重、減債、清死碼**：

- `fin_map_inv` 重構為呼叫新抽出的 `fin_map_inv_at`，消除與
  `cpath_coe_index` 原逆表邏輯的重複實作。
- 死碼掃描（私有 `fn` 定義 vs 全庫引用次數）：343 個套件私有函式中僅 2
  個命中率低（`fam_if_true`、`unit_a_example`），核實後兩者皆為函式值
  （作為高階參數傳遞），非死碼，不動。
- 公開 API 掃描：1350 個 `pub fn` 中 17 個低引用；13 個是既有、仍受
  REFACTORING.md 介面雙射保護的公開面（跨模組穩定介面，非本回合改動
  範圍，不動）；其餘 4 個是本回合新增的證書捷徑與 `duniv_poly_hit_decl_
  with_levels`——已接上 `positivity_certs_wbtest.mbt`／`univ_poly_wbtest.mbt`
  測試驗證，不再是死碼。
- 審計重跑：`moon check` 0 警告（修正前曾有「VarianceNegative 未建構」等
  3 個 `unused_constructor`/`reserved_keyword` 警告，已消除）。

**審計與文件**：`tools/audit_spec.py` 新增 `DVariance`/`DPositivityCert`/
`DPositivityCerts`/`DCertValidationEntry` → 「Schema 擴展：互歸納、商與
宇宙多態」族；`dpositivity_cert`/`dpositivity_certs`/
`dterm_family_positivity`/`inductive_schema_validate`/`hit_schema_validate`
前綴映射；`--write`+`--check` 綠於 2455 符號。spec.mbt 兩處登記項更新
（Schema 擴展 + 可計算單值性）。SPEC.md：§四第 1 條狀態改為 (a)(b)(c)(e)
✅／(d)(f)(g) 待辦；§四第 9 條追加本輪強化記錄；§1.9.1 新增證書設計段落
（CN+EN）；round banner 更新。README.mbt.md 徽章與內文數字同步
（80/80 測試、2455 符號）。

**最終驗證**：`moon check` 乾淨（0 警告 0 錯誤）；`moon test` 80/80；
`moon run cmd/main` 43/43；`python3 tools/audit_spec.py --check` 綠於
2455 符號（53 條規格登記、55 個規格族，數目不變——僅新增符號分類）。

**§四第 1 條現況**：(a)(b)(c)(e) ✅ 完成；(d) Bush 非均勻巢狀、(f) HIT
移動維度 comp 更廣化簡、(g) IR 超出 Tarski `DDecode` 仍列 remaining。
第 9 條持續是攻堅對象：本輪完成路徑群胚定律與兩項效能優化；剩餘待辦
（>8 元素全稱逆律預算、n≤18 枚舉門檻、宇宙僅 Bool/Unit 積、items 5/7
的 BigNat 移植）維持在 §四第 9 條記錄，未變動。

---

## 2026-10-22 — 回合 2（Round 2）

### 任務 / Task

指示：「第9條a,b,c,d，聯網搜尋第3條的相關論文後，開始進行相關開發」——完成第 9
條四子項 (a)(b)(c)(d)，並聯網研讀後開發第 3 條（AST `Equiv` 高階相干：adjoint
equivalence／半伴隨等價、命題截斷、單價公理一等陳述）。

### 聯網研讀 / Research

- HoTT book（people.csail.mit.edu/jgross/tmp/hott-book-html）Def 4.2.1
  `ishae(f)`（g、η、ε、三角律 τ）；Def 4.3.1 `biinv(f)`（現有 AST `Equiv`
  正是此型）；Thm：`isContr(fiber f) ≃ ishae(f) ≃ biinv(f)`。
- Coq HoTT 庫論文（dl.acm.org/10.1145/3018610.3018615、
  arxiv.org/html/1610.04591v2）：確認三角律是「adjoint equivalence 兩條
  三角律之一，另一條可證但不可假設為資料」。
- Cubical Type Theory 論文（cse.chalmers.se cubicaltt、Agda cubical 文件、
  cubical-methods）：`fiber`／`isEquiv`／`Equiv` 的 cubical 形式化，
  `univalence : (A B:U) → Equiv (Path U A B) (Equiv A B)` 的一等陳述形式。
- Agda cubical 命題截斷 HIT：`∥A∥` 兩建構子 `∣_∣`／`squash`；squash
  兩端點皆為繫於自身型別的自由變數，而非既有 cell 的實例化——與現有
  `DHitFaceExpr{cell,args,dims}` schema 表達力的落差確認。

### 第 9 條開發 / Item 9 development

**(a) 符號化恆等層去 `LawUndecided` 天花板**：推導
`cpath_coe_index(p,0,1,i)=p.e.table[i]` 對任意 `e`／`p` 恆成立（不論雙射與
否），故 `cpath_to_equiv(cpath_ua(e))` 的表literally就是`e.table`，是 O(n)
事實。新增 `fin_map_round_trip_identity`／`cpath_round_trip_identity`（O(n)
計算核）、`fin_map_witnesses`（私有，建構 2–3 張結構各異見證表）、
`ua_section_proved`／`ua_retraction_proved`（任意大小即時判 `LawHolds`，
無預算天花板）於 `univalence_compute.mbt`。`univalence_compute_wbtest.mbt`
新增 13 項測試：與既有窮舉版本在可窮舉範圍內逐一交叉核對一致，並在 16、
256 元素型（舊版皆 `LawUndecided`）即時判 `LawHolds`。

**(b) 枚舉上界 18→20**：推導 `20! = 2432902008176640000` 為最大仍落在
`Int64` 內的階乘（`21!` 溢位），`fin_equiv_enum_max()` 由 18 改 20；新增
`fin_ty(n)`（遞迴 `TySum` 建構任意 n 元素型）測試 n=19/20/21 邊界與閉式
交叉驗證，n=20 全套測試仍在約 6 秒內完成。

**(c) 有限宇宙擴充 `TySum`**：延續先前步驟加入 `Ty::TySum`/
`PVal::PVLeft`/`PVRight`（`elems_of`/`in_ty` 隨附支援，`wiring.mbt`/
`kan_dep.mbt` 對其刻意 `abort` 樁）後，本回合新增 `fin_sum_swap(a,b)`
（通用 `A+B ≃ B+A` 見證）並編入 `univalence_compute_all`，新檔
`finite_universe_sum_wbtest.mbt`（4 測試）。過程中發現並修正 `cpath_coe`
（元素級、非索引級搬運）反向方向恆在錯誤陣列中搜尋的潛伏錯誤——因舊有
呼叫端皆 `src==dst` 同形而意外answer正確，新測試首次以真正不同形狀型別
（`TySum(Bool,Unit)` vs `TySum(Unit,Bool)`）曝露。

**(d) `BigInt`／`BigRat` 精確整數與有理數層**：`bignat.mbt` 新增
`bignat_sub`（減法）、`bignat_divmod`（一般長除法，逐限位元二分搜商數）、
`bignat_gcd`（輾轉相除）；新檔 `bigint.mbt`（符號-量值 `BigInt`：加減乘除、
比較、gcd、字串化、部分轉 `Int64`）與 `bigrat.mbt`（`BigRat`：恆約分、
分母恆正，含 `bigrat_of_rat`／`rat_of_bigrat` 與既有 `Int32`-界 `Rat`
（symalg.mbt）雙向橋接）。以 46337⁴（= 4610113855108469761，超出
`Int32`）示範 `Rat` 鏈式乘法會靜默溢位而 `BigRat` 保持精確。18 項新白盒
測試（`bignat_wbtest.mbt` +3、`bigint_wbtest.mbt` 4、`bigrat_wbtest.mbt`
4，另 7 項併入既有測試檔）。尚未把 `qpoly.mbt`/`qmat.mbt`/
`Jacobi_interval.mbt` 遷移接上 `BigRat`（工具已備，遷移留待後續回合）。

### 第 3 條開發 / Item 3 development

新檔 `ishae.mbt`：`fin_fiber`／`fin_is_contr_fiber`／
`fin_is_equiv_via_contr`（`isEquiv(f):=Πy.isContr(fiber f y)`，以計表格
命中數判定）；`Ishae` 結構（f, g）＋`ishae_eta_holds`／`ishae_eps_holds`／
`ishae_triangle_holds`／`ishae_triangle_is_free`（證明並檢驗此嚴格相等
模型中三角律是 ε 在 `f(x)` 處的特例，非獨立資料——呼應 Coq HoTT 庫論文的
注記）／`ishae_holds`；`biinv_to_ishae(f,l,r)`（把 biinv 分離的左右逆併為
單一 ishae，`g:=l` 並以代換鏈推導 `f∘g~id`，而非假設，HoTT book
Thm 4.3.2 的具體化）；`fin_equiv_three_ways_agree`（雙射＝可縮纖維＝存在
ishae 三者窮舉一致定理，HoTT book Thm 4.2.3 的具體化）。過程中發現
`fin_map_is_equiv` 只驗單射（其文件已載明僅在來源/目標基數相等時等於
雙射，現有呼叫端皆已守衛此前提）——`fin_equiv_three_ways_agree` 對任意
`FinMap`（含跨基數）額外併入基數相等檢查以成立普適定理；新檔
`ishae_wbtest.mbt`（5 測試）含明確示範此一範圍邊界的對照測試
（`fin_map_is_equiv` 原始行為 vs 修正後 `fin_equiv_three_ways_agree`）。

命題截斷（squash HIT）與單價公理一等陳述（封裝 `cpath_ua`/
`cpath_to_equiv`/`ua_section_proved`/`ua_retraction_proved` 為單一具名
`Equiv(Path,Equiv)` 物件）兩項確認範圍但本回合不展開——前者需 schema 層
新增 `DHitFaceVar` 變體（影響面大），後者純屬封裝（內容已由現有函式覆蓋）。

### 文件同步 / Documentation sync

SPEC.md §四第 9 條（CN+EN）改寫為「(a)(b)(c)(d) 四子項全部完成」並附各
子項技術細節；第 3 條（CN+EN）改寫為「🔄 非截斷部分完成」並詳列
`ishae.mbt` 內容與命題截斷/單價公理封裝的精確待辦；round banner 兩版
追加本輪摘要。`tools/audit_spec.py`：新增 `BigInt`/`BigRat`/`Ishae` 的
`TYPE_FAMILY` 項與 `bigint_`/`bigrat_`/`ishae_`/`biinv_to_ishae` 前綴
分類，擴充「精確自然數計數」族描述涵蓋 BigInt/BigRat、擴充「可計算單值性
與 n 維立方演算法」族描述涵蓋 ishae/fiber/符號化恆等層；`--write`+
`--check` 綠於 2526 符號（原 2455）。spec.mbt：新增「半伴隨等價與可縮
纖維」「精確整數與有理數」兩條規格登記（53→55），擴充既有「可計算單值性
與 n 維立方演算法」「Finite universe 型別與值」登記項。README.mbt.md：
徽章與內文數字同步（102/102 測試、2526 符號、55 條規格登記），新增
「第九期新增」段落（CN+EN）。

### 最終驗證 / Final verification

`moon check`：0 錯誤、0 警告。`moon test`：**102/102 通過**（原 84，新增
18：bignat +3、bigint +4、bigrat +4、ishae +5、univalence_compute_wbtest
+1 大項（13 斷言）、finite_universe_sum 已於先前步驟完成不重複計入）。
`moon run cmd/main`：**passed 43/43**，兩條 PASS 行皆在。
`python3 tools/audit_spec.py --check`：綠於 2526 符號（55 條規格登記、
55 個規格族）。

### 找錯、去重、減債、清死碼 / Bug-finding and debt pass

本輪開發過程中已發現並修正兩個真實缺陷（記錄於上）：

1. `cpath_coe`（元素級搬運）反向方向恆在來源陣列（而非目的陣列）中搜尋
   的潛伏錯誤——已修正為依方向分流搜尋。
2. `fin_map_is_equiv` 只驗單射、在跨基數輸入下與真雙射判定不一致的範圍
   邊界——`fin_equiv_three_ways_agree` 已加入顯式基數檢查使三者一致定理
   普適成立；`fin_map_is_equiv` 本身保留不動（其文件已載明前提，現有
   呼叫端皆已守衛，改動它的風險/效益不成比例）。

兩者皆已在對應白盒測試中以專門斷言固定（防止回歸）。未發現其他待修的
死碼或重複實作；`bigint_raw_pub`（bigrat.mbt）是刻意重建 `bigint.mbt`
私有 `bigint_raw` 正規化邏輯的公開輔助函式，非重複——因 MoonBit 模組內
私有函式不可跨檔案呼叫，兩份邏輯皆為同一行數的簡單正規化，維護成本低。

## 2026-10-22 — 回合 3（Round 3）

### 任務 / Task

指示順序：「先把第9條待辨BigRat接上已整備好的函式」→「然後把第9條的a, c
兩項完成」→「繼而處理第1條（應為第3條之誤）的命題截斷事項」。本段記錄
第 9 條 (a)(c) 兩項的完成工作（BigRat 接線與第 3 條命題截斷留待後續段落）。

### 環境 / Environment

`~/.moon` 本回合再度遺失（累犯），以
`curl -fsSL https://cli.moonbitlang.com/install/unix.sh | bash` 重裝，
確認 `moon check`/`moon test`/`moon run cmd/main` 恢復綠燈（102/102、
43/43、0 警告）後才開始新工作。

### 第 9(c) 條範圍確認 / Scope disambiguation for item 9(c)

透過 `ask_user` 向使用者提出三選項（僅 wiring.mbt／wiring.mbt+kan_dep.mbt／
已完成無需再動），**使用者選擇「僅 wiring.mbt」**，明確排除 kan_dep.mbt 的
深層 Kan/coe/comp 語義工作（風險/範圍判斷過大，正確延後）。

### 第 9(a) 條：公開判定 API 根除 `LawUndecided` 出口

此前 `ua_section_proved`/`ua_retraction_proved` 已能任意大小即時判定，但
公開三值 API `ua_section_all`/`ua_retraction_all` 本身超過窮舉預算（約 8
元素起）仍可能回 `LawUndecided`。新增 `fn exhaustion_search_feasible(n)`
（遞增 `Int64` 乘法早退檢查 `n! <= law_enum_budget()`，比真正枚舉廉價
許多）：`ua_section_all`/`ua_retraction_all` 若 `n` 不可行則直接委派
`ua_section_proved`/`ua_retraction_proved`；若可行但窮舉中途耗盡預算，
亦改為委派 `_proved` 版本而非回 `LawUndecided`。

**效能陷阱與修正**：初版只加「耗盡後委派」而未加可行性捷徑，令
`univalence_compute_wbtest.mbt` 從約 3–5 秒暴漲到 39.7 秒（大 `n` 仍須先
燒光約 215536 節點的完整搜索預算才回退）；加回 `exhaustion_search_feasible`
捷徑後恢復到 3.4 秒（整套測試約 18 秒，反而比舊版略快）。

`univalence_compute_wbtest.mbt` 修正兩處舊斷言：「16 元素誠實回報未決定」
示範改為直接呼叫 `exhaust_tables`/`exhaust_equiv`（繞過公開 API）以保留
「原始窮舉確實不可行」的示範本意；另一處「(9a)」交叉驗證區塊的
`ua_section_all(b16,b16)==LawUndecided` 舊斷言改為 `LawHolds`，並新增
`b256` 規模的對應斷言。

### 第 9(c) 條：`SumWiring` 落地 `TySum` 等價

新檔 `sum_wiring.mbt`：`SumWiring` 列舉（`SWLeaf`/`SWSum`/`SWSwap`/
`SWComp`，無 `SWInv`——`sumwiring_inv` 把反向下推到葉與 `SWSwap`，從不
產生需展開的不透明包裝）與平行 API `sumwiring_src/dst/id/sum/swap/
comp/inv/wf/eq/apply`。範圍限制（記於模組註解）：`TySum` 可遞迴疊在
`TySum` 內（`SWSum`/`SWSwap` 遞迴），各分支可為任意 `Wiring` 支援型別，
但 `TySum` 疊在 `TyProd` 內（如 `TyProd(TySum(Bool,Unit),Bool)`）不受
支援——`Wiring` 的葉展平無法跨越 sum 邊界。

撰寫過程中的兩個失誤與修正：(1) `derive(Debug)` 因 `Wiring` 本身無
Debug 實作而編譯失敗（Error 4018）——移除該 derive 子句及對應
`extend ... Debug` 區塊；(2) `SWSwap` 分支內一行手誤殘留的亂碼程式碼
（`PVLeft(x=>x, y).0 |> ignore`）——修正為 `PVRight(y) => PVLeft(y)`；
(3) 加入 `SWInv` 構造子後因從未被任何函式產生而觸發 `unused_constructor`
警告（Warning 0006）——移除該構造子（`sumwiring_inv` 一律下推而非包裝）。

**`pathp_glue.mbt` 接線**：`Iso`/`Equiv` 的 `wiring` 欄位型別由 `Wiring`
改為 `SumWiring`（`iso_of_wiring`/`equiv_of_wiring` 內部包成 `SWLeaf(w)`，
呼叫端簽名不變，零破壞性）；新增 `iso_of_sumwiring`/`equiv_of_sumwiring`、
`iso_sum`/`iso_sum_swap`，以及本項實際交付物 `equiv_sum`/`equiv_sum_swap`；
`iso_wf`/`equiv_wf`/`equiv_ext_eq`/`equiv_comp`/`equiv_inv`/`equiv_id`/
`coe_computes`／Glue 良構檢查全數改用 `sumwiring_*`；`equiv_prod` 僅接受
兩側皆為 `SWLeaf` 的純積片段，否則 `abort`。

**第二個效能/正確性陷阱**：`sumwiring_comp`/`sumwiring_inv` 初版一律回
字面 `SWComp(w1,w2)` 包裝，未正規化。這令 `equiv_comp`/`equiv_inv` 的
範式不再與舊 `wiring_comp`/`wiring_inv` 一致（舊版永遠產生扁平
`Wiring`），造成依賴「組合後仍是扁平範式」做結構相等判斷的 5 個既有
測試（`upgrade_wbtest.mbt`、`theorems_wbtest.mbt`×2、`symbolic_wbtest.mbt`、
`dep_wbtest.mbt`）迴歸失敗。修正：`sumwiring_comp` 對 `(SWLeaf,SWLeaf)`
正規化回 `SWLeaf(wiring_comp(...))`（與舊版完全同形），對兩個
tag-preserving `SWSum` 遞迴化簡為逐分支組合，對「換位之後接回對應反
換位」化簡為分支恆等；其餘情形才退回字面 `SWComp`。`sumwiring_inv` 的
`SWComp` 分支亦改走 `sumwiring_comp`（而非裸 `SWComp`）以繼承此正規化。
修正後全部 5 個迴歸測試復原，且不影響新能力的語意正確性。

另修正 `equiv_id`：此函式先前仍呼叫舊 `wiring_id`（對 `TySum` 會
`abort`），改為 `equiv_of_sumwiring(sumwiring_id(ty))`，使
`equiv_id(TySum(...))` 不再無謂崩潰（由 `sum_wiring_wbtest.mbt` 的
`equiv_sum_swap` 兩次互逆測試揭露並修正）。

新檔 `sum_wiring_wbtest.mbt`（6 測試）：`sumwiring_wf` 對照
`elems_of`/`in_ty` 枚舉 oracle；`sumwiring_apply`/`sumwiring_inv` 往返；
`equiv_sum`/`equiv_sum_swap` 良構與外延正確性；與獨立
`univalence_compute.mbt` 的 `fin_sum_swap`（`FinMap` 層見證）逐元素
交叉核對；`equiv_prod` 的範圍限制以結構斷言而非實際觸發 `abort`
的方式記錄（呼叫 `abort` 路徑會使測試本身崩潰，故僅斷言雙方
wiring 的建構子形狀）。

### 最終驗證 / Final verification

`moon check`：0 錯誤、0 警告。`moon test`：**108/108 通過**（原 102，
新增 6：`sum_wiring_wbtest.mbt`）。`moon run cmd/main`：**passed 43/43**。
`moon info` + `python3 tools/audit_spec.py --write`／`--check`：綠於
**2547 個介面符號**（原 2526；新增 `SumWiring` 型別 + 4 構造子 + 10 個
`sumwiring_*` 函式 + `equiv_of_sumwiring`/`iso_of_sumwiring`/`iso_sum`/
`iso_sum_swap`/`equiv_sum`/`equiv_sum_swap`，`TYPE_FAMILY["SumWiring"]`
與 `sumwiring_` 前綴皆歸入既有「Wiring 符號等價」族，無需新規格族）。

### 文件同步 / Documentation sync

SPEC.md §四第 9 條（CN+EN）新增「第四回合（同日續）」段落詳述 (a) 再
強化與 (c) 落地接線的技術細節與陷阱記錄；round banner 兩版追加本輪
摘要行。`tools/audit_spec.py`：新增 `TYPE_FAMILY["SumWiring"]` 與
`sumwiring_` 前綴分類（歸入既有「Wiring 符號等價」族）。spec.mbt：
擴充既有「Wiring 符號等價」「同構／等價／ua／coe」「可計算單值性與
n 維立方演算法」三條規格登記的符號列與判定敘述（55 條規格登記不變，
僅擴充既有條目，未新增條目）。README.mbt.md：徽章與內文數字同步
（108/108 測試、2547 符號），「第九期新增」段落（CN+EN）追加 (a)(c)
本輪強化的兩條新bullet。

### 找錯、去重、減債、清死碼 / Bug-finding and debt pass

本輪開發過程中已發現並修正三個真實缺陷（記錄於上，皆已被對應白盒測試
固定防止回歸）：

1. `sumwiring_comp`/`sumwiring_inv` 未正規化導致與舊 `wiring_comp`/
   `wiring_inv` 範式不一致，造成 5 個既有測試迴歸——已修正為在純葉
   片段正規化回扁平形式。
2. `equiv_id` 仍呼叫對 `TySum` 會 `abort` 的舊 `wiring_id`——已改用
   `sumwiring_id`。
3. 新加入後又移除的 `SWInv` 構造子（`unused_constructor` 警告）——
   確認 `sumwiring_inv` 的下推設計使其永不需要，故直接移除而非保留
   作「API 完整性」。

本輪不重複執行第 9(a)(c) 之前已完成的找錯/去重分析（`bigint_abs`/
`bigrat_eq` 等既於前回合處理並記錄）；未發現本輪新增程式碼中其他待修
死碼或重複實作。

## 2026-10-22 — 回合 3（續）：單值性接上 qpoly/qmat

### 範圍澄清 / Scope clarification

使用者最初指示「把 BigRat 接上 qpoly/qmat/Jacobi_interval」。考量到
qpoly.mbt/qmat.mbt 本身即以 `Int32`-界 `Rat` 建構，而 Jordan.mbt、
algnum.mbt、algebraic_laws.mbt、Jacobi_interval.mbt 全部疊在其上
（合計約 4100 行），把 `QPoly`/`QMat` 的底層型別從 `Rat` 換成 `BigRat`
會是一次大規模、有一定回歸風險的重寫，故先以 `ask_user` 徵詢範圍。
使用者澄清三次後確認：**真正要求是「單值性定理能否用到 qpoly、qmat」，
途徑（`Rat` 或 `BigRat`）不重要**——即不是第 5/7 條那個獨立的型別遷移
待辦，而是要求把 `univalence_compute.mbt` 的判定機制（`FinMap`、
`fin_map_is_equiv`、`cpath_ua`）實際連接到 qpoly/qmat 的具體輸出資料
上。使用者再給出具體例子：「多項式根集的置換等價」。

### 實作 / Implementation

- `univalence_compute.mbt`：把 `univalence_compute_wbtest.mbt` 原有的
  私有測試輔助函式 `fin_ty(n)`（建構 n 元素有限型別）提升為公開工具，
  並刪除測試檔內的重複定義（去重）。
- 新檔 `qpoly_univalence.mbt`：
  - `qpoly_roots_ty(p)`：把 `qpoly_rational_roots(p)` 回傳的具體有理根
    陣列讀成 `fin_ty(n)` 有限型別（無根回 `None`）。
  - `qpoly_root_permutation_equiv`/`_is_equiv`/`_ua`：把任意索引置換
    包成該有限型別上的 `FinMap`，交給既有 `fin_map_is_equiv`／
    `cpath_ua` 判定／搬運——單值性的判定程序與 `coe` 因而直接作用在
    多項式的具體根集上。
  - `qmat_eigenvalue_permutation_equiv`/`_is_equiv`/`_ua`：經
    `qmat_charpoly(a)` 把同一構造延伸到矩陣的有理譜，將 `QMat` 一併
    接上（同一套 qpoly 機制，不必另建一套）。
  - `qpoly_all_root_permutations_are_equivalences`：窮舉驗證 n! 個置換
    全部是 `fin_map_is_equiv`（非抽樣），且每個皆可取得 `cpath_ua`
    路徑。
  - `all_permutations(n)`：小型置換窮舉輔助（遞迴回溯，供小 n 使用）。
- 新檔 `qpoly_univalence_wbtest.mbt`（5 測試）：四個相異有理根的四次式
  驗證全 S4（24 個置換）皆為等價並可沿 `cpath_coe` 雙向搬運（含 forth-
  and-back 恆等）；驗證非單射置換（`[0,0,2,3]`）與錯誤長度表皆被正確
  拒絕；驗證無理根多項式 `x²+1` 正確回報「無根」而非誤判為失敗；
  `diag(1,2,3)` 的 `QMat` 經特徵多項式驗證全 S3（6 個置換）。

`qpoly.mbt`/`qmat.mbt`/`Jacobi_interval.mbt` 本身的 `Int32`-界 `Rat`
內部表示完全不變動（依使用者澄清，途徑非重點）；第 5/7 條
`Int32`→`BigRat` 型別遷移仍是獨立、未動工的待辦。

### 最終驗證 / Final verification

`moon check`：0 錯誤、0 警告。`moon test`：**113/113 通過**（原 108，
新增 5：`qpoly_univalence_wbtest.mbt`）。`moon run cmd/main`：
**passed 43/43**。`moon info` + `tools/audit_spec.py --write`／
`--check`：綠於 **2557 個介面符號**（原 2547；新增 `fin_ty`（提升公開）、
`qpoly_roots_ty`、`qpoly_root_permutation_equiv/_is_equiv/_ua`、
`qmat_eigenvalue_permutation_equiv/_is_equiv/_ua`、`all_permutations`、
`qpoly_all_root_permutations_are_equivalences` 共 10 個新符號，皆以
`tools/audit_spec.py` 的 `EXACT` 精確分類表歸入既有「可計算單值性與
n 維立方演算法」族，避免被 `qmat_eigen` 前綴誤分類進「廣義特徵空間與
Jordan 理論」族）。

### 文件同步 / Documentation sync

SPEC.md §四第 9 條（CN+EN）新增「第五回合」段落記錄範圍澄清過程與
`qpoly_univalence.mbt` 的技術細節，並更新「剩餘待辦」行以區分「單值性
接上 qpoly/qmat」（已完成）與「`Int32`→`BigRat` 型別遷移」（仍獨立待辦）
兩件事；round banner 兩版追加摘要。spec.mbt：擴充既有「可計算單值性與
n 維立方演算法」規格登記的符號列與三段判定敘述（55 條規格登記不變）。
README.mbt.md：徽章與內文數字同步（113/113 測試、2557 符號），「第九期
新增」段落（CN+EN）追加一條新 bullet。

### 找錯、去重、減債、清死碼 / Bug-finding and debt pass

本段發現並修正一處去重機會：`fin_ty` 原本只是
`univalence_compute_wbtest.mbt` 的私有測試輔助函式；`qpoly_univalence.mbt`
需要同一構造，若在新檔重新定義會造成重複實作，故改為提升 `fin_ty` 為
`univalence_compute.mbt` 的公開函式，測試檔改用該公開版本（移除重複
定義）。未發現本段新增程式碼中其他待修死碼或重複實作。

## 2026-10-22 — 回合 3（再續）：第 3 條命題截斷（squash）

### 任務 / Task

上一段落已完成第 9 條 (a)(c) 與單值性接上 qpoly/qmat；使用者接著要求處理
「第 1 條的命題截斷事項」，經 `ask_user` 澄清為 SPEC.md §四第 3 條遺留的
`∥A∥` 式命題截斷（propositional truncation）HIT 表達力缺口。

### 問題分析 / Problem analysis

既有 `DHitFaceExpr{cell,args,dims}`（schema.mbt）的面語義一律是「實例化
某個已定義 cell」；但 `squash:∀x y:∥A∥. x≡y` 的兩個端點並非另一個 cell，
而是「本次呼叫 squash 時傳入的 x、y 自身」——這類面無法用舊表達式表示。

### 實作 / Implementation

1. `DHitFaceExpr` 文件註解擴充，說明新的 sentinel 語義與舊的「實例化
   另一 cell」語義並存。
2. 新增 `hit_face_var_sentinel() -> Int32 { -1 }`（具名 sentinel，避免
   裸字面量 -1 散落各處）。
3. 新增 `dhit_face_var(arg_index, total_args) -> DHitFaceExpr`：回傳
   `{cell: hit_face_var_sentinel(), args: [DTVar(total_args-1-arg_index)],
   dims: []}`。
4. `hit_face_instantiate`：新增早退分支——`face.cell ==
   hit_face_var_sentinel()` 時直接 `deval_dim(face.args[0], term_env,
   dim_env)`，不實例化任何 cell。
5. `hit_validate_face`：重構為先計算
   `param_values`/`source_values`/`local_types`/`local_values`，再分流；
   sentinel 分支要求 `face.args.length()==1 && face.dims.length()==0`，
   並以 `DVHitType(spec, param_values, hit_result_indices(source,
   param_values, source_values))` 為期望型別對 `face.args[0]` 做
   `d_check`（過程中先寫出一版直接把 `source_values` 當作 indices 傳入
   的錯誤版本，經覆核後改用 `hit_result_indices` 正確計算）。
6. 新檔 `ptrunc.mbt`：`ptrunc_schema_unchecked(name)`、
   `ptrunc_schema(name) -> DHitSpec?`（空字串或驗證失敗回 `None`）、
   `squash_schema()`（canonical `"Squash"` 實例：params=`[A:Type0]`，
   cell 0 `"point"` 零維一個外部引數，cell 1 `"squash"` 一維兩個遞迴
   引數 `x`/`y`，面 `[dhit_face_var(0,2), dhit_face_var(1,2)]`），以及
   `squash_type_term`/`squash_type_value`/`squash_point_value`/
   `squash_path_value` 便利封裝（仿 sphere3.mbt 的命名慣例）。
7. 確認 `dhit_spec_map_levels`（dterm_transform.mbt）原樣通過 `.cell`，
   對新 sentinel 值無需修改。

### 測試與既有缺陷修正 / Tests and a pre-existing bug fix

新檔 `ptrunc_wbtest.mbt`（5 測試：schema 驗證＋空字串回 `None`、兩端點
化簡、開放維度不誤化簡、引數互換對稱、自身自反、`d_check` 型別檢查）。
第一版用 `==`/`!=` 直接比較 `DValue`，因 `DValue` 無 `Eq` 實例而 11 處
編譯失敗（Error 4018）；改用 `conv_at`/`conv_hit_cell_at` 做語義相等
判定後，又在執行期於 `conv_hit_cell_at` 內部越界崩潰——追出既有缺陷：
`dims1.length()==dims2.length()` 只在短路 `&&` 鏈中被判定，判定鏈一旦
提前短路（例如 `c1==c2` 已為 false），後面逐維 `dim_eq_sem` 迴圈仍無
條件按 `dims1.length()` 索引 `dims2`；比較兩個維度數不同的 cell（squash
的 1 維 cell 對 point 的 0 維 cell）即會越界。修正：迴圈前先行再檢查
一次長度相等，不等則直接判 `ok=false` 並跳過迴圈。此缺陷與
`dhit_face_var` 本身無關，屬既有、獨立的 bug。

### 最終驗證 / Final verification

`moon check`：0 錯誤、0 警告。`moon test`：**118/118 通過**（原 113，
新增 5：`ptrunc_wbtest.mbt`）。`moon run cmd/main`：**passed 43/43**。
`tools/audit_spec.py --write`／`--check`：綠於 **2565 個介面符號**（原
2557；新增 `hit_face_var_sentinel`、`dhit_face_var`、`ptrunc_schema_unchecked`、
`ptrunc_schema`、`squash_schema`、`squash_type_term`、`squash_type_value`、
`squash_point_value`、`squash_path_value` 共 9 個新符號；為此新增專屬
規格族「命題截斷 HIT（squash）」，族數由 55 增至 56）。

### 文件同步 / Documentation sync

SPEC.md §四第 3 條（CN+EN）：待辦段改寫為完成敘述，記錄
`dhit_face_var`/`hit_face_var_sentinel` 機制、`ptrunc.mbt` 內容與
`conv_hit_cell_at` 缺陷修正；round banner 追加本段摘要；附錄由
`tools/audit_spec.py --write` 自動產生「命題截斷 HIT（squash）」新節。
README.mbt.md：徽章與內文數字同步（118/118 測試、2565 符號、56 規格
族），「第九期新增」段落（CN+EN）移除「命題截斷仍待」字句並追加一條
squash 新 bullet。

### 找錯、去重、減債、清死碼 / Bug-finding and debt pass

本段發現並修正一處既有缺陷：`conv_hit_cell_at`（schema.mbt）比較兩個
維度數不同的 HIT cell 時，逐維 `dim_eq_sem` 迴圈未重新檢查長度相等即
索引較短陣列，造成越界崩潰；已如上修正。除此之外未發現本段新增程式碼
中其他待修死碼或重複實作；`dhit_face_var`/`hit_face_var_sentinel` 與
`ptrunc.mbt` 的各函式皆為單一定義、無重疊實作。

## 2026-10-22 — 全代碼健檢：找錯、去重、減債、清死碼

### 任務 / Task

使用者要求對全代碼庫進行健檢：找錯、找重複、減技術債、清理死代碼，
而後推送至 GitHub（vv0101v01/Neurons）。

### 方法 / Methodology

1. **死碼掃描**：解析 `pkg.generated.mbti` 取得全部 `pub fn` 符號名，於
   全部 `*.mbt` 檔案逐一計算識別字出現次數（扣除其自身定義行），找出
   「定義後從未被引用」的候選（包含測試檔）。
2. **重複掃描**：對每個 `fn`/`pub fn` 以大括號配對擷取函式本體，去除
   空白後正規化並雜湊，找出本體完全相同（＞60 字元）的函式群。
3. **既有缺陷模式複查**：針對上一回合在 `conv_hit_cell_at` 發現的
   「長度相等只在短路 `&&` 鏈中檢查，後續迴圈卻無條件索引」模式，搜尋
   全部 `let mut ok = ...` 與配對陣列迴圈，逐一核對是否有相同缺陷。
4. **TODO/FIXME/XXX/HACK** 關鍵字掃描（結果：無）。

### 發現與處置 / Findings and actions

**死碼（11 個候選，逐一核實）：**

- `equiv_make_value`、`equiv_type_term`（equiv_ast.mbt）——純一行包裝
  `DVEquiv(...)`/`DEquivTy(...)`，而這兩個構造子本身在 equiv_ast.mbt、
  nbe_dep.mbt 多處皆已被直接呼叫，包裝函式自身毫無抽象價值且確認
  零引用 → **判定為真死碼，刪除**。
- 其餘 9 個（`cert_projector_of_vector`、`checked_line_conv`、
  `checked_line_of_pathp_term`、`checked_pathp_type`、
  `darg_mutual_function`、`dsystem_checked_of`、`mutual_elim_term`、
  `qmat_rational_spectrum`、`sym_mat_of_qmat`）逐一檢視：皆為語意完整、
  與同檔案內已被測試的同族 API 對稱的函式（例如 `darg_mutual_function`
  是已測試的 `darg_mutual` 的函數值版本；`mutual_elim_term` 是已測試的
  `mutual_intro_term`/`schema_elim_term` 的互歸納消去版本）→ **判定為
  「缺測試覆蓋」而非死碼**，逐一補上行為測試而非刪除：
  - `checked_line_of_pathp_term`／`checked_line_conv`／`checked_pathp_type`：
    併入 `phase6_infrastructure_laws.mbt` 既有的 `check_checked_lines`，
    涵蓋 `DPath`/`DPathP` 兩個分支、非 Path 項拒絕、兩條線互相 conv／
    不同基底型別線不 conv、PathP 型別建構的端點與線身正確性。
  - `cert_projector_of_vector`：併入 `bdd_certified_laws.mbt` 的
    `check_certified_projector`，驗證非單位向量正規化後與
    `cert_outer` 於其單位化版本一致、冪等、Hermitian、跡為一，以及
    零向量（範數不可逆）正確回報 `None`。
  - `darg_mutual_function`：於 `schema_extension_laws.mbt` 的
    `check_mutual_inductives` 末尾新增一個最小二元互歸納族（組件 1 的
    建構子攜帶一個指向組件 0 的 `Bool → ·` 函數引數），驗證
    `compile_mutual_inductive` 接受合法版本、拒絕目標組件越界版本。
  - `dsystem_checked_of`：併入 `dsystem_compat_laws.mbt` 的
    `check_dsystem_compatibility`，驗證其在既有「相容」／「衝突」兩個
    系統上與 `dsystem_checked(line, dsystem_of(branches), base)`
    分別給出相同的 accept/reject 結果。
  - `mutual_elim_term`：於 `check_mutual_inductives` 新增 AST
    項層級版本的「深度計算」消去（人工還原 `family.combined` 的
    tag-前置索引編碼與 motive/case 繫結順序），對既有 `even2_term`
    求值，驗證與已驗證的值層級 `eval_mutual_elim` 計算結果（2）一致
    ——此測試同時是對 `mutual_elim_term` 本身與其手動還原之編碼理解的
    雙重印證。
  - `qmat_rational_spectrum`／`sym_mat_of_qmat`：併入
    `algebraic_laws.mbt` 的 `check_generalized_projectors`（矩陣
    `[[2,1,0],[0,2,0],[0,0,3]]` 特徵值 {2:重數2, 3:重數1} 全有理，
    殘餘多項式次數應為 0；對應 `SymMat` 應與逐項 `sc_rat` 轉換結果
    相等）。

**重複（函式體雜湊掃描 2 群，逐一核實）：**

- `cube_ext_eq`（categories.mbt）與 `cube_approx_eq`（cube_algorithm.mbt）
  逐字元相同（連同空白正規化）——`cube_algorithm.mbt` 顯然是在不知道
  `categories.mbt` 已有同一函式的情況下重新實作了一遍 → **刪除
  `cube_approx_eq`，其在 `cube_algorithm.mbt` 內的兩個呼叫點改用
  `cube_ext_eq`**。
- `inductive_param_types_cached`／`hit_param_types_cached`
  （schema_registry.mbt）函式體文字相同，但分屬不同結構型別
  （`DInductiveSpec.params` 與 `DHitSpec.params`），MoonBit 無結構化
  多型可供合併，且與既有 `inductive_index_types_cached`／
  `hit_index_types_cached` 的既定命名慣例一致 → **判定為型別系統所迫
  的合理重複，不合併**。

**既有缺陷模式複查：** 系統性檢查所有 `let mut ok = ...` 搭配後續陣列
迴圈的站點（kan_ast.mbt、nbe_dep.mbt、schema.mbt、equiv_ast.mbt、
univalence_compute.mbt、refactor_certificate.mbt、verify.mbt 共 20+
處），確認除上一回合已修正的 `conv_hit_cell_at` 外，其餘全部正確地在
迴圈內以 `i < other.length() &&`（或單陣列迴圈、或陣列長度由構造保證
相等）二次防呆，**未發現其他同類潛伏越界錯誤**。

### 最終驗證 / Final verification

`moon check`：0 錯誤、0 警告。`moon test`：**118/118 通過**（不變——
本輪未新增測試函式，新增的是既有 `check_*` 函式內的斷言）。
`moon run cmd/main`：**passed 43/43**（不變）。
`tools/audit_spec.py --write`／`--check`：綠於 **2562 個介面符號**
（原 2565，淨減 3：移除 `equiv_make_value`、`equiv_type_term`、
`cube_approx_eq`）。

### 文件同步 / Documentation sync

SPEC.md round banner（§四開頭）新增本段摘要。README.mbt.md：徽章與
內文符號數同步（2562）。

### 找錯、去重、減債、清死碼 / Bug-finding and debt pass（本輪即為此專項）

本輪即「找錯去重減債清死碼」專項本身：刪除 3 個真死碼／重複符號，為
9 個缺測試的合理函式補上行為測試（過程中零發現新缺陷——所有 9 個函式
行為皆與其設計意圖一致），並系統性複查過一遍上一回合缺陷模式
（`let mut ok` + 陣列迴圈）確認無其他同類問題。
