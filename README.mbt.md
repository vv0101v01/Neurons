# username/cubical-hermitian

[![CI](https://github.com/vv0101v01/Neurons/actions/workflows/ci.yml/badge.svg)](https://github.com/vv0101v01/Neurons/actions/workflows/ci.yml)
[![moon test](https://img.shields.io/badge/moon%20test-118%2F118-brightgreen)](https://github.com/vv0101v01/Neurons)
[![theorems](https://img.shields.io/badge/cmd%2Fmain-43%2F43-brightgreen)](https://github.com/vv0101v01/Neurons)
[![interface](https://img.shields.io/badge/interface-2562%20symbols-blue)](SPEC.md)

> 🔀 **切換 / Toggle**：中文在上，英文收在 <kbd>English</kbd> 摺疊區內（按一下即切換）。
> Chinese first; press the <kbd>English</kbd> summary to toggle.

Hermitian 冪等投影與特徵空間正交分解；cubical 區間、面與系統在商與剪枝下的代數；
以 retraction 作 Kan comp；三層 NbE（βπ、型別化 η 長、依賴 Π/Σ 加累積宇宙層級）；
持久共享環境、call-by-need 語義 thunk 與維度線／型別族記憶化；一個承載 PathP、
Bool/Nat/List、Circle/Torus 與 `coe/comp/hcomp/hfill` 項構造子的立方 AST（Kan 運算
按型別化簡：Π、Σ、PathP、Glue、資料、HIT 與宇宙）；`DSystem` 合成系統（原始系統的
受檢相容性、first-match 範形與多分支 Glue partial 值）；一等 AST 等價、`ua` 與
`GlueEquiv`；尊重代換的受檢型別線與帶 elaboration 快取的 schema 註冊表；通用嚴格正性
歸納族與任意有限維 HIT schema 生成器（巢狀容器函子、互歸納、Tarski 歸納—遞迴、商胞腔
與宇宙 scheme）；正規形上的 HOAS；符號判定（interned DAG ROBDD 加預算／DPLL、
wiring）；精確有理與代數擴張代數（含廣義特徵空間與 Jordan 分解）；數值投影／立方體層
的精確認證影子；一般 Glue comp；迭代懸掛生成的球面（含 S³）；以符號區間包含認證的
Hermitian Jacobi 迭代；Miller pattern 高階合一的雙向 elaborator；帶 import/open／
namespace 語義的參數化模組；以及逐符號審計的規範形式／範疇化規格。

**第八期新增**：

- **可計算單值性定理**（`univalence_compute.mbt`、`bignat.mbt`）：等價以可枚舉的表（`FinMap`）表示，
  故「A ≃ B」可**搜尋判定**（單射前綴剪枝，任何大小即時）；計數（`|B|^|A|`、`n!`、
  路徑數）以 `BigNat` 精確決算，16 元素不溢位（舊 `Int32` 算式 `16^16 ≡ 0`、`16!` 回繞）；
  `ua` 的四條計算律、截面／收縮律（即「單值性本身是等價」）在預算內窮舉驗證
  （三值 `LawVerdict`，超預算回 `LawUndecided` 不抽樣）；路徑型別的元素個數被算出
  （n 元素型為 n!，`Bool × Bool` 為 24，16 元素型為 20922789888000）。
- **重構證書**（`refactor_certificate.mbt`）：把「介面」看成有限符號集，重構即符號集之間的
  映射；以單值性的判定程序認證其為雙射（補齊到 2 的冪後即 `fin_map_is_equiv`），等價者
  給出 ua 路徑，逐符號判定沿路徑 coe 搬運且往返為恆等。本專案的解耦手術（檔案級循環
  6 → 1、37 個宣告搬遷、0 符號遺失）即以此逐項登記與判定。
- **n 維立方體演算法**（`cube_algorithm.mbt`）：以面格上的 Möbius（容斥）和，導出任意
  維度、任意缺失面的 Kan 填充 `nfill` 與合成 `ncomp`；邊界方程逐面核對、對維度重標
  自然，成本 `2^(2n−1) − 1` 並可作預算判定；與手寫二維 `square_fill` 的關係被精確刻畫
  （同邊界、不同截面）。

**第九期新增**：

- **符號化恆等層去 `LawUndecided` 天花板**（`univalence_compute.mbt`）：`ua_section_proved`／
  `ua_retraction_proved` 以 O(n) 結構恆等（`cpath_coe_index(p,0,1,i)=p.e.table[i]` 對
  任意 `e`／`p` 成立，不論是否雙射）取代 n! 窮舉，16、256 元素型皆即時判 `LawHolds`；
  枚舉上界由 18 提升到 20（`20!` 為最大仍落在 `Int64` 內的階乘）。
- **有限宇宙擴充餘積 `TySum`**：`Ty`/`PVal` 新增 `TySum`/`PVLeft`/`PVRight`；
  `fin_sum_swap(a,b)` 為通用 `A+B ≃ B+A` 見證；過程中揪出並修正 `cpath_coe`
  反向搬運的潛伏錯誤（舊有呼叫端皆 `src==dst` 同形而意外answer正確）。
- **`BigInt`／`BigRat` 精確整數與有理數層**（`bigint.mbt`、`bigrat.mbt`）：
  符號-量值 `BigInt`、恆約分的 `BigRat`，與既有 `Int32`-界 `Rat`（symalg.mbt）
  雙向橋接；46337⁴ 示範 `Rat` 鏈式乘法會靜默溢位而 `BigRat` 保持精確。
- **半伴隨等價與可縮纖維**（`ishae.mbt`）：`Ishae`（g/η/ε/三角律 τ）、
  `biinv_to_ishae`（左右逆併為單一 ishae，代換鏈推導而非假設）、
  `fin_equiv_three_ways_agree`（雙射＝可縮纖維＝存在 ishae 三者窮舉一致，
  HoTT book Thm 4.2.3/4.3.2 的具體化）。
- **公開判定 API 根除 `LawUndecided` 出口**（`univalence_compute.mbt`）：
  `ua_section_all`／`ua_retraction_all` 本身（而非僅並行的 `_proved` 變體）
  加上 `exhaustion_search_feasible` 廉價可行性捷徑後，對任意大小皆判
  `LawHolds`，絕不回報未決定。
- **`SumWiring`：wiring 層落地 `TySum` 等價**（`sum_wiring.mbt`）：新構造子
  `equiv_sum`／`equiv_sum_swap` 把 AST 一等 `Equiv`/`Iso`（`pathp_glue.mbt`）
  擴充到 tag-preserving 分支組合與換位，`sumwiring_comp`／`sumwiring_inv`
  在純葉片段正規化回舊 `Wiring` 範式（保證零回歸）；`equiv_prod` 明確拒絕
  `TySum` 疊在 `TyProd` 內的混合片段（超出 `Wiring` 葉模型範圍）。
- **單值性機制接上 `qpoly`/`qmat` 的具體資料**（`qpoly_univalence.mbt`）：
  `qpoly_roots_ty` 把 `qpoly_rational_roots` 的具體有理根列表讀成有限
  型別，讓既有 `FinMap`/`fin_map_is_equiv`/`cpath_ua` 直接作用在多項式
  根集上；`qmat_eigenvalue_permutation_*` 經 `qmat_charpoly` 把同一構造
  延伸到矩陣的有理譜；`qpoly_all_root_permutations_are_equivalences`
  窮舉驗證對稱群的每個置換都是被 `ua` 見證的等價。
- **命題截斷 HIT（squash）**（`ptrunc.mbt`）：schema.mbt 新增
  `hit_face_var_sentinel`／`dhit_face_var`，讓通用 HIT 的面表達式除了
  「實例化另一已定義 cell」外，也能表「端點即本次呼叫的第 k 個引數」——
  填補了 `∥A∥` 式 HIT（`point:A→∥A∥`、`squash:∀x y.x≡y`）原本缺的表達力；
  `squash_schema`／`ptrunc_schema` 落地此一具體實例，過程中順帶修正
  `conv_hit_cell_at` 一個既有的（與本功能無關的）維度長度不匹配越界讀取
  缺陷。

執行：`moon test`（118 個測試）、`moon run cmd/main`（期望 43/43 項檢查）、
`python3 tools/audit_spec.py --check`（2562 個介面符號、53 條規格登記、56 個規格族）。

文件：`GUIDE.md`（導覽）、`SPEC.md`（規格書）、`ARCHITECTURE.md`（13 層依賴圖、循環 6 → 1 的手術與 `.pkg`／閉包結論）、
`REFACTORING.md`（重構審計），四者皆為中英雙語（<kbd>English</kbd> 摺疊切換）。

<details>
<summary><b>English</b></summary>

Hermitian idempotent projectors and orthogonal eigenspace decomposition;
cubical interval, faces and systems modulo quotient with pruning; Kan comp by
retraction; NbE in three layers (beta-pi, typed eta-long, and dependent Pi/Sigma
with a cumulative universe hierarchy); persistent shared environments,
call-by-need semantic thunks and memoized dimension lines / type families; a
cubical AST with PathP, data types (Bool/Nat/List), Circle/Torus HITs and
coe/comp/hcomp/hfill term constructors whose Kan operations reduce by type (Pi,
Sigma, PathP, Glue, data, HITs and universes); DSystem composition systems with
checked compatibility for raw systems, first-match normal forms and multi-branch
Glue partial values; first-class AST equivalences, ua and GlueEquiv; checked
substitution-respecting type lines and a schema registry with elaboration
caches; generic strictly-positive inductive-family and arbitrary
finite-dimensional HIT schema generators (nested container functors, mutual
families, Tarski induction-recursion, quotient cells and universe schemes); HOAS
on normal forms; symbolic decision (interned DAG ROBDDs with budgets/DPLL,
wirings); exact rational and algebraic-extension algebra with generalized
eigenspaces and Jordan decompositions; certified exact shadows of the numeric
projector/cube layer; general Glue comp; spheres by iterated suspension
(including S3); certified Hermitian Jacobi iteration by symbolic interval
inclusion; a Miller-pattern higher-order-unification bidirectional elaborator;
parameterized modules with import/open/namespace semantics; and an audited
per-symbol canonical-form/categorification specification.

**New in phase 8:**

- **Computable univalence** (`univalence_compute.mbt`, `bignat.mbt`): equivalences are
  enumerable tables (`FinMap`), so "A ≃ B" is *decided by search* (injective-prefix
  pruning, instant at every size); counts (`|B|^|A|`, `n!`, path counts) are exact
  `BigNat`, overflow-free at 16 elements (the old `Int32` formulas wrapped at
  `16^16 ≡ 0` and 16!); the four computation rules of `ua` and the
  section/retraction laws — i.e. "univalence itself is an equivalence" — are
  verified by budgeted exhaustion (three-valued `LawVerdict`, `LawUndecided` over
  budget, never a sample); the cardinality of the path type is computed (n! for a
  type of size n — 24 for `Bool × Bool`, 20922789888000 for a 16-element type).
- **Refactor certificates** (`refactor_certificate.mbt`): an interface is a finite
  symbol set and a refactor is a map between them; the bijection is certified by
  the univalence decision procedure (padded to a power of two it *is*
  `fin_map_is_equiv`), an equivalence yields a ua path, and per-symbol verdicts
  transport along it with an identity round trip. The decoupling surgery of this
  repository (six file-level cycles to one, 37 declarations moved, 0 symbols
  lost) is registered and decided this way.
- **The n-dimensional cube algorithm** (`cube_algorithm.mbt`): a Kan filler
  `nfill` and composite `ncomp` for an arbitrary dimension and an arbitrary
  missing face, by the Möbius (inclusion–exclusion) sum over the face lattice;
  boundary equations checked face by face, natural under relabelling dimensions,
  with a `2^(2n−1) − 1` cost exposed as a budget decision; its relation to the
  hand-written 2-D `square_fill` is stated exactly (same boundary, different
  section).

**New in phase 9:**

- **A symbolic identity layer eradicates the `LawUndecided` ceiling**
  (`univalence_compute.mbt`): `ua_section_proved`/`ua_retraction_proved`
  replace n!-exhaustion with an O(n) structural identity
  (`cpath_coe_index(p,0,1,i)=p.e.table[i]` holds for any `e`/`p` whatsoever,
  bijective or not), deciding `LawHolds` instantly at 16 and even 256
  elements; the enumeration ceiling is raised from 18 to 20 (`20!` is the
  largest factorial that still fits `Int64`).
- **The finite universe gained a coproduct, `TySum`**: `Ty`/`PVal` gained
  `TySum`/`PVLeft`/`PVRight`; `fin_sum_swap(a,b)` is the generic
  `A+B ≃ B+A` witness; writing its tests surfaced and fixed a latent bug in
  `cpath_coe`'s backward-direction transport (dormant because every prior
  caller happened to have `src==dst` as literally the same `Ty`).
- **A `BigInt`/`BigRat` exact integer and rational layer** (`bigint.mbt`,
  `bigrat.mbt`): sign-magnitude `BigInt`, always-reduced `BigRat`, bridged
  both ways to the existing `Int32`-bounded `Rat` (symalg.mbt); 46337⁴
  demonstrates chained `Rat` multiplication silently overflowing while
  `BigRat` stays exact.
- **Half-adjoint equivalences and contractible fibers** (`ishae.mbt`):
  `Ishae` (g/η/ε/triangle τ), `biinv_to_ishae` (biinv's left/right inverses
  merged into one ishae by a derived substitution chain, not assumed),
  and `fin_equiv_three_ways_agree` (bijective = contractible fibers = an
  ishae exists, agreeing exhaustively — a concretization of HoTT book
  Thm 4.2.3/4.3.2).
- **The public decision APIs eradicate their `LawUndecided` exit**
  (`univalence_compute.mbt`): `ua_section_all`/`ua_retraction_all`
  themselves (not just the parallel `_proved` variants) now never return
  `LawUndecided` for these two laws, at any size, via a cheap
  `exhaustion_search_feasible` feasibility short-circuit.
- **`SumWiring`: `TySum` equivalences land in the wiring layer**
  (`sum_wiring.mbt`): new `equiv_sum`/`equiv_sum_swap` constructors extend
  the AST-level `Equiv`/`Iso` (`pathp_glue.mbt`) to tag-preserving branch
  combination and swap; `sumwiring_comp`/`sumwiring_inv` normalise back to
  the old `Wiring` normal form on the pure-leaf fragment (zero regression
  by construction); `equiv_prod` explicitly rejects a `TySum` nested inside
  a `TyProd` (outside `Wiring`'s leaf model).
- **Computable univalence now acts on concrete `qpoly`/`qmat` data**
  (`qpoly_univalence.mbt`): `qpoly_roots_ty` reads a polynomial's concrete
  rational-root array as a finite type, letting the existing
  `FinMap`/`fin_map_is_equiv`/`cpath_ua` act directly on it;
  `qmat_eigenvalue_permutation_*` extends the same construction to a
  matrix's rational spectrum via `qmat_charpoly`;
  `qpoly_all_root_permutations_are_equivalences` exhaustively checks that
  every permutation in the symmetric group is a `ua`-witnessed equivalence.
- **Propositional truncation HIT (squash)** (`ptrunc.mbt`): schema.mbt
  gained `hit_face_var_sentinel`/`dhit_face_var`, letting a generic HIT
  face express not just "instantiate another, already-defined cell" but
  also "this endpoint *is* this call's k-th argument" — filling the
  expressiveness gap that an `∥A∥`-style HIT (`point:A→∥A∥`,
  `squash:∀x y.x≡y`) needed; `squash_schema`/`ptrunc_schema` land this
  concrete instance, surfacing (and fixing) a pre-existing, unrelated
  out-of-bounds bug in `conv_hit_cell_at` when comparing cells of
  different dimension.

Run: `moon test` (118 tests), `moon run cmd/main` (expected: 43/43 checks),
`python3 tools/audit_spec.py --check` (2,562 interface symbols, 53 spec entries,
56 specification families).

Docs: `GUIDE.md` (tour), `SPEC.md` (specification), `ARCHITECTURE.md` (13 layers, the
cycle surgery 6 → 1, and the `.pkg` vs closures conclusion), `REFACTORING.md`
(the refactor audit) — all three
are bilingual, with the English behind an <kbd>English</kbd> toggle.

</details>
