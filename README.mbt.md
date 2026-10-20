# username/cubical-hermitian

[![CI](https://github.com/vv0101v01/Neurons/actions/workflows/ci.yml/badge.svg)](https://github.com/vv0101v01/Neurons/actions/workflows/ci.yml)
[![moon test](https://img.shields.io/badge/moon%20test-55%2F55-brightgreen)](https://github.com/vv0101v01/Neurons)
[![theorems](https://img.shields.io/badge/cmd%2Fmain-43%2F43-brightgreen)](https://github.com/vv0101v01/Neurons)
[![interface](https://img.shields.io/badge/interface-2339%20symbols-blue)](SPEC.md)

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

- **可計算單值性定理**（`univalence_compute.mbt`）：等價以可枚舉的表（`FinMap`）表示，
  故「A ≃ B」可**搜尋判定**；`ua` 的四條計算律、截面／收縮律（即「單值性本身是等價」）
  在全部元素與全部表上窮舉驗證；路徑型別的元素個數被算出（n 元素型為 n!，
  `Bool × Bool` 為 24）。
- **重構證書**（`refactor_certificate.mbt`）：把「介面」看成有限符號集，重構即符號集之間的
  映射；以單值性的判定程序認證其為雙射（補齊到 2 的冪後即 `fin_map_is_equiv`），等價者
  給出 ua 路徑，逐符號判定沿路徑 coe 搬運且往返為恆等。本專案的解耦手術（檔案級循環
  6 → 1、37 個宣告搬遷、0 符號遺失）即以此逐項登記與判定。
- **n 維立方體演算法**（`cube_algorithm.mbt`）：以面格上的 Möbius（容斥）和，導出任意
  維度、任意缺失面的 Kan 填充 `nfill` 與合成 `ncomp`；邊界方程逐面核對、對維度重標
  自然，成本 `2^(2n−1) − 1` 並可作預算判定；與手寫二維 `square_fill` 的關係被精確刻畫
  （同邊界、不同截面）。

執行：`moon test`（55 個測試）、`moon run cmd/main`（期望 43/43 項檢查）、
`python3 tools/audit_spec.py --check`（2339 個介面符號、53 條規格登記、54 個規格族）。

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

- **Computable univalence** (`univalence_compute.mbt`): equivalences are
  enumerable tables (`FinMap`), so "A ≃ B" is *decided by search*; the four
  computation rules of `ua` and the section/retraction laws — i.e. "univalence
  itself is an equivalence" — are verified exhaustively over all elements and all
  tables; the cardinality of the path type is computed (n! for a type of size n,
  24 for `Bool × Bool`).
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

Run: `moon test` (55 tests), `moon run cmd/main` (expected: 43/43 checks),
`python3 tools/audit_spec.py --check` (2,339 interface symbols, 53 spec entries,
54 specification families).

Docs: `GUIDE.md` (tour), `SPEC.md` (specification), `ARCHITECTURE.md` (13 layers, the
cycle surgery 6 → 1, and the `.pkg` vs closures conclusion), `REFACTORING.md`
(the refactor audit) — all three
are bilingual, with the English behind an <kbd>English</kbd> toggle.

</details>
