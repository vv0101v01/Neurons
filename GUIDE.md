# cubical-hermitian 導覽（MoonBit 實作）

> 🔀 **切換 / Toggle**：每節先列中文，英文收在 <kbd>English</kbd> 摺疊區內 —— 按一下右側 ▸／<kbd>English</kbd> 即切換。
> Each section is Chinese first; press the <kbd>English</kbd> summary to toggle.


一組互相纏繞的概念做成**可執行、可測試的計算模型**：

- 冪等 Hermitian 矩陣（正交投影）與其特徵空間正交分解；
- 以投影 `P` 為 retraction，對特徵空間做 Kan 纖維化**剪枝**（ambient 先填充，再 `P ∘ fill`）；
- cubical 區間、面公式與系統（partial elements）的**商**、可交換性與相容性；
- 立方體在區間上的 `comp`（開盒填充公式）；
- NbE 的**單值性**（正規形唯一），型別導向版本給出 **η 長正規形**；
- `coe` 計算規則是求值器規則故 `coe^refl ≡ id`、`coe^(ua swap) ≡ swap` 定義成立；
- HOAS 與一階語法在正規形上的**同構**；
- 有限宇宙的 **ua**、`PathP` 積交換、`Glue` 可靠性與**一般 Glue comp**、`J` 律、正交性；
- 有限側**符號判定**：ROBDD（面）、BDD 區域範形（系統）、wiring（有限等價）；
- 單一立方 AST 承載 PathP、Bool/Nat/List、Circle/Torus，以及
  `coe/comp/hcomp/hfill` 項構造子，`hcomp` 按型別逐類化簡；
- 依賴語義以持久共享環境、最多算一次的 thunk 與引文鍵快取求值；
  composition 分支是可按值合併/排序的 `DSystem`，Glue 保存完整
  多分支 partial type/value 系統；
- 有限 schema 描述子可生成通用歸納族（巢狀正性函子、互歸納、
  Tarski 歸納—遞迴、構造子等式約束、宇宙 scheme）與任意有限維 HIT
  （含商型別）的檢查、依賴消去、conversion、quote 與 Kan comp；
- 原始 `DSystem` 可精確判定相容性並有 first-match 範形；AST 內有一等
  `Equiv`/`ua`/`GlueEquiv`；語義線與 schema 分別有受檢查入口與註冊快取；
- 精確有理/代數擴張代數給出廣義特徵空間與 Jordan 分解；BDD 是
  hash-consed DAG 並有預算/DPLL，數值投影/立方體有精確證書影子；
- `SPEC.md` 對全部型別、算子、規格、結構逐符號（2339 個、53 條規格）
  給出規範形式與範疇化；`ARCHITECTURE.md` 給出 13 層依賴圖、六個循環解成一個的
  手術與打包（`.pkg` vs 閉包）結論，`REFACTORING.md` 是重構審計。


<details>
<summary><b>English</b></summary>

A set of mutually entangled concepts turned into an **executable, testable
computational model**:

- idempotent Hermitian matrices (orthogonal projections) and their orthogonal
  eigenspace decomposition;
- Kan fibrations **pruned** to an eigenspace with the projection `P` as
  retraction (fill in the ambient space, then `P ∘ fill`);
- cubical intervals, face formulas and systems (partial elements) modulo a
  quotient, with commutativity and compatibility;
- `comp` of a cube over the interval (the open-box filling formula);
- **uniqueness of normal forms** for NbE, with the type-directed version
  producing **η-long normal forms**;
- `coe` is an evaluator rule, so `coe^refl ≡ id` and `coe^(ua swap) ≡ swap`
  hold definitionally;
- an **isomorphism** between HOAS and first-order syntax on normal forms;
- **ua**, `PathP` product exchange, `Glue` soundness, general `Glue comp`,
  the `J` rule and orthogonality, in a finite universe;
- **symbolic decision procedures** on the finite side: ROBDDs (faces), BDD
  region normal forms (systems), wirings (finite equivalences);
- a single cubical AST carrying `PathP`, Bool/Nat/List, Circle/Torus and the
  `coe/comp/hcomp/hfill` term constructors, with `hcomp` reducing by type;
- dependent semantics with persistent shared environments, at-most-once
  thunks and quotation-keyed caches; composition branches are `DSystem`s that
  merge/sort by value, and `Glue` keeps full multi-branch partial
  type/value systems;
- finite schema descriptors generate generic inductive families (nested
  positivity functors, mutual families, Tarski induction-recursion,
  constructor equality constraints, universe schemes) and HITs of arbitrary
  finite dimension (including quotients), each with checking, dependent
  elimination, conversion, quote and Kan comp;
- raw `DSystem`s get exact compatibility checking and a first-match normal
  form; the AST has first-class `Equiv`/`ua`/`GlueEquiv`; semantic lines and
  schemas have checked entry points and registry caches;
- exact rational / algebraic-extension algebra yields generalized eigenspaces
  and Jordan decompositions; BDDs are hash-consed DAGs with budgets/DPLL, and
  the numeric projector/cube layer has an exact certificate shadow;
- **computable univalence**: for finite types, equivalences are searched for,
  `ua` is proved to be an equivalence (section and retraction laws decided
  elementwise), and the type of paths is counted (n!);
- **the n-dimensional cube algorithm**: a Möbius (inclusion–exclusion) Kan
  filler for an arbitrary dimension and an arbitrary missing face, with
  coherence under relabelling and a `2^(2n−1) − 1` cost model;
- `SPEC.md` gives a canonical form and categorification for every type,
  operator, specification and structure (2,358 symbols, 52 families).

</details>

## 運行與驗收

```text
moon test                              # 55 個白箱測試
moon run cmd/main                      # 43 項定理登記表，期望 43/43
python3 tools/audit_spec.py --check    # SPEC.md 附錄與介面集合相等（2339 符號、54 族）
```


<details>
<summary><b>English</b></summary>

```text
moon test                              # 55 white-box tests
moon run cmd/main                      # 43 registered theorems, expect 43/43
python3 tools/audit_spec.py --check    # SPEC.md appendix == interface set
                                       # (2,358 symbols, 52 families)
```

`ARCHITECTURE.md` documents the seven-layer dependency analysis of all 69
source files, the six file-level cycles, and the packaging conclusion
(one package + file layering, rather than splitting along the cycles).

</details>

## 本次升級重點


<details>
<summary><b>English</b></summary>

The sections below follow the historical phases; the newest work (phase 8,
computable univalence and the n-dimensional cube algorithm) is described in
`SPEC.md` §1.11 and `ARCHITECTURE.md` §5.

</details>

### NbE 加 η（`nbe_eta.mbt`）

雙向型別檢查/求值；`quote_eta` 按型別產生 η 長範形：函數 `λx.f x`、積
`(fst p, snd p)`、Unit `()`。中性 spine 攜帶參數/姊妹型別，故
`f:(B→B)→B` 的範形是 `λg. f (λx. g x)`。積 η 令 `swap∘swap ≡ id` 在
函數層面定義成立。範疇化：物件 `LTy`、態射為項模 βπη 的自由笛卡兒閉範疇。


<details>
<summary><b>English</b></summary>

Bidirectional checking/evaluation; `quote_eta` builds η-long normal forms by
type: functions `λx. f x`, pairs `(fst p, snd p)`, unit `()`. Neutral spines
carry argument/sister types, so the normal form of `f : (B→B)→B` is
`λg. f (λx. g x)`. Product η makes `swap ∘ swap ≡ id` hold definitionally at
the function level. Categorification: objects `LTy`, morphisms are the terms
modulo βπη, i.e. the free cartesian closed category.

</details>

### 一般 Glue comp（`glue_comp.mbt`）

- 有限宇宙端點算法：任意線 `A0≃A1`、`T0≃T1`、端點等價 `e0/e1` 與面
  `φ0/φ1`。要求自然性方塊 `e₁∘coe_T = coe_A∘e₀`（箭頭範疇的態射，
  wiring 符號判定）。步驟：在 A 合成 `a_raw=coe_A(a0)`；在 T 合成
  `t1=coe_T(t0)`（φ 在 1 才亮起時由 `e₁⁻¹(a_raw)` 反造偏部分）；
  校正 `a1=e₁(t1)`。兩端 φ 皆成立時相干性保證校正是常值，逐一檢證；
  不相干線數據回 `None`。
- 特徵子空間線：型別線是變動投影 `P(j)` 的像。兩只相容開盒各自
  ambient 填充再逐點剪枝；帽子以 `(i,k)↦(1−k)a_cap(i)+k·U(1)(t_cap(i))`
  的校正方塊（A 內 hcomp）修到 `U(1)(t_cap)`，側面端點不動。


<details>
<summary><b>English</b></summary>

- Finite-universe endpoint algorithm: arbitrary lines `A0 ≃ A1`, `T0 ≃ T1`,
  endpoint equivalences `e0/e1` and faces `φ0/φ1`. It requires the naturality
  square `e₁ ∘ coe_T = coe_A ∘ e₀` (a morphism of the arrow category, decided
  symbolically by wiring). Steps: compose `a_raw = coe_A(a0)` in A; compose
  `t1 = coe_T(t0)` in T (when φ lights up only at 1, build the partial part
  from `e₁⁻¹(a_raw)`); correct `a1 = e₁(t1)`. If φ holds at both ends,
  coherence makes the correction constant, checked pointwise; incoherent line
  data yields `None`.
- Eigenspace lines: the type line is the image of a varying projection `P(j)`.
  Two compatible open boxes are each filled in the ambient space and pruned
  pointwise; the cap is repaired to `U(1)(t_cap)` by the correction square
  `(i,k) ↦ (1−k)a_cap(i) + k·U(1)(t_cap(i))` (an hcomp inside A), and the side
  endpoints do not move.

</details>

### 符號判定（`bdd.mbt`, `wiring.mbt`, `system_symbolic.mbt`）

- 面：ROBDD 為規範形，`sat/≤/≡/見證` 皆符號操作；
- 系統：有效區域 `φᵢ∧¬前覆蓋` 的 BDD 分割範形 `SystemNF`，商相等＝範形相等；
- 有限等價：wiring 帶號置換範形，wf 是 O(#葉) 置換性，合成是替換＋XOR，
  相等是結構相等。它同時是自由對稱冪冪範疇的態射（五邊形/三角形/六邊形
  相干律已驗）；
- 枚舉只留在 `*_extensional / *_oracle` 與白箱測試做差分校驗，不是判定路徑。


<details>
<summary><b>English</b></summary>

- Faces: ROBDDs are canonical, and `sat/≤/≡/witness` are all symbolic.
- Systems: the BDD partition normal form `SystemNF` over effective regions
  `φᵢ ∧ ¬(previous covers)`; quotient equality is normal-form equality.
- Finite equivalences: wirings are signed-permutation normal forms; `wf` is an
  O(#leaves) permutation check, composition is substitution + XOR, and
  equality is structural. They are also the morphisms of the free symmetric
  powerset category (pentagon/triangle/hexagon coherence checked).
- Enumeration survives only in `*_extensional` / `*_oracle` and the white-box
  tests as a differential oracle; it is never the decision path.

</details>

### 依賴 NbE：Π、Σ、宇宙（`nbe_dep.mbt`）

項與型別共用 `DTerm`；Π/Σ 的綁定後分量在語意域是閉包族，依賴代入
如 `snd p : B(fst p)` 直接計算。宇宙採累積 `Typeᵢ : Typeᵢ₊₁`。
轉換與範形由按型別的 `conv_at/quote_at`（含 η）與 `quote_ty` 給出；
範疇化為帶族範疇（CwF）句法模型。


<details>
<summary><b>English</b></summary>

Terms and types share `DTerm`; Π/Σ binding components are closure families in
the semantic domain, so dependent substitution such as `snd p : B(fst p)`
computes directly. Universes are cumulative, `Typeᵢ : Typeᵢ₊₁`. Conversion and
normal forms come from the type-directed `conv_at/quote_at` (with η) and
`quote_ty`; the categorification is the syntactic model of a category with
families (CwF).

</details>

### Kan coe/comp 全型別化（`kan_dep.mbt`）

型別線 `DLine{at,coe,fill}`，`comp=fill(1)`。Bool/Unit/Universe 是
常線；Π 在定義域反向 coe，Σ 沿第一分量路徑 coe 第二分量；依賴族
以「A 中路徑 → DLine」呈現。簡單型別與有限型別經非依賴嵌入，
有限 ua 是非恆常線；再加子空間線與 Glue，全專案型別族皆有 Kan 結構。


<details>
<summary><b>English</b></summary>

Type lines are `DLine{at, coe, fill}` with `comp = fill(1)`. Bool/Unit/Universe
are constant lines; Π contracts `coe` on the domain and Σ contracts along the
first component's path; dependent families are presented as
"path in A → DLine". Simple and finite types are embedded non-dependently, and
the finite `ua` is a non-constant line; adding subspace lines and Glue gives
every type family in the project a Kan structure.

</details>

### 特徵值／投影／仿射填充的符號代數（`symalg.mbt`, `spectral_symbolic.mbt`）

以 Q 上多變量多項式範形與分式精確表示 `SymC/SymMat`，相等即多項式
恆等。譜投影用拉格朗日式 `Pₖ=qₖ(A)/qₖ(λₖ)`，幂等、正交、單位
分解與譜分解用首一整除及多項式恆等證明；`det(XI−A)` 給出特徵
多項式。仿射填充在雙線性類中由四角唯一決定，其係數差分公式與
邊界方程均在座標原子上以恆等式成立；投影剪枝滿足 `(I−P)(PF)=0`。


<details>
<summary><b>English</b></summary>

Multivariate polynomial normal forms over Q plus exact fractions represent
`SymC/SymMat`; equality is polynomial identity. Spectral projectors use the
Lagrange form `Pₖ = qₖ(A)/qₖ(λₖ)`, and idempotence, orthogonality, the
resolution of the identity and the spectral decomposition are proved by monic
division and polynomial identities; `det(XI−A)` gives the characteristic
polynomial. Affine filling in the bilinear class is uniquely determined by the
four corners, and its coefficient-difference formulas and boundary equations
hold as identities on the coordinate atoms; projector pruning satisfies
`(I−P)(PF) = 0`.

</details>

### 立方 AST 與 hcomp 按型別化簡（`nbe_dep.mbt`, `kan_ast.mbt`, `ast_laws.mbt`）

`DTerm` 同時有項與維度兩套 de Bruijn 索引：`DLamDim/DAppDim` 是
`<i> e`/`e @ r`，型別線和 tube 都是維度綁定子下的 body；
`DComp/DHComp/DHFill` 攜帶 `Array[DTubeTerm]` 多分支系統，
`DCoe` 攜帶線與任意兩端點。`comp_value` 的核心派遣是：

| 型別 | 化簡口訣 |
|---|---|
| Π | 參數先沿定義域**反向填充**，再在被搬運的餘域合成 |
| Σ | 先取第一分量 filler，第二分量沿它合成 |
| PathP | 除原 tube 外再加左右端點分支 |
| Universe | `hcompU` 產生 Glue；Glue 再以 partial/base 兩合成＋hcomp 校正 |
| Bool/Nat/List | 構造子對齊才遞迴（`succ`、`cons` 分頭尾） |
| Circle/Torus | 全 base 回 base，非平凡系統留形式 hcomp 點 |

Bool/Nat/List/Circle/Torus 都有依賴消去子；消去子遇到形式 composition
時會在 motive 裡再 comp，因此不會只卡在 eliminator 外層。Circle 點範形
是 `loop@r`，Torus 點範形是對邊黏合的 `square@(i,j)`。填充則由
`comp` 限制到線段 `j≤r` 得到；任意端點 `coe` 由 fill 與線段重參數化
組成，`coe(r,r)` 定義恆等。


<details>
<summary><b>English</b></summary>

`DTerm` carries two de Bruijn index spaces — terms and dimensions:
`DLamDim/DAppDim` are `<i> e` and `e @ r`; type lines and tubes are bodies under
dimension binders. `DComp/DHComp/DHFill` carry multi-branch systems as
`Array[DTubeTerm]`, and `DCoe` carries a line with two arbitrary endpoints. The
dispatch at the heart of `comp_value` is:

| type | reduction recipe |
|---|---|
| Π | fill the argument backwards along the domain, then compose in the transported codomain |
| Σ | take the first component's filler, compose the second along it |
| PathP | add left/right endpoint branches to the existing tube |
| Universe | `hcompU` produces a Glue; Glue then composes partial/base plus an hcomp correction |
| Bool/Nat/List | recurse only when constructors align (`succ`, `cons` split head/tail) |
| Circle/Torus | all-base systems return base; non-trivial systems stay as formal hcomp points |

Bool/Nat/List/Circle/Torus each have a dependent eliminator; on a formal
composition the eliminator comps inside the motive, so it never gets stuck at
the eliminator's outer shell. The canonical point of Circle is `loop@r`, and of
Torus a square glued along opposite edges, `square@(i,j)`. Filling is `comp`
restricted to the segment `j ≤ r`; `coe` at arbitrary endpoints is fill plus
re-parameterisation of the segment, with `coe(r,r)` definitionally the identity.

</details>

### 語義系統、持久環境與惰性求值（`nbe_dep.mbt`, `semantic_system_laws.mbt`）

`DEnv/DDimEnv` 是帶長度的持久連結串列：脈絡延伸只 cons 一個節點並
共享尾部，陣列只留在公開邊界。構造子分量、函數引數、case 與 partial
分支以 `DVThunk` 延遲，第一次 `force_value` 後保存結果，
`lazy_force_count` 可驗證最多計算一次。維度線與 Π/Σ 族分別以簡化
維度鍵和引文鍵 memoize。

composition 的語義分支封裝為 `DSystem`。`dsystem_canonical` 沿型別線
以轉換合併同 body 分支（面取聯集）並按引文排序；`DPartialValue` 的
`partial_normal_form` 則用 BDD 計算 first-match 有效區域。`DVGlue`
保存完整 partial type `DSystem`，多分支元素以 `DPartial/DVPartial`
逐面給值，檢查、conversion、quote 與 Glue comp 都逐分支對齊。


<details>
<summary><b>English</b></summary>

`DEnv/DDimEnv` are length-tagged persistent linked lists: extending a context
conses one node and shares the tail, with arrays kept only at the public
boundary. Constructor fields, function arguments, case and partial branches are
delayed as `DVThunk`s; the first `force_value` stores the result, and
`lazy_force_count` verifies at-most-once computation. Dimension lines and Π/Σ
families are memoized under simplified dimension keys and quotation keys
respectively.

The semantic branches of a composition are packed as `DSystem`.
`dsystem_canonical` merges branches with the same body along a type line
(unioning faces) and sorts by quotation; `partial_normal_form` computes
first-match effective regions with BDDs. `DVGlue` keeps the full partial type
`DSystem`, and multi-branch elements are given face by face as
`DPartial/DVPartial`; checking, conversion, quote and Glue comp all align branch
by branch.

</details>

### 通用歸納族與 HIT schema 生成器（`schema.mbt`, `schema_laws.mbt`）

`DInductiveSpec` 以參數/索引 telescopes、完整引數型別與
`DPositiveFunctor` 解碼描述一族，結構化極性判定處理別名與巢狀遞迴；生成器自動產生
`DInductive/DIntro/DInductiveElim` 的求值、雙向檢查、motive/case
型別、IH、conversion、quote 與逐引數 filler 的 comp。範例包括
`NatS/BoolS/ListS/VecS/FinS/TreeS/WS`。

`DHitSpec` 以任意有限維 cells 與 face expressions 描述 HIT。
`hit_cell_value` 在端點維度遞迴代入 face；生成 case 型別按維數是
point、PathP 或巢狀 PathP square，端點由低維 face 的消去值給出。
同 cell 時 comp 逐引數計算；移動維度在端點可精確決定時亦計算，其餘保留形式中性合成範形。
範例包括 `CircleS/SegmentS/TorusS`。


<details>
<summary><b>English</b></summary>

`DInductiveSpec` decodes one family from parameter/index telescopes, full
argument types and a `DPositiveFunctor`; structural polarity checking handles
aliases and nested recursion. The generator produces evaluation, bidirectional
checking, motive/case types, induction hypotheses, conversion, quote and
per-argument comp for `DInductive/DIntro/DInductiveElim`. Examples include
`NatS/BoolS/ListS/VecS/FinS/TreeS/WS`.

`DHitSpec` describes a HIT by cells of arbitrary finite dimension plus face
expressions. `hit_cell_value` substitutes faces recursively at endpoint
dimensions; generated case types are points, `PathP`s or nested `PathP` squares
by dimension, and endpoints are given by eliminating the lower-dimensional
faces. For a cell against itself, comp is computed argument by argument; when a
moving dimension is exactly determined at the endpoints it also computes, and
otherwise a formal neutral composition is kept. Examples include
`CircleS/SegmentS/TorusS`.

</details>

### 第六期邊界收束（`schema_extensions.mbt`, `dsystem_compat.mbt`, `equiv_ast.mbt`, `checked_line.mbt`, `schema_registry.mbt`, `qpoly.mbt`, `qmat.mbt`, `Jordan.mbt`, `algnum.mbt`, `bdd_dag.mbt`, `certified_numeric.mbt`）

- **Schema**：互歸納（Sum-indexed 編譯）、`DDecode` Tarski 歸納—遞迴、
  商 HIT、宇宙 level schemes、構造子 Path 約束與高維 cells。
- **系統/等價**：原始 `DSystem` 相容性以面相對轉換判定；AST `Equiv`
  攜帶 fwd/bwd/section/retraction，`ua` 與 `GlueEquiv` 在 Kan 引擎中計算。
- **可信邊界**：`DCheckedTypeLine` 保存經檢查 body；schema registry
  快取驗證與 telescopes。
- **精確代數**：`QPoly/QMat`、二次與一般代數擴張、primary projectors、
  廣義特徵空間與 Jordan 分解。
- **可擴展/認證**：BDD DAG（root 判定、預算、最佳候選次序、DPLL）；
  `QuadC/CertMat/CertPath` 以精確恆等取代數值網格的真假來源。


<details>
<summary><b>English</b></summary>

- **Schema**: mutual induction (Sum-indexed compilation), `DDecode`
  Tarski induction-recursion, quotient HITs, universe level schemes,
  constructor `Path` constraints and higher-dimensional cells.
- **Systems/equivalences**: raw `DSystem` compatibility is decided by
  face-to-face conversion; the AST's `Equiv` carries
  fwd/bwd/section/retraction, and `ua` and `GlueEquiv` compute inside the Kan
  engine.
- **Trusted boundary**: `DCheckedTypeLine` keeps a checked body; the schema
  registry caches validation results and telescopes.
- **Exact algebra**: `QPoly/QMat`, quadratic and general algebraic extensions,
  primary projectors, generalized eigenspaces and Jordan decomposition.
- **Scalability/certification**: BDD DAGs (root decision, budgets, best
  candidate ordering, DPLL); `QuadC/CertMat/CertPath` replace numeric grids as
  the source of truth by exact identities.

</details>

### 第七期：容器函子、S³、Jacobi、HOU 與模組

- `DFunctorContainer(Shape, Positions, index)` 把任意有限依賴多項式
  函子寫成 `Σ s, Positions(s)→X`，與互歸納/`DDecode` 共用生成器。
- `sphere3.mbt` 以懸掛迭代定義 `S²/S³`，meridian 端點與消去由 HIT
  生成器計算。
- `jacobi_interval.mbt` 對每次複 Jacobi 酉旋轉保存可重算的符號區間
  包含證書，最終以 Gershgorin 圓盤分簇特徵值。
- `hou_elaborator.mbt` 以 Miller pattern HOU 驅動雙向 elaborator，
  解隱含引數與 Nat motive，優化後譯回 `DTerm`。
- `module_system.mbt` 實作參數化模組函子、遞迴 import 內聯、
  only/hiding/open/alias/rename、歧義拒絕與 opaque 邊界。


<details>
<summary><b>English</b></summary>

- `DFunctorContainer(Shape, Positions, index)` writes any finite dependent
  polynomial functor as `Σ s, Positions(s)→X`, sharing its generator with
  mutual induction and `DDecode`.
- `sphere3.mbt` defines `S²/S³` by iterated suspension; meridian endpoints and
  elimination are computed by the HIT generator.
- `jacobi_interval.mbt` stores a recomputable symbolic interval-containment
  certificate for each complex Jacobi unitary rotation, and finally clusters
  eigenvalues by Gershgorin discs.
- `hou_elaborator.mbt` drives a bidirectional elaborator by Miller-pattern HOU,
  solving implicit arguments and Nat motives, then compiles the optimised
  result back to `DTerm`.
- `module_system.mbt` implements parametric module functors, inline recursive
  imports, only/hiding/open/alias/rename, ambiguity rejection and opaque
  boundaries.

</details>

### 第八期：可計算單值性與 n 維立方演算法（`univalence_compute.mbt`, `cube_algorithm.mbt`）

**可計算單值性。** `pathp_glue.mbt` 只是*陳述*單值性（`ua e` 包住一個等價，
`coe` 讀回端點）；`univalence_compute.mbt` 把它*變成可判定*。可計算的等價是一張
表（`FinMap`：`elems_of` 的索引列），所以全部以窮舉判定，不抽樣：

- `fin_map_is_equiv` 判等價（在所有元素上單射＋滿射）；`fin_equiv_search`
  按字典序掃表*搜出*一個等價，故「A ≃ B」是判定問題；
- `cpath_ua` / `cpath_to_equiv` 是單值性映射的兩個方向；
- `ua_transport_computes`（沿 `ua e` 搬運即 `e`）、`ua_refl_is_identity`
  （`ua id = refl`）、`ua_functorial`（`ua (g∘f) = ua g ∘ ua f`）、
  `ua_inverse`（`ua e⁻¹ = ¬(ua e)`）是四條計算律；
- `ua_section` / `ua_retraction` 逐元素驗證兩條互逆律，`ua_section_all` /
  `ua_retraction_all` 對兩型之間**每一張表**窮舉 —— 這就是「單值性本身是等價」，且被判定；
- `univalence_decides`：等價存在 ⟺ 基數相同；`univalence_path_count` 數路徑：
  n 元素型的恆等型別有 **n!** 個元素，正是等價型別的基數（`Bool × Bool` 為 24）。
  `univalence_compute_all` 是定理表的登記入口。

**立方體演算法。** `cube.mbt` 手寫了二維開盒；`cube_algorithm.mbt` 用面格的
Möbius 和，導出**任意維度、任意缺失面**的填充：

```
F(x) = Σ_{∅ ≠ S ⊆ L} (−1)^{|S|+1} · (Π_{(d,s) ∈ S} w(d,s)(x_d)) · face_S(x)
```

其中 `w(d,0) = 1 − x_d`、`w(d,1) = x_d`，而 `S` 的交以**最後選中的面**作錨點 ——
這正是邊界上能望遠鏡式相消的關鍵。`nfill_respects_box` 在 2–4 維、每個缺失面上
逐面核對；`ncomp` 取缺失面即 composition；`nbox_wf` 判定開盒相容；
`nfill_permutation_natural` 證明填充與維度重標交換。成本是 `2^(2n−1) − 1` 項
（n = 2, 3, 4 分別 7、31、127），由 `nfill_within_budget` 作預算判定。

Möbius 填充對各維度是**對稱**的，而手寫的方形填充是**以底邊為錨**；兩者是同一個
邊界問題的兩個不同截面 —— 在全部已知面上相等
（`nfill_agrees_with_square_on_given_faces`）、複合端點相同
（`ncomp_endpoints_match_legacy_comp`）、內部不同
（`nfill_differs_from_square_fill`）。能推廣的是對稱的那一個。


<details>
<summary><b>English</b></summary>

**Computable univalence.** `pathp_glue.mbt` *states* univalence — `ua e` wraps
an equivalence and `coe` reads it back. `univalence_compute.mbt` *decides* it.
A computable equivalence is a table (`FinMap`: an array of indices into
`elems_of`), so everything is decided by enumeration, never by sampling:

- `fin_map_is_equiv` decides equivalence (injective + surjective on all
  elements); `fin_equiv_search` *finds* one by scanning tables in lexicographic
  order, so "A ≃ B" is a decision problem;
- `cpath_ua` / `cpath_to_equiv` are the two directions of the univalence map;
- `ua_transport_computes` (transport along `ua e` is `e`), `ua_refl_is_identity`
  (`ua id = refl`), `ua_functorial` (`ua (g∘f) = ua g ∘ ua f`) and `ua_inverse`
  (`ua e⁻¹ = ¬(ua e)`) are the computation rules;
- `ua_section` / `ua_retraction` verify the two inverse laws elementwise, and
  `ua_section_all` / `ua_retraction_all` exhaust every table between two types —
  this is "univalence is an equivalence", decided;
- `univalence_decides` says an equivalence exists iff the cardinalities agree,
  and `univalence_path_count` counts paths: for a type of size n the identity
  type has **n!** elements, the cardinality of the type of equivalences
  (24 for `Bool × Bool`). `univalence_compute_all` is the registry entry.

**The cube algorithm.** `cube.mbt` hand-writes the 2-dimensional open box.
`cube_algorithm.mbt` derives a filler for arbitrary dimension and arbitrary
missing face by the Möbius sum over the face lattice:

```
F(x) = Σ_{∅ ≠ S ⊆ L} (−1)^{|S|+1} · (Π_{(d,s) ∈ S} w(d,s)(x_d)) · face_S(x)
```

with `w(d,0) = 1 − x_d`, `w(d,1) = x_d`, and the intersection of `S` read off
its *last* selected side (the anchor that makes the boundary telescope).
`nfill_respects_box` checks the boundary on grids for dimensions 2–4 and every
missing face; `ncomp` is the missing face, i.e. composition; `nbox_wf` decides
compatibility of the box; `nfill_permutation_natural` shows filling commutes
with relabelling dimensions. The cost is `2^(2n−1) − 1` terms (7, 31, 127 for
n = 2, 3, 4), exposed through `nfill_within_budget`.

The Möbius filler is *symmetric* in the dimensions, whereas the hand-written
square filler is *bottom-anchored*; the two are different sections of the same
boundary problem — they agree on every given face
(`nfill_agrees_with_square_on_given_faces`), their composites have the same
endpoints (`ncomp_endpoints_match_legacy_comp`), and they differ in the
interior (`nfill_differs_from_square_fill`). The symmetric one is what
generalises.

</details>

### 第九期：用單值性做重構 —— 解耦手術（`refactor_certificate.mbt`）

原本 6 個檔案級循環把層數壓成 7 層，也令「上一層只依賴下一層」失效。手術原則：
**只解「佈局意外」，保留「翻譯必要」**。

| 循環 | 成因 | 判定 | 處理 |
|---|---|---|---|
| `interval ⇄ bdd ⇄ bdd_dag` | 面的語法與判定同住 | 佈局意外 | ✅ 抽出 `face_core.mbt`，判定歸 `bdd.mbt` |
| `nbe ⇄ nbe_eta` | `LTy` 留在 η 層 | 佈局意外 | ✅ `LTy` 上移 `nbe.mbt` |
| `pathp_glue ⇄ wiring` | `Ty/PVal` 由 ua 層擁有 | 佈局意外 | ✅ 抽出 `finite_universe.mbt` |
| `system ⇄ system_symbolic` | `VecSystem` 資料型別在商／剪枝檔 | 佈局意外 | ✅ 抽出 `system_core.mbt` |
| `verify ⇄ *` | 驗收層同時擁有範例 | 佈局意外 | ✅ 範例下沉 `examples.mbt`、`check_cube_comp` 歸 `cube.mbt` |
| `nbe_dep ⇄ schema ⇄ schema_functor` | 型別同時是語義值與 schema 描述子 | **必要翻譯** | ⛔ 保留 |

**認證方式**（`refactor_certificate.mbt`）：把介面看成有限符號集，重構就是符號集之間的
映射；補齊到 2 的冪後交給單值性的判定程序（`plan_agrees_with_univalence` 即
`fin_map_is_equiv`），等價者以 `certify` 給出 ua 路徑，逐符號判定（規格族、層號）以
`certificate_transport_int` 沿路徑 coe 搬運，往返為恆等；丟失、靜默改名、非置換一律拒絕。
`decoupling_steps()` 登記本次 8 次搬遷、37 個宣告，`refactor_certificates_sound()` 一次判定。

**量度**：循環 6 → 1、符號遺失 0、`moon test` 55/55、`moon run cmd/main` 43/43、
`audit_spec.py --check` 2,339 符號／54 族。重跑：`python3 tools/refactor_audit.py`。


<details>
<summary><b>English</b></summary>

**Phase 9: refactoring with univalence — the decoupling surgery (`refactor_certificate.mbt`).**

Six file-level cycles had flattened the layering to 7 levels and broken the
"each layer depends only on the one below" invariant. The rule applied: **break
only layout accidents, keep translations.**

- `interval ⇄ bdd ⇄ bdd_dag` (face syntax vs face decision) — layout accident,
  fixed by extracting `face_core.mbt` and re-homing the four decisions to `bdd.mbt`;
- `nbe ⇄ nbe_eta` (`LTy` stranded in the η layer) — fixed by moving `LTy` up;
- `pathp_glue ⇄ wiring` (`Ty`/`PVal` owned by the ua layer) — fixed by
  `finite_universe.mbt`;
- `system ⇄ system_symbolic` (`VecSystem`'s data type in the quotient file) —
  fixed by `system_core.mbt`;
- `verify ⇄ *` (the acceptance layer also owning the examples) — fixed by
  `examples.mbt` and by moving `check_cube_comp` to `cube.mbt`;
- `nbe_dep ⇄ schema ⇄ schema_functor` (types are simultaneously semantic values
  and schema descriptors) — an essential translation, deliberately kept.

**Certification.** Treat an interface as a finite symbol set and a refactor as a
map between symbol sets. Padded to the next power of two it is handed to the
univalence decision procedure (`plan_agrees_with_univalence`, i.e.
`fin_map_is_equiv`); an equivalence yields a ua path via `certify`, per-symbol
verdicts (specification family, layer) are transported along it with
`certificate_transport_int`, and the round trip is the identity. Lost symbols,
silent renames and non-permutations are rejected. `decoupling_steps()` records
the eight moves and 37 declarations of this surgery, and
`refactor_certificates_sound()` decides the whole thing at once.

**Measured.** cycles 6 → 1, 0 symbols lost, `moon test` 55/55, `moon run
cmd/main` 43/43, `audit_spec.py --check` 2,339 symbols / 54 families. Re-run:
`python3 tools/refactor_audit.py`.

</details>

## 概念對照（精簡表）

| 概念 | 實作 | 檔案 |
|---|---|---|
| 冪等 Hermitian | `is_hermitian`, `is_idempotent`, `P=Σvₖvₖ†` | `complex.mbt`, `projector.mbt` |
| 特徵空間良構 | `Cⁿ=im(P)⊕ker(P)`、特徵方程、`tr(P)` | `projector.mbt` |
| 可交換相容 | `PQ=QP ⇒ PQ` 為投影 | `projector.mbt` |
| 系統商/剪枝 | BDD 區域範形、刪不可滿足/被含蘊分支、聯集交換 | `bdd.mbt`, `system.mbt`, `system_symbolic.mbt` |
| Kan 剪枝/comp | `P∘fill`、開盒公式、帽子、路徑傳遞 | `cube.mbt` |
| NbE / coe 定義等 | βπ 與 η 長範形、`def_eq(_eta)` | `nbe.mbt`, `nbe_eta.mbt` |
| HOAS 同構 | 宿主函數綁定、smart βπ、reify=`nf` | `nbe.mbt` |
| ua/PathP/J | wiring 等價→路徑、積交換自然性、常值線 coe | `wiring.mbt`, `pathp_glue.mbt` |
| Glue 可靠/comp | `glue/unglue` 方程、有限線端點算法、子空間 hcomp 校正 | `pathp_glue.mbt`, `glue_comp.mbt` |
| 範疇化 | Karoubi、面偏序、□ 範疇、句法 CCC、冪冪相干 | `categories.mbt`, `wiring.mbt` |
| Π/Σ/宇宙 | 依賴 NbE、型別導向轉換、依賴代入、Typeᵢ 層級 | `nbe_dep.mbt` |
| Kan 全型別 | DLine 對 Π/Σ/U/嵌入之 coe/comp 遞迴 | `kan_dep.mbt` |
| 符號譜代數 | 特徵多項式、譜投影恆等、仿射唯一填充恆等 | `symalg.mbt`, `spectral_symbolic.mbt` |
| 立方 AST/hcomp | PathP、`DSystem`、按 Π/Σ/Path/Glue/資料/HIT/Universe 化簡 | `nbe_dep.mbt`, `kan_ast.mbt`, `ast_laws.mbt` |
| 環境/惰性/快取 | `DEnv` 共享尾、`DVThunk` 最多算一次、維度線/族 memoization | `nbe_dep.mbt`, `semantic_system_laws.mbt` |
| 通用歸納/HIT schema | telescopes、函子正性、互/巢狀/歸納遞迴、商、高維 cells、生成 elim/case 與 comp | `schema.mbt`, `schema_extensions.mbt` |
| 原始系統/Equiv/線 | DSystem checked 相容、first-match 範形、AST Equiv/ua/GlueEquiv、受檢查線與 registry | `dsystem_compat.mbt`, `equiv_ast.mbt`, `checked_line.mbt`, `schema_registry.mbt` |
| 精確譜理論擴展 | QPoly/QMat、代數數、廣義特徵空間、primary 投影、Jordan 分解 | `qpoly.mbt`, `qmat.mbt`, `algnum.mbt`, `Jordan.mbt` |
| DAG/認證數值 | BDD manager、預算/DPLL、QuadC 精確投影與多項式填充證書 | `bdd_dag.mbt`, `certified_numeric.mbt` |
| 容器/S³/Jacobi/HOU/模組 | container 巢狀遞迴、懸掛球面、區間酉旋轉證書、pattern HOU elaborator、模組函子與名字空間 | `schema_functor.mbt`, `sphere3.mbt`, `jacobi_interval.mbt`, `hou_elaborator.mbt`, `module_system.mbt` |
| 規格範形登記 | 53 條目＋2339 符號附錄＋審計 | `spec.mbt`, `SPEC.md`, `tools/audit_spec.py` |


<details>
<summary><b>English</b></summary>

| concept | implementation | files |
|---|---|---|
| idempotent Hermitian | `is_hermitian`, `is_idempotent`, `P = Σvₖvₖ†` | `complex.mbt`, `projector.mbt` |
| eigenspace well-formedness | `Cⁿ = im(P) ⊕ ker(P)`, eigen equation, `tr(P)` | `projector.mbt` |
| commuting compatibility | `PQ = QP ⇒ PQ` is a projector | `projector.mbt` |
| system quotient / pruning | BDD region normal forms, drop unsat/implied branches, commutative union | `bdd.mbt`, `system.mbt`, `system_symbolic.mbt` |
| Kan pruning / comp | `P ∘ fill`, open-box formula, caps, path transitivity | `cube.mbt` |
| NbE / definitional coe | βπ and η-long normal forms, `def_eq(_eta)` | `nbe.mbt`, `nbe_eta.mbt` |
| HOAS isomorphism | host-function binding, smart βπ, reify = `nf` | `nbe.mbt` |
| ua/PathP/J | wiring equivalences → paths, product-exchange naturality, constant-line coe | `wiring.mbt`, `pathp_glue.mbt` |
| Glue soundness/comp | `glue/unglue` equations, finite-line endpoint algorithm, subspace hcomp correction | `pathp_glue.mbt`, `glue_comp.mbt` |
| categorification | Karoubi, face posets, □-category, syntactic CCC, powerset coherence | `categories.mbt`, `wiring.mbt` |
| Π/Σ/universes | dependent NbE, type-directed conversion, dependent substitution, `Typeᵢ` hierarchy | `nbe_dep.mbt` |
| Kan for all types | `DLine` recursion for Π/Σ/U/embeddings | `kan_dep.mbt` |
| symbolic spectral algebra | characteristic polynomial, spectral projector identities, unique affine filling | `symalg.mbt`, `spectral_symbolic.mbt` |
| cubical AST / hcomp | `PathP`, `DSystem`, reduction by Π/Σ/Path/Glue/data/HIT/Universe | `nbe_dep.mbt`, `kan_ast.mbt`, `ast_laws.mbt` |
| environments/laziness/caches | shared-tail `DEnv`, at-most-once `DVThunk`, memoized dimension lines/families | `nbe_dep.mbt`, `semantic_system_laws.mbt` |
| generic inductive/HIT schemas | telescopes, functor positivity, mutual/nested/induction-recursion, quotients, higher cells, generated elim/case and comp | `schema.mbt`, `schema_extensions.mbt` |
| raw systems / Equiv / lines | checked `DSystem` compatibility, first-match normal forms, AST `Equiv`/`ua`/`GlueEquiv`, checked lines and registry | `dsystem_compat.mbt`, `equiv_ast.mbt`, `checked_line.mbt`, `schema_registry.mbt` |
| exact spectral theory | QPoly/QMat, algebraic numbers, generalized eigenspaces, primary projectors, Jordan decomposition | `qpoly.mbt`, `qmat.mbt`, `algnum.mbt`, `Jordan.mbt` |
| DAGs / certified numerics | BDD manager, budgets/DPLL, `QuadC` exact projectors and polynomial-filling certificates | `bdd_dag.mbt`, `certified_numeric.mbt` |
| containers / S³ / Jacobi / HOU / modules | container nested recursion, suspension spheres, interval unitary-rotation certificates, pattern-HOU elaborator, module functors and namespaces | `schema_functor.mbt`, `sphere3.mbt`, `jacobi_interval.mbt`, `hou_elaborator.mbt`, `module_system.mbt` |
| **computable univalence** | `FinMap` tables, `fin_equiv_search`, `ua` computation rules, section/retraction laws, path count n! | `univalence_compute.mbt` |
| **n-dimensional cube algorithm** | Möbius filler over the face lattice, `ncomp`, `nbox_wf`, relabelling naturality, `2^(2n−1) − 1` budget | `cube_algorithm.mbt` |
| specification registry | 53 entries + 2,339-symbol appendix + audit | `spec.mbt`, `SPEC.md`, `tools/audit_spec.py` |
| **architecture** | 13 layers, cycles 6 → 1, refactor audit, packaging decision | `ARCHITECTURE.md`, `REFACTORING.md`, `tools/arch_report.py`, `tools/refactor_audit.py` |

</details>

## 檔案地圖

```text
complex.mbt / projector.mbt   C、向量、矩陣、伴隨；投影與特徵空間分解
interval.mbt / bdd.mbt        De Morgan 區間與面；面公式 ROBDD
system.mbt / system_symbolic.mbt  系統、相容性、剪枝；BDD 區域範形
face_core.mbt                 面語法：Dim/Face/Bdd 宣告、化簡、代換、邊界（L2）
finite_universe.mbt           有限宇宙型別 Ty 及其元素 PVal（L0）
system_core.mbt               VecSystem/VecBranch 的資料型別（L3）
examples.mbt                  跨層共用範例：投影、向量、網格（L2）
refactor_certificate.mbt      重構證書：介面等價、ua 路徑、判定搬運、解耦手術登記
cube.mbt                      立方體、面限制、開盒 comp、特徵空間剪枝
cube_algorithm.mbt            n 維開盒的 Möbius 填充演算法、ncomp、維度重標自然性
univalence_compute.mbt        可計算單值性：等價搜尋、ua 四律、截面／收縮律、路徑計數
nbe.mbt / nbe_eta.mbt         βπ NbE＋HOAS；型別化 η NbE 與句法箭頭
wiring.mbt                    有限等價帶號置換範形、冪冪相干律
pathp_glue.mbt                有限宇宙：ua、coe、PathP、Glue、J
glue_comp.mbt                 一般 Glue comp（有限線＋子空間線）
categories.mbt                Karoubi／面偏序／立方體範疇／句法 CCC
nbe_dep.mbt / kan_dep.mbt     Π/Σ/宇宙與立方 AST 依賴 NbE；DLine 的 coe/comp
kan_ast.mbt / ast_laws.mbt    AST 的 comp/hcomp/hfill/coe 按型別化簡與律
schema.mbt / schema_laws.mbt  通用歸納族與 HIT schema 生成器及其律
schema_extensions.mbt / schema_functor.mbt / schema_positivity.mbt
                              函子/正性、互歸納、商、宇宙 scheme、高維 HIT
dsystem_compat.mbt / equiv_ast.mbt / checked_line.mbt / schema_registry.mbt
                              checked 邊界：系統、等價、線、註冊與快取
qpoly.mbt / qmat.mbt / Jordan.mbt / algnum.mbt
                              精確有理與代數擴張線性代數、Jordan 理論
bdd_dag.mbt / certified_numeric.mbt
                              interned BDD、預算/DPLL、認證數值影子
sphere3.mbt / jacobi_interval.mbt / hou_elaborator.mbt / module_system.mbt
                              S³、認證 Jacobi、HOU elaborator、參數化模組
semantic_system_laws.mbt      DSystem、持久環境、惰性/快取與多分支 Glue 律
symalg.mbt / spectral_symbolic.mbt  精確多項式代數；譜投影與仿射恆等
spec.mbt / verify.mbt         規格登記；43 項定理登記表
*_wbtest.mbt                  白箱測試（差分 oracle 只在這裡）
cmd/main/                     打印登記表的入口
```


<details>
<summary><b>English</b></summary>

```text
complex.mbt / projector.mbt   C, vectors, matrices, adjoint; projectors and eigenspace decomposition
interval.mbt / bdd.mbt        De Morgan interval and faces; face formulas as ROBDDs
system.mbt / system_symbolic.mbt  systems, compatibility, pruning; BDD region normal forms
cube.mbt                      cubes, face restriction, open-box comp, eigenspace pruning
cube_algorithm.mbt            Möbius filling for n-dimensional open boxes, ncomp, relabelling naturality
univalence_compute.mbt        computable univalence: equivalence search, ua rules, section/retraction, path counts
nbe.mbt / nbe_eta.mbt         βπ NbE + HOAS; typed η NbE and syntactic arrows
wiring.mbt                    finite-equivalence signed-permutation normal forms, powerset coherence
pathp_glue.mbt                finite universe: ua, coe, PathP, Glue, J
glue_comp.mbt                 general Glue comp (finite lines + subspace lines)
categories.mbt                Karoubi / face posets / cube category / syntactic CCC
nbe_dep.mbt / kan_dep.mbt     Π/Σ/universe cubical dependent NbE; coe/comp of DLine
kan_ast.mbt / ast_laws.mbt    type-directed comp/hcomp/hfill/coe in the AST, and their laws
schema.mbt / schema_laws.mbt  generic inductive-family and HIT schema generators and their laws
schema_extensions.mbt / schema_functor.mbt / schema_positivity.mbt
                              functors/positivity, mutual induction, quotients, universe schemes, higher HITs
dsystem_compat.mbt / equiv_ast.mbt / checked_line.mbt / schema_registry.mbt
                              the checked boundary: systems, equivalences, lines, registry and caches
qpoly.mbt / qmat.mbt / Jordan.mbt / algnum.mbt
                              exact rational and algebraic-extension linear algebra, Jordan theory
bdd_dag.mbt / certified_numeric.mbt
                              interned BDDs, budgets/DPLL, certified numeric shadows
sphere3.mbt / jacobi_interval.mbt / hou_elaborator.mbt / module_system.mbt
                              S³, certified Jacobi, HOU elaborator, parametric modules
semantic_system_laws.mbt      DSystem, persistent environments, laziness/caches and multi-branch Glue laws
symalg.mbt / spectral_symbolic.mbt  exact polynomial algebra; spectral projectors and affine identities
spec.mbt / verify.mbt         specification registry; the 42-theorem registry
*_wbtest.mbt                  white-box tests (differential oracles live only here)
cmd/main/                     entry point that prints the registry
ARCHITECTURE.md               layer analysis, cycles, build order, packaging decision
REFACTORING.md                refactor audit: interface bijection + cycle count, before/after
```

</details>

## 範圍與邊界

這是該理論片斷的**可執行模型/規範**，不是完整生產級 cubical 內核。
宇宙 scheme 與互歸納是可檢查的編譯/方案層，不是 AST 內一等宇宙多態
宣告語言；未以 `DPositiveFunctor` 表示的不透明型別算子仍保守拒絕。
未經 checked 入口的宿主型別線不自動尊重代換；原始 BDD 對某些函數
有指數下界，預算耗盡會誠實回報未決定。精確代數的 `Int32` 係數在
大型輸入仍可溢出，Jordan 分解不自動構造分裂域；原 `Double` 層是
近似診斷，精確結論屬於 `QuadC` 影子。細節見 `SPEC.md` 第四節。

<details>
<summary><b>English</b></summary>

This is an **executable model / specification** of the theory fragment, not a
production cubical kernel. Universe schemes and mutual induction are checkable
compilation/scheme layers, not a first-class universe-polymorphic declaration
language inside the AST; opaque type operators not represented by
`DPositiveFunctor` are still rejected conservatively. Host type lines that do not
pass through the checked entry points do not automatically respect
substitution; raw BDDs have exponential lower bounds for some functions, and
budget exhaustion honestly reports "undecided". `Int32` coefficients in the
exact algebra can still overflow on large inputs, and Jordan decomposition does
not construct splitting fields automatically; the original `Double` layer is
approximate diagnostics, and exact conclusions belong to the `QuadC` shadow.
See `SPEC.md` §4 for details.

</details>

