# 架構、依賴次序與打包方式 · Architecture, dependency order and packaging

> 🔀 **切換 / Toggle**：每一節先列中文，英文收在 <kbd>English</kbd> 摺疊區內 —— 在 GitHub／預覽器上按一下 `<summary>` 就是「撳掣」切換。
> Each section is Chinese first, with English behind a `<details>` button.
>
> 本文所有數字由 `python3 tools/arch_report.py` 從源碼靜態算出（可重跑）。
> All numbers below are produced by `python3 tools/arch_report.py` (re-runnable).

---

## 0. 摘要 · TL;DR

| 問題 | 結論 |
|---|---|
| 60 多個源碼檔該怎麼分層？ | 56 個庫檔案（33,600 行、1,468 個公共符號）分成 **13 層（L0–L12）**：數值／面幾何 → BDD／NbE → 立方體與有限宇宙 → 依賴內核 → 全型別 Kan → schema 擴展 → 定律 → 驗收。解耦後層數比之前多（7 → 13），因為循環被移除後每層只依賴下一層 |
| 先後依賴怎麼定？ | 以 **L0 → L12** 為建置／閱讀次序；跨層只可「高層引用低層」 |
| 用閉包還是 `.pkg` 架設？ | **兩者不是同一層次的問題**：`.pkg` 是「編譯單元與可見性邊界」（一目錄一 package、檔名無作用域、要 `pub` 才導出），閉包是「值的表示方式」（`Cube.cell`、`DLine`、HOAS 是 NbE 的必要手段）。解耦後只剩 1 個必要循環，故：**核心維持單一 package，面幾何與精確代數可切包** |
| 已經做了什麼？ | 用可計算單值性作認證工具，把 **6 個循環中的 5 個解掉**（6 → 1），只保留「型別論 ⇄ 元程式」那一個必要循環；介面 0 個符號遺失（見 §8 與 `REFACTORING.md`） |
| 下一步？ | `face_core`＋`interval`＋`bdd`＋`bdd_dag` 已成無環鏈，可整段抽成 `mesh` 包；`algexact` 系列本來就無環，可直接抽 |

<details>
<summary><b>English</b></summary>

| Question | Conclusion |
|---|---|
| How to layer ~60 source files? | The 56 library files (33,600 lines, 1,468 public symbols) form **13 layers (L0–L12)**: numeric/face geometry → BDD/NbE → cubes and the finite universe → the dependent kernel → Kan for all types → schema extensions → laws → acceptance. There are more layers than before (7 → 13) because, once the cycles are gone, each layer really does depend only on the one below. |
| What is the dependency order? | Build and read in **L0 → L12**; an edge may only point from a higher layer to a lower one. |
| Closures or `.pkg`? | **These are different axes.** A `.pkg` is a *compilation unit and visibility boundary* (a directory is a package, file names carry no scope, only `pub` exports); a closure is a *representation of a value* (`Cube.cell`, `DLine`, HOAS are what NbE needs). After the surgery only one essential cycle remains, so the kernel stays one package while face geometry and exact algebra can be extracted. |
| What has been done? | Using computable univalence as the certification tool, **5 of the 6 cycles are gone** (6 → 1); only the type-theory ⇄ metaprogramming cycle is kept, and no exported symbol was lost (see §8 and `REFACTORING.md`). |
| Next step? | `face_core` + `interval` + `bdd` + `bdd_dag` is now an acyclic chain and can be extracted as a `mesh` package; the `algexact` family is already acyclic and can be extracted as is. |

</details>

---

## 1. 清點 · Inventory

| 指標 | 值 |
|---|---|
| `.mbt` 檔案 | **75**（庫 56／測試 19） |
| 總行數 | **34,313**（庫 33,600） |
| 公共符號（原始碼宣告） | **1,468** |
| 公共符號（`pkg.generated.mbti`，含欄位與構造子） | **2,339** |
| 規格族（`SPEC.md` 附錄） | **54** |
| 白箱測試 | **55** 個 case、`moon run cmd/main` **43/43** |
| 最大檔案 | `schema.mbt` 4,117 行、`nbe_dep.mbt` 3,561、`hou_elaborator.mbt` 1,323、`schema_functor.mbt` 1,230 |

<details>
<summary><b>English</b></summary>

75 `.mbt` files (56 library, 19 test), 34,313 lines (33,600 library), 1,468 public declarations, 2,339 public symbols in `pkg.generated.mbti` (including fields and constructors), 54 specification families, 55 white-box test cases and 43/43 registered theorems. Largest files: `schema.mbt` (4,117), `nbe_dep.mbt` (3,561), `hou_elaborator.mbt` (1,323), `schema_functor.mbt` (1,230).

</details>

---

## 2. 分層架構 · The layers

層數 = 「最長依賴鏈深度」：L0 不引用任何其他檔案，L*n* 只引用 ≤ L(*n*−1) 的檔案。解耦手術之後 DAG 由 6 個循環壓成 1 個，**深度由 7 增到 13** —— 這是預期而且健康的：循環會把層數「壓扁」，把循環解掉之後每一層才真正只依賴下一層。

| 層 | 檔案 | 職責 |
|---|---|---|
| **L0** | `algebraic_laws` `bdd_certified_laws` `complex` `equiv_laws` `finite_universe` `nbe` `phase6_infrastructure_laws` `spec` `symalg` | 代數定律；BDD 認證定律；複數底座；等價定律；有限宇宙 `Ty` / `PVal`；未型別 NbE（含 `LTy`，故在 L0）；第六期基礎定律；規格登記（逐符號家族的機器可讀清單）；對稱代數／多項式底座 |
| **L1** | `interval` `nbe_eta` `projector` `qpoly` `spectral_symbolic` `wiring` | De Morgan 區間求值（`dmin/dmax/eval_dim*`）；型別化 η NbE；正交投影；單變量多項式；譜代數；wiring（Glue 的接線） |
| **L2** | `examples` `face_core` `qmat` | 跨層共用範例（投影、單位、網格、取樣向量）；面語法：`Dim/Face/Bdd` 宣告、化簡、代換、邊界、`face_holds`；有理矩陣 |
| **L3** | `Jacobi_interval` `Jordan` `algnum` `bdd_dag` `cube` `system_core` | 認證 Jacobi 方法；Jordan 分解；代數擴張數；ROBDD DAG 與節點表；`VecBranch/VecSystem` 資料型別 |
| **L4** | `bdd` `certified_numeric` `cube_algorithm` | 面的符號判定（`face_sat/unsat/le/eq_mod`）；認證數值影子；n 維立方體演算法（Möbius 填充） |
| **L5** | `categories` `pathp_glue` `system_symbolic` | 範疇化總檢；有限宇宙 `ua` / `Glue`；系統符號範形 |
| **L6** | `glue_comp` `system` `univalence_compute` | 一般 `Glue` comp；系統商與特徵空間剪枝；可計算單值性（判定程序） |
| **L7** | `dsystem_compat` `equiv_ast` `kan_ast` `nbe_dep` `refactor_certificate` `schema` `schema_functor` `schema_registry` | 依賴系統相容層；等價 AST；Kan 的 AST；依賴 NbE；**重構證書**（介面等價 / ua 路徑）；schema（型別即描述子）；schema 函子；schema 登記 |
| **L8** | `checked_line` `dterm_transform` `kan_dep` `schema_positivity` `sphere3` | 受檢查線；項變換；全型別 Kan；正性檢查；S³ |
| **L9** | `ast_laws` `schema_extensions` | AST 定律；互歸納／商／宇宙 scheme |
| **L10** | `dsystem_compat_laws` `hou_elaborator` `module_system` `schema_extension_laws` `schema_laws` | 依賴系統相容定律；HOU elaborator；參數化模組系統；schema 擴展定律；schema 定律 |
| **L11** | `semantic_system_laws` | 語義系統／持久環境／惰性定律 |
| **L12** | `verify` | 定理登記與驗收 |

> 注：本表由 `python3 tools/arch_report.py` 直接算出（每層＝檔案級凝縮圖上的最長路徑深度），故與工具輸出必然一致。`_wbtest.mbt` 不入圖（它們只依賴被測檔案）。

## 3. 依賴圖 · Dependency graph

### 3.1 分層示意（解耦後）

```text
L12 verify
L11 semantic_system_laws
L10 dsystem_compat_laws · hou_elaborator · module_system · schema_extension_laws · schema_laws
L9  ast_laws · schema_extensions
L8  checked_line · dterm_transform · kan_dep · schema_positivity · sphere3
L7  dsystem_compat · equiv_ast · kan_ast · nbe_dep · refactor_certificate · schema · schema_functor · schema_registry   ← 唯一循環（必要）
L6  glue_comp · system · univalence_compute
L5  categories · pathp_glue · system_symbolic
L4  bdd · certified_numeric · cube_algorithm
L3  Jacobi_interval · Jordan · algnum · bdd_dag · cube · system_core
L2  examples · face_core · qmat
L1  interval · nbe_eta · projector · qpoly · spectral_symbolic · wiring
L0  algebraic_laws · bdd_certified_laws · complex · equiv_laws · finite_universe · nbe · phase6_infrastructure_laws · spec · symalg
```

主要骨幹 / the main spine:

```text
面幾何 / faces    complex ← interval ← face_core ← bdd_dag ← bdd ← {cube, system, pathp_glue}
宇宙 / universe   finite_universe ← pathp_glue ← univalence_compute ← refactor_certificate
內核 / kernel     cube ← cube_algorithm ← kan_dep ← schema_extensions ← schema_laws ← verify
```

<details>
<summary><b>English</b></summary>

After the surgery the graph is acyclic except the kernel, and the longest chain is
13 ranks deep (0–12) instead of 7: cycles *flatten* a layering, so removing them
necessarily deepens it. `verify` sits on top (it is the acceptance layer);
`categories` is at rank 5, since it now only needs the shared `examples`;
`nbe_dep`/`schema`/`schema_functor`/`schema_registry`/`kan_ast`/`equiv_ast`/
`dsystem_compat` form the one deliberate SCC (and `refactor_certificate` lands at
the same rank because it consumes `univalence_compute`), and the floor is
`complex`, `symalg`, `nbe`, `finite_universe`, `spec` and the `*_laws` units.
Note the spine: `complex ← interval ← face_core ← bdd_dag ← bdd ← cube`, and
`finite_universe ← pathp_glue ← univalence_compute ← refactor_certificate`.

</details>

### 3.2 完整檔案邊（`A -> B` 表示 A 引用 B 的公共符號）

<details>
<summary><b>English</b> (the full edge list is generated; expand to see how to reproduce)</summary>

The complete edge list is emitted by `python3 tools/arch_report.py` (section “file dependencies”). Key edges in the new modules: `cube_algorithm.mbt -> complex.mbt, cube.mbt`; `univalence_compute.mbt -> cube.mbt, pathp_glue.mbt`; `verify.mbt -> …, cube_algorithm.mbt, univalence_compute.mbt, …`.

</details>

| 檔案 | 層 | 依賴（引用其公共符號） |
|---|---|---|
| `algebraic_laws` | 0 | — |
| `bdd_certified_laws` | 0 | — |
| `complex` | 0 | — |
| | 0 | — |
| `equiv_laws` | 0 | — |
| `finite_universe` | 0 | — |
| `nbe` | 0 | — |
| `phase6_infrastructure_laws` | 0 | — |
| `spec` | 0 | — |
| `symalg` | 0 | — |
| `interval` | 1 | `complex` |
| `nbe_eta` | 1 | `complex`, `nbe` |
| `projector` | 1 | `complex` |
| `qpoly` | 1 | `symalg` |
| `spectral_symbolic` | 1 | `symalg` |
| `wiring` | 1 | `finite_universe` |
| `examples` | 2 | `complex`, `projector` |
| `face_core` | 2 | `interval` |
| `qmat` | 2 | `complex`, `qpoly`, `symalg` |
| `Jacobi_interval` | 3 | `qmat`, `qpoly`, `symalg` |
| `Jordan` | 3 | `projector`, `qmat`, `qpoly`, `symalg` |
| `algnum` | 3 | `complex`, `qmat`, `qpoly`, `symalg` |
| `bdd_dag` | 3 | `face_core` |
| `cube` | 3 | `complex`, `examples`, `projector` |
| `system_core` | 3 | `complex`, `face_core` |
| `bdd` | 4 | `bdd_dag`, `face_core` |
| `certified_numeric` | 4 | `algnum`, `complex`, `symalg` |
| `cube_algorithm` | 4 | `complex`, `cube` |
| `categories` | 5 | `bdd`, `complex`, `cube`, `examples`, `face_core`, `nbe`, `nbe_eta`, `projector` |
| `pathp_glue` | 5 | `bdd`, `face_core`, `finite_universe`, `wiring` |
| `system_symbolic` | 5 | `bdd`, `complex`, `face_core`, `system_core` |
| `glue_comp` | 6 | `bdd`, `complex`, `cube`, `face_core`, `pathp_glue`, `projector` |
| `system` | 6 | `bdd`, `complex`, `face_core`, `system_core`, `system_symbolic` |
| `univalence_compute` | 6 | `cube`, `finite_universe`, `pathp_glue` |
| `dsystem_compat` | 7 | `bdd`, `face_core`, `interval`, `kan_ast`, `nbe`, `nbe_dep`, `system` |
| `equiv_ast` | 7 | `face_core`, `interval`, `kan_ast`, `nbe_dep`, `system` |
| `kan_ast` | 7 | `bdd`, `equiv_ast`, `face_core`, `interval`, `nbe_dep`, `schema` |
| `nbe_dep` | 7 | `bdd`, `complex`, `dsystem_compat`, `equiv_ast`, `face_core`, `interval`, `kan_ast`, `nbe`, `projector`, `schema`, `schema_functor`, `system` |
| `refactor_certificate` | 7 | `finite_universe`, `univalence_compute` |
| `schema` | 7 | `complex`, `face_core`, `interval`, `kan_ast`, `nbe_dep`, `schema_functor`, `schema_registry` |
| `schema_functor` | 7 | `complex`, `nbe_dep`, `schema`, `schema_registry`, `system` |
| `schema_registry` | 7 | `nbe_dep`, `schema` |
| `checked_line` | 8 | `interval`, `kan_ast`, `nbe_dep` |
| `dterm_transform` | 8 | `nbe_dep` |
| `kan_dep` | 8 | `cube`, `finite_universe`, `glue_comp`, `nbe`, `nbe_dep`, `pathp_glue` |
| `schema_positivity` | 8 | `nbe_dep`, `schema` |
| `sphere3` | 8 | `interval`, `kan_ast`, `nbe_dep`, `schema`, `schema_registry` |
| `ast_laws` | 9 | `cube`, `face_core`, `interval`, `kan_ast`, `kan_dep`, `nbe_dep` |
| `schema_extensions` | 9 | `dterm_transform`, `interval`, `nbe_dep`, `schema`, `schema_registry` |
| `dsystem_compat_laws` | 10 | `ast_laws`, `bdd`, `dsystem_compat`, `interval`, `nbe`, `nbe_dep`, `system` |
| `hou_elaborator` | 10 | `ast_laws`, `complex`, `nbe_dep` |
| `module_system` | 10 | `ast_laws`, `equiv_ast`, `nbe_dep`, `schema` |
| `schema_extension_laws` | 10 | `ast_laws`, `kan_ast`, `nbe_dep`, `schema`, `schema_extensions`, `schema_functor`, `schema_positivity`, `schema_registry` |
| `schema_laws` | 10 | `ast_laws`, `kan_ast`, `nbe_dep`, `schema`, `schema_registry` |
| `semantic_system_laws` | 11 | `ast_laws`, `bdd`, `dsystem_compat_laws`, `face_core`, `kan_ast`, `nbe`, `nbe_dep` |
| `verify` | 12 | `Jacobi_interval`, `algebraic_laws`, `ast_laws`, `bdd`, `bdd_certified_laws`, `categories`, `complex`, `cube`, `cube_algorithm`, `dsystem_compat_laws`, `equiv_laws`, `examples`, `face_core`, `glue_comp`, `hou_elaborator`, `interval`, `kan_dep`, `module_system`, `nbe`, `nbe_dep`, `nbe_eta`, `pathp_glue`, `phase6_infrastructure_laws`, `projector`, `refactor_certificate`, `schema_extension_laws`, `schema_laws`, `semantic_system_laws`, `spec`, `spectral_symbolic`, `sphere3`, `system`, `univalence_compute`, `wiring` |

<details>
<summary><b>English</b></summary>

`verify.mbt` is the acceptance layer: fan-out 34, fan-in 0. The floor files have no outgoing edges at all (`complex`, `symalg`, `finite_universe`, `spec`, `nbe`, the `*_laws` unit files); the most depended-upon files are `nbe_dep` (20), `complex` (19), `face_core` (16), `interval` (12), `bdd` (11). The kernel hubs have the largest fan-in *and* the only cycles.

</details>

---

## 4. 循環：六個 → 一個 · Cycles: six → one

同一個 package 內檔案可以互相引用（MoonBit 沒有檔案序問題），所以循環本身合法；問題是它們**決定了哪裡不能切 `.pkg`**，而且把層數壓扁成 7 層，令「上一層只依賴下一層」這個不變式失效。手術的原則：**只解「佈局意外」（同一組概念被拆散在兩處），保留「翻譯必要」（兩個概念的互譯本身）。**

| # | 循環 | 成因 | 判定 | 處置 |
|---|---|---|---|---|
| C1 | `interval ⇄ bdd ⇄ bdd_dag` | 面的**語法**（`Dim/Face/simplify/subst`）與面的**判定**（ROBDD）放在同一批檔案，兩邊互用 | 不必要 | ✅ 抽出 `face_core.mbt`（語法＋`Bdd` 宣告，L2）；`face_sat/le/eq_mod/unsat` 歸 `bdd.mbt`。鏈變成 `complex ← interval ← face_core ← bdd_dag ← bdd`（`bdd` 只再向下） |
| C2 | `nbe ⇄ nbe_eta` | `LTy`（型別）留在 η 層，而 βπ 層要用它 | 不必要 | ✅ `LTy` 上移 `nbe.mbt`；`nbe_eta` 只依賴 `nbe` |
| C3 | `pathp_glue ⇄ wiring` | 有限宇宙的 `Ty/PVal` 由 ua 層擁有，但 wiring 是最基層的等價範形 | 不必要 | ✅ 抽出 `finite_universe.mbt`（L0），兩者都只依賴它 |
| C4 | `system ⇄ system_symbolic` | `VecSystem` 的**資料型別**在商／剪枝檔，符號層卻要命名它 | 不必要 | ✅ 抽出 `system_core.mbt`（資料型別），`system` 呼叫符號比較、`system_symbolic` 只讀型別 |
| C5 | `nbe_dep ⇄ schema ⇄ schema_functor ⇄ schema_registry`（＋`kan_ast`/`equiv_ast`/`dsystem_compat`） | 型別同時是「語義值」與「schema 描述子」：`DTerm/DValue/DEnv` 被 `schema` 用，`DInductiveSpec/DHitSpec` 被 `nbe_dep` 用 | **必要** | ⛔ 保留。切開要引入兩份 mirror 型別＋一層 interface package，是把耦合換成重複 |
| C6 | `verify ⇄ categories/kan_dep` ＋ `*_laws` | 驗收層同時擁有「範例資料」與「被檢查者」 | 不必要 | ✅ 範例下沉 `examples.mbt`（L2）；`check_cube_comp` 歸 `cube.mbt`。`verify` 回到純彙總 |

**量度**（`python3 tools/refactor_audit.py`，基線取 `git HEAD`）：

```text
循環 before 6 → after 1        消除 5 個，僅保留 C5
符號 before 1430 → after 1541  遺失 0、新增 111（三個新模組）
搬遷 8 組、共 37 個公共宣告     見 §8 表
moon test 55/55 · cmd/main 43/43 · audit 2,339 符號
```

<details>
<summary><b>English</b></summary>

Inside one package, files may reference each other freely, so a cycle is legal;
what it really decides is *where a package boundary cannot be drawn*, and it also
flattens the layering so that "a layer only depends on the one below" stops
holding. The rule used for the surgery: **break only layout accidents (one
concept split over two files), keep translations (where the mutual reference
*is* the content).**

C1 (face syntax vs face decision), C2 (`LTy` stranded in the η layer), C3 (the
finite universe owned by the ua layer), C4 (`VecSystem`'s data type living in the
quotient file) and C6 (the acceptance layer also owning the example data) are
layout accidents and were fixed by extracting `face_core.mbt`,
`finite_universe.mbt`, `system_core.mbt` and `examples.mbt` and by re-homing four
decisions and one check. C5 — where types are simultaneously semantic values and
schema descriptors — is a translation and is kept: cutting it would replace
coupling with duplicated mirror types.

Measured with `python3 tools/refactor_audit.py` (baseline `git HEAD`): cycles
6 → 1, symbols 1430 → 1541 with **0 lost**, 8 move groups, 37 public declarations
relocated; `moon test` 55/55, `cmd/main` 43/43, audit 2,339 symbols.

</details>

---

## 5. 建置／閱讀次序 · Build and reading order

MoonBit 由 `moon.pkg` 決定編譯單元，同一 package 內檔案次序無關；下表是**概念次序**，也是新讀者／新貢獻者的最佳進入路徑，亦是未來切包時的切割線。

| 階段 | 內容 | 驗收 |
|---|---|---|
| **S0 底座** | `complex` → `symalg` → `interval` → `face_core` → `bdd_dag` → `bdd` | `moon test`：投影、BDD 範形 |
| **S1 幾何** | `projector` → `cube` → **`cube_algorithm` （n 維填充）** | `check_cube_comp`、`check_cube_algorithm` |
| **S2 有限宇宙** | `finite_universe` → `wiring` → `pathp_glue` → **`univalence_compute`** → **`refactor_certificate`** | `check_ua_coe`、`check_univalence`、`重構證書：解耦手術是介面等價` |
| **S3 NbE** | `nbe` → `nbe_eta` → `nbe_dep` | `check_nbe`、`check_eta_all`、`check_dep_all` |
| **S4 立方 AST 與 Kan** | `kan_ast` → `equiv_ast` → `glue_comp` → `kan_dep` → `checked_line` | `check_ast_*`、`check_kan_all_types` |
| **S5 Schema 與 HIT** | `schema` → `schema_functor` → `schema_positivity` → `schema_registry` → `schema_extensions` → `sphere3` | `check_mutual_*`、`check_tarski_*`、`check_sphere3` |
| **S6 代數** | `qpoly` → `qmat` → `algnum` → `Jordan` → `spectral_symbolic` → `certified_numeric` → `Jacobi_interval` | `check_symbolic_algebra_all`、`check_algebraic_extensions_and_Jordan`、`check_Jacobi_interval` |
| **S7 外層** | `dsystem_compat` → `hou_elaborator` → `module_system` → `*_laws` → `categories` → `verify` → `cmd/main` | `moon test`（55）、`moon run cmd/main`（43/43）、`python3 tools/audit_spec.py --check`（2,339 符號） |

<details>
<summary><b>English</b></summary>

`moon.pkg` fixes the compilation unit; file order inside a package is irrelevant. The table is the *conceptual* order — the best entry path for a new reader or contributor, and the future cutting lines for package extraction.

S0 floor: `complex` → `symalg` → `interval` → `face_core` → `bdd_dag` → `bdd`. S1 geometry: `projector` → `cube` → `cube_algorithm` (n-dimensional filling). S2 finite universe: `finite_universe` → `wiring` → `pathp_glue` → `univalence_compute` → `refactor_certificate` (the ua path applied to the interface itself). S3 NbE: `nbe` → `nbe_eta` → `nbe_dep`. S4 cubical AST and Kan: `kan_ast` → `equiv_ast` → `glue_comp` → `kan_dep` → `checked_line`. S5 schemas and HITs: `schema` → `schema_functor` → `schema_positivity` → `schema_registry` → `schema_extensions` → `sphere3`. S6 algebra: `qpoly` → `qmat` → `algnum` → `Jordan` → `spectral_symbolic` → `certified_numeric` → `Jacobi_interval`. S7 outer shell: `dsystem_compat` → `hou_elaborator` → `module_system` → `*_laws` → `categories` → `verify` → `cmd/main`, accepted by `moon test` (55), `moon run cmd/main` (43/43) and `python3 tools/audit_spec.py --check` (2,339 symbols).

</details>

---

## 6. 用閉包，還是用 `.pkg`？ · Closures or `.pkg`?

### 6.1 兩個概念不在同一層次

* **`.pkg`（封裝邊界）**：MoonBit 以「目錄 + `moon.pkg`」為一個 package，目錄內所有 `.mbt` **共用一個命名空間、沒有檔案作用域**，宣告可自由在檔案間搬動 [1](https://docs.moonbitlang.com/en/latest/language/packages.html)[9](https://docs.moonbitlang.com/en/latest/toolchain/moon/package-manage-tour.html)。跨 package 只可經 `moon.pkg` 的 `import`，並以 `@alias` 存取；預設一切 `fn`/`let` 對外**不可見**，要 `pub` 才導出 [2](https://docs.moonbitlang.com/en/latest/language/packages.html)。它有 `for "test"` / `for "wbtest"` 兩組測試專用導入 [1](https://docs.moonbitlang.com/en/latest/toolchain/moon/package.html)。
* **閉包（值的表示）**：`Cube.cell : (Array[Double]) -> CVec`、`DLine{at, coe, fill}`、HOAS 的 `HTm` 都是「把宿主函數放進語義域」的技術 —— 這是 **NbE/HOAS 的必要手段**（環境、閉包族、惰性 thunk），與「代碼放哪個目錄」無關。

所以問題不是二選一，而是：**架構邊界用 package 表達；值的表示用閉包表達。** 混用（例如「用閉包當模組系統」）會失去 `moon info` 的介面審計、失去 `_wbtest` 私有訪問、也讓 `audit_spec.py` 無法逐符號登記。

### 6.2 對本專案的三條硬約束（來自實測）

1. **package 依賴必須無環。** 手術前有 6 組循環；解掉 5 組之後只剩 C5（`nbe_dep ⇄ schema ⇄ schema_functor …`，23 個符號／5 個檔案），而它是「型別論 ↔ 元程式」的互譯，**不應斷**。故核心仍須留在同一 package；但**面幾何、代數兩段已可切包**（見 6.3）。
2. **白箱測試需要同 package。** 19 個 `_wbtest.mbt`／`test` 檔案依賴私有符號與手寫定律；一拆包就要全部改寫成黑箱或改可見性 [3](https://docs.moonbitlang.com/en/latest/language/tests.html)。
3. **閉包不可跨 package 傳遞語義不變式。** `Cube.cell` 是宿主函數，`audit_spec.py` 與 `moon info` 看得到的只是型別；一旦跨包，`nbox_wf` 這類「結構性檢查」就無法在邊界上強制執行。留在同 package 內，`nfill_respects_box` 才能對任意建構出來的 box 都成立。

### 6.3 結論與落地

| 方案 | 判定 | 理由 |
|---|---|---|
| 全部拆成多個 `.pkg`（按層切） | ❌ | 仍會撞上 C5，且要改寫 19 個測試檔 |
| 全部留在單一 package，用檔案命名分層 | ✅ **現行建議** | 零風險、保留全部測試與審計；`ARCHITECTURE.md` 的層表即是「軟邊界」 |
| 單一 package ＋ 抽出 2 個無環葉子包 | ✅ **已解鎖**（手術完成） | 見下；`mesh/` 與 `algexact/` 現在都是無環的 |
| 用閉包／trait 當模組系統（動態注入依賴） | ❌ | 失去靜態可見性、`moon info` 介面與 `--check` 審計；只在需要「多個 Kan 引擎」時才值得 |

**可抽出的葉子包（手術後皆為無環）**

```text
mesh/          face_core.mbt  interval.mbt  bdd_dag.mbt  bdd.mbt      ← C1 已斷，鏈 face_core←bdd_dag←bdd
algexact/      complex.mbt  symalg.mbt  qpoly.mbt  qmat.mbt  algnum.mbt
               Jordan.mbt  spectral_symbolic.mbt  certified_numeric.mbt  Jacobi_interval.mbt
（根目錄）     cubical-hermitian ← 其餘全部，只餘 C5 一個循環
```

每個 package 的 `moon.pkg` 只需 `import { "…/mesh" @mesh, "…/algexact" @alg }`；`finite_universe.mbt`（`Ty/PVal`）已獨立成 L0 檔，跟 `mesh` 一起搬或留在根部都無環。

抽出後 `moon.pkg` 只需寫：

```text
import { "username/cubical-hermitian/mesh" @mesh,
         "username/cubical-hermitian/algexact" @alg }
```

而 `finite_universe.mbt`（`Ty`/`PVal`）若要再拆 C3，可放進 `mesh`（同 L0）並由核心 import。

<details>
<summary><b>English</b></summary>

**Two different axes.** A `.pkg` is a *compilation unit and visibility boundary*: a package is a directory plus `moon.pkg`, all `.mbt` files in it share one namespace with no file scope, declarations move between files freely, and cross-package access requires `import` in `moon.pkg` plus `@alias`; by default nothing is visible outside, `pub` exports it. A closure is a *representation of a value*: `Cube.cell`, `DLine{at, coe, fill}`, and HOAS `HTm` put host functions into the semantic domain — a necessity for NbE/HOAS (environments, closure families, lazy thunks), unrelated to where code lives.

So the question is not either/or: **express architectural boundaries with packages; express value representations with closures.** Using closures as a module system would lose `moon info` interface auditing, private white-box access, and per-symbol registry checks.

**Three hard constraints, measured on this repository.** (1) Package dependencies must be acyclic; after the surgery only C5 remains (`nbe_dep ⇄ schema ⇄ schema_functor`, 23 symbols across 5 files), the type-theory ↔ metaprogramming mutual translation, which *should not* be cut — so the kernel stays one package (the acyclic face/geometry and exact-algebra chains can be extracted, see §6.3). (2) White-box tests need the same package: 19 `_wbtest.mbt`/test files reach private definitions and hand-written laws. (3) Closures cannot carry semantic invariants across packages: `Cube.cell` is a host function, so `nbox_wf`/`nfill_respects_box` can only be enforced inside one package.

**Decision table.** Splitting everything by layer ❌ (C5 would remain, and 19 test files would have to be rewritten). One package with file-level layering ✅ *current recommendation* (zero risk, keeps every test and audit; the layer table is the soft boundary). One package plus two acyclic leaves ✅ *unlocked by the surgery*: a `mesh/` package (`complex` → `interval` → `face_core` → `bdd_dag` → `bdd`, now one chain) and an `algexact/` package (already acyclic, depends only on `complex`). Closures/traits as a module system ❌ (loses static visibility, `moon info`, and the audit) — worth it only if you need swappable multiple Kan engines.

</details>

---

## 7. 如何重跑分析 · Reproducing the analysis

```text
python3 tools/arch_report.py                    # 分層表 + 檔案邊 + 循環
python3 tools/arch_report.py --mermaid          # Mermaid 圖（給 GitHub 用）
python3 tools/arch_report.py --json arch.json   # 機器可讀
moon info && moon test && moon run cmd/main     # 介面、測試、定理表
python3 tools/audit_spec.py --check             # 逐符號規格審計
python3 tools/refactor_audit.py --md REFACTORING.md   # 重構審計：介面雙射＋循環變化
python3 tools/move_decls.py NAME… --from A.mbt --to B.mbt  # 機械搬遷（本次手術所用）
```

<details>
<summary><b>English</b></summary>

`refactor_audit.py` rebuilds the *before* graph from `git show HEAD:<file>` and the *after* graph from the working tree, decides the bijection of the exported symbol sets (the same procedure univalence uses) and compares the SCC counts. `move_decls.py` moves `///|` blocks by declaration name, which is how the eight moves of §8 were performed.

`arch_report.py` parses every `.mbt` file, takes the *public* symbols (unique across the package, as `moon info` guarantees) as graph nodes, records for every `///|` block which other files' public symbols it mentions, condenses strongly connected components (mutual recursion inside a package is legal), and assigns each file a layer = longest path in the file-level condensation. Output: a layer table, the file edge list, the file-level cycles, and optionally Mermaid or JSON.

</details>

---

## 8. 用單值性做重構 · Refactoring with univalence

### 8.1 方法

重構的正當性通常靠「應該冇影響」；這裡把它變成**可判定**的命題：

1. **介面 = 有限符號集。** 一個 package 的 `.mbti` 就是一個有限的符號集（本專案 2,339 個），所以它是 `univalence_compute.mbt` 意義下的有限型別。
2. **重構 = 符號集之間的映射。** 把宣告由 `A.mbt` 搬到 `B.mbt`，令 `before = A∪B` 的有序宣告列、`after = B∪A` 的有序宣告列；映射不是置換就代表有符號被吞掉或憑空出現。
3. **判定 = `fin_map_is_equiv`。** `refactor_certificate.mbt` 把索引表補齊到 2 的冪（`next_pow2`），用 `ty_of_bits` 造出大小相同的有限型別 `Ty`，再交給單值性的判定程序（`plan_agrees_with_univalence`）；於是「重構無損」與「`A ≃ B`」是同一支演算法。
4. **證書 = ua 路徑。** `certify` 對等價的重構給出路徑；任何逐符號判定（規格族編號、層號、審計分類）沿路徑 **coe** 搬運（`certificate_transport_int`），往返為恆等（`certificate_transport_roundtrip`），複合是路徑複合（`certificate_compose`，即 ua 函子性）。丟失符號、靜默改名、非置換表一律拒絕。
5. **耦合 = 圖論量度。** 檔案級依賴圖的強連通分量數目，手術前後各算一次（`tools/refactor_audit.py`）。

三者一起構成「重構證明」的三段式：**介面守恆（等價）＋ 判定可搬運（ua）＋ 耦合減少（SCC 6 → 1）**。

### 8.2 手術清單（8 次搬遷、37 個公共宣告）

| 步驟 | 由 | 到 | 符號 | 效果 |
|---|---|---|---|---|
| C2 | `nbe_eta.mbt` | `nbe.mbt` | `LTy` | βπ 層不再依賴 η 層 |
| C3 | `pathp_glue.mbt` | `finite_universe.mbt` | `PVal`, `Ty` | wiring 與 ua 層並列於有限宇宙之上 |
| C4 | `system.mbt` | `system_core.mbt` | `VecBranch`, `VecSystem` | 符號層只讀型別，不再回指商／剪枝 |
| C1a | `interval.mbt` | `face_core.mbt` | `Face`, `face_holds`, `face_var0/1`, `pow2`, `assignment_of_mask` | 面語法下沉 |
| C1b | `bdd.mbt` | `face_core.mbt` | `Bdd`, `dim_/face_simplify`, `dim_/face_subst`, `face_bound`, `face_vars`, `sort_ints`, `contains_int`, 兩個私有走訪器 | DAG 與樹形 BDD 都只依賴語法 |
| C1c | `interval.mbt` | `bdd.mbt` | `face_sat`, `face_unsat`, `face_le`, `face_eq_mod` | 判定歸判定層 |
| C6a | `verify.mbt` | `examples.mbt` | `example_projector`, `example_unit`, `vec_e3`, `grid`, `inv_sqrt2`, `sample_vectors` | 範例下沉，`categories` 不再依賴驗收層 |
| C6b | `verify.mbt` | `cube.mbt` | `check_cube_comp` | `kan_dep` 不再依賴驗收層 |

### 8.3 驗證

```text
moon test                              55/55            （新增 6 個證書測試）
moon run cmd/main                      43/43            （新增「重構證書」一條）
python3 tools/audit_spec.py --check    2339 符號 / 54 族
python3 tools/refactor_audit.py        介面 0 遺失、循環 6 → 1
diff <(git show HEAD:pkg.generated.mbti) pkg.generated.mbti   逐一相同，只有新增／刪除
```

其後另有一輪**死碼清理**：刪除 65 個「package 內、19 個測試、`cmd/main`、`spec.mbt` 全都
沒有引用」的公共宣告（清單在 `tools/dead_code_removed.txt`，可重跑 `tools/deadcode.py`
核對）。`refactor_audit.py` 會把這些「刻意刪除」與「意外遺失」分開報告，所以介面守恆
仍然是 **0 遺失**。

<details>
<summary><b>English</b></summary>

**Method.**

A refactor is usually justified by "it should not matter"; here it becomes a
decidable proposition.

1. **An interface is a finite symbol set.** The package's `.mbti` is a finite set
   (2,339 symbols here), i.e. a finite type in the sense of
   `univalence_compute.mbt`.
2. **A refactor is a map between symbol sets.** Moving declarations from `A.mbt`
   to `B.mbt` gives an ordered `before` listing and an ordered `after` listing;
   if the map is not a permutation, a symbol was swallowed or invented.
3. **The decision is `fin_map_is_equiv`.** `refactor_certificate.mbt` pads the
   index set to the next power of two, builds a `Ty` of that size with
   `ty_of_bits`, and hands it to the univalence decision procedure
   (`plan_agrees_with_univalence`), so "the refactor loses nothing" and "A ≃ B"
   are literally the same algorithm.
4. **The certificate is the ua path.** `certify` returns the path of an
   equivalence; per-symbol verdicts (specification family, layer, audit class)
   are transported along it by `certificate_transport_int`, the round trip is the
   identity, and composition is path composition (ua functoriality). A lost
   symbol, a silent rename, or a non-permutation table is rejected.
5. **Coupling is a graph measurement.** The number of strongly connected
   components of the file dependency graph, computed before and after by
   `tools/refactor_audit.py`.

Together: **interface preservation (equivalence) + transportable verdicts (ua) +
less coupling (SCC 6 → 1)**.

**The surgery — 8 moves, 37 public declarations.**

`LTy` up to `nbe`; `PVal`/`Ty` into `finite_universe`; `VecBranch`/`VecSystem`
into `system_core`; the face syntax and the tree-BDD declaration into
`face_core`; the four face decisions into `bdd`; the shared examples into
`examples`; `check_cube_comp` into `cube`. The one cycle that remains
(`nbe_dep ⇄ schema ⇄ schema_functor ⇄ schema_registry` and friends) is the
type-theory ⇄ metaprogramming translation and is deliberately kept.

**Verification.**

55/55 tests, 43/43 theorems, 2,339 symbols across 54 families, refactor audit
"0 lost, cycles 6 → 1". A second pass then deleted 65 public declarations that
had no reference anywhere (package, the 19 test files, `cmd/main`, `spec.mbt`);
the manifest `tools/dead_code_removed.txt` records them, so `refactor_audit.py`
still reports 0 accidental losses.

</details>
