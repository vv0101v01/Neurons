# cubical-hermitian 導覽（MoonBit 實作）

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
- `SPEC.md` 對全部型別、算子、規格、結構逐符號（2277 個、51 條規格）
  給出規範形式與範疇化。

## 運行與驗收

```text
moon test                              # 34 個白箱測試
moon run cmd/main                      # 40 項定理登記表，期望 40/40
python3 tools/audit_spec.py --check    # SPEC.md 附錄與介面集合相等
```

## 本次升級重點

### NbE 加 η（`nbe_eta.mbt`）

雙向型別檢查/求值；`quote_eta` 按型別產生 η 長範形：函數 `λx.f x`、積
`(fst p, snd p)`、Unit `()`。中性 spine 攜帶參數/姊妹型別，故
`f:(B→B)→B` 的範形是 `λg. f (λx. g x)`。積 η 令 `swap∘swap ≡ id` 在
函數層面定義成立。範疇化：物件 `LTy`、態射為項模 βπη 的自由笛卡兒閉範疇。

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

### 符號判定（`bdd.mbt`, `wiring.mbt`, `system_symbolic.mbt`）

- 面：ROBDD 為規範形，`sat/≤/≡/見證` 皆符號操作；
- 系統：有效區域 `φᵢ∧¬前覆蓋` 的 BDD 分割範形 `SystemNF`，商相等＝範形相等；
- 有限等價：wiring 帶號置換範形，wf 是 O(#葉) 置換性，合成是替換＋XOR，
  相等是結構相等。它同時是自由對稱冪冪範疇的態射（五邊形/三角形/六邊形
  相干律已驗）；
- 枚舉只留在 `*_extensional / *_oracle` 與白箱測試做差分校驗，不是判定路徑。

### 依賴 NbE：Π、Σ、宇宙（`nbe_dep.mbt`）

項與型別共用 `DTerm`；Π/Σ 的綁定後分量在語意域是閉包族，依賴代入
如 `snd p : B(fst p)` 直接計算。宇宙採累積 `Typeᵢ : Typeᵢ₊₁`。
轉換與範形由按型別的 `conv_at/quote_at`（含 η）與 `quote_ty` 給出；
範疇化為帶族範疇（CwF）句法模型。

### Kan coe/comp 全型別化（`kan_dep.mbt`）

型別線 `DLine{at,coe,fill}`，`comp=fill(1)`。Bool/Unit/Universe 是
常線；Π 在定義域反向 coe，Σ 沿第一分量路徑 coe 第二分量；依賴族
以「A 中路徑 → DLine」呈現。簡單型別與有限型別經非依賴嵌入，
有限 ua 是非恆常線；再加子空間線與 Glue，全專案型別族皆有 Kan 結構。

### 特徵值／投影／仿射填充的符號代數（`symalg.mbt`, `spectral_symbolic.mbt`）

以 Q 上多變量多項式範形與分式精確表示 `SymC/SymMat`，相等即多項式
恆等。譜投影用拉格朗日式 `Pₖ=qₖ(A)/qₖ(λₖ)`，幂等、正交、單位
分解與譜分解用首一整除及多項式恆等證明；`det(XI−A)` 給出特徵
多項式。仿射填充在雙線性類中由四角唯一決定，其係數差分公式與
邊界方程均在座標原子上以恆等式成立；投影剪枝滿足 `(I−P)(PF)=0`。

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
| 規格範形登記 | 51 條目＋2277 符號附錄＋審計 | `spec.mbt`, `SPEC.md`, `tools/audit_spec.py` |

## 檔案地圖

```text
complex.mbt / projector.mbt   C、向量、矩陣、伴隨；投影與特徵空間分解
interval.mbt / bdd.mbt        De Morgan 區間與面；面公式 ROBDD
system.mbt / system_symbolic.mbt  系統、相容性、剪枝；BDD 區域範形
cube.mbt                      立方體、面限制、開盒 comp、特徵空間剪枝
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
spec.mbt / verify.mbt         規格登記；40 項定理登記表
*_wbtest.mbt                  白箱測試（差分 oracle 只在這裡）
cmd/main/                     打印登記表的入口
```

## 範圍與邊界

這是該理論片斷的**可執行模型/規範**，不是完整生產級 cubical 內核。
宇宙 scheme 與互歸納是可檢查的編譯/方案層，不是 AST 內一等宇宙多態
宣告語言；未以 `DPositiveFunctor` 表示的不透明型別算子仍保守拒絕。
未經 checked 入口的宿主型別線不自動尊重代換；原始 BDD 對某些函數
有指數下界，預算耗盡會誠實回報未決定。精確代數的 `Int32` 係數在
大型輸入仍可溢出，Jordan 分解不自動構造分裂域；原 `Double` 層是
近似診斷，精確結論屬於 `QuadC` 影子。細節見 `SPEC.md` 第四節。
