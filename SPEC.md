# cubical-hermitian 規格書（SPEC）

本文件對專案中**所有型別、算子、結構與規格逐樣**給出：

- **規範形式（canonical / normal form）**：選定的標準代表，相等由比較規範形式判定；
- **範疇化（categorification）**：該物件所屬／所生成的範疇結構（物件、態射、函子、自然變換、萬有性或相干律）；
- **判定（decision）**：其主導等式或謂詞的演算法。

程式碼中的 `spec.mbt:spec_registry` 是本文件的條目級登記（51 條）。文末**附錄**由
`tools/audit_spec.py` 自 `pkg.generated.mbti`（`moon info` 產生的公共介面）生成，
逐一列出每個公共宣告、列舉構造子與結構欄位及其所屬規格族；審計以集合相等保證
附錄與介面**無遺漏、無重複、無虛列**。

驗收（在專案根目錄）：

```text
moon info && python3 tools/audit_spec.py --write   # 重新生成附錄並審計
python3 tools/audit_spec.py --check                # 只審計，不改檔
moon test && moon run cmd/main                     # 期望 34 個 tests 全過、定理 40/40
```

---

## 一、歷期升級的正式規格

### 1.1 NbE 加 η（`nbe_eta.mbt`）

**型別與規範形式。** 單型別語言 `LTy ::= Bool | Unit | LTy × LTy | LTy → LTy`。
正規形是 **η 長（η-long）βπ-正規形**：`quote_eta` 按型別讀回語義值，

| 型別 | η 規則 | 範形 |
|---|---|---|
| `A → B` | 函數 η：`f ≡ λx. f x` | 一律 λ 開頭，對新中性變量施用後在 `B` 讀回 |
| `A × B` | 積 η：`p ≡ (fst p, snd p)` | 一律配對開頭，兩投影分別在 `A`、`B` 讀回 |
| `Unit` | 單位 η：`u ≡ ()` | 一律 `TmUnit` |
| `Bool` | 無 η（基型別） | 字面量或中性 spine |

**中性 spine 的型別攜帶。** 為了在 stuck 項內部也能 η 展開（例如
`f:(B→B)→B` 的範形是 `λg. f (λx. g x)`），`TNeutral` 的應用節點存參數型別、
投影節點存姊妹分量型別；`quote_tneutral` 因此能在 spine 的每一個位置重建型別。

**雙向程序。** `ty_infer / ty_check` 是句法雙向判定；`eval_infer_t / eval_check_t`
是與之一一對應的雙向求值。未註記 λ 不可推斷，`TmAnn(t, τ)` 提供註記並在求值
時被抹除；範形不含註記。

**範疇化。** 物件是 `LTy`，態射是閉函數項模 βπη，範形 `nf_eta` 是每個態射的
規範代表；這是 `Bool/Unit` 生成的**自由笛卡兒閉範疇（free CCC）**。合成
`tm_comp_at`、恒等 `tm_id_at` 及結合／恒等／逆律以 `def_eq_eta` 驗證
（`check_syntactic_category`）。未型別 NbE（`nbe.mbt`）是同一範疇在 βπ 商下的
較粗版本：其範形是 η 範形的 βπ 化簡；加上積 η 後，先前只能在元素上成立的
`swap ∘ swap = id` 現在在函數層面定義地成立（`check_eta_swap_involution`）。

**判定與單值性。** `nf_eta(nf_eta t) = nf_eta t`（範形冪等）；定義相等
= 範形結構相等。單純型別片斷強正規化，故對良型別輸入終止；不良型別輸入
由 `ty_check` 拒絕（`nf_eta` 回 `None`）。

### 1.2 一般 Glue 的 comp 求值（`glue_comp.mbt`）

**(a) 有限宇宙：端點 comp 算法，對一般數據成立。** 輸入是一條「等價線」
`GlueLineFinite{a_line, t_line, e0, e1, face0, face1}`：任意有限型別線
`A0≃A1`、`T0≃T1`（以 ua 呈現）、端點等價 `eᵢ:Tᵢ≃Aᵢ`、任意面公式 `φᵢ`。
前提是自然性方塊交換 `e₁∘coe_T = coe_A∘e₀`（`glue_line_coherent`，下文範疇化）。
算法是教科書 Glue-comp 的端點形態：

```text
a_raw := coe_A(a₀)                                -- 在 A 中合成未黏部分
若 φ₁ 不可滿足： (t₁, a₁) := (coe_T(t₀), a_raw)
若 φ₁ 可滿足：
    t₁ := coe_T(t₀)        （φ₀ 可滿足時)          -- 在 T 中合成偏部分
        | e₁⁻¹(a_raw)      （φ 僅在 1 出現時)      -- 「φ 亮起」：由 base 反造偏部分
    a₁ := e₁(t₁)                                 -- 校正：A 的帽子改到 e₁(t₁)
```

正確性（`glue_comp_finite_correct`）：輸出在目標 Glue 型別良構；若 φ 兩端皆可滿足，
相干性推出校正是常值的（`a₁ = a_raw`）——這是把「校正路徑存在」落到集合層模型
的相等形式；若 φ 只在 1 亮起，輸出 `base` 仍等於 `a_raw`（由構造）。不相干的線數據
（方塊不交換）以 `None` 拒絕。

**(b) 特徵子空間線：開盒 comp 與 hcomp 校正。** 「型別線」`SubLine` 是
`j ↦ im(P(j))`，`P(j)` 為 Hermitian 冪等；「等價線」`LinEquivLine` 是
`j ↦ U(j)`（秩一時的偏等距 `a(j)t(j)†`，一般地是逐點線性同構之矩陣族）。給定
在給定面上由 `U` 互相搬運的相容開盒（`glue_box_compatible`）：

1. 兩盒先以 ambient 公式填充，再逐點以 `P_T(j)`、`P_A(j)` 剪枝（變動投影線的
   retract Kan 結構，`fill_subline`）；
2. 原始帽子一般不滿足 `U(1)(t_cap) = a_cap`；構造校正方塊
   `(i,k) ↦ (1−k)·a_cap(i) + k·U(1)(t_cap(i))`，其 `k=1` 邊是 Glue 的正確帽子；
3. 側面處差異為零（開盒相容性），故校正不移動規定端點。

此方塊即教科書算法中在 `A` 內做的那次 `hcomp`，在仿射模型中顯式化。
可靠性 `glue_comp_vec_sound` 逐項驗證：填充合邊界、填充落子空間線、校正方塊
落 `A(1)`、帽子端點與 `U(1)` 相容方程。

**範疇化。** (a) 中等價線是**箭頭範疇（arrow category）**`Ty²` 的態射：
物件是等價 `T≃A`，態射是交換方塊；`glue_line_coherent` 判定該方塊。(b) 中
`SubLine` 是 Karoubi 包絡物件上的路徑（投影之連續族），剪枝填充是 retract 在
「值域隨參數變動」時的 Kan 提升。兩者合起來即：Glue 的 comp = 在 A 合成 +
在 T 合成 + 在 A 校正（hcomp），此處三個步驟逐一是函數 `coe_upath/coe_T`、
校正指派與校正方塊。

### 1.3 有限側符號判定（`bdd.mbt`, `wiring.mbt`, `system_symbolic.mbt`）

| 對象 | 舊判定（枚舉） | 新判定（符號） | 規範形 |
|---|---|---|---|
| 面公式 sat/≤/≡ | 2ⁿ 端點掃描 | ROBDD：`sat ⇔ bdd ≠ ⊥`；`f≤g ⇔ f∧¬g = ⊥`；`≡ ⇔ BDD` 結構相等 | 約化有序 BDD |
| 系統商相等 | 逐端點 lookup 比較 | 有效區域 `φᵢ∧¬(前覆蓋)` 的 BDD 區域分割按值合併排序 | `SystemNF` |
| 系統相容 | 交集面枚舉可滿足性 | `face_sat`（內部走 BDD） | — |
| 有限等價 wf/相等 | 逐元素檢查 2^k | wiring 置換性 O(#葉)；相等＝wiring 結構相等 | 帶號置換 `Wiring` |
| `coe` 往返律 | 逐元素往返 | `w;w⁻¹ = id` 的 wiring 等式 | `Wiring` |
| Glue 良構／可靠 | 逐端點、逐元素 | `face_sat`＋單一 BDD 見證；全稱陳述改為截面等式 `w⁻¹;w=id` | BDD＋`Wiring` |

枚舉代碼僅存於：(i) `elems_of` 作為有限型別的語義函數（定義域的列舉本身）；
(ii) `*_extensional / *_oracle` 函數與白箱測試中的暴力 oracle，用作符號判定的
**差分校驗**（differential testing）——它們不是任何庫內判定路徑的一部分。

**範疇化。** BDD 是生成元上面公式自由格的規範代表；wiring 是由
`id/not/swap/×/∘/⁻¹` 生成的**自由對稱冪冪範疇**的態射規範形（對象 `Ty`，
張量 `wiring_prod`，換位 `wiring_swap`，結合子／單位子顯式給出；
五邊形・三角形・六邊形相干律以 wiring 相等驗證，`check_wiring_coherence`）。

**複雜度注記。** ROBDD 在最壞情形指數大小（判定仍是符號化簡驅動而非盲掃描）；
wiring 判定是葉數的線性時間；`face_witness` 沿 BDD 一條到 ⊤ 的路徑讀出見證。

### 1.4 依賴型別 NbE：Π、Σ、宇宙（`nbe_dep.mbt`）

語法 `DTerm` 同時承載項與型別：`DUniv(i)`、`DBoolTy/DUnitTy`、
`DPi/DSigma`（第二分量在綁定子之下）、帶定義域註記的 `DLam`、只能在
check 模式導入的 `DPair`、投影與 `DAnn`；§1.7 在同一語法上再加入
維度、PathP、Kan、資料與 HIT 構造子，§1.8 再加入持久環境、惰性值、
語義系統以及通用歸納/HIT schema 構造子。語義域 `DValue` 中 Π/Σ 的
第二分量是閉包函數 `DValue -> DValue`，故依賴代入即閉包施用，例如
`snd` 的型別是 `B(fst p)` 並以定義方式計算。宇宙採累積層級
`Typeᵢ : Typeᵢ₊₁`，Π/Σ 形成於分量層級的最大值。

轉換與讀回均按型別進行，並同時帶項層級與維度層級：`conv_at/quote_at`
對 Π/Σ/Unit/Path 做 η，
`conv_ty/quote_ty` 處理作為宇宙元素的型別值；中性應用存參數型別，
中性投影存姊妹型別族，因此 spine 內仍有完整的型別導引。單純型別
片斷經 `lty_to_dterm` 嵌入（函數→Π、積→非依賴 Σ）。範疇化是帶族
範疇（categories with families）的句法模型：脈絡延伸是環境與型別
脈絡的平行 cons，代入是閉包施用，規範形是態射／項的標準代表。

### 1.5 Kan 結構推行至全專案型別（`kan_dep.mbt`）

型別線的規範結構是 `DLine{at, coe_fn, fill_fn}`，`comp` 定為
`fill(1)`，外部 `dcoe` 包裝保證 `coe(r,r)` 直接返回原值。構造子
遞迴覆蓋每個型別形成子：Bool/Unit/每層 Universe 為常線；Π 的 coe
在定義域反向傳輸並將餘域取在傳輸所得的參數路徑上；Σ 先傳第一
分量、再沿其路徑傳第二分量；fill/comp 採同一遞迴。依賴族因此以
`(A 中的路徑) -> DLine` 呈現，這正是依賴 comp 所需的數據。單純
型別（LTy）與有限型別（Ty）經非依賴族嵌入；有限 ua 路徑以
`dline_of_upath` 給出非恆常線。其餘專案型別族的 Kan 結構（特徵
空間與子空間線、有限與向量 Glue）由既有模組給出，並一併登記為
`check_kan_all_types`。

### 1.6 特徵值、投影 P 與仿射填充的完全符號代數（`symalg.mbt`, `spectral_symbolic.mbt`）

精確標量層由有理數、多變量多項式規範形、其分式與複有序對組成；
矩陣相等、Hermitian 與冪等都是多項式恆等。特徵值是多項式環中的
不同形式原子 λₖ，譜投影為拉格朗日公式 `Pₖ=qₖ(A)/qₖ(λₖ)`，
`qₖ(X)=∏_{j≠k}(X−λⱼ)`。冪等與正交化為單變量恆等
`qₖ²−qₖ(λₖ)qₖ ≡ 0 (mod m)`、`qₖqₗ ≡ 0 (mod m)`，以首一整除驗證；
單位分解與譜分解是多項式恆等 `Σqₖ/qₖ(λₖ)=1` 與
`Σλₖqₖ/qₖ(λₖ)=X`。特徵多項式由 `det(XI−A)` 精確展開，並在一般
Hermitian 2×2、對角特徵值矩陣與秩一投影上核對。

仿射唯一填充以座標原子 `i,j` 直接證明：四角一般雙線性插值與
`square_fill` 在仿射邊上給出的表達式是同一多項式；廣義雙線性
ansatz `k00+i·k10+j·k01+ij·k11` 的繫數可由四角值唯一解出
（差分公式逐項以多項式相等驗證），故在雙線性類中填充唯一。
對非仿射（多項式）邊，`square_fill` 的三個邊界方程仍是在 `i,j`
原子上的恆等；而投影剪枝滿足 `(I−P)(P·F)=0` 的精確恆等。

### 1.7 立方 AST：Path、資料、HIT 與 hcomp 按型別化簡（`nbe_dep.mbt`, `kan_ast.mbt`, `ast_laws.mbt`）

**語法樹。** `DTerm` 新增下列片斷；項變量與維度變量是分離的 de Bruijn
空間，`denv` 是維度環境，`dlevel` 是維度層級。型別線與 tube 都是「在一個
維度綁定子之下的 body」，系統是 `Array[DTubeTerm]`，每分支為
`d_tube(φ, body)`。

```text
PathP A a b       := DPathP(A, a, b)          Path A a b := DPath(A, a, b)
<i> e             := DLamDim(e)               e @ r      := DAppDim(e, r)
coe^j A r→s a     := DCoe(A, r, s, a)
comp^j A [φ↦u] a₀ := DComp(A, [d_tube(φ,u)], a₀)
hcomp A [φ↦u] a₀  := DHComp(A, [d_tube(φ,u)], a₀)
hfill A [φ↦u] a₀  := DHFill(A, [d_tube(φ,u)], a₀, r)   （在維度 r 取值）
```

資料與 HIT 亦在同一 AST：Bool（含 `DBoolElim`）、Nat、List 及各自的依賴
消去子；Circle 的 `base/loop/elim`；Torus 的 `base/loopA/loopB/square/elim`。
Circle 點正規化為 `loop@r`（`r=0,1` 皆為 base）；Torus 點正規化為
`square@(i,j)`，座標 `1` 等同 `0`，即方塊對邊黏合。雙向檢查器逐分支
要求 `tube(0)` 在其面上等於 base，且重疊分支在交面相容。

**Kan 化簡。** `comp_value` 先消去底面分支、頂面分支直接取其在 `1` 的帽，
再在新一般維度取樣型別線並按頭構造子派遣（`hcomp` 是常線的
`comp`）：

| 型別 | `comp` 的定義化簡 |
|---|---|
| `Π x:A. B x` | **反變**：結果是 `λy. comp^j B_j(x_j) [φ↦u_j(x_j)] (f₀ x₀)`，其中 `x_j` 是把目標參數 `y` 沿定義域線**反向填充**所得的路徑 |
| `Σ x:A. B x` | 先合成第一分量並取填充 `a_j=fill^j A [φ↦fst u] (fst a₀)`，第二分量再於線 `B_j(a_j)` 上合成 |
| `PathP A a b` | `<k> comp^j A_j(k) [φ↦u_j@k; k=0↦a_j; k=1↦b_j] (p₀@k)`：原 tube 之外加入隨 `j` 移動的左右**端點分支**，邊界律由此定義地成立 |
| `Universe Typeᵢ` | 空 tube 是恆等；非空 `hcomp` 回傳語義 Glue `Glue[φ₁↦T₁; …; φₙ↦Tₙ] A₀`，完整保留 DSystem；面決定處以 pack/unpack 在 `(partial, base)` 對與端點值之間轉換，多分支 partial 以 `DPartial/DVPartial` 表示 |
| `Glue` | 在 base 與每條 partial 型別分支分別 comp，再以各分支的 partial 填充在目標 base 型別中作 hcomp **校正**；僅目標分支亮起時，該 partial 分量由 base 沿對應 Glue 線反造 |
| `Bool`, `Nat`, `List A` | 按構造子遞迴：Bool 同字面量、Nat 的 `zero/succ`、List 的 `nil/cons`（head 另在元素線上 comp）；`Unit` 恆為 `()`。開放／不一致的宿主系統保留為形式 `DNComp/DNHComp` |
| `Circle`, `Torus` | 全為 base 的系統化簡為 base 點；非平凡 loop/square 系統保留為**形式 hcomp 點**（HIT 的標準 stuck composition） |
| 中性型別線 | 不強行化簡，保留 `DNComp(line, DSystem, base)`，quote 先把系統按值合併排序再完整讀回多分支 tube |

填充與一般 coe 由 comp 定義：
`fill^j A [φ↦u] a₀ @ r = comp^{j∧r} A [φ↦u; r=0↦a₀] a₀`，故在 `0` 是
base、在 `1` 是 comp、在既有面上是 tube 的前綴；`hfill` 是常線版。
`coe(r,r)` 是恆等，`coe(0→1)` 是空 tube 的 comp，反向與任意端點以
`¬j`、`r∨j`、`s∨¬j` 線段及 fill 化約，見
`coe_value`。語義維度/面的頂底與相交不再抽樣，而由既有 ROBDD
謂詞經 `dim_eq_sem`、`face_is_top_sem`、`face_is_bot_sem` 符號判定。

**消去與合成交換。** Bool/Nat/List/Circle/Torus 的依賴消去子在構造子上
按通常 β 律計算；若 scrutinee 是形式 composition，則先取其 filler，把
消去子逐分支作用，再於 `motive(filler j)` 線上 comp（`elim_over_comp`）。
因此例如把常值 Bool motive 的 Circle 消去子作用在形式 hcomp 點上仍會算
到常值，而非卡在 eliminator 外層。

**範疇化。** 這是 cubical CwF 的句法核心片斷：脈絡含項與維度變量，
`PathP` 是沿區間的依賴路徑物件；每一型別構造子保存 Kan 纖維化結構，
上表就是其提升運算。資料型別是帶依賴消去的初始代數；Circle/Torus 是
由點、路徑（及 Torus 的交換方塊）生成的高階歸納物件，其消去子是
motive 的截面。

### 1.8 語義系統重構與通用 schema 生成器（`nbe_dep.mbt`, `schema.mbt`）

#### 1.8.1 持久環境、惰性求值與語義快取

**環境。** 項環境 `DEnv` 與維度環境 `DDimEnv` 均為帶長度的持久連結
串列（`Nil | Cons(value, tail, length)`）。`denv_cons/ddim_cons` 只
新建一個節點並共享原尾部，故脈絡延伸是 O(1)，舊環境永不被改寫；
`DTVar(i)`／維度變量沿串列向外查找。宣告序陣列以
`denv_extend/ddim_extend` 逐一 cons（最後宣告成為索引 0），而公開的
陣列版邊界（例如 `deval(t, Array[DValue])`）只在入口以
`denv_from_array` 轉換一次。

**惰性值。** `DThunk{forced, compute, force_count}` 包作
`DValue::DVThunk`。`lazy_value` 建立未計算值，`force_value` 第一次
執行 `compute` 後把結果（再遞迴 force）存回同一 cell；後續 force 直接
取回，故 `force_count≤1`（`lazy_force_count/lazy_is_forced` 可觀察）。
求值器把函數引數、配對與資料構造子分量、消去子 case、partial 分支
與生成構造子引數放入 thunk，只有型別導向操作需要時才強制。

**快取。** `memo_dim_line` 以 `dim_simplify` 後的 `Dim` Debug 鍵
快取維度線；`memo_family` 以引數在定義域下 `quote_at` 的項 Debug 鍵
快取 Π/Σ 族。快取表是閉包內的關聯陣列，查到的值直接重用；鍵的
穩定性由化簡/引文保證。生成 schema 的 telescope 與 case 型別亦經
同一求值、轉換與引文基礎設施重用。

#### 1.8.2 `DSystem`、partial 值與多分支 Glue

語義 composition 分支不再以裸 `Array[DTubeBranch]` 傳遞，而是封裝為

```text
DSystem{ branches : Array[DTubeBranch] }
DTubeBranch{ face : Face, path : Dim -> DValue }
```

`dsystem_of/dsystem_singleton` 刪除底面並簡化面。給定型別線後，
`dsystem_canonical(level,dlevel,line,system)` 再以端點與一般維度的
型別導向轉換比較 branch paths：body 可轉換者把面以 `FOr` 聯集合併，
其餘類別按一般點 body 的引文鍵（再按面鍵）排序；AST 檢查器為已驗證
相容的 tube 系統套用此範形，quote 與中性 comp 轉換亦然。

值的對應物是 `DPartialValue`／`DValue::DVPartial`，AST 對應
`DPartial(Array[DFaceTerm])`。`partial_normal_form` 按 first-match
語義逐分支計算 BDD 有效區域 `φᵢ∧¬(前覆蓋)`，以 `conv_at` 合併同值
區域、按引文排序，並回傳 `DSystemNF{classes, undefined}`；
`tube_system_nf_at` 是 tube 在指定維度的取樣版。這與向量系統的
`SystemNF` 平行，但區域標籤換成任意依賴語義值。

`DVGlue` 的載荷改為 `(DSystem, base, level)`。`hcomp` 於 Universe
把全部型別分支放入 Glue，不再丟棄第一分支以外的 partial 線；
`DGlueParts.system` 是完整系統，`face` 是其 join，`line` 只保留作
單分支代表線。元素的 partial 分量以 `glue_partial_values` 按語義面
對齊各型別分支，並以 `glue_store_partial` 儲存：單分支沿用 raw 值，
多分支使用 `DVPartial`。檢查、轉換、quote 與 `comp_glue_value` 均
逐分支處理相容、校正與亮起分支；`DPartial` 是只能在 Glue pair 的
第一分量等 check 位置使用的導入形。

#### 1.8.3 通用歸納族 schema

一個歸納族由有限描述子 `DInductiveSpec` 完整給出：名稱、宇宙層級、
參數 telescope、索引 telescope 與構造子列。telescope 型別及構造子
引數型別都是 `DTerm`，其 `DTVar` 只指向 schema 局部綁定子（參數，
其後是先前 telescope/引數項目）。每項構造子引數必為三類之一：

| `DArgKind` | 語義引數型別 | 消去時多給的數據 |
|---|---|---|
| `DArgExternal` | 給定的外部型別 | 無 |
| `DArgRecursive` | 同族在給定索引項處 | 該遞迴引數的 IH |
| `DArgFunction` | `Π a:A. Family(index a)` | `Π a:A. motive(index a, f a)` |

構造子另給結果索引。`inductive_schema_validate` 檢查名稱不重複、
參數/索引 telescopes 可 elaboration、每項引數與遞迴/函數/結果索引
均良型別；外部型別與函數定義域若在句法上提及同名生成族即拒絕，
因此只接受保守的嚴格正性片斷。AST 形式為
`DInductive(spec, params++indices)`、`DIntro(spec, ctor, params, args)`
與 `DInductiveElim(spec, motive, cases, params, indices, scrut)`；
motive 是依序抽象索引與 scrutinee 的巢狀 λ。

生成器自動給出型別形成、構造子推斷、依賴消去、telescope 逐步的
type/value conversion 與 quote。消去在中性 scrutinee 上形成
`DNInductiveElim` 並可完整引文；遇到形式 `DNComp/DNHComp` 時按
型別線逐點取參數/索引，在 motive 中再 composition。當 base 與所有
tube 都是同一構造子時，`comp_inductive_value` 按引數序計算
fillers，並在後續引數型別中代入先前 fillers（即 Σ 的迭代形）；
函數遞迴引數直接由 Π 的 comp 規則完成。構造子不一致或 scrutinee
非 intro 時保留形式 comp。

內建範例為 `nat_schema`、`bool_schema`、`list_schema`（參數）、
`vec_schema`、`fin_schema`（索引）、`tree_schema` 與
`w_schema`（函數遞迴引數）；律涵蓋 Nat 加法、List 長度、Tree
葉數、Vec/Fin 索引正確性、W 的 Π 形 IH，以及 Nat/List/Vec comp。

#### 1.8.4 通用 HIT schema

`DHitSpec` 同樣含參數/索引 telescopes，但生成元是
`DHitCellSpec{name, dim_count, args, result_index, faces}`，其中
`dim_count∈{0,1,2}`，`faces` 按
`(dim0=0, dim0=1, dim1=0, dim1=1)` 排列。`DHitFaceExpr` 以目標
cell、引數項與維度式例示一個面；維度變量沿 `DDimEnv` 解釋
（最後一個 cell 維度是 `DVar(0)`）。`hit_schema_validate` 除共用
telescope/引數/正性檢查外，還逐 face 檢查目標引數型別、結果索引
轉換相等與維度變量範圍；2-cell 另以兩種化簡次序核對四個角落。

AST 形式為 `DHitType`、`DHitIntro(spec, cell, params, args, dims)` 與
`DHitElim`。`hit_cell_value` 是 cell 的智能構造子：先簡化每個維度，
若任一維是端點則例示該 face expression 並遞迴；conversion/quote
亦先正規化端點 cell。給定 motive 後，`hit_case_type` 依序生成
引數與 IH，最後按 cell 維數生成 point 型別、PathP 或巢狀 PathP
方塊型別；其端點值由較低維 face 的消去遞迴給出。消去時先供應
引數/IH，再把 cell 的實際維度逐一施於 case；中性與形式 comp 的
處理與歸納族相同。當 base/tube 恒為同一 cell 且所有 cell 維度沿
comp 線恒定時可逐引數 comp，否則保留形式 hcomp 點。

內建範例為 `circle_schema`、`segment_schema`（兩端點相異）與
`torus_schema`（base、兩 loop、交換 square）；律涵蓋端點正規化、
Circle/segment 的生成路徑消去、Torus square 消去、中性 elim 的
conversion/quote 與同 cell/移動 cell 的 comp 分界。

### 1.9 第六期：原六大邊界的收束

#### 1.9.1 Schema 函子、互歸納、商、宇宙 scheme 與高維 HIT

構造子引數不再侷限於三種硬編碼形狀：`DConstructorArg` 保存完整
`DTerm` 引數型別，並可攜帶 `DConstructorConstraint` 的依賴等式約束。
`DPositiveFunctor ::= Id | Const A | F×G | F+G | List F | Π(a:A),F`
給出可檢查的正性函子語法；`positive_functor_type`、`positive_functor_map`
與 `positive_functor_ih_type` 分別生成解碼型別、遞迴值映射與 decoded
induction hypothesis。巢狀遞迴（如經 `List` 的 rose tree）因此走同一套
引入、消去、轉換、引文與 comp。

正性判定改為結構化極性遞迴：先走訪完整 `DTerm`，記錄族出現的位置、
正/負極性與未知中性應用，透明別名在走訪中展開；負位置與無法證明正性的
中性族應用被拒絕。`DDecode` 把 Tarski 宇宙碼解碼回型別，令型別族與其
遞迴解碼可同時由 schema 生成（歸納—遞迴片斷）。`DMutualFamily` 將多個
分量編譯為以有限和索引的單一 schema，分量型別、構造子與消去子由偏移量
及索引等式還原；`DLevelExpr` 與 inductive/HIT level schemes 把宇宙層級
表示為可求值、可再驗證的 scheme。商型別表示為帶等式 1-cell 的 HIT。
HIT cells 推廣至任意有限維：任一坐標到端點時遞迴代入 face expression，
消去 case 是逐維巢狀 `PathP`；沿移動維度的 comp 在端點與目標維度可精確
判定時刻逐引數計算，否則保留有範形地位的形式中性合成。

#### 1.9.2 原始 `DSystem` 的相容性與 first-match 範形

宿主直接建立的 `DSystem` 不再假定相容。`conv_at_under_face` 把面轉成
BDD 滿足 cubes，在每個 cube 固定的局部維度脈絡下做型別導向轉換；
`dsystem_compatibility_report` 逐一檢查「分支在維度 0 與 base 相合」及
「兩分支在交面相合」，回報第一個衝突的種類與分支編號。`dsystem_checked`
及 `dsystem_checked_of` 是進入 composition 系統的受檢入口。對本質上採
first-match 優先序的原始系統，`DTubeNF` 以互不交疊的有效區域
`φ₁, φ₂∧¬φ₁, …` 分解並按值合併，給出精確語義範形；
`dsystem_first_match_checked` 只在不交化後還能與 base 相容時才提升為
composition 系統。

#### 1.9.3 AST 一等 `Equiv`、`ua` 與 `GlueEquiv`

`Equiv A B` 是 AST 型別形成子，其值由 `fwd : A→B`、`bwd : B→A` 及
section/retraction 兩條路徑證明組成；投影、`mk_equiv_term`、雙向檢查、
型別導向 conversion 與 quote 均遞迴至四個分量。`ua` 把一等等價送至
宇宙中的路徑，其型別線是 primitive `DVGlueEquiv`，沿它的 coe 在兩方向
直接計算為 `fwd`/`bwd`。`GlueEquiv` 的每條分支保存面、partial 型別與
指向 base 的一等等價，不再只保存一條型別線；glue/unglue、端點塌縮、
PathP 與 Kan comp 均保存這些分支資料。

#### 1.9.4 受檢查型別線與 schema 註冊表

`DCheckedTypeLine` 保存已檢查的開放型別 body、脈絡、環境與宇宙層級，
其 `at` 由在指定維度環境下求值 body 得到，故由構造尊重維度代換；
coe/fill/comp 直接派遣 AST Kan 引擎。裸宿主函數 `Dim -> DValue` 仍是
底層語義工具，但可信入口以 checked line 為界。`DSchemaRegistry` 以穩定
鍵 intern inductive/HIT plans，保存驗證結果、一般 telescope 型別及帶
語義引數快照的前綴鏈；schema 驗證與 telescope elaboration 先查表，
hit/miss 計數使重用可觀察。

#### 1.9.5 代數擴張、廣義特徵空間與 Jordan 理論

`QPoly`/`QMat` 提供精確單變量有理多項式與有理矩陣層（primitive
pseudo-remainder gcd、擴張歐氏、Yun squarefree 分解、有理根、特徵與
最小多項式、RREF）。`QuadNum a+b√d` 是二次根式的規範形（`d` 無平方
因數，含去巢平方根）；`AlgNum` 是 `Q[x]/(m)` 的餘式範形，可再基底化到
元素自身的極小多項式。廣義特徵空間由 `(A−λI)ᵏ` 的遞增核、代數/幾何
重數、指數與 Jordan 鏈給出；primary projectors 由互質因子的 Bézout
單位分解生成。Q 上分裂時得到完整 `PJP⁻¹=A`，未分裂部分明確保留殘餘
因子；`AlgMat` 把同一套理論搬到所選代數擴張。

#### 1.9.6 BDD DAG 擴展性與認證數值

面 BDD 的主表示改為 `BddManager` 中的 hash-consed DAG：節點以
`(rank,lo,hi)` 唯一化，apply 以 `(op,a,b)` memoize；同一 manager 內的
相等就是 root ID 相等、sat 就是 root 非 0，大小以 reachable node count
量測。`FaceDecision` 以節點預算把「無法在預算內決定」做為正式結果；
變量次序可在 index、首次出現、頻率與反序候選中選最小 DAG，亦有帶步數
預算的 DPLL sat/eq 後備。數值層的精確對應物是
`QuadC = QuadNum + i·QuadNum` 上的 `CertMat` 與次數至多 2 的係數式
`CertPath`/`CertSquare`：投影性、厄米性、正交分解、特徵空間填充與角落
相干均由精確結構相等驗證；原 `Double` 投影只回報對精確影子的最大偏差
與浮點 residual。`double_dyadic_interval` 給出包住一個 Double 的有理
dyadic 區間。

### 1.10 第七期：遞迴宣告、S³、認證 Jacobi、HOU elaborator 與模組

#### 1.10.1 互相歸納、歸納—遞迴與任意容器函子巢狀遞迴

互歸納與 Tarski 歸納—遞迴沿用 1.9.1 的編譯與 `DDecode`。正性函子
新增依賴多項式/container 節點
`DFunctorContainer(Shape, Positions, index)`，語義為
`Σ(s:Shape), Positions(s) → X(index s p)`；其 IH 型是
`Π(p:Positions(s)), P(index s p, contents p)`，map 逐 position 套用
消去子。`container_tree_schema` 把 Shape/Positions 本身做為族參數，故
同一生成器承載任意有限依賴多項式分支形狀與其巢狀遞迴；形狀/位置
型別不得提及本族，遞迴索引在 shape 與 position 兩綁定子下檢查，
互歸納編譯會把索引加上分量標籤。

#### 1.10.2 球面 `S³`

`suspension_schema` 對無索引 HIT `X` 生成 north、south 與每個
`x:X` 的 meridian 路徑。`sphere2_schema = Susp(circle_schema)`，
`sphere3_schema = Susp(sphere2_schema)`，且 `sphere_schema(n)` 遞迴迭代。
端點 meridian 在 0/1 分別化簡為 north/south；依賴消去、conversion、
quote 與 Kan/hcomp 全部由通用 HIT 生成器提供，恆等消去子在一般
meridian 上計算回自身。

#### 1.10.3 Jacobi 譜迭代的符號區間包含

精確複有理 Hermitian 矩陣先包成複矩形區間矩陣。每步以中點矩陣選
pivot，旋轉的 `|a|`、phase `a/|a|`、`c`、`s` 以有理區間算術和
「整數二分＋精確平方比較」的 sqrt 包絡表示；固定酉矩陣的區間包絡
再做 `J†AJ` 與 `VJ`，每乘一步以 dyadic 外向捨入控制分母並對
Hermitian 包絡對稱化。證書逐旋轉重算：係數包絡包含重算值、
`J†J-I` 區間含 0、after 包含相似變換、transform-after 包含 `VJ`。
最終特徵值是 Hermitian 區間矩陣的 Gershgorin 圓盤，重疊者組成帶
重數的簇。

#### 1.10.4 高階合一與雙向 semantic elaborator

完整高階合一不可判定；實作採 Miller pattern 片斷：
`?F x₁…xₙ` 的 spine 須為相異綁定變量，解由抽象這些變量得到，並
輔以 beta/eta/投影 WHNF、rigid 分解、occurs/scope 檢查、flex-headed
application 與閉項非常規 pattern fallback。命名表面語言 `STerm`
經雙向 `elab_infer/elab_check` 插入 implicit metavariables，求解後
以 `hou_semantic_optimize` 做 beta/投影/Nat 簡化，再譯至 `DTerm`；
Nat eliminator 的 dependent motive 可由預期結果型別以 HOU 解出。
未解 metavariable 的核心被拒絕，成功結果可再由依賴檢查器驗收。

#### 1.10.5 參數化模組、Open/Import 與名字空間

模組是 `params → imports → decls` 的 telescope。elaborator 遞迴
內聯 import：參數以 import 引數代換、目標宣告成為宿主 telescope
entries、逐條以 `d_check` 驗證；模組循環被拒絕。名字 bindings 與
entries 分離，同一個 entry 可由限定名、alias 或 opened/renamed 名
解析；`only/hiding` 篩選、歧義 open 拒絕、opaque export 在跨邊界後
中性化。`module_instantiate` 是函子套用：以閉合參數引數同時代換
整段宣告並逐條閉式檢查，從而把同一證明段抽象後實例化到不同型別。

---
---

## 二、規範形式目錄（逐結構）

| 結構 | 規範形式 | 相等之判定 |
|---|---|---|
| `Complex` | `(re,im)` | eps 分量 |
| `CVec` | 分量列 | eps 逐分量 |
| `CMat` | 列之列 | eps 逐分量 |
| 投影 `P` | `Σ vₖvₖ†`（ONB 外積）；不變量：`im(P)`、秩 `tr(P)` | 矩陣 eps 相等 |
| 向量分解 | `(Pv, (I−P)v)` 正交對 | 分量相等 |
| `Dim` | 端點布林化＋`dim_simplify` | 經面 BDD |
| `Face` | `BddManager` 中的 DAG root；樹形 `bdd_of_face` 為相容展開 | 同 manager root ID 相等；sat 為 root≠0 |
| `VecSystem` | `SystemNF`：值標記的不交 BDD 分割＋未定義區域 | 分割逐類相等 |
| `Cube` | 函數本身；路徑範例為 `path_line` | 網格外延 |
| 開盒填充 | `square_fill` 公式（仿射唯一式） | 邊界方程 |
| `Term`（未型別） | βπ 正規形 `nf` | 結構相等 |
| `Term`（型別化） | η 長 βπ 正規形 `nf_eta`（不含註記） | 結構相等 |
| `HTm` | `hoas_to_term` 後取正規形 | 經 `Term` 範形 |
| `Ty` | 葉序 `leaves_of_ty` | 結構相等 |
| `PVal` | 葉值列 `flatten_pval` | 結構相等 |
| 有限等價 | `Wiring` 帶號置換 | `wiring_eq` |
| `UPath` | 其等價的 wiring | `upath_eq` |
| `PathPVal` | `pathp_canonical`（遠端為 coe 像） | 端點與線相等 |
| `DTerm` | 按型別 `quote_at` 的 η 長依賴正規形；型別值以 `quote_ty` 讀回 | 結構相等 |
| 型別線 `DLine`／`DCheckedTypeLine` | 底層 `{at, coe_fn, fill_fn}`；受檢線保存已檢查 body＋環境，代換由求值給出 | coe/comp 律；checked 構造時檢查宇宙層級 |
| 立方 `DTerm` 系統 | 語法 `Array[DTubeTerm]`（面＋維度綁定 body）；形式合成為 `DNComp/DNHComp` | base／重疊相容＋按型別化簡；quote 多分支讀回 |
| 語義系統 `DSystem` | 相容系統：去底面/簡化面後同 body 分支以面聯集合併排序；任意原始系統：first-match 的 `DTubeNF` 不交區域分解 | 面相對 BDD-cube 轉換判定相容性；checked 入口才提升為 composition 系統 |
| partial 值 | `DSystemNF`：不交 BDD 有效區域＋值類別＋未定義區域 | 區域 BDD 相等＋類別值 `conv_at` |
| 持久環境 | `DEnv/DDimEnv` 帶長度連結串列，最內綁定在頭 | de Bruijn 索引查找與長度 |
| 惰性值/快取 | `DVThunk` 強制後的值；維度簡化鍵與引文項鍵的關聯表 | `force_count≤1`；鍵相等後重用 |
| HIT 點（具體） | Circle：`loop@r`（端點 base）；Torus：`square@(i,j)` 模對邊黏合 | Dim 的 ROBDD 語義相等＋點構造子 η/消去 |
| AST Glue 值 | `DVGlue(DSystem,A,i)`，元素為 `(raw 或 DPartial partial,base)`，決定面處 pack/unpack | 每分支 partial 沿其 T 線 coe 至 A 後與 base 轉換相等 |
| 生成歸納型別/值 | `DVInductive(spec,params,indices)` / `DVIntro(spec,ctor,params,args)`；引文為 `DInductive/DIntro` | 描述子相等＋telescopes/引數逐步 `conv_at` |
| 生成 HIT 型別/值 | `DVHitType(spec,params,indices)` / 非端點 `DVHitCell`；任意有限維端點逐維按 face 化簡 | 描述子、cell、引數與 `Dim` 語義相等；不可計算的移動維度 comp 保留形式中性範形 |
| 符號標量/矩陣 | 多變量多項式規範形與分式對；矩陣逐元素 | 多項式恆等（交叉相乘） |
| 譜投影 | `qₖ(A)/qₖ(λₖ)`（拉格朗日公式） | 模最小多項式整除＋求值矩陣恆等 |
| 仿射填充 | 四角雙線性插值（繫數由角差分唯一決定） | 在原子 i,j 的多項式恆等 |
| `GlueElem` | `(partial, base)`；`glue_from_base(a) = (e⁻¹a, a)` 為由 base 的範形 | 分量相等＋`glue_wf` |
| Glue comp 輸出 | 有限版：`(t₁, e₁(t₁))`；向量版：校正方塊 `k=1` 邊 | `glue_wf`／`glue_comp_vec_sound` |
| AST 等價 | `(fwd,bwd,section,retraction)` 四分量；`ua(e)` 的 primitive GlueEquiv 線 | 四分量型別導向轉換；沿 ua coe 為 fwd/bwd |
| Schema plan／telescope 快取 | registry 中以穩定鍵 intern 的 plan 與語義前綴鏈 | 鍵相等命中；hit/miss 計數 |
| `QPoly`／`QMat` | 去尾零升冪有理係數；有理矩陣與 RREF pivot 基底 | 精確結構相等；多項式模運算 |
| 代數數 | `QuadNum(a,b,d)`（d 無平方因數）或 `AlgNum` 模極小多項式餘式 | 係數結構相等 |
| Jordan 分解 | 廣義核鏈塊大小＋鏈基底，`PJP⁻¹=A` | 矩陣恆等與塊大小相等 |
| 認證數值立方體 | `QuadC` 矩陣與次數≤2 的 `CertPath/CertSquare` 係數 | 精確結構相等；Double 只比偏差/residual |
| 球面 `S³` | `Susp(Susp(S¹))` 的 north/south/meridian 生成子 | meridian 端點化簡與 HIT 消去/conversion |
| Jacobi 迭代 | 每步 before/after Hermitian 區間包絡＋累積酉區間矩陣 | 逐旋轉包含證書與 Gershgorin 簇重算 |
| HOU 核心 `UTerm` | zonked Miller-pattern 解經 beta/投影/Nat 簡化 | 無未解 meta 後譯 DTerm 並 dep_check |
| 參數化模組實例 | telescope 同時代換後的閉合宣告列 | 每宣告 `dep_check_closed`；名字由 bindings 解析 |
| 規格條目 | `SpecEntry` 六元組 | `spec_registry_sound` |

## 三、範疇目錄（逐範疇）

| 範疇 | 物件 | 態射 | 主要結構／律 | 實作 |
|---|---|---|---|---|
| Hilb（有限維） | `Cⁿ`（以 `CMat.n` 索引） | `CMat` | dagger `†`、雙積 ⊕ | `complex.mbt` |
| Karoubi 包絡 Kar(Hilb) | Hermitian 冪等 `P` | `QAP=A` 的矩陣 | 恒等 = P 自身；†；冪等分裂 | `categories.mbt` |
| 投影偏序 | 投影 | `P≤Q ⇔ QP=P`（蘊含唯一） | 交換者的積 = meet | `projector.mbt` |
| 面偏序／格 | `Face` 模 BDD | `φ≤ψ` | ∧ 積、∨ 餘積、⊤/⊥ | `interval.mbt`, `bdd.mbt` |
| 立方體範疇 □（De Morgan 味） | 維度 `n` | 面映射 `restrict_face`＋退化 `degenerate_cube` 生成 | 立方體恆等式 | `cube.mbt`, `categories.mbt` |
| 句法 CCC（βπ 版） | `LTy`（含未型別前身） | 項模 βπ | 積、指數 | `nbe.mbt` |
| 句法 CCC（βη 版） | `LTy` | 項模 βπη，範形為代表 | 積/指數萬有性；coe 箭頭是同構 | `nbe_eta.mbt` |
| 有限集合與 wiring | `Ty` | `Wiring` | 對稱冪冪（⊗、換位、結合子、單位子與三相干律） | `wiring.mbt` |
| 有限宇宙的路徑 | `Ty` | 同構（經 ua 變相等） | ua 計算性；積交換自然性方塊 | `pathp_glue.mbt` |
| 箭頭範疇 `Ty²` | 等價 `T≃A` | 交換方塊（等價線） | Glue comp 的定義域 | `glue_comp.mbt` |
| 句法帶族範疇 (CwF) | 脈絡與脈絡中的型別 (`DTerm/DValue`) | 代入與項（範形為代表） | Π/Σ 形成與依賴代入、Typeᵢ 宇宙族 | `nbe_dep.mbt` |
| Kan 纖維線 | `DLine` 的 `at(i)` | 立方體值與傳輸路徑 | coe/comp 對 Π/Σ/U 的遞迴；依賴族為路徑→線 | `kan_dep.mbt` |
| 立方 CwF 與 Kan 型別構造子 | 項＋維度脈絡中的 `DTerm/DValue` | 代入、維度作用與 comp/hcomp 項 | Π/Σ/PathP/資料/HIT/Glue/Universe 逐一保存 Kan 提升；消去子與形式 comp 交換 | `nbe_dep.mbt`, `kan_ast.mbt` |
| 生成歸納族函子 | `DInductiveSpec` 的參數化型別 | `DVIntro` 與生成消去子 | 嚴格正性函子的初始代數；comp 逐引數沿先前 filler 提升 | `schema.mbt` |
| 生成 HIT 胞腔 | `DHitSpec` 的參數化型別 | 任意有限維 cells 與逐維 face 化簡 | 消去子保存 cells；多維角落相干；可判定移動維度時逐引數 comp，否則形式中性合成 | `schema.mbt`, `schema_extensions.mbt` |
| 多項式代數 | Q 上多變量多項式與分式 | 矩陣與其多項式 `q(A)` | 譜分解是單位分解；插值給出投影 | `symalg.mbt`, `spectral_symbolic.mbt` |
| AST 等價與 ua | AST 型別 | 一等 `Equiv` 四分量 | ua 的 coe 計算性；GlueEquiv 沿偏等價黏合 | `equiv_ast.mbt`, `kan_ast.mbt` |
| 代數擴張線性代數 | `AlgNum` 擴張上的向量空間 | `AlgMat` | 廣義特徵空間、primary 分解與 Jordan 型 | `algnum.mbt`, `Jordan.mbt` |
| BDD DAG | 固定次序布林函數 | root ID 與 apply 格運算 | hash-consing 規範圖；預算把不可決定做為結果 | `bdd_dag.mbt` |
| 球面懸掛 | 無索引 HIT | meridian 胞腔 | Susp 是端塌縮商；S³ 為兩次迭代 | `sphere3.mbt` |
| 模組函子 | 參數模組與 import 圖 | 引數代換與內聯宣告 | open/alias 是名字投影；opaque 是邊界抽象 | `module_system.mbt` |
| Retract Kan 結構 | 特徵空間／子線 | 立方體 | 剪枝函子保持填充（在邊界恆等） | `cube.mbt`, `glue_comp.mbt` |

## 四、第六期後仍保留的邊界

- Schema 片斷仍是有限、可檢查的描述子語言：宇宙多態以宿主層 level
  scheme 呈現，而非 AST 內的一等宇宙多態宣告/抽象語法；互歸納經
  Sum-indexed 編譯而非原始互宣告，正性只認得透明別名與
  `DPositiveFunctor`（現含依賴 container 節點）所生成的間接用法。
  「任意函子」在此精確指任意有限依賴多項式/container 呈現；不能
  表為此類正性函子、或遞迴時改變族參數的非均勻巢狀型別（如 Bush）
  仍不在片斷內，不透明的中性型別算子應用仍被保守拒絕。HIT 的移動維度 comp 只在端點與目標維度可精確決定時化簡，
  其餘情形以形式中性合成為範形，而非宣稱定義性計算；歸納—遞迴涵蓋
  `DDecode` 的 Tarski 形式，不是任意同時遞迴定義語言。
- 原始 `DSystem` 相容性如今可精確回報，但判定要枚舉面的 BDD cubes，
  成本最壞仍隨維度變量指數增長；它判定的是給定型別線下、在這些面脈絡
  中的轉換相容。first-match 不交化只消除優先序重疊，不能修復有效分支
  在維度 0 與 base 的實質不合，此時 checked 提升正確地回 `None`。
- AST `Equiv` 是 section/retraction 型的一等等價，不是帶高階相干的
  adjoint equivalence，也沒有命題截斷或「所有等價皆由路徑分類」的
  單價公理陳述；`ua` 與 `GlueEquiv` 的計算規則已實作，但不主張邏輯上
  的完備刻畫。GlueEquiv 在 quote 時把面正規化為 BDD 面，故 re-elaboration
  後以轉換相等為準，而非原始句法相等。
- `DCheckedTypeLine` 劃定了可信邊界，但底層 `DLine` 與其他語義封閉仍可
  由宿主函數構成；未經 checked 入口的裸宿主線仍不自動尊重維度代換。
  schema registry 是進程內、鍵值式的共享與快取（鍵含 Debug 表示與語義
  快照），不是持久化、增量式或全域 hash-consing 的生產級內核。
- 精確代數以 `Int32` 有理係數運算：加/乘先約分以延緩溢出，但大型輸入
  仍可能溢出，沒有任意精度整數。`QPoly` 不做 Q 上一般不可約因式分解；
  有理譜/Jordan 分解只在特徵多項式於 Q（或所選單一 `AlgNum` 擴張）中
  分裂時完備，未自動構造分裂域或隔離所有複根。根式去巢只涵蓋二次片斷。
- 原 `Double` 數值 API 仍屬近似診斷：精確結論只對能表示為 `QuadC`
  與低次多項式立方體的影子成立；任意宿主函數 `Cube` 仍只能在網格上
  觀察。ROBDD 對某些布林函數/變量次序有固有指數下界，節點預算耗盡與
  DPLL 步數耗盡會回報「未決定」；把 DAG 展開回樹形 BDD、或把 BDD
  轉回 DNF 面公式時，大小亦可指數增長。

- S³ 是懸掛 HIT 的生成呈現，本專案不計算其同倫群、Hopf 不變量或
  與其他球面呈現之間的等價。Jacobi 區間層仍以 Int32 有理端點運算：
  dyadic 外向捨入控制分母，但極大矩陣元仍可能溢出；其證書驗證所
  表示的旋轉鏈，Gershgorin 簇在譜接近時可能只給合併簇而非逐一分離。
- 高階合一只實作可判定的 Miller pattern 片斷及閉項 fallback；完整
  HOU 不可判定，非 pattern 的 flex-flex/flex-rigid 問題會失敗而非
  猜測。參數化模組是 elaboration 期的 DTerm telescope，不是分離
  編譯/連結系統：宣告必須有 body，import 引數只能用參數與較早
  imports，且沒有二進位介面或增量重編譯。

---

## 附錄：公共介面逐符號登記（由 `tools/audit_spec.py` 生成，勿手改）

<!-- APPENDIX:BEGIN -->
共 **2277** 個公共符號（宣告＋構造子＋欄位），分屬 52 個規格族。

### 複數標量

- 規範形式：(re, im) 有序對
- 範疇化：交換環 C；共軛為對合
- 判定：eps 分量比較

| 符號 | 類別 |
|---|---|
| `Complex` | 結構 |
| `Complex.im` | 欄位 |
| `Complex.re` | 欄位 |
| `Complex::equal` | 函數 |
| `Complex::not_equal` | 函數 |
| `Complex::to_repr` | 函數 |
| `cx` | 函數 |
| `cx_add` | 函數 |
| `cx_approx_eq` | 函數 |
| `cx_conj` | 函數 |
| `cx_mul` | 函數 |
| `cx_real` | 函數 |
| `cx_scale` | 函數 |
| `cx_sub` | 函數 |
| `cx_zero` | 函數 |
| `eps` | 常量 |

### 複向量與內積

- 規範形式：分量列
- 範疇化：Hilbert 空間 Hilb 的物件；內積誘導對偶
- 判定：分量運算

| 符號 | 類別 |
|---|---|
| `CVec` | 型別別名 |
| `inner` | 函數 |
| `vec_add` | 函數 |
| `vec_approx_eq` | 函數 |
| `vec_norm2` | 函數 |
| `vec_orthogonal` | 函數 |
| `vec_scale` | 函數 |
| `vec_scale_c` | 函數 |
| `vec_sub` | 函數 |
| `vec_zero` | 函數 |

### 矩陣與伴隨

- 規範形式：列之列
- 範疇化：Hilb 態射；† 為 dagger 函子
- 判定：矩陣運算

| 符號 | 類別 |
|---|---|
| `CMat` | 結構 |
| `CMat.n` | 欄位 |
| `CMat.rows` | 欄位 |
| `mat_add` | 函數 |
| `mat_adjoint` | 函數 |
| `mat_approx_eq` | 函數 |
| `mat_commutes` | 函數 |
| `mat_from_rows` | 函數 |
| `mat_get` | 函數 |
| `mat_identity` | 函數 |
| `mat_mul` | 函數 |
| `mat_sub` | 函數 |
| `mat_trace_re` | 函數 |
| `mat_vec` | 函數 |
| `mat_zero` | 函數 |

### 投影與特徵空間

- 規範形式：Σ vₖvₖ†；分解為正交對 (Pv,(I−P)v)
- 範疇化：自伴冪等態射及其在 Hilb 中的分裂（雙積）
- 判定：特徵值方程／正交性／跡整數性

| 符號 | 類別 |
|---|---|
| `check_commuting` | 函數 |
| `check_eigenspace` | 函數 |
| `check_orthogonal_roundtrip` | 函數 |
| `check_projector` | 函數 |
| `commuting_product` | 函數 |
| `commuting_projectors_compatible` | 函數 |
| `complement` | 函數 |
| `decompose` | 函數 |
| `eigen_equations_hold` | 函數 |
| `eigenspace_kan_sound` | 函數 |
| `eigenspace_well_formed` | 函數 |
| `in_image` | 函數 |
| `in_kernel` | 函數 |
| `is_hermitian` | 函數 |
| `is_idempotent` | 函數 |
| `is_projector` | 函數 |
| `outer` | 函數 |
| `projector_certificate_ok` | 函數 |
| `projector_from_orthonormal` | 函數 |
| `prune_to_eigenspace` | 函數 |
| `pruning_is_retraction` | 函數 |

### Karoubi 包絡

- 規範形式：物件 P；態射被夾緊矩陣 QAP=A
- 範疇化：冪完備化；恒等是 P 本身；dagger
- 判定：QAP=A 與合成律

| 符號 | 類別 |
|---|---|
| `check_karoubi_category` | 函數 |
| `karoubi_comp` | 函數 |
| `karoubi_id` | 函數 |
| `karoubi_morphism` | 函數 |
| `karoubi_wrap` | 函數 |

### 區間

- 規範形式：De Morgan 表達式；端點布林化
- 範疇化：De Morgan 代數（區間物件）
- 判定：求值與重寫簡化

| 符號 | 類別 |
|---|---|
| `Dim` | 列舉 |
| `Dim::DAnd` | 構造子 |
| `Dim::DNeg` | 構造子 |
| `Dim::DOne` | 構造子 |
| `Dim::DOr` | 構造子 |
| `Dim::DVar` | 構造子 |
| `Dim::DZero` | 構造子 |
| `Dim::equal` | 函數 |
| `Dim::not_equal` | 函數 |
| `Dim::to_repr` | 函數 |
| `dmax` | 函數 |
| `dmin` | 函數 |
| `eval_dim` | 函數 |
| `eval_dim_bool` | 函數 |
| `interval_laws_hold` | 函數 |

### 面公式與 BDD

- 規範形式：由 interned DAG 展開的 ROBDD 樹（相容表示）；主判定在同一 manager 以 root 代表
- 範疇化：面格（自由有界分配格的商）的規範代表
- 判定：DAG apply/root 相等判定；樹形 API 為逐公式展開

| 符號 | 類別 |
|---|---|
| `Bdd` | 列舉 |
| `Bdd::BddNode` | 構造子 |
| `Bdd::BddOne` | 構造子 |
| `Bdd::BddZero` | 構造子 |
| `Bdd::equal` | 函數 |
| `Bdd::not_equal` | 函數 |
| `Bdd::to_repr` | 函數 |
| `Face` | 列舉 |
| `Face::FAnd` | 構造子 |
| `Face::FBot` | 構造子 |
| `Face::FEq0` | 構造子 |
| `Face::FEq1` | 構造子 |
| `Face::FOr` | 構造子 |
| `Face::FTop` | 構造子 |
| `Face::equal` | 函數 |
| `Face::not_equal` | 函數 |
| `Face::to_repr` | 函數 |
| `assignment_of_mask` | 函數 |
| `bdd_and` | 函數 |
| `bdd_face_eq` | 函數 |
| `bdd_face_le` | 函數 |
| `bdd_not` | 函數 |
| `bdd_of_face` | 函數 |
| `bdd_or` | 函數 |
| `bdd_sat_face` | 函數 |
| `bdd_satisfying_cubes` | 函數 |
| `check_bdd_canonical` | 函數 |
| `check_interval_faces` | 函數 |
| `contains_int` | 函數 |
| `dim_simplify` | 函數 |
| `dim_subst` | 函數 |
| `face_bound` | 函數 |
| `face_eq_mod` | 函數 |
| `face_holds` | 函數 |
| `face_join_universal` | 函數 |
| `face_le` | 函數 |
| `face_maps_commute` | 函數 |
| `face_meet_universal` | 函數 |
| `face_not` | 函數 |
| `face_of_bdd` | 函數 |
| `face_sat` | 函數 |
| `face_simplify` | 函數 |
| `face_subst` | 函數 |
| `face_unsat` | 函數 |
| `face_var0` | 函數 |
| `face_var1` | 函數 |
| `face_vars` | 函數 |
| `face_witness` | 函數 |
| `pow2` | 函數 |
| `sort_ints` | 函數 |

### 面偏序範疇

- 規範形式：BDD 等價類
- 範疇化：偏序範疇：∧積、∨餘積、⊤/⊥ 終始
- 判定：bdd_face_le 與萬有性等式

| 符號 | 類別 |
|---|---|
| `check_face_poset_category` | 函數 |

### 系統與剪枝

- 規範形式：分支列；語義範形見系統符號範形
- 範疇化：面上 presheaf 的偏元素；聯集拼接
- 判定：重疊面的 BDD 可滿足性

| 符號 | 類別 |
|---|---|
| `VecBranch` | 結構 |
| `VecBranch.face` | 欄位 |
| `VecBranch.value` | 欄位 |
| `VecSystem` | 結構 |
| `VecSystem.branches` | 欄位 |
| `branch` | 函數 |
| `check_systems` | 函數 |
| `compatibility_respects_quotient` | 函數 |
| `prune_system` | 函數 |
| `pruning_respects_quotient` | 函數 |
| `system_compatible` | 函數 |
| `system_domain_bdd` | 函數 |
| `system_eq_mod` | 函數 |
| `system_eq_mod_sym` | 函數 |
| `system_extend_top` | 函數 |
| `system_lookup` | 函數 |
| `system_normal_form` | 函數 |
| `system_of` | 函數 |
| `system_union` | 函數 |
| `union_commutes_mod` | 函數 |

### 系統符號範形

- 規範形式：值標記不交 BDD 分割＋未定義區域
- 範疇化：偏元素在面格切片中的像分解
- 判定：BDD 區域運算

| 符號 | 類別 |
|---|---|
| `SymRegion` | 結構 |
| `SymRegion.region` | 欄位 |
| `SymRegion.value` | 欄位 |
| `SystemNF` | 結構 |
| `SystemNF.classes` | 欄位 |
| `SystemNF.undefined` | 欄位 |
| `vec_lex_lt` | 函數 |

### 立方體與 Kan 填充

- 規範形式：函數 Iⁿ→Cᵐ；填充用仿射公式；帽子為 comp 結果
- 範疇化：□ 上 cubical set 的實現；retract 的 Kan 結構
- 判定：邊界方程（網格）

| 符號 | 類別 |
|---|---|
| `Cube` | 結構 |
| `Cube.cell` | 欄位 |
| `Cube.dim` | 欄位 |
| `bumped_filler` | 函數 |
| `check_cube3_and_moving_hit_comp` | 函數 |
| `check_cube_comp` | 函數 |
| `check_cubical_identities` | 函數 |
| `check_kan_pruning` | 函數 |
| `cube_const` | 函數 |
| `cube_eval` | 函數 |
| `cube_ext_eq` | 函數 |
| `cube_in_eigenspace` | 函數 |
| `degenerate_cube` | 函數 |
| `filler_respects_box` | 函數 |
| `kan_comp_eigenspace` | 函數 |
| `kan_comp_path` | 函數 |
| `kan_fill_eigenspace` | 函數 |
| `open_box_wf` | 函數 |
| `path_end` | 函數 |
| `path_eval` | 函數 |
| `path_line` | 函數 |
| `path_refl` | 函數 |
| `path_start` | 函數 |
| `path_sym` | 函數 |
| `path_trans` | 函數 |
| `path_trans_endpoints` | 函數 |
| `prune_cube` | 函數 |
| `pruning_repairs_filler` | 函數 |
| `restrict_face` | 函數 |
| `square_fill` | 函數 |

### 未型別 NbE

- 規範形式：βπ 正規形 nf
- 範疇化：句法範疇在 βπ 商下的態射代表
- 判定：eval/quote 後結構比較

| 符號 | 類別 |
|---|---|
| `Neutral` | 列舉 |
| `Neutral::NeApp` | 構造子 |
| `Neutral::NeFst` | 構造子 |
| `Neutral::NeSnd` | 構造子 |
| `Neutral::NeVar` | 構造子 |
| `Term` | 列舉 |
| `Term::TmAnn` | 構造子 |
| `Term::TmApp` | 構造子 |
| `Term::TmBool` | 構造子 |
| `Term::TmCoeRefl` | 構造子 |
| `Term::TmCoeUaSwap` | 構造子 |
| `Term::TmFst` | 構造子 |
| `Term::TmLam` | 構造子 |
| `Term::TmPair` | 構造子 |
| `Term::TmSnd` | 構造子 |
| `Term::TmUnit` | 構造子 |
| `Term::TmVar` | 構造子 |
| `Term::equal` | 函數 |
| `Term::not_equal` | 函數 |
| `Term::to_repr` | 函數 |
| `Value` | 列舉 |
| `Value::VBool` | 構造子 |
| `Value::VClosure` | 構造子 |
| `Value::VNeutral` | 構造子 |
| `Value::VPair` | 構造子 |
| `Value::VUnit` | 構造子 |
| `check_nbe` | 函數 |
| `coe_rules_definitional` | 函數 |
| `def_eq` | 函數 |
| `eval` | 函數 |
| `eval_check_t` | 函數 |
| `eval_decode_term` | 函數 |
| `eval_glue_equiv_term` | 函數 |
| `eval_inductive_decode` | 函數 |
| `eval_infer_t` | 函數 |
| `eval_mk_equiv_term` | 函數 |
| `eval_mutual_elim` | 函數 |
| `eval_ua_term` | 函數 |
| `nbe_single_valued` | 函數 |
| `nf` | 函數 |
| `quote` | 函數 |
| `quote_decode_neutral` | 函數 |
| `quote_glue_equiv_type` | 函數 |
| `quote_neutral` | 函數 |
| `quote_schema_args_full` | 函數 |
| `swap_involutive_on_element` | 函數 |
| `tm_const` | 函數 |
| `tm_id` | 函數 |
| `tm_swap` | 函數 |
| `vapp` | 函數 |
| `vfst` | 函數 |
| `vsnd` | 函數 |

### HOAS

- 規範形式：經 reify 的 de Bruijn 範形
- 範疇化：函子範疇式綁定；與一階語法範疇等價（模定義相等）
- 判定：reflect/reify 往返

| 符號 | 類別 |
|---|---|
| `HTm` | 列舉 |
| `HTm::HApp` | 構造子 |
| `HTm::HBool` | 構造子 |
| `HTm::HFst` | 構造子 |
| `HTm::HLam` | 構造子 |
| `HTm::HPair` | 構造子 |
| `HTm::HSnd` | 構造子 |
| `HTm::HUnit` | 構造子 |
| `HTm::HVar` | 構造子 |
| `check_hoas` | 函數 |
| `happ` | 函數 |
| `hfst` | 函數 |
| `hoas_const_example` | 函數 |
| `hoas_roundtrip_hoas` | 函數 |
| `hoas_roundtrip_term` | 函數 |
| `hoas_swap_example` | 函數 |
| `hoas_to_term` | 函數 |
| `hsnd` | 函數 |
| `term_to_hoas` | 函數 |

### 型別化 NbE 與 η

- 規範形式：η 長 βπ 範形 nf_eta
- 範疇化：自由笛卡兒閉範疇的態射代表
- 判定：雙向檢查＋按型別 quote

| 符號 | 類別 |
|---|---|
| `LTy` | 列舉 |
| `LTy::LBool` | 構造子 |
| `LTy::LFun` | 構造子 |
| `LTy::LProd` | 構造子 |
| `LTy::LUnit` | 構造子 |
| `LTy::equal` | 函數 |
| `LTy::not_equal` | 函數 |
| `LTy::to_repr` | 函數 |
| `TNeutral` | 列舉 |
| `TNeutral::TNeApp` | 構造子 |
| `TNeutral::TNeFst` | 構造子 |
| `TNeutral::TNeSnd` | 構造子 |
| `TNeutral::TNeVar` | 構造子 |
| `TValue` | 列舉 |
| `TValue::TVBool` | 構造子 |
| `TValue::TVClosure` | 構造子 |
| `TValue::TVNeutral` | 構造子 |
| `TValue::TVPair` | 構造子 |
| `TValue::TVUnit` | 構造子 |
| `TypedValue` | 結構 |
| `TypedValue.ty` | 欄位 |
| `TypedValue.value` | 欄位 |
| `check_eta_all` | 函數 |
| `check_eta_function` | 函數 |
| `check_eta_product` | 函數 |
| `check_eta_spine` | 函數 |
| `check_eta_swap_involution` | 函數 |
| `check_eta_unit` | 函數 |
| `def_eq_eta` | 函數 |
| `eta_single_valued_on` | 函數 |
| `nf_eta` | 函數 |
| `quote_eta` | 函數 |
| `quote_tneutral` | 函數 |
| `tapp` | 函數 |
| `tfst` | 函數 |
| `tm_coe_swap_at` | 函數 |
| `tm_swap_at` | 函數 |
| `tsnd` | 函數 |
| `ty_check` | 函數 |
| `ty_infer` | 函數 |

### 依賴型別 NbE（Π/Σ/宇宙）

- 規範形式：按型別 quote 的 η 長依賴正規形；Π/Σ 第二分量為語義閉包族；累積 Typeᵢ 層級
- 範疇化：帶族範疇 (CwF) 模型：脈絡延伸與依賴代入是閉包施用
- 判定：雙向 elaboration＋型別導向轉換；相等=範形相等

| 符號 | 類別 |
|---|---|
| `DFamilyParts` | 結構 |
| `DFamilyParts.dom` | 欄位 |
| `DFamilyParts.fam` | 欄位 |
| `DInfer` | 結構 |
| `DInfer.ty` | 欄位 |
| `DInfer.value` | 欄位 |
| `DNeutral` | 列舉 |
| `DNeutral::DNApp` | 構造子 |
| `DNeutral::DNAppDim` | 構造子 |
| `DNeutral::DNBoolElim` | 構造子 |
| `DNeutral::DNCircleElim` | 構造子 |
| `DNeutral::DNComp` | 構造子 |
| `DNeutral::DNDecode` | 構造子 |
| `DNeutral::DNEquivBwd` | 構造子 |
| `DNeutral::DNEquivFwd` | 構造子 |
| `DNeutral::DNEquivRetr` | 構造子 |
| `DNeutral::DNEquivSect` | 構造子 |
| `DNeutral::DNFst` | 構造子 |
| `DNeutral::DNHComp` | 構造子 |
| `DNeutral::DNHitElim` | 構造子 |
| `DNeutral::DNInductiveElim` | 構造子 |
| `DNeutral::DNListElim` | 構造子 |
| `DNeutral::DNNatElim` | 構造子 |
| `DNeutral::DNSnd` | 構造子 |
| `DNeutral::DNTorusElim` | 構造子 |
| `DNeutral::DNVar` | 構造子 |
| `DTerm` | 列舉 |
| `DTerm::DAnn` | 構造子 |
| `DTerm::DApp` | 構造子 |
| `DTerm::DAppDim` | 構造子 |
| `DTerm::DBoolElim` | 構造子 |
| `DTerm::DBoolLit` | 構造子 |
| `DTerm::DBoolTy` | 構造子 |
| `DTerm::DCircleBase` | 構造子 |
| `DTerm::DCircleElim` | 構造子 |
| `DTerm::DCircleLoop` | 構造子 |
| `DTerm::DCircleTy` | 構造子 |
| `DTerm::DCoe` | 構造子 |
| `DTerm::DComp` | 構造子 |
| `DTerm::DCons` | 構造子 |
| `DTerm::DDecode` | 構造子 |
| `DTerm::DEquivBwd` | 構造子 |
| `DTerm::DEquivFwd` | 構造子 |
| `DTerm::DEquivRetr` | 構造子 |
| `DTerm::DEquivSect` | 構造子 |
| `DTerm::DEquivTy` | 構造子 |
| `DTerm::DFst` | 構造子 |
| `DTerm::DGlueEquiv` | 構造子 |
| `DTerm::DHComp` | 構造子 |
| `DTerm::DHFill` | 構造子 |
| `DTerm::DHitElim` | 構造子 |
| `DTerm::DHitIntro` | 構造子 |
| `DTerm::DHitType` | 構造子 |
| `DTerm::DInductive` | 構造子 |
| `DTerm::DInductiveElim` | 構造子 |
| `DTerm::DIntro` | 構造子 |
| `DTerm::DLam` | 構造子 |
| `DTerm::DLamDim` | 構造子 |
| `DTerm::DListElim` | 構造子 |
| `DTerm::DListTy` | 構造子 |
| `DTerm::DMkEquiv` | 構造子 |
| `DTerm::DNatElim` | 構造子 |
| `DTerm::DNatTy` | 構造子 |
| `DTerm::DNatZero` | 構造子 |
| `DTerm::DNil` | 構造子 |
| `DTerm::DPair` | 構造子 |
| `DTerm::DPartial` | 構造子 |
| `DTerm::DPath` | 構造子 |
| `DTerm::DPathP` | 構造子 |
| `DTerm::DPi` | 構造子 |
| `DTerm::DSigma` | 構造子 |
| `DTerm::DSnd` | 構造子 |
| `DTerm::DSucc` | 構造子 |
| `DTerm::DTVar` | 構造子 |
| `DTerm::DTorusBase` | 構造子 |
| `DTerm::DTorusElim` | 構造子 |
| `DTerm::DTorusLoopA` | 構造子 |
| `DTerm::DTorusLoopB` | 構造子 |
| `DTerm::DTorusSquare` | 構造子 |
| `DTerm::DTorusTy` | 構造子 |
| `DTerm::DUa` | 構造子 |
| `DTerm::DUnitLit` | 構造子 |
| `DTerm::DUnitTy` | 構造子 |
| `DTerm::DUniv` | 構造子 |
| `DTerm::equal` | 函數 |
| `DTerm::not_equal` | 函數 |
| `DTerm::to_repr` | 函數 |
| `DTypeVal` | 結構 |
| `DTypeVal.level` | 欄位 |
| `DTypeVal.value` | 欄位 |
| `DValue` | 列舉 |
| `DValue::DVBool` | 構造子 |
| `DValue::DVBoolTy` | 構造子 |
| `DValue::DVCirclePoint` | 構造子 |
| `DValue::DVCircleTy` | 構造子 |
| `DValue::DVCons` | 構造子 |
| `DValue::DVEquiv` | 構造子 |
| `DValue::DVEquivTy` | 構造子 |
| `DValue::DVGlue` | 構造子 |
| `DValue::DVGlueEquiv` | 構造子 |
| `DValue::DVHitCell` | 構造子 |
| `DValue::DVHitType` | 構造子 |
| `DValue::DVInductive` | 構造子 |
| `DValue::DVIntro` | 構造子 |
| `DValue::DVLam` | 構造子 |
| `DValue::DVListTy` | 構造子 |
| `DValue::DVNatTy` | 構造子 |
| `DValue::DVNeutral` | 構造子 |
| `DValue::DVNil` | 構造子 |
| `DValue::DVPair` | 構造子 |
| `DValue::DVPartial` | 構造子 |
| `DValue::DVPathLam` | 構造子 |
| `DValue::DVPathTy` | 構造子 |
| `DValue::DVPi` | 構造子 |
| `DValue::DVSigma` | 構造子 |
| `DValue::DVSucc` | 構造子 |
| `DValue::DVThunk` | 構造子 |
| `DValue::DVTorusPoint` | 構造子 |
| `DValue::DVTorusTy` | 構造子 |
| `DValue::DVUnit` | 構造子 |
| `DValue::DVUnitTy` | 構造子 |
| `DValue::DVUniv` | 構造子 |
| `DValue::DVZeroNat` | 構造子 |
| `as_pi` | 函數 |
| `as_sigma` | 函數 |
| `as_univ_level` | 函數 |
| `check_dep_all` | 函數 |
| `check_dep_pi` | 函數 |
| `check_dep_sigma` | 函數 |
| `check_dep_universe` | 函數 |
| `conv_at` | 函數 |
| `conv_neutral` | 函數 |
| `conv_ty` | 函數 |
| `d_as_type` | 函數 |
| `d_check` | 函數 |
| `d_infer` | 函數 |
| `dapp_typed` | 函數 |
| `dep_check_closed` | 函數 |
| `dep_id_term` | 函數 |
| `dep_id_type` | 函數 |
| `dep_nf_closed` | 函數 |
| `dep_type_of_closed` | 函數 |
| `dep_type_val_of` | 函數 |
| `deval` | 函數 |
| `dfst_typed` | 函數 |
| `dsnd_typed` | 函數 |
| `lty_to_dterm` | 函數 |
| `quote_at` | 函數 |
| `quote_dneutral` | 函數 |
| `quote_ty` | 函數 |

### 立方 AST 與維度 NbE

- 規範形式：DTerm 的項/維度雙 de Bruijn 索引；線與 tube body；帶 dlevel 的 quote
- 範疇化：帶區間脈絡的 cubical CwF；PathP 為依賴路徑物件，Glue 值為 (raw/DPartial partial,base) 對
- 判定：雙向檢查＋Dim/Face 簡化及 ROBDD 語義謂詞

| 符號 | 類別 |
|---|---|
| `DGlueParts` | 結構 |
| `DGlueParts.base` | 欄位 |
| `DGlueParts.face` | 欄位 |
| `DGlueParts.level` | 欄位 |
| `DGlueParts.line` | 欄位 |
| `DGlueParts.system` | 欄位 |
| `DPathParts` | 結構 |
| `DPathParts.left` | 欄位 |
| `DPathParts.line` | 欄位 |
| `DPathParts.right` | 欄位 |
| `DTubeTerm` | 結構 |
| `DTubeTerm.body` | 欄位 |
| `DTubeTerm.face` | 欄位 |
| `DTubeTerm::equal` | 函數 |
| `DTubeTerm::not_equal` | 函數 |
| `DTubeTerm::to_repr` | 函數 |
| `as_glue` | 函數 |
| `as_list_elem` | 函數 |
| `as_path` | 函數 |
| `check_ast_paths` | 函數 |
| `d_tube` | 函數 |
| `dapp_dim` | 函數 |
| `dep_def_eq_closed` | 函數 |
| `deval_dim` | 函數 |
| `dim_quote` | 函數 |
| `eval_dim_expr` | 函數 |
| `eval_tube_terms` | 函數 |
| `face_eval_env` | 函數 |
| `face_quote` | 函數 |
| `fresh_dim` | 函數 |
| `quote_tube_branches` | 函數 |

### AST Kan comp/hcomp

- 規範形式：分支一律攜帶為 DSystem；在一般維度按型別頭派遣；頂分支取帽、形式合成為 DNComp/DNHComp
- 範疇化：各型別構造子保存 Kan 纖維化結構；hcompU 是 Glue 黏合
- 判定：系統 base/重疊相容＋型別遞迴；coe/fill 為 comp 線段限制

| 符號 | 類別 |
|---|---|
| `check_ast_coe_terms` | 函數 |
| `check_ast_hcomp_data_terms` | 函數 |
| `check_ast_hcomp_hit_terms` | 函數 |
| `check_ast_hcomp_sigma_path_terms` | 函數 |
| `check_ast_hcomp_univ_term` | 函數 |
| `check_ast_kan_all` | 函數 |
| `check_ast_kan_terms` | 函數 |
| `check_ast_kan_types` | 函數 |
| `coe_value` | 函數 |
| `comp_glue_value` | 函數 |
| `comp_path_value` | 函數 |
| `comp_pi_value` | 函數 |
| `comp_sigma_value` | 函數 |
| `comp_univ_value` | 函數 |
| `comp_value` | 函數 |
| `dim_eq_sem` | 函數 |
| `dim_nvars_sem` | 函數 |
| `dim_vars_of` | 函數 |
| `face_is_bot_sem` | 函數 |
| `face_is_sat_sem` | 函數 |
| `face_is_top_sem` | 函數 |
| `face_nvars_sem` | 函數 |
| `fill_value` | 函數 |
| `hcomp_univ_value` | 函數 |
| `hcomp_value` | 函數 |
| `hfill_value` | 函數 |

### 資料型別與 HIT 消去

- 規範形式：Nat/List 構造子遞迴；Circle loop@r；Torus square@(i,j) 模對邊等同
- 範疇化：初始代數與 HIT 的依賴消去是 motive 截面，並與形式 composition 交換
- 判定：構造子模式遞迴、Dim 語義相等、motive 中的 comp

| 符號 | 類別 |
|---|---|
| `check_ast_bool_elim` | 函數 |
| `check_ast_data` | 函數 |
| `check_ast_hits` | 函數 |
| `check_ast_list_len` | 函數 |
| `check_ast_nat_dep` | 函數 |
| `check_ast_nat_pred` | 函數 |
| `circle_dim_of` | 函數 |
| `circle_point` | 函數 |
| `comp_bool_value` | 函數 |
| `comp_circle_value` | 函數 |
| `comp_list_value` | 函數 |
| `comp_nat_value` | 函數 |
| `comp_torus_value` | 函數 |
| `d_nat_lit` | 函數 |
| `dv_nat_lit` | 函數 |
| `eval_bool_elim` | 函數 |
| `eval_circle_elim` | 函數 |
| `eval_list_elim` | 函數 |
| `eval_nat_elim` | 函數 |
| `eval_torus_elim` | 函數 |
| `torus_dims_of` | 函數 |
| `torus_point` | 函數 |

### 持久環境、惰性與語義快取

- 規範形式：帶長度持久連結串列 DEnv/DDimEnv（de Bruijn 頭在最內）；DVThunk 最多強制一次；快取鍵為簡化維度/引文項 Debug 鍵
- 範疇化：CwF 脈絡延伸是共享尾部的 cons；惰性值是 call-by-need 語義值，memoized 族/維度線是外延函數的有限圖延伸
- 判定：環境索引、force_count 與快取鍵相等

| 符號 | 類別 |
|---|---|
| `DDimEnv` | 列舉 |
| `DDimEnv::DDimEnvCons` | 構造子 |
| `DDimEnv::DDimEnvNil` | 構造子 |
| `DEnv` | 列舉 |
| `DEnv::DEnvCons` | 構造子 |
| `DEnv::DEnvNil` | 構造子 |
| `DThunk` | 結構 |
| `DThunk.compute` | 欄位 |
| `DThunk.force_count` | 欄位 |
| `DThunk.forced` | 欄位 |
| `check_persistent_env_lazy_cache` | 函數 |
| `ddim_at` | 函數 |
| `ddim_cons` | 函數 |
| `ddim_empty` | 函數 |
| `ddim_extend` | 函數 |
| `ddim_from_array` | 函數 |
| `ddim_len` | 函數 |
| `ddim_to_array` | 函數 |
| `denv_at` | 函數 |
| `denv_cons` | 函數 |
| `denv_empty` | 函數 |
| `denv_extend` | 函數 |
| `denv_from_array` | 函數 |
| `denv_len` | 函數 |
| `denv_tail` | 函數 |
| `denv_to_array` | 函數 |
| `dim_cache_key` | 函數 |
| `dterm_cache_key` | 函數 |
| `force_value` | 函數 |
| `lazy_deval` | 函數 |
| `lazy_force_count` | 函數 |
| `lazy_is_forced` | 函數 |
| `lazy_value` | 函數 |
| `memo_dim_line` | 函數 |
| `memo_family` | 函數 |

### 依賴語義系統與 partial 值

- 規範形式：DSystem 分支去 ⊥、按值合併同 body 並以引文排序；DPartialValue 的 BDD 有效區域分割 DSystemNF
- 範疇化：面格切片中的偏元素；多分支 Glue 為 partial type 系統與 base 的極限式配對
- 判定：BDD 區域運算＋分支 body 的型別導向轉換/引文鍵

| 符號 | 類別 |
|---|---|
| `DFaceTerm` | 結構 |
| `DFaceTerm.body` | 欄位 |
| `DFaceTerm.face` | 欄位 |
| `DFaceTerm::equal` | 函數 |
| `DFaceTerm::not_equal` | 函數 |
| `DFaceTerm::to_repr` | 函數 |
| `DFaceValue` | 結構 |
| `DFaceValue.face` | 欄位 |
| `DFaceValue.value` | 欄位 |
| `DPartialValue` | 結構 |
| `DPartialValue.branches` | 欄位 |
| `DSystem` | 結構 |
| `DSystem.branches` | 欄位 |
| `DSystemClass` | 結構 |
| `DSystemClass.region` | 欄位 |
| `DSystemClass.value` | 欄位 |
| `DSystemNF` | 結構 |
| `DSystemNF.classes` | 欄位 |
| `DSystemNF.undefined` | 欄位 |
| `DTubeBranch` | 結構 |
| `DTubeBranch.face` | 欄位 |
| `DTubeBranch.path` | 欄位 |
| `check_dsystem_canonical_partial_nf` | 函數 |
| `check_multibranch_glue_partial` | 函數 |
| `check_phase5_semantic_systems` | 函數 |
| `d_face_term` | 函數 |
| `dface_value` | 函數 |
| `dsystem_canonical` | 函數 |
| `dsystem_checked` | 函數 |
| `dsystem_checked_of` | 函數 |
| `dsystem_compatibility` | 函數 |
| `dsystem_compatibility_report` | 函數 |
| `dsystem_compatible_with_base` | 函數 |
| `dsystem_domain_face` | 函數 |
| `dsystem_empty` | 函數 |
| `dsystem_first_match_checked` | 函數 |
| `dsystem_first_match_eq` | 函數 |
| `dsystem_first_match_normal_form` | 函數 |
| `dsystem_first_match_system` | 函數 |
| `dsystem_first_path` | 函數 |
| `dsystem_map` | 函數 |
| `dsystem_of` | 函數 |
| `dsystem_of_first_match_nf` | 函數 |
| `dsystem_pairwise_compatible` | 函數 |
| `dsystem_singleton` | 函數 |
| `glue_partial_values` | 函數 |
| `glue_store_partial` | 函數 |
| `map_branches` | 函數 |
| `partial_domain_bdd` | 函數 |
| `partial_empty` | 函數 |
| `partial_eq_at` | 函數 |
| `partial_normal_form` | 函數 |
| `partial_of` | 函數 |
| `partial_singleton` | 函數 |
| `tube_branch` | 函數 |
| `tube_system_nf_at` | 函數 |

### 通用歸納族 schema

- 規範形式：telescope＋完整 DTerm 引數型別（外部、直接/巢狀/函數遞迴與約束）；值為 DVIntro，中性消去按生成 case 型別引文
- 範疇化：結構化嚴格正性函子的依賴初始代數；消去子是 motive 截面，comp 沿先前引數 filler 遞迴
- 判定：schema 結構相等、telescope elaboration、極性正性判定與生成檢查

| 符號 | 類別 |
|---|---|
| `DArgKind` | 列舉 |
| `DArgKind::DArgDecoded` | 構造子 |
| `DArgKind::DArgDecodedFunction` | 構造子 |
| `DArgKind::DArgExternal` | 構造子 |
| `DArgKind::DArgFunction` | 構造子 |
| `DArgKind::DArgNested` | 構造子 |
| `DArgKind::DArgRecursive` | 構造子 |
| `DArgKind::equal` | 函數 |
| `DArgKind::not_equal` | 函數 |
| `DArgKind::to_repr` | 函數 |
| `DConstructorArg` | 結構 |
| `DConstructorArg.index` | 欄位 |
| `DConstructorArg.kind` | 欄位 |
| `DConstructorArg.name` | 欄位 |
| `DConstructorArg.nested` | 欄位 |
| `DConstructorArg.target` | 欄位 |
| `DConstructorArg.ty` | 欄位 |
| `DConstructorArg::equal` | 函數 |
| `DConstructorArg::not_equal` | 函數 |
| `DConstructorArg::to_repr` | 函數 |
| `DConstructorSpec` | 結構 |
| `DConstructorSpec.args` | 欄位 |
| `DConstructorSpec.constraints` | 欄位 |
| `DConstructorSpec.name` | 欄位 |
| `DConstructorSpec.result_index` | 欄位 |
| `DConstructorSpec::equal` | 函數 |
| `DConstructorSpec::not_equal` | 函數 |
| `DConstructorSpec::to_repr` | 函數 |
| `DInductiveSpec` | 結構 |
| `DInductiveSpec.constructors` | 欄位 |
| `DInductiveSpec.decode_cases` | 欄位 |
| `DInductiveSpec.decode_level` | 欄位 |
| `DInductiveSpec.indices` | 欄位 |
| `DInductiveSpec.level` | 欄位 |
| `DInductiveSpec.name` | 欄位 |
| `DInductiveSpec.params` | 欄位 |
| `DInductiveSpec::equal` | 函數 |
| `DInductiveSpec::not_equal` | 函數 |
| `DInductiveSpec::to_repr` | 函數 |
| `DTelescopeEntry` | 結構 |
| `DTelescopeEntry.name` | 欄位 |
| `DTelescopeEntry.ty` | 欄位 |
| `DTelescopeEntry::equal` | 函數 |
| `DTelescopeEntry::not_equal` | 函數 |
| `DTelescopeEntry::to_repr` | 函數 |
| `bool_schema` | 函數 |
| `check_generated_inductive_schemas` | 函數 |
| `check_schema_indexed` | 函數 |
| `check_schema_inductive_comp` | 函數 |
| `check_schema_list` | 函數 |
| `check_schema_nat_add` | 函數 |
| `check_schema_nat_neutral_quote` | 函數 |
| `check_schema_tree` | 函數 |
| `check_schema_validation` | 函數 |
| `check_schema_vec_comp` | 函數 |
| `check_schema_w` | 函數 |
| `check_telescope_terms` | 函數 |
| `comp_inductive_value` | 函數 |
| `comp_schema_args` | 函數 |
| `conv_inductive_elim_neutral` | 函數 |
| `conv_inductive_type` | 函數 |
| `conv_intro_at` | 函數 |
| `conv_schema_args` | 函數 |
| `conv_telescope_values` | 函數 |
| `darg_decoded` | 函數 |
| `darg_decoded_function` | 函數 |
| `darg_external` | 函數 |
| `darg_function` | 函數 |
| `darg_mutual` | 函數 |
| `darg_mutual_function` | 函數 |
| `darg_nested` | 函數 |
| `darg_recursive` | 函數 |
| `dconstructor_constraint` | 函數 |
| `dconstructor_spec` | 函數 |
| `dconstructor_spec_constrained` | 函數 |
| `dinductive_level_scheme` | 函數 |
| `dinductive_recursive_spec` | 函數 |
| `dinductive_spec` | 函數 |
| `dtelescope_entry` | 函數 |
| `eval_inductive_elim` | 函數 |
| `eval_inductive_elim_term` | 函數 |
| `eval_inductive_type_term` | 函數 |
| `eval_intro_term` | 函數 |
| `fin_schema` | 函數 |
| `inductive_arg_type` | 函數 |
| `inductive_arg_type_full` | 函數 |
| `inductive_case_type` | 函數 |
| `inductive_decode_cases_validate` | 函數 |
| `inductive_index_types` | 函數 |
| `inductive_index_types_cached` | 函數 |
| `inductive_motive_type` | 函數 |
| `inductive_param_types` | 函數 |
| `inductive_param_types_cached` | 函數 |
| `inductive_parameter_positivity` | 函數 |
| `inductive_plan_type_term` | 函數 |
| `inductive_result_indices` | 函數 |
| `inductive_schema_key` | 函數 |
| `inductive_schema_validate` | 函數 |
| `infer_inductive_elim` | 函數 |
| `infer_inductive_type` | 函數 |
| `infer_intro` | 函數 |
| `list_schema` | 函數 |
| `nat_schema` | 函數 |
| `nat_schema_lit` | 函數 |
| `quote_inductive_elim_neutral` | 函數 |
| `quote_inductive_type` | 函數 |
| `quote_intro_at` | 函數 |
| `quote_schema_args` | 函數 |
| `quote_schema_motive` | 函數 |
| `quote_telescope_values` | 函數 |
| `schema_apply_constraint_proofs` | 函數 |
| `schema_arg_spec_prefix` | 函數 |
| `schema_arg_type` | 函數 |
| `schema_arg_type_full` | 函數 |
| `schema_concat_values` | 函數 |
| `schema_constraint_parts` | 函數 |
| `schema_constraints_hold` | 函數 |
| `schema_constraints_pi` | 函數 |
| `schema_elim_term` | 函數 |
| `schema_examples` | 函數 |
| `schema_intro_term` | 函數 |
| `schema_motives_conv` | 函數 |
| `schema_registry_hit_by_id` | 函數 |
| `schema_registry_hit_by_name` | 函數 |
| `schema_registry_hit_plan` | 函數 |
| `schema_registry_inductive_by_id` | 函數 |
| `schema_registry_inductive_by_name` | 函數 |
| `schema_registry_inductive_plan` | 函數 |
| `schema_registry_new` | 函數 |
| `schema_registry_register_hit` | 函數 |
| `schema_registry_register_inductive` | 函數 |
| `schema_registry_stats` | 函數 |
| `schema_registry_validate_hit` | 函數 |
| `schema_registry_validate_inductive` | 函數 |
| `schema_telescope_family_occurs` | 函數 |
| `schema_type_term` | 函數 |
| `schema_value_prefix` | 函數 |
| `telescope_next_type` | 函數 |
| `telescope_type_values` | 函數 |
| `telescope_type_values_cached` | 函數 |
| `tree_schema` | 函數 |
| `vec_schema` | 函數 |
| `w_schema` | 函數 |

### 通用 HIT schema

- 規範形式：任意有限維 cell；任一端點按 face expression 逐維化簡；case 為逐維巢狀 PathP
- 範疇化：帶 face 映射的胞腔型高階初始代數；消去子保存各維 cells
- 判定：face 引數/索引檢查、多維角落雙路化簡轉換與維度語義相等

| 符號 | 類別 |
|---|---|
| `DHitCellSpec` | 結構 |
| `DHitCellSpec.args` | 欄位 |
| `DHitCellSpec.constraints` | 欄位 |
| `DHitCellSpec.dim_count` | 欄位 |
| `DHitCellSpec.faces` | 欄位 |
| `DHitCellSpec.name` | 欄位 |
| `DHitCellSpec.result_index` | 欄位 |
| `DHitCellSpec::equal` | 函數 |
| `DHitCellSpec::not_equal` | 函數 |
| `DHitCellSpec::to_repr` | 函數 |
| `DHitFaceExpr` | 結構 |
| `DHitFaceExpr.args` | 欄位 |
| `DHitFaceExpr.cell` | 欄位 |
| `DHitFaceExpr.dims` | 欄位 |
| `DHitFaceExpr::equal` | 函數 |
| `DHitFaceExpr::not_equal` | 函數 |
| `DHitFaceExpr::to_repr` | 函數 |
| `DHitSpec` | 結構 |
| `DHitSpec.cells` | 欄位 |
| `DHitSpec.indices` | 欄位 |
| `DHitSpec.level` | 欄位 |
| `DHitSpec.name` | 欄位 |
| `DHitSpec.params` | 欄位 |
| `DHitSpec::equal` | 函數 |
| `DHitSpec::not_equal` | 函數 |
| `DHitSpec::to_repr` | 函數 |
| `check_generated_hit_schemas` | 函數 |
| `check_hit_endpoint_conversion` | 函數 |
| `check_hit_schema_arguments` | 函數 |
| `check_hit_schema_circle_segment` | 函數 |
| `check_hit_schema_torus_comp` | 函數 |
| `check_hit_schema_validation` | 函數 |
| `circle_schema` | 函數 |
| `comp_hit_value` | 函數 |
| `conv_hit_cell_at` | 函數 |
| `conv_hit_elim_neutral` | 函數 |
| `conv_hit_type` | 函數 |
| `dhit_cell_spec` | 函數 |
| `dhit_face` | 函數 |
| `dhit_level_scheme` | 函數 |
| `dhit_spec` | 函數 |
| `eval_hit_elim` | 函數 |
| `eval_hit_elim_term` | 函數 |
| `eval_hit_intro_term` | 函數 |
| `eval_hit_type_term` | 函數 |
| `hit_arg_type` | 函數 |
| `hit_case_type` | 函數 |
| `hit_cell_result_indices` | 函數 |
| `hit_cell_value` | 函數 |
| `hit_elim_term` | 函數 |
| `hit_index_types` | 函數 |
| `hit_index_types_cached` | 函數 |
| `hit_intro_term` | 函數 |
| `hit_motive_type` | 函數 |
| `hit_param_types` | 函數 |
| `hit_param_types_cached` | 函數 |
| `hit_parameter_positivity` | 函數 |
| `hit_plan_type_term` | 函數 |
| `hit_result_indices` | 函數 |
| `hit_schema_examples` | 函數 |
| `hit_schema_key` | 函數 |
| `hit_schema_validate` | 函數 |
| `hit_type_term` | 函數 |
| `infer_hit_elim` | 函數 |
| `infer_hit_intro` | 函數 |
| `infer_hit_type` | 函數 |
| `quote_hit_cell_at` | 函數 |
| `quote_hit_elim_neutral` | 函數 |
| `quote_hit_type` | 函數 |
| `segment_schema` | 函數 |
| `torus_schema` | 函數 |

### 依賴 Kan 線（coe/comp）

- 規範形式：DLine{at, coe, fill}，comp=fill(1)；coe 在 Π 定義域反向、在 Σ 沿第一分量路徑
- 範疇化：型別即 Kan 纖維化結構；依賴族為 (路徑)→DLine；與子空間/Glue 線共同覆蓋全型別族
- 判定：按型別構造子遞迴；coe(r,r) 定義恆等

| 符號 | 類別 |
|---|---|
| `DLine` | 結構 |
| `DLine.at` | 欄位 |
| `DLine.coe_fn` | 欄位 |
| `DLine.fill_fn` | 欄位 |
| `check_kan_all_types` | 函數 |
| `check_kan_coe_dependent` | 函數 |
| `check_kan_coe_pi_sigma` | 函數 |
| `check_kan_comp_tube` | 函數 |
| `check_kan_dep_all` | 函數 |
| `check_kan_embeddings` | 函數 |
| `dbool_not` | 函數 |
| `dcoe` | 函數 |
| `dcomp` | 函數 |
| `dfill` | 函數 |
| `dline_at` | 函數 |
| `dline_bool` | 函數 |
| `dline_bool_not_ua` | 函數 |
| `dline_const` | 函數 |
| `dline_from_maps` | 函數 |
| `dline_of_lty` | 函數 |
| `dline_of_ty` | 函數 |
| `dline_of_upath` | 函數 |
| `dline_pi` | 函數 |
| `dline_pi_constfam` | 函數 |
| `dline_sigma` | 函數 |
| `dline_sigma_constfam` | 函數 |
| `dline_unit` | 函數 |
| `dline_univ` | 函數 |
| `dvalue_of_ty` | 函數 |
| `dvalue_to_pval` | 函數 |
| `path_from` | 函數 |

### 精確符號代數

- 規範形式：Q 上多變量多項式規範形（合併去零排序）；分式；複符號量 (re,im)
- 範疇化：多項式戒與分式體承載矩陣代數；共軛為對合
- 判定：多項式恆等／分式交叉相乘（精確）

| 符號 | 類別 |
|---|---|
| `Poly` | 結構 |
| `Poly.terms` | 欄位 |
| `PolyTerm` | 結構 |
| `PolyTerm.coeff` | 欄位 |
| `PolyTerm.exps` | 欄位 |
| `Rat` | 結構 |
| `Rat.den` | 欄位 |
| `Rat.num` | 欄位 |
| `Rat::equal` | 函數 |
| `Rat::not_equal` | 函數 |
| `Rat::to_repr` | 函數 |
| `SymC` | 結構 |
| `SymC.im` | 欄位 |
| `SymC.re` | 欄位 |
| `SymFrac` | 結構 |
| `SymFrac.den` | 欄位 |
| `SymFrac.num` | 欄位 |
| `SymMat` | 結構 |
| `SymMat.n` | 欄位 |
| `SymMat.rows` | 欄位 |
| `SymVec` | 型別別名 |
| `UPoly` | 結構 |
| `UPoly.coeffs` | 欄位 |
| `charpoly_sym` | 函數 |
| `frac_add` | 函數 |
| `frac_div` | 函數 |
| `frac_eq` | 函數 |
| `frac_int` | 函數 |
| `frac_is_zero` | 函數 |
| `frac_make` | 函數 |
| `frac_mul` | 函數 |
| `frac_neg` | 函數 |
| `frac_one` | 函數 |
| `frac_poly` | 函數 |
| `frac_rat` | 函數 |
| `frac_sub` | 函數 |
| `frac_var` | 函數 |
| `frac_zero` | 函數 |
| `int_abs` | 函數 |
| `int_gcd` | 函數 |
| `poly_add` | 函數 |
| `poly_const` | 函數 |
| `poly_eq` | 函數 |
| `poly_int` | 函數 |
| `poly_is_zero` | 函數 |
| `poly_mul` | 函數 |
| `poly_neg` | 函數 |
| `poly_normalize` | 函數 |
| `poly_one` | 函數 |
| `poly_scale` | 函數 |
| `poly_sub` | 函數 |
| `poly_var` | 函數 |
| `poly_zero` | 函數 |
| `rat_add` | 函數 |
| `rat_div` | 函數 |
| `rat_eq` | 函數 |
| `rat_int` | 函數 |
| `rat_inv` | 函數 |
| `rat_is_one` | 函數 |
| `rat_is_square` | 函數 |
| `rat_is_zero` | 函數 |
| `rat_make` | 函數 |
| `rat_mul` | 函數 |
| `rat_neg` | 函數 |
| `rat_one` | 函數 |
| `rat_sign` | 函數 |
| `rat_sqrt_if_square` | 函數 |
| `rat_sub` | 函數 |
| `rat_zero` | 函數 |
| `sc_add` | 函數 |
| `sc_conj` | 函數 |
| `sc_eq` | 函數 |
| `sc_i` | 函數 |
| `sc_int` | 函數 |
| `sc_is_zero` | 函數 |
| `sc_make` | 函數 |
| `sc_mul` | 函數 |
| `sc_neg` | 函數 |
| `sc_one` | 函數 |
| `sc_rat` | 函數 |
| `sc_real_frac` | 函數 |
| `sc_scale_frac` | 函數 |
| `sc_sub` | 函數 |
| `sc_var` | 函數 |
| `sc_zero` | 函數 |
| `sym_det` | 函數 |
| `sym_inner` | 函數 |
| `sym_is_hermitian` | 函數 |
| `sym_is_idempotent` | 函數 |
| `sym_mat_add` | 函數 |
| `sym_mat_adjoint` | 函數 |
| `sym_mat_eq` | 函數 |
| `sym_mat_from_rows` | 函數 |
| `sym_mat_identity` | 函數 |
| `sym_mat_mul` | 函數 |
| `sym_mat_of_qmat` | 函數 |
| `sym_mat_scale` | 函數 |
| `sym_mat_sub` | 函數 |
| `sym_mat_trace` | 函數 |
| `sym_mat_vec` | 函數 |
| `sym_mat_zero` | 函數 |
| `sym_outer` | 函數 |
| `sym_projector_rank_one` | 函數 |
| `sym_scalar_matrix` | 函數 |
| `sym_vec_add` | 函數 |
| `sym_vec_eq` | 函數 |
| `sym_vec_scale` | 函數 |
| `sym_vec_scale_c` | 函數 |
| `sym_vec_sub` | 函數 |
| `upoly_add` | 函數 |
| `upoly_const` | 函數 |
| `upoly_eq` | 函數 |
| `upoly_mul` | 函數 |
| `upoly_neg` | 函數 |
| `upoly_normalize` | 函數 |
| `upoly_of_rpoly` | 函數 |
| `upoly_sub` | 函數 |
| `upoly_x` | 函數 |
| `upoly_zero` | 函數 |

### 譜投影與仿射唯一填充

- 規範形式：Pₖ=qₖ(A)/qₖ(λₖ)；雙線性角插值 k00+i k10+j k01+ij k11
- 範疇化：單位分解與譜分解；雙線性是兩仿射方向的張量黏合
- 判定：首一整除（模最小多項式）與在原子 i,j 的恆等

| 符號 | 類別 |
|---|---|
| `RPoly` | 結構 |
| `RPoly.coeffs` | 欄位 |
| `RPolyDiv` | 結構 |
| `RPolyDiv.quotient` | 欄位 |
| `RPolyDiv.remainder` | 欄位 |
| `SymPath` | 型別別名 |
| `SymSquare` | 型別別名 |
| `check_spectral_identities` | 函數 |
| `check_spectral_matrices` | 函數 |
| `check_symbolic_affine_filler` | 函數 |
| `check_symbolic_algebra_all` | 函數 |
| `check_symbolic_nonlinear_boundary` | 函數 |
| `check_symbolic_pruning` | 函數 |
| `rpoly_add` | 函數 |
| `rpoly_const` | 函數 |
| `rpoly_degree` | 函數 |
| `rpoly_divisible_by` | 函數 |
| `rpoly_divmod_monic` | 函數 |
| `rpoly_eq` | 函數 |
| `rpoly_eval` | 函數 |
| `rpoly_eval_mat` | 函數 |
| `rpoly_factor` | 函數 |
| `rpoly_is_zero` | 函數 |
| `rpoly_mul` | 函數 |
| `rpoly_neg` | 函數 |
| `rpoly_normalize` | 函數 |
| `rpoly_one` | 函數 |
| `rpoly_scale` | 函數 |
| `rpoly_sub` | 函數 |
| `rpoly_x` | 函數 |
| `rpoly_zero` | 函數 |
| `spectral_denominator` | 函數 |
| `spectral_minpoly` | 函數 |
| `spectral_projector_sym` | 函數 |
| `spectral_q` | 函數 |
| `sym_affine_path` | 函數 |
| `sym_bilinear_ansatz` | 函數 |
| `sym_bilinear_from_corners` | 函數 |
| `sym_frac_one_minus` | 函數 |
| `sym_hermitian2` | 函數 |
| `sym_square_fill` | 函數 |

### 句法笛卡兒閉範疇

- 規範形式：帶註記閉箭頭，其 nf_eta
- 範疇化：自由 CCC：積與指數的萬有性
- 判定：def_eq_eta 驗證範疇律

| 符號 | 類別 |
|---|---|
| `check_syntactic_category` | 函數 |
| `tm_comp_at` | 函數 |
| `tm_comp_closed` | 函數 |
| `tm_id_at` | 函數 |
| `tm_shift` | 函數 |

### 有限宇宙型別與值

- 規範形式：葉序／葉值列
- 範疇化：有限集合範疇中由 Bool/Unit 以積生成
- 判定：樹遞迴

| 符號 | 類別 |
|---|---|
| `PVal` | 列舉 |
| `PVal::PVBool` | 構造子 |
| `PVal::PVPair` | 構造子 |
| `PVal::PVUnit` | 構造子 |
| `PVal::equal` | 函數 |
| `PVal::not_equal` | 函數 |
| `PVal::to_repr` | 函數 |
| `Ty` | 列舉 |
| `Ty::TyBool` | 構造子 |
| `Ty::TyProd` | 構造子 |
| `Ty::TyUnit` | 構造子 |
| `Ty::equal` | 函數 |
| `Ty::not_equal` | 函數 |
| `Ty::to_repr` | 函數 |
| `elems_of` | 函數 |
| `in_ty` | 函數 |
| `pval_fst` | 函數 |
| `pval_not` | 函數 |
| `pval_snd` | 函數 |
| `pval_swap` | 函數 |
| `pval_to_dvalue` | 函數 |

### Wiring 符號等價

- 規範形式：帶號置換（Unit 輸出 /(−1,false)）
- 範疇化：自由對稱冪冪範疇態射；⊗／換位／結合子／單位子
- 判定：置換性 O(#葉)；相等=結構相等

| 符號 | 類別 |
|---|---|
| `LeafKind` | 列舉 |
| `LeafKind::LKBool` | 構造子 |
| `LeafKind::LKUnit` | 構造子 |
| `LeafKind::equal` | 函數 |
| `LeafKind::not_equal` | 函數 |
| `LeafKind::to_repr` | 函數 |
| `LeafMap` | 結構 |
| `LeafMap.neg` | 欄位 |
| `LeafMap.src_index` | 欄位 |
| `LeafMap::equal` | 函數 |
| `LeafMap::not_equal` | 函數 |
| `LeafMap::to_repr` | 函數 |
| `Wiring` | 結構 |
| `Wiring.dst` | 欄位 |
| `Wiring.mapping` | 欄位 |
| `Wiring.src` | 欄位 |
| `check_wiring_category` | 函數 |
| `check_wiring_coherence` | 函數 |
| `flatten_pval` | 函數 |
| `leaf_count` | 函數 |
| `leaves_of_ty` | 函數 |
| `wiring_apply` | 函數 |
| `wiring_assoc` | 函數 |
| `wiring_comp` | 函數 |
| `wiring_eq` | 函數 |
| `wiring_id` | 函數 |
| `wiring_inv` | 函數 |
| `wiring_left_unitor` | 函數 |
| `wiring_not` | 函數 |
| `wiring_prod` | 函數 |
| `wiring_right_unitor` | 函數 |
| `wiring_swap` | 函數 |
| `wiring_wf` | 函數 |

### 同構、等價、ua、coe

- 規範形式：wiring；coe 按端點計算
- 範疇化：ua 在有限宇宙；積交換為自然性方塊
- 判定：wiring_eq 與 w;w⁻¹=id

| 符號 | 類別 |
|---|---|
| `Equiv` | 結構 |
| `Equiv.bwd` | 欄位 |
| `Equiv.dst` | 欄位 |
| `Equiv.fwd` | 欄位 |
| `Equiv.src` | 欄位 |
| `Equiv.wiring` | 欄位 |
| `Iso` | 結構 |
| `Iso.dst` | 欄位 |
| `Iso.from_fn` | 欄位 |
| `Iso.src` | 欄位 |
| `Iso.to_fn` | 欄位 |
| `Iso.wiring` | 欄位 |
| `UPath` | 結構 |
| `UPath.equiv` | 欄位 |
| `check_coe_definitional` | 函數 |
| `check_ua_coe` | 函數 |
| `coe_computes` | 函數 |
| `coe_upath` | 函數 |
| `equiv_bool_not` | 函數 |
| `equiv_bwd_value` | 函數 |
| `equiv_comp` | 函數 |
| `equiv_ext_eq` | 函數 |
| `equiv_ext_eq_oracle` | 函數（差分測試 oracle，非判定路徑） |
| `equiv_fun_value` | 函數 |
| `equiv_fwd_value` | 函數 |
| `equiv_id` | 函數 |
| `equiv_id_value` | 函數 |
| `equiv_inv` | 函數 |
| `equiv_inv_fun_value` | 函數 |
| `equiv_inv_value` | 函數 |
| `equiv_make_value` | 函數 |
| `equiv_of_wiring` | 函數 |
| `equiv_parts` | 函數 |
| `equiv_prod` | 函數 |
| `equiv_retr_type` | 函數 |
| `equiv_retr_value` | 函數 |
| `equiv_sect_type` | 函數 |
| `equiv_sect_value` | 函數 |
| `equiv_swap` | 函數 |
| `equiv_type_term` | 函數 |
| `equiv_wf` | 函數 |
| `equiv_wf_extensional` | 函數（差分測試 oracle，非判定路徑） |
| `iso_bool_not` | 函數 |
| `iso_of_wiring` | 函數 |
| `iso_swap` | 函數 |
| `iso_to_equiv` | 函數 |
| `iso_to_path` | 函數 |
| `iso_wf` | 函數 |
| `iso_wf_extensional` | 函數（差分測試 oracle，非判定路徑） |
| `swap_naturality` | 函數 |
| `ua` | 函數 |
| `ua_line_value` | 函數 |
| `ua_term` | 函數 |
| `ua_type_at` | 函數 |
| `ua_value` | 函數 |
| `upath_eq` | 函數 |
| `upath_left` | 函數 |
| `upath_right` | 函數 |

### PathP、離散路徑與 J

- 規範形式：規範 PathP 元（遠端為 coe 像）；離散路徑常值
- 範疇化：依賴路徑物件；J 來自常值線 coe 的恆等性
- 判定：端點與點值檢驗

| 符號 | 類別 |
|---|---|
| `DiscPath` | 結構 |
| `DiscPath.hi` | 欄位 |
| `DiscPath.lo` | 欄位 |
| `DiscPath.point` | 欄位 |
| `DiscPath.ty` | 欄位 |
| `Family` | 結構 |
| `Family.fiber` | 欄位 |
| `PathPVal` | 結構 |
| `PathPVal.at0` | 欄位 |
| `PathPVal.at1` | 欄位 |
| `PathPVal.line` | 欄位 |
| `PathPVal.point` | 欄位 |
| `check_j` | 函數 |
| `check_pathp_exchange` | 函數 |
| `disc_path_sym` | 函數 |
| `disc_path_wf` | 函數 |
| `disc_samples` | 函數 |
| `j_elim_disc` | 函數 |
| `j_roundtrip` | 函數 |
| `pathp_canonical` | 函數 |
| `pathp_fst` | 函數 |
| `pathp_prod` | 函數 |
| `pathp_prod_exchange_roundtrip` | 函數 |
| `pathp_snd` | 函數 |
| `pathp_wf` | 函數 |
| `refl_path` | 函數 |

### 有限 Glue

- 規範形式：(partial, base) 對；glue_from_base 由 base 範形
- 範疇化：沿等價黏合的極限式構造；unglue 為纖維化投影
- 判定：face_sat＋相容方程

| 符號 | 類別 |
|---|---|
| `GlueData` | 結構 |
| `GlueData.base_ty` | 欄位 |
| `GlueData.equiv` | 欄位 |
| `GlueData.face` | 欄位 |
| `GlueData.partial_ty` | 欄位 |
| `GlueElem` | 結構 |
| `GlueElem.base` | 欄位 |
| `GlueElem.partial` | 欄位 |
| `check_glue` | 函數 |
| `glue_equiv_base_of` | 函數 |
| `glue_equiv_collapse` | 函數 |
| `glue_equiv_domain_face` | 函數 |
| `glue_equiv_partial_values` | 函數 |
| `glue_equiv_store_partial` | 函數 |
| `glue_equiv_systems_conv` | 函數 |
| `glue_equiv_term` | 函數 |
| `glue_equiv_top_index` | 函數 |
| `glue_from_base` | 函數 |
| `glue_restrict` | 函數 |
| `glue_sound` | 函數 |
| `glue_wf` | 函數 |
| `make_glue` | 函數 |
| `unglue` | 函數 |

### Glue comp（有限線）

- 規範形式：輸出 (t₁, e₁(t₁))
- 範疇化：箭頭範疇 Ty²：等價線是其態射，comp 是沿線合成
- 判定：自然性方塊 wiring_eq；不相干則拒絕

| 符號 | 類別 |
|---|---|
| `GlueLineFinite` | 結構 |
| `GlueLineFinite.a_line` | 欄位 |
| `GlueLineFinite.e0` | 欄位 |
| `GlueLineFinite.e1` | 欄位 |
| `GlueLineFinite.face0` | 欄位 |
| `GlueLineFinite.face1` | 欄位 |
| `GlueLineFinite.t_line` | 欄位 |
| `check_glue_comp_all` | 函數 |
| `check_glue_comp_finite` | 函數 |
| `check_glue_comp_vec` | 函數 |
| `glue_comp_finite` | 函數 |
| `glue_comp_finite_correct` | 函數 |
| `glue_data_at0` | 函數 |
| `glue_data_at1` | 函數 |
| `glue_line_coherent` | 函數 |

### Glue comp（子空間線）

- 規範形式：校正方塊 k=1 邊
- 範疇化：變動 retract 線上的 Kan 提升；校正為 hcomp
- 判定：邊界／帽子／落點方程（網格）

| 符號 | 類別 |
|---|---|
| `GlueCompVecResult` | 結構 |
| `GlueCompVecResult.a_cap` | 欄位 |
| `GlueCompVecResult.a_cap_raw` | 欄位 |
| `GlueCompVecResult.a_fill_raw` | 欄位 |
| `GlueCompVecResult.correction` | 欄位 |
| `GlueCompVecResult.t_cap` | 欄位 |
| `GlueCompVecResult.t_fill` | 欄位 |
| `GlueLineVec` | 結構 |
| `GlueLineVec.base_line` | 欄位 |
| `GlueLineVec.equiv` | 欄位 |
| `GlueLineVec.face_active` | 欄位 |
| `GlueLineVec.part_line` | 欄位 |
| `LinEquivLine` | 結構 |
| `LinEquivLine.bwd` | 欄位 |
| `LinEquivLine.fwd` | 欄位 |
| `SubLine` | 結構 |
| `SubLine.proj` | 欄位 |
| `VecBox` | 結構 |
| `VecBox.bottom` | 欄位 |
| `VecBox.left` | 欄位 |
| `VecBox.right` | 欄位 |
| `cube_in_subline` | 函數 |
| `fill_subline` | 函數 |
| `glue_box_compatible` | 函數 |
| `glue_comp_vec` | 函數 |
| `glue_comp_vec_sound` | 函數 |
| `lin_equiv_from_unit_paths` | 函數 |
| `map_cube_equiv_line` | 函數 |
| `map_cube_matrix` | 函數 |
| `outer2` | 函數 |
| `prune_cube_subline` | 函數 |
| `subline_const` | 函數 |
| `subline_from_unit_path` | 函數 |
| `vec_box` | 函數 |
| `vec_normalize` | 函數 |

### BDD DAG、預算與 DPLL

- 規範形式：hash-consed DAG 節點 ID；root 的 reachable node count 為 ROBDD 大小
- 範疇化：布林函數在固定變量次序下的共享規範圖；apply 是格運算的 memoized 實現
- 判定：同 manager root-id 相等、root≠0 的 sat、節點預算 FaceDecision、或有步數預算的 DPLL；另有候選變量次序最小化與 3ⁿ 最壞節點界

| 符號 | 類別 |
|---|---|
| `BddApplyEntry` | 結構 |
| `BddApplyEntry.a` | 欄位 |
| `BddApplyEntry.b` | 欄位 |
| `BddApplyEntry.op` | 欄位 |
| `BddApplyEntry.result` | 欄位 |
| `BddBestBuild` | 結構 |
| `BddBestBuild.built` | 欄位 |
| `BddBestBuild.order` | 欄位 |
| `BddDagFace` | 結構 |
| `BddDagFace.manager` | 欄位 |
| `BddDagFace.ok` | 欄位 |
| `BddDagFace.root` | 欄位 |
| `BddDagNode` | 結構 |
| `BddDagNode.hi` | 欄位 |
| `BddDagNode.lo` | 欄位 |
| `BddDagNode.rank` | 欄位 |
| `BddManager` | 結構 |
| `BddManager.apply_buckets` | 欄位 |
| `BddManager.apply_hits` | 欄位 |
| `BddManager.apply_misses` | 欄位 |
| `BddManager.buckets` | 欄位 |
| `BddManager.exceeded` | 欄位 |
| `BddManager.max_nodes` | 欄位 |
| `BddManager.mk_calls` | 欄位 |
| `BddManager.n` | 欄位 |
| `BddManager.nodes` | 欄位 |
| `BddManager.order` | 欄位 |
| `BddManager.position` | 欄位 |
| `FaceDecision` | 列舉 |
| `FaceDecision::FaceBudgetExceeded` | 構造子 |
| `FaceDecision::FaceDecided` | 構造子 |
| `FaceDecision::equal` | 函數 |
| `FaceDecision::not_equal` | 函數 |
| `FaceDecision::to_repr` | 函數 |
| `FaceSatDecision` | 列舉 |
| `FaceSatDecision::FaceSat` | 構造子 |
| `FaceSatDecision::FaceSearchBudgetExceeded` | 構造子 |
| `FaceSatDecision::FaceUnsat` | 構造子 |
| `FaceSatDecision::equal` | 函數 |
| `FaceSatDecision::not_equal` | 函數 |
| `FaceSatDecision::to_repr` | 函數 |
| `bdd_dag_and` | 函數 |
| `bdd_dag_build_face` | 函數 |
| `bdd_dag_face_eq` | 函數 |
| `bdd_dag_face_le` | 函數 |
| `bdd_dag_false` | 函數 |
| `bdd_dag_not` | 函數 |
| `bdd_dag_of_face` | 函數 |
| `bdd_dag_of_face_best` | 函數 |
| `bdd_dag_or` | 函數 |
| `bdd_dag_reachable_count` | 函數 |
| `bdd_dag_sat_face` | 函數 |
| `bdd_dag_true` | 函數 |
| `bdd_dag_var` | 函數 |
| `bdd_dag_witness` | 函數 |
| `bdd_dag_xor` | 函數 |
| `bdd_manager_new` | 函數 |
| `bdd_manager_node_count` | 函數 |
| `bdd_manager_stats` | 函數 |
| `bdd_manager_with_order` | 函數 |
| `bdd_tree_of_dag` | 函數 |
| `bdd_var_order_candidates` | 函數 |
| `bdd_worst_case_nodes` | 函數 |
| `face_eq_dpll` | 函數 |
| `face_eq_within_budget` | 函數 |
| `face_sat_dpll` | 函數 |
| `face_sat_within_budget` | 函數 |

### 原始 DSystem 相容性與 first-match 範形

- 規範形式：相容系統沿用 DSystem 型別導向範形；任意 first-match 系統化為不交有效區域 DTubeNF
- 範疇化：面相對切片中的偏元素；checked 構造是進入 composition 系統子類的反射
- 判定：BDD cube 枚舉上的局部脈絡轉換，檢查 base 與兩兩重疊；不相容回報首個衝突

| 符號 | 類別 |
|---|---|
| `DSystemCompatibility` | 結構 |
| `DSystemCompatibility.branch` | 欄位 |
| `DSystemCompatibility.compatible` | 欄位 |
| `DSystemCompatibility.other_branch` | 欄位 |
| `DSystemCompatibility.reason` | 欄位 |
| `DSystemCompatibility::equal` | 函數 |
| `DSystemCompatibility::not_equal` | 函數 |
| `DSystemCompatibility::to_repr` | 函數 |
| `DSystemIncompatibility` | 列舉 |
| `DSystemIncompatibility::DSystemBaseIncompatible` | 構造子 |
| `DSystemIncompatibility::DSystemBranchesIncompatible` | 構造子 |
| `DSystemIncompatibility::DSystemOk` | 構造子 |
| `DSystemIncompatibility::equal` | 函數 |
| `DSystemIncompatibility::not_equal` | 函數 |
| `DSystemIncompatibility::to_repr` | 函數 |
| `DTubeNF` | 結構 |
| `DTubeNF.classes` | 欄位 |
| `DTubeNF.undefined` | 欄位 |
| `DTubeNFClass` | 結構 |
| `DTubeNFClass.path` | 欄位 |
| `DTubeNFClass.region` | 欄位 |
| `check_dsystem_compatibility` | 函數 |
| `check_dsystem_first_match_nf` | 函數 |
| `conv_at_under_face` | 函數 |
| `dtube_nf_class` | 函數 |
| `tube_paths_conv_under_face` | 函數 |

### AST 一等 Equiv 與 GlueEquiv

- 規範形式：DEquiv 攜帶 fwd/bwd/sect/retr 四項；DVGlueEquiv 攜帶完整 Equiv 分支與 base/partial 對
- 範疇化：AST 內的等價是帶同倫逆證明的同構；ua 是通往宇宙路徑的函子，GlueEquiv 是沿 partial 等價系統的黏合
- 判定：雙向檢查四個分量與兩條 PathP 證明；conversion/quote 按 Equiv 分量與分支面遞迴；沿 ua 的 coe 定義地為 fwd/bwd

| 符號 | 類別 |
|---|---|
| `DEquivBranch` | 結構 |
| `DEquivBranch.equiv` | 欄位 |
| `DEquivBranch.face` | 欄位 |
| `DEquivBranch.ty` | 欄位 |
| `DEquivBranch::equal` | 函數 |
| `DEquivBranch::not_equal` | 函數 |
| `DEquivBranch::to_repr` | 函數 |
| `DEquivBranchValue` | 結構 |
| `DEquivBranchValue.equiv` | 欄位 |
| `DEquivBranchValue.face` | 欄位 |
| `DEquivBranchValue.ty` | 欄位 |
| `DEquivParts` | 結構 |
| `DEquivParts.bwd` | 欄位 |
| `DEquivParts.dst` | 欄位 |
| `DEquivParts.fwd` | 欄位 |
| `DEquivParts.retr` | 欄位 |
| `DEquivParts.sect` | 欄位 |
| `DEquivParts.src` | 欄位 |
| `DEquivTypeParts` | 結構 |
| `DEquivTypeParts.dst` | 欄位 |
| `DEquivTypeParts.level` | 欄位 |
| `DEquivTypeParts.src` | 欄位 |
| `DGlueEquivParts` | 結構 |
| `DGlueEquivParts.base` | 欄位 |
| `DGlueEquivParts.branches` | 欄位 |
| `DGlueEquivParts.face` | 欄位 |
| `DGlueEquivParts.level` | 欄位 |
| `as_equiv_type` | 函數 |
| `as_glue_equiv` | 函數 |
| `bool_not_equiv_term` | 函數 |
| `bool_not_term` | 函數 |
| `check_equiv_ast` | 函數 |
| `comp_equiv_value` | 函數 |
| `comp_glue_equiv_value` | 函數 |
| `d_check_glue_equiv_partial` | 函數 |
| `d_equiv_branch` | 函數 |
| `dequiv_branch_value` | 函數 |
| `infer_equiv_projection` | 函數 |
| `infer_equiv_ty` | 函數 |
| `infer_glue_equiv` | 函數 |
| `infer_mk_equiv` | 函數 |
| `infer_ua` | 函數 |
| `mk_equiv_term` | 函數 |

### 受檢查語義型別線

- 規範形式：DCheckedTypeLine 保存已檢查的開放型別 body、脈絡、環境與宇宙層級，不保存裸宿主函數
- 範疇化：可代換的立方型別線由句法 body 在維度環境下求值，天然與維度代換交換
- 判定：構造時以新鮮維度檢查 body : Typeᵢ；at 以維度求值，coe/comp 直接派遣 AST Kan

| 符號 | 類別 |
|---|---|
| `DCheckedTypeLine` | 結構 |
| `DCheckedTypeLine.body` | 欄位 |
| `DCheckedTypeLine.constant` | 欄位 |
| `DCheckedTypeLine.ctx` | 欄位 |
| `DCheckedTypeLine.denv` | 欄位 |
| `DCheckedTypeLine.env` | 欄位 |
| `DCheckedTypeLine.level` | 欄位 |
| `DCheckedTypeLine.line` | 欄位 |
| `check_phase6_infrastructure` | 函數 |
| `checked_coe_value` | 函數 |
| `checked_comp_value` | 函數 |
| `checked_constant_type_line` | 函數 |
| `checked_constant_type_line_closed` | 函數 |
| `checked_fill_value` | 函數 |
| `checked_line_at` | 函數 |
| `checked_line_body` | 函數 |
| `checked_line_conv` | 函數 |
| `checked_line_endpoints` | 函數 |
| `checked_line_fn` | 函數 |
| `checked_line_is_constant` | 函數 |
| `checked_line_level` | 函數 |
| `checked_line_of_pathp_term` | 函數 |
| `checked_line_quote_body` | 函數 |
| `checked_line_reify_closed` | 函數 |
| `checked_pathp_type` | 函數 |
| `checked_type_line` | 函數 |
| `checked_type_line_closed` | 函數 |
| `checked_ua_line` | 函數 |

### Schema 註冊與 elaboration 快取

- 規範形式：DSchemaRegistry 中以穩定 Debug 鍵 intern 的 DInductivePlan/DHitPlan 與 telescope 前綴鏈
- 範疇化：schema 描述子是可共享計劃；快取只保存同一 elaboration 函數的有限圖，不改變指稱
- 判定：驗證布爾值與語義 telescope 前綴按 (term,args,args) 鍵查表；hit/miss 計數可觀察

| 符號 | 類別 |
|---|---|
| `DHitPlan` | 結構 |
| `DHitPlan.generic_index_types` | 欄位 |
| `DHitPlan.generic_param_types` | 欄位 |
| `DHitPlan.id` | 欄位 |
| `DHitPlan.key` | 欄位 |
| `DHitPlan.spec` | 欄位 |
| `DHitPlan.valid` | 欄位 |
| `DInductivePlan` | 結構 |
| `DInductivePlan.generic_index_types` | 欄位 |
| `DInductivePlan.generic_param_types` | 欄位 |
| `DInductivePlan.id` | 欄位 |
| `DInductivePlan.key` | 欄位 |
| `DInductivePlan.spec` | 欄位 |
| `DInductivePlan.valid` | 欄位 |
| `DSchemaRegistry` | 結構 |
| `DSchemaRegistry.hits` | 欄位 |
| `DSchemaRegistry.inductives` | 欄位 |
| `DSchemaRegistry.telescope_hits` | 欄位 |
| `DSchemaRegistry.telescope_misses` | 欄位 |
| `DSchemaRegistry.telescopes` | 欄位 |
| `DSchemaRegistry.validation_hits` | 欄位 |
| `DSchemaRegistry.validation_misses` | 欄位 |
| `DTelescopeCacheEntry` | 結構 |
| `DTelescopeCacheEntry.entries` | 欄位 |
| `DTelescopeCacheEntry.prefix_types` | 欄位 |
| `DTelescopeCacheEntry.prefix_values` | 欄位 |
| `DTelescopeCacheEntry.types` | 欄位 |
| `DTelescopeCacheEntry.values` | 欄位 |
| `default_schema_registry` | 常量 |

### Schema 函子、正性與歸納遞迴

- 規範形式：DPositiveFunctor 的 Id/Const/Product/Sum/List/Pi/Container 語法及其解碼型別；DPositivityReport 記錄出現與極性
- 範疇化：正性型別函子的初始代數與 decoded induction hypothesis；DDecode 是 Tarski 宇宙的歸納—遞迴解碼函數
- 判定：在別名展開後的 DTerm 上做極性遞迴：巢狀函子與正位置接受、負位置/未知中性族應用拒絕；IH 由函子遞迴生成

| 符號 | 類別 |
|---|---|
| `DPositiveFunctor` | 列舉 |
| `DPositiveFunctor::DFunctorConst` | 構造子 |
| `DPositiveFunctor::DFunctorContainer` | 構造子 |
| `DPositiveFunctor::DFunctorIdentity` | 構造子 |
| `DPositiveFunctor::DFunctorList` | 構造子 |
| `DPositiveFunctor::DFunctorPi` | 構造子 |
| `DPositiveFunctor::DFunctorProduct` | 構造子 |
| `DPositiveFunctor::DFunctorSum` | 構造子 |
| `DPositiveFunctor::equal` | 函數 |
| `DPositiveFunctor::not_equal` | 函數 |
| `DPositiveFunctor::to_repr` | 函數 |
| `DPositivityReport` | 結構 |
| `DPositivityReport.negative_polarity` | 欄位 |
| `DPositivityReport.occurs` | 欄位 |
| `DPositivityReport.positive_polarity` | 欄位 |
| `DPositivityReport.strictly_positive` | 欄位 |
| `DPositivityReport.unknown` | 欄位 |
| `DPositivityReport::equal` | 函數 |
| `DPositivityReport::not_equal` | 函數 |
| `DPositivityReport::to_repr` | 函數 |
| `check_container_functor_tree` | 函數 |
| `check_nested_rose_tree` | 函數 |
| `check_structural_positivity` | 函數 |
| `check_tarski_induction_recursion` | 函數 |
| `comp_schema_args_decoded` | 函數 |
| `container_tree_schema` | 函數 |
| `conv_decode_neutral` | 函數 |
| `conv_schema_args_full` | 函數 |
| `decode_term` | 函數 |
| `dfunctor_const` | 函數 |
| `dfunctor_container` | 函數 |
| `dfunctor_identity` | 函數 |
| `dfunctor_list` | 函數 |
| `dfunctor_pi` | 函數 |
| `dfunctor_product` | 函數 |
| `dfunctor_sum` | 函數 |
| `dpositivity_report` | 函數 |
| `dterm_children` | 函數 |
| `dterm_family_occurs` | 函數 |
| `dterm_family_positivity` | 函數 |
| `dterm_family_strictly_positive` | 函數 |
| `dterm_shift` | 函數 |
| `dterm_substitute` | 函數 |
| `infer_decode` | 函數 |
| `positive_functor_ih_type` | 函數 |
| `positive_functor_map` | 函數 |
| `positive_functor_type` | 函數 |

### Schema 擴展：互歸納、商與宇宙多態

- 規範形式：DMutualFamily 的 Sum-indexed 合併 schema；DLevelExpr 的層級 scheme；商即帶等式 1-cell 的 HIT
- 範疇化：互相歸納族是索引和上的單一初始代數；宇宙 scheme 是層級指派的函數；商構造為高階胞腔黏合
- 判定：互構子以分量索引約束編譯並以 Σ motive 消去；scheme 依層級向量求值並可再驗證；構造子等式以 Path 約束檢查

| 符號 | 類別 |
|---|---|
| `DConstructorConstraint` | 結構 |
| `DConstructorConstraint.lhs` | 欄位 |
| `DConstructorConstraint.rhs` | 欄位 |
| `DConstructorConstraint.ty` | 欄位 |
| `DConstructorConstraint::equal` | 函數 |
| `DConstructorConstraint::not_equal` | 函數 |
| `DConstructorConstraint::to_repr` | 函數 |
| `DHitLevelScheme` | 結構 |
| `DHitLevelScheme.build` | 欄位 |
| `DHitLevelScheme.level_arity` | 欄位 |
| `DHitLevelScheme.name` | 欄位 |
| `DHitLevelScheme.result_level` | 欄位 |
| `DInductiveLevelScheme` | 結構 |
| `DInductiveLevelScheme.build` | 欄位 |
| `DInductiveLevelScheme.level_arity` | 欄位 |
| `DInductiveLevelScheme.name` | 欄位 |
| `DInductiveLevelScheme.result_level` | 欄位 |
| `DLevelExpr` | 列舉 |
| `DLevelExpr::DLevelConst` | 構造子 |
| `DLevelExpr::DLevelMax` | 構造子 |
| `DLevelExpr::DLevelSucc` | 構造子 |
| `DLevelExpr::DLevelVar` | 構造子 |
| `DLevelExpr::equal` | 函數 |
| `DLevelExpr::not_equal` | 函數 |
| `DLevelExpr::to_repr` | 函數 |
| `DMutualFamily` | 結構 |
| `DMutualFamily.combined` | 欄位 |
| `DMutualFamily.components` | 欄位 |
| `DMutualFamily.ctor_offsets` | 欄位 |
| `DMutualFamily.name` | 欄位 |
| `check_schema_extensions` | 函數 |
| `circle_level_scheme` | 函數 |
| `compile_mutual_inductive` | 函數 |
| `cube3_schema` | 函數 |
| `dlevel_const` | 函數 |
| `dlevel_eval` | 函數 |
| `dlevel_max` | 函數 |
| `dlevel_succ` | 函數 |
| `dlevel_var` | 函數 |
| `equal_nat_pair_schema` | 函數 |
| `even_odd_components` | 函數 |
| `even_odd_family` | 函數 |
| `instantiate_hit_level_scheme` | 函數 |
| `instantiate_inductive_level_scheme` | 函數 |
| `list_level_scheme` | 函數 |
| `mutual_ctor_index` | 函數 |
| `mutual_elim_term` | 函數 |
| `mutual_intro_term` | 函數 |
| `mutual_intro_value` | 函數 |
| `mutual_motive_function` | 函數 |
| `mutual_nat_term` | 函數 |
| `mutual_nat_value` | 函數 |
| `mutual_type_term` | 函數 |
| `mutual_type_value` | 函數 |
| `quotient_eq_term` | 函數 |
| `quotient_point_term` | 函數 |
| `quotient_schema` | 函數 |
| `rose_tree_schema` | 函數 |
| `tarski_universe_schema` | 函數 |
| `tree_forest_components` | 函數 |
| `tree_forest_family` | 函數 |

### 精確單變量多項式與有理矩陣

- 規範形式：QPoly 的升冪稠密係數（尾零去除）；QMat 的有理列之列；RREF 與 pivot 列
- 範疇化：Q[x] 歐氏環與 Qⁿ 線性範疇；特徵/最小多項式是矩陣代數的表示不變量
- 判定：primitive pseudo-remainder gcd、Yun 重因數分解、有理根定理、Faddeev–LeVerrier、RREF；相等全為有理結構相等

| 符號 | 類別 |
|---|---|
| `QMat` | 結構 |
| `QMat.n` | 欄位 |
| `QMat.rows` | 欄位 |
| `QMat::equal` | 函數 |
| `QMat::not_equal` | 函數 |
| `QMat::to_repr` | 函數 |
| `QPoly` | 結構 |
| `QPoly.coeffs` | 欄位 |
| `QPoly::equal` | 函數 |
| `QPoly::not_equal` | 函數 |
| `QPoly::to_repr` | 函數 |
| `QPolyDiv` | 結構 |
| `QPolyDiv.quotient` | 欄位 |
| `QPolyDiv.remainder` | 欄位 |
| `QPolyExtGcd` | 結構 |
| `QPolyExtGcd.g` | 欄位 |
| `QPolyExtGcd.s` | 欄位 |
| `QPolyExtGcd.t` | 欄位 |
| `QPolyFactor` | 結構 |
| `QPolyFactor.factor` | 欄位 |
| `QPolyFactor.multiplicity` | 欄位 |
| `QPolyRationalFactorization` | 結構 |
| `QPolyRationalFactorization.multiplicities` | 欄位 |
| `QPolyRationalFactorization.residual` | 欄位 |
| `QPolyRationalFactorization.roots` | 欄位 |
| `QRref` | 結構 |
| `QRref.pivots` | 欄位 |
| `QRref.rank` | 欄位 |
| `QRref.rows` | 欄位 |
| `QVec` | 型別別名 |
| `qmat_add` | 函數 |
| `qmat_charpoly` | 函數 |
| `qmat_column_basis` | 函數 |
| `qmat_det` | 函數 |
| `qmat_eq` | 函數 |
| `qmat_from_columns` | 函數 |
| `qmat_from_int_rows` | 函數 |
| `qmat_from_rows` | 函數 |
| `qmat_identity` | 函數 |
| `qmat_inverse` | 函數 |
| `qmat_is_zero` | 函數 |
| `qmat_minimal_polynomial` | 函數 |
| `qmat_mul` | 函數 |
| `qmat_nullity` | 函數 |
| `qmat_nullspace` | 函數 |
| `qmat_poly_eval` | 函數 |
| `qmat_pow` | 函數 |
| `qmat_rank` | 函數 |
| `qmat_scalar` | 函數 |
| `qmat_scale` | 函數 |
| `qmat_sub` | 函數 |
| `qmat_trace` | 函數 |
| `qmat_transpose` | 函數 |
| `qmat_vec` | 函數 |
| `qmat_zero` | 函數 |
| `qpoly_add` | 函數 |
| `qpoly_coeff` | 函數 |
| `qpoly_const` | 函數 |
| `qpoly_degree` | 函數 |
| `qpoly_derivative` | 函數 |
| `qpoly_div_exact` | 函數 |
| `qpoly_divmod` | 函數 |
| `qpoly_eq` | 函數 |
| `qpoly_eval` | 函數 |
| `qpoly_extgcd` | 函數 |
| `qpoly_factor` | 函數 |
| `qpoly_factor_rational_roots` | 函數 |
| `qpoly_gcd` | 函數 |
| `qpoly_int` | 函數 |
| `qpoly_integer_coeffs` | 函數 |
| `qpoly_irreducible_upto3` | 函數 |
| `qpoly_is_one` | 函數 |
| `qpoly_is_squarefree` | 函數 |
| `qpoly_is_zero` | 函數 |
| `qpoly_leading` | 函數 |
| `qpoly_mod` | 函數 |
| `qpoly_monic` | 函數 |
| `qpoly_mul` | 函數 |
| `qpoly_neg` | 函數 |
| `qpoly_normalize` | 函數 |
| `qpoly_one` | 函數 |
| `qpoly_pow` | 函數 |
| `qpoly_primitive_part` | 函數 |
| `qpoly_pseudo_remainder` | 函數 |
| `qpoly_rational_roots` | 函數 |
| `qpoly_root_factor` | 函數 |
| `qpoly_root_multiplicity` | 函數 |
| `qpoly_scale` | 函數 |
| `qpoly_squarefree_factorization` | 函數 |
| `qpoly_squarefree_part` | 函數 |
| `qpoly_sub` | 函數 |
| `qpoly_x` | 函數 |
| `qpoly_zero` | 函數 |
| `qrows_nullspace` | 函數 |
| `qrows_rank` | 函數 |
| `qrows_rref` | 函數 |
| `qvec_add` | 函數 |
| `qvec_eq` | 函數 |
| `qvec_in_span` | 函數 |
| `qvec_independent_subset` | 函數 |
| `qvec_is_zero` | 函數 |
| `qvec_rank` | 函數 |
| `qvec_scale` | 函數 |
| `qvec_sub` | 函數 |
| `qvec_zero` | 函數 |

### 代數擴張與根式範形

- 規範形式：QuadNum 的 a+b√d（d 無平方因數）；AlgNum 的 Q[x]/(m) 餘式多項式
- 範疇化：二次擴張與一般有限代數擴張體；範數/跡由乘法矩陣行列式/跡給出
- 判定：模極小多項式的剩餘算術與擴張歐氏求逆；根式去巢以平方判別；相等為係數相等

| 符號 | 類別 |
|---|---|
| `AlgNum` | 結構 |
| `AlgNum.modulus` | 欄位 |
| `AlgNum.poly` | 欄位 |
| `AlgNum::equal` | 函數 |
| `AlgNum::not_equal` | 函數 |
| `AlgNum::to_repr` | 函數 |
| `QuadNum` | 結構 |
| `QuadNum.a` | 欄位 |
| `QuadNum.b` | 欄位 |
| `QuadNum.d` | 欄位 |
| `QuadNum::equal` | 函數 |
| `QuadNum::not_equal` | 函數 |
| `QuadNum::to_repr` | 函數 |
| `alg_add` | 函數 |
| `alg_coeffs` | 函數 |
| `alg_compatible` | 函數 |
| `alg_div` | 函數 |
| `alg_eq` | 函數 |
| `alg_eval_qpoly` | 函數 |
| `alg_ext_degree` | 函數 |
| `alg_generator` | 函數 |
| `alg_int` | 函數 |
| `alg_inv` | 函數 |
| `alg_is_zero` | 函數 |
| `alg_make` | 函數 |
| `alg_minimal_polynomial` | 函數 |
| `alg_modulus_irreducible_small` | 函數 |
| `alg_mul` | 函數 |
| `alg_multiplication_matrix` | 函數 |
| `alg_neg` | 函數 |
| `alg_norm` | 函數 |
| `alg_of_quad` | 函數 |
| `alg_one` | 函數 |
| `alg_pow` | 函數 |
| `alg_rat` | 函數 |
| `alg_rebase_to_minimal` | 函數 |
| `alg_scale_rat` | 函數 |
| `alg_sqrt_rat` | 函數 |
| `alg_sub` | 函數 |
| `alg_to_rat` | 函數 |
| `alg_trace` | 函數 |
| `alg_zero` | 函數 |
| `int_sqrt_exact` | 函數 |
| `int_squarefree_decomp` | 函數 |
| `quad_add` | 函數 |
| `quad_compatible` | 函數 |
| `quad_conj` | 函數 |
| `quad_denested_sqrt` | 函數 |
| `quad_div` | 函數 |
| `quad_eq` | 函數 |
| `quad_int` | 函數 |
| `quad_inv` | 函數 |
| `quad_is_rat` | 函數 |
| `quad_is_zero` | 函數 |
| `quad_make` | 函數 |
| `quad_mul` | 函數 |
| `quad_neg` | 函數 |
| `quad_norm` | 函數 |
| `quad_one` | 函數 |
| `quad_pow` | 函數 |
| `quad_rat` | 函數 |
| `quad_sqrt_int` | 函數 |
| `quad_sqrt_rat` | 函數 |
| `quad_sub` | 函數 |
| `quad_to_double` | 函數 |
| `quad_to_rat` | 函數 |
| `quad_trace` | 函數 |
| `quad_zero` | 函數 |

### 廣義特徵空間與 Jordan 理論

- 規範形式：(A−λI) 冪次零化列、遞增 nullity、Jordan 塊大小與鏈底基；PJP⁻¹=A
- 範疇化：主分解是互質多項式因子的單位分解；Jordan 型是相似等價的完全不變量片斷
- 判定：以特徵多項式重數、冪次核維度與鏈提升精確判定；不可在 Q 完全分裂者回報殘餘因子，AlgMat 在擴張上續行

| 符號 | 類別 |
|---|---|
| `AlgGeneralizedEigenspace` | 結構 |
| `AlgGeneralizedEigenspace.algebraic_multiplicity` | 欄位 |
| `AlgGeneralizedEigenspace.basis` | 欄位 |
| `AlgGeneralizedEigenspace.block_sizes` | 欄位 |
| `AlgGeneralizedEigenspace.eigenvalue` | 欄位 |
| `AlgGeneralizedEigenspace.geometric_multiplicity` | 欄位 |
| `AlgGeneralizedEigenspace.index` | 欄位 |
| `AlgGeneralizedEigenspace.nullities` | 欄位 |
| `AlgJordanDecomposition` | 結構 |
| `AlgJordanDecomposition.block_sizes` | 欄位 |
| `AlgJordanDecomposition.eigenvalues` | 欄位 |
| `AlgJordanDecomposition.j` | 欄位 |
| `AlgJordanDecomposition.p` | 欄位 |
| `AlgMat` | 結構 |
| `AlgMat.modulus` | 欄位 |
| `AlgMat.n` | 欄位 |
| `AlgMat.rows` | 欄位 |
| `AlgRref` | 結構 |
| `AlgRref.pivots` | 欄位 |
| `AlgRref.rank` | 欄位 |
| `AlgRref.rows` | 欄位 |
| `AlgVec` | 型別別名 |
| `QGeneralizedEigenspace` | 結構 |
| `QGeneralizedEigenspace.algebraic_multiplicity` | 欄位 |
| `QGeneralizedEigenspace.basis` | 欄位 |
| `QGeneralizedEigenspace.block_sizes` | 欄位 |
| `QGeneralizedEigenspace.eigenvalue` | 欄位 |
| `QGeneralizedEigenspace.geometric_multiplicity` | 欄位 |
| `QGeneralizedEigenspace.index` | 欄位 |
| `QGeneralizedEigenspace.nullities` | 欄位 |
| `QJordanDecomposition` | 結構 |
| `QJordanDecomposition.block_sizes` | 欄位 |
| `QJordanDecomposition.eigenvalues` | 欄位 |
| `QJordanDecomposition.j` | 欄位 |
| `QJordanDecomposition.p` | 欄位 |
| `QPrimaryProjector` | 結構 |
| `QPrimaryProjector.cofactor` | 欄位 |
| `QPrimaryProjector.complement` | 欄位 |
| `QPrimaryProjector.factor` | 欄位 |
| `QPrimaryProjector.polynomial` | 欄位 |
| `QPrimaryProjector.projector` | 欄位 |
| `QRationalSpectrum` | 結構 |
| `QRationalSpectrum.eigenvalues` | 欄位 |
| `QRationalSpectrum.multiplicities` | 欄位 |
| `QRationalSpectrum.residual` | 欄位 |
| `algmat_Jordan_chains` | 函數 |
| `algmat_Jordan_decomposition` | 函數 |
| `algmat_add` | 函數 |
| `algmat_charpoly` | 函數 |
| `algmat_eigenvalue_multiplicity` | 函數 |
| `algmat_eq` | 函數 |
| `algmat_from_columns` | 函數 |
| `algmat_from_qmat` | 函數 |
| `algmat_generalized_eigenspace` | 函數 |
| `algmat_identity` | 函數 |
| `algmat_mul` | 函數 |
| `algmat_nullity` | 函數 |
| `algmat_nullspace` | 函數 |
| `algmat_pow` | 函數 |
| `algmat_rank` | 函數 |
| `algmat_scalar` | 函數 |
| `algmat_sub` | 函數 |
| `algmat_trace` | 函數 |
| `algmat_vec` | 函數 |
| `algmat_zero` | 函數 |
| `algrows_nullspace` | 函數 |
| `algrows_rref` | 函數 |
| `algvec_in_span` | 函數 |
| `algvec_is_zero` | 函數 |
| `algvec_rank` | 函數 |
| `algvec_zero` | 函數 |
| `check_algebraic_extensions_and_Jordan` | 函數 |
| `qmat_Jordan_block_sizes` | 函數 |
| `qmat_Jordan_chains` | 函數 |
| `qmat_Jordan_decomposition` | 函數 |
| `qmat_Jordan_decomposition_auto` | 函數 |
| `qmat_diagonalizable_at` | 函數 |
| `qmat_eigen_nullities` | 函數 |
| `qmat_eigenvalue_multiplicity` | 函數 |
| `qmat_generalized_eigenspace` | 函數 |
| `qmat_generalized_projector` | 函數 |
| `qmat_is_diagonalizable_rational` | 函數 |
| `qmat_primary_projector` | 函數 |
| `qmat_primary_subspace_basis` | 函數 |
| `qmat_rational_spectrum` | 函數 |
| `qmat_vector_annihilator` | 函數 |

### 認證數值影子與精確立方體

- 規範形式：QuadC=QuadNum+i·QuadNum；CertMat 與次數≤2 的 CertPath/CertSquare 係數
- 範疇化：精確複二次矩陣代數與多項式立方體；Double 矩陣只是精確影子的近似表示
- 判定：P²=P、P†=P、正交分解與盒邊界以精確結構相等驗證；數值一致性只量測對影子的偏差與浮點 residual

| 符號 | 類別 |
|---|---|
| `CertMat` | 結構 |
| `CertMat.n` | 欄位 |
| `CertMat.rows` | 欄位 |
| `CertPath` | 結構 |
| `CertPath.coeffs` | 欄位 |
| `CertSquare` | 結構 |
| `CertSquare.coeffs` | 欄位 |
| `CertVec` | 型別別名 |
| `NumericProjectorCertificate` | 結構 |
| `NumericProjectorCertificate.exact` | 欄位 |
| `NumericProjectorCertificate.max_deviation` | 欄位 |
| `NumericProjectorCertificate.numeric_residual` | 欄位 |
| `NumericProjectorCertificate.ok` | 欄位 |
| `NumericProjectorCertificate.tolerance` | 欄位 |
| `ProjectorCertificate` | 結構 |
| `ProjectorCertificate.complement_projector` | 欄位 |
| `ProjectorCertificate.hermitian` | 欄位 |
| `ProjectorCertificate.idempotent` | 欄位 |
| `ProjectorCertificate.matrix` | 欄位 |
| `ProjectorCertificate.orthogonal_split` | 欄位 |
| `ProjectorCertificate.trace` | 欄位 |
| `QuadC` | 結構 |
| `QuadC.im` | 欄位 |
| `QuadC.re` | 欄位 |
| `QuadC::equal` | 函數 |
| `QuadC::not_equal` | 函數 |
| `QuadC::to_repr` | 函數 |
| `cert_complement` | 函數 |
| `cert_eigenspace_kan_sound` | 函數 |
| `cert_example_projector` | 函數 |
| `cert_example_unit` | 函數 |
| `cert_filler_respects_box` | 函數 |
| `cert_in_image` | 函數 |
| `cert_in_kernel` | 函數 |
| `cert_inner` | 函數 |
| `cert_is_hermitian` | 函數 |
| `cert_is_idempotent` | 函數 |
| `cert_is_projector` | 函數 |
| `cert_mat_add` | 函數 |
| `cert_mat_adjoint` | 函數 |
| `cert_mat_eq` | 函數 |
| `cert_mat_from_rows` | 函數 |
| `cert_mat_identity` | 函數 |
| `cert_mat_mul` | 函數 |
| `cert_mat_scale_quad` | 函數 |
| `cert_mat_sub` | 函數 |
| `cert_mat_to_numeric` | 函數 |
| `cert_mat_trace` | 函數 |
| `cert_mat_vec` | 函數 |
| `cert_mat_zero` | 函數 |
| `cert_open_box_wf` | 函數 |
| `cert_outer` | 函數 |
| `cert_path_const` | 函數 |
| `cert_path_end` | 函數 |
| `cert_path_eq` | 函數 |
| `cert_path_in_image` | 函數 |
| `cert_path_is_affine` | 函數 |
| `cert_path_line` | 函數 |
| `cert_path_start` | 函數 |
| `cert_path_sym` | 函數 |
| `cert_projector_of_vector` | 函數 |
| `cert_pruning_repairs_filler` | 函數 |
| `cert_square_add` | 函數 |
| `cert_square_apply` | 函數 |
| `cert_square_bilinear` | 函數 |
| `cert_square_bump` | 函數 |
| `cert_square_eq` | 函數 |
| `cert_square_face` | 函數 |
| `cert_square_fill` | 函數 |
| `cert_square_in_image` | 函數 |
| `cert_vec_add` | 函數 |
| `cert_vec_eq` | 函數 |
| `cert_vec_scale` | 函數 |
| `cert_vec_scale_quad` | 函數 |
| `cert_vec_sub` | 函數 |
| `cert_vec_to_numeric` | 函數 |
| `cert_vec_zero` | 函數 |
| `certify_numeric_projector` | 函數 |
| `certify_projector` | 函數 |
| `check_bdd_and_certified_numeric` | 函數 |
| `double_dyadic_interval` | 函數 |
| `numeric_mat_max_deviation` | 函數 |
| `numeric_projector_residual` | 函數 |
| `qcc_add` | 函數 |
| `qcc_conj` | 函數 |
| `qcc_eq` | 函數 |
| `qcc_i` | 函數 |
| `qcc_is_zero` | 函數 |
| `qcc_make` | 函數 |
| `qcc_mul` | 函數 |
| `qcc_neg` | 函數 |
| `qcc_one` | 函數 |
| `qcc_rat` | 函數 |
| `qcc_real` | 函數 |
| `qcc_scale_quad` | 函數 |
| `qcc_sub` | 函數 |
| `qcc_to_complex` | 函數 |
| `qcc_zero` | 函數 |

### 球面與懸掛 HIT

- 規範形式：Susp(X) 的 north/south 兩點與每點一條 meridian；S²=Susp(S¹)、S³=Susp(S²)
- 範疇化：懸掛是把 X×I 兩端各塌縮為一點的 HIT 商；迭代懸掛給出球面族
- 判定：generic HIT schema 驗證、meridian 端點 face 化簡、依賴消去與 hcomp

| 符號 | 類別 |
|---|---|
| `check_sphere3` | 函數 |
| `sphere2_north_term` | 函數 |
| `sphere2_north_value` | 函數 |
| `sphere2_schema` | 函數 |
| `sphere3_meridian_term` | 函數 |
| `sphere3_meridian_value` | 函數 |
| `sphere3_north_term` | 函數 |
| `sphere3_north_value` | 函數 |
| `sphere3_schema` | 函數 |
| `sphere3_south_term` | 函數 |
| `sphere3_south_value` | 函數 |
| `sphere3_type_term` | 函數 |
| `sphere3_type_value` | 函數 |
| `sphere_schema` | 函數 |
| `suspension_schema` | 函數 |

### Jacobi 區間譜迭代

- 規範形式：RatInterval/CInterval 矩形包絡與 dyadic 外向捨入後的 Hermitian 區間矩陣；每次旋轉保存 before/after 與累積酉變換
- 範疇化：Hermitian 相似變換在區間矩陣包絡上的單調提升；Gershgorin 圓盤給出譜的像分解與重數簇
- 判定：精確有理平方比較證明 sqrt/相位/c/s 包絡包含真值；逐旋轉重算 J†J−I∋0 與 J†AJ⊆after，最終圓盤分簇計數

| 符號 | 類別 |
|---|---|
| `CInterval` | 結構 |
| `CInterval.im` | 欄位 |
| `CInterval.re` | 欄位 |
| `CInterval::equal` | 函數 |
| `CInterval::not_equal` | 函數 |
| `CInterval::to_repr` | 函數 |
| `EigenInterval` | 結構 |
| `EigenInterval.count` | 欄位 |
| `EigenInterval.hi` | 欄位 |
| `EigenInterval.lo` | 欄位 |
| `EigenInterval::equal` | 函數 |
| `EigenInterval::not_equal` | 函數 |
| `EigenInterval::to_repr` | 函數 |
| `JacobiCertificate` | 結構 |
| `JacobiCertificate.eigenvalues` | 欄位 |
| `JacobiCertificate.final_matrix` | 欄位 |
| `JacobiCertificate.initial` | 欄位 |
| `JacobiCertificate.precision_bits` | 欄位 |
| `JacobiCertificate.rotations` | 欄位 |
| `JacobiCertificate.transform` | 欄位 |
| `JacobiCertificate::equal` | 函數 |
| `JacobiCertificate::not_equal` | 函數 |
| `JacobiCertificate::to_repr` | 函數 |
| `JacobiCoefficients` | 結構 |
| `JacobiCoefficients.cosine` | 欄位 |
| `JacobiCoefficients.modulus` | 欄位 |
| `JacobiCoefficients.p` | 欄位 |
| `JacobiCoefficients.phase` | 欄位 |
| `JacobiCoefficients.q` | 欄位 |
| `JacobiCoefficients.sine` | 欄位 |
| `JacobiCoefficients::equal` | 函數 |
| `JacobiCoefficients::not_equal` | 函數 |
| `JacobiCoefficients::to_repr` | 函數 |
| `JacobiRotationCertificate` | 結構 |
| `JacobiRotationCertificate.after` | 欄位 |
| `JacobiRotationCertificate.after_off_sq_upper` | 欄位 |
| `JacobiRotationCertificate.before` | 欄位 |
| `JacobiRotationCertificate.before_off_sq_upper` | 欄位 |
| `JacobiRotationCertificate.coeffs` | 欄位 |
| `JacobiRotationCertificate.transform_after` | 欄位 |
| `JacobiRotationCertificate.transform_before` | 欄位 |
| `JacobiRotationCertificate.unitary_residual_contains_zero` | 欄位 |
| `JacobiRotationCertificate::equal` | 函數 |
| `JacobiRotationCertificate::not_equal` | 函數 |
| `JacobiRotationCertificate::to_repr` | 函數 |
| `QCIntervalMat` | 結構 |
| `QCIntervalMat.n` | 欄位 |
| `QCIntervalMat.rows` | 欄位 |
| `QCIntervalMat::equal` | 函數 |
| `QCIntervalMat::not_equal` | 函數 |
| `QCIntervalMat::to_repr` | 函數 |
| `QCpx` | 結構 |
| `QCpx.im` | 欄位 |
| `QCpx.re` | 欄位 |
| `QCpx::equal` | 函數 |
| `QCpx::not_equal` | 函數 |
| `QCpx::to_repr` | 函數 |
| `QCpxMat` | 結構 |
| `QCpxMat.n` | 欄位 |
| `QCpxMat.rows` | 欄位 |
| `QCpxMat::equal` | 函數 |
| `QCpxMat::not_equal` | 函數 |
| `QCpxMat::to_repr` | 函數 |
| `RatInterval` | 結構 |
| `RatInterval.hi` | 欄位 |
| `RatInterval.lo` | 欄位 |
| `RatInterval::equal` | 函數 |
| `RatInterval::not_equal` | 函數 |
| `RatInterval::to_repr` | 函數 |
| `cinterval` | 函數 |
| `cinterval_add` | 函數 |
| `cinterval_conj` | 函數 |
| `cinterval_contains` | 函數 |
| `cinterval_hull` | 函數 |
| `cinterval_midpoint` | 函數 |
| `cinterval_mul` | 函數 |
| `cinterval_neg` | 函數 |
| `cinterval_normalize` | 函數 |
| `cinterval_one` | 函數 |
| `cinterval_point` | 函數 |
| `cinterval_sub` | 函數 |
| `cinterval_subset` | 函數 |
| `cinterval_zero` | 函數 |
| `eigen_interval_contains` | 函數 |
| `jacobi_certificate_sound` | 函數 |
| `jacobi_coefficients` | 函數 |
| `jacobi_interval_eigen` | 函數 |
| `jacobi_similarity_interval` | 函數 |
| `jacobi_unitary_interval` | 函數 |
| `jacobi_unitary_residual_contains_zero` | 函數 |
| `qci_mat_add` | 函數 |
| `qci_mat_adjoint` | 函數 |
| `qci_mat_contains` | 函數 |
| `qci_mat_contains_point` | 函數 |
| `qci_mat_from_point` | 函數 |
| `qci_mat_from_rows` | 函數 |
| `qci_mat_hermitian_hull` | 函數 |
| `qci_mat_identity` | 函數 |
| `qci_mat_is_hermitian` | 函數 |
| `qci_mat_midpoint` | 函數 |
| `qci_mat_mul` | 函數 |
| `qci_mat_normalize` | 函數 |
| `qci_mat_sub` | 函數 |
| `qci_mat_zero` | 函數 |
| `qci_off_frobenius_sq_upper` | 函數 |
| `qcpx` | 函數 |
| `qcpx_is_zero` | 函數 |
| `qcpx_mat_from_qmat` | 函數 |
| `qcpx_mat_from_rows` | 函數 |
| `qcpx_mat_is_hermitian` | 函數 |
| `qcpx_real` | 函數 |
| `rat_abs_exact` | 函數 |
| `rat_cmp_exact` | 函數 |
| `rat_interval` | 函數 |
| `rat_interval_abs` | 函數 |
| `rat_interval_add` | 函數 |
| `rat_interval_contains` | 函數 |
| `rat_interval_div` | 函數 |
| `rat_interval_hull` | 函數 |
| `rat_interval_midpoint` | 函數 |
| `rat_interval_mul` | 函數 |
| `rat_interval_neg` | 函數 |
| `rat_interval_normalize` | 函數 |
| `rat_interval_point` | 函數 |
| `rat_interval_recip` | 函數 |
| `rat_interval_sqrt` | 函數 |
| `rat_interval_sub` | 函數 |
| `rat_interval_subset` | 函數 |
| `rat_interval_width` | 函數 |
| `rat_le_exact` | 函數 |
| `rat_round_down_pow2` | 函數 |
| `rat_round_up_pow2` | 函數 |
| `rat_sqrt_interval` | 函數 |

### 高階合一與雙向 elaborator

- 規範形式：UTerm 的 Miller pattern spine `?F x₁…xₙ` 與 zonk 後 beta/投影簡化核心；表面 STerm 按名解析為 de Bruijn UTerm
- 範疇化：pattern HOU 是高階合一的可判定片斷；雙向 elaboration 把隱含引數與 dependent motive 問題送入同一合一器再編譯至依賴覈心
- 判定：WHNF 後 rigid 分解、pattern 抽象、occurs/scope 檢查與閉項 fallback；check/infer 插入隱含 metavariables，未解者拒絕轉 DTerm

| 符號 | 類別 |
|---|---|
| `ElabResult` | 結構 |
| `ElabResult.term` | 欄位 |
| `ElabResult.ty` | 欄位 |
| `ElabResult::equal` | 函數 |
| `ElabResult::not_equal` | 函數 |
| `ElabResult::to_repr` | 函數 |
| `ElabVar` | 結構 |
| `ElabVar.name` | 欄位 |
| `ElabVar.ty` | 欄位 |
| `ElabVar::equal` | 函數 |
| `ElabVar::not_equal` | 函數 |
| `ElabVar::to_repr` | 函數 |
| `Elaborator` | 結構 |
| `Elaborator.unifier` | 欄位 |
| `Elaborator.vars` | 欄位 |
| `Elaborator::equal` | 函數 |
| `Elaborator::not_equal` | 函數 |
| `Elaborator::to_repr` | 函數 |
| `STerm` | 列舉 |
| `STerm::SAnn` | 構造子 |
| `STerm::SApp` | 構造子 |
| `STerm::SBoolLit` | 構造子 |
| `STerm::SFst` | 構造子 |
| `STerm::SHole` | 構造子 |
| `STerm::SLam` | 構造子 |
| `STerm::SNatElim` | 構造子 |
| `STerm::SNatZero` | 構造子 |
| `STerm::SPair` | 構造子 |
| `STerm::SSnd` | 構造子 |
| `STerm::SSucc` | 構造子 |
| `STerm::SUnitLit` | 構造子 |
| `STerm::SVar` | 構造子 |
| `STerm::equal` | 函數 |
| `STerm::not_equal` | 函數 |
| `STerm::to_repr` | 函數 |
| `UMetaInfo` | 結構 |
| `UMetaInfo.context_depth` | 欄位 |
| `UMetaInfo.solution` | 欄位 |
| `UMetaInfo::equal` | 函數 |
| `UMetaInfo::not_equal` | 函數 |
| `UMetaInfo::to_repr` | 函數 |
| `UTerm` | 列舉 |
| `UTerm::UApp` | 構造子 |
| `UTerm::UBoolLit` | 構造子 |
| `UTerm::UConst` | 構造子 |
| `UTerm::UFst` | 構造子 |
| `UTerm::UImplicitPi` | 構造子 |
| `UTerm::ULam` | 構造子 |
| `UTerm::UMeta` | 構造子 |
| `UTerm::UNatElim` | 構造子 |
| `UTerm::UNatZero` | 構造子 |
| `UTerm::UPair` | 構造子 |
| `UTerm::UPi` | 構造子 |
| `UTerm::USigma` | 構造子 |
| `UTerm::USnd` | 構造子 |
| `UTerm::USucc` | 構造子 |
| `UTerm::UType` | 構造子 |
| `UTerm::UVar` | 構造子 |
| `UTerm::equal` | 函數 |
| `UTerm::not_equal` | 函數 |
| `UTerm::to_repr` | 函數 |
| `Unifier` | 結構 |
| `Unifier.metas` | 欄位 |
| `Unifier.solved_count` | 欄位 |
| `Unifier::equal` | 函數 |
| `Unifier::not_equal` | 函數 |
| `Unifier::to_repr` | 函數 |
| `check_hou_elaborator` | 函數 |
| `elab_check` | 函數 |
| `elab_infer` | 函數 |
| `elab_result_to_dterm` | 函數 |
| `elab_type_to_dterm` | 函數 |
| `elaborator_new` | 函數 |
| `hou_fresh_meta` | 函數 |
| `hou_semantic_optimize` | 函數 |
| `hou_unify` | 函數 |
| `unifier_new` | 函數 |
| `uterm_contains_unsolved_meta` | 函數 |
| `uterm_whnf` | 函數 |
| `uty_arrow` | 函數 |
| `uty_bool` | 函數 |
| `uty_implicit_arrow` | 函數 |
| `uty_nat` | 函數 |
| `uty_unit` | 函數 |

### 參數化模組與名字空間

- 規範形式：模組 telescope（參數→imports→本地宣告）與分離的 name→ordinal bindings；實例是同時代換後的閉合宣告
- 範疇化：參數化模組是模組函子，import 是函子套用的內聯，open/alias/rename 是同一 telescope entry 的不同名字投影
- 判定：循環檢測、參數引數依賴檢查、import 選擇/隱藏/改名的歧義拒絕、opaque export 中性化，以及實例閉合後逐宣告 dep_check

| 符號 | 類別 |
|---|---|
| `ModuleBinding` | 結構 |
| `ModuleBinding.name` | 欄位 |
| `ModuleBinding.ordinal` | 欄位 |
| `ModuleBinding::equal` | 函數 |
| `ModuleBinding::not_equal` | 函數 |
| `ModuleBinding::to_repr` | 函數 |
| `ModuleDecl` | 結構 |
| `ModuleDecl.body` | 欄位 |
| `ModuleDecl.exported` | 欄位 |
| `ModuleDecl.name` | 欄位 |
| `ModuleDecl.transparent` | 欄位 |
| `ModuleDecl.ty` | 欄位 |
| `ModuleDecl::equal` | 函數 |
| `ModuleDecl::not_equal` | 函數 |
| `ModuleDecl::to_repr` | 函數 |
| `ModuleDef` | 結構 |
| `ModuleDef.decls` | 欄位 |
| `ModuleDef.imports` | 欄位 |
| `ModuleDef.opens` | 欄位 |
| `ModuleDef.params` | 欄位 |
| `ModuleDef.path` | 欄位 |
| `ModuleDef::equal` | 函數 |
| `ModuleDef::not_equal` | 函數 |
| `ModuleDef::to_repr` | 函數 |
| `ModuleEntry` | 結構 |
| `ModuleEntry.body` | 欄位 |
| `ModuleEntry.canonical_name` | 欄位 |
| `ModuleEntry.exported` | 欄位 |
| `ModuleEntry.local_name` | 欄位 |
| `ModuleEntry.source_module` | 欄位 |
| `ModuleEntry.transparent` | 欄位 |
| `ModuleEntry.ty` | 欄位 |
| `ModuleEntry::equal` | 函數 |
| `ModuleEntry::not_equal` | 函數 |
| `ModuleEntry::to_repr` | 函數 |
| `ModuleEnv` | 結構 |
| `ModuleEnv.modules` | 欄位 |
| `ModuleEnv::equal` | 函數 |
| `ModuleEnv::not_equal` | 函數 |
| `ModuleEnv::to_repr` | 函數 |
| `ModuleExport` | 結構 |
| `ModuleExport.name` | 欄位 |
| `ModuleExport.ordinal` | 欄位 |
| `ModuleExport.transparent` | 欄位 |
| `ModuleExport::equal` | 函數 |
| `ModuleExport::not_equal` | 函數 |
| `ModuleExport::to_repr` | 函數 |
| `ModuleImport` | 結構 |
| `ModuleImport.alias_name` | 欄位 |
| `ModuleImport.args` | 欄位 |
| `ModuleImport.hiding` | 欄位 |
| `ModuleImport.module_path` | 欄位 |
| `ModuleImport.only` | 欄位 |
| `ModuleImport.opened` | 欄位 |
| `ModuleImport.renames` | 欄位 |
| `ModuleImport::equal` | 函數 |
| `ModuleImport::not_equal` | 函數 |
| `ModuleImport::to_repr` | 函數 |
| `ModuleInstance` | 結構 |
| `ModuleInstance.bindings` | 欄位 |
| `ModuleInstance.decls` | 欄位 |
| `ModuleInstance.module_path` | 欄位 |
| `ModuleInstance::equal` | 函數 |
| `ModuleInstance::not_equal` | 函數 |
| `ModuleInstance::to_repr` | 函數 |
| `ModuleInstanceDecl` | 結構 |
| `ModuleInstanceDecl.body` | 欄位 |
| `ModuleInstanceDecl.canonical_name` | 欄位 |
| `ModuleInstanceDecl.exported` | 欄位 |
| `ModuleInstanceDecl.name` | 欄位 |
| `ModuleInstanceDecl.transparent` | 欄位 |
| `ModuleInstanceDecl.ty` | 欄位 |
| `ModuleInstanceDecl::equal` | 函數 |
| `ModuleInstanceDecl::not_equal` | 函數 |
| `ModuleInstanceDecl::to_repr` | 函數 |
| `ModuleRename` | 結構 |
| `ModuleRename.from_name` | 欄位 |
| `ModuleRename.to_name` | 欄位 |
| `ModuleRename::equal` | 函數 |
| `ModuleRename::not_equal` | 函數 |
| `ModuleRename::to_repr` | 函數 |
| `ModuleSignature` | 結構 |
| `ModuleSignature.bindings` | 欄位 |
| `ModuleSignature.entries` | 欄位 |
| `ModuleSignature.exports` | 欄位 |
| `ModuleSignature.module_path` | 欄位 |
| `ModuleSignature::equal` | 函數 |
| `ModuleSignature::not_equal` | 函數 |
| `ModuleSignature::to_repr` | 函數 |
| `bool_ops_module` | 函數 |
| `check_module_system` | 函數 |
| `generic_iterate_module` | 函數 |
| `module_decl` | 函數 |
| `module_def` | 函數 |
| `module_env_add` | 函數 |
| `module_env_find` | 函數 |
| `module_env_new` | 函數 |
| `module_example_env` | 函數 |
| `module_import` | 函數 |
| `module_instance_find` | 函數 |
| `module_instantiate` | 函數 |
| `module_ref` | 函數 |
| `module_rename` | 函數 |
| `module_resolve` | 函數 |
| `module_signature` | 函數 |
| `module_validate` | 函數 |

### 範疇化總檢

- 規範形式：範疇律的布爾合取
- 範疇化：彙總各範疇的身分／合成／相干律
- 判定：逐律求值

| 符號 | 類別 |
|---|---|
| `check_categories_all` | 函數 |

### 定理登記與範例

- 規範形式：(名稱, Bool) 登記列；具體見證向量／項
- 範疇化：可判定命題在見證上的實現
- 判定：moon test／登記表

| 符號 | 類別 |
|---|---|
| `CheckResult` | 結構 |
| `CheckResult.name` | 欄位 |
| `CheckResult.ok` | 欄位 |
| `all_checks_pass` | 函數 |
| `check_Jacobi_interval` | 函數 |
| `check_constructor_constraints` | 函數 |
| `check_mutual_inductives` | 函數 |
| `check_quotient_schema` | 函數 |
| `check_universe_schemes` | 函數 |
| `example_projector` | 函數 |
| `example_unit` | 函數 |
| `grid` | 函數 |
| `inv_sqrt2` | 函數 |
| `print_report` | 函數 |
| `run_all_checks` | 函數 |
| `sample_terms` | 函數 |
| `sample_vectors` | 函數 |
| `vec_e3` | 函數 |

### 規格登記

- 規範形式：SpecEntry 六元組
- 範疇化：規格之規格；完備性對產生介面核對
- 判定：spec_registry_sound＋本審計

| 符號 | 類別 |
|---|---|
| `SpecEntry` | 結構 |
| `SpecEntry.canonical` | 欄位 |
| `SpecEntry.categorical` | 欄位 |
| `SpecEntry.decision` | 欄位 |
| `SpecEntry.kind` | 欄位 |
| `SpecEntry.name` | 欄位 |
| `SpecEntry.symbols` | 欄位 |
| `SpecKind` | 列舉 |
| `SpecKind::SpecOperator` | 構造子 |
| `SpecKind::SpecStructure` | 構造子 |
| `SpecKind::SpecTheorem` | 構造子 |
| `SpecKind::SpecType` | 構造子 |
| `SpecKind::equal` | 函數 |
| `SpecKind::not_equal` | 函數 |
| `SpecKind::to_repr` | 函數 |
| `spec_count` | 函數 |
| `spec_covers` | 函數 |
| `spec_registry` | 函數 |
| `spec_registry_sound` | 函數 |

### 輔助工具

- 規範形式：整數／網格等具體值
- 範疇化：基礎集合層工具
- 判定：直接計算

| 符號 | 類別 |
|---|---|
| `int_pow` | 函數 |
<!-- APPENDIX:END -->
