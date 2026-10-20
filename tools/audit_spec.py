#!/usr/bin/env python3
"""Generate / audit the per-symbol specification appendix in SPEC.md.

Parses pkg.generated.mbti (run `moon info` first) for every public
declaration, enum constructor and struct field, classifies each symbol
into a specification family (canonical form / categorification / decision
procedure), and (re)writes the appendix of SPEC.md between the
APPENDIX markers.  --check verifies the appendix is exactly the set of
interface symbols, each listed once, each classified.
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MBTI = ROOT / "pkg.generated.mbti"
SPEC = ROOT / "SPEC.md"

FAMILIES = {
    "複數標量": ("(re, im) 有序對", "交換環 C；共軛為對合", "eps 分量比較"),
    "複向量與內積": ("分量列", "Hilbert 空間 Hilb 的物件；內積誘導對偶", "分量運算"),
    "矩陣與伴隨": ("列之列", "Hilb 態射；† 為 dagger 函子", "矩陣運算"),
    "投影與特徵空間": ("Σ vₖvₖ†；分解為正交對 (Pv,(I−P)v)", "自伴冪等態射及其在 Hilb 中的分裂（雙積）", "特徵值方程／正交性／跡整數性"),
    "Karoubi 包絡": ("物件 P；態射被夾緊矩陣 QAP=A", "冪完備化；恒等是 P 本身；dagger", "QAP=A 與合成律"),
    "區間": ("De Morgan 表達式；端點布林化", "De Morgan 代數（區間物件）", "求值與重寫簡化"),
    "面公式與 BDD": ("由 interned DAG 展開的 ROBDD 樹（相容表示）；主判定在同一 manager 以 root 代表", "面格（自由有界分配格的商）的規範代表", "DAG apply/root 相等判定；樹形 API 為逐公式展開"),
    "面偏序範疇": ("BDD 等價類", "偏序範疇：∧積、∨餘積、⊤/⊥ 終始", "bdd_face_le 與萬有性等式"),
    "系統與剪枝": ("分支列；語義範形見系統符號範形", "面上 presheaf 的偏元素；聯集拼接", "重疊面的 BDD 可滿足性"),
    "系統符號範形": ("值標記不交 BDD 分割＋未定義區域", "偏元素在面格切片中的像分解", "BDD 區域運算"),
    "立方體與 Kan 填充": ("函數 Iⁿ→Cᵐ；填充用仿射公式；帽子為 comp 結果", "□ 上 cubical set 的實現；retract 的 Kan 結構", "邊界方程（網格）"),
    "未型別 NbE": ("βπ 正規形 nf", "句法範疇在 βπ 商下的態射代表", "eval/quote 後結構比較"),
    "HOAS": ("經 reify 的 de Bruijn 範形", "函子範疇式綁定；與一階語法範疇等價（模定義相等）", "reflect/reify 往返"),
    "型別化 NbE 與 η": ("η 長 βπ 範形 nf_eta", "自由笛卡兒閉範疇的態射代表", "雙向檢查＋按型別 quote"),
    "依賴型別 NbE（Π/Σ/宇宙）": ("按型別 quote 的 η 長依賴正規形；Π/Σ 第二分量為語義閉包族；累積 Typeᵢ 層級", "帶族範疇 (CwF) 模型：脈絡延伸與依賴代入是閉包施用", "雙向 elaboration＋型別導向轉換；相等=範形相等"),
    "立方 AST 與維度 NbE": ("DTerm 的項/維度雙 de Bruijn 索引；線與 tube body；帶 dlevel 的 quote", "帶區間脈絡的 cubical CwF；PathP 為依賴路徑物件，Glue 值為 (raw/DPartial partial,base) 對", "雙向檢查＋Dim/Face 簡化及 ROBDD 語義謂詞"),
    "AST Kan comp/hcomp": ("分支一律攜帶為 DSystem；在一般維度按型別頭派遣；頂分支取帽、形式合成為 DNComp/DNHComp", "各型別構造子保存 Kan 纖維化結構；hcompU 是 Glue 黏合", "系統 base/重疊相容＋型別遞迴；coe/fill 為 comp 線段限制"),
    "資料型別與 HIT 消去": ("Nat/List 構造子遞迴；Circle loop@r；Torus square@(i,j) 模對邊等同", "初始代數與 HIT 的依賴消去是 motive 截面，並與形式 composition 交換", "構造子模式遞迴、Dim 語義相等、motive 中的 comp"),
    "持久環境、惰性與語義快取": ("帶長度持久連結串列 DEnv/DDimEnv（de Bruijn 頭在最內）；DVThunk 最多強制一次；快取鍵為簡化維度/引文項 Debug 鍵", "CwF 脈絡延伸是共享尾部的 cons；惰性值是 call-by-need 語義值，memoized 族/維度線是外延函數的有限圖延伸", "環境索引、force_count 與快取鍵相等"),
    "依賴語義系統與 partial 值": ("DSystem 分支去 ⊥、按值合併同 body 並以引文排序；DPartialValue 的 BDD 有效區域分割 DSystemNF", "面格切片中的偏元素；多分支 Glue 為 partial type 系統與 base 的極限式配對", "BDD 區域運算＋分支 body 的型別導向轉換/引文鍵"),
    "通用歸納族 schema": ("telescope＋完整 DTerm 引數型別（外部、直接/巢狀/函數遞迴與約束）；值為 DVIntro，中性消去按生成 case 型別引文", "結構化嚴格正性函子的依賴初始代數；消去子是 motive 截面，comp 沿先前引數 filler 遞迴", "schema 結構相等、telescope elaboration、極性正性判定與生成檢查"),
    "通用 HIT schema": ("任意有限維 cell；任一端點按 face expression 逐維化簡；case 為逐維巢狀 PathP", "帶 face 映射的胞腔型高階初始代數；消去子保存各維 cells", "face 引數/索引檢查、多維角落雙路化簡轉換與維度語義相等"),
    "依賴 Kan 線（coe/comp）": ("DLine{at, coe, fill}，comp=fill(1)；coe 在 Π 定義域反向、在 Σ 沿第一分量路徑", "型別即 Kan 纖維化結構；依賴族為 (路徑)→DLine；與子空間/Glue 線共同覆蓋全型別族", "按型別構造子遞迴；coe(r,r) 定義恆等"),
    "精確符號代數": ("Q 上多變量多項式規範形（合併去零排序）；分式；複符號量 (re,im)", "多項式戒與分式體承載矩陣代數；共軛為對合", "多項式恆等／分式交叉相乘（精確）"),
    "譜投影與仿射唯一填充": ("Pₖ=qₖ(A)/qₖ(λₖ)；雙線性角插值 k00+i k10+j k01+ij k11", "單位分解與譜分解；雙線性是兩仿射方向的張量黏合", "首一整除（模最小多項式）與在原子 i,j 的恆等"),
    "句法笛卡兒閉範疇": ("帶註記閉箭頭，其 nf_eta", "自由 CCC：積與指數的萬有性", "def_eq_eta 驗證範疇律"),
    "有限宇宙型別與值": ("葉序／葉值列", "有限集合範疇中由 Bool/Unit 以積生成", "樹遞迴"),
    "Wiring 符號等價": ("帶號置換（Unit 輸出 /(−1,false)）", "自由對稱冪冪範疇態射；⊗／換位／結合子／單位子", "置換性 O(#葉)；相等=結構相等"),
    "同構、等價、ua、coe": ("wiring；coe 按端點計算", "ua 在有限宇宙；積交換為自然性方塊", "wiring_eq 與 w;w⁻¹=id"),
    "PathP、離散路徑與 J": ("規範 PathP 元（遠端為 coe 像）；離散路徑常值", "依賴路徑物件；J 來自常值線 coe 的恆等性", "端點與點值檢驗"),
    "有限 Glue": ("(partial, base) 對；glue_from_base 由 base 範形", "沿等價黏合的極限式構造；unglue 為纖維化投影", "face_sat＋相容方程"),
    "Glue comp（有限線）": ("輸出 (t₁, e₁(t₁))", "箭頭範疇 Ty²：等價線是其態射，comp 是沿線合成", "自然性方塊 wiring_eq；不相干則拒絕"),
    "Glue comp（子空間線）": ("校正方塊 k=1 邊", "變動 retract 線上的 Kan 提升；校正為 hcomp", "邊界／帽子／落點方程（網格）"),
    "BDD DAG、預算與 DPLL": ("hash-consed DAG 節點 ID；root 的 reachable node count 為 ROBDD 大小", "布林函數在固定變量次序下的共享規範圖；apply 是格運算的 memoized 實現", "同 manager root-id 相等、root≠0 的 sat、節點預算 FaceDecision、或有步數預算的 DPLL；另有候選變量次序最小化與 3ⁿ 最壞節點界"),
    "原始 DSystem 相容性與 first-match 範形": ("相容系統沿用 DSystem 型別導向範形；任意 first-match 系統化為不交有效區域 DTubeNF", "面相對切片中的偏元素；checked 構造是進入 composition 系統子類的反射", "BDD cube 枚舉上的局部脈絡轉換，檢查 base 與兩兩重疊；不相容回報首個衝突"),
    "AST 一等 Equiv 與 GlueEquiv": ("DEquiv 攜帶 fwd/bwd/sect/retr 四項；DVGlueEquiv 攜帶完整 Equiv 分支與 base/partial 對", "AST 內的等價是帶同倫逆證明的同構；ua 是通往宇宙路徑的函子，GlueEquiv 是沿 partial 等價系統的黏合", "雙向檢查四個分量與兩條 PathP 證明；conversion/quote 按 Equiv 分量與分支面遞迴；沿 ua 的 coe 定義地為 fwd/bwd"),
    "受檢查語義型別線": ("DCheckedTypeLine 保存已檢查的開放型別 body、脈絡、環境與宇宙層級，不保存裸宿主函數", "可代換的立方型別線由句法 body 在維度環境下求值，天然與維度代換交換", "構造時以新鮮維度檢查 body : Typeᵢ；at 以維度求值，coe/comp 直接派遣 AST Kan"),
    "Schema 註冊與 elaboration 快取": ("DSchemaRegistry 中以穩定 Debug 鍵 intern 的 DInductivePlan/DHitPlan 與 telescope 前綴鏈", "schema 描述子是可共享計劃；快取只保存同一 elaboration 函數的有限圖，不改變指稱", "驗證布爾值與語義 telescope 前綴按 (term,args,args) 鍵查表；hit/miss 計數可觀察"),
    "Schema 函子、正性與歸納遞迴": ("DPositiveFunctor 的 Id/Const/Product/Sum/List/Pi/Container 語法及其解碼型別；DPositivityReport 記錄出現與極性", "正性型別函子的初始代數與 decoded induction hypothesis；DDecode 是 Tarski 宇宙的歸納—遞迴解碼函數", "在別名展開後的 DTerm 上做極性遞迴：巢狀函子與正位置接受、負位置/未知中性族應用拒絕；IH 由函子遞迴生成"),
    "Schema 擴展：互歸納、商與宇宙多態": ("DMutualFamily 的 Sum-indexed 合併 schema；DLevelExpr 的層級 scheme；商即帶等式 1-cell 的 HIT", "互相歸納族是索引和上的單一初始代數；宇宙 scheme 是層級指派的函數；商構造為高階胞腔黏合", "互構子以分量索引約束編譯並以 Σ motive 消去；scheme 依層級向量求值並可再驗證；構造子等式以 Path 約束檢查"),
    "精確單變量多項式與有理矩陣": ("QPoly 的升冪稠密係數（尾零去除）；QMat 的有理列之列；RREF 與 pivot 列", "Q[x] 歐氏環與 Qⁿ 線性範疇；特徵/最小多項式是矩陣代數的表示不變量", "primitive pseudo-remainder gcd、Yun 重因數分解、有理根定理、Faddeev–LeVerrier、RREF；相等全為有理結構相等"),
    "代數擴張與根式範形": ("QuadNum 的 a+b√d（d 無平方因數）；AlgNum 的 Q[x]/(m) 餘式多項式", "二次擴張與一般有限代數擴張體；範數/跡由乘法矩陣行列式/跡給出", "模極小多項式的剩餘算術與擴張歐氏求逆；根式去巢以平方判別；相等為係數相等"),
    "廣義特徵空間與 Jordan 理論": ("(A−λI) 冪次零化列、遞增 nullity、Jordan 塊大小與鏈底基；PJP⁻¹=A", "主分解是互質多項式因子的單位分解；Jordan 型是相似等價的完全不變量片斷", "以特徵多項式重數、冪次核維度與鏈提升精確判定；不可在 Q 完全分裂者回報殘餘因子，AlgMat 在擴張上續行"),
    "認證數值影子與精確立方體": ("QuadC=QuadNum+i·QuadNum；CertMat 與次數≤2 的 CertPath/CertSquare 係數", "精確複二次矩陣代數與多項式立方體；Double 矩陣只是精確影子的近似表示", "P²=P、P†=P、正交分解與盒邊界以精確結構相等驗證；數值一致性只量測對影子的偏差與浮點 residual"),
    "球面與懸掛 HIT": ("Susp(X) 的 north/south 兩點與每點一條 meridian；S²=Susp(S¹)、S³=Susp(S²)", "懸掛是把 X×I 兩端各塌縮為一點的 HIT 商；迭代懸掛給出球面族", "generic HIT schema 驗證、meridian 端點 face 化簡、依賴消去與 hcomp"),
    "Jacobi 區間譜迭代": ("RatInterval/CInterval 矩形包絡與 dyadic 外向捨入後的 Hermitian 區間矩陣；每次旋轉保存 before/after 與累積酉變換", "Hermitian 相似變換在區間矩陣包絡上的單調提升；Gershgorin 圓盤給出譜的像分解與重數簇", "精確有理平方比較證明 sqrt/相位/c/s 包絡包含真值；逐旋轉重算 J†J−I∋0 與 J†AJ⊆after，最終圓盤分簇計數"),
    "高階合一與雙向 elaborator": ("UTerm 的 Miller pattern spine `?F x₁…xₙ` 與 zonk 後 beta/投影簡化核心；表面 STerm 按名解析為 de Bruijn UTerm", "pattern HOU 是高階合一的可判定片斷；雙向 elaboration 把隱含引數與 dependent motive 問題送入同一合一器再編譯至依賴覈心", "WHNF 後 rigid 分解、pattern 抽象、occurs/scope 檢查與閉項 fallback；check/infer 插入隱含 metavariables，未解者拒絕轉 DTerm"),
    "參數化模組與名字空間": ("模組 telescope（參數→imports→本地宣告）與分離的 name→ordinal bindings；實例是同時代換後的閉合宣告", "參數化模組是模組函子，import 是函子套用的內聯，open/alias/rename 是同一 telescope entry 的不同名字投影", "循環檢測、參數引數依賴檢查、import 選擇/隱藏/改名的歧義拒絕、opaque export 中性化，以及實例閉合後逐宣告 dep_check"),
    "範疇化總檢": ("範疇律的布爾合取", "彙總各範疇的身分／合成／相干律", "逐律求值"),
    "定理登記與範例": ("(名稱, Bool) 登記列；具體見證向量／項", "可判定命題在見證上的實現", "moon test／登記表"),
    "規格登記": ("SpecEntry 六元組", "規格之規格；完備性對產生介面核對", "spec_registry_sound＋本審計"),
    "輔助工具": ("整數／網格等具體值", "基礎集合層工具", "直接計算"),
    "重構證書與介面等價": (
        "SymbolSet 為排序去重的符號名集（介面）；RefactorPlan 為「有序宣告列 before/after ＋索引表」，索引表須為置換且每個索引兩側同名；RefactorCertificate 是該等價的 ua 像",
        "移動宣告＝同一個 package 命名空間內的介面等價；證書是路徑，判定向量沿路徑傳輸（coe），複合是路徑複合（ua 函子性）",
        "索引表以 `index_table_is_bijection` 判定置換性；`plan_agrees_with_univalence` 把計劃補齊到 2 的冪後拉回有限宇宙，故判定即 `fin_map_is_equiv`；丟失／改名／非置換一律拒絕",
    ),
    "可計算單值性與 n 維立方演算法": (
        "FinMap 為 |A| 長的目標索引列（可枚舉的表）；CPath 為 ua 像 (src, dst, 等價表)；NBox 為 2n−1 個 (n−1)-面立方體加一個缺失面，nfill 為面子格上的 Möbius 交錯和，ncomp 取缺失面",
        "等價的類型（表）與 ua 像（路徑）互為逆，兩方向逆律在全部元素上判決；開盒到填充是邊界限制映射的截面，且與維度重標交換",
        "表可枚舉故『ua 是等價』為窮舉判定（路徑數 = n!）；nfill 在樣本網格逐面核對，成本 2^(2n−1)−1 可作預算判決",
    ),
}

# English names for the generated appendix headings.
EN_FAMILY_NAMES = {
    "複數標量": "Complex scalars",
    "複向量與內積": "Complex vectors and inner product",
    "矩陣與伴隨": "Matrices and adjoint",
    "投影與特徵空間": "Projectors and eigenspaces",
    "Karoubi 包絡": "Karoubi envelope",
    "區間": "Interval",
    "面公式與 BDD": "Face formulas and BDDs",
    "面偏序範疇": "Face poset category",
    "系統與剪枝": "Systems and pruning",
    "系統符號範形": "Symbolic system normal forms",
    "立方體與 Kan 填充": "Cubes and Kan filling",
    "未型別 NbE": "Untyped NbE",
    "HOAS": "HOAS",
    "型別化 NbE 與 η": "Typed NbE and eta",
    "依賴型別 NbE（Π/Σ/宇宙）": "Dependent NbE (Pi/Sigma/universes)",
    "立方 AST 與維度 NbE": "Cubical AST and dimension NbE",
    "AST Kan comp/hcomp": "AST Kan comp/hcomp",
    "資料型別與 HIT 消去": "Data types and HIT elimination",
    "持久環境、惰性與語義快取": "Persistent environments, laziness and semantic caches",
    "依賴語義系統與 partial 值": "Dependent semantic systems and partial values",
    "通用歸納族 schema": "Generic inductive-family schemas",
    "通用 HIT schema": "Generic HIT schemas",
    "依賴 Kan 線（coe/comp）": "Dependent Kan lines (coe/comp)",
    "精確符號代數": "Exact symbolic algebra",
    "譜投影與仿射唯一填充": "Spectral projectors and unique affine filling",
    "句法笛卡兒閉範疇": "Syntactic cartesian closed category",
    "有限宇宙型別與值": "Finite universe types and values",
    "Wiring 符號等價": "Symbolic wirings of equivalences",
    "同構、等價、ua、coe": "Isomorphisms, equivalences, ua, coe",
    "PathP、離散路徑與 J": "PathP, discrete paths and J",
    "有限 Glue": "Finite Glue",
    "Glue comp（有限線）": "Glue comp (finite lines)",
    "Glue comp（子空間線）": "Glue comp (subspace lines)",
    "BDD DAG、預算與 DPLL": "BDD DAGs, budgets and DPLL",
    "原始 DSystem 相容性與 first-match 範形": "Raw DSystem compatibility and first-match normal forms",
    "AST 一等 Equiv 與 GlueEquiv": "First-class Equiv and GlueEquiv in the AST",
    "受檢查語義型別線": "Checked semantic type lines",
    "Schema 註冊與 elaboration 快取": "Schema registry and elaboration caches",
    "Schema 函子、正性與歸納遞迴": "Schema functors, positivity and induction-recursion",
    "Schema 擴展：互歸納、商與宇宙多態": "Schema extensions: mutual induction, quotients, universe polymorphism",
    "精確單變量多項式與有理矩陣": "Exact univariate polynomials and rational matrices",
    "代數擴張與根式範形": "Algebraic extensions and radical normal forms",
    "廣義特徵空間與 Jordan 理論": "Generalized eigenspaces and Jordan theory",
    "認證數值影子與精確立方體": "Certified numeric shadows and exact cubes",
    "球面與懸掛 HIT": "Spheres and suspension HITs",
    "Jacobi 區間譜迭代": "Jacobi interval spectral iteration",
    "高階合一與雙向 elaborator": "Higher-order unification and bidirectional elaboration",
    "參數化模組與名字空間": "Parametric modules and namespaces",
    "範疇化總檢": "Categorification audit",
    "定理登記與範例": "Theorem registry and examples",
    "規格登記": "Specification registry",
    "輔助工具": "Utilities",
    "可計算單值性與 n 維立方演算法": "Computable univalence and the n-dimensional cube algorithm",
    "重構證書與介面等價": "Refactor certificates and interface equivalence",
}

TYPE_FAMILY = {
    "Complex": "複數標量", "CVec": "複向量與內積", "CMat": "矩陣與伴隨",
    "Dim": "區間", "Face": "面公式與 BDD", "Bdd": "面公式與 BDD",
    "VecBranch": "系統與剪枝", "VecSystem": "系統與剪枝",
    "SymRegion": "系統符號範形", "SystemNF": "系統符號範形",
    "Cube": "立方體與 Kan 填充",
    "Term": "未型別 NbE", "Neutral": "未型別 NbE", "Value": "未型別 NbE",
    "HTm": "HOAS",
    "LTy": "型別化 NbE 與 η", "TNeutral": "型別化 NbE 與 η",
    "TValue": "型別化 NbE 與 η", "TypedValue": "型別化 NbE 與 η",
    "Ty": "有限宇宙型別與值", "PVal": "有限宇宙型別與值",
    "LeafKind": "Wiring 符號等價", "LeafMap": "Wiring 符號等價", "Wiring": "Wiring 符號等價",
    "Iso": "同構、等價、ua、coe", "Equiv": "同構、等價、ua、coe", "UPath": "同構、等價、ua、coe",
    "PathPVal": "PathP、離散路徑與 J", "DiscPath": "PathP、離散路徑與 J", "Family": "PathP、離散路徑與 J",
    "GlueData": "有限 Glue", "GlueElem": "有限 Glue",
    "GlueLineFinite": "Glue comp（有限線）",
    "SubLine": "Glue comp（子空間線）", "LinEquivLine": "Glue comp（子空間線）",
    "GlueLineVec": "Glue comp（子空間線）", "VecBox": "Glue comp（子空間線）",
    "GlueCompVecResult": "Glue comp（子空間線）",
    "DEnv": "持久環境、惰性與語義快取", "DDimEnv": "持久環境、惰性與語義快取",
    "DThunk": "持久環境、惰性與語義快取",
    "DSystem": "依賴語義系統與 partial 值", "DFaceTerm": "依賴語義系統與 partial 值",
    "DFaceValue": "依賴語義系統與 partial 值", "DPartialValue": "依賴語義系統與 partial 值",
    "DSystemClass": "依賴語義系統與 partial 值", "DSystemNF": "依賴語義系統與 partial 值",
    "DArgKind": "通用歸納族 schema", "DTelescopeEntry": "通用歸納族 schema",
    "DConstructorArg": "通用歸納族 schema", "DConstructorSpec": "通用歸納族 schema",
    "DInductiveSpec": "通用歸納族 schema",
    "DHitFaceExpr": "通用 HIT schema", "DHitCellSpec": "通用 HIT schema", "DHitSpec": "通用 HIT schema",
    "DTerm": "依賴型別 NbE（Π/Σ/宇宙）", "DNeutral": "依賴型別 NbE（Π/Σ/宇宙）",
    "DValue": "依賴型別 NbE（Π/Σ/宇宙）", "DInfer": "依賴型別 NbE（Π/Σ/宇宙）",
    "DTypeVal": "依賴型別 NbE（Π/Σ/宇宙）", "DFamilyParts": "依賴型別 NbE（Π/Σ/宇宙）",
    "DTubeTerm": "立方 AST 與維度 NbE", "DPathParts": "立方 AST 與維度 NbE",
    "DGlueParts": "立方 AST 與維度 NbE", "DTubeBranch": "依賴語義系統與 partial 值",
    "DLine": "依賴 Kan 線（coe/comp）",
    "Rat": "精確符號代數", "PolyTerm": "精確符號代數", "Poly": "精確符號代數",
    "SymFrac": "精確符號代數", "SymC": "精確符號代數", "SymMat": "精確符號代數",
    "UPoly": "精確符號代數", "SymVec": "精確符號代數",
    "RPoly": "譜投影與仿射唯一填充", "RPolyDiv": "譜投影與仿射唯一填充",
    "SymPath": "譜投影與仿射唯一填充", "SymSquare": "譜投影與仿射唯一填充",
    "CheckResult": "定理登記與範例",
    "SpecKind": "規格登記", "SpecEntry": "規格登記",
    "BddApplyEntry": "BDD DAG、預算與 DPLL", "BddBestBuild": "BDD DAG、預算與 DPLL",
    "BddDagFace": "BDD DAG、預算與 DPLL", "BddDagNode": "BDD DAG、預算與 DPLL",
    "BddManager": "BDD DAG、預算與 DPLL", "FaceDecision": "BDD DAG、預算與 DPLL",
    "FaceSatDecision": "BDD DAG、預算與 DPLL",
    "SymbolSet": "重構證書與介面等價", "IndexTable": "重構證書與介面等價",
    "RefactorPlan": "重構證書與介面等價", "RefactorCertificate": "重構證書與介面等價",
    "DecoupleStep": "重構證書與介面等價",
    "FinMap": "可計算單值性與 n 維立方演算法", "CPath": "可計算單值性與 n 維立方演算法",
    "NBox": "可計算單值性與 n 維立方演算法", "NBoxSide": "可計算單值性與 n 維立方演算法",
    "DSystemCompatibility": "原始 DSystem 相容性與 first-match 範形",
    "DSystemIncompatibility": "原始 DSystem 相容性與 first-match 範形",
    "DTubeNF": "原始 DSystem 相容性與 first-match 範形",
    "DTubeNFClass": "原始 DSystem 相容性與 first-match 範形",
    "DEquivBranch": "AST 一等 Equiv 與 GlueEquiv", "DEquivBranchValue": "AST 一等 Equiv 與 GlueEquiv",
    "DEquivParts": "AST 一等 Equiv 與 GlueEquiv", "DEquivTypeParts": "AST 一等 Equiv 與 GlueEquiv",
    "DGlueEquivParts": "AST 一等 Equiv 與 GlueEquiv",
    "DCheckedTypeLine": "受檢查語義型別線",
    "DHitPlan": "Schema 註冊與 elaboration 快取", "DInductivePlan": "Schema 註冊與 elaboration 快取",
    "DSchemaRegistry": "Schema 註冊與 elaboration 快取", "DTelescopeCacheEntry": "Schema 註冊與 elaboration 快取",
    "DPositiveFunctor": "Schema 函子、正性與歸納遞迴", "DPositivityReport": "Schema 函子、正性與歸納遞迴",
    "DConstructorConstraint": "Schema 擴展：互歸納、商與宇宙多態",
    "DHitLevelScheme": "Schema 擴展：互歸納、商與宇宙多態",
    "DInductiveLevelScheme": "Schema 擴展：互歸納、商與宇宙多態",
    "DLevelExpr": "Schema 擴展：互歸納、商與宇宙多態", "DMutualFamily": "Schema 擴展：互歸納、商與宇宙多態",
    "QPoly": "精確單變量多項式與有理矩陣", "QMat": "精確單變量多項式與有理矩陣",
    "QVec": "精確單變量多項式與有理矩陣", "QPolyDiv": "精確單變量多項式與有理矩陣",
    "QPolyExtGcd": "精確單變量多項式與有理矩陣", "QPolyFactor": "精確單變量多項式與有理矩陣",
    "QPolyRationalFactorization": "精確單變量多項式與有理矩陣", "QRref": "精確單變量多項式與有理矩陣",
    "QuadNum": "代數擴張與根式範形", "AlgNum": "代數擴張與根式範形",
    "AlgGeneralizedEigenspace": "廣義特徵空間與 Jordan 理論", "AlgJordanDecomposition": "廣義特徵空間與 Jordan 理論",
    "AlgMat": "廣義特徵空間與 Jordan 理論", "AlgRref": "廣義特徵空間與 Jordan 理論", "AlgVec": "廣義特徵空間與 Jordan 理論",
    "QGeneralizedEigenspace": "廣義特徵空間與 Jordan 理論", "QJordanDecomposition": "廣義特徵空間與 Jordan 理論",
    "QPrimaryProjector": "廣義特徵空間與 Jordan 理論", "QRationalSpectrum": "廣義特徵空間與 Jordan 理論",
    "CertMat": "認證數值影子與精確立方體", "CertVec": "認證數值影子與精確立方體",
    "CertPath": "認證數值影子與精確立方體", "CertSquare": "認證數值影子與精確立方體",
    "QuadC": "認證數值影子與精確立方體", "ProjectorCertificate": "認證數值影子與精確立方體",
    "NumericProjectorCertificate": "認證數值影子與精確立方體",
    "RatInterval": "Jacobi 區間譜迭代", "CInterval": "Jacobi 區間譜迭代",
    "QCpx": "Jacobi 區間譜迭代", "QCpxMat": "Jacobi 區間譜迭代",
    "QCIntervalMat": "Jacobi 區間譜迭代", "JacobiCoefficients": "Jacobi 區間譜迭代",
    "JacobiRotationCertificate": "Jacobi 區間譜迭代", "JacobiCertificate": "Jacobi 區間譜迭代",
    "EigenInterval": "Jacobi 區間譜迭代",
    "UTerm": "高階合一與雙向 elaborator", "UMetaInfo": "高階合一與雙向 elaborator",
    "Unifier": "高階合一與雙向 elaborator", "STerm": "高階合一與雙向 elaborator",
    "ElabVar": "高階合一與雙向 elaborator", "Elaborator": "高階合一與雙向 elaborator",
    "ElabResult": "高階合一與雙向 elaborator",
    "ModuleRename": "參數化模組與名字空間", "ModuleImport": "參數化模組與名字空間",
    "ModuleDecl": "參數化模組與名字空間", "ModuleDef": "參數化模組與名字空間",
    "ModuleEnv": "參數化模組與名字空間", "ModuleEntry": "參數化模組與名字空間",
    "ModuleBinding": "參數化模組與名字空間", "ModuleExport": "參數化模組與名字空間",
    "ModuleSignature": "參數化模組與名字空間", "ModuleInstanceDecl": "參數化模組與名字空間",
    "ModuleInstance": "參數化模組與名字空間",
}

EXACT = {
    "bool_ops_module": "參數化模組與名字空間", "generic_iterate_module": "參數化模組與名字空間",
    "container_tree_schema": "Schema 函子、正性與歸納遞迴",
    "as_equiv_type": "AST 一等 Equiv 與 GlueEquiv", "as_glue_equiv": "AST 一等 Equiv 與 GlueEquiv",
    "bool_not_equiv_term": "AST 一等 Equiv 與 GlueEquiv", "bool_not_term": "AST 一等 Equiv 與 GlueEquiv",
    "comp_equiv_value": "AST 一等 Equiv 與 GlueEquiv", "comp_glue_equiv_value": "AST 一等 Equiv 與 GlueEquiv",
    "d_check_glue_equiv_partial": "AST 一等 Equiv 與 GlueEquiv", "d_equiv_branch": "AST 一等 Equiv 與 GlueEquiv",
    "dequiv_branch_value": "AST 一等 Equiv 與 GlueEquiv", "mk_equiv_term": "AST 一等 Equiv 與 GlueEquiv",
    "conv_at_under_face": "原始 DSystem 相容性與 first-match 範形",
    "tube_paths_conv_under_face": "原始 DSystem 相容性與 first-match 範形",
    "dtube_nf_class": "原始 DSystem 相容性與 first-match 範形",
    "default_schema_registry": "Schema 註冊與 elaboration 快取",
    "dterm_children": "Schema 函子、正性與歸納遞迴", "dterm_shift": "Schema 函子、正性與歸納遞迴",
    "dterm_substitute": "Schema 函子、正性與歸納遞迴", "conv_schema_args_full": "Schema 函子、正性與歸納遞迴",
    "decode_term": "Schema 函子、正性與歸納遞迴", "infer_decode": "Schema 函子、正性與歸納遞迴",
    "conv_decode_neutral": "Schema 函子、正性與歸納遞迴", "comp_schema_args_decoded": "Schema 函子、正性與歸納遞迴",
    "circle_level_scheme": "Schema 擴展：互歸納、商與宇宙多態", "list_level_scheme": "Schema 擴展：互歸納、商與宇宙多態",
    "cube3_schema": "Schema 擴展：互歸納、商與宇宙多態", "equal_nat_pair_schema": "Schema 擴展：互歸納、商與宇宙多態",
    "even_odd_components": "Schema 擴展：互歸納、商與宇宙多態", "even_odd_family": "Schema 擴展：互歸納、商與宇宙多態",
    "tree_forest_components": "Schema 擴展：互歸納、商與宇宙多態", "tree_forest_family": "Schema 擴展：互歸納、商與宇宙多態",
    "rose_tree_schema": "Schema 擴展：互歸納、商與宇宙多態", "tarski_universe_schema": "Schema 擴展：互歸納、商與宇宙多態",
    "quotient_eq_term": "Schema 擴展：互歸納、商與宇宙多態", "quotient_point_term": "Schema 擴展：互歸納、商與宇宙多態",
    "quotient_schema": "Schema 擴展：互歸納、商與宇宙多態",
    "int_sqrt_exact": "代數擴張與根式範形", "int_squarefree_decomp": "代數擴張與根式範形",
    "double_dyadic_interval": "認證數值影子與精確立方體",
    "eps": "複數標量",
    "outer": "投影與特徵空間", "outer2": "Glue comp（子空間線）",
    "assignment_of_mask": "面公式與 BDD", "pow2": "面公式與 BDD",
    "vec_box": "Glue comp（子空間線）", "vec_lex_lt": "系統符號範形",
    "vec_normalize": "Glue comp（子空間線）",
    "vec_e3": "定理登記與範例", "grid": "定理登記與範例",
    "inv_sqrt2": "定理登記與範例", "example_unit": "定理登記與範例",
    "example_projector": "定理登記與範例", "sample_vectors": "定理登記與範例",
    "sample_terms": "定理登記與範例",
    "disc_samples": "PathP、離散路徑與 J",
    "tm_id": "未型別 NbE", "tm_const": "未型別 NbE", "tm_swap": "未型別 NbE",
    "coe_rules_definitional": "未型別 NbE", "swap_involutive_on_element": "未型別 NbE",
    "cube_in_subline": "Glue comp（子空間線）",
    "prune_cube_subline": "Glue comp（子空間線）",
    "int_pow": "輔助工具", "sort_ints": "面公式與 BDD", "contains_int": "面公式與 BDD",
    "dmin": "區間", "dmax": "區間",
    "check_categories_all": "範疇化總檢",
    "spec_registry_sound": "規格登記",
    "deval": "依賴型別 NbE（Π/Σ/宇宙）", "d_infer": "依賴型別 NbE（Π/Σ/宇宙）",
    "d_check": "依賴型別 NbE（Π/Σ/宇宙）", "d_as_type": "依賴型別 NbE（Π/Σ/宇宙）",
    "dapp_typed": "依賴型別 NbE（Π/Σ/宇宙）", "dfst_typed": "依賴型別 NbE（Π/Σ/宇宙）",
    "dsnd_typed": "依賴型別 NbE（Π/Σ/宇宙）", "as_pi": "依賴型別 NbE（Π/Σ/宇宙）",
    "as_sigma": "依賴型別 NbE（Π/Σ/宇宙）", "as_univ_level": "依賴型別 NbE（Π/Σ/宇宙）",
    "conv_at": "依賴型別 NbE（Π/Σ/宇宙）", "conv_ty": "依賴型別 NbE（Π/Σ/宇宙）",
    "conv_neutral": "依賴型別 NbE（Π/Σ/宇宙）", "quote_at": "依賴型別 NbE（Π/Σ/宇宙）",
    "quote_ty": "依賴型別 NbE（Π/Σ/宇宙）", "quote_dneutral": "依賴型別 NbE（Π/Σ/宇宙）",
    "dep_type_val_of": "依賴型別 NbE（Π/Σ/宇宙）", "lty_to_dterm": "依賴型別 NbE（Π/Σ/宇宙）",
    "as_path": "立方 AST 與維度 NbE", "as_glue": "立方 AST 與維度 NbE",
    "as_list_elem": "立方 AST 與維度 NbE", "d_tube": "立方 AST 與維度 NbE",
    "fresh_dim": "立方 AST 與維度 NbE", "deval_dim": "立方 AST 與維度 NbE",
    "eval_dim_expr": "立方 AST 與維度 NbE", "eval_tube_terms": "立方 AST 與維度 NbE",
    "dim_quote": "立方 AST 與維度 NbE", "face_eval_env": "立方 AST 與維度 NbE",
    "face_quote": "立方 AST 與維度 NbE", "quote_tube_branches": "立方 AST 與維度 NbE",
    "dapp_dim": "立方 AST 與維度 NbE", "dep_def_eq_closed": "立方 AST 與維度 NbE",
    "dim_vars_of": "AST Kan comp/hcomp", "dim_nvars_sem": "AST Kan comp/hcomp",
    "dim_eq_sem": "AST Kan comp/hcomp", "face_nvars_sem": "AST Kan comp/hcomp",
    "face_is_top_sem": "AST Kan comp/hcomp", "face_is_bot_sem": "AST Kan comp/hcomp",
    "face_is_sat_sem": "AST Kan comp/hcomp", "tube_branch": "依賴語義系統與 partial 值",
    "map_branches": "依賴語義系統與 partial 值", "comp_value": "AST Kan comp/hcomp",
    "hcomp_value": "AST Kan comp/hcomp", "fill_value": "AST Kan comp/hcomp",
    "hfill_value": "AST Kan comp/hcomp", "coe_value": "AST Kan comp/hcomp",
    "comp_pi_value": "AST Kan comp/hcomp", "comp_sigma_value": "AST Kan comp/hcomp",
    "comp_path_value": "AST Kan comp/hcomp", "comp_glue_value": "AST Kan comp/hcomp",
    "comp_univ_value": "AST Kan comp/hcomp", "hcomp_univ_value": "AST Kan comp/hcomp",
    "circle_point": "資料型別與 HIT 消去", "torus_point": "資料型別與 HIT 消去",
    "circle_dim_of": "資料型別與 HIT 消去", "torus_dims_of": "資料型別與 HIT 消去",
    "d_nat_lit": "資料型別與 HIT 消去", "dv_nat_lit": "資料型別與 HIT 消去",
    "eval_bool_elim": "資料型別與 HIT 消去", "eval_nat_elim": "資料型別與 HIT 消去", "eval_list_elim": "資料型別與 HIT 消去",
    "eval_circle_elim": "資料型別與 HIT 消去", "eval_torus_elim": "資料型別與 HIT 消去",
    "comp_bool_value": "資料型別與 HIT 消去", "comp_nat_value": "資料型別與 HIT 消去",
    "comp_list_value": "資料型別與 HIT 消去", "comp_circle_value": "資料型別與 HIT 消去",
    "comp_torus_value": "資料型別與 HIT 消去",
    "quote_eta": "型別化 NbE 與 η", "quote_tneutral": "型別化 NbE 與 η",
    "nf_eta": "型別化 NbE 與 η", "def_eq_eta": "型別化 NbE 與 η",
    "sym_affine_path": "譜投影與仿射唯一填充", "sym_square_fill": "譜投影與仿射唯一填充",
    "sym_bilinear_from_corners": "譜投影與仿射唯一填充", "sym_bilinear_ansatz": "譜投影與仿射唯一填充",
    "sym_frac_one_minus": "譜投影與仿射唯一填充", "sym_hermitian2": "譜投影與仿射唯一填充",
    "d_face_term": "依賴語義系統與 partial 值", "dface_value": "依賴語義系統與 partial 值",
    "glue_partial_values": "依賴語義系統與 partial 值", "glue_store_partial": "依賴語義系統與 partial 值",
    "dim_cache_key": "持久環境、惰性與語義快取",
    "check_telescope_terms": "通用歸納族 schema", "telescope_type_values": "通用歸納族 schema",
    "conv_telescope_values": "通用歸納族 schema", "quote_telescope_values": "通用歸納族 schema",
    "conv_schema_args": "通用歸納族 schema", "quote_schema_args": "通用歸納族 schema",
    "schema_motives_conv": "通用歸納族 schema", "quote_schema_motive": "通用歸納族 schema",
    "comp_schema_args": "通用歸納族 schema", "comp_inductive_value": "通用歸納族 schema",
    "eval_inductive_elim": "通用歸納族 schema", "eval_inductive_elim_term": "通用歸納族 schema",
    "eval_inductive_type_term": "通用歸納族 schema", "eval_intro_term": "通用歸納族 schema",
    "infer_inductive_elim": "通用歸納族 schema", "infer_inductive_type": "通用歸納族 schema",
    "infer_intro": "通用歸納族 schema", "conv_inductive_elim_neutral": "通用歸納族 schema",
    "conv_inductive_type": "通用歸納族 schema", "conv_intro_at": "通用歸納族 schema",
    "quote_inductive_elim_neutral": "通用歸納族 schema",
    "quote_inductive_type": "通用歸納族 schema", "quote_intro_at": "通用歸納族 schema",
    "nat_schema": "通用歸納族 schema", "bool_schema": "通用歸納族 schema",
    "list_schema": "通用歸納族 schema", "vec_schema": "通用歸納族 schema",
    "fin_schema": "通用歸納族 schema", "tree_schema": "通用歸納族 schema", "w_schema": "通用歸納族 schema",
    "nat_schema_lit": "通用歸納族 schema",
    "eval_hit_elim": "通用 HIT schema", "eval_hit_elim_term": "通用 HIT schema",
    "eval_hit_intro_term": "通用 HIT schema", "eval_hit_type_term": "通用 HIT schema",
    "infer_hit_elim": "通用 HIT schema", "infer_hit_intro": "通用 HIT schema", "infer_hit_type": "通用 HIT schema",
    "conv_hit_cell_at": "通用 HIT schema", "conv_hit_elim_neutral": "通用 HIT schema",
    "conv_hit_type": "通用 HIT schema", "quote_hit_cell_at": "通用 HIT schema",
    "quote_hit_elim_neutral": "通用 HIT schema", "quote_hit_type": "通用 HIT schema",
    "comp_hit_value": "通用 HIT schema", "circle_schema": "通用 HIT schema",
    "segment_schema": "通用 HIT schema", "torus_schema": "通用 HIT schema",
}

CHECK_FAMILY_HINTS = [
    ("sphere3", "球面與懸掛 HIT"),
    ("jacobi_interval", "Jacobi 區間譜迭代"),
    ("hou_elaborator", "高階合一與雙向 elaborator"),
    ("module_system", "參數化模組與名字空間"),
    ("container_functor", "Schema 函子、正性與歸納遞迴"),
    ("bdd_and_certified", "認證數值影子與精確立方體"),
    ("algebraic_extensions", "廣義特徵空間與 Jordan 理論"),
    ("phase6_infrastructure", "受檢查語義型別線"),
    ("equiv_ast", "AST 一等 Equiv 與 GlueEquiv"),
    ("dsystem_compatibility", "原始 DSystem 相容性與 first-match 範形"),
    ("dsystem_first_match", "原始 DSystem 相容性與 first-match 範形"),
    ("schema_extensions", "Schema 擴展：互歸納、商與宇宙多態"),
    ("structural_positivity", "Schema 函子、正性與歸納遞迴"),
    ("tarski", "Schema 函子、正性與歸納遞迴"),
    ("nested_rose", "Schema 函子、正性與歸納遞迴"),
    ("hit_schema", "通用 HIT schema"), ("hit_endpoint", "通用 HIT schema"),
    ("generated_hit", "通用 HIT schema"), ("schema", "通用歸納族 schema"),
    ("generated_inductive", "通用歸納族 schema"), ("persistent", "持久環境、惰性與語義快取"),
    ("dsystem", "依賴語義系統與 partial 值"), ("multibranch", "依賴語義系統與 partial 值"),
    ("phase5", "依賴語義系統與 partial 值"),
    ("ast_kan", "AST Kan comp/hcomp"), ("ast_coe", "AST Kan comp/hcomp"),
    ("ast_hcomp", "AST Kan comp/hcomp"), ("ast_bool", "資料型別與 HIT 消去"), ("ast_nat", "資料型別與 HIT 消去"),
    ("ast_list", "資料型別與 HIT 消去"), ("ast_data", "資料型別與 HIT 消去"),
    ("ast_hits", "資料型別與 HIT 消去"), ("ast", "立方 AST 與維度 NbE"),
    ("dep", "依賴型別 NbE（Π/Σ/宇宙）"),
    ("kan_coe", "依賴 Kan 線（coe/comp）"), ("kan_comp", "依賴 Kan 線（coe/comp）"),
    ("kan_embeddings", "依賴 Kan 線（coe/comp）"), ("kan_dep", "依賴 Kan 線（coe/comp）"),
    ("kan_all", "依賴 Kan 線（coe/comp）"),
    ("spectral", "譜投影與仿射唯一填充"), ("symbolic", "譜投影與仿射唯一填充"),
    ("bdd", "面公式與 BDD"), ("eta", "型別化 NbE 與 η"),
    ("wiring", "Wiring 符號等價"),
    ("glue_comp", "Glue comp（有限線）"), ("glue", "有限 Glue"),
    ("karoubi", "Karoubi 包絡"), ("face_poset", "面偏序範疇"),
    ("syntactic", "句法笛卡兒閉範疇"), ("cubical", "立方體與 Kan 填充"),
    ("categories", "範疇化總檢"),
    ("projector", "投影與特徵空間"), ("eigenspace", "投影與特徵空間"),
    ("commuting", "投影與特徵空間"), ("orthogonal", "投影與特徵空間"),
    ("kan", "立方體與 Kan 填充"), ("cube", "立方體與 Kan 填充"),
    ("interval", "面公式與 BDD"), ("systems", "系統與剪枝"),
    ("nbe", "未型別 NbE"), ("coe", "同構、等價、ua、coe"),
    ("hoas", "HOAS"), ("ua", "同構、等價、ua、coe"),
    ("pathp", "PathP、離散路徑與 J"), ("j", "PathP、離散路徑與 J"),
]

PREFIXES = [
    ("symbol_set", "重構證書與介面等價"),
    ("symbol_set_size", "重構證書與介面等價"),
    ("symbol_set_items", "重構證書與介面等價"),
    ("symbol_set_eq", "重構證書與介面等價"),
    ("symbol_set_contains", "重構證書與介面等價"),
    ("symbol_set_index", "重構證書與介面等價"),
    ("ordered_items", "重構證書與介面等價"),
    ("ordered_index", "重構證書與介面等價"),
    ("index_table", "重構證書與介面等價"),
    ("index_table_size", "重構證書與介面等價"),
    ("index_table_identity", "重構證書與介面等價"),
    ("index_table_is_bijection", "重構證書與介面等價"),
    ("index_table_inv", "重構證書與介面等價"),
    ("index_table_comp", "重構證書與介面等價"),
    ("index_table_is_identity", "重構證書與介面等價"),
    ("refactor_plan", "重構證書與介面等價"),
    ("refactor_plan_size", "重構證書與介面等價"),
    ("plan_preserves_symbol_set", "重構證書與介面等價"),
    ("plan_of_ordered", "重構證書與介面等價"),
    ("refactor_is_equivalence", "重構證書與介面等價"),
    ("certify", "重構證書與介面等價"),
    ("certificate_label", "重構證書與介面等價"),
    ("certificate_is_identity", "重構證書與介面等價"),
    ("certificate_transport_int", "重構證書與介面等價"),
    ("certificate_transport_roundtrip", "重構證書與介面等價"),
    ("certificate_compose", "重構證書與介面等價"),
    ("certificate_inverse", "重構證書與介面等價"),
    ("ty_of_bits", "重構證書與介面等價"),
    ("next_pow2", "重構證書與介面等價"),
    ("log2_int", "重構證書與介面等價"),
    ("plan_to_fin_map", "重構證書與介面等價"),
    ("plan_agrees_with_univalence", "重構證書與介面等價"),
    ("decouple_step", "重構證書與介面等價"),
    ("decoupling_steps", "重構證書與介面等價"),
    ("decoupling_certified", "重構證書與介面等價"),
    ("decoupling_conserves_names", "重構證書與介面等價"),
    ("decoupling_preserves_families", "重構證書與介面等價"),
    ("refactor_certificates_sound", "重構證書與介面等價"),
    ("fin_", "可計算單值性與 n 維立方演算法"),
    ("fin", "可計算單值性與 n 維立方演算法"),
    ("ua_", "可計算單值性與 n 維立方演算法"),
    ("cpath_", "可計算單值性與 n 維立方演算法"),
    ("ty_card", "可計算單值性與 n 維立方演算法"),
    ("j_rule_on_ua", "可計算單值性與 n 維立方演算法"),
    ("transport_", "可計算單值性與 n 維立方演算法"),
    ("nbox", "可計算單值性與 n 維立方演算法"),
    ("nfill", "可計算單值性與 n 維立方演算法"),
    ("ncomp", "可計算單值性與 n 維立方演算法"),
    ("cube_approx_eq", "可計算單值性與 n 維立方演算法"),
    ("sphere", "球面與懸掛 HIT"), ("suspension_", "球面與懸掛 HIT"),
    ("rat_interval", "Jacobi 區間譜迭代"), ("rat_sqrt_interval", "Jacobi 區間譜迭代"),
    ("rat_cmp_exact", "Jacobi 區間譜迭代"), ("rat_le_exact", "Jacobi 區間譜迭代"),
    ("rat_abs_exact", "Jacobi 區間譜迭代"), ("rat_round_", "Jacobi 區間譜迭代"),
    ("cinterval", "Jacobi 區間譜迭代"), ("qci_", "Jacobi 區間譜迭代"),
    ("qcpx", "Jacobi 區間譜迭代"), ("jacobi_", "Jacobi 區間譜迭代"),
    ("eigen_interval", "Jacobi 區間譜迭代"),
    ("elab_", "高階合一與雙向 elaborator"), ("elaborator_", "高階合一與雙向 elaborator"),
    ("hou_", "高階合一與雙向 elaborator"), ("unifier_", "高階合一與雙向 elaborator"),
    ("uterm_", "高階合一與雙向 elaborator"), ("uty_", "高階合一與雙向 elaborator"),
    ("module_", "參數化模組與名字空間"),
    ("bdd_manager", "BDD DAG、預算與 DPLL"), ("bdd_dag", "BDD DAG、預算與 DPLL"),
    ("bdd_tree_of_dag", "BDD DAG、預算與 DPLL"), ("bdd_worst", "BDD DAG、預算與 DPLL"),
    ("bdd_var_order", "BDD DAG、預算與 DPLL"),
    ("face_sat_dpll", "BDD DAG、預算與 DPLL"), ("face_eq_dpll", "BDD DAG、預算與 DPLL"),
    ("face_sat_within_budget", "BDD DAG、預算與 DPLL"), ("face_eq_within_budget", "BDD DAG、預算與 DPLL"),
    ("checked_", "受檢查語義型別線"),
    ("infer_equiv", "AST 一等 Equiv 與 GlueEquiv"), ("infer_glue_equiv", "AST 一等 Equiv 與 GlueEquiv"),
    ("infer_mk_equiv", "AST 一等 Equiv 與 GlueEquiv"), ("infer_ua", "AST 一等 Equiv 與 GlueEquiv"),
    ("dfunctor_", "Schema 函子、正性與歸納遞迴"), ("positive_functor_", "Schema 函子、正性與歸納遞迴"),
    ("dterm_family_", "Schema 函子、正性與歸納遞迴"), ("dpositivity_", "Schema 函子、正性與歸納遞迴"),
    ("mutual_", "Schema 擴展：互歸納、商與宇宙多態"), ("compile_mutual", "Schema 擴展：互歸納、商與宇宙多態"),
    ("instantiate_", "Schema 擴展：互歸納、商與宇宙多態"), ("dlevel_", "Schema 擴展：互歸納、商與宇宙多態"),
    ("qmat_generalized", "廣義特徵空間與 Jordan 理論"), ("qmat_Jordan", "廣義特徵空間與 Jordan 理論"),
    ("qmat_primary", "廣義特徵空間與 Jordan 理論"), ("qmat_eigen", "廣義特徵空間與 Jordan 理論"),
    ("qmat_diagonalizable", "廣義特徵空間與 Jordan 理論"), ("qmat_is_diagonalizable", "廣義特徵空間與 Jordan 理論"),
    ("qmat_rational_spectrum", "廣義特徵空間與 Jordan 理論"), ("qmat_vector_annihilator", "廣義特徵空間與 Jordan 理論"),
    ("qpoly_", "精確單變量多項式與有理矩陣"), ("qmat_", "精確單變量多項式與有理矩陣"),
    ("qrows_", "精確單變量多項式與有理矩陣"), ("qvec_", "精確單變量多項式與有理矩陣"),
    ("quad_", "代數擴張與根式範形"), ("alg_", "代數擴張與根式範形"),
    ("algmat_", "廣義特徵空間與 Jordan 理論"), ("algrows_", "廣義特徵空間與 Jordan 理論"),
    ("algvec_", "廣義特徵空間與 Jordan 理論"),
    ("cert_", "認證數值影子與精確立方體"), ("certify_", "認證數值影子與精確立方體"),
    ("qcc_", "認證數值影子與精確立方體"), ("numeric_", "認證數值影子與精確立方體"),
    ("cx", "複數標量"), ("cx_", "複數標量"),
    ("vec_", "複向量與內積"), ("inner", "複向量與內積"),
    ("mat_", "矩陣與伴隨"),
    ("is_", "投影與特徵空間"), ("eigen", "投影與特徵空間"),
    ("projector_", "投影與特徵空間"), ("decompose", "投影與特徵空間"),
    ("complement", "投影與特徵空間"),
    ("in_image", "投影與特徵空間"), ("in_kernel", "投影與特徵空間"),
    ("prune_to_eigenspace", "投影與特徵空間"), ("pruning_is_retraction", "投影與特徵空間"),
    ("commuting", "投影與特徵空間"),
    ("karoubi_", "Karoubi 包絡"),
    ("eval_dim", "區間"), ("interval_", "區間"),
    ("bdd_", "面公式與 BDD"), ("dim_", "面公式與 BDD"), ("face_", "面公式與 BDD"),
    ("system_", "系統與剪枝"), ("branch", "系統與剪枝"),
    ("prune_system", "系統與剪枝"), ("pruning_respects", "系統與剪枝"),
    ("compatibility_", "系統與剪枝"), ("union_", "系統與剪枝"),
    ("cube_", "立方體與 Kan 填充"), ("path_line", "立方體與 Kan 填充"),
    ("path_refl", "立方體與 Kan 填充"), ("path_sym", "立方體與 Kan 填充"),
    ("path_eval", "立方體與 Kan 填充"), ("path_start", "立方體與 Kan 填充"),
    ("path_end", "立方體與 Kan 填充"), ("path_trans", "立方體與 Kan 填充"),
    ("restrict_face", "立方體與 Kan 填充"), ("degenerate_", "立方體與 Kan 填充"),
    ("square_fill", "立方體與 Kan 填充"), ("open_box", "立方體與 Kan 填充"),
    ("filler_", "立方體與 Kan 填充"), ("kan_", "立方體與 Kan 填充"),
    ("prune_cube", "立方體與 Kan 填充"), ("bumped_filler", "立方體與 Kan 填充"),
    ("pruning_repairs", "立方體與 Kan 填充"), ("eigenspace_kan", "立方體與 Kan 填充"),
    ("eval", "未型別 NbE"), ("quote", "未型別 NbE"), ("nf", "未型別 NbE"),
    ("def_eq", "未型別 NbE"), ("nbe_", "未型別 NbE"),
    ("vapp", "未型別 NbE"), ("vfst", "未型別 NbE"), ("vsnd", "未型別 NbE"),
    ("happ", "HOAS"), ("hfst", "HOAS"), ("hsnd", "HOAS"), ("hoas_", "HOAS"),
    ("term_to_hoas", "HOAS"),
    ("ty_", "型別化 NbE 與 η"), ("eval_check_t", "型別化 NbE 與 η"),
    ("eval_infer_t", "型別化 NbE 與 η"), ("tapp", "型別化 NbE 與 η"),
    ("tfst", "型別化 NbE 與 η"), ("tsnd", "型別化 NbE 與 η"),
    ("quote_eta", "型別化 NbE 與 η"), ("quote_tneutral", "型別化 NbE 與 η"),
    ("nf_eta", "型別化 NbE 與 η"), ("def_eq_eta", "型別化 NbE 與 η"),
    ("eta_", "型別化 NbE 與 η"),
    ("tm_shift", "句法笛卡兒閉範疇"), ("tm_comp", "句法笛卡兒閉範疇"),
    ("tm_id_at", "句法笛卡兒閉範疇"), ("tm_swap_at", "型別化 NbE 與 η"),
    ("tm_coe_swap_at", "型別化 NbE 與 η"),
    ("elems_of", "有限宇宙型別與值"), ("in_ty", "有限宇宙型別與值"),
    ("pval_", "有限宇宙型別與值"), ("flatten_pval", "Wiring 符號等價"),
    ("leaf_", "Wiring 符號等價"), ("leaves_", "Wiring 符號等價"), ("wiring_", "Wiring 符號等價"),
    ("iso_", "同構、等價、ua、coe"), ("equiv_", "同構、等價、ua、coe"),
    ("ua", "同構、等價、ua、coe"), ("upath_", "同構、等價、ua、coe"),
    ("coe_upath", "同構、等價、ua、coe"), ("coe_computes", "同構、等價、ua、coe"),
    ("swap_naturality", "同構、等價、ua、coe"),
    ("pathp_", "PathP、離散路徑與 J"), ("disc_", "PathP、離散路徑與 J"),
    ("refl_path", "PathP、離散路徑與 J"), ("j_", "PathP、離散路徑與 J"),
    ("glue_data", "Glue comp（有限線）"), ("glue_line", "Glue comp（有限線）"),
    ("glue_comp_finite", "Glue comp（有限線）"),
    ("glue_box", "Glue comp（子空間線）"), ("glue_comp_vec", "Glue comp（子空間線）"),
    ("subline_", "Glue comp（子空間線）"), ("lin_equiv", "Glue comp（子空間線）"),
    ("fill_subline", "Glue comp（子空間線）"), ("map_cube", "Glue comp（子空間線）"),
    ("glue_", "有限 Glue"), ("make_glue", "有限 Glue"), ("unglue", "有限 Glue"),
    ("dep_", "依賴型別 NbE（Π/Σ/宇宙）"),
    ("dline_", "依賴 Kan 線（coe/comp）"), ("dcoe", "依賴 Kan 線（coe/comp）"),
    ("dcomp", "依賴 Kan 線（coe/comp）"), ("dfill", "依賴 Kan 線（coe/comp）"),
    ("dbool_not", "依賴 Kan 線（coe/comp）"), ("path_from", "依賴 Kan 線（coe/comp）"),
    ("pval_to_dvalue", "依賴 Kan 線（coe/comp）"), ("dvalue_", "依賴 Kan 線（coe/comp）"),
    ("rat_", "精確符號代數"), ("int_abs", "精確符號代數"), ("int_gcd", "精確符號代數"),
    ("poly_", "精確符號代數"), ("frac_", "精確符號代數"), ("sc_", "精確符號代數"),
    ("sym_", "精確符號代數"), ("upoly_", "精確符號代數"), ("charpoly_sym", "精確符號代數"),
    ("rpoly_", "譜投影與仿射唯一填充"), ("spectral_", "譜投影與仿射唯一填充"),
    ("spec_", "規格登記"),
    ("denv_", "持久環境、惰性與語義快取"), ("ddim_", "持久環境、惰性與語義快取"),
    ("lazy_", "持久環境、惰性與語義快取"), ("force_value", "持久環境、惰性與語義快取"),
    ("memo_", "持久環境、惰性與語義快取"), ("dterm_cache", "持久環境、惰性與語義快取"),
    ("dim_cache", "持久環境、惰性與語義快取"),
    ("dsystem_", "依賴語義系統與 partial 值"), ("partial_", "依賴語義系統與 partial 值"),
    ("tube_system_", "依賴語義系統與 partial 值"), ("glue_partial_", "依賴語義系統與 partial 值"),
    ("glue_store_", "依賴語義系統與 partial 值"),
    ("darg_", "通用歸納族 schema"), ("dtelescope_", "通用歸納族 schema"),
    ("dconstructor_", "通用歸納族 schema"), ("dinductive_", "通用歸納族 schema"),
    ("inductive_", "通用歸納族 schema"), ("schema_", "通用歸納族 schema"),
    ("telescope_", "通用歸納族 schema"),
    ("dhit_", "通用 HIT schema"), ("hit_", "通用 HIT schema"),
    ("run_all_checks", "定理登記與範例"), ("all_checks_pass", "定理登記與範例"),
    ("check_cube_algorithm", "可計算單值性與 n 維立方演算法"),
    ("fin_equiv_search", "可計算單值性與 n 維立方演算法"),
    ("fin_equiv_count", "可計算單值性與 n 維立方演算法"),
    ("fin_map", "可計算單值性與 n 維立方演算法"),
    ("univalence_decides", "可計算單值性與 n 維立方演算法"),
    ("univalence_compute_all", "可計算單值性與 n 維立方演算法"),
    ("univalence_path_count", "可計算單值性與 n 維立方演算法"),
    ("transport_roundtrip", "可計算單值性與 n 維立方演算法"),
    ("ncomp", "可計算單值性與 n 維立方演算法"),
    ("nfill", "可計算單值性與 n 維立方演算法"),
    ("cube_permute", "可計算單值性與 n 維立方演算法"),
    ("default_samples", "可計算單值性與 n 維立方演算法"),
    ("fact", "可計算單值性與 n 維立方演算法"),
    ("print_report", "定理登記與範例"),
]

KIND_ZH = {
    "fn": "函數 / fn", "struct": "結構 / struct", "enum": "列舉 / enum",
    "type": "型別別名 / type", "let": "常量 / let",
    "constructor": "構造子 / constructor", "field": "欄位 / field",
}


def parse_mbti(text):
    decls = []
    top = re.compile(r"^pub (fn|struct|enum|type|let) ([A-Za-z_][A-Za-z0-9_]*(?:::[A-Za-z_][A-Za-z0-9_]*)?)")
    block = None  # (name, kind)
    for raw in text.splitlines():
        line = raw.rstrip()
        m = top.match(line)
        if m:
            kind, sym = m.group(1), m.group(2)
            decls.append((sym, kind))
            if kind in ("struct", "enum") and line.rstrip().endswith("{"):
                block = (sym, kind)
            else:
                block = None
            continue
        if block is not None:
            if line.startswith("}"):
                block = None
                continue
            name, kind = block
            if kind == "struct":
                fm = re.match(r"^\s+(?:mut\s+)?([a-z_][A-Za-z0-9_]*)\s*:", line)
                if fm:
                    decls.append((f"{name}.{fm.group(1)}", "field"))
            else:
                vm = re.match(r"^\s+([A-Z][A-Za-z0-9_]*)", line)
                if vm:
                    decls.append((f"{name}::{vm.group(1)}", "constructor"))
    return decls


def classify(sym, kind):
    if kind in ("field", "constructor"):
        owner = re.split(r"[.:]", sym)[0]
        return TYPE_FAMILY.get(owner)
    if kind in ("struct", "enum", "type"):
        return TYPE_FAMILY.get(sym)
    if "::" in sym:  # derived Eq/Debug methods belong to their type's family
        return TYPE_FAMILY.get(sym.split("::")[0])
    if sym in EXACT:
        return EXACT[sym]
    if sym.startswith("check_"):
        rest = sym[len("check_"):]
        for hint, fam in CHECK_FAMILY_HINTS:
            if rest == hint or rest.startswith(hint + "_") or rest.startswith(hint):
                return fam
        return "定理登記與範例"
    for prefix, fam in PREFIXES:
        if sym == prefix or sym.startswith(prefix):
            return fam
    return None


def render(decls):
    out = []
    by_family = {name: [] for name in FAMILIES}
    for sym, kind in decls:
        fam = classify(sym, kind)
        assert fam in FAMILIES, f"unclassified symbol: {sym} ({kind}) -> {fam}"
        by_family[fam].append((sym, kind))
    total = len(decls)
    families = sum(1 for v in by_family.values() if v)
    out.append(
        f"共 **{total}** 個公共符號（宣告＋構造子＋欄位），分屬 {families} 個規格族。"
        f" / **{total}** public symbols (declarations + constructors + fields) in "
        f"{families} specification families."
    )
    for fam, (canon, cat, dec) in FAMILIES.items():
        items = sorted(by_family[fam])
        if not items:
            continue
        out.append("")
        en = EN_FAMILY_NAMES.get(fam, "")
        out.append(f"### {fam} — {en}" if en else f"### {fam}")
        out.append("")
        out.append(f"- 規範形式 / Canonical form：{canon}")
        out.append(f"- 範疇化 / Categorification：{cat}")
        out.append(f"- 判定 / Decision procedure：{dec}")
        out.append("")
        out.append("| 符號 / Symbol | 類別 / Kind |")
        out.append("|---|---|")
        for sym, kind in items:
            note = ""
            if "oracle" in sym or "extensional" in sym:
                note = "（差分測試 oracle，非判定路徑 / diff-test oracle, not a decision path）"
            out.append(f"| `{sym}` | {KIND_ZH[kind]}{note} |")
    return "\n".join(out) + "\n"


def appendix_of(spec_text):
    m = re.search(r"<!-- APPENDIX:BEGIN -->\n(.*?)\n<!-- APPENDIX:END -->", spec_text, re.S)
    return m.group(1) if m else None


def symbols_in_appendix(app):
    return re.findall(r"^\| `([^`]+)` \|", app, re.M)


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "--check"
    decls = parse_mbti(MBTI.read_text())
    syms = [s for s, _ in decls]
    assert len(syms) == len(set(syms)), "duplicate symbols parsed from mbti"
    rendered = render(decls)
    spec = SPEC.read_text()
    if mode == "--write":
        new = re.sub(
            r"(<!-- APPENDIX:BEGIN -->\n).*?(\n<!-- APPENDIX:END -->)",
            lambda m: m.group(1) + rendered.rstrip("\n") + m.group(2),
            spec, flags=re.S,
        )
        assert new != spec or rendered.strip() in spec
        SPEC.write_text(new)
        spec = new
        print(f"appendix written: {len(syms)} symbols")
    app = appendix_of(spec)
    assert app is not None, "appendix markers not found in SPEC.md"
    listed = symbols_in_appendix(app)
    missing = sorted(set(syms) - set(listed))
    extra = sorted(set(listed) - set(syms))
    dup = sorted({s for s in listed if listed.count(s) > 1})
    assert not missing, f"missing from appendix: {missing[:20]}"
    assert not extra, f"not in interface: {extra[:20]}"
    assert not dup, f"duplicated in appendix: {dup[:20]}"
    if mode == "--check":
        assert app.strip() == rendered.strip(), "appendix is stale: run with --write"
    kinds = {}
    for _, k in decls:
        kinds[k] = kinds.get(k, 0) + 1
    print(f"audit ok: {len(syms)} symbols, by kind {kinds}")


if __name__ == "__main__":
    main()
