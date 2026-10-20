///|
// Interned DAG binary decision diagrams.
//
// The legacy `Bdd` type is a tree: equal subdiagrams can occur many
// times, and structural recursion may revisit them exponentially
// often.  `BddManager` is the scalable representation.  Every node
// `(rank, low, high)` is interned in a hash table, Boolean `apply`
// operations are memoized, and two faces are equal exactly when
// their root node identifiers in one manager are equal.  A manager
// may carry a hard node budget; exceeding it sets an explicit flag
// instead of silently consuming exponential memory.  Variable order
// is part of a manager, and statistics expose node and cache counts.
//
// No representation can make every Boolean function small: over `n`
// ordered variables some functions require exponentially many BDD
// nodes.  The functions here therefore also provide a tight
// worst-case node bound and budget-aware decision procedures which
// return an explicit budget-exceeded result; a separate DPLL
// fallback decides satisfiability by branching on face variables
// when a caller prefers search to canonical-form construction.

///|
pub struct BddDagNode {
  rank : Int32 // position in the manager's variable order
  lo : Int32
  hi : Int32
}

///|
pub struct BddApplyEntry {
  op : Int32 // 0=and, 1=or, 2=xor, 3=not (b ignored)
  a : Int32
  b : Int32
  result : Int32
}

///|
pub struct BddManager {
  n : Int32
  order : Array[Int32] // variable ids by rank
  position : Array[Int32] // rank by variable id
  nodes : Array[BddDagNode] // 0=false, 1=true, then interned nodes
  buckets : Array[Array[Int32]]
  apply_buckets : Array[Array[BddApplyEntry]]
  max_nodes : Int32 // 0 means unbounded
  mut exceeded : Bool
  mut apply_hits : Int32
  mut apply_misses : Int32
  mut mk_calls : Int32
}

///|
fn bdd_buckets_new(size : Int32) -> Array[Array[Int32]] {
  let out : Array[Array[Int32]] = []
  for _i in 0..<size {
    out.push([])
  }
  out
}

///|
fn bdd_apply_buckets_new(size : Int32) -> Array[Array[BddApplyEntry]] {
  let out : Array[Array[BddApplyEntry]] = []
  for _i in 0..<size {
    out.push([])
  }
  out
}

///|
fn bdd_node_hash(rank : Int32, lo : Int32, hi : Int32, size : Int32) -> Int32 {
  let mut h = 0
  h = (h * 33 + rank + 1) % size
  h = (h * 33 + lo + 1) % size
  h = (h * 33 + hi + 1) % size
  h
}

///|
fn bdd_apply_hash(op : Int32, a : Int32, b : Int32, size : Int32) -> Int32 {
  let mut h = 0
  h = (h * 33 + op + 1) % size
  h = (h * 33 + a + 1) % size
  h = (h * 33 + b + 1) % size
  h
}

///|
fn bdd_manager_rehash(m : BddManager) -> Unit {
  let new_size = m.buckets.length() * 2
  let fresh = bdd_buckets_new(new_size)
  for id in 2..<m.nodes.length() {
    let node = m.nodes[id]
    fresh[bdd_node_hash(node.rank, node.lo, node.hi, new_size)].push(id)
  }
  // Replace bucket contents in place (the array itself is shared).
  while m.buckets.length() > 0 {
    ignore(m.buckets.pop())
  }
  for i in 0..<fresh.length() {
    m.buckets.push(fresh[i])
  }
}

///|
pub fn bdd_manager_new(n : Int32, max_nodes~ : Int32 = 0) -> BddManager {
  let order : Array[Int32] = []
  let position : Array[Int32] = []
  for i in 0..<n {
    order.push(i)
    position.push(i)
  }
  BddManager::{
    n,
    order,
    position,
    nodes: [
      BddDagNode::{ rank: n, lo: 0, hi: 0, },
      BddDagNode::{ rank: n, lo: 1, hi: 1, },
    ],
    buckets: bdd_buckets_new(1024),
    apply_buckets: bdd_apply_buckets_new(1024),
    max_nodes,
    exceeded: false,
    apply_hits: 0,
    apply_misses: 0,
    mk_calls: 0,
  }
}

///|
/// A manager with a prescribed variable order.  Non-permutation
/// inputs are completed with the missing variables in index order.
pub fn bdd_manager_with_order(
  order_in : Array[Int32],
  n : Int32,
  max_nodes~ : Int32 = 0,
) -> BddManager {
  let order : Array[Int32] = []
  let seen : Array[Bool] = []
  for _i in 0..<n {
    seen.push(false)
  }
  for i in 0..<order_in.length() {
    let v = order_in[i]
    if v >= 0 && v < n && !seen[v] {
      seen[v] = true
      order.push(v)
    }
  }
  for v in 0..<n {
    if !seen[v] {
      seen[v] = true
      order.push(v)
    }
  }
  let position : Array[Int32] = []
  for _i in 0..<n {
    position.push(0)
  }
  for r in 0..<order.length() {
    position[order[r]] = r
  }
  BddManager::{
    n,
    order,
    position,
    nodes: [
      BddDagNode::{ rank: n, lo: 0, hi: 0, },
      BddDagNode::{ rank: n, lo: 1, hi: 1, },
    ],
    buckets: bdd_buckets_new(1024),
    apply_buckets: bdd_apply_buckets_new(1024),
    max_nodes,
    exceeded: false,
    apply_hits: 0,
    apply_misses: 0,
    mk_calls: 0,
  }
}

///|
fn bdd_dag_mk(m : BddManager, rank : Int32, lo : Int32, hi : Int32) -> Int32 {
  if lo == hi {
    return lo
  }
  m.mk_calls = m.mk_calls + 1
  let bucket = bdd_node_hash(rank, lo, hi, m.buckets.length())
  for i in 0..<m.buckets[bucket].length() {
    let id = m.buckets[bucket][i]
    let node = m.nodes[id]
    if node.rank == rank && node.lo == lo && node.hi == hi {
      return id
    }
  }
  if m.max_nodes > 0 && m.nodes.length() - 2 >= m.max_nodes {
    m.exceeded = true
    return 0
  }
  let id = m.nodes.length()
  m.nodes.push(BddDagNode::{ rank, lo, hi, })
  m.buckets[bucket].push(id)
  if m.nodes.length() > m.buckets.length() * 4 {
    bdd_manager_rehash(m)
  }
  id
}

///|
fn bdd_dag_top(m : BddManager, id : Int32) -> Int32 {
  m.nodes[id].rank
}

///|
fn bdd_cofactor(m : BddManager, id : Int32, rank : Int32, high : Bool) -> Int32 {
  if id < 2 || bdd_dag_top(m, id) != rank {
    id
  } else if high {
    m.nodes[id].hi
  } else {
    m.nodes[id].lo
  }
}

///|
fn bdd_apply_lookup(m : BddManager, op : Int32, a : Int32, b : Int32) -> Int32? {
  let bucket = bdd_apply_hash(op, a, b, m.apply_buckets.length())
  for i in 0..<m.apply_buckets[bucket].length() {
    let e = m.apply_buckets[bucket][i]
    if e.op == op && e.a == a && e.b == b {
      return Some(e.result)
    }
  }
  None
}

///|
fn bdd_apply_store(
  m : BddManager,
  op : Int32,
  a : Int32,
  b : Int32,
  result : Int32,
) -> Unit {
  let bucket = bdd_apply_hash(op, a, b, m.apply_buckets.length())
  m.apply_buckets[bucket].push(BddApplyEntry::{ op, a, b, result, })
}

///|
fn bdd_dag_not_rec(m : BddManager, a : Int32) -> Int32 {
  if m.exceeded {
    return 0
  }
  if a == 0 {
    return 1
  }
  if a == 1 {
    return 0
  }
  match bdd_apply_lookup(m, 3, a, 0) {
    Some(r) => {
      m.apply_hits = m.apply_hits + 1
      r
    }
    None => {
      m.apply_misses = m.apply_misses + 1
      let node = m.nodes[a]
      let result = bdd_dag_mk(
        m,
        node.rank,
        bdd_dag_not_rec(m, node.lo),
        bdd_dag_not_rec(m, node.hi),
      )
      bdd_apply_store(m, 3, a, 0, result)
      result
    }
  }
}

///|
fn bdd_dag_apply(m : BddManager, op : Int32, a0 : Int32, b0 : Int32) -> Int32 {
  if m.exceeded {
    return 0
  }
  // Terminal and identity rules.
  if op == 0 { // and
    if a0 == 0 || b0 == 0 {
      return 0
    }
    if a0 == 1 {
      return b0
    }
    if b0 == 1 {
      return a0
    }
    if a0 == b0 {
      return a0
    }
  } else if op == 1 { // or
    if a0 == 1 || b0 == 1 {
      return 1
    }
    if a0 == 0 {
      return b0
    }
    if b0 == 0 {
      return a0
    }
    if a0 == b0 {
      return a0
    }
  } else { // xor
    if a0 == 0 {
      return b0
    }
    if b0 == 0 {
      return a0
    }
    if a0 == b0 {
      return 0
    }
    if a0 == 1 {
      return bdd_dag_not_rec(m, b0)
    }
    if b0 == 1 {
      return bdd_dag_not_rec(m, a0)
    }
  }
  let (a, b) = if a0 <= b0 { (a0, b0) } else { (b0, a0) }
  match bdd_apply_lookup(m, op, a, b) {
    Some(r) => {
      m.apply_hits = m.apply_hits + 1
      r
    }
    None => {
      m.apply_misses = m.apply_misses + 1
      let ra = bdd_dag_top(m, a)
      let rb = bdd_dag_top(m, b)
      let rank = if ra < rb { ra } else { rb }
      let lo = bdd_dag_apply(
        m,
        op,
        bdd_cofactor(m, a, rank, false),
        bdd_cofactor(m, b, rank, false),
      )
      let hi = bdd_dag_apply(
        m,
        op,
        bdd_cofactor(m, a, rank, true),
        bdd_cofactor(m, b, rank, true),
      )
      let result = bdd_dag_mk(m, rank, lo, hi)
      bdd_apply_store(m, op, a, b, result)
      result
    }
  }
}

///|
pub fn bdd_dag_var(m : BddManager, variable : Int32) -> Int32 {
  if variable < 0 || variable >= m.n {
    0
  } else {
    bdd_dag_mk(m, m.position[variable], 0, 1)
  }
}

///|
pub fn bdd_dag_not(m : BddManager, a : Int32) -> Int32 {
  bdd_dag_not_rec(m, a)
}

///|
pub fn bdd_dag_and(m : BddManager, a : Int32, b : Int32) -> Int32 {
  bdd_dag_apply(m, 0, a, b)
}

///|
pub fn bdd_dag_or(m : BddManager, a : Int32, b : Int32) -> Int32 {
  bdd_dag_apply(m, 1, a, b)
}

///|
fn bdd_dag_of_dim(m : BddManager, r : Dim) -> Int32 {
  match dim_simplify(r) {
    DZero => 0
    DOne => 1
    DVar(i) => bdd_dag_var(m, i)
    DNeg(a) => bdd_dag_not(m, bdd_dag_of_dim(m, a))
    DAnd(a, b) => bdd_dag_and(m, bdd_dag_of_dim(m, a), bdd_dag_of_dim(m, b))
    DOr(a, b) => bdd_dag_or(m, bdd_dag_of_dim(m, a), bdd_dag_of_dim(m, b))
  }
}

///|
/// Build a face in an existing manager.  Variables outside the
/// manager's range denote false, matching `face_bound`.
pub fn bdd_dag_build_face(m : BddManager, f : Face) -> Int32 {
  match f {
    FTop => 1
    FBot => 0
    FEq0(r) => bdd_dag_not(m, bdd_dag_of_dim(m, r))
    FEq1(r) => bdd_dag_of_dim(m, r)
    FAnd(a, b) =>
      bdd_dag_and(m, bdd_dag_build_face(m, a), bdd_dag_build_face(m, b))
    FOr(a, b) =>
      bdd_dag_or(m, bdd_dag_build_face(m, a), bdd_dag_build_face(m, b))
  }
}

///|
pub struct BddDagFace {
  manager : BddManager
  root : Int32
  ok : Bool
}

///|
pub fn bdd_dag_of_face(
  f : Face,
  n : Int32,
  max_nodes~ : Int32 = 0,
) -> BddDagFace {
  let manager = bdd_manager_new(n, max_nodes~)
  let root = bdd_dag_build_face(manager, f)
  BddDagFace::{ manager, root, ok: !manager.exceeded, }
}

///|
pub fn bdd_manager_node_count(m : BddManager) -> Int32 {
  m.nodes.length() - 2
}

///|
/// A safe worst-case bound on ROBDD node count over `n` variables,
/// saturated at the largest `Int32`.
pub fn bdd_worst_case_nodes(n : Int32) -> Int32 {
  let max = 2147483647
  if n < 0 {
    return 0
  }
  if n >= 31 {
    return max
  }
  let mut pow = 1
  for _i in 0..<(n + 1) {
    pow = pow * 2
  }
  pow - 1
}

///|
fn bdd_tree_of_id(m : BddManager, id : Int32, memo : Array[Bdd?]) -> Bdd {
  if id == 0 {
    return BddZero
  }
  if id == 1 {
    return BddOne
  }
  match memo[id] {
    Some(b) => b
    None => {
      let node = m.nodes[id]
      let out = BddNode(
        m.order[node.rank],
        bdd_tree_of_id(m, node.lo, memo),
        bdd_tree_of_id(m, node.hi, memo),
      )
      memo[id] = Some(out)
      out
    }
  }
}

///|
/// Expand a DAG root to the legacy tree representation.  Shared
/// subdiagrams are built once and shared as values.
pub fn bdd_tree_of_dag(m : BddManager, root : Int32) -> Bdd {
  let memo : Array[Bdd?] = []
  for _i in 0..<m.nodes.length() {
    memo.push(None)
  }
  bdd_tree_of_id(m, root, memo)
}

///|
fn bdd_dag_witness_into(m : BddManager, id : Int32, env : Array[Bool]) -> Bool {
  if id == 0 {
    false
  } else if id == 1 {
    true
  } else {
    let node = m.nodes[id]
    if bdd_dag_witness_into(m, node.lo, env) {
      true
    } else {
      env[m.order[node.rank]] = true
      if bdd_dag_witness_into(m, node.hi, env) {
        true
      } else {
        env[m.order[node.rank]] = false
        false
      }
    }
  }
}

///|
pub fn bdd_dag_witness(m : BddManager, root : Int32) -> Array[Bool]? {
  let env : Array[Bool] = []
  for _i in 0..<m.n {
    env.push(false)
  }
  if bdd_dag_witness_into(m, root, env) {
    Some(env)
  } else {
    None
  }
}

///|
pub enum FaceDecision {
  FaceDecided(Bool)
  FaceBudgetExceeded
} derive(Debug, Eq)

///|
pub extend FaceDecision with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend FaceDecision with Eq::{not_equal, equal}

///|
/// Equality decided by root identity in one shared DAG manager.
pub fn bdd_dag_face_eq(f : Face, g : Face, n : Int32) -> Bool {
  let m = bdd_manager_new(n)
  bdd_dag_build_face(m, f) == bdd_dag_build_face(m, g)
}

///|
pub fn bdd_dag_face_le(f : Face, g : Face, n : Int32) -> Bool {
  let m = bdd_manager_new(n)
  let a = bdd_dag_build_face(m, f)
  let b = bdd_dag_build_face(m, g)
  bdd_dag_and(m, a, bdd_dag_not(m, b)) == 0
}

///|
pub fn bdd_dag_sat_face(f : Face, n : Int32) -> Bool {
  let built = bdd_dag_of_face(f, n)
  built.root != 0
}

///|
/// Budget-aware equality: if canonical construction would exceed
/// `max_nodes`, the result says so explicitly rather than guessing.
pub fn face_eq_within_budget(
  f : Face,
  g : Face,
  n : Int32,
  max_nodes : Int32,
) -> FaceDecision {
  let m = bdd_manager_new(n, max_nodes~)
  let a = bdd_dag_build_face(m, f)
  if m.exceeded {
    return FaceBudgetExceeded
  }
  let b = bdd_dag_build_face(m, g)
  if m.exceeded {
    FaceBudgetExceeded
  } else {
    FaceDecided(a == b)
  }
}

///|
pub fn face_not(f : Face) -> Face {
  match f {
    FTop => FBot
    FBot => FTop
    FEq0(r) => FEq1(r)
    FEq1(r) => FEq0(r)
    FAnd(a, b) => face_simplify(FOr(face_not(a), face_not(b)))
    FOr(a, b) => face_simplify(FAnd(face_not(a), face_not(b)))
  }
}

///|
fn face_dpll(
  f : Face,
  vars : Array[Int32],
  idx : Int32,
  env : Array[Bool],
  steps : Array[Int32],
  max_steps : Int32,
) -> Int32 {
  // Return codes: 1 sat (env filled), 0 unsat, -1 budget exceeded.
  steps[0] = steps[0] + 1
  if max_steps > 0 && steps[0] > max_steps {
    return -1
  }
  let simplified = face_simplify(f)
  match simplified {
    FTop => return 1
    FBot => return 0
    _ => ()
  }
  let remaining = face_vars(simplified)
  if remaining.length() == 0 {
    return if face_holds(simplified, env) { 1 } else { 0 }
  }
  if idx >= vars.length() {
    return if face_holds(simplified, env) { 1 } else { 0 }
  }
  let v = remaining[0]
  env[v] = false
  let low = face_dpll(
    face_subst(simplified, v, false),
    vars,
    idx + 1,
    env,
    steps,
    max_steps,
  )
  if low != 0 {
    return low
  }
  env[v] = true
  let high = face_dpll(
    face_subst(simplified, v, true),
    vars,
    idx + 1,
    env,
    steps,
    max_steps,
  )
  if high != 1 {
    env[v] = false
  }
  high
}

///|
pub enum FaceSatDecision {
  FaceSat(Array[Bool])
  FaceUnsat
  FaceSearchBudgetExceeded
} derive(Debug, Eq)

///|
pub extend FaceSatDecision with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend FaceSatDecision with Eq::{not_equal, equal}

///|
/// Satisfiability by DPLL search on the face itself, with an explicit
/// step budget.  This trades canonical-form size for search and can
/// decide instances whose DAG exceeds a chosen node budget.
pub fn face_sat_dpll(
  f : Face,
  n : Int32,
  max_steps~ : Int32 = 100000,
) -> FaceSatDecision {
  let env : Array[Bool] = []
  for _i in 0..<n {
    env.push(false)
  }
  let bounded = face_bound(f, n)
  let result = face_dpll(bounded, face_vars(bounded), 0, env, [0], max_steps)
  if result == 1 {
    FaceSat(env)
  } else if result == 0 {
    FaceUnsat
  } else {
    FaceSearchBudgetExceeded
  }
}

///|
/// Equality through DPLL on the symmetric difference, used when a
/// caller does not want to build BDDs at all.
pub fn face_eq_dpll(
  f : Face,
  g : Face,
  n : Int32,
  max_steps~ : Int32 = 100000,
) -> FaceDecision {
  let difference = FOr(FAnd(f, face_not(g)), FAnd(g, face_not(f)))
  match face_sat_dpll(difference, n, max_steps~) {
    FaceSat(_) => FaceDecided(false)
    FaceUnsat => FaceDecided(true)
    FaceSearchBudgetExceeded => FaceBudgetExceeded
  }
}

// ---------------------------------------------------------------------------
// Variable-order candidates
// ---------------------------------------------------------------------------

///|
fn dim_var_counts_into(
  r : Dim,
  counts : Array[Int32],
  first : Array[Int32],
) -> Unit {
  match r {
    DZero | DOne => ()
    DVar(i) =>
      if i >= 0 && i < counts.length() {
        counts[i] = counts[i] + 1
        if !contains_int(first, i) {
          first.push(i)
        }
      }
    DNeg(a) => dim_var_counts_into(a, counts, first)
    DAnd(a, b) => {
      dim_var_counts_into(a, counts, first)
      dim_var_counts_into(b, counts, first)
    }
    DOr(a, b) => {
      dim_var_counts_into(a, counts, first)
      dim_var_counts_into(b, counts, first)
    }
  }
}

///|
fn face_var_counts_into(
  f : Face,
  counts : Array[Int32],
  first : Array[Int32],
) -> Unit {
  match f {
    FTop | FBot => ()
    FEq0(r) | FEq1(r) => dim_var_counts_into(r, counts, first)
    FAnd(a, b) => {
      face_var_counts_into(a, counts, first)
      face_var_counts_into(b, counts, first)
    }
    FOr(a, b) => {
      face_var_counts_into(a, counts, first)
      face_var_counts_into(b, counts, first)
    }
  }
}

///|
/// Variable orderings worth trying: index order, first-occurrence
/// order in the syntax, decreasing occurrence frequency, and reverse
/// index order.  Missing variables are appended in index order.
pub fn bdd_var_order_candidates(f : Face, n : Int32) -> Array[Array[Int32]] {
  let counts : Array[Int32] = []
  for _i in 0..<n {
    counts.push(0)
  }
  let first : Array[Int32] = []
  face_var_counts_into(f, counts, first)
  let identity : Array[Int32] = []
  let reverse : Array[Int32] = []
  for i in 0..<n {
    identity.push(i)
    reverse.push(n - 1 - i)
  }
  let frequency : Array[Int32] = []
  for i in 0..<n {
    frequency.push(i)
  }
  for _pass in 0..<frequency.length() {
    for j in 0..<(frequency.length() - 1) {
      if counts[frequency[j + 1]] > counts[frequency[j]] {
        let tmp = frequency[j]
        frequency[j] = frequency[j + 1]
        frequency[j + 1] = tmp
      }
    }
  }
  [identity, first, frequency, reverse]
}

///|
pub struct BddBestBuild {
  built : BddDagFace
  order : Array[Int32]
}

///|
/// Build using the smallest DAG among the candidate orders.
pub fn bdd_dag_of_face_best(
  f : Face,
  n : Int32,
  max_nodes~ : Int32 = 0,
) -> BddBestBuild {
  let candidates = bdd_var_order_candidates(f, n)
  let mut best_order = candidates[0]
  let first_manager = bdd_manager_with_order(best_order, n, max_nodes~)
  let first_root = bdd_dag_build_face(first_manager, f)
  let mut best = BddDagFace::{
    manager: first_manager,
    root: first_root,
    ok: !first_manager.exceeded,
  }
  for c in 1..<candidates.length() {
    let manager = bdd_manager_with_order(candidates[c], n, max_nodes~)
    let root = bdd_dag_build_face(manager, f)
    let candidate = BddDagFace::{ manager, root, ok: !manager.exceeded, }
    if candidate.ok &&
      (
        !best.ok ||
        bdd_dag_reachable_count(manager, root) <
        bdd_dag_reachable_count(best.manager, best.root)
      ) {
      best = candidate
      best_order = candidates[c]
    }
  }
  BddBestBuild::{ built: best, order: best_order, }
}

///|
fn bdd_mark_reachable(m : BddManager, id : Int32, seen : Array[Bool]) -> Unit {
  if id < 2 || seen[id] {
    return
  }
  seen[id] = true
  bdd_mark_reachable(m, m.nodes[id].lo, seen)
  bdd_mark_reachable(m, m.nodes[id].hi, seen)
}

///|
/// The number of nonterminal DAG nodes reachable from a root.  This
/// is the size of the represented ROBDD, as opposed to
/// `bdd_manager_node_count`, which also counts interned intermediate
/// nodes created during apply operations.
pub fn bdd_dag_reachable_count(m : BddManager, root : Int32) -> Int32 {
  let seen : Array[Bool] = []
  for _i in 0..<m.nodes.length() {
    seen.push(false)
  }
  bdd_mark_reachable(m, root, seen)
  let mut count = 0
  for i in 0..<seen.length() {
    if seen[i] {
      count = count + 1
    }
  }
  count
}
