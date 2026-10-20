///|
// Semantic data types of a vector system (partial elements over the face
// lattice).
//
// Extracted from system.mbt so that the symbolic layer (system_symbolic.mbt)
// can name VecSystem without depending on the whole quotient/pruning API, and
// system.mbt can call the symbolic comparison without a cycle.

///|
pub struct VecBranch {
  face : Face
  value : CVec
}

///|
pub struct VecSystem {
  branches : Array[VecBranch]
}
