# username/cubical-hermitian

Hermitian idempotent projectors and orthogonal eigenspace decomposition;
cubical interval, faces and systems modulo quotient with pruning; Kan comp
by retraction; NbE in three layers (beta-pi, typed eta-long, and dependent
Pi/Sigma with a cumulative universe hierarchy); persistent shared
environments, call-by-need semantic thunks and memoized dimension lines /
type families; a cubical AST with PathP, data types (Bool/Nat/List),
Circle/Torus HITs and coe/comp/hcomp/hfill term constructors whose Kan
operations reduce by type (Pi, Sigma, PathP, Glue, data, HITs and
universes); DSystem composition systems with checked compatibility for raw systems,
first-match normal forms and multi-branch Glue partial values; first-class
AST equivalences, ua and GlueEquiv; checked substitution-respecting type
lines and a schema registry with elaboration caches; generic
strictly-positive inductive-family and arbitrary finite-dimensional HIT
schema generators (nested container functors, mutual families, Tarski induction-recursion,
quotient cells and universe schemes); HOAS on normal forms; symbolic
decision (interned DAG ROBDDs with budgets/DPLL, wirings); exact rational
and algebraic-extension algebra with generalized eigenspaces and Jordan
decompositions; certified exact shadows of the numeric projector/cube
layer; general Glue comp; spheres by iterated suspension (including S3);
certified Hermitian Jacobi iteration by symbolic interval inclusion;
a Miller-pattern higher-order-unification bidirectional elaborator;
parameterized modules with import/open/namespace semantics; and an
audited per-symbol canonical-form/categorification specification.

Run: `moon test` (34 tests), `moon run cmd/main` (expected: 40/40 checks),
`python3 tools/audit_spec.py --check` (2277 interface symbols, 51 spec entries).
Details (in Chinese): GUIDE.md and SPEC.md.
