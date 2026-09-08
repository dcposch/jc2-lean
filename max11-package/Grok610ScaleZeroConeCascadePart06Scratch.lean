import Grok610ScaleZeroConeCascadePart05Scratch

open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section DegreeLemmas610

variable {k : Type*} [Field k] [CharZero k]

theorem natDegree_smul_lt610 (c : k) {p : k[X]} {d : ℕ}
    (hp : p.natDegree < d) : (c • p).natDegree < d :=
  (natDegree_smul_le610 c p).trans_lt hp

end DegreeLemmas610

end Max11DegreeRoutes
