import Grok610ScaleZeroValuationEndgameScratch
import LowScale68ScaleZero

open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section DegreeLemmas610

variable {k : Type*} [Field k] [CharZero k]

theorem natDegree_add_lt610 {p q : k[X]} {d : ℕ}
    (hp : p.natDegree < d) (hq : q.natDegree < d) :
    (p + q).natDegree < d :=
  (natDegree_add_le p q).trans_lt (max_lt hp hq)

end DegreeLemmas610

end Max11DegreeRoutes
