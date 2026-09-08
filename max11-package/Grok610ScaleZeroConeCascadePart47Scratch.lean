import Grok610ScaleZeroConeCascadePart25Scratch

open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section PrimitivePolynomial610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 4000000 in
theorem algebraMap_degreeZeroEtaGroupPolynomial610
    (A B C0 D0 : k[X]) :
    algebraMap k[X] (RatFunc k)
        (degreeZeroEtaGroupPolynomial610 A B C0 D0) =
      degreeZeroEtaGroup610
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0) := by
  simp only [degreeZeroEtaGroupPolynomial610, degreeZeroEtaGroup610,
    map_add, map_sub, map_neg, map_mul, map_pow, Polynomial.smul_eq_C_mul,
    RatFunc.algebraMap_C, map_div₀, map_ofNat, map_one]
  ring

end PrimitivePolynomial610

end Max11DegreeRoutes
