import Grok610ScaleZeroConeCascadePart01Scratch
import Grok610ScaleZeroConeCascadePart07Scratch
import Grok610ScaleZeroConeCascadePart09Scratch
import Grok610ScaleZeroConeCascadePart28Scratch

open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section SourcePrimitiveDegree610

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 64000000 in
/-- A constant free core makes the polynomial primitive constant, hence
cannot support derivative `C (j / t) ≠ 0`. -/
theorem degreeZeroPrimitivePolynomial610_false_of_constant_core
    (l alpha beta delta epsilon zeta eta theta j : k)
    (A B C0 D0 E0 : k[X]) (hj : j ≠ 0)
    (hA : A.natDegree = 0) (hB : B.natDegree = 0)
    (hC : C0.natDegree = 0) (hD : D0.natDegree = 0)
    (hE : E0.natDegree = 0)
    (hder :
      derivative
          (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon
            zeta eta theta A B C0 D0 E0) =
        C j) :
    False := by
  have hdeg :
      (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon zeta
          eta theta A B C0 D0 E0).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C610 _ j hj hder
  have hle :
      (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon zeta
          eta theta A B C0 D0 E0).natDegree ≤
        0 := by
    rw [eq_C_of_natDegree_eq_zero hA, eq_C_of_natDegree_eq_zero hB,
      eq_C_of_natDegree_eq_zero hC, eq_C_of_natDegree_eq_zero hD,
      eq_C_of_natDegree_eq_zero hE]
    simp only [degreeZeroPrimitivePolynomial610, degreeZeroBaseGroupPolynomial610,
      degreeZeroAlphaGroupPolynomial610, degreeZeroBetaGroupPolynomial610,
      degreeZeroDeltaGroupPolynomial610, degreeZeroEpsilonGroupPolynomial610,
      degreeZeroZetaGroupPolynomial610, degreeZeroEtaGroupPolynomial610,
      degreeZeroThetaGroupPolynomial610, ← Polynomial.C_pow, ← Polynomial.C_mul,
      smul_C, ← Polynomial.C_add, ← Polynomial.C_sub, natDegree_C, le_refl]
  omega

end SourcePrimitiveDegree610

end Max11DegreeRoutes
