import Grok610ScaleZeroConeCascadePart01Scratch
import Grok610ScaleZeroConeCascadePart36Scratch
import Grok610ScaleZeroConeCascadePart53Scratch

open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section HighACone610

variable {k : Type*} [Field k] [CharZero k]

theorem uniqueHighA_impossible_of_l_ne610
    (l alpha beta delta epsilon zeta eta theta j : k)
    (A B C0 D0 E0 : k[X]) (hl : l ≠ 0) (hj : j ≠ 0)
    (hcone : UniqueHighACone610 A B C0 D0 E0)
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
  have hA : A ≠ 0 := by
    intro hA0
    rcases hcone with ⟨hApos, _⟩
    simp [hA0] at hApos
  have hc : (-(10935 / 2239488 * l : k)) ≠ 0 :=
    neg_ne_zero.mpr (mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hl)
  have hlead :
      ((-(10935 / 2239488 * l : k)) • A ^ 7).natDegree =
        7 * A.natDegree := by
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :=
    degreeZeroPrimitiveHighARest610_natDegree_lt l alpha beta delta
      epsilon zeta eta theta A B C0 D0 E0 hcone
  rw [degreeZeroPrimitivePolynomial610_eq_A7_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by
      rwa [hlead])] at hdeg
  rw [hlead] at hdeg
  rcases hcone with ⟨hApos, _⟩
  omega

end HighACone610

end Max11DegreeRoutes
