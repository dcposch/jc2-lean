import Fable410ScaleTwoAlignedNinthFacePart04Scratch

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxHeartbeats 64000000 in
/-- Generic Wronskian quotient for the weight-`15` bracket: over a
characteristic-zero field, `H D' - 15 D H' = 0` forces
`D = C c * H¹⁵`.  Even-type: no squaring, no parity split — distinct
from the odd-type half-integral quotient
`fifteenthPowerRelation_of_weightFifteenHalfRow_410`. -/
theorem fifteenthPowerRelation_of_weightFifteenRow_410 {K : Type*}
    [Field K] [CharZero K] {H D : K[X]} (hH : H ≠ 0)
    (hrow : H * D.derivative - (15 : K[X]) * D * H.derivative = 0) :
    ∃ c : K, D = Polynomial.C c * H ^ 15 := by
  have hC15 : Polynomial.C (15 : K) = (15 : K[X]) :=
    Polynomial.C_eq_natCast 15
  have hW : Polynomial.wronskian D (H ^ 15) = 0 := by
    rw [Polynomial.wronskian, Polynomial.derivative_pow]
    calc
      D * (Polynomial.C (15 : K) * H ^ (15 - 1) * H.derivative) -
          D.derivative * H ^ 15 =
          H ^ 14 *
            (Polynomial.C (15 : K) * D * H.derivative -
              H * D.derivative) := by ring
      _ = 0 := by
        rw [hC15]
        have hfac :
            (15 : K[X]) * D * H.derivative - H * D.derivative = 0 := by
          linear_combination -hrow
        rw [hfac, mul_zero]
  exact eq_C_mul_of_wronskian_eq_zero (pow_ne_zero 15 hH) hW

end Max11DegreeRoutes
