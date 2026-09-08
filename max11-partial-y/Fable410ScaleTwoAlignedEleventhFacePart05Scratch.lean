import Fable410ScaleTwoAlignedEleventhFacePart04Scratch

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxHeartbeats 64000000 in
/-- Generic Wronskian quotient for the weight-`18` bracket: over a
characteristic-zero field, `H D' - 18 D H' = 0` forces
`D = C c * H¹⁸`.  Even-type: no squaring, no parity split. -/
theorem eighteenthPowerRelation_of_weightEighteenRow_410 {K : Type*}
    [Field K] [CharZero K] {H D : K[X]} (hH : H ≠ 0)
    (hrow : H * D.derivative - (18 : K[X]) * D * H.derivative = 0) :
    ∃ c : K, D = Polynomial.C c * H ^ 18 := by
  have hC18 : Polynomial.C (18 : K) = (18 : K[X]) :=
    Polynomial.C_eq_natCast 18
  have hW : Polynomial.wronskian D (H ^ 18) = 0 := by
    rw [Polynomial.wronskian, Polynomial.derivative_pow]
    calc
      D * (Polynomial.C (18 : K) * H ^ (18 - 1) * H.derivative) -
          D.derivative * H ^ 18 =
          H ^ 17 *
            (Polynomial.C (18 : K) * D * H.derivative -
              H * D.derivative) := by ring
      _ = 0 := by
        rw [hC18]
        have hfac :
            (18 : K[X]) * D * H.derivative - H * D.derivative = 0 := by
          linear_combination -hrow
        rw [hfac, mul_zero]
  exact eq_C_mul_of_wronskian_eq_zero (pow_ne_zero 18 hH) hW

end Max11DegreeRoutes
