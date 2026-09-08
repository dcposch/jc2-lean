import Fable410ScaleTwoAlignedEighthFacePart04Scratch

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxHeartbeats 64000000 in
/-- Generic Wronskian quotient for the weight-`27/2` bracket: over a
characteristic-zero field, `2 H D' - 27 D H' = 0` forces
`D² = C c * H²⁷`. -/
theorem twentySeventhPowerRelation_of_weightTwentySevenHalfRow_410
    {K : Type*} [Field K] [CharZero K] {H D : K[X]} (hH : H ≠ 0)
    (hrow : (2 : K[X]) * H * D.derivative -
      (27 : K[X]) * D * H.derivative = 0) :
    ∃ c : K, D ^ 2 = Polynomial.C c * H ^ 27 := by
  have hrowC :
      Polynomial.C (2 : K) * H * D.derivative -
          Polynomial.C (27 : K) * D * H.derivative = 0 := by
    have hC2 : Polynomial.C (2 : K) = (2 : K[X]) :=
      Polynomial.C_eq_natCast 2
    have hC27 : Polynomial.C (27 : K) = (27 : K[X]) :=
      Polynomial.C_eq_natCast 27
    rw [hC2, hC27]
    exact hrow
  have hW : Polynomial.wronskian (D ^ 2) (H ^ 27) = 0 := by
    rw [Polynomial.wronskian, Polynomial.derivative_pow,
      Polynomial.derivative_pow]
    calc
      D ^ 2 * (Polynomial.C (27 : K) * H ^ (27 - 1) * H.derivative) -
          (Polynomial.C (2 : K) * D ^ (2 - 1) * D.derivative) * H ^ 27 =
          D * H ^ 26 *
            (Polynomial.C (27 : K) * D * H.derivative -
              Polynomial.C (2 : K) * H * D.derivative) := by ring
      _ = 0 := by
        rw [sub_eq_zero.mpr (sub_eq_zero.mp hrowC).symm, mul_zero]
  exact eq_C_mul_of_wronskian_eq_zero (pow_ne_zero 27 hH) hW

end Max11DegreeRoutes
