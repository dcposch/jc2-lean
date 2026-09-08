import Fable410ScaleTwoAlignedNinthFacePart05Scratch

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxHeartbeats 64000000 in
/-- Weight-fifteen polynomial first integral of the aligned `(4,10)`
tenth defect: `M₁₆ = κ₉ H¹⁵` — even-type and chamber-free, the fifth
rung of the even ladder `H⁴, H⁶, H⁹, H¹², H¹⁵`, one level below the
odd twenty-seventh-power shape of the degree-`4` row. -/
theorem alignedTenthDefectPowerRelation_410 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hH : H ≠ 0)
    (hp4 : p.coeff 4 = H ^ 2) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect410 H (p.coeff 2) (p.coeff 3) (q.coeff 8) =
      Polynomial.C κ * H ^ 4) :
    ∃ κ₉ : K,
      alignedTenthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) (q.coeff 0) (q.coeff 1) (q.coeff 2) (q.coeff 3)
          (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ =
        Polynomial.C κ₉ * H ^ 15 :=
  fifteenthPowerRelation_of_weightFifteenRow_410 hH
    (alignedTenthDefectRow_eq_zero_410 hp hq hjac hp4 hq10 haligned hM)

/-! ## Square chamber -/

end Max11DegreeRoutes
