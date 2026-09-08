import Fable610ScaleTwoAlignedTenthFacePart04Scratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

/-- Weight-`25` polynomial first integral of the aligned `(6,10)`
tenth defect: `Ω = κ₉ H²⁵`.  The even exponent makes the integral
chamber-free — no square root of `H` is required and `κ₉` is preserved
in both chambers. -/
theorem alignedTenthDefectPowerRelation_610 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hH : H ≠ 0)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect610 H (p.coeff 4) (p.coeff 5) (q.coeff 8) =
      Polynomial.C κ * H ^ 5) :
    ∃ κ₉ : K,
      alignedTenthDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
        (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 0) (q.coeff 1)
        (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6)
        (q.coeff 7) κ = Polynomial.C κ₉ * H ^ 25 := by
  let O : K[X] :=
    alignedTenthDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2) (p.coeff
    3) (p.coeff 4) (p.coeff 5) (q.coeff 0) (q.coeff 1) (q.coeff 2)
    (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ
  have hrow : H * O.derivative - (25 : K[X]) * O * H.derivative = 0 := by
    simpa only [O] using
      alignedTenthDefectRow_eq_zero_610 hp hq hjac hp6 hq10 haligned hM
  have hC25 : Polynomial.C (25 : K) = (25 : K[X]) := C_ofNat_poly
  have hW : Polynomial.wronskian O (H ^ 25) = 0 := by
    rw [Polynomial.wronskian, Polynomial.derivative_pow]
    calc
      O * (Polynomial.C (25 : K) * H ^ (25 - 1) * H.derivative) -
          O.derivative * H ^ 25 =
          H ^ 24 *
            (Polynomial.C (25 : K) * O * H.derivative -
              H * O.derivative) := by
        ring
      _ = 0 := by
        rw [hC25]
        have hfac :
            (25 : K[X]) * O * H.derivative - H * O.derivative = 0 := by
          linear_combination -hrow
        rw [hfac, mul_zero]
  exact eq_C_mul_of_wronskian_eq_zero (pow_ne_zero 25 hH) hW

end Max11DegreeRoutes
