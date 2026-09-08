import Fable610ScaleTwoAlignedNinthFacePart04Scratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

/-- Squared weight-`45/2` polynomial first integral of the aligned
`(6,10)` ninth defect: `L² = κ₈ H⁴⁵`.  The odd exponent forces a
square/nonsquare chamber split exactly as for `D`, `F`, and `I`. -/
theorem alignedNinthDefectPowerRelation_610 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hH : H ≠ 0)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect610 H (p.coeff 4) (p.coeff 5) (q.coeff 8) =
      Polynomial.C κ * H ^ 5) :
    ∃ κ₈ : K,
      alignedNinthDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2) (p.coeff
        3) (p.coeff 4) (p.coeff 5) (q.coeff 1) (q.coeff 2) (q.coeff 3)
        (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ ^ 2 = Polynomial.C
        κ₈ * H ^ 45 := by
  let L : K[X] :=
    alignedNinthDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2) (p.coeff 3)
      (p.coeff 4) (p.coeff 5) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff
      4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ
  have hrow :
      (2 : K[X]) * H * L.derivative -
        (45 : K[X]) * L * H.derivative = 0 := by
    simpa only [L] using
      alignedNinthDefectRow_eq_zero_610 hp hq hjac hp6 hq10 haligned hM
  have hC45 : Polynomial.C (45 : K) = (45 : K[X]) := C_ofNat_poly
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) := C_ofNat_poly
  have hW : Polynomial.wronskian (L ^ 2) (H ^ 45) = 0 := by
    rw [Polynomial.wronskian, Polynomial.derivative_pow,
      Polynomial.derivative_pow]
    calc
      L ^ 2 * (Polynomial.C (45 : K) * H ^ (45 - 1) * H.derivative) -
          Polynomial.C (2 : K) * L ^ (2 - 1) * L.derivative * H ^ 45 =
          L * H ^ 44 *
            (Polynomial.C (45 : K) * L * H.derivative -
              Polynomial.C (2 : K) * H * L.derivative) := by
        ring
      _ = 0 := by
        rw [hC45, hC2]
        have hfac :
            (45 : K[X]) * L * H.derivative -
              (2 : K[X]) * H * L.derivative = 0 := by
          linear_combination -hrow
        rw [hfac, mul_zero]
  exact eq_C_mul_of_wronskian_eq_zero (pow_ne_zero 45 hH) hW

end Max11DegreeRoutes
