import Fable610ScaleTwoAlignedEleventhFacePart04Scratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

set_option maxHeartbeats 8000000 in
/-- Squared weight-`55/2` polynomial first integral of the aligned
`(6,10)` eleventh defect: `Λ² = κ₁₀ H⁵⁵`.  The odd exponent forces a
square/nonsquare chamber split exactly as for `D`, `F`, `I`, and
`L`. -/
theorem alignedEleventhDefectPowerRelation_610 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hH : H ≠ 0)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect610 H (p.coeff 4) (p.coeff 5) (q.coeff 8) =
      Polynomial.C κ * H ^ 5) :
    ∃ κ₁₀ : K,
      alignedEleventhDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
      (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 1) (q.coeff 2) (q.coeff
      3) (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ ^ 2 =
      Polynomial.C κ₁₀ * H ^ 55 := by
  let L : K[X] :=
    alignedEleventhDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
    (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 1) (q.coeff 2) (q.coeff
    3) (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ
  have hrow :
      (2 : K[X]) * H * L.derivative -
        (55 : K[X]) * L * H.derivative = 0 := by
    simpa only [L] using
      alignedEleventhDefectRow_eq_zero_610 hp hq hjac hp6 hq10 haligned hM
  have hC55 : Polynomial.C (55 : K) = (55 : K[X]) := C_ofNat_poly
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) := C_ofNat_poly
  have hW : Polynomial.wronskian (L ^ 2) (H ^ 55) = 0 := by
    rw [Polynomial.wronskian, Polynomial.derivative_pow,
      Polynomial.derivative_pow]
    calc
      L ^ 2 * (Polynomial.C (55 : K) * H ^ (55 - 1) * H.derivative) -
          Polynomial.C (2 : K) * L ^ (2 - 1) * L.derivative * H ^ 55 =
          L * H ^ 54 *
            (Polynomial.C (55 : K) * L * H.derivative -
              Polynomial.C (2 : K) * H * L.derivative) := by
        ring
      _ = 0 := by
        rw [hC55, hC2]
        have hfac :
            (55 : K[X]) * L * H.derivative -
              (2 : K[X]) * H * L.derivative = 0 := by
          linear_combination -hrow
        rw [hfac, mul_zero]
  exact eq_C_mul_of_wronskian_eq_zero (pow_ne_zero 55 hH) hW

end Max11DegreeRoutes
