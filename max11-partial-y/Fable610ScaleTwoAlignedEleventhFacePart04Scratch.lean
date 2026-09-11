import Fable610ScaleTwoAlignedTenthFacePart04Scratch
import Fable610ScaleTwoAlignedEleventhFacePart01Scratch
import Fable610ScaleTwoAlignedEleventhFacePart03Scratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

set_option maxHeartbeats 3200000000 in
/-- On the aligned face, with the consumed degree-`13` through
degree-`5` rows, the degree-`4` row is the weighted derivative
`2 H Λ' - 55 Λ H' = 0`. -/
theorem alignedEleventhDefectRow_eq_zero_610 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect610 H (p.coeff 4) (p.coeff 5) (q.coeff 8) =
      Polynomial.C κ * H ^ 5) :
    (2 : K[X]) * H * (alignedEleventhDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
      (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 1) (q.coeff 2) (q.coeff
      3) (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ).derivative -
      (55 : K[X]) * alignedEleventhDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
      (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 1) (q.coeff 2) (q.coeff
      3) (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ * H.derivative = 0 := by
  have hrow := alignedEleventhCoefficientJacobianRow_610 hp hq hjac
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) := C_ofNat_poly
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) := C_ofNat_poly
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) := C_ofNat_poly
  have hC5 : Polynomial.C (5 : K) = (5 : K[X]) := C_ofNat_poly
  rw [hC2, hC3, hC4, hC5] at hrow
  have hDrow :=
    alignedThirdDefectRow_eq_zero_610 hp hq hjac hp6 hq10 haligned hM
  have hErow :=
    alignedFourthDefectRow_eq_zero_610 hp hq hjac hp6 hq10 haligned hM
  have hFrow :=
    alignedFifthDefectRow_eq_zero_610 hp hq hjac hp6 hq10 haligned hM
  have hGrow :=
    alignedSixthDefectRow_eq_zero_610 hp hq hjac hp6 hq10 haligned hM
  have hIrow :=
    alignedSeventhDefectRow_eq_zero_610 hp hq hjac hp6 hq10 haligned hM
  have hJrow :=
    alignedEighthDefectRow_eq_zero_610 hp hq hjac hp6 hq10 haligned hM
  have hLrow :=
    alignedNinthDefectRow_eq_zero_610 hp hq hjac hp6 hq10 haligned hM
  have hOrow :=
    alignedTenthDefectRow_eq_zero_610 hp hq hjac hp6 hq10 haligned hM
  have hid := alignedEleventhDefect_weightedDerivative_identity_610
    H (p.coeff 0) (p.coeff 1) (p.coeff 2) (p.coeff 3) (p.coeff 4)
    (p.coeff 5) (q.coeff 0) (q.coeff 1) (q.coeff 2) (q.coeff 3)
    (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ
  rw [hrow, hDrow, hErow, hFrow, hGrow, hIrow, hJrow, hLrow, hOrow] at hid
  simp only [Polynomial.derivative_zero, mul_zero, zero_mul, add_zero,
    sub_zero, zero_add] at hid
  linear_combination -hid

end Max11DegreeRoutes
