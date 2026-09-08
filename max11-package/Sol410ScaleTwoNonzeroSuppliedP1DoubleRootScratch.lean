import Sol410ScaleTwoNonzeroSuppliedGroundDoubleRootScratch

/-!
# The remaining quartic coefficient has a double supplied root

Once the nonzero square face has reached the terminal valuation packet, the
literal degree-one Keller row kills the derivative of `p₁` at the supplied
root.  The nonzero Jacobian is used only to keep `q₁(a)` nonzero.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false

set_option maxHeartbeats 64000000 in
theorem nonzeroFace410_linearRoot_suppliedP1DoubleRoot
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hdegree : h0.natDegree = 1) (hH : H = h0 ^ 2)
    (hp4 : p.coeff 4 = H ^ 2) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 3 * H ^ 3 - (2 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0) (hlambda : lambda ≠ 0) (hj : j ≠ 0) :
    h0 ^ 2 ∣ p.coeff 1 := by
  obtain ⟨t2, a22, s22, vis, w73, q54, b42, b31, hp3, hp2, hq8,
      hq7, hq6, hq5, hq4, hq3, hT, hU, hW, hV, hX, hY⟩ :=
    nonzeroFace410_linearRoot_suppliedThetaInputs p q H h0 j lambda a
      hp hq hh0 hdegree hH hp4 hq10 hN hD hroot hlambda
  obtain ⟨_, _, _, _, _, _, ha1, _, _, _, _, _, _, _, _, _, _, hkelP,
      _, _, _, _⟩ :=
    nonzeroFace410_thetaZeroBranchClosurePacket p q H h0 j lambda t2 a22
      s22 vis w73 q54 b42 b31 a hp hq hH hp4 hq10 hN hD hp3 hp2 hq8
      hq7 hq6 hq5 hq4 hq3 hdegree hroot hT hU hW hV hX hY
  have hq20 : (q.coeff 2).eval a = 0 := by
    rw [ha1] at hY
    norm_num at hY
    exact hY
  have hp20 : (p.coeff 2).eval a = 0 := by
    rw [hp2, eval_mul, eval_pow, hroot]
    norm_num
  have hq1nz : (q.coeff 1).eval a ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hkelP
    exact hj hkelP.symm
  have hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j) := by
    simpa [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hD
  have hrow := twelfthCoefficientJacobianRow_410 hp hq hjac
  have hrowa := congrArg (fun f : k[X] => f.eval a) hrow
  simp only [eval_add, eval_sub, eval_mul, eval_C, eval_zero, hp20, hq20,
    ha1, zero_mul, mul_zero, add_zero, sub_zero] at hrowa
  have hp1kill : (p.coeff 1).derivative.eval a = 0 :=
    (mul_eq_zero.mp hrowa).resolve_right hq1nz
  exact linearPolynomial_sq_dvd_of_eval_derivative_zero_410 h0
    (p.coeff 1) a hdegree hroot ha1 hp1kill

end Max11DegreeRoutes
