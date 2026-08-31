import Sol610ScaleTwoDegreeZeroPrimitiveScratch

/-! # Differential-Jacobian bridge for the `(6,10)` degree-zero primitive

The degree-zero primitive is inhomogeneous: its derivative is the constant
coefficient of the depressed differential Jacobian, rather than zero.  This
module packages the residual-tower transport and derives that statement from
one monic sextic-decic Jacobian identity.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000

section DegreeZeroDepressedRows610

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]

/-- The residual tower transports rows thirteen through two into the literal
degree-zero row. -/
theorem degreeZeroPrimitive610_deriv_eq_row_of_depressed_rows
    (d : Derivation k F F)
    (L A B C0 D0 E0 P Q R S0 T0 U0 V0 W0 X0 : F)
    (hL : d L = 0)
    (h13 : (10 : F) * d A - 6 * d P = 0)
    (h12 : (10 : F) * d B + 9 * L * d A - 6 * d Q = 0)
    (h11 : (10 : F) * d C0 + 9 * L * d B + 8 * P * d A -
      4 * A * d P - 6 * d R = 0)
    (h10 : (10 : F) * d D0 + 9 * L * d C0 + 8 * P * d B +
      7 * Q * d A - 3 * B * d P - 4 * A * d Q - 6 * d S0 = 0)
    (h9 : (10 : F) * d E0 + 9 * L * d D0 + 8 * P * d C0 +
      7 * Q * d B + 6 * R * d A - 2 * C0 * d P - 3 * B * d Q -
      4 * A * d R - 6 * d T0 = 0)
    (h8 : (9 : F) * L * d E0 + 8 * P * d D0 + 7 * Q * d C0 +
      6 * R * d B + 5 * S0 * d A - D0 * d P - 2 * C0 * d Q -
      3 * B * d R - 4 * A * d S0 - 6 * d U0 = 0)
    (h7 : (8 : F) * P * d E0 + 7 * Q * d D0 + 6 * R * d C0 +
      5 * S0 * d B + 4 * T0 * d A - D0 * d Q - 2 * C0 * d R -
      3 * B * d S0 - 4 * A * d T0 - 6 * d V0 = 0)
    (h6 : (7 : F) * Q * d E0 + 6 * R * d D0 + 5 * S0 * d C0 +
      4 * T0 * d B + 3 * U0 * d A - D0 * d R - 2 * C0 * d S0 -
      3 * B * d T0 - 4 * A * d U0 - 6 * d W0 = 0)
    (h5 : (6 : F) * R * d E0 + 5 * S0 * d D0 + 4 * T0 * d C0 +
      3 * U0 * d B + 2 * V0 * d A - D0 * d S0 - 2 * C0 * d T0 -
      3 * B * d U0 - 4 * A * d V0 - 6 * d X0 = 0)
    (h4 : (5 : F) * S0 * d E0 + 4 * T0 * d D0 + 3 * U0 * d C0 +
      2 * V0 * d B + W0 * d A - D0 * d T0 - 2 * C0 * d U0 -
      3 * B * d V0 - 4 * A * d W0 = 0)
    (h3 : (4 : F) * T0 * d E0 + 3 * U0 * d D0 + 2 * V0 * d C0 +
      W0 * d B - D0 * d U0 - 2 * C0 * d V0 - 3 * B * d W0 -
      4 * A * d X0 = 0)
    (h2 : (3 : F) * U0 * d E0 + 2 * V0 * d D0 + W0 * d C0 -
      D0 * d V0 - 2 * C0 * d W0 - 3 * B * d X0 = 0) :
    d (degreeZeroPrimitive610 L A B C0 D0 E0 P Q R S0 T0 U0 V0 W0 X0) =
      W0 * d E0 - D0 * d X0 := by
  have halpha := alphaResidual610_deriv_zero d A P h13
  have hbeta := betaResidual610_deriv_zero d L A B Q hL h12
  have hgamma := gammaResidual610_deriv_zero d L A B C0 P R hL halpha h11
  have hdelta := deltaResidual610_deriv_zero d L A B C0 D0 P Q S0 hL
    halpha hbeta h10
  have hepsilon := epsilonResidual610_deriv_zero d L A B C0 D0 E0 P Q R
    T0 hL halpha hbeta hgamma h9
  have hzeta := zetaResidual610_deriv_zero d L A B C0 D0 E0 P Q R S0 U0
    hL halpha hbeta hgamma hdelta (by linear_combination h8)
  have heta := etaResidual610_deriv_zero d L A B C0 D0 E0 P Q R S0 T0 V0
    hL halpha hbeta hgamma hdelta hepsilon (by linear_combination h7)
  have htheta := thetaResidual610_deriv_zero d L A B C0 D0 E0 P Q R S0 T0
    U0 W0 hL halpha hbeta hgamma hdelta hepsilon hzeta
    (by linear_combination h6)
  have hiota := iotaResidual610_deriv_zero d L A B C0 D0 E0 P Q R S0 T0 U0
    V0 X0 hL halpha hbeta hgamma hdelta hepsilon hzeta heta
    (by linear_combination h5)
  have hkappa := kappaResidual610_deriv_zero d L A B C0 D0 E0 P Q R S0 T0
    U0 V0 W0 hL halpha hbeta hgamma hdelta hepsilon hzeta heta htheta
    (by linear_combination h6) (by linear_combination h4)
  have hlambda := lambdaResidual610_deriv_zero d L A B C0 D0 E0 P Q R S0 T0
    U0 V0 W0 X0 hL halpha hbeta hgamma hdelta hepsilon hzeta heta htheta
    (by linear_combination h6) (by linear_combination h5)
    (by linear_combination h3)
  have hmu := muResidual610_deriv_zero d L A B C0 D0 E0 P Q R S0 T0 U0 V0
    W0 X0 hL halpha hbeta hgamma hdelta hepsilon hzeta heta htheta
    (by linear_combination h6) (by linear_combination h5)
    (by linear_combination h4) (by linear_combination h2)
  exact degreeZeroPrimitive610_deriv_eq_row d L A B C0 D0 E0 P Q R S0 T0 U0
    V0 W0 X0 hL halpha hbeta hgamma hdelta hepsilon hzeta heta htheta hiota
    hkappa hlambda hmu

end DegreeZeroDepressedRows610

section DegreeZeroMonicBridge610

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]

/-- Degree zero of any coefficient differential Jacobian. -/
theorem differentialJacobian_coeff_0
    (d : Derivation k F F) (f g : F[X]) :
    (differentialJacobian d f g).coeff 0 =
      g.coeff 1 * d (f.coeff 0) - f.coeff 1 * d (g.coeff 0) := by
  have hanti : (Finset.HasAntidiagonal.antidiagonal 0 :
      Finset (ℕ × ℕ)) = ({(0, 0)} : Finset (ℕ × ℕ)) := by decide
  have hfirst :
      (coefficientDeriv d f * g.derivative).coeff 0 =
        g.coeff 1 * d (f.coeff 0) := by
    rw [Polynomial.coeff_mul, hanti, Finset.sum_singleton,
      coeff_coefficientDeriv, Polynomial.coeff_derivative]
    ring
  have hsecond :
      (f.derivative * coefficientDeriv d g).coeff 0 =
        f.coeff 1 * d (g.coeff 0) := by
    rw [Polynomial.coeff_mul, hanti, Finset.sum_singleton,
      coeff_coefficientDeriv, Polynomial.coeff_derivative]
    ring
  simp only [differentialJacobian, Polynomial.coeff_sub, hfirst, hsecond]

/-- A constant depressed monic differential Jacobian makes the degree-zero
primitive differentiate to that same constant. -/
theorem degreeZeroPrimitive610_deriv_eq_constant_of_monic_differentialJacobian
    (d : Derivation k F F) (f g : F[X]) (c : F)
    (hf_high : ∀ n, 6 < n → f.coeff n = 0) (hf6 : f.coeff 6 = 1)
    (hf5 : f.coeff 5 = 0)
    (hg_high : ∀ n, 10 < n → g.coeff n = 0) (hg10 : g.coeff 10 = 1)
    (hL : d (g.coeff 9) = 0)
    (hjac : differentialJacobian d f g = Polynomial.C c) :
    d (degreeZeroPrimitive610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
      (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
      (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3) (g.coeff 2)
      (g.coeff 1) (g.coeff 0)) = c := by
  have hcoeff (n : ℕ) (hn : n ≠ 0) :
      (differentialJacobian d f g).coeff n = 0 := by
    rw [hjac]
    simp [Polynomial.coeff_C, hn]
  have h13 := (differentialJacobian_coeff_13_monicSexticDecic d f g
    hf_high hf6 hf5 hg_high hg10 hL).symm.trans (hcoeff 13 (by norm_num))
  have h12 := (differentialJacobian_coeff_12_monicSexticDecic d f g
    hf_high hf6 hf5 hg_high hg10 hL).symm.trans (hcoeff 12 (by norm_num))
  have h11 := (differentialJacobian_coeff_11_monicSexticDecic d f g
    hf_high hf6 hf5 hg_high hg10 hL).symm.trans (hcoeff 11 (by norm_num))
  have h10 := (differentialJacobian_coeff_10_monicSexticDecic d f g
    hf_high hf6 hf5 hg_high hg10 hL).symm.trans (hcoeff 10 (by norm_num))
  have h9 := (differentialJacobian_coeff_9_monicSexticDecic d f g
    hf_high hf6 hf5 hg_high hg10 hL).symm.trans (hcoeff 9 (by norm_num))
  have h8 := (differentialJacobian_coeff_8_monicSexticDecic d f g
    hf_high hf6 hf5 hg_high hg10 hL).symm.trans (hcoeff 8 (by norm_num))
  have h7 := (differentialJacobian_coeff_7_monicSexticDecic d f g
    hf_high hf6 hf5 hg_high hg10 hL).symm.trans (hcoeff 7 (by norm_num))
  have h6 := (differentialJacobian_coeff_6_monicSexticDecic d f g
    hf_high hf6 hf5 hg_high hg10 hL).symm.trans (hcoeff 6 (by norm_num))
  have h5 := (differentialJacobian_coeff_5_monicSexticDecic d f g
    hf_high hf6 hf5 hg_high hg10 hL).symm.trans (hcoeff 5 (by norm_num))
  have h4 := (differentialJacobian_coeff_4_monicSexticDecic d f g
    hf_high hf6 hf5 hg_high hg10 hL).symm.trans (hcoeff 4 (by norm_num))
  have h3 := (differentialJacobian_coeff_3_monicSexticDecic d f g
    hf_high hf6 hf5 hg_high hg10 hL).symm.trans (hcoeff 3 (by norm_num))
  have h2 := (differentialJacobian_coeff_2_monicSexticDecic d f g
    hf_high hf6 hf5 hg_high hg10 hL).symm.trans (hcoeff 2 (by norm_num))
  have hrow := degreeZeroPrimitive610_deriv_eq_row_of_depressed_rows d
    (g.coeff 9) (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1)
    (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5)
    (g.coeff 4) (g.coeff 3) (g.coeff 2) (g.coeff 1) (g.coeff 0) hL
    (by linear_combination h13) (by linear_combination h12)
    (by linear_combination h11) (by linear_combination h10)
    (by linear_combination h9) (by linear_combination h8)
    (by linear_combination h7) (by linear_combination h6)
    (by linear_combination h5) (by linear_combination h4)
    (by linear_combination h3) (by linear_combination h2)
  have hconstant :
      (differentialJacobian d f g).coeff 0 = c := by
    have h := congrArg (fun t : F[X] => t.coeff 0) hjac
    simpa using h
  calc
    d (degreeZeroPrimitive610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
        (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
        (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3) (g.coeff 2)
        (g.coeff 1) (g.coeff 0)) =
        g.coeff 1 * d (f.coeff 0) - f.coeff 1 * d (g.coeff 0) := hrow
    _ = (differentialJacobian d f g).coeff 0 :=
      (differentialJacobian_coeff_0 d f g).symm
    _ = c := hconstant

#print axioms differentialJacobian_coeff_0
#print axioms degreeZeroPrimitive610_deriv_eq_row_of_depressed_rows
#print axioms degreeZeroPrimitive610_deriv_eq_constant_of_monic_differentialJacobian

end DegreeZeroMonicBridge610

section DegreeZeroRatFuncBridge610

variable {k : Type*} [Field k] [CharZero k]

/-- Explicit ordinary-derivative specialization of the monic bridge.  The
affine source depression supplies precisely the displayed simple pole as its
constant outer-polynomial coefficient. -/
theorem degreeZeroPrimitive610_ratFuncDeriv_eq_simplePole
    (f g : (RatFunc k)[X]) (j : k) (h : RatFunc k)
    (hf_high : ∀ n, 6 < n → f.coeff n = 0) (hf6 : f.coeff 6 = 1)
    (hf5 : f.coeff 5 = 0)
    (hg_high : ∀ n, 10 < n → g.coeff n = 0) (hg10 : g.coeff 10 = 1)
    (hL : ratFuncDerivation68 (g.coeff 9) = 0)
    (hjac : differentialJacobian ratFuncDerivation68 f g =
      Polynomial.C (RatFunc.C j / h)) :
    Differential.deriv
        (degreeZeroPrimitive610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
          (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3) (g.coeff 2)
          (g.coeff 1) (g.coeff 0)) =
      RatFunc.C j / h := by
  simpa only [ratFuncDerivation68, ratFuncDerivation46_apply] using
    degreeZeroPrimitive610_deriv_eq_constant_of_monic_differentialJacobian
      ratFuncDerivation68 f g (RatFunc.C j / h) hf_high hf6 hf5 hg_high
      hg10 hL hjac

#print axioms degreeZeroPrimitive610_ratFuncDeriv_eq_simplePole

end DegreeZeroRatFuncBridge610

end Max11DegreeRoutes
