import Grok810DegreeZeroPrimitiveSplitPart4Scratch

/-! # SPEED: theorems of `Grok810DegreeZeroPrimitiveScratch`, part 6 of 8, so that no single
module retains all the reflective bridge proof terms at once.
Statements unchanged. -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option maxRecDepth 8000000

section DegreeZeroMonicBridge810

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]

set_option maxHeartbeats 400000000 in
/-- Lane Z2: a constant depressed monic differential Jacobian makes the
degree-zero primitive differentiate to that same constant. -/
theorem rhoResidual810_deriv_eq_constant_of_monic_differentialJacobian
    (d : Derivation k F F) (f g : F[X]) (c : F)
    (hf_high : ∀ n, 8 < n → f.coeff n = 0) (hf8 : f.coeff 8 = 1)
    (hf7 : f.coeff 7 = 0)
    (hg_high : ∀ n, 10 < n → g.coeff n = 0) (hg10 : g.coeff 10 = 1)
    (hL : d (g.coeff 9) = 0)
    (hjac : differentialJacobian d f g = Polynomial.C c) :
    d (rhoResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
      (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
      (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
      (g.coeff 3) (g.coeff 2) (g.coeff 1)) = c := by
  have hcoeff (n : ℕ) (hn : n ≠ 0) :
      (differentialJacobian d f g).coeff n = 0 := by
    rw [hjac]
    simp [Polynomial.coeff_C, hn]
  have h15 := (differentialJacobian_coeff_15_monicOcticDecic d f g
    hf_high hf8 hf7 hg_high hg10 hL).symm.trans (hcoeff 15 (by norm_num))
  have h14 := (differentialJacobian_coeff_14_monicOcticDecic d f g
    hf_high hf8 hf7 hg_high hg10 hL).symm.trans (hcoeff 14 (by norm_num))
  have h13 := (differentialJacobian_coeff_13_monicOcticDecic d f g
    hf_high hf8 hf7 hg_high hg10 hL).symm.trans (hcoeff 13 (by norm_num))
  have h12 := (differentialJacobian_coeff_12_monicOcticDecic d f g
    hf_high hf8 hf7 hg_high hg10 hL).symm.trans (hcoeff 12 (by norm_num))
  have h11 := (differentialJacobian_coeff_11_monicOcticDecic d f g
    hf_high hf8 hf7 hg_high hg10 hL).symm.trans (hcoeff 11 (by norm_num))
  have h10 := (differentialJacobian_coeff_10_monicOcticDecic d f g
    hf_high hf8 hf7 hg_high hg10 hL).symm.trans (hcoeff 10 (by norm_num))
  have h9 := (differentialJacobian_coeff_9_monicOcticDecic d f g
    hf_high hf8 hf7 hg_high hg10 hL).symm.trans (hcoeff 9 (by norm_num))
  have h8 := (differentialJacobian_coeff_8_monicOcticDecic d f g
    hf_high hf8 hf7 hg_high hg10 hL).symm.trans (hcoeff 8 (by norm_num))
  have h7 := (differentialJacobian_coeff_7_monicOcticDecic d f g
    hf_high hf8 hf7 hg_high hg10 hL).symm.trans (hcoeff 7 (by norm_num))
  have h6 := (differentialJacobian_coeff_6_monicOcticDecic d f g
    hf_high hf8 hf7 hg_high hg10 hL).symm.trans (hcoeff 6 (by norm_num))
  have h5 := (differentialJacobian_coeff_5_monicOcticDecic d f g
    hf_high hf8 hf7 hg_high hg10 hL).symm.trans (hcoeff 5 (by norm_num))
  have h4 := (differentialJacobian_coeff_4_monicOcticDecic d f g
    hf_high hf8 hf7 hg_high hg10 hL).symm.trans (hcoeff 4 (by norm_num))
  have h3 := (differentialJacobian_coeff_3_monicOcticDecic d f g
    hf_high hf8 hf7 hg_high hg10 hL).symm.trans (hcoeff 3 (by norm_num))
  have h2 := (differentialJacobian_coeff_2_monicOcticDecic d f g
    hf_high hf8 hf7 hg_high hg10 hL).symm.trans (hcoeff 2 (by norm_num))
  have halpha : d (alphaResidual810 (f.coeff 6) (g.coeff 8)) = 0 :=
    alphaResidual810_deriv_zero d (f.coeff 6) (g.coeff 8) (by
      linear_combination h15)
  have hbeta : d (betaResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
      (g.coeff 7)) = 0 :=
    betaResidual810_deriv_zero d (g.coeff 9) (f.coeff 6) (f.coeff 5)
      (g.coeff 7) hL (by linear_combination h14)
  have hgamma : d (gammaResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
      (f.coeff 4) (g.coeff 8) (g.coeff 6)) = 0 :=
    gammaResidual810_deriv_zero d (g.coeff 9) (f.coeff 6) (f.coeff 5)
      (f.coeff 4) (g.coeff 8) (g.coeff 6) hL halpha
      (by linear_combination h13)
  have hdelta : d (deltaResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
      (f.coeff 4) (f.coeff 3) (g.coeff 8) (g.coeff 7) (g.coeff 5)) = 0 :=
    deltaResidual810_deriv_zero d (g.coeff 9) (f.coeff 6) (f.coeff 5)
      (f.coeff 4) (f.coeff 3) (g.coeff 8) (g.coeff 7) (g.coeff 5)
      hL halpha hbeta (by linear_combination h12)
  have hepsilon : d (epsilonResidual810 (g.coeff 9) (f.coeff 6)
      (f.coeff 5) (f.coeff 4) (f.coeff 3) (f.coeff 2) (g.coeff 8)
      (g.coeff 7) (g.coeff 6) (g.coeff 4)) = 0 :=
    epsilonResidual810_deriv_zero d (g.coeff 9) (f.coeff 6) (f.coeff 5)
      (f.coeff 4) (f.coeff 3) (f.coeff 2) (g.coeff 8) (g.coeff 7)
      (g.coeff 6) (g.coeff 4) hL halpha hbeta hgamma
      (by linear_combination h11)
  have hzeta : d (zetaResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
      (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (g.coeff 8)
      (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 3)) = 0 :=
    zetaResidual810_deriv_zero d (g.coeff 9) (f.coeff 6) (f.coeff 5)
      (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (g.coeff 8)
      (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 3) hL halpha hbeta
      hgamma hdelta (by linear_combination h10)
  have heta : d (etaResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
      (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
      (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
      (g.coeff 2)) = 0 :=
    etaResidual810_deriv_zero d (g.coeff 9) (f.coeff 6) (f.coeff 5)
      (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
      (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
      (g.coeff 2) hL halpha hbeta hgamma hdelta hepsilon
      (by linear_combination h9)
  have htheta : d (thetaResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
      (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
      (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
      (g.coeff 3) (g.coeff 1)) = 0 :=
    thetaResidual810_deriv_zero d (g.coeff 9) (f.coeff 6) (f.coeff 5)
      (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
      (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
      (g.coeff 3) (g.coeff 1) hL halpha hbeta hgamma hdelta hepsilon
      hzeta (by linear_combination h8)
  have hiota : d (iotaResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
      (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
      (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
      (g.coeff 3) (g.coeff 2) (g.coeff 0)) = 0 :=
    iotaResidual810_deriv_zero d (g.coeff 9) (f.coeff 6) (f.coeff 5)
      (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
      (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
      (g.coeff 3) (g.coeff 2) (g.coeff 0) hL halpha hbeta hgamma hdelta
      hepsilon hzeta heta (by linear_combination h7)
  have hkappa : d (kappaResidual810 (g.coeff 9) (f.coeff 6)
      (f.coeff 5) (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1)
      (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5)
      (g.coeff 4) (g.coeff 3) (g.coeff 2) (g.coeff 1)) = 0 :=
    kappaResidual810_deriv_zero d (g.coeff 9) (f.coeff 6) (f.coeff 5)
      (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
      (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
      (g.coeff 3) (g.coeff 2) (g.coeff 1) hL halpha hbeta hgamma hdelta
      hepsilon hzeta heta htheta (by linear_combination h8)
      (by linear_combination h6)
  have hmu : d (muResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
      (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
      (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
      (g.coeff 3) (g.coeff 2) (g.coeff 1)) = 0 :=
    muResidual810_deriv_zero d (g.coeff 9) (f.coeff 6) (f.coeff 5)
      (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
      (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
      (g.coeff 3) (g.coeff 2) (g.coeff 1) (g.coeff 0) hL halpha hbeta
      hgamma hdelta hepsilon hzeta heta htheta hiota
      (by linear_combination h8) (by linear_combination h7)
      (by linear_combination h5)
  have hnu : d (nuResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
      (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
      (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
      (g.coeff 3) (g.coeff 2) (g.coeff 1)) = 0 :=
    nuResidual810_deriv_zero d (g.coeff 9) (f.coeff 6) (f.coeff 5)
      (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
      (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
      (g.coeff 3) (g.coeff 2) (g.coeff 1) (g.coeff 0) hL halpha hbeta
      hgamma hdelta hepsilon hzeta heta htheta hiota
      (by linear_combination h8) (by linear_combination h7)
      (by linear_combination h6) (by linear_combination h4)
  have hxi : d (xiResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
      (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
      (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
      (g.coeff 3) (g.coeff 2) (g.coeff 1)) = 0 :=
    xiResidual810_deriv_zero d (g.coeff 9) (f.coeff 6) (f.coeff 5)
      (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
      (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
      (g.coeff 3) (g.coeff 2) (g.coeff 1) (g.coeff 0) hL halpha hbeta
      hgamma hdelta hepsilon hzeta heta htheta hiota
      (by linear_combination h8) (by linear_combination h7)
      (by linear_combination h6) (by linear_combination h5)
      (by linear_combination h3)
  have homicron : d (omicronResidual810 (g.coeff 9) (f.coeff 6)
      (f.coeff 5) (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1)
      (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5)
      (g.coeff 4) (g.coeff 3) (g.coeff 2) (g.coeff 1)) = 0 :=
    omicronResidual810_deriv_zero d (g.coeff 9) (f.coeff 6) (f.coeff 5)
      (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
      (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
      (g.coeff 3) (g.coeff 2) (g.coeff 1) (g.coeff 0) hL halpha hbeta
      hgamma hdelta hepsilon hzeta heta htheta hiota
      (by linear_combination h8) (by linear_combination h7)
      (by linear_combination h6) (by linear_combination h5)
      (by linear_combination h4) (by linear_combination h2)
  have hrow := rhoResidual810_deriv_eq_row d (g.coeff 9) (f.coeff 6)
    (f.coeff 5) (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1)
    (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5)
    (g.coeff 4) (g.coeff 3) (g.coeff 2) (g.coeff 1) (g.coeff 0)
    hL halpha hbeta hgamma hdelta hepsilon hzeta heta htheta hiota
    hkappa hmu hnu hxi homicron
  have hconstant :=
    degreeZeroRow_eq_constant_of_monic_differentialJacobian d f g c
      hf_high hf8 hf7 hg_high hg10 hL hjac
  exact hrow.trans hconstant


end DegreeZeroMonicBridge810

end Max11DegreeRoutes

end
