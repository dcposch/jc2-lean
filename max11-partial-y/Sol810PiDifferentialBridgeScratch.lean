import Sol810PiResidualScratch

/-! # Monic differential-Jacobian bridge for the `(8,10)` pi integral

This module packages the complete residual tower behind `pi` into one honest
interface.  A constant differential Jacobian for a depressed monic octic and
decic makes the degree-one integral a differential constant. -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 100000

section DegreeOneDepressedRow810

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- Degree one of the differential Jacobian of a depressed monic octic and
a monic decic.  The high-degree assumptions are retained for a uniform API
with the already verified rows fifteen through two. -/
theorem differentialJacobian_coeff_1_monicOcticDecic
    (d : Derivation k F F) (f g : F[X])
    (_hf_high : ∀ n, 8 < n → f.coeff n = 0) (_hf8 : f.coeff 8 = 1)
    (_hf7 : f.coeff 7 = 0)
    (_hg_high : ∀ n, 10 < n → g.coeff n = 0) (_hg10 : g.coeff 10 = 1)
    (_hL : d (g.coeff 9) = 0) :
    (differentialJacobian d f g).coeff 1 =
      (2 : F) * g.coeff 2 * d (f.coeff 0) +
        (1 : F) * g.coeff 1 * d (f.coeff 1) -
          (1 : F) * f.coeff 1 * d (g.coeff 1) -
          (2 : F) * f.coeff 2 * d (g.coeff 0) := by
  have hanti : (Finset.HasAntidiagonal.antidiagonal 1 :
      Finset (ℕ × ℕ)) =
      ({(0, 1), (1, 0)} : Finset (ℕ × ℕ)) := by decide
  have hne : ((0, 1) : ℕ × ℕ) ≠ (1, 0) := by decide
  have hfirst :
      (coefficientDeriv d f * g.derivative).coeff 1 =
        (2 : F) * g.coeff 2 * d (f.coeff 0) +
          (1 : F) * g.coeff 1 * d (f.coeff 1) := by
    rw [Polynomial.coeff_mul, hanti]
    have hpair :
        (∑ p ∈ ({(0, 1), (1, 0)} : Finset (ℕ × ℕ)),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (coefficientDeriv d f).coeff 0 * g.derivative.coeff 1 +
            (coefficientDeriv d f).coeff 1 * g.derivative.coeff 0 := by
      rw [Finset.sum_insert (by simp [hne]), Finset.sum_singleton]
    have hder1g : g.derivative.coeff 1 = (2 : F) * g.coeff 2 := by
      rw [Polynomial.coeff_derivative]
      ring
    have hder0g : g.derivative.coeff 0 = (1 : F) * g.coeff 1 := by
      rw [Polynomial.coeff_derivative]
      ring
    rw [hpair, coeff_coefficientDeriv, coeff_coefficientDeriv,
      hder1g, hder0g]
    ring
  have hsecond :
      (f.derivative * coefficientDeriv d g).coeff 1 =
        (1 : F) * f.coeff 1 * d (g.coeff 1) +
          (2 : F) * f.coeff 2 * d (g.coeff 0) := by
    rw [Polynomial.coeff_mul, hanti]
    have hpair :
        (∑ p ∈ ({(0, 1), (1, 0)} : Finset (ℕ × ℕ)),
            f.derivative.coeff p.1 * (coefficientDeriv d g).coeff p.2) =
          f.derivative.coeff 0 * (coefficientDeriv d g).coeff 1 +
            f.derivative.coeff 1 * (coefficientDeriv d g).coeff 0 := by
      rw [Finset.sum_insert (by simp [hne]), Finset.sum_singleton]
    have hder0f : f.derivative.coeff 0 = (1 : F) * f.coeff 1 := by
      rw [Polynomial.coeff_derivative]
      ring
    have hder1f : f.derivative.coeff 1 = (2 : F) * f.coeff 2 := by
      rw [Polynomial.coeff_derivative]
      ring
    rw [hpair, coeff_coefficientDeriv, coeff_coefficientDeriv,
      hder0f, hder1f]
  simp only [differentialJacobian, Polynomial.coeff_sub, hfirst, hsecond]
  ring

end DegreeOneDepressedRow810

section PiMonicDifferentialBridge810

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]

set_option maxHeartbeats 400000000 in
/-- A constant depressed differential Jacobian makes the degree-one `pi`
integral a differential constant. -/
theorem piResidual810_deriv_zero_of_monic_differentialJacobian
    (d : Derivation k F F) (f g : F[X]) (c : F)
    (hf_high : ∀ n, 8 < n → f.coeff n = 0) (hf8 : f.coeff 8 = 1)
    (hf7 : f.coeff 7 = 0)
    (hg_high : ∀ n, 10 < n → g.coeff n = 0) (hg10 : g.coeff 10 = 1)
    (hL : d (g.coeff 9) = 0)
    (hjac : differentialJacobian d f g = Polynomial.C c) :
    d (piResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
      (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
      (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
      (g.coeff 3) (g.coeff 2) (g.coeff 1)) = 0 := by
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
  have h1 := (differentialJacobian_coeff_1_monicOcticDecic d f g
    hf_high hf8 hf7 hg_high hg10 hL).symm.trans (hcoeff 1 (by norm_num))
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
  apply piResidual810_deriv_zero d (g.coeff 9) (f.coeff 6) (f.coeff 5)
    (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
    (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
    (g.coeff 3) (g.coeff 2) (g.coeff 1) (g.coeff 0) hL halpha hbeta
    hgamma hdelta hepsilon hzeta heta htheta hiota hkappa hmu hnu hxi
  linear_combination h1

#print axioms differentialJacobian_coeff_1_monicOcticDecic
#print axioms piResidual810_deriv_zero_of_monic_differentialJacobian

end PiMonicDifferentialBridge810

end Max11DegreeRoutes
