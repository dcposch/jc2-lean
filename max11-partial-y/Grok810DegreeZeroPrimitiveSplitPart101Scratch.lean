import Fable810ScaleZeroThirteenthDefectPart101Scratch
import Fable810ScaleZeroFourteenthDefectPart101Scratch
import Grok810DegreeZeroPrimitiveSplitBaseScratch
import Grok810DegreeZeroRowScratch
import Fable810ScaleZeroThirteenthDefectPart21Scratch
import Fable810ScaleZeroFourteenthDefectPart102Scratch
import Fable810ScaleZeroFourteenthDefectPart24Scratch

/-! # SPEED: theorems of `Grok810DegreeZeroPrimitiveScratch`, part 0 of 8, so that no single
module retains all the reflective bridge proof terms at once.
Statements unchanged. -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

set_option maxRecDepth 1000000
set_option maxRecDepth 8000000

section DegreeZeroPrimitive810

variable {F : Type*} [Field F] [CharZero F]

section DerivativeCertificate

variable {k : Type*} [Field k] [Algebra k F]

set_option maxHeartbeats 64000000 in
/-- Exact differential transport of the primitive.  In particular, after
all old residuals are differential constants its derivative is the literal
degree-zero Jacobian row `W dG - F dX`. -/
theorem rhoResidual810_deriv_identity
    (d : Derivation k F F)
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 X0 : F) :
    d (rhoResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0) =
      (W0 * d G0 - F0 * d X0) +
      (-(3 * A ^ 3 - 16 * A * C0 - 8 * B ^ 2 + 128 * E0) / 128) *
        d (kappaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0) +
      ((A * B - 4 * D0) / 4) *
        d (muResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0) +
      ((3 * A ^ 2 - 16 * C0) / 16) *
        d (nuResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0) -
      B * d (xiResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0) -
      A * d (omicronResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0) +
      rhoLCertificate810 A B C0 D0 E0 F0 G0 * d L +
      rhoAlphaCertificate810 F0 G0 * d (alphaResidual810 A P) +
      rhoBetaCertificate810 A B C0 D0 E0 F0 G0 *
        d (betaResidual810 L A B Q) +
      rhoGammaCertificate810 A B C0 D0 E0 F0 G0 *
        d (gammaResidual810 L A B C0 P R) +
      rhoDeltaCertificate810 A B C0 D0 E0 F0 G0 *
        d (deltaResidual810 L A B C0 D0 P Q S0) +
      rhoEpsilonCertificate810 A B C0 D0 E0 F0 G0 *
        d (epsilonResidual810 L A B C0 D0 E0 P Q R T0) +
      rhoZetaCertificate810 A B C0 D0 E0 F0 G0 *
        d (zetaResidual810 L A B C0 D0 E0 F0 P Q R S0 U0) +
      rhoEtaCertificate810 A B C0 D0 E0 F0 *
        d (etaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 V0) +
      rhoThetaCertificate810 A B C0 D0 E0 G0 *
        d (thetaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 W0) +
      rhoIotaCertificate810 F0 *
        d (iotaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 X0) := by
  have hd1 : d (1 : F) = 0 := d.map_one_eq_zero
  have hd_ofNat (n : ℕ) [Nat.AtLeastTwo n] :
      d (ofNat(n) : F) = 0 := by
    rw [← Nat.cast_ofNat]
    exact d.map_natCast n
  -- Keep each denominator a scalar atom while differentiating.  In particular,
  -- do not introduce its square or duplicate the polynomial numerator.
  have hd_div_ofNat (a : F) (n : ℕ) [Nat.AtLeastTwo n] :
      d (a / (ofNat(n) : F)) = (ofNat(n) : F)⁻¹ • d a :=
    d.leibniz_div_const a _ (hd_ofNat n)
  have hd_mul_atom (a b : F) : a * d b = a • d b := rfl
  simp only [hd_mul_atom]
  simp only [rhoResidual810, rhoBaseGroup810, rhoBetaGroup810,
    rhoGammaGroup810, rhoDeltaGroup810, rhoEpsilonGroup810, rhoZetaGroup810,
    rhoEtaGroup810, rhoThetaGroup810, rhoAlphaCertificate810,
    rhoBetaCertificate810, rhoGammaCertificate810, rhoDeltaCertificate810,
    rhoEpsilonCertificate810, rhoZetaCertificate810, rhoEtaCertificate810,
    rhoThetaCertificate810, rhoIotaCertificate810, rhoLCertificate810,
    kappaResidual810, muResidual810, nuResidual810, xiResidual810,
    omicronResidual810,
    thetaResidual810, iotaResidual810, map_add, map_sub, map_neg,
    Derivation.leibniz, hd_div_ofNat, Derivation.leibniz_pow,
    hd1, hd_ofNat, smul_zero, zero_smul, add_zero, zero_add, sub_zero]
  -- The identity already holds with `alpha`…`eta` kept as opaque residual
  -- atoms: only the tower above them has to be expanded.  Compare the small
  -- scalar coefficient of each coordinate derivative.
  module


end DerivativeCertificate

end DegreeZeroPrimitive810

end Max11DegreeRoutes

end

#print axioms Max11DegreeRoutes.rhoResidual810_deriv_identity
/-! # SPEED: theorems of `Grok810DegreeZeroPrimitiveScratch`, part 2 of 8, so that no single
module retains all the reflective bridge proof terms at once.
Statements unchanged. -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option maxRecDepth 8000000

section DegreeZeroPrimitive810

variable {F : Type*} [Field F] [CharZero F]

section DerivativeCertificate

variable {k : Type*} [Field k] [Algebra k F]

set_option maxHeartbeats 64000000 in
theorem rhoResidual810_deriv_eq_row
    (d : Derivation k F F)
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 X0 : F)
    (hL : d L = 0)
    (halpha : d (alphaResidual810 A P) = 0)
    (hbeta : d (betaResidual810 L A B Q) = 0)
    (hgamma : d (gammaResidual810 L A B C0 P R) = 0)
    (hdelta : d (deltaResidual810 L A B C0 D0 P Q S0) = 0)
    (hepsilon : d (epsilonResidual810 L A B C0 D0 E0 P Q R T0) = 0)
    (hzeta : d (zetaResidual810 L A B C0 D0 E0 F0 P Q R S0 U0) = 0)
    (heta : d (etaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 V0) = 0)
    (htheta : d (thetaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 W0) = 0)
    (hiota : d (iotaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 X0) = 0)
    (hkappa : d (kappaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0) = 0)
    (hmu : d (muResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0) = 0)
    (hnu : d (nuResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0) = 0)
    (hxi : d (xiResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0) = 0)
    (homicron : d (omicronResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0) = 0) :
    d (rhoResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0) =
      W0 * d G0 - F0 * d X0 := by
  rw [rhoResidual810_deriv_identity d L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 X0]
  rw [hL, halpha, hbeta, hgamma, hdelta, hepsilon, hzeta, heta, htheta,
    hiota, hkappa, hmu, hnu, hxi, homicron]
  simp only [mul_zero, add_zero, sub_zero]


end DerivativeCertificate

end DegreeZeroPrimitive810

end Max11DegreeRoutes

end

#print axioms Max11DegreeRoutes.rhoResidual810_deriv_eq_row
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
