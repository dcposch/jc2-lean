import Fable810ScaleZeroThirteenthDefectPart02Scratch
import Fable810ScaleZeroFourteenthDefectPart02Scratch
import Grok810DegreeZeroPrimitiveSplitBaseScratch

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
