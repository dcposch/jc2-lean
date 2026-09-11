import Sol610ScaleTwoDegreeZeroPrimitivePart17Scratch
import Sol610ScaleTwoDegreeZeroPrimitivePart16Scratch
import Sol610ScaleTwoDegreeZeroPrimitivePart15Scratch
import Sol610ScaleTwoDegreeZeroPrimitivePart14Scratch
import Sol610ScaleTwoDegreeZeroPrimitivePart13Scratch
import Sol610ScaleTwoDegreeZeroPrimitivePart12Scratch
import Sol610ScaleTwoDegreeZeroPrimitivePart11Scratch
import Sol610ScaleTwoDegreeZeroPrimitivePart10Scratch
import Sol610ScaleTwoDegreeZeroPrimitivePart09Scratch

noncomputable section
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section DegreeZeroPrimitive610

variable {F : Type*} [Field F] [CharZero F]

section DifferentialCertificate

variable {k : Type*} [Field k] [Algebra k F]

set_option maxHeartbeats 800000000 in
/-- Exact differential transport of the primitive.  In particular, after
all old residuals are differential constants its derivative is the literal
degree-zero Jacobian row `W dE - D dX`. -/
theorem degreeZeroPrimitive610_deriv_identity
    (d : Derivation k F F)
    (L A B C0 D0 E0 P Q R S0 T0 U0 V0 W0 X0 : F) :
    d (degreeZeroPrimitive610 L A B C0 D0 E0 P Q R S0 T0 U0 V0 W0 X0) =
      (W0 * d E0 - D0 * d X0) +
      (A ^ 2 - 12 * C0) / 12 *
        d (kappaResidual610 L A B C0 D0 E0 P Q R S0 T0 U0 V0 W0) -
      B * d (lambdaResidual610 L A B C0 D0 E0 P Q R S0 T0 U0 V0 W0) -
      A * d (muResidual610 L A B C0 D0 E0 P Q R S0 T0 U0 V0 W0) +
      degreeZeroLCertificate610 A B C0 D0 E0 * d L +
      degreeZeroAlphaCertificate610 A B C0 D0 E0 *
        d (alphaResidual610 A P) +
      degreeZeroBetaCertificate610 A B C0 D0 E0 *
        d (betaResidual610 L A B Q) +
      D0 * E0 * d (gammaResidual610 L A B C0 P R) +
      degreeZeroDeltaCertificate610 A B C0 D0 E0 *
        d (deltaResidual610 L A B C0 D0 P Q S0) +
      degreeZeroEpsilonCertificate610 A B C0 D0 E0 *
        d (epsilonResidual610 L A B C0 D0 E0 P Q R T0) +
      degreeZeroZetaCertificate610 A B C0 D0 E0 *
        d (zetaResidual610 L A B C0 D0 E0 P Q R S0 U0) +
      degreeZeroEtaCertificate610 A B C0 D0 *
        d (etaResidual610 L A B C0 D0 E0 P Q R S0 T0 V0) +
      degreeZeroThetaCertificate610 A B C0 E0 *
        d (thetaResidual610 L A B C0 D0 E0 P Q R S0 T0 U0 W0) +
      D0 * d (iotaResidual610 L A B C0 D0 E0 P Q R S0 T0 U0 V0 X0) := by
  have hd1 : d (1 : F) = 0 := d.map_one_eq_zero
  have hd_ofNat (n : ℕ) [Nat.AtLeastTwo n] :
      d (ofNat(n) : F) = 0 := by
    rw [← Nat.cast_ofNat]
    exact d.map_natCast n
  simp only [degreeZeroPrimitive610, degreeZeroBaseGroup610,
    degreeZeroAlphaGroup610, degreeZeroBetaGroup610,
    degreeZeroDeltaGroup610, degreeZeroEpsilonGroup610,
    degreeZeroZetaGroup610, degreeZeroEtaGroup610,
    degreeZeroThetaGroup610, degreeZeroLCertificate610,
    degreeZeroAlphaCertificate610, degreeZeroBetaCertificate610,
    degreeZeroDeltaCertificate610, degreeZeroEpsilonCertificate610,
    degreeZeroZetaCertificate610, degreeZeroEtaCertificate610,
    degreeZeroThetaCertificate610, kappaResidual610, lambdaResidual610,
    muResidual610, alphaResidual610, betaResidual610, gammaResidual610,
    deltaResidual610, epsilonResidual610, zetaResidual610, etaResidual610,
    thetaResidual610, iotaResidual610, map_add, map_sub, map_neg,
    Derivation.leibniz, Derivation.leibniz_div, Derivation.leibniz_pow,
    nsmul_eq_mul]
  simp only [hd1, hd_ofNat, zero_mul, mul_zero, add_zero, zero_add, sub_zero]
  ring

end DifferentialCertificate

end DegreeZeroPrimitive610

end Max11DegreeRoutes
