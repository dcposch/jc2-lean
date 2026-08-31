import Fable610ScaleZeroTwelfthDefectScratch

/-! # Exact primitive for the `(6,10)` degree-zero row

The last Jacobian row is inhomogeneous, so this weight-fifteen primitive is
not a first integral.  Its derivative is the literal row zero, modulo the
already established residual tower.  The grouped formula and differential
certificate were independently reconstructed by
`derive_610_degree_zero_residual.py` (SHA256
`cd333da32d89eb7eb86f0fc1043ee718f65716faa41edcf29bc4ca2248473b58`).
-/

noncomputable section

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000

section DegreeZeroPrimitive610

variable {F : Type*} [Field F] [CharZero F]

def degreeZeroAlphaGroup610 (A B C0 D0 E0 : F) : F :=
  (35 * A ^ 5 * B - 51 * A ^ 4 * D0 - 222 * A ^ 3 * B * C0 -
    117 * A ^ 2 * B ^ 3 + 189 * A ^ 2 * B * E0 +
    297 * A ^ 2 * C0 * D0 + 324 * A * B ^ 2 * D0 +
    324 * A * B * C0 ^ 2 - 324 * A * D0 * E0 +
    108 * B ^ 3 * C0 - 324 * B * C0 * E0 - 324 * B * D0 ^ 2 -
    324 * C0 ^ 2 * D0) / 729

def degreeZeroBetaGroup610 (A B C0 D0 E0 : F) : F :=
  7 * (385 * A ^ 6 - 3420 * A ^ 4 * C0 - 7380 * A ^ 3 * B ^ 2 +
    3024 * A ^ 3 * E0 + 18144 * A ^ 2 * B * D0 +
    9072 * A ^ 2 * C0 ^ 2 + 19440 * A * B ^ 2 * C0 -
    15552 * A * C0 * E0 - 15552 * A * D0 ^ 2 + 1620 * B ^ 4 -
    7776 * B ^ 2 * E0 - 31104 * B * C0 * D0 - 5184 * C0 ^ 3 +
    46656 * E0 ^ 2) / 559872

def degreeZeroDeltaGroup610 (A B C0 D0 : F) : F :=
  (49 * A ^ 5 - 360 * A ^ 3 * C0 - 600 * A ^ 2 * B ^ 2 +
    1440 * A * B * D0 + 720 * A * C0 ^ 2 + 720 * B ^ 2 * C0 -
    2160 * D0 ^ 2) / 5184

def degreeZeroEpsilonGroup610 (A B C0 D0 : F) : F :=
  -(7 * A ^ 3 * B - 9 * A ^ 2 * D0 - 24 * A * B * C0 -
    4 * B ^ 3 + 36 * C0 * D0) / 54

def degreeZeroZetaGroup610 (A B C0 D0 : F) : F :=
  -(7 * A ^ 4 - 40 * A ^ 2 * C0 - 48 * A * B ^ 2 +
    96 * B * D0 + 48 * C0 ^ 2) / 192

def degreeZeroEtaGroup610 (A B C0 D0 : F) : F :=
  (7 * A ^ 2 * B - 12 * A * D0 - 12 * B * C0) / 36

def degreeZeroThetaGroup610 (A B C0 E0 : F) : F :=
  (7 * A ^ 3 - 36 * A * C0 - 18 * B ^ 2 + 216 * E0) / 216

def degreeZeroBaseGroup610 (L A B C0 D0 E0 : F) : F :=
  -(10935 * A ^ 7 * L + 62720 * A ^ 6 * B -
    113724 * A ^ 5 * C0 * L - 92160 * A ^ 5 * D0 -
    301806 * A ^ 4 * B ^ 2 * L - 491520 * A ^ 4 * B * C0 +
    122472 * A ^ 4 * E0 * L - 343040 * A ^ 3 * B ^ 3 +
    769824 * A ^ 3 * B * D0 * L + 483840 * A ^ 3 * B * E0 +
    384912 * A ^ 3 * C0 ^ 2 * L + 668160 * A ^ 3 * C0 * D0 +
    1224720 * A ^ 2 * B ^ 2 * C0 * L + 1071360 * A ^ 2 * B ^ 2 * D0 +
    1071360 * A ^ 2 * B * C0 ^ 2 - 699840 * A ^ 2 * C0 * E0 * L -
    559872 * A ^ 2 * D0 ^ 2 * L - 622080 * A ^ 2 * D0 * E0 +
    209952 * A * B ^ 4 * L + 737280 * A * B ^ 3 * C0 -
    839808 * A * B ^ 2 * E0 * L - 2519424 * A * B * C0 * D0 * L -
    1658880 * A * B * C0 * E0 - 1244160 * A * B * D0 ^ 2 -
    419904 * A * C0 ^ 3 * L - 1244160 * A * C0 ^ 2 * D0 +
    36864 * B ^ 5 - 419904 * B ^ 3 * D0 * L - 276480 * B ^ 3 * E0 -
    629856 * B ^ 2 * C0 ^ 2 * L - 1244160 * B ^ 2 * C0 * D0 -
    414720 * B * C0 ^ 3 + 1679616 * B * D0 * E0 * L +
    839808 * C0 ^ 2 * E0 * L + 1679616 * C0 * D0 ^ 2 * L +
    2488320 * C0 * D0 * E0 + 829440 * D0 ^ 3) / 2239488

/-- The canonical weight-fifteen primitive after the polynomial-part faces
have been transported back to their literal residual functions. -/
def degreeZeroPrimitive610
    (L A B C0 D0 E0 P Q R S0 T0 U0 V0 W0 X0 : F) : F :=
  degreeZeroBaseGroup610 L A B C0 D0 E0 +
    alphaResidual610 A P * degreeZeroAlphaGroup610 A B C0 D0 E0 +
    betaResidual610 L A B Q * degreeZeroBetaGroup610 A B C0 D0 E0 +
    deltaResidual610 L A B C0 D0 P Q S0 *
      degreeZeroDeltaGroup610 A B C0 D0 +
    epsilonResidual610 L A B C0 D0 E0 P Q R T0 *
      degreeZeroEpsilonGroup610 A B C0 D0 +
    zetaResidual610 L A B C0 D0 E0 P Q R S0 U0 *
      degreeZeroZetaGroup610 A B C0 D0 +
    etaResidual610 L A B C0 D0 E0 P Q R S0 T0 V0 *
      degreeZeroEtaGroup610 A B C0 D0 +
    thetaResidual610 L A B C0 D0 E0 P Q R S0 T0 U0 W0 *
      degreeZeroThetaGroup610 A B C0 E0

def degreeZeroLCertificate610 (A B C0 D0 E0 : F) : F :=
  (A ^ 7 - 12 * A ^ 5 * C0 - 30 * A ^ 4 * B ^ 2 + 24 * A ^ 4 * E0 +
    96 * A ^ 3 * B * D0 + 48 * A ^ 3 * C0 ^ 2 +
    144 * A ^ 2 * B ^ 2 * C0 - 192 * A ^ 2 * C0 * E0 -
    96 * A ^ 2 * D0 ^ 2 + 24 * A * B ^ 4 - 192 * A * B ^ 2 * E0 -
    384 * A * B * C0 * D0 - 64 * A * C0 ^ 3 + 384 * A * E0 ^ 2 -
    64 * B ^ 3 * D0 - 96 * B ^ 2 * C0 ^ 2 + 768 * B * D0 * E0 +
    384 * C0 ^ 2 * E0 + 384 * C0 * D0 ^ 2) / 1024

def degreeZeroAlphaCertificate610 (A B C0 D0 E0 : F) : F :=
  -(8 * A ^ 5 * B - 15 * A ^ 4 * D0 - 60 * A ^ 3 * B * C0 -
    30 * A ^ 2 * B ^ 3 + 108 * A ^ 2 * B * E0 +
    108 * A ^ 2 * C0 * D0 + 108 * A * B ^ 2 * D0 +
    108 * A * B * C0 ^ 2 - 324 * A * D0 * E0 + 36 * B ^ 3 * C0 -
    324 * B * C0 * E0 - 162 * B * D0 ^ 2 - 162 * C0 ^ 2 * D0) / 729

def degreeZeroBetaCertificate610 (A B C0 D0 E0 : F) : F :=
  -7 * (187 * A ^ 6 - 1980 * A ^ 4 * C0 - 3960 * A ^ 3 * B ^ 2 +
    4320 * A ^ 3 * E0 + 12960 * A ^ 2 * B * D0 +
    6480 * A ^ 2 * C0 ^ 2 + 12960 * A * B ^ 2 * C0 -
    31104 * A * C0 * E0 - 15552 * A * D0 ^ 2 + 1080 * B ^ 4 -
    15552 * B ^ 2 * E0 - 31104 * B * C0 * D0 - 5184 * C0 ^ 3 -
    93312 * E0 ^ 2) / 1119744

def degreeZeroDeltaCertificate610 (A B C0 D0 E0 : F) : F :=
  -(91 * A ^ 5 - 840 * A ^ 3 * C0 - 1260 * A ^ 2 * B ^ 2 +
    2160 * A ^ 2 * E0 + 4320 * A * B * D0 + 2160 * A * C0 ^ 2 +
    2160 * B ^ 2 * C0 - 25920 * C0 * E0 - 12960 * D0 ^ 2) / 31104

def degreeZeroEpsilonCertificate610 (A B C0 D0 E0 : F) : F :=
  (4 * A ^ 3 * B - 9 * A ^ 2 * D0 - 18 * A * B * C0 - 3 * B ^ 3 +
    54 * B * E0 + 54 * C0 * D0) / 81

def degreeZeroZetaCertificate610 (A B C0 D0 E0 : F) : F :=
  (A ^ 4 - 8 * A ^ 2 * C0 - 8 * A * B ^ 2 + 32 * A * E0 +
    32 * B * D0 + 16 * C0 ^ 2) / 64

def degreeZeroEtaCertificate610 (A B C0 D0 : F) : F :=
  -(A ^ 2 * B - 3 * A * D0 - 3 * B * C0) / 9

def degreeZeroThetaCertificate610 (A B C0 E0 : F) : F :=
  -(5 * A ^ 3 - 36 * A * C0 - 18 * B ^ 2 - 216 * E0) / 216

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

theorem degreeZeroPrimitive610_deriv_eq_row
    (d : Derivation k F F)
    (L A B C0 D0 E0 P Q R S0 T0 U0 V0 W0 X0 : F)
    (hL : d L = 0)
    (halpha : d (alphaResidual610 A P) = 0)
    (hbeta : d (betaResidual610 L A B Q) = 0)
    (hgamma : d (gammaResidual610 L A B C0 P R) = 0)
    (hdelta : d (deltaResidual610 L A B C0 D0 P Q S0) = 0)
    (hepsilon : d (epsilonResidual610 L A B C0 D0 E0 P Q R T0) = 0)
    (hzeta : d (zetaResidual610 L A B C0 D0 E0 P Q R S0 U0) = 0)
    (heta : d (etaResidual610 L A B C0 D0 E0 P Q R S0 T0 V0) = 0)
    (htheta : d (thetaResidual610 L A B C0 D0 E0 P Q R S0 T0 U0 W0) = 0)
    (hiota : d (iotaResidual610 L A B C0 D0 E0 P Q R S0 T0 U0 V0 X0) = 0)
    (hkappa : d (kappaResidual610 L A B C0 D0 E0 P Q R S0 T0 U0 V0 W0) = 0)
    (hlambda : d (lambdaResidual610 L A B C0 D0 E0 P Q R S0 T0 U0 V0 W0) = 0)
    (hmu : d (muResidual610 L A B C0 D0 E0 P Q R S0 T0 U0 V0 W0) = 0) :
    d (degreeZeroPrimitive610 L A B C0 D0 E0 P Q R S0 T0 U0 V0 W0 X0) =
      W0 * d E0 - D0 * d X0 := by
  rw [degreeZeroPrimitive610_deriv_identity d L A B C0 D0 E0 P Q R S0 T0 U0 V0 W0 X0]
  rw [hL, halpha, hbeta, hgamma, hdelta, hepsilon, hzeta, heta, htheta,
    hiota, hkappa, hlambda, hmu]
  ring

end DifferentialCertificate

#print axioms degreeZeroPrimitive610_deriv_identity
#print axioms degreeZeroPrimitive610_deriv_eq_row

end DegreeZeroPrimitive610

end Max11DegreeRoutes
