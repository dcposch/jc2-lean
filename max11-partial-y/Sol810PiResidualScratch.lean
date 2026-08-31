import Fable810ScaleZeroFourteenthDefectScratch

/-! # The pure degree-one integral for the depressed `(8,10)` pair

This is the grouped exact primitive produced by `derive_810_pi_residual.py`.
The seven old residuals are kept as their literal coordinate witnesses; no
source clearing is performed here.

Grouped-job command-source SHA256:
`1b51be27f83ca97f5cecb7ca2b211532c9024630077d41e0eda9fa272a934ab5`.
Certificate-audit generator SHA256:
`25e3507b2e2b674a6489443bd761bf3e7d7364fc23018661c0a3feda16d0f017`.
Grouped-output SHA256:
`b01d2559558ff23253f377873f84ea26a2253d7ecc9f021a4fd3f951ee972fe4`.
-/

noncomputable section

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000

section Depression810SixteenthIntegral

variable {F : Type*} [Field F] [CharZero F]

def piBetaGroup810 (A B C0 D0 E0 F0 : F) : F :=
  -(7 : F) *
    (255 * A ^ 5 * B - 336 * A ^ 4 * D0 - 1416 * A ^ 3 * B * C0 +
      352 * A ^ 3 * F0 - 720 * A ^ 2 * B ^ 3 +
      1472 * A ^ 2 * B * E0 + 1600 * A ^ 2 * C0 * D0 +
      1600 * A * B ^ 2 * D0 + 1664 * A * B * C0 ^ 2 -
      1536 * A * C0 * F0 - 2048 * A * D0 * E0 +
      576 * B ^ 3 * C0 - 768 * B ^ 2 * F0 - 2048 * B * C0 * E0 -
      1024 * B * D0 ^ 2 - 1024 * C0 ^ 2 * D0 + 4096 * E0 * F0) /
    32768

def piGammaGroup810 (A B C0 D0 E0 F0 : F) : F :=
  -(75 * A ^ 6 - 600 * A ^ 4 * C0 - 1200 * A ^ 3 * B ^ 2 +
      768 * A ^ 3 * E0 + 2496 * A ^ 2 * B * D0 +
      1344 * A ^ 2 * C0 ^ 2 + 2688 * A * B ^ 2 * C0 -
      1536 * A * B * F0 - 3072 * A * C0 * E0 - 1536 * A * D0 ^ 2 +
      240 * B ^ 4 - 1536 * B ^ 2 * E0 - 3072 * B * C0 * D0 -
      512 * C0 ^ 3 + 3072 * D0 * F0 + 3072 * E0 ^ 2) /
    4096

def piDeltaGroup810 (A B C0 D0 E0 F0 : F) : F :=
  5 * (165 * A ^ 4 * B - 216 * A ^ 3 * D0 - 696 * A ^ 2 * B * C0 +
      160 * A ^ 2 * F0 - 240 * A * B ^ 3 + 640 * A * B * E0 +
      768 * A * C0 * D0 + 384 * B ^ 2 * D0 + 384 * B * C0 ^ 2 -
      512 * C0 * F0 - 1024 * D0 * E0) /
    4096

def piEpsilonGroup810 (A B C0 D0 E0 F0 : F) : F :=
  (3 * A ^ 5 - 20 * A ^ 3 * C0 - 30 * A ^ 2 * B ^ 2 +
      24 * A ^ 2 * E0 + 56 * A * B * D0 + 32 * A * C0 ^ 2 +
      32 * B ^ 2 * C0 - 32 * B * F0 - 64 * C0 * E0 - 32 * D0 ^ 2) /
    64

def piZetaGroup810 (A B C0 D0 E0 F0 : F) : F :=
  -(75 * A ^ 3 * B - 96 * A ^ 2 * D0 - 216 * A * B * C0 +
      96 * A * F0 - 40 * B ^ 3 + 192 * B * E0 +
      192 * C0 * D0) /
    256

def piEtaGroup810 (A B C0 D0 E0 G0 : F) : F :=
  -(15 * A ^ 4 - 80 * A ^ 2 * C0 - 80 * A * B ^ 2 +
      128 * A * E0 + 128 * B * D0 + 64 * C0 ^ 2 - 512 * G0) /
    256

def piThetaGroup810 (A B C0 D0 F0 : F) : F :=
  (5 * A ^ 2 * B - 8 * A * D0 - 8 * B * C0 + 32 * F0) / 32

def piBaseGroup810 (L A B C0 D0 E0 F0 G0 : F) : F :=
  (5775 * A ^ 8 - 36225 * A ^ 6 * B * L - 61600 * A ^ 6 * C0 -
      184800 * A ^ 5 * B ^ 2 + 47880 * A ^ 5 * D0 * L +
      80640 * A ^ 5 * E0 + 249480 * A ^ 4 * B * C0 * L +
      421120 * A ^ 4 * B * D0 + 219520 * A ^ 4 * C0 ^ 2 -
      54432 * A ^ 4 * F0 * L - 76800 * A ^ 4 * G0 +
      168000 * A ^ 3 * B ^ 3 * L + 878080 * A ^ 3 * B ^ 2 * C0 -
      274176 * A ^ 3 * B * E0 * L - 409600 * A ^ 3 * B * F0 -
      290304 * A ^ 3 * C0 * D0 * L - 512000 * A ^ 3 * C0 * E0 -
      256000 * A ^ 3 * D0 ^ 2 + 224000 * A ^ 2 * B ^ 4 -
      435456 * A ^ 2 * B ^ 2 * D0 * L - 768000 * A ^ 2 * B ^ 2 * E0 -
      451584 * A ^ 2 * B * C0 ^ 2 * L - 1597440 * A ^ 2 * B * C0 * D0 +
      184320 * A ^ 2 * B * G0 * L - 276480 * A ^ 2 * C0 ^ 3 +
      285696 * A ^ 2 * C0 * F0 * L + 409600 * A ^ 2 * C0 * G0 +
      350208 * A ^ 2 * D0 * E0 * L + 532480 * A ^ 2 * D0 * F0 +
      327680 * A ^ 2 * E0 ^ 2 - 306432 * A * B ^ 3 * C0 * L -
      542720 * A * B ^ 3 * D0 - 829440 * A * B ^ 2 * C0 ^ 2 +
      285696 * A * B ^ 2 * F0 * L + 409600 * A * B ^ 2 * G0 +
      737280 * A * B * C0 * E0 * L + 1146880 * A * B * C0 * F0 +
      368640 * A * B * D0 ^ 2 * L + 1392640 * A * B * D0 * E0 +
      387072 * A * C0 ^ 2 * D0 * L + 737280 * A * C0 ^ 2 * E0 +
      737280 * A * C0 * D0 ^ 2 - 294912 * A * D0 * G0 * L -
      442368 * A * E0 * F0 * L - 655360 * A * E0 * G0 -
      327680 * A * F0 ^ 2 - 16128 * B ^ 5 * L - 143360 * B ^ 4 * C0 +
      129024 * B ^ 3 * E0 * L + 204800 * B ^ 3 * F0 +
      387072 * B ^ 2 * C0 * D0 * L + 737280 * B ^ 2 * C0 * E0 +
      368640 * B ^ 2 * D0 ^ 2 + 129024 * B * C0 ^ 3 * L +
      737280 * B * C0 ^ 2 * D0 - 294912 * B * C0 * G0 * L -
      442368 * B * D0 * F0 * L - 655360 * B * D0 * G0 -
      294912 * B * E0 ^ 2 * L - 983040 * B * E0 * F0 +
      61440 * C0 ^ 4 - 221184 * C0 ^ 2 * F0 * L -
      327680 * C0 ^ 2 * G0 - 589824 * C0 * D0 * E0 * L -
      983040 * C0 * D0 * F0 - 655360 * C0 * E0 ^ 2 -
      98304 * D0 ^ 3 * L - 655360 * D0 ^ 2 * E0 +
      1179648 * F0 * G0 * L + 1310720 * G0 ^ 2) /
    1048576

/-- CAS-grouped primitive of the degree-one row.  Earlier residuals remain
literal functions of the original depressed coordinates. -/
def piResidual810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : F) : F :=
  piBaseGroup810 L A B C0 D0 E0 F0 G0 +
    betaResidual810 L A B Q * piBetaGroup810 A B C0 D0 E0 F0 +
    gammaResidual810 L A B C0 P R * piGammaGroup810 A B C0 D0 E0 F0 +
    deltaResidual810 L A B C0 D0 P Q S0 *
      piDeltaGroup810 A B C0 D0 E0 F0 +
    epsilonResidual810 L A B C0 D0 E0 P Q R T0 *
      piEpsilonGroup810 A B C0 D0 E0 F0 +
    zetaResidual810 L A B C0 D0 E0 F0 P Q R S0 U0 *
      piZetaGroup810 A B C0 D0 E0 F0 +
    etaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 V0 *
      piEtaGroup810 A B C0 D0 E0 G0 +
    thetaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 W0 *
      piThetaGroup810 A B C0 D0 F0

/-! The following factored coefficients are the exact triangular certificate
which transports the native coordinates `P,...,X` to the residual witnesses.
They were independently reconstructed from the native residual definitions;
the leftover coefficient is identically zero. -/

def piAlphaCertificate810 (E0 F0 G0 : F) : F :=
  2 * E0 * G0 + F0 ^ 2

def piBetaCertificate810 (A B C0 D0 E0 F0 G0 : F) : F :=
  7 * (255 * A ^ 5 * B - 408 * A ^ 4 * D0 -
      1632 * A ^ 3 * B * C0 + 768 * A ^ 3 * F0 -
      816 * A ^ 2 * B ^ 3 + 2304 * A ^ 2 * B * E0 +
      2304 * A ^ 2 * C0 * D0 + 2304 * A * B ^ 2 * D0 +
      2304 * A * B * C0 ^ 2 - 4096 * A * B * G0 -
      4096 * A * C0 * F0 - 4096 * A * D0 * E0 +
      768 * B ^ 3 * C0 - 2048 * B ^ 2 * F0 -
      4096 * B * C0 * E0 - 2048 * B * D0 ^ 2 -
      2048 * C0 ^ 2 * D0 + 32768 * D0 * G0 + 32768 * E0 * F0) /
    131072

def piGammaCertificate810 (A B C0 D0 E0 F0 G0 : F) : F :=
  (39 * A ^ 6 - 360 * A ^ 4 * C0 - 720 * A ^ 3 * B ^ 2 +
      640 * A ^ 3 * E0 + 1920 * A ^ 2 * B * D0 +
      960 * A ^ 2 * C0 ^ 2 - 1536 * A ^ 2 * G0 +
      1920 * A * B ^ 2 * C0 - 3072 * A * B * F0 -
      3072 * A * C0 * E0 - 1536 * A * D0 ^ 2 + 160 * B ^ 4 -
      1536 * B ^ 2 * E0 - 3072 * B * C0 * D0 - 512 * C0 ^ 3 +
      12288 * C0 * G0 + 12288 * D0 * F0 + 6144 * E0 ^ 2) /
    8192

def piDeltaCertificate810 (A B C0 D0 E0 F0 G0 : F) : F :=
  -5 * (209 * A ^ 4 * B - 352 * A ^ 3 * D0 -
      1056 * A ^ 2 * B * C0 + 768 * A ^ 2 * F0 -
      352 * A * B ^ 3 + 1536 * A * B * E0 + 1536 * A * C0 * D0 +
      768 * B ^ 2 * D0 + 768 * B * C0 ^ 2 - 4096 * B * G0 -
      4096 * C0 * F0 - 4096 * D0 * E0) /
    16384

def piEpsilonCertificate810 (A B C0 D0 E0 F0 G0 : F) : F :=
  -(A ^ 5 - 8 * A ^ 3 * C0 - 12 * A ^ 2 * B ^ 2 +
      16 * A ^ 2 * E0 + 32 * A * B * D0 + 16 * A * C0 ^ 2 -
      64 * A * G0 + 16 * B ^ 2 * C0 - 64 * B * F0 -
      64 * C0 * E0 - 32 * D0 ^ 2) /
    64

def piZetaCertificate810 (A B C0 D0 E0 F0 : F) : F :=
  (65 * A ^ 3 * B - 120 * A ^ 2 * D0 - 240 * A * B * C0 +
      384 * A * F0 - 40 * B ^ 3 + 384 * B * E0 + 384 * C0 * D0) /
    512

def piEtaCertificate810 (A B C0 D0 E0 G0 : F) : F :=
  (7 * A ^ 4 - 48 * A ^ 2 * C0 - 48 * A * B ^ 2 +
      128 * A * E0 + 128 * B * D0 + 64 * C0 ^ 2 + 512 * G0) /
    256

def piThetaCertificate810 (A B C0 D0 F0 : F) : F :=
  -(7 * A ^ 2 * B - 16 * A * D0 - 16 * B * C0 - 128 * F0) / 64

def piIotaCertificate810 (E0 : F) : F := 2 * E0

def piLCertificate810 (A B C0 D0 E0 F0 G0 : F) : F :=
  3 * (4991 * A ^ 6 * B - 7728 * A ^ 5 * D0 -
      38640 * A ^ 4 * B * C0 + 13440 * A ^ 4 * F0 -
      25760 * A ^ 3 * B ^ 3 + 53760 * A ^ 3 * B * E0 +
      53760 * A ^ 3 * C0 * D0 + 80640 * A ^ 2 * B ^ 2 * D0 +
      80640 * A ^ 2 * B * C0 ^ 2 - 86016 * A ^ 2 * B * G0 -
      86016 * A ^ 2 * C0 * F0 - 86016 * A ^ 2 * D0 * E0 +
      53760 * A * B ^ 3 * C0 - 86016 * A * B ^ 2 * F0 -
      172032 * A * B * C0 * E0 - 86016 * A * B * D0 ^ 2 -
      86016 * A * C0 ^ 2 * D0 + 196608 * A * D0 * G0 +
      196608 * A * E0 * F0 + 2688 * B ^ 5 - 28672 * B ^ 3 * E0 -
      86016 * B ^ 2 * C0 * D0 - 28672 * B * C0 ^ 3 +
      196608 * B * C0 * G0 + 196608 * B * D0 * F0 +
      98304 * B * E0 ^ 2 + 98304 * C0 ^ 2 * F0 +
      196608 * C0 * D0 * E0 + 32768 * D0 ^ 3 + 1572864 * F0 * G0) /
    2097152

section DerivativeCertificate

variable {k : Type*} [Field k] [Algebra k F]

set_option maxHeartbeats 800000000 in
theorem piResidual810_deriv_identity
    (d : Derivation k F F)
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 X0 : F) :
    d (piResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0) =
      ((2 : F) * V0 * d G0 + W0 * d F0 - F0 * d W0 -
        (2 : F) * E0 * d X0) +
      ((A * B - 8 * D0) / 4) *
        d (kappaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0) +
      ((A ^ 2 - 8 * C0) / 4) *
        d (muResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0) -
      2 * B * d (nuResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0) -
      2 * A * d (xiResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0) +
      piLCertificate810 A B C0 D0 E0 F0 G0 * d L +
      piAlphaCertificate810 E0 F0 G0 * d (alphaResidual810 A P) +
      piBetaCertificate810 A B C0 D0 E0 F0 G0 *
        d (betaResidual810 L A B Q) +
      piGammaCertificate810 A B C0 D0 E0 F0 G0 *
        d (gammaResidual810 L A B C0 P R) +
      piDeltaCertificate810 A B C0 D0 E0 F0 G0 *
        d (deltaResidual810 L A B C0 D0 P Q S0) +
      piEpsilonCertificate810 A B C0 D0 E0 F0 G0 *
        d (epsilonResidual810 L A B C0 D0 E0 P Q R T0) +
      piZetaCertificate810 A B C0 D0 E0 F0 *
        d (zetaResidual810 L A B C0 D0 E0 F0 P Q R S0 U0) +
      piEtaCertificate810 A B C0 D0 E0 G0 *
        d (etaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 V0) +
      piThetaCertificate810 A B C0 D0 F0 *
        d (thetaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 W0) +
      piIotaCertificate810 E0 *
        d (iotaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 X0) := by
  -- `map_natCast` does not match `OfNat` atoms left by Leibniz.  The
  -- generic `ofNat` form is the one that closes every numeral (same
  -- two-pass as `degreeZeroPrimitive610_deriv_identity`).
  have hd1 : d (1 : F) = 0 := d.map_one_eq_zero
  have hd_ofNat (n : ℕ) [Nat.AtLeastTwo n] :
      d (ofNat(n) : F) = 0 := by
    rw [← Nat.cast_ofNat]
    exact d.map_natCast n
  simp only [piResidual810, piBaseGroup810, piBetaGroup810,
    piGammaGroup810, piDeltaGroup810, piEpsilonGroup810, piZetaGroup810,
    piEtaGroup810, piThetaGroup810, piAlphaCertificate810,
    piBetaCertificate810, piGammaCertificate810, piDeltaCertificate810,
    piEpsilonCertificate810, piZetaCertificate810, piEtaCertificate810,
    piThetaCertificate810, piIotaCertificate810, piLCertificate810,
    kappaResidual810, muResidual810, nuResidual810, xiResidual810,
    alphaResidual810, betaResidual810, gammaResidual810, deltaResidual810,
    epsilonResidual810, zetaResidual810, etaResidual810, thetaResidual810,
    iotaResidual810, map_add, map_sub, map_neg, Derivation.leibniz,
    Derivation.leibniz_div, Derivation.leibniz_pow, nsmul_eq_mul]
  simp only [hd1, hd_ofNat, zero_mul, mul_zero, add_zero, zero_add, sub_zero]
  ring

set_option maxHeartbeats 400000000 in
theorem piResidual810_deriv_zero
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
    (hrow : (2 : F) * V0 * d G0 + W0 * d F0 - F0 * d W0 -
      (2 : F) * E0 * d X0 = 0) :
    d (piResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0) = 0 := by
  rw [piResidual810_deriv_identity d L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 X0]
  rw [hrow, hkappa, hmu, hnu, hxi, hL, halpha, hbeta, hgamma, hdelta,
    hepsilon, hzeta, heta, htheta, hiota]
  ring

end DerivativeCertificate

#print axioms piResidual810_deriv_identity
#print axioms piResidual810_deriv_zero

end Depression810SixteenthIntegral

end Max11DegreeRoutes
