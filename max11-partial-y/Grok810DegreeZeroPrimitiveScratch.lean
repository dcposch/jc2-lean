import Sol810PiDifferentialBridgeScratch
import Grok810DegreeZeroRowScratch

/-! # Grouped primitive of the depressed `(8,10)` degree-zero row

Lane Z1 of the `(8,10)` chamber map, with the differential-bridge facts of
lane Z2.  After the Pi chain consumes degree `1`, coefficient `0` is the
unique unused Keller row.  This file records the grouped exact primitive
`ρ` produced by `derive_810_degree_zero_residual.py`: its derivative is
the literal degree-zero Jacobian row `W G' - F X'`, modulo the residual
tower `α` through `ο`.  The solved `d(π)` multiplier is identically zero,
so `π` is already a differential constant on this locus and does not
appear as a correction.

The old residuals remain their literal coordinate witnesses.  No source
clearing, pole order, or `h^{97}` jet is introduced.  Affine depression
to `C(j)/h₀` is left to a later source-wrapper lane.

Grouped-job command-source SHA256:
`bc53bb8db120bc997efe573cc42244236090e42f36a116f31ea4d874020bc340`.
Grouped-output SHA256:
`a05a73099a3eae9dd1c66b5f7a9d56ce922189d737c550be1adc6f0a2d940c78`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000

section DegreeZeroPrimitive810

variable {F : Type*} [Field F] [CharZero F]

def rhoBetaGroup810 (A B C0 D0 E0 F0 : F) : F :=
  (2601 * A ^ 7 - 24192 * A ^ 5 * C0 - 62748 * A ^ 4 * B ^ 2 +
      30912 * A ^ 4 * E0 + 139776 * A ^ 3 * B * D0 +
      69888 * A ^ 3 * C0 ^ 2 + 217728 * A ^ 2 * B ^ 2 * C0 -
      143360 * A ^ 2 * B * F0 - 157696 * A ^ 2 * C0 * E0 -
      86016 * A ^ 2 * D0 ^ 2 + 36288 * A * B ^ 4 -
      157696 * A * B ^ 2 * E0 - 344064 * A * B * C0 * D0 -
      57344 * A * C0 ^ 3 + 229376 * A * D0 * F0 +
      114688 * A * E0 ^ 2 - 57344 * B ^ 3 * D0 -
      93184 * B ^ 2 * C0 ^ 2 + 229376 * B * C0 * F0 +
      229376 * B * D0 * E0 + 114688 * C0 ^ 2 * E0 +
      114688 * C0 * D0 ^ 2 - 458752 * F0 ^ 2) /
    1048576

def rhoGammaGroup810 (A B C0 D0 E0 F0 : F) : F :=
  -(3 : F) *
    (255 * A ^ 5 * B - 336 * A ^ 4 * D0 - 1416 * A ^ 3 * B * C0 +
      352 * A ^ 3 * F0 - 720 * A ^ 2 * B ^ 3 + 1472 * A ^ 2 * B * E0 +
      1600 * A ^ 2 * C0 * D0 + 1600 * A * B ^ 2 * D0 +
      1664 * A * B * C0 ^ 2 - 1536 * A * C0 * F0 -
      2048 * A * D0 * E0 + 576 * B ^ 3 * C0 - 768 * B ^ 2 * F0 -
      2048 * B * C0 * E0 - 1024 * B * D0 ^ 2 - 1024 * C0 ^ 2 * D0 +
      4096 * E0 * F0) /
    16384

def rhoDeltaGroup810 (A B C0 D0 E0 F0 : F) : F :=
  -(5 : F) *
    (561 * A ^ 6 - 4464 * A ^ 4 * C0 - 9360 * A ^ 3 * B ^ 2 +
      5376 * A ^ 3 * E0 + 19968 * A ^ 2 * B * D0 +
      9984 * A ^ 2 * C0 ^ 2 + 20736 * A * B ^ 2 * C0 -
      16384 * A * B * F0 - 20480 * A * C0 * E0 - 12288 * A * D0 ^ 2 +
      1728 * B ^ 4 - 10240 * B ^ 2 * E0 - 24576 * B * C0 * D0 -
      4096 * C0 ^ 3 + 32768 * D0 * F0 + 16384 * E0 ^ 2) /
    262144

def rhoEpsilonGroup810 (A B C0 D0 E0 F0 : F) : F :=
  (51 * A ^ 4 * B - 66 * A ^ 3 * D0 - 216 * A ^ 2 * B * C0 +
      80 * A ^ 2 * F0 - 72 * A * B ^ 3 + 192 * A * B * E0 +
      224 * A * C0 * D0 + 112 * B ^ 2 * D0 + 128 * B * C0 ^ 2 -
      256 * C0 * F0 - 256 * D0 * E0) /
    512

def rhoZetaGroup810 (A B C0 D0 E0 F0 : F) : F :=
  (3 : F) *
    (51 * A ^ 5 - 336 * A ^ 3 * C0 - 540 * A ^ 2 * B ^ 2 +
      448 * A ^ 2 * E0 + 1024 * A * B * D0 + 512 * A * C0 ^ 2 +
      576 * B ^ 2 * C0 - 1024 * B * F0 - 1024 * C0 * E0 -
      512 * D0 ^ 2) /
    8192

def rhoEtaGroup810 (A B C0 D0 E0 F0 : F) : F :=
  -(51 * A ^ 3 * B - 72 * A ^ 2 * D0 - 144 * A * B * C0 +
      128 * A * F0 - 24 * B ^ 3 + 128 * B * E0 + 128 * C0 * D0) /
    512

def rhoThetaGroup810 (A B C0 D0 E0 G0 : F) : F :=
  -(51 * A ^ 4 - 288 * A ^ 2 * C0 - 288 * A * B ^ 2 + 512 * A * E0 +
      512 * B * D0 + 256 * C0 ^ 2 - 4096 * G0) /
    4096

def rhoBaseGroup810 (L A B C0 D0 E0 F0 G0 : F) : F :=
  (369495 * A ^ 8 * L + 5026560 * A ^ 7 * B - 3931200 * A ^ 6 * C0 * L -
      6666240 * A ^ 6 * D0 - 12156480 * A ^ 5 * B ^ 2 * L -
      41287680 * A ^ 5 * B * C0 + 5096448 * A ^ 5 * E0 * L +
      8437760 * A ^ 5 * F0 - 35051520 * A ^ 4 * B ^ 3 +
      27933696 * A ^ 4 * B * D0 * L + 46694400 * A ^ 4 * B * E0 +
      13966848 * A ^ 4 * C0 ^ 2 * L + 48988160 * A ^ 4 * C0 * D0 -
      3760128 * A ^ 4 * G0 * L + 57673728 * A ^ 3 * B ^ 2 * C0 * L +
      100188160 * A ^ 3 * B ^ 2 * D0 + 101335040 * A ^ 3 * B * C0 ^ 2 -
      30081024 * A ^ 3 * B * F0 * L - 33423360 * A ^ 3 * B * G0 -
      32145408 * A ^ 3 * C0 * E0 * L - 55705600 * A ^ 3 * C0 * F0 -
      17104896 * A ^ 3 * D0 ^ 2 * L - 59637760 * A ^ 3 * D0 * E0 +
      14515200 * A ^ 2 * B ^ 4 * L + 103219200 * A ^ 2 * B ^ 3 * C0 -
      49545216 * A ^ 2 * B ^ 2 * E0 * L - 86507520 * A ^ 2 * B ^ 2 * F0 -
      105283584 * A ^ 2 * B * C0 * D0 * L -
      184811520 * A ^ 2 * B * C0 * E0 - 96337920 * A ^ 2 * B * D0 ^ 2 -
      17547264 * A ^ 2 * C0 ^ 3 * L - 96337920 * A ^ 2 * C0 ^ 2 * D0 +
      21233664 * A ^ 2 * C0 * G0 * L + 42467328 * A ^ 2 * D0 * F0 * L +
      47185920 * A ^ 2 * D0 * G0 + 21233664 * A ^ 2 * E0 ^ 2 * L +
      78643200 * A ^ 2 * E0 * F0 + 10321920 * A * B ^ 5 -
      35094528 * A * B ^ 3 * D0 * L - 61603840 * A * B ^ 3 * E0 -
      54706176 * A * B ^ 2 * C0 ^ 2 * L -
      196608000 * A * B ^ 2 * C0 * D0 + 21233664 * A * B ^ 2 * G0 * L -
      66846720 * A * B * C0 ^ 3 + 84934656 * A * B * C0 * F0 * L +
      94371840 * A * B * C0 * G0 + 89653248 * A * B * D0 * E0 * L +
      167772160 * A * B * D0 * F0 + 83886080 * A * B * E0 ^ 2 +
      44826624 * A * C0 ^ 2 * E0 * L + 83886080 * A * C0 ^ 2 * F0 +
      47185920 * A * C0 * D0 ^ 2 * L + 178257920 * A * C0 * D0 * E0 +
      31457280 * A * D0 ^ 3 - 37748736 * A * E0 * G0 * L -
      37748736 * A * F0 ^ 2 * L - 83886080 * A * F0 * G0 -
      9289728 * B ^ 4 * C0 * L - 16384000 * B ^ 4 * D0 -
      34734080 * B ^ 3 * C0 ^ 2 + 14155776 * B ^ 3 * F0 * L +
      15728640 * B ^ 3 * G0 + 47185920 * B ^ 2 * C0 * E0 * L +
      89128960 * B ^ 2 * C0 * F0 + 23592960 * B ^ 2 * D0 ^ 2 * L +
      89128960 * B ^ 2 * D0 * E0 + 49545216 * B * C0 ^ 2 * D0 * L +
      94371840 * B * C0 ^ 2 * E0 + 94371840 * B * C0 * D0 ^ 2 -
      37748736 * B * D0 * G0 * L - 75497472 * B * E0 * F0 * L -
      83886080 * B * E0 * G0 - 83886080 * B * F0 ^ 2 +
      4128768 * C0 ^ 4 * L + 31457280 * C0 ^ 3 * D0 -
      18874368 * C0 ^ 2 * G0 * L - 75497472 * C0 * D0 * F0 * L -
      83886080 * C0 * D0 * G0 - 37748736 * C0 * E0 ^ 2 * L -
      167772160 * C0 * E0 * F0 - 37748736 * D0 ^ 2 * E0 * L -
      83886080 * D0 ^ 2 * F0 - 83886080 * D0 * E0 ^ 2 +
      150994944 * G0 ^ 2 * L) /
    268435456

/-- CAS-grouped primitive of the degree-zero row.  Earlier residuals remain
literal functions of the original depressed coordinates. -/
def rhoResidual810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : F) : F :=
  rhoBaseGroup810 L A B C0 D0 E0 F0 G0 +
    betaResidual810 L A B Q * rhoBetaGroup810 A B C0 D0 E0 F0 +
    gammaResidual810 L A B C0 P R * rhoGammaGroup810 A B C0 D0 E0 F0 +
    deltaResidual810 L A B C0 D0 P Q S0 *
      rhoDeltaGroup810 A B C0 D0 E0 F0 +
    epsilonResidual810 L A B C0 D0 E0 P Q R T0 *
      rhoEpsilonGroup810 A B C0 D0 E0 F0 +
    zetaResidual810 L A B C0 D0 E0 F0 P Q R S0 U0 *
      rhoZetaGroup810 A B C0 D0 E0 F0 +
    etaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 V0 *
      rhoEtaGroup810 A B C0 D0 E0 F0 +
    thetaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 W0 *
      rhoThetaGroup810 A B C0 D0 E0 G0

/-! The following factored coefficients are the exact triangular certificate
which transports the native coordinates `P,...,X` to the residual witnesses.
They were independently reconstructed from the native residual definitions;
the leftover coefficient is identically zero. -/

def rhoAlphaCertificate810 (F0 G0 : F) : F :=
  F0 * G0

def rhoBetaCertificate810 (A B C0 D0 E0 F0 G0 : F) : F :=
  -(2805 * A ^ 7 - 28560 * A ^ 5 * C0 - 71400 * A ^ 4 * B ^ 2 +
      45696 * A ^ 4 * E0 + 182784 * A ^ 3 * B * D0 +
      91392 * A ^ 3 * C0 ^ 2 - 86016 * A ^ 3 * G0 +
      274176 * A ^ 2 * B ^ 2 * C0 - 258048 * A ^ 2 * B * F0 -
      258048 * A ^ 2 * C0 * E0 - 129024 * A ^ 2 * D0 ^ 2 +
      45696 * A * B ^ 4 - 258048 * A * B ^ 2 * E0 -
      516096 * A * B * C0 * D0 - 86016 * A * C0 ^ 3 +
      458752 * A * C0 * G0 + 458752 * A * D0 * F0 +
      229376 * A * E0 ^ 2 - 86016 * B ^ 3 * D0 -
      129024 * B ^ 2 * C0 ^ 2 + 229376 * B ^ 2 * G0 +
      458752 * B * C0 * F0 + 458752 * B * D0 * E0 +
      229376 * C0 ^ 2 * E0 + 229376 * C0 * D0 ^ 2 -
      3670016 * E0 * G0 - 1835008 * F0 ^ 2) /
    4194304

def rhoGammaCertificate810 (A B C0 D0 E0 F0 G0 : F) : F :=
  (117 * A ^ 5 * B - 180 * A ^ 4 * D0 - 720 * A ^ 3 * B * C0 +
      320 * A ^ 3 * F0 - 360 * A ^ 2 * B ^ 3 + 960 * A ^ 2 * B * E0 +
      960 * A ^ 2 * C0 * D0 + 960 * A * B ^ 2 * D0 +
      960 * A * B * C0 ^ 2 - 1536 * A * B * G0 - 1536 * A * C0 * F0 -
      1536 * A * D0 * E0 + 320 * B ^ 3 * C0 - 768 * B ^ 2 * F0 -
      1536 * B * C0 * E0 - 768 * B * D0 ^ 2 - 768 * C0 ^ 2 * D0 +
      6144 * D0 * G0 + 6144 * E0 * F0) /
    8192

def rhoDeltaCertificate810 (A B C0 D0 E0 F0 G0 : F) : F :=
  (1881 * A ^ 6 - 16720 * A ^ 4 * C0 - 33440 * A ^ 3 * B ^ 2 +
      28160 * A ^ 3 * E0 + 84480 * A ^ 2 * B * D0 +
      42240 * A ^ 2 * C0 ^ 2 - 61440 * A ^ 2 * G0 +
      84480 * A * B ^ 2 * C0 - 122880 * A * B * F0 -
      122880 * A * C0 * E0 - 61440 * A * D0 ^ 2 + 7040 * B ^ 4 -
      61440 * B ^ 2 * E0 - 122880 * B * C0 * D0 - 20480 * C0 ^ 3 +
      327680 * C0 * G0 + 327680 * D0 * F0 + 163840 * E0 ^ 2) /
    524288

def rhoEpsilonCertificate810 (A B C0 D0 E0 F0 G0 : F) : F :=
  -(5 * A ^ 4 * B - 8 * A ^ 3 * D0 - 24 * A ^ 2 * B * C0 +
      16 * A ^ 2 * F0 - 8 * A * B ^ 3 + 32 * A * B * E0 +
      32 * A * C0 * D0 + 16 * B ^ 2 * D0 + 16 * B * C0 ^ 2 -
      64 * B * G0 - 64 * C0 * F0 - 64 * D0 * E0) /
    128

def rhoZetaCertificate810 (A B C0 D0 E0 F0 G0 : F) : F :=
  -(273 * A ^ 5 - 2080 * A ^ 3 * C0 - 3120 * A ^ 2 * B ^ 2 +
      3840 * A ^ 2 * E0 + 7680 * A * B * D0 + 3840 * A * C0 ^ 2 -
      12288 * A * G0 + 3840 * B ^ 2 * C0 - 12288 * B * F0 -
      12288 * C0 * E0 - 6144 * D0 ^ 2) /
    32768

def rhoEtaCertificate810 (A B C0 D0 E0 F0 : F) : F :=
  (7 * A ^ 3 * B - 12 * A ^ 2 * D0 - 24 * A * B * C0 + 32 * A * F0 -
      4 * B ^ 3 + 32 * B * E0 + 32 * C0 * D0) /
    128

def rhoThetaCertificate810 (A B C0 D0 E0 G0 : F) : F :=
  (35 * A ^ 4 - 224 * A ^ 2 * C0 - 224 * A * B ^ 2 + 512 * A * E0 +
      512 * B * D0 + 256 * C0 ^ 2 + 4096 * G0) /
    4096

def rhoIotaCertificate810 (F0 : F) : F := F0

def rhoLCertificate810 (A B C0 D0 E0 F0 G0 : F) : F :=
  -(3 : F) *
    (27807 * A ^ 8 - 319424 * A ^ 6 * C0 - 958272 * A ^ 5 * B ^ 2 +
      494592 * A ^ 5 * E0 + 2472960 * A ^ 4 * B * D0 +
      1236480 * A ^ 4 * C0 ^ 2 - 860160 * A ^ 4 * G0 +
      4945920 * A ^ 3 * B ^ 2 * C0 - 3440640 * A ^ 3 * B * F0 -
      3440640 * A ^ 3 * C0 * E0 - 1720320 * A ^ 3 * D0 ^ 2 +
      1236480 * A ^ 2 * B ^ 4 - 5160960 * A ^ 2 * B ^ 2 * E0 -
      10321920 * A ^ 2 * B * C0 * D0 - 1720320 * A ^ 2 * C0 ^ 3 +
      5505024 * A ^ 2 * C0 * G0 + 5505024 * A ^ 2 * D0 * F0 +
      2752512 * A ^ 2 * E0 ^ 2 - 3440640 * A * B ^ 3 * D0 -
      5160960 * A * B ^ 2 * C0 ^ 2 + 5505024 * A * B ^ 2 * G0 +
      11010048 * A * B * C0 * F0 + 11010048 * A * B * D0 * E0 +
      5505024 * A * C0 ^ 2 * E0 + 5505024 * A * C0 * D0 ^ 2 -
      12582912 * A * E0 * G0 - 6291456 * A * F0 ^ 2 -
      860160 * B ^ 4 * C0 + 1835008 * B ^ 3 * F0 +
      5505024 * B ^ 2 * C0 * E0 + 2752512 * B ^ 2 * D0 ^ 2 +
      5505024 * B * C0 ^ 2 * D0 - 12582912 * B * D0 * G0 -
      12582912 * B * E0 * F0 + 458752 * C0 ^ 4 -
      6291456 * C0 ^ 2 * G0 - 12582912 * C0 * D0 * F0 -
      6291456 * C0 * E0 ^ 2 - 6291456 * D0 ^ 2 * E0 -
      50331648 * G0 ^ 2) /
    268435456

section DerivativeCertificate

variable {k : Type*} [Field k] [Algebra k F]

set_option maxHeartbeats 800000000 in
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
  simp only [rhoResidual810, rhoBaseGroup810, rhoBetaGroup810,
    rhoGammaGroup810, rhoDeltaGroup810, rhoEpsilonGroup810, rhoZetaGroup810,
    rhoEtaGroup810, rhoThetaGroup810, rhoAlphaCertificate810,
    rhoBetaCertificate810, rhoGammaCertificate810, rhoDeltaCertificate810,
    rhoEpsilonCertificate810, rhoZetaCertificate810, rhoEtaCertificate810,
    rhoThetaCertificate810, rhoIotaCertificate810, rhoLCertificate810,
    kappaResidual810, muResidual810, nuResidual810, xiResidual810,
    omicronResidual810, alphaResidual810, betaResidual810, gammaResidual810,
    deltaResidual810, epsilonResidual810, zetaResidual810, etaResidual810,
    thetaResidual810, iotaResidual810, map_add, map_sub, map_neg,
    Derivation.leibniz, Derivation.leibniz_div, Derivation.leibniz_pow,
    nsmul_eq_mul]
  simp only [hd1, hd_ofNat, zero_mul, mul_zero, add_zero, zero_add, sub_zero]
  ring

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
  ring

/-- Lane Z2: on the residual-constant locus, `dρ = 0` if and only if the
degree-zero Jacobian coefficient vanishes. -/
theorem rhoResidual810_deriv_eq_zero_iff_row
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
    d (rhoResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0) = 0 ↔
      W0 * d G0 - F0 * d X0 = 0 := by
  rw [rhoResidual810_deriv_eq_row d L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 X0
    hL halpha hbeta hgamma hdelta hepsilon hzeta heta htheta hiota hkappa
    hmu hnu hxi homicron]

end DerivativeCertificate

end DegreeZeroPrimitive810

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

#print axioms rhoResidual810_deriv_identity
#print axioms rhoResidual810_deriv_eq_row
#print axioms rhoResidual810_deriv_eq_zero_iff_row
#print axioms rhoResidual810_deriv_eq_constant_of_monic_differentialJacobian

end Max11DegreeRoutes
