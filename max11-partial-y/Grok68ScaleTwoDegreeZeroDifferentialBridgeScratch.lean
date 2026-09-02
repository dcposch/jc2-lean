import Grok68ScaleTwoDegreeZeroPrimitiveScratch
import LowScale68SourceBridge

/-! # Differential-Jacobian bridge for the `(6,8)` degree-zero primitive

Lane P1 of `Grok68AlignedSquareTowerPlanScratch.md`.  The weight-13
primitive is inhomogeneous: its derivative is the constant coefficient
`U * dE - D * dV` of the depressed differential Jacobian, rather than
zero.  This module records the residual-tower transport of that row.

CAS job `20260902T115530Z-68-degree-zero-h0-row-51785` confirms the
identity `d(rho) = U dE - D dV` modulo rows `h11` through `h2`, using
the grouped primitive of job `20260902T110334Z-68-degree-zero-93934`.
The next unused Jacobian row is `h1`.  No source clearing, pole order,
or chamber closure is claimed.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000

section DegreeZeroCertificates68

variable {F : Type*} [Field F] [CharZero F]

/-- Multiplier of `d(alphaResidual68)` in the free transport identity. -/
def degreeZeroAlphaCertificate68 (D E : F) : F :=
  D * E

def degreeZeroBetaCertificate68 (A B C0 D E : F) : F :=
  -(91 * A ^ 5 - 840 * A ^ 3 * C0 - 1260 * A ^ 2 * B ^ 2 +
      2160 * A ^ 2 * E + 4320 * A * B * D + 2160 * A * C0 ^ 2 +
      2160 * B ^ 2 * C0 - 25920 * C0 * E - 12960 * D ^ 2) / 31104

def degreeZeroGammaCertificate68 (A B C0 D E : F) : F :=
  (4 * A ^ 3 * B - 9 * A ^ 2 * D - 18 * A * B * C0 - 3 * B ^ 3 +
      54 * B * E + 54 * C0 * D) / 81

def degreeZeroDeltaCertificate68 (A B C0 D E : F) : F :=
  (A ^ 4 - 8 * A ^ 2 * C0 - 8 * A * B ^ 2 + 32 * A * E +
      32 * B * D + 16 * C0 ^ 2) / 64

def degreeZeroEpsilonCertificate68 (A B C0 D : F) : F :=
  -(A ^ 2 * B - 3 * A * D - 3 * B * C0) / 9

def degreeZeroZetaCertificate68 (A B C0 E : F) : F :=
  -(5 * A ^ 3 - 36 * A * C0 - 18 * B ^ 2 - 216 * E) / 216

/-- Multiplier of `d(etaResidual68)`.  The eta group of the primitive
vanishes, but the last octic residual still carries `dV`. -/
def degreeZeroEtaCertificate68 (D : F) : F :=
  D

def degreeZeroLCertificate68 (A B C0 D E : F) : F :=
  -7 * (187 * A ^ 6 - 1980 * A ^ 4 * C0 - 3960 * A ^ 3 * B ^ 2 +
      4320 * A ^ 3 * E + 12960 * A ^ 2 * B * D +
      6480 * A ^ 2 * C0 ^ 2 + 12960 * A * B ^ 2 * C0 -
      31104 * A * C0 * E - 15552 * A * D ^ 2 + 1080 * B ^ 4 -
      15552 * B ^ 2 * E - 31104 * B * C0 * D - 5184 * C0 ^ 3 -
      93312 * E ^ 2) / 1119744

end DegreeZeroCertificates68

section DegreeZeroIdentity68

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]

set_option maxHeartbeats 800000000 in
/-- Exact differential transport of the primitive.  After the old
residuals and the three first integrals are differential constants,
the derivative is the literal degree-zero Jacobian row `U dE - D dV`. -/
theorem degreeZeroPrimitive68_deriv_identity
    (d : Derivation k F F)
    (L A B C0 D E P Q R S T U V : F) :
    d (degreeZeroPrimitive68 L A B C0 D E P Q R S T U V) =
      (U * d E - D * d V) +
      degreeZeroFourGroup68 A C0 *
        d (firstIntegralFour68 L A B C0 D E
          (betaResidual68 L A B Q)
          (gammaResidual68 L A B C0 P R)
          (deltaResidual68 L A B C0 D P Q S)
          (epsilonResidual68 L A B C0 D E P Q R T)
          (zetaResidual68 L A B C0 D E P Q R S U)) +
      degreeZeroThreeGroup68 B *
        d (firstIntegralThree68 L A B C0 D E
          (betaResidual68 L A B Q)
          (gammaResidual68 L A B C0 P R)
          (deltaResidual68 L A B C0 D P Q S)
          (epsilonResidual68 L A B C0 D E P Q R T)
          (zetaResidual68 L A B C0 D E P Q R S U)) +
      degreeZeroTwoGroup68 A *
        d (firstIntegralTwo68 L A B C0 D E
          (betaResidual68 L A B Q)
          (gammaResidual68 L A B C0 P R)
          (deltaResidual68 L A B C0 D P Q S)
          (epsilonResidual68 L A B C0 D E P Q R T)
          (zetaResidual68 L A B C0 D E P Q R S U)) +
      degreeZeroLCertificate68 A B C0 D E * d L +
      degreeZeroAlphaCertificate68 D E * d (alphaResidual68 A P) +
      degreeZeroBetaCertificate68 A B C0 D E *
        d (betaResidual68 L A B Q) +
      degreeZeroGammaCertificate68 A B C0 D E *
        d (gammaResidual68 L A B C0 P R) +
      degreeZeroDeltaCertificate68 A B C0 D E *
        d (deltaResidual68 L A B C0 D P Q S) +
      degreeZeroEpsilonCertificate68 A B C0 D *
        d (epsilonResidual68 L A B C0 D E P Q R T) +
      degreeZeroZetaCertificate68 A B C0 E *
        d (zetaResidual68 L A B C0 D E P Q R S U) +
      degreeZeroEtaCertificate68 D *
        d (etaResidual68 L A B C0 D E P Q R S T V) := by
  have hd1 : d (1 : F) = 0 := by
    simpa only [Nat.cast_one] using d.map_natCast 1
  have hd_ofNat (n : ℕ) [Nat.AtLeastTwo n] :
      d (ofNat(n) : F) = 0 := by
    rw [← Nat.cast_ofNat]
    exact d.map_natCast n
  simp only [degreeZeroPrimitive68, degreeZeroBaseGroup68,
    degreeZeroBetaGroup68, degreeZeroGammaGroup68, degreeZeroDeltaGroup68,
    degreeZeroEpsilonGroup68, degreeZeroZetaGroup68,
    degreeZeroFourGroup68, degreeZeroThreeGroup68, degreeZeroTwoGroup68,
    degreeZeroLCertificate68, degreeZeroAlphaCertificate68,
    degreeZeroBetaCertificate68, degreeZeroGammaCertificate68,
    degreeZeroDeltaCertificate68, degreeZeroEpsilonCertificate68,
    degreeZeroZetaCertificate68, degreeZeroEtaCertificate68,
    firstIntegralFour68, firstIntegralThree68, firstIntegralTwo68,
    alphaResidual68, betaResidual68, gammaResidual68, deltaResidual68,
    epsilonResidual68, zetaResidual68, etaResidual68, map_add, map_sub,
    map_neg, Derivation.leibniz, Derivation.leibniz_div,
    Derivation.leibniz_pow, Derivation.leibniz_inv, nsmul_eq_mul,
    smul_eq_mul]
  simp only [hd1, hd_ofNat, derivation_ofNat_zero68 d, zero_mul, mul_zero,
    add_zero, zero_add, sub_zero]
  ring

/-- On the residual-constant locus, with the three first integrals
likewise constant, the primitive differentiates to the last Jacobian
row. -/
theorem degreeZeroPrimitive68_deriv_eq_row
    (d : Derivation k F F)
    (L A B C0 D E P Q R S T U V : F)
    (hL : d L = 0)
    (halpha : d (alphaResidual68 A P) = 0)
    (hbeta : d (betaResidual68 L A B Q) = 0)
    (hgamma : d (gammaResidual68 L A B C0 P R) = 0)
    (hdelta : d (deltaResidual68 L A B C0 D P Q S) = 0)
    (hepsilon : d (epsilonResidual68 L A B C0 D E P Q R T) = 0)
    (hzeta : d (zetaResidual68 L A B C0 D E P Q R S U) = 0)
    (heta : d (etaResidual68 L A B C0 D E P Q R S T V) = 0)
    (hI4 : d (firstIntegralFour68 L A B C0 D E
      (betaResidual68 L A B Q)
      (gammaResidual68 L A B C0 P R)
      (deltaResidual68 L A B C0 D P Q S)
      (epsilonResidual68 L A B C0 D E P Q R T)
      (zetaResidual68 L A B C0 D E P Q R S U)) = 0)
    (hI3 : d (firstIntegralThree68 L A B C0 D E
      (betaResidual68 L A B Q)
      (gammaResidual68 L A B C0 P R)
      (deltaResidual68 L A B C0 D P Q S)
      (epsilonResidual68 L A B C0 D E P Q R T)
      (zetaResidual68 L A B C0 D E P Q R S U)) = 0)
    (hI2 : d (firstIntegralTwo68 L A B C0 D E
      (betaResidual68 L A B Q)
      (gammaResidual68 L A B C0 P R)
      (deltaResidual68 L A B C0 D P Q S)
      (epsilonResidual68 L A B C0 D E P Q R T)
      (zetaResidual68 L A B C0 D E P Q R S U)) = 0) :
    d (degreeZeroPrimitive68 L A B C0 D E P Q R S T U V) =
      U * d E - D * d V := by
  rw [degreeZeroPrimitive68_deriv_identity d L A B C0 D E P Q R S T U V]
  rw [hL, halpha, hbeta, hgamma, hdelta, hepsilon, hzeta, heta, hI4, hI3,
    hI2]
  ring

end DegreeZeroIdentity68

section DegreeZeroDepressedRows68

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]

set_option maxHeartbeats 2000000 in
/-- The seven Faber residuals are differential constants as soon as the
upper Jacobian rows `h11` through `h5` vanish.  This is the row-wise
form of `depressedUpperResiduals_deriv_zero68`, which needs a constant
bracket rather than the individual upper rows. -/
theorem upperResiduals_deriv_zero68_of_rows
    (d : Derivation k F F)
    (L A B C0 D E P Q R S T U V : F)
    (hL : d L = 0)
    (h11 : (8 : F) * d A - 6 * d P = 0)
    (h10 : (7 : F) * L * d A + 8 * d B - 6 * d Q = 0)
    (h9 : (6 : F) * P * d A + 7 * L * d B + 8 * d C0 -
      4 * A * d P - 6 * d R = 0)
    (h8 : (5 : F) * Q * d A + 6 * P * d B + 7 * L * d C0 + 8 * d D -
      4 * A * d Q - 3 * B * d P - 6 * d S = 0)
    (h7 : (4 : F) * R * d A + 5 * Q * d B + 6 * P * d C0 + 7 * L * d D +
      8 * d E - 4 * A * d R - 3 * B * d Q - 2 * C0 * d P -
      6 * d T = 0)
    (h6 : (3 : F) * S * d A + 4 * R * d B + 5 * Q * d C0 + 6 * P * d D +
      7 * L * d E - 4 * A * d S - 3 * B * d R - 2 * C0 * d Q -
      D * d P - 6 * d U = 0)
    (h5 : (2 : F) * T * d A + 3 * S * d B + 4 * R * d C0 + 5 * Q * d D +
      6 * P * d E - 4 * A * d T - 3 * B * d S - 2 * C0 * d R -
      D * d Q - 6 * d V = 0) :
    d (alphaResidual68 A P) = 0 ∧
    d (betaResidual68 L A B Q) = 0 ∧
    d (gammaResidual68 L A B C0 P R) = 0 ∧
    d (deltaResidual68 L A B C0 D P Q S) = 0 ∧
    d (epsilonResidual68 L A B C0 D E P Q R T) = 0 ∧
    d (zetaResidual68 L A B C0 D E P Q R S U) = 0 ∧
    d (etaResidual68 L A B C0 D E P Q R S T V) = 0 := by
  have hc1 : d (1 : F) = 0 := by simpa only [Nat.cast_one] using d.map_natCast 1
  have hc2 : d (2 : F) = 0 := d.map_natCast 2
  have hc3 : d (3 : F) = 0 := d.map_natCast 3
  have hc4 : d (4 : F) = 0 := d.map_natCast 4
  have hc5 : d (5 : F) = 0 := d.map_natCast 5
  have hc6 : d (6 : F) = 0 := d.map_natCast 6
  have hc7 : d (7 : F) = 0 := d.map_natCast 7
  have hc9 : d (9 : F) = 0 := d.map_natCast 9
  have hc27 : d (27 : F) = 0 := d.map_natCast 27
  have hc35 : d (35 : F) = 0 := d.map_natCast 35
  have hc36 : d (36 : F) = 0 := d.map_natCast 36
  have hc72 : d (72 : F) = 0 := d.map_natCast 72
  have hc81 : d (81 : F) = 0 := d.map_natCast 81
  have hc243 : d (243 : F) = 0 := d.map_natCast 243
  have hc432 : d (432 : F) = 0 := d.map_natCast 432
  have hc1296 : d (1296 : F) = 0 := d.map_natCast 1296
  have hc12 : d (1 / 2 : F) = 0 := by
    simp [Derivation.leibniz_div, Derivation.leibniz_inv, hc1, hc2]
  have hc13 : d (1 / 3 : F) = 0 := by
    simp [Derivation.leibniz_div, Derivation.leibniz_inv, hc1, hc3]
  have hc19 : d (1 / 9 : F) = 0 := by
    simp [Derivation.leibniz_div, Derivation.leibniz_inv, hc1, hc9]
  have hcInv2 : d ((2 : F)⁻¹) = 0 := by
    simp [Derivation.leibniz_inv, hc2]
  have hcInv3 : d ((3 : F)⁻¹) = 0 := by
    simp [Derivation.leibniz_inv, hc3]
  have hcInv9 : d ((9 : F)⁻¹) = 0 := by
    simp [Derivation.leibniz_inv, hc9]
  have hPderiv : d P = (4 / 3 : F) * d A := by
    linear_combination (-1 / 6 : F) * h11
  have hQderiv : d Q = (7 / 6 : F) * L * d A + (4 / 3 : F) * d B := by
    linear_combination (-1 / 6 : F) * h10
  have hRderiv : d R = P * d A + (7 / 6 : F) * L * d B +
      (4 / 3 : F) * d C0 - (2 / 3 : F) * A * d P := by
    linear_combination (-1 / 6 : F) * h9
  have hSderiv : d S = (5 / 6 : F) * Q * d A + P * d B +
      (7 / 6 : F) * L * d C0 + (4 / 3 : F) * d D -
      (2 / 3 : F) * A * d Q - (1 / 2 : F) * B * d P := by
    linear_combination (-1 / 6 : F) * h8
  have hTderiv : d T = (2 / 3 : F) * R * d A + (5 / 6 : F) * Q * d B +
      P * d C0 + (7 / 6 : F) * L * d D + (4 / 3 : F) * d E -
      (2 / 3 : F) * A * d R - (1 / 2 : F) * B * d Q -
      (1 / 3 : F) * C0 * d P := by
    linear_combination (-1 / 6 : F) * h7
  have hUderiv : d U = (1 / 2 : F) * S * d A + (2 / 3 : F) * R * d B +
      (5 / 6 : F) * Q * d C0 + P * d D + (7 / 6 : F) * L * d E -
      (2 / 3 : F) * A * d S - (1 / 2 : F) * B * d R -
      (1 / 3 : F) * C0 * d Q - (1 / 6 : F) * D * d P := by
    linear_combination (-1 / 6 : F) * h6
  have hVderiv : d V = (1 / 3 : F) * T * d A + (1 / 2 : F) * S * d B +
      (2 / 3 : F) * R * d C0 + (5 / 6 : F) * Q * d D + P * d E -
      (2 / 3 : F) * A * d T - (1 / 2 : F) * B * d S -
      (1 / 3 : F) * C0 * d R - (1 / 6 : F) * D * d Q := by
    linear_combination (-1 / 6 : F) * h5
  have halpha : d (alphaResidual68 A P) = 0 := by
    simp only [alphaResidual68, map_sub, Derivation.leibniz,
      derivation_natDiv_zero68, smul_eq_mul, zero_mul, add_zero]
    rw [hPderiv]
    simp [Derivation.leibniz_div, hc1, hc2, hc3, hc4, hc5, hc6, hc7,
      hc9, hc27, hc35, hc36, hc72, hc81, hc243, hc432, hc1296,
      hc12, hc13, hc19] <;> ring
  have hbeta : d (betaResidual68 L A B Q) = 0 := by
    simp only [betaResidual68, map_sub, Derivation.leibniz,
      derivation_natDiv_zero68, hL, smul_eq_mul, zero_mul, add_zero,
      mul_zero, zero_add]
    rw [hQderiv]
    simp [Derivation.leibniz_div, hc1, hc2, hc3, hc4, hc5, hc6, hc7,
      hc9, hc27, hc35, hc36, hc72, hc81, hc243, hc432, hc1296,
      hc12, hc13, hc19] <;> ring
  have hgamma : d (gammaResidual68 L A B C0 P R) = 0 := by
    simp only [gammaResidual68, map_sub, map_add, Derivation.leibniz,
      Derivation.leibniz_pow, derivation_natDiv_zero68, hL, halpha,
      nsmul_eq_mul, smul_eq_mul, zero_mul, add_zero, mul_zero, zero_add]
    rw [hRderiv, hPderiv]
    simp only [alphaResidual68]
    simp [Derivation.leibniz_div, hc1, hc2, hc3, hc4, hc5, hc6, hc7,
      hc9, hc27, hc35, hc36, hc72, hc81, hc243, hc432, hc1296,
      hc12, hc13] <;> ring
  have hdelta : d (deltaResidual68 L A B C0 D P Q S) = 0 := by
    simp only [deltaResidual68, map_sub, map_add, Derivation.leibniz,
      Derivation.leibniz_pow, derivation_natDiv_zero68, hL, halpha, hbeta,
      nsmul_eq_mul, smul_eq_mul, zero_mul, add_zero, mul_zero, zero_add]
    rw [hSderiv, hPderiv, hQderiv]
    simp only [alphaResidual68, betaResidual68]
    simp [Derivation.leibniz_div, hc1, hc2, hc3, hc4, hc5, hc6, hc7,
      hc9, hc27, hc35, hc36, hc72, hc81, hc243, hc432, hc1296,
      hc12, hc13] <;> ring
  have hepsilon : d (epsilonResidual68 L A B C0 D E P Q R T) = 0 := by
    simp only [epsilonResidual68, map_sub, map_add, map_neg,
      Derivation.leibniz, Derivation.leibniz_pow, derivation_natDiv_zero68,
      hL, halpha, hbeta, hgamma, nsmul_eq_mul, smul_eq_mul, zero_mul,
      add_zero, mul_zero, zero_add]
    rw [hTderiv, hRderiv, hQderiv, hPderiv]
    simp only [alphaResidual68, betaResidual68, gammaResidual68]
    simp [Derivation.leibniz_div, hc1, hc2, hc3, hc4, hc5, hc6, hc7,
      hc9, hc27, hc35, hc36, hc72, hc81, hc243, hc432, hc1296,
      hc12, hc13] <;> ring
  have hzeta : d (zetaResidual68 L A B C0 D E P Q R S U) = 0 := by
    simp only [zetaResidual68, map_sub, map_add, map_neg,
      Derivation.leibniz, Derivation.leibniz_pow, derivation_natDiv_zero68,
      hL, halpha, hbeta, hgamma, hdelta, nsmul_eq_mul, smul_eq_mul,
      zero_mul, add_zero, mul_zero, zero_add]
    rw [hUderiv, hSderiv, hRderiv, hQderiv, hPderiv]
    simp only [alphaResidual68, betaResidual68, gammaResidual68,
      deltaResidual68]
    simp [Derivation.leibniz_div, hc1, hc2, hc3, hc4, hc5, hc6, hc7,
      hc9, hc27, hc35, hc36, hc72, hc81, hc243, hc432, hc1296,
      hc12, hc13, hc19]
    rw [hcInv2]
    ring
  have heta : d (etaResidual68 L A B C0 D E P Q R S T V) = 0 := by
    simp only [etaResidual68, map_sub, map_add, map_neg,
      Derivation.leibniz, Derivation.leibniz_pow, derivation_natDiv_zero68,
      hL, halpha, hbeta, hgamma, hdelta, hepsilon, nsmul_eq_mul,
      smul_eq_mul, zero_mul, add_zero, mul_zero, zero_add]
    rw [hVderiv, hTderiv, hSderiv, hRderiv, hQderiv, hPderiv]
    simp only [alphaResidual68, betaResidual68, gammaResidual68,
      deltaResidual68, epsilonResidual68]
    simp [Derivation.leibniz_div, hc1, hc2, hc3, hc4, hc5, hc6, hc7,
      hc9, hc27, hc35, hc36, hc72, hc81, hc243, hc432, hc1296,
      hc12, hc13, hc19]
    rw [hcInv2, hcInv3, hcInv9]
    ring
  exact ⟨halpha, hbeta, hgamma, hdelta, hepsilon, hzeta, heta⟩

/-- The residual tower transports rows `h11` through `h2` into the
literal degree-zero row.  Row `h1` is not used. -/
theorem degreeZeroPrimitive68_deriv_eq_row_of_depressed_rows
    (d : Derivation k F F)
    (L A B C0 D E P Q R S T U V : F)
    (hL : d L = 0)
    (h11 : (8 : F) * d A - 6 * d P = 0)
    (h10 : (7 : F) * L * d A + 8 * d B - 6 * d Q = 0)
    (h9 : (6 : F) * P * d A + 7 * L * d B + 8 * d C0 -
      4 * A * d P - 6 * d R = 0)
    (h8 : (5 : F) * Q * d A + 6 * P * d B + 7 * L * d C0 + 8 * d D -
      4 * A * d Q - 3 * B * d P - 6 * d S = 0)
    (h7 : (4 : F) * R * d A + 5 * Q * d B + 6 * P * d C0 + 7 * L * d D +
      8 * d E - 4 * A * d R - 3 * B * d Q - 2 * C0 * d P -
      6 * d T = 0)
    (h6 : (3 : F) * S * d A + 4 * R * d B + 5 * Q * d C0 + 6 * P * d D +
      7 * L * d E - 4 * A * d S - 3 * B * d R - 2 * C0 * d Q -
      D * d P - 6 * d U = 0)
    (h5 : (2 : F) * T * d A + 3 * S * d B + 4 * R * d C0 + 5 * Q * d D +
      6 * P * d E - 4 * A * d T - 3 * B * d S - 2 * C0 * d R -
      D * d Q - 6 * d V = 0)
    (h4 : U * d A + 2 * T * d B + 3 * S * d C0 + 4 * R * d D +
      5 * Q * d E - 4 * A * d U - 3 * B * d T - 2 * C0 * d S -
      D * d R = 0)
    (h3 : U * d B + 2 * T * d C0 + 3 * S * d D + 4 * R * d E -
      4 * A * d V - 3 * B * d U - 2 * C0 * d T - D * d S = 0)
    (h2 : U * d C0 + 2 * T * d D + 3 * S * d E - 3 * B * d V -
      2 * C0 * d U - D * d T = 0) :
    d (degreeZeroPrimitive68 L A B C0 D E P Q R S T U V) =
      U * d E - D * d V := by
  rcases upperResiduals_deriv_zero68_of_rows d L A B C0 D E P Q R S T U V
      hL h11 h10 h9 h8 h7 h6 h5 with
    ⟨halpha, hbeta, hgamma, hdelta, hepsilon, hzeta, heta⟩
  have hrec := reconstructOcticCoefficients68 L P Q R S T U V A B C0 D E
  dsimp only at hrec
  rcases hrec with ⟨_hPeq, hQeq, hReq, hSeq, hTeq, hUeq, hVeq⟩
  have hI4 := lowerRowFour_integrated68_eq_deriv d L A B C0 D E
    (alphaResidual68 A P) (betaResidual68 L A B Q)
    (gammaResidual68 L A B C0 P R)
    (deltaResidual68 L A B C0 D P Q S)
    (epsilonResidual68 L A B C0 D E P Q R T)
    (zetaResidual68 L A B C0 D E P Q R S U)
    hL halpha hbeta hgamma hdelta hepsilon hzeta
  dsimp only at hI4
  rw [← hQeq, ← hReq, ← hSeq, ← hTeq, ← hUeq] at hI4
  have hI3 := lowerRowThree_integrated68_eq_deriv d L A B C0 D E
    (alphaResidual68 A P) (betaResidual68 L A B Q)
    (gammaResidual68 L A B C0 P R)
    (deltaResidual68 L A B C0 D P Q S)
    (epsilonResidual68 L A B C0 D E P Q R T)
    (zetaResidual68 L A B C0 D E P Q R S U)
    (etaResidual68 L A B C0 D E P Q R S T V)
    hL halpha hbeta hgamma hdelta hepsilon hzeta heta
  dsimp only at hI3
  rw [← hReq, ← hSeq, ← hTeq, ← hUeq, ← hVeq] at hI3
  have hI2 := lowerRowTwo_integrated68_eq_deriv d L A B C0 D E
    (alphaResidual68 A P) (betaResidual68 L A B Q)
    (gammaResidual68 L A B C0 P R)
    (deltaResidual68 L A B C0 D P Q S)
    (epsilonResidual68 L A B C0 D E P Q R T)
    (zetaResidual68 L A B C0 D E P Q R S U)
    (etaResidual68 L A B C0 D E P Q R S T V)
    hL halpha hbeta hgamma hdelta hepsilon hzeta heta
  dsimp only at hI2
  rw [← hQeq, ← hReq, ← hSeq, ← hTeq, ← hUeq, ← hVeq] at hI2
  refine degreeZeroPrimitive68_deriv_eq_row d L A B C0 D E P Q R S T U V
    hL halpha hbeta hgamma hdelta hepsilon hzeta heta ?_ ?_ ?_
  · exact hI4.symm.trans h4
  · exact hI3.symm.trans h3
  · rw [← hI2, h2, h4]
    ring

end DegreeZeroDepressedRows68

section DegreeZeroMonicBridge68

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]

/-- A constant depressed monic differential Jacobian makes the
degree-zero primitive differentiate to that same constant. -/
theorem degreeZeroPrimitive68_deriv_eq_constant_of_monic_differentialJacobian
    (d : Derivation k F F)
    (L A B C0 D E P Q R S T U V c : F)
    (hL : d L = 0)
    (hjac : differentialJacobian d (depressedSextic68 A B C0 D E)
        (depressedOctic68 L P Q R S T U V) = Polynomial.C c) :
    d (degreeZeroPrimitive68 L A B C0 D E P Q R S T U V) = c := by
  rcases depressedUpperRows68 d L P Q R S T U V A B C0 D E c hL hjac with
    ⟨h11, h10, h9, h8, h7, h6, h5⟩
  rcases depressedLowerRows68 d L P Q R S T U V A B C0 D E c hL hjac with
    ⟨h4, h3, h2, _h1, h0⟩
  have hrow := degreeZeroPrimitive68_deriv_eq_row_of_depressed_rows d
    L A B C0 D E P Q R S T U V hL
    (by linear_combination h11) (by linear_combination h10)
    (by linear_combination h9) (by linear_combination h8)
    (by linear_combination h7) (by linear_combination h6)
    (by linear_combination h5) (by linear_combination h4)
    (by linear_combination h3) (by linear_combination h2)
  exact hrow.trans h0

#print axioms degreeZeroPrimitive68_deriv_identity
#print axioms degreeZeroPrimitive68_deriv_eq_row_of_depressed_rows
#print axioms degreeZeroPrimitive68_deriv_eq_constant_of_monic_differentialJacobian

end DegreeZeroMonicBridge68

section DegreeZeroRatFuncBridge68

variable {k : Type*} [Field k] [CharZero k]

/-- Explicit ordinary-derivative specialization of the monic bridge.
The affine source depression supplies precisely the displayed simple
pole as its constant outer-polynomial coefficient, matching
`SquareZeroLIntegratedLocalRootData68.source.bracket_eq`. -/
theorem degreeZeroPrimitive68_ratFuncDeriv_eq_simplePole
    (L A B C0 D E P Q R S T U V : RatFunc k) (j : k) (h : RatFunc k)
    (hL : ratFuncDerivation68 L = 0)
    (hjac : differentialJacobian ratFuncDerivation68
        (depressedSextic68 A B C0 D E)
        (depressedOctic68 L P Q R S T U V) =
      Polynomial.C (RatFunc.C j / h)) :
    Differential.deriv
        (degreeZeroPrimitive68 L A B C0 D E P Q R S T U V) =
      RatFunc.C j / h := by
  simpa only [ratFuncDerivation68, ratFuncDerivation46_apply] using
    degreeZeroPrimitive68_deriv_eq_constant_of_monic_differentialJacobian
      ratFuncDerivation68 L A B C0 D E P Q R S T U V (RatFunc.C j / h)
      hL hjac

#print axioms degreeZeroPrimitive68_ratFuncDeriv_eq_simplePole

end DegreeZeroRatFuncBridge68

end Max11DegreeRoutes
