import Grok68ScaleTwoDegreeZeroPrimitiveScratch
import LowScale68SourceBridge

/-! # Aligned-square cleared numerator of the `(6,8)` weight-13 primitive

Lane C of `Grok68AlignedSquareTowerPlanScratch.md`.  Parent: the weight-13
primitive `degreeZeroPrimitive68` in
`Grok68ScaleTwoDegreeZeroPrimitiveScratch.lean`.  Model: the `(6,10)`
cleared-numerator bridge
(`alignedSquareJetQuotient610_map`, the MixedPair bars, and
`algebraMap N = h0^21 * (C scale * primitive)`), specialised to the
no-peel `(6,8)` arithmetic `step 5 * weight 13 = 65`.

On the aligned face `3 b₇ = 4 a₅ h₀²` one has `L = depressedL68 = 0`,
and every remaining depressed coefficient `X` of weight `w` satisfies
`(integer) · h^{5 w} · X = Xbar(h, aᵢ, bᵢ)` with `Xbar` polynomial.
Weighted homogeneity then clears the primitive as
`h^{65} · (scale · ρ)`.  The ordinary simple-pole derivative is a
hypothesis (lane P1); this file does not prove it and does not close the
chamber.

CAS job `20260902T114621Z-68-aligned-square-clearing-48447`
(`derive_68_aligned_square_clearing.py`, command-source SHA256
`a32c43754700c123975c357917a1efcc858375b4f102913da36baaf696b6c755`):

* thirteen bar identities, content-minimal integer scales
  `1, 12, 27, 144, 324, 46656, 9, 27, 216, 486, 11664, 11664, 1679616`
  for `L, A, B, C0, D, E, P, Q, R, S, T, U, V`;
* compact integer scale `5642219814912 = 2^{17} · 3^{16}` (`50` terms);
* source numerator `219` terms, `H_MIN = 0`, native ceiling `65`.

No pole-order, chamber-closure, or finite-root claim.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## Bookkeeping: weight, native clearing, ceiling, integer scale -/

/-- Weighted degree of the `(6,8)` degree-zero primitive. -/
def alignedSquarePrimitiveWeight68 : ℕ := 13

/-- Source `h`-adic step of one sextic depression depth: the centre is
`a₅/(6 h⁵)`. -/
def alignedSquareCoordinateClearingStep68 : ℕ := 5

/-- Source-homogeneous clearing of a weight-`13` polynomial in
coordinates of denominator `h^{5 d}`. -/
def alignedSquareSourceClearingPower68 : ℕ := 65

/-- Native tower ceiling of the weight-thirteen primitive (no peel). -/
def alignedSquareTowerCeiling68 : ℕ := 65

/-- Integer scale of the aligned-square compact numerator. -/
def alignedSquareGroupedIntegerScale68 : ℕ := 5642219814912

theorem alignedSquarePrimitiveWeight68_eq :
    alignedSquarePrimitiveWeight68 = 13 :=
  rfl

theorem alignedSquareCoordinateClearingStep68_eq :
    alignedSquareCoordinateClearingStep68 = 5 :=
  rfl

theorem alignedSquareSourceClearingPower68_eq :
    alignedSquareSourceClearingPower68 = 65 :=
  rfl

theorem alignedSquareTowerCeiling68_eq :
    alignedSquareTowerCeiling68 = 65 :=
  rfl

theorem alignedSquareGroupedIntegerScale68_eq :
    alignedSquareGroupedIntegerScale68 = 5642219814912 :=
  rfl

theorem alignedSquareSourceClearingPower68_eq_mul :
    alignedSquareSourceClearingPower68 =
      alignedSquareCoordinateClearingStep68 *
        alignedSquarePrimitiveWeight68 :=
  rfl

theorem alignedSquareTowerCeiling68_eq_clearing :
    alignedSquareTowerCeiling68 = alignedSquareSourceClearingPower68 :=
  rfl

theorem alignedSquareGroupedIntegerScale68_eq_pow :
    alignedSquareGroupedIntegerScale68 = 2 ^ 17 * 3 ^ 16 := by
  decide

#print axioms alignedSquareSourceClearingPower68_eq_mul
#print axioms alignedSquareTowerCeiling68_eq_clearing
#print axioms alignedSquareGroupedIntegerScale68_eq_pow

/-! ## Thirteen integer bars -/

section AlignedSquareBars68

variable {R : Type*} [CommRing R]

/-- The aligned septic coefficient vanishes. -/
def alignedSquareLBar68 (h a5 b7 : R) : R :=
  (0 : R)

/-- Polynomial numerator of `12 h¹⁰ A`. -/
def alignedSquareABar68 (h a5 a4 : R) : R :=
  (12 : R) * a4 * h ^ 6 - (5 : R) * a5 ^ 2

/-- Polynomial numerator of `27 h¹⁵ B`. -/
def alignedSquareBBar68 (h a5 a4 a3 : R) : R :=
  (27 : R) * a3 * h ^ 12 - (18 : R) * a4 * a5 * h ^ 6 + (5 : R) * a5 ^ 3

/-- Polynomial numerator of `144 h²⁰ C0`. -/
def alignedSquareCBar68 (h a5 a4 a3 a2 : R) : R :=
  (144 : R) * a2 * h ^ 18 - (72 : R) * a3 * a5 * h ^ 12 +
    (24 : R) * a4 * a5 ^ 2 * h ^ 6 - (5 : R) * a5 ^ 4

/-- Polynomial numerator of `324 h²⁵ D`. -/
def alignedSquareDBar68 (h a5 a4 a3 a2 a1 : R) : R :=
  (324 : R) * a1 * h ^ 24 - (108 : R) * a2 * a5 * h ^ 18 +
    (27 : R) * a3 * a5 ^ 2 * h ^ 12 - (6 : R) * a4 * a5 ^ 3 * h ^ 6 +
    a5 ^ 5

/-- Polynomial numerator of `46656 h³⁰ E`. -/
def alignedSquareEBar68 (h a5 a4 a3 a2 a1 a0 : R) : R :=
  (46656 : R) * a0 * h ^ 30 - (7776 : R) * a1 * a5 * h ^ 24 +
    (1296 : R) * a2 * a5 ^ 2 * h ^ 18 - (216 : R) * a3 * a5 ^ 3 * h ^ 12 +
    (36 : R) * a4 * a5 ^ 4 * h ^ 6 - (5 : R) * a5 ^ 6

/-- Polynomial numerator of `9 h¹⁰ P` on `3 b₇ = 4 a₅ h²`. -/
def alignedSquarePBar68 (h a5 b6 : R) : R :=
  (9 : R) * b6 * h ^ 4 - (7 : R) * a5 ^ 2

/-- Polynomial numerator of `27 h¹⁵ Q` on `3 b₇ = 4 a₅ h²`. -/
def alignedSquareQBar68 (h a5 b6 b5 : R) : R :=
  (27 : R) * b5 * h ^ 10 - (27 : R) * a5 * b6 * h ^ 4 + (14 : R) * a5 ^ 3

/-- Polynomial numerator of `216 h²⁰ R` on `3 b₇ = 4 a₅ h²`. -/
def alignedSquareRBar68 (h a5 b6 b5 b4 : R) : R :=
  (216 : R) * b4 * h ^ 16 - (180 : R) * a5 * b5 * h ^ 10 +
    (90 : R) * a5 ^ 2 * b6 * h ^ 4 - (35 : R) * a5 ^ 4

/-- Polynomial numerator of `486 h²⁵ S` on `3 b₇ = 4 a₅ h²`. -/
def alignedSquareSBar68 (h a5 b6 b5 b4 b3 : R) : R :=
  (486 : R) * b3 * h ^ 22 - (324 : R) * a5 * b4 * h ^ 16 +
    (135 : R) * a5 ^ 2 * b5 * h ^ 10 - (45 : R) * a5 ^ 3 * b6 * h ^ 4 +
    (14 : R) * a5 ^ 5

/-- Polynomial numerator of `11664 h³⁰ T` on `3 b₇ = 4 a₅ h²`. -/
def alignedSquareTBar68 (h a5 b6 b5 b4 b3 b2 : R) : R :=
  (11664 : R) * b2 * h ^ 28 - (5832 : R) * a5 * b3 * h ^ 22 +
    (1944 : R) * a5 ^ 2 * b4 * h ^ 16 - (540 : R) * a5 ^ 3 * b5 * h ^ 10 +
    (135 : R) * a5 ^ 4 * b6 * h ^ 4 - (35 : R) * a5 ^ 6

/-- Polynomial numerator of `11664 h³⁵ U` on `3 b₇ = 4 a₅ h²`. -/
def alignedSquareUBar68 (h a5 b6 b5 b4 b3 b2 b1 : R) : R :=
  (11664 : R) * b1 * h ^ 34 - (3888 : R) * a5 * b2 * h ^ 28 +
    (972 : R) * a5 ^ 2 * b3 * h ^ 22 - (216 : R) * a5 ^ 3 * b4 * h ^ 16 +
    (45 : R) * a5 ^ 4 * b5 * h ^ 10 - (9 : R) * a5 ^ 5 * b6 * h ^ 4 +
    (2 : R) * a5 ^ 7

/-- Polynomial numerator of `1679616 h⁴⁰ V` on `3 b₇ = 4 a₅ h²`. -/
def alignedSquareVBar68 (h a5 b6 b5 b4 b3 b2 b1 b0 : R) : R :=
  (1679616 : R) * b0 * h ^ 40 - (279936 : R) * a5 * b1 * h ^ 34 +
    (46656 : R) * a5 ^ 2 * b2 * h ^ 28 -
    (7776 : R) * a5 ^ 3 * b3 * h ^ 22 +
    (1296 : R) * a5 ^ 4 * b4 * h ^ 16 - (216 : R) * a5 ^ 5 * b5 * h ^ 10 +
    (36 : R) * a5 ^ 6 * b6 * h ^ 4 - (7 : R) * a5 ^ 8

end AlignedSquareBars68

section AlignedSquareBarIdentities68

variable {F : Type*} [Field F] [CharZero F]

theorem alignedSquare_b7_eq68
    (h a5 b7 : F) (haligned : (3 : F) * b7 = (4 : F) * a5 * h ^ 2) :
    b7 = (4 : F) * a5 * h ^ 2 / 3 := by
  have h3 : (3 : F) ≠ 0 := by norm_num
  rw [eq_div_iff_mul_eq h3, mul_comm]
  exact haligned

theorem alignedSquareLBar68_eq
    (h a5 b7 : F) (hh : h ≠ 0)
    (haligned : (3 : F) * b7 = (4 : F) * a5 * h ^ 2) :
    (1 : F) * h ^ 5 *
        depressedL68 h (sexticDepressionR68 h a5) b7 =
      alignedSquareLBar68 h a5 b7 := by
  have hdisc : (4 : F) * a5 * h ^ 2 - (3 : F) * b7 = 0 := by
    linear_combination -haligned
  simp only [alignedSquareLBar68, one_mul]
  rw [depressedL68_eq_zero_of_aligned h a5 b7 hh hdisc]
  ring

theorem alignedSquareABar68_eq
    (h a5 a4 : F) (hh : h ≠ 0) :
    (12 : F) * h ^ 10 *
        depressedA68 h (sexticDepressionR68 h a5) a5 a4 =
      alignedSquareABar68 h a5 a4 := by
  simp only [alignedSquareABar68, depressedA68, sexticDepressionR68]
  field_simp [hh]
  ring

theorem alignedSquareBBar68_eq
    (h a5 a4 a3 : F) (hh : h ≠ 0) :
    (27 : F) * h ^ 15 *
        depressedB68 h (sexticDepressionR68 h a5) a5 a4 a3 =
      alignedSquareBBar68 h a5 a4 a3 := by
  simp only [alignedSquareBBar68, depressedB68, sexticDepressionR68]
  field_simp [hh]
  ring

theorem alignedSquareCBar68_eq
    (h a5 a4 a3 a2 : F) (hh : h ≠ 0) :
    (144 : F) * h ^ 20 *
        depressedC68 h (sexticDepressionR68 h a5) a5 a4 a3 a2 =
      alignedSquareCBar68 h a5 a4 a3 a2 := by
  simp only [alignedSquareCBar68, depressedC68, sexticDepressionR68]
  field_simp [hh]
  ring

theorem alignedSquareDBar68_eq
    (h a5 a4 a3 a2 a1 : F) (hh : h ≠ 0) :
    (324 : F) * h ^ 25 *
        depressedD68 h (sexticDepressionR68 h a5) a5 a4 a3 a2 a1 =
      alignedSquareDBar68 h a5 a4 a3 a2 a1 := by
  simp only [alignedSquareDBar68, depressedD68, sexticDepressionR68]
  field_simp [hh]
  ring

set_option maxHeartbeats 800000000 in
theorem alignedSquareEBar68_eq
    (h a5 a4 a3 a2 a1 a0 : F) (hh : h ≠ 0) :
    (46656 : F) * h ^ 30 *
        depressedE68 h (sexticDepressionR68 h a5) a5 a4 a3 a2 a1 a0 =
      alignedSquareEBar68 h a5 a4 a3 a2 a1 a0 := by
  simp only [alignedSquareEBar68, depressedE68, sexticDepressionR68]
  field_simp [hh]
  ring

theorem alignedSquarePBar68_eq
    (h a5 b7 b6 : F) (hh : h ≠ 0)
    (haligned : (3 : F) * b7 = (4 : F) * a5 * h ^ 2) :
    (9 : F) * h ^ 10 *
        depressedP68 h (sexticDepressionR68 h a5) b7 b6 =
      alignedSquarePBar68 h a5 b6 := by
  simp only [alignedSquarePBar68, depressedP68, sexticDepressionR68]
  rw [alignedSquare_b7_eq68 h a5 b7 haligned]
  field_simp [hh]
  ring

theorem alignedSquareQBar68_eq
    (h a5 b7 b6 b5 : F) (hh : h ≠ 0)
    (haligned : (3 : F) * b7 = (4 : F) * a5 * h ^ 2) :
    (27 : F) * h ^ 15 *
        depressedQ68 h (sexticDepressionR68 h a5) b7 b6 b5 =
      alignedSquareQBar68 h a5 b6 b5 := by
  simp only [alignedSquareQBar68, depressedQ68, sexticDepressionR68]
  rw [alignedSquare_b7_eq68 h a5 b7 haligned]
  field_simp [hh]
  ring

set_option maxHeartbeats 800000000 in
theorem alignedSquareRBar68_eq
    (h a5 b7 b6 b5 b4 : F) (hh : h ≠ 0)
    (haligned : (3 : F) * b7 = (4 : F) * a5 * h ^ 2) :
    (216 : F) * h ^ 20 *
        depressedR68 h (sexticDepressionR68 h a5) b7 b6 b5 b4 =
      alignedSquareRBar68 h a5 b6 b5 b4 := by
  simp only [alignedSquareRBar68, depressedR68, sexticDepressionR68]
  rw [alignedSquare_b7_eq68 h a5 b7 haligned]
  field_simp [hh]
  ring

set_option maxHeartbeats 800000000 in
theorem alignedSquareSBar68_eq
    (h a5 b7 b6 b5 b4 b3 : F) (hh : h ≠ 0)
    (haligned : (3 : F) * b7 = (4 : F) * a5 * h ^ 2) :
    (486 : F) * h ^ 25 *
        depressedS68 h (sexticDepressionR68 h a5) b7 b6 b5 b4 b3 =
      alignedSquareSBar68 h a5 b6 b5 b4 b3 := by
  simp only [alignedSquareSBar68, depressedS68, sexticDepressionR68]
  rw [alignedSquare_b7_eq68 h a5 b7 haligned]
  field_simp [hh]
  ring

set_option maxHeartbeats 800000000 in
theorem alignedSquareTBar68_eq
    (h a5 b7 b6 b5 b4 b3 b2 : F) (hh : h ≠ 0)
    (haligned : (3 : F) * b7 = (4 : F) * a5 * h ^ 2) :
    (11664 : F) * h ^ 30 *
        depressedT68 h (sexticDepressionR68 h a5) b7 b6 b5 b4 b3 b2 =
      alignedSquareTBar68 h a5 b6 b5 b4 b3 b2 := by
  simp only [alignedSquareTBar68, depressedT68, sexticDepressionR68]
  rw [alignedSquare_b7_eq68 h a5 b7 haligned]
  field_simp [hh]
  ring

set_option maxHeartbeats 800000000 in
theorem alignedSquareUBar68_eq
    (h a5 b7 b6 b5 b4 b3 b2 b1 : F) (hh : h ≠ 0)
    (haligned : (3 : F) * b7 = (4 : F) * a5 * h ^ 2) :
    (11664 : F) * h ^ 35 *
        depressedU68 h (sexticDepressionR68 h a5) b7 b6 b5 b4 b3 b2 b1 =
      alignedSquareUBar68 h a5 b6 b5 b4 b3 b2 b1 := by
  simp only [alignedSquareUBar68, depressedU68, sexticDepressionR68]
  rw [alignedSquare_b7_eq68 h a5 b7 haligned]
  field_simp [hh]
  ring

set_option maxHeartbeats 800000000 in
theorem alignedSquareVBar68_eq
    (h a5 b7 b6 b5 b4 b3 b2 b1 b0 : F) (hh : h ≠ 0)
    (haligned : (3 : F) * b7 = (4 : F) * a5 * h ^ 2) :
    (1679616 : F) * h ^ 40 *
        depressedV68 h (sexticDepressionR68 h a5) b7 b6 b5 b4 b3 b2 b1
          b0 =
      alignedSquareVBar68 h a5 b6 b5 b4 b3 b2 b1 b0 := by
  simp only [alignedSquareVBar68, depressedV68, sexticDepressionR68]
  rw [alignedSquare_b7_eq68 h a5 b7 haligned]
  field_simp [hh]
  ring

theorem alignedSquareL_eq_zero68
    (h a5 b7 : F) (hh : h ≠ 0)
    (haligned : (3 : F) * b7 = (4 : F) * a5 * h ^ 2) :
    depressedL68 h (sexticDepressionR68 h a5) b7 = 0 := by
  have hbar := alignedSquareLBar68_eq h a5 b7 hh haligned
  simp only [alignedSquareLBar68, one_mul] at hbar
  have hh5 : h ^ 5 ≠ 0 := pow_ne_zero 5 hh
  exact (mul_eq_zero.mp hbar).resolve_left hh5

end AlignedSquareBarIdentities68

#print axioms alignedSquareLBar68_eq
#print axioms alignedSquareABar68_eq
#print axioms alignedSquarePBar68_eq
#print axioms alignedSquareVBar68_eq
#print axioms alignedSquareL_eq_zero68

/-! ## Compact integer numerator and source polynomial -/

section AlignedSquareCompact68

variable {R : Type*} [CommRing R]

/-- Integer `50`-term compact of the weight-13 primitive after clearing
the bar denominators.  The last primitive slot `V` is unused, as is the
aligned `L = 0`. -/
def alignedSquareClearedCompact68
    (A B C0 D0 E0 P Q R0 S0 T0 U0 : R) : R :=
  -((311220 : R) * A ^ 5 * B) + 46683 * A ^ 5 * Q +
    373464 * A ^ 4 * B * P + 373464 * A ^ 4 * D0 -
    29484 * A ^ 4 * S0 + 1493856 * A ^ 3 * B * C0 -
    157248 * A ^ 3 * B * R0 - 294840 * A ^ 3 * C0 * Q -
    471744 * A ^ 3 * D0 * P + 9072 * A ^ 3 * U0 +
    1770496 * A ^ 2 * B ^ 3 - 1048320 * A ^ 2 * B ^ 2 * Q -
    1415232 * A ^ 2 * B * C0 * P - 52416 * A ^ 2 * B * E0 +
    24192 * A ^ 2 * B * T0 - 1415232 * A ^ 2 * C0 * D0 +
    163296 * A ^ 2 * C0 * S0 + 217728 * A ^ 2 * D0 * R0 +
    15120 * A ^ 2 * E0 * Q - 1118208 * A * B ^ 3 * P -
    3354624 * A * B ^ 2 * D0 + 387072 * A * B ^ 2 * S0 -
    1415232 * A * B * C0 ^ 2 + 435456 * A * B * C0 * R0 +
    1935360 * A * B * D0 * Q + 48384 * A * B * E0 * P +
    408240 * A * C0 ^ 2 * Q + 1306368 * A * C0 * D0 * P -
    46656 * A * C0 * U0 + 48384 * A * D0 * E0 -
    41472 * A * D0 * T0 - 10368 * A * E0 * S0 -
    1118208 * B ^ 3 * C0 + 172032 * B ^ 3 * R0 +
    967680 * B ^ 2 * C0 * Q + 1548288 * B ^ 2 * D0 * P -
    55296 * B ^ 2 * U0 + 653184 * B * C0 ^ 2 * P +
    48384 * B * C0 * E0 - 41472 * B * C0 * T0 +
    1548288 * B * D0 ^ 2 - 663552 * B * D0 * S0 -
    13824 * B * E0 * R0 + 653184 * C0 ^ 2 * D0 -
    139968 * C0 ^ 2 * S0 - 373248 * C0 * D0 * R0 -
    25920 * C0 * E0 * Q - 829440 * D0 ^ 2 * Q -
    41472 * D0 * E0 * P + 10368 * E0 * U0

/-- Source-level polynomial numerator: the compact evaluated on the
thirteen aligned bars.  The letters `b7` and `b0` are retained so the
signature lists every source coefficient; `Lbar = 0` and the primitive
ignores `V`. -/
def alignedSquareClearedNumerator68
    (h a5 a4 a3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 b0 : R) : R :=
  alignedSquareClearedCompact68
    (alignedSquareABar68 h a5 a4)
    (alignedSquareBBar68 h a5 a4 a3)
    (alignedSquareCBar68 h a5 a4 a3 a2)
    (alignedSquareDBar68 h a5 a4 a3 a2 a1)
    (alignedSquareEBar68 h a5 a4 a3 a2 a1 a0)
    (alignedSquarePBar68 h a5 b6)
    (alignedSquareQBar68 h a5 b6 b5)
    (alignedSquareRBar68 h a5 b6 b5 b4)
    (alignedSquareSBar68 h a5 b6 b5 b4 b3)
    (alignedSquareTBar68 h a5 b6 b5 b4 b3 b2)
    (alignedSquareUBar68 h a5 b6 b5 b4 b3 b2 b1)

end AlignedSquareCompact68

section AlignedSquareCompactMap68

variable {R S : Type*} [CommRing R] [CommRing S]

theorem alignedSquareClearedNumerator68_map
    (f : R →+* S)
    (h a5 a4 a3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 b0 : R) :
    f (alignedSquareClearedNumerator68 h a5 a4 a3 a2 a1 a0 b7 b6 b5 b4
          b3 b2 b1 b0) =
      alignedSquareClearedNumerator68 (f h) (f a5) (f a4) (f a3) (f a2)
        (f a1) (f a0) (f b7) (f b6) (f b5) (f b4) (f b3) (f b2) (f b1)
        (f b0) := by
  simp only [alignedSquareClearedNumerator68,
    alignedSquareClearedCompact68, alignedSquareABar68,
    alignedSquareBBar68, alignedSquareCBar68, alignedSquareDBar68,
    alignedSquareEBar68, alignedSquarePBar68, alignedSquareQBar68,
    alignedSquareRBar68, alignedSquareSBar68, alignedSquareTBar68,
    alignedSquareUBar68, map_add, map_sub, map_neg, map_mul, map_pow,
    map_ofNat]

end AlignedSquareCompactMap68

#print axioms alignedSquareClearedNumerator68_map

/-! ## Compact = scale · ρ(bars / integers); weighted `h⁵` scaling -/

section AlignedSquareCompactBridge68

variable {F : Type*} [Field F] [CharZero F]

omit [CharZero F] in
theorem degreeZeroPrimitive68_independent_of_V
    (L A B C0 D E P Q R S T U V W : F) :
    degreeZeroPrimitive68 L A B C0 D E P Q R S T U V =
      degreeZeroPrimitive68 L A B C0 D E P Q R S T U W :=
  rfl

set_option maxHeartbeats 800000000 in
theorem degreeZeroPrimitive68_weightedScale
    (t L A B C0 D E P Q R S T U V : F) :
    degreeZeroPrimitive68 (t ^ 5 * L) (t ^ 10 * A) (t ^ 15 * B)
        (t ^ 20 * C0) (t ^ 25 * D) (t ^ 30 * E) (t ^ 10 * P)
        (t ^ 15 * Q) (t ^ 20 * R) (t ^ 25 * S) (t ^ 30 * T)
        (t ^ 35 * U) (t ^ 40 * V) =
      t ^ 65 * degreeZeroPrimitive68 L A B C0 D E P Q R S T U V := by
  have h :=
    degreeZeroPrimitive68_weighted_homogeneous (t ^ 5) L A B C0 D E P Q
      R S T U V
  simp only [← pow_mul] at h
  norm_num at h
  exact h

set_option maxHeartbeats 800000000 in
/-- Exact numerical clearing from the depressed primitive to the compact
integer numerator.  CAS:
`derive_68_aligned_square_clearing.py`
(`20260902T114621Z-68-aligned-square-clearing-48447`). -/
theorem alignedSquareClearedCompact68_eq_scaledPrimitive
    (A B C0 D0 E0 P Q R0 S0 T0 U0 : F) :
    alignedSquareClearedCompact68 A B C0 D0 E0 P Q R0 S0 T0 U0 =
      (5642219814912 : F) *
        degreeZeroPrimitive68 0 (A / 12) (B / 27) (C0 / 144)
          (D0 / 324) (E0 / 46656) (P / 9) (Q / 27) (R0 / 216)
          (S0 / 486) (T0 / 11664) (U0 / 11664) 0 := by
  simp only [alignedSquareClearedCompact68, degreeZeroPrimitive68,
    degreeZeroBaseGroup68, degreeZeroBetaGroup68, degreeZeroGammaGroup68,
    degreeZeroDeltaGroup68, degreeZeroEpsilonGroup68,
    degreeZeroZetaGroup68, degreeZeroFourGroup68, degreeZeroThreeGroup68,
    degreeZeroTwoGroup68, firstIntegralFour68, firstIntegralThree68,
    firstIntegralTwo68, alphaResidual68, betaResidual68,
    gammaResidual68, deltaResidual68, epsilonResidual68, zetaResidual68]
  ring

end AlignedSquareCompactBridge68

#print axioms degreeZeroPrimitive68_weightedScale
#print axioms alignedSquareClearedCompact68_eq_scaledPrimitive

/-! ## Source primitive and `h^{65}` clearing identity -/

section AlignedSquareSourcePrimitive68

variable {F : Type*} [Field F] [CharZero F]

/-- The weight-13 primitive on the sextic-octic depression of a literal
aligned `(6,8)` source. -/
def alignedSquareSourcePrimitive68
    (h a5 a4 a3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 b0 : F) : F :=
  degreeZeroPrimitive68
    (depressedL68 h (sexticDepressionR68 h a5) b7)
    (depressedA68 h (sexticDepressionR68 h a5) a5 a4)
    (depressedB68 h (sexticDepressionR68 h a5) a5 a4 a3)
    (depressedC68 h (sexticDepressionR68 h a5) a5 a4 a3 a2)
    (depressedD68 h (sexticDepressionR68 h a5) a5 a4 a3 a2 a1)
    (depressedE68 h (sexticDepressionR68 h a5) a5 a4 a3 a2 a1 a0)
    (depressedP68 h (sexticDepressionR68 h a5) b7 b6)
    (depressedQ68 h (sexticDepressionR68 h a5) b7 b6 b5)
    (depressedR68 h (sexticDepressionR68 h a5) b7 b6 b5 b4)
    (depressedS68 h (sexticDepressionR68 h a5) b7 b6 b5 b4 b3)
    (depressedT68 h (sexticDepressionR68 h a5) b7 b6 b5 b4 b3 b2)
    (depressedU68 h (sexticDepressionR68 h a5) b7 b6 b5 b4 b3 b2 b1)
    (depressedV68 h (sexticDepressionR68 h a5) b7 b6 b5 b4 b3 b2 b1 b0)

set_option maxHeartbeats 800000000 in
/-- Depressed aligned coordinates are the bars over the native
denominators. -/
theorem alignedSquareSourcePrimitive68_eq_bars
    (h a5 a4 a3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 b0 : F) (hh : h ≠ 0)
    (haligned : (3 : F) * b7 = (4 : F) * a5 * h ^ 2) :
    alignedSquareSourcePrimitive68 h a5 a4 a3 a2 a1 a0 b7 b6 b5 b4 b3
        b2 b1 b0 =
      degreeZeroPrimitive68 0
        (alignedSquareABar68 h a5 a4 / ((12 : F) * h ^ 10))
        (alignedSquareBBar68 h a5 a4 a3 / ((27 : F) * h ^ 15))
        (alignedSquareCBar68 h a5 a4 a3 a2 / ((144 : F) * h ^ 20))
        (alignedSquareDBar68 h a5 a4 a3 a2 a1 / ((324 : F) * h ^ 25))
        (alignedSquareEBar68 h a5 a4 a3 a2 a1 a0 /
          ((46656 : F) * h ^ 30))
        (alignedSquarePBar68 h a5 b6 / ((9 : F) * h ^ 10))
        (alignedSquareQBar68 h a5 b6 b5 / ((27 : F) * h ^ 15))
        (alignedSquareRBar68 h a5 b6 b5 b4 / ((216 : F) * h ^ 20))
        (alignedSquareSBar68 h a5 b6 b5 b4 b3 / ((486 : F) * h ^ 25))
        (alignedSquareTBar68 h a5 b6 b5 b4 b3 b2 /
          ((11664 : F) * h ^ 30))
        (alignedSquareUBar68 h a5 b6 b5 b4 b3 b2 b1 /
          ((11664 : F) * h ^ 35))
        (alignedSquareVBar68 h a5 b6 b5 b4 b3 b2 b1 b0 /
          ((1679616 : F) * h ^ 40)) := by
  have hL := alignedSquareL_eq_zero68 h a5 b7 hh haligned
  have hA := alignedSquareABar68_eq h a5 a4 hh
  have hB := alignedSquareBBar68_eq h a5 a4 a3 hh
  have hC := alignedSquareCBar68_eq h a5 a4 a3 a2 hh
  have hD := alignedSquareDBar68_eq h a5 a4 a3 a2 a1 hh
  have hE := alignedSquareEBar68_eq h a5 a4 a3 a2 a1 a0 hh
  have hP := alignedSquarePBar68_eq h a5 b7 b6 hh haligned
  have hQ := alignedSquareQBar68_eq h a5 b7 b6 b5 hh haligned
  have hR := alignedSquareRBar68_eq h a5 b7 b6 b5 b4 hh haligned
  have hS := alignedSquareSBar68_eq h a5 b7 b6 b5 b4 b3 hh haligned
  have hT := alignedSquareTBar68_eq h a5 b7 b6 b5 b4 b3 b2 hh haligned
  have hU :=
    alignedSquareUBar68_eq h a5 b7 b6 b5 b4 b3 b2 b1 hh haligned
  have hV :=
    alignedSquareVBar68_eq h a5 b7 b6 b5 b4 b3 b2 b1 b0 hh haligned
  dsimp only [alignedSquareSourcePrimitive68]
  rw [hL]
  have hdiv
      {c : F} {n : ℕ} {X bar : F} (hc : c ≠ 0)
      (hn : h ^ n ≠ 0) (hid : c * h ^ n * X = bar) :
      X = bar / (c * h ^ n) := by
    field_simp [hc, hn]
    linear_combination hid
  have h12 : (12 : F) ≠ 0 := by norm_num
  have h27 : (27 : F) ≠ 0 := by norm_num
  have h144 : (144 : F) ≠ 0 := by norm_num
  have h324 : (324 : F) ≠ 0 := by norm_num
  have h46656 : (46656 : F) ≠ 0 := by norm_num
  have h9 : (9 : F) ≠ 0 := by norm_num
  have h216 : (216 : F) ≠ 0 := by norm_num
  have h486 : (486 : F) ≠ 0 := by norm_num
  have h11664 : (11664 : F) ≠ 0 := by norm_num
  have h1679616 : (1679616 : F) ≠ 0 := by norm_num
  rw [hdiv h12 (pow_ne_zero 10 hh) hA,
    hdiv h27 (pow_ne_zero 15 hh) hB,
    hdiv h144 (pow_ne_zero 20 hh) hC,
    hdiv h324 (pow_ne_zero 25 hh) hD,
    hdiv h46656 (pow_ne_zero 30 hh) hE,
    hdiv h9 (pow_ne_zero 10 hh) hP,
    hdiv h27 (pow_ne_zero 15 hh) hQ,
    hdiv h216 (pow_ne_zero 20 hh) hR,
    hdiv h486 (pow_ne_zero 25 hh) hS,
    hdiv h11664 (pow_ne_zero 30 hh) hT,
    hdiv h11664 (pow_ne_zero 35 hh) hU,
    hdiv h1679616 (pow_ne_zero 40 hh) hV]

set_option maxHeartbeats 800000000 in
/-- Exact algebraic bridge from the source-level compact numerator to
the depressed primitive. -/
theorem alignedSquareClearedNumerator68_eq_pow_mul_primitive_field
    (h a5 a4 a3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 b0 : F) (hh : h ≠ 0)
    (haligned : (3 : F) * b7 = (4 : F) * a5 * h ^ 2) :
    alignedSquareClearedNumerator68 h a5 a4 a3 a2 a1 a0 b7 b6 b5 b4 b3
        b2 b1 b0 =
      h ^ 65 * ((5642219814912 : F) *
        alignedSquareSourcePrimitive68 h a5 a4 a3 a2 a1 a0 b7 b6 b5 b4
          b3 b2 b1 b0) := by
  let Abar := alignedSquareABar68 h a5 a4
  let Bbar := alignedSquareBBar68 h a5 a4 a3
  let Cbar := alignedSquareCBar68 h a5 a4 a3 a2
  let Dbar := alignedSquareDBar68 h a5 a4 a3 a2 a1
  let Ebar := alignedSquareEBar68 h a5 a4 a3 a2 a1 a0
  let Pbar := alignedSquarePBar68 h a5 b6
  let Qbar := alignedSquareQBar68 h a5 b6 b5
  let Rbar := alignedSquareRBar68 h a5 b6 b5 b4
  let Sbar := alignedSquareSBar68 h a5 b6 b5 b4 b3
  let Tbar := alignedSquareTBar68 h a5 b6 b5 b4 b3 b2
  let Ubar := alignedSquareUBar68 h a5 b6 b5 b4 b3 b2 b1
  let Vbar := alignedSquareVBar68 h a5 b6 b5 b4 b3 b2 b1 b0
  have hcompact :=
    alignedSquareClearedCompact68_eq_scaledPrimitive Abar Bbar Cbar
      Dbar Ebar Pbar Qbar Rbar Sbar Tbar Ubar
  have hpeel :=
    alignedSquareSourcePrimitive68_eq_bars h a5 a4 a3 a2 a1 a0 b7 b6 b5
      b4 b3 b2 b1 b0 hh haligned
  have hwt :=
    degreeZeroPrimitive68_weightedScale h (0 : F)
      (Abar / ((12 : F) * h ^ 10)) (Bbar / ((27 : F) * h ^ 15))
      (Cbar / ((144 : F) * h ^ 20)) (Dbar / ((324 : F) * h ^ 25))
      (Ebar / ((46656 : F) * h ^ 30)) (Pbar / ((9 : F) * h ^ 10))
      (Qbar / ((27 : F) * h ^ 15)) (Rbar / ((216 : F) * h ^ 20))
      (Sbar / ((486 : F) * h ^ 25)) (Tbar / ((11664 : F) * h ^ 30))
      (Ubar / ((11664 : F) * h ^ 35)) (Vbar / ((1679616 : F) * h ^ 40))
  have hL : h ^ 5 * (0 : F) = 0 := by ring
  have hA : h ^ 10 * (Abar / ((12 : F) * h ^ 10)) = Abar / 12 := by
    field_simp [hh]
  have hB : h ^ 15 * (Bbar / ((27 : F) * h ^ 15)) = Bbar / 27 := by
    field_simp [hh]
  have hC : h ^ 20 * (Cbar / ((144 : F) * h ^ 20)) = Cbar / 144 := by
    field_simp [hh]
  have hD : h ^ 25 * (Dbar / ((324 : F) * h ^ 25)) = Dbar / 324 := by
    field_simp [hh]
  have hE : h ^ 30 * (Ebar / ((46656 : F) * h ^ 30)) = Ebar / 46656 := by
    field_simp [hh]
  have hP : h ^ 10 * (Pbar / ((9 : F) * h ^ 10)) = Pbar / 9 := by
    field_simp [hh]
  have hQ : h ^ 15 * (Qbar / ((27 : F) * h ^ 15)) = Qbar / 27 := by
    field_simp [hh]
  have hR : h ^ 20 * (Rbar / ((216 : F) * h ^ 20)) = Rbar / 216 := by
    field_simp [hh]
  have hS : h ^ 25 * (Sbar / ((486 : F) * h ^ 25)) = Sbar / 486 := by
    field_simp [hh]
  have hT : h ^ 30 * (Tbar / ((11664 : F) * h ^ 30)) = Tbar / 11664 := by
    field_simp [hh]
  have hU : h ^ 35 * (Ubar / ((11664 : F) * h ^ 35)) = Ubar / 11664 := by
    field_simp [hh]
  have hV : h ^ 40 * (Vbar / ((1679616 : F) * h ^ 40)) =
      Vbar / 1679616 := by
    field_simp [hh]
  have hwt' :
      degreeZeroPrimitive68 0 (Abar / 12) (Bbar / 27) (Cbar / 144)
          (Dbar / 324) (Ebar / 46656) (Pbar / 9) (Qbar / 27)
          (Rbar / 216) (Sbar / 486) (Tbar / 11664) (Ubar / 11664)
          (Vbar / 1679616) =
        h ^ 65 *
          degreeZeroPrimitive68 0 (Abar / ((12 : F) * h ^ 10))
            (Bbar / ((27 : F) * h ^ 15))
            (Cbar / ((144 : F) * h ^ 20))
            (Dbar / ((324 : F) * h ^ 25))
            (Ebar / ((46656 : F) * h ^ 30))
            (Pbar / ((9 : F) * h ^ 10)) (Qbar / ((27 : F) * h ^ 15))
            (Rbar / ((216 : F) * h ^ 20))
            (Sbar / ((486 : F) * h ^ 25))
            (Tbar / ((11664 : F) * h ^ 30))
            (Ubar / ((11664 : F) * h ^ 35))
            (Vbar / ((1679616 : F) * h ^ 40)) := by
    rw [hL, hA, hB, hC, hD, hE, hP, hQ, hR, hS, hT, hU, hV] at hwt
    exact hwt
  have hh65 : h ^ 65 ≠ 0 := pow_ne_zero 65 hh
  dsimp only [alignedSquareClearedNumerator68]
  rw [hcompact]
  rw [degreeZeroPrimitive68_independent_of_V 0 (Abar / 12) (Bbar / 27)
    (Cbar / 144) (Dbar / 324) (Ebar / 46656) (Pbar / 9) (Qbar / 27)
    (Rbar / 216) (Sbar / 486) (Tbar / 11664) (Ubar / 11664) 0
    (Vbar / 1679616)]
  rw [hwt', ← hpeel]
  ring

end AlignedSquareSourcePrimitive68

#print axioms alignedSquareSourcePrimitive68_eq_bars
#print axioms alignedSquareClearedNumerator68_eq_pow_mul_primitive_field

section AlignedSquareClearedNumeratorRatFunc68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 800000000 in
/-- Source-level identity in `k(x)`: the polynomial numerator is
`h₀^{65}` times the grouped integer scale times the depressed
primitive. -/
theorem alignedSquareClearedNumerator68_eq_pow_mul_primitive
    (h0 a5 a4 a3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 b0 : k[X])
    (hh : h0 ≠ 0)
    (haligned : (3 : k[X]) * b7 = (4 : k[X]) * a5 * h0 ^ 2) :
    algebraMap k[X] (RatFunc k)
        (alignedSquareClearedNumerator68 h0 a5 a4 a3 a2 a1 a0 b7 b6 b5
          b4 b3 b2 b1 b0) =
      (algebraMap k[X] (RatFunc k) h0) ^ 65 *
        (RatFunc.C (5642219814912 : k) *
          alignedSquareSourcePrimitive68
            (algebraMap k[X] (RatFunc k) h0)
            (algebraMap k[X] (RatFunc k) a5)
            (algebraMap k[X] (RatFunc k) a4)
            (algebraMap k[X] (RatFunc k) a3)
            (algebraMap k[X] (RatFunc k) a2)
            (algebraMap k[X] (RatFunc k) a1)
            (algebraMap k[X] (RatFunc k) a0)
            (algebraMap k[X] (RatFunc k) b7)
            (algebraMap k[X] (RatFunc k) b6)
            (algebraMap k[X] (RatFunc k) b5)
            (algebraMap k[X] (RatFunc k) b4)
            (algebraMap k[X] (RatFunc k) b3)
            (algebraMap k[X] (RatFunc k) b2)
            (algebraMap k[X] (RatFunc k) b1)
            (algebraMap k[X] (RatFunc k) b0)) := by
  let φ : k[X] →+* RatFunc k := algebraMap k[X] (RatFunc k)
  have hhRF : φ h0 ≠ 0 := RatFunc.algebraMap_ne_zero hh
  have halignedRF :
      (3 : RatFunc k) * φ b7 = (4 : RatFunc k) * φ a5 * φ h0 ^ 2 := by
    have hmapped := congrArg φ haligned
    simpa [φ, map_mul, map_pow, map_ofNat] using hmapped
  have hmap :=
    alignedSquareClearedNumerator68_map φ h0 a5 a4 a3 a2 a1 a0 b7 b6 b5
      b4 b3 b2 b1 b0
  have hfield :=
    alignedSquareClearedNumerator68_eq_pow_mul_primitive_field (φ h0)
      (φ a5) (φ a4) (φ a3) (φ a2) (φ a1) (φ a0) (φ b7) (φ b6) (φ b5)
      (φ b4) (φ b3) (φ b2) (φ b1) (φ b0) hhRF halignedRF
  have hscale : (5642219814912 : RatFunc k) =
      RatFunc.C (5642219814912 : k) :=
    (map_natCast (RatFunc.C : k →+* RatFunc k) 5642219814912).symm
  rw [hmap, hfield, hscale]

end AlignedSquareClearedNumeratorRatFunc68

#print axioms alignedSquareClearedNumerator68_eq_pow_mul_primitive

/-! ## Scaled simple-pole derivative, taking the unscaled pole as a hypothesis -/

section AlignedSquareScaledDeriv68

variable {k : Type*} [Field k] [CharZero k]

/-- Scaled wrapper derivative: `deriv (C scale · ρ) = C (scale · j) / h0`.
The unscaled simple pole is a hypothesis supplied by lane P1; this lemma
does not reopen AffineBracket or the source Jacobian. -/
theorem alignedSquarePrimitive68_scaledDeriv_eq_simplePole
    (h0 : k[X]) (j : k)
    (a5 a4 a3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 b0 : k[X])
    (hderiv :
      Differential.deriv
          (alignedSquareSourcePrimitive68
            (algebraMap k[X] (RatFunc k) h0)
            (algebraMap k[X] (RatFunc k) a5)
            (algebraMap k[X] (RatFunc k) a4)
            (algebraMap k[X] (RatFunc k) a3)
            (algebraMap k[X] (RatFunc k) a2)
            (algebraMap k[X] (RatFunc k) a1)
            (algebraMap k[X] (RatFunc k) a0)
            (algebraMap k[X] (RatFunc k) b7)
            (algebraMap k[X] (RatFunc k) b6)
            (algebraMap k[X] (RatFunc k) b5)
            (algebraMap k[X] (RatFunc k) b4)
            (algebraMap k[X] (RatFunc k) b3)
            (algebraMap k[X] (RatFunc k) b2)
            (algebraMap k[X] (RatFunc k) b1)
            (algebraMap k[X] (RatFunc k) b0)) =
        RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    Differential.deriv
        (RatFunc.C (5642219814912 : k) *
          alignedSquareSourcePrimitive68
            (algebraMap k[X] (RatFunc k) h0)
            (algebraMap k[X] (RatFunc k) a5)
            (algebraMap k[X] (RatFunc k) a4)
            (algebraMap k[X] (RatFunc k) a3)
            (algebraMap k[X] (RatFunc k) a2)
            (algebraMap k[X] (RatFunc k) a1)
            (algebraMap k[X] (RatFunc k) a0)
            (algebraMap k[X] (RatFunc k) b7)
            (algebraMap k[X] (RatFunc k) b6)
            (algebraMap k[X] (RatFunc k) b5)
            (algebraMap k[X] (RatFunc k) b4)
            (algebraMap k[X] (RatFunc k) b3)
            (algebraMap k[X] (RatFunc k) b2)
            (algebraMap k[X] (RatFunc k) b1)
            (algebraMap k[X] (RatFunc k) b0)) =
      RatFunc.C (5642219814912 * j) /
        algebraMap k[X] (RatFunc k) h0 := by
  let hRF : RatFunc k := algebraMap k[X] (RatFunc k) h0
  let prim : RatFunc k :=
    alignedSquareSourcePrimitive68 hRF
      (algebraMap k[X] (RatFunc k) a5)
      (algebraMap k[X] (RatFunc k) a4)
      (algebraMap k[X] (RatFunc k) a3)
      (algebraMap k[X] (RatFunc k) a2)
      (algebraMap k[X] (RatFunc k) a1)
      (algebraMap k[X] (RatFunc k) a0)
      (algebraMap k[X] (RatFunc k) b7)
      (algebraMap k[X] (RatFunc k) b6)
      (algebraMap k[X] (RatFunc k) b5)
      (algebraMap k[X] (RatFunc k) b4)
      (algebraMap k[X] (RatFunc k) b3)
      (algebraMap k[X] (RatFunc k) b2)
      (algebraMap k[X] (RatFunc k) b1)
      (algebraMap k[X] (RatFunc k) b0)
  have hmul :
      Differential.deriv
          (RatFunc.C (5642219814912 : k) * prim) =
        RatFunc.C (5642219814912 : k) * Differential.deriv prim := by
    simpa [ratFuncDerivation46_apply, Algebra.smul_def] using
      ratFuncDerivation46.map_smul (5642219814912 : k) prim
  have hleib :
      Differential.deriv (RatFunc.C (5642219814912 : k) * prim) =
        RatFunc.C (5642219814912 : k) * (RatFunc.C j / hRF) := by
    rw [hmul]
    simpa [prim, hRF] using hderiv
  have hscale :
      RatFunc.C (5642219814912 : k) * (RatFunc.C j / hRF) =
        RatFunc.C (5642219814912 * j) / hRF := by
    rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_assoc, ← map_mul]
  simpa [prim, hRF] using (hleib.trans hscale)

end AlignedSquareScaledDeriv68

#print axioms alignedSquarePrimitive68_scaledDeriv_eq_simplePole

end Max11DegreeRoutes
