import Grok810AlignedSquareSourceWrapperScratch
import Grok810DegreeZeroSourceNumeratorScratch
import Grok810DegreeZeroCompactBridgeScratch
import Grok810DegreeZeroTowerOrders111to118Scratch

/-! # (coordinator split: heavy blocks only) Aligned-square cleared numerator and pole ceiling for `(8,10)`

Lanes C and T of `Grok810AlignedFaceTowerPlanScratch.md`.  Untracked
repair of the previous compact-block emitter (`FixScratch`).  No tracked
file was edited.  The broken draft is not imported.

Parents (tracked, green):

* `Grok810AlignedSquareSourceWrapperScratch`
  (`alignedSquareSourcePrimitive810`,
  `alignedSquarePrimitive810_deriv_eq_simplePole_of_source`,
  native arithmetic `119 / 0 / 119 / 119`);
* `Grok810DegreeZeroSourceNumeratorScratch`
  (`degreeZeroClearedSource810`, 25 blocks, scale `2^{62}`,
  `degreeZeroClearedSource810_map`, and the landed bar identities
  `depressedA810_eq_cleared` … `depressedW810_eq_cleared`);
* `Grok810DegreeZeroCompactBridgeScratch`
  (`rhoResidual810_eq_clearedCompact`: compact `= 2^{28} ρ`, and the
  sixteen integer-cleared identities);
* `Grok810DegreeZeroTowerOrders111to118Scratch`
  (`degreeZero_pow_dvd_of_remaining_pole810`,
  `degreeZero_of_pow_dvd_simplePole_ne_zero810`, generic in `n`).

The aligned face `λ = 0` specialises the ninth-power source numerator
without a peel.  Clearing is `7 · 17 = 119`, base order `0`, remaining
pole `119`, native ceiling `119`.  These are not the nonzero-face
Pi-tower numbers `102 / 17 / 118`.

The `λ = 0` instance of `source = 2^{62} h^{119} ρ` is proved from the
numerator file's 25 compact blocks: `L = 0` kills the 40 `L`-monomials
of the 215-term compact, and each surviving block is discharged by its
own `field_simp; ring`.  A one-shot 977-term ring is not used.

CAS: `derive_810_aligned_square_clearing.py` (job
`20260902T132022Z-810-aligned-square-clearing-58464`).

No chamber-closure claim (lane Z follows).  No `sorry`, no new axioms,
no finite-root shortcut.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option maxHeartbeats 800000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## Bookkeeping: extra compact-to-source integer scale -/

/-- Remaining integer scale after the grouped compact `2^{28}` is
removed from the source numerator `2^{62}`. -/
def alignedSquareCompactToSourceIntegerScale810 : ℕ := 17179869184

theorem alignedSquareCompactToSourceIntegerScale810_eq :
    alignedSquareCompactToSourceIntegerScale810 = 17179869184 :=
  rfl

theorem alignedSquareCompactToSourceIntegerScale810_eq_pow :
    alignedSquareCompactToSourceIntegerScale810 = 2 ^ 34 :=
  rfl

theorem alignedSquareClearedIntegerScale810_eq_grouped_mul :
    degreeZeroClearedIntegerScale810 =
      degreeZeroGroupedIntegerScale810 *
        alignedSquareCompactToSourceIntegerScale810 :=
  rfl

#print axioms alignedSquareCompactToSourceIntegerScale810_eq_pow
#print axioms alignedSquareClearedIntegerScale810_eq_grouped_mul

/-! ## Source-level numerator at `λ = 0` -/

section AlignedSquareClearedNumerator810

variable {R : Type*} [CommRing R]

/-- The `h^{119}`-cleared source numerator on the aligned face
`λ = 0`.  The ninth-power scalar is specialised here; `b₉` remains an
argument of the primitive, as `alignedSquareSourcePrimitive810` does. -/
def alignedSquareClearedNumerator810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) : R :=
  degreeZeroClearedSource810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4
    b3 b2 b1 0

end AlignedSquareClearedNumerator810

section AlignedSquareClearedNumeratorMap810

variable {R S : Type*} [CommRing R] [CommRing S]

set_option maxHeartbeats 800000000 in
theorem alignedSquareClearedNumerator810_map
    (f : R →+* S)
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) :
    f (alignedSquareClearedNumerator810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7
        b6 b5 b4 b3 b2 b1) =
      alignedSquareClearedNumerator810 (f h) (f a7) (f a6) (f a5) (f a4)
        (f a3) (f a2) (f a1) (f a0) (f b8) (f b7) (f b6) (f b5) (f b4)
        (f b3) (f b2) (f b1) := by
  have h0 : f 0 = 0 := map_zero f
  simpa [alignedSquareClearedNumerator810, h0] using
    degreeZeroClearedSource810_map f h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6
      b5 b4 b3 b2 b1 0

#print axioms alignedSquareClearedNumerator810_map

end AlignedSquareClearedNumeratorMap810

/-! ## Compact = `2^{28} ρ` -/

section AlignedSquareCompactResidual810

variable {F : Type*} [Field F] [CharZero F]

/-- Exact numerical clearing from the grouped primitive to the compact
integer numerator.  Reuses the landed
`rhoResidual810_eq_clearedCompact`. -/
theorem alignedSquareClearedCompact810_eq_scaledRho
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : F) :
    degreeZeroClearedCompact810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0
        W0 =
      (degreeZeroGroupedIntegerScale810 : F) *
        rhoResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 :=
  rhoResidual810_eq_clearedCompact L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0
    V0 W0

#print axioms alignedSquareClearedCompact810_eq_scaledRho

end AlignedSquareCompactResidual810

/-! ## Integer bars on the aligned face `λ = 0` -/

section AlignedSquareBars810

variable {R : Type*} [CommRing R]

def alignedSquareLBar810 : R :=
  (0 : R)

def alignedSquareABar810 (h a7 a6 : R) : R :=
  (16 : R) * a6 * h ^ 8 - (7 : R) * a7 ^ 2

def alignedSquareBBar810 (h a7 a6 a5 : R) : R :=
  (32 : R) * a5 * h ^ 16 - (24 : R) * a6 * a7 * h ^ 8 + (7 : R) * a7 ^ 3

def alignedSquareCBar810 (h a7 a6 a5 a4 : R) : R :=
  (2048 : R) * a4 * h ^ 24 - (1280 : R) * a5 * a7 * h ^ 16 +
    (480 : R) * a6 * a7 ^ 2 * h ^ 8 - (105 : R) * a7 ^ 4

def alignedSquareDBar810 (h a7 a6 a5 a4 a3 : R) : R :=
  (1024 : R) * a3 * h ^ 32 - (512 : R) * a4 * a7 * h ^ 24 +
    (160 : R) * a5 * a7 ^ 2 * h ^ 16 - (40 : R) * a6 * a7 ^ 3 * h ^ 8 +
    (7 : R) * a7 ^ 5

def alignedSquareEBar810 (h a7 a6 a5 a4 a3 a2 : R) : R :=
  (65536 : R) * a2 * h ^ 40 - (24576 : R) * a3 * a7 * h ^ 32 +
    (6144 : R) * a4 * a7 ^ 2 * h ^ 24 - (1280 : R) * a5 * a7 ^ 3 * h ^ 16 +
    (240 : R) * a6 * a7 ^ 4 * h ^ 8 - (35 : R) * a7 ^ 6

def alignedSquareFBar810 (h a7 a6 a5 a4 a3 a2 a1 : R) : R :=
  (131072 : R) * a1 * h ^ 48 - (32768 : R) * a2 * a7 * h ^ 40 +
    (6144 : R) * a3 * a7 ^ 2 * h ^ 32 - (1024 : R) * a4 * a7 ^ 3 * h ^ 24 +
    (160 : R) * a5 * a7 ^ 4 * h ^ 16 - (24 : R) * a6 * a7 ^ 5 * h ^ 8 +
    (3 : R) * a7 ^ 7

def alignedSquareGBar810 (h a7 a6 a5 a4 a3 a2 a1 a0 : R) : R :=
  (16777216 : R) * a0 * h ^ 56 - (2097152 : R) * a1 * a7 * h ^ 48 +
    (262144 : R) * a2 * a7 ^ 2 * h ^ 40 -
    (32768 : R) * a3 * a7 ^ 3 * h ^ 32 +
    (4096 : R) * a4 * a7 ^ 4 * h ^ 24 - (512 : R) * a5 * a7 ^ 5 * h ^ 16 +
    (64 : R) * a6 * a7 ^ 6 * h ^ 8 - (7 : R) * a7 ^ 8

def alignedSquarePBar810 (h a7 b8 : R) : R :=
  -(45 : R) * a7 ^ 2 + (64 : R) * b8 * h ^ 6

def alignedSquareQBar810 (h a7 b8 b7 : R) : R :=
  (64 : R) * b7 * h ^ 14 - (64 : R) * a7 * b8 * h ^ 6 +
    (30 : R) * a7 ^ 3

def alignedSquareRBar810 (h a7 b8 b7 b6 : R) : R :=
  -(315 : R) * a7 ^ 4 + (896 : R) * a7 ^ 2 * b8 * h ^ 6 -
    (1792 : R) * a7 * b7 * h ^ 14 + (2048 : R) * b6 * h ^ 22

def alignedSquareSBar810 (h a7 b8 b7 b6 b5 : R) : R :=
  (252 : R) * a7 ^ 5 - (896 : R) * a7 ^ 3 * b8 * h ^ 6 +
    (2688 : R) * a7 ^ 2 * b7 * h ^ 14 - (6144 : R) * a7 * b6 * h ^ 22 +
    (8192 : R) * b5 * h ^ 30

def alignedSquareTBar810 (h a7 b8 b7 b6 b5 b4 : R) : R :=
  -(525 : R) * a7 ^ 6 + (2240 : R) * a7 ^ 4 * b8 * h ^ 6 -
    (8960 : R) * a7 ^ 3 * b7 * h ^ 14 + (30720 : R) * a7 ^ 2 * b6 * h ^ 22 -
    (81920 : R) * a7 * b5 * h ^ 30 + (131072 : R) * b4 * h ^ 38

def alignedSquareUBar810 (h a7 b8 b7 b6 b5 b4 b3 : R) : R :=
  (90 : R) * a7 ^ 7 - (448 : R) * a7 ^ 5 * b8 * h ^ 6 +
    (2240 : R) * a7 ^ 4 * b7 * h ^ 14 - (10240 : R) * a7 ^ 3 * b6 * h ^ 22 +
    (40960 : R) * a7 ^ 2 * b5 * h ^ 30 - (131072 : R) * a7 * b4 * h ^ 38 +
    (262144 : R) * b3 * h ^ 46

def alignedSquareVBar810 (h a7 b8 b7 b6 b5 b4 b3 b2 : R) : R :=
  -(315 : R) * a7 ^ 8 + (1792 : R) * a7 ^ 6 * b8 * h ^ 6 -
    (10752 : R) * a7 ^ 5 * b7 * h ^ 14 +
    (61440 : R) * a7 ^ 4 * b6 * h ^ 22 -
    (327680 : R) * a7 ^ 3 * b5 * h ^ 30 +
    (1572864 : R) * a7 ^ 2 * b4 * h ^ 38 -
    (6291456 : R) * a7 * b3 * h ^ 46 + (16777216 : R) * b2 * h ^ 54

def alignedSquareWBar810 (h a7 b8 b7 b6 b5 b4 b3 b2 b1 : R) : R :=
  (40 : R) * a7 ^ 9 - (256 : R) * a7 ^ 7 * b8 * h ^ 6 +
    (1792 : R) * a7 ^ 6 * b7 * h ^ 14 - (12288 : R) * a7 ^ 5 * b6 * h ^ 22 +
    (81920 : R) * a7 ^ 4 * b5 * h ^ 30 -
    (524288 : R) * a7 ^ 3 * b4 * h ^ 38 +
    (3145728 : R) * a7 ^ 2 * b3 * h ^ 46 -
    (16777216 : R) * a7 * b2 * h ^ 54 + (67108864 : R) * b1 * h ^ 62

end AlignedSquareBars810

/-! ## Bar identities: `(int) · h^{7d} · X = X̄` on `λ = 0` -/

section AlignedSquareBarEq810

variable {F : Type*} [Field F] [CharZero F]

theorem alignedSquareLBar810_eq
    (h a7 b9 : F) (hh : h ≠ 0)
    (hN : (5 : F) * a7 * h ^ 2 - (4 : F) * b9 = 0) :
    (4 : F) * h ^ 7 *
        depressedL810 h (octicDepressionR810 h a7) b9 =
      alignedSquareLBar810 := by
  have hL := alignedSquareL_eq_zero810 h a7 b9 hh hN
  simp only [alignedSquareLBar810, hL]
  ring

theorem alignedSquareABar810_eq
    (h a7 a6 : F) (hh : h ≠ 0) :
    (16 : F) * h ^ 14 *
        depressedA810 h (octicDepressionR810 h a7) a7 a6 =
      alignedSquareABar810 h a7 a6 := by
  rw [depressedA810_eq_cleared h a7 a6 hh]
  have h16 : (16 : F) ≠ 0 := by norm_num
  have hh14 : h ^ 14 ≠ 0 := pow_ne_zero 14 hh
  field_simp [hh, h16, hh14]
  simp only [alignedSquareABar810]
  ring

theorem alignedSquareBBar810_eq
    (h a7 a6 a5 : F) (hh : h ≠ 0) :
    (32 : F) * h ^ 21 *
        depressedB810 h (octicDepressionR810 h a7) a7 a6 a5 =
      alignedSquareBBar810 h a7 a6 a5 := by
  rw [depressedB810_eq_cleared h a7 a6 a5 hh]
  have h32 : (32 : F) ≠ 0 := by norm_num
  have hh21 : h ^ 21 ≠ 0 := pow_ne_zero 21 hh
  field_simp [hh, h32, hh21]
  simp only [alignedSquareBBar810]
  ring

theorem alignedSquareCBar810_eq
    (h a7 a6 a5 a4 : F) (hh : h ≠ 0) :
    (2048 : F) * h ^ 28 *
        depressedC810 h (octicDepressionR810 h a7) a7 a6 a5 a4 =
      alignedSquareCBar810 h a7 a6 a5 a4 := by
  rw [depressedC810_eq_cleared h a7 a6 a5 a4 hh]
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have hh28 : h ^ 28 ≠ 0 := pow_ne_zero 28 hh
  field_simp [hh, h2048, hh28]
  simp only [alignedSquareCBar810]
  ring

theorem alignedSquareDBar810_eq
    (h a7 a6 a5 a4 a3 : F) (hh : h ≠ 0) :
    (1024 : F) * h ^ 35 *
        depressedD810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 =
      alignedSquareDBar810 h a7 a6 a5 a4 a3 := by
  rw [depressedD810_eq_cleared h a7 a6 a5 a4 a3 hh]
  have h1024 : (1024 : F) ≠ 0 := by norm_num
  have hh35 : h ^ 35 ≠ 0 := pow_ne_zero 35 hh
  field_simp [hh, h1024, hh35]
  simp only [alignedSquareDBar810]
  ring

theorem alignedSquareEBar810_eq
    (h a7 a6 a5 a4 a3 a2 : F) (hh : h ≠ 0) :
    (65536 : F) * h ^ 42 *
        depressedE810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2 =
      alignedSquareEBar810 h a7 a6 a5 a4 a3 a2 := by
  rw [depressedE810_eq_cleared h a7 a6 a5 a4 a3 a2 hh]
  have h65536 : (65536 : F) ≠ 0 := by norm_num
  have hh42 : h ^ 42 ≠ 0 := pow_ne_zero 42 hh
  field_simp [hh, h65536, hh42]
  simp only [alignedSquareEBar810]
  ring

theorem alignedSquareFBar810_eq
    (h a7 a6 a5 a4 a3 a2 a1 : F) (hh : h ≠ 0) :
    (131072 : F) * h ^ 49 *
        depressedF810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2
          a1 =
      alignedSquareFBar810 h a7 a6 a5 a4 a3 a2 a1 := by
  rw [depressedF810_eq_cleared h a7 a6 a5 a4 a3 a2 a1 hh]
  have h131072 : (131072 : F) ≠ 0 := by norm_num
  have hh49 : h ^ 49 ≠ 0 := pow_ne_zero 49 hh
  field_simp [hh, h131072, hh49]
  simp only [alignedSquareFBar810]
  ring

theorem alignedSquareGBar810_eq
    (h a7 a6 a5 a4 a3 a2 a1 a0 : F) (hh : h ≠ 0) :
    (16777216 : F) * h ^ 56 *
        depressedG810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2 a1
          a0 =
      alignedSquareGBar810 h a7 a6 a5 a4 a3 a2 a1 a0 := by
  rw [depressedG810_eq_cleared h a7 a6 a5 a4 a3 a2 a1 a0 hh]
  have h16777216 : (16777216 : F) ≠ 0 := by norm_num
  have hh56 : h ^ 56 ≠ 0 := pow_ne_zero 56 hh
  field_simp [hh, h16777216, hh56]
  simp only [alignedSquareGBar810]
  ring

theorem alignedSquarePBar810_eq
    (h a7 b9 b8 : F) (hh : h ≠ 0)
    (hN : (5 : F) * a7 * h ^ 2 - (4 : F) * b9 = 0) :
    (64 : F) * h ^ 14 *
        depressedP810 h (octicDepressionR810 h a7) b9 b8 =
      alignedSquarePBar810 h a7 b8 := by
  rw [depressedP810_eq_cleared_ninthPower h a7 b9 b8 (0 : F) hh
    (by simpa using hN)]
  have h64 : (64 : F) ≠ 0 := by norm_num
  have hh14 : h ^ 14 ≠ 0 := pow_ne_zero 14 hh
  field_simp [hh, h64, hh14]
  simp only [alignedSquarePBar810]
  ring

theorem alignedSquareQBar810_eq
    (h a7 b9 b8 b7 : F) (hh : h ≠ 0)
    (hN : (5 : F) * a7 * h ^ 2 - (4 : F) * b9 = 0) :
    (64 : F) * h ^ 21 *
        depressedQ810 h (octicDepressionR810 h a7) b9 b8 b7 =
      alignedSquareQBar810 h a7 b8 b7 := by
  rw [depressedQ810_eq_cleared h a7 b9 b8 b7 (0 : F) hh
    (by simpa using hN)]
  have h64 : (64 : F) ≠ 0 := by norm_num
  have hh21 : h ^ 21 ≠ 0 := pow_ne_zero 21 hh
  field_simp [hh, h64, hh21]
  simp only [alignedSquareQBar810]
  ring

theorem alignedSquareRBar810_eq
    (h a7 b9 b8 b7 b6 : F) (hh : h ≠ 0)
    (hN : (5 : F) * a7 * h ^ 2 - (4 : F) * b9 = 0) :
    (2048 : F) * h ^ 28 *
        depressedR810 h (octicDepressionR810 h a7) b9 b8 b7 b6 =
      alignedSquareRBar810 h a7 b8 b7 b6 := by
  rw [depressedR810_eq_cleared h a7 b9 b8 b7 b6 (0 : F) hh
    (by simpa using hN)]
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have hh28 : h ^ 28 ≠ 0 := pow_ne_zero 28 hh
  field_simp [hh, h2048, hh28]
  simp only [alignedSquareRBar810]
  ring

theorem alignedSquareSBar810_eq
    (h a7 b9 b8 b7 b6 b5 : F) (hh : h ≠ 0)
    (hN : (5 : F) * a7 * h ^ 2 - (4 : F) * b9 = 0) :
    (8192 : F) * h ^ 35 *
        depressedS810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 =
      alignedSquareSBar810 h a7 b8 b7 b6 b5 := by
  rw [depressedS810_eq_cleared h a7 b9 b8 b7 b6 b5 (0 : F) hh
    (by simpa using hN)]
  have h8192 : (8192 : F) ≠ 0 := by norm_num
  have hh35 : h ^ 35 ≠ 0 := pow_ne_zero 35 hh
  field_simp [hh, h8192, hh35]
  simp only [alignedSquareSBar810]
  ring

theorem alignedSquareTBar810_eq
    (h a7 b9 b8 b7 b6 b5 b4 : F) (hh : h ≠ 0)
    (hN : (5 : F) * a7 * h ^ 2 - (4 : F) * b9 = 0) :
    (131072 : F) * h ^ 42 *
        depressedT810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4 =
      alignedSquareTBar810 h a7 b8 b7 b6 b5 b4 := by
  rw [depressedT810_eq_cleared h a7 b9 b8 b7 b6 b5 b4 (0 : F) hh
    (by simpa using hN)]
  have h131072 : (131072 : F) ≠ 0 := by norm_num
  have hh42 : h ^ 42 ≠ 0 := pow_ne_zero 42 hh
  field_simp [hh, h131072, hh42]
  simp only [alignedSquareTBar810]
  ring

theorem alignedSquareUBar810_eq
    (h a7 b9 b8 b7 b6 b5 b4 b3 : F) (hh : h ≠ 0)
    (hN : (5 : F) * a7 * h ^ 2 - (4 : F) * b9 = 0) :
    (262144 : F) * h ^ 49 *
        depressedU810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4
          b3 =
      alignedSquareUBar810 h a7 b8 b7 b6 b5 b4 b3 := by
  rw [depressedU810_eq_cleared h a7 b9 b8 b7 b6 b5 b4 b3 (0 : F) hh
    (by simpa using hN)]
  have h262144 : (262144 : F) ≠ 0 := by norm_num
  have hh49 : h ^ 49 ≠ 0 := pow_ne_zero 49 hh
  field_simp [hh, h262144, hh49]
  simp only [alignedSquareUBar810]
  ring

theorem alignedSquareVBar810_eq
    (h a7 b9 b8 b7 b6 b5 b4 b3 b2 : F) (hh : h ≠ 0)
    (hN : (5 : F) * a7 * h ^ 2 - (4 : F) * b9 = 0) :
    (16777216 : F) * h ^ 56 *
        depressedV810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4 b3
          b2 =
      alignedSquareVBar810 h a7 b8 b7 b6 b5 b4 b3 b2 := by
  rw [depressedV810_eq_cleared h a7 b9 b8 b7 b6 b5 b4 b3 b2 (0 : F) hh
    (by simpa using hN)]
  have h16777216 : (16777216 : F) ≠ 0 := by norm_num
  have hh56 : h ^ 56 ≠ 0 := pow_ne_zero 56 hh
  field_simp [hh, h16777216, hh56]
  simp only [alignedSquareVBar810]
  ring

theorem alignedSquareWBar810_eq
    (h a7 b9 b8 b7 b6 b5 b4 b3 b2 b1 : F) (hh : h ≠ 0)
    (hN : (5 : F) * a7 * h ^ 2 - (4 : F) * b9 = 0) :
    (67108864 : F) * h ^ 63 *
        depressedW810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4 b3
          b2 b1 =
      alignedSquareWBar810 h a7 b8 b7 b6 b5 b4 b3 b2 b1 := by
  rw [depressedW810_eq_cleared h a7 b9 b8 b7 b6 b5 b4 b3 b2 b1 (0 : F)
    hh (by simpa using hN)]
  have h67108864 : (67108864 : F) ≠ 0 := by norm_num
  have hh63 : h ^ 63 ≠ 0 := pow_ne_zero 63 hh
  field_simp [hh, h67108864, hh63]
  simp only [alignedSquareWBar810]
  ring

#print axioms alignedSquareLBar810_eq
#print axioms alignedSquareABar810_eq
#print axioms alignedSquareWBar810_eq

end AlignedSquareBarEq810

/-! ## Compact blocks of the 215-term integer numerator -/

section AlignedSquareCompactBlocks810

variable {K : Type*} [CommRing K]

/-- Compact block `0` of `degreeZeroClearedCompact810`. -/
def alignedSquareCompactBlock0_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : K) : K :=
    - (7245315 : K) * L * A ^ 8
    + (66242880 : K) * L * A ^ 6 * C0
    + (198728640 : K) * L * A ^ 5 * B ^ 2
    - (77552640 : K) * L * A ^ 5 * E0
    - (387763200 : K) * L * A ^ 4 * B * D0
    - (193881600 : K) * L * A ^ 4 * C0 ^ 2
    + (94003200 : K) * L * A ^ 4 * G0
    - (775526400 : K) * L * A ^ 3 * B ^ 2 * C0
    + (376012800 : K) * L * A ^ 3 * B * F0

/-- Compact block `1` of `degreeZeroClearedCompact810`. -/
def alignedSquareCompactBlock1_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : K) : K :=
    (376012800 : K) * L * A ^ 3 * C0 * E0
    + (188006400 : K) * L * A ^ 3 * D0 ^ 2
    - (193881600 : K) * L * A ^ 2 * B ^ 4
    + (564019200 : K) * L * A ^ 2 * B ^ 2 * E0
    + (1128038400 : K) * L * A ^ 2 * B * C0 * D0
    + (188006400 : K) * L * A ^ 2 * C0 ^ 3
    - (360972288 : K) * L * A ^ 2 * C0 * G0
    - (360972288 : K) * L * A ^ 2 * D0 * F0
    - (180486144 : K) * L * A ^ 2 * E0 ^ 2

/-- Compact block `2` of `degreeZeroClearedCompact810`. -/
def alignedSquareCompactBlock2_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : K) : K :=
    (376012800 : K) * L * A * B ^ 3 * D0
    + (564019200 : K) * L * A * B ^ 2 * C0 ^ 2
    - (360972288 : K) * L * A * B ^ 2 * G0
    - (721944576 : K) * L * A * B * C0 * F0
    - (721944576 : K) * L * A * B * D0 * E0
    - (360972288 : K) * L * A * C0 ^ 2 * E0
    - (360972288 : K) * L * A * C0 * D0 ^ 2
    + (339738624 : K) * L * A * E0 * G0
    + (169869312 : K) * L * A * F0 ^ 2

/-- Compact block `3` of `degreeZeroClearedCompact810`. -/
def alignedSquareCompactBlock3_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : K) : K :=
    (94003200 : K) * L * B ^ 4 * C0
    - (120324096 : K) * L * B ^ 3 * F0
    - (360972288 : K) * L * B ^ 2 * C0 * E0
    - (180486144 : K) * L * B ^ 2 * D0 ^ 2
    - (360972288 : K) * L * B * C0 ^ 2 * D0
    + (339738624 : K) * L * B * D0 * G0
    + (339738624 : K) * L * B * E0 * F0
    - (30081024 : K) * L * C0 ^ 4
    + (169869312 : K) * L * C0 ^ 2 * G0

/-- Compact block `4` of `degreeZeroClearedCompact810`. -/
def alignedSquareCompactBlock4_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : K) : K :=
    (339738624 : K) * L * C0 * D0 * F0
    + (169869312 : K) * L * C0 * E0 ^ 2
    + (169869312 : K) * L * D0 ^ 2 * E0
    - (150994944 : K) * L * G0 ^ 2
    - (64402800 : K) * A ^ 7 * B
    + (7360320 : K) * A ^ 7 * Q
    + (58882560 : K) * A ^ 6 * B * P
    + (73603200 : K) * A ^ 6 * D0
    - (7180800 : K) * A ^ 6 * S0

/-- Compact block `5` of `degreeZeroClearedCompact810`. -/
def alignedSquareCompactBlock5_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : K) : K :=
    (441619200 : K) * A ^ 5 * B * C0
    - (51701760 : K) * A ^ 5 * B * R
    - (60318720 : K) * A ^ 5 * C0 * Q
    - (68935680 : K) * A ^ 5 * D0 * P
    - (86169600 : K) * A ^ 5 * F0
    + (6266880 : K) * A ^ 5 * U0
    + (368016000 : K) * A ^ 4 * B ^ 3
    - (150796800 : K) * A ^ 4 * B ^ 2 * Q
    - (344678400 : K) * A ^ 4 * B * C0 * P

/-- Compact block `6` of `degreeZeroClearedCompact810`. -/
def alignedSquareCompactBlock6_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : K) : K :=
    - (430848000 : K) * A ^ 4 * B * E0
    + (41779200 : K) * A ^ 4 * B * T0
    - (430848000 : K) * A ^ 4 * C0 * D0
    + (52224000 : K) * A ^ 4 * C0 * S0
    + (62668800 : K) * A ^ 4 * D0 * R
    + (73113600 : K) * A ^ 4 * E0 * Q
    + (83558400 : K) * A ^ 4 * F0 * P
    - (3342336 : K) * A ^ 4 * W0
    - (229785600 : K) * A ^ 3 * B ^ 3 * P

/-- Compact block `7` of `degreeZeroClearedCompact810`. -/
def alignedSquareCompactBlock7_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : K) : K :=
    - (861696000 : K) * A ^ 3 * B ^ 2 * D0
    + (104448000 : K) * A ^ 3 * B ^ 2 * S0
    - (861696000 : K) * A ^ 3 * B * C0 ^ 2
    + (250675200 : K) * A ^ 3 * B * C0 * R
    + (292454400 : K) * A ^ 3 * B * D0 * Q
    + (334233600 : K) * A ^ 3 * B * E0 * P
    + (417792000 : K) * A ^ 3 * B * G0
    - (26738688 : K) * A ^ 3 * B * V0
    + (146227200 : K) * A ^ 3 * C0 ^ 2 * Q

/-- Compact block `8` of `degreeZeroClearedCompact810`. -/
def alignedSquareCompactBlock8_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : K) : K :=
    (334233600 : K) * A ^ 3 * C0 * D0 * P
    + (417792000 : K) * A ^ 3 * C0 * F0
    - (40108032 : K) * A ^ 3 * C0 * U0
    + (417792000 : K) * A ^ 3 * D0 * E0
    - (53477376 : K) * A ^ 3 * D0 * T0
    - (66846720 : K) * A ^ 3 * E0 * S0
    - (80216064 : K) * A ^ 3 * F0 * R
    - (93585408 : K) * A ^ 3 * G0 * Q
    - (861696000 : K) * A ^ 2 * B ^ 3 * C0

/-- Compact block `9` of `degreeZeroClearedCompact810`. -/
def alignedSquareCompactBlock9_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : K) : K :=
    (125337600 : K) * A ^ 2 * B ^ 3 * R
    + (438681600 : K) * A ^ 2 * B ^ 2 * C0 * Q
    + (501350400 : K) * A ^ 2 * B ^ 2 * D0 * P
    + (626688000 : K) * A ^ 2 * B ^ 2 * F0
    - (60162048 : K) * A ^ 2 * B ^ 2 * U0
    + (501350400 : K) * A ^ 2 * B * C0 ^ 2 * P
    + (1253376000 : K) * A ^ 2 * B * C0 * E0
    - (160432128 : K) * A ^ 2 * B * C0 * T0
    + (626688000 : K) * A ^ 2 * B * D0 ^ 2

/-- Compact block `10` of `degreeZeroClearedCompact810`. -/
def alignedSquareCompactBlock10_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : K) : K :=
    - (200540160 : K) * A ^ 2 * B * D0 * S0
    - (240648192 : K) * A ^ 2 * B * E0 * R
    - (280756224 : K) * A ^ 2 * B * F0 * Q
    - (320864256 : K) * A ^ 2 * B * G0 * P
    + (626688000 : K) * A ^ 2 * C0 ^ 2 * D0
    - (100270080 : K) * A ^ 2 * C0 ^ 2 * S0
    - (240648192 : K) * A ^ 2 * C0 * D0 * R
    - (280756224 : K) * A ^ 2 * C0 * E0 * Q
    - (320864256 : K) * A ^ 2 * C0 * F0 * P

/-- Compact block `11` of `degreeZeroClearedCompact810`. -/
def alignedSquareCompactBlock11_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : K) : K :=
    (18874368 : K) * A ^ 2 * C0 * W0
    - (140378112 : K) * A ^ 2 * D0 ^ 2 * Q
    - (320864256 : K) * A ^ 2 * D0 * E0 * P
    - (401080320 : K) * A ^ 2 * D0 * G0
    + (37748736 : K) * A ^ 2 * D0 * V0
    - (401080320 : K) * A ^ 2 * E0 * F0
    + (56623104 : K) * A ^ 2 * E0 * U0
    + (75497472 : K) * A ^ 2 * F0 * T0
    + (94371840 : K) * A ^ 2 * G0 * S0

/-- Compact block `12` of `degreeZeroClearedCompact810`. -/
def alignedSquareCompactBlock12_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : K) : K :=
    - (86169600 : K) * A * B ^ 5
    + (73113600 : K) * A * B ^ 4 * Q
    + (334233600 : K) * A * B ^ 3 * C0 * P
    + (417792000 : K) * A * B ^ 3 * E0
    - (53477376 : K) * A * B ^ 3 * T0
    + (1253376000 : K) * A * B ^ 2 * C0 * D0
    - (200540160 : K) * A * B ^ 2 * C0 * S0
    - (240648192 : K) * A * B ^ 2 * D0 * R
    - (280756224 : K) * A * B ^ 2 * E0 * Q

/-- Compact block `13` of `degreeZeroClearedCompact810`. -/
def alignedSquareCompactBlock13_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : K) : K :=
    - (320864256 : K) * A * B ^ 2 * F0 * P
    + (18874368 : K) * A * B ^ 2 * W0
    + (417792000 : K) * A * B * C0 ^ 3
    - (240648192 : K) * A * B * C0 ^ 2 * R
    - (561512448 : K) * A * B * C0 * D0 * Q
    - (641728512 : K) * A * B * C0 * E0 * P
    - (802160640 : K) * A * B * C0 * G0
    + (75497472 : K) * A * B * C0 * V0
    - (320864256 : K) * A * B * D0 ^ 2 * P

/-- Compact block `14` of `degreeZeroClearedCompact810`. -/
def alignedSquareCompactBlock14_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : K) : K :=
    - (802160640 : K) * A * B * D0 * F0
    + (113246208 : K) * A * B * D0 * U0
    - (401080320 : K) * A * B * E0 ^ 2
    + (150994944 : K) * A * B * E0 * T0
    + (188743680 : K) * A * B * F0 * S0
    + (226492416 : K) * A * B * G0 * R
    - (93585408 : K) * A * C0 ^ 3 * Q
    - (320864256 : K) * A * C0 ^ 2 * D0 * P
    - (401080320 : K) * A * C0 ^ 2 * F0

/-- Compact block `15` of `degreeZeroClearedCompact810`. -/
def alignedSquareCompactBlock15_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : K) : K :=
    (56623104 : K) * A * C0 ^ 2 * U0
    - (802160640 : K) * A * C0 * D0 * E0
    + (150994944 : K) * A * C0 * D0 * T0
    + (188743680 : K) * A * C0 * E0 * S0
    + (226492416 : K) * A * C0 * F0 * R
    + (264241152 : K) * A * C0 * G0 * Q
    - (133693440 : K) * A * D0 ^ 3
    + (94371840 : K) * A * D0 ^ 2 * S0
    + (226492416 : K) * A * D0 * E0 * R

/-- Compact block `16` of `degreeZeroClearedCompact810`. -/
def alignedSquareCompactBlock16_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : K) : K :=
    (264241152 : K) * A * D0 * F0 * Q
    + (301989888 : K) * A * D0 * G0 * P
    + (132120576 : K) * A * E0 ^ 2 * Q
    + (301989888 : K) * A * E0 * F0 * P
    - (33554432 : K) * A * E0 * W0
    + (377487360 : K) * A * F0 * G0
    - (67108864 : K) * A * F0 * V0
    - (100663296 : K) * A * G0 * U0
    + (16711680 : K) * B ^ 5 * P

/-- Compact block `17` of `degreeZeroClearedCompact810`. -/
def alignedSquareCompactBlock17_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : K) : K :=
    (104448000 : K) * B ^ 4 * D0
    - (16711680 : K) * B ^ 4 * S0
    + (208896000 : K) * B ^ 3 * C0 ^ 2
    - (80216064 : K) * B ^ 3 * C0 * R
    - (93585408 : K) * B ^ 3 * D0 * Q
    - (106954752 : K) * B ^ 3 * E0 * P
    - (133693440 : K) * B ^ 3 * G0
    + (12582912 : K) * B ^ 3 * V0
    - (140378112 : K) * B ^ 2 * C0 ^ 2 * Q

/-- Compact block `18` of `degreeZeroClearedCompact810`. -/
def alignedSquareCompactBlock18_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : K) : K :=
    - (320864256 : K) * B ^ 2 * C0 * D0 * P
    - (401080320 : K) * B ^ 2 * C0 * F0
    + (56623104 : K) * B ^ 2 * C0 * U0
    - (401080320 : K) * B ^ 2 * D0 * E0
    + (75497472 : K) * B ^ 2 * D0 * T0
    + (94371840 : K) * B ^ 2 * E0 * S0
    + (113246208 : K) * B ^ 2 * F0 * R
    + (132120576 : K) * B ^ 2 * G0 * Q
    - (106954752 : K) * B * C0 ^ 3 * P

/-- Compact block `19` of `degreeZeroClearedCompact810`. -/
def alignedSquareCompactBlock19_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : K) : K :=
    - (401080320 : K) * B * C0 ^ 2 * E0
    + (75497472 : K) * B * C0 ^ 2 * T0
    - (401080320 : K) * B * C0 * D0 ^ 2
    + (188743680 : K) * B * C0 * D0 * S0
    + (226492416 : K) * B * C0 * E0 * R
    + (264241152 : K) * B * C0 * F0 * Q
    + (301989888 : K) * B * C0 * G0 * P
    + (113246208 : K) * B * D0 ^ 2 * R
    + (264241152 : K) * B * D0 * E0 * Q

/-- Compact block `20` of `degreeZeroClearedCompact810`. -/
def alignedSquareCompactBlock20_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : K) : K :=
    (301989888 : K) * B * D0 * F0 * P
    - (33554432 : K) * B * D0 * W0
    + (150994944 : K) * B * E0 ^ 2 * P
    + (377487360 : K) * B * E0 * G0
    - (67108864 : K) * B * E0 * V0
    + (188743680 : K) * B * F0 ^ 2
    - (100663296 : K) * B * F0 * U0
    - (134217728 : K) * B * G0 * T0
    - (133693440 : K) * C0 ^ 3 * D0

/-- Compact block `21` of `degreeZeroClearedCompact810`. -/
def alignedSquareCompactBlock21_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : K) : K :=
    (31457280 : K) * C0 ^ 3 * S0
    + (113246208 : K) * C0 ^ 2 * D0 * R
    + (132120576 : K) * C0 ^ 2 * E0 * Q
    + (150994944 : K) * C0 ^ 2 * F0 * P
    - (16777216 : K) * C0 ^ 2 * W0
    + (132120576 : K) * C0 * D0 ^ 2 * Q
    + (301989888 : K) * C0 * D0 * E0 * P
    + (377487360 : K) * C0 * D0 * G0
    - (67108864 : K) * C0 * D0 * V0

/-- Compact block `22` of `degreeZeroClearedCompact810`. -/
def alignedSquareCompactBlock22_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : K) : K :=
    (377487360 : K) * C0 * E0 * F0
    - (100663296 : K) * C0 * E0 * U0
    - (134217728 : K) * C0 * F0 * T0
    - (167772160 : K) * C0 * G0 * S0
    + (50331648 : K) * D0 ^ 3 * P
    + (188743680 : K) * D0 ^ 2 * F0
    - (50331648 : K) * D0 ^ 2 * U0
    + (188743680 : K) * D0 * E0 ^ 2
    - (134217728 : K) * D0 * E0 * T0

/-- Compact block `23` of `degreeZeroClearedCompact810`. -/
def alignedSquareCompactBlock23_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : K) : K :=
    - (167772160 : K) * D0 * F0 * S0
    - (201326592 : K) * D0 * G0 * R
    - (83886080 : K) * E0 ^ 2 * S0
    - (201326592 : K) * E0 * F0 * R
    - (234881024 : K) * E0 * G0 * Q
    - (117440512 : K) * F0 ^ 2 * Q
    - (268435456 : K) * F0 * G0 * P
    + (268435456 : K) * G0 * W0

/-- The 215-term compact is the sum of the 24 blocks. -/
theorem alignedSquareClearedCompact810_blockSum
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : K) :
    degreeZeroClearedCompact810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0
        W0 =
      alignedSquareCompactBlock0_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      alignedSquareCompactBlock1_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      alignedSquareCompactBlock2_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      alignedSquareCompactBlock3_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      alignedSquareCompactBlock4_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      alignedSquareCompactBlock5_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      alignedSquareCompactBlock6_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      alignedSquareCompactBlock7_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      alignedSquareCompactBlock8_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      alignedSquareCompactBlock9_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      alignedSquareCompactBlock10_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      alignedSquareCompactBlock11_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      alignedSquareCompactBlock12_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      alignedSquareCompactBlock13_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      alignedSquareCompactBlock14_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      alignedSquareCompactBlock15_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      alignedSquareCompactBlock16_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      alignedSquareCompactBlock17_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      alignedSquareCompactBlock18_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      alignedSquareCompactBlock19_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      alignedSquareCompactBlock20_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      alignedSquareCompactBlock21_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      alignedSquareCompactBlock22_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      alignedSquareCompactBlock23_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 := by
  simp only [degreeZeroClearedCompact810, alignedSquareCompactBlock0_810, alignedSquareCompactBlock1_810, alignedSquareCompactBlock2_810, alignedSquareCompactBlock3_810, alignedSquareCompactBlock4_810, alignedSquareCompactBlock5_810, alignedSquareCompactBlock6_810, alignedSquareCompactBlock7_810, alignedSquareCompactBlock8_810, alignedSquareCompactBlock9_810, alignedSquareCompactBlock10_810, alignedSquareCompactBlock11_810, alignedSquareCompactBlock12_810, alignedSquareCompactBlock13_810, alignedSquareCompactBlock14_810, alignedSquareCompactBlock15_810, alignedSquareCompactBlock16_810, alignedSquareCompactBlock17_810, alignedSquareCompactBlock18_810, alignedSquareCompactBlock19_810, alignedSquareCompactBlock20_810, alignedSquareCompactBlock21_810, alignedSquareCompactBlock22_810, alignedSquareCompactBlock23_810]
  ring

#print axioms alignedSquareClearedCompact810_blockSum

end AlignedSquareCompactBlocks810

/-! ## Compact-block expansions at `λ = 0` -/

section AlignedSquareCompactExpansions810

variable {R : Type*} [CommRing R]

/-- Compact block `0` vanishes on the aligned face. -/
def alignedSquareCompactBlock0Expansion810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) : R :=
  0

/-- Compact block `1` vanishes on the aligned face. -/
def alignedSquareCompactBlock1Expansion810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) : R :=
  0

/-- Compact block `2` vanishes on the aligned face. -/
def alignedSquareCompactBlock2Expansion810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) : R :=
  0

/-- Compact block `3` vanishes on the aligned face. -/
def alignedSquareCompactBlock3Expansion810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) : R :=
  0

set_option maxHeartbeats 200000000 in
/-- Integer expansion of compact block `4` after the extra
`2^{34}` scale, on `λ = 0`. -/
def alignedSquareCompactBlock4Expansion810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    (1264493347523788800 : R) * (h ^ 80) * (a6 ^ 6) * a3
    - (123365204636467200 : R) * (h ^ 78) * (a6 ^ 6) * b5
    - (3319295037249945600 : R) * (h ^ 72) * (a7 ^ 2) * (a6 ^ 5) * a3
    - (632246673761894400 : R) * (h ^ 72) * a7 * (a6 ^ 6) * a4
    - (1106431679083315200 : R) * (h ^ 72) * (a6 ^ 7) * a5
    + (323833662170726400 : R) * (h ^ 70) * (a7 ^ 2) * (a6 ^ 5) * b5
    + (92523903477350400 : R) * (h ^ 70) * a7 * (a6 ^ 6) * b6
    + (126449334752378880 : R) * (h ^ 70) * (a6 ^ 7) * b7
    + (1011594678019031040 : R) * (h ^ 70) * (a6 ^ 6) * a5 * b8
    + (3630478946992128000 : R) * (h ^ 64) * (a7 ^ 4) * (a6 ^ 4) * a3
    + (1659647518624972800 : R) * (h ^ 64) * (a7 ^ 3) * (a6 ^ 5) * a4
    + (2874746594761113600 : R) * (h ^ 64) * (a7 ^ 2) * (a6 ^ 6) * a5
    + (829823759312486400 : R) * (h ^ 64) * a7 * (a6 ^ 8)
    - (354193067999232000 : R) * (h ^ 62) * (a7 ^ 4) * (a6 ^ 4) * b5
    - (242875246628044800 : R) * (h ^ 62) * (a7 ^ 3) * (a6 ^ 5) * b6
    - (427730295450501120 : R) * (h ^ 62) * (a7 ^ 2) * (a6 ^ 6) * b7
    - (2655436029799956480 : R) * (h ^ 62) * (a7 ^ 2) * (a6 ^ 5) * a5 * b8
    - (885145343266652160 : R) * (h ^ 62) * a7 * (a6 ^ 7) * b8
    - (2117779385745408000 : R) * (h ^ 56) * (a7 ^ 6) * (a6 ^ 3) * a3
    - (1815239473496064000 : R) * (h ^ 56) * (a7 ^ 5) * (a6 ^ 4) * a4
    - (3098873101182566400 : R) * (h ^ 56) * (a7 ^ 4) * (a6 ^ 5) * a5
    - (2240030207429836800 : R) * (h ^ 56) * (a7 ^ 3) * (a6 ^ 7)
    + (206612622999552000 : R) * (h ^ 54) * (a7 ^ 6) * (a6 ^ 3) * b5
    + (265644800999424000 : R) * (h ^ 54) * (a7 ^ 5) * (a6 ^ 4) * b6
    + (614524972978667520 : R) * (h ^ 54) * (a7 ^ 4) * (a6 ^ 5) * b7
    + (2904383157593702400 : R) * (h ^ 54) * (a7 ^ 4) * (a6 ^ 4) * a5 * b8
    + (2613607515102904320 : R) * (h ^ 54) * (a7 ^ 3) * (a6 ^ 6) * b8
    + (694896360947712000 : R) * (h ^ 48) * (a7 ^ 8) * (a6 ^ 2) * a3
    + (1058889692872704000 : R) * (h ^ 48) * (a7 ^ 7) * (a6 ^ 3) * a4
    + (1767967612207104000 : R) * (h ^ 48) * (a7 ^ 6) * (a6 ^ 4) * a5
    + (2473790855656243200 : R) * (h ^ 48) * (a7 ^ 5) * (a6 ^ 6)
    - (67794766921728000 : R) * (h ^ 46) * (a7 ^ 8) * (a6 ^ 2) * b5
    - (154959467249664000 : R) * (h ^ 46) * (a7 ^ 7) * (a6 ^ 3) * b6
    - (486830992942694400 : R) * (h ^ 46) * (a7 ^ 6) * (a6 ^ 4) * b7
    - (1694223508596326400 : R) * (h ^ 46) * (a7 ^ 6) * (a6 ^ 3) * a5 * b8
    - (3302850359092838400 : R) * (h ^ 46) * (a7 ^ 5) * (a6 ^ 5) * b8
    - (121606863165849600 : R) * (h ^ 40) * (a7 ^ 10) * a6 * a3
    - (347448180473856000 : R) * (h ^ 40) * (a7 ^ 9) * (a6 ^ 2) * a4
    - (558398861475840000 : R) * (h ^ 40) * (a7 ^ 8) * (a6 ^ 3) * a5
    - (1381249197696614400 : R) * (h ^ 40) * (a7 ^ 7) * (a6 ^ 5)
    + (11864084211302400 : R) * (h ^ 38) * (a7 ^ 10) * a6 * b5
    + (50846075191296000 : R) * (h ^ 38) * (a7 ^ 9) * (a6 ^ 2) * b6
    + (229937251142860800 : R) * (h ^ 38) * (a7 ^ 8) * (a6 ^ 3) * b7
    + (555917088758169600 : R) * (h ^ 38) * (a7 ^ 8) * (a6 ^ 2) * a5 * b8
    + (2315352706488729600 : R) * (h ^ 38) * (a7 ^ 7) * (a6 ^ 4) * b8
    + (8867167105843200 : R) * (h ^ 32) * (a7 ^ 12) * a3
    + (60803431582924800 : R) * (h ^ 32) * (a7 ^ 11) * a6 * a4
    + (90119371810406400 : R) * (h ^ 32) * (a7 ^ 10) * (a6 ^ 2) * a5
    + (356199960281088000 : R) * (h ^ 32) * (a7 ^ 9) * (a6 ^ 4)
    - (865089473740800 : R) * (h ^ 30) * (a7 ^ 12) * b5
    - (8898063158476800 : R) * (h ^ 30) * (a7 ^ 11) * a6 * b6
    - (64807560004239360 : R) * (h ^ 30) * (a7 ^ 10) * (a6 ^ 2) * b7
    - (97285490532679680 : R) * (h ^ 30) * (a7 ^ 10) * a6 * a5 * b8
    - (972289948935782400 : R) * (h ^ 30) * (a7 ^ 9) * (a6 ^ 3) * b8
    - (4433583552921600 : R) * (h ^ 24) * (a7 ^ 13) * a4
    - (4908610362163200 : R) * (h ^ 24) * (a7 ^ 12) * a6 * a5
    + (4817577349939200 : R) * (h ^ 24) * (a7 ^ 11) * (a6 ^ 3)
    + (648817105305600 : R) * (h ^ 22) * (a7 ^ 13) * b6
    + (10099919605923840 : R) * (h ^ 22) * (a7 ^ 12) * a6 * b7
    + (7093733684674560 : R) * (h ^ 22) * (a7 ^ 12) * a5 * b8
    + (244548435805470720 : R) * (h ^ 22) * (a7 ^ 11) * (a6 ^ 2) * b8
    - (207824229043200 : R) * (h ^ 16) * (a7 ^ 14) * a5
    - (27143147740262400 : R) * (h ^ 16) * (a7 ^ 13) * (a6 ^ 2)
    - (671796044451840 : R) * (h ^ 14) * (a7 ^ 14) * b7
    - (34106152502231040 : R) * (h ^ 14) * (a7 ^ 13) * a6 * b8
    + (6374543578233600 : R) * (h ^ 8) * (a7 ^ 15) * a6
    + (2034311965593600 : R) * (h ^ 6) * (a7 ^ 15) * b8
    - (496380990151200 : R) * (a7 ^ 17)

set_option maxHeartbeats 200000000 in
/-- Integer expansion of compact block `5` after the extra
`2^{34}` scale, on `λ = 0`. -/
def alignedSquareCompactBlock5Expansion810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    - (1480382455637606400 : R) * (h ^ 88) * (a6 ^ 5) * a1
    + (107664178591825920 : R) * (h ^ 86) * (a6 ^ 5) * b3
    + (3238336621707264000 : R) * (h ^ 80) * (a7 ^ 2) * (a6 ^ 4) * a1
    + (370095613909401600 : R) * (h ^ 80) * a7 * (a6 ^ 5) * a2
    + (7586960085142732800 : R) * (h ^ 80) * (a6 ^ 5) * a5 * a4
    + (6322466737618944000 : R) * (h ^ 80) * (a6 ^ 4) * (a5 ^ 3)
    - (235515390669619200 : R) * (h ^ 78) * (a7 ^ 2) * (a6 ^ 4) * b3
    - (53832089295912960 : R) * (h ^ 78) * a7 * (a6 ^ 5) * b4
    - (888229473382563840 : R) * (h ^ 78) * (a6 ^ 5) * a5 * b6
    - (1036267718946324480 : R) * (h ^ 78) * (a6 ^ 5) * a4 * b7
    - (1184305964510085120 : R) * (h ^ 78) * (a6 ^ 5) * a3 * b8
    - (2590669297365811200 : R) * (h ^ 78) * (a6 ^ 4) * (a5 ^ 2) * b7
    - (5921529822550425600 : R) * (h ^ 78) * (a6 ^ 4) * a5 * a4 * b8
    - (2833544543993856000 : R) * (h ^ 72) * (a7 ^ 4) * (a6 ^ 3) * a1
    - (809584155426816000 : R) * (h ^ 72) * (a7 ^ 3) * (a6 ^ 4) * a2
    + (763322203688140800 : R) * (h ^ 72) * (a7 ^ 2) * (a6 ^ 5) * a3
    - (12432899529768960000 : R) * (h ^ 72) * (a7 ^ 2) * (a6 ^ 4) * a5 * a4
    - (11064316790833152000 : R) * (h ^ 72) * (a7 ^ 2) * (a6 ^ 3) * (a5 ^ 3)
    - (5690220063857049600 : R) * (h ^ 72) * a7 * (a6 ^ 6) * a4
    - (18967400212856832000 : R) * (h ^ 72) * a7 * (a6 ^ 5) * (a5 ^ 2)
    + (206075966835916800 : R) * (h ^ 70) * (a7 ^ 4) * (a6 ^ 3) * b3
    + (117757695334809600 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 4) * b4
    + (16822527904972800 : R) * (h ^ 70) * (a7 ^ 2) * (a6 ^ 5) * b5
    + (1943001973024358400 : R) * (h ^ 70) * (a7 ^ 2) * (a6 ^ 4) * a5 * b6
    + (2266835635195084800 : R) * (h ^ 70) * (a7 ^ 2) * (a6 ^ 4) * a4 * b7
    + (2590669297365811200 : R) * (h ^ 70) * (a7 ^ 2) * (a6 ^ 4) * a3 * b8
    + (4533671270390169600 : R) * (h ^ 70) * (a7 ^ 2) * (a6 ^ 3) * (a5 ^ 2) * b7
    + (10362677189463244800 : R) * (h ^ 70) * (a7 ^ 2) * (a6 ^ 3) * a5 * a4 * b8
    + (666172105036922880 : R) * (h ^ 70) * a7 * (a6 ^ 6) * b6
    + (5310872059599912960 : R) * (h ^ 70) * a7 * (a6 ^ 5) * a5 * b7
    + (6069568068114186240 : R) * (h ^ 70) * a7 * (a6 ^ 5) * a4 * b8
    + (6291625436459827200 : R) * (h ^ 70) * a7 * (a6 ^ 4) * (a5 ^ 2) * b8
    + (1239675737997312000 : R) * (h ^ 64) * (a7 ^ 6) * (a6 ^ 2) * a1
    + (708386135998464000 : R) * (h ^ 64) * (a7 ^ 5) * (a6 ^ 3) * a2
    - (1669767320567808000 : R) * (h ^ 64) * (a7 ^ 4) * (a6 ^ 4) * a3
    + (7235658389127168000 : R) * (h ^ 64) * (a7 ^ 4) * (a6 ^ 3) * a5 * a4
    + (7260957893984256000 : R) * (h ^ 64) * (a7 ^ 4) * (a6 ^ 2) * (a5 ^ 3)
    + (10093779594982195200 : R) * (h ^ 64) * (a7 ^ 3) * (a6 ^ 5) * a4
    + (35600017548902400000 : R) * (h ^ 64) * (a7 ^ 3) * (a6 ^ 4) * (a5 ^ 2)
    + (16003743929597952000 : R) * (h ^ 64) * (a7 ^ 2) * (a6 ^ 6) * a5
    - (90158235490713600 : R) * (h ^ 62) * (a7 ^ 6) * (a6 ^ 2) * b3
    - (103037983417958400 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 3) * b4
    - (36799279792128000 : R) * (h ^ 62) * (a7 ^ 4) * (a6 ^ 4) * b5
    - (1700126726396313600 : R) * (h ^ 62) * (a7 ^ 4) * (a6 ^ 3) * a5 * b6
    - (1983481180795699200 : R) * (h ^ 62) * (a7 ^ 4) * (a6 ^ 3) * a4 * b7
    - (2266835635195084800 : R) * (h ^ 62) * (a7 ^ 4) * (a6 ^ 3) * a3 * b8
    - (2975221771193548800 : R) * (h ^ 62) * (a7 ^ 4) * (a6 ^ 2) * (a5 ^ 2) * b7
    - (6800506905585254400 : R) * (h ^ 62) * (a7 ^ 4) * (a6 ^ 2) * a5 * a4 * b8
    - (1655757309046947840 : R) * (h ^ 62) * (a7 ^ 3) * (a6 ^ 5) * b6
    - (11050823721576038400 : R) * (h ^ 62) * (a7 ^ 3) * (a6 ^ 4) * a5 * b7
    - (12629512824658329600 : R) * (h ^ 62) * (a7 ^ 3) * (a6 ^ 4) * a4 * b8
    - (11010344513804697600 : R) * (h ^ 62) * (a7 ^ 3) * (a6 ^ 3) * (a5 ^ 2) * b8
    - (2283027318303621120 : R) * (h ^ 62) * (a7 ^ 2) * (a6 ^ 6) * b7
    - (9270895128430510080 : R) * (h ^ 62) * (a7 ^ 2) * (a6 ^ 5) * a5 * b8
    - (271179067686912000 : R) * (h ^ 56) * (a7 ^ 8) * a6 * a1
    - (309918934499328000 : R) * (h ^ 56) * (a7 ^ 7) * (a6 ^ 2) * a2
    + (1461046405496832000 : R) * (h ^ 56) * (a7 ^ 6) * (a6 ^ 3) * a3
    - (1571731739246592000 : R) * (h ^ 56) * (a7 ^ 6) * (a6 ^ 2) * a5 * a4
    - (2117779385745408000 : R) * (h ^ 56) * (a7 ^ 6) * a6 * (a5 ^ 3)
    - (6198378689986560000 : R) * (h ^ 56) * (a7 ^ 5) * (a6 ^ 4) * a4
    - (25995241240657920000 : R) * (h ^ 56) * (a7 ^ 5) * (a6 ^ 3) * (a5 ^ 2)
    - (32672774481562828800 : R) * (h ^ 56) * (a7 ^ 4) * (a6 ^ 5) * a5
    - (4000935982399488000 : R) * (h ^ 56) * (a7 ^ 3) * (a6 ^ 7)
    + (19722114013593600 : R) * (h ^ 54) * (a7 ^ 8) * a6 * b3
    + (45079117745356800 : R) * (h ^ 54) * (a7 ^ 7) * (a6 ^ 2) * b4
    + (32199369818112000 : R) * (h ^ 54) * (a7 ^ 6) * (a6 ^ 3) * b5
    + (743805442798387200 : R) * (h ^ 54) * (a7 ^ 6) * (a6 ^ 2) * a5 * b6
    + (867773016598118400 : R) * (h ^ 54) * (a7 ^ 6) * (a6 ^ 2) * a4 * b7
    + (991740590397849600 : R) * (h ^ 54) * (a7 ^ 6) * (a6 ^ 2) * a3 * b8
    + (867773016598118400 : R) * (h ^ 54) * (a7 ^ 6) * a6 * (a5 ^ 2) * b7
    + (1983481180795699200 : R) * (h ^ 54) * (a7 ^ 6) * a6 * a5 * a4 * b8
    + (1709326546344345600 : R) * (h ^ 54) * (a7 ^ 5) * (a6 ^ 4) * b6
    + (9173600461180108800 : R) * (h ^ 54) * (a7 ^ 5) * (a6 ^ 3) * a5 * b7
    + (10484114812777267200 : R) * (h ^ 54) * (a7 ^ 5) * (a6 ^ 3) * a4 * b8
    + (7225538587184332800 : R) * (h ^ 54) * (a7 ^ 5) * (a6 ^ 2) * (a5 ^ 2) * b8
    + (5430699714423029760 : R) * (h ^ 54) * (a7 ^ 4) * (a6 ^ 5) * b7
    + (19004988048644505600 : R) * (h ^ 54) * (a7 ^ 4) * (a6 ^ 4) * a5 * b8
    + (3078732888208834560 : R) * (h ^ 54) * (a7 ^ 3) * (a6 ^ 6) * b8
    + (23728168422604800 : R) * (h ^ 48) * (a7 ^ 10) * a1
    + (67794766921728000 : R) * (h ^ 48) * (a7 ^ 9) * a6 * a2
    - (639207802404864000 : R) * (h ^ 48) * (a7 ^ 8) * (a6 ^ 2) * a3
    - (4842483351552000 : R) * (h ^ 48) * (a7 ^ 8) * a6 * a5 * a4
    + (231632120315904000 : R) * (h ^ 48) * (a7 ^ 8) * (a5 ^ 3)
    + (1057044937310208000 : R) * (h ^ 48) * (a7 ^ 7) * (a6 ^ 3) * a4
    + (9117704367636480000 : R) * (h ^ 48) * (a7 ^ 7) * (a6 ^ 2) * (a5 ^ 2)
    + (26514078742609920000 : R) * (h ^ 48) * (a7 ^ 6) * (a6 ^ 4) * a5
    + (8936169125865062400 : R) * (h ^ 48) * (a7 ^ 5) * (a6 ^ 6)
    - (1725684976189440 : R) * (h ^ 46) * (a7 ^ 10) * b3
    - (9861057006796800 : R) * (h ^ 46) * (a7 ^ 9) * a6 * b4
    - (14087224295424000 : R) * (h ^ 46) * (a7 ^ 8) * (a6 ^ 2) * b5
    - (162707440612147200 : R) * (h ^ 46) * (a7 ^ 8) * a6 * a5 * b6
    - (189825347380838400 : R) * (h ^ 46) * (a7 ^ 8) * a6 * a4 * b7
    - (216943254149529600 : R) * (h ^ 46) * (a7 ^ 8) * a6 * a3 * b8
    - (94912673690419200 : R) * (h ^ 46) * (a7 ^ 8) * (a5 ^ 2) * b7
    - (216943254149529600 : R) * (h ^ 46) * (a7 ^ 8) * a5 * a4 * b8
    - (937806645952512000 : R) * (h ^ 46) * (a7 ^ 7) * (a6 ^ 3) * b6
    - (3796506947616768000 : R) * (h ^ 46) * (a7 ^ 7) * (a6 ^ 2) * a5 * b7
    - (4338865082990592000 : R) * (h ^ 46) * (a7 ^ 7) * (a6 ^ 2) * a4 * b8
    - (2107448754595430400 : R) * (h ^ 46) * (a7 ^ 7) * a6 * (a5 ^ 2) * b8
    - (5355862054089523200 : R) * (h ^ 46) * (a7 ^ 6) * (a6 ^ 4) * b7
    - (15513656378366361600 : R) * (h ^ 46) * (a7 ^ 6) * (a6 ^ 3) * a5 * b8
    - (7169557682800558080 : R) * (h ^ 46) * (a7 ^ 5) * (a6 ^ 5) * b8
    - (5932042105651200 : R) * (h ^ 40) * (a7 ^ 11) * a2
    + (139826706776064000 : R) * (h ^ 40) * (a7 ^ 10) * a6 * a3
    + (30931362408038400 : R) * (h ^ 40) * (a7 ^ 10) * a5 * a4
    + (405557980692480000 : R) * (h ^ 40) * (a7 ^ 9) * (a6 ^ 2) * a4
    - (1501169838981120000 : R) * (h ^ 40) * (a7 ^ 9) * a6 * (a5 ^ 2)
    - (10665050744291328000 : R) * (h ^ 40) * (a7 ^ 8) * (a6 ^ 3) * a5
    - (8102608068044390400 : R) * (h ^ 40) * (a7 ^ 7) * (a6 ^ 5)
    + (862842488094720 : R) * (h ^ 38) * (a7 ^ 11) * b4
    + (3081580314624000 : R) * (h ^ 38) * (a7 ^ 10) * a6 * b5
    + (14236901053562880 : R) * (h ^ 38) * (a7 ^ 10) * a5 * b6
    + (16609717895823360 : R) * (h ^ 38) * (a7 ^ 10) * a4 * b7
    + (18982534738083840 : R) * (h ^ 38) * (a7 ^ 10) * a3 * b8
    + (288259827145113600 : R) * (h ^ 38) * (a7 ^ 9) * (a6 ^ 2) * b6
    + (783029557945958400 : R) * (h ^ 38) * (a7 ^ 9) * a6 * a5 * b7
    + (894890923366809600 : R) * (h ^ 38) * (a7 ^ 9) * a6 * a4 * b8
    + (230502207533875200 : R) * (h ^ 38) * (a7 ^ 9) * (a5 ^ 2) * b8
    + (2801684776904294400 : R) * (h ^ 38) * (a7 ^ 8) * (a6 ^ 3) * b7
    + (6299102343698841600 : R) * (h ^ 38) * (a7 ^ 8) * (a6 ^ 2) * a5 * b8
    + (6908274171445248000 : R) * (h ^ 38) * (a7 ^ 7) * (a6 ^ 4) * b8
    - (12234836842905600 : R) * (h ^ 32) * (a7 ^ 12) * a3
    - (187388972944588800 : R) * (h ^ 32) * (a7 ^ 11) * a6 * a4
    + (88186161659904000 : R) * (h ^ 32) * (a7 ^ 11) * (a5 ^ 2)
    + (2113592655347712000 : R) * (h ^ 32) * (a7 ^ 10) * (a6 ^ 2) * a5
    + (3748104200257536000 : R) * (h ^ 32) * (a7 ^ 9) * (a6 ^ 4)
    - (269638277529600 : R) * (h ^ 30) * (a7 ^ 12) * b5
    - (47040323502735360 : R) * (h ^ 30) * (a7 ^ 11) * a6 * b6
    - (64362656846315520 : R) * (h ^ 30) * (a7 ^ 11) * a5 * b7
    - (73557322110074880 : R) * (h ^ 30) * (a7 ^ 11) * a4 * b8
    - (819392205658521600 : R) * (h ^ 30) * (a7 ^ 10) * (a6 ^ 2) * b7
    - (1271151879782400000 : R) * (h ^ 30) * (a7 ^ 10) * a6 * a5 * b8
    - (3522774570526310400 : R) * (h ^ 30) * (a7 ^ 9) * (a6 ^ 3) * b8
    + (21040211843481600 : R) * (h ^ 24) * (a7 ^ 13) * a4
    - (160532579192832000 : R) * (h ^ 24) * (a7 ^ 12) * a6 * a5
    - (886332495691776000 : R) * (h ^ 24) * (a7 ^ 11) * (a6 ^ 3)
    + (3181731674849280 : R) * (h ^ 22) * (a7 ^ 13) * b6
    + (126947386300170240 : R) * (h ^ 22) * (a7 ^ 12) * a6 * b7
    + (101882823164559360 : R) * (h ^ 22) * (a7 ^ 12) * a5 * b8
    + (1001821760284262400 : R) * (h ^ 22) * (a7 ^ 11) * (a6 ^ 2) * b8
    - (1139774691686400 : R) * (h ^ 16) * (a7 ^ 14) * a5
    + (79862337321984000 : R) * (h ^ 16) * (a7 ^ 13) * (a6 ^ 2)
    - (8133069873438720 : R) * (h ^ 14) * (a7 ^ 14) * b7
    - (150503660320849920 : R) * (h ^ 14) * (a7 ^ 13) * a6 * b8
    + (4849434202099200 : R) * (h ^ 8) * (a7 ^ 15) * a6
    + (9321584843612160 : R) * (h ^ 6) * (a7 ^ 15) * b8
    - (1020690212539200 : R) * (a7 ^ 17)

set_option maxHeartbeats 200000000 in
/-- Integer expansion of compact block `6` after the extra
`2^{34}` scale, on `λ = 0`. -/
def alignedSquareCompactBlock6Expansion810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    - (57420895248973824 : R) * (h ^ 94) * (a6 ^ 4) * b1
    - (7401912278188032000 : R) * (h ^ 88) * (a6 ^ 4) * a5 * a2
    - (7401912278188032000 : R) * (h ^ 88) * (a6 ^ 4) * a4 * a3
    + (100486566685704192 : R) * (h ^ 86) * (a7 ^ 2) * (a6 ^ 3) * b1
    + (14355223812243456 : R) * (h ^ 86) * a7 * (a6 ^ 4) * b2
    + (717761190612172800 : R) * (h ^ 86) * (a6 ^ 4) * a5 * b4
    + (897201488265216000 : R) * (h ^ 86) * (a6 ^ 4) * a4 * b5
    + (1076641785918259200 : R) * (h ^ 86) * (a6 ^ 4) * a3 * b6
    + (1256082083571302400 : R) * (h ^ 86) * (a6 ^ 4) * a2 * b7
    + (1435522381224345600 : R) * (h ^ 86) * (a6 ^ 4) * a1 * b8
    - (1009351674298368000 : R) * (h ^ 80) * (a7 ^ 2) * (a6 ^ 4) * a1
    + (12953346486829056000 : R) * (h ^ 80) * (a7 ^ 2) * (a6 ^ 3) * a5 * a2
    + (12953346486829056000 : R) * (h ^ 80) * (a7 ^ 2) * (a6 ^ 3) * a4 * a3
    + (5551434208641024000 : R) * (h ^ 80) * a7 * (a6 ^ 5) * a2
    + (7401912278188032000 : R) * (h ^ 80) * a7 * (a6 ^ 4) * a5 * a3
    + (3700956139094016000 : R) * (h ^ 80) * a7 * (a6 ^ 4) * (a4 ^ 2)
    - (65944309387493376 : R) * (h ^ 78) * (a7 ^ 4) * (a6 ^ 2) * b1
    - (25121641671426048 : R) * (h ^ 78) * (a7 ^ 3) * (a6 ^ 3) * b2
    - (2691604464795648 : R) * (h ^ 78) * (a7 ^ 2) * (a6 ^ 4) * b3
    - (1256082083571302400 : R) * (h ^ 78) * (a7 ^ 2) * (a6 ^ 3) * a5 * b4
    - (1570102604464128000 : R) * (h ^ 78) * (a7 ^ 2) * (a6 ^ 3) * a4 * b5
    - (1884123125356953600 : R) * (h ^ 78) * (a7 ^ 2) * (a6 ^ 3) * a3 * b6
    - (2198143646249779200 : R) * (h ^ 78) * (a7 ^ 2) * (a6 ^ 3) * a2 * b7
    - (2512164167142604800 : R) * (h ^ 78) * (a7 ^ 2) * (a6 ^ 3) * a1 * b8
    - (538320892959129600 : R) * (h ^ 78) * a7 * (a6 ^ 5) * b4
    - (1009351674298368000 : R) * (h ^ 78) * a7 * (a6 ^ 4) * a5 * b5
    - (1211222009158041600 : R) * (h ^ 78) * a7 * (a6 ^ 4) * a4 * b6
    - (1413092344017715200 : R) * (h ^ 78) * a7 * (a6 ^ 4) * a3 * b7
    - (1614962678877388800 : R) * (h ^ 78) * a7 * (a6 ^ 4) * a2 * b8
    - (3947686548366950400 : R) * (h ^ 78) * (a6 ^ 3) * (a5 ^ 3) * b8
    + (1766365430022144000 : R) * (h ^ 72) * (a7 ^ 4) * (a6 ^ 3) * a1
    - (8500633631981568000 : R) * (h ^ 72) * (a7 ^ 4) * (a6 ^ 2) * a5 * a2
    - (8500633631981568000 : R) * (h ^ 72) * (a7 ^ 4) * (a6 ^ 2) * a4 * a3
    - (10493051780726784000 : R) * (h ^ 72) * (a7 ^ 3) * (a6 ^ 4) * a2
    - (12953346486829056000 : R) * (h ^ 72) * (a7 ^ 3) * (a6 ^ 3) * a5 * a3
    - (6476673243414528000 : R) * (h ^ 72) * (a7 ^ 3) * (a6 ^ 3) * (a4 ^ 2)
    - (3816611018440704000 : R) * (h ^ 72) * (a7 ^ 2) * (a6 ^ 5) * a3
    - (4163575656480768000 : R) * (h ^ 72) * (a7 ^ 2) * (a6 ^ 4) * a5 * a4
    + (2775717104320512000 : R) * (h ^ 72) * (a7 ^ 2) * (a6 ^ 3) * (a5 ^ 3)
    + (19233756904685568 : R) * (h ^ 70) * (a7 ^ 6) * a6 * b1
    + (16486077346873344 : R) * (h ^ 70) * (a7 ^ 5) * (a6 ^ 2) * b2
    + (4710307813392384 : R) * (h ^ 70) * (a7 ^ 4) * (a6 ^ 3) * b3
    + (824303867343667200 : R) * (h ^ 70) * (a7 ^ 4) * (a6 ^ 2) * a5 * b4
    + (1030379834179584000 : R) * (h ^ 70) * (a7 ^ 4) * (a6 ^ 2) * a4 * b5
    + (1236455801015500800 : R) * (h ^ 70) * (a7 ^ 4) * (a6 ^ 2) * a3 * b6
    + (1442531767851417600 : R) * (h ^ 70) * (a7 ^ 4) * (a6 ^ 2) * a2 * b7
    + (1648607734687334400 : R) * (h ^ 70) * (a7 ^ 4) * (a6 ^ 2) * a1 * b8
    + (1099520423869022208 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 4) * b4
    + (1766365430022144000 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 3) * a5 * b5
    + (2119638516026572800 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 3) * a4 * b6
    + (2472911602031001600 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 3) * a3 * b7
    + (2826184688035430400 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 3) * a2 * b8
    + (546732156911616000 : R) * (h ^ 70) * (a7 ^ 2) * (a6 ^ 5) * b5
    + (757013755723776000 : R) * (h ^ 70) * (a7 ^ 2) * (a6 ^ 4) * a5 * b6
    + (883182715011072000 : R) * (h ^ 70) * (a7 ^ 2) * (a6 ^ 4) * a4 * b7
    + (1009351674298368000 : R) * (h ^ 70) * (a7 ^ 2) * (a6 ^ 4) * a3 * b8
    + (5181338594731622400 : R) * (h ^ 70) * (a7 ^ 2) * (a6 ^ 2) * (a5 ^ 3) * b8
    + (8882294733825638400 : R) * (h ^ 70) * a7 * (a6 ^ 4) * (a5 ^ 2) * b8
    - (1159177313452032000 : R) * (h ^ 64) * (a7 ^ 6) * (a6 ^ 2) * a1
    + (2479351475994624000 : R) * (h ^ 64) * (a7 ^ 6) * a6 * a5 * a2
    + (2479351475994624000 : R) * (h ^ 64) * (a7 ^ 6) * a6 * a4 * a3
    + (7737048576294912000 : R) * (h ^ 64) * (a7 ^ 5) * (a6 ^ 3) * a2
    + (8500633631981568000 : R) * (h ^ 64) * (a7 ^ 5) * (a6 ^ 2) * a5 * a3
    + (4250316815990784000 : R) * (h ^ 64) * (a7 ^ 5) * (a6 ^ 2) * (a4 ^ 2)
    + (7232044174147584000 : R) * (h ^ 64) * (a7 ^ 4) * (a6 ^ 4) * a3
    + (7286257398841344000 : R) * (h ^ 64) * (a7 ^ 4) * (a6 ^ 3) * a5 * a4
    - (3643128699420672000 : R) * (h ^ 64) * (a7 ^ 4) * (a6 ^ 2) * (a5 ^ 3)
    + (1676995750526976000 : R) * (h ^ 64) * (a7 ^ 3) * (a6 ^ 5) * a4
    - (5377951889620992000 : R) * (h ^ 64) * (a7 ^ 3) * (a6 ^ 4) * (a5 ^ 2)
    - (2103692161449984 : R) * (h ^ 62) * (a7 ^ 8) * b1
    - (4808439226171392 : R) * (h ^ 62) * (a7 ^ 7) * a6 * b2
    - (3091139502538752 : R) * (h ^ 62) * (a7 ^ 6) * (a6 ^ 2) * b3
    - (240421961308569600 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a5 * b4
    - (300527451635712000 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a4 * b5
    - (360632941962854400 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a3 * b6
    - (420738432289996800 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a2 * b7
    - (480843922617139200 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a1 * b8
    - (893780907591204864 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 3) * b4
    - (1159177313452032000 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 2) * a5 * b5
    - (1391012776142438400 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 2) * a4 * b6
    - (1622848238832844800 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 2) * a3 * b7
    - (1854683701523251200 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 2) * a2 * b8
    - (1100981880980766720 : R) * (h ^ 62) * (a7 ^ 4) * (a6 ^ 4) * b5
    - (1324774072516608000 : R) * (h ^ 62) * (a7 ^ 4) * (a6 ^ 3) * a5 * b6
    - (1545569751269376000 : R) * (h ^ 62) * (a7 ^ 4) * (a6 ^ 3) * a4 * b7
    - (1766365430022144000 : R) * (h ^ 62) * (a7 ^ 4) * (a6 ^ 3) * a3 * b8
    - (2266835635195084800 : R) * (h ^ 62) * (a7 ^ 4) * a6 * (a5 ^ 3) * b8
    - (325936478158848000 : R) * (h ^ 62) * (a7 ^ 3) * (a6 ^ 5) * b6
    - (404792077713408000 : R) * (h ^ 62) * (a7 ^ 3) * (a6 ^ 4) * a5 * b7
    - (462619517386752000 : R) * (h ^ 62) * (a7 ^ 3) * (a6 ^ 4) * a4 * b8
    - (14248681135511961600 : R) * (h ^ 62) * (a7 ^ 3) * (a6 ^ 3) * (a5 ^ 2) * b8
    - (6661721050369228800 : R) * (h ^ 62) * (a7 ^ 2) * (a6 ^ 5) * a5 * b8
    + (338093383090176000 : R) * (h ^ 56) * (a7 ^ 8) * a6 * a1
    - (271179067686912000 : R) * (h ^ 56) * (a7 ^ 8) * a5 * a2
    - (271179067686912000 : R) * (h ^ 56) * (a7 ^ 8) * a4 * a3
    - (2753046119448576000 : R) * (h ^ 56) * (a7 ^ 7) * (a6 ^ 2) * a2
    - (2479351475994624000 : R) * (h ^ 56) * (a7 ^ 7) * a6 * a5 * a3
    - (1239675737997312000 : R) * (h ^ 56) * (a7 ^ 7) * a6 * (a4 ^ 2)
    - (5350845277274112000 : R) * (h ^ 56) * (a7 ^ 6) * (a6 ^ 3) * a3
    - (4781606417989632000 : R) * (h ^ 56) * (a7 ^ 6) * (a6 ^ 2) * a5 * a4
    + (1593868805996544000 : R) * (h ^ 56) * (a7 ^ 6) * a6 * (a5 ^ 3)
    - (3153402569687040000 : R) * (h ^ 56) * (a7 ^ 5) * (a6 ^ 4) * a4
    + (8500633631981568000 : R) * (h ^ 56) * (a7 ^ 5) * (a6 ^ 3) * (a5 ^ 2)
    + (4096712679358464000 : R) * (h ^ 56) * (a7 ^ 4) * (a6 ^ 5) * a5
    + (525923040362496 : R) * (h ^ 54) * (a7 ^ 9) * b2
    + (901582354907136 : R) * (h ^ 54) * (a7 ^ 8) * a6 * b3
    + (26296152018124800 : R) * (h ^ 54) * (a7 ^ 8) * a5 * b4
    + (32870190022656000 : R) * (h ^ 54) * (a7 ^ 8) * a4 * b5
    + (39444228027187200 : R) * (h ^ 54) * (a7 ^ 8) * a3 * b6
    + (46018266031718400 : R) * (h ^ 54) * (a7 ^ 8) * a2 * b7
    + (52592304036249600 : R) * (h ^ 54) * (a7 ^ 8) * a1 * b8
    + (361148131879944192 : R) * (h ^ 54) * (a7 ^ 7) * (a6 ^ 2) * b4
    + (338093383090176000 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a5 * b5
    + (405712059708211200 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a4 * b6
    + (473330736326246400 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a3 * b7
    + (540949412944281600 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a2 * b8
    + (880238772627701760 : R) * (h ^ 54) * (a7 ^ 6) * (a6 ^ 3) * b5
    + (869382985089024000 : R) * (h ^ 54) * (a7 ^ 6) * (a6 ^ 2) * a5 * b6
    + (1014280149270528000 : R) * (h ^ 54) * (a7 ^ 6) * (a6 ^ 2) * a4 * b7
    + (1159177313452032000 : R) * (h ^ 54) * (a7 ^ 6) * (a6 ^ 2) * a3 * b8
    + (330580196799283200 : R) * (h ^ 54) * (a7 ^ 6) * (a5 ^ 3) * b8
    + (649057811413598208 : R) * (h ^ 54) * (a7 ^ 5) * (a6 ^ 4) * b6
    + (708386135998464000 : R) * (h ^ 54) * (a7 ^ 5) * (a6 ^ 3) * a5 * b7
    + (809584155426816000 : R) * (h ^ 54) * (a7 ^ 5) * (a6 ^ 3) * a4 * b8
    + (8500633631981568000 : R) * (h ^ 54) * (a7 ^ 5) * (a6 ^ 2) * (a5 ^ 2) * b8
    + (147197119168512000 : R) * (h ^ 54) * (a7 ^ 4) * (a6 ^ 5) * b7
    + (12802995143678361600 : R) * (h ^ 54) * (a7 ^ 4) * (a6 ^ 4) * a5 * b8
    + (1665430262592307200 : R) * (h ^ 54) * (a7 ^ 3) * (a6 ^ 6) * b8
    - (36978963775488000 : R) * (h ^ 48) * (a7 ^ 10) * a1
    + (463997950230528000 : R) * (h ^ 48) * (a7 ^ 9) * a6 * a2
    + (271179067686912000 : R) * (h ^ 48) * (a7 ^ 9) * a5 * a3
    + (135589533843456000 : R) * (h ^ 48) * (a7 ^ 9) * (a4 ^ 2)
    + (1913472707198976000 : R) * (h ^ 48) * (a7 ^ 8) * (a6 ^ 2) * a3
    + (1394635205246976000 : R) * (h ^ 48) * (a7 ^ 8) * a6 * a5 * a4
    - (232439200874496000 : R) * (h ^ 48) * (a7 ^ 8) * (a5 ^ 3)
    + (2308579818209280000 : R) * (h ^ 48) * (a7 ^ 7) * (a6 ^ 3) * a4
    - (4980840018739200000 : R) * (h ^ 48) * (a7 ^ 7) * (a6 ^ 2) * (a5 ^ 2)
    - (7784567289151488000 : R) * (h ^ 48) * (a7 ^ 6) * (a6 ^ 4) * a5
    - (1082909163257856000 : R) * (h ^ 48) * (a7 ^ 5) * (a6 ^ 6)
    - (98610570067968 : R) * (h ^ 46) * (a7 ^ 10) * b3
    - (72464681775661056 : R) * (h ^ 46) * (a7 ^ 9) * a6 * b4
    - (36978963775488000 : R) * (h ^ 46) * (a7 ^ 9) * a5 * b5
    - (44374756530585600 : R) * (h ^ 46) * (a7 ^ 9) * a4 * b6
    - (51770549285683200 : R) * (h ^ 46) * (a7 ^ 9) * a3 * b7
    - (59166342040780800 : R) * (h ^ 46) * (a7 ^ 9) * a2 * b8
    - (348739299736289280 : R) * (h ^ 46) * (a7 ^ 8) * (a6 ^ 2) * b5
    - (253570037317632000 : R) * (h ^ 46) * (a7 ^ 8) * a6 * a5 * b6
    - (295831710203904000 : R) * (h ^ 46) * (a7 ^ 8) * a6 * a4 * b7
    - (338093383090176000 : R) * (h ^ 46) * (a7 ^ 8) * a6 * a3 * b8
    - (511988379747876864 : R) * (h ^ 46) * (a7 ^ 7) * (a6 ^ 3) * b6
    - (464878401748992000 : R) * (h ^ 46) * (a7 ^ 7) * (a6 ^ 2) * a5 * b7
    - (531289601998848000 : R) * (h ^ 46) * (a7 ^ 7) * (a6 ^ 2) * a4 * b8
    - (2231416328395161600 : R) * (h ^ 46) * (a7 ^ 7) * a6 * (a5 ^ 2) * b8
    - (290533763891331072 : R) * (h ^ 46) * (a7 ^ 6) * (a6 ^ 4) * b7
    - (9795968280664473600 : R) * (h ^ 46) * (a7 ^ 6) * (a6 ^ 3) * a5 * b8
    - (3698590471107379200 : R) * (h ^ 46) * (a7 ^ 5) * (a6 ^ 5) * b8
    - (28504617910272000 : R) * (h ^ 40) * (a7 ^ 11) * a2
    - (325051694972928000 : R) * (h ^ 40) * (a7 ^ 10) * a6 * a3
    - (152538225573888000 : R) * (h ^ 40) * (a7 ^ 10) * a5 * a4
    - (812845419724800000 : R) * (h ^ 40) * (a7 ^ 9) * (a6 ^ 2) * a4
    + (1278415604809728000 : R) * (h ^ 40) * (a7 ^ 9) * a6 * (a5 ^ 2)
    + (5881245443555328000 : R) * (h ^ 40) * (a7 ^ 8) * (a6 ^ 3) * a5
    + (2389263060566016000 : R) * (h ^ 40) * (a7 ^ 7) * (a6 ^ 5)
    + (5768718348976128 : R) * (h ^ 38) * (a7 ^ 11) * b4
    + (68331842347991040 : R) * (h ^ 38) * (a7 ^ 10) * a6 * b5
    + (27734222831616000 : R) * (h ^ 38) * (a7 ^ 10) * a5 * b6
    + (32356593303552000 : R) * (h ^ 38) * (a7 ^ 10) * a4 * b7
    + (36978963775488000 : R) * (h ^ 38) * (a7 ^ 10) * a3 * b8
    + (199522388847624192 : R) * (h ^ 38) * (a7 ^ 9) * (a6 ^ 2) * b6
    + (135589533843456000 : R) * (h ^ 38) * (a7 ^ 9) * a6 * a5 * b7
    + (154959467249664000 : R) * (h ^ 38) * (a7 ^ 9) * a6 * a4 * b8
    + (216943254149529600 : R) * (h ^ 38) * (a7 ^ 9) * (a5 ^ 2) * b8
    + (226689600901349376 : R) * (h ^ 38) * (a7 ^ 8) * (a6 ^ 3) * b7
    + (3732309454041907200 : R) * (h ^ 38) * (a7 ^ 8) * (a6 ^ 2) * a5 * b8
    + (3402691897926352896 : R) * (h ^ 38) * (a7 ^ 7) * (a6 ^ 4) * b8
    + (20258983084032000 : R) * (h ^ 32) * (a7 ^ 12) * a3
    + (134681568215040000 : R) * (h ^ 32) * (a7 ^ 11) * a6 * a4
    - (120759428579328000 : R) * (h ^ 32) * (a7 ^ 11) * (a5 ^ 2)
    - (2209642447896576000 : R) * (h ^ 32) * (a7 ^ 10) * (a6 ^ 2) * a5
    - (2183221717122416640 : R) * (h ^ 32) * (a7 ^ 9) * (a6 ^ 4)
    - (5282984251883520 : R) * (h ^ 30) * (a7 ^ 12) * b5
    - (38292157215277056 : R) * (h ^ 30) * (a7 ^ 11) * a6 * b6
    - (14830105264128000 : R) * (h ^ 30) * (a7 ^ 11) * a5 * b7
    - (16948691730432000 : R) * (h ^ 30) * (a7 ^ 11) * a4 * b8
    - (87133444299030528 : R) * (h ^ 30) * (a7 ^ 10) * (a6 ^ 2) * b7
    - (708939562667212800 : R) * (h ^ 30) * (a7 ^ 10) * a6 * a5 * b8
    - (1659482592686112768 : R) * (h ^ 30) * (a7 ^ 9) * (a6 ^ 3) * b8
    - (8010905075712000 : R) * (h ^ 24) * (a7 ^ 13) * a4
    + (413398642212864000 : R) * (h ^ 24) * (a7 ^ 12) * a6 * a5
    + (1057468658346885120 : R) * (h ^ 24) * (a7 ^ 11) * (a6 ^ 3)
    + (2882144288636928 : R) * (h ^ 22) * (a7 ^ 13) * b6
    + (16425978669563904 : R) * (h ^ 22) * (a7 ^ 12) * a6 * b7
    + (53812096244121600 : R) * (h ^ 22) * (a7 ^ 12) * a5 * b8
    + (452270902009135104 : R) * (h ^ 22) * (a7 ^ 11) * (a6 ^ 2) * b8
    - (30885018329088000 : R) * (h ^ 16) * (a7 ^ 14) * a5
    - (286300781982351360 : R) * (h ^ 16) * (a7 ^ 13) * (a6 ^ 2)
    - (1206757684887552 : R) * (h ^ 14) * (a7 ^ 14) * b7
    - (65250702259126272 : R) * (h ^ 14) * (a7 ^ 13) * a6 * b8
    + (41063262151188480 : R) * (h ^ 8) * (a7 ^ 15) * a6
    + (3886741477441536 : R) * (h ^ 6) * (a7 ^ 15) * b8
    - (2435063799114240 : R) * (a7 ^ 17)

set_option maxHeartbeats 200000000 in
/-- Integer expansion of compact block `7` after the extra
`2^{34}` scale, on `λ = 0`. -/
def alignedSquareCompactBlock7Expansion810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    (7177611906121728000 : R) * (h ^ 96) * (a6 ^ 3) * a5 * a0
    - (459367161991790592 : R) * (h ^ 94) * (a6 ^ 3) * a5 * b2
    - (9420615626784768000 : R) * (h ^ 88) * (a7 ^ 2) * (a6 ^ 2) * a5 * a0
    - (5383208929591296000 : R) * (h ^ 88) * a7 * (a6 ^ 4) * a0
    - (897201488265216000 : R) * (h ^ 88) * a7 * (a6 ^ 3) * a5 * a1
    - (14803824556376064000 : R) * (h ^ 88) * (a6 ^ 3) * (a5 ^ 2) * a3
    - (14803824556376064000 : R) * (h ^ 88) * (a6 ^ 3) * a5 * (a4 ^ 2)
    + (602919400114225152 : R) * (h ^ 86) * (a7 ^ 2) * (a6 ^ 2) * a5 * b2
    + (344525371493842944 : R) * (h ^ 86) * a7 * (a6 ^ 4) * b2
    + (172262685746921472 : R) * (h ^ 86) * a7 * (a6 ^ 3) * a5 * b3
    + (1794402976530432000 : R) * (h ^ 86) * (a6 ^ 3) * (a5 ^ 2) * b5
    + (4306567143673036800 : R) * (h ^ 86) * (a6 ^ 3) * a5 * a4 * b6
    + (5024328334285209600 : R) * (h ^ 86) * (a6 ^ 3) * a5 * a3 * b7
    + (5742089524897382400 : R) * (h ^ 86) * (a6 ^ 3) * a5 * a2 * b8
    + (2512164167142604800 : R) * (h ^ 86) * (a6 ^ 3) * (a4 ^ 2) * b7
    + (4121519336718336000 : R) * (h ^ 80) * (a7 ^ 4) * a6 * a5 * a0
    + (8635564324552704000 : R) * (h ^ 80) * (a7 ^ 3) * (a6 ^ 3) * a0
    + (1177576953348096000 : R) * (h ^ 80) * (a7 ^ 3) * (a6 ^ 2) * a5 * a1
    + (672901116198912000 : R) * (h ^ 80) * (a7 ^ 2) * (a6 ^ 4) * a1
    - (3925256511160320000 : R) * (h ^ 80) * (a7 ^ 2) * (a6 ^ 3) * a5 * a2
    + (19430019730243584000 : R) * (h ^ 80) * (a7 ^ 2) * (a6 ^ 2) * (a5 ^ 2) * a3
    + (19430019730243584000 : R) * (h ^ 80) * (a7 ^ 2) * (a6 ^ 2) * a5 * (a4 ^ 2)
    + (22205736834564096000 : R) * (h ^ 80) * a7 * (a6 ^ 4) * a5 * a3
    + (11102868417282048000 : R) * (h ^ 80) * a7 * (a6 ^ 4) * (a4 ^ 2)
    + (25906692973658112000 : R) * (h ^ 80) * a7 * (a6 ^ 3) * (a5 ^ 2) * a4
    - (263777237549973504 : R) * (h ^ 78) * (a7 ^ 4) * a6 * a5 * b2
    - (552676116771373056 : R) * (h ^ 78) * (a7 ^ 3) * (a6 ^ 3) * b2
    - (226094775042834432 : R) * (h ^ 78) * (a7 ^ 3) * (a6 ^ 2) * a5 * b3
    - (129197014310191104 : R) * (h ^ 78) * (a7 ^ 2) * (a6 ^ 4) * b3
    - (43065671436730368 : R) * (h ^ 78) * (a7 ^ 2) * (a6 ^ 3) * a5 * b4
    - (2355153906696192000 : R) * (h ^ 78) * (a7 ^ 2) * (a6 ^ 2) * (a5 ^ 2) * b5
    - (5652369376070860800 : R) * (h ^ 78) * (a7 ^ 2) * (a6 ^ 2) * a5 * a4 * b6
    - (6594430938749337600 : R) * (h ^ 78) * (a7 ^ 2) * (a6 ^ 2) * a5 * a3 * b7
    - (7536492501427814400 : R) * (h ^ 78) * (a7 ^ 2) * (a6 ^ 2) * a5 * a2 * b8
    - (3297215469374668800 : R) * (h ^ 78) * (a7 ^ 2) * (a6 ^ 2) * (a4 ^ 2) * b7
    - (2691604464795648000 : R) * (h ^ 78) * a7 * (a6 ^ 4) * a5 * b5
    - (3229925357754777600 : R) * (h ^ 78) * a7 * (a6 ^ 4) * a4 * b6
    - (3768246250713907200 : R) * (h ^ 78) * a7 * (a6 ^ 4) * a3 * b7
    - (4306567143673036800 : R) * (h ^ 78) * a7 * (a6 ^ 4) * a2 * b8
    - (4037406697193472000 : R) * (h ^ 78) * a7 * (a6 ^ 3) * (a5 ^ 2) * b6
    - (9420615626784768000 : R) * (h ^ 78) * a7 * (a6 ^ 3) * a5 * a4 * b7
    - (7177611906121728000 : R) * (h ^ 78) * a7 * (a6 ^ 3) * a5 * a3 * b8
    - (2512164167142604800 : R) * (h ^ 78) * a7 * (a6 ^ 3) * (a4 ^ 2) * b8
    - (601054903271424000 : R) * (h ^ 72) * (a7 ^ 6) * a5 * a0
    - (5151899170897920000 : R) * (h ^ 72) * (a7 ^ 5) * (a6 ^ 2) * a0
    - (515189917089792000 : R) * (h ^ 72) * (a7 ^ 5) * a6 * a5 * a1
    - (1079445540569088000 : R) * (h ^ 72) * (a7 ^ 4) * (a6 ^ 3) * a1
    + (5151899170897920000 : R) * (h ^ 72) * (a7 ^ 4) * (a6 ^ 2) * a5 * a2
    - (8500633631981568000 : R) * (h ^ 72) * (a7 ^ 4) * a6 * (a5 ^ 2) * a3
    - (8500633631981568000 : R) * (h ^ 72) * (a7 ^ 4) * a6 * a5 * (a4 ^ 2)
    + (2943942383370240000 : R) * (h ^ 72) * (a7 ^ 3) * (a6 ^ 4) * a2
    - (31766540193890304000 : R) * (h ^ 72) * (a7 ^ 3) * (a6 ^ 3) * a5 * a3
    - (16633274466041856000 : R) * (h ^ 72) * (a7 ^ 3) * (a6 ^ 3) * (a4 ^ 2)
    - (34002534527926272000 : R) * (h ^ 72) * (a7 ^ 3) * (a6 ^ 2) * (a5 ^ 2) * a4
    - (8327151312961536000 : R) * (h ^ 72) * (a7 ^ 2) * (a6 ^ 5) * a3
    - (31920746699685888000 : R) * (h ^ 72) * (a7 ^ 2) * (a6 ^ 4) * a5 * a4
    - (8095841554268160000 : R) * (h ^ 72) * (a7 ^ 2) * (a6 ^ 3) * (a5 ^ 3)
    + (38467513809371136 : R) * (h ^ 70) * (a7 ^ 6) * a5 * b2
    + (329721546937466880 : R) * (h ^ 70) * (a7 ^ 5) * (a6 ^ 2) * b2
    + (98916464081240064 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a5 * b3
    + (207253543789264896 : R) * (h ^ 70) * (a7 ^ 4) * (a6 ^ 3) * b3
    + (56523693760708608 : R) * (h ^ 70) * (a7 ^ 4) * (a6 ^ 2) * a5 * b4
    + (1030379834179584000 : R) * (h ^ 70) * (a7 ^ 4) * a6 * (a5 ^ 2) * b5
    + (2472911602031001600 : R) * (h ^ 70) * (a7 ^ 4) * a6 * a5 * a4 * b6
    + (2885063535702835200 : R) * (h ^ 70) * (a7 ^ 4) * a6 * a5 * a3 * b7
    + (3297215469374668800 : R) * (h ^ 70) * (a7 ^ 4) * a6 * a5 * a2 * b8
    + (1442531767851417600 : R) * (h ^ 70) * (a7 ^ 4) * a6 * (a4 ^ 2) * b7
    + (32299253577547776 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 4) * b4
    + (4326754177159004160 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 3) * a5 * b5
    + (5181338594731622400 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 3) * a4 * b6
    + (6044895027186892800 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 3) * a3 * b7
    + (6908451459642163200 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 3) * a2 * b8
    + (5299096290066432000 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 2) * (a5 ^ 2) * b6
    + (12364558010155008000 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 2) * a5 * a4 * b7
    + (9420615626784768000 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 2) * a5 * a3 * b8
    + (3297215469374668800 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 2) * (a4 ^ 2) * b8
    + (1009351674298368000 : R) * (h ^ 70) * (a7 ^ 2) * (a6 ^ 5) * b5
    + (5046758371491840000 : R) * (h ^ 70) * (a7 ^ 2) * (a6 ^ 4) * a5 * b6
    + (5887884766740480000 : R) * (h ^ 70) * (a7 ^ 2) * (a6 ^ 4) * a4 * b7
    + (5383208929591296000 : R) * (h ^ 70) * (a7 ^ 2) * (a6 ^ 4) * a3 * b8
    + (4710307813392384000 : R) * (h ^ 70) * (a7 ^ 2) * (a6 ^ 3) * (a5 ^ 2) * b7
    + (8074813394386944000 : R) * (h ^ 70) * (a7 ^ 2) * (a6 ^ 3) * a5 * a4 * b8
    + (1352373532360704000 : R) * (h ^ 64) * (a7 ^ 7) * a6 * a0
    + (75131862908928000 : R) * (h ^ 64) * (a7 ^ 7) * a5 * a1
    + (643987396362240000 : R) * (h ^ 64) * (a7 ^ 6) * (a6 ^ 2) * a1
    - (2253955887267840000 : R) * (h ^ 64) * (a7 ^ 6) * a6 * a5 * a2
    + (1239675737997312000 : R) * (h ^ 64) * (a7 ^ 6) * (a5 ^ 2) * a3
    + (1239675737997312000 : R) * (h ^ 64) * (a7 ^ 6) * a5 * (a4 ^ 2)
    - (4722574239989760000 : R) * (h ^ 64) * (a7 ^ 5) * (a6 ^ 3) * a2
    + (16191683108536320000 : R) * (h ^ 64) * (a7 ^ 5) * (a6 ^ 2) * a5 * a3
    + (9080222288707584000 : R) * (h ^ 64) * (a7 ^ 5) * (a6 ^ 2) * (a4 ^ 2)
    + (14876108855967744000 : R) * (h ^ 64) * (a7 ^ 5) * a6 * (a5 ^ 2) * a4
    + (12895519047155712000 : R) * (h ^ 64) * (a7 ^ 4) * (a6 ^ 4) * a3
    + (47011518021107712000 : R) * (h ^ 64) * (a7 ^ 4) * (a6 ^ 3) * a5 * a4
    + (10625792039976960000 : R) * (h ^ 64) * (a7 ^ 4) * (a6 ^ 2) * (a5 ^ 3)
    + (9368045227081728000 : R) * (h ^ 64) * (a7 ^ 3) * (a6 ^ 5) * a4
    + (12722036728135680000 : R) * (h ^ 64) * (a7 ^ 3) * (a6 ^ 4) * (a5 ^ 2)
    - (86551906071085056 : R) * (h ^ 62) * (a7 ^ 7) * a6 * b2
    - (14425317678514176 : R) * (h ^ 62) * (a7 ^ 7) * a5 * b3
    - (123645580101550080 : R) * (h ^ 62) * (a7 ^ 6) * (a6 ^ 2) * b3
    - (24729116020310016 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a5 * b4
    - (150263725817856000 : R) * (h ^ 62) * (a7 ^ 6) * (a5 ^ 2) * b5
    - (360632941962854400 : R) * (h ^ 62) * (a7 ^ 6) * a5 * a4 * b6
    - (420738432289996800 : R) * (h ^ 62) * (a7 ^ 6) * a5 * a3 * b7
    - (480843922617139200 : R) * (h ^ 62) * (a7 ^ 6) * a5 * a2 * b8
    - (210369216144998400 : R) * (h ^ 62) * (a7 ^ 6) * (a4 ^ 2) * b7
    - (51813385947316224 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 3) * b4
    - (2587725354982440960 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 2) * a5 * b5
    - (3091139502538752000 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 2) * a4 * b6
    - (3606329419628544000 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 2) * a3 * b7
    - (4121519336718336000 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 2) * a2 * b8
    - (2318354626904064000 : R) * (h ^ 62) * (a7 ^ 5) * a6 * (a5 ^ 2) * b6
    - (5409494129442816000 : R) * (h ^ 62) * (a7 ^ 5) * a6 * a5 * a4 * b7
    - (4121519336718336000 : R) * (h ^ 62) * (a7 ^ 5) * a6 * a5 * a3 * b8
    - (1442531767851417600 : R) * (h ^ 62) * (a7 ^ 5) * a6 * (a4 ^ 2) * b8
    - (1920291560352645120 : R) * (h ^ 62) * (a7 ^ 4) * (a6 ^ 4) * b5
    - (8023925247474401280 : R) * (h ^ 62) * (a7 ^ 4) * (a6 ^ 3) * a5 * b6
    - (9359283493797888000 : R) * (h ^ 62) * (a7 ^ 4) * (a6 ^ 3) * a4 * b7
    - (8635564324552704000 : R) * (h ^ 62) * (a7 ^ 4) * (a6 ^ 3) * a3 * b8
    - (6182279005077504000 : R) * (h ^ 62) * (a7 ^ 4) * (a6 ^ 2) * (a5 ^ 2) * b7
    - (10598192580132864000 : R) * (h ^ 62) * (a7 ^ 4) * (a6 ^ 2) * a5 * a4 * b8
    - (1514027511447552000 : R) * (h ^ 62) * (a7 ^ 3) * (a6 ^ 5) * b6
    - (5053767758118912000 : R) * (h ^ 62) * (a7 ^ 3) * (a6 ^ 4) * a5 * b7
    - (4878533092442112000 : R) * (h ^ 62) * (a7 ^ 3) * (a6 ^ 4) * a4 * b8
    - (3252355394961408000 : R) * (h ^ 62) * (a7 ^ 3) * (a6 ^ 3) * (a5 ^ 2) * b8
    - (131480760090624000 : R) * (h ^ 56) * (a7 ^ 9) * a0
    - (169046691545088000 : R) * (h ^ 56) * (a7 ^ 8) * a6 * a1
    + (328701900226560000 : R) * (h ^ 56) * (a7 ^ 8) * a5 * a2
    + (2817444859084800000 : R) * (h ^ 56) * (a7 ^ 7) * (a6 ^ 2) * a2
    - (3364834145992704000 : R) * (h ^ 56) * (a7 ^ 7) * a6 * a5 * a3
    - (2113083644313600000 : R) * (h ^ 56) * (a7 ^ 7) * a6 * (a4 ^ 2)
    - (2169432541495296000 : R) * (h ^ 56) * (a7 ^ 7) * (a5 ^ 2) * a4
    - (7227225220841472000 : R) * (h ^ 56) * (a7 ^ 6) * (a6 ^ 3) * a3
    - (25043634864783360000 : R) * (h ^ 56) * (a7 ^ 6) * (a6 ^ 2) * a5 * a4
    - (4648784017489920000 : R) * (h ^ 56) * (a7 ^ 6) * a6 * (a5 ^ 3)
    - (15166231749328896000 : R) * (h ^ 56) * (a7 ^ 5) * (a6 ^ 4) * a4
    - (18648746925490176000 : R) * (h ^ 56) * (a7 ^ 5) * (a6 ^ 3) * (a5 ^ 2)
    - (6234520839782400000 : R) * (h ^ 56) * (a7 ^ 4) * (a6 ^ 5) * a5
    + (8414768645799936 : R) * (h ^ 54) * (a7 ^ 9) * b2
    + (32456964776656896 : R) * (h ^ 54) * (a7 ^ 8) * a6 * b3
    + (3606329419628544 : R) * (h ^ 54) * (a7 ^ 8) * a5 * b4
    + (30911395025387520 : R) * (h ^ 54) * (a7 ^ 7) * (a6 ^ 2) * b4
    + (681338665351249920 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a5 * b5
    + (811424119416422400 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a4 * b6
    + (946661472652492800 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a3 * b7
    + (1081898825888563200 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a2 * b8
    + (338093383090176000 : R) * (h ^ 54) * (a7 ^ 7) * (a5 ^ 2) * b6
    + (788884560543744000 : R) * (h ^ 54) * (a7 ^ 7) * a5 * a4 * b7
    + (601054903271424000 : R) * (h ^ 54) * (a7 ^ 7) * a5 * a3 * b8
    + (210369216144998400 : R) * (h ^ 54) * (a7 ^ 7) * (a4 ^ 2) * b8
    + (1449032973948026880 : R) * (h ^ 54) * (a7 ^ 6) * (a6 ^ 3) * b5
    + (4735515320049991680 : R) * (h ^ 54) * (a7 ^ 6) * (a6 ^ 2) * a5 * b6
    + (5522191923806208000 : R) * (h ^ 54) * (a7 ^ 6) * (a6 ^ 2) * a4 * b7
    + (5151899170897920000 : R) * (h ^ 54) * (a7 ^ 6) * (a6 ^ 2) * a3 * b8
    + (2704747064721408000 : R) * (h ^ 54) * (a7 ^ 6) * a6 * (a5 ^ 2) * b7
    + (4636709253808128000 : R) * (h ^ 54) * (a7 ^ 6) * a6 * a5 * a4 * b8
    + (2816406593690664960 : R) * (h ^ 54) * (a7 ^ 5) * (a6 ^ 4) * b6
    + (7966418487239245824 : R) * (h ^ 54) * (a7 ^ 5) * (a6 ^ 3) * a5 * b7
    + (7740115182944256000 : R) * (h ^ 54) * (a7 ^ 5) * (a6 ^ 3) * a4 * b8
    + (4268716455886848000 : R) * (h ^ 54) * (a7 ^ 5) * (a6 ^ 2) * (a5 ^ 2) * b8
    + (1278774972776448000 : R) * (h ^ 54) * (a7 ^ 4) * (a6 ^ 5) * b7
    + (3245346008334336000 : R) * (h ^ 54) * (a7 ^ 4) * (a6 ^ 4) * a5 * b8
    + (16435095011328000 : R) * (h ^ 48) * (a7 ^ 10) * a1
    - (739579275509760000 : R) * (h ^ 48) * (a7 ^ 9) * a6 * a2
    + (219525911937024000 : R) * (h ^ 48) * (a7 ^ 9) * a5 * a3
    + (172568497618944000 : R) * (h ^ 48) * (a7 ^ 9) * (a4 ^ 2)
    + (1649211472871424000 : R) * (h ^ 48) * (a7 ^ 8) * (a6 ^ 2) * a3
    + (5610488633229312000 : R) * (h ^ 48) * (a7 ^ 8) * a6 * a5 * a4
    + (677947669217280000 : R) * (h ^ 48) * (a7 ^ 8) * (a5 ^ 3)
    + (9227658986520576000 : R) * (h ^ 48) * (a7 ^ 7) * (a6 ^ 3) * a4
    + (9866016284737536000 : R) * (h ^ 48) * (a7 ^ 7) * (a6 ^ 2) * (a5 ^ 2)
    + (10027379346898944000 : R) * (h ^ 48) * (a7 ^ 6) * (a6 ^ 4) * a5
    + (935178125967360000 : R) * (h ^ 48) * (a7 ^ 5) * (a6 ^ 6)
    - (3155538242174976 : R) * (h ^ 46) * (a7 ^ 10) * b3
    - (8114241194164224 : R) * (h ^ 46) * (a7 ^ 9) * a6 * b4
    - (66491698674401280 : R) * (h ^ 46) * (a7 ^ 9) * a5 * b5
    - (78888456054374400 : R) * (h ^ 46) * (a7 ^ 9) * a4 * b6
    - (92036532063436800 : R) * (h ^ 46) * (a7 ^ 9) * a3 * b7
    - (105184608072499200 : R) * (h ^ 46) * (a7 ^ 9) * a2 * b8
    - (541754397189734400 : R) * (h ^ 46) * (a7 ^ 8) * (a6 ^ 2) * b5
    - (1226554494796431360 : R) * (h ^ 46) * (a7 ^ 8) * a6 * a5 * b6
    - (1429853265985536000 : R) * (h ^ 46) * (a7 ^ 8) * a6 * a4 * b7
    - (1352373532360704000 : R) * (h ^ 46) * (a7 ^ 8) * a6 * a3 * b8
    - (394442280271872000 : R) * (h ^ 46) * (a7 ^ 8) * (a5 ^ 2) * b7
    - (676186766180352000 : R) * (h ^ 46) * (a7 ^ 8) * a5 * a4 * b8
    - (2070833471202263040 : R) * (h ^ 46) * (a7 ^ 7) * (a6 ^ 3) * b6
    - (4651987854786822144 : R) * (h ^ 46) * (a7 ^ 7) * (a6 ^ 2) * a5 * b7
    - (4556210829262848000 : R) * (h ^ 46) * (a7 ^ 7) * (a6 ^ 2) * a4 * b8
    - (1867563449450496000 : R) * (h ^ 46) * (a7 ^ 7) * a6 * (a5 ^ 2) * b8
    - (2338968356800954368 : R) * (h ^ 46) * (a7 ^ 6) * (a6 ^ 4) * b7
    - (5094296031596642304 : R) * (h ^ 46) * (a7 ^ 6) * (a6 ^ 3) * a5 * b8
    - (742556895805440000 : R) * (h ^ 46) * (a7 ^ 5) * (a6 ^ 5) * b8
    + (71903540674560000 : R) * (h ^ 40) * (a7 ^ 11) * a2
    - (87164700327936000 : R) * (h ^ 40) * (a7 ^ 10) * a6 * a3
    - (428376349212672000 : R) * (h ^ 40) * (a7 ^ 10) * a5 * a4
    - (2538656174702592000 : R) * (h ^ 40) * (a7 ^ 9) * (a6 ^ 2) * a4
    - (2185689449889792000 : R) * (h ^ 40) * (a7 ^ 9) * a6 * (a5 ^ 2)
    - (6062285651674398720 : R) * (h ^ 40) * (a7 ^ 8) * (a6 ^ 3) * a5
    - (1626571290968064000 : R) * (h ^ 40) * (a7 ^ 7) * (a6 ^ 5)
    + (788884560543744 : R) * (h ^ 38) * (a7 ^ 11) * b4
    + (100301036983418880 : R) * (h ^ 38) * (a7 ^ 10) * a6 * b5
    + (117240924198666240 : R) * (h ^ 38) * (a7 ^ 10) * a5 * b6
    + (136616727281664000 : R) * (h ^ 38) * (a7 ^ 10) * a4 * b7
    + (131480760090624000 : R) * (h ^ 38) * (a7 ^ 10) * a3 * b8
    + (751352170099507200 : R) * (h ^ 38) * (a7 ^ 9) * (a6 ^ 2) * b6
    + (1188837293385842688 : R) * (h ^ 38) * (a7 ^ 9) * a6 * a5 * b7
    + (1176283228667904000 : R) * (h ^ 38) * (a7 ^ 9) * a6 * a4 * b8
    + (272353003044864000 : R) * (h ^ 38) * (a7 ^ 9) * (a5 ^ 2) * b8
    + (1685919928399429632 : R) * (h ^ 38) * (a7 ^ 8) * (a6 ^ 3) * b7
    + (2959186485024129024 : R) * (h ^ 38) * (a7 ^ 8) * (a6 ^ 2) * a5 * b8
    + (1344053828521033728 : R) * (h ^ 38) * (a7 ^ 7) * (a6 ^ 4) * b8
    - (11299127820288000 : R) * (h ^ 32) * (a7 ^ 12) * a3
    + (286669511589888000 : R) * (h ^ 32) * (a7 ^ 11) * a6 * a4
    + (163383370579968000 : R) * (h ^ 32) * (a7 ^ 11) * (a5 ^ 2)
    + (1661733812510392320 : R) * (h ^ 32) * (a7 ^ 10) * (a6 ^ 2) * a5
    + (1085876437820375040 : R) * (h ^ 32) * (a7 ^ 9) * (a6 ^ 4)
    - (7354705017569280 : R) * (h ^ 30) * (a7 ^ 12) * b5
    - (134365706232791040 : R) * (h ^ 30) * (a7 ^ 11) * a6 * b6
    - (111654899539771392 : R) * (h ^ 30) * (a7 ^ 11) * a5 * b7
    - (111964084764672000 : R) * (h ^ 30) * (a7 ^ 11) * a4 * b8
    - (597460093092495360 : R) * (h ^ 30) * (a7 ^ 10) * (a6 ^ 2) * b7
    - (751112016466280448 : R) * (h ^ 30) * (a7 ^ 10) * a6 * a5 * b8
    - (956610910221238272 : R) * (h ^ 30) * (a7 ^ 9) * (a6 ^ 3) * b8
    - (6748981886976000 : R) * (h ^ 24) * (a7 ^ 13) * a4
    - (189668866612592640 : R) * (h ^ 24) * (a7 ^ 12) * a6 * a5
    - (336512163568680960 : R) * (h ^ 24) * (a7 ^ 11) * (a6 ^ 3)
    + (9468155516682240 : R) * (h ^ 22) * (a7 ^ 13) * b6
    + (103905527543365632 : R) * (h ^ 22) * (a7 ^ 12) * a6 * b7
    + (69904622243807232 : R) * (h ^ 22) * (a7 ^ 12) * a5 * b8
    + (333808885888450560 : R) * (h ^ 22) * (a7 ^ 11) * (a6 ^ 2) * b8
    + (5133928352501760 : R) * (h ^ 16) * (a7 ^ 14) * a5
    + (42782871811276800 : R) * (h ^ 16) * (a7 ^ 13) * (a6 ^ 2)
    - (7085855191252992 : R) * (h ^ 14) * (a7 ^ 14) * b7
    - (56961503425462272 : R) * (h ^ 14) * (a7 ^ 13) * a6 * b8
    + (92109483863040 : R) * (h ^ 8) * (a7 ^ 15) * a6
    + (3795144712568832 : R) * (h ^ 6) * (a7 ^ 15) * b8
    - (318677532378240 : R) * (a7 ^ 17)

set_option maxHeartbeats 200000000 in
/-- Integer expansion of compact block `8` after the extra
`2^{34}` scale, on `λ = 0`. -/
def alignedSquareCompactBlock8Expansion810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    (7177611906121728000 : R) * (h ^ 96) * (a6 ^ 3) * a4 * a1
    + (7177611906121728000 : R) * (h ^ 96) * (a6 ^ 3) * a3 * a2
    - (689050742987685888 : R) * (h ^ 94) * (a6 ^ 3) * a4 * b3
    - (918734323983581184 : R) * (h ^ 94) * (a6 ^ 3) * a3 * b4
    - (1148417904979476480 : R) * (h ^ 94) * (a6 ^ 3) * a2 * b5
    - (1378101485975371776 : R) * (h ^ 94) * (a6 ^ 3) * a1 * b6
    - (1607785066971267072 : R) * (h ^ 94) * (a6 ^ 3) * a0 * b7
    - (9420615626784768000 : R) * (h ^ 88) * (a7 ^ 2) * (a6 ^ 2) * a4 * a1
    - (9420615626784768000 : R) * (h ^ 88) * (a7 ^ 2) * (a6 ^ 2) * a3 * a2
    - (4486007441326080000 : R) * (h ^ 88) * a7 * (a6 ^ 3) * a5 * a1
    - (5383208929591296000 : R) * (h ^ 88) * a7 * (a6 ^ 3) * a4 * a2
    - (2691604464795648000 : R) * (h ^ 88) * a7 * (a6 ^ 3) * (a3 ^ 2)
    - (14803824556376064000 : R) * (h ^ 88) * (a6 ^ 2) * (a5 ^ 3) * a4
    + (904379100171337728 : R) * (h ^ 86) * (a7 ^ 2) * (a6 ^ 2) * a4 * b3
    + (1205838800228450304 : R) * (h ^ 86) * (a7 ^ 2) * (a6 ^ 2) * a3 * b4
    + (1507298500285562880 : R) * (h ^ 86) * (a7 ^ 2) * (a6 ^ 2) * a2 * b5
    + (1808758200342675456 : R) * (h ^ 86) * (a7 ^ 2) * (a6 ^ 2) * a1 * b6
    + (2110217900399788032 : R) * (h ^ 86) * (a7 ^ 2) * (a6 ^ 2) * a0 * b7
    + (430656714367303680 : R) * (h ^ 86) * a7 * (a6 ^ 3) * a5 * b3
    + (803892533485633536 : R) * (h ^ 86) * a7 * (a6 ^ 3) * a4 * b4
    + (1004865666857041920 : R) * (h ^ 86) * a7 * (a6 ^ 3) * a3 * b5
    + (1205838800228450304 : R) * (h ^ 86) * a7 * (a6 ^ 3) * a2 * b6
    + (1406811933599858688 : R) * (h ^ 86) * a7 * (a6 ^ 3) * a1 * b7
    + (1607785066971267072 : R) * (h ^ 86) * a7 * (a6 ^ 3) * a0 * b8
    + (5742089524897382400 : R) * (h ^ 86) * (a6 ^ 3) * a4 * a3 * b8
    + (4121519336718336000 : R) * (h ^ 80) * (a7 ^ 4) * a6 * a4 * a1
    + (4121519336718336000 : R) * (h ^ 80) * (a7 ^ 4) * a6 * a3 * a2
    - (753649250142781440 : R) * (h ^ 80) * (a7 ^ 3) * (a6 ^ 3) * a0
    + (5887884766740480000 : R) * (h ^ 80) * (a7 ^ 3) * (a6 ^ 2) * a5 * a1
    + (7065461720088576000 : R) * (h ^ 80) * (a7 ^ 3) * (a6 ^ 2) * a4 * a2
    + (3532730860044288000 : R) * (h ^ 80) * (a7 ^ 3) * (a6 ^ 2) * (a3 ^ 2)
    + (1682252790497280000 : R) * (h ^ 80) * (a7 ^ 2) * (a6 ^ 4) * a1
    + (2243003720663040000 : R) * (h ^ 80) * (a7 ^ 2) * (a6 ^ 3) * a5 * a2
    - (1682252790497280000 : R) * (h ^ 80) * (a7 ^ 2) * (a6 ^ 3) * a4 * a3
    + (12953346486829056000 : R) * (h ^ 80) * (a7 ^ 2) * a6 * (a5 ^ 3) * a4
    + (33308605251846144000 : R) * (h ^ 80) * a7 * (a6 ^ 3) * (a5 ^ 2) * a4
    + (9252390347735040000 : R) * (h ^ 80) * a7 * (a6 ^ 2) * (a5 ^ 4)
    - (395665856324960256 : R) * (h ^ 78) * (a7 ^ 4) * a6 * a4 * b3
    - (527554475099947008 : R) * (h ^ 78) * (a7 ^ 4) * a6 * a3 * b4
    - (659443093874933760 : R) * (h ^ 78) * (a7 ^ 4) * a6 * a2 * b5
    - (791331712649920512 : R) * (h ^ 78) * (a7 ^ 4) * a6 * a1 * b6
    - (923220331424907264 : R) * (h ^ 78) * (a7 ^ 4) * a6 * a0 * b7
    - (565236937607086080 : R) * (h ^ 78) * (a7 ^ 3) * (a6 ^ 2) * a5 * b3
    - (1055108950199894016 : R) * (h ^ 78) * (a7 ^ 3) * (a6 ^ 2) * a4 * b4
    - (1318886187749867520 : R) * (h ^ 78) * (a7 ^ 3) * (a6 ^ 2) * a3 * b5
    - (1582663425299841024 : R) * (h ^ 78) * (a7 ^ 3) * (a6 ^ 2) * a2 * b6
    - (1846440662849814528 : R) * (h ^ 78) * (a7 ^ 3) * (a6 ^ 2) * a1 * b7
    - (2110217900399788032 : R) * (h ^ 78) * (a7 ^ 3) * (a6 ^ 2) * a0 * b8
    - (161496267887738880 : R) * (h ^ 78) * (a7 ^ 2) * (a6 ^ 4) * b3
    - (358880595306086400 : R) * (h ^ 78) * (a7 ^ 2) * (a6 ^ 3) * a5 * b4
    - (502432833428520960 : R) * (h ^ 78) * (a7 ^ 2) * (a6 ^ 3) * a4 * b5
    - (602919400114225152 : R) * (h ^ 78) * (a7 ^ 2) * (a6 ^ 3) * a3 * b6
    - (703405966799929344 : R) * (h ^ 78) * (a7 ^ 2) * (a6 ^ 3) * a2 * b7
    - (803892533485633536 : R) * (h ^ 78) * (a7 ^ 2) * (a6 ^ 3) * a1 * b8
    - (7536492501427814400 : R) * (h ^ 78) * (a7 ^ 2) * (a6 ^ 2) * a4 * a3 * b8
    - (3588805953060864000 : R) * (h ^ 78) * a7 * (a6 ^ 3) * a5 * a3 * b8
    - (2871044762448691200 : R) * (h ^ 78) * a7 * (a6 ^ 3) * (a4 ^ 2) * b8
    - (601054903271424000 : R) * (h ^ 72) * (a7 ^ 6) * a4 * a1
    - (601054903271424000 : R) * (h ^ 72) * (a7 ^ 6) * a3 * a2
    + (989164640812400640 : R) * (h ^ 72) * (a7 ^ 5) * (a6 ^ 2) * a0
    - (2575949585448960000 : R) * (h ^ 72) * (a7 ^ 5) * a6 * a5 * a1
    - (3091139502538752000 : R) * (h ^ 72) * (a7 ^ 5) * a6 * a4 * a2
    - (1545569751269376000 : R) * (h ^ 72) * (a7 ^ 5) * a6 * (a3 ^ 2)
    - (2269779577578455040 : R) * (h ^ 72) * (a7 ^ 4) * (a6 ^ 3) * a1
    - (2943942383370240000 : R) * (h ^ 72) * (a7 ^ 4) * (a6 ^ 2) * a5 * a2
    + (2207956787527680000 : R) * (h ^ 72) * (a7 ^ 4) * (a6 ^ 2) * a4 * a3
    - (2833544543993856000 : R) * (h ^ 72) * (a7 ^ 4) * (a5 ^ 3) * a4
    - (700938662707200000 : R) * (h ^ 72) * (a7 ^ 3) * (a6 ^ 4) * a2
    + (1752346656768000000 : R) * (h ^ 72) * (a7 ^ 3) * (a6 ^ 3) * a5 * a3
    + (1626177697480704000 : R) * (h ^ 72) * (a7 ^ 3) * (a6 ^ 3) * (a4 ^ 2)
    - (38860039460487168000 : R) * (h ^ 72) * (a7 ^ 3) * (a6 ^ 2) * (a5 ^ 2) * a4
    - (8095841554268160000 : R) * (h ^ 72) * (a7 ^ 3) * a6 * (a5 ^ 4)
    - (24981453938884608000 : R) * (h ^ 72) * (a7 ^ 2) * (a6 ^ 4) * a5 * a4
    - (24287524662804480000 : R) * (h ^ 72) * (a7 ^ 2) * (a6 ^ 3) * (a5 ^ 3)
    + (57701270714056704 : R) * (h ^ 70) * (a7 ^ 6) * a4 * b3
    + (76935027618742272 : R) * (h ^ 70) * (a7 ^ 6) * a3 * b4
    + (96168784523427840 : R) * (h ^ 70) * (a7 ^ 6) * a2 * b5
    + (115402541428113408 : R) * (h ^ 70) * (a7 ^ 6) * a1 * b6
    + (134636298332798976 : R) * (h ^ 70) * (a7 ^ 6) * a0 * b7
    + (247291160203100160 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a5 * b3
    + (461610165712453632 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a4 * b4
    + (577012707140567040 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a3 * b5
    + (692415248568680448 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a2 * b6
    + (807817789996793856 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a1 * b7
    + (923220331424907264 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a0 * b8
    + (247291160203100160 : R) * (h ^ 70) * (a7 ^ 4) * (a6 ^ 3) * b3
    + (471030781339238400 : R) * (h ^ 70) * (a7 ^ 4) * (a6 ^ 2) * a5 * b4
    + (659443093874933760 : R) * (h ^ 70) * (a7 ^ 4) * (a6 ^ 2) * a4 * b5
    + (791331712649920512 : R) * (h ^ 70) * (a7 ^ 4) * (a6 ^ 2) * a3 * b6
    + (923220331424907264 : R) * (h ^ 70) * (a7 ^ 4) * (a6 ^ 2) * a2 * b7
    + (1055108950199894016 : R) * (h ^ 70) * (a7 ^ 4) * (a6 ^ 2) * a1 * b8
    + (3297215469374668800 : R) * (h ^ 70) * (a7 ^ 4) * a6 * a4 * a3 * b8
    + (116636193474478080 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 4) * b4
    + (179440297653043200 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 3) * a5 * b5
    + (226094775042834432 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 3) * a4 * b6
    + (263777237549973504 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 3) * a3 * b7
    + (301459700057112576 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 3) * a2 * b8
    + (4710307813392384000 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 2) * a5 * a3 * b8
    + (3768246250713907200 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 2) * (a4 ^ 2) * b8
    + (1345802232397824000 : R) * (h ^ 70) * (a7 ^ 2) * (a6 ^ 4) * a3 * b8
    + (2691604464795648000 : R) * (h ^ 70) * (a7 ^ 2) * (a6 ^ 3) * a5 * a4 * b8
    - (432759530355425280 : R) * (h ^ 64) * (a7 ^ 7) * a6 * a0
    + (375659314544640000 : R) * (h ^ 64) * (a7 ^ 7) * a5 * a1
    + (450791177453568000 : R) * (h ^ 64) * (a7 ^ 7) * a4 * a2
    + (225395588726784000 : R) * (h ^ 64) * (a7 ^ 7) * (a3 ^ 2)
    + (1047123506485002240 : R) * (h ^ 64) * (a7 ^ 6) * (a6 ^ 2) * a1
    + (1287974792724480000 : R) * (h ^ 64) * (a7 ^ 6) * a6 * a5 * a2
    - (965981094543360000 : R) * (h ^ 64) * (a7 ^ 6) * a6 * a4 * a3
    + (960951859638435840 : R) * (h ^ 64) * (a7 ^ 5) * (a6 ^ 3) * a2
    - (2299954987008000000 : R) * (h ^ 64) * (a7 ^ 5) * (a6 ^ 2) * a5 * a3
    - (2134358227943424000 : R) * (h ^ 64) * (a7 ^ 5) * (a6 ^ 2) * (a4 ^ 2)
    + (14876108855967744000 : R) * (h ^ 64) * (a7 ^ 5) * a6 * (a5 ^ 2) * a4
    + (1770965339996160000 : R) * (h ^ 64) * (a7 ^ 5) * (a5 ^ 4)
    - (735985595842560000 : R) * (h ^ 64) * (a7 ^ 4) * (a6 ^ 4) * a3
    + (34757795936993280000 : R) * (h ^ 64) * (a7 ^ 4) * (a6 ^ 3) * a5 * a4
    + (28082450391367680000 : R) * (h ^ 64) * (a7 ^ 4) * (a6 ^ 2) * (a5 ^ 3)
    + (6245363484721152000 : R) * (h ^ 64) * (a7 ^ 3) * (a6 ^ 5) * a4
    + (23420113067704320000 : R) * (h ^ 64) * (a7 ^ 3) * (a6 ^ 4) * (a5 ^ 2)
    - (36063294196285440 : R) * (h ^ 62) * (a7 ^ 7) * a5 * b3
    - (67318149166399488 : R) * (h ^ 62) * (a7 ^ 7) * a4 * b4
    - (84147686457999360 : R) * (h ^ 62) * (a7 ^ 7) * a3 * b5
    - (100977223749599232 : R) * (h ^ 62) * (a7 ^ 7) * a2 * b6
    - (117806761041199104 : R) * (h ^ 62) * (a7 ^ 7) * a1 * b7
    - (134636298332798976 : R) * (h ^ 62) * (a7 ^ 7) * a0 * b8
    - (139101277614243840 : R) * (h ^ 62) * (a7 ^ 6) * (a6 ^ 2) * b3
    - (206075966835916800 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a5 * b4
    - (288506353570283520 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a4 * b5
    - (346207624284340224 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a3 * b6
    - (403908894998396928 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a2 * b7
    - (461610165712453632 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a1 * b8
    - (480843922617139200 : R) * (h ^ 62) * (a7 ^ 6) * a4 * a3 * b8
    - (177029068653330432 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 3) * b4
    - (235515390669619200 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 2) * a5 * b5
    - (296749392243720192 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 2) * a4 * b6
    - (346207624284340224 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 2) * a3 * b7
    - (395665856324960256 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 2) * a2 * b8
    - (2060759668359168000 : R) * (h ^ 62) * (a7 ^ 5) * a6 * a5 * a3 * b8
    - (1648607734687334400 : R) * (h ^ 62) * (a7 ^ 5) * a6 * (a4 ^ 2) * b8
    - (51869461040332800 : R) * (h ^ 62) * (a7 ^ 4) * (a6 ^ 4) * b5
    - (68972364410388480 : R) * (h ^ 62) * (a7 ^ 4) * (a6 ^ 3) * a5 * b6
    - (82430386734366720 : R) * (h ^ 62) * (a7 ^ 4) * (a6 ^ 3) * a4 * b7
    - (2154965824627015680 : R) * (h ^ 62) * (a7 ^ 4) * (a6 ^ 3) * a3 * b8
    - (3532730860044288000 : R) * (h ^ 62) * (a7 ^ 4) * (a6 ^ 2) * a5 * a4 * b8
    - (897201488265216000 : R) * (h ^ 62) * (a7 ^ 3) * (a6 ^ 4) * a4 * b8
    - (560750930165760000 : R) * (h ^ 62) * (a7 ^ 3) * (a6 ^ 3) * (a5 ^ 2) * b8
    + (63110764843499520 : R) * (h ^ 56) * (a7 ^ 9) * a0
    - (176372048178708480 : R) * (h ^ 56) * (a7 ^ 8) * a6 * a1
    - (187829657272320000 : R) * (h ^ 56) * (a7 ^ 8) * a5 * a2
    + (140872242954240000 : R) * (h ^ 56) * (a7 ^ 8) * a4 * a3
    - (456265070322647040 : R) * (h ^ 56) * (a7 ^ 7) * (a6 ^ 2) * a2
    + (1006230306816000000 : R) * (h ^ 56) * (a7 ^ 7) * a6 * a5 * a3
    + (933781724725248000 : R) * (h ^ 56) * (a7 ^ 7) * a6 * (a4 ^ 2)
    - (1859513606995968000 : R) * (h ^ 56) * (a7 ^ 7) * (a5 ^ 2) * a4
    + (1161829928203714560 : R) * (h ^ 56) * (a7 ^ 6) * (a6 ^ 3) * a3
    - (17461258261364736000 : R) * (h ^ 56) * (a7 ^ 6) * (a6 ^ 2) * a5 * a4
    - (10625792039976960000 : R) * (h ^ 56) * (a7 ^ 6) * a6 * (a5 ^ 3)
    - (10352425961521152000 : R) * (h ^ 56) * (a7 ^ 5) * (a6 ^ 4) * a4
    - (33218195116523520000 : R) * (h ^ 56) * (a7 ^ 5) * (a6 ^ 3) * (a5 ^ 2)
    - (9758380444876800000 : R) * (h ^ 56) * (a7 ^ 4) * (a6 ^ 5) * a5
    + (33809338309017600 : R) * (h ^ 54) * (a7 ^ 8) * a6 * b3
    + (30052745163571200 : R) * (h ^ 54) * (a7 ^ 8) * a5 * b4
    + (42073843228999680 : R) * (h ^ 54) * (a7 ^ 8) * a4 * b5
    + (50488611874799616 : R) * (h ^ 54) * (a7 ^ 8) * a3 * b6
    + (58903380520599552 : R) * (h ^ 54) * (a7 ^ 8) * a2 * b7
    + (67318149166399488 : R) * (h ^ 54) * (a7 ^ 8) * a1 * b8
    + (98401274164150272 : R) * (h ^ 54) * (a7 ^ 7) * (a6 ^ 2) * b4
    + (103037983417958400 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a5 * b5
    + (129827859106627584 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a4 * b6
    + (151465835624398848 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a3 * b7
    + (173103812142170112 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a2 * b8
    + (300527451635712000 : R) * (h ^ 54) * (a7 ^ 7) * a5 * a3 * b8
    + (240421961308569600 : R) * (h ^ 54) * (a7 ^ 7) * (a4 ^ 2) * b8
    + (78137137425285120 : R) * (h ^ 54) * (a7 ^ 6) * (a6 ^ 3) * b5
    + (90526228288634880 : R) * (h ^ 54) * (a7 ^ 6) * (a6 ^ 2) * a5 * b6
    + (108189882588856320 : R) * (h ^ 54) * (a7 ^ 6) * (a6 ^ 2) * a4 * b7
    + (1282822893553582080 : R) * (h ^ 54) * (a7 ^ 6) * (a6 ^ 2) * a3 * b8
    + (1545569751269376000 : R) * (h ^ 54) * (a7 ^ 6) * a6 * a5 * a4 * b8
    + (18126273817608192 : R) * (h ^ 54) * (a7 ^ 5) * (a6 ^ 4) * b6
    + (22373962113613824 : R) * (h ^ 54) * (a7 ^ 5) * (a6 ^ 3) * a5 * b7
    + (1389933330601869312 : R) * (h ^ 54) * (a7 ^ 5) * (a6 ^ 3) * a4 * b8
    + (735985595842560000 : R) * (h ^ 54) * (a7 ^ 5) * (a6 ^ 2) * (a5 ^ 2) * b8
    + (350469331353600000 : R) * (h ^ 54) * (a7 ^ 4) * (a6 ^ 4) * a5 * b8
    + (5177054928568320 : R) * (h ^ 48) * (a7 ^ 10) * a1
    + (82222432470958080 : R) * (h ^ 48) * (a7 ^ 9) * a6 * a2
    - (146741919744000000 : R) * (h ^ 48) * (a7 ^ 9) * a5 * a3
    - (136176501522432000 : R) * (h ^ 48) * (a7 ^ 9) * (a4 ^ 2)
    - (679668323041935360 : R) * (h ^ 48) * (a7 ^ 8) * (a6 ^ 2) * a3
    + (3687834074480640000 : R) * (h ^ 48) * (a7 ^ 8) * a6 * a5 * a4
    + (1307470504919040000 : R) * (h ^ 48) * (a7 ^ 8) * (a5 ^ 3)
    + (6684846550155264000 : R) * (h ^ 48) * (a7 ^ 7) * (a6 ^ 3) * a4
    + (17283442991431680000 : R) * (h ^ 48) * (a7 ^ 7) * (a6 ^ 2) * (a5 ^ 2)
    + (16416270974976000000 : R) * (h ^ 48) * (a7 ^ 6) * (a6 ^ 4) * a5
    + (1463757066731520000 : R) * (h ^ 48) * (a7 ^ 5) * (a6 ^ 6)
    - (2958317102039040 : R) * (h ^ 46) * (a7 ^ 10) * b3
    - (23516273090494464 : R) * (h ^ 46) * (a7 ^ 9) * a6 * b4
    - (15026372581785600 : R) * (h ^ 46) * (a7 ^ 9) * a5 * b5
    - (18933229453049856 : R) * (h ^ 46) * (a7 ^ 9) * a4 * b6
    - (22088767695224832 : R) * (h ^ 46) * (a7 ^ 9) * a3 * b7
    - (25244305937399808 : R) * (h ^ 46) * (a7 ^ 9) * a2 * b8
    - (42986158707179520 : R) * (h ^ 46) * (a7 ^ 8) * (a6 ^ 2) * b5
    - (39605224876277760 : R) * (h ^ 46) * (a7 ^ 8) * a6 * a5 * b6
    - (47333073632624640 : R) * (h ^ 46) * (a7 ^ 8) * a6 * a4 * b7
    - (335839427202908160 : R) * (h ^ 46) * (a7 ^ 8) * a6 * a3 * b8
    - (225395588726784000 : R) * (h ^ 46) * (a7 ^ 8) * a5 * a4 * b8
    - (27134211806724096 : R) * (h ^ 46) * (a7 ^ 7) * (a6 ^ 3) * b6
    - (29365825274118144 : R) * (h ^ 46) * (a7 ^ 7) * (a6 ^ 2) * a5 * b7
    - (793907662235369472 : R) * (h ^ 46) * (a7 ^ 7) * (a6 ^ 2) * a4 * b8
    - (321993698181120000 : R) * (h ^ 46) * (a7 ^ 7) * a6 * (a5 ^ 2) * b8
    - (5440160195936256 : R) * (h ^ 46) * (a7 ^ 6) * (a6 ^ 4) * b7
    - (536950557873537024 : R) * (h ^ 46) * (a7 ^ 6) * (a6 ^ 3) * a5 * b8
    - (52570399703040000 : R) * (h ^ 46) * (a7 ^ 5) * (a6 ^ 5) * b8
    - (3430826083614720 : R) * (h ^ 40) * (a7 ^ 11) * a2
    + (174091678745886720 : R) * (h ^ 40) * (a7 ^ 10) * a6 * a3
    - (266630068174848000 : R) * (h ^ 40) * (a7 ^ 10) * a5 * a4
    - (2095258993164288000 : R) * (h ^ 40) * (a7 ^ 9) * (a6 ^ 2) * a4
    - (3893325169950720000 : R) * (h ^ 40) * (a7 ^ 9) * a6 * (a5 ^ 2)
    - (10850631908925112320 : R) * (h ^ 40) * (a7 ^ 8) * (a6 ^ 3) * a5
    - (2846142958141440000 : R) * (h ^ 40) * (a7 ^ 7) * (a6 ^ 5)
    + (2005081591382016 : R) * (h ^ 38) * (a7 ^ 11) * b4
    + (10119322785546240 : R) * (h ^ 38) * (a7 ^ 10) * a6 * b5
    + (5775761961123840 : R) * (h ^ 38) * (a7 ^ 10) * a5 * b6
    + (6902739904757760 : R) * (h ^ 38) * (a7 ^ 10) * a4 * b7
    + (32541488122429440 : R) * (h ^ 38) * (a7 ^ 10) * a3 * b8
    + (14796760408915968 : R) * (h ^ 38) * (a7 ^ 9) * (a6 ^ 2) * b6
    + (12847548557426688 : R) * (h ^ 38) * (a7 ^ 9) * a6 * a5 * b7
    + (197070876410118144 : R) * (h ^ 38) * (a7 ^ 9) * a6 * a4 * b8
    + (46957414318080000 : R) * (h ^ 38) * (a7 ^ 9) * (a5 ^ 2) * b8
    + (8100920621531136 : R) * (h ^ 38) * (a7 ^ 8) * (a6 ^ 3) * b7
    + (302255484482617344 : R) * (h ^ 38) * (a7 ^ 8) * (a6 ^ 2) * a5 * b8
    + (91164082471698432 : R) * (h ^ 38) * (a7 ^ 7) * (a6 ^ 4) * b8
    - (16400427232788480 : R) * (h ^ 32) * (a7 ^ 12) * a3
    + (318409002713088000 : R) * (h ^ 32) * (a7 ^ 11) * a6 * a4
    + (318842677493760000 : R) * (h ^ 32) * (a7 ^ 11) * (a5 ^ 2)
    + (3520738661152849920 : R) * (h ^ 32) * (a7 ^ 10) * (a6 ^ 2) * a5
    + (2273516653620756480 : R) * (h ^ 32) * (a7 ^ 9) * (a6 ^ 4)
    - (842298619330560 : R) * (h ^ 30) * (a7 ^ 12) * b5
    - (3437785843236864 : R) * (h ^ 30) * (a7 ^ 11) * a6 * b6
    - (1873600831291392 : R) * (h ^ 30) * (a7 ^ 11) * a5 * b7
    - (17782772802256896 : R) * (h ^ 30) * (a7 ^ 11) * a4 * b8
    - (4384774340739072 : R) * (h ^ 30) * (a7 ^ 10) * (a6 ^ 2) * b7
    - (73540006563545088 : R) * (h ^ 30) * (a7 ^ 10) * a6 * a5 * b8
    - (61540758070493184 : R) * (h ^ 30) * (a7 ^ 9) * (a6 ^ 3) * b8
    - (18876972269568000 : R) * (h ^ 24) * (a7 ^ 13) * a4
    - (561262222143651840 : R) * (h ^ 24) * (a7 ^ 12) * a6 * a5
    - (955574599318241280 : R) * (h ^ 24) * (a7 ^ 11) * (a6 ^ 3)
    + (279983582871552 : R) * (h ^ 22) * (a7 ^ 13) * b6
    + (1007218194382848 : R) * (h ^ 22) * (a7 ^ 12) * a6 * b7
    + (6444611631316992 : R) * (h ^ 22) * (a7 ^ 12) * a5 * b8
    + (20098569927131136 : R) * (h ^ 22) * (a7 ^ 11) * (a6 ^ 2) * b8
    + (35274272638402560 : R) * (h ^ 16) * (a7 ^ 14) * a5
    + (223158951989084160 : R) * (h ^ 16) * (a7 ^ 13) * (a6 ^ 2)
    - (80450111078400 : R) * (h ^ 14) * (a7 ^ 14) * b7
    - (3154859560796160 : R) * (h ^ 14) * (a7 ^ 13) * a6 * b8
    - (27503156613488640 : R) * (h ^ 8) * (a7 ^ 15) * a6
    + (189396815118336 : R) * (h ^ 6) * (a7 ^ 15) * b8
    + (1399936633267200 : R) * (a7 ^ 17)

set_option maxHeartbeats 200000000 in
/-- Integer expansion of compact block `9` after the extra
`2^{34}` scale, on `λ = 0`. -/
def alignedSquareCompactBlock9Expansion810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    (10766417859182592000 : R) * (h ^ 96) * (a6 ^ 2) * (a5 ^ 2) * a1
    + (21532835718365184000 : R) * (h ^ 96) * (a6 ^ 2) * a5 * a4 * a2
    + (10766417859182592000 : R) * (h ^ 96) * (a6 ^ 2) * a5 * (a3 ^ 2)
    - (1033576114481528832 : R) * (h ^ 94) * (a6 ^ 2) * (a5 ^ 2) * b3
    - (2756202971950743552 : R) * (h ^ 94) * (a6 ^ 2) * a5 * a4 * b4
    - (9420615626784768000 : R) * (h ^ 88) * (a7 ^ 2) * a6 * (a5 ^ 2) * a1
    - (18841231253569536000 : R) * (h ^ 88) * (a7 ^ 2) * a6 * a5 * a4 * a2
    - (9420615626784768000 : R) * (h ^ 88) * (a7 ^ 2) * a6 * a5 * (a3 ^ 2)
    - (16149626788773888000 : R) * (h ^ 88) * a7 * (a6 ^ 3) * a5 * a1
    - (16149626788773888000 : R) * (h ^ 88) * a7 * (a6 ^ 3) * a4 * a2
    - (8074813394386944000 : R) * (h ^ 88) * a7 * (a6 ^ 3) * (a3 ^ 2)
    - (16149626788773888000 : R) * (h ^ 88) * a7 * (a6 ^ 2) * (a5 ^ 2) * a2
    - (18841231253569536000 : R) * (h ^ 88) * a7 * (a6 ^ 2) * a5 * a4 * a3
    + (904379100171337728 : R) * (h ^ 86) * (a7 ^ 2) * a6 * (a5 ^ 2) * b3
    + (2411677600456900608 : R) * (h ^ 86) * (a7 ^ 2) * a6 * a5 * a4 * b4
    + (1550364171722293248 : R) * (h ^ 86) * a7 * (a6 ^ 3) * a5 * b3
    + (2067152228963057664 : R) * (h ^ 86) * a7 * (a6 ^ 3) * a4 * b4
    + (2239414914709979136 : R) * (h ^ 86) * a7 * (a6 ^ 2) * (a5 ^ 2) * b4
    + (1722626857469214720 : R) * (h ^ 86) * a7 * (a6 ^ 2) * a5 * a4 * b5
    + (2153283571836518400 : R) * (h ^ 86) * (a6 ^ 2) * (a5 ^ 3) * b6
    + (7536492501427814400 : R) * (h ^ 86) * (a6 ^ 2) * (a5 ^ 2) * a4 * b7
    + (8613134287346073600 : R) * (h ^ 86) * (a6 ^ 2) * (a5 ^ 2) * a3 * b8
    + (8613134287346073600 : R) * (h ^ 86) * (a6 ^ 2) * a5 * (a4 ^ 2) * b8
    + (2060759668359168000 : R) * (h ^ 80) * (a7 ^ 4) * (a5 ^ 2) * a1
    + (4121519336718336000 : R) * (h ^ 80) * (a7 ^ 4) * a5 * a4 * a2
    + (2060759668359168000 : R) * (h ^ 80) * (a7 ^ 4) * a5 * (a3 ^ 2)
    + (18841231253569536000 : R) * (h ^ 80) * (a7 ^ 3) * (a6 ^ 2) * a5 * a1
    + (18841231253569536000 : R) * (h ^ 80) * (a7 ^ 3) * (a6 ^ 2) * a4 * a2
    + (9420615626784768000 : R) * (h ^ 80) * (a7 ^ 3) * (a6 ^ 2) * (a3 ^ 2)
    + (14130923440177152000 : R) * (h ^ 80) * (a7 ^ 3) * a6 * (a5 ^ 2) * a2
    + (16486077346873344000 : R) * (h ^ 80) * (a7 ^ 3) * a6 * a5 * a4 * a3
    + (6056110045790208000 : R) * (h ^ 80) * (a7 ^ 2) * (a6 ^ 4) * a1
    + (19177681811668992000 : R) * (h ^ 80) * (a7 ^ 2) * (a6 ^ 3) * a5 * a2
    + (14130923440177152000 : R) * (h ^ 80) * (a7 ^ 2) * (a6 ^ 3) * a4 * a3
    + (2859829743845376000 : R) * (h ^ 80) * (a7 ^ 2) * (a6 ^ 2) * (a5 ^ 2) * a3
    - (1345802232397824000 : R) * (h ^ 80) * (a7 ^ 2) * (a6 ^ 2) * a5 * (a4 ^ 2)
    - (197832928162480128 : R) * (h ^ 78) * (a7 ^ 4) * (a5 ^ 2) * b3
    - (527554475099947008 : R) * (h ^ 78) * (a7 ^ 4) * a5 * a4 * b4
    - (1808758200342675456 : R) * (h ^ 78) * (a7 ^ 3) * (a6 ^ 2) * a5 * b3
    - (2411677600456900608 : R) * (h ^ 78) * (a7 ^ 3) * (a6 ^ 2) * a4 * b4
    - (1959488050371231744 : R) * (h ^ 78) * (a7 ^ 3) * a6 * (a5 ^ 2) * b4
    - (1507298500285562880 : R) * (h ^ 78) * (a7 ^ 3) * a6 * a5 * a4 * b5
    - (581386564395859968 : R) * (h ^ 78) * (a7 ^ 2) * (a6 ^ 4) * b3
    - (2713137300514013184 : R) * (h ^ 78) * (a7 ^ 2) * (a6 ^ 3) * a5 * b4
    - (1291970143101911040 : R) * (h ^ 78) * (a7 ^ 2) * (a6 ^ 3) * a4 * b5
    - (1238138053805998080 : R) * (h ^ 78) * (a7 ^ 2) * (a6 ^ 2) * (a5 ^ 2) * b5
    - (645985071550955520 : R) * (h ^ 78) * (a7 ^ 2) * (a6 ^ 2) * a5 * a4 * b6
    - (1884123125356953600 : R) * (h ^ 78) * (a7 ^ 2) * a6 * (a5 ^ 3) * b6
    - (6594430938749337600 : R) * (h ^ 78) * (a7 ^ 2) * a6 * (a5 ^ 2) * a4 * b7
    - (7536492501427814400 : R) * (h ^ 78) * (a7 ^ 2) * a6 * (a5 ^ 2) * a3 * b8
    - (7536492501427814400 : R) * (h ^ 78) * (a7 ^ 2) * a6 * a5 * (a4 ^ 2) * b8
    - (4844888036632166400 : R) * (h ^ 78) * a7 * (a6 ^ 3) * (a5 ^ 2) * b6
    - (11304738752141721600 : R) * (h ^ 78) * a7 * (a6 ^ 3) * a5 * a4 * b7
    - (12919701431019110400 : R) * (h ^ 78) * a7 * (a6 ^ 3) * a5 * a3 * b8
    - (6459850715509555200 : R) * (h ^ 78) * a7 * (a6 ^ 3) * (a4 ^ 2) * b8
    - (6594430938749337600 : R) * (h ^ 78) * a7 * (a6 ^ 2) * (a5 ^ 3) * b7
    - (22609477504283443200 : R) * (h ^ 78) * a7 * (a6 ^ 2) * (a5 ^ 2) * a4 * b8
    - (7212658839257088000 : R) * (h ^ 72) * (a7 ^ 5) * a6 * a5 * a1
    - (7212658839257088000 : R) * (h ^ 72) * (a7 ^ 5) * a6 * a4 * a2
    - (3606329419628544000 : R) * (h ^ 72) * (a7 ^ 5) * a6 * (a3 ^ 2)
    - (3091139502538752000 : R) * (h ^ 72) * (a7 ^ 5) * (a5 ^ 2) * a2
    - (3606329419628544000 : R) * (h ^ 72) * (a7 ^ 5) * a5 * a4 * a3
    - (8831827150110720000 : R) * (h ^ 72) * (a7 ^ 4) * (a6 ^ 3) * a1
    - (22005969315692544000 : R) * (h ^ 72) * (a7 ^ 4) * (a6 ^ 2) * a5 * a2
    - (16486077346873344000 : R) * (h ^ 72) * (a7 ^ 4) * (a6 ^ 2) * a4 * a3
    - (2502351025864704000 : R) * (h ^ 72) * (a7 ^ 4) * a6 * (a5 ^ 2) * a3
    + (1177576953348096000 : R) * (h ^ 72) * (a7 ^ 4) * a6 * a5 * (a4 ^ 2)
    - (5299096290066432000 : R) * (h ^ 72) * (a7 ^ 3) * (a6 ^ 4) * a2
    - (714957435961344000 : R) * (h ^ 72) * (a7 ^ 3) * (a6 ^ 3) * a5 * a3
    + (1009351674298368000 : R) * (h ^ 72) * (a7 ^ 3) * (a6 ^ 3) * (a4 ^ 2)
    + (10682305219657728000 : R) * (h ^ 72) * (a7 ^ 3) * (a6 ^ 2) * (a5 ^ 2) * a4
    + (692415248568680448 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a5 * b3
    + (923220331424907264 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a4 * b4
    + (428638011018706944 : R) * (h ^ 70) * (a7 ^ 5) * (a5 ^ 2) * b4
    + (329721546937466880 : R) * (h ^ 70) * (a7 ^ 5) * a5 * a4 * b5
    + (847855406410629120 : R) * (h ^ 70) * (a7 ^ 4) * (a6 ^ 3) * b3
    + (3118223772465758208 : R) * (h ^ 70) * (a7 ^ 4) * (a6 ^ 2) * a5 * b4
    + (1507298500285562880 : R) * (h ^ 70) * (a7 ^ 4) * (a6 ^ 2) * a4 * b5
    + (1083370797080248320 : R) * (h ^ 70) * (a7 ^ 4) * a6 * (a5 ^ 2) * b5
    + (565236937607086080 : R) * (h ^ 70) * (a7 ^ 4) * a6 * a5 * a4 * b6
    + (412151933671833600 : R) * (h ^ 70) * (a7 ^ 4) * (a5 ^ 3) * b6
    + (1442531767851417600 : R) * (h ^ 70) * (a7 ^ 4) * (a5 ^ 2) * a4 * b7
    + (1648607734687334400 : R) * (h ^ 70) * (a7 ^ 4) * (a5 ^ 2) * a3 * b8
    + (1648607734687334400 : R) * (h ^ 70) * (a7 ^ 4) * a5 * (a4 ^ 2) * b8
    + (775182085861146624 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 4) * b4
    + (1453466410989649920 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 3) * a5 * b5
    + (484488803663216640 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 3) * a4 * b6
    + (6096484112762142720 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 2) * (a5 ^ 2) * b6
    + (13377274190034370560 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 2) * a5 * a4 * b7
    + (15072985002855628800 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 2) * a5 * a3 * b8
    + (7536492501427814400 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 2) * (a4 ^ 2) * b8
    + (5770127071405670400 : R) * (h ^ 70) * (a7 ^ 3) * a6 * (a5 ^ 3) * b7
    + (19783292816248012800 : R) * (h ^ 70) * (a7 ^ 3) * a6 * (a5 ^ 2) * a4 * b8
    + (3633666027474124800 : R) * (h ^ 70) * (a7 ^ 2) * (a6 ^ 4) * a5 * b6
    + (4239277032053145600 : R) * (h ^ 70) * (a7 ^ 2) * (a6 ^ 4) * a4 * b7
    + (4844888036632166400 : R) * (h ^ 70) * (a7 ^ 2) * (a6 ^ 4) * a3 * b8
    + (13071104182163865600 : R) * (h ^ 70) * (a7 ^ 2) * (a6 ^ 3) * (a5 ^ 2) * b7
    + (29876809559231692800 : R) * (h ^ 70) * (a7 ^ 2) * (a6 ^ 3) * a5 * a4 * b8
    + (10362677189463244800 : R) * (h ^ 70) * (a7 ^ 2) * (a6 ^ 2) * (a5 ^ 3) * b8
    + (901582354907136000 : R) * (h ^ 64) * (a7 ^ 7) * a5 * a1
    + (901582354907136000 : R) * (h ^ 64) * (a7 ^ 7) * a4 * a2
    + (450791177453568000 : R) * (h ^ 64) * (a7 ^ 7) * (a3 ^ 2)
    + (4765506733080576000 : R) * (h ^ 64) * (a7 ^ 6) * (a6 ^ 2) * a1
    + (8243038673436672000 : R) * (h ^ 64) * (a7 ^ 6) * a6 * a5 * a2
    + (6311076484349952000 : R) * (h ^ 64) * (a7 ^ 6) * a6 * a4 * a3
    + (547389286907904000 : R) * (h ^ 64) * (a7 ^ 6) * (a5 ^ 2) * a3
    - (257594958544896000 : R) * (h ^ 64) * (a7 ^ 6) * a5 * (a4 ^ 2)
    + (7451854157905920000 : R) * (h ^ 64) * (a7 ^ 5) * (a6 ^ 3) * a2
    + (597988296622080000 : R) * (h ^ 64) * (a7 ^ 5) * (a6 ^ 2) * a5 * a3
    - (1177576953348096000 : R) * (h ^ 64) * (a7 ^ 5) * (a6 ^ 2) * (a4 ^ 2)
    - (9347017067200512000 : R) * (h ^ 64) * (a7 ^ 5) * a6 * (a5 ^ 2) * a4
    - (1072436153942016000 : R) * (h ^ 64) * (a7 ^ 4) * (a6 ^ 4) * a3
    - (14735483036762112000 : R) * (h ^ 64) * (a7 ^ 4) * (a6 ^ 3) * a5 * a4
    - (5312238889992192000 : R) * (h ^ 64) * (a7 ^ 4) * (a6 ^ 2) * (a5 ^ 3)
    - (86551906071085056 : R) * (h ^ 62) * (a7 ^ 7) * a5 * b3
    - (115402541428113408 : R) * (h ^ 62) * (a7 ^ 7) * a4 * b4
    - (457488646375735296 : R) * (h ^ 62) * (a7 ^ 6) * (a6 ^ 2) * b3
    - (1170511491628007424 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a5 * b4
    - (577012707140567040 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a4 * b5
    - (236987361861304320 : R) * (h ^ 62) * (a7 ^ 6) * (a5 ^ 2) * b5
    - (123645580101550080 : R) * (h ^ 62) * (a7 ^ 6) * a5 * a4 * b6
    - (1095146566613729280 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 3) * b4
    - (1666271388987555840 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 2) * a5 * b5
    - (565236937607086080 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 2) * a4 * b6
    - (2552398046381998080 : R) * (h ^ 62) * (a7 ^ 5) * a6 * (a5 ^ 2) * b6
    - (5213721960948695040 : R) * (h ^ 62) * (a7 ^ 5) * a6 * a5 * a4 * b7
    - (5770127071405670400 : R) * (h ^ 62) * (a7 ^ 5) * a6 * a5 * a3 * b8
    - (2885063535702835200 : R) * (h ^ 62) * (a7 ^ 5) * a6 * (a4 ^ 2) * b8
    - (1262215296869990400 : R) * (h ^ 62) * (a7 ^ 5) * (a5 ^ 3) * b7
    - (4327595303554252800 : R) * (h ^ 62) * (a7 ^ 5) * (a5 ^ 2) * a4 * b8
    - (393647152976363520 : R) * (h ^ 62) * (a7 ^ 4) * (a6 ^ 4) * b5
    - (5813865643958599680 : R) * (h ^ 62) * (a7 ^ 4) * (a6 ^ 3) * a5 * b6
    - (6323588239479275520 : R) * (h ^ 62) * (a7 ^ 4) * (a6 ^ 3) * a4 * b7
    - (7065461720088576000 : R) * (h ^ 62) * (a7 ^ 4) * (a6 ^ 3) * a3 * b8
    - (15247413589070315520 : R) * (h ^ 62) * (a7 ^ 4) * (a6 ^ 2) * (a5 ^ 2) * b7
    - (34608986658900541440 : R) * (h ^ 62) * (a7 ^ 4) * (a6 ^ 2) * a5 * a4 * b8
    - (9067342540780339200 : R) * (h ^ 62) * (a7 ^ 4) * a6 * (a5 ^ 3) * b8
    - (908416506868531200 : R) * (h ^ 62) * (a7 ^ 3) * (a6 ^ 5) * b6
    - (8478554064106291200 : R) * (h ^ 62) * (a7 ^ 3) * (a6 ^ 4) * a5 * b7
    - (9689776073264332800 : R) * (h ^ 62) * (a7 ^ 3) * (a6 ^ 4) * a4 * b8
    - (18353377944325324800 : R) * (h ^ 62) * (a7 ^ 3) * (a6 ^ 3) * (a5 ^ 2) * b8
    - (1126977943633920000 : R) * (h ^ 56) * (a7 ^ 8) * a6 * a1
    - (1000192924975104000 : R) * (h ^ 56) * (a7 ^ 8) * a5 * a2
    - (788884560543744000 : R) * (h ^ 56) * (a7 ^ 8) * a4 * a3
    - (3847824693264384000 : R) * (h ^ 56) * (a7 ^ 7) * (a6 ^ 2) * a2
    - (112697794363392000 : R) * (h ^ 56) * (a7 ^ 7) * a6 * a5 * a3
    + (450791177453568000 : R) * (h ^ 56) * (a7 ^ 7) * a6 * (a4 ^ 2)
    + (2044659983450112000 : R) * (h ^ 56) * (a7 ^ 7) * (a5 ^ 2) * a4
    + (1741065925165056000 : R) * (h ^ 56) * (a7 ^ 6) * (a6 ^ 3) * a3
    + (17090505517459046400 : R) * (h ^ 56) * (a7 ^ 6) * (a6 ^ 2) * a5 * a4
    + (4648209028743168000 : R) * (h ^ 56) * (a7 ^ 6) * a6 * (a5 ^ 3)
    + (5042815591514112000 : R) * (h ^ 56) * (a7 ^ 5) * (a6 ^ 4) * a4
    + (9394330426933248000 : R) * (h ^ 56) * (a7 ^ 5) * (a6 ^ 3) * (a5 ^ 2)
    + (108189882588856320 : R) * (h ^ 54) * (a7 ^ 8) * a6 * b3
    + (142450012075327488 : R) * (h ^ 54) * (a7 ^ 8) * a5 * b4
    + (72126588392570880 : R) * (h ^ 54) * (a7 ^ 8) * a4 * b5
    + (568769668467130368 : R) * (h ^ 54) * (a7 ^ 7) * (a6 ^ 2) * b4
    + (623379799678648320 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a5 * b5
    + (216379765177712640 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a4 * b6
    + (355481042791956480 : R) * (h ^ 54) * (a7 ^ 7) * (a5 ^ 2) * b6
    + (667170942631280640 : R) * (h ^ 54) * (a7 ^ 7) * a5 * a4 * b7
    + (721265883925708800 : R) * (h ^ 54) * (a7 ^ 7) * a5 * a3 * b8
    + (360632941962854400 : R) * (h ^ 54) * (a7 ^ 7) * (a4 ^ 2) * b8
    + (551989196881920000 : R) * (h ^ 54) * (a7 ^ 6) * (a6 ^ 3) * b5
    + (3448828502118236160 : R) * (h ^ 54) * (a7 ^ 6) * (a6 ^ 2) * a5 * b6
    + (3500715486625136640 : R) * (h ^ 54) * (a7 ^ 6) * (a6 ^ 2) * a4 * b7
    + (3812405386464460800 : R) * (h ^ 54) * (a7 ^ 6) * (a6 ^ 2) * a3 * b8
    + (5835813785834618880 : R) * (h ^ 54) * (a7 ^ 6) * a6 * (a5 ^ 2) * b7
    + (13127039087447900160 : R) * (h ^ 54) * (a7 ^ 6) * a6 * a5 * a4 * b8
    + (1983481180795699200 : R) * (h ^ 54) * (a7 ^ 6) * (a5 ^ 3) * b8
    + (1725991363050209280 : R) * (h ^ 54) * (a7 ^ 5) * (a6 ^ 4) * b6
    + (12317086939223162880 : R) * (h ^ 54) * (a7 ^ 5) * (a6 ^ 3) * a5 * b7
    + (13945455070024826880 : R) * (h ^ 54) * (a7 ^ 5) * (a6 ^ 3) * a4 * b8
    + (21091433614298578944 : R) * (h ^ 54) * (a7 ^ 5) * (a6 ^ 2) * (a5 ^ 2) * b8
    + (1788444997897420800 : R) * (h ^ 54) * (a7 ^ 4) * (a6 ^ 5) * b7
    + (10516182756596121600 : R) * (h ^ 54) * (a7 ^ 4) * (a6 ^ 4) * a5 * b8
    + (98610570067968000 : R) * (h ^ 48) * (a7 ^ 10) * a1
    + (862842488094720000 : R) * (h ^ 48) * (a7 ^ 9) * a6 * a2
    - (5282709110784000 : R) * (h ^ 48) * (a7 ^ 9) * a5 * a3
    - (56348897181696000 : R) * (h ^ 48) * (a7 ^ 9) * (a4 ^ 2)
    - (1050504440315904000 : R) * (h ^ 48) * (a7 ^ 8) * (a6 ^ 2) * a3
    - (6492801677760921600 : R) * (h ^ 48) * (a7 ^ 8) * a6 * a5 * a4
    - (1016795725037568000 : R) * (h ^ 48) * (a7 ^ 8) * (a5 ^ 3)
    - (7278437551885516800 : R) * (h ^ 48) * (a7 ^ 7) * (a6 ^ 3) * a4
    - (10779997450555883520 : R) * (h ^ 48) * (a7 ^ 7) * (a6 ^ 2) * (a5 ^ 2)
    - (5338606231093248000 : R) * (h ^ 48) * (a7 ^ 6) * (a6 ^ 4) * a5
    - (9466614726524928 : R) * (h ^ 46) * (a7 ^ 10) * b3
    - (128475485574266880 : R) * (h ^ 46) * (a7 ^ 9) * a6 * b4
    - (75507522223472640 : R) * (h ^ 46) * (a7 ^ 9) * a5 * b5
    - (27047470647214080 : R) * (h ^ 46) * (a7 ^ 9) * a4 * b6
    - (283998441795747840 : R) * (h ^ 46) * (a7 ^ 8) * (a6 ^ 2) * b5
    - (896430455736238080 : R) * (h ^ 46) * (a7 ^ 8) * a6 * a5 * b6
    - (851995325387243520 : R) * (h ^ 46) * (a7 ^ 8) * a6 * a4 * b7
    - (901582354907136000 : R) * (h ^ 46) * (a7 ^ 8) * a6 * a3 * b8
    - (729295601774100480 : R) * (h ^ 46) * (a7 ^ 8) * (a5 ^ 2) * b7
    - (1620594282945576960 : R) * (h ^ 46) * (a7 ^ 8) * a5 * a4 * b8
    - (1291654720703692800 : R) * (h ^ 46) * (a7 ^ 7) * (a6 ^ 3) * b6
    - (6613106573243842560 : R) * (h ^ 46) * (a7 ^ 7) * (a6 ^ 2) * a5 * b7
    - (7408431007751208960 : R) * (h ^ 46) * (a7 ^ 7) * (a6 ^ 2) * a4 * b8
    - (7916150671043198976 : R) * (h ^ 46) * (a7 ^ 7) * a6 * (a5 ^ 2) * b8
    - (3095417418814586880 : R) * (h ^ 46) * (a7 ^ 6) * (a6 ^ 4) * b7
    - (14912797737920495616 : R) * (h ^ 46) * (a7 ^ 6) * (a6 ^ 3) * a5 * b8
    - (1935116413068902400 : R) * (h ^ 46) * (a7 ^ 5) * (a6 ^ 5) * b8
    - (70876347236352000 : R) * (h ^ 40) * (a7 ^ 11) * a2
    + (278662905593856000 : R) * (h ^ 40) * (a7 ^ 10) * a6 * a3
    + (803323965446553600 : R) * (h ^ 40) * (a7 ^ 10) * a5 * a4
    + (3879873128536473600 : R) * (h ^ 40) * (a7 ^ 9) * (a6 ^ 2) * a4
    + (4038097094395822080 : R) * (h ^ 40) * (a7 ^ 9) * a6 * (a5 ^ 2)
    + (7546907909192417280 : R) * (h ^ 40) * (a7 ^ 8) * (a6 ^ 3) * a5
    + (960744589885440000 : R) * (h ^ 40) * (a7 ^ 7) * (a6 ^ 5)
    + (10649941567340544 : R) * (h ^ 38) * (a7 ^ 11) * b4
    + (63392509329408000 : R) * (h ^ 38) * (a7 ^ 10) * a6 * b5
    + (85791195959132160 : R) * (h ^ 38) * (a7 ^ 10) * a5 * b6
    + (76916244653015040 : R) * (h ^ 38) * (a7 ^ 10) * a4 * b7
    + (78888456054374400 : R) * (h ^ 38) * (a7 ^ 10) * a3 * b8
    + (475101701666242560 : R) * (h ^ 38) * (a7 ^ 9) * (a6 ^ 2) * b6
    + (1553750403663790080 : R) * (h ^ 38) * (a7 ^ 9) * a6 * a5 * b7
    + (1720331830957178880 : R) * (h ^ 38) * (a7 ^ 9) * a6 * a4 * b8
    + (963199873975320576 : R) * (h ^ 38) * (a7 ^ 9) * (a5 ^ 2) * b8
    + (2115498597049958400 : R) * (h ^ 38) * (a7 ^ 8) * (a6 ^ 3) * b7
    + (7782962002711805952 : R) * (h ^ 38) * (a7 ^ 8) * (a6 ^ 2) * a5 * b8
    + (3249450004204486656 : R) * (h ^ 38) * (a7 ^ 7) * (a6 ^ 4) * b8
    - (27349025292288000 : R) * (h ^ 32) * (a7 ^ 12) * a3
    - (904619912645836800 : R) * (h ^ 32) * (a7 ^ 11) * a6 * a4
    - (489992023525294080 : R) * (h ^ 32) * (a7 ^ 11) * (a5 ^ 2)
    - (3923748992487260160 : R) * (h ^ 32) * (a7 ^ 10) * (a6 ^ 2) * a5
    - (1603664175672852480 : R) * (h ^ 32) * (a7 ^ 9) * (a6 ^ 4)
    - (5177054928568320 : R) * (h ^ 30) * (a7 ^ 12) * b5
    - (85755977898393600 : R) * (h ^ 30) * (a7 ^ 11) * a6 * b6
    - (134788322961653760 : R) * (h ^ 30) * (a7 ^ 11) * a5 * b7
    - (147422802251612160 : R) * (h ^ 30) * (a7 ^ 11) * a4 * b8
    - (713421060896194560 : R) * (h ^ 30) * (a7 ^ 10) * (a6 ^ 2) * b7
    - (1769394111372066816 : R) * (h ^ 30) * (a7 ^ 10) * a6 * a5 * b8
    - (2147310568199946240 : R) * (h ^ 30) * (a7 ^ 9) * (a6 ^ 3) * b8
    + (77886942452121600 : R) * (h ^ 24) * (a7 ^ 13) * a4
    + (887928890555105280 : R) * (h ^ 24) * (a7 ^ 12) * a6 * a5
    + (1052299258704691200 : R) * (h ^ 24) * (a7 ^ 11) * (a6 ^ 3)
    + (6070713219809280 : R) * (h ^ 22) * (a7 ^ 13) * b6
    + (118717881620889600 : R) * (h ^ 22) * (a7 ^ 12) * a6 * b7
    + (147928951818289152 : R) * (h ^ 22) * (a7 ^ 12) * a5 * b8
    + (697923353268191232 : R) * (h ^ 22) * (a7 ^ 11) * (a6 ^ 2) * b8
    - (73831586197340160 : R) * (h ^ 16) * (a7 ^ 14) * a5
    - (339206687503810560 : R) * (h ^ 16) * (a7 ^ 13) * (a6 ^ 2)
    - (7799287177543680 : R) * (h ^ 14) * (a7 ^ 14) * b7
    - (111617727977226240 : R) * (h ^ 14) * (a7 ^ 13) * a6 * b8
    + (53729854849843200 : R) * (h ^ 8) * (a7 ^ 15) * a6
    + (7030986610507776 : R) * (h ^ 6) * (a7 ^ 15) * b8
    - (3347114583214080 : R) * (a7 ^ 17)

set_option maxHeartbeats 200000000 in
/-- Integer expansion of compact block `10` after the extra
`2^{34}` scale, on `λ = 0`. -/
def alignedSquareCompactBlock10Expansion810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    (10766417859182592000 : R) * (h ^ 96) * (a6 ^ 2) * (a4 ^ 2) * a3
    - (3445253714938429440 : R) * (h ^ 94) * (a6 ^ 2) * a5 * a3 * b5
    - (4134304457926115328 : R) * (h ^ 94) * (a6 ^ 2) * a5 * a2 * b6
    - (4823355200913801216 : R) * (h ^ 94) * (a6 ^ 2) * a5 * a1 * b7
    - (5512405943901487104 : R) * (h ^ 94) * (a6 ^ 2) * a5 * a0 * b8
    - (1722626857469214720 : R) * (h ^ 94) * (a6 ^ 2) * (a4 ^ 2) * b5
    - (4134304457926115328 : R) * (h ^ 94) * (a6 ^ 2) * a4 * a3 * b6
    - (4823355200913801216 : R) * (h ^ 94) * (a6 ^ 2) * a4 * a2 * b7
    - (5512405943901487104 : R) * (h ^ 94) * (a6 ^ 2) * a4 * a1 * b8
    + (3875910429305733120 : R) * (h ^ 88) * (a7 ^ 2) * (a6 ^ 2) * a5 * a0
    + (3875910429305733120 : R) * (h ^ 88) * (a7 ^ 2) * (a6 ^ 2) * a4 * a1
    - (9420615626784768000 : R) * (h ^ 88) * (a7 ^ 2) * a6 * (a4 ^ 2) * a3
    - (13458022323978240000 : R) * (h ^ 88) * a7 * (a6 ^ 2) * a5 * a4 * a3
    - (5383208929591296000 : R) * (h ^ 88) * a7 * (a6 ^ 2) * (a4 ^ 3)
    + (3014597000571125760 : R) * (h ^ 86) * (a7 ^ 2) * a6 * a5 * a3 * b5
    + (3617516400685350912 : R) * (h ^ 86) * (a7 ^ 2) * a6 * a5 * a2 * b6
    + (4220435800799576064 : R) * (h ^ 86) * (a7 ^ 2) * a6 * a5 * a1 * b7
    + (4823355200913801216 : R) * (h ^ 86) * (a7 ^ 2) * a6 * a5 * a0 * b8
    + (1507298500285562880 : R) * (h ^ 86) * (a7 ^ 2) * a6 * (a4 ^ 2) * b5
    + (3617516400685350912 : R) * (h ^ 86) * (a7 ^ 2) * a6 * a4 * a3 * b6
    + (4220435800799576064 : R) * (h ^ 86) * (a7 ^ 2) * a6 * a4 * a2 * b7
    + (4823355200913801216 : R) * (h ^ 86) * (a7 ^ 2) * a6 * a4 * a1 * b8
    + (2583940286203822080 : R) * (h ^ 86) * a7 * (a6 ^ 3) * a3 * b5
    + (3100728343444586496 : R) * (h ^ 86) * a7 * (a6 ^ 3) * a2 * b6
    + (3617516400685350912 : R) * (h ^ 86) * a7 * (a6 ^ 3) * a1 * b7
    + (4134304457926115328 : R) * (h ^ 86) * a7 * (a6 ^ 3) * a0 * b8
    + (3875910429305733120 : R) * (h ^ 86) * a7 * (a6 ^ 2) * a5 * a4 * b5
    + (6718244744129937408 : R) * (h ^ 86) * a7 * (a6 ^ 2) * a5 * a3 * b6
    + (7837952201484926976 : R) * (h ^ 86) * a7 * (a6 ^ 2) * a5 * a2 * b7
    + (8957659658839916544 : R) * (h ^ 86) * a7 * (a6 ^ 2) * a5 * a1 * b8
    + (3359122372064968704 : R) * (h ^ 86) * a7 * (a6 ^ 2) * (a4 ^ 2) * b6
    + (5426274601028026368 : R) * (h ^ 86) * a7 * (a6 ^ 2) * a4 * a3 * b7
    + (6201456686889172992 : R) * (h ^ 86) * a7 * (a6 ^ 2) * a4 * a2 * b8
    - (3391421625642516480 : R) * (h ^ 80) * (a7 ^ 4) * a6 * a5 * a0
    - (3391421625642516480 : R) * (h ^ 80) * (a7 ^ 4) * a6 * a4 * a1
    + (2060759668359168000 : R) * (h ^ 80) * (a7 ^ 4) * (a4 ^ 2) * a3
    - (2906932821979299840 : R) * (h ^ 80) * (a7 ^ 3) * (a6 ^ 3) * a0
    - (5167880572407644160 : R) * (h ^ 80) * (a7 ^ 3) * (a6 ^ 2) * a5 * a1
    - (3229925357754777600 : R) * (h ^ 80) * (a7 ^ 3) * (a6 ^ 2) * a4 * a2
    + (11775769533480960000 : R) * (h ^ 80) * (a7 ^ 3) * a6 * a5 * a4 * a3
    + (4710307813392384000 : R) * (h ^ 80) * (a7 ^ 3) * a6 * (a4 ^ 3)
    + (5046758371491840000 : R) * (h ^ 80) * (a7 ^ 2) * (a6 ^ 3) * a4 * a3
    + (4205631976243200000 : R) * (h ^ 80) * (a7 ^ 2) * (a6 ^ 2) * (a5 ^ 2) * a3
    + (8411263952486400000 : R) * (h ^ 80) * (a7 ^ 2) * (a6 ^ 2) * a5 * (a4 ^ 2)
    - (659443093874933760 : R) * (h ^ 78) * (a7 ^ 4) * a5 * a3 * b5
    - (791331712649920512 : R) * (h ^ 78) * (a7 ^ 4) * a5 * a2 * b6
    - (923220331424907264 : R) * (h ^ 78) * (a7 ^ 4) * a5 * a1 * b7
    - (1055108950199894016 : R) * (h ^ 78) * (a7 ^ 4) * a5 * a0 * b8
    - (329721546937466880 : R) * (h ^ 78) * (a7 ^ 4) * (a4 ^ 2) * b5
    - (791331712649920512 : R) * (h ^ 78) * (a7 ^ 4) * a4 * a3 * b6
    - (923220331424907264 : R) * (h ^ 78) * (a7 ^ 4) * a4 * a2 * b7
    - (1055108950199894016 : R) * (h ^ 78) * (a7 ^ 4) * a4 * a1 * b8
    - (3014597000571125760 : R) * (h ^ 78) * (a7 ^ 3) * (a6 ^ 2) * a3 * b5
    - (3617516400685350912 : R) * (h ^ 78) * (a7 ^ 3) * (a6 ^ 2) * a2 * b6
    - (4220435800799576064 : R) * (h ^ 78) * (a7 ^ 3) * (a6 ^ 2) * a1 * b7
    - (4823355200913801216 : R) * (h ^ 78) * (a7 ^ 3) * (a6 ^ 2) * a0 * b8
    - (3391421625642516480 : R) * (h ^ 78) * (a7 ^ 3) * a6 * a5 * a4 * b5
    - (5878464151113695232 : R) * (h ^ 78) * (a7 ^ 3) * a6 * a5 * a3 * b6
    - (6858208176299311104 : R) * (h ^ 78) * (a7 ^ 3) * a6 * a5 * a2 * b7
    - (7837952201484926976 : R) * (h ^ 78) * (a7 ^ 3) * a6 * a5 * a1 * b8
    - (2939232075556847616 : R) * (h ^ 78) * (a7 ^ 3) * a6 * (a4 ^ 2) * b6
    - (4747990275899523072 : R) * (h ^ 78) * (a7 ^ 3) * a6 * a4 * a3 * b7
    - (5426274601028026368 : R) * (h ^ 78) * (a7 ^ 3) * a6 * a4 * a2 * b8
    - (2099451482540605440 : R) * (h ^ 78) * (a7 ^ 2) * (a6 ^ 3) * a4 * b5
    - (4069705950771019776 : R) * (h ^ 78) * (a7 ^ 2) * (a6 ^ 3) * a3 * b6
    - (4747990275899523072 : R) * (h ^ 78) * (a7 ^ 2) * (a6 ^ 3) * a2 * b7
    - (5426274601028026368 : R) * (h ^ 78) * (a7 ^ 2) * (a6 ^ 3) * a1 * b8
    - (1211222009158041600 : R) * (h ^ 78) * (a7 ^ 2) * (a6 ^ 2) * (a5 ^ 2) * b5
    - (5232479079562739712 : R) * (h ^ 78) * (a7 ^ 2) * (a6 ^ 2) * a5 * a4 * b6
    - (6104558926156529664 : R) * (h ^ 78) * (a7 ^ 2) * (a6 ^ 2) * a5 * a3 * b7
    - (6976638772750319616 : R) * (h ^ 78) * (a7 ^ 2) * (a6 ^ 2) * a5 * a2 * b8
    - (2826184688035430400 : R) * (h ^ 78) * (a7 ^ 2) * (a6 ^ 2) * (a4 ^ 2) * b7
    - (3875910429305733120 : R) * (h ^ 78) * (a7 ^ 2) * (a6 ^ 2) * a4 * a3 * b8
    + (741873480609300480 : R) * (h ^ 72) * (a7 ^ 6) * a5 * a0
    + (741873480609300480 : R) * (h ^ 72) * (a7 ^ 6) * a4 * a1
    + (3391421625642516480 : R) * (h ^ 72) * (a7 ^ 5) * (a6 ^ 2) * a0
    + (4521895500856688640 : R) * (h ^ 72) * (a7 ^ 5) * a6 * a5 * a1
    + (2826184688035430400 : R) * (h ^ 72) * (a7 ^ 5) * a6 * a4 * a2
    - (2575949585448960000 : R) * (h ^ 72) * (a7 ^ 5) * a5 * a4 * a3
    - (1030379834179584000 : R) * (h ^ 72) * (a7 ^ 5) * (a4 ^ 3)
    + (2967493922437201920 : R) * (h ^ 72) * (a7 ^ 4) * (a6 ^ 3) * a1
    + (3280392941469696000 : R) * (h ^ 72) * (a7 ^ 4) * (a6 ^ 2) * a5 * a2
    - (3854461706226892800 : R) * (h ^ 72) * (a7 ^ 4) * (a6 ^ 2) * a4 * a3
    - (3679927979212800000 : R) * (h ^ 72) * (a7 ^ 4) * a6 * (a5 ^ 2) * a3
    - (7359855958425600000 : R) * (h ^ 72) * (a7 ^ 4) * a6 * a5 * (a4 ^ 2)
    - (3154223982182400000 : R) * (h ^ 72) * (a7 ^ 3) * (a6 ^ 3) * a5 * a3
    - (2943942383370240000 : R) * (h ^ 72) * (a7 ^ 3) * (a6 ^ 3) * (a4 ^ 2)
    - (4205631976243200000 : R) * (h ^ 72) * (a7 ^ 3) * (a6 ^ 2) * (a5 ^ 2) * a4
    + (1154025414281134080 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a3 * b5
    + (1384830497137360896 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a2 * b6
    + (1615635579993587712 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a1 * b7
    + (1846440662849814528 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a0 * b8
    + (741873480609300480 : R) * (h ^ 70) * (a7 ^ 5) * a5 * a4 * b5
    + (1285914033056120832 : R) * (h ^ 70) * (a7 ^ 5) * a5 * a3 * b6
    + (1500233038565474304 : R) * (h ^ 70) * (a7 ^ 5) * a5 * a2 * b7
    + (1714552044074827776 : R) * (h ^ 70) * (a7 ^ 5) * a5 * a1 * b8
    + (642957016528060416 : R) * (h ^ 70) * (a7 ^ 5) * (a4 ^ 2) * b6
    + (1038622872853020672 : R) * (h ^ 70) * (a7 ^ 5) * a4 * a3 * b7
    + (1186997568974880768 : R) * (h ^ 70) * (a7 ^ 5) * a4 * a2 * b8
    + (2390481215296634880 : R) * (h ^ 70) * (a7 ^ 4) * (a6 ^ 2) * a4 * b5
    + (4677335658698637312 : R) * (h ^ 70) * (a7 ^ 4) * (a6 ^ 2) * a3 * b6
    + (5456891601815076864 : R) * (h ^ 70) * (a7 ^ 4) * (a6 ^ 2) * a2 * b7
    + (6236447544931516416 : R) * (h ^ 70) * (a7 ^ 4) * (a6 ^ 2) * a1 * b8
    + (1059819258013286400 : R) * (h ^ 70) * (a7 ^ 4) * a6 * (a5 ^ 2) * b5
    + (4578419194617397248 : R) * (h ^ 70) * (a7 ^ 4) * a6 * a5 * a4 * b6
    + (5341489060386963456 : R) * (h ^ 70) * (a7 ^ 4) * a6 * a5 * a3 * b7
    + (6104558926156529664 : R) * (h ^ 70) * (a7 ^ 4) * a6 * a5 * a2 * b8
    + (2472911602031001600 : R) * (h ^ 70) * (a7 ^ 4) * a6 * (a4 ^ 2) * b7
    + (3391421625642516480 : R) * (h ^ 70) * (a7 ^ 4) * a6 * a4 * a3 * b8
    + (1042996730108313600 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 3) * a5 * b5
    + (2511266965654339584 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 3) * a4 * b6
    + (3306636085001453568 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 3) * a3 * b7
    + (3779012668573089792 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 3) * a2 * b8
    + (1392905310531747840 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 2) * (a5 ^ 2) * b6
    + (3721143172579983360 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 2) * a5 * a4 * b7
    + (3714414161417994240 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 2) * a5 * a3 * b8
    + (1588046634229432320 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 2) * (a4 ^ 2) * b8
    - (1298278591066275840 : R) * (h ^ 64) * (a7 ^ 7) * a6 * a0
    - (989164640812400640 : R) * (h ^ 64) * (a7 ^ 7) * a5 * a1
    - (618227900507750400 : R) * (h ^ 64) * (a7 ^ 7) * a4 * a2
    - (3395837539217571840 : R) * (h ^ 64) * (a7 ^ 6) * (a6 ^ 2) * a1
    - (2870343823785984000 : R) * (h ^ 64) * (a7 ^ 6) * a6 * a5 * a2
    + (474710709318451200 : R) * (h ^ 64) * (a7 ^ 6) * a6 * a4 * a3
    + (804984245452800000 : R) * (h ^ 64) * (a7 ^ 6) * (a5 ^ 2) * a3
    + (1609968490905600000 : R) * (h ^ 64) * (a7 ^ 6) * a5 * (a4 ^ 2)
    - (1703280950378496000 : R) * (h ^ 64) * (a7 ^ 5) * (a6 ^ 3) * a2
    + (1951045244178923520 : R) * (h ^ 64) * (a7 ^ 5) * (a6 ^ 2) * a5 * a3
    + (2588356199778877440 : R) * (h ^ 64) * (a7 ^ 5) * (a6 ^ 2) * (a4 ^ 2)
    + (3679927979212800000 : R) * (h ^ 64) * (a7 ^ 5) * a6 * (a5 ^ 2) * a4
    + (591416996659200000 : R) * (h ^ 64) * (a7 ^ 4) * (a6 ^ 4) * a3
    + (2891371983667200000 : R) * (h ^ 64) * (a7 ^ 4) * (a6 ^ 3) * a5 * a4
    + (657129996288000000 : R) * (h ^ 64) * (a7 ^ 4) * (a6 ^ 2) * (a5 ^ 3)
    - (144253176785141760 : R) * (h ^ 62) * (a7 ^ 7) * a3 * b5
    - (173103812142170112 : R) * (h ^ 62) * (a7 ^ 7) * a2 * b6
    - (201954447499198464 : R) * (h ^ 62) * (a7 ^ 7) * a1 * b7
    - (230805082856226816 : R) * (h ^ 62) * (a7 ^ 7) * a0 * b8
    - (886126657394442240 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a4 * b5
    - (1755767237442011136 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a3 * b6
    - (2048395110349012992 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a2 * b7
    - (2341022983256014848 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a1 * b8
    - (231835462690406400 : R) * (h ^ 62) * (a7 ^ 6) * (a5 ^ 2) * b5
    - (1001529198822555648 : R) * (h ^ 62) * (a7 ^ 6) * a5 * a4 * b6
    - (1168450731959648256 : R) * (h ^ 62) * (a7 ^ 6) * a5 * a3 * b7
    - (1335372265096740864 : R) * (h ^ 62) * (a7 ^ 6) * a5 * a2 * b8
    - (540949412944281600 : R) * (h ^ 62) * (a7 ^ 6) * (a4 ^ 2) * b7
    - (741873480609300480 : R) * (h ^ 62) * (a7 ^ 6) * a4 * a3 * b8
    - (1164329212622929920 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 2) * a5 * b5
    - (2831483784325496832 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 2) * a4 * b6
    - (3765007914092199936 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 2) * a3 * b7
    - (4302866187533942784 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 2) * a2 * b8
    - (1218792146715279360 : R) * (h ^ 62) * (a7 ^ 5) * a6 * (a5 ^ 2) * b6
    - (3256000276007485440 : R) * (h ^ 62) * (a7 ^ 5) * a6 * a5 * a4 * b7
    - (3250112391240744960 : R) * (h ^ 62) * (a7 ^ 5) * a6 * a5 * a3 * b8
    - (1389540804950753280 : R) * (h ^ 62) * (a7 ^ 5) * a6 * (a4 ^ 2) * b8
    - (195561886895308800 : R) * (h ^ 62) * (a7 ^ 4) * (a6 ^ 4) * b5
    - (1110286841728204800 : R) * (h ^ 62) * (a7 ^ 4) * (a6 ^ 3) * a5 * b6
    - (1660383504220815360 : R) * (h ^ 62) * (a7 ^ 4) * (a6 ^ 3) * a4 * b7
    - (1877394114194964480 : R) * (h ^ 62) * (a7 ^ 4) * (a6 ^ 3) * a3 * b8
    - (886126657394442240 : R) * (h ^ 62) * (a7 ^ 4) * (a6 ^ 2) * (a5 ^ 2) * b7
    - (1890852136518942720 : R) * (h ^ 62) * (a7 ^ 4) * (a6 ^ 2) * a5 * a4 * b8
    + (162284823883284480 : R) * (h ^ 56) * (a7 ^ 9) * a0
    + (1267367196040888320 : R) * (h ^ 56) * (a7 ^ 8) * a6 * a1
    + (627887711453184000 : R) * (h ^ 56) * (a7 ^ 8) * a5 * a2
    + (107465396767948800 : R) * (h ^ 56) * (a7 ^ 8) * a4 * a3
    + (1931962189086720000 : R) * (h ^ 56) * (a7 ^ 7) * (a6 ^ 2) * a2
    + (104049963612241920 : R) * (h ^ 56) * (a7 ^ 7) * a6 * a5 * a3
    - (574344759355637760 : R) * (h ^ 56) * (a7 ^ 7) * a6 * (a4 ^ 2)
    - (804984245452800000 : R) * (h ^ 56) * (a7 ^ 7) * (a5 ^ 2) * a4
    - (42404598660464640 : R) * (h ^ 56) * (a7 ^ 6) * (a6 ^ 3) * a3
    - (2443616746796482560 : R) * (h ^ 56) * (a7 ^ 6) * (a6 ^ 2) * a5 * a4
    - (574988746752000000 : R) * (h ^ 56) * (a7 ^ 6) * a6 * (a5 ^ 3)
    - (492847497216000000 : R) * (h ^ 56) * (a7 ^ 5) * (a6 ^ 4) * a4
    - (657129996288000000 : R) * (h ^ 56) * (a7 ^ 5) * (a6 ^ 3) * (a5 ^ 2)
    + (105935926701588480 : R) * (h ^ 54) * (a7 ^ 8) * a4 * b5
    + (213675018112991232 : R) * (h ^ 54) * (a7 ^ 8) * a3 * b6
    + (249287521131823104 : R) * (h ^ 54) * (a7 ^ 8) * a2 * b7
    + (284900024150654976 : R) * (h ^ 54) * (a7 ^ 8) * a1 * b8
    + (419879782428180480 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a5 * b5
    + (1035531733350481920 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a4 * b6
    + (1395649485396246528 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a3 * b7
    + (1595027983309996032 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a2 * b8
    + (266610782093967360 : R) * (h ^ 54) * (a7 ^ 7) * (a5 ^ 2) * b6
    + (712250060376637440 : R) * (h ^ 54) * (a7 ^ 7) * a5 * a4 * b7
    + (710962085583912960 : R) * (h ^ 54) * (a7 ^ 7) * a5 * a3 * b8
    + (303962051082977280 : R) * (h ^ 54) * (a7 ^ 7) * (a4 ^ 2) * b8
    + (259618918933463040 : R) * (h ^ 54) * (a7 ^ 6) * (a6 ^ 3) * b5
    + (1230935909046681600 : R) * (h ^ 54) * (a7 ^ 6) * (a6 ^ 2) * a5 * b6
    + (1860093195652694016 : R) * (h ^ 54) * (a7 ^ 6) * (a6 ^ 2) * a4 * b7
    + (2124054429601628160 : R) * (h ^ 54) * (a7 ^ 6) * (a6 ^ 2) * a3 * b8
    + (775360825220136960 : R) * (h ^ 54) * (a7 ^ 6) * a6 * (a5 ^ 2) * b7
    + (1654495619454074880 : R) * (h ^ 54) * (a7 ^ 6) * a6 * a5 * a4 * b8
    + (195877309293527040 : R) * (h ^ 54) * (a7 ^ 5) * (a6 ^ 4) * b6
    + (667686132548370432 : R) * (h ^ 54) * (a7 ^ 5) * (a6 ^ 3) * a5 * b7
    + (803443932741500928 : R) * (h ^ 54) * (a7 ^ 5) * (a6 ^ 3) * a4 * b8
    + (413581848543756288 : R) * (h ^ 54) * (a7 ^ 5) * (a6 ^ 2) * (a5 ^ 2) * b8
    - (152987255848304640 : R) * (h ^ 48) * (a7 ^ 10) * a1
    - (712411057225728000 : R) * (h ^ 48) * (a7 ^ 9) * a6 * a2
    - (154828657309777920 : R) * (h ^ 48) * (a7 ^ 9) * a5 * a3
    + (2374703524085760 : R) * (h ^ 48) * (a7 ^ 9) * (a4 ^ 2)
    - (459770345470033920 : R) * (h ^ 48) * (a7 ^ 8) * (a6 ^ 2) * a3
    + (477884647200522240 : R) * (h ^ 48) * (a7 ^ 8) * a6 * a5 * a4
    + (125778788352000000 : R) * (h ^ 48) * (a7 ^ 8) * (a5 ^ 3)
    + (349862581323694080 : R) * (h ^ 48) * (a7 ^ 7) * (a6 ^ 3) * a4
    + (566335987525877760 : R) * (h ^ 48) * (a7 ^ 7) * (a6 ^ 2) * (a5 ^ 2)
    + (215620780032000000 : R) * (h ^ 48) * (a7 ^ 6) * (a6 ^ 4) * a5
    - (48178307090350080 : R) * (h ^ 46) * (a7 ^ 9) * a5 * b5
    - (121375524529373184 : R) * (h ^ 46) * (a7 ^ 9) * a4 * b6
    - (166849084555001856 : R) * (h ^ 46) * (a7 ^ 9) * a3 * b7
    - (190684668062859264 : R) * (h ^ 46) * (a7 ^ 9) * a2 * b8
    - (124551187377684480 : R) * (h ^ 46) * (a7 ^ 8) * (a6 ^ 2) * b5
    - (439521398017228800 : R) * (h ^ 46) * (a7 ^ 8) * a6 * a5 * b6
    - (674158205881810944 : R) * (h ^ 46) * (a7 ^ 8) * a6 * a4 * b7
    - (780512724391034880 : R) * (h ^ 46) * (a7 ^ 8) * a6 * a3 * b8
    - (169610180516904960 : R) * (h ^ 46) * (a7 ^ 8) * (a5 ^ 2) * b7
    - (361920916755578880 : R) * (h ^ 46) * (a7 ^ 8) * a5 * a4 * b8
    - (257640957644636160 : R) * (h ^ 46) * (a7 ^ 7) * (a6 ^ 3) * b6
    - (736477786209779712 : R) * (h ^ 46) * (a7 ^ 7) * (a6 ^ 2) * a5 * b7
    - (896004635498643456 : R) * (h ^ 46) * (a7 ^ 7) * (a6 ^ 2) * a4 * b8
    - (361884117475786752 : R) * (h ^ 46) * (a7 ^ 7) * a6 * (a5 ^ 2) * b8
    - (112026207507185664 : R) * (h ^ 46) * (a7 ^ 6) * (a6 ^ 4) * b7
    - (298368560554573824 : R) * (h ^ 46) * (a7 ^ 6) * (a6 ^ 3) * a5 * b8
    + (84523345772544000 : R) * (h ^ 40) * (a7 ^ 11) * a2
    + (228546976268943360 : R) * (h ^ 40) * (a7 ^ 10) * a6 * a3
    + (16524817213685760 : R) * (h ^ 40) * (a7 ^ 10) * a5 * a4
    + (23676547781099520 : R) * (h ^ 40) * (a7 ^ 9) * (a6 ^ 2) * a4
    - (118207624029143040 : R) * (h ^ 40) * (a7 ^ 9) * a6 * (a5 ^ 2)
    - (175407504556032000 : R) * (h ^ 40) * (a7 ^ 8) * (a6 ^ 3) * a5
    - (23102226432000000 : R) * (h ^ 40) * (a7 ^ 7) * (a6 ^ 5)
    + (25409830822871040 : R) * (h ^ 38) * (a7 ^ 10) * a6 * b5
    + (49657465641369600 : R) * (h ^ 38) * (a7 ^ 10) * a5 * b6
    + (77951655638728704 : R) * (h ^ 38) * (a7 ^ 10) * a4 * b7
    + (92130446892072960 : R) * (h ^ 38) * (a7 ^ 10) * a3 * b8
    + (122151328095928320 : R) * (h ^ 38) * (a7 ^ 9) * (a6 ^ 2) * b6
    + (261020166509297664 : R) * (h ^ 38) * (a7 ^ 9) * a6 * a5 * b7
    + (322651485307404288 : R) * (h ^ 38) * (a7 ^ 9) * a6 * a4 * b8
    + (79162150697828352 : R) * (h ^ 38) * (a7 ^ 9) * (a5 ^ 2) * b8
    + (146235737983942656 : R) * (h ^ 38) * (a7 ^ 8) * (a6 ^ 3) * b7
    + (327815541383233536 : R) * (h ^ 38) * (a7 ^ 8) * (a6 ^ 2) * a5 * b8
    + (47971803989016576 : R) * (h ^ 38) * (a7 ^ 7) * (a6 ^ 4) * b8
    - (30102774986833920 : R) * (h ^ 32) * (a7 ^ 12) * a3
    - (56529973715927040 : R) * (h ^ 32) * (a7 ^ 11) * a6 * a4
    - (1656192195624960 : R) * (h ^ 32) * (a7 ^ 11) * (a5 ^ 2)
    + (16196768806993920 : R) * (h ^ 32) * (a7 ^ 10) * (a6 ^ 2) * a5
    + (18351946633052160 : R) * (h ^ 32) * (a7 ^ 9) * (a6 ^ 4)
    - (1852800164167680 : R) * (h ^ 30) * (a7 ^ 12) * b5
    - (24551390592368640 : R) * (h ^ 30) * (a7 ^ 11) * a6 * b6
    - (29142064809639936 : R) * (h ^ 30) * (a7 ^ 11) * a5 * b7
    - (36939720793522176 : R) * (h ^ 30) * (a7 ^ 11) * a4 * b8
    - (68651634917376000 : R) * (h ^ 30) * (a7 ^ 10) * (a6 ^ 2) * b7
    - (115509776829382656 : R) * (h ^ 30) * (a7 ^ 10) * a6 * a5 * b8
    - (62222078664769536 : R) * (h ^ 30) * (a7 ^ 9) * (a6 ^ 3) * b8
    + (8958584373903360 : R) * (h ^ 24) * (a7 ^ 13) * a4
    + (14325566676664320 : R) * (h ^ 24) * (a7 ^ 12) * a6 * a5
    + (1010946209218560 : R) * (h ^ 24) * (a7 ^ 11) * (a6 ^ 3)
    + (1759389760880640 : R) * (h ^ 22) * (a7 ^ 13) * b6
    + (13623281373413376 : R) * (h ^ 22) * (a7 ^ 12) * a6 * b7
    + (12775037085941760 : R) * (h ^ 22) * (a7 ^ 12) * a5 * b8
    + (28965174912221184 : R) * (h ^ 22) * (a7 ^ 11) * (a6 ^ 2) * b8
    - (2578491569848320 : R) * (h ^ 16) * (a7 ^ 14) * a5
    - (4163860463616000 : R) * (h ^ 16) * (a7 ^ 13) * (a6 ^ 2)
    - (961416945893376 : R) * (h ^ 14) * (a7 ^ 14) * b7
    - (5684124252635136 : R) * (h ^ 14) * (a7 ^ 13) * a6 * b8
    + (1147594947932160 : R) * (h ^ 8) * (a7 ^ 15) * a6
    + (395668377796608 : R) * (h ^ 6) * (a7 ^ 15) * b8
    - (91797307983360 : R) * (a7 ^ 17)

set_option maxHeartbeats 200000000 in
/-- Integer expansion of compact block `11` after the extra
`2^{34}` scale, on `λ = 0`. -/
def alignedSquareCompactBlock11Expansion810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    - (6890507429876858880 : R) * (h ^ 104) * (a6 ^ 2) * a3 * a0
    - (6890507429876858880 : R) * (h ^ 104) * (a6 ^ 2) * a2 * a1
    + (324259173170675712 : R) * (h ^ 102) * (a6 ^ 2) * a4 * b1
    + (648518346341351424 : R) * (h ^ 102) * (a6 ^ 2) * a3 * b2
    + (972777519512027136 : R) * (h ^ 102) * (a6 ^ 2) * a2 * b3
    + (1297036692682702848 : R) * (h ^ 102) * (a6 ^ 2) * a1 * b4
    + (1621295865853378560 : R) * (h ^ 102) * (a6 ^ 2) * a0 * b5
    + (6029194001142251520 : R) * (h ^ 96) * (a7 ^ 2) * a6 * a3 * a0
    + (6029194001142251520 : R) * (h ^ 96) * (a7 ^ 2) * a6 * a2 * a1
    + (3445253714938429440 : R) * (h ^ 96) * a7 * (a6 ^ 2) * a4 * a0
    + (3445253714938429440 : R) * (h ^ 96) * a7 * (a6 ^ 2) * a3 * a1
    + (1722626857469214720 : R) * (h ^ 96) * a7 * (a6 ^ 2) * (a2 ^ 2)
    - (283726776524341248 : R) * (h ^ 94) * (a7 ^ 2) * a6 * a4 * b1
    - (567453553048682496 : R) * (h ^ 94) * (a7 ^ 2) * a6 * a3 * b2
    - (851180329573023744 : R) * (h ^ 94) * (a7 ^ 2) * a6 * a2 * b3
    - (1134907106097364992 : R) * (h ^ 94) * (a7 ^ 2) * a6 * a1 * b4
    - (1418633882621706240 : R) * (h ^ 94) * (a7 ^ 2) * a6 * a0 * b5
    - (202661983231672320 : R) * (h ^ 94) * a7 * (a6 ^ 2) * a5 * b1
    - (405323966463344640 : R) * (h ^ 94) * a7 * (a6 ^ 2) * a4 * b2
    - (607985949695016960 : R) * (h ^ 94) * a7 * (a6 ^ 2) * a3 * b3
    - (810647932926689280 : R) * (h ^ 94) * a7 * (a6 ^ 2) * a2 * b4
    - (1013309916158361600 : R) * (h ^ 94) * a7 * (a6 ^ 2) * a1 * b5
    - (1215971899390033920 : R) * (h ^ 94) * a7 * (a6 ^ 2) * a0 * b6
    - (2411677600456900608 : R) * (h ^ 94) * (a6 ^ 2) * (a3 ^ 2) * b7
    - (5512405943901487104 : R) * (h ^ 94) * (a6 ^ 2) * a3 * a2 * b8
    - (1318886187749867520 : R) * (h ^ 88) * (a7 ^ 4) * a3 * a0
    - (1318886187749867520 : R) * (h ^ 88) * (a7 ^ 4) * a2 * a1
    - (3014597000571125760 : R) * (h ^ 88) * (a7 ^ 3) * a6 * a4 * a0
    - (3014597000571125760 : R) * (h ^ 88) * (a7 ^ 3) * a6 * a3 * a1
    - (1507298500285562880 : R) * (h ^ 88) * (a7 ^ 3) * a6 * (a2 ^ 2)
    - (1076641785918259200 : R) * (h ^ 88) * (a7 ^ 2) * (a6 ^ 2) * a5 * a0
    - (1076641785918259200 : R) * (h ^ 88) * (a7 ^ 2) * (a6 ^ 2) * a4 * a1
    + (2799268643387473920 : R) * (h ^ 88) * (a7 ^ 2) * (a6 ^ 2) * a3 * a2
    + (62065232364699648 : R) * (h ^ 86) * (a7 ^ 4) * a4 * b1
    + (124130464729399296 : R) * (h ^ 86) * (a7 ^ 4) * a3 * b2
    + (186195697094098944 : R) * (h ^ 86) * (a7 ^ 4) * a2 * b3
    + (248260929458798592 : R) * (h ^ 86) * (a7 ^ 4) * a1 * b4
    + (310326161823498240 : R) * (h ^ 86) * (a7 ^ 4) * a0 * b5
    + (177329235327713280 : R) * (h ^ 86) * (a7 ^ 3) * a6 * a5 * b1
    + (354658470655426560 : R) * (h ^ 86) * (a7 ^ 3) * a6 * a4 * b2
    + (531987705983139840 : R) * (h ^ 86) * (a7 ^ 3) * a6 * a3 * b3
    + (709316941310853120 : R) * (h ^ 86) * (a7 ^ 3) * a6 * a2 * b4
    + (886646176638566400 : R) * (h ^ 86) * (a7 ^ 3) * a6 * a1 * b5
    + (1063975411966279680 : R) * (h ^ 86) * (a7 ^ 3) * a6 * a0 * b6
    + (75998243711877120 : R) * (h ^ 86) * (a7 ^ 2) * (a6 ^ 3) * b1
    + (151996487423754240 : R) * (h ^ 86) * (a7 ^ 2) * (a6 ^ 2) * a5 * b2
    + (227994731135631360 : R) * (h ^ 86) * (a7 ^ 2) * (a6 ^ 2) * a4 * b3
    + (303992974847508480 : R) * (h ^ 86) * (a7 ^ 2) * (a6 ^ 2) * a3 * b4
    + (379991218559385600 : R) * (h ^ 86) * (a7 ^ 2) * (a6 ^ 2) * a2 * b5
    + (455989462271262720 : R) * (h ^ 86) * (a7 ^ 2) * (a6 ^ 2) * a1 * b6
    + (531987705983139840 : R) * (h ^ 86) * (a7 ^ 2) * (a6 ^ 2) * a0 * b7
    + (2110217900399788032 : R) * (h ^ 86) * (a7 ^ 2) * a6 * (a3 ^ 2) * b7
    + (4823355200913801216 : R) * (h ^ 86) * (a7 ^ 2) * a6 * a3 * a2 * b8
    + (2411677600456900608 : R) * (h ^ 86) * a7 * (a6 ^ 2) * a4 * a3 * b7
    + (2756202971950743552 : R) * (h ^ 86) * a7 * (a6 ^ 2) * a4 * a2 * b8
    + (4478829829419958272 : R) * (h ^ 86) * a7 * (a6 ^ 2) * (a3 ^ 2) * b8
    + (659443093874933760 : R) * (h ^ 80) * (a7 ^ 5) * a4 * a0
    + (659443093874933760 : R) * (h ^ 80) * (a7 ^ 5) * a3 * a1
    + (329721546937466880 : R) * (h ^ 80) * (a7 ^ 5) * (a2 ^ 2)
    + (942061562678476800 : R) * (h ^ 80) * (a7 ^ 4) * a6 * a5 * a0
    + (942061562678476800 : R) * (h ^ 80) * (a7 ^ 4) * a6 * a4 * a1
    - (2449360062964039680 : R) * (h ^ 80) * (a7 ^ 4) * a6 * a3 * a2
    + (269160446479564800 : R) * (h ^ 80) * (a7 ^ 3) * (a6 ^ 3) * a0
    + (269160446479564800 : R) * (h ^ 80) * (a7 ^ 3) * (a6 ^ 2) * a5 * a1
    - (1668794768173301760 : R) * (h ^ 80) * (a7 ^ 3) * (a6 ^ 2) * a4 * a2
    - (2449360062964039680 : R) * (h ^ 80) * (a7 ^ 3) * (a6 ^ 2) * (a3 ^ 2)
    - (38790770227937280 : R) * (h ^ 78) * (a7 ^ 5) * a5 * b1
    - (77581540455874560 : R) * (h ^ 78) * (a7 ^ 5) * a4 * b2
    - (116372310683811840 : R) * (h ^ 78) * (a7 ^ 5) * a3 * b3
    - (155163080911749120 : R) * (h ^ 78) * (a7 ^ 5) * a2 * b4
    - (193953851139686400 : R) * (h ^ 78) * (a7 ^ 5) * a1 * b5
    - (232744621367623680 : R) * (h ^ 78) * (a7 ^ 5) * a0 * b6
    - (83123079059865600 : R) * (h ^ 78) * (a7 ^ 4) * (a6 ^ 2) * b1
    - (132996926495784960 : R) * (h ^ 78) * (a7 ^ 4) * a6 * a5 * b2
    - (199495389743677440 : R) * (h ^ 78) * (a7 ^ 4) * a6 * a4 * b3
    - (265993852991569920 : R) * (h ^ 78) * (a7 ^ 4) * a6 * a3 * b4
    - (332492316239462400 : R) * (h ^ 78) * (a7 ^ 4) * a6 * a2 * b5
    - (398990779487354880 : R) * (h ^ 78) * (a7 ^ 4) * a6 * a1 * b6
    - (465489242735247360 : R) * (h ^ 78) * (a7 ^ 4) * a6 * a0 * b7
    - (461610165712453632 : R) * (h ^ 78) * (a7 ^ 4) * (a3 ^ 2) * b7
    - (1055108950199894016 : R) * (h ^ 78) * (a7 ^ 4) * a3 * a2 * b8
    - (44332308831928320 : R) * (h ^ 78) * (a7 ^ 3) * (a6 ^ 3) * b2
    - (66498463247892480 : R) * (h ^ 78) * (a7 ^ 3) * (a6 ^ 2) * a5 * b3
    - (88664617663856640 : R) * (h ^ 78) * (a7 ^ 3) * (a6 ^ 2) * a4 * b4
    - (110830772079820800 : R) * (h ^ 78) * (a7 ^ 3) * (a6 ^ 2) * a3 * b5
    - (132996926495784960 : R) * (h ^ 78) * (a7 ^ 3) * (a6 ^ 2) * a2 * b6
    - (155163080911749120 : R) * (h ^ 78) * (a7 ^ 3) * (a6 ^ 2) * a1 * b7
    - (177329235327713280 : R) * (h ^ 78) * (a7 ^ 3) * (a6 ^ 2) * a0 * b8
    - (2110217900399788032 : R) * (h ^ 78) * (a7 ^ 3) * a6 * a4 * a3 * b7
    - (2411677600456900608 : R) * (h ^ 78) * (a7 ^ 3) * a6 * a4 * a2 * b8
    - (3918976100742463488 : R) * (h ^ 78) * (a7 ^ 3) * a6 * (a3 ^ 2) * b8
    - (753649250142781440 : R) * (h ^ 78) * (a7 ^ 2) * (a6 ^ 2) * a5 * a3 * b7
    - (861313428734607360 : R) * (h ^ 78) * (a7 ^ 2) * (a6 ^ 2) * a5 * a2 * b8
    - (602919400114225152 : R) * (h ^ 78) * (a7 ^ 2) * (a6 ^ 2) * (a4 ^ 2) * b7
    - (3962041772179193856 : R) * (h ^ 78) * (a7 ^ 2) * (a6 ^ 2) * a4 * a3 * b8
    - (206075966835916800 : R) * (h ^ 72) * (a7 ^ 6) * a5 * a0
    - (206075966835916800 : R) * (h ^ 72) * (a7 ^ 6) * a4 * a1
    + (535797513773383680 : R) * (h ^ 72) * (a7 ^ 6) * a3 * a2
    - (232744621367623680 : R) * (h ^ 72) * (a7 ^ 5) * (a6 ^ 2) * a0
    - (235515390669619200 : R) * (h ^ 72) * (a7 ^ 5) * a6 * a5 * a1
    + (1460195422151639040 : R) * (h ^ 72) * (a7 ^ 5) * a6 * a4 * a2
    + (2143190055093534720 : R) * (h ^ 72) * (a7 ^ 5) * a6 * (a3 ^ 2)
    - (58878847667404800 : R) * (h ^ 72) * (a7 ^ 4) * (a6 ^ 3) * a1
    + (546732156911616000 : R) * (h ^ 72) * (a7 ^ 4) * (a6 ^ 2) * a5 * a2
    + (2161694835789004800 : R) * (h ^ 72) * (a7 ^ 4) * (a6 ^ 2) * a4 * a3
    + (29093077670952960 : R) * (h ^ 70) * (a7 ^ 6) * a6 * b1
    + (29093077670952960 : R) * (h ^ 70) * (a7 ^ 6) * a5 * b2
    + (43639616506429440 : R) * (h ^ 70) * (a7 ^ 6) * a4 * b3
    + (58186155341905920 : R) * (h ^ 70) * (a7 ^ 6) * a3 * b4
    + (72732694177382400 : R) * (h ^ 70) * (a7 ^ 6) * a2 * b5
    + (87279233012858880 : R) * (h ^ 70) * (a7 ^ 6) * a1 * b6
    + (101825771848335360 : R) * (h ^ 70) * (a7 ^ 6) * a0 * b7
    + (47380155064123392 : R) * (h ^ 70) * (a7 ^ 5) * (a6 ^ 2) * b2
    + (58186155341905920 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a5 * b3
    + (77581540455874560 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a4 * b4
    + (96976925569843200 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a3 * b5
    + (116372310683811840 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a2 * b6
    + (135767695797780480 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a1 * b7
    + (155163080911749120 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a0 * b8
    + (461610165712453632 : R) * (h ^ 70) * (a7 ^ 5) * a4 * a3 * b7
    + (527554475099947008 : R) * (h ^ 70) * (a7 ^ 5) * a4 * a2 * b8
    + (857276022037413888 : R) * (h ^ 70) * (a7 ^ 5) * (a3 ^ 2) * b8
    + (16624615811973120 : R) * (h ^ 70) * (a7 ^ 4) * (a6 ^ 3) * b3
    + (22166154415964160 : R) * (h ^ 70) * (a7 ^ 4) * (a6 ^ 2) * a5 * b4
    + (27707693019955200 : R) * (h ^ 70) * (a7 ^ 4) * (a6 ^ 2) * a4 * b5
    + (33249231623946240 : R) * (h ^ 70) * (a7 ^ 4) * (a6 ^ 2) * a3 * b6
    + (38790770227937280 : R) * (h ^ 70) * (a7 ^ 4) * (a6 ^ 2) * a2 * b7
    + (44332308831928320 : R) * (h ^ 70) * (a7 ^ 4) * (a6 ^ 2) * a1 * b8
    + (659443093874933760 : R) * (h ^ 70) * (a7 ^ 4) * a6 * a5 * a3 * b7
    + (753649250142781440 : R) * (h ^ 70) * (a7 ^ 4) * a6 * a5 * a2 * b8
    + (527554475099947008 : R) * (h ^ 70) * (a7 ^ 4) * a6 * (a4 ^ 2) * b7
    + (3466786550656794624 : R) * (h ^ 70) * (a7 ^ 4) * a6 * a4 * a3 * b8
    + (188412312535695360 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 3) * a3 * b7
    + (215328357183651840 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 3) * a2 * b8
    + (376824625071390720 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 2) * a5 * a4 * b7
    + (1184305964510085120 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 2) * a5 * a3 * b8
    + (861313428734607360 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 2) * (a4 ^ 2) * b8
    + (49094568569733120 : R) * (h ^ 64) * (a7 ^ 7) * a6 * a0
    + (51518991708979200 : R) * (h ^ 64) * (a7 ^ 7) * a5 * a1
    - (319417748595671040 : R) * (h ^ 64) * (a7 ^ 7) * a4 * a2
    - (468822824551710720 : R) * (h ^ 64) * (a7 ^ 7) * (a3 ^ 2)
    + (49657381084200960 : R) * (h ^ 64) * (a7 ^ 6) * (a6 ^ 2) * a1
    - (478390637297664000 : R) * (h ^ 64) * (a7 ^ 6) * a6 * a5 * a2
    - (1891482981315379200 : R) * (h ^ 64) * (a7 ^ 6) * a6 * a4 * a3
    - (139626981611274240 : R) * (h ^ 64) * (a7 ^ 5) * (a6 ^ 3) * a2
    - (644302818760458240 : R) * (h ^ 64) * (a7 ^ 5) * (a6 ^ 2) * a5 * a3
    - (458413885410508800 : R) * (h ^ 64) * (a7 ^ 5) * (a6 ^ 2) * (a4 ^ 2)
    - (3182055370260480 : R) * (h ^ 62) * (a7 ^ 8) * b1
    - (16001192719024128 : R) * (h ^ 62) * (a7 ^ 7) * a6 * b2
    - (12728221481041920 : R) * (h ^ 62) * (a7 ^ 7) * a5 * b3
    - (16970961974722560 : R) * (h ^ 62) * (a7 ^ 7) * a4 * b4
    - (21213702468403200 : R) * (h ^ 62) * (a7 ^ 7) * a3 * b5
    - (25456442962083840 : R) * (h ^ 62) * (a7 ^ 7) * a2 * b6
    - (29699183455764480 : R) * (h ^ 62) * (a7 ^ 7) * a1 * b7
    - (33941923949445120 : R) * (h ^ 62) * (a7 ^ 7) * a0 * b8
    - (17507798526984192 : R) * (h ^ 62) * (a7 ^ 6) * (a6 ^ 2) * b3
    - (19395385113968640 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a5 * b4
    - (24244231392460800 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a4 * b5
    - (29093077670952960 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a3 * b6
    - (33941923949445120 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a2 * b7
    - (38790770227937280 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a1 * b8
    - (144253176785141760 : R) * (h ^ 62) * (a7 ^ 6) * a5 * a3 * b7
    - (164860773468733440 : R) * (h ^ 62) * (a7 ^ 6) * a5 * a2 * b8
    - (115402541428113408 : R) * (h ^ 62) * (a7 ^ 6) * (a4 ^ 2) * b7
    - (758359557956173824 : R) * (h ^ 62) * (a7 ^ 6) * a4 * a3 * b8
    - (4987384743591936 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 3) * b4
    - (6234230929489920 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 2) * a5 * b5
    - (7481077115387904 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 2) * a4 * b6
    - (206560851463766016 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 2) * a3 * b7
    - (236069544530018304 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 2) * a2 * b8
    - (329721546937466880 : R) * (h ^ 62) * (a7 ^ 5) * a6 * a5 * a4 * b7
    - (1036267718946324480 : R) * (h ^ 62) * (a7 ^ 5) * a6 * a5 * a3 * b8
    - (753649250142781440 : R) * (h ^ 62) * (a7 ^ 5) * a6 * (a4 ^ 2) * b8
    - (94206156267847680 : R) * (h ^ 62) * (a7 ^ 4) * (a6 ^ 3) * a4 * b7
    - (289347479965532160 : R) * (h ^ 62) * (a7 ^ 4) * (a6 ^ 3) * a3 * b8
    - (58878847667404800 : R) * (h ^ 62) * (a7 ^ 4) * (a6 ^ 2) * (a5 ^ 2) * b7
    - (511404848311173120 : R) * (h ^ 62) * (a7 ^ 4) * (a6 ^ 2) * a5 * a4 * b8
    + (530342561710080 : R) * (h ^ 56) * (a7 ^ 9) * a0
    - (9640870139658240 : R) * (h ^ 56) * (a7 ^ 8) * a6 * a1
    + (104647951908864000 : R) * (h ^ 56) * (a7 ^ 8) * a5 * a2
    + (413761902162739200 : R) * (h ^ 56) * (a7 ^ 8) * a4 * a3
    + (149267465203875840 : R) * (h ^ 56) * (a7 ^ 7) * (a6 ^ 2) * a2
    + (563764966415400960 : R) * (h ^ 56) * (a7 ^ 7) * a6 * a5 * a3
    + (401112149734195200 : R) * (h ^ 56) * (a7 ^ 7) * a6 * (a4 ^ 2)
    + (157080354312683520 : R) * (h ^ 56) * (a7 ^ 6) * (a6 ^ 3) * a3
    + (269055305680158720 : R) * (h ^ 56) * (a7 ^ 6) * (a6 ^ 2) * a5 * a4
    + (1644061941301248 : R) * (h ^ 54) * (a7 ^ 9) * b2
    + (5773157600329728 : R) * (h ^ 54) * (a7 ^ 8) * a6 * b3
    + (4242740493680640 : R) * (h ^ 54) * (a7 ^ 8) * a5 * b4
    + (5303425617100800 : R) * (h ^ 54) * (a7 ^ 8) * a4 * b5
    + (6364110740520960 : R) * (h ^ 54) * (a7 ^ 8) * a3 * b6
    + (7424795863941120 : R) * (h ^ 54) * (a7 ^ 8) * a2 * b7
    + (8485480987361280 : R) * (h ^ 54) * (a7 ^ 8) * a1 * b8
    + (5198903292985344 : R) * (h ^ 54) * (a7 ^ 7) * (a6 ^ 2) * b4
    + (5454952063303680 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a5 * b5
    + (6545942475964416 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a4 * b6
    + (72550862441938944 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a3 * b7
    + (82915271362215936 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a2 * b8
    + (72126588392570880 : R) * (h ^ 54) * (a7 ^ 7) * a5 * a4 * b7
    + (226683563519508480 : R) * (h ^ 54) * (a7 ^ 7) * a5 * a3 * b8
    + (164860773468733440 : R) * (h ^ 54) * (a7 ^ 7) * (a4 ^ 2) * b8
    + (1298798110310400 : R) * (h ^ 54) * (a7 ^ 6) * (a6 ^ 3) * b5
    + (1558557732372480 : R) * (h ^ 54) * (a7 ^ 6) * (a6 ^ 2) * a5 * b6
    + (100734781435674624 : R) * (h ^ 54) * (a7 ^ 6) * (a6 ^ 2) * a4 * b7
    + (305304142463631360 : R) * (h ^ 54) * (a7 ^ 6) * (a6 ^ 2) * a3 * b8
    + (51518991708979200 : R) * (h ^ 54) * (a7 ^ 6) * a6 * (a5 ^ 2) * b7
    + (447479242272276480 : R) * (h ^ 54) * (a7 ^ 6) * a6 * a5 * a4 * b8
    + (29439423833702400 : R) * (h ^ 54) * (a7 ^ 5) * (a6 ^ 3) * a5 * b7
    + (124486706496798720 : R) * (h ^ 54) * (a7 ^ 5) * (a6 ^ 3) * a4 * b8
    + (75701375572377600 : R) * (h ^ 54) * (a7 ^ 5) * (a6 ^ 2) * (a5 ^ 2) * b8
    - (356323908648960 : R) * (h ^ 48) * (a7 ^ 10) * a1
    - (50432601206292480 : R) * (h ^ 48) * (a7 ^ 9) * a6 * a2
    - (123323586403368960 : R) * (h ^ 48) * (a7 ^ 9) * a5 * a3
    - (87743282754355200 : R) * (h ^ 48) * (a7 ^ 9) * (a4 ^ 2)
    - (165058613084160000 : R) * (h ^ 48) * (a7 ^ 8) * (a6 ^ 2) * a3
    - (235423392470138880 : R) * (h ^ 48) * (a7 ^ 8) * a6 * a5 * a4
    - (65055869632512000 : R) * (h ^ 48) * (a7 ^ 7) * (a6 ^ 3) * a4
    - (39230660778393600 : R) * (h ^ 48) * (a7 ^ 7) * (a6 ^ 2) * (a5 ^ 2)
    - (566803612827648 : R) * (h ^ 46) * (a7 ^ 10) * b3
    - (1685190548127744 : R) * (h ^ 46) * (a7 ^ 9) * a6 * b4
    - (1193270763847680 : R) * (h ^ 46) * (a7 ^ 9) * a5 * b5
    - (1431924916617216 : R) * (h ^ 46) * (a7 ^ 9) * a4 * b6
    - (7981655553736704 : R) * (h ^ 46) * (a7 ^ 9) * a3 * b7
    - (9121892061413376 : R) * (h ^ 46) * (a7 ^ 9) * a2 * b8
    - (1343734205644800 : R) * (h ^ 46) * (a7 ^ 8) * (a6 ^ 2) * b5
    - (1363738015825920 : R) * (h ^ 46) * (a7 ^ 8) * a6 * a5 * b6
    - (34047992461787136 : R) * (h ^ 46) * (a7 ^ 8) * a6 * a4 * b7
    - (100992376394219520 : R) * (h ^ 46) * (a7 ^ 8) * a6 * a3 * b8
    - (11269779436339200 : R) * (h ^ 46) * (a7 ^ 8) * (a5 ^ 2) * b7
    - (97886084247060480 : R) * (h ^ 46) * (a7 ^ 8) * a5 * a4 * b8
    - (306145268858880 : R) * (h ^ 46) * (a7 ^ 7) * (a6 ^ 3) * b6
    - (31268564505722880 : R) * (h ^ 46) * (a7 ^ 7) * (a6 ^ 2) * a5 * b7
    - (130824841275113472 : R) * (h ^ 46) * (a7 ^ 7) * (a6 ^ 2) * a4 * b8
    - (66238703625830400 : R) * (h ^ 46) * (a7 ^ 7) * a6 * (a5 ^ 2) * b8
    - (3679927979212800 : R) * (h ^ 46) * (a7 ^ 6) * (a6 ^ 4) * b7
    - (36799279792128000 : R) * (h ^ 46) * (a7 ^ 6) * (a6 ^ 3) * a5 * b8
    + (5185933431275520 : R) * (h ^ 40) * (a7 ^ 11) * a2
    + (54227801745653760 : R) * (h ^ 40) * (a7 ^ 10) * a6 * a3
    + (51498867102842880 : R) * (h ^ 40) * (a7 ^ 10) * a5 * a4
    + (68204549080350720 : R) * (h ^ 40) * (a7 ^ 9) * (a6 ^ 2) * a4
    + (34326828181094400 : R) * (h ^ 40) * (a7 ^ 9) * a6 * (a5 ^ 2)
    + (18906862111948800 : R) * (h ^ 40) * (a7 ^ 8) * (a6 ^ 3) * a5
    + (159813048729600 : R) * (h ^ 38) * (a7 ^ 11) * b4
    + (429973202534400 : R) * (h ^ 38) * (a7 ^ 10) * a6 * b5
    + (298317690961920 : R) * (h ^ 38) * (a7 ^ 10) * a5 * b6
    + (3503575548297216 : R) * (h ^ 38) * (a7 ^ 10) * a4 * b7
    + (9977069442170880 : R) * (h ^ 38) * (a7 ^ 10) * a3 * b8
    + (314915055206400 : R) * (h ^ 38) * (a7 ^ 9) * (a6 ^ 2) * b6
    + (10455324787998720 : R) * (h ^ 38) * (a7 ^ 9) * a6 * a5 * b7
    + (42989135119515648 : R) * (h ^ 38) * (a7 ^ 9) * a6 * a4 * b8
    + (14489716418150400 : R) * (h ^ 38) * (a7 ^ 9) * (a5 ^ 2) * b8
    + (4574881052098560 : R) * (h ^ 38) * (a7 ^ 8) * (a6 ^ 3) * b7
    + (38623781899468800 : R) * (h ^ 38) * (a7 ^ 8) * (a6 ^ 2) * a5 * b8
    + (4468483974758400 : R) * (h ^ 38) * (a7 ^ 7) * (a6 ^ 4) * b8
    - (5285358788935680 : R) * (h ^ 32) * (a7 ^ 12) * a3
    - (22322680304762880 : R) * (h ^ 32) * (a7 ^ 11) * a6 * a4
    - (7508993664614400 : R) * (h ^ 32) * (a7 ^ 11) * (a5 ^ 2)
    - (19806329178685440 : R) * (h ^ 32) * (a7 ^ 10) * (a6 ^ 2) * a5
    - (2273772463718400 : R) * (h ^ 32) * (a7 ^ 9) * (a6 ^ 4)
    - (39675808972800 : R) * (h ^ 30) * (a7 ^ 12) * b5
    - (99756319703040 : R) * (h ^ 30) * (a7 ^ 11) * a6 * b6
    - (1054470171525120 : R) * (h ^ 30) * (a7 ^ 11) * a5 * b7
    - (4191600318087168 : R) * (h ^ 30) * (a7 ^ 11) * a4 * b8
    - (2012610702606336 : R) * (h ^ 30) * (a7 ^ 10) * (a6 ^ 2) * b7
    - (12664972718899200 : R) * (h ^ 30) * (a7 ^ 10) * a6 * a5 * b8
    - (5464712376483840 : R) * (h ^ 30) * (a7 ^ 9) * (a6 ^ 3) * b8
    + (2159189431418880 : R) * (h ^ 24) * (a7 ^ 13) * a4
    + (6473863303004160 : R) * (h ^ 24) * (a7 ^ 12) * a6 * a5
    + (2772518389678080 : R) * (h ^ 24) * (a7 ^ 11) * (a6 ^ 3)
    + (9003356651520 : R) * (h ^ 22) * (a7 ^ 13) * b6
    + (366684011495424 : R) * (h ^ 22) * (a7 ^ 12) * a6 * b7
    + (1229672624947200 : R) * (h ^ 22) * (a7 ^ 12) * a5 * b8
    + (2350564566368256 : R) * (h ^ 22) * (a7 ^ 11) * (a6 ^ 2) * b8
    - (624525065256960 : R) * (h ^ 16) * (a7 ^ 14) * a5
    - (1187595359354880 : R) * (h ^ 16) * (a7 ^ 13) * (a6 ^ 2)
    - (23480460509184 : R) * (h ^ 14) * (a7 ^ 14) * b7
    - (415571267026944 : R) * (h ^ 14) * (a7 ^ 13) * a6 * b8
    + (208738851471360 : R) * (h ^ 8) * (a7 ^ 15) * a6
    + (25807021277184 : R) * (h ^ 6) * (a7 ^ 15) * b8
    - (12878683453440 : R) * (a7 ^ 17)

set_option maxHeartbeats 200000000 in
/-- Integer expansion of compact block `12` after the extra
`2^{34}` scale, on `λ = 0`. -/
def alignedSquareCompactBlock12Expansion810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    (7177611906121728000 : R) * (h ^ 96) * a6 * (a5 ^ 3) * a2
    + (21532835718365184000 : R) * (h ^ 96) * a6 * (a5 ^ 2) * a4 * a3
    - (918734323983581184 : R) * (h ^ 94) * a6 * (a5 ^ 3) * b4
    - (3445253714938429440 : R) * (h ^ 94) * a6 * (a5 ^ 2) * a4 * b5
    - (4134304457926115328 : R) * (h ^ 94) * a6 * (a5 ^ 2) * a3 * b6
    - (4823355200913801216 : R) * (h ^ 94) * a6 * (a5 ^ 2) * a2 * b7
    - (3140205208928256000 : R) * (h ^ 88) * (a7 ^ 2) * (a5 ^ 3) * a2
    - (9420615626784768000 : R) * (h ^ 88) * (a7 ^ 2) * (a5 ^ 2) * a4 * a3
    - (16149626788773888000 : R) * (h ^ 88) * a7 * (a6 ^ 2) * (a5 ^ 2) * a2
    - (32299253577547776000 : R) * (h ^ 88) * a7 * (a6 ^ 2) * a5 * a4 * a3
    - (16149626788773888000 : R) * (h ^ 88) * a7 * a6 * (a5 ^ 3) * a3
    - (10766417859182592000 : R) * (h ^ 88) * a7 * a6 * (a5 ^ 2) * (a4 ^ 2)
    - (1480382455637606400 : R) * (h ^ 88) * a6 * (a5 ^ 5)
    + (401946266742816768 : R) * (h ^ 86) * (a7 ^ 2) * (a5 ^ 3) * b4
    + (1507298500285562880 : R) * (h ^ 86) * (a7 ^ 2) * (a5 ^ 2) * a4 * b5
    + (1808758200342675456 : R) * (h ^ 86) * (a7 ^ 2) * (a5 ^ 2) * a3 * b6
    + (2110217900399788032 : R) * (h ^ 86) * (a7 ^ 2) * (a5 ^ 2) * a2 * b7
    + (2067152228963057664 : R) * (h ^ 86) * a7 * (a6 ^ 2) * (a5 ^ 2) * b4
    + (5167880572407644160 : R) * (h ^ 86) * a7 * (a6 ^ 2) * a5 * a4 * b5
    + (6201456686889172992 : R) * (h ^ 86) * a7 * (a6 ^ 2) * a5 * a3 * b6
    + (7235032801370701824 : R) * (h ^ 86) * a7 * (a6 ^ 2) * a5 * a2 * b7
    + (2727492524326256640 : R) * (h ^ 86) * a7 * a6 * (a5 ^ 3) * b5
    + (4651092515166879744 : R) * (h ^ 86) * a7 * a6 * (a5 ^ 2) * a4 * b6
    + (5426274601028026368 : R) * (h ^ 86) * a7 * a6 * (a5 ^ 2) * a3 * b7
    + (4823355200913801216 : R) * (h ^ 86) * a7 * a6 * (a5 ^ 2) * a2 * b8
    + (1256082083571302400 : R) * (h ^ 86) * a6 * (a5 ^ 4) * b7
    + (5742089524897382400 : R) * (h ^ 86) * a6 * (a5 ^ 3) * a4 * b8
    + (9514821783052615680 : R) * (h ^ 80) * (a7 ^ 3) * a6 * (a5 ^ 2) * a2
    + (23551539066961920000 : R) * (h ^ 80) * (a7 ^ 3) * a6 * a5 * a4 * a3
    + (7065461720088576000 : R) * (h ^ 80) * (a7 ^ 3) * (a5 ^ 3) * a3
    + (4710307813392384000 : R) * (h ^ 80) * (a7 ^ 3) * (a5 ^ 2) * (a4 ^ 2)
    + (12112220091580416000 : R) * (h ^ 80) * (a7 ^ 2) * (a6 ^ 3) * a5 * a2
    + (12112220091580416000 : R) * (h ^ 80) * (a7 ^ 2) * (a6 ^ 3) * a4 * a3
    + (31289901903249408000 : R) * (h ^ 80) * (a7 ^ 2) * (a6 ^ 2) * (a5 ^ 2) * a3
    + (16149626788773888000 : R) * (h ^ 80) * (a7 ^ 2) * (a6 ^ 2) * a5 * (a4 ^ 2)
    + (6729011161989120000 : R) * (h ^ 80) * (a7 ^ 2) * a6 * (a5 ^ 3) * a4
    + (647667324341452800 : R) * (h ^ 80) * (a7 ^ 2) * (a5 ^ 5)
    + (5551434208641024000 : R) * (h ^ 80) * a7 * (a6 ^ 2) * (a5 ^ 4)
    - (1507298500285562880 : R) * (h ^ 78) * (a7 ^ 3) * a6 * (a5 ^ 2) * b4
    - (3768246250713907200 : R) * (h ^ 78) * (a7 ^ 3) * a6 * a5 * a4 * b5
    - (4521895500856688640 : R) * (h ^ 78) * (a7 ^ 3) * a6 * a5 * a3 * b6
    - (5275544750999470080 : R) * (h ^ 78) * (a7 ^ 3) * a6 * a5 * a2 * b7
    - (1193277979392737280 : R) * (h ^ 78) * (a7 ^ 3) * (a5 ^ 3) * b5
    - (2034852975385509888 : R) * (h ^ 78) * (a7 ^ 3) * (a5 ^ 2) * a4 * b6
    - (2373995137949761536 : R) * (h ^ 78) * (a7 ^ 3) * (a5 ^ 2) * a3 * b7
    - (2110217900399788032 : R) * (h ^ 78) * (a7 ^ 3) * (a5 ^ 2) * a2 * b8
    - (1550364171722293248 : R) * (h ^ 78) * (a7 ^ 2) * (a6 ^ 3) * a5 * b4
    - (1937955214652866560 : R) * (h ^ 78) * (a7 ^ 2) * (a6 ^ 3) * a4 * b5
    - (2325546257583439872 : R) * (h ^ 78) * (a7 ^ 2) * (a6 ^ 3) * a3 * b6
    - (2713137300514013184 : R) * (h ^ 78) * (a7 ^ 2) * (a6 ^ 3) * a2 * b7
    - (5329376840295383040 : R) * (h ^ 78) * (a7 ^ 2) * (a6 ^ 2) * (a5 ^ 2) * b5
    - (6976638772750319616 : R) * (h ^ 78) * (a7 ^ 2) * (a6 ^ 2) * a5 * a4 * b6
    - (8139411901542039552 : R) * (h ^ 78) * (a7 ^ 2) * (a6 ^ 2) * a5 * a3 * b7
    - (7235032801370701824 : R) * (h ^ 78) * (a7 ^ 2) * (a6 ^ 2) * a5 * a2 * b8
    - (2476276107611996160 : R) * (h ^ 78) * (a7 ^ 2) * a6 * (a5 ^ 3) * b6
    - (3391421625642516480 : R) * (h ^ 78) * (a7 ^ 2) * a6 * (a5 ^ 2) * a4 * b7
    - (3617516400685350912 : R) * (h ^ 78) * (a7 ^ 2) * a6 * (a5 ^ 2) * a3 * b8
    - (549535911562444800 : R) * (h ^ 78) * (a7 ^ 2) * (a5 ^ 4) * b7
    - (2512164167142604800 : R) * (h ^ 78) * (a7 ^ 2) * (a5 ^ 3) * a4 * b8
    - (3768246250713907200 : R) * (h ^ 78) * a7 * (a6 ^ 2) * (a5 ^ 3) * b7
    - (12919701431019110400 : R) * (h ^ 78) * a7 * (a6 ^ 2) * (a5 ^ 2) * a4 * b8
    - (4844888036632166400 : R) * (h ^ 78) * a7 * a6 * (a5 ^ 4) * b8
    - (1071595027546767360 : R) * (h ^ 72) * (a7 ^ 5) * (a5 ^ 2) * a2
    - (4121519336718336000 : R) * (h ^ 72) * (a7 ^ 5) * a5 * a4 * a3
    - (8973136384512491520 : R) * (h ^ 72) * (a7 ^ 4) * (a6 ^ 2) * a5 * a2
    - (12364558010155008000 : R) * (h ^ 72) * (a7 ^ 4) * (a6 ^ 2) * a4 * a3
    - (20963813711979479040 : R) * (h ^ 72) * (a7 ^ 4) * a6 * (a5 ^ 2) * a3
    - (11775769533480960000 : R) * (h ^ 72) * (a7 ^ 4) * a6 * a5 * (a4 ^ 2)
    - (2943942383370240000 : R) * (h ^ 72) * (a7 ^ 4) * (a5 ^ 3) * a4
    - (3028055022895104000 : R) * (h ^ 72) * (a7 ^ 3) * (a6 ^ 4) * a2
    - (19682357648818176000 : R) * (h ^ 72) * (a7 ^ 3) * (a6 ^ 3) * a5 * a3
    - (6056110045790208000 : R) * (h ^ 72) * (a7 ^ 3) * (a6 ^ 3) * (a4 ^ 2)
    - (10934643138232320000 : R) * (h ^ 72) * (a7 ^ 3) * (a6 ^ 2) * (a5 ^ 2) * a4
    - (3178756835377152000 : R) * (h ^ 72) * (a7 ^ 3) * a6 * (a5 ^ 4)
    - (8327151312961536000 : R) * (h ^ 72) * (a7 ^ 2) * (a6 ^ 3) * (a5 ^ 3)
    + (263777237549973504 : R) * (h ^ 70) * (a7 ^ 5) * (a5 ^ 2) * b4
    + (659443093874933760 : R) * (h ^ 70) * (a7 ^ 5) * a5 * a4 * b5
    + (791331712649920512 : R) * (h ^ 70) * (a7 ^ 5) * a5 * a3 * b6
    + (923220331424907264 : R) * (h ^ 70) * (a7 ^ 5) * a5 * a2 * b7
    + (1582663425299841024 : R) * (h ^ 70) * (a7 ^ 4) * (a6 ^ 2) * a5 * b4
    + (1978329281624801280 : R) * (h ^ 70) * (a7 ^ 4) * (a6 ^ 2) * a4 * b5
    + (2373995137949761536 : R) * (h ^ 70) * (a7 ^ 4) * (a6 ^ 2) * a3 * b6
    + (2769660994274721792 : R) * (h ^ 70) * (a7 ^ 4) * (a6 ^ 2) * a2 * b7
    + (3827125098381312000 : R) * (h ^ 70) * (a7 ^ 4) * a6 * (a5 ^ 2) * b5
    + (5087132438463774720 : R) * (h ^ 70) * (a7 ^ 4) * a6 * a5 * a4 * b6
    + (5934987844874403840 : R) * (h ^ 70) * (a7 ^ 4) * a6 * a5 * a3 * b7
    + (5275544750999470080 : R) * (h ^ 70) * (a7 ^ 4) * a6 * a5 * a2 * b8
    + (1083370797080248320 : R) * (h ^ 70) * (a7 ^ 4) * (a5 ^ 3) * b6
    + (1483746961218600960 : R) * (h ^ 70) * (a7 ^ 4) * (a5 ^ 2) * a4 * b7
    + (1582663425299841024 : R) * (h ^ 70) * (a7 ^ 4) * (a5 ^ 2) * a3 * b8
    + (387591042930573312 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 4) * b4
    + (3391421625642516480 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 3) * a5 * b5
    + (2616239539781369856 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 3) * a4 * b6
    + (3052279463078264832 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 3) * a3 * b7
    + (2713137300514013184 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 3) * a2 * b8
    + (4643017701772492800 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 2) * (a5 ^ 2) * b6
    + (5087132438463774720 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 2) * a5 * a4 * b7
    + (5426274601028026368 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 2) * a5 * a3 * b8
    + (4176472927874580480 : R) * (h ^ 70) * (a7 ^ 3) * a6 * (a5 ^ 3) * b7
    + (11154008902113165312 : R) * (h ^ 70) * (a7 ^ 3) * a6 * (a5 ^ 2) * a4 * b8
    + (2119638516026572800 : R) * (h ^ 70) * (a7 ^ 3) * (a5 ^ 4) * b8
    + (4239277032053145600 : R) * (h ^ 70) * (a7 ^ 2) * (a6 ^ 3) * (a5 ^ 2) * b7
    + (9689776073264332800 : R) * (h ^ 70) * (a7 ^ 2) * (a6 ^ 3) * a5 * a4 * b8
    + (13188861877498675200 : R) * (h ^ 70) * (a7 ^ 2) * (a6 ^ 2) * (a5 ^ 3) * b8
    + (1648607734687334400 : R) * (h ^ 64) * (a7 ^ 6) * a6 * a5 * a2
    + (4121519336718336000 : R) * (h ^ 64) * (a7 ^ 6) * a6 * a4 * a3
    + (3182585712822190080 : R) * (h ^ 64) * (a7 ^ 6) * (a5 ^ 2) * a3
    + (2060759668359168000 : R) * (h ^ 64) * (a7 ^ 6) * a5 * (a4 ^ 2)
    + (2702539107933880320 : R) * (h ^ 64) * (a7 ^ 5) * (a6 ^ 3) * a2
    + (17314797127792066560 : R) * (h ^ 64) * (a7 ^ 5) * (a6 ^ 2) * a5 * a3
    + (6182279005077504000 : R) * (h ^ 64) * (a7 ^ 5) * (a6 ^ 2) * (a4 ^ 2)
    + (7055157921746780160 : R) * (h ^ 64) * (a7 ^ 5) * a6 * (a5 ^ 2) * a4
    + (328126911479808000 : R) * (h ^ 64) * (a7 ^ 5) * (a5 ^ 4)
    + (3974322217549824000 : R) * (h ^ 64) * (a7 ^ 4) * (a6 ^ 4) * a3
    + (5046758371491840000 : R) * (h ^ 64) * (a7 ^ 4) * (a6 ^ 3) * a5 * a4
    + (4920589412204544000 : R) * (h ^ 64) * (a7 ^ 4) * (a6 ^ 2) * (a5 ^ 3)
    + (6245363484721152000 : R) * (h ^ 64) * (a7 ^ 3) * (a6 ^ 4) * (a5 ^ 2)
    - (527554475099947008 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a5 * b4
    - (659443093874933760 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a4 * b5
    - (791331712649920512 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a3 * b6
    - (923220331424907264 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a2 * b7
    - (654291194704035840 : R) * (h ^ 62) * (a7 ^ 6) * (a5 ^ 2) * b5
    - (890248176731160576 : R) * (h ^ 62) * (a7 ^ 6) * a5 * a4 * b6
    - (1038622872853020672 : R) * (h ^ 62) * (a7 ^ 6) * a5 * a3 * b7
    - (923220331424907264 : R) * (h ^ 62) * (a7 ^ 6) * a5 * a2 * b8
    - (508713243846377472 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 3) * b4
    - (3373757971342295040 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 2) * a5 * b5
    - (2670744530193481728 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 2) * a4 * b6
    - (3115868618559062016 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 2) * a3 * b7
    - (2769660994274721792 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 2) * a2 * b8
    - (3322533373871652864 : R) * (h ^ 62) * (a7 ^ 5) * a6 * (a5 ^ 2) * b6
    - (3709367403046502400 : R) * (h ^ 62) * (a7 ^ 5) * a6 * a5 * a4 * b7
    - (3956658563249602560 : R) * (h ^ 62) * (a7 ^ 5) * a6 * a5 * a3 * b8
    - (1105941022019420160 : R) * (h ^ 62) * (a7 ^ 5) * (a5 ^ 3) * b7
    - (2406967292643508224 : R) * (h ^ 62) * (a7 ^ 5) * (a5 ^ 2) * a4 * b8
    - (696452655265873920 : R) * (h ^ 62) * (a7 ^ 4) * (a6 ^ 4) * b5
    - (2785810621063495680 : R) * (h ^ 62) * (a7 ^ 4) * (a6 ^ 3) * a5 * b6
    - (1907674664423915520 : R) * (h ^ 62) * (a7 ^ 4) * (a6 ^ 3) * a4 * b7
    - (2034852975385509888 : R) * (h ^ 62) * (a7 ^ 4) * (a6 ^ 3) * a3 * b8
    - (6941816139987025920 : R) * (h ^ 62) * (a7 ^ 4) * (a6 ^ 2) * (a5 ^ 2) * b7
    - (12491736321116602368 : R) * (h ^ 62) * (a7 ^ 4) * (a6 ^ 2) * a5 * a4 * b8
    - (10146788081349427200 : R) * (h ^ 62) * (a7 ^ 4) * a6 * (a5 ^ 3) * b8
    - (2119638516026572800 : R) * (h ^ 62) * (a7 ^ 3) * (a6 ^ 4) * a5 * b7
    - (2422444018316083200 : R) * (h ^ 62) * (a7 ^ 3) * (a6 ^ 4) * a4 * b8
    - (13323442100738457600 : R) * (h ^ 62) * (a7 ^ 3) * (a6 ^ 3) * (a5 ^ 2) * b8
    - (18031647098142720 : R) * (h ^ 56) * (a7 ^ 8) * a5 * a2
    - (450791177453568000 : R) * (h ^ 56) * (a7 ^ 8) * a4 * a3
    - (633683598020444160 : R) * (h ^ 56) * (a7 ^ 7) * (a6 ^ 2) * a2
    - (4672128560608051200 : R) * (h ^ 56) * (a7 ^ 7) * a6 * a5 * a3
    - (2060759668359168000 : R) * (h ^ 56) * (a7 ^ 7) * a6 * (a4 ^ 2)
    - (993672552586936320 : R) * (h ^ 56) * (a7 ^ 7) * (a5 ^ 2) * a4
    - (4174694296017960960 : R) * (h ^ 56) * (a7 ^ 6) * (a6 ^ 3) * a3
    - (3774870121076490240 : R) * (h ^ 56) * (a7 ^ 6) * (a6 ^ 2) * a5 * a4
    + (44005805418086400 : R) * (h ^ 56) * (a7 ^ 6) * a6 * (a5 ^ 3)
    - (473133597327360000 : R) * (h ^ 56) * (a7 ^ 5) * (a6 ^ 4) * a4
    - (3469646380400640000 : R) * (h ^ 56) * (a7 ^ 5) * (a6 ^ 3) * (a5 ^ 2)
    - (2342011306770432000 : R) * (h ^ 56) * (a7 ^ 4) * (a6 ^ 5) * a5
    + (57701270714056704 : R) * (h ^ 54) * (a7 ^ 8) * a5 * b4
    + (72126588392570880 : R) * (h ^ 54) * (a7 ^ 8) * a4 * b5
    + (86551906071085056 : R) * (h ^ 54) * (a7 ^ 8) * a3 * b6
    + (100977223749599232 : R) * (h ^ 54) * (a7 ^ 8) * a2 * b7
    + (247291160203100160 : R) * (h ^ 54) * (a7 ^ 7) * (a6 ^ 2) * b4
    + (1089626674644910080 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a5 * b5
    + (890248176731160576 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a4 * b6
    + (1038622872853020672 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a3 * b7
    + (923220331424907264 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a2 * b8
    + (564905744088956928 : R) * (h ^ 54) * (a7 ^ 7) * (a5 ^ 2) * b6
    + (649139295533137920 : R) * (h ^ 54) * (a7 ^ 7) * a5 * a4 * b7
    + (692415248568680448 : R) * (h ^ 54) * (a7 ^ 7) * a5 * a3 * b8
    + (880974758223544320 : R) * (h ^ 54) * (a7 ^ 6) * (a6 ^ 3) * b5
    + (2749347791829467136 : R) * (h ^ 54) * (a7 ^ 6) * (a6 ^ 2) * a5 * b6
    + (1947417886599413760 : R) * (h ^ 54) * (a7 ^ 6) * (a6 ^ 2) * a4 * b7
    + (2077245745706041344 : R) * (h ^ 54) * (a7 ^ 6) * (a6 ^ 2) * a3 * b8
    + (3310352812260458496 : R) * (h ^ 54) * (a7 ^ 6) * a6 * (a5 ^ 2) * b7
    + (5193114364265103360 : R) * (h ^ 54) * (a7 ^ 6) * a6 * a5 * a4 * b8
    + (1914789191850393600 : R) * (h ^ 54) * (a7 ^ 6) * (a5 ^ 3) * b8
    + (522339491449405440 : R) * (h ^ 54) * (a7 ^ 5) * (a6 ^ 4) * b6
    + (4292267994953809920 : R) * (h ^ 54) * (a7 ^ 5) * (a6 ^ 3) * a5 * b7
    + (4154491491412082688 : R) * (h ^ 54) * (a7 ^ 5) * (a6 ^ 3) * a4 * b8
    + (14510692007631912960 : R) * (h ^ 54) * (a7 ^ 5) * (a6 ^ 2) * (a5 ^ 2) * b8
    + (397432221754982400 : R) * (h ^ 54) * (a7 ^ 4) * (a6 ^ 5) * b7
    + (5904707294645452800 : R) * (h ^ 54) * (a7 ^ 4) * (a6 ^ 4) * a5 * b8
    - (19534284356321280 : R) * (h ^ 48) * (a7 ^ 9) * a6 * a2
    + (378101100089180160 : R) * (h ^ 48) * (a7 ^ 9) * a5 * a3
    + (225395588726784000 : R) * (h ^ 48) * (a7 ^ 9) * (a4 ^ 2)
    + (1472396683357716480 : R) * (h ^ 48) * (a7 ^ 8) * (a6 ^ 2) * a3
    + (713216041471180800 : R) * (h ^ 48) * (a7 ^ 8) * a6 * a5 * a4
    - (263766504426700800 : R) * (h ^ 48) * (a7 ^ 8) * (a5 ^ 3)
    + (104601952809123840 : R) * (h ^ 48) * (a7 ^ 7) * (a6 ^ 3) * a4
    - (1291079731956940800 : R) * (h ^ 48) * (a7 ^ 7) * (a6 ^ 2) * (a5 ^ 2)
    + (1240497150492672000 : R) * (h ^ 48) * (a7 ^ 6) * (a6 ^ 4) * a5
    + (351301696015564800 : R) * (h ^ 48) * (a7 ^ 5) * (a6 ^ 6)
    - (52892831487885312 : R) * (h ^ 46) * (a7 ^ 9) * a6 * b4
    - (114951750250659840 : R) * (h ^ 46) * (a7 ^ 9) * a5 * b5
    - (97370894329970688 : R) * (h ^ 46) * (a7 ^ 9) * a4 * b6
    - (113599376718299136 : R) * (h ^ 46) * (a7 ^ 9) * a3 * b7
    - (100977223749599232 : R) * (h ^ 46) * (a7 ^ 9) * a2 * b8
    - (410541965180928000 : R) * (h ^ 46) * (a7 ^ 8) * (a6 ^ 2) * b5
    - (879042796034457600 : R) * (h ^ 46) * (a7 ^ 8) * a6 * a5 * b6
    - (649139295533137920 : R) * (h ^ 46) * (a7 ^ 8) * a6 * a4 * b7
    - (692415248568680448 : R) * (h ^ 46) * (a7 ^ 8) * a6 * a3 * b8
    - (474570412064243712 : R) * (h ^ 46) * (a7 ^ 8) * (a5 ^ 2) * b7
    - (692415248568680448 : R) * (h ^ 46) * (a7 ^ 8) * a5 * a4 * b8
    - (650132876087525376 : R) * (h ^ 46) * (a7 ^ 7) * (a6 ^ 3) * b6
    - (2836506886017122304 : R) * (h ^ 46) * (a7 ^ 7) * (a6 ^ 2) * a5 * b7
    - (2540916671086854144 : R) * (h ^ 46) * (a7 ^ 7) * (a6 ^ 2) * a4 * b8
    - (5179719426420768768 : R) * (h ^ 46) * (a7 ^ 7) * a6 * (a5 ^ 2) * b8
    - (902502336901939200 : R) * (h ^ 46) * (a7 ^ 6) * (a6 ^ 4) * b7
    - (8220223119965552640 : R) * (h ^ 46) * (a7 ^ 6) * (a6 ^ 3) * a5 * b8
    - (965192538547814400 : R) * (h ^ 46) * (a7 ^ 5) * (a6 ^ 5) * b8
    + (14462883609968640 : R) * (h ^ 40) * (a7 ^ 11) * a2
    - (187923572100956160 : R) * (h ^ 40) * (a7 ^ 10) * a6 * a3
    - (12115012894064640 : R) * (h ^ 40) * (a7 ^ 10) * a5 * a4
    + (225274841089966080 : R) * (h ^ 40) * (a7 ^ 9) * (a6 ^ 2) * a4
    + (1076787175929937920 : R) * (h ^ 40) * (a7 ^ 9) * a6 * (a5 ^ 2)
    + (1136149014144614400 : R) * (h ^ 40) * (a7 ^ 8) * (a6 ^ 3) * a5
    - (202486394231193600 : R) * (h ^ 40) * (a7 ^ 7) * (a6 ^ 5)
    + (4207384322899968 : R) * (h ^ 38) * (a7 ^ 11) * b4
    + (83772027143454720 : R) * (h ^ 38) * (a7 ^ 10) * a6 * b5
    + (91623306817437696 : R) * (h ^ 38) * (a7 ^ 10) * a5 * b6
    + (70999610448936960 : R) * (h ^ 38) * (a7 ^ 10) * a4 * b7
    + (75732917812199424 : R) * (h ^ 38) * (a7 ^ 10) * a3 * b8
    + (297087485626810368 : R) * (h ^ 38) * (a7 ^ 9) * (a6 ^ 2) * b6
    + (761179686096076800 : R) * (h ^ 38) * (a7 ^ 9) * a6 * a5 * b7
    + (662362503405109248 : R) * (h ^ 38) * (a7 ^ 9) * a6 * a4 * b8
    + (604398271170871296 : R) * (h ^ 38) * (a7 ^ 9) * (a5 ^ 2) * b8
    + (731875576280776704 : R) * (h ^ 38) * (a7 ^ 8) * (a6 ^ 3) * b7
    + (4221530579373391872 : R) * (h ^ 38) * (a7 ^ 8) * (a6 ^ 2) * a5 * b8
    + (1612912433288970240 : R) * (h ^ 38) * (a7 ^ 7) * (a6 ^ 4) * b8
    + (4375844046766080 : R) * (h ^ 32) * (a7 ^ 12) * a3
    - (111148199690895360 : R) * (h ^ 32) * (a7 ^ 11) * a6 * a4
    - (162231996792176640 : R) * (h ^ 32) * (a7 ^ 11) * (a5 ^ 2)
    - (1067489607894958080 : R) * (h ^ 32) * (a7 ^ 10) * (a6 ^ 2) * a5
    - (248265766128844800 : R) * (h ^ 32) * (a7 ^ 9) * (a6 ^ 4)
    - (6327511579361280 : R) * (h ^ 30) * (a7 ^ 12) * b5
    - (59222690937962496 : R) * (h ^ 30) * (a7 ^ 11) * a6 * b6
    - (71870670484537344 : R) * (h ^ 30) * (a7 ^ 11) * a5 * b7
    - (62584841803137024 : R) * (h ^ 30) * (a7 ^ 11) * a4 * b8
    - (275200970223255552 : R) * (h ^ 30) * (a7 ^ 10) * (a6 ^ 2) * b7
    - (946943217138401280 : R) * (h ^ 30) * (a7 ^ 10) * a6 * a5 * b8
    - (1060357447480246272 : R) * (h ^ 30) * (a7 ^ 9) * (a6 ^ 3) * b8
    + (14082822037831680 : R) * (h ^ 24) * (a7 ^ 13) * a4
    + (292713444409344000 : R) * (h ^ 24) * (a7 ^ 12) * a6 * a5
    + (287334095262842880 : R) * (h ^ 24) * (a7 ^ 11) * (a6 ^ 3)
    + (4351191404249088 : R) * (h ^ 22) * (a7 ^ 13) * b6
    + (48943712943734784 : R) * (h ^ 22) * (a7 ^ 12) * a6 * b7
    + (78296792633966592 : R) * (h ^ 22) * (a7 ^ 12) * a5 * b8
    + (342622425701154816 : R) * (h ^ 22) * (a7 ^ 11) * (a6 ^ 2) * b8
    - (26787920876666880 : R) * (h ^ 16) * (a7 ^ 14) * a5
    - (111969220731863040 : R) * (h ^ 16) * (a7 ^ 13) * (a6 ^ 2)
    - (3330931521748992 : R) * (h ^ 14) * (a7 ^ 14) * b7
    - (54404273261248512 : R) * (h ^ 14) * (a7 ^ 13) * a6 * b8
    + (19502872414126080 : R) * (h ^ 8) * (a7 ^ 15) * a6
    + (3395644708356096 : R) * (h ^ 6) * (a7 ^ 15) * b8
    - (1284714043146240 : R) * (a7 ^ 17)

set_option maxHeartbeats 200000000 in
/-- Integer expansion of compact block `13` after the extra
`2^{34}` scale, on `λ = 0`. -/
def alignedSquareCompactBlock13Expansion810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    - (13781014859753717760 : R) * (h ^ 104) * a6 * a5 * a4 * a0
    + (324259173170675712 : R) * (h ^ 102) * a6 * (a5 ^ 2) * b1
    + (1297036692682702848 : R) * (h ^ 102) * a6 * a5 * a4 * b2
    + (6029194001142251520 : R) * (h ^ 96) * (a7 ^ 2) * a5 * a4 * a0
    + (10335761144815288320 : R) * (h ^ 96) * a7 * (a6 ^ 2) * a4 * a0
    + (8613134287346073600 : R) * (h ^ 96) * a7 * a6 * (a5 ^ 2) * a0
    + (1722626857469214720 : R) * (h ^ 96) * a7 * a6 * a5 * a4 * a1
    + (7177611906121728000 : R) * (h ^ 96) * a6 * a5 * (a4 ^ 3)
    - (141863388262170624 : R) * (h ^ 94) * (a7 ^ 2) * (a5 ^ 2) * b1
    - (567453553048682496 : R) * (h ^ 94) * (a7 ^ 2) * a5 * a4 * b2
    - (486388759756013568 : R) * (h ^ 94) * a7 * (a6 ^ 2) * a5 * b1
    - (972777519512027136 : R) * (h ^ 94) * a7 * (a6 ^ 2) * a4 * b2
    - (891712726219358208 : R) * (h ^ 94) * a7 * a6 * (a5 ^ 2) * b2
    - (486388759756013568 : R) * (h ^ 94) * a7 * a6 * a5 * a4 * b3
    - (5512405943901487104 : R) * (h ^ 94) * a6 * (a5 ^ 2) * a1 * b8
    - (4134304457926115328 : R) * (h ^ 94) * a6 * a5 * (a4 ^ 2) * b6
    - (9646710401827602432 : R) * (h ^ 94) * a6 * a5 * a4 * a3 * b7
    - (11024811887802974208 : R) * (h ^ 94) * a6 * a5 * a4 * a2 * b8
    - (5512405943901487104 : R) * (h ^ 94) * a6 * a5 * (a3 ^ 2) * b8
    - (7536492501427814400 : R) * (h ^ 88) * (a7 ^ 3) * a6 * a4 * a0
    - (3768246250713907200 : R) * (h ^ 88) * (a7 ^ 3) * (a5 ^ 2) * a0
    - (753649250142781440 : R) * (h ^ 88) * (a7 ^ 3) * a5 * a4 * a1
    - (9689776073264332800 : R) * (h ^ 88) * (a7 ^ 2) * (a6 ^ 2) * a5 * a0
    - (1291970143101911040 : R) * (h ^ 88) * (a7 ^ 2) * (a6 ^ 2) * a4 * a1
    + (2799268643387473920 : R) * (h ^ 88) * (a7 ^ 2) * a6 * (a5 ^ 2) * a1
    + (7536492501427814400 : R) * (h ^ 88) * (a7 ^ 2) * a6 * a5 * a4 * a2
    + (3875910429305733120 : R) * (h ^ 88) * (a7 ^ 2) * a6 * a5 * (a3 ^ 2)
    - (3140205208928256000 : R) * (h ^ 88) * (a7 ^ 2) * a5 * (a4 ^ 3)
    - (5383208929591296000 : R) * (h ^ 88) * a7 * (a6 ^ 2) * (a4 ^ 3)
    - (13458022323978240000 : R) * (h ^ 88) * a7 * a6 * (a5 ^ 2) * (a4 ^ 2)
    + (354658470655426560 : R) * (h ^ 86) * (a7 ^ 3) * a6 * a5 * b1
    + (709316941310853120 : R) * (h ^ 86) * (a7 ^ 3) * a6 * a4 * b2
    + (390124317720969216 : R) * (h ^ 86) * (a7 ^ 3) * (a5 ^ 2) * b2
    + (212795082393255936 : R) * (h ^ 86) * (a7 ^ 3) * a5 * a4 * b3
    + (182395784908505088 : R) * (h ^ 86) * (a7 ^ 2) * (a6 ^ 3) * b1
    + (1033576114481528832 : R) * (h ^ 86) * (a7 ^ 2) * (a6 ^ 2) * a5 * b2
    + (364791569817010176 : R) * (h ^ 86) * (a7 ^ 2) * (a6 ^ 2) * a4 * b3
    + (319192623589883904 : R) * (h ^ 86) * (a7 ^ 2) * a6 * (a5 ^ 2) * b3
    + (121597189939003392 : R) * (h ^ 86) * (a7 ^ 2) * a6 * a5 * a4 * b4
    + (2411677600456900608 : R) * (h ^ 86) * (a7 ^ 2) * (a5 ^ 2) * a1 * b8
    + (1808758200342675456 : R) * (h ^ 86) * (a7 ^ 2) * a5 * (a4 ^ 2) * b6
    + (4220435800799576064 : R) * (h ^ 86) * (a7 ^ 2) * a5 * a4 * a3 * b7
    + (4823355200913801216 : R) * (h ^ 86) * (a7 ^ 2) * a5 * a4 * a2 * b8
    + (2411677600456900608 : R) * (h ^ 86) * (a7 ^ 2) * a5 * (a3 ^ 2) * b8
    + (8268608915852230656 : R) * (h ^ 86) * a7 * (a6 ^ 2) * a5 * a1 * b8
    + (3100728343444586496 : R) * (h ^ 86) * a7 * (a6 ^ 2) * (a4 ^ 2) * b6
    + (7235032801370701824 : R) * (h ^ 86) * a7 * (a6 ^ 2) * a4 * a3 * b7
    + (8268608915852230656 : R) * (h ^ 86) * a7 * (a6 ^ 2) * a4 * a2 * b8
    + (4134304457926115328 : R) * (h ^ 86) * a7 * (a6 ^ 2) * (a3 ^ 2) * b8
    + (5167880572407644160 : R) * (h ^ 86) * a7 * a6 * (a5 ^ 2) * a4 * b6
    + (6029194001142251520 : R) * (h ^ 86) * a7 * a6 * (a5 ^ 2) * a3 * b7
    + (8268608915852230656 : R) * (h ^ 86) * a7 * a6 * (a5 ^ 2) * a2 * b8
    + (8440871601599152128 : R) * (h ^ 86) * a7 * a6 * a5 * (a4 ^ 2) * b7
    + (19293420803655204864 : R) * (h ^ 86) * a7 * a6 * a5 * a4 * a3 * b8
    + (1318886187749867520 : R) * (h ^ 80) * (a7 ^ 5) * a4 * a0
    + (6829946329418956800 : R) * (h ^ 80) * (a7 ^ 4) * a6 * a5 * a0
    + (942061562678476800 : R) * (h ^ 80) * (a7 ^ 4) * a6 * a4 * a1
    - (1224680031482019840 : R) * (h ^ 80) * (a7 ^ 4) * (a5 ^ 2) * a1
    - (3297215469374668800 : R) * (h ^ 80) * (a7 ^ 4) * a5 * a4 * a2
    - (1695710812821258240 : R) * (h ^ 80) * (a7 ^ 4) * a5 * (a3 ^ 2)
    + (2422444018316083200 : R) * (h ^ 80) * (a7 ^ 3) * (a6 ^ 3) * a0
    - (4602643634800558080 : R) * (h ^ 80) * (a7 ^ 3) * (a6 ^ 2) * a5 * a1
    - (5652369376070860800 : R) * (h ^ 80) * (a7 ^ 3) * (a6 ^ 2) * a4 * a2
    - (2906932821979299840 : R) * (h ^ 80) * (a7 ^ 3) * (a6 ^ 2) * (a3 ^ 2)
    - (5679285420718817280 : R) * (h ^ 80) * (a7 ^ 3) * a6 * (a5 ^ 2) * a2
    - (11277822707493765120 : R) * (h ^ 80) * (a7 ^ 3) * a6 * a5 * a4 * a3
    + (3925256511160320000 : R) * (h ^ 80) * (a7 ^ 3) * a6 * (a4 ^ 3)
    + (5887884766740480000 : R) * (h ^ 80) * (a7 ^ 3) * (a5 ^ 2) * (a4 ^ 2)
    + (15140275114475520000 : R) * (h ^ 80) * (a7 ^ 2) * (a6 ^ 2) * a5 * (a4 ^ 2)
    + (8411263952486400000 : R) * (h ^ 80) * (a7 ^ 2) * a6 * (a5 ^ 3) * a4
    - (62065232364699648 : R) * (h ^ 78) * (a7 ^ 5) * a5 * b1
    - (124130464729399296 : R) * (h ^ 78) * (a7 ^ 5) * a4 * b2
    - (186195697094098944 : R) * (h ^ 78) * (a7 ^ 4) * (a6 ^ 2) * b1
    - (731483095726817280 : R) * (h ^ 78) * (a7 ^ 4) * a6 * a5 * b2
    - (265993852991569920 : R) * (h ^ 78) * (a7 ^ 4) * a6 * a4 * b3
    - (139646772820574208 : R) * (h ^ 78) * (a7 ^ 4) * (a5 ^ 2) * b3
    - (53198770598313984 : R) * (h ^ 78) * (a7 ^ 4) * a5 * a4 * b4
    - (273593677362757632 : R) * (h ^ 78) * (a7 ^ 3) * (a6 ^ 3) * b2
    - (364791569817010176 : R) * (h ^ 78) * (a7 ^ 3) * (a6 ^ 2) * a5 * b3
    - (91197892454252544 : R) * (h ^ 78) * (a7 ^ 3) * (a6 ^ 2) * a4 * b4
    - (78531518502273024 : R) * (h ^ 78) * (a7 ^ 3) * a6 * (a5 ^ 2) * b4
    - (25332747903959040 : R) * (h ^ 78) * (a7 ^ 3) * a6 * a5 * a4 * b5
    - (6029194001142251520 : R) * (h ^ 78) * (a7 ^ 3) * a6 * a5 * a1 * b8
    - (2260947750428344320 : R) * (h ^ 78) * (a7 ^ 3) * a6 * (a4 ^ 2) * b6
    - (5275544750999470080 : R) * (h ^ 78) * (a7 ^ 3) * a6 * a4 * a3 * b7
    - (6029194001142251520 : R) * (h ^ 78) * (a7 ^ 3) * a6 * a4 * a2 * b8
    - (3014597000571125760 : R) * (h ^ 78) * (a7 ^ 3) * a6 * (a3 ^ 2) * b8
    - (2260947750428344320 : R) * (h ^ 78) * (a7 ^ 3) * (a5 ^ 2) * a4 * b6
    - (2637772375499735040 : R) * (h ^ 78) * (a7 ^ 3) * (a5 ^ 2) * a3 * b7
    - (3617516400685350912 : R) * (h ^ 78) * (a7 ^ 3) * (a5 ^ 2) * a2 * b8
    - (3692881325699629056 : R) * (h ^ 78) * (a7 ^ 3) * a5 * (a4 ^ 2) * b7
    - (8440871601599152128 : R) * (h ^ 78) * (a7 ^ 3) * a5 * a4 * a3 * b8
    - (3100728343444586496 : R) * (h ^ 78) * (a7 ^ 2) * (a6 ^ 3) * a1 * b8
    - (5813865643958599680 : R) * (h ^ 78) * (a7 ^ 2) * (a6 ^ 2) * a5 * a4 * b6
    - (6782843251285032960 : R) * (h ^ 78) * (a7 ^ 2) * (a6 ^ 2) * a5 * a3 * b7
    - (9818973087574523904 : R) * (h ^ 78) * (a7 ^ 2) * (a6 ^ 2) * a5 * a2 * b8
    - (6330653701199364096 : R) * (h ^ 78) * (a7 ^ 2) * (a6 ^ 2) * (a4 ^ 2) * b7
    - (14470065602741403648 : R) * (h ^ 78) * (a7 ^ 2) * (a6 ^ 2) * a4 * a3 * b8
    - (1614962678877388800 : R) * (h ^ 78) * (a7 ^ 2) * a6 * (a5 ^ 3) * b6
    - (9043791001713377280 : R) * (h ^ 78) * (a7 ^ 2) * a6 * (a5 ^ 2) * a4 * b7
    - (10594155173435670528 : R) * (h ^ 78) * (a7 ^ 2) * a6 * (a5 ^ 2) * a3 * b8
    - (9043791001713377280 : R) * (h ^ 78) * (a7 ^ 2) * a6 * a5 * (a4 ^ 2) * b8
    - (1133417817597542400 : R) * (h ^ 72) * (a7 ^ 6) * a5 * a0
    - (164860773468733440 : R) * (h ^ 72) * (a7 ^ 6) * a4 * a1
    - (2296275059028787200 : R) * (h ^ 72) * (a7 ^ 5) * (a6 ^ 2) * a0
    + (3385533740875776000 : R) * (h ^ 72) * (a7 ^ 5) * a6 * a5 * a1
    + (4121519336718336000 : R) * (h ^ 72) * (a7 ^ 5) * a6 * a4 * a2
    + (2119638516026572800 : R) * (h ^ 72) * (a7 ^ 5) * a6 * (a3 ^ 2)
    + (2484687371564482560 : R) * (h ^ 72) * (a7 ^ 5) * (a5 ^ 2) * a2
    + (4934047434528522240 : R) * (h ^ 72) * (a7 ^ 5) * a5 * a4 * a3
    - (686919889453056000 : R) * (h ^ 72) * (a7 ^ 5) * (a4 ^ 3)
    + (1877394114194964480 : R) * (h ^ 72) * (a7 ^ 4) * (a6 ^ 3) * a1
    + (6752562701056081920 : R) * (h ^ 72) * (a7 ^ 4) * (a6 ^ 2) * a5 * a2
    + (8458367030620323840 : R) * (h ^ 72) * (a7 ^ 4) * (a6 ^ 2) * a4 * a3
    + (6019100484399267840 : R) * (h ^ 72) * (a7 ^ 4) * a6 * (a5 ^ 2) * a3
    - (6082605527240540160 : R) * (h ^ 72) * (a7 ^ 4) * a6 * a5 * (a4 ^ 2)
    - (3679927979212800000 : R) * (h ^ 72) * (a7 ^ 4) * (a5 ^ 3) * a4
    - (3785068778618880000 : R) * (h ^ 72) * (a7 ^ 3) * (a6 ^ 3) * (a4 ^ 2)
    - (12616895928729600000 : R) * (h ^ 72) * (a7 ^ 3) * (a6 ^ 2) * (a5 ^ 2) * a4
    - (1752346656768000000 : R) * (h ^ 72) * (a7 ^ 3) * a6 * (a5 ^ 4)
    + (62065232364699648 : R) * (h ^ 70) * (a7 ^ 6) * a6 * b1
    + (122190926218002432 : R) * (h ^ 70) * (a7 ^ 6) * a5 * b2
    + (46548924273524736 : R) * (h ^ 70) * (a7 ^ 6) * a4 * b3
    + (262668929829175296 : R) * (h ^ 70) * (a7 ^ 5) * (a6 ^ 2) * b2
    + (257681545085583360 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a5 * b3
    + (66498463247892480 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a4 * b4
    + (34357539344744448 : R) * (h ^ 70) * (a7 ^ 5) * (a5 ^ 2) * b4
    + (11083077207982080 : R) * (h ^ 70) * (a7 ^ 5) * a5 * a4 * b5
    + (1055108950199894016 : R) * (h ^ 70) * (a7 ^ 5) * a5 * a1 * b8
    + (395665856324960256 : R) * (h ^ 70) * (a7 ^ 5) * (a4 ^ 2) * b6
    + (923220331424907264 : R) * (h ^ 70) * (a7 ^ 5) * a4 * a3 * b7
    + (1055108950199894016 : R) * (h ^ 70) * (a7 ^ 5) * a4 * a2 * b8
    + (527554475099947008 : R) * (h ^ 70) * (a7 ^ 5) * (a3 ^ 2) * b8
    + (94047826593447936 : R) * (h ^ 70) * (a7 ^ 4) * (a6 ^ 3) * b3
    + (89297936361455616 : R) * (h ^ 70) * (a7 ^ 4) * (a6 ^ 2) * a5 * b4
    + (18999560927969280 : R) * (h ^ 70) * (a7 ^ 4) * (a6 ^ 2) * a4 * b5
    + (3165326850599682048 : R) * (h ^ 70) * (a7 ^ 4) * (a6 ^ 2) * a1 * b8
    + (16228791625973760 : R) * (h ^ 70) * (a7 ^ 4) * a6 * (a5 ^ 2) * b5
    + (4102717687883366400 : R) * (h ^ 70) * (a7 ^ 4) * a6 * a5 * a4 * b6
    + (4780962430593269760 : R) * (h ^ 70) * (a7 ^ 4) * a6 * a5 * a3 * b7
    + (6971255563820728320 : R) * (h ^ 70) * (a7 ^ 4) * a6 * a5 * a2 * b8
    + (4616101657124536320 : R) * (h ^ 70) * (a7 ^ 4) * a6 * (a4 ^ 2) * b7
    + (10551089501998940160 : R) * (h ^ 70) * (a7 ^ 4) * a6 * a4 * a3 * b8
    + (706546172008857600 : R) * (h ^ 70) * (a7 ^ 4) * (a5 ^ 3) * b6
    + (3956658563249602560 : R) * (h ^ 70) * (a7 ^ 4) * (a5 ^ 2) * a4 * b7
    + (4634942888378105856 : R) * (h ^ 70) * (a7 ^ 4) * (a5 ^ 2) * a3 * b8
    + (3956658563249602560 : R) * (h ^ 70) * (a7 ^ 4) * a5 * (a4 ^ 2) * b8
    + (1453466410989649920 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 3) * a4 * b6
    + (1695710812821258240 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 3) * a3 * b7
    + (2713137300514013184 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 3) * a2 * b8
    + (2422444018316083200 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 2) * (a5 ^ 2) * b6
    + (9985852564391854080 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 2) * a5 * a4 * b7
    + (11799993973664120832 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 2) * a5 * a3 * b8
    + (6782843251285032960 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 2) * (a4 ^ 2) * b8
    + (2355153906696192000 : R) * (h ^ 70) * (a7 ^ 3) * a6 * (a5 ^ 3) * b7
    + (8548535780190978048 : R) * (h ^ 70) * (a7 ^ 3) * a6 * (a5 ^ 2) * a4 * b8
    + (695506388071219200 : R) * (h ^ 64) * (a7 ^ 7) * a6 * a0
    - (600196253409607680 : R) * (h ^ 64) * (a7 ^ 7) * a5 * a1
    - (721265883925708800 : R) * (h ^ 64) * (a7 ^ 7) * a4 * a2
    - (370936740304650240 : R) * (h ^ 64) * (a7 ^ 7) * (a3 ^ 2)
    - (1938586059449303040 : R) * (h ^ 64) * (a7 ^ 6) * (a6 ^ 2) * a1
    - (4794946156914278400 : R) * (h ^ 64) * (a7 ^ 6) * a6 * a5 * a2
    - (6167559293160652800 : R) * (h ^ 64) * (a7 ^ 6) * a6 * a4 * a3
    - (2633356461924679680 : R) * (h ^ 64) * (a7 ^ 6) * (a5 ^ 2) * a3
    - (236803365462343680 : R) * (h ^ 64) * (a7 ^ 6) * a5 * (a4 ^ 2)
    - (1869823976637726720 : R) * (h ^ 64) * (a7 ^ 5) * (a6 ^ 3) * a2
    - (6688216531819560960 : R) * (h ^ 64) * (a7 ^ 5) * (a6 ^ 2) * a5 * a3
    + (146040570375045120 : R) * (h ^ 64) * (a7 ^ 5) * (a6 ^ 2) * (a4 ^ 2)
    + (4586346810892615680 : R) * (h ^ 64) * (a7 ^ 5) * a6 * (a5 ^ 2) * a4
    + (766651662336000000 : R) * (h ^ 64) * (a7 ^ 5) * (a5 ^ 4)
    + (5914169966592000000 : R) * (h ^ 64) * (a7 ^ 4) * (a6 ^ 3) * a5 * a4
    + (3285649981440000000 : R) * (h ^ 64) * (a7 ^ 4) * (a6 ^ 2) * (a5 ^ 3)
    - (6788384789889024 : R) * (h ^ 62) * (a7 ^ 8) * b1
    - (80975732850819072 : R) * (h ^ 62) * (a7 ^ 7) * a6 * b2
    - (42912289564655616 : R) * (h ^ 62) * (a7 ^ 7) * a5 * b3
    - (11637231068381184 : R) * (h ^ 62) * (a7 ^ 7) * a4 * b4
    - (89772925384654848 : R) * (h ^ 62) * (a7 ^ 6) * (a6 ^ 2) * b3
    - (63035001620398080 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a5 * b4
    - (13853846509977600 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a4 * b5
    - (1055108950199894016 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a1 * b8
    - (7100096336363520 : R) * (h ^ 62) * (a7 ^ 6) * (a5 ^ 2) * b5
    - (682128767535022080 : R) * (h ^ 62) * (a7 ^ 6) * a5 * a4 * b6
    - (793392472318279680 : R) * (h ^ 62) * (a7 ^ 6) * a5 * a3 * b7
    - (1170511491628007424 : R) * (h ^ 62) * (a7 ^ 6) * a5 * a2 * b8
    - (807817789996793856 : R) * (h ^ 62) * (a7 ^ 6) * (a4 ^ 2) * b7
    - (1846440662849814528 : R) * (h ^ 62) * (a7 ^ 6) * a4 * a3 * b8
    - (22799473113563136 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 3) * b4
    - (18405824648970240 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 2) * a5 * b5
    - (1381327453091266560 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 2) * a4 * b6
    - (1607392541320151040 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 2) * a3 * b7
    - (2628351759872950272 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 2) * a2 * b8
    - (1681075213543931904 : R) * (h ^ 62) * (a7 ^ 5) * a6 * (a5 ^ 2) * b6
    - (7032143219232079872 : R) * (h ^ 62) * (a7 ^ 5) * a6 * a5 * a4 * b7
    - (8318403598450950144 : R) * (h ^ 62) * (a7 ^ 5) * a6 * a5 * a3 * b8
    - (4945823204062003200 : R) * (h ^ 62) * (a7 ^ 5) * a6 * (a4 ^ 2) * b8
    - (1030379834179584000 : R) * (h ^ 62) * (a7 ^ 5) * (a5 ^ 3) * b7
    - (3739984403833552896 : R) * (h ^ 62) * (a7 ^ 5) * (a5 ^ 2) * a4 * b8
    - (1135520633585664000 : R) * (h ^ 62) * (a7 ^ 4) * (a6 ^ 3) * a5 * b6
    - (2402256984830115840 : R) * (h ^ 62) * (a7 ^ 4) * (a6 ^ 3) * a4 * b7
    - (2890783195190525952 : R) * (h ^ 62) * (a7 ^ 4) * (a6 ^ 3) * a3 * b8
    - (3414973164709478400 : R) * (h ^ 62) * (a7 ^ 4) * (a6 ^ 2) * (a5 ^ 2) * b7
    - (9296801821404168192 : R) * (h ^ 62) * (a7 ^ 4) * (a6 ^ 2) * a5 * a4 * b8
    - (1924497192328888320 : R) * (h ^ 62) * (a7 ^ 4) * a6 * (a5 ^ 3) * b8
    - (67618676618035200 : R) * (h ^ 56) * (a7 ^ 9) * a0
    + (654935182100398080 : R) * (h ^ 56) * (a7 ^ 8) * a6 * a1
    + (805306239150981120 : R) * (h ^ 56) * (a7 ^ 8) * a5 * a2
    + (1079322876303114240 : R) * (h ^ 56) * (a7 ^ 8) * a4 * a3
    + (1812180533363343360 : R) * (h ^ 56) * (a7 ^ 7) * (a6 ^ 2) * a2
    + (4714999721565880320 : R) * (h ^ 56) * (a7 ^ 7) * a6 * a5 * a3
    + (1422982150461849600 : R) * (h ^ 56) * (a7 ^ 7) * a6 * (a4 ^ 2)
    + (408426006592880640 : R) * (h ^ 56) * (a7 ^ 7) * (a5 ^ 2) * a4
    + (1630418376390082560 : R) * (h ^ 56) * (a7 ^ 6) * (a6 ^ 3) * a3
    - (1028171877392056320 : R) * (h ^ 56) * (a7 ^ 6) * (a6 ^ 2) * a5 * a4
    - (1368330839103897600 : R) * (h ^ 56) * (a7 ^ 6) * a6 * (a5 ^ 3)
    - (887125494988800000 : R) * (h ^ 56) * (a7 ^ 5) * (a6 ^ 4) * a4
    - (2217813737472000000 : R) * (h ^ 56) * (a7 ^ 5) * (a6 ^ 3) * (a5 ^ 2)
    + (8061206937993216 : R) * (h ^ 54) * (a7 ^ 9) * b2
    + (27456592051961856 : R) * (h ^ 54) * (a7 ^ 8) * a6 * b3
    + (10485630077239296 : R) * (h ^ 54) * (a7 ^ 8) * a5 * b4
    + (2424423139246080 : R) * (h ^ 54) * (a7 ^ 8) * a4 * b5
    + (115402541428113408 : R) * (h ^ 54) * (a7 ^ 8) * a1 * b8
    + (21715904404389888 : R) * (h ^ 54) * (a7 ^ 7) * (a6 ^ 2) * b4
    + (12987981103104000 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a5 * b5
    + (419901429063352320 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a4 * b6
    + (486854471649853440 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a3 * b7
    + (820182348006948864 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a2 * b8
    + (271799480544657408 : R) * (h ^ 54) * (a7 ^ 7) * (a5 ^ 2) * b6
    + (1165208066010906624 : R) * (h ^ 54) * (a7 ^ 7) * a5 * a4 * b7
    + (1380708977800642560 : R) * (h ^ 54) * (a7 ^ 7) * a5 * a3 * b8
    + (865519060710850560 : R) * (h ^ 54) * (a7 ^ 7) * (a4 ^ 2) * b8
    + (4675673197117440 : R) * (h ^ 54) * (a7 ^ 6) * (a6 ^ 3) * b5
    + (1063248085024505856 : R) * (h ^ 54) * (a7 ^ 6) * (a6 ^ 2) * a5 * b6
    + (2265398298619674624 : R) * (h ^ 54) * (a7 ^ 6) * (a6 ^ 2) * a4 * b7
    + (2736688839580975104 : R) * (h ^ 54) * (a7 ^ 6) * (a6 ^ 2) * a3 * b8
    + (2360097998169440256 : R) * (h ^ 54) * (a7 ^ 6) * a6 * (a5 ^ 2) * b7
    + (6542167302790447104 : R) * (h ^ 54) * (a7 ^ 6) * a6 * a5 * a4 * b8
    + (841967521643888640 : R) * (h ^ 54) * (a7 ^ 6) * (a5 ^ 3) * b8
    + (170328095037849600 : R) * (h ^ 54) * (a7 ^ 5) * (a6 ^ 4) * b6
    + (1523490183394099200 : R) * (h ^ 54) * (a7 ^ 5) * (a6 ^ 3) * a5 * b7
    + (2164049989695700992 : R) * (h ^ 54) * (a7 ^ 5) * (a6 ^ 3) * a4 * b8
    + (2711118597165416448 : R) * (h ^ 54) * (a7 ^ 5) * (a6 ^ 2) * (a5 ^ 2) * b8
    - (72690077364387840 : R) * (h ^ 48) * (a7 ^ 10) * a1
    - (565823426128773120 : R) * (h ^ 48) * (a7 ^ 9) * a6 * a2
    - (782645932641484800 : R) * (h ^ 48) * (a7 ^ 9) * a5 * a3
    - (333545222103367680 : R) * (h ^ 48) * (a7 ^ 9) * (a4 ^ 2)
    - (1543016801233797120 : R) * (h ^ 48) * (a7 ^ 8) * (a6 ^ 2) * a3
    - (1518686067857817600 : R) * (h ^ 48) * (a7 ^ 8) * a6 * a5 * a4
    - (30249199652044800 : R) * (h ^ 48) * (a7 ^ 8) * (a5 ^ 3)
    + (2523379185745920 : R) * (h ^ 48) * (a7 ^ 7) * (a6 ^ 3) * a4
    + (818657477850562560 : R) * (h ^ 48) * (a7 ^ 7) * (a6 ^ 2) * (a5 ^ 2)
    + (646862340096000000 : R) * (h ^ 48) * (a7 ^ 6) * (a6 ^ 4) * a5
    - (2704747064721408 : R) * (h ^ 46) * (a7 ^ 10) * b3
    - (6621705699065856 : R) * (h ^ 46) * (a7 ^ 9) * a6 * b4
    - (2159251858391040 : R) * (h ^ 46) * (a7 ^ 9) * a5 * b5
    - (41025785309429760 : R) * (h ^ 46) * (a7 ^ 9) * a4 * b6
    - (47333073632624640 : R) * (h ^ 46) * (a7 ^ 9) * a3 * b7
    - (82945576651456512 : R) * (h ^ 46) * (a7 ^ 9) * a2 * b8
    - (4448383527813120 : R) * (h ^ 46) * (a7 ^ 8) * (a6 ^ 2) * b5
    - (317570343575224320 : R) * (h ^ 46) * (a7 ^ 8) * a6 * a5 * b6
    - (681149257293496320 : R) * (h ^ 46) * (a7 ^ 8) * a6 * a4 * b7
    - (827395006846205952 : R) * (h ^ 46) * (a7 ^ 8) * a6 * a3 * b8
    - (378895666891456512 : R) * (h ^ 46) * (a7 ^ 8) * (a5 ^ 2) * b7
    - (1082732221342679040 : R) * (h ^ 46) * (a7 ^ 8) * a5 * a4 * b8
    - (199584450185527296 : R) * (h ^ 46) * (a7 ^ 7) * (a6 ^ 3) * b6
    - (1412217819956772864 : R) * (h ^ 46) * (a7 ^ 7) * (a6 ^ 2) * a5 * b7
    - (2031571345493458944 : R) * (h ^ 46) * (a7 ^ 7) * (a6 ^ 2) * a4 * b8
    - (1869691004450242560 : R) * (h ^ 46) * (a7 ^ 7) * a6 * (a5 ^ 2) * b8
    - (215275786783948800 : R) * (h ^ 46) * (a7 ^ 6) * (a6 ^ 4) * b7
    - (1157116553783672832 : R) * (h ^ 46) * (a7 ^ 6) * (a6 ^ 3) * a5 * b8
    + (57264566760898560 : R) * (h ^ 40) * (a7 ^ 11) * a2
    + (466297186481602560 : R) * (h ^ 40) * (a7 ^ 10) * a6 * a3
    + (365969698958868480 : R) * (h ^ 40) * (a7 ^ 10) * a5 * a4
    + (528977365083095040 : R) * (h ^ 40) * (a7 ^ 9) * (a6 ^ 2) * a4
    + (245982431155322880 : R) * (h ^ 40) * (a7 ^ 9) * a6 * (a5 ^ 2)
    - (233298295668080640 : R) * (h ^ 40) * (a7 ^ 8) * (a6 ^ 3) * a5
    - (69306679296000000 : R) * (h ^ 40) * (a7 ^ 7) * (a6 ^ 5)
    + (649669638094848 : R) * (h ^ 38) * (a7 ^ 11) * b4
    + (1354267612938240 : R) * (h ^ 38) * (a7 ^ 10) * a6 * b5
    + (30513460534050816 : R) * (h ^ 38) * (a7 ^ 10) * a5 * b6
    + (65556969909387264 : R) * (h ^ 38) * (a7 ^ 10) * a4 * b7
    + (80240829586735104 : R) * (h ^ 38) * (a7 ^ 10) * a3 * b8
    + (85047025229365248 : R) * (h ^ 38) * (a7 ^ 9) * (a6 ^ 2) * b6
    + (415924113522032640 : R) * (h ^ 38) * (a7 ^ 9) * a6 * a5 * b7
    + (606905086815240192 : R) * (h ^ 38) * (a7 ^ 9) * a6 * a4 * b8
    + (299064770458288128 : R) * (h ^ 38) * (a7 ^ 9) * (a5 ^ 2) * b8
    + (248408126577967104 : R) * (h ^ 38) * (a7 ^ 8) * (a6 ^ 3) * b7
    + (1065489671405961216 : R) * (h ^ 38) * (a7 ^ 8) * (a6 ^ 2) * a5 * b8
    + (154730457445957632 : R) * (h ^ 38) * (a7 ^ 7) * (a6 ^ 4) * b8
    - (45193576442757120 : R) * (h ^ 32) * (a7 ^ 12) * a3
    - (207890594062663680 : R) * (h ^ 32) * (a7 ^ 11) * a6 * a4
    - (78593229324288000 : R) * (h ^ 32) * (a7 ^ 11) * (a5 ^ 2)
    - (158552132419584000 : R) * (h ^ 32) * (a7 ^ 10) * (a6 ^ 2) * a5
    + (28955637543075840 : R) * (h ^ 32) * (a7 ^ 9) * (a6 ^ 4)
    - (132585640427520 : R) * (h ^ 30) * (a7 ^ 12) * b5
    - (15703008205602816 : R) * (h ^ 30) * (a7 ^ 11) * a6 * b6
    - (39236907590221824 : R) * (h ^ 30) * (a7 ^ 11) * a5 * b7
    - (57883575969644544 : R) * (h ^ 30) * (a7 ^ 11) * a4 * b8
    - (103843056448438272 : R) * (h ^ 30) * (a7 ^ 10) * (a6 ^ 2) * b7
    - (310844387342942208 : R) * (h ^ 30) * (a7 ^ 10) * a6 * a5 * b8
    - (176564664577032192 : R) * (h ^ 30) * (a7 ^ 9) * (a6 ^ 3) * b8
    + (21992295133347840 : R) * (h ^ 24) * (a7 ^ 13) * a4
    + (80201051392573440 : R) * (h ^ 24) * (a7 ^ 12) * a6 * a5
    + (24169402497761280 : R) * (h ^ 24) * (a7 ^ 11) * (a6 ^ 3)
    + (1064582416171008 : R) * (h ^ 22) * (a7 ^ 13) * b6
    + (18741096804777984 : R) * (h ^ 22) * (a7 ^ 12) * a6 * b7
    + (28950248458027008 : R) * (h ^ 22) * (a7 ^ 12) * a5 * b8
    + (72768962860941312 : R) * (h ^ 22) * (a7 ^ 11) * (a6 ^ 2) * b8
    - (8902313665781760 : R) * (h ^ 16) * (a7 ^ 14) * a5
    - (17378986471096320 : R) * (h ^ 16) * (a7 ^ 13) * (a6 ^ 2)
    - (1237854951309312 : R) * (h ^ 14) * (a7 ^ 14) * b7
    - (12907651396534272 : R) * (h ^ 14) * (a7 ^ 13) * a6 * b8
    + (3682756423342080 : R) * (h ^ 8) * (a7 ^ 15) * a6
    + (835469994885120 : R) * (h ^ 6) * (a7 ^ 15) * b8
    - (258664208866560 : R) * (a7 ^ 17)

set_option maxHeartbeats 200000000 in
/-- Integer expansion of compact block `14` after the extra
`2^{34}` scale, on `λ = 0`. -/
def alignedSquareCompactBlock14Expansion810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    - (13781014859753717760 : R) * (h ^ 104) * a6 * a5 * a3 * a1
    - (6890507429876858880 : R) * (h ^ 104) * a6 * a5 * (a2 ^ 2)
    - (6890507429876858880 : R) * (h ^ 104) * a6 * (a4 ^ 2) * a1
    + (1945555039024054272 : R) * (h ^ 102) * a6 * a5 * a3 * b3
    + (2594073385365405696 : R) * (h ^ 102) * a6 * a5 * a2 * b4
    + (3242591731706757120 : R) * (h ^ 102) * a6 * a5 * a1 * b5
    + (3891110078048108544 : R) * (h ^ 102) * a6 * a5 * a0 * b6
    + (6029194001142251520 : R) * (h ^ 96) * (a7 ^ 2) * a5 * a3 * a1
    + (3014597000571125760 : R) * (h ^ 96) * (a7 ^ 2) * a5 * (a2 ^ 2)
    + (3014597000571125760 : R) * (h ^ 96) * (a7 ^ 2) * (a4 ^ 2) * a1
    + (10335761144815288320 : R) * (h ^ 96) * a7 * (a6 ^ 2) * a3 * a1
    + (5167880572407644160 : R) * (h ^ 96) * a7 * (a6 ^ 2) * (a2 ^ 2)
    + (15503641717222932480 : R) * (h ^ 96) * a7 * a6 * a5 * a4 * a1
    + (8613134287346073600 : R) * (h ^ 96) * a7 * a6 * a5 * a3 * a2
    + (1722626857469214720 : R) * (h ^ 96) * a7 * a6 * (a4 ^ 2) * a2
    - (851180329573023744 : R) * (h ^ 94) * (a7 ^ 2) * a5 * a3 * b3
    - (1134907106097364992 : R) * (h ^ 94) * (a7 ^ 2) * a5 * a2 * b4
    - (1418633882621706240 : R) * (h ^ 94) * (a7 ^ 2) * a5 * a1 * b5
    - (1702360659146047488 : R) * (h ^ 94) * (a7 ^ 2) * a5 * a0 * b6
    - (1459166279268040704 : R) * (h ^ 94) * a7 * (a6 ^ 2) * a3 * b3
    - (1945555039024054272 : R) * (h ^ 94) * a7 * (a6 ^ 2) * a2 * b4
    - (2431943798780067840 : R) * (h ^ 94) * a7 * (a6 ^ 2) * a1 * b5
    - (2918332558536081408 : R) * (h ^ 94) * a7 * (a6 ^ 2) * a0 * b6
    - (972777519512027136 : R) * (h ^ 94) * a7 * a6 * a5 * a4 * b3
    - (1945555039024054272 : R) * (h ^ 94) * a7 * a6 * a5 * a3 * b4
    - (2431943798780067840 : R) * (h ^ 94) * a7 * a6 * a5 * a2 * b5
    - (2918332558536081408 : R) * (h ^ 94) * a7 * a6 * a5 * a1 * b6
    - (3404721318292094976 : R) * (h ^ 94) * a7 * a6 * a5 * a0 * b7
    - (1607785066971267072 : R) * (h ^ 94) * a6 * (a4 ^ 3) * b7
    - (5512405943901487104 : R) * (h ^ 94) * a6 * (a4 ^ 2) * a3 * b8
    - (7536492501427814400 : R) * (h ^ 88) * (a7 ^ 3) * a6 * a3 * a1
    - (3768246250713907200 : R) * (h ^ 88) * (a7 ^ 3) * a6 * (a2 ^ 2)
    - (6782843251285032960 : R) * (h ^ 88) * (a7 ^ 3) * a5 * a4 * a1
    - (3768246250713907200 : R) * (h ^ 88) * (a7 ^ 3) * a5 * a3 * a2
    - (753649250142781440 : R) * (h ^ 88) * (a7 ^ 3) * (a4 ^ 2) * a2
    - (8397805930162421760 : R) * (h ^ 88) * (a7 ^ 2) * (a6 ^ 2) * a4 * a1
    - (6459850715509555200 : R) * (h ^ 88) * (a7 ^ 2) * (a6 ^ 2) * a3 * a2
    - (4844888036632166400 : R) * (h ^ 88) * (a7 ^ 2) * a6 * (a5 ^ 2) * a1
    - (5167880572407644160 : R) * (h ^ 88) * (a7 ^ 2) * a6 * a5 * a4 * a2
    - (1614962678877388800 : R) * (h ^ 88) * (a7 ^ 2) * a6 * a5 * (a3 ^ 2)
    + (3552917893530255360 : R) * (h ^ 88) * (a7 ^ 2) * a6 * (a4 ^ 2) * a3
    + (1063975411966279680 : R) * (h ^ 86) * (a7 ^ 3) * a6 * a3 * b3
    + (1418633882621706240 : R) * (h ^ 86) * (a7 ^ 3) * a6 * a2 * b4
    + (1773292353277132800 : R) * (h ^ 86) * (a7 ^ 3) * a6 * a1 * b5
    + (2127950823932559360 : R) * (h ^ 86) * (a7 ^ 3) * a6 * a0 * b6
    + (425590164786511872 : R) * (h ^ 86) * (a7 ^ 3) * a5 * a4 * b3
    + (851180329573023744 : R) * (h ^ 86) * (a7 ^ 3) * a5 * a3 * b4
    + (1063975411966279680 : R) * (h ^ 86) * (a7 ^ 3) * a5 * a2 * b5
    + (1276770494359535616 : R) * (h ^ 86) * (a7 ^ 3) * a5 * a1 * b6
    + (1489565576752791552 : R) * (h ^ 86) * (a7 ^ 3) * a5 * a0 * b7
    + (729583139634020352 : R) * (h ^ 86) * (a7 ^ 2) * (a6 ^ 2) * a4 * b3
    + (1459166279268040704 : R) * (h ^ 86) * (a7 ^ 2) * (a6 ^ 2) * a3 * b4
    + (1823957849085050880 : R) * (h ^ 86) * (a7 ^ 2) * (a6 ^ 2) * a2 * b5
    + (2188749418902061056 : R) * (h ^ 86) * (a7 ^ 2) * (a6 ^ 2) * a1 * b6
    + (2553540988719071232 : R) * (h ^ 86) * (a7 ^ 2) * (a6 ^ 2) * a0 * b7
    + (303992974847508480 : R) * (h ^ 86) * (a7 ^ 2) * a6 * (a5 ^ 2) * b3
    + (729583139634020352 : R) * (h ^ 86) * (a7 ^ 2) * a6 * a5 * a4 * b4
    + (1063975411966279680 : R) * (h ^ 86) * (a7 ^ 2) * a6 * a5 * a3 * b5
    + (1276770494359535616 : R) * (h ^ 86) * (a7 ^ 2) * a6 * a5 * a2 * b6
    + (1489565576752791552 : R) * (h ^ 86) * (a7 ^ 2) * a6 * a5 * a1 * b7
    + (1702360659146047488 : R) * (h ^ 86) * (a7 ^ 2) * a6 * a5 * a0 * b8
    + (703405966799929344 : R) * (h ^ 86) * (a7 ^ 2) * (a4 ^ 3) * b7
    + (2411677600456900608 : R) * (h ^ 86) * (a7 ^ 2) * (a4 ^ 2) * a3 * b8
    + (3014597000571125760 : R) * (h ^ 86) * a7 * a6 * a5 * (a4 ^ 2) * b7
    + (6890507429876858880 : R) * (h ^ 86) * a7 * a6 * a5 * a4 * a3 * b8
    + (4363988038922010624 : R) * (h ^ 86) * a7 * a6 * (a4 ^ 3) * b8
    + (1318886187749867520 : R) * (h ^ 80) * (a7 ^ 5) * a3 * a1
    + (659443093874933760 : R) * (h ^ 80) * (a7 ^ 5) * (a2 ^ 2)
    - (598486169231032320 : R) * (h ^ 80) * (a7 ^ 4) * a6 * a5 * a0
    + (5887884766740480000 : R) * (h ^ 80) * (a7 ^ 4) * a6 * a4 * a1
    + (4710307813392384000 : R) * (h ^ 80) * (a7 ^ 4) * a6 * a3 * a2
    + (2119638516026572800 : R) * (h ^ 80) * (a7 ^ 4) * (a5 ^ 2) * a1
    + (2260947750428344320 : R) * (h ^ 80) * (a7 ^ 4) * a5 * a4 * a2
    + (706546172008857600 : R) * (h ^ 80) * (a7 ^ 4) * a5 * (a3 ^ 2)
    - (1554401578419486720 : R) * (h ^ 80) * (a7 ^ 4) * (a4 ^ 2) * a3
    + (4171986920433254400 : R) * (h ^ 80) * (a7 ^ 3) * (a6 ^ 2) * a5 * a1
    + (3068429089867038720 : R) * (h ^ 80) * (a7 ^ 3) * (a6 ^ 2) * a4 * a2
    + (1211222009158041600 : R) * (h ^ 80) * (a7 ^ 3) * (a6 ^ 2) * (a3 ^ 2)
    + (1480382455637606400 : R) * (h ^ 80) * (a7 ^ 3) * a6 * (a5 ^ 2) * a2
    - (3526001848882298880 : R) * (h ^ 80) * (a7 ^ 3) * a6 * a5 * a4 * a3
    - (2637772375499735040 : R) * (h ^ 80) * (a7 ^ 3) * a6 * (a4 ^ 3)
    - (186195697094098944 : R) * (h ^ 78) * (a7 ^ 5) * a3 * b3
    - (248260929458798592 : R) * (h ^ 78) * (a7 ^ 5) * a2 * b4
    - (310326161823498240 : R) * (h ^ 78) * (a7 ^ 5) * a1 * b5
    - (372391394188197888 : R) * (h ^ 78) * (a7 ^ 5) * a0 * b6
    - (531987705983139840 : R) * (h ^ 78) * (a7 ^ 4) * a6 * a4 * b3
    - (1063975411966279680 : R) * (h ^ 78) * (a7 ^ 4) * a6 * a3 * b4
    - (1329969264957849600 : R) * (h ^ 78) * (a7 ^ 4) * a6 * a2 * b5
    - (1595963117949419520 : R) * (h ^ 78) * (a7 ^ 4) * a6 * a1 * b6
    - (1861956970940989440 : R) * (h ^ 78) * (a7 ^ 4) * a6 * a0 * b7
    - (132996926495784960 : R) * (h ^ 78) * (a7 ^ 4) * (a5 ^ 2) * b3
    - (319192623589883904 : R) * (h ^ 78) * (a7 ^ 4) * a5 * a4 * b4
    - (465489242735247360 : R) * (h ^ 78) * (a7 ^ 4) * a5 * a3 * b5
    - (558587091282296832 : R) * (h ^ 78) * (a7 ^ 4) * a5 * a2 * b6
    - (651684939829346304 : R) * (h ^ 78) * (a7 ^ 4) * a5 * a1 * b7
    - (744782788376395776 : R) * (h ^ 78) * (a7 ^ 4) * a5 * a0 * b8
    - (303992974847508480 : R) * (h ^ 78) * (a7 ^ 3) * (a6 ^ 2) * a5 * b3
    - (547187354725515264 : R) * (h ^ 78) * (a7 ^ 3) * (a6 ^ 2) * a4 * b4
    - (797981558974709760 : R) * (h ^ 78) * (a7 ^ 3) * (a6 ^ 2) * a3 * b5
    - (957577870769651712 : R) * (h ^ 78) * (a7 ^ 3) * (a6 ^ 2) * a2 * b6
    - (1117174182564593664 : R) * (h ^ 78) * (a7 ^ 3) * (a6 ^ 2) * a1 * b7
    - (1276770494359535616 : R) * (h ^ 78) * (a7 ^ 3) * (a6 ^ 2) * a0 * b8
    - (202661983231672320 : R) * (h ^ 78) * (a7 ^ 3) * a6 * (a5 ^ 2) * b4
    - (329325722751467520 : R) * (h ^ 78) * (a7 ^ 3) * a6 * a5 * a4 * b5
    - (425590164786511872 : R) * (h ^ 78) * (a7 ^ 3) * a6 * a5 * a3 * b6
    - (496521858917597184 : R) * (h ^ 78) * (a7 ^ 3) * a6 * a5 * a2 * b7
    - (567453553048682496 : R) * (h ^ 78) * (a7 ^ 3) * a6 * a5 * a1 * b8
    - (1318886187749867520 : R) * (h ^ 78) * (a7 ^ 3) * a5 * (a4 ^ 2) * b7
    - (3014597000571125760 : R) * (h ^ 78) * (a7 ^ 3) * a5 * a4 * a3 * b8
    - (1909244767028379648 : R) * (h ^ 78) * (a7 ^ 3) * (a4 ^ 3) * b8
    - (1130473875214172160 : R) * (h ^ 78) * (a7 ^ 2) * (a6 ^ 2) * (a4 ^ 2) * b7
    - (2583940286203822080 : R) * (h ^ 78) * (a7 ^ 2) * (a6 ^ 2) * a4 * a3 * b8
    - (1884123125356953600 : R) * (h ^ 78) * (a7 ^ 2) * a6 * (a5 ^ 2) * a4 * b7
    - (2153283571836518400 : R) * (h ^ 78) * (a7 ^ 2) * a6 * (a5 ^ 2) * a3 * b8
    - (7321164144244162560 : R) * (h ^ 78) * (a7 ^ 2) * a6 * a5 * (a4 ^ 2) * b8
    + (261837699038576640 : R) * (h ^ 72) * (a7 ^ 6) * a5 * a0
    - (968557044128808960 : R) * (h ^ 72) * (a7 ^ 6) * a4 * a1
    - (824303867343667200 : R) * (h ^ 72) * (a7 ^ 6) * a3 * a2
    + (448864626923274240 : R) * (h ^ 72) * (a7 ^ 5) * (a6 ^ 2) * a0
    - (2657514106776453120 : R) * (h ^ 72) * (a7 ^ 5) * a6 * a5 * a1
    - (2178517363693977600 : R) * (h ^ 72) * (a7 ^ 5) * a6 * a4 * a2
    - (883182715011072000 : R) * (h ^ 72) * (a7 ^ 5) * a6 * (a3 ^ 2)
    - (647667324341452800 : R) * (h ^ 72) * (a7 ^ 5) * (a5 ^ 2) * a2
    + (1542625808886005760 : R) * (h ^ 72) * (a7 ^ 5) * a5 * a4 * a3
    + (1154025414281134080 : R) * (h ^ 72) * (a7 ^ 5) * (a4 ^ 3)
    - (782247547581235200 : R) * (h ^ 72) * (a7 ^ 4) * (a6 ^ 3) * a1
    - (1295334648682905600 : R) * (h ^ 72) * (a7 ^ 4) * (a6 ^ 2) * a5 * a2
    + (979071124069416960 : R) * (h ^ 72) * (a7 ^ 4) * (a6 ^ 2) * a4 * a3
    + (1169165689395609600 : R) * (h ^ 72) * (a7 ^ 4) * a6 * (a5 ^ 2) * a3
    + (4251052801586626560 : R) * (h ^ 72) * (a7 ^ 4) * a6 * a5 * (a4 ^ 2)
    + (93097848547049472 : R) * (h ^ 70) * (a7 ^ 6) * a4 * b3
    + (186195697094098944 : R) * (h ^ 70) * (a7 ^ 6) * a3 * b4
    + (232744621367623680 : R) * (h ^ 70) * (a7 ^ 6) * a2 * b5
    + (279293545641148416 : R) * (h ^ 70) * (a7 ^ 6) * a1 * b6
    + (325842469914673152 : R) * (h ^ 70) * (a7 ^ 6) * a0 * b7
    + (212795082393255936 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a5 * b3
    + (398990779487354880 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a4 * b4
    + (581861553419059200 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a3 * b5
    + (698233864102871040 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a2 * b6
    + (814606174786682880 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a1 * b7
    + (930978485470494720 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a0 * b8
    + (88664617663856640 : R) * (h ^ 70) * (a7 ^ 5) * (a5 ^ 2) * b4
    + (144080003703767040 : R) * (h ^ 70) * (a7 ^ 5) * a5 * a4 * b5
    + (186195697094098944 : R) * (h ^ 70) * (a7 ^ 5) * a5 * a3 * b6
    + (217228313276448768 : R) * (h ^ 70) * (a7 ^ 5) * a5 * a2 * b7
    + (248260929458798592 : R) * (h ^ 70) * (a7 ^ 5) * a5 * a1 * b8
    + (56998682783907840 : R) * (h ^ 70) * (a7 ^ 4) * (a6 ^ 3) * b3
    + (199495389743677440 : R) * (h ^ 70) * (a7 ^ 4) * (a6 ^ 2) * a5 * b4
    + (246994292063600640 : R) * (h ^ 70) * (a7 ^ 4) * (a6 ^ 2) * a4 * b5
    + (319192623589883904 : R) * (h ^ 70) * (a7 ^ 4) * (a6 ^ 2) * a3 * b6
    + (372391394188197888 : R) * (h ^ 70) * (a7 ^ 4) * (a6 ^ 2) * a2 * b7
    + (425590164786511872 : R) * (h ^ 70) * (a7 ^ 4) * (a6 ^ 2) * a1 * b8
    + (83123079059865600 : R) * (h ^ 70) * (a7 ^ 4) * a6 * (a5 ^ 2) * b5
    + (114947343614214144 : R) * (h ^ 70) * (a7 ^ 4) * a6 * a5 * a4 * b6
    + (139646772820574208 : R) * (h ^ 70) * (a7 ^ 4) * a6 * a5 * a3 * b7
    + (159596311794941952 : R) * (h ^ 70) * (a7 ^ 4) * a6 * a5 * a2 * b8
    + (741873480609300480 : R) * (h ^ 70) * (a7 ^ 4) * a6 * (a4 ^ 2) * b7
    + (1695710812821258240 : R) * (h ^ 70) * (a7 ^ 4) * a6 * a4 * a3 * b8
    + (824303867343667200 : R) * (h ^ 70) * (a7 ^ 4) * (a5 ^ 2) * a4 * b7
    + (942061562678476800 : R) * (h ^ 70) * (a7 ^ 4) * (a5 ^ 2) * a3 * b8
    + (3203009313106821120 : R) * (h ^ 70) * (a7 ^ 4) * a5 * (a4 ^ 2) * b8
    + (1413092344017715200 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 2) * a5 * a4 * b7
    + (1614962678877388800 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 2) * a5 * a3 * b8
    + (2637772375499735040 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 2) * (a4 ^ 2) * b8
    + (392525651116032000 : R) * (h ^ 70) * (a7 ^ 3) * a6 * (a5 ^ 3) * b7
    + (4037406697193472000 : R) * (h ^ 70) * (a7 ^ 3) * a6 * (a5 ^ 2) * a4 * b8
    - (327297123798220800 : R) * (h ^ 64) * (a7 ^ 7) * a6 * a0
    + (364118050225520640 : R) * (h ^ 64) * (a7 ^ 7) * a5 * a1
    + (365784841133752320 : R) * (h ^ 64) * (a7 ^ 7) * a4 * a2
    + (154556975126937600 : R) * (h ^ 64) * (a7 ^ 7) * (a3 ^ 2)
    + (565323524147773440 : R) * (h ^ 64) * (a7 ^ 6) * (a6 ^ 2) * a1
    + (839976031208079360 : R) * (h ^ 64) * (a7 ^ 6) * a6 * a5 * a2
    - (592468404653260800 : R) * (h ^ 64) * (a7 ^ 6) * a6 * a4 * a3
    - (511509989110579200 : R) * (h ^ 64) * (a7 ^ 6) * (a5 ^ 2) * a3
    - (1859835600694149120 : R) * (h ^ 64) * (a7 ^ 6) * a5 * (a4 ^ 2)
    + (233412574681497600 : R) * (h ^ 64) * (a7 ^ 5) * (a6 ^ 3) * a2
    - (830191752110407680 : R) * (h ^ 64) * (a7 ^ 5) * (a6 ^ 2) * a5 * a3
    - (1477438513254236160 : R) * (h ^ 64) * (a7 ^ 5) * (a6 ^ 2) * (a4 ^ 2)
    - (2315200402921881600 : R) * (h ^ 64) * (a7 ^ 5) * a6 * (a5 ^ 2) * a4
    - (34911693205143552 : R) * (h ^ 62) * (a7 ^ 7) * a5 * b3
    - (69823386410287104 : R) * (h ^ 62) * (a7 ^ 7) * a4 * b4
    - (101825771848335360 : R) * (h ^ 62) * (a7 ^ 7) * a3 * b5
    - (122190926218002432 : R) * (h ^ 62) * (a7 ^ 7) * a2 * b6
    - (142556080587669504 : R) * (h ^ 62) * (a7 ^ 7) * a1 * b7
    - (162921234957336576 : R) * (h ^ 62) * (a7 ^ 7) * a0 * b8
    - (51536309017116672 : R) * (h ^ 62) * (a7 ^ 6) * (a6 ^ 2) * b3
    - (139646772820574208 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a5 * b4
    - (180100004629708800 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a4 * b5
    - (232744621367623680 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a3 * b6
    - (271535391595560960 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a2 * b7
    - (310326161823498240 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a1 * b8
    - (36366347088691200 : R) * (h ^ 62) * (a7 ^ 6) * (a5 ^ 2) * b5
    - (50289462831218688 : R) * (h ^ 62) * (a7 ^ 6) * a5 * a4 * b6
    - (61095463109001216 : R) * (h ^ 62) * (a7 ^ 6) * a5 * a3 * b7
    - (69823386410287104 : R) * (h ^ 62) * (a7 ^ 6) * a5 * a2 * b8
    - (108189882588856320 : R) * (h ^ 62) * (a7 ^ 6) * (a4 ^ 2) * b7
    - (247291160203100160 : R) * (h ^ 62) * (a7 ^ 6) * a4 * a3 * b8
    - (35624176739942400 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 3) * b4
    - (80748133943869440 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 2) * a5 * b5
    - (86210507710660608 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 2) * a4 * b6
    - (104735079615430656 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 2) * a3 * b7
    - (119697233846206464 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 2) * a2 * b8
    - (26836879810756608 : R) * (h ^ 62) * (a7 ^ 5) * a6 * (a5 ^ 2) * b6
    - (961422313176170496 : R) * (h ^ 62) * (a7 ^ 5) * a6 * a5 * a4 * b7
    - (1099718335962021888 : R) * (h ^ 62) * (a7 ^ 5) * a6 * a5 * a3 * b8
    - (1721617505794916352 : R) * (h ^ 62) * (a7 ^ 5) * a6 * (a4 ^ 2) * b8
    - (171729972363264000 : R) * (h ^ 62) * (a7 ^ 5) * (a5 ^ 3) * b7
    - (1766365430022144000 : R) * (h ^ 62) * (a7 ^ 5) * (a5 ^ 2) * a4 * b8
    - (264954814503321600 : R) * (h ^ 62) * (a7 ^ 4) * (a6 ^ 3) * a4 * b7
    - (302805502289510400 : R) * (h ^ 62) * (a7 ^ 4) * (a6 ^ 3) * a3 * b8
    - (441591357505536000 : R) * (h ^ 62) * (a7 ^ 4) * (a6 ^ 2) * (a5 ^ 2) * b7
    - (2893474799655321600 : R) * (h ^ 62) * (a7 ^ 4) * (a6 ^ 2) * a5 * a4 * b8
    - (728976209215488000 : R) * (h ^ 62) * (a7 ^ 4) * a6 * (a5 ^ 3) * b8
    + (57276996664688640 : R) * (h ^ 56) * (a7 ^ 9) * a0
    - (98137049923584000 : R) * (h ^ 56) * (a7 ^ 8) * a6 * a1
    - (119554366054072320 : R) * (h ^ 56) * (a7 ^ 8) * a5 * a2
    + (71804594694389760 : R) * (h ^ 56) * (a7 ^ 8) * a4 * a3
    - (173670953983672320 : R) * (h ^ 56) * (a7 ^ 7) * (a6 ^ 2) * a2
    + (545983028715847680 : R) * (h ^ 56) * (a7 ^ 7) * a6 * a5 * a3
    + (956807559795179520 : R) * (h ^ 56) * (a7 ^ 7) * a6 * (a4 ^ 2)
    + (1012900176278323200 : R) * (h ^ 56) * (a7 ^ 7) * (a5 ^ 2) * a4
    + (160155722695311360 : R) * (h ^ 56) * (a7 ^ 6) * (a6 ^ 3) * a3
    + (1633940593170186240 : R) * (h ^ 56) * (a7 ^ 6) * (a6 ^ 2) * a5 * a4
    + (412020507672576000 : R) * (h ^ 56) * (a7 ^ 6) * a6 * (a5 ^ 3)
    + (14546538835476480 : R) * (h ^ 54) * (a7 ^ 8) * a6 * b3
    + (22910798665875456 : R) * (h ^ 54) * (a7 ^ 8) * a5 * b4
    + (31517500810199040 : R) * (h ^ 54) * (a7 ^ 8) * a4 * b5
    + (40730308739334144 : R) * (h ^ 54) * (a7 ^ 8) * a3 * b6
    + (47518693529223168 : R) * (h ^ 54) * (a7 ^ 8) * a2 * b7
    + (54307078319112192 : R) * (h ^ 54) * (a7 ^ 8) * a1 * b8
    + (32002385438048256 : R) * (h ^ 54) * (a7 ^ 7) * (a6 ^ 2) * b4
    + (56528641563033600 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a5 * b5
    + (62861828539023360 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a4 * b6
    + (76369328886251520 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a3 * b7
    + (87279233012858880 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a2 * b8
    + (11741134917206016 : R) * (h ^ 54) * (a7 ^ 7) * (a5 ^ 2) * b6
    + (150147555542433792 : R) * (h ^ 54) * (a7 ^ 7) * a5 * a4 * b7
    + (172012821729509376 : R) * (h ^ 54) * (a7 ^ 7) * a5 * a3 * b8
    + (248321540037279744 : R) * (h ^ 54) * (a7 ^ 7) * (a4 ^ 2) * b8
    + (13804368486727680 : R) * (h ^ 54) * (a7 ^ 6) * (a6 ^ 3) * b5
    + (25782997915533312 : R) * (h ^ 54) * (a7 ^ 6) * (a6 ^ 2) * a5 * b6
    + (257395809501315072 : R) * (h ^ 54) * (a7 ^ 6) * (a6 ^ 2) * a4 * b7
    + (294879122964873216 : R) * (h ^ 54) * (a7 ^ 6) * (a6 ^ 2) * a3 * b8
    + (297258088170258432 : R) * (h ^ 54) * (a7 ^ 6) * a6 * (a5 ^ 2) * b7
    + (1896072067971809280 : R) * (h ^ 54) * (a7 ^ 6) * a6 * a5 * a4 * b8
    + (318927091531776000 : R) * (h ^ 54) * (a7 ^ 6) * (a5 ^ 3) * b8
    + (165596759064576000 : R) * (h ^ 54) * (a7 ^ 5) * (a6 ^ 3) * a5 * b7
    + (517292733077913600 : R) * (h ^ 54) * (a7 ^ 5) * (a6 ^ 3) * a4 * b8
    + (778041915604992000 : R) * (h ^ 54) * (a7 ^ 5) * (a6 ^ 2) * (a5 ^ 2) * b8
    + (234096521379840 : R) * (h ^ 48) * (a7 ^ 10) * a1
    + (32820865007616000 : R) * (h ^ 48) * (a7 ^ 9) * a6 * a2
    - (79963685010800640 : R) * (h ^ 48) * (a7 ^ 9) * a5 * a3
    - (135812341982822400 : R) * (h ^ 48) * (a7 ^ 9) * (a4 ^ 2)
    - (147430400317194240 : R) * (h ^ 48) * (a7 ^ 8) * (a6 ^ 2) * a3
    - (1064262326519070720 : R) * (h ^ 48) * (a7 ^ 8) * a6 * a5 * a4
    - (180258972106752000 : R) * (h ^ 48) * (a7 ^ 8) * (a5 ^ 3)
    - (290425173159444480 : R) * (h ^ 48) * (a7 ^ 7) * (a6 ^ 3) * a4
    - (434625779544883200 : R) * (h ^ 48) * (a7 ^ 7) * (a6 ^ 2) * (a5 ^ 2)
    - (1272822148104192 : R) * (h ^ 46) * (a7 ^ 10) * b3
    - (8940060325969920 : R) * (h ^ 46) * (a7 ^ 9) * a6 * b4
    - (9275583171133440 : R) * (h ^ 46) * (a7 ^ 9) * a5 * b5
    - (11000819994329088 : R) * (h ^ 46) * (a7 ^ 9) * a4 * b6
    - (13364632555094016 : R) * (h ^ 46) * (a7 ^ 9) * a3 * b7
    - (15273865777250304 : R) * (h ^ 46) * (a7 ^ 9) * a2 * b8
    - (12329304918589440 : R) * (h ^ 46) * (a7 ^ 8) * (a6 ^ 2) * b5
    - (18052134092144640 : R) * (h ^ 46) * (a7 ^ 8) * a6 * a5 * b6
    - (82030262212362240 : R) * (h ^ 46) * (a7 ^ 8) * a6 * a4 * b7
    - (94268390343966720 : R) * (h ^ 46) * (a7 ^ 8) * a6 * a3 * b8
    - (45527067801944064 : R) * (h ^ 46) * (a7 ^ 8) * (a5 ^ 2) * b7
    - (275702368866140160 : R) * (h ^ 46) * (a7 ^ 8) * a5 * a4 * b8
    - (4241503543099392 : R) * (h ^ 46) * (a7 ^ 7) * (a6 ^ 3) * b6
    - (152001589844901888 : R) * (h ^ 46) * (a7 ^ 7) * (a6 ^ 2) * a5 * b7
    - (454968978041733120 : R) * (h ^ 46) * (a7 ^ 7) * (a6 ^ 2) * a4 * b8
    - (508780348415410176 : R) * (h ^ 46) * (a7 ^ 7) * a6 * (a5 ^ 2) * b8
    - (20699594883072000 : R) * (h ^ 46) * (a7 ^ 6) * (a6 ^ 4) * b7
    - (275994598440960000 : R) * (h ^ 46) * (a7 ^ 6) * (a6 ^ 3) * a5 * b8
    - (663446114795520 : R) * (h ^ 40) * (a7 ^ 11) * a2
    + (43823306385653760 : R) * (h ^ 40) * (a7 ^ 10) * a6 * a3
    + (152868326190612480 : R) * (h ^ 40) * (a7 ^ 10) * a5 * a4
    + (252675349995847680 : R) * (h ^ 40) * (a7 ^ 9) * (a6 ^ 2) * a4
    + (282979346719703040 : R) * (h ^ 40) * (a7 ^ 9) * a6 * (a5 ^ 2)
    + (152696475824947200 : R) * (h ^ 40) * (a7 ^ 8) * (a6 ^ 3) * a5
    + (768996714479616 : R) * (h ^ 38) * (a7 ^ 11) * b4
    + (3412050868961280 : R) * (h ^ 38) * (a7 ^ 10) * a6 * b5
    + (2962781720543232 : R) * (h ^ 38) * (a7 ^ 10) * a5 * b6
    + (8808451320840192 : R) * (h ^ 38) * (a7 ^ 10) * a4 * b7
    + (10157717377253376 : R) * (h ^ 38) * (a7 ^ 10) * a3 * b8
    + (3768891784298496 : R) * (h ^ 38) * (a7 ^ 9) * (a6 ^ 2) * b6
    + (44595323904983040 : R) * (h ^ 38) * (a7 ^ 9) * a6 * a5 * b7
    + (125792993956331520 : R) * (h ^ 38) * (a7 ^ 9) * a6 * a4 * b8
    + (73669317022973952 : R) * (h ^ 38) * (a7 ^ 9) * (a5 ^ 2) * b8
    + (23770136259330048 : R) * (h ^ 38) * (a7 ^ 8) * (a6 ^ 3) * b7
    + (240501693081452544 : R) * (h ^ 38) * (a7 ^ 8) * (a6 ^ 2) * a5 * b8
    + (32527934816256000 : R) * (h ^ 38) * (a7 ^ 7) * (a6 ^ 4) * b8
    - (4365074238013440 : R) * (h ^ 32) * (a7 ^ 12) * a3
    - (68694650734510080 : R) * (h ^ 32) * (a7 ^ 11) * a6 * a4
    - (40613373573857280 : R) * (h ^ 32) * (a7 ^ 11) * (a5 ^ 2)
    - (132142486876323840 : R) * (h ^ 32) * (a7 ^ 10) * (a6 ^ 2) * a5
    - (17807196133785600 : R) * (h ^ 32) * (a7 ^ 9) * (a6 ^ 4)
    - (288847288074240 : R) * (h ^ 30) * (a7 ^ 12) * b5
    - (1034244096786432 : R) * (h ^ 30) * (a7 ^ 11) * a6 * b6
    - (4283511317987328 : R) * (h ^ 30) * (a7 ^ 11) * a5 * b7
    - (11268743611023360 : R) * (h ^ 30) * (a7 ^ 11) * a4 * b8
    - (9914088092073984 : R) * (h ^ 30) * (a7 ^ 10) * (a6 ^ 2) * b7
    - (65459788355469312 : R) * (h ^ 30) * (a7 ^ 10) * a6 * a5 * b8
    - (35332686436368384 : R) * (h ^ 30) * (a7 ^ 9) * (a6 ^ 3) * b8
    + (6010540554977280 : R) * (h ^ 24) * (a7 ^ 13) * a4
    + (35596366373191680 : R) * (h ^ 24) * (a7 ^ 12) * a6 * a5
    + (19192603811512320 : R) * (h ^ 24) * (a7 ^ 11) * (a6 ^ 3)
    + (86276850057216 : R) * (h ^ 22) * (a7 ^ 13) * b6
    + (1788937602859008 : R) * (h ^ 22) * (a7 ^ 12) * a6 * b7
    + (5716982573826048 : R) * (h ^ 22) * (a7 ^ 12) * a5 * b8
    + (13796111932194816 : R) * (h ^ 22) * (a7 ^ 11) * (a6 ^ 2) * b8
    - (3067351083417600 : R) * (h ^ 16) * (a7 ^ 14) * a5
    - (7421434014597120 : R) * (h ^ 16) * (a7 ^ 13) * (a6 ^ 2)
    - (117200903307264 : R) * (h ^ 14) * (a7 ^ 14) * b7
    - (2324605416505344 : R) * (h ^ 14) * (a7 ^ 13) * a6 * b8
    + (1237133280337920 : R) * (h ^ 8) * (a7 ^ 15) * a6
    + (143415376183296 : R) * (h ^ 6) * (a7 ^ 15) * b8
    - (75539381944320 : R) * (a7 ^ 17)

set_option maxHeartbeats 200000000 in
/-- Integer expansion of compact block `15` after the extra
`2^{34}` scale, on `λ = 0`. -/
def alignedSquareCompactBlock15Expansion810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    - (13781014859753717760 : R) * (h ^ 104) * a6 * a4 * a3 * a2
    - (2296835809958952960 : R) * (h ^ 104) * a6 * (a3 ^ 3)
    + (972777519512027136 : R) * (h ^ 102) * a6 * (a4 ^ 2) * b3
    + (2594073385365405696 : R) * (h ^ 102) * a6 * a4 * a3 * b4
    + (3242591731706757120 : R) * (h ^ 102) * a6 * a4 * a2 * b5
    + (3891110078048108544 : R) * (h ^ 102) * a6 * a4 * a1 * b6
    + (4539628424389459968 : R) * (h ^ 102) * a6 * a4 * a0 * b7
    + (1621295865853378560 : R) * (h ^ 102) * a6 * (a3 ^ 2) * b5
    + (3891110078048108544 : R) * (h ^ 102) * a6 * a3 * a2 * b6
    + (6029194001142251520 : R) * (h ^ 96) * (a7 ^ 2) * a4 * a3 * a2
    + (1004865666857041920 : R) * (h ^ 96) * (a7 ^ 2) * (a3 ^ 3)
    + (8613134287346073600 : R) * (h ^ 96) * a7 * a6 * a5 * a3 * a2
    + (6890507429876858880 : R) * (h ^ 96) * a7 * a6 * (a4 ^ 2) * a2
    + (8613134287346073600 : R) * (h ^ 96) * a7 * a6 * a4 * (a3 ^ 2)
    - (425590164786511872 : R) * (h ^ 94) * (a7 ^ 2) * (a4 ^ 2) * b3
    - (1134907106097364992 : R) * (h ^ 94) * (a7 ^ 2) * a4 * a3 * b4
    - (1418633882621706240 : R) * (h ^ 94) * (a7 ^ 2) * a4 * a2 * b5
    - (1702360659146047488 : R) * (h ^ 94) * (a7 ^ 2) * a4 * a1 * b6
    - (1986087435670388736 : R) * (h ^ 94) * (a7 ^ 2) * a4 * a0 * b7
    - (709316941310853120 : R) * (h ^ 94) * (a7 ^ 2) * (a3 ^ 2) * b5
    - (1702360659146047488 : R) * (h ^ 94) * (a7 ^ 2) * a3 * a2 * b6
    - (1215971899390033920 : R) * (h ^ 94) * a7 * a6 * a5 * a4 * b3
    - (1621295865853378560 : R) * (h ^ 94) * a7 * a6 * a5 * a3 * b4
    - (2026619832316723200 : R) * (h ^ 94) * a7 * a6 * a5 * a2 * b5
    - (2431943798780067840 : R) * (h ^ 94) * a7 * a6 * a5 * a1 * b6
    - (2837267765243412480 : R) * (h ^ 94) * a7 * a6 * a5 * a0 * b7
    - (1783425452438716416 : R) * (h ^ 94) * a7 * a6 * (a4 ^ 2) * b4
    - (4458563631096791040 : R) * (h ^ 94) * a7 * a6 * a4 * a3 * b5
    - (5350276357316149248 : R) * (h ^ 94) * a7 * a6 * a4 * a2 * b6
    - (3972174871340777472 : R) * (h ^ 94) * a7 * a6 * a4 * a1 * b7
    - (4539628424389459968 : R) * (h ^ 94) * a7 * a6 * a4 * a0 * b8
    - (2675138178658074624 : R) * (h ^ 94) * a7 * a6 * (a3 ^ 2) * b6
    - (3404721318292094976 : R) * (h ^ 94) * a7 * a6 * a3 * a2 * b7
    + (2127950823932559360 : R) * (h ^ 88) * (a7 ^ 3) * a6 * a4 * a0
    - (3768246250713907200 : R) * (h ^ 88) * (a7 ^ 3) * a5 * a3 * a2
    - (3014597000571125760 : R) * (h ^ 88) * (a7 ^ 3) * (a4 ^ 2) * a2
    - (3768246250713907200 : R) * (h ^ 88) * (a7 ^ 3) * a4 * (a3 ^ 2)
    - (3229925357754777600 : R) * (h ^ 88) * (a7 ^ 2) * (a6 ^ 2) * a3 * a2
    - (6459850715509555200 : R) * (h ^ 88) * (a7 ^ 2) * a6 * a5 * a4 * a2
    - (4306567143673036800 : R) * (h ^ 88) * (a7 ^ 2) * a6 * a5 * (a3 ^ 2)
    - (5598537286774947840 : R) * (h ^ 88) * (a7 ^ 2) * a6 * (a4 ^ 2) * a3
    + (531987705983139840 : R) * (h ^ 86) * (a7 ^ 3) * a5 * a4 * b3
    + (709316941310853120 : R) * (h ^ 86) * (a7 ^ 3) * a5 * a3 * b4
    + (886646176638566400 : R) * (h ^ 86) * (a7 ^ 3) * a5 * a2 * b5
    + (1063975411966279680 : R) * (h ^ 86) * (a7 ^ 3) * a5 * a1 * b6
    + (1241304647293992960 : R) * (h ^ 86) * (a7 ^ 3) * a5 * a0 * b7
    + (780248635441938432 : R) * (h ^ 86) * (a7 ^ 3) * (a4 ^ 2) * b4
    + (1950621588604846080 : R) * (h ^ 86) * (a7 ^ 3) * a4 * a3 * b5
    + (2340745906325815296 : R) * (h ^ 86) * (a7 ^ 3) * a4 * a2 * b6
    + (1737826506211590144 : R) * (h ^ 86) * (a7 ^ 3) * a4 * a1 * b7
    + (1986087435670388736 : R) * (h ^ 86) * (a7 ^ 3) * a4 * a0 * b8
    + (1170372953162907648 : R) * (h ^ 86) * (a7 ^ 3) * (a3 ^ 2) * b6
    + (1489565576752791552 : R) * (h ^ 86) * (a7 ^ 3) * a3 * a2 * b7
    + (455989462271262720 : R) * (h ^ 86) * (a7 ^ 2) * (a6 ^ 2) * a4 * b3
    + (607985949695016960 : R) * (h ^ 86) * (a7 ^ 2) * (a6 ^ 2) * a3 * b4
    + (759982437118771200 : R) * (h ^ 86) * (a7 ^ 2) * (a6 ^ 2) * a2 * b5
    + (911978924542525440 : R) * (h ^ 86) * (a7 ^ 2) * (a6 ^ 2) * a1 * b6
    + (1063975411966279680 : R) * (h ^ 86) * (a7 ^ 2) * (a6 ^ 2) * a0 * b7
    + (379991218559385600 : R) * (h ^ 86) * (a7 ^ 2) * a6 * (a5 ^ 2) * b3
    + (1823957849085050880 : R) * (h ^ 86) * (a7 ^ 2) * a6 * a5 * a4 * b4
    + (2279947311356313600 : R) * (h ^ 86) * (a7 ^ 2) * a6 * a5 * a3 * b5
    + (2735936773627576320 : R) * (h ^ 86) * (a7 ^ 2) * a6 * a5 * a2 * b6
    + (2482609294587985920 : R) * (h ^ 86) * (a7 ^ 2) * a6 * a5 * a1 * b7
    + (2837267765243412480 : R) * (h ^ 86) * (a7 ^ 2) * a6 * a5 * a0 * b8
    + (1671961361661296640 : R) * (h ^ 86) * (a7 ^ 2) * a6 * (a4 ^ 2) * b5
    + (4012707267987111936 : R) * (h ^ 86) * (a7 ^ 2) * a6 * a4 * a3 * b6
    + (3688448094816436224 : R) * (h ^ 86) * (a7 ^ 2) * a6 * a4 * a2 * b7
    + (2269814212194729984 : R) * (h ^ 86) * (a7 ^ 2) * a6 * a4 * a1 * b8
    + (1808758200342675456 : R) * (h ^ 86) * (a7 ^ 2) * a6 * (a3 ^ 2) * b7
    + (1702360659146047488 : R) * (h ^ 86) * (a7 ^ 2) * a6 * a3 * a2 * b8
    - (930978485470494720 : R) * (h ^ 80) * (a7 ^ 5) * a4 * a0
    - (1329969264957849600 : R) * (h ^ 80) * (a7 ^ 4) * a6 * a5 * a0
    - (864480022222602240 : R) * (h ^ 80) * (a7 ^ 4) * a6 * a4 * a1
    + (1521152346795540480 : R) * (h ^ 80) * (a7 ^ 4) * a6 * a3 * a2
    + (2826184688035430400 : R) * (h ^ 80) * (a7 ^ 4) * a5 * a4 * a2
    + (1884123125356953600 : R) * (h ^ 80) * (a7 ^ 4) * a5 * (a3 ^ 2)
    + (2449360062964039680 : R) * (h ^ 80) * (a7 ^ 4) * (a4 ^ 2) * a3
    + (2153283571836518400 : R) * (h ^ 80) * (a7 ^ 3) * (a6 ^ 2) * a4 * a2
    + (1480382455637606400 : R) * (h ^ 80) * (a7 ^ 3) * (a6 ^ 2) * (a3 ^ 2)
    + (1345802232397824000 : R) * (h ^ 80) * (a7 ^ 3) * a6 * (a5 ^ 2) * a2
    + (4575727590152601600 : R) * (h ^ 80) * (a7 ^ 3) * a6 * a5 * a4 * a3
    + (933089547795824640 : R) * (h ^ 80) * (a7 ^ 3) * a6 * (a4 ^ 3)
    - (299243084615516160 : R) * (h ^ 78) * (a7 ^ 4) * a6 * a4 * b3
    - (398990779487354880 : R) * (h ^ 78) * (a7 ^ 4) * a6 * a3 * b4
    - (498738474359193600 : R) * (h ^ 78) * (a7 ^ 4) * a6 * a2 * b5
    - (598486169231032320 : R) * (h ^ 78) * (a7 ^ 4) * a6 * a1 * b6
    - (698233864102871040 : R) * (h ^ 78) * (a7 ^ 4) * a6 * a0 * b7
    - (166246158119731200 : R) * (h ^ 78) * (a7 ^ 4) * (a5 ^ 2) * b3
    - (797981558974709760 : R) * (h ^ 78) * (a7 ^ 4) * a5 * a4 * b4
    - (997476948718387200 : R) * (h ^ 78) * (a7 ^ 4) * a5 * a3 * b5
    - (1196972338462064640 : R) * (h ^ 78) * (a7 ^ 4) * a5 * a2 * b6
    - (1086141566382243840 : R) * (h ^ 78) * (a7 ^ 4) * a5 * a1 * b7
    - (1241304647293992960 : R) * (h ^ 78) * (a7 ^ 4) * a5 * a0 * b8
    - (731483095726817280 : R) * (h ^ 78) * (a7 ^ 4) * (a4 ^ 2) * b5
    - (1755559429744361472 : R) * (h ^ 78) * (a7 ^ 4) * a4 * a3 * b6
    - (1613696041482190848 : R) * (h ^ 78) * (a7 ^ 4) * a4 * a2 * b7
    - (993043717835194368 : R) * (h ^ 78) * (a7 ^ 4) * a4 * a1 * b8
    - (791331712649920512 : R) * (h ^ 78) * (a7 ^ 4) * (a3 ^ 2) * b7
    - (744782788376395776 : R) * (h ^ 78) * (a7 ^ 4) * a3 * a2 * b8
    - (284993413919539200 : R) * (h ^ 78) * (a7 ^ 3) * (a6 ^ 2) * a5 * b3
    - (633318697598976000 : R) * (h ^ 78) * (a7 ^ 3) * (a6 ^ 2) * a4 * b4
    - (791648371998720000 : R) * (h ^ 78) * (a7 ^ 3) * (a6 ^ 2) * a3 * b5
    - (949978046398464000 : R) * (h ^ 78) * (a7 ^ 3) * (a6 ^ 2) * a2 * b6
    - (930978485470494720 : R) * (h ^ 78) * (a7 ^ 3) * (a6 ^ 2) * a1 * b7
    - (1063975411966279680 : R) * (h ^ 78) * (a7 ^ 3) * (a6 ^ 2) * a0 * b8
    - (443323088319283200 : R) * (h ^ 78) * (a7 ^ 3) * a6 * (a5 ^ 2) * b4
    - (1456633004477644800 : R) * (h ^ 78) * (a7 ^ 3) * a6 * a5 * a4 * b5
    - (1747959605373173760 : R) * (h ^ 78) * (a7 ^ 3) * a6 * a5 * a3 * b6
    - (1773292353277132800 : R) * (h ^ 78) * (a7 ^ 3) * a6 * a5 * a2 * b7
    - (1418633882621706240 : R) * (h ^ 78) * (a7 ^ 3) * a6 * a5 * a1 * b8
    - (1086774885079842816 : R) * (h ^ 78) * (a7 ^ 3) * a6 * (a4 ^ 2) * b6
    - (2234348365129187328 : R) * (h ^ 78) * (a7 ^ 3) * a6 * a4 * a3 * b7
    - (1702360659146047488 : R) * (h ^ 78) * (a7 ^ 3) * a6 * a4 * a2 * b8
    - (815714482507481088 : R) * (h ^ 78) * (a7 ^ 3) * a6 * (a3 ^ 2) * b8
    + (581861553419059200 : R) * (h ^ 72) * (a7 ^ 6) * a5 * a0
    + (378210009722388480 : R) * (h ^ 72) * (a7 ^ 6) * a4 * a1
    - (47276251215298560 : R) * (h ^ 72) * (a7 ^ 6) * a3 * a2
    + (498738474359193600 : R) * (h ^ 72) * (a7 ^ 5) * (a6 ^ 2) * a0
    + (540300013889126400 : R) * (h ^ 72) * (a7 ^ 5) * a6 * a5 * a1
    - (807679251531694080 : R) * (h ^ 72) * (a7 ^ 5) * a6 * a4 * a2
    - (685419056081141760 : R) * (h ^ 72) * (a7 ^ 5) * a6 * (a3 ^ 2)
    - (588788476674048000 : R) * (h ^ 72) * (a7 ^ 5) * (a5 ^ 2) * a2
    - (2001880820691763200 : R) * (h ^ 72) * (a7 ^ 5) * a5 * a4 * a3
    - (408226677160673280 : R) * (h ^ 72) * (a7 ^ 5) * (a4 ^ 3)
    - (841126395248640000 : R) * (h ^ 72) * (a7 ^ 4) * (a6 ^ 2) * a5 * a2
    - (1429914871922688000 : R) * (h ^ 72) * (a7 ^ 4) * (a6 ^ 2) * a4 * a3
    - (841126395248640000 : R) * (h ^ 72) * (a7 ^ 4) * a6 * (a5 ^ 2) * a3
    - (1009351674298368000 : R) * (h ^ 72) * (a7 ^ 4) * a6 * a5 * (a4 ^ 2)
    + (43639616506429440 : R) * (h ^ 70) * (a7 ^ 6) * a4 * b3
    + (58186155341905920 : R) * (h ^ 70) * (a7 ^ 6) * a3 * b4
    + (72732694177382400 : R) * (h ^ 70) * (a7 ^ 6) * a2 * b5
    + (87279233012858880 : R) * (h ^ 70) * (a7 ^ 6) * a1 * b6
    + (101825771848335360 : R) * (h ^ 70) * (a7 ^ 6) * a0 * b7
    + (187026927884697600 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a5 * b3
    + (411182164416135168 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a4 * b4
    + (513977705520168960 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a3 * b5
    + (616773246624202752 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a2 * b6
    + (610954631090012160 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a1 * b7
    + (698233864102871040 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a0 * b8
    + (193953851139686400 : R) * (h ^ 70) * (a7 ^ 5) * (a5 ^ 2) * b4
    + (637276939458969600 : R) * (h ^ 70) * (a7 ^ 5) * a5 * a4 * b5
    + (764732327350763520 : R) * (h ^ 70) * (a7 ^ 5) * a5 * a3 * b6
    + (775815404558745600 : R) * (h ^ 70) * (a7 ^ 5) * a5 * a2 * b7
    + (620652323646996480 : R) * (h ^ 70) * (a7 ^ 5) * a5 * a1 * b8
    + (475464012222431232 : R) * (h ^ 70) * (a7 ^ 5) * (a4 ^ 2) * b6
    + (977527409744019456 : R) * (h ^ 70) * (a7 ^ 5) * a4 * a3 * b7
    + (744782788376395776 : R) * (h ^ 70) * (a7 ^ 5) * a4 * a2 * b8
    + (356875086097022976 : R) * (h ^ 70) * (a7 ^ 5) * (a3 ^ 2) * b8
    + (53436265109913600 : R) * (h ^ 70) * (a7 ^ 4) * (a6 ^ 3) * b3
    + (300826381359513600 : R) * (h ^ 70) * (a7 ^ 4) * (a6 ^ 2) * a5 * b4
    + (471030781339238400 : R) * (h ^ 70) * (a7 ^ 4) * (a6 ^ 2) * a4 * b5
    + (565236937607086080 : R) * (h ^ 70) * (a7 ^ 4) * (a6 ^ 2) * a3 * b6
    + (598486169231032320 : R) * (h ^ 70) * (a7 ^ 4) * (a6 ^ 2) * a2 * b7
    + (531987705983139840 : R) * (h ^ 70) * (a7 ^ 4) * (a6 ^ 2) * a1 * b8
    + (296868139499520000 : R) * (h ^ 70) * (a7 ^ 4) * a6 * (a5 ^ 2) * b5
    + (831230790598656000 : R) * (h ^ 70) * (a7 ^ 4) * a6 * a5 * a4 * b6
    + (897729253846548480 : R) * (h ^ 70) * (a7 ^ 4) * a6 * a5 * a3 * b7
    + (797981558974709760 : R) * (h ^ 70) * (a7 ^ 4) * a6 * a5 * a2 * b8
    + (517025551752364032 : R) * (h ^ 70) * (a7 ^ 4) * a6 * (a4 ^ 2) * b7
    + (922112023704109056 : R) * (h ^ 70) * (a7 ^ 4) * a6 * a4 * a3 * b8
    - (327297123798220800 : R) * (h ^ 64) * (a7 ^ 7) * a6 * a0
    - (236381256076492800 : R) * (h ^ 64) * (a7 ^ 7) * a5 * a1
    - (58792261126717440 : R) * (h ^ 64) * (a7 ^ 7) * a4 * a2
    + (16516382636113920 : R) * (h ^ 64) * (a7 ^ 7) * (a3 ^ 2)
    - (202612505208422400 : R) * (h ^ 64) * (a7 ^ 6) * (a6 ^ 2) * a1
    + (267119478020505600 : R) * (h ^ 64) * (a7 ^ 6) * a6 * a5 * a2
    + (615890063909191680 : R) * (h ^ 64) * (a7 ^ 6) * a6 * a4 * a3
    + (367992797921280000 : R) * (h ^ 64) * (a7 ^ 6) * (a5 ^ 2) * a3
    + (441591357505536000 : R) * (h ^ 64) * (a7 ^ 6) * a5 * (a4 ^ 2)
    + (126168959287296000 : R) * (h ^ 64) * (a7 ^ 5) * (a6 ^ 3) * a2
    + (494161757208576000 : R) * (h ^ 64) * (a7 ^ 5) * (a6 ^ 2) * a5 * a3
    + (294394238337024000 : R) * (h ^ 64) * (a7 ^ 5) * (a6 ^ 2) * (a4 ^ 2)
    + (336450558099456000 : R) * (h ^ 64) * (a7 ^ 5) * a6 * (a5 ^ 2) * a4
    - (27274760316518400 : R) * (h ^ 62) * (a7 ^ 7) * a5 * b3
    - (58671039969755136 : R) * (h ^ 62) * (a7 ^ 7) * a4 * b4
    - (73338799962193920 : R) * (h ^ 62) * (a7 ^ 7) * a3 * b5
    - (88006559954632704 : R) * (h ^ 62) * (a7 ^ 7) * a2 * b6
    - (89097550367293440 : R) * (h ^ 62) * (a7 ^ 7) * a1 * b7
    - (101825771848335360 : R) * (h ^ 62) * (a7 ^ 7) * a0 * b8
    - (46756731971174400 : R) * (h ^ 62) * (a7 ^ 6) * (a6 ^ 2) * b3
    - (194646543465185280 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a5 * b4
    - (302706546243010560 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a4 * b5
    - (363247855491612672 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a3 * b6
    - (386937933023674368 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a2 * b7
    - (349116932051435520 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a1 * b8
    - (129879811031040000 : R) * (h ^ 62) * (a7 ^ 6) * (a5 ^ 2) * b5
    - (363663470886912000 : R) * (h ^ 62) * (a7 ^ 6) * a5 * a4 * b6
    - (392756548557864960 : R) * (h ^ 62) * (a7 ^ 6) * a5 * a3 * b7
    - (349116932051435520 : R) * (h ^ 62) * (a7 ^ 6) * a5 * a2 * b8
    - (226198678891659264 : R) * (h ^ 62) * (a7 ^ 6) * (a4 ^ 2) * b7
    - (403424010370547712 : R) * (h ^ 62) * (a7 ^ 6) * a4 * a3 * b8
    - (50467583714918400 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 3) * b4
    - (185542587187200000 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 2) * a5 * b5
    - (251862929551392768 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 2) * a4 * b6
    - (278462314850549760 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 2) * a3 * b7
    - (265993852991569920 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 2) * a2 * b8
    - (148434069749760000 : R) * (h ^ 62) * (a7 ^ 5) * a6 * (a5 ^ 2) * b6
    - (364494701677510656 : R) * (h ^ 62) * (a7 ^ 5) * a6 * a5 * a4 * b7
    - (354658470655426560 : R) * (h ^ 62) * (a7 ^ 5) * a6 * a5 * a3 * b8
    - (195616312720883712 : R) * (h ^ 62) * (a7 ^ 5) * a6 * (a4 ^ 2) * b8
    + (47730830553907200 : R) * (h ^ 56) * (a7 ^ 9) * a0
    + (132964456543027200 : R) * (h ^ 56) * (a7 ^ 8) * a6 * a1
    + (44132077456588800 : R) * (h ^ 56) * (a7 ^ 8) * a5 * a2
    + (4242740493680640 : R) * (h ^ 56) * (a7 ^ 8) * a4 * a3
    - (15260877796147200 : R) * (h ^ 56) * (a7 ^ 7) * (a6 ^ 2) * a2
    - (200447841691238400 : R) * (h ^ 56) * (a7 ^ 7) * a6 * a5 * a3
    - (125606146772828160 : R) * (h ^ 56) * (a7 ^ 7) * a6 * (a4 ^ 2)
    - (147197119168512000 : R) * (h ^ 56) * (a7 ^ 7) * (a5 ^ 2) * a4
    - (69655779606528000 : R) * (h ^ 56) * (a7 ^ 6) * (a6 ^ 3) * a3
    - (186624918945792000 : R) * (h ^ 56) * (a7 ^ 6) * (a6 ^ 2) * a5 * a4
    - (35046933135360000 : R) * (h ^ 56) * (a7 ^ 6) * a6 * (a5 ^ 3)
    + (12785043898368000 : R) * (h ^ 54) * (a7 ^ 8) * a6 * b3
    + (27577813208924160 : R) * (h ^ 54) * (a7 ^ 8) * a5 * b4
    + (42275878490603520 : R) * (h ^ 54) * (a7 ^ 8) * a4 * b5
    + (50731054188724224 : R) * (h ^ 54) * (a7 ^ 8) * a3 * b6
    + (54731352368480256 : R) * (h ^ 54) * (a7 ^ 8) * a2 * b7
    + (50912885924167680 : R) * (h ^ 54) * (a7 ^ 8) * a1 * b8
    + (43120097262305280 : R) * (h ^ 54) * (a7 ^ 7) * (a6 ^ 2) * b4
    + (118623560741683200 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a5 * b5
    + (160308795329740800 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a4 * b6
    + (177831437263699968 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a3 * b7
    + (171649158258622464 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a2 * b8
    + (64939905515520000 : R) * (h ^ 54) * (a7 ^ 7) * (a5 ^ 2) * b6
    + (159466431983910912 : R) * (h ^ 54) * (a7 ^ 7) * a5 * a4 * b7
    + (155163080911749120 : R) * (h ^ 54) * (a7 ^ 7) * a5 * a3 * b8
    + (85582136815386624 : R) * (h ^ 54) * (a7 ^ 7) * (a4 ^ 2) * b8
    + (28449863368704000 : R) * (h ^ 54) * (a7 ^ 6) * (a6 ^ 3) * b5
    + (86537062664110080 : R) * (h ^ 54) * (a7 ^ 6) * (a6 ^ 2) * a5 * b6
    + (105497041173479424 : R) * (h ^ 54) * (a7 ^ 6) * (a6 ^ 2) * a4 * b7
    + (107367310452326400 : R) * (h ^ 54) * (a7 ^ 6) * (a6 ^ 2) * a3 * b8
    + (59614833263247360 : R) * (h ^ 54) * (a7 ^ 6) * a6 * (a5 ^ 2) * b7
    + (131057387984388096 : R) * (h ^ 54) * (a7 ^ 6) * a6 * a5 * a4 * b8
    - (19390649912524800 : R) * (h ^ 48) * (a7 ^ 10) * a1
    - (31223918320680960 : R) * (h ^ 48) * (a7 ^ 9) * a6 * a2
    - (6889718100787200 : R) * (h ^ 48) * (a7 ^ 9) * a5 * a3
    - (1396207968583680 : R) * (h ^ 48) * (a7 ^ 9) * (a4 ^ 2)
    + (23489981448192000 : R) * (h ^ 48) * (a7 ^ 8) * (a6 ^ 2) * a3
    + (77540179920814080 : R) * (h ^ 48) * (a7 ^ 8) * a6 * a5 * a4
    + (15333033246720000 : R) * (h ^ 48) * (a7 ^ 8) * (a5 ^ 3)
    + (24970939858944000 : R) * (h ^ 48) * (a7 ^ 7) * (a6 ^ 3) * a4
    + (27928024842240000 : R) * (h ^ 48) * (a7 ^ 7) * (a6 ^ 2) * (a5 ^ 2)
    - (1118691341107200 : R) * (h ^ 46) * (a7 ^ 10) * b3
    - (11392894673879040 : R) * (h ^ 46) * (a7 ^ 9) * a6 * b4
    - (16383796995686400 : R) * (h ^ 46) * (a7 ^ 9) * a5 * b5
    - (21926959097315328 : R) * (h ^ 46) * (a7 ^ 9) * a4 * b6
    - (24501826351005696 : R) * (h ^ 46) * (a7 ^ 9) * a3 * b7
    - (24183620813979648 : R) * (h ^ 46) * (a7 ^ 9) * a2 * b8
    - (23824827836006400 : R) * (h ^ 46) * (a7 ^ 8) * (a6 ^ 2) * b5
    - (54751298196602880 : R) * (h ^ 46) * (a7 ^ 8) * a6 * a5 * b6
    - (66675695073361920 : R) * (h ^ 46) * (a7 ^ 8) * a6 * a4 * b7
    - (68308121948258304 : R) * (h ^ 46) * (a7 ^ 8) * a6 * a3 * b8
    - (26081489552670720 : R) * (h ^ 46) * (a7 ^ 8) * (a5 ^ 2) * b7
    - (57337607243169792 : R) * (h ^ 46) * (a7 ^ 8) * a5 * a4 * b8
    - (12320027789230080 : R) * (h ^ 46) * (a7 ^ 7) * (a6 ^ 3) * b6
    - (33011118637056000 : R) * (h ^ 46) * (a7 ^ 7) * (a6 ^ 2) * a5 * b7
    - (36781962483990528 : R) * (h ^ 46) * (a7 ^ 7) * (a6 ^ 2) * a4 * b8
    - (20217957250498560 : R) * (h ^ 46) * (a7 ^ 7) * a6 * (a5 ^ 2) * b8
    + (6016073434398720 : R) * (h ^ 40) * (a7 ^ 11) * a2
    + (7182708690124800 : R) * (h ^ 40) * (a7 ^ 10) * a6 * a3
    + (1797347176611840 : R) * (h ^ 40) * (a7 ^ 10) * a5 * a4
    - (9302689783480320 : R) * (h ^ 40) * (a7 ^ 9) * (a6 ^ 2) * a4
    - (11489386482892800 : R) * (h ^ 40) * (a7 ^ 9) * a6 * (a5 ^ 2)
    - (7187359334400000 : R) * (h ^ 40) * (a7 ^ 8) * (a6 ^ 3) * a5
    + (957102591836160 : R) * (h ^ 38) * (a7 ^ 11) * b4
    + (6110185563095040 : R) * (h ^ 38) * (a7 ^ 10) * a6 * b5
    + (7389958310461440 : R) * (h ^ 38) * (a7 ^ 10) * a5 * b6
    + (8977823557484544 : R) * (h ^ 38) * (a7 ^ 10) * a4 * b7
    + (9334029086097408 : R) * (h ^ 38) * (a7 ^ 10) * a3 * b8
    + (10141351941242880 : R) * (h ^ 38) * (a7 ^ 9) * (a6 ^ 2) * b6
    + (20719043031859200 : R) * (h ^ 38) * (a7 ^ 9) * a6 * a5 * b7
    + (23133488425205760 : R) * (h ^ 38) * (a7 ^ 9) * a6 * a4 * b8
    + (8845356297093120 : R) * (h ^ 38) * (a7 ^ 9) * (a5 ^ 2) * b8
    + (4442295411671040 : R) * (h ^ 38) * (a7 ^ 8) * (a6 ^ 3) * b7
    + (10790847633162240 : R) * (h ^ 38) * (a7 ^ 8) * (a6 ^ 2) * a5 * b8
    - (1805573003673600 : R) * (h ^ 32) * (a7 ^ 12) * a3
    - (1926465973125120 : R) * (h ^ 32) * (a7 ^ 11) * a6 * a4
    - (318991918694400 : R) * (h ^ 32) * (a7 ^ 11) * (a5 ^ 2)
    + (2674044960768000 : R) * (h ^ 32) * (a7 ^ 10) * (a6 ^ 2) * a5
    + (598946611200000 : R) * (h ^ 32) * (a7 ^ 9) * (a6 ^ 4)
    - (495383457300480 : R) * (h ^ 30) * (a7 ^ 12) * b5
    - (2533861254758400 : R) * (h ^ 30) * (a7 ^ 11) * a6 * b6
    - (2746046899814400 : R) * (h ^ 30) * (a7 ^ 11) * a5 * b7
    - (3080603679326208 : R) * (h ^ 30) * (a7 ^ 11) * a4 * b8
    - (3607399067811840 : R) * (h ^ 30) * (a7 ^ 10) * (a6 ^ 2) * b7
    - (6732949110128640 : R) * (h ^ 30) * (a7 ^ 10) * a6 * a5 * b8
    - (1392825681838080 : R) * (h ^ 30) * (a7 ^ 9) * (a6 ^ 3) * b8
    + (532349473259520 : R) * (h ^ 24) * (a7 ^ 13) * a4
    + (539263343001600 : R) * (h ^ 24) * (a7 ^ 12) * a6 * a5
    - (194835067699200 : R) * (h ^ 24) * (a7 ^ 11) * (a6 ^ 3)
    + (199128168529920 : R) * (h ^ 22) * (a7 ^ 13) * b6
    + (882467678453760 : R) * (h ^ 22) * (a7 ^ 12) * a6 * b7
    + (880229555896320 : R) * (h ^ 22) * (a7 ^ 12) * a5 * b8
    + (1119388937748480 : R) * (h ^ 22) * (a7 ^ 11) * (a6 ^ 2) * b8
    - (145885475635200 : R) * (h ^ 16) * (a7 ^ 14) * a5
    - (112857396019200 : R) * (h ^ 16) * (a7 ^ 13) * (a6 ^ 2)
    - (67599740436480 : R) * (h ^ 14) * (a7 ^ 14) * b7
    - (269351575879680 : R) * (h ^ 14) * (a7 ^ 13) * a6 * b8
    + (45712680222720 : R) * (h ^ 8) * (a7 ^ 15) * a6
    + (20218824622080 : R) * (h ^ 6) * (a7 ^ 15) * b8
    - (4025371607040 : R) * (a7 ^ 17)

set_option maxHeartbeats 200000000 in
/-- Integer expansion of compact block `16` after the extra
`2^{34}` scale, on `λ = 0`. -/
def alignedSquareCompactBlock16Expansion810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    (6485183463413514240 : R) * (h ^ 112) * a6 * a1 * a0
    - (576460752303423488 : R) * (h ^ 110) * a6 * a2 * b1
    - (1152921504606846976 : R) * (h ^ 110) * a6 * a1 * b2
    - (1729382256910270464 : R) * (h ^ 110) * a6 * a0 * b3
    - (2837267765243412480 : R) * (h ^ 104) * (a7 ^ 2) * a1 * a0
    - (1621295865853378560 : R) * (h ^ 104) * a7 * a6 * a2 * a0
    - (810647932926689280 : R) * (h ^ 104) * a7 * a6 * (a1 ^ 2)
    + (252201579132747776 : R) * (h ^ 102) * (a7 ^ 2) * a2 * b1
    + (504403158265495552 : R) * (h ^ 102) * (a7 ^ 2) * a1 * b2
    + (756604737398243328 : R) * (h ^ 102) * (a7 ^ 2) * a0 * b3
    + (216172782113783808 : R) * (h ^ 102) * a7 * a6 * a3 * b1
    + (432345564227567616 : R) * (h ^ 102) * a7 * a6 * a2 * b2
    + (648518346341351424 : R) * (h ^ 102) * a7 * a6 * a1 * b3
    + (864691128455135232 : R) * (h ^ 102) * a7 * a6 * a0 * b4
    + (4539628424389459968 : R) * (h ^ 102) * a6 * a3 * a1 * b7
    + (5188146770730811392 : R) * (h ^ 102) * a6 * a3 * a0 * b8
    + (2269814212194729984 : R) * (h ^ 102) * a6 * (a2 ^ 2) * b7
    + (5188146770730811392 : R) * (h ^ 102) * a6 * a2 * a1 * b8
    + (709316941310853120 : R) * (h ^ 96) * (a7 ^ 3) * a2 * a0
    + (354658470655426560 : R) * (h ^ 96) * (a7 ^ 3) * (a1 ^ 2)
    - (3343922723322593280 : R) * (h ^ 96) * (a7 ^ 2) * a6 * a3 * a0
    - (3343922723322593280 : R) * (h ^ 96) * (a7 ^ 2) * a6 * a2 * a1
    - (94575592174780416 : R) * (h ^ 94) * (a7 ^ 3) * a3 * b1
    - (189151184349560832 : R) * (h ^ 94) * (a7 ^ 3) * a2 * b2
    - (283726776524341248 : R) * (h ^ 94) * (a7 ^ 3) * a1 * b3
    - (378302368699121664 : R) * (h ^ 94) * (a7 ^ 3) * a0 * b4
    - (54043195528445952 : R) * (h ^ 94) * (a7 ^ 2) * a6 * a4 * b1
    - (108086391056891904 : R) * (h ^ 94) * (a7 ^ 2) * a6 * a3 * b2
    - (162129586585337856 : R) * (h ^ 94) * (a7 ^ 2) * a6 * a2 * b3
    - (216172782113783808 : R) * (h ^ 94) * (a7 ^ 2) * a6 * a1 * b4
    - (270215977642229760 : R) * (h ^ 94) * (a7 ^ 2) * a6 * a0 * b5
    - (1986087435670388736 : R) * (h ^ 94) * (a7 ^ 2) * a3 * a1 * b7
    - (2269814212194729984 : R) * (h ^ 94) * (a7 ^ 2) * a3 * a0 * b8
    - (993043717835194368 : R) * (h ^ 94) * (a7 ^ 2) * (a2 ^ 2) * b7
    - (2269814212194729984 : R) * (h ^ 94) * (a7 ^ 2) * a2 * a1 * b8
    - (2269814212194729984 : R) * (h ^ 94) * a7 * a6 * a4 * a1 * b7
    - (2594073385365405696 : R) * (h ^ 94) * a7 * a6 * a4 * a0 * b8
    - (2837267765243412480 : R) * (h ^ 94) * a7 * a6 * a3 * a2 * b7
    - (7133701809754865664 : R) * (h ^ 94) * a7 * a6 * a3 * a1 * b8
    - (3566850904877432832 : R) * (h ^ 94) * a7 * a6 * (a2 ^ 2) * b8
    + (1462966191453634560 : R) * (h ^ 88) * (a7 ^ 4) * a3 * a0
    + (1462966191453634560 : R) * (h ^ 88) * (a7 ^ 4) * a2 * a1
    + (1773292353277132800 : R) * (h ^ 88) * (a7 ^ 3) * a6 * a4 * a0
    + (3901243177209692160 : R) * (h ^ 88) * (a7 ^ 3) * a6 * a3 * a1
    + (1950621588604846080 : R) * (h ^ 88) * (a7 ^ 3) * a6 * (a2 ^ 2)
    + (23643898043695104 : R) * (h ^ 86) * (a7 ^ 4) * a4 * b1
    + (47287796087390208 : R) * (h ^ 86) * (a7 ^ 4) * a3 * b2
    + (70931694131085312 : R) * (h ^ 86) * (a7 ^ 4) * a2 * b3
    + (94575592174780416 : R) * (h ^ 86) * (a7 ^ 4) * a1 * b4
    + (118219490218475520 : R) * (h ^ 86) * (a7 ^ 4) * a0 * b5
    + (11258999068426240 : R) * (h ^ 86) * (a7 ^ 3) * a6 * a5 * b1
    + (22517998136852480 : R) * (h ^ 86) * (a7 ^ 3) * a6 * a4 * b2
    + (33776997205278720 : R) * (h ^ 86) * (a7 ^ 3) * a6 * a3 * b3
    + (45035996273704960 : R) * (h ^ 86) * (a7 ^ 3) * a6 * a2 * b4
    + (56294995342131200 : R) * (h ^ 86) * (a7 ^ 3) * a6 * a1 * b5
    + (67553994410557440 : R) * (h ^ 86) * (a7 ^ 3) * a6 * a0 * b6
    + (993043717835194368 : R) * (h ^ 86) * (a7 ^ 3) * a4 * a1 * b7
    + (1134907106097364992 : R) * (h ^ 86) * (a7 ^ 3) * a4 * a0 * b8
    + (1241304647293992960 : R) * (h ^ 86) * (a7 ^ 3) * a3 * a2 * b7
    + (3120994541767753728 : R) * (h ^ 86) * (a7 ^ 3) * a3 * a1 * b8
    + (1560497270883876864 : R) * (h ^ 86) * (a7 ^ 3) * (a2 ^ 2) * b8
    + (709316941310853120 : R) * (h ^ 86) * (a7 ^ 2) * a6 * a5 * a1 * b7
    + (810647932926689280 : R) * (h ^ 86) * (a7 ^ 2) * a6 * a5 * a0 * b8
    + (993043717835194368 : R) * (h ^ 86) * (a7 ^ 2) * a6 * a4 * a2 * b7
    + (3080462145121419264 : R) * (h ^ 86) * (a7 ^ 2) * a6 * a4 * a1 * b8
    + (531987705983139840 : R) * (h ^ 86) * (a7 ^ 2) * a6 * (a3 ^ 2) * b7
    + (3647915698170101760 : R) * (h ^ 86) * (a7 ^ 2) * a6 * a3 * a2 * b8
    + (287104476244869120 : R) * (h ^ 86) * (a5 ^ 5) * b8
    - (775815404558745600 : R) * (h ^ 80) * (a7 ^ 5) * a4 * a0
    - (1706793890029240320 : R) * (h ^ 80) * (a7 ^ 5) * a3 * a1
    - (853396945014620160 : R) * (h ^ 80) * (a7 ^ 5) * (a2 ^ 2)
    - (562070344119091200 : R) * (h ^ 80) * (a7 ^ 4) * a6 * a5 * a0
    - (1626045756085370880 : R) * (h ^ 80) * (a7 ^ 4) * a6 * a4 * a1
    - (1892039609076940800 : R) * (h ^ 80) * (a7 ^ 4) * a6 * a3 * a2
    - (201870334859673600 : R) * (h ^ 80) * (a7 ^ 2) * (a5 ^ 5)
    - (4925812092436480 : R) * (h ^ 78) * (a7 ^ 5) * a5 * b1
    - (9851624184872960 : R) * (h ^ 78) * (a7 ^ 5) * a4 * b2
    - (14777436277309440 : R) * (h ^ 78) * (a7 ^ 5) * a3 * b3
    - (19703248369745920 : R) * (h ^ 78) * (a7 ^ 5) * a2 * b4
    - (24629060462182400 : R) * (h ^ 78) * (a7 ^ 5) * a1 * b5
    - (29554872554618880 : R) * (h ^ 78) * (a7 ^ 5) * a0 * b6
    - (2111062325329920 : R) * (h ^ 78) * (a7 ^ 4) * (a6 ^ 2) * b1
    - (4222124650659840 : R) * (h ^ 78) * (a7 ^ 4) * a6 * a5 * b2
    - (6333186975989760 : R) * (h ^ 78) * (a7 ^ 4) * a6 * a4 * b3
    - (8444249301319680 : R) * (h ^ 78) * (a7 ^ 4) * a6 * a3 * b4
    - (10555311626649600 : R) * (h ^ 78) * (a7 ^ 4) * a6 * a2 * b5
    - (12666373951979520 : R) * (h ^ 78) * (a7 ^ 4) * a6 * a1 * b6
    - (14777436277309440 : R) * (h ^ 78) * (a7 ^ 4) * a6 * a0 * b7
    - (310326161823498240 : R) * (h ^ 78) * (a7 ^ 4) * a5 * a1 * b7
    - (354658470655426560 : R) * (h ^ 78) * (a7 ^ 4) * a5 * a0 * b8
    - (434456626552897536 : R) * (h ^ 78) * (a7 ^ 4) * a4 * a2 * b7
    - (1347702188490620928 : R) * (h ^ 78) * (a7 ^ 4) * a4 * a1 * b8
    - (232744621367623680 : R) * (h ^ 78) * (a7 ^ 4) * (a3 ^ 2) * b7
    - (1595963117949419520 : R) * (h ^ 78) * (a7 ^ 4) * a3 * a2 * b8
    - (177329235327713280 : R) * (h ^ 78) * (a7 ^ 3) * (a6 ^ 2) * a1 * b7
    - (202661983231672320 : R) * (h ^ 78) * (a7 ^ 3) * (a6 ^ 2) * a0 * b8
    - (265993852991569920 : R) * (h ^ 78) * (a7 ^ 3) * a6 * a5 * a2 * b7
    - (911978924542525440 : R) * (h ^ 78) * (a7 ^ 3) * a6 * a5 * a1 * b8
    - (301459700057112576 : R) * (h ^ 78) * (a7 ^ 3) * a6 * a4 * a3 * b7
    - (1195705701066866688 : R) * (h ^ 78) * (a7 ^ 3) * a6 * a4 * a2 * b8
    - (633318697598976000 : R) * (h ^ 78) * (a7 ^ 3) * a6 * (a3 ^ 2) * b8
    - (1076641785918259200 : R) * (h ^ 78) * a7 * a6 * (a5 ^ 4) * b8
    + (245905775552102400 : R) * (h ^ 72) * (a7 ^ 6) * a5 * a0
    + (711395018287349760 : R) * (h ^ 72) * (a7 ^ 6) * a4 * a1
    + (827767328971161600 : R) * (h ^ 72) * (a7 ^ 6) * a3 * a2
    + (141309234401771520 : R) * (h ^ 72) * (a7 ^ 5) * (a6 ^ 2) * a0
    + (473801550641233920 : R) * (h ^ 72) * (a7 ^ 5) * a6 * a5 * a1
    + (606798477137018880 : R) * (h ^ 72) * (a7 ^ 5) * a6 * a4 * a2
    + (320023854380482560 : R) * (h ^ 72) * (a7 ^ 5) * a6 * (a3 ^ 2)
    + (757013755723776000 : R) * (h ^ 72) * (a7 ^ 3) * a6 * (a5 ^ 4)
    + (1231453023109120 : R) * (h ^ 70) * (a7 ^ 6) * a6 * b1
    + (1847179534663680 : R) * (h ^ 70) * (a7 ^ 6) * a5 * b2
    + (2770769301995520 : R) * (h ^ 70) * (a7 ^ 6) * a4 * b3
    + (3694359069327360 : R) * (h ^ 70) * (a7 ^ 6) * a3 * b4
    + (4617948836659200 : R) * (h ^ 70) * (a7 ^ 6) * a2 * b5
    + (5541538603991040 : R) * (h ^ 70) * (a7 ^ 6) * a1 * b6
    + (6465128371322880 : R) * (h ^ 70) * (a7 ^ 6) * a0 * b7
    + (738871813865472 : R) * (h ^ 70) * (a7 ^ 5) * (a6 ^ 2) * b2
    + (1108307720798208 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a5 * b3
    + (1477743627730944 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a4 * b4
    + (1847179534663680 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a3 * b5
    + (2216615441596416 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a2 * b6
    + (111200207986753536 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a1 * b7
    + (127085951984861184 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a0 * b8
    + (116372310683811840 : R) * (h ^ 70) * (a7 ^ 5) * a5 * a2 * b7
    + (398990779487354880 : R) * (h ^ 70) * (a7 ^ 5) * a5 * a1 * b8
    + (131888618774986752 : R) * (h ^ 70) * (a7 ^ 5) * a4 * a3 * b7
    + (523121244216754176 : R) * (h ^ 70) * (a7 ^ 5) * a4 * a2 * b8
    + (277076930199552000 : R) * (h ^ 70) * (a7 ^ 5) * (a3 ^ 2) * b8
    + (60956924643901440 : R) * (h ^ 70) * (a7 ^ 4) * (a6 ^ 2) * a2 * b7
    + (221661544159641600 : R) * (h ^ 70) * (a7 ^ 4) * (a6 ^ 2) * a1 * b8
    + (72040001851883520 : R) * (h ^ 70) * (a7 ^ 4) * a6 * a5 * a3 * b7
    + (310326161823498240 : R) * (h ^ 70) * (a7 ^ 4) * a6 * a5 * a2 * b8
    + (37682462507139072 : R) * (h ^ 70) * (a7 ^ 4) * a6 * (a4 ^ 2) * b7
    + (345792008889040896 : R) * (h ^ 70) * (a7 ^ 4) * a6 * a4 * a3 * b8
    + (314020520892825600 : R) * (h ^ 70) * (a7 ^ 3) * (a5 ^ 4) * b8
    + (1614962678877388800 : R) * (h ^ 70) * (a7 ^ 2) * (a6 ^ 2) * (a5 ^ 3) * b8
    - (87205015977984000 : R) * (h ^ 64) * (a7 ^ 7) * a6 * a0
    - (207288178405539840 : R) * (h ^ 64) * (a7 ^ 7) * a5 * a1
    - (265474333747445760 : R) * (h ^ 64) * (a7 ^ 7) * a4 * a2
    - (140010436291461120 : R) * (h ^ 64) * (a7 ^ 7) * (a3 ^ 2)
    - (114121060625940480 : R) * (h ^ 64) * (a7 ^ 6) * (a6 ^ 2) * a1
    - (155682600155873280 : R) * (h ^ 64) * (a7 ^ 6) * a6 * a5 * a2
    - (172307215967846400 : R) * (h ^ 64) * (a7 ^ 6) * a6 * a4 * a3
    - (220795678752768000 : R) * (h ^ 64) * (a7 ^ 5) * (a5 ^ 4)
    - (1135520633585664000 : R) * (h ^ 64) * (a7 ^ 4) * (a6 ^ 2) * (a5 ^ 3)
    - (134690174402560 : R) * (h ^ 62) * (a7 ^ 8) * b1
    - (426610511577088 : R) * (h ^ 62) * (a7 ^ 7) * a6 * b2
    - (484884627849216 : R) * (h ^ 62) * (a7 ^ 7) * a5 * b3
    - (646512837132288 : R) * (h ^ 62) * (a7 ^ 7) * a4 * b4
    - (808141046415360 : R) * (h ^ 62) * (a7 ^ 7) * a3 * b5
    - (969769255698432 : R) * (h ^ 62) * (a7 ^ 7) * a2 * b6
    - (14708167044759552 : R) * (h ^ 62) * (a7 ^ 7) * a1 * b7
    - (16809333765439488 : R) * (h ^ 62) * (a7 ^ 7) * a0 * b8
    - (184717953466368 : R) * (h ^ 62) * (a7 ^ 6) * (a6 ^ 2) * b3
    - (246290604621824 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a5 * b4
    - (307863255777280 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a4 * b5
    - (369435906932736 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a3 * b6
    - (37282240274628608 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a2 * b7
    - (135706123146625024 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a1 * b8
    - (31517500810199040 : R) * (h ^ 62) * (a7 ^ 6) * a5 * a3 * b7
    - (135767695797780480 : R) * (h ^ 62) * (a7 ^ 6) * a5 * a2 * b8
    - (16486077346873344 : R) * (h ^ 62) * (a7 ^ 6) * (a4 ^ 2) * b7
    - (151284003888955392 : R) * (h ^ 62) * (a7 ^ 6) * a4 * a3 * b8
    - (15377769626075136 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 2) * a3 * b7
    - (69823386410287104 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 2) * a2 * b8
    - (16624615811973120 : R) * (h ^ 62) * (a7 ^ 5) * a6 * a5 * a4 * b7
    - (80906463618269184 : R) * (h ^ 62) * (a7 ^ 5) * a6 * a5 * a3 * b8
    - (42115693390331904 : R) * (h ^ 62) * (a7 ^ 5) * a6 * (a4 ^ 2) * b8
    - (942061562678476800 : R) * (h ^ 62) * (a7 ^ 4) * a6 * (a5 ^ 3) * b8
    - (1211222009158041600 : R) * (h ^ 62) * (a7 ^ 3) * (a6 ^ 3) * (a5 ^ 2) * b8
    + (11104723843153920 : R) * (h ^ 56) * (a7 ^ 9) * a0
    + (69614419071467520 : R) * (h ^ 56) * (a7 ^ 8) * a6 * a1
    + (68111137568194560 : R) * (h ^ 56) * (a7 ^ 8) * a5 * a2
    + (75384406985932800 : R) * (h ^ 56) * (a7 ^ 8) * a4 * a3
    + (34783050344693760 : R) * (h ^ 56) * (a7 ^ 7) * (a6 ^ 2) * a2
    + (39978242785935360 : R) * (h ^ 56) * (a7 ^ 7) * a6 * a5 * a3
    + (20768400259153920 : R) * (h ^ 56) * (a7 ^ 7) * a6 * (a4 ^ 2)
    + (662387036258304000 : R) * (h ^ 56) * (a7 ^ 6) * a6 * (a5 ^ 3)
    + (851640475189248000 : R) * (h ^ 56) * (a7 ^ 5) * (a6 ^ 3) * (a5 ^ 2)
    + (45217415692288 : R) * (h ^ 54) * (a7 ^ 9) * b2
    + (105862353911808 : R) * (h ^ 54) * (a7 ^ 8) * a6 * b3
    + (107752139522048 : R) * (h ^ 54) * (a7 ^ 8) * a5 * b4
    + (134690174402560 : R) * (h ^ 54) * (a7 ^ 8) * a4 * b5
    + (161628209283072 : R) * (h ^ 54) * (a7 ^ 8) * a3 * b6
    + (4643443762528256 : R) * (h ^ 54) * (a7 ^ 8) * a2 * b7
    + (16944023939842048 : R) * (h ^ 54) * (a7 ^ 8) * a1 * b8
    + (39582418599936 : R) * (h ^ 54) * (a7 ^ 7) * (a6 ^ 2) * b4
    + (49478023249920 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a5 * b5
    + (59373627899904 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a4 * b6
    + (9264759853547520 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a3 * b7
    + (42175067018231808 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a2 * b8
    + (7273269417738240 : R) * (h ^ 54) * (a7 ^ 7) * a5 * a4 * b7
    + (35396577832992768 : R) * (h ^ 54) * (a7 ^ 7) * a5 * a3 * b8
    + (18425615858270208 : R) * (h ^ 54) * (a7 ^ 7) * (a4 ^ 2) * b8
    + (3359557778669568 : R) * (h ^ 54) * (a7 ^ 6) * (a6 ^ 2) * a4 * b7
    + (17040231207272448 : R) * (h ^ 54) * (a7 ^ 6) * (a6 ^ 2) * a3 * b8
    + (1731730813747200 : R) * (h ^ 54) * (a7 ^ 6) * a6 * (a5 ^ 2) * b7
    + (18287077393170432 : R) * (h ^ 54) * (a7 ^ 6) * a6 * a5 * a4 * b8
    + (137383977890611200 : R) * (h ^ 54) * (a7 ^ 6) * (a5 ^ 3) * b8
    + (1059819258013286400 : R) * (h ^ 54) * (a7 ^ 5) * (a6 ^ 2) * (a5 ^ 2) * b8
    + (454208253434265600 : R) * (h ^ 54) * (a7 ^ 4) * (a6 ^ 4) * a5 * b8
    - (8612824083333120 : R) * (h ^ 48) * (a7 ^ 10) * a1
    - (20962887115735040 : R) * (h ^ 48) * (a7 ^ 9) * a6 * a2
    - (17490481218846720 : R) * (h ^ 48) * (a7 ^ 9) * a5 * a3
    - (9086175113379840 : R) * (h ^ 48) * (a7 ^ 9) * (a4 ^ 2)
    - (8373768887992320 : R) * (h ^ 48) * (a7 ^ 8) * (a6 ^ 2) * a3
    - (8958228037632000 : R) * (h ^ 48) * (a7 ^ 8) * a6 * a5 * a4
    - (96598109454336000 : R) * (h ^ 48) * (a7 ^ 8) * (a5 ^ 3)
    - (745185415790592000 : R) * (h ^ 48) * (a7 ^ 7) * (a6 ^ 2) * (a5 ^ 2)
    - (319365178195968000 : R) * (h ^ 48) * (a7 ^ 6) * (a6 ^ 4) * a5
    - (10958609055744 : R) * (h ^ 46) * (a7 ^ 10) * b3
    - (22557168238592 : R) * (h ^ 46) * (a7 ^ 9) * a6 * b4
    - (21646635171840 : R) * (h ^ 46) * (a7 ^ 9) * a5 * b5
    - (25975962206208 : R) * (h ^ 46) * (a7 ^ 9) * a4 * b6
    - (1109931218436096 : R) * (h ^ 46) * (a7 ^ 9) * a3 * b7
    - (5086959265382400 : R) * (h ^ 46) * (a7 ^ 9) * a2 * b8
    - (7730941132800 : R) * (h ^ 46) * (a7 ^ 8) * (a6 ^ 2) * b5
    - (9277129359360 : R) * (h ^ 46) * (a7 ^ 8) * a6 * a5 * b6
    - (2002313753395200 : R) * (h ^ 46) * (a7 ^ 8) * a6 * a4 * b7
    - (10181030996606976 : R) * (h ^ 46) * (a7 ^ 8) * a6 * a3 * b8
    - (757632231014400 : R) * (h ^ 46) * (a7 ^ 8) * (a5 ^ 2) * b7
    - (8000596359512064 : R) * (h ^ 46) * (a7 ^ 8) * a5 * a4 * b8
    - (671045690327040 : R) * (h ^ 46) * (a7 ^ 7) * (a6 ^ 2) * a5 * b7
    - (3656425918169088 : R) * (h ^ 46) * (a7 ^ 7) * (a6 ^ 2) * a4 * b8
    - (310994115137372160 : R) * (h ^ 46) * (a7 ^ 7) * a6 * (a5 ^ 2) * b8
    - (529909629006643200 : R) * (h ^ 46) * (a7 ^ 6) * (a6 ^ 3) * a5 * b8
    - (68131238015139840 : R) * (h ^ 46) * (a7 ^ 5) * (a6 ^ 5) * b8
    + (2513569883095040 : R) * (h ^ 40) * (a7 ^ 11) * a2
    + (4995011397550080 : R) * (h ^ 40) * (a7 ^ 10) * a6 * a3
    + (3919224766464000 : R) * (h ^ 40) * (a7 ^ 10) * a5 * a4
    + (1783044935516160 : R) * (h ^ 40) * (a7 ^ 9) * (a6 ^ 2) * a4
    + (218261621204582400 : R) * (h ^ 40) * (a7 ^ 9) * a6 * (a5 ^ 2)
    + (372592707895296000 : R) * (h ^ 40) * (a7 ^ 8) * (a6 ^ 3) * a5
    + (47904776729395200 : R) * (h ^ 40) * (a7 ^ 7) * (a6 ^ 5)
    + (2292438794240 : R) * (h ^ 38) * (a7 ^ 11) * b4
    + (4386235351040 : R) * (h ^ 38) * (a7 ^ 10) * a6 * b5
    + (4058744094720 : R) * (h ^ 38) * (a7 ^ 10) * a5 * b6
    + (232971911036928 : R) * (h ^ 38) * (a7 ^ 10) * a4 * b7
    + (1192594306498560 : R) * (h ^ 38) * (a7 ^ 10) * a3 * b8
    + (1417339207680 : R) * (h ^ 38) * (a7 ^ 9) * (a6 ^ 2) * b6
    + (396704654295040 : R) * (h ^ 38) * (a7 ^ 9) * a6 * a5 * b7
    + (2165780208680960 : R) * (h ^ 38) * (a7 ^ 9) * a6 * a4 * b8
    + (30875317300101120 : R) * (h ^ 38) * (a7 ^ 9) * (a5 ^ 2) * b8
    + (62910533468160 : R) * (h ^ 38) * (a7 ^ 8) * (a6 ^ 3) * b7
    + (232557532592209920 : R) * (h ^ 38) * (a7 ^ 8) * (a6 ^ 2) * a5 * b8
    + (99358055438745600 : R) * (h ^ 38) * (a7 ^ 7) * (a6 ^ 4) * b8
    - (582525785210880 : R) * (h ^ 32) * (a7 ^ 12) * a3
    - (1054807393566720 : R) * (h ^ 32) * (a7 ^ 11) * a6 * a4
    - (21531531726028800 : R) * (h ^ 32) * (a7 ^ 11) * (a5 ^ 2)
    - (163359672332451840 : R) * (h ^ 32) * (a7 ^ 10) * (a6 ^ 2) * a5
    - (69861132730368000 : R) * (h ^ 32) * (a7 ^ 9) * (a6 ^ 4)
    - (439227514880 : R) * (h ^ 30) * (a7 ^ 12) * b5
    - (801279836160 : R) * (h ^ 30) * (a7 ^ 11) * a6 * b6
    - (45115947089920 : R) * (h ^ 30) * (a7 ^ 11) * a5 * b7
    - (247666067898368 : R) * (h ^ 30) * (a7 ^ 11) * a4 * b8
    - (46390881288192 : R) * (h ^ 30) * (a7 ^ 10) * (a6 ^ 2) * b7
    - (45503897527123968 : R) * (h ^ 30) * (a7 ^ 10) * a6 * a5 * b8
    - (58026028223692800 : R) * (h ^ 30) * (a7 ^ 9) * (a6 ^ 3) * b8
    + (120192289996800 : R) * (h ^ 24) * (a7 ^ 13) * a4
    + (31902152890777600 : R) * (h ^ 24) * (a7 ^ 12) * a6 * a5
    + (40784801908654080 : R) * (h ^ 24) * (a7 ^ 11) * (a6 ^ 3)
    + (79272345600 : R) * (h ^ 22) * (a7 ^ 13) * b6
    + (9643510202368 : R) * (h ^ 22) * (a7 ^ 12) * a6 * b7
    + (3334651464646656 : R) * (h ^ 22) * (a7 ^ 12) * a5 * b8
    + (16953876192165888 : R) * (h ^ 22) * (a7 ^ 11) * (a6 ^ 2) * b8
    - (2334204113059840 : R) * (h ^ 16) * (a7 ^ 14) * a5
    - (11909854467194880 : R) * (h ^ 16) * (a7 ^ 13) * (a6 ^ 2)
    - (607673909248 : R) * (h ^ 14) * (a7 ^ 14) * b7
    - (2475378111152128 : R) * (h ^ 14) * (a7 ^ 13) * a6 * b8
    + (1738259924746240 : R) * (h ^ 8) * (a7 ^ 15) * a6
    + (144437568077824 : R) * (h ^ 6) * (a7 ^ 15) * b8
    - (101417221427200 : R) * (a7 ^ 17)

set_option maxHeartbeats 200000000 in
/-- Integer expansion of compact block `17` after the extra
`2^{34}` scale, on `λ = 0`. -/
def alignedSquareCompactBlock17Expansion810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    - (2296835809958952960 : R) * (h ^ 104) * (a5 ^ 3) * a0
    + (216172782113783808 : R) * (h ^ 102) * (a5 ^ 3) * b2
    + (5167880572407644160 : R) * (h ^ 96) * a7 * a6 * (a5 ^ 2) * a0
    + (287104476244869120 : R) * (h ^ 96) * a7 * (a5 ^ 3) * a1
    + (1794402976530432000 : R) * (h ^ 96) * (a5 ^ 4) * a3
    + (3588805953060864000 : R) * (h ^ 96) * (a5 ^ 3) * (a4 ^ 2)
    - (486388759756013568 : R) * (h ^ 94) * a7 * a6 * (a5 ^ 2) * b2
    - (81064793292668928 : R) * (h ^ 94) * a7 * (a5 ^ 3) * b3
    - (287104476244869120 : R) * (h ^ 94) * (a5 ^ 4) * b5
    - (1378101485975371776 : R) * (h ^ 94) * (a5 ^ 3) * a4 * b6
    - (1607785066971267072 : R) * (h ^ 94) * (a5 ^ 3) * a3 * b7
    - (1837468647967162368 : R) * (h ^ 94) * (a5 ^ 3) * a2 * b8
    - (2411677600456900608 : R) * (h ^ 94) * (a5 ^ 2) * (a4 ^ 2) * b7
    - (1507298500285562880 : R) * (h ^ 88) * (a7 ^ 3) * (a5 ^ 2) * a0
    - (3875910429305733120 : R) * (h ^ 88) * (a7 ^ 2) * (a6 ^ 2) * a5 * a0
    - (645985071550955520 : R) * (h ^ 88) * (a7 ^ 2) * a6 * (a5 ^ 2) * a1
    + (1256082083571302400 : R) * (h ^ 88) * (a7 ^ 2) * (a5 ^ 3) * a2
    - (5383208929591296000 : R) * (h ^ 88) * a7 * a6 * (a5 ^ 3) * a3
    - (8074813394386944000 : R) * (h ^ 88) * a7 * a6 * (a5 ^ 2) * (a4 ^ 2)
    - (5383208929591296000 : R) * (h ^ 88) * a7 * (a5 ^ 4) * a4
    + (141863388262170624 : R) * (h ^ 86) * (a7 ^ 3) * (a5 ^ 2) * b2
    + (364791569817010176 : R) * (h ^ 86) * (a7 ^ 2) * (a6 ^ 2) * a5 * b2
    + (182395784908505088 : R) * (h ^ 86) * (a7 ^ 2) * a6 * (a5 ^ 2) * b3
    + (20266198323167232 : R) * (h ^ 86) * (a7 ^ 2) * (a5 ^ 3) * b4
    + (861313428734607360 : R) * (h ^ 86) * a7 * a6 * (a5 ^ 3) * b5
    + (3100728343444586496 : R) * (h ^ 86) * a7 * a6 * (a5 ^ 2) * a4 * b6
    + (3617516400685350912 : R) * (h ^ 86) * a7 * a6 * (a5 ^ 2) * a3 * b7
    + (4134304457926115328 : R) * (h ^ 86) * a7 * a6 * (a5 ^ 2) * a2 * b8
    + (3617516400685350912 : R) * (h ^ 86) * a7 * a6 * a5 * (a4 ^ 2) * b7
    + (1076641785918259200 : R) * (h ^ 86) * a7 * (a5 ^ 4) * b6
    + (5024328334285209600 : R) * (h ^ 86) * a7 * (a5 ^ 3) * a4 * b7
    + (2296835809958952960 : R) * (h ^ 86) * a7 * (a5 ^ 3) * a3 * b8
    + (2411677600456900608 : R) * (h ^ 86) * a7 * (a5 ^ 2) * (a4 ^ 2) * b8
    + (2260947750428344320 : R) * (h ^ 80) * (a7 ^ 4) * a6 * a5 * a0
    + (188412312535695360 : R) * (h ^ 80) * (a7 ^ 4) * (a5 ^ 2) * a1
    + (968977607326433280 : R) * (h ^ 80) * (a7 ^ 3) * (a6 ^ 3) * a0
    + (484488803663216640 : R) * (h ^ 80) * (a7 ^ 3) * (a6 ^ 2) * a5 * a1
    - (2826184688035430400 : R) * (h ^ 80) * (a7 ^ 3) * a6 * (a5 ^ 2) * a2
    + (336450558099456000 : R) * (h ^ 80) * (a7 ^ 3) * (a5 ^ 3) * a3
    + (1224680031482019840 : R) * (h ^ 80) * (a7 ^ 3) * (a5 ^ 2) * (a4 ^ 2)
    + (6056110045790208000 : R) * (h ^ 80) * (a7 ^ 2) * (a6 ^ 2) * (a5 ^ 2) * a3
    + (6056110045790208000 : R) * (h ^ 80) * (a7 ^ 2) * (a6 ^ 2) * a5 * (a4 ^ 2)
    + (14467373998276608000 : R) * (h ^ 80) * (a7 ^ 2) * a6 * (a5 ^ 3) * a4
    + (1682252790497280000 : R) * (h ^ 80) * (a7 ^ 2) * (a5 ^ 5)
    - (212795082393255936 : R) * (h ^ 78) * (a7 ^ 4) * a6 * a5 * b2
    - (53198770598313984 : R) * (h ^ 78) * (a7 ^ 4) * (a5 ^ 2) * b3
    - (91197892454252544 : R) * (h ^ 78) * (a7 ^ 3) * (a6 ^ 3) * b2
    - (136796838681378816 : R) * (h ^ 78) * (a7 ^ 3) * (a6 ^ 2) * a5 * b3
    - (45598946227126272 : R) * (h ^ 78) * (a7 ^ 3) * a6 * (a5 ^ 2) * b4
    - (255438541364920320 : R) * (h ^ 78) * (a7 ^ 3) * (a5 ^ 3) * b5
    - (904379100171337728 : R) * (h ^ 78) * (a7 ^ 3) * (a5 ^ 2) * a4 * b6
    - (1055108950199894016 : R) * (h ^ 78) * (a7 ^ 3) * (a5 ^ 2) * a3 * b7
    - (1205838800228450304 : R) * (h ^ 78) * (a7 ^ 3) * (a5 ^ 2) * a2 * b8
    - (1055108950199894016 : R) * (h ^ 78) * (a7 ^ 3) * a5 * (a4 ^ 2) * b7
    - (968977607326433280 : R) * (h ^ 78) * (a7 ^ 2) * (a6 ^ 2) * (a5 ^ 2) * b5
    - (2325546257583439872 : R) * (h ^ 78) * (a7 ^ 2) * (a6 ^ 2) * a5 * a4 * b6
    - (2713137300514013184 : R) * (h ^ 78) * (a7 ^ 2) * (a6 ^ 2) * a5 * a3 * b7
    - (3100728343444586496 : R) * (h ^ 78) * (a7 ^ 2) * (a6 ^ 2) * a5 * a2 * b8
    - (1356568650257006592 : R) * (h ^ 78) * (a7 ^ 2) * (a6 ^ 2) * (a4 ^ 2) * b7
    - (2906932821979299840 : R) * (h ^ 78) * (a7 ^ 2) * a6 * (a5 ^ 3) * b6
    - (10174264876927549440 : R) * (h ^ 78) * (a7 ^ 2) * a6 * (a5 ^ 2) * a4 * b7
    - (5167880572407644160 : R) * (h ^ 78) * (a7 ^ 2) * a6 * (a5 ^ 2) * a3 * b8
    - (3617516400685350912 : R) * (h ^ 78) * (a7 ^ 2) * a6 * a5 * (a4 ^ 2) * b8
    - (2041133385803366400 : R) * (h ^ 78) * (a7 ^ 2) * (a5 ^ 4) * b7
    - (4593671619917905920 : R) * (h ^ 78) * (a7 ^ 2) * (a5 ^ 3) * a4 * b8
    - (329721546937466880 : R) * (h ^ 72) * (a7 ^ 6) * a5 * a0
    - (847855406410629120 : R) * (h ^ 72) * (a7 ^ 5) * (a6 ^ 2) * a0
    - (282618468803543040 : R) * (h ^ 72) * (a7 ^ 5) * a6 * a5 * a1
    + (824303867343667200 : R) * (h ^ 72) * (a7 ^ 5) * (a5 ^ 2) * a2
    - (121122200915804160 : R) * (h ^ 72) * (a7 ^ 4) * (a6 ^ 3) * a1
    + (2119638516026572800 : R) * (h ^ 72) * (a7 ^ 4) * (a6 ^ 2) * a5 * a2
    - (757013755723776000 : R) * (h ^ 72) * (a7 ^ 4) * a6 * (a5 ^ 2) * a3
    - (1837020047223029760 : R) * (h ^ 72) * (a7 ^ 4) * a6 * a5 * (a4 ^ 2)
    - (1974544212846182400 : R) * (h ^ 72) * (a7 ^ 4) * (a5 ^ 3) * a4
    - (3028055022895104000 : R) * (h ^ 72) * (a7 ^ 3) * (a6 ^ 3) * a5 * a3
    - (1514027511447552000 : R) * (h ^ 72) * (a7 ^ 3) * (a6 ^ 3) * (a4 ^ 2)
    - (14383261358751744000 : R) * (h ^ 72) * (a7 ^ 3) * (a6 ^ 2) * (a5 ^ 2) * a4
    - (5116852237762560000 : R) * (h ^ 72) * (a7 ^ 3) * a6 * (a5 ^ 4)
    + (31032616182349824 : R) * (h ^ 70) * (a7 ^ 6) * a5 * b2
    + (79798155897470976 : R) * (h ^ 70) * (a7 ^ 5) * (a6 ^ 2) * b2
    + (79798155897470976 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a5 * b3
    + (13299692649578496 : R) * (h ^ 70) * (a7 ^ 5) * (a5 ^ 2) * b4
    + (34199209670344704 : R) * (h ^ 70) * (a7 ^ 4) * (a6 ^ 3) * b3
    + (34199209670344704 : R) * (h ^ 70) * (a7 ^ 4) * (a6 ^ 2) * a5 * b4
    + (574736718071070720 : R) * (h ^ 70) * (a7 ^ 4) * a6 * (a5 ^ 2) * b5
    + (1356568650257006592 : R) * (h ^ 70) * (a7 ^ 4) * a6 * a5 * a4 * b6
    + (1582663425299841024 : R) * (h ^ 70) * (a7 ^ 4) * a6 * a5 * a3 * b7
    + (1808758200342675456 : R) * (h ^ 70) * (a7 ^ 4) * a6 * a5 * a2 * b8
    + (791331712649920512 : R) * (h ^ 70) * (a7 ^ 4) * a6 * (a4 ^ 2) * b7
    + (825095515715665920 : R) * (h ^ 70) * (a7 ^ 4) * (a5 ^ 3) * b6
    + (2885063535702835200 : R) * (h ^ 70) * (a7 ^ 4) * (a5 ^ 2) * a4 * b7
    + (1507298500285562880 : R) * (h ^ 70) * (a7 ^ 4) * (a5 ^ 2) * a3 * b8
    + (1055108950199894016 : R) * (h ^ 70) * (a7 ^ 4) * a5 * (a4 ^ 2) * b8
    + (484488803663216640 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 3) * a5 * b5
    + (581386564395859968 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 3) * a4 * b6
    + (678284325128503296 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 3) * a3 * b7
    + (775182085861146624 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 3) * a2 * b8
    + (2906932821979299840 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 2) * (a5 ^ 2) * b6
    + (6782843251285032960 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 2) * a5 * a4 * b7
    + (3875910429305733120 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 2) * a5 * a3 * b8
    + (1356568650257006592 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 2) * (a4 ^ 2) * b8
    + (5008627308240568320 : R) * (h ^ 70) * (a7 ^ 3) * a6 * (a5 ^ 3) * b7
    + (9205287269601116160 : R) * (h ^ 70) * (a7 ^ 3) * a6 * (a5 ^ 2) * a4 * b8
    + (1637392716084019200 : R) * (h ^ 70) * (a7 ^ 3) * (a5 ^ 4) * b8
    + (247291160203100160 : R) * (h ^ 64) * (a7 ^ 7) * a6 * a0
    + (41215193367183360 : R) * (h ^ 64) * (a7 ^ 7) * a5 * a1
    + (105981925801328640 : R) * (h ^ 64) * (a7 ^ 6) * (a6 ^ 2) * a1
    - (1236455801015500800 : R) * (h ^ 64) * (a7 ^ 6) * a6 * a5 * a2
    - (294394238337024000 : R) * (h ^ 64) * (a7 ^ 6) * (a5 ^ 2) * a3
    + (20607596683591680 : R) * (h ^ 64) * (a7 ^ 6) * a5 * (a4 ^ 2)
    - (529909629006643200 : R) * (h ^ 64) * (a7 ^ 5) * (a6 ^ 3) * a2
    + (567760316792832000 : R) * (h ^ 64) * (a7 ^ 5) * (a6 ^ 2) * a5 * a3
    + (688882517708636160 : R) * (h ^ 64) * (a7 ^ 5) * (a6 ^ 2) * (a4 ^ 2)
    + (3868655714146713600 : R) * (h ^ 64) * (a7 ^ 5) * a6 * (a5 ^ 2) * a4
    + (681750466815590400 : R) * (h ^ 64) * (a7 ^ 5) * (a5 ^ 4)
    + (567760316792832000 : R) * (h ^ 64) * (a7 ^ 4) * (a6 ^ 4) * a3
    + (6245363484721152000 : R) * (h ^ 64) * (a7 ^ 4) * (a6 ^ 3) * a5 * a4
    + (6085023765626880000 : R) * (h ^ 64) * (a7 ^ 4) * (a6 ^ 2) * (a5 ^ 3)
    - (23274462136762368 : R) * (h ^ 62) * (a7 ^ 7) * a6 * b2
    - (11637231068381184 : R) * (h ^ 62) * (a7 ^ 7) * a5 * b3
    - (29924308461551616 : R) * (h ^ 62) * (a7 ^ 6) * (a6 ^ 2) * b3
    - (19949538974367744 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a5 * b4
    - (85201156036362240 : R) * (h ^ 62) * (a7 ^ 6) * (a5 ^ 2) * b5
    - (197832928162480128 : R) * (h ^ 62) * (a7 ^ 6) * a5 * a4 * b6
    - (230805082856226816 : R) * (h ^ 62) * (a7 ^ 6) * a5 * a3 * b7
    - (263777237549973504 : R) * (h ^ 62) * (a7 ^ 6) * a5 * a2 * b8
    - (115402541428113408 : R) * (h ^ 62) * (a7 ^ 6) * (a4 ^ 2) * b7
    - (8549802417586176 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 3) * b4
    - (431052538553303040 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 2) * a5 * b5
    - (508713243846377472 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 2) * a4 * b6
    - (593498784487440384 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 2) * a3 * b7
    - (678284325128503296 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 2) * a2 * b8
    - (1644501058757591040 : R) * (h ^ 62) * (a7 ^ 5) * a6 * (a5 ^ 2) * b6
    - (3833012983148052480 : R) * (h ^ 62) * (a7 ^ 5) * a6 * a5 * a4 * b7
    - (2260947750428344320 : R) * (h ^ 62) * (a7 ^ 5) * a6 * a5 * a3 * b8
    - (791331712649920512 : R) * (h ^ 62) * (a7 ^ 5) * a6 * (a4 ^ 2) * b8
    - (1381534436155195392 : R) * (h ^ 62) * (a7 ^ 5) * (a5 ^ 3) * b7
    - (2602445066899292160 : R) * (h ^ 62) * (a7 ^ 5) * (a5 ^ 2) * a4 * b8
    - (90841650686853120 : R) * (h ^ 62) * (a7 ^ 4) * (a6 ^ 4) * b5
    - (1271783109615943680 : R) * (h ^ 62) * (a7 ^ 4) * (a6 ^ 3) * a5 * b6
    - (1483746961218600960 : R) * (h ^ 62) * (a7 ^ 4) * (a6 ^ 3) * a4 * b7
    - (968977607326433280 : R) * (h ^ 62) * (a7 ^ 4) * (a6 ^ 3) * a3 * b8
    - (4513063673706577920 : R) * (h ^ 62) * (a7 ^ 4) * (a6 ^ 2) * (a5 ^ 2) * b7
    - (6056110045790208000 : R) * (h ^ 62) * (a7 ^ 4) * (a6 ^ 2) * a5 * a4 * b8
    - (3918527499998330880 : R) * (h ^ 62) * (a7 ^ 4) * a6 * (a5 ^ 3) * b8
    - (24042196130856960 : R) * (h ^ 56) * (a7 ^ 9) * a0
    - (30911395025387520 : R) * (h ^ 56) * (a7 ^ 8) * a6 * a1
    + (180316470981427200 : R) * (h ^ 56) * (a7 ^ 8) * a5 * a2
    + (463670925380812800 : R) * (h ^ 56) * (a7 ^ 7) * (a6 ^ 2) * a2
    + (441591357505536000 : R) * (h ^ 56) * (a7 ^ 7) * a6 * a5 * a3
    - (15455697512693760 : R) * (h ^ 56) * (a7 ^ 7) * a6 * (a4 ^ 2)
    + (56578892680396800 : R) * (h ^ 56) * (a7 ^ 7) * (a5 ^ 2) * a4
    - (141940079198208000 : R) * (h ^ 56) * (a7 ^ 6) * (a6 ^ 3) * a3
    - (2470940212042137600 : R) * (h ^ 56) * (a7 ^ 6) * (a6 ^ 2) * a5 * a4
    - (1600253919127142400 : R) * (h ^ 56) * (a7 ^ 6) * a6 * (a5 ^ 3)
    - (993580554387456000 : R) * (h ^ 56) * (a7 ^ 5) * (a6 ^ 4) * a4
    - (3518931130122240000 : R) * (h ^ 56) * (a7 ^ 5) * (a6 ^ 3) * (a5 ^ 2)
    + (2262794929963008 : R) * (h ^ 54) * (a7 ^ 9) * b2
    + (8727923301285888 : R) * (h ^ 54) * (a7 ^ 8) * a6 * b3
    + (2909307767095296 : R) * (h ^ 54) * (a7 ^ 8) * a5 * b4
    + (7481077115387904 : R) * (h ^ 54) * (a7 ^ 7) * (a6 ^ 2) * b4
    + (127801734054543360 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a5 * b5
    + (148374696121860096 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a4 * b6
    + (173103812142170112 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a3 * b7
    + (197832928162480128 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a2 * b8
    + (232354981934530560 : R) * (h ^ 54) * (a7 ^ 7) * (a5 ^ 2) * b6
    + (540949412944281600 : R) * (h ^ 54) * (a7 ^ 7) * a5 * a4 * b7
    + (329721546937466880 : R) * (h ^ 54) * (a7 ^ 7) * a5 * a3 * b8
    + (115402541428113408 : R) * (h ^ 54) * (a7 ^ 7) * (a4 ^ 2) * b8
    + (107763134638325760 : R) * (h ^ 54) * (a7 ^ 6) * (a6 ^ 3) * b5
    + (1074402905366200320 : R) * (h ^ 54) * (a7 ^ 6) * (a6 ^ 2) * a5 * b6
    + (1251911498528194560 : R) * (h ^ 54) * (a7 ^ 6) * (a6 ^ 2) * a4 * b7
    + (847855406410629120 : R) * (h ^ 54) * (a7 ^ 6) * (a6 ^ 2) * a3 * b8
    + (2473480908536020992 : R) * (h ^ 54) * (a7 ^ 6) * a6 * (a5 ^ 2) * b7
    + (3409085279942737920 : R) * (h ^ 54) * (a7 ^ 6) * a6 * a5 * a4 * b8
    + (1072795694244298752 : R) * (h ^ 54) * (a7 ^ 6) * (a5 ^ 3) * b8
    + (204393714045419520 : R) * (h ^ 54) * (a7 ^ 5) * (a6 ^ 4) * b6
    + (1761949516447088640 : R) * (h ^ 54) * (a7 ^ 5) * (a6 ^ 3) * a5 * b7
    + (1302063659844894720 : R) * (h ^ 54) * (a7 ^ 5) * (a6 ^ 3) * a4 * b8
    + (3422963865464340480 : R) * (h ^ 54) * (a7 ^ 5) * (a6 ^ 2) * (a5 ^ 2) * b8
    + (3005274516357120 : R) * (h ^ 48) * (a7 ^ 10) * a1
    - (135237353236070400 : R) * (h ^ 48) * (a7 ^ 9) * a6 * a2
    - (101964671090688000 : R) * (h ^ 48) * (a7 ^ 9) * a5 * a3
    - (16529009839964160 : R) * (h ^ 48) * (a7 ^ 9) * (a4 ^ 2)
    - (165596759064576000 : R) * (h ^ 48) * (a7 ^ 8) * (a6 ^ 2) * a3
    - (94528149966028800 : R) * (h ^ 48) * (a7 ^ 8) * a6 * a5 * a4
    - (17969821715005440 : R) * (h ^ 48) * (a7 ^ 8) * (a5 ^ 3)
    + (510097159618560000 : R) * (h ^ 48) * (a7 ^ 7) * (a6 ^ 3) * a4
    + (1366937175903436800 : R) * (h ^ 48) * (a7 ^ 7) * (a6 ^ 2) * (a5 ^ 2)
    + (983230756945920000 : R) * (h ^ 48) * (a7 ^ 6) * (a6 ^ 4) * a5
    - (848548098736128 : R) * (h ^ 46) * (a7 ^ 10) * b3
    - (2181980825321472 : R) * (h ^ 46) * (a7 ^ 9) * a6 * b4
    - (12627203850240000 : R) * (h ^ 46) * (a7 ^ 9) * a5 * b5
    - (14425317678514176 : R) * (h ^ 46) * (a7 ^ 9) * a4 * b6
    - (16829537291599872 : R) * (h ^ 46) * (a7 ^ 9) * a3 * b7
    - (19233756904685568 : R) * (h ^ 46) * (a7 ^ 9) * a2 * b8
    - (47925650270453760 : R) * (h ^ 46) * (a7 ^ 8) * (a6 ^ 2) * b5
    - (302165380363714560 : R) * (h ^ 46) * (a7 ^ 8) * a6 * a5 * b6
    - (351617118413783040 : R) * (h ^ 46) * (a7 ^ 8) * a6 * a4 * b7
    - (247291160203100160 : R) * (h ^ 46) * (a7 ^ 8) * a6 * a3 * b8
    - (338212473406488576 : R) * (h ^ 46) * (a7 ^ 8) * (a5 ^ 2) * b7
    - (479126622893506560 : R) * (h ^ 46) * (a7 ^ 8) * a5 * a4 * b8
    - (228857504166051840 : R) * (h ^ 46) * (a7 ^ 7) * (a6 ^ 3) * b6
    - (1436840867464740864 : R) * (h ^ 46) * (a7 ^ 7) * (a6 ^ 2) * a5 * b7
    - (1092938609826201600 : R) * (h ^ 46) * (a7 ^ 7) * (a6 ^ 2) * a4 * b8
    - (1858305183587500032 : R) * (h ^ 46) * (a7 ^ 7) * a6 * (a5 ^ 2) * b8
    - (250051106187509760 : R) * (h ^ 46) * (a7 ^ 6) * (a6 ^ 4) * b7
    - (1285030850341109760 : R) * (h ^ 46) * (a7 ^ 6) * (a6 ^ 3) * a5 * b8
    + (13148076009062400 : R) * (h ^ 40) * (a7 ^ 11) * a2
    + (76473503318016000 : R) * (h ^ 40) * (a7 ^ 10) * a6 * a3
    + (82812754250956800 : R) * (h ^ 40) * (a7 ^ 10) * a5 * a4
    + (39070485341798400 : R) * (h ^ 40) * (a7 ^ 9) * (a6 ^ 2) * a4
    + (35623755464048640 : R) * (h ^ 40) * (a7 ^ 9) * a6 * (a5 ^ 2)
    - (500431188079411200 : R) * (h ^ 40) * (a7 ^ 8) * (a6 ^ 3) * a5
    - (105346152529920000 : R) * (h ^ 40) * (a7 ^ 7) * (a6 ^ 5)
    + (212137024684032 : R) * (h ^ 38) * (a7 ^ 11) * b4
    + (9470402887680000 : R) * (h ^ 38) * (a7 ^ 10) * a6 * b5
    + (28288093425500160 : R) * (h ^ 38) * (a7 ^ 10) * a5 * b6
    + (32870190022656000 : R) * (h ^ 38) * (a7 ^ 10) * a4 * b7
    + (24042196130856960 : R) * (h ^ 38) * (a7 ^ 10) * a3 * b8
    + (95924357934612480 : R) * (h ^ 38) * (a7 ^ 9) * (a6 ^ 2) * b6
    + (389549514999988224 : R) * (h ^ 38) * (a7 ^ 9) * a6 * a5 * b7
    + (305250025875701760 : R) * (h ^ 38) * (a7 ^ 9) * a6 * a4 * b8
    + (251520405372665856 : R) * (h ^ 38) * (a7 ^ 9) * (a5 ^ 2) * b8
    + (269132479800016896 : R) * (h ^ 38) * (a7 ^ 8) * (a6 ^ 3) * b7
    + (1035073907016597504 : R) * (h ^ 38) * (a7 ^ 8) * (a6 ^ 2) * a5 * b8
    + (173403463420477440 : R) * (h ^ 38) * (a7 ^ 7) * (a6 ^ 4) * b8
    - (8804515184640000 : R) * (h ^ 32) * (a7 ^ 12) * a3
    - (54361592325734400 : R) * (h ^ 32) * (a7 ^ 11) * a6 * a4
    - (39693575226654720 : R) * (h ^ 32) * (a7 ^ 11) * (a5 ^ 2)
    - (21979549956833280 : R) * (h ^ 32) * (a7 ^ 10) * (a6 ^ 2) * a5
    + (65818243104768000 : R) * (h ^ 32) * (a7 ^ 9) * (a6 ^ 4)
    - (701599013928960 : R) * (h ^ 30) * (a7 ^ 12) * b5
    - (17835136238223360 : R) * (h ^ 30) * (a7 ^ 11) * a6 * b6
    - (35104706921496576 : R) * (h ^ 30) * (a7 ^ 11) * a5 * b7
    - (28362278248120320 : R) * (h ^ 30) * (a7 ^ 11) * a4 * b8
    - (108256870891782144 : R) * (h ^ 30) * (a7 ^ 10) * (a6 ^ 2) * b7
    - (276899072651034624 : R) * (h ^ 30) * (a7 ^ 10) * a6 * a5 * b8
    - (183594448003792896 : R) * (h ^ 30) * (a7 ^ 9) * (a6 ^ 3) * b8
    + (7065623435673600 : R) * (h ^ 24) * (a7 ^ 13) * a4
    + (43447490948628480 : R) * (h ^ 24) * (a7 ^ 12) * a6 * a5
    + (4027318555115520 : R) * (h ^ 24) * (a7 ^ 11) * (a6 ^ 3)
    + (1240918728376320 : R) * (h ^ 22) * (a7 ^ 13) * b6
    + (19281983205015552 : R) * (h ^ 22) * (a7 ^ 12) * a6 * b7
    + (24593151616352256 : R) * (h ^ 22) * (a7 ^ 12) * a5 * b8
    + (72533327399092224 : R) * (h ^ 22) * (a7 ^ 11) * (a6 ^ 2) * b8
    - (5501192049131520 : R) * (h ^ 16) * (a7 ^ 14) * a5
    - (11165947774894080 : R) * (h ^ 16) * (a7 ^ 13) * (a6 ^ 2)
    - (1282681370836992 : R) * (h ^ 14) * (a7 ^ 14) * b7
    - (12666166912745472 : R) * (h ^ 14) * (a7 ^ 13) * a6 * b8
    + (2765206657597440 : R) * (h ^ 8) * (a7 ^ 15) * a6
    + (824371827965952 : R) * (h ^ 6) * (a7 ^ 15) * b8
    - (210519335792640 : R) * (a7 ^ 17)

set_option maxHeartbeats 200000000 in
/-- Integer expansion of compact block `18` after the extra
`2^{34}` scale, on `λ = 0`. -/
def alignedSquareCompactBlock18Expansion810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    - (6890507429876858880 : R) * (h ^ 104) * (a5 ^ 2) * a4 * a1
    - (6890507429876858880 : R) * (h ^ 104) * (a5 ^ 2) * a3 * a2
    + (972777519512027136 : R) * (h ^ 102) * (a5 ^ 2) * a4 * b3
    + (1297036692682702848 : R) * (h ^ 102) * (a5 ^ 2) * a3 * b4
    + (1621295865853378560 : R) * (h ^ 102) * (a5 ^ 2) * a2 * b5
    + (1945555039024054272 : R) * (h ^ 102) * (a5 ^ 2) * a1 * b6
    + (2269814212194729984 : R) * (h ^ 102) * (a5 ^ 2) * a0 * b7
    + (10335761144815288320 : R) * (h ^ 96) * a7 * a6 * a5 * a4 * a1
    + (10335761144815288320 : R) * (h ^ 96) * a7 * a6 * a5 * a3 * a2
    + (4306567143673036800 : R) * (h ^ 96) * a7 * (a5 ^ 3) * a1
    + (5167880572407644160 : R) * (h ^ 96) * a7 * (a5 ^ 2) * a4 * a2
    + (2583940286203822080 : R) * (h ^ 96) * a7 * (a5 ^ 2) * (a3 ^ 2)
    - (1459166279268040704 : R) * (h ^ 94) * a7 * a6 * a5 * a4 * b3
    - (1945555039024054272 : R) * (h ^ 94) * a7 * a6 * a5 * a3 * b4
    - (2431943798780067840 : R) * (h ^ 94) * a7 * a6 * a5 * a2 * b5
    - (2918332558536081408 : R) * (h ^ 94) * a7 * a6 * a5 * a1 * b6
    - (3404721318292094976 : R) * (h ^ 94) * a7 * a6 * a5 * a0 * b7
    - (607985949695016960 : R) * (h ^ 94) * a7 * (a5 ^ 3) * b3
    - (1134907106097364992 : R) * (h ^ 94) * a7 * (a5 ^ 2) * a4 * b4
    - (1418633882621706240 : R) * (h ^ 94) * a7 * (a5 ^ 2) * a3 * b5
    - (1702360659146047488 : R) * (h ^ 94) * a7 * (a5 ^ 2) * a2 * b6
    - (1986087435670388736 : R) * (h ^ 94) * a7 * (a5 ^ 2) * a1 * b7
    - (2269814212194729984 : R) * (h ^ 94) * a7 * (a5 ^ 2) * a0 * b8
    - (5512405943901487104 : R) * (h ^ 94) * (a5 ^ 2) * a4 * a3 * b8
    - (1837468647967162368 : R) * (h ^ 94) * a5 * (a4 ^ 3) * b8
    + (1063975411966279680 : R) * (h ^ 88) * (a7 ^ 3) * (a5 ^ 2) * a0
    - (3014597000571125760 : R) * (h ^ 88) * (a7 ^ 3) * a5 * a4 * a1
    - (3014597000571125760 : R) * (h ^ 88) * (a7 ^ 3) * a5 * a3 * a2
    - (3875910429305733120 : R) * (h ^ 88) * (a7 ^ 2) * (a6 ^ 2) * a4 * a1
    - (3875910429305733120 : R) * (h ^ 88) * (a7 ^ 2) * (a6 ^ 2) * a3 * a2
    - (8074813394386944000 : R) * (h ^ 88) * (a7 ^ 2) * a6 * (a5 ^ 2) * a1
    - (7751820858611466240 : R) * (h ^ 88) * (a7 ^ 2) * a6 * a5 * a4 * a2
    - (3875910429305733120 : R) * (h ^ 88) * (a7 ^ 2) * a6 * a5 * (a3 ^ 2)
    - (2153283571836518400 : R) * (h ^ 88) * (a7 ^ 2) * (a5 ^ 3) * a2
    + (1614962678877388800 : R) * (h ^ 88) * (a7 ^ 2) * (a5 ^ 2) * a4 * a3
    + (1291970143101911040 : R) * (h ^ 88) * (a7 ^ 2) * a5 * (a4 ^ 3)
    + (425590164786511872 : R) * (h ^ 86) * (a7 ^ 3) * a5 * a4 * b3
    + (567453553048682496 : R) * (h ^ 86) * (a7 ^ 3) * a5 * a3 * b4
    + (709316941310853120 : R) * (h ^ 86) * (a7 ^ 3) * a5 * a2 * b5
    + (851180329573023744 : R) * (h ^ 86) * (a7 ^ 3) * a5 * a1 * b6
    + (993043717835194368 : R) * (h ^ 86) * (a7 ^ 3) * a5 * a0 * b7
    + (547187354725515264 : R) * (h ^ 86) * (a7 ^ 2) * (a6 ^ 2) * a4 * b3
    + (729583139634020352 : R) * (h ^ 86) * (a7 ^ 2) * (a6 ^ 2) * a3 * b4
    + (911978924542525440 : R) * (h ^ 86) * (a7 ^ 2) * (a6 ^ 2) * a2 * b5
    + (1094374709451030528 : R) * (h ^ 86) * (a7 ^ 2) * (a6 ^ 2) * a1 * b6
    + (1276770494359535616 : R) * (h ^ 86) * (a7 ^ 2) * (a6 ^ 2) * a0 * b7
    + (1139973655678156800 : R) * (h ^ 86) * (a7 ^ 2) * a6 * (a5 ^ 2) * b3
    + (1702360659146047488 : R) * (h ^ 86) * (a7 ^ 2) * a6 * a5 * a4 * b4
    + (2127950823932559360 : R) * (h ^ 86) * (a7 ^ 2) * a6 * a5 * a3 * b5
    + (2553540988719071232 : R) * (h ^ 86) * (a7 ^ 2) * a6 * a5 * a2 * b6
    + (2979131153505583104 : R) * (h ^ 86) * (a7 ^ 2) * a6 * a5 * a1 * b7
    + (3404721318292094976 : R) * (h ^ 86) * (a7 ^ 2) * a6 * a5 * a0 * b8
    + (506654958079180800 : R) * (h ^ 86) * (a7 ^ 2) * (a5 ^ 3) * b4
    + (709316941310853120 : R) * (h ^ 86) * (a7 ^ 2) * (a5 ^ 2) * a4 * b5
    + (851180329573023744 : R) * (h ^ 86) * (a7 ^ 2) * (a5 ^ 2) * a3 * b6
    + (993043717835194368 : R) * (h ^ 86) * (a7 ^ 2) * (a5 ^ 2) * a2 * b7
    + (1134907106097364992 : R) * (h ^ 86) * (a7 ^ 2) * (a5 ^ 2) * a1 * b8
    + (8268608915852230656 : R) * (h ^ 86) * a7 * a6 * a5 * a4 * a3 * b8
    + (1378101485975371776 : R) * (h ^ 86) * a7 * a6 * (a4 ^ 3) * b8
    + (3445253714938429440 : R) * (h ^ 86) * a7 * (a5 ^ 3) * a3 * b8
    + (6201456686889172992 : R) * (h ^ 86) * a7 * (a5 ^ 2) * (a4 ^ 2) * b8
    - (1595963117949419520 : R) * (h ^ 80) * (a7 ^ 4) * a6 * a5 * a0
    + (2260947750428344320 : R) * (h ^ 80) * (a7 ^ 4) * a6 * a4 * a1
    + (2260947750428344320 : R) * (h ^ 80) * (a7 ^ 4) * a6 * a3 * a2
    + (1805156200250081280 : R) * (h ^ 80) * (a7 ^ 4) * (a5 ^ 2) * a1
    + (2260947750428344320 : R) * (h ^ 80) * (a7 ^ 4) * a5 * a4 * a2
    + (1130473875214172160 : R) * (h ^ 80) * (a7 ^ 4) * a5 * (a3 ^ 2)
    + (4844888036632166400 : R) * (h ^ 80) * (a7 ^ 3) * (a6 ^ 2) * a5 * a1
    + (2906932821979299840 : R) * (h ^ 80) * (a7 ^ 3) * (a6 ^ 2) * a4 * a2
    + (1453466410989649920 : R) * (h ^ 80) * (a7 ^ 3) * (a6 ^ 2) * (a3 ^ 2)
    + (3902826473953689600 : R) * (h ^ 80) * (a7 ^ 3) * a6 * (a5 ^ 2) * a2
    - (2422444018316083200 : R) * (h ^ 80) * (a7 ^ 3) * a6 * a5 * a4 * a3
    - (968977607326433280 : R) * (h ^ 80) * (a7 ^ 3) * a6 * (a4 ^ 3)
    - (1682252790497280000 : R) * (h ^ 80) * (a7 ^ 3) * (a5 ^ 3) * a3
    - (3983574607897559040 : R) * (h ^ 80) * (a7 ^ 3) * (a5 ^ 2) * (a4 ^ 2)
    - (319192623589883904 : R) * (h ^ 78) * (a7 ^ 4) * a6 * a4 * b3
    - (425590164786511872 : R) * (h ^ 78) * (a7 ^ 4) * a6 * a3 * b4
    - (531987705983139840 : R) * (h ^ 78) * (a7 ^ 4) * a6 * a2 * b5
    - (638385247179767808 : R) * (h ^ 78) * (a7 ^ 4) * a6 * a1 * b6
    - (744782788376395776 : R) * (h ^ 78) * (a7 ^ 4) * a6 * a0 * b7
    - (315867700427489280 : R) * (h ^ 78) * (a7 ^ 4) * (a5 ^ 2) * b3
    - (496521858917597184 : R) * (h ^ 78) * (a7 ^ 4) * a5 * a4 * b4
    - (620652323646996480 : R) * (h ^ 78) * (a7 ^ 4) * a5 * a3 * b5
    - (744782788376395776 : R) * (h ^ 78) * (a7 ^ 4) * a5 * a2 * b6
    - (868913253105795072 : R) * (h ^ 78) * (a7 ^ 4) * a5 * a1 * b7
    - (993043717835194368 : R) * (h ^ 78) * (a7 ^ 4) * a5 * a0 * b8
    - (683984193406894080 : R) * (h ^ 78) * (a7 ^ 3) * (a6 ^ 2) * a5 * b3
    - (638385247179767808 : R) * (h ^ 78) * (a7 ^ 3) * (a6 ^ 2) * a4 * b4
    - (797981558974709760 : R) * (h ^ 78) * (a7 ^ 3) * (a6 ^ 2) * a3 * b5
    - (957577870769651712 : R) * (h ^ 78) * (a7 ^ 3) * (a6 ^ 2) * a2 * b6
    - (1117174182564593664 : R) * (h ^ 78) * (a7 ^ 3) * (a6 ^ 2) * a1 * b7
    - (1276770494359535616 : R) * (h ^ 78) * (a7 ^ 3) * (a6 ^ 2) * a0 * b8
    - (924645298494504960 : R) * (h ^ 78) * (a7 ^ 3) * a6 * (a5 ^ 2) * b4
    - (1063975411966279680 : R) * (h ^ 78) * (a7 ^ 3) * a6 * a5 * a4 * b5
    - (1276770494359535616 : R) * (h ^ 78) * (a7 ^ 3) * a6 * a5 * a3 * b6
    - (1489565576752791552 : R) * (h ^ 78) * (a7 ^ 3) * a6 * a5 * a2 * b7
    - (1702360659146047488 : R) * (h ^ 78) * (a7 ^ 3) * a6 * a5 * a1 * b8
    - (253327479039590400 : R) * (h ^ 78) * (a7 ^ 3) * (a5 ^ 3) * b5
    - (319192623589883904 : R) * (h ^ 78) * (a7 ^ 3) * (a5 ^ 2) * a4 * b6
    - (372391394188197888 : R) * (h ^ 78) * (a7 ^ 3) * (a5 ^ 2) * a3 * b7
    - (425590164786511872 : R) * (h ^ 78) * (a7 ^ 3) * (a5 ^ 2) * a2 * b8
    - (2411677600456900608 : R) * (h ^ 78) * (a7 ^ 3) * a5 * a4 * a3 * b8
    - (401946266742816768 : R) * (h ^ 78) * (a7 ^ 3) * (a4 ^ 3) * b8
    - (3100728343444586496 : R) * (h ^ 78) * (a7 ^ 2) * (a6 ^ 2) * a4 * a3 * b8
    - (6459850715509555200 : R) * (h ^ 78) * (a7 ^ 2) * a6 * (a5 ^ 2) * a3 * b8
    - (8010214887231848448 : R) * (h ^ 78) * (a7 ^ 2) * a6 * a5 * (a4 ^ 2) * b8
    - (4737223858040340480 : R) * (h ^ 78) * (a7 ^ 2) * (a5 ^ 3) * a4 * b8
    + (465489242735247360 : R) * (h ^ 72) * (a7 ^ 6) * a5 * a0
    - (329721546937466880 : R) * (h ^ 72) * (a7 ^ 6) * a4 * a1
    - (329721546937466880 : R) * (h ^ 72) * (a7 ^ 6) * a3 * a2
    + (598486169231032320 : R) * (h ^ 72) * (a7 ^ 5) * (a6 ^ 2) * a0
    - (2001188128366264320 : R) * (h ^ 72) * (a7 ^ 5) * a6 * a5 * a1
    - (1695710812821258240 : R) * (h ^ 72) * (a7 ^ 5) * a6 * a4 * a2
    - (847855406410629120 : R) * (h ^ 72) * (a7 ^ 5) * a6 * (a3 ^ 2)
    - (936173677911736320 : R) * (h ^ 72) * (a7 ^ 5) * (a5 ^ 2) * a2
    + (706546172008857600 : R) * (h ^ 72) * (a7 ^ 5) * a5 * a4 * a3
    + (282618468803543040 : R) * (h ^ 72) * (a7 ^ 5) * (a4 ^ 3)
    - (908416506868531200 : R) * (h ^ 72) * (a7 ^ 4) * (a6 ^ 3) * a1
    - (2220573683456409600 : R) * (h ^ 72) * (a7 ^ 4) * (a6 ^ 2) * a5 * a2
    + (908416506868531200 : R) * (h ^ 72) * (a7 ^ 4) * (a6 ^ 2) * a4 * a3
    + (3229925357754777600 : R) * (h ^ 72) * (a7 ^ 4) * a6 * (a5 ^ 2) * a3
    + (5066945404977807360 : R) * (h ^ 72) * (a7 ^ 4) * a6 * a5 * (a4 ^ 2)
    + (3120578926372454400 : R) * (h ^ 72) * (a7 ^ 4) * (a5 ^ 3) * a4
    + (46548924273524736 : R) * (h ^ 70) * (a7 ^ 6) * a4 * b3
    + (62065232364699648 : R) * (h ^ 70) * (a7 ^ 6) * a3 * b4
    + (77581540455874560 : R) * (h ^ 70) * (a7 ^ 6) * a2 * b5
    + (93097848547049472 : R) * (h ^ 70) * (a7 ^ 6) * a1 * b6
    + (108614156638224384 : R) * (h ^ 70) * (a7 ^ 6) * a0 * b7
    + (374053855769395200 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a5 * b3
    + (372391394188197888 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a4 * b4
    + (465489242735247360 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a3 * b5
    + (558587091282296832 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a2 * b6
    + (651684939829346304 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a1 * b7
    + (744782788376395776 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a0 * b8
    + (255464929643986944 : R) * (h ^ 70) * (a7 ^ 5) * (a5 ^ 2) * b4
    + (310326161823498240 : R) * (h ^ 70) * (a7 ^ 5) * a5 * a4 * b5
    + (372391394188197888 : R) * (h ^ 70) * (a7 ^ 5) * a5 * a3 * b6
    + (434456626552897536 : R) * (h ^ 70) * (a7 ^ 5) * a5 * a2 * b7
    + (496521858917597184 : R) * (h ^ 70) * (a7 ^ 5) * a5 * a1 * b8
    + (128247036263792640 : R) * (h ^ 70) * (a7 ^ 4) * (a6 ^ 3) * b3
    + (531987705983139840 : R) * (h ^ 70) * (a7 ^ 4) * (a6 ^ 2) * a5 * b4
    + (398990779487354880 : R) * (h ^ 70) * (a7 ^ 4) * (a6 ^ 2) * a4 * b5
    + (478788935384825856 : R) * (h ^ 70) * (a7 ^ 4) * (a6 ^ 2) * a3 * b6
    + (558587091282296832 : R) * (h ^ 70) * (a7 ^ 4) * (a6 ^ 2) * a2 * b7
    + (638385247179767808 : R) * (h ^ 70) * (a7 ^ 4) * (a6 ^ 2) * a1 * b8
    + (453218692969267200 : R) * (h ^ 70) * (a7 ^ 4) * a6 * (a5 ^ 2) * b5
    + (478788935384825856 : R) * (h ^ 70) * (a7 ^ 4) * a6 * a5 * a4 * b6
    + (558587091282296832 : R) * (h ^ 70) * (a7 ^ 4) * a6 * a5 * a3 * b7
    + (638385247179767808 : R) * (h ^ 70) * (a7 ^ 4) * a6 * a5 * a2 * b8
    + (1808758200342675456 : R) * (h ^ 70) * (a7 ^ 4) * a6 * a4 * a3 * b8
    + (97372749755842560 : R) * (h ^ 70) * (a7 ^ 4) * (a5 ^ 3) * b6
    + (116372310683811840 : R) * (h ^ 70) * (a7 ^ 4) * (a5 ^ 2) * a4 * b7
    + (1922913895584890880 : R) * (h ^ 70) * (a7 ^ 4) * (a5 ^ 2) * a3 * b8
    + (2242106519174774784 : R) * (h ^ 70) * (a7 ^ 4) * a5 * (a4 ^ 2) * b8
    + (3875910429305733120 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 2) * a5 * a3 * b8
    + (2519341779048726528 : R) * (h ^ 70) * (a7 ^ 3) * (a6 ^ 2) * (a4 ^ 2) * b8
    + (7967149215795118080 : R) * (h ^ 70) * (a7 ^ 3) * a6 * (a5 ^ 2) * a4 * b8
    + (986921637091737600 : R) * (h ^ 70) * (a7 ^ 3) * (a5 ^ 4) * b8
    - (349116932051435520 : R) * (h ^ 64) * (a7 ^ 7) * a6 * a0
    + (171527937101660160 : R) * (h ^ 64) * (a7 ^ 7) * a5 * a1
    + (247291160203100160 : R) * (h ^ 64) * (a7 ^ 7) * a4 * a2
    + (123645580101550080 : R) * (h ^ 64) * (a7 ^ 7) * (a3 ^ 2)
    + (485490733634027520 : R) * (h ^ 64) * (a7 ^ 6) * (a6 ^ 2) * a1
    + (992108583195770880 : R) * (h ^ 64) * (a7 ^ 6) * a6 * a5 * a2
    - (529909629006643200 : R) * (h ^ 64) * (a7 ^ 6) * a6 * a4 * a3
    - (936801430331719680 : R) * (h ^ 64) * (a7 ^ 6) * (a5 ^ 2) * a3
    - (1411620372826030080 : R) * (h ^ 64) * (a7 ^ 6) * a5 * (a4 ^ 2)
    + (378506877861888000 : R) * (h ^ 64) * (a7 ^ 5) * (a6 ^ 3) * a2
    - (2006086452668006400 : R) * (h ^ 64) * (a7 ^ 5) * (a6 ^ 2) * a5 * a3
    - (1559448336790978560 : R) * (h ^ 64) * (a7 ^ 5) * (a6 ^ 2) * (a4 ^ 2)
    - (5234750120829911040 : R) * (h ^ 64) * (a7 ^ 5) * a6 * (a5 ^ 2) * a4
    - (667644076228608000 : R) * (h ^ 64) * (a7 ^ 5) * (a5 ^ 4)
    - (50912885924167680 : R) * (h ^ 62) * (a7 ^ 7) * a5 * b3
    - (54307078319112192 : R) * (h ^ 62) * (a7 ^ 7) * a4 * b4
    - (67883847898890240 : R) * (h ^ 62) * (a7 ^ 7) * a3 * b5
    - (81460617478668288 : R) * (h ^ 62) * (a7 ^ 7) * a2 * b6
    - (95037387058446336 : R) * (h ^ 62) * (a7 ^ 7) * a1 * b7
    - (108614156638224384 : R) * (h ^ 62) * (a7 ^ 7) * a0 * b8
    - (102864810336583680 : R) * (h ^ 62) * (a7 ^ 6) * (a6 ^ 2) * b3
    - (288991238198132736 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a5 * b4
    - (232744621367623680 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a4 * b5
    - (279293545641148416 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a3 * b6
    - (325842469914673152 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a2 * b7
    - (372391394188197888 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a1 * b8
    - (125030964752547840 : R) * (h ^ 62) * (a7 ^ 6) * (a5 ^ 2) * b5
    - (139646772820574208 : R) * (h ^ 62) * (a7 ^ 6) * a5 * a4 * b6
    - (162921234957336576 : R) * (h ^ 62) * (a7 ^ 6) * a5 * a3 * b7
    - (186195697094098944 : R) * (h ^ 62) * (a7 ^ 6) * a5 * a2 * b8
    - (263777237549973504 : R) * (h ^ 62) * (a7 ^ 6) * a4 * a3 * b8
    - (92622859523850240 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 3) * b4
    - (252337918574592000 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 2) * a5 * b5
    - (179545850769309696 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 2) * a4 * b6
    - (209470159230861312 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 2) * a3 * b7
    - (239394467692412928 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 2) * a2 * b8
    - (171649158258622464 : R) * (h ^ 62) * (a7 ^ 5) * a6 * (a5 ^ 2) * b6
    - (174558466025717760 : R) * (h ^ 62) * (a7 ^ 5) * a6 * a5 * a4 * b7
    - (2319133905770250240 : R) * (h ^ 62) * (a7 ^ 5) * a6 * a5 * a3 * b8
    - (1398961420577538048 : R) * (h ^ 62) * (a7 ^ 5) * a6 * (a4 ^ 2) * b8
    - (31586770042748928 : R) * (h ^ 62) * (a7 ^ 5) * (a5 ^ 3) * b7
    - (2170343594253090816 : R) * (h ^ 62) * (a7 ^ 5) * (a5 ^ 2) * a4 * b8
    - (726733205494824960 : R) * (h ^ 62) * (a7 ^ 4) * (a6 ^ 3) * a3 * b8
    - (4259464065539112960 : R) * (h ^ 62) * (a7 ^ 4) * (a6 ^ 2) * a5 * a4 * b8
    - (1985058292786790400 : R) * (h ^ 62) * (a7 ^ 4) * a6 * (a5 ^ 3) * b8
    + (50912885924167680 : R) * (h ^ 56) * (a7 ^ 9) * a0
    - (51367465262776320 : R) * (h ^ 56) * (a7 ^ 8) * a6 * a1
    - (100462033832509440 : R) * (h ^ 56) * (a7 ^ 8) * a5 * a2
    + (77278487563468800 : R) * (h ^ 56) * (a7 ^ 8) * a4 * a3
    - (217483743571476480 : R) * (h ^ 56) * (a7 ^ 7) * (a6 ^ 2) * a2
    + (1162326898869534720 : R) * (h ^ 56) * (a7 ^ 7) * a6 * a5 * a3
    + (859999168742031360 : R) * (h ^ 56) * (a7 ^ 7) * a6 * (a4 ^ 2)
    + (1409339745191854080 : R) * (h ^ 56) * (a7 ^ 7) * (a5 ^ 2) * a4
    + (397432221754982400 : R) * (h ^ 56) * (a7 ^ 6) * (a6 ^ 3) * a3
    + (2799058361788661760 : R) * (h ^ 56) * (a7 ^ 6) * (a6 ^ 2) * a5 * a4
    + (1344356546405990400 : R) * (h ^ 56) * (a7 ^ 6) * a6 * (a5 ^ 3)
    + (27274760316518400 : R) * (h ^ 54) * (a7 ^ 8) * a6 * b3
    + (39033212541861888 : R) * (h ^ 54) * (a7 ^ 8) * a5 * b4
    + (33941923949445120 : R) * (h ^ 54) * (a7 ^ 8) * a4 * b5
    + (40730308739334144 : R) * (h ^ 54) * (a7 ^ 8) * a3 * b6
    + (47518693529223168 : R) * (h ^ 54) * (a7 ^ 8) * a2 * b7
    + (54307078319112192 : R) * (h ^ 54) * (a7 ^ 8) * a1 * b8
    + (73044405723856896 : R) * (h ^ 54) * (a7 ^ 7) * (a6 ^ 2) * b4
    + (136460388123279360 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a5 * b5
    + (104735079615430656 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a4 * b6
    + (122190926218002432 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a3 * b7
    + (139646772820574208 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a2 * b8
    + (47320781436223488 : R) * (h ^ 54) * (a7 ^ 7) * (a5 ^ 2) * b6
    + (50912885924167680 : R) * (h ^ 54) * (a7 ^ 7) * a5 * a4 * b7
    + (346692508912189440 : R) * (h ^ 54) * (a7 ^ 7) * a5 * a3 * b8
    + (193711408825761792 : R) * (h ^ 54) * (a7 ^ 7) * (a4 ^ 2) * b8
    + (41190454355558400 : R) * (h ^ 54) * (a7 ^ 6) * (a6 ^ 3) * b5
    + (93157222174949376 : R) * (h ^ 54) * (a7 ^ 6) * (a6 ^ 2) * a5 * b6
    + (65459424759644160 : R) * (h ^ 54) * (a7 ^ 6) * (a6 ^ 2) * a4 * b7
    + (657711363061186560 : R) * (h ^ 54) * (a7 ^ 6) * (a6 ^ 2) * a3 * b8
    + (55060381223092224 : R) * (h ^ 54) * (a7 ^ 6) * a6 * (a5 ^ 2) * b7
    + (2298734116784308224 : R) * (h ^ 54) * (a7 ^ 6) * a6 * a5 * a4 * b8
    + (520829587106562048 : R) * (h ^ 54) * (a7 ^ 6) * (a5 ^ 3) * b8
    + (711592930380349440 : R) * (h ^ 54) * (a7 ^ 5) * (a6 ^ 3) * a4 * b8
    + (1425709239946444800 : R) * (h ^ 54) * (a7 ^ 5) * (a6 ^ 2) * (a5 ^ 2) * b8
    - (3778690752184320 : R) * (h ^ 48) * (a7 ^ 10) * a1
    + (30267407629025280 : R) * (h ^ 48) * (a7 ^ 9) * a6 * a2
    - (168355352134287360 : R) * (h ^ 48) * (a7 ^ 9) * a5 * a3
    - (118171687232471040 : R) * (h ^ 48) * (a7 ^ 9) * (a4 ^ 2)
    - (344794369590558720 : R) * (h ^ 48) * (a7 ^ 8) * (a6 ^ 2) * a3
    - (1487639876626022400 : R) * (h ^ 48) * (a7 ^ 8) * a6 * a5 * a4
    - (348695740714844160 : R) * (h ^ 48) * (a7 ^ 8) * (a5 ^ 3)
    - (471241062938050560 : R) * (h ^ 48) * (a7 ^ 7) * (a6 ^ 3) * a4
    - (968445332029440000 : R) * (h ^ 48) * (a7 ^ 7) * (a6 ^ 2) * (a5 ^ 2)
    - (2386541527695360 : R) * (h ^ 46) * (a7 ^ 10) * b3
    - (18971111064600576 : R) * (h ^ 46) * (a7 ^ 9) * a6 * b4
    - (18334699990548480 : R) * (h ^ 46) * (a7 ^ 9) * a5 * b5
    - (15273865777250304 : R) * (h ^ 46) * (a7 ^ 9) * a4 * b6
    - (17819510073458688 : R) * (h ^ 46) * (a7 ^ 9) * a3 * b7
    - (20365154369667072 : R) * (h ^ 46) * (a7 ^ 9) * a2 * b8
    - (32015373419151360 : R) * (h ^ 46) * (a7 ^ 8) * (a6 ^ 2) * b5
    - (50226378351575040 : R) * (h ^ 46) * (a7 ^ 8) * a6 * a5 * b6
    - (38184664443125760 : R) * (h ^ 46) * (a7 ^ 8) * a6 * a4 * b7
    - (198196591633367040 : R) * (h ^ 46) * (a7 ^ 8) * a6 * a3 * b8
    - (15175508878688256 : R) * (h ^ 46) * (a7 ^ 8) * (a5 ^ 2) * b7
    - (309723844199841792 : R) * (h ^ 46) * (a7 ^ 8) * a5 * a4 * b8
    - (14394393913982976 : R) * (h ^ 46) * (a7 ^ 7) * (a6 ^ 3) * b6
    - (29287897387499520 : R) * (h ^ 46) * (a7 ^ 7) * (a6 ^ 2) * a5 * b7
    - (569471019446697984 : R) * (h ^ 46) * (a7 ^ 7) * (a6 ^ 2) * a4 * b8
    - (736946706444189696 : R) * (h ^ 46) * (a7 ^ 7) * a6 * (a5 ^ 2) * b8
    - (430551573567897600 : R) * (h ^ 46) * (a7 ^ 6) * (a6 ^ 3) * a5 * b8
    + (281744485908480 : R) * (h ^ 40) * (a7 ^ 11) * a2
    + (99702034000773120 : R) * (h ^ 40) * (a7 ^ 10) * a6 * a3
    + (196912633306152960 : R) * (h ^ 40) * (a7 ^ 10) * a5 * a4
    + (369550389286010880 : R) * (h ^ 40) * (a7 ^ 9) * (a6 ^ 2) * a4
    + (493938997387591680 : R) * (h ^ 40) * (a7 ^ 9) * a6 * (a5 ^ 2)
    + (294082101588787200 : R) * (h ^ 40) * (a7 ^ 8) * (a6 ^ 3) * a5
    + (1617544813215744 : R) * (h ^ 38) * (a7 ^ 11) * b4
    + (8163487289180160 : R) * (h ^ 38) * (a7 ^ 10) * a6 * b5
    + (6724527216132096 : R) * (h ^ 38) * (a7 ^ 10) * a5 * b6
    + (5568596897955840 : R) * (h ^ 38) * (a7 ^ 10) * a4 * b7
    + (19887846064128000 : R) * (h ^ 38) * (a7 ^ 10) * a3 * b8
    + (11051844205805568 : R) * (h ^ 38) * (a7 ^ 9) * (a6 ^ 2) * b6
    + (15758953342304256 : R) * (h ^ 38) * (a7 ^ 9) * a6 * a5 * b7
    + (151794458604601344 : R) * (h ^ 38) * (a7 ^ 9) * a6 * a4 * b8
    + (94842364404695040 : R) * (h ^ 38) * (a7 ^ 9) * (a5 ^ 2) * b8
    + (4320127214419968 : R) * (h ^ 38) * (a7 ^ 8) * (a6 ^ 3) * b7
    + (327603153102962688 : R) * (h ^ 38) * (a7 ^ 8) * (a6 ^ 2) * a5 * b8
    + (46130525739417600 : R) * (h ^ 38) * (a7 ^ 7) * (a6 ^ 4) * b8
    - (9609351455047680 : R) * (h ^ 32) * (a7 ^ 12) * a3
    - (96155420967567360 : R) * (h ^ 32) * (a7 ^ 11) * a6 * a4
    - (62603553952235520 : R) * (h ^ 32) * (a7 ^ 11) * (a5 ^ 2)
    - (220453494010675200 : R) * (h ^ 32) * (a7 ^ 10) * (a6 ^ 2) * a5
    - (31714736445849600 : R) * (h ^ 32) * (a7 ^ 9) * (a6 ^ 4)
    - (679501407191040 : R) * (h ^ 30) * (a7 ^ 12) * b5
    - (2773339839922176 : R) * (h ^ 30) * (a7 ^ 11) * a6 * b6
    - (2104856231804928 : R) * (h ^ 30) * (a7 ^ 11) * a5 * b7
    - (13484788291731456 : R) * (h ^ 30) * (a7 ^ 11) * a4 * b8
    - (3282991262466048 : R) * (h ^ 30) * (a7 ^ 10) * (a6 ^ 2) * b7
    - (82619955450740736 : R) * (h ^ 30) * (a7 ^ 10) * a6 * a5 * b8
    - (45719925792178176 : R) * (h ^ 30) * (a7 ^ 9) * (a6 ^ 3) * b8
    + (8300280969953280 : R) * (h ^ 24) * (a7 ^ 13) * a4
    + (54665032992030720 : R) * (h ^ 24) * (a7 ^ 12) * a6 * a5
    + (30966849428520960 : R) * (h ^ 24) * (a7 ^ 11) * (a6 ^ 3)
    + (225869108871168 : R) * (h ^ 22) * (a7 ^ 13) * b6
    + (812545770258432 : R) * (h ^ 22) * (a7 ^ 12) * a6 * b7
    + (6902109161127936 : R) * (h ^ 22) * (a7 ^ 12) * a5 * b8
    + (16842069368635392 : R) * (h ^ 22) * (a7 ^ 11) * (a6 ^ 2) * b8
    - (4480405034434560 : R) * (h ^ 16) * (a7 ^ 14) * a5
    - (11228531887964160 : R) * (h ^ 16) * (a7 ^ 13) * (a6 ^ 2)
    - (64900929945600 : R) * (h ^ 14) * (a7 ^ 14) * b7
    - (2727903772016640 : R) * (h ^ 14) * (a7 ^ 13) * a6 * b8
    + (1789756617277440 : R) * (h ^ 8) * (a7 ^ 15) * a6
    + (163454448697344 : R) * (h ^ 6) * (a7 ^ 15) * b8
    - (105640874035200 : R) * (a7 ^ 17)

set_option maxHeartbeats 200000000 in
/-- Integer expansion of compact block `19` after the extra
`2^{34}` scale, on `λ = 0`. -/
def alignedSquareCompactBlock19Expansion810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    - (6890507429876858880 : R) * (h ^ 104) * a5 * (a4 ^ 2) * a2
    - (6890507429876858880 : R) * (h ^ 104) * a5 * a4 * (a3 ^ 2)
    + (1297036692682702848 : R) * (h ^ 102) * a5 * (a4 ^ 2) * b4
    + (3242591731706757120 : R) * (h ^ 102) * a5 * a4 * a3 * b5
    + (3891110078048108544 : R) * (h ^ 102) * a5 * a4 * a2 * b6
    + (4539628424389459968 : R) * (h ^ 102) * a5 * a4 * a1 * b7
    + (5188146770730811392 : R) * (h ^ 102) * a5 * a4 * a0 * b8
    + (1945555039024054272 : R) * (h ^ 102) * a5 * (a3 ^ 2) * b6
    + (4539628424389459968 : R) * (h ^ 102) * a5 * a3 * a2 * b7
    - (3647915698170101760 : R) * (h ^ 96) * (a7 ^ 2) * a5 * a4 * a0
    + (5167880572407644160 : R) * (h ^ 96) * a7 * a6 * (a4 ^ 2) * a2
    + (5167880572407644160 : R) * (h ^ 96) * a7 * a6 * a4 * (a3 ^ 2)
    + (8613134287346073600 : R) * (h ^ 96) * a7 * (a5 ^ 2) * a4 * a2
    + (4306567143673036800 : R) * (h ^ 96) * a7 * (a5 ^ 2) * (a3 ^ 2)
    + (9474447716080680960 : R) * (h ^ 96) * a7 * a5 * (a4 ^ 2) * a3
    - (972777519512027136 : R) * (h ^ 94) * a7 * a6 * (a4 ^ 2) * b4
    - (2431943798780067840 : R) * (h ^ 94) * a7 * a6 * a4 * a3 * b5
    - (2918332558536081408 : R) * (h ^ 94) * a7 * a6 * a4 * a2 * b6
    - (3404721318292094976 : R) * (h ^ 94) * a7 * a6 * a4 * a1 * b7
    - (3891110078048108544 : R) * (h ^ 94) * a7 * a6 * a4 * a0 * b8
    - (1459166279268040704 : R) * (h ^ 94) * a7 * a6 * (a3 ^ 2) * b6
    - (3404721318292094976 : R) * (h ^ 94) * a7 * a6 * a3 * a2 * b7
    - (1621295865853378560 : R) * (h ^ 94) * a7 * (a5 ^ 2) * a4 * b4
    - (2026619832316723200 : R) * (h ^ 94) * a7 * (a5 ^ 2) * a3 * b5
    - (2431943798780067840 : R) * (h ^ 94) * a7 * (a5 ^ 2) * a2 * b6
    - (2837267765243412480 : R) * (h ^ 94) * a7 * (a5 ^ 2) * a1 * b7
    - (3242591731706757120 : R) * (h ^ 94) * a7 * (a5 ^ 2) * a0 * b8
    - (2431943798780067840 : R) * (h ^ 94) * a7 * a5 * (a4 ^ 2) * b5
    - (5836665117072162816 : R) * (h ^ 94) * a7 * a5 * a4 * a3 * b6
    - (6809442636584189952 : R) * (h ^ 94) * a7 * a5 * a4 * a2 * b7
    - (5188146770730811392 : R) * (h ^ 94) * a7 * a5 * a4 * a1 * b8
    - (3404721318292094976 : R) * (h ^ 94) * a7 * a5 * (a3 ^ 2) * b7
    - (4539628424389459968 : R) * (h ^ 94) * a7 * a5 * a3 * a2 * b8
    + (2735936773627576320 : R) * (h ^ 88) * (a7 ^ 3) * a6 * a4 * a0
    + (2279947311356313600 : R) * (h ^ 88) * (a7 ^ 3) * (a5 ^ 2) * a0
    + (2583940286203822080 : R) * (h ^ 88) * (a7 ^ 3) * a5 * a4 * a1
    + (2127950823932559360 : R) * (h ^ 88) * (a7 ^ 3) * a5 * a3 * a2
    - (1507298500285562880 : R) * (h ^ 88) * (a7 ^ 3) * (a4 ^ 2) * a2
    - (1507298500285562880 : R) * (h ^ 88) * (a7 ^ 3) * a4 * (a3 ^ 2)
    - (9689776073264332800 : R) * (h ^ 88) * (a7 ^ 2) * a6 * a5 * a4 * a2
    - (4844888036632166400 : R) * (h ^ 88) * (a7 ^ 2) * a6 * a5 * (a3 ^ 2)
    - (7105835787060510720 : R) * (h ^ 88) * (a7 ^ 2) * a6 * (a4 ^ 2) * a3
    - (2691604464795648000 : R) * (h ^ 88) * (a7 ^ 2) * (a5 ^ 3) * a2
    - (9689776073264332800 : R) * (h ^ 88) * (a7 ^ 2) * (a5 ^ 2) * a4 * a3
    - (2368611929020170240 : R) * (h ^ 88) * (a7 ^ 2) * a5 * (a4 ^ 3)
    + (283726776524341248 : R) * (h ^ 86) * (a7 ^ 3) * (a4 ^ 2) * b4
    + (709316941310853120 : R) * (h ^ 86) * (a7 ^ 3) * a4 * a3 * b5
    + (851180329573023744 : R) * (h ^ 86) * (a7 ^ 3) * a4 * a2 * b6
    + (993043717835194368 : R) * (h ^ 86) * (a7 ^ 3) * a4 * a1 * b7
    + (1134907106097364992 : R) * (h ^ 86) * (a7 ^ 3) * a4 * a0 * b8
    + (425590164786511872 : R) * (h ^ 86) * (a7 ^ 3) * (a3 ^ 2) * b6
    + (993043717835194368 : R) * (h ^ 86) * (a7 ^ 3) * a3 * a2 * b7
    + (1823957849085050880 : R) * (h ^ 86) * (a7 ^ 2) * a6 * a5 * a4 * b4
    + (2279947311356313600 : R) * (h ^ 86) * (a7 ^ 2) * a6 * a5 * a3 * b5
    + (2735936773627576320 : R) * (h ^ 86) * (a7 ^ 2) * a6 * a5 * a2 * b6
    + (3191926235898839040 : R) * (h ^ 86) * (a7 ^ 2) * a6 * a5 * a1 * b7
    + (3647915698170101760 : R) * (h ^ 86) * (a7 ^ 2) * a6 * a5 * a0 * b8
    + (1823957849085050880 : R) * (h ^ 86) * (a7 ^ 2) * a6 * (a4 ^ 2) * b5
    + (4377498837804122112 : R) * (h ^ 86) * (a7 ^ 2) * a6 * a4 * a3 * b6
    + (5107081977438142464 : R) * (h ^ 86) * (a7 ^ 2) * a6 * a4 * a2 * b7
    + (3891110078048108544 : R) * (h ^ 86) * (a7 ^ 2) * a6 * a4 * a1 * b8
    + (2553540988719071232 : R) * (h ^ 86) * (a7 ^ 2) * a6 * (a3 ^ 2) * b7
    + (3404721318292094976 : R) * (h ^ 86) * (a7 ^ 2) * a6 * a3 * a2 * b8
    + (506654958079180800 : R) * (h ^ 86) * (a7 ^ 2) * (a5 ^ 3) * b4
    + (2533274790395904000 : R) * (h ^ 86) * (a7 ^ 2) * (a5 ^ 2) * a4 * b5
    + (3039929748475084800 : R) * (h ^ 86) * (a7 ^ 2) * (a5 ^ 2) * a3 * b6
    + (3546584706554265600 : R) * (h ^ 86) * (a7 ^ 2) * (a5 ^ 2) * a2 * b7
    + (3242591731706757120 : R) * (h ^ 86) * (a7 ^ 2) * (a5 ^ 2) * a1 * b8
    + (2371145203810566144 : R) * (h ^ 86) * (a7 ^ 2) * a5 * (a4 ^ 2) * b6
    + (5532672142224654336 : R) * (h ^ 86) * (a7 ^ 2) * a5 * a4 * a3 * b7
    + (5188146770730811392 : R) * (h ^ 86) * (a7 ^ 2) * a5 * a4 * a2 * b8
    + (2553540988719071232 : R) * (h ^ 86) * (a7 ^ 2) * a5 * (a3 ^ 2) * b8
    - (797981558974709760 : R) * (h ^ 80) * (a7 ^ 5) * a4 * a0
    - (2564940725275852800 : R) * (h ^ 80) * (a7 ^ 4) * a6 * a5 * a0
    - (1937955214652866560 : R) * (h ^ 80) * (a7 ^ 4) * a6 * a4 * a1
    - (1595963117949419520 : R) * (h ^ 80) * (a7 ^ 4) * a6 * a3 * a2
    - (1614962678877388800 : R) * (h ^ 80) * (a7 ^ 4) * (a5 ^ 2) * a1
    + (339221327401451520 : R) * (h ^ 80) * (a7 ^ 4) * a5 * a4 * a2
    + (198110005092679680 : R) * (h ^ 80) * (a7 ^ 4) * a5 * (a3 ^ 2)
    + (2072535437892648960 : R) * (h ^ 80) * (a7 ^ 4) * (a4 ^ 2) * a3
    + (2422444018316083200 : R) * (h ^ 80) * (a7 ^ 3) * (a6 ^ 2) * a4 * a2
    + (1211222009158041600 : R) * (h ^ 80) * (a7 ^ 3) * (a6 ^ 2) * (a3 ^ 2)
    + (4037406697193472000 : R) * (h ^ 80) * (a7 ^ 3) * a6 * (a5 ^ 2) * a2
    + (10631837635942809600 : R) * (h ^ 80) * (a7 ^ 3) * a6 * a5 * a4 * a3
    + (1776458946765127680 : R) * (h ^ 80) * (a7 ^ 3) * a6 * (a4 ^ 3)
    + (2355153906696192000 : R) * (h ^ 80) * (a7 ^ 3) * (a5 ^ 3) * a3
    + (3095345134514995200 : R) * (h ^ 80) * (a7 ^ 3) * (a5 ^ 2) * (a4 ^ 2)
    - (487655397151211520 : R) * (h ^ 78) * (a7 ^ 4) * a5 * a4 * b4
    - (609569246439014400 : R) * (h ^ 78) * (a7 ^ 4) * a5 * a3 * b5
    - (731483095726817280 : R) * (h ^ 78) * (a7 ^ 4) * a5 * a2 * b6
    - (853396945014620160 : R) * (h ^ 78) * (a7 ^ 4) * a5 * a1 * b7
    - (975310794302423040 : R) * (h ^ 78) * (a7 ^ 4) * a5 * a0 * b8
    - (531987705983139840 : R) * (h ^ 78) * (a7 ^ 4) * (a4 ^ 2) * b5
    - (1276770494359535616 : R) * (h ^ 78) * (a7 ^ 4) * a4 * a3 * b6
    - (1489565576752791552 : R) * (h ^ 78) * (a7 ^ 4) * a4 * a2 * b7
    - (1134907106097364992 : R) * (h ^ 78) * (a7 ^ 4) * a4 * a1 * b8
    - (744782788376395776 : R) * (h ^ 78) * (a7 ^ 4) * (a3 ^ 2) * b7
    - (993043717835194368 : R) * (h ^ 78) * (a7 ^ 4) * a3 * a2 * b8
    - (455989462271262720 : R) * (h ^ 78) * (a7 ^ 3) * (a6 ^ 2) * a4 * b4
    - (569986827839078400 : R) * (h ^ 78) * (a7 ^ 3) * (a6 ^ 2) * a3 * b5
    - (683984193406894080 : R) * (h ^ 78) * (a7 ^ 3) * (a6 ^ 2) * a2 * b6
    - (797981558974709760 : R) * (h ^ 78) * (a7 ^ 3) * (a6 ^ 2) * a1 * b7
    - (911978924542525440 : R) * (h ^ 78) * (a7 ^ 3) * (a6 ^ 2) * a0 * b8
    - (759982437118771200 : R) * (h ^ 78) * (a7 ^ 3) * a6 * (a5 ^ 2) * b4
    - (2786602269435494400 : R) * (h ^ 78) * (a7 ^ 3) * a6 * a5 * a4 * b5
    - (3343922723322593280 : R) * (h ^ 78) * (a7 ^ 3) * a6 * a5 * a3 * b6
    - (3901243177209692160 : R) * (h ^ 78) * (a7 ^ 3) * a6 * a5 * a2 * b7
    - (3647915698170101760 : R) * (h ^ 78) * (a7 ^ 3) * a6 * a5 * a1 * b8
    - (1778358902857924608 : R) * (h ^ 78) * (a7 ^ 3) * a6 * (a4 ^ 2) * b6
    - (4149504106668490752 : R) * (h ^ 78) * (a7 ^ 3) * a6 * a4 * a3 * b7
    - (3891110078048108544 : R) * (h ^ 78) * (a7 ^ 3) * a6 * a4 * a2 * b8
    - (1915155741539303424 : R) * (h ^ 78) * (a7 ^ 3) * a6 * (a3 ^ 2) * b8
    - (633318697598976000 : R) * (h ^ 78) * (a7 ^ 3) * (a5 ^ 3) * b5
    - (2127950823932559360 : R) * (h ^ 78) * (a7 ^ 3) * (a5 ^ 2) * a4 * b6
    - (2482609294587985920 : R) * (h ^ 78) * (a7 ^ 3) * (a5 ^ 2) * a3 * b7
    - (2533274790395904000 : R) * (h ^ 78) * (a7 ^ 3) * (a5 ^ 2) * a2 * b8
    - (1613696041482190848 : R) * (h ^ 78) * (a7 ^ 3) * a5 * (a4 ^ 2) * b7
    - (3343922723322593280 : R) * (h ^ 78) * (a7 ^ 3) * a5 * a4 * a3 * b8
    + (685765402243891200 : R) * (h ^ 72) * (a7 ^ 6) * a5 * a0
    + (565236937607086080 : R) * (h ^ 72) * (a7 ^ 6) * a4 * a1
    + (465489242735247360 : R) * (h ^ 72) * (a7 ^ 6) * a3 * a2
    + (641235181318963200 : R) * (h ^ 72) * (a7 ^ 5) * (a6 ^ 2) * a0
    + (1816833013737062400 : R) * (h ^ 72) * (a7 ^ 5) * a6 * a5 * a1
    + (452130176457768960 : R) * (h ^ 72) * (a7 ^ 5) * a6 * a4 * a2
    + (204690582184919040 : R) * (h ^ 72) * (a7 ^ 5) * a6 * (a3 ^ 2)
    + (44282830808678400 : R) * (h ^ 72) * (a7 ^ 5) * (a5 ^ 2) * a2
    - (1503290780402319360 : R) * (h ^ 72) * (a7 ^ 5) * a5 * a4 * a3
    - (518133859473162240 : R) * (h ^ 72) * (a7 ^ 5) * (a4 ^ 3)
    - (1892534389309440000 : R) * (h ^ 72) * (a7 ^ 4) * (a6 ^ 2) * a5 * a2
    - (2523379185745920000 : R) * (h ^ 72) * (a7 ^ 4) * (a6 ^ 2) * a4 * a3
    - (3364505580994560000 : R) * (h ^ 72) * (a7 ^ 4) * a6 * (a5 ^ 2) * a3
    - (3322449261232128000 : R) * (h ^ 72) * (a7 ^ 4) * a6 * a5 * (a4 ^ 2)
    - (1261689592872960000 : R) * (h ^ 72) * (a7 ^ 4) * (a5 ^ 3) * a4
    + (232744621367623680 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a4 * b4
    + (290930776709529600 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a3 * b5
    + (349116932051435520 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a2 * b6
    + (407303087393341440 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a1 * b7
    + (465489242735247360 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a0 * b8
    + (193953851139686400 : R) * (h ^ 70) * (a7 ^ 5) * (a5 ^ 2) * b4
    + (742566172934799360 : R) * (h ^ 70) * (a7 ^ 5) * a5 * a4 * b5
    + (891079407521759232 : R) * (h ^ 70) * (a7 ^ 5) * a5 * a3 * b6
    + (1039592642108719104 : R) * (h ^ 70) * (a7 ^ 5) * a5 * a2 * b7
    + (975310794302423040 : R) * (h ^ 70) * (a7 ^ 5) * a5 * a1 * b8
    + (518688013333561344 : R) * (h ^ 70) * (a7 ^ 5) * (a4 ^ 2) * b6
    + (1210272031111643136 : R) * (h ^ 70) * (a7 ^ 5) * a4 * a3 * b7
    + (1134907106097364992 : R) * (h ^ 70) * (a7 ^ 5) * a4 * a2 * b8
    + (558587091282296832 : R) * (h ^ 70) * (a7 ^ 5) * (a3 ^ 2) * b8
    + (356241767399424000 : R) * (h ^ 70) * (a7 ^ 4) * (a6 ^ 2) * a5 * b4
    + (664984632478924800 : R) * (h ^ 70) * (a7 ^ 4) * (a6 ^ 2) * a4 * b5
    + (797981558974709760 : R) * (h ^ 70) * (a7 ^ 4) * (a6 ^ 2) * a3 * b6
    + (930978485470494720 : R) * (h ^ 70) * (a7 ^ 4) * (a6 ^ 2) * a2 * b7
    + (911978924542525440 : R) * (h ^ 70) * (a7 ^ 4) * (a6 ^ 2) * a1 * b8
    + (910395627798528000 : R) * (h ^ 70) * (a7 ^ 4) * a6 * (a5 ^ 2) * b5
    + (2294196982052290560 : R) * (h ^ 70) * (a7 ^ 4) * a6 * a5 * a4 * b6
    + (2676563145727672320 : R) * (h ^ 70) * (a7 ^ 4) * a6 * a5 * a3 * b7
    + (2761269521531535360 : R) * (h ^ 70) * (a7 ^ 4) * a6 * a5 * a2 * b8
    + (1210272031111643136 : R) * (h ^ 70) * (a7 ^ 4) * a6 * (a4 ^ 2) * b7
    + (2507942042491944960 : R) * (h ^ 70) * (a7 ^ 4) * a6 * a4 * a3 * b8
    + (451239572039270400 : R) * (h ^ 70) * (a7 ^ 4) * (a5 ^ 3) * b6
    + (1280095417521930240 : R) * (h ^ 70) * (a7 ^ 4) * (a5 ^ 2) * a4 * b7
    + (1380634760765767680 : R) * (h ^ 70) * (a7 ^ 4) * (a5 ^ 2) * a3 * b8
    + (821414350785871872 : R) * (h ^ 70) * (a7 ^ 4) * a5 * (a4 ^ 2) * b8
    - (327297123798220800 : R) * (h ^ 64) * (a7 ^ 7) * a6 * a0
    - (485750493256089600 : R) * (h ^ 64) * (a7 ^ 7) * a5 * a1
    - (337947268302766080 : R) * (h ^ 64) * (a7 ^ 7) * a4 * a2
    - (162739403221893120 : R) * (h ^ 64) * (a7 ^ 7) * (a3 ^ 2)
    - (454208253434265600 : R) * (h ^ 64) * (a7 ^ 6) * (a6 ^ 2) * a1
    - (229052323882598400 : R) * (h ^ 64) * (a7 ^ 6) * a6 * a5 * a2
    + (273724794124369920 : R) * (h ^ 64) * (a7 ^ 6) * a6 * a4 * a3
    + (320895904540262400 : R) * (h ^ 64) * (a7 ^ 6) * (a5 ^ 2) * a3
    + (579195924916469760 : R) * (h ^ 64) * (a7 ^ 6) * a5 * (a4 ^ 2)
    + (283880158396416000 : R) * (h ^ 64) * (a7 ^ 5) * (a6 ^ 3) * a2
    + (1466714151714816000 : R) * (h ^ 64) * (a7 ^ 5) * (a6 ^ 2) * a5 * a3
    + (750705307759411200 : R) * (h ^ 64) * (a7 ^ 5) * (a6 ^ 2) * (a4 ^ 2)
    + (1734823190200320000 : R) * (h ^ 64) * (a7 ^ 5) * a6 * (a5 ^ 2) * a4
    + (157711199109120000 : R) * (h ^ 64) * (a7 ^ 5) * (a5 ^ 4)
    - (29093077670952960 : R) * (h ^ 62) * (a7 ^ 7) * a4 * b4
    - (36366347088691200 : R) * (h ^ 62) * (a7 ^ 7) * a3 * b5
    - (43639616506429440 : R) * (h ^ 62) * (a7 ^ 7) * a2 * b6
    - (50912885924167680 : R) * (h ^ 62) * (a7 ^ 7) * a1 * b7
    - (58186155341905920 : R) * (h ^ 62) * (a7 ^ 7) * a0 * b8
    - (176636543002214400 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a5 * b4
    - (335263085541457920 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a4 * b5
    - (402315702649749504 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a3 * b6
    - (469368319758041088 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a2 * b7
    - (465489242735247360 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a1 * b8
    - (230320198228377600 : R) * (h ^ 62) * (a7 ^ 6) * (a5 ^ 2) * b5
    - (609707784904114176 : R) * (h ^ 62) * (a7 ^ 6) * a5 * a4 * b6
    - (711325749054799872 : R) * (h ^ 62) * (a7 ^ 6) * a5 * a3 * b7
    - (734808018889211904 : R) * (h ^ 62) * (a7 ^ 6) * a5 * a2 * b8
    - (352996009074229248 : R) * (h ^ 62) * (a7 ^ 6) * (a4 ^ 2) * b7
    - (731483095726817280 : R) * (h ^ 62) * (a7 ^ 6) * a4 * a3 * b8
    - (53436265109913600 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 3) * b4
    - (400771988324352000 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 2) * a5 * b5
    - (523675398077153280 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 2) * a4 * b6
    - (610954631090012160 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 2) * a3 * b7
    - (645985071550955520 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 2) * a2 * b8
    - (626391774343987200 : R) * (h ^ 62) * (a7 ^ 5) * a6 * (a5 ^ 2) * b6
    - (1355737419466407936 : R) * (h ^ 62) * (a7 ^ 5) * a6 * a5 * a4 * b7
    - (1470091026801623040 : R) * (h ^ 62) * (a7 ^ 5) * a6 * a5 * a3 * b8
    - (616060763089403904 : R) * (h ^ 62) * (a7 ^ 5) * a6 * (a4 ^ 2) * b8
    - (238978852297113600 : R) * (h ^ 62) * (a7 ^ 5) * (a5 ^ 3) * b7
    - (599436147277430784 : R) * (h ^ 62) * (a7 ^ 5) * (a5 ^ 2) * a4 * b8
    + (40912140474777600 : R) * (h ^ 56) * (a7 ^ 9) * a0
    + (231835462690406400 : R) * (h ^ 56) * (a7 ^ 8) * a6 * a1
    + (195799903245434880 : R) * (h ^ 56) * (a7 ^ 8) * a5 * a2
    + (134826067167805440 : R) * (h ^ 56) * (a7 ^ 8) * a4 * a3
    + (64081771049779200 : R) * (h ^ 56) * (a7 ^ 7) * (a6 ^ 2) * a2
    - (152280212963328000 : R) * (h ^ 56) * (a7 ^ 7) * a6 * a5 * a3
    - (145522597319147520 : R) * (h ^ 56) * (a7 ^ 7) * a6 * (a4 ^ 2)
    - (222779438247444480 : R) * (h ^ 56) * (a7 ^ 7) * (a5 ^ 2) * a4
    - (201081778864128000 : R) * (h ^ 56) * (a7 ^ 6) * (a6 ^ 3) * a3
    - (712328915976192000 : R) * (h ^ 56) * (a7 ^ 6) * (a6 ^ 2) * a5 * a4
    - (259566348533760000 : R) * (h ^ 56) * (a7 ^ 6) * a6 * (a5 ^ 3)
    + (21592518583910400 : R) * (h ^ 54) * (a7 ^ 8) * a5 * b4
    + (41215193367183360 : R) * (h ^ 54) * (a7 ^ 8) * a4 * b5
    + (49458232040620032 : R) * (h ^ 54) * (a7 ^ 8) * a3 * b6
    + (57701270714056704 : R) * (h ^ 54) * (a7 ^ 8) * a2 * b7
    + (58186155341905920 : R) * (h ^ 54) * (a7 ^ 8) * a1 * b8
    + (38963943309312000 : R) * (h ^ 54) * (a7 ^ 7) * (a6 ^ 2) * b4
    + (195252649249996800 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a5 * b5
    + (260902564399153152 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a4 * b6
    + (304386325132345344 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a3 * b7
    + (323902931403276288 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a2 * b8
    + (157414330969620480 : R) * (h ^ 54) * (a7 ^ 7) * (a5 ^ 2) * b6
    + (359524634242056192 : R) * (h ^ 54) * (a7 ^ 7) * a5 * a4 * b7
    + (390055048488419328 : R) * (h ^ 54) * (a7 ^ 7) * a5 * a3 * b8
    + (179684389234409472 : R) * (h ^ 54) * (a7 ^ 7) * (a4 ^ 2) * b8
    + (55662776156160000 : R) * (h ^ 54) * (a7 ^ 6) * (a6 ^ 3) * b5
    + (261243962759577600 : R) * (h ^ 54) * (a7 ^ 6) * (a6 ^ 2) * a5 * b6
    + (296749392243720192 : R) * (h ^ 54) * (a7 ^ 6) * (a6 ^ 2) * a4 * b7
    + (325961217170472960 : R) * (h ^ 54) * (a7 ^ 6) * (a6 ^ 2) * a3 * b8
    + (322188517897666560 : R) * (h ^ 54) * (a7 ^ 6) * a6 * (a5 ^ 2) * b7
    + (626668851274186752 : R) * (h ^ 54) * (a7 ^ 6) * a6 * a5 * a4 * b8
    + (102271074057584640 : R) * (h ^ 54) * (a7 ^ 6) * (a5 ^ 3) * b8
    - (28979432836300800 : R) * (h ^ 48) * (a7 ^ 10) * a1
    - (85826709969960960 : R) * (h ^ 48) * (a7 ^ 9) * a6 * a2
    - (63662331254538240 : R) * (h ^ 48) * (a7 ^ 9) * a5 * a3
    - (21417992587837440 : R) * (h ^ 48) * (a7 ^ 9) * (a4 ^ 2)
    + (19954525431398400 : R) * (h ^ 48) * (a7 ^ 8) * (a6 ^ 2) * a3
    + (119691880169472000 : R) * (h ^ 48) * (a7 ^ 8) * a6 * a5 * a4
    + (27817375747276800 : R) * (h ^ 48) * (a7 ^ 8) * (a5 ^ 3)
    + (90683939487744000 : R) * (h ^ 48) * (a7 ^ 7) * (a6 ^ 3) * a4
    + (147032836669440000 : R) * (h ^ 48) * (a7 ^ 7) * (a6 ^ 2) * (a5 ^ 2)
    - (9375698858803200 : R) * (h ^ 46) * (a7 ^ 9) * a6 * b4
    - (23344543118131200 : R) * (h ^ 46) * (a7 ^ 9) * a5 * b5
    - (31547806099439616 : R) * (h ^ 46) * (a7 ^ 9) * a4 * b6
    - (36805773782679552 : R) * (h ^ 46) * (a7 ^ 9) * a3 * b7
    - (39518097169711104 : R) * (h ^ 46) * (a7 ^ 9) * a2 * b8
    - (39613342364467200 : R) * (h ^ 46) * (a7 ^ 8) * (a6 ^ 2) * b5
    - (125350252621332480 : R) * (h ^ 46) * (a7 ^ 8) * a6 * a5 * b6
    - (146179727315435520 : R) * (h ^ 46) * (a7 ^ 8) * a6 * a4 * b7
    - (161102917602902016 : R) * (h ^ 46) * (a7 ^ 8) * a6 * a3 * b8
    - (80544423645020160 : R) * (h ^ 46) * (a7 ^ 8) * (a5 ^ 2) * b7
    - (165936611236773888 : R) * (h ^ 46) * (a7 ^ 8) * a5 * a4 * b8
    - (33954293455257600 : R) * (h ^ 46) * (a7 ^ 7) * (a6 ^ 3) * b6
    - (128191373487636480 : R) * (h ^ 46) * (a7 ^ 7) * (a6 ^ 2) * a5 * b7
    - (132818805612085248 : R) * (h ^ 46) * (a7 ^ 7) * (a6 ^ 2) * a4 * b8
    - (134852352367656960 : R) * (h ^ 46) * (a7 ^ 7) * a6 * (a5 ^ 2) * b8
    + (12537777597972480 : R) * (h ^ 40) * (a7 ^ 11) * a2
    + (27156232305377280 : R) * (h ^ 40) * (a7 ^ 10) * a6 * a3
    + (18722162076549120 : R) * (h ^ 40) * (a7 ^ 10) * a5 * a4
    - (16779452067348480 : R) * (h ^ 40) * (a7 ^ 9) * (a6 ^ 2) * a4
    - (22785318243532800 : R) * (h ^ 40) * (a7 ^ 9) * a6 * (a5 ^ 2)
    - (34653339648000000 : R) * (h ^ 40) * (a7 ^ 8) * (a6 ^ 3) * a5
    + (745794227404800 : R) * (h ^ 38) * (a7 ^ 11) * b4
    + (9269156826316800 : R) * (h ^ 38) * (a7 ^ 10) * a6 * b5
    + (14690725719441408 : R) * (h ^ 38) * (a7 ^ 10) * a5 * b6
    + (17391447862935552 : R) * (h ^ 38) * (a7 ^ 10) * a4 * b7
    + (19259011312386048 : R) * (h ^ 38) * (a7 ^ 10) * a3 * b8
    + (23650301839933440 : R) * (h ^ 38) * (a7 ^ 9) * (a6 ^ 2) * b6
    + (60688371076300800 : R) * (h ^ 38) * (a7 ^ 9) * a6 * a5 * b7
    + (64846283818401792 : R) * (h ^ 38) * (a7 ^ 9) * a6 * a4 * b8
    + (33583401554411520 : R) * (h ^ 38) * (a7 ^ 9) * (a5 ^ 2) * b8
    + (15731692111134720 : R) * (h ^ 38) * (a7 ^ 8) * (a6 ^ 3) * b7
    + (51685206943334400 : R) * (h ^ 38) * (a7 ^ 8) * (a6 ^ 2) * a5 * b8
    - (4628862877040640 : R) * (h ^ 32) * (a7 ^ 12) * a3
    - (8131434837442560 : R) * (h ^ 32) * (a7 ^ 11) * a6 * a4
    - (3544623297331200 : R) * (h ^ 32) * (a7 ^ 11) * (a5 ^ 2)
    + (6294782921932800 : R) * (h ^ 32) * (a7 ^ 10) * (a6 ^ 2) * a5
    + (2887778304000000 : R) * (h ^ 32) * (a7 ^ 9) * (a6 ^ 4)
    - (714719467929600 : R) * (h ^ 30) * (a7 ^ 12) * b5
    - (5396176375382016 : R) * (h ^ 30) * (a7 ^ 11) * a6 * b6
    - (6984214964600832 : R) * (h ^ 30) * (a7 ^ 11) * a5 * b7
    - (7614677441839104 : R) * (h ^ 30) * (a7 ^ 11) * a4 * b8
    - (10750598420889600 : R) * (h ^ 30) * (a7 ^ 10) * (a6 ^ 2) * b7
    - (24204151294525440 : R) * (h ^ 30) * (a7 ^ 10) * a6 * a5 * b8
    - (6055066368737280 : R) * (h ^ 30) * (a7 ^ 9) * (a6 ^ 3) * b8
    + (1549044390297600 : R) * (h ^ 24) * (a7 ^ 13) * a4
    + (2785024946995200 : R) * (h ^ 24) * (a7 ^ 12) * a6 * a5
    - (573943106764800 : R) * (h ^ 24) * (a7 ^ 11) * (a6 ^ 3)
    + (404437994569728 : R) * (h ^ 22) * (a7 ^ 13) * b6
    + (2397780232372224 : R) * (h ^ 22) * (a7 ^ 12) * a6 * b7
    + (2743501729038336 : R) * (h ^ 22) * (a7 ^ 12) * a5 * b8
    + (4072569191792640 : R) * (h ^ 22) * (a7 ^ 11) * (a6 ^ 2) * b8
    - (518792777072640 : R) * (h ^ 16) * (a7 ^ 14) * a5
    - (485324498534400 : R) * (h ^ 16) * (a7 ^ 13) * (a6 ^ 2)
    - (175138639183872 : R) * (h ^ 14) * (a7 ^ 14) * b7
    - (890954047291392 : R) * (h ^ 14) * (a7 ^ 13) * a6 * b8
    + (166087772282880 : R) * (h ^ 8) * (a7 ^ 15) * a6
    + (63648228704256 : R) * (h ^ 6) * (a7 ^ 15) * b8
    - (13813654256640 : R) * (a7 ^ 17)

set_option maxHeartbeats 200000000 in
/-- Integer expansion of compact block `20` after the extra
`2^{34}` scale, on `λ = 0`. -/
def alignedSquareCompactBlock20Expansion810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    (6485183463413514240 : R) * (h ^ 112) * a5 * a2 * a0
    + (3242591731706757120 : R) * (h ^ 112) * a5 * (a1 ^ 2)
    - (576460752303423488 : R) * (h ^ 110) * a5 * a3 * b1
    - (1152921504606846976 : R) * (h ^ 110) * a5 * a2 * b2
    - (1729382256910270464 : R) * (h ^ 110) * a5 * a1 * b3
    - (2305843009213693952 : R) * (h ^ 110) * a5 * a0 * b4
    - (4863887597560135680 : R) * (h ^ 104) * a7 * a6 * a2 * a0
    - (2431943798780067840 : R) * (h ^ 104) * a7 * a6 * (a1 ^ 2)
    - (2431943798780067840 : R) * (h ^ 104) * a7 * a5 * a3 * a0
    - (2431943798780067840 : R) * (h ^ 104) * a7 * a5 * a2 * a1
    - (2296835809958952960 : R) * (h ^ 104) * (a4 ^ 3) * a3
    + (432345564227567616 : R) * (h ^ 102) * a7 * a6 * a3 * b1
    + (864691128455135232 : R) * (h ^ 102) * a7 * a6 * a2 * b2
    + (1297036692682702848 : R) * (h ^ 102) * a7 * a6 * a1 * b3
    + (1729382256910270464 : R) * (h ^ 102) * a7 * a6 * a0 * b4
    + (288230376151711744 : R) * (h ^ 102) * a7 * a5 * a4 * b1
    + (576460752303423488 : R) * (h ^ 102) * a7 * a5 * a3 * b2
    + (864691128455135232 : R) * (h ^ 102) * a7 * a5 * a2 * b3
    + (1152921504606846976 : R) * (h ^ 102) * a7 * a5 * a1 * b4
    + (1441151880758558720 : R) * (h ^ 102) * a7 * a5 * a0 * b5
    + (5188146770730811392 : R) * (h ^ 102) * a5 * a3 * a1 * b8
    + (2594073385365405696 : R) * (h ^ 102) * a5 * (a2 ^ 2) * b8
    + (1418633882621706240 : R) * (h ^ 96) * (a7 ^ 3) * a2 * a0
    + (709316941310853120 : R) * (h ^ 96) * (a7 ^ 3) * (a1 ^ 2)
    + (1823957849085050880 : R) * (h ^ 96) * (a7 ^ 2) * a6 * a3 * a0
    + (1823957849085050880 : R) * (h ^ 96) * (a7 ^ 2) * a6 * a2 * a1
    + (607985949695016960 : R) * (h ^ 96) * (a7 ^ 2) * a5 * a4 * a0
    - (3039929748475084800 : R) * (h ^ 96) * (a7 ^ 2) * a5 * a3 * a1
    - (1519964874237542400 : R) * (h ^ 96) * (a7 ^ 2) * a5 * (a2 ^ 2)
    + (4306567143673036800 : R) * (h ^ 96) * a7 * a5 * (a4 ^ 2) * a3
    + (1148417904979476480 : R) * (h ^ 96) * a7 * (a4 ^ 4)
    - (126100789566373888 : R) * (h ^ 94) * (a7 ^ 3) * a3 * b1
    - (252201579132747776 : R) * (h ^ 94) * (a7 ^ 3) * a2 * b2
    - (378302368699121664 : R) * (h ^ 94) * (a7 ^ 3) * a1 * b3
    - (504403158265495552 : R) * (h ^ 94) * (a7 ^ 3) * a0 * b4
    - (216172782113783808 : R) * (h ^ 94) * (a7 ^ 2) * a6 * a4 * b1
    - (432345564227567616 : R) * (h ^ 94) * (a7 ^ 2) * a6 * a3 * b2
    - (648518346341351424 : R) * (h ^ 94) * (a7 ^ 2) * a6 * a2 * b3
    - (864691128455135232 : R) * (h ^ 94) * (a7 ^ 2) * a6 * a1 * b4
    - (1080863910568919040 : R) * (h ^ 94) * (a7 ^ 2) * a6 * a0 * b5
    - (90071992547409920 : R) * (h ^ 94) * (a7 ^ 2) * (a5 ^ 2) * b1
    - (180143985094819840 : R) * (h ^ 94) * (a7 ^ 2) * a5 * a4 * b2
    - (270215977642229760 : R) * (h ^ 94) * (a7 ^ 2) * a5 * a3 * b3
    - (360287970189639680 : R) * (h ^ 94) * (a7 ^ 2) * a5 * a2 * b4
    - (450359962737049600 : R) * (h ^ 94) * (a7 ^ 2) * a5 * a1 * b5
    - (540431955284459520 : R) * (h ^ 94) * (a7 ^ 2) * a5 * a0 * b6
    - (3891110078048108544 : R) * (h ^ 94) * a7 * a6 * a3 * a1 * b8
    - (1945555039024054272 : R) * (h ^ 94) * a7 * a6 * (a2 ^ 2) * b8
    - (2594073385365405696 : R) * (h ^ 94) * a7 * a5 * a4 * a1 * b8
    - (3242591731706757120 : R) * (h ^ 94) * a7 * a5 * a3 * a2 * b8
    - (531987705983139840 : R) * (h ^ 88) * (a7 ^ 4) * a3 * a0
    - (531987705983139840 : R) * (h ^ 88) * (a7 ^ 4) * a2 * a1
    - (455989462271262720 : R) * (h ^ 88) * (a7 ^ 3) * a6 * a4 * a0
    + (2279947311356313600 : R) * (h ^ 88) * (a7 ^ 3) * a6 * a3 * a1
    + (1139973655678156800 : R) * (h ^ 88) * (a7 ^ 3) * a6 * (a2 ^ 2)
    - (126663739519795200 : R) * (h ^ 88) * (a7 ^ 3) * (a5 ^ 2) * a0
    + (1697294109565255680 : R) * (h ^ 88) * (a7 ^ 3) * a5 * a4 * a1
    + (2153283571836518400 : R) * (h ^ 88) * (a7 ^ 3) * a5 * a3 * a2
    - (1614962678877388800 : R) * (h ^ 88) * (a7 ^ 2) * a6 * (a4 ^ 2) * a3
    - (2691604464795648000 : R) * (h ^ 88) * (a7 ^ 2) * (a5 ^ 2) * a4 * a3
    - (2512164167142604800 : R) * (h ^ 88) * (a7 ^ 2) * a5 * (a4 ^ 3)
    + (63050394783186944 : R) * (h ^ 86) * (a7 ^ 4) * a4 * b1
    + (126100789566373888 : R) * (h ^ 86) * (a7 ^ 4) * a3 * b2
    + (189151184349560832 : R) * (h ^ 86) * (a7 ^ 4) * a2 * b3
    + (252201579132747776 : R) * (h ^ 86) * (a7 ^ 4) * a1 * b4
    + (315251973915934720 : R) * (h ^ 86) * (a7 ^ 4) * a0 * b5
    + (90071992547409920 : R) * (h ^ 86) * (a7 ^ 3) * a6 * a5 * b1
    + (135107988821114880 : R) * (h ^ 86) * (a7 ^ 3) * a6 * a4 * b2
    + (202661983231672320 : R) * (h ^ 86) * (a7 ^ 3) * a6 * a3 * b3
    + (270215977642229760 : R) * (h ^ 86) * (a7 ^ 3) * a6 * a2 * b4
    + (337769972052787200 : R) * (h ^ 86) * (a7 ^ 3) * a6 * a1 * b5
    + (405323966463344640 : R) * (h ^ 86) * (a7 ^ 3) * a6 * a0 * b6
    + (45035996273704960 : R) * (h ^ 86) * (a7 ^ 3) * (a5 ^ 2) * b2
    + (67553994410557440 : R) * (h ^ 86) * (a7 ^ 3) * a5 * a4 * b3
    + (90071992547409920 : R) * (h ^ 86) * (a7 ^ 3) * a5 * a3 * b4
    + (112589990684262400 : R) * (h ^ 86) * (a7 ^ 3) * a5 * a2 * b5
    + (135107988821114880 : R) * (h ^ 86) * (a7 ^ 3) * a5 * a1 * b6
    + (157625986957967360 : R) * (h ^ 86) * (a7 ^ 3) * a5 * a0 * b7
    + (1134907106097364992 : R) * (h ^ 86) * (a7 ^ 3) * a3 * a1 * b8
    + (567453553048682496 : R) * (h ^ 86) * (a7 ^ 3) * (a2 ^ 2) * b8
    + (1945555039024054272 : R) * (h ^ 86) * (a7 ^ 2) * a6 * a4 * a1 * b8
    + (2431943798780067840 : R) * (h ^ 86) * (a7 ^ 2) * a6 * a3 * a2 * b8
    + (810647932926689280 : R) * (h ^ 86) * (a7 ^ 2) * (a5 ^ 2) * a1 * b8
    + (1134907106097364992 : R) * (h ^ 86) * (a7 ^ 2) * a5 * a4 * a2 * b8
    + (607985949695016960 : R) * (h ^ 86) * (a7 ^ 2) * a5 * (a3 ^ 2) * b8
    + (132996926495784960 : R) * (h ^ 80) * (a7 ^ 5) * a4 * a0
    - (664984632478924800 : R) * (h ^ 80) * (a7 ^ 5) * a3 * a1
    - (332492316239462400 : R) * (h ^ 80) * (a7 ^ 5) * (a2 ^ 2)
    + (118747255799808000 : R) * (h ^ 80) * (a7 ^ 4) * a6 * a5 * a0
    - (1272970582173941760 : R) * (h ^ 80) * (a7 ^ 4) * a6 * a4 * a1
    - (1614962678877388800 : R) * (h ^ 80) * (a7 ^ 4) * a6 * a3 * a2
    - (546237376679116800 : R) * (h ^ 80) * (a7 ^ 4) * (a5 ^ 2) * a1
    - (774232107814748160 : R) * (h ^ 80) * (a7 ^ 4) * a5 * a4 * a2
    - (415615395299328000 : R) * (h ^ 80) * (a7 ^ 4) * a5 * (a3 ^ 2)
    + (353273086004428800 : R) * (h ^ 80) * (a7 ^ 4) * (a4 ^ 2) * a3
    + (2018703348596736000 : R) * (h ^ 80) * (a7 ^ 3) * a6 * a5 * a4 * a3
    + (897201488265216000 : R) * (h ^ 80) * (a7 ^ 3) * a6 * (a4 ^ 3)
    + (560750930165760000 : R) * (h ^ 80) * (a7 ^ 3) * (a5 ^ 3) * a3
    + (2018703348596736000 : R) * (h ^ 80) * (a7 ^ 3) * (a5 ^ 2) * (a4 ^ 2)
    - (23643898043695104 : R) * (h ^ 78) * (a7 ^ 5) * a5 * b1
    - (39406496739491840 : R) * (h ^ 78) * (a7 ^ 5) * a4 * b2
    - (59109745109237760 : R) * (h ^ 78) * (a7 ^ 5) * a3 * b3
    - (78812993478983680 : R) * (h ^ 78) * (a7 ^ 5) * a2 * b4
    - (98516241848729600 : R) * (h ^ 78) * (a7 ^ 5) * a1 * b5
    - (118219490218475520 : R) * (h ^ 78) * (a7 ^ 5) * a0 * b6
    - (16888498602639360 : R) * (h ^ 78) * (a7 ^ 4) * (a6 ^ 2) * b1
    - (43628621390151680 : R) * (h ^ 78) * (a7 ^ 4) * a6 * a5 * b2
    - (50665495807918080 : R) * (h ^ 78) * (a7 ^ 4) * a6 * a4 * b3
    - (67553994410557440 : R) * (h ^ 78) * (a7 ^ 4) * a6 * a3 * b4
    - (84442493013196800 : R) * (h ^ 78) * (a7 ^ 4) * a6 * a2 * b5
    - (101330991615836160 : R) * (h ^ 78) * (a7 ^ 4) * a6 * a1 * b6
    - (118219490218475520 : R) * (h ^ 78) * (a7 ^ 4) * a6 * a0 * b7
    - (14777436277309440 : R) * (h ^ 78) * (a7 ^ 4) * (a5 ^ 2) * b3
    - (19703248369745920 : R) * (h ^ 78) * (a7 ^ 4) * a5 * a4 * b4
    - (24629060462182400 : R) * (h ^ 78) * (a7 ^ 4) * a5 * a3 * b5
    - (29554872554618880 : R) * (h ^ 78) * (a7 ^ 4) * a5 * a2 * b6
    - (34480684647055360 : R) * (h ^ 78) * (a7 ^ 4) * a5 * a1 * b7
    - (39406496739491840 : R) * (h ^ 78) * (a7 ^ 4) * a5 * a0 * b8
    - (567453553048682496 : R) * (h ^ 78) * (a7 ^ 4) * a4 * a1 * b8
    - (709316941310853120 : R) * (h ^ 78) * (a7 ^ 4) * a3 * a2 * b8
    - (810647932926689280 : R) * (h ^ 78) * (a7 ^ 3) * a6 * a5 * a1 * b8
    - (851180329573023744 : R) * (h ^ 78) * (a7 ^ 3) * a6 * a4 * a2 * b8
    - (455989462271262720 : R) * (h ^ 78) * (a7 ^ 3) * a6 * (a3 ^ 2) * b8
    - (303992974847508480 : R) * (h ^ 78) * (a7 ^ 3) * (a5 ^ 2) * a2 * b8
    - (344525371493842944 : R) * (h ^ 78) * (a7 ^ 3) * a5 * a4 * a3 * b8
    - (21935256974131200 : R) * (h ^ 72) * (a7 ^ 6) * a5 * a0
    + (371283086467399680 : R) * (h ^ 72) * (a7 ^ 6) * a4 * a1
    + (471030781339238400 : R) * (h ^ 72) * (a7 ^ 6) * a3 * a2
    - (17812088369971200 : R) * (h ^ 72) * (a7 ^ 5) * (a6 ^ 2) * a0
    + (548018585516113920 : R) * (h ^ 72) * (a7 ^ 5) * a6 * a5 * a1
    + (580674080861061120 : R) * (h ^ 72) * (a7 ^ 5) * a6 * a4 * a2
    + (311711546474496000 : R) * (h ^ 72) * (a7 ^ 5) * a6 * (a3 ^ 2)
    + (209588906486661120 : R) * (h ^ 72) * (a7 ^ 5) * (a5 ^ 2) * a2
    - (203503109626920960 : R) * (h ^ 72) * (a7 ^ 5) * a5 * a4 * a3
    - (192337569046855680 : R) * (h ^ 72) * (a7 ^ 5) * (a4 ^ 3)
    - (378506877861888000 : R) * (h ^ 72) * (a7 ^ 4) * (a6 ^ 2) * a4 * a3
    - (630844796436480000 : R) * (h ^ 72) * (a7 ^ 4) * a6 * (a5 ^ 2) * a3
    - (1429914871922688000 : R) * (h ^ 72) * (a7 ^ 4) * a6 * a5 * (a4 ^ 2)
    - (700938662707200000 : R) * (h ^ 72) * (a7 ^ 4) * (a5 ^ 3) * a4
    + (7881299347898368 : R) * (h ^ 70) * (a7 ^ 6) * a6 * b1
    + (11452513114914816 : R) * (h ^ 70) * (a7 ^ 6) * a5 * b2
    + (14777436277309440 : R) * (h ^ 70) * (a7 ^ 6) * a4 * b3
    + (19703248369745920 : R) * (h ^ 70) * (a7 ^ 6) * a3 * b4
    + (24629060462182400 : R) * (h ^ 70) * (a7 ^ 6) * a2 * b5
    + (29554872554618880 : R) * (h ^ 70) * (a7 ^ 6) * a1 * b6
    + (34480684647055360 : R) * (h ^ 70) * (a7 ^ 6) * a0 * b7
    + (7388718138654720 : R) * (h ^ 70) * (a7 ^ 5) * (a6 ^ 2) * b2
    + (14038564463443968 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a5 * b3
    + (14777436277309440 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a4 * b4
    + (18471795346636800 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a3 * b5
    + (22166154415964160 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a2 * b6
    + (25860513485291520 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a1 * b7
    + (29554872554618880 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a0 * b8
    + (3940649673949184 : R) * (h ^ 70) * (a7 ^ 5) * (a5 ^ 2) * b4
    + (4925812092436480 : R) * (h ^ 70) * (a7 ^ 5) * a5 * a4 * b5
    + (5910974510923776 : R) * (h ^ 70) * (a7 ^ 5) * a5 * a3 * b6
    + (6896136929411072 : R) * (h ^ 70) * (a7 ^ 5) * a5 * a2 * b7
    + (220676381741154304 : R) * (h ^ 70) * (a7 ^ 5) * a5 * a1 * b8
    + (248260929458798592 : R) * (h ^ 70) * (a7 ^ 5) * a4 * a2 * b8
    + (132996926495784960 : R) * (h ^ 70) * (a7 ^ 5) * (a3 ^ 2) * b8
    + (151996487423754240 : R) * (h ^ 70) * (a7 ^ 4) * (a6 ^ 2) * a1 * b8
    + (297659787871518720 : R) * (h ^ 70) * (a7 ^ 4) * a6 * a5 * a2 * b8
    + (258394028620382208 : R) * (h ^ 70) * (a7 ^ 4) * a6 * a4 * a3 * b8
    + (82331430687866880 : R) * (h ^ 70) * (a7 ^ 4) * (a5 ^ 2) * a3 * b8
    + (43065671436730368 : R) * (h ^ 70) * (a7 ^ 4) * a5 * (a4 ^ 2) * b8
    + (865865406873600 : R) * (h ^ 64) * (a7 ^ 7) * a6 * a0
    - (145593206581493760 : R) * (h ^ 64) * (a7 ^ 7) * a5 * a1
    - (169363273584476160 : R) * (h ^ 64) * (a7 ^ 7) * a4 * a2
    - (90915867721728000 : R) * (h ^ 64) * (a7 ^ 7) * (a3 ^ 2)
    - (103755414755082240 : R) * (h ^ 64) * (a7 ^ 6) * (a6 ^ 2) * a1
    - (205482230556917760 : R) * (h ^ 64) * (a7 ^ 6) * a6 * a5 * a2
    - (12969426844385280 : R) * (h ^ 64) * (a7 ^ 6) * a6 * a4 * a3
    + (80800704343572480 : R) * (h ^ 64) * (a7 ^ 6) * (a5 ^ 2) * a3
    + (275499818208460800 : R) * (h ^ 64) * (a7 ^ 6) * a5 * (a4 ^ 2)
    + (236566798663680000 : R) * (h ^ 64) * (a7 ^ 5) * (a6 ^ 2) * a5 * a3
    + (252337918574592000 : R) * (h ^ 64) * (a7 ^ 5) * (a6 ^ 2) * (a4 ^ 2)
    + (735985595842560000 : R) * (h ^ 64) * (a7 ^ 5) * a6 * (a5 ^ 2) * a4
    + (87617332838400000 : R) * (h ^ 64) * (a7 ^ 5) * (a5 ^ 4)
    - (862017116176384 : R) * (h ^ 62) * (a7 ^ 8) * b1
    - (3355709487972352 : R) * (h ^ 62) * (a7 ^ 7) * a6 * b2
    - (3687761999560704 : R) * (h ^ 62) * (a7 ^ 7) * a5 * b3
    - (4310085580881920 : R) * (h ^ 62) * (a7 ^ 7) * a4 * b4
    - (5387606976102400 : R) * (h ^ 62) * (a7 ^ 7) * a3 * b5
    - (6465128371322880 : R) * (h ^ 62) * (a7 ^ 7) * a2 * b6
    - (7542649766543360 : R) * (h ^ 62) * (a7 ^ 7) * a1 * b7
    - (8620171161763840 : R) * (h ^ 62) * (a7 ^ 7) * a0 * b8
    - (2216615441596416 : R) * (h ^ 62) * (a7 ^ 6) * (a6 ^ 2) * b3
    - (3694359069327360 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a5 * b4
    - (3694359069327360 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a4 * b5
    - (4433230883192832 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a3 * b6
    - (5172102697058304 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a2 * b7
    - (76842668642009088 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a1 * b8
    - (923589767331840 : R) * (h ^ 62) * (a7 ^ 6) * (a5 ^ 2) * b5
    - (1108307720798208 : R) * (h ^ 62) * (a7 ^ 6) * a5 * a4 * b6
    - (1293025674264576 : R) * (h ^ 62) * (a7 ^ 6) * a5 * a3 * b7
    - (79613437944004608 : R) * (h ^ 62) * (a7 ^ 6) * a5 * a2 * b8
    - (75364925014278144 : R) * (h ^ 62) * (a7 ^ 6) * a4 * a3 * b8
    - (52248792551915520 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 2) * a2 * b8
    - (79323166874271744 : R) * (h ^ 62) * (a7 ^ 5) * a6 * a5 * a3 * b8
    - (32299253577547776 : R) * (h ^ 62) * (a7 ^ 5) * a6 * (a4 ^ 2) * b8
    - (18999560927969280 : R) * (h ^ 62) * (a7 ^ 5) * (a5 ^ 2) * a4 * b8
    + (1262720385024000 : R) * (h ^ 56) * (a7 ^ 9) * a0
    + (49839831294935040 : R) * (h ^ 56) * (a7 ^ 8) * a6 * a1
    + (54250462060216320 : R) * (h ^ 56) * (a7 ^ 8) * a5 * a2
    + (33969658700759040 : R) * (h ^ 56) * (a7 ^ 8) * a4 * a3
    + (36217913018941440 : R) * (h ^ 56) * (a7 ^ 7) * (a6 ^ 2) * a2
    - (48354717503324160 : R) * (h ^ 56) * (a7 ^ 7) * a6 * a5 * a3
    - (85187240342323200 : R) * (h ^ 56) * (a7 ^ 7) * a6 * (a4 ^ 2)
    - (143149198391377920 : R) * (h ^ 56) * (a7 ^ 7) * (a5 ^ 2) * a4
    - (29570849832960000 : R) * (h ^ 56) * (a7 ^ 6) * (a6 ^ 3) * a3
    - (256280698552320000 : R) * (h ^ 56) * (a7 ^ 6) * (a6 ^ 2) * a5 * a4
    - (120473832652800000 : R) * (h ^ 56) * (a7 ^ 6) * a6 * (a5 ^ 3)
    + (350194453446656 : R) * (h ^ 54) * (a7 ^ 9) * b2
    + (987911197556736 : R) * (h ^ 54) * (a7 ^ 8) * a6 * b3
    + (971281084186624 : R) * (h ^ 54) * (a7 ^ 8) * a5 * b4
    + (1077521395220480 : R) * (h ^ 54) * (a7 ^ 8) * a4 * b5
    + (1293025674264576 : R) * (h ^ 54) * (a7 ^ 8) * a3 * b6
    + (1508529953308672 : R) * (h ^ 54) * (a7 ^ 8) * a2 * b7
    + (9482188277940224 : R) * (h ^ 54) * (a7 ^ 8) * a1 * b8
    + (554153860399104 : R) * (h ^ 54) * (a7 ^ 7) * (a6 ^ 2) * b4
    + (857619069665280 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a5 * b5
    + (831230790598656 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a4 * b6
    + (969769255698432 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a3 * b7
    + (25075462183059456 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a2 * b8
    + (197912092999680 : R) * (h ^ 54) * (a7 ^ 7) * (a5 ^ 2) * b6
    + (230897441832960 : R) * (h ^ 54) * (a7 ^ 7) * a5 * a4 * b7
    + (21094130578882560 : R) * (h ^ 54) * (a7 ^ 7) * a5 * a3 * b8
    + (9420615626784768 : R) * (h ^ 54) * (a7 ^ 7) * (a4 ^ 2) * b8
    + (13180945393778688 : R) * (h ^ 54) * (a7 ^ 6) * (a6 ^ 2) * a3 * b8
    + (18089165300170752 : R) * (h ^ 54) * (a7 ^ 6) * a6 * a5 * a4 * b8
    + (1979120929996800 : R) * (h ^ 54) * (a7 ^ 6) * (a5 ^ 3) * b8
    - (5710201969704960 : R) * (h ^ 48) * (a7 ^ 10) * a1
    - (16865724538552320 : R) * (h ^ 48) * (a7 ^ 9) * a6 * a2
    - (3214244807966720 : R) * (h ^ 48) * (a7 ^ 9) * a5 * a3
    + (4922918358220800 : R) * (h ^ 48) * (a7 ^ 9) * (a4 ^ 2)
    + (10221512137113600 : R) * (h ^ 48) * (a7 ^ 8) * (a6 ^ 2) * a3
    + (96054817566228480 : R) * (h ^ 48) * (a7 ^ 8) * a6 * a5 * a4
    + (24012464219750400 : R) * (h ^ 48) * (a7 ^ 8) * (a5 ^ 3)
    + (29570849832960000 : R) * (h ^ 48) * (a7 ^ 7) * (a6 ^ 3) * a4
    + (61605937152000000 : R) * (h ^ 48) * (a7 ^ 7) * (a6 ^ 2) * (a5 ^ 2)
    - (99574521790464 : R) * (h ^ 46) * (a7 ^ 10) * b3
    - (243576185290752 : R) * (h ^ 46) * (a7 ^ 9) * a6 * b4
    - (225657581731840 : R) * (h ^ 46) * (a7 ^ 9) * a5 * b5
    - (242442313924608 : R) * (h ^ 46) * (a7 ^ 9) * a4 * b6
    - (282849366245376 : R) * (h ^ 46) * (a7 ^ 9) * a3 * b7
    - (2868900714774528 : R) * (h ^ 46) * (a7 ^ 9) * a2 * b8
    - (123695058124800 : R) * (h ^ 46) * (a7 ^ 8) * (a6 ^ 2) * b5
    - (182450210734080 : R) * (h ^ 46) * (a7 ^ 8) * a6 * a5 * b6
    - (173173081374720 : R) * (h ^ 46) * (a7 ^ 8) * a6 * a4 * b7
    - (6157539993452544 : R) * (h ^ 46) * (a7 ^ 8) * a6 * a3 * b8
    - (39685497815040 : R) * (h ^ 46) * (a7 ^ 8) * (a5 ^ 2) * b7
    - (4797718987800576 : R) * (h ^ 46) * (a7 ^ 8) * a5 * a4 * b8
    - (2879620953145344 : R) * (h ^ 46) * (a7 ^ 7) * (a6 ^ 2) * a4 * b8
    - (2251250057871360 : R) * (h ^ 46) * (a7 ^ 7) * a6 * (a5 ^ 2) * b8
    + (1838131917619200 : R) * (h ^ 40) * (a7 ^ 11) * a2
    - (49327531622400 : R) * (h ^ 40) * (a7 ^ 10) * a6 * a3
    - (8184769858764800 : R) * (h ^ 40) * (a7 ^ 10) * a5 * a4
    - (16747320343265280 : R) * (h ^ 40) * (a7 ^ 9) * (a6 ^ 2) * a4
    - (24300763899494400 : R) * (h ^ 40) * (a7 ^ 9) * a6 * (a5 ^ 2)
    - (13861335859200000 : R) * (h ^ 40) * (a7 ^ 8) * (a6 ^ 3) * a5
    + (23901493002240 : R) * (h ^ 38) * (a7 ^ 11) * b4
    + (53794465382400 : R) * (h ^ 38) * (a7 ^ 10) * a6 * b5
    + (48041356689408 : R) * (h ^ 38) * (a7 ^ 10) * a5 * b6
    + (50508815400960 : R) * (h ^ 38) * (a7 ^ 10) * a4 * b7
    + (674653462855680 : R) * (h ^ 38) * (a7 ^ 10) * a3 * b8
    + (25512105738240 : R) * (h ^ 38) * (a7 ^ 9) * (a6 ^ 2) * b6
    + (36378372997120 : R) * (h ^ 38) * (a7 ^ 9) * a6 * a5 * b7
    + (1321063220772864 : R) * (h ^ 38) * (a7 ^ 9) * a6 * a4 * b8
    + (556455962869760 : R) * (h ^ 38) * (a7 ^ 9) * (a5 ^ 2) * b8
    + (647079772815360 : R) * (h ^ 38) * (a7 ^ 8) * (a6 ^ 2) * a5 * b8
    - (132905775923200 : R) * (h ^ 32) * (a7 ^ 12) * a3
    + (3055755146035200 : R) * (h ^ 32) * (a7 ^ 11) * a6 * a4
    + (2326921216000000 : R) * (h ^ 32) * (a7 ^ 11) * (a5 ^ 2)
    + (8239427176366080 : R) * (h ^ 32) * (a7 ^ 10) * (a6 ^ 2) * a5
    + (1155111321600000 : R) * (h ^ 32) * (a7 ^ 9) * (a6 ^ 4)
    - (5167382528000 : R) * (h ^ 30) * (a7 ^ 12) * b5
    - (11002095599616 : R) * (h ^ 30) * (a7 ^ 11) * a6 * b6
    - (9585024827392 : R) * (h ^ 30) * (a7 ^ 11) * a5 * b7
    - (140342351364096 : R) * (h ^ 30) * (a7 ^ 11) * a4 * b8
    - (4960687226880 : R) * (h ^ 30) * (a7 ^ 10) * (a6 ^ 2) * b7
    - (282911643271168 : R) * (h ^ 30) * (a7 ^ 10) * a6 * a5 * b8
    - (53923314401280 : R) * (h ^ 30) * (a7 ^ 9) * (a6 ^ 3) * b8
    - (185382802554880 : R) * (h ^ 24) * (a7 ^ 13) * a4
    - (1618448487546880 : R) * (h ^ 24) * (a7 ^ 12) * a6 * a5
    - (922420940636160 : R) * (h ^ 24) * (a7 ^ 11) * (a6 ^ 3)
    + (1038643888128 : R) * (h ^ 22) * (a7 ^ 13) * b6
    + (2124733743104 : R) * (h ^ 22) * (a7 ^ 12) * a6 * b7
    + (28737223524352 : R) * (h ^ 22) * (a7 ^ 12) * a5 * b8
    + (32608465453056 : R) * (h ^ 22) * (a7 ^ 11) * (a6 ^ 2) * b8
    + (106542496972800 : R) * (h ^ 16) * (a7 ^ 14) * a5
    + (276102744637440 : R) * (h ^ 16) * (a7 ^ 13) * (a6 ^ 2)
    - (197711101952 : R) * (h ^ 14) * (a7 ^ 14) * b7
    - (6210958917632 : R) * (h ^ 14) * (a7 ^ 13) * a6 * b8
    - (36956834324480 : R) * (h ^ 8) * (a7 ^ 15) * a6
    + (375486676992 : R) * (h ^ 6) * (a7 ^ 15) * b8
    + (1871129523200 : R) * (a7 ^ 17)

set_option maxHeartbeats 200000000 in
/-- Integer expansion of compact block `21` after the extra
`2^{34}` scale, on `λ = 0`. -/
def alignedSquareCompactBlock21Expansion810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    (6485183463413514240 : R) * (h ^ 112) * a4 * a3 * a0
    - (288230376151711744 : R) * (h ^ 110) * (a4 ^ 2) * b1
    - (1152921504606846976 : R) * (h ^ 110) * a4 * a3 * b2
    - (4053239664633446400 : R) * (h ^ 104) * a7 * a5 * a3 * a0
    - (3242591731706757120 : R) * (h ^ 104) * a7 * (a4 ^ 2) * a0
    - (810647932926689280 : R) * (h ^ 104) * a7 * a4 * a3 * a1
    + (360287970189639680 : R) * (h ^ 102) * a7 * a5 * a4 * b1
    + (720575940379279360 : R) * (h ^ 102) * a7 * a5 * a3 * b2
    + (648518346341351424 : R) * (h ^ 102) * a7 * (a4 ^ 2) * b2
    + (432345564227567616 : R) * (h ^ 102) * a7 * a4 * a3 * b3
    + (540431955284459520 : R) * (h ^ 102) * (a4 ^ 3) * b5
    + (1945555039024054272 : R) * (h ^ 102) * (a4 ^ 2) * a3 * b6
    + (2269814212194729984 : R) * (h ^ 102) * (a4 ^ 2) * a2 * b7
    + (2594073385365405696 : R) * (h ^ 102) * (a4 ^ 2) * a1 * b8
    + (2269814212194729984 : R) * (h ^ 102) * a4 * (a3 ^ 2) * b7
    + (5188146770730811392 : R) * (h ^ 102) * a4 * a3 * a2 * b8
    + (1519964874237542400 : R) * (h ^ 96) * (a7 ^ 2) * a6 * a3 * a0
    + (3039929748475084800 : R) * (h ^ 96) * (a7 ^ 2) * a5 * a4 * a0
    + (506654958079180800 : R) * (h ^ 96) * (a7 ^ 2) * a5 * a3 * a1
    - (1418633882621706240 : R) * (h ^ 96) * (a7 ^ 2) * (a4 ^ 2) * a1
    - (3546584706554265600 : R) * (h ^ 96) * (a7 ^ 2) * a4 * a3 * a2
    - (135107988821114880 : R) * (h ^ 94) * (a7 ^ 2) * a6 * a4 * b1
    - (270215977642229760 : R) * (h ^ 94) * (a7 ^ 2) * a6 * a3 * b2
    - (112589990684262400 : R) * (h ^ 94) * (a7 ^ 2) * (a5 ^ 2) * b1
    - (630503947831869440 : R) * (h ^ 94) * (a7 ^ 2) * a5 * a4 * b2
    - (270215977642229760 : R) * (h ^ 94) * (a7 ^ 2) * a5 * a3 * b3
    - (229683580995895296 : R) * (h ^ 94) * (a7 ^ 2) * (a4 ^ 2) * b3
    - (108086391056891904 : R) * (h ^ 94) * (a7 ^ 2) * a4 * a3 * b4
    - (1013309916158361600 : R) * (h ^ 94) * a7 * a5 * (a4 ^ 2) * b5
    - (2431943798780067840 : R) * (h ^ 94) * a7 * a5 * a4 * a3 * b6
    - (2837267765243412480 : R) * (h ^ 94) * a7 * a5 * a4 * a2 * b7
    - (3242591731706757120 : R) * (h ^ 94) * a7 * a5 * a4 * a1 * b8
    - (1418633882621706240 : R) * (h ^ 94) * a7 * a5 * (a3 ^ 2) * b7
    - (3242591731706757120 : R) * (h ^ 94) * a7 * a5 * a3 * a2 * b8
    - (1378101485975371776 : R) * (h ^ 94) * a7 * (a4 ^ 3) * b6
    - (4823355200913801216 : R) * (h ^ 94) * a7 * (a4 ^ 2) * a3 * b7
    - (5512405943901487104 : R) * (h ^ 94) * a7 * (a4 ^ 2) * a2 * b8
    - (4215369251218784256 : R) * (h ^ 94) * a7 * a4 * (a3 ^ 2) * b8
    - (332492316239462400 : R) * (h ^ 88) * (a7 ^ 4) * a3 * a0
    - (1013309916158361600 : R) * (h ^ 88) * (a7 ^ 3) * a6 * a4 * a0
    - (189995609279692800 : R) * (h ^ 88) * (a7 ^ 3) * a6 * a3 * a1
    - (633318697598976000 : R) * (h ^ 88) * (a7 ^ 3) * (a5 ^ 2) * a0
    + (1899956092796928000 : R) * (h ^ 88) * (a7 ^ 3) * a5 * a4 * a1
    + (2216615441596416000 : R) * (h ^ 88) * (a7 ^ 3) * a5 * a3 * a2
    + (3293257227514675200 : R) * (h ^ 88) * (a7 ^ 3) * (a4 ^ 2) * a2
    + (2419277424828088320 : R) * (h ^ 88) * (a7 ^ 3) * a4 * (a3 ^ 2)
    + (29554872554618880 : R) * (h ^ 86) * (a7 ^ 4) * a4 * b1
    + (59109745109237760 : R) * (h ^ 86) * (a7 ^ 4) * a3 * b2
    + (84442493013196800 : R) * (h ^ 86) * (a7 ^ 3) * a6 * a5 * b1
    + (213920982300098560 : R) * (h ^ 86) * (a7 ^ 3) * a6 * a4 * b2
    + (101330991615836160 : R) * (h ^ 86) * (a7 ^ 3) * a6 * a3 * b3
    + (140737488355328000 : R) * (h ^ 86) * (a7 ^ 3) * (a5 ^ 2) * b2
    + (219550481834311680 : R) * (h ^ 86) * (a7 ^ 3) * a5 * a4 * b3
    + (67553994410557440 : R) * (h ^ 86) * (a7 ^ 3) * a5 * a3 * b4
    + (56294995342131200 : R) * (h ^ 86) * (a7 ^ 3) * (a4 ^ 2) * b4
    + (22517998136852480 : R) * (h ^ 86) * (a7 ^ 3) * a4 * a3 * b5
    + (379991218559385600 : R) * (h ^ 86) * (a7 ^ 2) * a6 * (a4 ^ 2) * b5
    + (911978924542525440 : R) * (h ^ 86) * (a7 ^ 2) * a6 * a4 * a3 * b6
    + (1063975411966279680 : R) * (h ^ 86) * (a7 ^ 2) * a6 * a4 * a2 * b7
    + (1215971899390033920 : R) * (h ^ 86) * (a7 ^ 2) * a6 * a4 * a1 * b8
    + (531987705983139840 : R) * (h ^ 86) * (a7 ^ 2) * a6 * (a3 ^ 2) * b7
    + (1215971899390033920 : R) * (h ^ 86) * (a7 ^ 2) * a6 * a3 * a2 * b8
    + (633318697598976000 : R) * (h ^ 86) * (a7 ^ 2) * (a5 ^ 2) * a4 * b5
    + (759982437118771200 : R) * (h ^ 86) * (a7 ^ 2) * (a5 ^ 2) * a3 * b6
    + (886646176638566400 : R) * (h ^ 86) * (a7 ^ 2) * (a5 ^ 2) * a2 * b7
    + (1013309916158361600 : R) * (h ^ 86) * (a7 ^ 2) * (a5 ^ 2) * a1 * b8
    + (2279947311356313600 : R) * (h ^ 86) * (a7 ^ 2) * a5 * (a4 ^ 2) * b6
    + (5319877059831398400 : R) * (h ^ 86) * (a7 ^ 2) * a5 * a4 * a3 * b7
    + (6079859496950169600 : R) * (h ^ 86) * (a7 ^ 2) * a5 * a4 * a2 * b8
    + (2634605782011740160 : R) * (h ^ 86) * (a7 ^ 2) * a5 * (a3 ^ 2) * b8
    + (1808758200342675456 : R) * (h ^ 86) * (a7 ^ 2) * (a4 ^ 3) * b7
    + (5552938340547821568 : R) * (h ^ 86) * (a7 ^ 2) * (a4 ^ 2) * a3 * b8
    + (210578466951659520 : R) * (h ^ 80) * (a7 ^ 5) * a4 * a0
    + (41561539529932800 : R) * (h ^ 80) * (a7 ^ 5) * a3 * a1
    + (395824185999360000 : R) * (h ^ 80) * (a7 ^ 4) * a6 * a5 * a0
    - (728316502238822400 : R) * (h ^ 80) * (a7 ^ 4) * a6 * a4 * a1
    - (831230790598656000 : R) * (h ^ 80) * (a7 ^ 4) * a6 * a3 * a2
    - (633318697598976000 : R) * (h ^ 80) * (a7 ^ 4) * (a5 ^ 2) * a1
    - (3562417673994240000 : R) * (h ^ 80) * (a7 ^ 4) * a5 * a4 * a2
    - (1512048390517555200 : R) * (h ^ 80) * (a7 ^ 4) * a5 * (a3 ^ 2)
    - (2865767106635366400 : R) * (h ^ 80) * (a7 ^ 4) * (a4 ^ 2) * a3
    - (18471795346636800 : R) * (h ^ 78) * (a7 ^ 5) * a5 * b1
    - (44824890041171968 : R) * (h ^ 78) * (a7 ^ 5) * a4 * b2
    - (22166154415964160 : R) * (h ^ 78) * (a7 ^ 5) * a3 * b3
    - (15832967439974400 : R) * (h ^ 78) * (a7 ^ 4) * (a6 ^ 2) * b1
    - (91479367430963200 : R) * (h ^ 78) * (a7 ^ 4) * a6 * a5 * b2
    - (73887181386547200 : R) * (h ^ 78) * (a7 ^ 4) * a6 * a4 * b3
    - (25332747903959040 : R) * (h ^ 78) * (a7 ^ 4) * a6 * a3 * b4
    - (47498902319923200 : R) * (h ^ 78) * (a7 ^ 4) * (a5 ^ 2) * b3
    - (53480245575024640 : R) * (h ^ 78) * (a7 ^ 4) * a5 * a4 * b4
    - (14073748835532800 : R) * (h ^ 78) * (a7 ^ 4) * a5 * a3 * b5
    - (94733921849180160 : R) * (h ^ 78) * (a7 ^ 4) * (a4 ^ 2) * b5
    - (203717514394337280 : R) * (h ^ 78) * (a7 ^ 4) * a4 * a3 * b6
    - (232744621367623680 : R) * (h ^ 78) * (a7 ^ 4) * a4 * a2 * b7
    - (265993852991569920 : R) * (h ^ 78) * (a7 ^ 4) * a4 * a1 * b8
    - (116372310683811840 : R) * (h ^ 78) * (a7 ^ 4) * (a3 ^ 2) * b7
    - (265993852991569920 : R) * (h ^ 78) * (a7 ^ 4) * a3 * a2 * b8
    - (474989023199232000 : R) * (h ^ 78) * (a7 ^ 3) * a6 * a5 * a4 * b5
    - (569986827839078400 : R) * (h ^ 78) * (a7 ^ 3) * a6 * a5 * a3 * b6
    - (664984632478924800 : R) * (h ^ 78) * (a7 ^ 3) * a6 * a5 * a2 * b7
    - (759982437118771200 : R) * (h ^ 78) * (a7 ^ 3) * a6 * a5 * a1 * b8
    - (816981119902679040 : R) * (h ^ 78) * (a7 ^ 3) * a6 * (a4 ^ 2) * b6
    - (1906289279772917760 : R) * (h ^ 78) * (a7 ^ 3) * a6 * a4 * a3 * b7
    - (2178616319740477440 : R) * (h ^ 78) * (a7 ^ 3) * a6 * a4 * a2 * b8
    - (987977168254402560 : R) * (h ^ 78) * (a7 ^ 3) * a6 * (a3 ^ 2) * b8
    - (131941395333120000 : R) * (h ^ 78) * (a7 ^ 3) * (a5 ^ 3) * b5
    - (1234971460318003200 : R) * (h ^ 78) * (a7 ^ 3) * (a5 ^ 2) * a4 * b6
    - (1440800037037670400 : R) * (h ^ 78) * (a7 ^ 3) * (a5 ^ 2) * a3 * b7
    - (1646628613757337600 : R) * (h ^ 78) * (a7 ^ 3) * (a5 ^ 2) * a2 * b8
    - (2682104684331663360 : R) * (h ^ 78) * (a7 ^ 3) * a5 * (a4 ^ 2) * b7
    - (5725201026294743040 : R) * (h ^ 78) * (a7 ^ 3) * a5 * a4 * a3 * b8
    - (1528409123538862080 : R) * (h ^ 78) * (a7 ^ 3) * (a4 ^ 3) * b8
    - (79659617432371200 : R) * (h ^ 72) * (a7 ^ 6) * a5 * a0
    + (160704619515740160 : R) * (h ^ 72) * (a7 ^ 6) * a4 * a1
    + (181831735443456000 : R) * (h ^ 72) * (a7 ^ 6) * a3 * a2
    - (59373627899904000 : R) * (h ^ 72) * (a7 ^ 5) * (a6 ^ 2) * a0
    + (484884627849216000 : R) * (h ^ 72) * (a7 ^ 5) * a6 * a5 * a1
    + (1266637395197952000 : R) * (h ^ 72) * (a7 ^ 5) * a6 * a4 * a2
    + (567018146444083200 : R) * (h ^ 72) * (a7 ^ 5) * a6 * (a3 ^ 2)
    + (940082441748480000 : R) * (h ^ 72) * (a7 ^ 5) * (a5 ^ 2) * a2
    + (2896245568957317120 : R) * (h ^ 72) * (a7 ^ 5) * a5 * a4 * a3
    + (716441776658841600 : R) * (h ^ 72) * (a7 ^ 5) * (a4 ^ 3)
    + (6926923254988800 : R) * (h ^ 70) * (a7 ^ 6) * a6 * b1
    + (18779658602414080 : R) * (h ^ 70) * (a7 ^ 6) * a5 * b2
    + (15423949114441728 : R) * (h ^ 70) * (a7 ^ 6) * a4 * b3
    + (5541538603991040 : R) * (h ^ 70) * (a7 ^ 6) * a3 * b4
    + (14513553486643200 : R) * (h ^ 70) * (a7 ^ 5) * (a6 ^ 2) * b2
    + (30346520926617600 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a5 * b3
    + (17944029765304320 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a4 * b4
    + (5277655813324800 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a3 * b5
    + (11434920928870400 : R) * (h ^ 70) * (a7 ^ 5) * (a5 ^ 2) * b4
    + (114898965102592000 : R) * (h ^ 70) * (a7 ^ 5) * a5 * a4 * b5
    + (127323446496460800 : R) * (h ^ 70) * (a7 ^ 5) * a5 * a3 * b6
    + (145465388354764800 : R) * (h ^ 70) * (a7 ^ 5) * a5 * a2 * b7
    + (166246158119731200 : R) * (h ^ 70) * (a7 ^ 5) * a5 * a1 * b8
    + (177553535699779584 : R) * (h ^ 70) * (a7 ^ 5) * (a4 ^ 2) * b6
    + (409981497718603776 : R) * (h ^ 70) * (a7 ^ 5) * a4 * a3 * b7
    + (467705858176843776 : R) * (h ^ 70) * (a7 ^ 5) * a4 * a2 * b8
    + (216120005555650560 : R) * (h ^ 70) * (a7 ^ 5) * (a3 ^ 2) * b8
    + (89060441849856000 : R) * (h ^ 70) * (a7 ^ 4) * (a6 ^ 2) * a4 * b5
    + (106872530219827200 : R) * (h ^ 70) * (a7 ^ 4) * (a6 ^ 2) * a3 * b6
    + (124684618589798400 : R) * (h ^ 70) * (a7 ^ 4) * (a6 ^ 2) * a2 * b7
    + (142496706959769600 : R) * (h ^ 70) * (a7 ^ 4) * (a6 ^ 2) * a1 * b8
    + (148434069749760000 : R) * (h ^ 70) * (a7 ^ 4) * a6 * (a5 ^ 2) * b5
    + (878729692918579200 : R) * (h ^ 70) * (a7 ^ 4) * a6 * a5 * a4 * b6
    + (1025184641738342400 : R) * (h ^ 70) * (a7 ^ 4) * a6 * a5 * a3 * b7
    + (1171639590558105600 : R) * (h ^ 70) * (a7 ^ 4) * a6 * a5 * a2 * b8
    + (919895408262512640 : R) * (h ^ 70) * (a7 ^ 4) * a6 * (a4 ^ 2) * b7
    + (2001287084412764160 : R) * (h ^ 70) * (a7 ^ 4) * a6 * a4 * a3 * b8
    + (217703302299648000 : R) * (h ^ 70) * (a7 ^ 4) * (a5 ^ 3) * b6
    + (1288407725427916800 : R) * (h ^ 70) * (a7 ^ 4) * (a5 ^ 2) * a4 * b7
    + (1409134102157721600 : R) * (h ^ 70) * (a7 ^ 4) * (a5 ^ 2) * a3 * b8
    + (2102618076028600320 : R) * (h ^ 70) * (a7 ^ 4) * a5 * (a4 ^ 2) * b8
    + (23378365985587200 : R) * (h ^ 64) * (a7 ^ 7) * a6 * a0
    - (106934377748889600 : R) * (h ^ 64) * (a7 ^ 7) * a5 * a1
    - (271015872351436800 : R) * (h ^ 64) * (a7 ^ 7) * a4 * a2
    - (124035219534643200 : R) * (h ^ 64) * (a7 ^ 7) * (a3 ^ 2)
    - (92771293593600000 : R) * (h ^ 64) * (a7 ^ 6) * (a6 ^ 2) * a1
    - (661768560967680000 : R) * (h ^ 64) * (a7 ^ 6) * a6 * a5 * a2
    - (1004750218136125440 : R) * (h ^ 64) * (a7 ^ 6) * a6 * a4 * a3
    - (690713204568883200 : R) * (h ^ 64) * (a7 ^ 6) * (a5 ^ 2) * a3
    - (958042964188200960 : R) * (h ^ 64) * (a7 ^ 6) * a5 * (a4 ^ 2)
    - (757632231014400 : R) * (h ^ 62) * (a7 ^ 8) * b1
    - (5887884766740480 : R) * (h ^ 62) * (a7 ^ 7) * a6 * b2
    - (6176506569031680 : R) * (h ^ 62) * (a7 ^ 7) * a5 * b3
    - (3740538557693952 : R) * (h ^ 62) * (a7 ^ 7) * a4 * b4
    - (1154487209164800 : R) * (h ^ 62) * (a7 ^ 7) * a3 * b5
    - (4700412208742400 : R) * (h ^ 62) * (a7 ^ 6) * (a6 ^ 2) * b3
    - (7256776743321600 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a5 * b4
    - (42647307262361600 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a4 * b5
    - (47746292436172800 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a3 * b6
    - (54549520633036800 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a2 * b7
    - (62342309294899200 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a1 * b8
    - (34806414966784000 : R) * (h ^ 62) * (a7 ^ 6) * (a5 ^ 2) * b5
    - (190111058000609280 : R) * (h ^ 62) * (a7 ^ 6) * a5 * a4 * b6
    - (219872088985436160 : R) * (h ^ 62) * (a7 ^ 6) * a5 * a3 * b7
    - (250754621830594560 : R) * (h ^ 62) * (a7 ^ 6) * a5 * a2 * b8
    - (194209762471051264 : R) * (h ^ 62) * (a7 ^ 6) * (a4 ^ 2) * b7
    - (425436233158623232 : R) * (h ^ 62) * (a7 ^ 6) * a4 * a3 * b8
    - (55662776156160000 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 2) * a5 * b5
    - (155855773237248000 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 2) * a4 * b6
    - (181831735443456000 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 2) * a3 * b7
    - (207807697649664000 : R) * (h ^ 62) * (a7 ^ 5) * (a6 ^ 2) * a2 * b8
    - (230072808112128000 : R) * (h ^ 62) * (a7 ^ 5) * a6 * (a5 ^ 2) * b6
    - (872792330128588800 : R) * (h ^ 62) * (a7 ^ 5) * a6 * a5 * a4 * b7
    - (965811013838438400 : R) * (h ^ 62) * (a7 ^ 5) * a6 * a5 * a3 * b8
    - (699500501498068992 : R) * (h ^ 62) * (a7 ^ 5) * a6 * (a4 ^ 2) * b8
    - (199149043580928000 : R) * (h ^ 62) * (a7 ^ 5) * (a5 ^ 3) * b7
    - (924249474308505600 : R) * (h ^ 62) * (a7 ^ 5) * (a5 ^ 2) * a4 * b8
    - (2272896693043200 : R) * (h ^ 56) * (a7 ^ 9) * a0
    + (40912140474777600 : R) * (h ^ 56) * (a7 ^ 8) * a6 * a1
    + (140973711556608000 : R) * (h ^ 56) * (a7 ^ 8) * a5 * a2
    + (212886539426856960 : R) * (h ^ 56) * (a7 ^ 8) * a4 * a3
    + (115964116992000000 : R) * (h ^ 56) * (a7 ^ 7) * (a6 ^ 2) * a2
    + (467196234537369600 : R) * (h ^ 56) * (a7 ^ 7) * a6 * a5 * a3
    + (314939987491553280 : R) * (h ^ 56) * (a7 ^ 7) * a6 * (a4 ^ 2)
    + (406090875823718400 : R) * (h ^ 56) * (a7 ^ 7) * (a5 ^ 2) * a4
    + (593478580961280 : R) * (h ^ 54) * (a7 ^ 9) * b2
    + (1883257259950080 : R) * (h ^ 54) * (a7 ^ 8) * a6 * b3
    + (1471971191685120 : R) * (h ^ 54) * (a7 ^ 8) * a5 * b4
    + (5028934257213440 : R) * (h ^ 54) * (a7 ^ 8) * a4 * b5
    + (5330483911065600 : R) * (h ^ 54) * (a7 ^ 8) * a3 * b6
    + (5966353819238400 : R) * (h ^ 54) * (a7 ^ 8) * a2 * b7
    + (6818690079129600 : R) * (h ^ 54) * (a7 ^ 8) * a1 * b8
    + (1113255523123200 : R) * (h ^ 54) * (a7 ^ 7) * (a6 ^ 2) * b4
    + (25829933318144000 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a5 * b5
    + (67312789047214080 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a4 * b6
    + (77906239983452160 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a3 * b7
    + (88837790745231360 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a2 * b8
    + (49462561367654400 : R) * (h ^ 54) * (a7 ^ 7) * (a5 ^ 2) * b6
    + (183248387456368640 : R) * (h ^ 54) * (a7 ^ 7) * a5 * a4 * b7
    + (203555336429240320 : R) * (h ^ 54) * (a7 ^ 7) * a5 * a3 * b8
    + (145570116837310464 : R) * (h ^ 54) * (a7 ^ 7) * (a4 ^ 2) * b8
    + (6957847019520000 : R) * (h ^ 54) * (a7 ^ 6) * (a6 ^ 3) * b5
    + (80711025426432000 : R) * (h ^ 54) * (a7 ^ 6) * (a6 ^ 2) * a5 * b6
    + (146980652816793600 : R) * (h ^ 54) * (a7 ^ 6) * (a6 ^ 2) * a4 * b7
    + (164019647073484800 : R) * (h ^ 54) * (a7 ^ 6) * (a6 ^ 2) * a3 * b8
    + (199149043580928000 : R) * (h ^ 54) * (a7 ^ 6) * a6 * (a5 ^ 2) * b7
    + (602741279230525440 : R) * (h ^ 54) * (a7 ^ 6) * a6 * a5 * a4 * b8
    + (129467494170624000 : R) * (h ^ 54) * (a7 ^ 6) * (a5 ^ 3) * b8
    - (4510279375257600 : R) * (h ^ 48) * (a7 ^ 10) * a1
    - (49313740750848000 : R) * (h ^ 48) * (a7 ^ 9) * a6 * a2
    - (97885069561036800 : R) * (h ^ 48) * (a7 ^ 9) * a5 * a3
    - (65191526174556160 : R) * (h ^ 48) * (a7 ^ 9) * (a4 ^ 2)
    - (78067043559014400 : R) * (h ^ 48) * (a7 ^ 8) * (a6 ^ 2) * a3
    - (260501792410828800 : R) * (h ^ 48) * (a7 ^ 8) * a6 * a5 * a4
    - (54483807633408000 : R) * (h ^ 48) * (a7 ^ 8) * (a5 ^ 3)
    - (187040457031680 : R) * (h ^ 46) * (a7 ^ 10) * b3
    - (443756021022720 : R) * (h ^ 46) * (a7 ^ 9) * a6 * b4
    - (2962695284326400 : R) * (h ^ 46) * (a7 ^ 9) * a5 * b5
    - (7259514784972800 : R) * (h ^ 46) * (a7 ^ 9) * a4 * b6
    - (8341057343324160 : R) * (h ^ 46) * (a7 ^ 9) * a3 * b7
    - (9489343693455360 : R) * (h ^ 46) * (a7 ^ 9) * a2 * b8
    - (4791572889600000 : R) * (h ^ 46) * (a7 ^ 8) * (a6 ^ 2) * b5
    - (34610134961356800 : R) * (h ^ 46) * (a7 ^ 8) * a6 * a5 * b6
    - (61563030428712960 : R) * (h ^ 46) * (a7 ^ 8) * a6 * a4 * b7
    - (68865162026680320 : R) * (h ^ 46) * (a7 ^ 8) * a6 * a3 * b8
    - (41508174561280000 : R) * (h ^ 46) * (a7 ^ 8) * (a5 ^ 2) * b7
    - (124298415130542080 : R) * (h ^ 46) * (a7 ^ 8) * a5 * a4 * b8
    - (9393093476352000 : R) * (h ^ 46) * (a7 ^ 7) * (a6 ^ 3) * b6
    - (65886945804288000 : R) * (h ^ 46) * (a7 ^ 7) * (a6 ^ 2) * a5 * b7
    - (97292347968061440 : R) * (h ^ 46) * (a7 ^ 7) * (a6 ^ 2) * a4 * b8
    - (123880600711987200 : R) * (h ^ 46) * (a7 ^ 7) * a6 * (a5 ^ 2) * b8
    + (5238316597248000 : R) * (h ^ 40) * (a7 ^ 11) * a2
    + (32536541528064000 : R) * (h ^ 40) * (a7 ^ 10) * a6 * a3
    + (53316565713551360 : R) * (h ^ 40) * (a7 ^ 10) * a5 * a4
    + (41247470046412800 : R) * (h ^ 40) * (a7 ^ 9) * (a6 ^ 2) * a4
    + (51067698020352000 : R) * (h ^ 40) * (a7 ^ 9) * a6 * (a5 ^ 2)
    + (43800613355520 : R) * (h ^ 38) * (a7 ^ 11) * b4
    + (1088462153318400 : R) * (h ^ 38) * (a7 ^ 10) * a6 * b5
    + (3704308629504000 : R) * (h ^ 38) * (a7 ^ 10) * a5 * b6
    + (6439025573363712 : R) * (h ^ 38) * (a7 ^ 10) * a4 * b7
    + (7215657800171520 : R) * (h ^ 38) * (a7 ^ 10) * a3 * b8
    + (6023127918182400 : R) * (h ^ 38) * (a7 ^ 9) * (a6 ^ 2) * b6
    + (27369464345395200 : R) * (h ^ 38) * (a7 ^ 9) * a6 * a5 * b7
    + (39942336859340800 : R) * (h ^ 38) * (a7 ^ 9) * a6 * a4 * b8
    + (25287801071206400 : R) * (h ^ 38) * (a7 ^ 9) * (a5 ^ 2) * b8
    + (7204270768128000 : R) * (h ^ 38) * (a7 ^ 8) * (a6 ^ 3) * b7
    + (39064445544038400 : R) * (h ^ 38) * (a7 ^ 8) * (a6 ^ 2) * a5 * b8
    - (3381738445209600 : R) * (h ^ 32) * (a7 ^ 12) * a3
    - (16782516258078720 : R) * (h ^ 32) * (a7 ^ 11) * a6 * a4
    - (10324369054105600 : R) * (h ^ 32) * (a7 ^ 11) * (a5 ^ 2)
    - (15731559235584000 : R) * (h ^ 32) * (a7 ^ 10) * (a6 ^ 2) * a5
    - (81648313958400 : R) * (h ^ 30) * (a7 ^ 12) * b5
    - (1285004722176000 : R) * (h ^ 30) * (a7 ^ 11) * a6 * b6
    - (2837631121489920 : R) * (h ^ 30) * (a7 ^ 11) * a5 * b7
    - (4090581747761152 : R) * (h ^ 30) * (a7 ^ 11) * a4 * b8
    - (4470854595379200 : R) * (h ^ 30) * (a7 ^ 10) * (a6 ^ 2) * b7
    - (15862790619136000 : R) * (h ^ 30) * (a7 ^ 10) * a6 * a5 * b8
    - (4055844991795200 : R) * (h ^ 30) * (a7 ^ 9) * (a6 ^ 3) * b8
    + (1702150117785600 : R) * (h ^ 24) * (a7 ^ 13) * a4
    + (6317742017740800 : R) * (h ^ 24) * (a7 ^ 12) * a6 * a5
    + (1591109222400000 : R) * (h ^ 24) * (a7 ^ 11) * (a6 ^ 3)
    + (91201182105600 : R) * (h ^ 22) * (a7 ^ 13) * b6
    + (923049834577920 : R) * (h ^ 22) * (a7 ^ 12) * a6 * b7
    + (1606182208798720 : R) * (h ^ 22) * (a7 ^ 12) * a5 * b8
    + (2455867333017600 : R) * (h ^ 22) * (a7 ^ 11) * (a6 ^ 2) * b8
    - (632182987161600 : R) * (h ^ 16) * (a7 ^ 14) * a5
    - (951425512243200 : R) * (h ^ 16) * (a7 ^ 13) * (a6 ^ 2)
    - (63390688542720 : R) * (h ^ 14) * (a7 ^ 14) * b7
    - (494265717227520 : R) * (h ^ 14) * (a7 ^ 13) * a6 * b8
    + (188946203443200 : R) * (h ^ 8) * (a7 ^ 15) * a6
    + (33058212741120 : R) * (h ^ 6) * (a7 ^ 15) * b8
    - (12459767040000 : R) * (a7 ^ 17)

set_option maxHeartbeats 200000000 in
/-- Integer expansion of compact block `22` after the extra
`2^{34}` scale, on `λ = 0`. -/
def alignedSquareCompactBlock22Expansion810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    (6485183463413514240 : R) * (h ^ 112) * a4 * a2 * a1
    + (3242591731706757120 : R) * (h ^ 112) * (a3 ^ 2) * a1
    + (3242591731706757120 : R) * (h ^ 112) * a3 * (a2 ^ 2)
    - (1729382256910270464 : R) * (h ^ 110) * a4 * a2 * b3
    - (2305843009213693952 : R) * (h ^ 110) * a4 * a1 * b4
    - (2882303761517117440 : R) * (h ^ 110) * a4 * a0 * b5
    - (864691128455135232 : R) * (h ^ 110) * (a3 ^ 2) * b3
    - (2305843009213693952 : R) * (h ^ 110) * a3 * a2 * b4
    - (4053239664633446400 : R) * (h ^ 104) * a7 * a5 * a2 * a1
    - (5674535530486824960 : R) * (h ^ 104) * a7 * a4 * a3 * a1
    - (3242591731706757120 : R) * (h ^ 104) * a7 * a4 * (a2 ^ 2)
    - (3242591731706757120 : R) * (h ^ 104) * a7 * (a3 ^ 2) * a2
    + (1080863910568919040 : R) * (h ^ 102) * a7 * a5 * a2 * b3
    + (1441151880758558720 : R) * (h ^ 102) * a7 * a5 * a1 * b4
    + (1801439850948198400 : R) * (h ^ 102) * a7 * a5 * a0 * b5
    + (1513209474796486656 : R) * (h ^ 102) * a7 * a4 * a3 * b3
    + (2594073385365405696 : R) * (h ^ 102) * a7 * a4 * a2 * b4
    + (1801439850948198400 : R) * (h ^ 102) * a7 * a4 * a1 * b5
    + (2161727821137838080 : R) * (h ^ 102) * a7 * a4 * a0 * b6
    + (1297036692682702848 : R) * (h ^ 102) * a7 * (a3 ^ 2) * b4
    + (1441151880758558720 : R) * (h ^ 102) * a7 * a3 * a2 * b5
    + (864691128455135232 : R) * (h ^ 102) * (a3 ^ 3) * b8
    + (1519964874237542400 : R) * (h ^ 96) * (a7 ^ 2) * a6 * a2 * a1
    + (2533274790395904000 : R) * (h ^ 96) * (a7 ^ 2) * a5 * a3 * a1
    + (1519964874237542400 : R) * (h ^ 96) * (a7 ^ 2) * a5 * (a2 ^ 2)
    + (1418633882621706240 : R) * (h ^ 96) * (a7 ^ 2) * (a4 ^ 2) * a1
    + (3546584706554265600 : R) * (h ^ 96) * (a7 ^ 2) * a4 * a3 * a2
    - (405323966463344640 : R) * (h ^ 94) * (a7 ^ 2) * a6 * a2 * b3
    - (540431955284459520 : R) * (h ^ 94) * (a7 ^ 2) * a6 * a1 * b4
    - (675539944105574400 : R) * (h ^ 94) * (a7 ^ 2) * a6 * a0 * b5
    - (675539944105574400 : R) * (h ^ 94) * (a7 ^ 2) * a5 * a3 * b3
    - (1261007895663738880 : R) * (h ^ 94) * (a7 ^ 2) * a5 * a2 * b4
    - (1125899906842624000 : R) * (h ^ 94) * (a7 ^ 2) * a5 * a1 * b5
    - (1351079888211148800 : R) * (h ^ 94) * (a7 ^ 2) * a5 * a0 * b6
    - (378302368699121664 : R) * (h ^ 94) * (a7 ^ 2) * (a4 ^ 2) * b3
    - (1513209474796486656 : R) * (h ^ 94) * (a7 ^ 2) * a4 * a3 * b4
    - (1396115884484853760 : R) * (h ^ 94) * (a7 ^ 2) * a4 * a2 * b5
    - (810647932926689280 : R) * (h ^ 94) * (a7 ^ 2) * a4 * a1 * b6
    - (945755921747804160 : R) * (h ^ 94) * (a7 ^ 2) * a4 * a0 * b7
    - (675539944105574400 : R) * (h ^ 94) * (a7 ^ 2) * (a3 ^ 2) * b5
    - (540431955284459520 : R) * (h ^ 94) * (a7 ^ 2) * a3 * a2 * b6
    - (1297036692682702848 : R) * (h ^ 94) * a7 * a4 * (a3 ^ 2) * b8
    - (332492316239462400 : R) * (h ^ 88) * (a7 ^ 4) * a2 * a1
    - (823314306878668800 : R) * (h ^ 88) * (a7 ^ 3) * a6 * a3 * a1
    - (506654958079180800 : R) * (h ^ 88) * (a7 ^ 3) * a6 * (a2 ^ 2)
    - (1013309916158361600 : R) * (h ^ 88) * (a7 ^ 3) * a5 * a4 * a1
    - (1329969264957849600 : R) * (h ^ 88) * (a7 ^ 3) * a5 * a3 * a2
    - (709316941310853120 : R) * (h ^ 88) * (a7 ^ 3) * (a4 ^ 2) * a2
    + (164662861375733760 : R) * (h ^ 88) * (a7 ^ 3) * a4 * (a3 ^ 2)
    + (88664617663856640 : R) * (h ^ 86) * (a7 ^ 4) * a2 * b3
    + (118219490218475520 : R) * (h ^ 86) * (a7 ^ 4) * a1 * b4
    + (147774362773094400 : R) * (h ^ 86) * (a7 ^ 4) * a0 * b5
    + (219550481834311680 : R) * (h ^ 86) * (a7 ^ 3) * a6 * a3 * b3
    + (427841964600197120 : R) * (h ^ 86) * (a7 ^ 3) * a6 * a2 * b4
    + (422212465065984000 : R) * (h ^ 86) * (a7 ^ 3) * a6 * a1 * b5
    + (506654958079180800 : R) * (h ^ 86) * (a7 ^ 3) * a6 * a0 * b6
    + (270215977642229760 : R) * (h ^ 86) * (a7 ^ 3) * a5 * a4 * b3
    + (585467951558164480 : R) * (h ^ 86) * (a7 ^ 3) * a5 * a3 * b4
    + (647392446434508800 : R) * (h ^ 86) * (a7 ^ 3) * a5 * a2 * b5
    + (506654958079180800 : R) * (h ^ 86) * (a7 ^ 3) * a5 * a1 * b6
    + (591097451092377600 : R) * (h ^ 86) * (a7 ^ 3) * a5 * a0 * b7
    + (315251973915934720 : R) * (h ^ 86) * (a7 ^ 3) * (a4 ^ 2) * b4
    + (714946440845066240 : R) * (h ^ 86) * (a7 ^ 3) * a4 * a3 * b5
    + (506654958079180800 : R) * (h ^ 86) * (a7 ^ 3) * a4 * a2 * b6
    + (275845477176442880 : R) * (h ^ 86) * (a7 ^ 3) * a4 * a1 * b7
    + (315251973915934720 : R) * (h ^ 86) * (a7 ^ 3) * a4 * a0 * b8
    + (236438980436951040 : R) * (h ^ 86) * (a7 ^ 3) * (a3 ^ 2) * b6
    + (157625986957967360 : R) * (h ^ 86) * (a7 ^ 3) * a3 * a2 * b7
    + (405323966463344640 : R) * (h ^ 86) * (a7 ^ 2) * a5 * (a3 ^ 2) * b8
    + (648518346341351424 : R) * (h ^ 86) * (a7 ^ 2) * (a4 ^ 2) * a3 * b8
    - (88664617663856640 : R) * (h ^ 80) * (a7 ^ 5) * a4 * a0
    + (169016927421726720 : R) * (h ^ 80) * (a7 ^ 5) * a3 * a1
    + (105289233475829760 : R) * (h ^ 80) * (a7 ^ 5) * (a2 ^ 2)
    + (292909897639526400 : R) * (h ^ 80) * (a7 ^ 4) * a6 * a4 * a1
    + (395824185999360000 : R) * (h ^ 80) * (a7 ^ 4) * a6 * a3 * a2
    + (158329674399744000 : R) * (h ^ 80) * (a7 ^ 4) * (a5 ^ 2) * a1
    + (451239572039270400 : R) * (h ^ 80) * (a7 ^ 4) * a5 * a4 * a2
    - (43540660459929600 : R) * (h ^ 80) * (a7 ^ 4) * a5 * (a3 ^ 2)
    - (202661983231672320 : R) * (h ^ 80) * (a7 ^ 4) * (a4 ^ 2) * a3
    - (45071180645793792 : R) * (h ^ 78) * (a7 ^ 5) * a3 * b3
    - (89649780082343936 : R) * (h ^ 78) * (a7 ^ 5) * a2 * b4
    - (92358976733184000 : R) * (h ^ 78) * (a7 ^ 5) * a1 * b5
    - (110830772079820800 : R) * (h ^ 78) * (a7 ^ 5) * a0 * b6
    - (78109306037207040 : R) * (h ^ 78) * (a7 ^ 4) * a6 * a4 * b3
    - (177329235327713280 : R) * (h ^ 78) * (a7 ^ 4) * a6 * a3 * b4
    - (214624669741875200 : R) * (h ^ 78) * (a7 ^ 4) * a6 * a2 * b5
    - (189995609279692800 : R) * (h ^ 78) * (a7 ^ 4) * a6 * a1 * b6
    - (221661544159641600 : R) * (h ^ 78) * (a7 ^ 4) * a6 * a0 * b7
    - (42221246506598400 : R) * (h ^ 78) * (a7 ^ 4) * (a5 ^ 2) * b3
    - (205476732998778880 : R) * (h ^ 78) * (a7 ^ 4) * a5 * a4 * b4
    - (263882790666240000 : R) * (h ^ 78) * (a7 ^ 4) * a5 * a3 * b5
    - (232216855786291200 : R) * (h ^ 78) * (a7 ^ 4) * a5 * a2 * b6
    - (172403423235276800 : R) * (h ^ 78) * (a7 ^ 4) * a5 * a1 * b7
    - (197032483697459200 : R) * (h ^ 78) * (a7 ^ 4) * a5 * a0 * b8
    - (138626426029998080 : R) * (h ^ 78) * (a7 ^ 4) * (a4 ^ 2) * b5
    - (240661105087610880 : R) * (h ^ 78) * (a7 ^ 4) * a4 * a3 * b6
    - (147774362773094400 : R) * (h ^ 78) * (a7 ^ 4) * a4 * a2 * b7
    - (78812993478983680 : R) * (h ^ 78) * (a7 ^ 4) * a4 * a1 * b8
    - (66498463247892480 : R) * (h ^ 78) * (a7 ^ 4) * (a3 ^ 2) * b7
    - (39406496739491840 : R) * (h ^ 78) * (a7 ^ 4) * a3 * a2 * b8
    - (101330991615836160 : R) * (h ^ 78) * (a7 ^ 3) * a6 * (a3 ^ 2) * b8
    - (405323966463344640 : R) * (h ^ 78) * (a7 ^ 3) * a5 * a4 * a3 * b8
    - (108086391056891904 : R) * (h ^ 78) * (a7 ^ 3) * (a4 ^ 3) * b8
    + (55415386039910400 : R) * (h ^ 72) * (a7 ^ 6) * a5 * a0
    - (36481795809607680 : R) * (h ^ 72) * (a7 ^ 6) * a4 * a1
    - (68691988945305600 : R) * (h ^ 72) * (a7 ^ 6) * a3 * a2
    - (84112639524864000 : R) * (h ^ 72) * (a7 ^ 5) * a6 * a5 * a1
    - (121913849287802880 : R) * (h ^ 72) * (a7 ^ 5) * a6 * a4 * a2
    + (5343626510991360 : R) * (h ^ 72) * (a7 ^ 5) * a6 * (a3 ^ 2)
    - (64321430224896000 : R) * (h ^ 72) * (a7 ^ 5) * (a5 ^ 2) * a2
    + (139528025564774400 : R) * (h ^ 72) * (a7 ^ 5) * a5 * a4 * a3
    + (50665495807918080 : R) * (h ^ 72) * (a7 ^ 5) * (a4 ^ 3)
    + (15146872184242176 : R) * (h ^ 70) * (a7 ^ 6) * a4 * b3
    + (35219556460920832 : R) * (h ^ 70) * (a7 ^ 6) * a3 * b4
    + (44486240459816960 : R) * (h ^ 70) * (a7 ^ 6) * a2 * b5
    + (41561539529932800 : R) * (h ^ 70) * (a7 ^ 6) * a1 * b6
    + (48488462784921600 : R) * (h ^ 70) * (a7 ^ 6) * a0 * b7
    + (22430037206630400 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a5 * b3
    + (56365364086308864 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a4 * b4
    + (77845423246540800 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a3 * b5
    + (76526009293209600 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a2 * b6
    + (64651283713228800 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a1 * b7
    + (73887181386547200 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a0 * b8
    + (29906716275507200 : R) * (h ^ 70) * (a7 ^ 5) * (a5 ^ 2) * b4
    + (86729477198970880 : R) * (h ^ 70) * (a7 ^ 5) * a5 * a4 * b5
    + (87081320919859200 : R) * (h ^ 70) * (a7 ^ 5) * a5 * a3 * b6
    + (67729916271001600 : R) * (h ^ 70) * (a7 ^ 5) * a5 * a2 * b7
    + (49258120924364800 : R) * (h ^ 70) * (a7 ^ 5) * a5 * a1 * b8
    + (44860074413260800 : R) * (h ^ 70) * (a7 ^ 5) * (a4 ^ 2) * b6
    + (66498463247892480 : R) * (h ^ 70) * (a7 ^ 5) * a4 * a3 * b7
    + (37436171902517248 : R) * (h ^ 70) * (a7 ^ 5) * a4 * a2 * b8
    + (33988103437811712 : R) * (h ^ 70) * (a7 ^ 5) * (a3 ^ 2) * b8
    + (101330991615836160 : R) * (h ^ 70) * (a7 ^ 4) * a6 * a4 * a3 * b8
    + (63331869759897600 : R) * (h ^ 70) * (a7 ^ 4) * (a5 ^ 2) * a3 * b8
    + (101330991615836160 : R) * (h ^ 70) * (a7 ^ 4) * a5 * (a4 ^ 2) * b8
    - (20780769764966400 : R) * (h ^ 64) * (a7 ^ 7) * a6 * a0
    + (2886218022912000 : R) * (h ^ 64) * (a7 ^ 7) * a5 * a1
    + (13928063544852480 : R) * (h ^ 64) * (a7 ^ 7) * a4 * a2
    - (3815992543150080 : R) * (h ^ 64) * (a7 ^ 7) * (a3 ^ 2)
    + (10514079940608000 : R) * (h ^ 64) * (a7 ^ 6) * (a6 ^ 2) * a1
    + (32284410170572800 : R) * (h ^ 64) * (a7 ^ 6) * a6 * a5 * a2
    - (34461443193569280 : R) * (h ^ 64) * (a7 ^ 6) * a6 * a4 * a3
    - (25357486915584000 : R) * (h ^ 64) * (a7 ^ 6) * (a5 ^ 2) * a3
    - (51209754063667200 : R) * (h ^ 64) * (a7 ^ 6) * a5 * (a4 ^ 2)
    - (4156153952993280 : R) * (h ^ 62) * (a7 ^ 7) * a5 * b3
    - (10643272556871680 : R) * (h ^ 62) * (a7 ^ 7) * a4 * b4
    - (15258472614461440 : R) * (h ^ 62) * (a7 ^ 7) * a3 * b5
    - (15816474765557760 : R) * (h ^ 62) * (a7 ^ 7) * a2 * b6
    - (14142468312268800 : R) * (h ^ 62) * (a7 ^ 7) * a1 * b7
    - (16162820928307200 : R) * (h ^ 62) * (a7 ^ 7) * a0 * b8
    - (2803754650828800 : R) * (h ^ 62) * (a7 ^ 6) * (a6 ^ 2) * b3
    - (15217240928419840 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a5 * b4
    - (23199695346073600 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a4 * b5
    - (25398718601625600 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a3 * b6
    - (22320086043852800 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a2 * b7
    - (18471795346636800 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a1 * b8
    - (12149603486924800 : R) * (h ^ 62) * (a7 ^ 6) * (a5 ^ 2) * b5
    - (27443810229288960 : R) * (h ^ 62) * (a7 ^ 6) * a5 * a4 * b6
    - (23859402322739200 : R) * (h ^ 62) * (a7 ^ 6) * a5 * a3 * b7
    - (17240342323527680 : R) * (h ^ 62) * (a7 ^ 6) * a5 * a2 * b8
    - (12083632789258240 : R) * (h ^ 62) * (a7 ^ 6) * (a4 ^ 2) * b7
    - (33864958135500800 : R) * (h ^ 62) * (a7 ^ 6) * a4 * a3 * b8
    - (31665934879948800 : R) * (h ^ 62) * (a7 ^ 5) * a6 * a5 * a3 * b8
    - (25332747903959040 : R) * (h ^ 62) * (a7 ^ 5) * a6 * (a4 ^ 2) * b8
    - (31665934879948800 : R) * (h ^ 62) * (a7 ^ 5) * (a5 ^ 2) * a4 * b8
    + (4545793386086400 : R) * (h ^ 56) * (a7 ^ 9) * a0
    + (1001156876697600 : R) * (h ^ 56) * (a7 ^ 8) * a6 * a1
    - (1678902716006400 : R) * (h ^ 56) * (a7 ^ 8) * a5 * a2
    + (9546166110781440 : R) * (h ^ 56) * (a7 ^ 8) * a4 * a3
    - (3834546801868800 : R) * (h ^ 56) * (a7 ^ 7) * (a6 ^ 2) * a2
    + (13142599925760000 : R) * (h ^ 56) * (a7 ^ 7) * a6 * a5 * a3
    + (13037459126353920 : R) * (h ^ 56) * (a7 ^ 7) * a6 * (a4 ^ 2)
    + (17317308137472000 : R) * (h ^ 56) * (a7 ^ 7) * (a5 ^ 2) * a4
    + (1002960762961920 : R) * (h ^ 54) * (a7 ^ 8) * a6 * b3
    + (2755651017113600 : R) * (h ^ 54) * (a7 ^ 8) * a5 * b4
    + (4322626885386240 : R) * (h ^ 54) * (a7 ^ 8) * a4 * b5
    + (4949863909294080 : R) * (h ^ 54) * (a7 ^ 8) * a3 * b6
    + (4613138473287680 : R) * (h ^ 54) * (a7 ^ 8) * a2 * b7
    + (4040705232076800 : R) * (h ^ 54) * (a7 ^ 8) * a1 * b8
    + (1830686860247040 : R) * (h ^ 54) * (a7 ^ 7) * (a6 ^ 2) * b4
    + (6033570057420800 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a5 * b5
    + (7240284068904960 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a4 * b6
    + (6926923254988800 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a3 * b7
    + (5695470231879680 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a2 * b8
    + (3752083429785600 : R) * (h ^ 54) * (a7 ^ 7) * (a5 ^ 2) * b6
    + (7292510871224320 : R) * (h ^ 54) * (a7 ^ 7) * a5 * a4 * b7
    + (11313974649815040 : R) * (h ^ 54) * (a7 ^ 7) * a5 * a3 * b8
    + (7311752324710400 : R) * (h ^ 54) * (a7 ^ 7) * (a4 ^ 2) * b8
    + (3958241859993600 : R) * (h ^ 54) * (a7 ^ 6) * (a6 ^ 2) * a3 * b8
    + (15832967439974400 : R) * (h ^ 54) * (a7 ^ 6) * a6 * a5 * a4 * b8
    + (3298534883328000 : R) * (h ^ 54) * (a7 ^ 6) * (a5 ^ 3) * b8
    - (712647817297920 : R) * (h ^ 48) * (a7 ^ 10) * a1
    - (32212254720000 : R) * (h ^ 48) * (a7 ^ 9) * a6 * a2
    - (3638535231897600 : R) * (h ^ 48) * (a7 ^ 9) * a5 * a3
    - (2940334610841600 : R) * (h ^ 48) * (a7 ^ 9) * (a4 ^ 2)
    - (1748159063654400 : R) * (h ^ 48) * (a7 ^ 8) * (a6 ^ 2) * a3
    - (8888649567436800 : R) * (h ^ 48) * (a7 ^ 8) * a6 * a5 * a4
    - (1932735283200000 : R) * (h ^ 48) * (a7 ^ 8) * (a5 ^ 3)
    - (87759066759168 : R) * (h ^ 46) * (a7 ^ 10) * b3
    - (641324516638720 : R) * (h ^ 46) * (a7 ^ 9) * a6 * b4
    - (1078144165478400 : R) * (h ^ 46) * (a7 ^ 9) * a5 * b5
    - (1339127853219840 : R) * (h ^ 46) * (a7 ^ 9) * a4 * b6
    - (1346901744025600 : R) * (h ^ 46) * (a7 ^ 9) * a3 * b7
    - (1178539026022400 : R) * (h ^ 46) * (a7 ^ 9) * a2 * b8
    - (708669603840000 : R) * (h ^ 46) * (a7 ^ 8) * (a6 ^ 2) * b5
    - (1834810028851200 : R) * (h ^ 46) * (a7 ^ 8) * a6 * a5 * b6
    - (1908511667650560 : R) * (h ^ 46) * (a7 ^ 8) * a6 * a4 * b7
    - (3059391104286720 : R) * (h ^ 46) * (a7 ^ 8) * a6 * a3 * b8
    - (980111536947200 : R) * (h ^ 46) * (a7 ^ 8) * (a5 ^ 2) * b7
    - (4492879388999680 : R) * (h ^ 46) * (a7 ^ 8) * a5 * a4 * b8
    - (1979120929996800 : R) * (h ^ 46) * (a7 ^ 7) * (a6 ^ 2) * a4 * b8
    - (2473901162496000 : R) * (h ^ 46) * (a7 ^ 7) * a6 * (a5 ^ 2) * b8
    + (169424380231680 : R) * (h ^ 40) * (a7 ^ 11) * a2
    + (1010252812124160 : R) * (h ^ 40) * (a7 ^ 10) * a6 * a3
    + (1959036589178880 : R) * (h ^ 40) * (a7 ^ 10) * a5 * a4
    + (1147078390579200 : R) * (h ^ 40) * (a7 ^ 9) * (a6 ^ 2) * a4
    + (1486998208512000 : R) * (h ^ 40) * (a7 ^ 9) * a6 * (a5 ^ 2)
    + (55003498676224 : R) * (h ^ 38) * (a7 ^ 11) * b4
    + (244960775372800 : R) * (h ^ 38) * (a7 ^ 10) * a6 * b5
    + (325102180761600 : R) * (h ^ 38) * (a7 ^ 10) * a5 * b6
    + (351513545277440 : R) * (h ^ 38) * (a7 ^ 10) * a4 * b7
    + (446582109503488 : R) * (h ^ 38) * (a7 ^ 10) * a3 * b8
    + (211956636057600 : R) * (h ^ 38) * (a7 ^ 9) * (a6 ^ 2) * b6
    + (474271763660800 : R) * (h ^ 38) * (a7 ^ 9) * a6 * a5 * b7
    + (1141258709893120 : R) * (h ^ 38) * (a7 ^ 9) * a6 * a4 * b8
    + (661424963584000 : R) * (h ^ 38) * (a7 ^ 9) * (a5 ^ 2) * b8
    + (618475290624000 : R) * (h ^ 38) * (a7 ^ 8) * (a6 ^ 2) * a5 * b8
    - (131292620390400 : R) * (h ^ 32) * (a7 ^ 12) * a3
    - (507880553840640 : R) * (h ^ 32) * (a7 ^ 11) * a6 * a4
    - (314150014156800 : R) * (h ^ 32) * (a7 ^ 11) * (a5 ^ 2)
    - (381715218432000 : R) * (h ^ 32) * (a7 ^ 10) * (a6 ^ 2) * a5
    - (20726488760320 : R) * (h ^ 30) * (a7 ^ 12) * b5
    - (72588302745600 : R) * (h ^ 30) * (a7 ^ 11) * a6 * b6
    - (83558924288000 : R) * (h ^ 30) * (a7 ^ 11) * a5 * b7
    - (143036906471424 : R) * (h ^ 30) * (a7 ^ 11) * a4 * b8
    - (54116587929600 : R) * (h ^ 30) * (a7 ^ 10) * (a6 ^ 2) * b7
    - (326202766131200 : R) * (h ^ 30) * (a7 ^ 10) * a6 * a5 * b8
    - (51539607552000 : R) * (h ^ 30) * (a7 ^ 9) * (a6 ^ 3) * b8
    + (54706726502400 : R) * (h ^ 24) * (a7 ^ 13) * a4
    + (159614553292800 : R) * (h ^ 24) * (a7 ^ 12) * a6 * a5
    + (32614907904000 : R) * (h ^ 24) * (a7 ^ 11) * (a6 ^ 3)
    + (6081510113280 : R) * (h ^ 22) * (a7 ^ 13) * b6
    + (18407332249600 : R) * (h ^ 22) * (a7 ^ 12) * a6 * b7
    + (38198700933120 : R) * (h ^ 22) * (a7 ^ 12) * a5 * b8
    + (39460012032000 : R) * (h ^ 22) * (a7 ^ 11) * (a6 ^ 2) * b8
    - (16255097241600 : R) * (h ^ 16) * (a7 ^ 14) * a5
    - (20062745395200 : R) * (h ^ 16) * (a7 ^ 13) * (a6 ^ 2)
    - (1530552647680 : R) * (h ^ 14) * (a7 ^ 14) * b7
    - (8931644538880 : R) * (h ^ 14) * (a7 ^ 13) * a6 * b8
    + (3990750167040 : R) * (h ^ 8) * (a7 ^ 15) * a6
    + (623049441280 : R) * (h ^ 6) * (a7 ^ 15) * b8
    - (256945274880 : R) * (a7 ^ 17)

set_option maxHeartbeats 200000000 in
/-- Integer expansion of compact block `23` after the extra
`2^{34}` scale, on `λ = 0`. -/
def alignedSquareCompactBlock23Expansion810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    (4611686018427387904 : R) * (h ^ 118) * a0 * b1
    - (576460752303423488 : R) * (h ^ 110) * a7 * a1 * b1
    - (1152921504606846976 : R) * (h ^ 110) * a7 * a0 * b2
    - (2882303761517117440 : R) * (h ^ 110) * a3 * a1 * b5
    - (3458764513820540928 : R) * (h ^ 110) * a3 * a0 * b6
    - (1441151880758558720 : R) * (h ^ 110) * (a2 ^ 2) * b5
    - (3458764513820540928 : R) * (h ^ 110) * a2 * a1 * b6
    - (4035225266123964416 : R) * (h ^ 110) * a2 * a0 * b7
    - (2017612633061982208 : R) * (h ^ 110) * (a1 ^ 2) * b7
    - (4611686018427387904 : R) * (h ^ 110) * a1 * a0 * b8
    + (3242591731706757120 : R) * (h ^ 104) * (a7 ^ 2) * a1 * a0
    + (72057594037927936 : R) * (h ^ 102) * (a7 ^ 2) * a2 * b1
    + (144115188075855872 : R) * (h ^ 102) * (a7 ^ 2) * a1 * b2
    + (216172782113783808 : R) * (h ^ 102) * (a7 ^ 2) * a0 * b3
    + (1441151880758558720 : R) * (h ^ 102) * a7 * a4 * a1 * b5
    + (1729382256910270464 : R) * (h ^ 102) * a7 * a4 * a0 * b6
    + (1801439850948198400 : R) * (h ^ 102) * a7 * a3 * a2 * b5
    + (3891110078048108544 : R) * (h ^ 102) * a7 * a3 * a1 * b6
    + (4539628424389459968 : R) * (h ^ 102) * a7 * a3 * a0 * b7
    + (1945555039024054272 : R) * (h ^ 102) * a7 * (a2 ^ 2) * b6
    + (4539628424389459968 : R) * (h ^ 102) * a7 * a2 * a1 * b7
    + (5188146770730811392 : R) * (h ^ 102) * a7 * a2 * a0 * b8
    + (2594073385365405696 : R) * (h ^ 102) * a7 * (a1 ^ 2) * b8
    - (2702159776422297600 : R) * (h ^ 96) * (a7 ^ 3) * a2 * a0
    - (1351079888211148800 : R) * (h ^ 96) * (a7 ^ 3) * (a1 ^ 2)
    - (9007199254740992 : R) * (h ^ 94) * (a7 ^ 3) * a3 * b1
    - (18014398509481984 : R) * (h ^ 94) * (a7 ^ 3) * a2 * b2
    - (27021597764222976 : R) * (h ^ 94) * (a7 ^ 3) * a1 * b3
    - (36028797018963968 : R) * (h ^ 94) * (a7 ^ 3) * a0 * b4
    - (450359962737049600 : R) * (h ^ 94) * (a7 ^ 2) * a5 * a1 * b5
    - (540431955284459520 : R) * (h ^ 94) * (a7 ^ 2) * a5 * a0 * b6
    - (630503947831869440 : R) * (h ^ 94) * (a7 ^ 2) * a4 * a2 * b5
    - (1621295865853378560 : R) * (h ^ 94) * (a7 ^ 2) * a4 * a1 * b6
    - (1891511843495608320 : R) * (h ^ 94) * (a7 ^ 2) * a4 * a0 * b7
    - (337769972052787200 : R) * (h ^ 94) * (a7 ^ 2) * (a3 ^ 2) * b5
    - (1891511843495608320 : R) * (h ^ 94) * (a7 ^ 2) * a3 * a2 * b6
    - (2837267765243412480 : R) * (h ^ 94) * (a7 ^ 2) * a3 * a1 * b7
    - (3242591731706757120 : R) * (h ^ 94) * (a7 ^ 2) * a3 * a0 * b8
    - (1418633882621706240 : R) * (h ^ 94) * (a7 ^ 2) * (a2 ^ 2) * b7
    - (3242591731706757120 : R) * (h ^ 94) * (a7 ^ 2) * a2 * a1 * b8
    + (1393301134717747200 : R) * (h ^ 88) * (a7 ^ 4) * a3 * a0
    + (1393301134717747200 : R) * (h ^ 88) * (a7 ^ 4) * a2 * a1
    + (1125899906842624 : R) * (h ^ 86) * (a7 ^ 4) * a4 * b1
    + (2251799813685248 : R) * (h ^ 86) * (a7 ^ 4) * a3 * b2
    + (3377699720527872 : R) * (h ^ 86) * (a7 ^ 4) * a2 * b3
    + (4503599627370496 : R) * (h ^ 86) * (a7 ^ 4) * a1 * b4
    + (5629499534213120 : R) * (h ^ 86) * (a7 ^ 4) * a0 * b5
    + (112589990684262400 : R) * (h ^ 86) * (a7 ^ 3) * a6 * a1 * b5
    + (135107988821114880 : R) * (h ^ 86) * (a7 ^ 3) * a6 * a0 * b6
    + (168884986026393600 : R) * (h ^ 86) * (a7 ^ 3) * a5 * a2 * b5
    + (472877960873902080 : R) * (h ^ 86) * (a7 ^ 3) * a5 * a1 * b6
    + (551690954352885760 : R) * (h ^ 86) * (a7 ^ 3) * a5 * a0 * b7
    + (191402984163246080 : R) * (h ^ 86) * (a7 ^ 3) * a4 * a3 * b5
    + (607985949695016960 : R) * (h ^ 86) * (a7 ^ 3) * a4 * a2 * b6
    + (1024568915226787840 : R) * (h ^ 86) * (a7 ^ 3) * a4 * a1 * b7
    + (1170935903116328960 : R) * (h ^ 86) * (a7 ^ 3) * a4 * a0 * b8
    + (320881473450147840 : R) * (h ^ 86) * (a7 ^ 3) * (a3 ^ 2) * b6
    + (1142788405445263360 : R) * (h ^ 86) * (a7 ^ 3) * a3 * a2 * b7
    + (1486187877032263680 : R) * (h ^ 86) * (a7 ^ 3) * a3 * a1 * b8
    + (743093938516131840 : R) * (h ^ 86) * (a7 ^ 3) * (a2 ^ 2) * b8
    - (468655836223242240 : R) * (h ^ 80) * (a7 ^ 5) * a4 * a0
    - (557320453887098880 : R) * (h ^ 80) * (a7 ^ 5) * a3 * a1
    - (278660226943549440 : R) * (h ^ 80) * (a7 ^ 5) * (a2 ^ 2)
    - (140737488355328 : R) * (h ^ 78) * (a7 ^ 5) * a5 * b1
    - (281474976710656 : R) * (h ^ 78) * (a7 ^ 5) * a4 * b2
    - (422212465065984 : R) * (h ^ 78) * (a7 ^ 5) * a3 * b3
    - (562949953421312 : R) * (h ^ 78) * (a7 ^ 5) * a2 * b4
    - (20406935811522560 : R) * (h ^ 78) * (a7 ^ 5) * a1 * b5
    - (24488322973827072 : R) * (h ^ 78) * (a7 ^ 5) * a0 * b6
    - (38702809297715200 : R) * (h ^ 78) * (a7 ^ 4) * a6 * a2 * b5
    - (113997365567815680 : R) * (h ^ 78) * (a7 ^ 4) * a6 * a1 * b6
    - (132996926495784960 : R) * (h ^ 78) * (a7 ^ 4) * a6 * a0 * b7
    - (45739683715481600 : R) * (h ^ 78) * (a7 ^ 4) * a5 * a3 * b5
    - (156218612074414080 : R) * (h ^ 78) * (a7 ^ 4) * a5 * a2 * b6
    - (280771289268879360 : R) * (h ^ 78) * (a7 ^ 4) * a5 * a1 * b7
    - (320881473450147840 : R) * (h ^ 78) * (a7 ^ 4) * a5 * a0 * b8
    - (23925373020405760 : R) * (h ^ 78) * (a7 ^ 4) * (a4 ^ 2) * b5
    - (173107110677053440 : R) * (h ^ 78) * (a7 ^ 4) * a4 * a3 * b6
    - (339881034378117120 : R) * (h ^ 78) * (a7 ^ 4) * a4 * a2 * b7
    - (478507460408115200 : R) * (h ^ 78) * (a7 ^ 4) * a4 * a1 * b8
    - (177329235327713280 : R) * (h ^ 78) * (a7 ^ 4) * (a3 ^ 2) * b7
    - (517913957147607040 : R) * (h ^ 78) * (a7 ^ 4) * a3 * a2 * b8
    + (124024911613132800 : R) * (h ^ 72) * (a7 ^ 6) * a5 * a0
    + (168357220445061120 : R) * (h ^ 72) * (a7 ^ 6) * a4 * a1
    + (179440297653043200 : R) * (h ^ 72) * (a7 ^ 6) * a3 * a2
    + (17592186044416 : R) * (h ^ 70) * (a7 ^ 6) * a6 * b1
    + (35184372088832 : R) * (h ^ 70) * (a7 ^ 6) * a5 * b2
    + (52776558133248 : R) * (h ^ 70) * (a7 ^ 6) * a4 * b3
    + (70368744177664 : R) * (h ^ 70) * (a7 ^ 6) * a3 * b4
    + (6553089301544960 : R) * (h ^ 70) * (a7 ^ 6) * a2 * b5
    + (19685656183701504 : R) * (h ^ 70) * (a7 ^ 6) * a1 * b6
    + (22966598880985088 : R) * (h ^ 70) * (a7 ^ 6) * a0 * b7
    + (9763663254650880 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a3 * b5
    + (34938081484210176 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a2 * b6
    + (65390155527094272 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a1 * b7
    + (74731606316679168 : R) * (h ^ 70) * (a7 ^ 5) * a6 * a0 * b8
    + (10555311626649600 : R) * (h ^ 70) * (a7 ^ 5) * a5 * a4 * b5
    + (40215737297534976 : R) * (h ^ 70) * (a7 ^ 5) * a5 * a3 * b6
    + (83861950873731072 : R) * (h ^ 70) * (a7 ^ 5) * a5 * a2 * b7
    + (123989727241043968 : R) * (h ^ 70) * (a7 ^ 5) * a5 * a1 * b8
    + (20899517020766208 : R) * (h ^ 70) * (a7 ^ 5) * (a4 ^ 2) * b6
    + (91250669012385792 : R) * (h ^ 70) * (a7 ^ 5) * a4 * a3 * b7
    + (143692975610789888 : R) * (h ^ 70) * (a7 ^ 5) * a4 * a2 * b8
    + (74309393851613184 : R) * (h ^ 70) * (a7 ^ 5) * (a3 ^ 2) * b8
    - (28301429298954240 : R) * (h ^ 64) * (a7 ^ 7) * a6 * a0
    - (42155275808931840 : R) * (h ^ 64) * (a7 ^ 7) * a5 * a1
    - (47696814412922880 : R) * (h ^ 64) * (a7 ^ 7) * a4 * a2
    - (24541099531960320 : R) * (h ^ 64) * (a7 ^ 7) * (a3 ^ 2)
    - (1924145348608 : R) * (h ^ 62) * (a7 ^ 8) * b1
    - (4398046511104 : R) * (h ^ 62) * (a7 ^ 7) * a6 * b2
    - (6597069766656 : R) * (h ^ 62) * (a7 ^ 7) * a5 * b3
    - (8796093022208 : R) * (h ^ 62) * (a7 ^ 7) * a4 * b4
    - (1577799185858560 : R) * (h ^ 62) * (a7 ^ 7) * a3 * b5
    - (5772436045824000 : R) * (h ^ 62) * (a7 ^ 7) * a2 * b6
    - (11044594301009920 : R) * (h ^ 62) * (a7 ^ 7) * a1 * b7
    - (12622393486868480 : R) * (h ^ 62) * (a7 ^ 7) * a0 * b8
    - (2133052557885440 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a4 * b5
    - (8431055161786368 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a3 * b6
    - (18302470555959296 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a2 * b7
    - (27953983624577024 : R) * (h ^ 62) * (a7 ^ 6) * a6 * a1 * b8
    - (1099511627776000 : R) * (h ^ 62) * (a7 ^ 6) * (a5 ^ 2) * b5
    - (9024791440785408 : R) * (h ^ 62) * (a7 ^ 6) * a5 * a4 * b6
    - (20611444974288896 : R) * (h ^ 62) * (a7 ^ 6) * a5 * a3 * b7
    - (34111248740122624 : R) * (h ^ 62) * (a7 ^ 6) * a5 * a2 * b8
    - (10652068649893888 : R) * (h ^ 62) * (a7 ^ 6) * (a4 ^ 2) * b7
    - (36574154786340864 : R) * (h ^ 62) * (a7 ^ 6) * a4 * a3 * b8
    + (4723776830832640 : R) * (h ^ 56) * (a7 ^ 9) * a0
    + (9308053123891200 : R) * (h ^ 56) * (a7 ^ 8) * a6 * a1
    + (11039783937638400 : R) * (h ^ 56) * (a7 ^ 8) * a5 * a2
    + (11732476263137280 : R) * (h ^ 56) * (a7 ^ 8) * a4 * a3
    + (481036337152 : R) * (h ^ 54) * (a7 ^ 9) * b2
    + (824633720832 : R) * (h ^ 54) * (a7 ^ 8) * a6 * b3
    + (1099511627776 : R) * (h ^ 54) * (a7 ^ 8) * a5 * b4
    + (332602267402240 : R) * (h ^ 54) * (a7 ^ 8) * a4 * b5
    + (1340648271642624 : R) * (h ^ 54) * (a7 ^ 8) * a3 * b6
    + (2978336481476608 : R) * (h ^ 54) * (a7 ^ 8) * a2 * b7
    + (4635266144796672 : R) * (h ^ 54) * (a7 ^ 8) * a1 * b8
    + (426060755763200 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a5 * b5
    + (1797701511413760 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a4 * b6
    + (4242740493680640 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a3 * b7
    + (7267771859599360 : R) * (h ^ 54) * (a7 ^ 7) * a6 * a2 * b8
    + (923589767331840 : R) * (h ^ 54) * (a7 ^ 7) * (a5 ^ 2) * b6
    + (4502500115742720 : R) * (h ^ 54) * (a7 ^ 7) * a5 * a4 * b7
    + (8037429999042560 : R) * (h ^ 54) * (a7 ^ 7) * a5 * a3 * b8
    + (4134163720437760 : R) * (h ^ 54) * (a7 ^ 7) * (a4 ^ 2) * b8
    - (1525336160337920 : R) * (h ^ 48) * (a7 ^ 10) * a1
    - (2314128379084800 : R) * (h ^ 48) * (a7 ^ 9) * a6 * a2
    - (2530594730803200 : R) * (h ^ 48) * (a7 ^ 9) * a5 * a3
    - (1297767318159360 : R) * (h ^ 48) * (a7 ^ 9) * (a4 ^ 2)
    - (90194313216 : R) * (h ^ 46) * (a7 ^ 10) * b3
    - (137438953472 : R) * (h ^ 46) * (a7 ^ 9) * a6 * b4
    - (64596308131840 : R) * (h ^ 46) * (a7 ^ 9) * a5 * b5
    - (276973850984448 : R) * (h ^ 46) * (a7 ^ 9) * a4 * b6
    - (666926816690176 : R) * (h ^ 46) * (a7 ^ 9) * a3 * b7
    - (1166272599425024 : R) * (h ^ 46) * (a7 ^ 9) * a2 * b8
    - (39943195852800 : R) * (h ^ 46) * (a7 ^ 8) * (a6 ^ 2) * b5
    - (353561707806720 : R) * (h ^ 46) * (a7 ^ 8) * a6 * a5 * b6
    - (883904269516800 : R) * (h ^ 46) * (a7 ^ 8) * a6 * a4 * b7
    - (1624528430039040 : R) * (h ^ 46) * (a7 ^ 8) * a6 * a3 * b8
    - (452775452344320 : R) * (h ^ 46) * (a7 ^ 8) * (a5 ^ 2) * b7
    - (1711114970726400 : R) * (h ^ 46) * (a7 ^ 8) * a5 * a4 * b8
    + (367842474065920 : R) * (h ^ 40) * (a7 ^ 11) * a2
    + (505023729500160 : R) * (h ^ 40) * (a7 ^ 10) * a6 * a3
    + (529376194068480 : R) * (h ^ 40) * (a7 ^ 10) * a5 * a4
    + (15032385536 : R) * (h ^ 38) * (a7 ^ 11) * b4
    + (11843372318720 : R) * (h ^ 38) * (a7 ^ 10) * a6 * b5
    + (53092238229504 : R) * (h ^ 38) * (a7 ^ 10) * a5 * b6
    + (134923176378368 : R) * (h ^ 38) * (a7 ^ 10) * a4 * b7
    + (252574141775872 : R) * (h ^ 38) * (a7 ^ 10) * a3 * b8
    + (32792075304960 : R) * (h ^ 38) * (a7 ^ 9) * (a6 ^ 2) * b6
    + (171218871255040 : R) * (h ^ 38) * (a7 ^ 9) * a6 * a5 * b7
    + (331056079175680 : R) * (h ^ 38) * (a7 ^ 9) * a6 * a4 * b8
    + (169135812116480 : R) * (h ^ 38) * (a7 ^ 9) * (a5 ^ 2) * b8
    - (77918256496640 : R) * (h ^ 32) * (a7 ^ 12) * a3
    - (101371965603840 : R) * (h ^ 32) * (a7 ^ 11) * a6 * a4
    - (51700668825600 : R) * (h ^ 32) * (a7 ^ 11) * (a5 ^ 2)
    - (864362168320 : R) * (h ^ 30) * (a7 ^ 12) * b5
    - (9644349063168 : R) * (h ^ 30) * (a7 ^ 11) * a6 * b6
    - (25509018730496 : R) * (h ^ 30) * (a7 ^ 11) * a5 * b7
    - (50080392413184 : R) * (h ^ 30) * (a7 ^ 11) * a4 * b8
    - (15710721933312 : R) * (h ^ 30) * (a7 ^ 10) * (a6 ^ 2) * b7
    - (63183263891456 : R) * (h ^ 30) * (a7 ^ 10) * a6 * a5 * b8
    + (15237319229440 : R) * (h ^ 24) * (a7 ^ 13) * a4
    + (19146662215680 : R) * (h ^ 24) * (a7 ^ 12) * a6 * a5
    + (699005927424 : R) * (h ^ 22) * (a7 ^ 13) * b6
    + (4588694405120 : R) * (h ^ 22) * (a7 ^ 12) * a6 * b7
    + (9341218324480 : R) * (h ^ 22) * (a7 ^ 12) * a5 * b8
    + (5736197259264 : R) * (h ^ 22) * (a7 ^ 11) * (a6 ^ 2) * b8
    - (2815195873280 : R) * (h ^ 16) * (a7 ^ 14) * a5
    - (1725117235200 : R) * (h ^ 16) * (a7 ^ 13) * (a6 ^ 2)
    - (330481270784 : R) * (h ^ 14) * (a7 ^ 14) * b7
    - (1664073334784 : R) * (h ^ 14) * (a7 ^ 13) * a6 * b8
    + (498030346240 : R) * (h ^ 8) * (a7 ^ 15) * a6
    + (119103029248 : R) * (h ^ 6) * (a7 ^ 15) * b8
    - (35486187520 : R) * (a7 ^ 17)

end AlignedSquareCompactExpansions810

/-! ## Block-by-block `2^{34} · compact(bars / integers)` -/

section AlignedSquareCompactBlockClearing810

variable {F : Type*} [Field F] [CharZero F]

theorem alignedSquareCompactBlock0_of_L_zero
    (A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : F) :
    alignedSquareCompactBlock0_810 (0 : F) A B C0 D0 E0 F0
        G0 P Q R S0 T0 U0 V0 W0 = 0 := by
  simp only [alignedSquareCompactBlock0_810]
  ring

theorem alignedSquareCompactBlock0_eq_expansion
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F)
    (hh : h ≠ 0) :
    (alignedSquareCompactToSourceIntegerScale810 : F) *
      alignedSquareCompactBlock0_810
        (0 : F)
        (alignedSquareABar810 h a7 a6 / 16)
        (alignedSquareBBar810 h a7 a6 a5 / 32)
        (alignedSquareCBar810 h a7 a6 a5 a4 / 2048)
        (alignedSquareDBar810 h a7 a6 a5 a4 a3 / 1024)
        (alignedSquareEBar810 h a7 a6 a5 a4 a3 a2 / 65536)
        (alignedSquareFBar810 h a7 a6 a5 a4 a3 a2 a1 / 131072)
        (alignedSquareGBar810 h a7 a6 a5 a4 a3 a2 a1 a0 / 16777216)
        (alignedSquarePBar810 h a7 b8 / 64)
        (alignedSquareQBar810 h a7 b8 b7 / 64)
        (alignedSquareRBar810 h a7 b8 b7 b6 / 2048)
        (alignedSquareSBar810 h a7 b8 b7 b6 b5 / 8192)
        (alignedSquareTBar810 h a7 b8 b7 b6 b5 b4 / 131072)
        (alignedSquareUBar810 h a7 b8 b7 b6 b5 b4 b3 / 262144)
        (alignedSquareVBar810 h a7 b8 b7 b6 b5 b4 b3 b2 / 16777216)
        (alignedSquareWBar810 h a7 b8 b7 b6 b5 b4 b3 b2 b1 / 67108864) =
      alignedSquareCompactBlock0Expansion810 h a7 a6 a5 a4 a3
        a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 := by
  rw [alignedSquareCompactBlock0_of_L_zero]
  simp only [alignedSquareCompactBlock0Expansion810]
  ring

theorem alignedSquareCompactBlock1_of_L_zero
    (A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : F) :
    alignedSquareCompactBlock1_810 (0 : F) A B C0 D0 E0 F0
        G0 P Q R S0 T0 U0 V0 W0 = 0 := by
  simp only [alignedSquareCompactBlock1_810]
  ring

theorem alignedSquareCompactBlock1_eq_expansion
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F)
    (hh : h ≠ 0) :
    (alignedSquareCompactToSourceIntegerScale810 : F) *
      alignedSquareCompactBlock1_810
        (0 : F)
        (alignedSquareABar810 h a7 a6 / 16)
        (alignedSquareBBar810 h a7 a6 a5 / 32)
        (alignedSquareCBar810 h a7 a6 a5 a4 / 2048)
        (alignedSquareDBar810 h a7 a6 a5 a4 a3 / 1024)
        (alignedSquareEBar810 h a7 a6 a5 a4 a3 a2 / 65536)
        (alignedSquareFBar810 h a7 a6 a5 a4 a3 a2 a1 / 131072)
        (alignedSquareGBar810 h a7 a6 a5 a4 a3 a2 a1 a0 / 16777216)
        (alignedSquarePBar810 h a7 b8 / 64)
        (alignedSquareQBar810 h a7 b8 b7 / 64)
        (alignedSquareRBar810 h a7 b8 b7 b6 / 2048)
        (alignedSquareSBar810 h a7 b8 b7 b6 b5 / 8192)
        (alignedSquareTBar810 h a7 b8 b7 b6 b5 b4 / 131072)
        (alignedSquareUBar810 h a7 b8 b7 b6 b5 b4 b3 / 262144)
        (alignedSquareVBar810 h a7 b8 b7 b6 b5 b4 b3 b2 / 16777216)
        (alignedSquareWBar810 h a7 b8 b7 b6 b5 b4 b3 b2 b1 / 67108864) =
      alignedSquareCompactBlock1Expansion810 h a7 a6 a5 a4 a3
        a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 := by
  rw [alignedSquareCompactBlock1_of_L_zero]
  simp only [alignedSquareCompactBlock1Expansion810]
  ring

theorem alignedSquareCompactBlock2_of_L_zero
    (A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : F) :
    alignedSquareCompactBlock2_810 (0 : F) A B C0 D0 E0 F0
        G0 P Q R S0 T0 U0 V0 W0 = 0 := by
  simp only [alignedSquareCompactBlock2_810]
  ring

theorem alignedSquareCompactBlock2_eq_expansion
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F)
    (hh : h ≠ 0) :
    (alignedSquareCompactToSourceIntegerScale810 : F) *
      alignedSquareCompactBlock2_810
        (0 : F)
        (alignedSquareABar810 h a7 a6 / 16)
        (alignedSquareBBar810 h a7 a6 a5 / 32)
        (alignedSquareCBar810 h a7 a6 a5 a4 / 2048)
        (alignedSquareDBar810 h a7 a6 a5 a4 a3 / 1024)
        (alignedSquareEBar810 h a7 a6 a5 a4 a3 a2 / 65536)
        (alignedSquareFBar810 h a7 a6 a5 a4 a3 a2 a1 / 131072)
        (alignedSquareGBar810 h a7 a6 a5 a4 a3 a2 a1 a0 / 16777216)
        (alignedSquarePBar810 h a7 b8 / 64)
        (alignedSquareQBar810 h a7 b8 b7 / 64)
        (alignedSquareRBar810 h a7 b8 b7 b6 / 2048)
        (alignedSquareSBar810 h a7 b8 b7 b6 b5 / 8192)
        (alignedSquareTBar810 h a7 b8 b7 b6 b5 b4 / 131072)
        (alignedSquareUBar810 h a7 b8 b7 b6 b5 b4 b3 / 262144)
        (alignedSquareVBar810 h a7 b8 b7 b6 b5 b4 b3 b2 / 16777216)
        (alignedSquareWBar810 h a7 b8 b7 b6 b5 b4 b3 b2 b1 / 67108864) =
      alignedSquareCompactBlock2Expansion810 h a7 a6 a5 a4 a3
        a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 := by
  rw [alignedSquareCompactBlock2_of_L_zero]
  simp only [alignedSquareCompactBlock2Expansion810]
  ring

theorem alignedSquareCompactBlock3_of_L_zero
    (A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : F) :
    alignedSquareCompactBlock3_810 (0 : F) A B C0 D0 E0 F0
        G0 P Q R S0 T0 U0 V0 W0 = 0 := by
  simp only [alignedSquareCompactBlock3_810]
  ring

theorem alignedSquareCompactBlock3_eq_expansion
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F)
    (hh : h ≠ 0) :
    (alignedSquareCompactToSourceIntegerScale810 : F) *
      alignedSquareCompactBlock3_810
        (0 : F)
        (alignedSquareABar810 h a7 a6 / 16)
        (alignedSquareBBar810 h a7 a6 a5 / 32)
        (alignedSquareCBar810 h a7 a6 a5 a4 / 2048)
        (alignedSquareDBar810 h a7 a6 a5 a4 a3 / 1024)
        (alignedSquareEBar810 h a7 a6 a5 a4 a3 a2 / 65536)
        (alignedSquareFBar810 h a7 a6 a5 a4 a3 a2 a1 / 131072)
        (alignedSquareGBar810 h a7 a6 a5 a4 a3 a2 a1 a0 / 16777216)
        (alignedSquarePBar810 h a7 b8 / 64)
        (alignedSquareQBar810 h a7 b8 b7 / 64)
        (alignedSquareRBar810 h a7 b8 b7 b6 / 2048)
        (alignedSquareSBar810 h a7 b8 b7 b6 b5 / 8192)
        (alignedSquareTBar810 h a7 b8 b7 b6 b5 b4 / 131072)
        (alignedSquareUBar810 h a7 b8 b7 b6 b5 b4 b3 / 262144)
        (alignedSquareVBar810 h a7 b8 b7 b6 b5 b4 b3 b2 / 16777216)
        (alignedSquareWBar810 h a7 b8 b7 b6 b5 b4 b3 b2 b1 / 67108864) =
      alignedSquareCompactBlock3Expansion810 h a7 a6 a5 a4 a3
        a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 := by
  rw [alignedSquareCompactBlock3_of_L_zero]
  simp only [alignedSquareCompactBlock3Expansion810]
  ring

set_option maxHeartbeats 800000000 in
theorem alignedSquareCompactBlock4_eq_expansion
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F)
    (hh : h ≠ 0) :
    (alignedSquareCompactToSourceIntegerScale810 : F) *
      alignedSquareCompactBlock4_810
        (0 : F)
        (alignedSquareABar810 h a7 a6 / 16)
        (alignedSquareBBar810 h a7 a6 a5 / 32)
        (alignedSquareCBar810 h a7 a6 a5 a4 / 2048)
        (alignedSquareDBar810 h a7 a6 a5 a4 a3 / 1024)
        (alignedSquareEBar810 h a7 a6 a5 a4 a3 a2 / 65536)
        (alignedSquareFBar810 h a7 a6 a5 a4 a3 a2 a1 / 131072)
        (alignedSquareGBar810 h a7 a6 a5 a4 a3 a2 a1 a0 / 16777216)
        (alignedSquarePBar810 h a7 b8 / 64)
        (alignedSquareQBar810 h a7 b8 b7 / 64)
        (alignedSquareRBar810 h a7 b8 b7 b6 / 2048)
        (alignedSquareSBar810 h a7 b8 b7 b6 b5 / 8192)
        (alignedSquareTBar810 h a7 b8 b7 b6 b5 b4 / 131072)
        (alignedSquareUBar810 h a7 b8 b7 b6 b5 b4 b3 / 262144)
        (alignedSquareVBar810 h a7 b8 b7 b6 b5 b4 b3 b2 / 16777216)
        (alignedSquareWBar810 h a7 b8 b7 b6 b5 b4 b3 b2 b1 / 67108864) =
      alignedSquareCompactBlock4Expansion810 h a7 a6 a5 a4 a3
        a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h32 : (32 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have h1024 : (1024 : F) ≠ 0 := by norm_num
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have h8192 : (8192 : F) ≠ 0 := by norm_num
  have h65536 : (65536 : F) ≠ 0 := by norm_num
  have h131072 : (131072 : F) ≠ 0 := by norm_num
  have h262144 : (262144 : F) ≠ 0 := by norm_num
  have h16777216 : (16777216 : F) ≠ 0 := by norm_num
  have h67108864 : (67108864 : F) ≠ 0 := by norm_num
  have h17179869184 : (17179869184 : F) ≠ 0 := by norm_num
  simp only [alignedSquareCompactBlock4_810,
    alignedSquareCompactBlock4Expansion810,
    alignedSquareCompactToSourceIntegerScale810, alignedSquareABar810, alignedSquareBBar810, alignedSquareCBar810, alignedSquareDBar810, alignedSquareEBar810, alignedSquareFBar810, alignedSquareGBar810, alignedSquarePBar810, alignedSquareQBar810, alignedSquareRBar810, alignedSquareSBar810, alignedSquareTBar810, alignedSquareUBar810, alignedSquareVBar810, alignedSquareWBar810]
  field_simp [hh, h2, h4, h8, h16, h32, h64, h1024, h2048, h8192, h65536, h131072, h262144, h16777216, h67108864, h17179869184]
  ring

set_option maxHeartbeats 800000000 in
theorem alignedSquareCompactBlock5_eq_expansion
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F)
    (hh : h ≠ 0) :
    (alignedSquareCompactToSourceIntegerScale810 : F) *
      alignedSquareCompactBlock5_810
        (0 : F)
        (alignedSquareABar810 h a7 a6 / 16)
        (alignedSquareBBar810 h a7 a6 a5 / 32)
        (alignedSquareCBar810 h a7 a6 a5 a4 / 2048)
        (alignedSquareDBar810 h a7 a6 a5 a4 a3 / 1024)
        (alignedSquareEBar810 h a7 a6 a5 a4 a3 a2 / 65536)
        (alignedSquareFBar810 h a7 a6 a5 a4 a3 a2 a1 / 131072)
        (alignedSquareGBar810 h a7 a6 a5 a4 a3 a2 a1 a0 / 16777216)
        (alignedSquarePBar810 h a7 b8 / 64)
        (alignedSquareQBar810 h a7 b8 b7 / 64)
        (alignedSquareRBar810 h a7 b8 b7 b6 / 2048)
        (alignedSquareSBar810 h a7 b8 b7 b6 b5 / 8192)
        (alignedSquareTBar810 h a7 b8 b7 b6 b5 b4 / 131072)
        (alignedSquareUBar810 h a7 b8 b7 b6 b5 b4 b3 / 262144)
        (alignedSquareVBar810 h a7 b8 b7 b6 b5 b4 b3 b2 / 16777216)
        (alignedSquareWBar810 h a7 b8 b7 b6 b5 b4 b3 b2 b1 / 67108864) =
      alignedSquareCompactBlock5Expansion810 h a7 a6 a5 a4 a3
        a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h32 : (32 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have h1024 : (1024 : F) ≠ 0 := by norm_num
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have h8192 : (8192 : F) ≠ 0 := by norm_num
  have h65536 : (65536 : F) ≠ 0 := by norm_num
  have h131072 : (131072 : F) ≠ 0 := by norm_num
  have h262144 : (262144 : F) ≠ 0 := by norm_num
  have h16777216 : (16777216 : F) ≠ 0 := by norm_num
  have h67108864 : (67108864 : F) ≠ 0 := by norm_num
  have h17179869184 : (17179869184 : F) ≠ 0 := by norm_num
  simp only [alignedSquareCompactBlock5_810,
    alignedSquareCompactBlock5Expansion810,
    alignedSquareCompactToSourceIntegerScale810, alignedSquareABar810, alignedSquareBBar810, alignedSquareCBar810, alignedSquareDBar810, alignedSquareEBar810, alignedSquareFBar810, alignedSquareGBar810, alignedSquarePBar810, alignedSquareQBar810, alignedSquareRBar810, alignedSquareSBar810, alignedSquareTBar810, alignedSquareUBar810, alignedSquareVBar810, alignedSquareWBar810]
  field_simp [hh, h2, h4, h8, h16, h32, h64, h1024, h2048, h8192, h65536, h131072, h262144, h16777216, h67108864, h17179869184]
  ring

set_option maxHeartbeats 800000000 in
theorem alignedSquareCompactBlock6_eq_expansion
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F)
    (hh : h ≠ 0) :
    (alignedSquareCompactToSourceIntegerScale810 : F) *
      alignedSquareCompactBlock6_810
        (0 : F)
        (alignedSquareABar810 h a7 a6 / 16)
        (alignedSquareBBar810 h a7 a6 a5 / 32)
        (alignedSquareCBar810 h a7 a6 a5 a4 / 2048)
        (alignedSquareDBar810 h a7 a6 a5 a4 a3 / 1024)
        (alignedSquareEBar810 h a7 a6 a5 a4 a3 a2 / 65536)
        (alignedSquareFBar810 h a7 a6 a5 a4 a3 a2 a1 / 131072)
        (alignedSquareGBar810 h a7 a6 a5 a4 a3 a2 a1 a0 / 16777216)
        (alignedSquarePBar810 h a7 b8 / 64)
        (alignedSquareQBar810 h a7 b8 b7 / 64)
        (alignedSquareRBar810 h a7 b8 b7 b6 / 2048)
        (alignedSquareSBar810 h a7 b8 b7 b6 b5 / 8192)
        (alignedSquareTBar810 h a7 b8 b7 b6 b5 b4 / 131072)
        (alignedSquareUBar810 h a7 b8 b7 b6 b5 b4 b3 / 262144)
        (alignedSquareVBar810 h a7 b8 b7 b6 b5 b4 b3 b2 / 16777216)
        (alignedSquareWBar810 h a7 b8 b7 b6 b5 b4 b3 b2 b1 / 67108864) =
      alignedSquareCompactBlock6Expansion810 h a7 a6 a5 a4 a3
        a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h32 : (32 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have h1024 : (1024 : F) ≠ 0 := by norm_num
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have h8192 : (8192 : F) ≠ 0 := by norm_num
  have h65536 : (65536 : F) ≠ 0 := by norm_num
  have h131072 : (131072 : F) ≠ 0 := by norm_num
  have h262144 : (262144 : F) ≠ 0 := by norm_num
  have h16777216 : (16777216 : F) ≠ 0 := by norm_num
  have h67108864 : (67108864 : F) ≠ 0 := by norm_num
  have h17179869184 : (17179869184 : F) ≠ 0 := by norm_num
  simp only [alignedSquareCompactBlock6_810,
    alignedSquareCompactBlock6Expansion810,
    alignedSquareCompactToSourceIntegerScale810, alignedSquareABar810, alignedSquareBBar810, alignedSquareCBar810, alignedSquareDBar810, alignedSquareEBar810, alignedSquareFBar810, alignedSquareGBar810, alignedSquarePBar810, alignedSquareQBar810, alignedSquareRBar810, alignedSquareSBar810, alignedSquareTBar810, alignedSquareUBar810, alignedSquareVBar810, alignedSquareWBar810]
  field_simp [hh, h2, h4, h8, h16, h32, h64, h1024, h2048, h8192, h65536, h131072, h262144, h16777216, h67108864, h17179869184]
  ring

set_option maxHeartbeats 800000000 in
theorem alignedSquareCompactBlock7_eq_expansion
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F)
    (hh : h ≠ 0) :
    (alignedSquareCompactToSourceIntegerScale810 : F) *
      alignedSquareCompactBlock7_810
        (0 : F)
        (alignedSquareABar810 h a7 a6 / 16)
        (alignedSquareBBar810 h a7 a6 a5 / 32)
        (alignedSquareCBar810 h a7 a6 a5 a4 / 2048)
        (alignedSquareDBar810 h a7 a6 a5 a4 a3 / 1024)
        (alignedSquareEBar810 h a7 a6 a5 a4 a3 a2 / 65536)
        (alignedSquareFBar810 h a7 a6 a5 a4 a3 a2 a1 / 131072)
        (alignedSquareGBar810 h a7 a6 a5 a4 a3 a2 a1 a0 / 16777216)
        (alignedSquarePBar810 h a7 b8 / 64)
        (alignedSquareQBar810 h a7 b8 b7 / 64)
        (alignedSquareRBar810 h a7 b8 b7 b6 / 2048)
        (alignedSquareSBar810 h a7 b8 b7 b6 b5 / 8192)
        (alignedSquareTBar810 h a7 b8 b7 b6 b5 b4 / 131072)
        (alignedSquareUBar810 h a7 b8 b7 b6 b5 b4 b3 / 262144)
        (alignedSquareVBar810 h a7 b8 b7 b6 b5 b4 b3 b2 / 16777216)
        (alignedSquareWBar810 h a7 b8 b7 b6 b5 b4 b3 b2 b1 / 67108864) =
      alignedSquareCompactBlock7Expansion810 h a7 a6 a5 a4 a3
        a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h32 : (32 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have h1024 : (1024 : F) ≠ 0 := by norm_num
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have h8192 : (8192 : F) ≠ 0 := by norm_num
  have h65536 : (65536 : F) ≠ 0 := by norm_num
  have h131072 : (131072 : F) ≠ 0 := by norm_num
  have h262144 : (262144 : F) ≠ 0 := by norm_num
  have h16777216 : (16777216 : F) ≠ 0 := by norm_num
  have h67108864 : (67108864 : F) ≠ 0 := by norm_num
  have h17179869184 : (17179869184 : F) ≠ 0 := by norm_num
  simp only [alignedSquareCompactBlock7_810,
    alignedSquareCompactBlock7Expansion810,
    alignedSquareCompactToSourceIntegerScale810, alignedSquareABar810, alignedSquareBBar810, alignedSquareCBar810, alignedSquareDBar810, alignedSquareEBar810, alignedSquareFBar810, alignedSquareGBar810, alignedSquarePBar810, alignedSquareQBar810, alignedSquareRBar810, alignedSquareSBar810, alignedSquareTBar810, alignedSquareUBar810, alignedSquareVBar810, alignedSquareWBar810]
  field_simp [hh, h2, h4, h8, h16, h32, h64, h1024, h2048, h8192, h65536, h131072, h262144, h16777216, h67108864, h17179869184]
  ring

set_option maxHeartbeats 800000000 in
theorem alignedSquareCompactBlock8_eq_expansion
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F)
    (hh : h ≠ 0) :
    (alignedSquareCompactToSourceIntegerScale810 : F) *
      alignedSquareCompactBlock8_810
        (0 : F)
        (alignedSquareABar810 h a7 a6 / 16)
        (alignedSquareBBar810 h a7 a6 a5 / 32)
        (alignedSquareCBar810 h a7 a6 a5 a4 / 2048)
        (alignedSquareDBar810 h a7 a6 a5 a4 a3 / 1024)
        (alignedSquareEBar810 h a7 a6 a5 a4 a3 a2 / 65536)
        (alignedSquareFBar810 h a7 a6 a5 a4 a3 a2 a1 / 131072)
        (alignedSquareGBar810 h a7 a6 a5 a4 a3 a2 a1 a0 / 16777216)
        (alignedSquarePBar810 h a7 b8 / 64)
        (alignedSquareQBar810 h a7 b8 b7 / 64)
        (alignedSquareRBar810 h a7 b8 b7 b6 / 2048)
        (alignedSquareSBar810 h a7 b8 b7 b6 b5 / 8192)
        (alignedSquareTBar810 h a7 b8 b7 b6 b5 b4 / 131072)
        (alignedSquareUBar810 h a7 b8 b7 b6 b5 b4 b3 / 262144)
        (alignedSquareVBar810 h a7 b8 b7 b6 b5 b4 b3 b2 / 16777216)
        (alignedSquareWBar810 h a7 b8 b7 b6 b5 b4 b3 b2 b1 / 67108864) =
      alignedSquareCompactBlock8Expansion810 h a7 a6 a5 a4 a3
        a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h32 : (32 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have h1024 : (1024 : F) ≠ 0 := by norm_num
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have h8192 : (8192 : F) ≠ 0 := by norm_num
  have h65536 : (65536 : F) ≠ 0 := by norm_num
  have h131072 : (131072 : F) ≠ 0 := by norm_num
  have h262144 : (262144 : F) ≠ 0 := by norm_num
  have h16777216 : (16777216 : F) ≠ 0 := by norm_num
  have h67108864 : (67108864 : F) ≠ 0 := by norm_num
  have h17179869184 : (17179869184 : F) ≠ 0 := by norm_num
  simp only [alignedSquareCompactBlock8_810,
    alignedSquareCompactBlock8Expansion810,
    alignedSquareCompactToSourceIntegerScale810, alignedSquareABar810, alignedSquareBBar810, alignedSquareCBar810, alignedSquareDBar810, alignedSquareEBar810, alignedSquareFBar810, alignedSquareGBar810, alignedSquarePBar810, alignedSquareQBar810, alignedSquareRBar810, alignedSquareSBar810, alignedSquareTBar810, alignedSquareUBar810, alignedSquareVBar810, alignedSquareWBar810]
  field_simp [hh, h2, h4, h8, h16, h32, h64, h1024, h2048, h8192, h65536, h131072, h262144, h16777216, h67108864, h17179869184]
  ring

set_option maxHeartbeats 800000000 in
theorem alignedSquareCompactBlock9_eq_expansion
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F)
    (hh : h ≠ 0) :
    (alignedSquareCompactToSourceIntegerScale810 : F) *
      alignedSquareCompactBlock9_810
        (0 : F)
        (alignedSquareABar810 h a7 a6 / 16)
        (alignedSquareBBar810 h a7 a6 a5 / 32)
        (alignedSquareCBar810 h a7 a6 a5 a4 / 2048)
        (alignedSquareDBar810 h a7 a6 a5 a4 a3 / 1024)
        (alignedSquareEBar810 h a7 a6 a5 a4 a3 a2 / 65536)
        (alignedSquareFBar810 h a7 a6 a5 a4 a3 a2 a1 / 131072)
        (alignedSquareGBar810 h a7 a6 a5 a4 a3 a2 a1 a0 / 16777216)
        (alignedSquarePBar810 h a7 b8 / 64)
        (alignedSquareQBar810 h a7 b8 b7 / 64)
        (alignedSquareRBar810 h a7 b8 b7 b6 / 2048)
        (alignedSquareSBar810 h a7 b8 b7 b6 b5 / 8192)
        (alignedSquareTBar810 h a7 b8 b7 b6 b5 b4 / 131072)
        (alignedSquareUBar810 h a7 b8 b7 b6 b5 b4 b3 / 262144)
        (alignedSquareVBar810 h a7 b8 b7 b6 b5 b4 b3 b2 / 16777216)
        (alignedSquareWBar810 h a7 b8 b7 b6 b5 b4 b3 b2 b1 / 67108864) =
      alignedSquareCompactBlock9Expansion810 h a7 a6 a5 a4 a3
        a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h32 : (32 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have h1024 : (1024 : F) ≠ 0 := by norm_num
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have h8192 : (8192 : F) ≠ 0 := by norm_num
  have h65536 : (65536 : F) ≠ 0 := by norm_num
  have h131072 : (131072 : F) ≠ 0 := by norm_num
  have h262144 : (262144 : F) ≠ 0 := by norm_num
  have h16777216 : (16777216 : F) ≠ 0 := by norm_num
  have h67108864 : (67108864 : F) ≠ 0 := by norm_num
  have h17179869184 : (17179869184 : F) ≠ 0 := by norm_num
  simp only [alignedSquareCompactBlock9_810,
    alignedSquareCompactBlock9Expansion810,
    alignedSquareCompactToSourceIntegerScale810, alignedSquareABar810, alignedSquareBBar810, alignedSquareCBar810, alignedSquareDBar810, alignedSquareEBar810, alignedSquareFBar810, alignedSquareGBar810, alignedSquarePBar810, alignedSquareQBar810, alignedSquareRBar810, alignedSquareSBar810, alignedSquareTBar810, alignedSquareUBar810, alignedSquareVBar810, alignedSquareWBar810]
  field_simp [hh, h2, h4, h8, h16, h32, h64, h1024, h2048, h8192, h65536, h131072, h262144, h16777216, h67108864, h17179869184]
  ring

set_option maxHeartbeats 800000000 in
theorem alignedSquareCompactBlock10_eq_expansion
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F)
    (hh : h ≠ 0) :
    (alignedSquareCompactToSourceIntegerScale810 : F) *
      alignedSquareCompactBlock10_810
        (0 : F)
        (alignedSquareABar810 h a7 a6 / 16)
        (alignedSquareBBar810 h a7 a6 a5 / 32)
        (alignedSquareCBar810 h a7 a6 a5 a4 / 2048)
        (alignedSquareDBar810 h a7 a6 a5 a4 a3 / 1024)
        (alignedSquareEBar810 h a7 a6 a5 a4 a3 a2 / 65536)
        (alignedSquareFBar810 h a7 a6 a5 a4 a3 a2 a1 / 131072)
        (alignedSquareGBar810 h a7 a6 a5 a4 a3 a2 a1 a0 / 16777216)
        (alignedSquarePBar810 h a7 b8 / 64)
        (alignedSquareQBar810 h a7 b8 b7 / 64)
        (alignedSquareRBar810 h a7 b8 b7 b6 / 2048)
        (alignedSquareSBar810 h a7 b8 b7 b6 b5 / 8192)
        (alignedSquareTBar810 h a7 b8 b7 b6 b5 b4 / 131072)
        (alignedSquareUBar810 h a7 b8 b7 b6 b5 b4 b3 / 262144)
        (alignedSquareVBar810 h a7 b8 b7 b6 b5 b4 b3 b2 / 16777216)
        (alignedSquareWBar810 h a7 b8 b7 b6 b5 b4 b3 b2 b1 / 67108864) =
      alignedSquareCompactBlock10Expansion810 h a7 a6 a5 a4 a3
        a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h32 : (32 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have h1024 : (1024 : F) ≠ 0 := by norm_num
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have h8192 : (8192 : F) ≠ 0 := by norm_num
  have h65536 : (65536 : F) ≠ 0 := by norm_num
  have h131072 : (131072 : F) ≠ 0 := by norm_num
  have h262144 : (262144 : F) ≠ 0 := by norm_num
  have h16777216 : (16777216 : F) ≠ 0 := by norm_num
  have h67108864 : (67108864 : F) ≠ 0 := by norm_num
  have h17179869184 : (17179869184 : F) ≠ 0 := by norm_num
  simp only [alignedSquareCompactBlock10_810,
    alignedSquareCompactBlock10Expansion810,
    alignedSquareCompactToSourceIntegerScale810, alignedSquareABar810, alignedSquareBBar810, alignedSquareCBar810, alignedSquareDBar810, alignedSquareEBar810, alignedSquareFBar810, alignedSquareGBar810, alignedSquarePBar810, alignedSquareQBar810, alignedSquareRBar810, alignedSquareSBar810, alignedSquareTBar810, alignedSquareUBar810, alignedSquareVBar810, alignedSquareWBar810]
  field_simp [hh, h2, h4, h8, h16, h32, h64, h1024, h2048, h8192, h65536, h131072, h262144, h16777216, h67108864, h17179869184]
  ring

set_option maxHeartbeats 800000000 in
theorem alignedSquareCompactBlock11_eq_expansion
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F)
    (hh : h ≠ 0) :
    (alignedSquareCompactToSourceIntegerScale810 : F) *
      alignedSquareCompactBlock11_810
        (0 : F)
        (alignedSquareABar810 h a7 a6 / 16)
        (alignedSquareBBar810 h a7 a6 a5 / 32)
        (alignedSquareCBar810 h a7 a6 a5 a4 / 2048)
        (alignedSquareDBar810 h a7 a6 a5 a4 a3 / 1024)
        (alignedSquareEBar810 h a7 a6 a5 a4 a3 a2 / 65536)
        (alignedSquareFBar810 h a7 a6 a5 a4 a3 a2 a1 / 131072)
        (alignedSquareGBar810 h a7 a6 a5 a4 a3 a2 a1 a0 / 16777216)
        (alignedSquarePBar810 h a7 b8 / 64)
        (alignedSquareQBar810 h a7 b8 b7 / 64)
        (alignedSquareRBar810 h a7 b8 b7 b6 / 2048)
        (alignedSquareSBar810 h a7 b8 b7 b6 b5 / 8192)
        (alignedSquareTBar810 h a7 b8 b7 b6 b5 b4 / 131072)
        (alignedSquareUBar810 h a7 b8 b7 b6 b5 b4 b3 / 262144)
        (alignedSquareVBar810 h a7 b8 b7 b6 b5 b4 b3 b2 / 16777216)
        (alignedSquareWBar810 h a7 b8 b7 b6 b5 b4 b3 b2 b1 / 67108864) =
      alignedSquareCompactBlock11Expansion810 h a7 a6 a5 a4 a3
        a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h32 : (32 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have h1024 : (1024 : F) ≠ 0 := by norm_num
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have h8192 : (8192 : F) ≠ 0 := by norm_num
  have h65536 : (65536 : F) ≠ 0 := by norm_num
  have h131072 : (131072 : F) ≠ 0 := by norm_num
  have h262144 : (262144 : F) ≠ 0 := by norm_num
  have h16777216 : (16777216 : F) ≠ 0 := by norm_num
  have h67108864 : (67108864 : F) ≠ 0 := by norm_num
  have h17179869184 : (17179869184 : F) ≠ 0 := by norm_num
  simp only [alignedSquareCompactBlock11_810,
    alignedSquareCompactBlock11Expansion810,
    alignedSquareCompactToSourceIntegerScale810, alignedSquareABar810, alignedSquareBBar810, alignedSquareCBar810, alignedSquareDBar810, alignedSquareEBar810, alignedSquareFBar810, alignedSquareGBar810, alignedSquarePBar810, alignedSquareQBar810, alignedSquareRBar810, alignedSquareSBar810, alignedSquareTBar810, alignedSquareUBar810, alignedSquareVBar810, alignedSquareWBar810]
  field_simp [hh, h2, h4, h8, h16, h32, h64, h1024, h2048, h8192, h65536, h131072, h262144, h16777216, h67108864, h17179869184]
  ring

set_option maxHeartbeats 800000000 in
theorem alignedSquareCompactBlock12_eq_expansion
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F)
    (hh : h ≠ 0) :
    (alignedSquareCompactToSourceIntegerScale810 : F) *
      alignedSquareCompactBlock12_810
        (0 : F)
        (alignedSquareABar810 h a7 a6 / 16)
        (alignedSquareBBar810 h a7 a6 a5 / 32)
        (alignedSquareCBar810 h a7 a6 a5 a4 / 2048)
        (alignedSquareDBar810 h a7 a6 a5 a4 a3 / 1024)
        (alignedSquareEBar810 h a7 a6 a5 a4 a3 a2 / 65536)
        (alignedSquareFBar810 h a7 a6 a5 a4 a3 a2 a1 / 131072)
        (alignedSquareGBar810 h a7 a6 a5 a4 a3 a2 a1 a0 / 16777216)
        (alignedSquarePBar810 h a7 b8 / 64)
        (alignedSquareQBar810 h a7 b8 b7 / 64)
        (alignedSquareRBar810 h a7 b8 b7 b6 / 2048)
        (alignedSquareSBar810 h a7 b8 b7 b6 b5 / 8192)
        (alignedSquareTBar810 h a7 b8 b7 b6 b5 b4 / 131072)
        (alignedSquareUBar810 h a7 b8 b7 b6 b5 b4 b3 / 262144)
        (alignedSquareVBar810 h a7 b8 b7 b6 b5 b4 b3 b2 / 16777216)
        (alignedSquareWBar810 h a7 b8 b7 b6 b5 b4 b3 b2 b1 / 67108864) =
      alignedSquareCompactBlock12Expansion810 h a7 a6 a5 a4 a3
        a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h32 : (32 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have h1024 : (1024 : F) ≠ 0 := by norm_num
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have h8192 : (8192 : F) ≠ 0 := by norm_num
  have h65536 : (65536 : F) ≠ 0 := by norm_num
  have h131072 : (131072 : F) ≠ 0 := by norm_num
  have h262144 : (262144 : F) ≠ 0 := by norm_num
  have h16777216 : (16777216 : F) ≠ 0 := by norm_num
  have h67108864 : (67108864 : F) ≠ 0 := by norm_num
  have h17179869184 : (17179869184 : F) ≠ 0 := by norm_num
  simp only [alignedSquareCompactBlock12_810,
    alignedSquareCompactBlock12Expansion810,
    alignedSquareCompactToSourceIntegerScale810, alignedSquareABar810, alignedSquareBBar810, alignedSquareCBar810, alignedSquareDBar810, alignedSquareEBar810, alignedSquareFBar810, alignedSquareGBar810, alignedSquarePBar810, alignedSquareQBar810, alignedSquareRBar810, alignedSquareSBar810, alignedSquareTBar810, alignedSquareUBar810, alignedSquareVBar810, alignedSquareWBar810]
  field_simp [hh, h2, h4, h8, h16, h32, h64, h1024, h2048, h8192, h65536, h131072, h262144, h16777216, h67108864, h17179869184]
  ring

set_option maxHeartbeats 800000000 in
theorem alignedSquareCompactBlock13_eq_expansion
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F)
    (hh : h ≠ 0) :
    (alignedSquareCompactToSourceIntegerScale810 : F) *
      alignedSquareCompactBlock13_810
        (0 : F)
        (alignedSquareABar810 h a7 a6 / 16)
        (alignedSquareBBar810 h a7 a6 a5 / 32)
        (alignedSquareCBar810 h a7 a6 a5 a4 / 2048)
        (alignedSquareDBar810 h a7 a6 a5 a4 a3 / 1024)
        (alignedSquareEBar810 h a7 a6 a5 a4 a3 a2 / 65536)
        (alignedSquareFBar810 h a7 a6 a5 a4 a3 a2 a1 / 131072)
        (alignedSquareGBar810 h a7 a6 a5 a4 a3 a2 a1 a0 / 16777216)
        (alignedSquarePBar810 h a7 b8 / 64)
        (alignedSquareQBar810 h a7 b8 b7 / 64)
        (alignedSquareRBar810 h a7 b8 b7 b6 / 2048)
        (alignedSquareSBar810 h a7 b8 b7 b6 b5 / 8192)
        (alignedSquareTBar810 h a7 b8 b7 b6 b5 b4 / 131072)
        (alignedSquareUBar810 h a7 b8 b7 b6 b5 b4 b3 / 262144)
        (alignedSquareVBar810 h a7 b8 b7 b6 b5 b4 b3 b2 / 16777216)
        (alignedSquareWBar810 h a7 b8 b7 b6 b5 b4 b3 b2 b1 / 67108864) =
      alignedSquareCompactBlock13Expansion810 h a7 a6 a5 a4 a3
        a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h32 : (32 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have h1024 : (1024 : F) ≠ 0 := by norm_num
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have h8192 : (8192 : F) ≠ 0 := by norm_num
  have h65536 : (65536 : F) ≠ 0 := by norm_num
  have h131072 : (131072 : F) ≠ 0 := by norm_num
  have h262144 : (262144 : F) ≠ 0 := by norm_num
  have h16777216 : (16777216 : F) ≠ 0 := by norm_num
  have h67108864 : (67108864 : F) ≠ 0 := by norm_num
  have h17179869184 : (17179869184 : F) ≠ 0 := by norm_num
  simp only [alignedSquareCompactBlock13_810,
    alignedSquareCompactBlock13Expansion810,
    alignedSquareCompactToSourceIntegerScale810, alignedSquareABar810, alignedSquareBBar810, alignedSquareCBar810, alignedSquareDBar810, alignedSquareEBar810, alignedSquareFBar810, alignedSquareGBar810, alignedSquarePBar810, alignedSquareQBar810, alignedSquareRBar810, alignedSquareSBar810, alignedSquareTBar810, alignedSquareUBar810, alignedSquareVBar810, alignedSquareWBar810]
  field_simp [hh, h2, h4, h8, h16, h32, h64, h1024, h2048, h8192, h65536, h131072, h262144, h16777216, h67108864, h17179869184]
  ring

set_option maxHeartbeats 800000000 in
theorem alignedSquareCompactBlock14_eq_expansion
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F)
    (hh : h ≠ 0) :
    (alignedSquareCompactToSourceIntegerScale810 : F) *
      alignedSquareCompactBlock14_810
        (0 : F)
        (alignedSquareABar810 h a7 a6 / 16)
        (alignedSquareBBar810 h a7 a6 a5 / 32)
        (alignedSquareCBar810 h a7 a6 a5 a4 / 2048)
        (alignedSquareDBar810 h a7 a6 a5 a4 a3 / 1024)
        (alignedSquareEBar810 h a7 a6 a5 a4 a3 a2 / 65536)
        (alignedSquareFBar810 h a7 a6 a5 a4 a3 a2 a1 / 131072)
        (alignedSquareGBar810 h a7 a6 a5 a4 a3 a2 a1 a0 / 16777216)
        (alignedSquarePBar810 h a7 b8 / 64)
        (alignedSquareQBar810 h a7 b8 b7 / 64)
        (alignedSquareRBar810 h a7 b8 b7 b6 / 2048)
        (alignedSquareSBar810 h a7 b8 b7 b6 b5 / 8192)
        (alignedSquareTBar810 h a7 b8 b7 b6 b5 b4 / 131072)
        (alignedSquareUBar810 h a7 b8 b7 b6 b5 b4 b3 / 262144)
        (alignedSquareVBar810 h a7 b8 b7 b6 b5 b4 b3 b2 / 16777216)
        (alignedSquareWBar810 h a7 b8 b7 b6 b5 b4 b3 b2 b1 / 67108864) =
      alignedSquareCompactBlock14Expansion810 h a7 a6 a5 a4 a3
        a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h32 : (32 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have h1024 : (1024 : F) ≠ 0 := by norm_num
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have h8192 : (8192 : F) ≠ 0 := by norm_num
  have h65536 : (65536 : F) ≠ 0 := by norm_num
  have h131072 : (131072 : F) ≠ 0 := by norm_num
  have h262144 : (262144 : F) ≠ 0 := by norm_num
  have h16777216 : (16777216 : F) ≠ 0 := by norm_num
  have h67108864 : (67108864 : F) ≠ 0 := by norm_num
  have h17179869184 : (17179869184 : F) ≠ 0 := by norm_num
  simp only [alignedSquareCompactBlock14_810,
    alignedSquareCompactBlock14Expansion810,
    alignedSquareCompactToSourceIntegerScale810, alignedSquareABar810, alignedSquareBBar810, alignedSquareCBar810, alignedSquareDBar810, alignedSquareEBar810, alignedSquareFBar810, alignedSquareGBar810, alignedSquarePBar810, alignedSquareQBar810, alignedSquareRBar810, alignedSquareSBar810, alignedSquareTBar810, alignedSquareUBar810, alignedSquareVBar810, alignedSquareWBar810]
  field_simp [hh, h2, h4, h8, h16, h32, h64, h1024, h2048, h8192, h65536, h131072, h262144, h16777216, h67108864, h17179869184]
  ring

set_option maxHeartbeats 800000000 in
theorem alignedSquareCompactBlock15_eq_expansion
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F)
    (hh : h ≠ 0) :
    (alignedSquareCompactToSourceIntegerScale810 : F) *
      alignedSquareCompactBlock15_810
        (0 : F)
        (alignedSquareABar810 h a7 a6 / 16)
        (alignedSquareBBar810 h a7 a6 a5 / 32)
        (alignedSquareCBar810 h a7 a6 a5 a4 / 2048)
        (alignedSquareDBar810 h a7 a6 a5 a4 a3 / 1024)
        (alignedSquareEBar810 h a7 a6 a5 a4 a3 a2 / 65536)
        (alignedSquareFBar810 h a7 a6 a5 a4 a3 a2 a1 / 131072)
        (alignedSquareGBar810 h a7 a6 a5 a4 a3 a2 a1 a0 / 16777216)
        (alignedSquarePBar810 h a7 b8 / 64)
        (alignedSquareQBar810 h a7 b8 b7 / 64)
        (alignedSquareRBar810 h a7 b8 b7 b6 / 2048)
        (alignedSquareSBar810 h a7 b8 b7 b6 b5 / 8192)
        (alignedSquareTBar810 h a7 b8 b7 b6 b5 b4 / 131072)
        (alignedSquareUBar810 h a7 b8 b7 b6 b5 b4 b3 / 262144)
        (alignedSquareVBar810 h a7 b8 b7 b6 b5 b4 b3 b2 / 16777216)
        (alignedSquareWBar810 h a7 b8 b7 b6 b5 b4 b3 b2 b1 / 67108864) =
      alignedSquareCompactBlock15Expansion810 h a7 a6 a5 a4 a3
        a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h32 : (32 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have h1024 : (1024 : F) ≠ 0 := by norm_num
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have h8192 : (8192 : F) ≠ 0 := by norm_num
  have h65536 : (65536 : F) ≠ 0 := by norm_num
  have h131072 : (131072 : F) ≠ 0 := by norm_num
  have h262144 : (262144 : F) ≠ 0 := by norm_num
  have h16777216 : (16777216 : F) ≠ 0 := by norm_num
  have h67108864 : (67108864 : F) ≠ 0 := by norm_num
  have h17179869184 : (17179869184 : F) ≠ 0 := by norm_num
  simp only [alignedSquareCompactBlock15_810,
    alignedSquareCompactBlock15Expansion810,
    alignedSquareCompactToSourceIntegerScale810, alignedSquareABar810, alignedSquareBBar810, alignedSquareCBar810, alignedSquareDBar810, alignedSquareEBar810, alignedSquareFBar810, alignedSquareGBar810, alignedSquarePBar810, alignedSquareQBar810, alignedSquareRBar810, alignedSquareSBar810, alignedSquareTBar810, alignedSquareUBar810, alignedSquareVBar810, alignedSquareWBar810]
  field_simp [hh, h2, h4, h8, h16, h32, h64, h1024, h2048, h8192, h65536, h131072, h262144, h16777216, h67108864, h17179869184]
  ring

set_option maxHeartbeats 800000000 in
theorem alignedSquareCompactBlock16_eq_expansion
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F)
    (hh : h ≠ 0) :
    (alignedSquareCompactToSourceIntegerScale810 : F) *
      alignedSquareCompactBlock16_810
        (0 : F)
        (alignedSquareABar810 h a7 a6 / 16)
        (alignedSquareBBar810 h a7 a6 a5 / 32)
        (alignedSquareCBar810 h a7 a6 a5 a4 / 2048)
        (alignedSquareDBar810 h a7 a6 a5 a4 a3 / 1024)
        (alignedSquareEBar810 h a7 a6 a5 a4 a3 a2 / 65536)
        (alignedSquareFBar810 h a7 a6 a5 a4 a3 a2 a1 / 131072)
        (alignedSquareGBar810 h a7 a6 a5 a4 a3 a2 a1 a0 / 16777216)
        (alignedSquarePBar810 h a7 b8 / 64)
        (alignedSquareQBar810 h a7 b8 b7 / 64)
        (alignedSquareRBar810 h a7 b8 b7 b6 / 2048)
        (alignedSquareSBar810 h a7 b8 b7 b6 b5 / 8192)
        (alignedSquareTBar810 h a7 b8 b7 b6 b5 b4 / 131072)
        (alignedSquareUBar810 h a7 b8 b7 b6 b5 b4 b3 / 262144)
        (alignedSquareVBar810 h a7 b8 b7 b6 b5 b4 b3 b2 / 16777216)
        (alignedSquareWBar810 h a7 b8 b7 b6 b5 b4 b3 b2 b1 / 67108864) =
      alignedSquareCompactBlock16Expansion810 h a7 a6 a5 a4 a3
        a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h32 : (32 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have h1024 : (1024 : F) ≠ 0 := by norm_num
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have h8192 : (8192 : F) ≠ 0 := by norm_num
  have h65536 : (65536 : F) ≠ 0 := by norm_num
  have h131072 : (131072 : F) ≠ 0 := by norm_num
  have h262144 : (262144 : F) ≠ 0 := by norm_num
  have h16777216 : (16777216 : F) ≠ 0 := by norm_num
  have h67108864 : (67108864 : F) ≠ 0 := by norm_num
  have h17179869184 : (17179869184 : F) ≠ 0 := by norm_num
  simp only [alignedSquareCompactBlock16_810,
    alignedSquareCompactBlock16Expansion810,
    alignedSquareCompactToSourceIntegerScale810, alignedSquareABar810, alignedSquareBBar810, alignedSquareCBar810, alignedSquareDBar810, alignedSquareEBar810, alignedSquareFBar810, alignedSquareGBar810, alignedSquarePBar810, alignedSquareQBar810, alignedSquareRBar810, alignedSquareSBar810, alignedSquareTBar810, alignedSquareUBar810, alignedSquareVBar810, alignedSquareWBar810]
  field_simp [hh, h2, h4, h8, h16, h32, h64, h1024, h2048, h8192, h65536, h131072, h262144, h16777216, h67108864, h17179869184]
  ring

set_option maxHeartbeats 800000000 in
theorem alignedSquareCompactBlock17_eq_expansion
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F)
    (hh : h ≠ 0) :
    (alignedSquareCompactToSourceIntegerScale810 : F) *
      alignedSquareCompactBlock17_810
        (0 : F)
        (alignedSquareABar810 h a7 a6 / 16)
        (alignedSquareBBar810 h a7 a6 a5 / 32)
        (alignedSquareCBar810 h a7 a6 a5 a4 / 2048)
        (alignedSquareDBar810 h a7 a6 a5 a4 a3 / 1024)
        (alignedSquareEBar810 h a7 a6 a5 a4 a3 a2 / 65536)
        (alignedSquareFBar810 h a7 a6 a5 a4 a3 a2 a1 / 131072)
        (alignedSquareGBar810 h a7 a6 a5 a4 a3 a2 a1 a0 / 16777216)
        (alignedSquarePBar810 h a7 b8 / 64)
        (alignedSquareQBar810 h a7 b8 b7 / 64)
        (alignedSquareRBar810 h a7 b8 b7 b6 / 2048)
        (alignedSquareSBar810 h a7 b8 b7 b6 b5 / 8192)
        (alignedSquareTBar810 h a7 b8 b7 b6 b5 b4 / 131072)
        (alignedSquareUBar810 h a7 b8 b7 b6 b5 b4 b3 / 262144)
        (alignedSquareVBar810 h a7 b8 b7 b6 b5 b4 b3 b2 / 16777216)
        (alignedSquareWBar810 h a7 b8 b7 b6 b5 b4 b3 b2 b1 / 67108864) =
      alignedSquareCompactBlock17Expansion810 h a7 a6 a5 a4 a3
        a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h32 : (32 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have h1024 : (1024 : F) ≠ 0 := by norm_num
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have h8192 : (8192 : F) ≠ 0 := by norm_num
  have h65536 : (65536 : F) ≠ 0 := by norm_num
  have h131072 : (131072 : F) ≠ 0 := by norm_num
  have h262144 : (262144 : F) ≠ 0 := by norm_num
  have h16777216 : (16777216 : F) ≠ 0 := by norm_num
  have h67108864 : (67108864 : F) ≠ 0 := by norm_num
  have h17179869184 : (17179869184 : F) ≠ 0 := by norm_num
  simp only [alignedSquareCompactBlock17_810,
    alignedSquareCompactBlock17Expansion810,
    alignedSquareCompactToSourceIntegerScale810, alignedSquareABar810, alignedSquareBBar810, alignedSquareCBar810, alignedSquareDBar810, alignedSquareEBar810, alignedSquareFBar810, alignedSquareGBar810, alignedSquarePBar810, alignedSquareQBar810, alignedSquareRBar810, alignedSquareSBar810, alignedSquareTBar810, alignedSquareUBar810, alignedSquareVBar810, alignedSquareWBar810]
  field_simp [hh, h2, h4, h8, h16, h32, h64, h1024, h2048, h8192, h65536, h131072, h262144, h16777216, h67108864, h17179869184]
  ring

set_option maxHeartbeats 800000000 in
theorem alignedSquareCompactBlock18_eq_expansion
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F)
    (hh : h ≠ 0) :
    (alignedSquareCompactToSourceIntegerScale810 : F) *
      alignedSquareCompactBlock18_810
        (0 : F)
        (alignedSquareABar810 h a7 a6 / 16)
        (alignedSquareBBar810 h a7 a6 a5 / 32)
        (alignedSquareCBar810 h a7 a6 a5 a4 / 2048)
        (alignedSquareDBar810 h a7 a6 a5 a4 a3 / 1024)
        (alignedSquareEBar810 h a7 a6 a5 a4 a3 a2 / 65536)
        (alignedSquareFBar810 h a7 a6 a5 a4 a3 a2 a1 / 131072)
        (alignedSquareGBar810 h a7 a6 a5 a4 a3 a2 a1 a0 / 16777216)
        (alignedSquarePBar810 h a7 b8 / 64)
        (alignedSquareQBar810 h a7 b8 b7 / 64)
        (alignedSquareRBar810 h a7 b8 b7 b6 / 2048)
        (alignedSquareSBar810 h a7 b8 b7 b6 b5 / 8192)
        (alignedSquareTBar810 h a7 b8 b7 b6 b5 b4 / 131072)
        (alignedSquareUBar810 h a7 b8 b7 b6 b5 b4 b3 / 262144)
        (alignedSquareVBar810 h a7 b8 b7 b6 b5 b4 b3 b2 / 16777216)
        (alignedSquareWBar810 h a7 b8 b7 b6 b5 b4 b3 b2 b1 / 67108864) =
      alignedSquareCompactBlock18Expansion810 h a7 a6 a5 a4 a3
        a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h32 : (32 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have h1024 : (1024 : F) ≠ 0 := by norm_num
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have h8192 : (8192 : F) ≠ 0 := by norm_num
  have h65536 : (65536 : F) ≠ 0 := by norm_num
  have h131072 : (131072 : F) ≠ 0 := by norm_num
  have h262144 : (262144 : F) ≠ 0 := by norm_num
  have h16777216 : (16777216 : F) ≠ 0 := by norm_num
  have h67108864 : (67108864 : F) ≠ 0 := by norm_num
  have h17179869184 : (17179869184 : F) ≠ 0 := by norm_num
  simp only [alignedSquareCompactBlock18_810,
    alignedSquareCompactBlock18Expansion810,
    alignedSquareCompactToSourceIntegerScale810, alignedSquareABar810, alignedSquareBBar810, alignedSquareCBar810, alignedSquareDBar810, alignedSquareEBar810, alignedSquareFBar810, alignedSquareGBar810, alignedSquarePBar810, alignedSquareQBar810, alignedSquareRBar810, alignedSquareSBar810, alignedSquareTBar810, alignedSquareUBar810, alignedSquareVBar810, alignedSquareWBar810]
  field_simp [hh, h2, h4, h8, h16, h32, h64, h1024, h2048, h8192, h65536, h131072, h262144, h16777216, h67108864, h17179869184]
  ring

set_option maxHeartbeats 800000000 in
theorem alignedSquareCompactBlock19_eq_expansion
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F)
    (hh : h ≠ 0) :
    (alignedSquareCompactToSourceIntegerScale810 : F) *
      alignedSquareCompactBlock19_810
        (0 : F)
        (alignedSquareABar810 h a7 a6 / 16)
        (alignedSquareBBar810 h a7 a6 a5 / 32)
        (alignedSquareCBar810 h a7 a6 a5 a4 / 2048)
        (alignedSquareDBar810 h a7 a6 a5 a4 a3 / 1024)
        (alignedSquareEBar810 h a7 a6 a5 a4 a3 a2 / 65536)
        (alignedSquareFBar810 h a7 a6 a5 a4 a3 a2 a1 / 131072)
        (alignedSquareGBar810 h a7 a6 a5 a4 a3 a2 a1 a0 / 16777216)
        (alignedSquarePBar810 h a7 b8 / 64)
        (alignedSquareQBar810 h a7 b8 b7 / 64)
        (alignedSquareRBar810 h a7 b8 b7 b6 / 2048)
        (alignedSquareSBar810 h a7 b8 b7 b6 b5 / 8192)
        (alignedSquareTBar810 h a7 b8 b7 b6 b5 b4 / 131072)
        (alignedSquareUBar810 h a7 b8 b7 b6 b5 b4 b3 / 262144)
        (alignedSquareVBar810 h a7 b8 b7 b6 b5 b4 b3 b2 / 16777216)
        (alignedSquareWBar810 h a7 b8 b7 b6 b5 b4 b3 b2 b1 / 67108864) =
      alignedSquareCompactBlock19Expansion810 h a7 a6 a5 a4 a3
        a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h32 : (32 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have h1024 : (1024 : F) ≠ 0 := by norm_num
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have h8192 : (8192 : F) ≠ 0 := by norm_num
  have h65536 : (65536 : F) ≠ 0 := by norm_num
  have h131072 : (131072 : F) ≠ 0 := by norm_num
  have h262144 : (262144 : F) ≠ 0 := by norm_num
  have h16777216 : (16777216 : F) ≠ 0 := by norm_num
  have h67108864 : (67108864 : F) ≠ 0 := by norm_num
  have h17179869184 : (17179869184 : F) ≠ 0 := by norm_num
  simp only [alignedSquareCompactBlock19_810,
    alignedSquareCompactBlock19Expansion810,
    alignedSquareCompactToSourceIntegerScale810, alignedSquareABar810, alignedSquareBBar810, alignedSquareCBar810, alignedSquareDBar810, alignedSquareEBar810, alignedSquareFBar810, alignedSquareGBar810, alignedSquarePBar810, alignedSquareQBar810, alignedSquareRBar810, alignedSquareSBar810, alignedSquareTBar810, alignedSquareUBar810, alignedSquareVBar810, alignedSquareWBar810]
  field_simp [hh, h2, h4, h8, h16, h32, h64, h1024, h2048, h8192, h65536, h131072, h262144, h16777216, h67108864, h17179869184]
  ring

set_option maxHeartbeats 800000000 in
theorem alignedSquareCompactBlock20_eq_expansion
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F)
    (hh : h ≠ 0) :
    (alignedSquareCompactToSourceIntegerScale810 : F) *
      alignedSquareCompactBlock20_810
        (0 : F)
        (alignedSquareABar810 h a7 a6 / 16)
        (alignedSquareBBar810 h a7 a6 a5 / 32)
        (alignedSquareCBar810 h a7 a6 a5 a4 / 2048)
        (alignedSquareDBar810 h a7 a6 a5 a4 a3 / 1024)
        (alignedSquareEBar810 h a7 a6 a5 a4 a3 a2 / 65536)
        (alignedSquareFBar810 h a7 a6 a5 a4 a3 a2 a1 / 131072)
        (alignedSquareGBar810 h a7 a6 a5 a4 a3 a2 a1 a0 / 16777216)
        (alignedSquarePBar810 h a7 b8 / 64)
        (alignedSquareQBar810 h a7 b8 b7 / 64)
        (alignedSquareRBar810 h a7 b8 b7 b6 / 2048)
        (alignedSquareSBar810 h a7 b8 b7 b6 b5 / 8192)
        (alignedSquareTBar810 h a7 b8 b7 b6 b5 b4 / 131072)
        (alignedSquareUBar810 h a7 b8 b7 b6 b5 b4 b3 / 262144)
        (alignedSquareVBar810 h a7 b8 b7 b6 b5 b4 b3 b2 / 16777216)
        (alignedSquareWBar810 h a7 b8 b7 b6 b5 b4 b3 b2 b1 / 67108864) =
      alignedSquareCompactBlock20Expansion810 h a7 a6 a5 a4 a3
        a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h32 : (32 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have h1024 : (1024 : F) ≠ 0 := by norm_num
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have h8192 : (8192 : F) ≠ 0 := by norm_num
  have h65536 : (65536 : F) ≠ 0 := by norm_num
  have h131072 : (131072 : F) ≠ 0 := by norm_num
  have h262144 : (262144 : F) ≠ 0 := by norm_num
  have h16777216 : (16777216 : F) ≠ 0 := by norm_num
  have h67108864 : (67108864 : F) ≠ 0 := by norm_num
  have h17179869184 : (17179869184 : F) ≠ 0 := by norm_num
  simp only [alignedSquareCompactBlock20_810,
    alignedSquareCompactBlock20Expansion810,
    alignedSquareCompactToSourceIntegerScale810, alignedSquareABar810, alignedSquareBBar810, alignedSquareCBar810, alignedSquareDBar810, alignedSquareEBar810, alignedSquareFBar810, alignedSquareGBar810, alignedSquarePBar810, alignedSquareQBar810, alignedSquareRBar810, alignedSquareSBar810, alignedSquareTBar810, alignedSquareUBar810, alignedSquareVBar810, alignedSquareWBar810]
  field_simp [hh, h2, h4, h8, h16, h32, h64, h1024, h2048, h8192, h65536, h131072, h262144, h16777216, h67108864, h17179869184]
  ring

set_option maxHeartbeats 800000000 in
theorem alignedSquareCompactBlock21_eq_expansion
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F)
    (hh : h ≠ 0) :
    (alignedSquareCompactToSourceIntegerScale810 : F) *
      alignedSquareCompactBlock21_810
        (0 : F)
        (alignedSquareABar810 h a7 a6 / 16)
        (alignedSquareBBar810 h a7 a6 a5 / 32)
        (alignedSquareCBar810 h a7 a6 a5 a4 / 2048)
        (alignedSquareDBar810 h a7 a6 a5 a4 a3 / 1024)
        (alignedSquareEBar810 h a7 a6 a5 a4 a3 a2 / 65536)
        (alignedSquareFBar810 h a7 a6 a5 a4 a3 a2 a1 / 131072)
        (alignedSquareGBar810 h a7 a6 a5 a4 a3 a2 a1 a0 / 16777216)
        (alignedSquarePBar810 h a7 b8 / 64)
        (alignedSquareQBar810 h a7 b8 b7 / 64)
        (alignedSquareRBar810 h a7 b8 b7 b6 / 2048)
        (alignedSquareSBar810 h a7 b8 b7 b6 b5 / 8192)
        (alignedSquareTBar810 h a7 b8 b7 b6 b5 b4 / 131072)
        (alignedSquareUBar810 h a7 b8 b7 b6 b5 b4 b3 / 262144)
        (alignedSquareVBar810 h a7 b8 b7 b6 b5 b4 b3 b2 / 16777216)
        (alignedSquareWBar810 h a7 b8 b7 b6 b5 b4 b3 b2 b1 / 67108864) =
      alignedSquareCompactBlock21Expansion810 h a7 a6 a5 a4 a3
        a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h32 : (32 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have h1024 : (1024 : F) ≠ 0 := by norm_num
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have h8192 : (8192 : F) ≠ 0 := by norm_num
  have h65536 : (65536 : F) ≠ 0 := by norm_num
  have h131072 : (131072 : F) ≠ 0 := by norm_num
  have h262144 : (262144 : F) ≠ 0 := by norm_num
  have h16777216 : (16777216 : F) ≠ 0 := by norm_num
  have h67108864 : (67108864 : F) ≠ 0 := by norm_num
  have h17179869184 : (17179869184 : F) ≠ 0 := by norm_num
  simp only [alignedSquareCompactBlock21_810,
    alignedSquareCompactBlock21Expansion810,
    alignedSquareCompactToSourceIntegerScale810, alignedSquareABar810, alignedSquareBBar810, alignedSquareCBar810, alignedSquareDBar810, alignedSquareEBar810, alignedSquareFBar810, alignedSquareGBar810, alignedSquarePBar810, alignedSquareQBar810, alignedSquareRBar810, alignedSquareSBar810, alignedSquareTBar810, alignedSquareUBar810, alignedSquareVBar810, alignedSquareWBar810]
  field_simp [hh, h2, h4, h8, h16, h32, h64, h1024, h2048, h8192, h65536, h131072, h262144, h16777216, h67108864, h17179869184]
  ring

set_option maxHeartbeats 800000000 in
theorem alignedSquareCompactBlock22_eq_expansion
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F)
    (hh : h ≠ 0) :
    (alignedSquareCompactToSourceIntegerScale810 : F) *
      alignedSquareCompactBlock22_810
        (0 : F)
        (alignedSquareABar810 h a7 a6 / 16)
        (alignedSquareBBar810 h a7 a6 a5 / 32)
        (alignedSquareCBar810 h a7 a6 a5 a4 / 2048)
        (alignedSquareDBar810 h a7 a6 a5 a4 a3 / 1024)
        (alignedSquareEBar810 h a7 a6 a5 a4 a3 a2 / 65536)
        (alignedSquareFBar810 h a7 a6 a5 a4 a3 a2 a1 / 131072)
        (alignedSquareGBar810 h a7 a6 a5 a4 a3 a2 a1 a0 / 16777216)
        (alignedSquarePBar810 h a7 b8 / 64)
        (alignedSquareQBar810 h a7 b8 b7 / 64)
        (alignedSquareRBar810 h a7 b8 b7 b6 / 2048)
        (alignedSquareSBar810 h a7 b8 b7 b6 b5 / 8192)
        (alignedSquareTBar810 h a7 b8 b7 b6 b5 b4 / 131072)
        (alignedSquareUBar810 h a7 b8 b7 b6 b5 b4 b3 / 262144)
        (alignedSquareVBar810 h a7 b8 b7 b6 b5 b4 b3 b2 / 16777216)
        (alignedSquareWBar810 h a7 b8 b7 b6 b5 b4 b3 b2 b1 / 67108864) =
      alignedSquareCompactBlock22Expansion810 h a7 a6 a5 a4 a3
        a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h32 : (32 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have h1024 : (1024 : F) ≠ 0 := by norm_num
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have h8192 : (8192 : F) ≠ 0 := by norm_num
  have h65536 : (65536 : F) ≠ 0 := by norm_num
  have h131072 : (131072 : F) ≠ 0 := by norm_num
  have h262144 : (262144 : F) ≠ 0 := by norm_num
  have h16777216 : (16777216 : F) ≠ 0 := by norm_num
  have h67108864 : (67108864 : F) ≠ 0 := by norm_num
  have h17179869184 : (17179869184 : F) ≠ 0 := by norm_num
  simp only [alignedSquareCompactBlock22_810,
    alignedSquareCompactBlock22Expansion810,
    alignedSquareCompactToSourceIntegerScale810, alignedSquareABar810, alignedSquareBBar810, alignedSquareCBar810, alignedSquareDBar810, alignedSquareEBar810, alignedSquareFBar810, alignedSquareGBar810, alignedSquarePBar810, alignedSquareQBar810, alignedSquareRBar810, alignedSquareSBar810, alignedSquareTBar810, alignedSquareUBar810, alignedSquareVBar810, alignedSquareWBar810]
  field_simp [hh, h2, h4, h8, h16, h32, h64, h1024, h2048, h8192, h65536, h131072, h262144, h16777216, h67108864, h17179869184]
  ring

set_option maxHeartbeats 800000000 in
theorem alignedSquareCompactBlock23_eq_expansion
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F)
    (hh : h ≠ 0) :
    (alignedSquareCompactToSourceIntegerScale810 : F) *
      alignedSquareCompactBlock23_810
        (0 : F)
        (alignedSquareABar810 h a7 a6 / 16)
        (alignedSquareBBar810 h a7 a6 a5 / 32)
        (alignedSquareCBar810 h a7 a6 a5 a4 / 2048)
        (alignedSquareDBar810 h a7 a6 a5 a4 a3 / 1024)
        (alignedSquareEBar810 h a7 a6 a5 a4 a3 a2 / 65536)
        (alignedSquareFBar810 h a7 a6 a5 a4 a3 a2 a1 / 131072)
        (alignedSquareGBar810 h a7 a6 a5 a4 a3 a2 a1 a0 / 16777216)
        (alignedSquarePBar810 h a7 b8 / 64)
        (alignedSquareQBar810 h a7 b8 b7 / 64)
        (alignedSquareRBar810 h a7 b8 b7 b6 / 2048)
        (alignedSquareSBar810 h a7 b8 b7 b6 b5 / 8192)
        (alignedSquareTBar810 h a7 b8 b7 b6 b5 b4 / 131072)
        (alignedSquareUBar810 h a7 b8 b7 b6 b5 b4 b3 / 262144)
        (alignedSquareVBar810 h a7 b8 b7 b6 b5 b4 b3 b2 / 16777216)
        (alignedSquareWBar810 h a7 b8 b7 b6 b5 b4 b3 b2 b1 / 67108864) =
      alignedSquareCompactBlock23Expansion810 h a7 a6 a5 a4 a3
        a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h32 : (32 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have h1024 : (1024 : F) ≠ 0 := by norm_num
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have h8192 : (8192 : F) ≠ 0 := by norm_num
  have h65536 : (65536 : F) ≠ 0 := by norm_num
  have h131072 : (131072 : F) ≠ 0 := by norm_num
  have h262144 : (262144 : F) ≠ 0 := by norm_num
  have h16777216 : (16777216 : F) ≠ 0 := by norm_num
  have h67108864 : (67108864 : F) ≠ 0 := by norm_num
  have h17179869184 : (17179869184 : F) ≠ 0 := by norm_num
  simp only [alignedSquareCompactBlock23_810,
    alignedSquareCompactBlock23Expansion810,
    alignedSquareCompactToSourceIntegerScale810, alignedSquareABar810, alignedSquareBBar810, alignedSquareCBar810, alignedSquareDBar810, alignedSquareEBar810, alignedSquareFBar810, alignedSquareGBar810, alignedSquarePBar810, alignedSquareQBar810, alignedSquareRBar810, alignedSquareSBar810, alignedSquareTBar810, alignedSquareUBar810, alignedSquareVBar810, alignedSquareWBar810]
  field_simp [hh, h2, h4, h8, h16, h32, h64, h1024, h2048, h8192, h65536, h131072, h262144, h16777216, h67108864, h17179869184]
  ring

#print axioms alignedSquareCompactBlock0_eq_expansion
#print axioms alignedSquareCompactBlock4_eq_expansion
#print axioms alignedSquareCompactBlock23_eq_expansion

set_option maxHeartbeats 800000000 in
/-- Sum of the 24 compact-block expansions. -/
theorem alignedSquareCompact_eq_sum_expansions
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F)
    (hh : h ≠ 0) :
    (alignedSquareCompactToSourceIntegerScale810 : F) *
        degreeZeroClearedCompact810
          (0 : F)
          (alignedSquareABar810 h a7 a6 / 16)
          (alignedSquareBBar810 h a7 a6 a5 / 32)
          (alignedSquareCBar810 h a7 a6 a5 a4 / 2048)
          (alignedSquareDBar810 h a7 a6 a5 a4 a3 / 1024)
          (alignedSquareEBar810 h a7 a6 a5 a4 a3 a2 / 65536)
          (alignedSquareFBar810 h a7 a6 a5 a4 a3 a2 a1 / 131072)
          (alignedSquareGBar810 h a7 a6 a5 a4 a3 a2 a1 a0 / 16777216)
          (alignedSquarePBar810 h a7 b8 / 64)
          (alignedSquareQBar810 h a7 b8 b7 / 64)
          (alignedSquareRBar810 h a7 b8 b7 b6 / 2048)
          (alignedSquareSBar810 h a7 b8 b7 b6 b5 / 8192)
          (alignedSquareTBar810 h a7 b8 b7 b6 b5 b4 / 131072)
          (alignedSquareUBar810 h a7 b8 b7 b6 b5 b4 b3 / 262144)
          (alignedSquareVBar810 h a7 b8 b7 b6 b5 b4 b3 b2 / 16777216)
          (alignedSquareWBar810 h a7 b8 b7 b6 b5 b4 b3 b2 b1 / 67108864) =
      alignedSquareCompactBlock0Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock1Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock2Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock3Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock4Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock5Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock6Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock7Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock8Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock9Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock10Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock11Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock12Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock13Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock14Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock15Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock16Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock17Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock18Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock19Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock20Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock21Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock22Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock23Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 := by
  have hsum :=
    alignedSquareClearedCompact810_blockSum
      (0 : F)
      (alignedSquareABar810 h a7 a6 / 16)
      (alignedSquareBBar810 h a7 a6 a5 / 32)
      (alignedSquareCBar810 h a7 a6 a5 a4 / 2048)
      (alignedSquareDBar810 h a7 a6 a5 a4 a3 / 1024)
      (alignedSquareEBar810 h a7 a6 a5 a4 a3 a2 / 65536)
      (alignedSquareFBar810 h a7 a6 a5 a4 a3 a2 a1 / 131072)
      (alignedSquareGBar810 h a7 a6 a5 a4 a3 a2 a1 a0 / 16777216)
      (alignedSquarePBar810 h a7 b8 / 64)
      (alignedSquareQBar810 h a7 b8 b7 / 64)
      (alignedSquareRBar810 h a7 b8 b7 b6 / 2048)
      (alignedSquareSBar810 h a7 b8 b7 b6 b5 / 8192)
      (alignedSquareTBar810 h a7 b8 b7 b6 b5 b4 / 131072)
      (alignedSquareUBar810 h a7 b8 b7 b6 b5 b4 b3 / 262144)
      (alignedSquareVBar810 h a7 b8 b7 b6 b5 b4 b3 b2 / 16777216)
      (alignedSquareWBar810 h a7 b8 b7 b6 b5 b4 b3 b2 b1 / 67108864)
  have hb0 :=
    alignedSquareCompactBlock0_eq_expansion h a7 a6 a5 a4 a3 a2 a1
      a0 b8 b7 b6 b5 b4 b3 b2 b1 hh
  have hb1 :=
    alignedSquareCompactBlock1_eq_expansion h a7 a6 a5 a4 a3 a2 a1
      a0 b8 b7 b6 b5 b4 b3 b2 b1 hh
  have hb2 :=
    alignedSquareCompactBlock2_eq_expansion h a7 a6 a5 a4 a3 a2 a1
      a0 b8 b7 b6 b5 b4 b3 b2 b1 hh
  have hb3 :=
    alignedSquareCompactBlock3_eq_expansion h a7 a6 a5 a4 a3 a2 a1
      a0 b8 b7 b6 b5 b4 b3 b2 b1 hh
  have hb4 :=
    alignedSquareCompactBlock4_eq_expansion h a7 a6 a5 a4 a3 a2 a1
      a0 b8 b7 b6 b5 b4 b3 b2 b1 hh
  have hb5 :=
    alignedSquareCompactBlock5_eq_expansion h a7 a6 a5 a4 a3 a2 a1
      a0 b8 b7 b6 b5 b4 b3 b2 b1 hh
  have hb6 :=
    alignedSquareCompactBlock6_eq_expansion h a7 a6 a5 a4 a3 a2 a1
      a0 b8 b7 b6 b5 b4 b3 b2 b1 hh
  have hb7 :=
    alignedSquareCompactBlock7_eq_expansion h a7 a6 a5 a4 a3 a2 a1
      a0 b8 b7 b6 b5 b4 b3 b2 b1 hh
  have hb8 :=
    alignedSquareCompactBlock8_eq_expansion h a7 a6 a5 a4 a3 a2 a1
      a0 b8 b7 b6 b5 b4 b3 b2 b1 hh
  have hb9 :=
    alignedSquareCompactBlock9_eq_expansion h a7 a6 a5 a4 a3 a2 a1
      a0 b8 b7 b6 b5 b4 b3 b2 b1 hh
  have hb10 :=
    alignedSquareCompactBlock10_eq_expansion h a7 a6 a5 a4 a3 a2 a1
      a0 b8 b7 b6 b5 b4 b3 b2 b1 hh
  have hb11 :=
    alignedSquareCompactBlock11_eq_expansion h a7 a6 a5 a4 a3 a2 a1
      a0 b8 b7 b6 b5 b4 b3 b2 b1 hh
  have hb12 :=
    alignedSquareCompactBlock12_eq_expansion h a7 a6 a5 a4 a3 a2 a1
      a0 b8 b7 b6 b5 b4 b3 b2 b1 hh
  have hb13 :=
    alignedSquareCompactBlock13_eq_expansion h a7 a6 a5 a4 a3 a2 a1
      a0 b8 b7 b6 b5 b4 b3 b2 b1 hh
  have hb14 :=
    alignedSquareCompactBlock14_eq_expansion h a7 a6 a5 a4 a3 a2 a1
      a0 b8 b7 b6 b5 b4 b3 b2 b1 hh
  have hb15 :=
    alignedSquareCompactBlock15_eq_expansion h a7 a6 a5 a4 a3 a2 a1
      a0 b8 b7 b6 b5 b4 b3 b2 b1 hh
  have hb16 :=
    alignedSquareCompactBlock16_eq_expansion h a7 a6 a5 a4 a3 a2 a1
      a0 b8 b7 b6 b5 b4 b3 b2 b1 hh
  have hb17 :=
    alignedSquareCompactBlock17_eq_expansion h a7 a6 a5 a4 a3 a2 a1
      a0 b8 b7 b6 b5 b4 b3 b2 b1 hh
  have hb18 :=
    alignedSquareCompactBlock18_eq_expansion h a7 a6 a5 a4 a3 a2 a1
      a0 b8 b7 b6 b5 b4 b3 b2 b1 hh
  have hb19 :=
    alignedSquareCompactBlock19_eq_expansion h a7 a6 a5 a4 a3 a2 a1
      a0 b8 b7 b6 b5 b4 b3 b2 b1 hh
  have hb20 :=
    alignedSquareCompactBlock20_eq_expansion h a7 a6 a5 a4 a3 a2 a1
      a0 b8 b7 b6 b5 b4 b3 b2 b1 hh
  have hb21 :=
    alignedSquareCompactBlock21_eq_expansion h a7 a6 a5 a4 a3 a2 a1
      a0 b8 b7 b6 b5 b4 b3 b2 b1 hh
  have hb22 :=
    alignedSquareCompactBlock22_eq_expansion h a7 a6 a5 a4 a3 a2 a1
      a0 b8 b7 b6 b5 b4 b3 b2 b1 hh
  have hb23 :=
    alignedSquareCompactBlock23_eq_expansion h a7 a6 a5 a4 a3 a2 a1
      a0 b8 b7 b6 b5 b4 b3 b2 b1 hh
  rw [hsum, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add]
  rw [hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19, hb20, hb21, hb22, hb23]

#print axioms alignedSquareCompact_eq_sum_expansions

end AlignedSquareCompactBlockClearing810

/-! ## Source numerator equals the sum of compact-block expansions -/

section AlignedSquareSourceEqExpansion810

variable {R : Type*} [CommRing R]

set_option maxHeartbeats 1600000000 in
/-- The `λ = 0` source numerator is the sum of the 24 compact-block
expansions.  Each expansion is an integer polynomial; this is not the
977-term `field_simp` transport. -/
theorem alignedSquareClearedNumerator810_eq_sum_expansions
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) :
    alignedSquareClearedNumerator810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6
        b5 b4 b3 b2 b1 =
      alignedSquareCompactBlock0Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock1Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock2Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock3Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock4Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock5Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock6Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock7Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock8Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock9Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock10Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock11Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock12Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock13Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock14Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock15Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock16Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock17Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock18Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock19Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock20Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock21Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock22Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock23Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 := by
  simp only [alignedSquareClearedNumerator810,
    degreeZeroClearedSource810, degreeZeroClearedSourceBlock0_810, degreeZeroClearedSourceBlock1_810, degreeZeroClearedSourceBlock2_810, degreeZeroClearedSourceBlock3_810, degreeZeroClearedSourceBlock4_810, degreeZeroClearedSourceBlock5_810, degreeZeroClearedSourceBlock6_810, degreeZeroClearedSourceBlock7_810, degreeZeroClearedSourceBlock8_810, degreeZeroClearedSourceBlock9_810, degreeZeroClearedSourceBlock10_810, degreeZeroClearedSourceBlock11_810, degreeZeroClearedSourceBlock12_810, degreeZeroClearedSourceBlock13_810, degreeZeroClearedSourceBlock14_810, degreeZeroClearedSourceBlock15_810, degreeZeroClearedSourceBlock16_810, degreeZeroClearedSourceBlock17_810, degreeZeroClearedSourceBlock18_810, degreeZeroClearedSourceBlock19_810, degreeZeroClearedSourceBlock20_810, degreeZeroClearedSourceBlock21_810, degreeZeroClearedSourceBlock22_810, degreeZeroClearedSourceBlock23_810, degreeZeroClearedSourceBlock24_810,
    alignedSquareCompactBlock0Expansion810, alignedSquareCompactBlock1Expansion810, alignedSquareCompactBlock2Expansion810, alignedSquareCompactBlock3Expansion810, alignedSquareCompactBlock4Expansion810, alignedSquareCompactBlock5Expansion810, alignedSquareCompactBlock6Expansion810, alignedSquareCompactBlock7Expansion810, alignedSquareCompactBlock8Expansion810, alignedSquareCompactBlock9Expansion810, alignedSquareCompactBlock10Expansion810, alignedSquareCompactBlock11Expansion810, alignedSquareCompactBlock12Expansion810, alignedSquareCompactBlock13Expansion810, alignedSquareCompactBlock14Expansion810, alignedSquareCompactBlock15Expansion810, alignedSquareCompactBlock16Expansion810, alignedSquareCompactBlock17Expansion810, alignedSquareCompactBlock18Expansion810, alignedSquareCompactBlock19Expansion810, alignedSquareCompactBlock20Expansion810, alignedSquareCompactBlock21Expansion810, alignedSquareCompactBlock22Expansion810, alignedSquareCompactBlock23Expansion810]
  ring

#print axioms alignedSquareClearedNumerator810_eq_sum_expansions

end AlignedSquareSourceEqExpansion810

/-! ## Field identity `N = 2^{62} h^{119} ρ` -/


end Max11DegreeRoutes
