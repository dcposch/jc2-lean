import Grok810AlignedSquareSourceWrapperScratch
import Grok810DegreeZeroSourceNumeratorScratch
import Grok810DegreeZeroCompactBridgeScratch
import Grok810DegreeZeroTowerOrders111to118Scratch
import Grok810SpeedValLibScratch

/-! # Split base of `Grok810AlignedSquareClearedNumeratorBlocksScratch`.

Bars, compact blocks and the block-sum identity.  The block expansions
and their clearing identities live in the `…Part<n>Scratch` modules;
`Grok810AlignedSquareClearedNumeratorBlocksScratch` re-exports the whole family.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

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
  simp only [Max11ReflectVal.polyR_cons, Max11ReflectVal.monoR_cons, Max11ReflectVal.polyR_nil_left, Max11ReflectVal.polyR_nil_right, Max11ReflectVal.monoR_nil_left, Max11ReflectVal.monoR_nil_right, pow_zero, pow_one, one_mul, mul_one, alignedSquareLBar810, hL]
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
  simp only [Max11ReflectVal.polyR_cons, Max11ReflectVal.monoR_cons, Max11ReflectVal.polyR_nil_left, Max11ReflectVal.polyR_nil_right, Max11ReflectVal.monoR_nil_left, Max11ReflectVal.monoR_nil_right, pow_zero, pow_one, one_mul, mul_one, alignedSquareABar810]
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
  simp only [Max11ReflectVal.polyR_cons, Max11ReflectVal.monoR_cons, Max11ReflectVal.polyR_nil_left, Max11ReflectVal.polyR_nil_right, Max11ReflectVal.monoR_nil_left, Max11ReflectVal.monoR_nil_right, pow_zero, pow_one, one_mul, mul_one, alignedSquareBBar810]
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
  simp only [Max11ReflectVal.polyR_cons, Max11ReflectVal.monoR_cons, Max11ReflectVal.polyR_nil_left, Max11ReflectVal.polyR_nil_right, Max11ReflectVal.monoR_nil_left, Max11ReflectVal.monoR_nil_right, pow_zero, pow_one, one_mul, mul_one, alignedSquareCBar810]
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
  simp only [Max11ReflectVal.polyR_cons, Max11ReflectVal.monoR_cons, Max11ReflectVal.polyR_nil_left, Max11ReflectVal.polyR_nil_right, Max11ReflectVal.monoR_nil_left, Max11ReflectVal.monoR_nil_right, pow_zero, pow_one, one_mul, mul_one, alignedSquareDBar810]
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
  simp only [Max11ReflectVal.polyR_cons, Max11ReflectVal.monoR_cons, Max11ReflectVal.polyR_nil_left, Max11ReflectVal.polyR_nil_right, Max11ReflectVal.monoR_nil_left, Max11ReflectVal.monoR_nil_right, pow_zero, pow_one, one_mul, mul_one, alignedSquareEBar810]
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
  simp only [Max11ReflectVal.polyR_cons, Max11ReflectVal.monoR_cons, Max11ReflectVal.polyR_nil_left, Max11ReflectVal.polyR_nil_right, Max11ReflectVal.monoR_nil_left, Max11ReflectVal.monoR_nil_right, pow_zero, pow_one, one_mul, mul_one, alignedSquareFBar810]
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
  simp only [Max11ReflectVal.polyR_cons, Max11ReflectVal.monoR_cons, Max11ReflectVal.polyR_nil_left, Max11ReflectVal.polyR_nil_right, Max11ReflectVal.monoR_nil_left, Max11ReflectVal.monoR_nil_right, pow_zero, pow_one, one_mul, mul_one, alignedSquareGBar810]
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
  simp only [Max11ReflectVal.polyR_cons, Max11ReflectVal.monoR_cons, Max11ReflectVal.polyR_nil_left, Max11ReflectVal.polyR_nil_right, Max11ReflectVal.monoR_nil_left, Max11ReflectVal.monoR_nil_right, pow_zero, pow_one, one_mul, mul_one, alignedSquarePBar810]
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
  simp only [Max11ReflectVal.polyR_cons, Max11ReflectVal.monoR_cons, Max11ReflectVal.polyR_nil_left, Max11ReflectVal.polyR_nil_right, Max11ReflectVal.monoR_nil_left, Max11ReflectVal.monoR_nil_right, pow_zero, pow_one, one_mul, mul_one, alignedSquareQBar810]
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
  simp only [Max11ReflectVal.polyR_cons, Max11ReflectVal.monoR_cons, Max11ReflectVal.polyR_nil_left, Max11ReflectVal.polyR_nil_right, Max11ReflectVal.monoR_nil_left, Max11ReflectVal.monoR_nil_right, pow_zero, pow_one, one_mul, mul_one, alignedSquareRBar810]
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
  simp only [Max11ReflectVal.polyR_cons, Max11ReflectVal.monoR_cons, Max11ReflectVal.polyR_nil_left, Max11ReflectVal.polyR_nil_right, Max11ReflectVal.monoR_nil_left, Max11ReflectVal.monoR_nil_right, pow_zero, pow_one, one_mul, mul_one, alignedSquareSBar810]
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
  simp only [Max11ReflectVal.polyR_cons, Max11ReflectVal.monoR_cons, Max11ReflectVal.polyR_nil_left, Max11ReflectVal.polyR_nil_right, Max11ReflectVal.monoR_nil_left, Max11ReflectVal.monoR_nil_right, pow_zero, pow_one, one_mul, mul_one, alignedSquareTBar810]
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
  simp only [Max11ReflectVal.polyR_cons, Max11ReflectVal.monoR_cons, Max11ReflectVal.polyR_nil_left, Max11ReflectVal.polyR_nil_right, Max11ReflectVal.monoR_nil_left, Max11ReflectVal.monoR_nil_right, pow_zero, pow_one, one_mul, mul_one, alignedSquareUBar810]
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
  simp only [Max11ReflectVal.polyR_cons, Max11ReflectVal.monoR_cons, Max11ReflectVal.polyR_nil_left, Max11ReflectVal.polyR_nil_right, Max11ReflectVal.monoR_nil_left, Max11ReflectVal.monoR_nil_right, pow_zero, pow_one, one_mul, mul_one, alignedSquareVBar810]
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
  simp only [Max11ReflectVal.polyR_cons, Max11ReflectVal.monoR_cons, Max11ReflectVal.polyR_nil_left, Max11ReflectVal.polyR_nil_right, Max11ReflectVal.monoR_nil_left, Max11ReflectVal.monoR_nil_right, pow_zero, pow_one, one_mul, mul_one, alignedSquareWBar810]
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
  simp only [Max11ReflectVal.polyR_cons, Max11ReflectVal.monoR_cons, Max11ReflectVal.polyR_nil_left, Max11ReflectVal.polyR_nil_right, Max11ReflectVal.monoR_nil_left, Max11ReflectVal.monoR_nil_right, pow_zero, pow_one, one_mul, mul_one, degreeZeroClearedCompact810, alignedSquareCompactBlock0_810, alignedSquareCompactBlock1_810, alignedSquareCompactBlock2_810, alignedSquareCompactBlock3_810, alignedSquareCompactBlock4_810, alignedSquareCompactBlock5_810, alignedSquareCompactBlock6_810, alignedSquareCompactBlock7_810, alignedSquareCompactBlock8_810, alignedSquareCompactBlock9_810, alignedSquareCompactBlock10_810, alignedSquareCompactBlock11_810, alignedSquareCompactBlock12_810, alignedSquareCompactBlock13_810, alignedSquareCompactBlock14_810, alignedSquareCompactBlock15_810, alignedSquareCompactBlock16_810, alignedSquareCompactBlock17_810, alignedSquareCompactBlock18_810, alignedSquareCompactBlock19_810, alignedSquareCompactBlock20_810, alignedSquareCompactBlock21_810, alignedSquareCompactBlock22_810, alignedSquareCompactBlock23_810]
  ring

#print axioms alignedSquareClearedCompact810_blockSum

end AlignedSquareCompactBlocks810

end Max11DegreeRoutes
