import Grok610AlignedSquareTowerOrders69to75Scratch
import Grok610AlignedSquareM1M2Scratch
import Grok610RemainingAlignedFacesScratch

/-! # CLOSED. Source-facing closure of the `(6,10)` scale-two aligned-square chamber

Untracked working note.  No tracked file was edited.

`Grok610AlignedSquareTowerOrders69to75Scratch` exhausted the MixedPair
jet through the native ceiling `75` and recorded
`alignedSquareFace610_order75Grandchildren : False` from hypotheses
`hclear : algebraMap jet = h0^21 * rho`, `hderiv : rho' = C j / h0`,
`hj : j ≠ 0`, with `h0` linear and a root `a`.  That packet is not yet
the chamber: the source-primitive identity identifying the MixedPair
jet of `normalized610ScaleTwo_alignedSquare_m1m2Reduction` with a
clearing of `alignedSquarePeeledPrimitive610` was missing.

This file supplies that identity and instantiates `hclear`/`hderiv` from
a literal source.

* The wrapper derivative
  `alignedSquarePrimitive610_deriv_eq_simplePole_of_source` is the analog
  of `degreeZeroPrimitive610_ratFuncDeriv_eq_simplePole` used by
  `degreeZeroFace610_linearRoot`.  AffineBracket divides by exactly one
  power of `h`, and `N = 0` makes `L` a field constant, so the ordinary
  derivative is the simple pole `C j / h0`, not the zero derivative that
  vacated the `(8,10)` Pi cancel-and-expose
  (`Grok810PiChamberClosureScratch`).
* CAS job `20260902T091644Z-610-aligned-square-chamber-identity-60795`
  (`derive_610_aligned_square_chamber_identity.py`): the MixedPair compact
  equals `h^54 * jet` identically, and on a specialised MixedPair source
  (`w1=1`, `b8=13`, remaining letters numeric) the primitive is not a
  constant and its ordinary `h`-derivative is not `0`.  Combined with the
  wrapper lemma the pole is genuine.
* The identity `jet / h^21 = 58498535041007616 * peeled` is the analog of
  `degreeZeroPostCollapseJetQuotient610_div_eq_clearedPrimitive`.  The
  tower then closes the chamber on the raw M1M2 hypotheses.

**CLOSED:** `alignedSquareFace610_squareChamber`.
**CLOSED:** `normalized610ScaleTwo_alignedSquare_false`.
**CLOSED:** `planeKeller610AlignedSquareExclusion_closed`.

There is no unused compact-numerator order after `75`.  The aligned
nonsquare face is not opened.

No total-degree or twice-prime theorem is used.  No `sorry`, no new
axioms, no finite-root shortcut, no closure overclaim.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option maxHeartbeats 800000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## MixedPair bars not already in the source wrapper -/

section AlignedSquareMixedBars610

variable {F : Type*} [Field F] [CharZero F]

/-- MixedPair numerator of `324 h^{25} D`. -/
def alignedSquareMixedDBar610 (h w1 e1 e3 a2 a1 : F) : F :=
  (324 : F) * a1 * h ^ 24 - (108 : F) * a2 * h ^ 22 * w1 -
    (2 : F) * e1 * h ^ 21 * w1 ^ 3 + e3 * h ^ 22 * w1 ^ 2

/-- MixedPair numerator of `46656 h^{30} E`. -/
def alignedSquareMixedEBar610 (h w1 e1 e3 a2 a1 a0 : F) : F :=
  (46656 : F) * a0 * h ^ 30 - (7776 : F) * a1 * h ^ 28 * w1 +
    (1296 : F) * a2 * h ^ 26 * w1 ^ 2 + (12 : F) * e1 * h ^ 25 * w1 ^ 4 -
    (8 : F) * e3 * h ^ 26 * w1 ^ 3 - h ^ 24 * w1 ^ 6

/-- MixedPair numerator of `9 h^{15} Q` on `λ = 0`. -/
def alignedSquareMixedQBar610 (h w1 b8 b7 : F) : F :=
  (9 : F) * b7 * h ^ 8 - (12 : F) * b8 * h ^ 6 * w1 +
    (10 : F) * h ^ 12 * w1 ^ 3

/-- MixedPair numerator of `432 h^{20} R` on `λ = 0`. -/
def alignedSquareMixedRBar610 (h w1 b8 b7 b6 : F) : F :=
  (432 : F) * b6 * h ^ 14 - (504 : F) * b7 * h ^ 12 * w1 +
    (336 : F) * b8 * h ^ 10 * w1 ^ 2 - (210 : F) * h ^ 16 * w1 ^ 4

/-- MixedPair numerator of `216 h^{25} S` on `λ = 0`. -/
def alignedSquareMixedSBar610 (h w1 b8 b7 b6 b5 : F) : F :=
  (216 : F) * b5 * h ^ 20 - (216 : F) * b6 * h ^ 18 * w1 +
    (126 : F) * b7 * h ^ 16 * w1 ^ 2 - (56 : F) * b8 * h ^ 14 * w1 ^ 3 +
    (28 : F) * h ^ 20 * w1 ^ 5

/-- MixedPair numerator of `7776 h^{30} T` on `λ = 0`. -/
def alignedSquareMixedTBar610 (h w1 b8 b7 b6 b5 b4 : F) : F :=
  (7776 : F) * b4 * h ^ 26 - (6480 : F) * b5 * h ^ 24 * w1 +
    (3240 : F) * b6 * h ^ 22 * w1 ^ 2 - (1260 : F) * b7 * h ^ 20 * w1 ^ 3 +
    (420 : F) * b8 * h ^ 18 * w1 ^ 4 - (175 : F) * h ^ 24 * w1 ^ 6

/-- MixedPair numerator of `11664 h^{35} U` on `λ = 0`. -/
def alignedSquareMixedUBar610 (h w1 b8 b7 b6 b5 b4 b3 : F) : F :=
  (11664 : F) * b3 * h ^ 32 - (7776 : F) * b4 * h ^ 30 * w1 +
    (3240 : F) * b5 * h ^ 28 * w1 ^ 2 - (1080 : F) * b6 * h ^ 26 * w1 ^ 3 +
    (315 : F) * b7 * h ^ 24 * w1 ^ 4 - (84 : F) * b8 * h ^ 22 * w1 ^ 5 +
    (30 : F) * h ^ 28 * w1 ^ 7

/-- MixedPair numerator of `186624 h^{40} V` on `λ = 0`. -/
def alignedSquareMixedVBar610 (h w1 b8 b7 b6 b5 b4 b3 b2 : F) : F :=
  (186624 : F) * b2 * h ^ 38 - (93312 : F) * b3 * h ^ 36 * w1 +
    (31104 : F) * b4 * h ^ 34 * w1 ^ 2 - (8640 : F) * b5 * h ^ 32 * w1 ^ 3 +
    (2160 : F) * b6 * h ^ 30 * w1 ^ 4 - (504 : F) * b7 * h ^ 28 * w1 ^ 5 +
    (112 : F) * b8 * h ^ 26 * w1 ^ 6 - (35 : F) * h ^ 32 * w1 ^ 8

/-- MixedPair numerator of `5038848 h^{45} W` on `λ = 0`. -/
def alignedSquareMixedWBar610 (h w1 b8 b7 b6 b5 b4 b3 b2 b1 : F) : F :=
  (5038848 : F) * b1 * h ^ 44 - (1679616 : F) * b2 * h ^ 42 * w1 +
    (419904 : F) * b3 * h ^ 40 * w1 ^ 2 - (93312 : F) * b4 * h ^ 38 * w1 ^ 3 +
    (19440 : F) * b5 * h ^ 36 * w1 ^ 4 - (3888 : F) * b6 * h ^ 34 * w1 ^ 5 +
    (756 : F) * b7 * h ^ 32 * w1 ^ 6 - (144 : F) * b8 * h ^ 30 * w1 ^ 7 +
    (40 : F) * h ^ 36 * w1 ^ 9

theorem alignedSquareCBar610_eq_generic
    (h w1 f2 e1 e3 a3 a2 : F)
    (he1 : (3 : F) * f2 - w1 ^ 2 = h * e1)
    (ha3 : (27 : F) * a3 = w1 ^ 3 + h ^ 2 * e3) :
    (144 : F) * a2 * h ^ 18 - (72 : F) * a3 * (h ^ 4 * w1) * h ^ 12 +
        (24 : F) * (h ^ 2 * f2) * (h ^ 4 * w1) ^ 2 * h ^ 6 -
        (5 : F) * (h ^ 4 * w1) ^ 4 =
      alignedSquareCBar610 h w1 e1 e3 a2 := by
  simp only [alignedSquareCBar610]
  have h27 : (27 : F) ≠ 0 := by norm_num
  have h3 : (3 : F) ≠ 0 := by norm_num
  have ha3' : a3 = (w1 ^ 3 + h ^ 2 * e3) / 27 := by
    field_simp [h27]
    linear_combination ha3
  have hf2 : f2 = (w1 ^ 2 + h * e1) / 3 := by
    field_simp [h3]
    linear_combination he1
  rw [ha3', hf2]
  field_simp [h27, h3]
  ring

theorem alignedSquareMixedDBar610_eq_generic
    (h w1 f2 e1 e3 a3 a2 a1 : F)
    (he1 : (3 : F) * f2 - w1 ^ 2 = h * e1)
    (ha3 : (27 : F) * a3 = w1 ^ 3 + h ^ 2 * e3) :
    (324 : F) * a1 * h ^ 24 - (108 : F) * a2 * (h ^ 4 * w1) * h ^ 18 +
        (27 : F) * a3 * (h ^ 4 * w1) ^ 2 * h ^ 12 -
        (6 : F) * (h ^ 2 * f2) * (h ^ 4 * w1) ^ 3 * h ^ 6 +
        (h ^ 4 * w1) ^ 5 =
      alignedSquareMixedDBar610 h w1 e1 e3 a2 a1 := by
  simp only [alignedSquareMixedDBar610]
  have h27 : (27 : F) ≠ 0 := by norm_num
  have h3 : (3 : F) ≠ 0 := by norm_num
  have ha3' : a3 = (w1 ^ 3 + h ^ 2 * e3) / 27 := by
    field_simp [h27]
    linear_combination ha3
  have hf2 : f2 = (w1 ^ 2 + h * e1) / 3 := by
    field_simp [h3]
    linear_combination he1
  rw [ha3', hf2]
  field_simp [h27, h3]
  ring

theorem alignedSquareMixedEBar610_eq_generic
    (h w1 f2 e1 e3 a3 a2 a1 a0 : F)
    (he1 : (3 : F) * f2 - w1 ^ 2 = h * e1)
    (ha3 : (27 : F) * a3 = w1 ^ 3 + h ^ 2 * e3) :
    (46656 : F) * a0 * h ^ 30 - (7776 : F) * a1 * (h ^ 4 * w1) * h ^ 24 +
        (1296 : F) * a2 * (h ^ 4 * w1) ^ 2 * h ^ 18 -
        (216 : F) * a3 * (h ^ 4 * w1) ^ 3 * h ^ 12 +
        (36 : F) * (h ^ 2 * f2) * (h ^ 4 * w1) ^ 4 * h ^ 6 -
        (5 : F) * (h ^ 4 * w1) ^ 6 =
      alignedSquareMixedEBar610 h w1 e1 e3 a2 a1 a0 := by
  simp only [alignedSquareMixedEBar610]
  have h27 : (27 : F) ≠ 0 := by norm_num
  have h3 : (3 : F) ≠ 0 := by norm_num
  have ha3' : a3 = (w1 ^ 3 + h ^ 2 * e3) / 27 := by
    field_simp [h27]
    linear_combination ha3
  have hf2 : f2 = (w1 ^ 2 + h * e1) / 3 := by
    field_simp [h3]
    linear_combination he1
  rw [ha3', hf2]
  field_simp [h27, h3]
  ring

theorem alignedSquareMixedQBar610_eq_generic (h w1 b8 b7 : F) :
    (10 : F) * (h ^ 4 * w1) ^ 3 - (12 : F) * (h ^ 4 * w1) * b8 * h ^ 2 +
        (9 : F) * b7 * h ^ 8 =
      alignedSquareMixedQBar610 h w1 b8 b7 := by
  simp only [alignedSquareMixedQBar610]
  ring

theorem alignedSquareMixedRBar610_eq_generic (h w1 b8 b7 b6 : F) :
    -((210 : F) * (h ^ 4 * w1) ^ 4) + (336 : F) * (h ^ 4 * w1) ^ 2 * b8 * h ^ 2 -
        (504 : F) * (h ^ 4 * w1) * b7 * h ^ 8 + (432 : F) * b6 * h ^ 14 =
      alignedSquareMixedRBar610 h w1 b8 b7 b6 := by
  simp only [alignedSquareMixedRBar610]
  ring

theorem alignedSquareMixedSBar610_eq_generic (h w1 b8 b7 b6 b5 : F) :
    (28 : F) * (h ^ 4 * w1) ^ 5 - (56 : F) * (h ^ 4 * w1) ^ 3 * b8 * h ^ 2 +
        (126 : F) * (h ^ 4 * w1) ^ 2 * b7 * h ^ 8 -
        (216 : F) * (h ^ 4 * w1) * b6 * h ^ 14 + (216 : F) * b5 * h ^ 20 =
      alignedSquareMixedSBar610 h w1 b8 b7 b6 b5 := by
  simp only [alignedSquareMixedSBar610]
  ring

theorem alignedSquareMixedTBar610_eq_generic (h w1 b8 b7 b6 b5 b4 : F) :
    -((175 : F) * (h ^ 4 * w1) ^ 6) + (420 : F) * (h ^ 4 * w1) ^ 4 * b8 * h ^ 2 -
        (1260 : F) * (h ^ 4 * w1) ^ 3 * b7 * h ^ 8 +
        (3240 : F) * (h ^ 4 * w1) ^ 2 * b6 * h ^ 14 -
        (6480 : F) * (h ^ 4 * w1) * b5 * h ^ 20 + (7776 : F) * b4 * h ^ 26 =
      alignedSquareMixedTBar610 h w1 b8 b7 b6 b5 b4 := by
  simp only [alignedSquareMixedTBar610]
  ring

theorem alignedSquareMixedUBar610_eq_generic
    (h w1 b8 b7 b6 b5 b4 b3 : F) :
    (30 : F) * (h ^ 4 * w1) ^ 7 - (84 : F) * (h ^ 4 * w1) ^ 5 * b8 * h ^ 2 +
        (315 : F) * (h ^ 4 * w1) ^ 4 * b7 * h ^ 8 -
        (1080 : F) * (h ^ 4 * w1) ^ 3 * b6 * h ^ 14 +
        (3240 : F) * (h ^ 4 * w1) ^ 2 * b5 * h ^ 20 -
        (7776 : F) * (h ^ 4 * w1) * b4 * h ^ 26 + (11664 : F) * b3 * h ^ 32 =
      alignedSquareMixedUBar610 h w1 b8 b7 b6 b5 b4 b3 := by
  simp only [alignedSquareMixedUBar610]
  ring

theorem alignedSquareMixedVBar610_eq_generic
    (h w1 b8 b7 b6 b5 b4 b3 b2 : F) :
    -((35 : F) * (h ^ 4 * w1) ^ 8) + (112 : F) * (h ^ 4 * w1) ^ 6 * b8 * h ^ 2 -
        (504 : F) * (h ^ 4 * w1) ^ 5 * b7 * h ^ 8 +
        (2160 : F) * (h ^ 4 * w1) ^ 4 * b6 * h ^ 14 -
        (8640 : F) * (h ^ 4 * w1) ^ 3 * b5 * h ^ 20 +
        (31104 : F) * (h ^ 4 * w1) ^ 2 * b4 * h ^ 26 -
        (93312 : F) * (h ^ 4 * w1) * b3 * h ^ 32 + (186624 : F) * b2 * h ^ 38 =
      alignedSquareMixedVBar610 h w1 b8 b7 b6 b5 b4 b3 b2 := by
  simp only [alignedSquareMixedVBar610]
  ring

theorem alignedSquareMixedWBar610_eq_generic
    (h w1 b8 b7 b6 b5 b4 b3 b2 b1 : F) :
    (40 : F) * (h ^ 4 * w1) ^ 9 - (144 : F) * (h ^ 4 * w1) ^ 7 * b8 * h ^ 2 +
        (756 : F) * (h ^ 4 * w1) ^ 6 * b7 * h ^ 8 -
        (3888 : F) * (h ^ 4 * w1) ^ 5 * b6 * h ^ 14 +
        (19440 : F) * (h ^ 4 * w1) ^ 4 * b5 * h ^ 20 -
        (93312 : F) * (h ^ 4 * w1) ^ 3 * b4 * h ^ 26 +
        (419904 : F) * (h ^ 4 * w1) ^ 2 * b3 * h ^ 32 -
        (1679616 : F) * (h ^ 4 * w1) * b2 * h ^ 38 +
        (5038848 : F) * b1 * h ^ 44 =
      alignedSquareMixedWBar610 h w1 b8 b7 b6 b5 b4 b3 b2 b1 := by
  simp only [alignedSquareMixedWBar610]
  ring

end AlignedSquareMixedBars610

#print axioms alignedSquareCBar610_eq_generic
#print axioms alignedSquareMixedDBar610_eq_generic
#print axioms alignedSquareMixedWBar610_eq_generic

/-! ## Compact = `h^{54}` · jet after the MixedPair peel -/

section AlignedSquareCompactFactor610

variable {F : Type*} [Field F] [CharZero F]

set_option maxHeartbeats 800000000 in
/-- Exact order-`54` factorization of the MixedPair compact numerator.
CAS: `derive_610_aligned_square_chamber_identity.py` (job
`20260902T091644Z-610-aligned-square-chamber-identity-60795`). -/
theorem alignedSquareClearedCompact610_mixedPair_factored
    (h w1 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F) :
    degreeZeroClearedCompact610
        (alignedSquareABar610 h w1 e1)
        (alignedSquareBBar610 h w1 e1 e3)
        (alignedSquareCBar610 h w1 e1 e3 a2)
        (alignedSquareMixedDBar610 h w1 e1 e3 a2 a1)
        (alignedSquareMixedEBar610 h w1 e1 e3 a2 a1 a0)
        (alignedSquarePBar610 h w1 b8)
        (alignedSquareMixedQBar610 h w1 b8 b7)
        (alignedSquareMixedRBar610 h w1 b8 b7 b6)
        (alignedSquareMixedSBar610 h w1 b8 b7 b6 b5)
        (alignedSquareMixedTBar610 h w1 b8 b7 b6 b5 b4)
        (alignedSquareMixedUBar610 h w1 b8 b7 b6 b5 b4 b3)
        (alignedSquareMixedVBar610 h w1 b8 b7 b6 b5 b4 b3 b2)
        (alignedSquareMixedWBar610 h w1 b8 b7 b6 b5 b4 b3 b2 b1) 0 =
      h ^ 54 *
        alignedSquareJetQuotient610 h w1 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4
          b3 b2 b1 := by
  simp only [degreeZeroClearedCompact610, alignedSquareABar610,
    alignedSquareBBar610, alignedSquareCBar610, alignedSquareMixedDBar610,
    alignedSquareMixedEBar610, alignedSquarePBar610,
    alignedSquareMixedQBar610, alignedSquareMixedRBar610,
    alignedSquareMixedSBar610, alignedSquareMixedTBar610,
    alignedSquareMixedUBar610, alignedSquareMixedVBar610,
    alignedSquareMixedWBar610, alignedSquareJetQuotient610]
  have h3 : (3 : F) ≠ 0 := by norm_num
  field_simp [h3]
  ring

end AlignedSquareCompactFactor610

#print axioms alignedSquareClearedCompact610_mixedPair_factored

/-! ## Source-primitive identity: `jet / h^{21} = scale · ρ` -/

section AlignedSquareSourcePrimitiveIdentity610

variable {F : Type*} [Field F] [CharZero F]

/-- The aligned `λ = 0` ninth-power identity on the MixedPair `b₉`. -/
theorem alignedSquareMixedPair_ninthPower610
    (h w1 : F) :
    (5 : F) * (h ^ 4 * w1) * h ^ 4 -
        (3 : F) * ((5 : F) / 3 * (h ^ 4 * w1) * h ^ 4) = 0 := by
  have h3 : (3 : F) ≠ 0 := by norm_num
  field_simp [h3]
  ring

set_option maxHeartbeats 800000000 in
/-- Depressed MixedPair coordinates are the MixedPair bars over the
native denominators. -/
theorem alignedSquarePeeledPrimitive610_eq_mixedBars
    (h w1 f2 e1 e3 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F)
    (hh : h ≠ 0)
    (he1 : (3 : F) * f2 - w1 ^ 2 = h * e1)
    (ha3 : (27 : F) * a3 = w1 ^ 3 + h ^ 2 * e3) :
    alignedSquarePeeledPrimitive610 h w1 f2 a3 a2 a1 a0 b8 b7 b6 b5 b4
        b3 b2 b1 =
      degreeZeroPrimitive610 0
        (alignedSquareABar610 h w1 e1 / ((12 : F) * h ^ 10))
        (alignedSquareBBar610 h w1 e1 e3 / ((54 : F) * h ^ 15))
        (alignedSquareCBar610 h w1 e1 e3 a2 / ((144 : F) * h ^ 20))
        (alignedSquareMixedDBar610 h w1 e1 e3 a2 a1 / ((324 : F) * h ^ 25))
        (alignedSquareMixedEBar610 h w1 e1 e3 a2 a1 a0 /
          ((46656 : F) * h ^ 30))
        (alignedSquarePBar610 h w1 b8 / ((4 : F) * h ^ 10))
        (alignedSquareMixedQBar610 h w1 b8 b7 / ((9 : F) * h ^ 15))
        (alignedSquareMixedRBar610 h w1 b8 b7 b6 / ((432 : F) * h ^ 20))
        (alignedSquareMixedSBar610 h w1 b8 b7 b6 b5 / ((216 : F) * h ^ 25))
        (alignedSquareMixedTBar610 h w1 b8 b7 b6 b5 b4 /
          ((7776 : F) * h ^ 30))
        (alignedSquareMixedUBar610 h w1 b8 b7 b6 b5 b4 b3 /
          ((11664 : F) * h ^ 35))
        (alignedSquareMixedVBar610 h w1 b8 b7 b6 b5 b4 b3 b2 /
          ((186624 : F) * h ^ 40))
        (alignedSquareMixedWBar610 h w1 b8 b7 b6 b5 b4 b3 b2 b1 /
          ((5038848 : F) * h ^ 45)) 0 := by
  let a5 : F := h ^ 4 * w1
  let a4 : F := h ^ 2 * f2
  let b9 : F := (5 : F) / 3 * (h ^ 4 * w1) * h ^ 4
  have hN : (5 : F) * a5 * h ^ 4 - (3 : F) * b9 = 0 := by
    simpa [a5, b9] using alignedSquareMixedPair_ninthPower610 h w1
  have hL := alignedSquareL_eq_zero610 h a5 b9 hh (by simpa [a5, b9] using hN)
  have hA := depressedA610_eq_cleared h a5 a4 hh
  have hB := depressedB610_eq_cleared h a5 a4 a3 hh
  have hC := depressedC610_eq_cleared h a5 a4 a3 a2 hh
  have hD := depressedD610_eq_cleared h a5 a4 a3 a2 a1 hh
  have hE := depressedE610_eq_cleared h a5 a4 a3 a2 a1 a0 hh
  have hP :=
    depressedP610_eq_cleared_ninthPower h a5 b9 b8 0 hh
      (by simpa [a5, b9] using hN)
  have hQ :=
    depressedQ610_eq_cleared h a5 b9 b8 b7 0 hh
      (by simpa [a5, b9] using hN)
  have hR :=
    depressedR610_eq_cleared h a5 b9 b8 b7 b6 0 hh
      (by simpa [a5, b9] using hN)
  have hS :=
    depressedS610_eq_cleared h a5 b9 b8 b7 b6 b5 0 hh
      (by simpa [a5, b9] using hN)
  have hT :=
    depressedT610_eq_cleared h a5 b9 b8 b7 b6 b5 b4 0 hh
      (by simpa [a5, b9] using hN)
  have hU :=
    depressedU610_eq_cleared h a5 b9 b8 b7 b6 b5 b4 b3 0 hh
      (by simpa [a5, b9] using hN)
  have hV :=
    depressedV610_eq_cleared h a5 b9 b8 b7 b6 b5 b4 b3 b2 0 hh
      (by simpa [a5, b9] using hN)
  have hW :=
    depressedW610_eq_cleared h a5 b9 b8 b7 b6 b5 b4 b3 b2 b1 0 hh
      (by simpa [a5, b9] using hN)
  have hAbar := alignedSquareABar610_eq_generic h w1 f2 e1 he1
  have hBbar := alignedSquareBBar610_eq_generic h w1 f2 e1 e3 a3 he1 ha3
  have hCbar := alignedSquareCBar610_eq_generic h w1 f2 e1 e3 a3 a2 he1 ha3
  have hDbar :=
    alignedSquareMixedDBar610_eq_generic h w1 f2 e1 e3 a3 a2 a1 he1 ha3
  have hEbar :=
    alignedSquareMixedEBar610_eq_generic h w1 f2 e1 e3 a3 a2 a1 a0 he1 ha3
  have hPbar := alignedSquarePBar610_eq_generic h w1 b8
  have hQbar := alignedSquareMixedQBar610_eq_generic h w1 b8 b7
  have hRbar := alignedSquareMixedRBar610_eq_generic h w1 b8 b7 b6
  have hSbar := alignedSquareMixedSBar610_eq_generic h w1 b8 b7 b6 b5
  have hTbar := alignedSquareMixedTBar610_eq_generic h w1 b8 b7 b6 b5 b4
  have hUbar :=
    alignedSquareMixedUBar610_eq_generic h w1 b8 b7 b6 b5 b4 b3
  have hVbar :=
    alignedSquareMixedVBar610_eq_generic h w1 b8 b7 b6 b5 b4 b3 b2
  have hWbar :=
    alignedSquareMixedWBar610_eq_generic h w1 b8 b7 b6 b5 b4 b3 b2 b1
  dsimp only [alignedSquarePeeledPrimitive610, alignedSquareSourcePrimitive610]
  rw [hL, hA, hB, hC, hD, hE, hP, hQ, hR, hS, hT, hU, hV, hW]
  simp [a5, a4, b9, mul_zero, zero_mul, add_zero, sub_zero, zero_add]
  rw [hAbar, hBbar, hCbar, hDbar, hEbar, hPbar, hQbar, hRbar, hSbar, hTbar,
    hUbar, hVbar, hWbar]

set_option maxHeartbeats 800000000 in
/-- Exact algebraic bridge from the MixedPair jet to the source-level
peeled primitive. -/
theorem alignedSquareJetQuotient610_div_eq_clearedPrimitive
    (h w1 f2 e1 e3 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F)
    (hh : h ≠ 0)
    (he1 : (3 : F) * f2 - w1 ^ 2 = h * e1)
    (ha3 : (27 : F) * a3 = w1 ^ 3 + h ^ 2 * e3) :
    alignedSquareJetQuotient610 h w1 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3
        b2 b1 / h ^ 21 =
      (58498535041007616 : F) *
        alignedSquarePeeledPrimitive610 h w1 f2 a3 a2 a1 a0 b8 b7 b6 b5
          b4 b3 b2 b1 := by
  let Abar := alignedSquareABar610 h w1 e1
  let Bbar := alignedSquareBBar610 h w1 e1 e3
  let Cbar := alignedSquareCBar610 h w1 e1 e3 a2
  let Dbar := alignedSquareMixedDBar610 h w1 e1 e3 a2 a1
  let Ebar := alignedSquareMixedEBar610 h w1 e1 e3 a2 a1 a0
  let Pbar := alignedSquarePBar610 h w1 b8
  let Qbar := alignedSquareMixedQBar610 h w1 b8 b7
  let Rbar := alignedSquareMixedRBar610 h w1 b8 b7 b6
  let Sbar := alignedSquareMixedSBar610 h w1 b8 b7 b6 b5
  let Tbar := alignedSquareMixedTBar610 h w1 b8 b7 b6 b5 b4
  let Ubar := alignedSquareMixedUBar610 h w1 b8 b7 b6 b5 b4 b3
  let Vbar := alignedSquareMixedVBar610 h w1 b8 b7 b6 b5 b4 b3 b2
  let Wbar := alignedSquareMixedWBar610 h w1 b8 b7 b6 b5 b4 b3 b2 b1
  have hfactor :=
    alignedSquareClearedCompact610_mixedPair_factored h w1 e1 e3 a2 a1 a0
      b8 b7 b6 b5 b4 b3 b2 b1
  have hcompact :=
    degreeZeroPrimitive610_eq_clearedCompact Abar Bbar Cbar Dbar Ebar Pbar
      Qbar Rbar Sbar Tbar Ubar Vbar Wbar 0
  have hpeel :=
    alignedSquarePeeledPrimitive610_eq_mixedBars h w1 f2 e1 e3 a3 a2 a1 a0
      b8 b7 b6 b5 b4 b3 b2 b1 hh he1 ha3
  have hscale :=
    degreeZeroPrimitive610_weightedScale h (0 : F)
      (Abar / ((12 : F) * h ^ 10)) (Bbar / ((54 : F) * h ^ 15))
      (Cbar / ((144 : F) * h ^ 20)) (Dbar / ((324 : F) * h ^ 25))
      (Ebar / ((46656 : F) * h ^ 30)) (Pbar / ((4 : F) * h ^ 10))
      (Qbar / ((9 : F) * h ^ 15)) (Rbar / ((432 : F) * h ^ 20))
      (Sbar / ((216 : F) * h ^ 25)) (Tbar / ((7776 : F) * h ^ 30))
      (Ubar / ((11664 : F) * h ^ 35)) (Vbar / ((186624 : F) * h ^ 40))
      (Wbar / ((5038848 : F) * h ^ 45)) (0 : F)
  have hL : h ^ 5 * (0 : F) = 0 := by ring
  have hX : h ^ 50 * (0 : F) = 0 := by ring
  have hA : h ^ 10 * (Abar / ((12 : F) * h ^ 10)) = Abar / 12 := by
    field_simp [hh]
  have hB : h ^ 15 * (Bbar / ((54 : F) * h ^ 15)) = Bbar / 54 := by
    field_simp [hh]
  have hC : h ^ 20 * (Cbar / ((144 : F) * h ^ 20)) = Cbar / 144 := by
    field_simp [hh]
  have hD : h ^ 25 * (Dbar / ((324 : F) * h ^ 25)) = Dbar / 324 := by
    field_simp [hh]
  have hE : h ^ 30 * (Ebar / ((46656 : F) * h ^ 30)) = Ebar / 46656 := by
    field_simp [hh]
  have hP : h ^ 10 * (Pbar / ((4 : F) * h ^ 10)) = Pbar / 4 := by
    field_simp [hh]
  have hQ : h ^ 15 * (Qbar / ((9 : F) * h ^ 15)) = Qbar / 9 := by
    field_simp [hh]
  have hR : h ^ 20 * (Rbar / ((432 : F) * h ^ 20)) = Rbar / 432 := by
    field_simp [hh]
  have hS : h ^ 25 * (Sbar / ((216 : F) * h ^ 25)) = Sbar / 216 := by
    field_simp [hh]
  have hT : h ^ 30 * (Tbar / ((7776 : F) * h ^ 30)) = Tbar / 7776 := by
    field_simp [hh]
  have hU : h ^ 35 * (Ubar / ((11664 : F) * h ^ 35)) = Ubar / 11664 := by
    field_simp [hh]
  have hV : h ^ 40 * (Vbar / ((186624 : F) * h ^ 40)) = Vbar / 186624 := by
    field_simp [hh]
  have hW : h ^ 45 * (Wbar / ((5038848 : F) * h ^ 45)) = Wbar / 5038848 := by
    field_simp [hh]
  have hscale' :
      degreeZeroPrimitive610 0 (Abar / 12) (Bbar / 54) (Cbar / 144)
          (Dbar / 324) (Ebar / 46656) (Pbar / 4) (Qbar / 9) (Rbar / 432)
          (Sbar / 216) (Tbar / 7776) (Ubar / 11664) (Vbar / 186624)
          (Wbar / 5038848) 0 =
        h ^ 75 *
          degreeZeroPrimitive610 0 (Abar / ((12 : F) * h ^ 10))
            (Bbar / ((54 : F) * h ^ 15)) (Cbar / ((144 : F) * h ^ 20))
            (Dbar / ((324 : F) * h ^ 25)) (Ebar / ((46656 : F) * h ^ 30))
            (Pbar / ((4 : F) * h ^ 10)) (Qbar / ((9 : F) * h ^ 15))
            (Rbar / ((432 : F) * h ^ 20)) (Sbar / ((216 : F) * h ^ 25))
            (Tbar / ((7776 : F) * h ^ 30)) (Ubar / ((11664 : F) * h ^ 35))
            (Vbar / ((186624 : F) * h ^ 40))
            (Wbar / ((5038848 : F) * h ^ 45)) 0 := by
    rw [hL, hA, hB, hC, hD, hE, hP, hQ, hR, hS, hT, hU, hV, hW, hX]
      at hscale
    exact hscale
  have hh21 : h ^ 21 ≠ 0 := pow_ne_zero 21 hh
  have hh75 : h ^ 75 ≠ 0 := pow_ne_zero 75 hh
  calc
    alignedSquareJetQuotient610 h w1 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3
          b2 b1 / h ^ 21 =
        (h ^ 54 *
            alignedSquareJetQuotient610 h w1 e1 e3 a2 a1 a0 b8 b7 b6 b5
              b4 b3 b2 b1) / h ^ 75 := by
      field_simp [hh]
    _ = degreeZeroClearedCompact610 Abar Bbar Cbar Dbar Ebar Pbar Qbar
          Rbar Sbar Tbar Ubar Vbar Wbar 0 / h ^ 75 := by
      rw [hfactor]
    _ = ((58498535041007616 : F) *
          degreeZeroPrimitive610 (-(0 : F) / 3) (Abar / 12) (Bbar / 54)
            (Cbar / 144) (Dbar / 324) (Ebar / 46656) (Pbar / 4)
            (Qbar / 9) (Rbar / 432) (Sbar / 216) (Tbar / 7776)
            (Ubar / 11664) (Vbar / 186624) (Wbar / 5038848) 0) / h ^ 75 := by
      rw [hcompact]
    _ = ((58498535041007616 : F) *
          degreeZeroPrimitive610 0 (Abar / 12) (Bbar / 54) (Cbar / 144)
            (Dbar / 324) (Ebar / 46656) (Pbar / 4) (Qbar / 9)
            (Rbar / 432) (Sbar / 216) (Tbar / 7776) (Ubar / 11664)
            (Vbar / 186624) (Wbar / 5038848) 0) / h ^ 75 := by
      simp only [neg_zero, zero_div]
    _ = ((58498535041007616 : F) * (h ^ 75 *
          degreeZeroPrimitive610 0 (Abar / ((12 : F) * h ^ 10))
            (Bbar / ((54 : F) * h ^ 15)) (Cbar / ((144 : F) * h ^ 20))
            (Dbar / ((324 : F) * h ^ 25)) (Ebar / ((46656 : F) * h ^ 30))
            (Pbar / ((4 : F) * h ^ 10)) (Qbar / ((9 : F) * h ^ 15))
            (Rbar / ((432 : F) * h ^ 20)) (Sbar / ((216 : F) * h ^ 25))
            (Tbar / ((7776 : F) * h ^ 30)) (Ubar / ((11664 : F) * h ^ 35))
            (Vbar / ((186624 : F) * h ^ 40))
            (Wbar / ((5038848 : F) * h ^ 45)) 0)) / h ^ 75 := by
      rw [hscale']
    _ = (58498535041007616 : F) *
        alignedSquarePeeledPrimitive610 h w1 f2 a3 a2 a1 a0 b8 b7 b6 b5
          b4 b3 b2 b1 := by
      rw [← hpeel]
      field_simp [hh75]

end AlignedSquareSourcePrimitiveIdentity610

#print axioms alignedSquarePeeledPrimitive610_eq_mixedBars
#print axioms alignedSquareJetQuotient610_div_eq_clearedPrimitive

/-! ## Polynomial jet maps, scaled derivative, and the source False -/

section AlignedSquareJetMap610

variable {R S : Type*} [CommRing R] [CommRing S]

set_option maxHeartbeats 800000000 in
theorem alignedSquareJetQuotient610_map
    (f : R →+* S)
    (h w1 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) :
    f (alignedSquareJetQuotient610 h w1 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4
          b3 b2 b1) =
      alignedSquareJetQuotient610 (f h) (f w1) (f e1) (f e3) (f a2)
        (f a1) (f a0) (f b8) (f b7) (f b6) (f b5) (f b4) (f b3) (f b2)
        (f b1) := by
  simp only [alignedSquareJetQuotient610, map_add, map_sub, map_neg,
    map_mul, map_pow, map_ofNat]

end AlignedSquareJetMap610

#print axioms alignedSquareJetQuotient610_map

section AlignedSquareSourceFalse610

variable {k : Type*} [Field k] [CharZero k]

/-- Scaled wrapper derivative: `deriv (scale · ρ) = C (scale · j) / h0`. -/
theorem alignedSquarePrimitive610_scaledDeriv_eq_simplePole_of_source
    (p q : k[X][X]) (H h0 : k[X]) (j : k)
    (w1 f2 e1 e2 e3 : k[X])
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9 = 0)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hw : p.coeff 5 = h0 ^ 4 * w1)
    (hp4 : p.coeff 4 = h0 ^ 2 * f2)
    (he1 : (3 : k[X]) * f2 - w1 ^ 2 = h0 * e1)
    (he2 : (27 : k[X]) * p.coeff 3 - w1 ^ 3 = h0 * e2)
    (he3 : e2 = h0 * e3) :
    Differential.deriv
        ((58498535041007616 : RatFunc k) *
          alignedSquarePeeledPrimitive610
            (algebraMap k[X] (RatFunc k) h0)
            (algebraMap k[X] (RatFunc k) w1)
            (algebraMap k[X] (RatFunc k) f2)
            (algebraMap k[X] (RatFunc k) (p.coeff 3))
            (algebraMap k[X] (RatFunc k) (p.coeff 2))
            (algebraMap k[X] (RatFunc k) (p.coeff 1))
            (algebraMap k[X] (RatFunc k) (p.coeff 0))
            (algebraMap k[X] (RatFunc k) (q.coeff 8))
            (algebraMap k[X] (RatFunc k) (q.coeff 7))
            (algebraMap k[X] (RatFunc k) (q.coeff 6))
            (algebraMap k[X] (RatFunc k) (q.coeff 5))
            (algebraMap k[X] (RatFunc k) (q.coeff 4))
            (algebraMap k[X] (RatFunc k) (q.coeff 3))
            (algebraMap k[X] (RatFunc k) (q.coeff 2))
            (algebraMap k[X] (RatFunc k) (q.coeff 1))) =
      RatFunc.C (58498535041007616 * j) /
        algebraMap k[X] (RatFunc k) h0 := by
  let hRF : RatFunc k := algebraMap k[X] (RatFunc k) h0
  let prim : RatFunc k :=
    alignedSquarePeeledPrimitive610 hRF
      (algebraMap k[X] (RatFunc k) w1)
      (algebraMap k[X] (RatFunc k) f2)
      (algebraMap k[X] (RatFunc k) (p.coeff 3))
      (algebraMap k[X] (RatFunc k) (p.coeff 2))
      (algebraMap k[X] (RatFunc k) (p.coeff 1))
      (algebraMap k[X] (RatFunc k) (p.coeff 0))
      (algebraMap k[X] (RatFunc k) (q.coeff 8))
      (algebraMap k[X] (RatFunc k) (q.coeff 7))
      (algebraMap k[X] (RatFunc k) (q.coeff 6))
      (algebraMap k[X] (RatFunc k) (q.coeff 5))
      (algebraMap k[X] (RatFunc k) (q.coeff 4))
      (algebraMap k[X] (RatFunc k) (q.coeff 3))
      (algebraMap k[X] (RatFunc k) (q.coeff 2))
      (algebraMap k[X] (RatFunc k) (q.coeff 1))
  have hprim :
      Differential.deriv prim = RatFunc.C j / hRF := by
    simpa [prim, hRF] using
      alignedSquarePrimitive610_deriv_eq_simplePole_of_source p q H h0 j
        w1 f2 e1 e2 e3 hp hq hh0 hH hp6 hq10 hN hD hw hp4 he1 he2 he3
  have hnum : (58498535041007616 : RatFunc k) =
      RatFunc.C (58498535041007616 : k) :=
    (map_natCast (RatFunc.C : k →+* RatFunc k) 58498535041007616).symm
  have hmul :
      Differential.deriv
          (RatFunc.C (58498535041007616 : k) * prim) =
        RatFunc.C (58498535041007616 : k) * Differential.deriv prim := by
    simpa [ratFuncDerivation46_apply, Algebra.smul_def] using
      ratFuncDerivation46.map_smul (58498535041007616 : k) prim
  have hleib :
      Differential.deriv ((58498535041007616 : RatFunc k) * prim) =
        (58498535041007616 : RatFunc k) * (RatFunc.C j / hRF) := by
    rw [hnum, hmul, hprim]
  have hscale :
      (58498535041007616 : RatFunc k) * (RatFunc.C j / hRF) =
        RatFunc.C (58498535041007616 * j) / hRF := by
    rw [hnum, div_eq_mul_inv, div_eq_mul_inv, ← mul_assoc, ← map_mul]
  simpa [prim, hRF] using (hleib.trans hscale)

set_option maxHeartbeats 800000000 in
/-- **CLOSED** on a literal MixedPair source.  The jet is the pole-`21`
numerator of the scaled peeled primitive, whose derivative is the
genuine simple pole, so the order-`75` grandchildren are False. -/
theorem alignedSquareJetQuotient610_false_of_source
    (p q : k[X][X]) (H h0 : k[X]) (j a : k)
    (w1 f2 e1 e2 e3 : k[X])
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hdegree : h0.natDegree = 1) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9 = 0)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0) (hj : j ≠ 0)
    (hw : p.coeff 5 = h0 ^ 4 * w1)
    (hp4 : p.coeff 4 = h0 ^ 2 * f2)
    (he1 : (3 : k[X]) * f2 - w1 ^ 2 = h0 * e1)
    (he2 : (27 : k[X]) * p.coeff 3 - w1 ^ 3 = h0 * e2)
    (he3 : e2 = h0 * e3) : False := by
  let hRF : RatFunc k := algebraMap k[X] (RatFunc k) h0
  let w1RF : RatFunc k := algebraMap k[X] (RatFunc k) w1
  let f2RF : RatFunc k := algebraMap k[X] (RatFunc k) f2
  let e1RF : RatFunc k := algebraMap k[X] (RatFunc k) e1
  let e3RF : RatFunc k := algebraMap k[X] (RatFunc k) e3
  let a3RF : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 3)
  let a2RF : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 2)
  let a1RF : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 1)
  let a0RF : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 0)
  let b8RF : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 8)
  let b7RF : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 7)
  let b6RF : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 6)
  let b5RF : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 5)
  let b4RF : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 4)
  let b3RF : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 3)
  let b2RF : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 2)
  let b1RF : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 1)
  let quotient : k[X] :=
    alignedSquareJetQuotient610 h0 w1 e1 e3 (p.coeff 2) (p.coeff 1)
      (p.coeff 0) (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
      (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
  let rho : RatFunc k :=
    (58498535041007616 : RatFunc k) *
      alignedSquarePeeledPrimitive610 hRF w1RF f2RF a3RF a2RF a1RF a0RF
        b8RF b7RF b6RF b5RF b4RF b3RF b2RF b1RF
  have hhRF : hRF ≠ 0 := RatFunc.algebraMap_ne_zero hh0
  have he1RF :
      (3 : RatFunc k) * f2RF - w1RF ^ 2 = hRF * e1RF := by
    have hmapped := congrArg (algebraMap k[X] (RatFunc k)) he1
    simpa [f2RF, w1RF, hRF, e1RF, map_sub, map_mul, map_pow, map_ofNat]
      using hmapped
  have ha3RF :
      (27 : RatFunc k) * a3RF = w1RF ^ 3 + hRF ^ 2 * e3RF := by
    have he2' : (27 : k[X]) * p.coeff 3 = w1 ^ 3 + h0 * e2 := by
      linear_combination he2
    have ha3poly : (27 : k[X]) * p.coeff 3 = w1 ^ 3 + h0 ^ 2 * e3 := by
      calc
        (27 : k[X]) * p.coeff 3 = w1 ^ 3 + h0 * e2 := he2'
        _ = w1 ^ 3 + h0 * (h0 * e3) := by rw [he3]
        _ = w1 ^ 3 + h0 ^ 2 * e3 := by ring
    have hmapped := congrArg (algebraMap k[X] (RatFunc k)) ha3poly
    simpa [a3RF, w1RF, hRF, e3RF, map_add, map_mul, map_pow, map_ofNat]
      using hmapped
  have hbridge :=
    alignedSquareJetQuotient610_div_eq_clearedPrimitive hRF w1RF f2RF e1RF
      e3RF a3RF a2RF a1RF a0RF b8RF b7RF b6RF b5RF b4RF b3RF b2RF b1RF
      hhRF he1RF ha3RF
  have hmap :=
    alignedSquareJetQuotient610_map (algebraMap k[X] (RatFunc k)) h0 w1 e1
      e3 (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
      (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
      (q.coeff 1)
  have hclear :
      algebraMap k[X] (RatFunc k) quotient =
        hRF ^ alignedSquareRemainingPole610 * rho := by
    dsimp only [quotient, rho, alignedSquareRemainingPole610]
    rw [hmap]
    simp only [a2RF, a1RF, a0RF, b8RF, b7RF, b6RF, b5RF, b4RF, b3RF, b2RF,
      b1RF]
    rw [mul_comm (hRF ^ 21), ← div_eq_iff (pow_ne_zero 21 hhRF)]
    simpa [hRF, w1RF, e1RF, e3RF] using hbridge
  have hderiv :
      Differential.deriv rho =
        RatFunc.C (58498535041007616 * j) / hRF := by
    simpa [rho, hRF, w1RF, f2RF, a3RF, a2RF, a1RF, a0RF, b8RF, b7RF, b6RF,
      b5RF, b4RF, b3RF, b2RF, b1RF] using
      alignedSquarePrimitive610_scaledDeriv_eq_simplePole_of_source p q H
        h0 j w1 f2 e1 e2 e3 hp hq hh0 hH hp6 hq10 hN hD hw hp4 he1 he2 he3
  have hjscaled : (58498535041007616 : k) * j ≠ 0 :=
    mul_ne_zero (by norm_num) hj
  exact alignedSquareFace610_order75Grandchildren h0 w1 e1 e3 (p.coeff 2)
    (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7) (q.coeff 6)
    (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1) rho
    (58498535041007616 * j) a hh0 hdegree hroot hclear hderiv hjscaled

end AlignedSquareSourceFalse610

#print axioms alignedSquarePrimitive610_scaledDeriv_eq_simplePole_of_source
#print axioms alignedSquareJetQuotient610_false_of_source

/-! ## Chamber closure on the M1M2 hypotheses -/

section AlignedSquareChamber610

variable {K : Type*} [Field K] [CharZero K]

/-- **CLOSED.** Source-facing joint packet of the `(6,10)` aligned-square
chamber.  The M1M2 MixedPair peel supplies `w₁, f₂, e₁, e₃`; the wrapper
supplies the genuine simple pole; the identity supplies the pole-`21`
clearing; the order-`75` grandchildren are then False. -/
theorem alignedSquareFace610_squareChamber
    {P Q : MvPolynomial (Fin 2) K} {H h0 : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0) :
    False := by
  dsimp only at haligned
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  obtain ⟨a, j, _κ, _μ, _κ₃, _ν, _κ₅, _ν₂, _κ₇, _μ₃, _κ₉, w1, f2, e1, e2,
    _u2, e3, _s2, hdeg1, hroot, hj, _hrowK, _hroweval, _hD1, hp5w1, hp4f2,
    he1, he2, he3, _hu2, _hs2, _hR9, _hR8, _hR10, _hbranch, _hlimbA,
    _hlimbB⟩ :=
    normalized610ScaleTwo_alignedSquare_m1m2Reduction hsource hh0 hHsq
      haligned
  rcases hsource with
    ⟨_hH, _hHdegree, hPdegree, hQdegree, hp6src, hq10src, hKeller⟩
  have hp : p.natDegree = 6 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  have hp6 : p.coeff 6 = H ^ 3 := by
    simpa only [p] using hp6src
  have hq10 : q.coeff 10 = H ^ 5 := by
    simpa only [q] using hq10src
  obtain ⟨jKeller, hjKeller, hjac⟩ :=
    bivariateJacobian_eq_C_of_keller hKeller
  have hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C jKeller) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hjac
  exact alignedSquareJetQuotient610_false_of_source p q H h0 jKeller a w1
    f2 e1 e2 e3 hp hq hh0 hdeg1 hHsq hp6 hq10 haligned hD hroot hjKeller
    hp5w1 hp4f2 he1 he2 he3

/-- Source-facing exclusion of a normalized scale-two `(6,10)` aligned
square face.  The nonsquare chamber is not reopened. -/
theorem normalized610ScaleTwo_alignedSquare_false
    {P Q : MvPolynomial (Fin 2) K} {H h0 : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0) :
    False :=
  alignedSquareFace610_squareChamber hsource hh0 hHsq haligned

/-- **CLOSED.** The remaining aligned-square exclusion of the normalized
`(6,10)` route. -/
theorem planeKeller610AlignedSquareExclusion_closed :
    PlaneKeller610AlignedSquareExclusion (K := K) :=
  fun _P _Q _H _h0 hsource hh0 hHsq hN =>
    normalized610ScaleTwo_alignedSquare_false hsource hh0 hHsq hN

end AlignedSquareChamber610

#print axioms alignedSquareFace610_squareChamber
#print axioms normalized610ScaleTwo_alignedSquare_false
#print axioms planeKeller610AlignedSquareExclusion_closed

end Max11DegreeRoutes
