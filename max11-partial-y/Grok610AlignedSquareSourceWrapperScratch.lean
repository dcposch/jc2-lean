import Sol610ScaleTwoDegreeZeroPostCollapseCoordinateBridgeScratch

/-! # Aligned-square source wrapper for the `(6,10)` weight-fifteen primitive

Untracked working note.  No tracked file was edited.

`Grok610AlignedSquareM1M2Scratch` reduced both live MixedPair limbs and
did not close the square chamber.  This file is route M3: the analog of
`Grok610DegreeZeroSourceWrapperScratch` together with the pole/clearing
bookkeeping of the linear-root sibling, instantiated on the committed
aligned peel rather than copied from Backwire.

The affine source Jacobian still divides by exactly one power of `h`
(`differentialJacobian_affineDepress_sourceToRatFunc68`).  On the aligned
face `N = 0` the depressed `z⁹` coefficient is the constant `L = 0`, so
the weight-fifteen primitive satisfies the ordinary simple-pole equation
`ρ' = C(j)/h₀`.  This is not assumed, and it is not the linear-root
remaining pole `6`.

Under the MixedPair peel `p₅ = h₀⁴ w₁`, `p₄ = h₀² f₂`,
`3 f₂ - w₁² = h₀ e₁`, `27 p₃ - w₁³ = h₀² e₃`, `λ = 0`:

* `pole(A) = 2`, `pole(B) = 2`, `pole(C) = 4`, `pole(P) = 8`
  (the last because MixedPair does not peel `q₈`);
* native homogeneous clearing of the same weight-fifteen primitive is
  still `5 · 15 = 75`;
* the cleared compact numerator has base order `54` (not `69`) and
  remaining pole `21` (not `6`);
* the base-order head is the single monomial `67814496 b₈ w₁¹³`.

On the live `μ = 0` limb `w₁(a) ≠ 0`, the order-`21` pole obstruction
therefore forces `q₈(a) = 0`, which is a new `q`-side peel, not
`0 = j`.  The `w₁(a) = 0` child kills this MixedPair head automatically
and has a strictly later base order `61` (remaining pole `14`).  The
square chamber is not claimed empty.

CAS: `derive_610_aligned_square_source_wrapper.py` (job
`20260902T022625Z-aligned-square-source-wrapper-789`).  No `sorry`, no
new axioms, no finite-root shortcut, no closure overclaim.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## Bookkeeping: weight, native clearing, computed remaining pole -/

/-- Weighted degree of the `(6,10)` degree-zero primitive. -/
def alignedSquarePrimitiveWeight610 : ℕ := 15

/-- Source `h`-adic step of one sextic depression depth: the centre is
`a₅/(6 h⁵)`. -/
def alignedSquareCoordinateClearingStep610 : ℕ := 5

/-- Source-homogeneous clearing of a weight-`15` polynomial in
coordinates of denominator `h^{5d}`.  Instantiated from the same
primitive as the linear-root wrapper; not a claim that the aligned
vanishing order is `69`. -/
def alignedSquareSourceClearingPower610 : ℕ := 75

/-- Ordinary pole of `ρ'` supplied by AffineBracket: `ρ' = C(j)/h₀`. -/
def alignedSquareDerivativePoleOrder610 : ℕ := 1

/-- Lowest surviving power of `h` in the MixedPair-cleared compact
numerator.  Not `69`. -/
def alignedSquareBaseOrder610 : ℕ := 54

/-- Remaining pole of `ρ` after the MixedPair peel: `75 - 54 = 21`.
Not the linear-root remaining pole `6`. -/
def alignedSquareRemainingPole610 : ℕ := 21

/-- Native tower ceiling of the weight-fifteen primitive. -/
def alignedSquareTowerCeiling610 : ℕ := 75

/-- Compact integer scale of `degreeZeroClearedCompact610`. -/
def alignedSquareGroupedIntegerScale610 : ℕ := 58498535041007616

/-- Coefficient of the MixedPair base-order head `b₈ w₁¹³`. -/
def alignedSquareBaseHeadCoeff610 : ℕ := 67814496

theorem alignedSquarePrimitiveWeight610_eq :
    alignedSquarePrimitiveWeight610 = 15 :=
  rfl

theorem alignedSquareCoordinateClearingStep610_eq :
    alignedSquareCoordinateClearingStep610 = 5 :=
  rfl

theorem alignedSquareSourceClearingPower610_eq :
    alignedSquareSourceClearingPower610 = 75 :=
  rfl

theorem alignedSquareDerivativePoleOrder610_eq :
    alignedSquareDerivativePoleOrder610 = 1 :=
  rfl

theorem alignedSquareBaseOrder610_eq :
    alignedSquareBaseOrder610 = 54 :=
  rfl

theorem alignedSquareRemainingPole610_eq :
    alignedSquareRemainingPole610 = 21 :=
  rfl

theorem alignedSquareTowerCeiling610_eq :
    alignedSquareTowerCeiling610 = 75 :=
  rfl

theorem alignedSquareGroupedIntegerScale610_eq :
    alignedSquareGroupedIntegerScale610 = 58498535041007616 :=
  rfl

theorem alignedSquareBaseHeadCoeff610_eq :
    alignedSquareBaseHeadCoeff610 = 67814496 :=
  rfl

theorem alignedSquareSourceClearingPower610_eq_mul :
    alignedSquareSourceClearingPower610 =
      alignedSquareCoordinateClearingStep610 *
        alignedSquarePrimitiveWeight610 :=
  rfl

theorem alignedSquareRemainingPole610_eq_sub :
    alignedSquareRemainingPole610 =
      alignedSquareSourceClearingPower610 - alignedSquareBaseOrder610 :=
  rfl

theorem alignedSquareTowerCeiling610_eq_clearing :
    alignedSquareTowerCeiling610 = alignedSquareSourceClearingPower610 :=
  rfl

theorem alignedSquareGroupedIntegerScale610_eq_pow :
    alignedSquareGroupedIntegerScale610 = 2 ^ 24 * 3 ^ 20 := by
  decide

theorem alignedSquareBaseHeadCoeff610_eq_factor :
    alignedSquareBaseHeadCoeff610 = 2 ^ 5 * 3 ^ 8 * 17 * 19 := by
  decide

theorem alignedSquareBaseOrder610_ne_sixtyNine :
    alignedSquareBaseOrder610 ≠ 69 := by
  decide

theorem alignedSquareRemainingPole610_ne_six :
    alignedSquareRemainingPole610 ≠ 6 := by
  decide

theorem alignedSquareDerivativePoleOrder610_ne_remaining :
    alignedSquareDerivativePoleOrder610 ≠
      alignedSquareRemainingPole610 := by
  decide

#print axioms alignedSquareSourceClearingPower610_eq_mul
#print axioms alignedSquareRemainingPole610_eq_sub
#print axioms alignedSquareBaseOrder610_ne_sixtyNine
#print axioms alignedSquareRemainingPole610_ne_six

/-! ## MixedPair numerators and exact poles -/

section AlignedSquareBars610

variable {F : Type*} [Field F] [CharZero F]

/-- Polynomial numerator of `12 h¹⁰ A` after the MixedPair peel. -/
def alignedSquareABar610 (h w1 e1 : F) : F :=
  (4 : F) * e1 * h ^ 9 - h ^ 8 * w1 ^ 2

/-- Polynomial numerator of `54 h¹⁵ B` after the MixedPair peel. -/
def alignedSquareBBar610 (h w1 e1 e3 : F) : F :=
  -((12 : F) * e1 * h ^ 13 * w1) + (2 : F) * e3 * h ^ 14

/-- Polynomial numerator of `4 h¹⁰ P` on `λ = 0` after `a₅ = h⁴ w₁`. -/
def alignedSquarePBar610 (h w1 b8 : F) : F :=
  (4 : F) * b8 * h ^ 2 - (5 : F) * h ^ 8 * w1 ^ 2

/-- Polynomial numerator of `144 h²⁰ C` after the MixedPair peel. -/
def alignedSquareCBar610 (h w1 e1 e3 a2 : F) : F :=
  ((432 : F) * a2 * h ^ 18 + (24 : F) * e1 * h ^ 17 * w1 ^ 2 -
      (8 : F) * e3 * h ^ 18 * w1 + h ^ 16 * w1 ^ 4) / 3

theorem alignedSquareABar610_eq_generic
    (h w1 f2 e1 : F)
    (he1 : (3 : F) * f2 - w1 ^ 2 = h * e1) :
    (12 : F) * (h ^ 2 * f2) * h ^ 6 - (5 : F) * (h ^ 4 * w1) ^ 2 =
      alignedSquareABar610 h w1 e1 := by
  simp only [alignedSquareABar610]
  have h12 : (12 : F) * f2 = (4 : F) * ((3 : F) * f2) := by ring
  calc
    (12 : F) * (h ^ 2 * f2) * h ^ 6 - (5 : F) * (h ^ 4 * w1) ^ 2 =
        (12 : F) * f2 * h ^ 8 - (5 : F) * h ^ 8 * w1 ^ 2 := by ring
    _ = ((4 : F) * ((3 : F) * f2) - (5 : F) * w1 ^ 2) * h ^ 8 := by ring
    _ = ((4 : F) * (w1 ^ 2 + h * e1) - (5 : F) * w1 ^ 2) * h ^ 8 := by
      rw [← he1]; ring
    _ = (4 : F) * e1 * h ^ 9 - h ^ 8 * w1 ^ 2 := by ring

theorem alignedSquareBBar610_eq_generic
    (h w1 f2 e1 e3 a3 : F)
    (he1 : (3 : F) * f2 - w1 ^ 2 = h * e1)
    (ha3 : (27 : F) * a3 = w1 ^ 3 + h ^ 2 * e3) :
    (54 : F) * a3 * h ^ 12 - (36 : F) * (h ^ 2 * f2) * (h ^ 4 * w1) * h ^ 6 +
        (10 : F) * (h ^ 4 * w1) ^ 3 =
      alignedSquareBBar610 h w1 e1 e3 := by
  simp only [alignedSquareBBar610]
  have h27 : (27 : F) ≠ 0 := by norm_num
  have ha3' : a3 = (w1 ^ 3 + h ^ 2 * e3) / 27 := by
    field_simp [h27]
    linear_combination ha3
  rw [ha3']
  have hf2 : f2 = (w1 ^ 2 + h * e1) / 3 := by
    have h3 : (3 : F) ≠ 0 := by norm_num
    field_simp [h3]
    linear_combination he1
  rw [hf2]
  field_simp [h27]
  ring

theorem alignedSquarePBar610_eq_generic
    (h w1 b8 : F) :
    -((5 : F) * (h ^ 4 * w1) ^ 2) + (4 : F) * b8 * h ^ 2 =
      alignedSquarePBar610 h w1 b8 := by
  simp only [alignedSquarePBar610]
  ring

theorem alignedSquareDepressedA_eq_peeled
    (h w1 f2 e1 : F) (hh : h ≠ 0)
    (he1 : (3 : F) * f2 - w1 ^ 2 = h * e1) :
    depressedA610 h (sexticDepressionR610 h (h ^ 4 * w1))
        (h ^ 4 * w1) (h ^ 2 * f2) =
      alignedSquareABar610 h w1 e1 / ((12 : F) * h ^ 10) := by
  have hA :=
    depressedA610_eq_cleared h (h ^ 4 * w1) (h ^ 2 * f2) hh
  have hbar := alignedSquareABar610_eq_generic h w1 f2 e1 he1
  rw [hA, hbar]

theorem alignedSquareA_pole_two610
    (h w1 e1 : F) (hh : h ≠ 0) :
    alignedSquareABar610 h w1 e1 / ((12 : F) * h ^ 10) =
      -w1 ^ 2 / ((12 : F) * h ^ 2) + e1 / ((3 : F) * h) := by
  simp only [alignedSquareABar610]
  field_simp [hh]
  ring

theorem alignedSquareB_pole_two610
    (h w1 e1 e3 : F) (hh : h ≠ 0) :
    alignedSquareBBar610 h w1 e1 e3 / ((54 : F) * h ^ 15) =
      -((2 : F) * e1 * w1) / ((9 : F) * h ^ 2) +
        e3 / ((27 : F) * h) := by
  simp only [alignedSquareBBar610]
  field_simp [hh]
  ring

theorem alignedSquareP_pole_eight610
    (h w1 b8 : F) (hh : h ≠ 0) :
    alignedSquarePBar610 h w1 b8 / ((4 : F) * h ^ 10) =
      b8 / h ^ 8 - (5 : F) * w1 ^ 2 / ((4 : F) * h ^ 2) := by
  simp only [alignedSquarePBar610]
  field_simp [hh]

theorem alignedSquareL_eq_zero610
    (h a5 b9 : F) (hh : h ≠ 0)
    (hN : (5 : F) * a5 * h ^ 4 - (3 : F) * b9 = 0) :
    depressedL610 h (sexticDepressionR610 h a5) b9 = 0 := by
  have hL := depressedL610_eq_of_ninthPower h a5 b9 (0 : F) hh
    (by simpa using hN)
  simpa using hL

end AlignedSquareBars610

#print axioms alignedSquareABar610_eq_generic
#print axioms alignedSquareBBar610_eq_generic
#print axioms alignedSquarePBar610_eq_generic
#print axioms alignedSquareDepressedA_eq_peeled
#print axioms alignedSquareA_pole_two610
#print axioms alignedSquareB_pole_two610
#print axioms alignedSquareP_pole_eight610
#print axioms alignedSquareL_eq_zero610

/-! ## Source primitive on the aligned depression -/

section AlignedSquarePrimitiveDummy610

variable {F : Type*} [Field F] [CharZero F]

omit [CharZero F] in
/-- The weight-fifteen primitive does not use its last slot. -/
theorem alignedSquarePrimitive610_independent_of_X0
    (L A B C0 D0 E0 P Q R S0 T0 U0 V0 W0 X0 Y0 : F) :
    degreeZeroPrimitive610 L A B C0 D0 E0 P Q R S0 T0 U0 V0 W0 X0 =
      degreeZeroPrimitive610 L A B C0 D0 E0 P Q R S0 T0 U0 V0 W0 Y0 :=
  rfl

#print axioms alignedSquarePrimitive610_independent_of_X0

end AlignedSquarePrimitiveDummy610

section AlignedSquareSourcePrimitive610

variable {F : Type*} [Field F] [CharZero F]

/-- The weight-fifteen primitive on the sextic-decic depression of a
literal aligned `(6,10)` source.  The ninth-power scalar is specialised
to `λ = 0`, so `L` is definitionally the depressed `z⁹` coefficient of
the aligned face. -/
def alignedSquareSourcePrimitive610
    (h a5 a4 a3 a2 a1 a0 b9 b8 b7 b6 b5 b4 b3 b2 b1 : F) : F :=
  degreeZeroPrimitive610
    (depressedL610 h (sexticDepressionR610 h a5) b9)
    (depressedA610 h (sexticDepressionR610 h a5) a5 a4)
    (depressedB610 h (sexticDepressionR610 h a5) a5 a4 a3)
    (depressedC610 h (sexticDepressionR610 h a5) a5 a4 a3 a2)
    (depressedD610 h (sexticDepressionR610 h a5) a5 a4 a3 a2 a1)
    (depressedE610 h (sexticDepressionR610 h a5) a5 a4 a3 a2 a1 a0)
    (depressedP610 h (sexticDepressionR610 h a5) b9 b8)
    (depressedQ610 h (sexticDepressionR610 h a5) b9 b8 b7)
    (depressedR610 h (sexticDepressionR610 h a5) b9 b8 b7 b6)
    (depressedS610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5)
    (depressedT610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5 b4)
    (depressedU610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5 b4 b3)
    (depressedV610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5 b4 b3 b2)
    (depressedW610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5 b4 b3 b2
      b1)
    0

/-- MixedPair specialisation of the aligned source primitive. -/
def alignedSquarePeeledPrimitive610
    (h w1 f2 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F) : F :=
  alignedSquareSourcePrimitive610 h (h ^ 4 * w1) (h ^ 2 * f2) a3 a2 a1
    a0 ((5 : F) / 3 * (h ^ 4 * w1) * h ^ 4) b8 b7 b6 b5 b4 b3 b2 b1

end AlignedSquareSourcePrimitive610

/-! ## Affine source wrapper: `ρ' = C(j)/h₀` -/

section AlignedSquareSourceWrapper610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 800000000 in
/-- The weight-fifteen primitive, on the MixedPair peel of a literal
aligned `(6,10)` source, has the ordinary simple-pole derivative
supplied by the affine source Jacobian.  AffineBracket divides by
exactly one power of `h`, independently of the inner degrees, and
`N = 0` makes `L` a field constant, so the derivative pole is `1`
rather than a higher-order pole `C(j)/h₀ᵏ` for `k > 1`.  This is not
the remaining pole `21` of `ρ` itself. -/
theorem alignedSquarePrimitive610_deriv_eq_simplePole_of_source
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
        (alignedSquarePeeledPrimitive610
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
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0 := by
  let hRF : RatFunc k := algebraMap k[X] (RatFunc k) h0
  let a5 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 5)
  let a4 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 4)
  let a3 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 3)
  let a2 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 2)
  let a1 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 1)
  let a0 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 0)
  let b9 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 9)
  let b8 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 8)
  let b7 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 7)
  let b6 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 6)
  let b5 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 5)
  let b4 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 4)
  let b3 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 3)
  let b2 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 2)
  let b1 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 1)
  let w1RF : RatFunc k := algebraMap k[X] (RatFunc k) w1
  let f2RF : RatFunc k := algebraMap k[X] (RatFunc k) f2
  let f : (RatFunc k)[X] :=
    affineDepress68 hRF (sexticDepressionR610 hRF a5) (sourceToRatFunc68 p)
  let g : (RatFunc k)[X] :=
    affineDepress68 hRF (sexticDepressionR610 hRF a5) (sourceToRatFunc68 q)
  have hh : hRF ≠ 0 := RatFunc.algebraMap_ne_zero hh0
  have hpTop : algebraMap k[X] (RatFunc k) (p.coeff 6) = hRF ^ 6 := by
    simp only [hp6, hH, hRF, map_pow]
    ring
  have hqTop : algebraMap k[X] (RatFunc k) (q.coeff 10) = hRF ^ 10 := by
    simp only [hq10, hH, hRF, map_pow]
    ring
  have hpDep := affineDepress_sourceSextic68 p hRF
    (sexticDepressionR610 hRF a5) hp hh hpTop rfl
  have hNrat : 5 * a5 * hRF ^ 4 - 3 * b9 = 0 := by
    have hmapped := congrArg (algebraMap k[X] (RatFunc k)) hN
    have hH2 : algebraMap k[X] (RatFunc k) (H ^ 2) = hRF ^ 4 := by
      simp only [hH, hRF, map_pow]
      ring
    have hleft : algebraMap k[X] (RatFunc k)
        ((5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9) =
        5 * a5 * hRF ^ 4 - 3 * b9 := by
      simp only [map_sub, map_mul, map_ofNat, a5, b9, hH2]
    have hright : algebraMap k[X] (RatFunc k) (0 : k[X]) = 0 :=
      map_zero (algebraMap k[X] (RatFunc k))
    exact hleft.symm.trans (hmapped.trans hright)
  have hLval :
      depressedL610 hRF (sexticDepressionR610 hRF a5) b9 = 0 :=
    alignedSquareL_eq_zero610 hRF a5 b9 hh hNrat
  have hbracket := differentialJacobian_affineDepress_sourceToRatFunc68
    p q j hRF (sexticDepressionR610 hRF a5) hh hD
  have hf5 : f.coeff 5 = 0 := by
    dsimp only [f]
    rw [hpDep, coeff_depressedSextic68_five]
  have hf6 : f.coeff 6 = 1 := by
    dsimp only [f]
    rw [hpDep, coeff_depressedSextic68_six]
  have hf_high : ∀ n, 6 < n → f.coeff n = 0 := by
    intro n hn
    dsimp only [f]
    rw [hpDep, coeff_depressedSextic68_of_gt_six _ _ _ _ _ hn]
  have hg_high_src : ∀ n, 10 < n →
      (sourceToRatFunc68 q).coeff n = 0 := by
    intro n hn
    simp [sourceToRatFunc68, sourceToRatFunc46,
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : q.natDegree < n)]
  have hgTop : (sourceToRatFunc68 q).coeff 10 = hRF ^ 10 := by
    simpa [sourceToRatFunc68, sourceToRatFunc46] using hqTop
  obtain ⟨hg10, hg9, hg8, hg_high⟩ :=
    affineDepress_degreeTen_highCoeffs810 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src
  have hg9L : g.coeff 9 =
      depressedL610 hRF (sexticDepressionR610 hRF a5) b9 := by
    dsimp only [g]
    rw [hg9]
    simp [depressedL610, depressedL810, sexticDepressionR610,
      sourceToRatFunc68, sourceToRatFunc46, b9]
  have hg9const : g.coeff 9 = 0 := by
    rw [hg9L, hLval]
  have hLconst : ratFuncDerivation68 (g.coeff 9) = 0 := by
    rw [hg9const]
    have hx := ratFuncDerivation46_polynomial (C (0 : k) : k[X])
    simpa [ratFuncDerivation68, RatFunc.algebraMap_C] using hx
  have hprim :
      Differential.deriv
          (degreeZeroPrimitive610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
            (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
            (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3) (g.coeff 2)
            (g.coeff 1) (g.coeff 0)) =
        RatFunc.C j / hRF :=
    degreeZeroPrimitive610_ratFuncDeriv_eq_simplePole f g j hRF
      hf_high hf6 hf5 hg_high hg10 hLconst
      (by simpa only [f, g] using hbracket)
  have hf4 : f.coeff 4 =
      depressedA610 hRF (sexticDepressionR610 hRF a5) a5 a4 := by
    dsimp only [f, depressedA610, a5, a4]
    rw [hpDep, coeff_depressedSextic68_four]
  have hf3 : f.coeff 3 =
      depressedB610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 := by
    dsimp only [f, depressedB610, a5, a4, a3]
    rw [hpDep, coeff_depressedSextic68_three]
  have hf2 : f.coeff 2 =
      depressedC610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2 := by
    dsimp only [f, depressedC610, a5, a4, a3, a2]
    rw [hpDep, coeff_depressedSextic68_two]
  have hf1 : f.coeff 1 =
      depressedD610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2 a1 := by
    dsimp only [f, depressedD610, a5, a4, a3, a2, a1]
    rw [hpDep, coeff_depressedSextic68_one]
  have hf0 : f.coeff 0 =
      depressedE610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2 a1 a0 := by
    dsimp only [f, depressedE610, a5, a4, a3, a2, a1, a0]
    rw [hpDep, coeff_depressedSextic68_zero]
  have hg8' : g.coeff 8 =
      depressedP610 hRF (sexticDepressionR610 hRF a5) b9 b8 := by
    dsimp only [g]
    rw [hg8]
    simp [depressedP610, depressedP810, sexticDepressionR610,
      sourceToRatFunc68, sourceToRatFunc46, b9, b8]
  have hg7 : g.coeff 7 =
      depressedQ610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff7_810 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src]
    simp [depressedQ610, depressedQ810, sexticDepressionR610,
      sourceToRatFunc68, sourceToRatFunc46, b9, b8, b7]
  have hg6 : g.coeff 6 =
      depressedR610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff6_610 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src]
    simp [depressedR610, sexticDepressionR610, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6]
  have hg5 : g.coeff 5 =
      depressedS610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff5_610 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src]
    simp [depressedS610, sexticDepressionR610, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5]
  have hg4 : g.coeff 4 =
      depressedT610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5 b4 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff4_610 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src]
    simp [depressedT610, sexticDepressionR610, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4]
  have hg3 : g.coeff 3 =
      depressedU610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5 b4
        b3 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff3_610 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src]
    simp [depressedU610, sexticDepressionR610, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4, b3]
  have hg2 : g.coeff 2 =
      depressedV610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5 b4
        b3 b2 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff2_610 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src]
    simp [depressedV610, sexticDepressionR610, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4, b3, b2]
  have hg1 : g.coeff 1 =
      depressedW610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5 b4
        b3 b2 b1 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff1_610 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src]
    simp [depressedW610, sexticDepressionR610, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4, b3, b2, b1]
  have ha5peel : a5 = hRF ^ 4 * w1RF := by
    simp only [a5, w1RF, hRF, hw, map_mul, map_pow]
  have ha4peel : a4 = hRF ^ 2 * f2RF := by
    simp only [a4, f2RF, hRF, hp4, map_mul, map_pow]
  have hb9peel : b9 = (5 : RatFunc k) / 3 * (hRF ^ 4 * w1RF) * hRF ^ 4 := by
    have h3 : (3 : RatFunc k) ≠ 0 := by norm_num
    have hN' :
        (3 : RatFunc k) * b9 = (5 : RatFunc k) * a5 * hRF ^ 4 := by
      linear_combination -hNrat
    have hb9 : b9 = (5 : RatFunc k) / 3 * a5 * hRF ^ 4 := by
      field_simp [h3]
      linear_combination hN'
    simpa [ha5peel] using hb9
  have hcoords :
      degreeZeroPrimitive610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
          (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3) (g.coeff 2)
          (g.coeff 1) (g.coeff 0) =
        alignedSquarePeeledPrimitive610 hRF w1RF f2RF a3 a2 a1 a0 b8 b7
          b6 b5 b4 b3 b2 b1 := by
    rw [alignedSquarePrimitive610_independent_of_X0
      (g.coeff 9) (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1)
      (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5)
      (g.coeff 4) (g.coeff 3) (g.coeff 2) (g.coeff 1) (g.coeff 0) 0]
    simp only [alignedSquarePeeledPrimitive610,
      alignedSquareSourcePrimitive610]
    rw [hg9L, hf4, hf3, hf2, hf1, hf0, hg8', hg7, hg6, hg5, hg4, hg3,
      hg2, hg1, ha5peel, ha4peel, hb9peel]
  rw [← hcoords]
  exact hprim

#print axioms alignedSquarePrimitive610_deriv_eq_simplePole_of_source

end AlignedSquareSourceWrapper610

/-! ## Base-order head and the order-`21` pole obstruction -/

section AlignedSquareHead610

variable {R : Type*} [CommRing R]

/-- MixedPair base-order head of the cleared compact numerator. -/
def alignedSquareBaseHead610 (b8 w1 : R) : R :=
  (67814496 : R) * b8 * w1 ^ 13

set_option maxHeartbeats 800000000 in
/-- The `389`-term MixedPair jet quotient after cancelling `h⁵⁴`.
Its constant term is `alignedSquareBaseHead610`. -/
def alignedSquareJetQuotient610
    (h w1 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    (2106428730900480 : R) * h ^ 20 * e3 * a0 ^ 2
    + 58498535041007616 * h ^ 20 * a0 * b1
    - 12638572385402880 * h ^ 19 * w1 * e1 * a0 ^ 2
    - 37915717156208640 * h ^ 18 * w1 ^ 3 * a0 ^ 2
    - 2808571641200640 * h ^ 18 * w1 * e3 * a1 * a0
    - 9749755840167936 * h ^ 18 * w1 * a1 * b1
    - 19499511680335872 * h ^ 18 * w1 * a0 * b2
    - 13691786750853120 * h ^ 18 * e1 ^ 2 * a1 * a0
    - 2086844497920 * h ^ 18 * e3 ^ 3 * a0
    - 6687075336192 * h ^ 18 * e3 ^ 2 * b1
    + 113747151468625920 * h ^ 18 * a2 * a1 * a0
    + 18957858578104320 * h ^ 18 * a1 ^ 3
    - 20537680126279680 * h ^ 17 * w1 ^ 2 * e1 * a1 * a0
    + 93908002406400 * h ^ 17 * w1 * e1 * e3 ^ 2 * a0
    + 140428582060032 * h ^ 17 * w1 * e1 * e3 * b1
    + 178425204572160 * h ^ 17 * e1 ^ 3 * e3 * a0
    + 70214291030016 * h ^ 17 * e1 ^ 3 * b1
    - 3042619277967360 * h ^ 17 * e1 * e3 * a2 * a0
    - 1521309638983680 * h ^ 17 * e1 * e3 * a1 ^ 2
    - 3249918613389312 * h ^ 17 * e1 * a2 * b1
    - 6499837226778624 * h ^ 17 * e1 * a1 * b2
    - 9749755840167936 * h ^ 17 * e1 * a0 * b3
    + 49961856461045760 * h ^ 16 * w1 ^ 4 * a1 * a0
    + 117385003008000 * h ^ 16 * w1 ^ 3 * e3 ^ 2 * a0
    - 25076532510720 * h ^ 16 * w1 ^ 3 * e3 * b1
    - 401456710287360 * h ^ 16 * w1 ^ 2 * e1 ^ 2 * e3 * a0
    - 473946464452608 * h ^ 16 * w1 ^ 2 * e1 ^ 2 * b1
    - 2281964458475520 * h ^ 16 * w1 ^ 2 * e3 * a2 * a0
    - 1140982229237760 * h ^ 16 * w1 ^ 2 * e3 * a1 ^ 2
    + 2437438960041984 * h ^ 16 * w1 ^ 2 * a2 * b1
    + 4874877920083968 * h ^ 16 * w1 ^ 2 * a1 * b2
    + 7312316880125952 * h ^ 16 * w1 ^ 2 * a0 * b3
    - 1070551227432960 * h ^ 16 * w1 * e1 ^ 4 * a0
    + 22819644584755200 * h ^ 16 * w1 * e1 ^ 2 * a2 * a0
    + 11409822292377600 * h ^ 16 * w1 * e1 ^ 2 * a1 ^ 2
    + 3478074163200 * h ^ 16 * w1 * e3 ^ 3 * a1
    + 15603175784448 * h ^ 16 * w1 * e3 ^ 2 * b2
    - 37915717156208640 * h ^ 16 * w1 * a2 ^ 2 * a0
    - 37915717156208640 * h ^ 16 * w1 * a2 * a1 ^ 2
    + 29737534095360 * h ^ 16 * e1 ^ 2 * e3 ^ 2 * a1
    + 46809527353344 * h ^ 16 * e1 ^ 2 * e3 * b2
    + 453246976 * h ^ 16 * e3 ^ 5
    - 169034404331520 * h ^ 16 * e3 ^ 2 * a2 * a1
    - 722204136308736 * h ^ 16 * e3 * a2 * b2
    - 1083306204463104 * h ^ 16 * e3 * a1 * b3
    - 1444408272617472 * h ^ 16 * e3 * a0 * b4
    - 2544319940198400 * h ^ 15 * w1 ^ 4 * e1 * e3 * a0
    + 65825897840640 * h ^ 15 * w1 ^ 4 * e1 * b1
    - 1873464648007680 * h ^ 15 * w1 ^ 3 * e1 ^ 3 * a0
    + 57049111461888000 * h ^ 15 * w1 ^ 3 * e1 * a2 * a0
    + 28524555730944000 * h ^ 15 * w1 ^ 3 * e1 * a1 ^ 2
    - 44606301143040 * h ^ 15 * w1 ^ 2 * e1 * e3 ^ 2 * a1
    - 210642873090048 * h ^ 15 * w1 ^ 2 * e1 * e3 * b2
    - 475800545525760 * h ^ 15 * w1 * e1 ^ 3 * e3 * a1
    - 304261927796736 * h ^ 15 * w1 * e1 ^ 3 * b2
    - 54389637120 * h ^ 15 * w1 * e1 * e3 ^ 4
    + 5071032129945600 * h ^ 15 * w1 * e1 * e3 * a2 * a1
    + 7583143431241728 * h ^ 15 * w1 * e1 * a2 * b2
    + 11374715146862592 * h ^ 15 * w1 * e1 * a1 * b3
    + 15166286862483456 * h ^ 15 * w1 * e1 * a0 * b4
    - 111515752857600 * h ^ 15 * e1 ^ 5 * a1
    - 169967616000 * h ^ 15 * e1 ^ 3 * e3 ^ 3
    + 4817480523448320 * h ^ 15 * e1 ^ 3 * a2 * a1
    + 2202780303360 * h ^ 15 * e1 * e3 ^ 3 * a2
    + 7801587892224 * h ^ 15 * e1 * e3 ^ 2 * b3
    - 41075360252559360 * h ^ 15 * e1 * a2 ^ 2 * a1
    + 537476582522880 * h ^ 14 * w1 ^ 6 * e3 * a0
    - 470184984576 * h ^ 14 * w1 ^ 6 * b1
    + 10237146112327680 * h ^ 14 * w1 ^ 5 * e1 ^ 2 * a0
    - 28239310173634560 * h ^ 14 * w1 ^ 5 * a2 * a0
    - 14119655086817280 * h ^ 14 * w1 ^ 5 * a1 ^ 2
    - 141351107788800 * h ^ 14 * w1 ^ 4 * e3 ^ 2 * a1
    + 14627977297920 * h ^ 14 * w1 ^ 4 * e3 * b2
    - 624488216002560 * h ^ 14 * w1 ^ 3 * e1 ^ 2 * e3 * a1
    + 579267900997632 * h ^ 14 * w1 ^ 3 * e1 ^ 2 * b2
    - 23795466240 * h ^ 14 * w1 ^ 3 * e3 ^ 4
    + 6338790162432000 * h ^ 14 * w1 ^ 3 * e3 * a2 * a1
    - 1354132755578880 * h ^ 14 * w1 ^ 3 * a2 * b2
    - 2031199133368320 * h ^ 14 * w1 ^ 3 * a1 * b3
    - 2708265511157760 * h ^ 14 * w1 ^ 3 * a0 * b4
    + 1254552219648000 * h ^ 14 * w1 ^ 2 * e1 ^ 4 * a1
    + 1147281408000 * h ^ 14 * w1 ^ 2 * e1 ^ 2 * e3 ^ 3
    - 10839331177758720 * h ^ 14 * w1 ^ 2 * e1 ^ 2 * a2 * a1
    - 1652085227520 * h ^ 14 * w1 ^ 2 * e3 ^ 3 * a2
    - 17553572757504 * h ^ 14 * w1 ^ 2 * e3 ^ 2 * b3
    - 30806520189419520 * h ^ 14 * w1 ^ 2 * a2 ^ 2 * a1
    + 4206698496000 * h ^ 14 * w1 * e1 ^ 4 * e3 ^ 2
    - 79300090920960 * h ^ 14 * w1 * e1 ^ 2 * e3 ^ 2 * a2
    - 152130963898368 * h ^ 14 * w1 * e1 ^ 2 * e3 * b3
    + 140862003609600 * h ^ 14 * w1 * e3 ^ 2 * a2 ^ 2
    + 1263857238540288 * h ^ 14 * w1 * e3 * a2 * b3
    + 1685142984720384 * h ^ 14 * w1 * e3 * a1 * b4
    + 2106428730900480 * h ^ 14 * w1 * e3 * a0 * b5
    + 1185524121600 * h ^ 14 * e1 ^ 6 * e3
    - 61953196032000 * h ^ 14 * e1 ^ 4 * e3 * a2
    - 38032740974592 * h ^ 14 * e1 ^ 4 * b3
    + 802913420574720 * h ^ 14 * e1 ^ 2 * e3 * a2 ^ 2
    + 1895785857810432 * h ^ 14 * e1 ^ 2 * a2 * b3
    + 2527714477080576 * h ^ 14 * e1 ^ 2 * a1 * b4
    + 3159643096350720 * h ^ 14 * e1 ^ 2 * a0 * b5
    + 385263599616 * h ^ 14 * e3 ^ 3 * b4
    - 1521309638983680 * h ^ 14 * e3 * a2 ^ 3
    - 14624633760251904 * h ^ 14 * a2 ^ 2 * b3
    - 38999023360671744 * h ^ 14 * a2 * a1 * b4
    - 48748779200839680 * h ^ 14 * a2 * a0 * b5
    - 24374389600419840 * h ^ 14 * a1 ^ 2 * b5
    - 58498535041007616 * h ^ 14 * a1 * a0 * b6
    - 34124145440587776 * h ^ 14 * a0 ^ 2 * b7
    - 2328373457879040 * h ^ 13 * w1 ^ 7 * e1 * a0
    + 2274921358295040 * h ^ 13 * w1 ^ 5 * e1 * e3 * a1
    - 39495538704384 * h ^ 13 * w1 ^ 5 * e1 * b2
    + 4937359957770240 * h ^ 13 * w1 ^ 4 * e1 ^ 3 * a1
    + 2257594859520 * h ^ 13 * w1 ^ 4 * e1 * e3 ^ 3
    - 68696638385356800 * h ^ 13 * w1 ^ 4 * e1 * a2 * a1
    - 3441844224000 * h ^ 13 * w1 ^ 3 * e1 ^ 3 * e3 ^ 2
    - 69387579555840 * h ^ 13 * w1 ^ 3 * e1 * e3 ^ 2 * a2
    + 193089300332544 * h ^ 13 * w1 ^ 3 * e1 * e3 * b3
    - 26674292736000 * h ^ 13 * w1 ^ 2 * e1 ^ 5 * e3
    + 557578764288000 * h ^ 13 * w1 ^ 2 * e1 ^ 3 * e3 * a2
    + 570491114618880 * h ^ 13 * w1 ^ 2 * e1 ^ 3 * b3
    - 1204370130862080 * h ^ 13 * w1 ^ 2 * e1 * e3 * a2 ^ 2
    - 8531036360146944 * h ^ 13 * w1 ^ 2 * e1 * a2 * b3
    - 11374715146862592 * h ^ 13 * w1 ^ 2 * e1 * a1 * b4
    - 14218393933578240 * h ^ 13 * w1 ^ 2 * e1 * a0 * b5
    - 7113144729600 * h ^ 13 * w1 * e1 ^ 7
    + 408891093811200 * h ^ 13 * w1 * e1 ^ 5 * a2
    - 6423307364597760 * h ^ 13 * w1 * e1 ^ 3 * a2 ^ 2
    - 22537920577536 * h ^ 13 * w1 * e1 * e3 ^ 2 * b4
    + 22819644584755200 * h ^ 13 * w1 * e1 * a2 ^ 3
    - 22537920577536 * h ^ 13 * e1 ^ 3 * e3 * b4
    + 561714328240128 * h ^ 13 * e1 * e3 * a2 * b4
    + 702142910300160 * h ^ 13 * e1 * e3 * a1 * b5
    + 842571492360192 * h ^ 13 * e1 * e3 * a0 * b6
    + 20751991603200 * h ^ 12 * w1 ^ 9 * a0
    - 258708161986560 * h ^ 12 * w1 ^ 7 * e3 * a1
    + 156728328192 * h ^ 12 * w1 ^ 7 * b2
    - 7713405230469120 * h ^ 12 * w1 ^ 6 * e1 ^ 2 * a1
    - 1175644753920 * h ^ 12 * w1 ^ 6 * e3 ^ 3
    + 14511867728117760 * h ^ 12 * w1 ^ 6 * a2 * a1
    - 41560269004800 * h ^ 12 * w1 ^ 5 * e1 ^ 2 * e3 ^ 2
    + 126384519905280 * h ^ 12 * w1 ^ 5 * e3 ^ 2 * a2
    - 6582589784064 * h ^ 12 * w1 ^ 5 * e3 * b3
    - 46787569920000 * h ^ 12 * w1 ^ 4 * e1 ^ 4 * e3
    + 1645786652590080 * h ^ 12 * w1 ^ 4 * e1 ^ 2 * e3 * a2
    - 470655169560576 * h ^ 12 * w1 ^ 4 * e1 ^ 2 * b3
    - 3816479910297600 * h ^ 12 * w1 ^ 4 * e3 * a2 ^ 2
    + 592433080565760 * h ^ 12 * w1 ^ 4 * a2 * b3
    + 789910774087680 * h ^ 12 * w1 ^ 4 * a1 * b4
    + 987388467609600 * h ^ 12 * w1 ^ 4 * a0 * b5
    + 39122296012800 * h ^ 12 * w1 ^ 3 * e1 ^ 6
    - 418184073216000 * h ^ 12 * w1 ^ 3 * e1 ^ 4 * a2
    - 8430590916034560 * h ^ 12 * w1 ^ 3 * e1 ^ 2 * a2 ^ 2
    + 14302911135744 * h ^ 12 * w1 ^ 3 * e3 ^ 2 * b4
    + 28524555730944000 * h ^ 12 * w1 ^ 3 * a2 ^ 3
    + 253551606497280 * h ^ 12 * w1 ^ 2 * e1 ^ 2 * e3 * b4
    - 1263857238540288 * h ^ 12 * w1 ^ 2 * e3 * a2 * b4
    - 1579821548175360 * h ^ 12 * w1 ^ 2 * e3 * a1 * b5
    - 1895785857810432 * h ^ 12 * w1 ^ 2 * e3 * a0 * b6
    + 160582684114944 * h ^ 12 * w1 * e1 ^ 4 * b4
    - 5476714700341248 * h ^ 12 * w1 * e1 ^ 2 * a2 * b4
    - 6845893375426560 * h ^ 12 * w1 * e1 ^ 2 * a1 * b5
    - 8215072050511872 * h ^ 12 * w1 * e1 ^ 2 * a0 * b6
    - 1043422248960 * h ^ 12 * w1 * e3 ^ 3 * b5
    + 22749430293725184 * h ^ 12 * w1 * a2 ^ 2 * b4
    + 56873575734312960 * h ^ 12 * w1 * a2 * a1 * b5
    + 68248290881175552 * h ^ 12 * w1 * a2 * a0 * b6
    + 34124145440587776 * h ^ 12 * w1 * a1 ^ 2 * b6
    + 79623006028038144 * h ^ 12 * w1 * a1 * a0 * b7
    + 45498860587450368 * h ^ 12 * w1 * a0 ^ 2 * b8
    - 4695400120320 * h ^ 12 * e1 ^ 2 * e3 ^ 2 * b5
    + 39007939461120 * h ^ 12 * e3 ^ 2 * a2 * b5
    + 46809527353344 * h ^ 12 * e3 ^ 2 * a1 * b6
    + 54611115245568 * h ^ 12 * e3 ^ 2 * a0 * b7
    + 1068273617748480 * h ^ 11 * w1 ^ 8 * e1 * a1
    + 21307883950080 * h ^ 11 * w1 ^ 7 * e1 * e3 ^ 2
    + 259751681280000 * h ^ 11 * w1 ^ 6 * e1 ^ 3 * e3
    - 1714090051215360 * h ^ 11 * w1 ^ 6 * e1 * e3 * a2
    + 18102121906176 * h ^ 11 * w1 ^ 6 * e1 * b3
    + 208859712122880 * h ^ 11 * w1 ^ 5 * e1 ^ 5
    - 6732763578777600 * h ^ 11 * w1 ^ 5 * e1 ^ 3 * a2
    + 30711438336983040 * h ^ 11 * w1 ^ 5 * e1 * a2 ^ 2
    - 139453383573504 * h ^ 11 * w1 ^ 4 * e1 * e3 * b4
    - 718396218408960 * h ^ 11 * w1 ^ 3 * e1 ^ 3 * b4
    + 6951214811971584 * h ^ 11 * w1 ^ 3 * e1 * a2 * b4
    + 8689018514964480 * h ^ 11 * w1 ^ 3 * e1 * a1 * b5
    + 10426822217957376 * h ^ 11 * w1 ^ 3 * e1 * a0 * b6
    + 35215500902400 * h ^ 11 * w1 ^ 2 * e1 * e3 ^ 2 * b5
    + 89212602286080 * h ^ 11 * w1 * e1 ^ 3 * e3 * b5
    - 1521309638983680 * h ^ 11 * w1 * e1 * e3 * a2 * b5
    - 1825571566780416 * h ^ 11 * w1 * e1 * e3 * a1 * b6
    - 2129833494577152 * h ^ 11 * w1 * e1 * e3 * a0 * b7
    + 13381890342912 * h ^ 11 * e1 ^ 5 * b5
    - 760654819491840 * h ^ 11 * e1 ^ 3 * a2 * b5
    - 912785783390208 * h ^ 11 * e1 ^ 3 * a1 * b6
    - 1064916747288576 * h ^ 11 * e1 ^ 3 * a0 * b7
    - 417368899584 * h ^ 11 * e1 * e3 ^ 3 * b6
    + 9478929289052160 * h ^ 11 * e1 * a2 ^ 2 * b5
    + 22749430293725184 * h ^ 11 * e1 * a2 * a1 * b6
    + 26541002009346048 * h ^ 11 * e1 * a2 * a0 * b7
    + 13270501004673024 * h ^ 11 * e1 * a1 ^ 2 * b7
    + 30332573724966912 * h ^ 11 * e1 * a1 * a0 * b8
    - 6522826527360 * h ^ 10 * w1 ^ 10 * a1
    - 972141730560 * h ^ 10 * w1 ^ 9 * e3 ^ 2
    - 118279783440000 * h ^ 10 * w1 ^ 8 * e1 ^ 2 * e3
    + 118697068638720 * h ^ 10 * w1 ^ 8 * e3 * a2
    - 44079842304 * h ^ 10 * w1 ^ 8 * b3
    - 516534771916800 * h ^ 10 * w1 ^ 7 * e1 ^ 4
    + 5177815799869440 * h ^ 10 * w1 ^ 7 * e1 ^ 2 * a2
    - 3492560186818560 * h ^ 10 * w1 ^ 7 * a2 ^ 2
    + 2681795837952 * h ^ 10 * w1 ^ 6 * e3 * b4
    + 313770113040384 * h ^ 10 * w1 ^ 5 * e1 ^ 2 * b4
    - 236973232226304 * h ^ 10 * w1 ^ 5 * a2 * b4
    - 296216540282880 * h ^ 10 * w1 ^ 5 * a1 * b5
    - 355459848339456 * h ^ 10 * w1 ^ 5 * a0 * b6
    - 9684262748160 * h ^ 10 * w1 ^ 4 * e3 ^ 2 * b5
    - 299331757670400 * h ^ 10 * w1 ^ 3 * e1 ^ 2 * e3 * b5
    + 965446501662720 * h ^ 10 * w1 ^ 3 * e3 * a2 * b5
    + 1158535801995264 * h ^ 10 * w1 ^ 3 * e3 * a1 * b6
    + 1351625102327808 * h ^ 10 * w1 ^ 3 * e3 * a0 * b7
    - 351274621501440 * h ^ 10 * w1 ^ 2 * e1 ^ 4 * b5
    + 8557366719283200 * h ^ 10 * w1 ^ 2 * e1 ^ 2 * a2 * b5
    + 10268840063139840 * h ^ 10 * w1 ^ 2 * e1 ^ 2 * a1 * b6
    + 11980313406996480 * h ^ 10 * w1 ^ 2 * e1 ^ 2 * a0 * b7
    + 1565133373440 * h ^ 10 * w1 ^ 2 * e3 ^ 3 * b6
    - 21327590900367360 * h ^ 10 * w1 ^ 2 * a2 ^ 2 * b5
    - 51186218160881664 * h ^ 10 * w1 ^ 2 * a2 * a1 * b6
    - 59717254521028608 * h ^ 10 * w1 ^ 2 * a2 * a0 * b7
    - 29858627260514304 * h ^ 10 * w1 ^ 2 * a1 ^ 2 * b7
    - 68248290881175552 * h ^ 10 * w1 ^ 2 * a1 * a0 * b8
    + 17842520457216 * h ^ 10 * w1 * e1 ^ 2 * e3 ^ 2 * b6
    - 101420642598912 * h ^ 10 * w1 * e3 ^ 2 * a2 * b6
    - 118324083032064 * h ^ 10 * w1 * e3 ^ 2 * a1 * b7
    - 135227523465216 * h ^ 10 * w1 * e3 ^ 2 * a0 * b8
    + 8921260228608 * h ^ 10 * e1 ^ 4 * e3 * b6
    - 304261927796736 * h ^ 10 * e1 ^ 2 * e3 * a2 * b6
    - 354972249096192 * h ^ 10 * e1 ^ 2 * e3 * a1 * b7
    - 405682570395648 * h ^ 10 * e1 ^ 2 * e3 * a0 * b8
    - 13525843968 * h ^ 10 * e3 ^ 4 * b7
    + 1263857238540288 * h ^ 10 * e3 * a2 ^ 2 * b6
    + 2949000223260672 * h ^ 10 * e3 * a2 * a1 * b7
    + 3370285969440768 * h ^ 10 * e3 * a2 * a0 * b8
    + 1685142984720384 * h ^ 10 * e3 * a1 ^ 2 * b8
    + 7517337347520 * h ^ 9 * w1 ^ 10 * e1 * e3
    + 205018291296000 * h ^ 9 * w1 ^ 9 * e1 ^ 3
    - 472460881052160 * h ^ 9 * w1 ^ 9 * e1 * a2
    - 7470716977152 * h ^ 9 * w1 ^ 7 * e1 * b4
    + 87158364733440 * h ^ 9 * w1 ^ 5 * e1 * e3 * b5
    + 710912924467200 * h ^ 9 * w1 ^ 4 * e1 ^ 3 * b5
    - 4706551695605760 * h ^ 9 * w1 ^ 4 * e1 * a2 * b5
    - 5647862034726912 * h ^ 9 * w1 ^ 4 * e1 * a1 * b6
    - 6589172373848064 * h ^ 9 * w1 ^ 4 * e1 * a0 * b7
    - 39910901022720 * h ^ 9 * w1 ^ 3 * e1 * e3 ^ 2 * b6
    - 187346464800768 * h ^ 9 * w1 ^ 2 * e1 ^ 3 * e3 * b6
    + 2281964458475520 * h ^ 9 * w1 ^ 2 * e1 * e3 * a2 * b6
    + 2662291868221440 * h ^ 9 * w1 ^ 2 * e1 * e3 * a1 * b7
    + 3042619277967360 * h ^ 9 * w1 ^ 2 * e1 * e3 * a0 * b8
    - 66909451714560 * h ^ 9 * w1 * e1 ^ 5 * b6
    + 2890488314068992 * h ^ 9 * w1 * e1 ^ 3 * a2 * b6
    + 3372236366413824 * h ^ 9 * w1 * e1 ^ 3 * a1 * b7
    + 3853984418758656 * h ^ 9 * w1 * e1 ^ 3 * a0 * b8
    + 1541946212352 * h ^ 9 * w1 * e1 * e3 ^ 3 * b7
    - 24645216151535616 * h ^ 9 * w1 * e1 * a2 ^ 2 * b6
    - 57505504353583104 * h ^ 9 * w1 * e1 * a2 * a1 * b7
    - 65720576404094976 * h ^ 9 * w1 * e1 * a2 * a0 * b8
    - 32860288202047488 * h ^ 9 * w1 * e1 * a1 ^ 2 * b8
    + 2312919318528 * h ^ 9 * e1 ^ 3 * e3 ^ 2 * b7
    - 39441361010688 * h ^ 9 * e1 * e3 ^ 2 * a2 * b7
    - 45075841155072 * h ^ 9 * e1 * e3 ^ 2 * a1 * b8
    - 24284496600 * h ^ 8 * w1 ^ 12 * e3
    - 14193574012800 * h ^ 8 * w1 ^ 11 * e1 ^ 2
    + 2062916968320 * h ^ 8 * w1 ^ 11 * a2
    + 11972302848 * h ^ 8 * w1 ^ 9 * b4
    - 1037599580160 * h ^ 8 * w1 ^ 7 * e3 * b5
    - 185211525058560 * h ^ 8 * w1 ^ 6 * e1 ^ 2 * b5
    + 90510609530880 * h ^ 8 * w1 ^ 6 * a2 * b5
    + 108612731437056 * h ^ 8 * w1 ^ 6 * a1 * b6
    + 126714853343232 * h ^ 8 * w1 ^ 6 * a0 * b7
    + 5810557648896 * h ^ 8 * w1 ^ 5 * e3 ^ 2 * b6
    + 284365169786880 * h ^ 8 * w1 ^ 4 * e1 ^ 2 * e3 * b6
    - 627540226080768 * h ^ 8 * w1 ^ 4 * e3 * a2 * b6
    - 732130263760896 * h ^ 8 * w1 ^ 4 * e3 * a1 * b7
    - 836720301441024 * h ^ 8 * w1 ^ 4 * e3 * a0 * b8
    + 538621086302208 * h ^ 8 * w1 ^ 3 * e1 ^ 4 * b6
    - 9698348948520960 * h ^ 8 * w1 ^ 3 * e1 ^ 2 * a2 * b6
    - 11314740439941120 * h ^ 8 * w1 ^ 3 * e1 ^ 2 * a1 * b7
    - 12931131931361280 * h ^ 8 * w1 ^ 3 * e1 ^ 2 * a0 * b8
    - 1724545105920 * h ^ 8 * w1 ^ 3 * e3 ^ 3 * b7
    + 15640233326936064 * h ^ 8 * w1 ^ 3 * a2 ^ 2 * b6
    + 36493877762850816 * h ^ 8 * w1 ^ 3 * a2 * a1 * b7
    + 41707288871829504 * h ^ 8 * w1 ^ 3 * a2 * a0 * b8
    + 20853644435914752 * h ^ 8 * w1 ^ 3 * a1 ^ 2 * b8
    - 36428479266816 * h ^ 8 * w1 ^ 2 * e1 ^ 2 * e3 ^ 2 * b7
    + 147905103790080 * h ^ 8 * w1 ^ 2 * e3 ^ 2 * a2 * b7
    + 169034404331520 * h ^ 8 * w1 ^ 2 * e3 ^ 2 * a1 * b8
    - 43367237222400 * h ^ 8 * w1 * e1 ^ 4 * e3 * b7
    + 1124078788804608 * h ^ 8 * w1 * e1 ^ 2 * e3 * a2 * b7
    + 1284661472919552 * h ^ 8 * w1 * e1 ^ 2 * e3 * a1 * b8
    + 48950673408 * h ^ 8 * w1 * e3 ^ 4 * b8
    - 3194750241865728 * h ^ 8 * w1 * e3 * a2 ^ 2 * b7
    - 7302286267121664 * h ^ 8 * w1 * e3 * a2 * a1 * b8
    - 4336723722240 * h ^ 8 * e1 ^ 6 * b7
    + 281019697201152 * h ^ 8 * e1 ^ 4 * a2 * b7
    + 321165368229888 * h ^ 8 * e1 ^ 4 * a1 * b8
    + 293704040448 * h ^ 8 * e1 ^ 2 * e3 ^ 3 * b8
    - 4792125362798592 * h ^ 8 * e1 ^ 2 * a2 ^ 2 * b7
    - 10953429400682496 * h ^ 8 * e1 ^ 2 * a2 * a1 * b8
    - 1669475598336 * h ^ 8 * e3 ^ 3 * a2 * b8
    + 13270501004673024 * h ^ 8 * a2 ^ 3 * b7
    + 45498860587450368 * h ^ 8 * a2 ^ 2 * a1 * b8
    + 69754744080 * h ^ 7 * w1 ^ 13 * e1
    + 2918248819200 * h ^ 7 * w1 ^ 8 * e1 * b5
    - 49389740015616 * h ^ 7 * w1 ^ 6 * e1 * e3 * b6
    - 597166856552448 * h ^ 7 * w1 ^ 5 * e1 ^ 3 * b6
    + 2823931017363456 * h ^ 7 * w1 ^ 5 * e1 * a2 * b6
    + 3294586186924032 * h ^ 7 * w1 ^ 5 * e1 * a1 * b7
    + 3765241356484608 * h ^ 7 * w1 ^ 5 * e1 * a0 * b8
    + 36862151639040 * h ^ 7 * w1 ^ 4 * e1 * e3 ^ 2 * b7
    + 279285007712256 * h ^ 7 * w1 ^ 3 * e1 ^ 3 * e3 * b7
    - 2514386764431360 * h ^ 7 * w1 ^ 3 * e1 * e3 * a2 * b7
    - 2873584873635840 * h ^ 7 * w1 ^ 3 * e1 * e3 * a1 * b8
    + 175637310750720 * h ^ 7 * w1 ^ 2 * e1 ^ 5 * b7
    - 5901413641224192 * h ^ 7 * w1 ^ 2 * e1 ^ 3 * a2 * b7
    - 6744472732827648 * h ^ 7 * w1 ^ 2 * e1 ^ 3 * a1 * b8
    - 3083892424704 * h ^ 7 * w1 ^ 2 * e1 * e3 ^ 3 * b8
    + 35940940220989440 * h ^ 7 * w1 ^ 2 * e1 * a2 ^ 2 * b7
    + 82150720505118720 * h ^ 7 * w1 ^ 2 * e1 * a2 * a1 * b8
    - 11013901516800 * h ^ 7 * w1 * e1 ^ 3 * e3 ^ 2 * b8
    + 142740163657728 * h ^ 7 * w1 * e1 * e3 ^ 2 * a2 * b8
    - 3304170455040 * h ^ 7 * e1 ^ 5 * e3 * b8
    + 142740163657728 * h ^ 7 * e1 ^ 3 * e3 * a2 * b8
    - 1217047711186944 * h ^ 7 * e1 * e3 * a2 ^ 2 * b8
    - 26372304 * h ^ 6 * w1 ^ 15
    - 3242498688 * h ^ 6 * w1 ^ 10 * b5
    + 389099842560 * h ^ 6 * w1 ^ 8 * e3 * b6
    + 100543399317504 * h ^ 6 * w1 ^ 7 * e1 ^ 2 * b6
    - 33618226397184 * h ^ 6 * w1 ^ 7 * a2 * b6
    - 39221264130048 * h ^ 6 * w1 ^ 7 * a1 * b7
    - 44824301862912 * h ^ 6 * w1 ^ 7 * a0 * b8
    - 3201186852864 * h ^ 6 * w1 ^ 6 * e3 ^ 2 * b7
    - 232231555325952 * h ^ 6 * w1 ^ 5 * e1 ^ 2 * e3 * b7
    + 366065131880448 * h ^ 6 * w1 ^ 5 * e3 * a2 * b7
    + 418360150720512 * h ^ 6 * w1 ^ 5 * e3 * a1 * b8
    - 654574236825600 * h ^ 6 * w1 ^ 4 * e1 ^ 4 * b7
    + 8957502848286720 * h ^ 6 * w1 ^ 4 * e1 ^ 2 * a2 * b7
    + 10237146112327680 * h ^ 6 * w1 ^ 4 * e1 ^ 2 * a1 * b8
    + 1560302714880 * h ^ 6 * w1 ^ 4 * e3 ^ 3 * b8
    - 9883758560772096 * h ^ 6 * w1 ^ 4 * a2 ^ 2 * b7
    - 22591448138907648 * h ^ 6 * w1 ^ 4 * a2 * a1 * b8
    + 53197144326144 * h ^ 6 * w1 ^ 3 * e1 ^ 2 * e3 ^ 2 * b8
    - 159643604090880 * h ^ 6 * w1 ^ 3 * e3 ^ 2 * a2 * b8
    + 111515752857600 * h ^ 6 * w1 ^ 2 * e1 ^ 4 * e3 * b8
    - 2248157577609216 * h ^ 6 * w1 ^ 2 * e1 ^ 2 * e3 * a2 * b8
    + 4563928916951040 * h ^ 6 * w1 ^ 2 * e3 * a2 ^ 2 * b8
    + 25607321026560 * h ^ 6 * w1 * e1 ^ 6 * b8
    - 1338189034291200 * h ^ 6 * w1 * e1 ^ 4 * a2 * b8
    + 17342929884413952 * h ^ 6 * w1 * e1 ^ 2 * a2 ^ 2 * b8
    - 32860288202047488 * h ^ 6 * w1 * a2 ^ 3 * b8
    - 1102449553920 * h ^ 5 * w1 ^ 9 * e1 * b6
    + 26066807230464 * h ^ 5 * w1 ^ 7 * e1 * e3 * b7
    + 445110481041408 * h ^ 5 * w1 ^ 6 * e1 ^ 3 * b7
    - 1555776810491904 * h ^ 5 * w1 ^ 6 * e1 * a2 * b7
    - 1778030640562176 * h ^ 5 * w1 ^ 6 * e1 * a1 * b8
    - 29489721311232 * h ^ 5 * w1 ^ 5 * e1 * e3 ^ 2 * b8
    - 332482152038400 * h ^ 5 * w1 ^ 4 * e1 ^ 3 * e3 * b8
    + 2274921358295040 * h ^ 5 * w1 ^ 4 * e1 * e3 * a2 * b8
    - 323395683287040 * h ^ 5 * w1 ^ 3 * e1 ^ 5 * b8
    + 8617937380835328 * h ^ 5 * w1 ^ 3 * e1 ^ 3 * a2 * b8
    - 38793395794083840 * h ^ 5 * w1 ^ 3 * e1 * a2 ^ 2 * b8
    + 884317824 * h ^ 4 * w1 ^ 11 * b6
    - 142910127360 * h ^ 4 * w1 ^ 9 * e3 * b7
    - 51319026734976 * h ^ 4 * w1 ^ 8 * e1 ^ 2 * b7
    + 12256645040640 * h ^ 4 * w1 ^ 8 * a2 * b7
    + 14007594332160 * h ^ 4 * w1 ^ 8 * a1 * b8
    + 1655035379712 * h ^ 4 * w1 ^ 7 * e3 ^ 2 * b8
    + 169565897539584 * h ^ 4 * w1 ^ 6 * e1 ^ 2 * e3 * b8
    - 197558960062464 * h ^ 4 * w1 ^ 6 * e3 * a2 * b8
    + 673276357877760 * h ^ 4 * w1 ^ 5 * e1 ^ 4 * b8
    - 7166002278629376 * h ^ 4 * w1 ^ 5 * e1 ^ 2 * a2 * b8
    + 5647862034726912 * h ^ 4 * w1 ^ 5 * a2 ^ 2 * b8
    + 407293862976 * h ^ 3 * w1 ^ 10 * e1 * b7
    - 13033403615232 * h ^ 3 * w1 ^ 8 * e1 * e3 * b8
    - 302796245606400 * h ^ 3 * w1 ^ 7 * e1 ^ 3 * b8
    + 804347194540032 * h ^ 3 * w1 ^ 7 * e1 * a2 * b8
    - 243596808 * h ^ 2 * w1 ^ 12 * b7
    + 51719855616 * h ^ 2 * w1 ^ 10 * e3 * b8
    + 24980690262528 * h ^ 2 * w1 ^ 9 * e1 ^ 2 * b8
    - 4409798215680 * h ^ 2 * w1 ^ 9 * a2 * b8
    - 148106859264 * h * w1 ^ 11 * e1 * b8
    + 67814496 * w1 ^ 13 * b8

set_option maxHeartbeats 800000000 in
theorem alignedSquareJetQuotient610_head
    (w1 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) :
    alignedSquareJetQuotient610 0 w1 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3
        b2 b1 =
      alignedSquareBaseHead610 b8 w1 := by
  simp only [alignedSquareJetQuotient610, alignedSquareBaseHead610]
  ring

end AlignedSquareHead610

#print axioms alignedSquareJetQuotient610_head

section AlignedSquareHeadKill610

variable {k : Type*} [Field k] [CharZero k]

theorem alignedSquareBaseHeadCoeff610_ne_zero :
    (alignedSquareBaseHeadCoeff610 : k) ≠ 0 :=
  Nat.cast_ne_zero.mpr (by decide)

/-- On `w₁ ≠ 0` the MixedPair base-order head forces `b₈ = 0`. -/
theorem alignedSquareBaseHead610_q8_of_w1_ne_zero
    (b8 w1 : k) (hw1 : w1 ≠ 0)
    (hhead : alignedSquareBaseHead610 b8 w1 = 0) :
    b8 = 0 := by
  have hcoeff : (67814496 : k) ≠ 0 :=
    alignedSquareBaseHeadCoeff610_ne_zero
  have hw13 : w1 ^ 13 ≠ 0 := pow_ne_zero 13 hw1
  have hassoc :
      (67814496 : k) * (b8 * w1 ^ 13) = 0 := by
    simpa [alignedSquareBaseHead610, mul_assoc] using hhead
  have hb8w : b8 * w1 ^ 13 = 0 :=
    (mul_eq_zero.mp hassoc).resolve_left hcoeff
  exact (mul_eq_zero.mp hb8w).resolve_right hw13

end AlignedSquareHeadKill610

#print axioms alignedSquareBaseHead610_q8_of_w1_ne_zero

/-! ## Remaining-pole head obstruction (not pole-six) -/

section AlignedSquareLocalPole610

variable {k : Type*} [Field k] [CharZero k]

local instance alignedSquareLocalPoleHahnCharZero610 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-- Per-order head obstruction.  If `h₀ⁿ ρ` is polynomial for `n ≠ 0`
and `ρ'` is the simple pole `C j / h₀`, then the exponent-`-n` Hahn
coefficient of `ρ` vanishes, so the numerator evaluates to zero at the
linear root.  The relevant derivative coefficient is at exponent
`-(n+1)`, which is distinct from `-1`. -/
theorem alignedSquare_localLinearPole_head_eval_zero610
    (n : ℕ) (hn : n ≠ 0) (a j : k) (h0 A0 : k[X]) (rho : RatFunc k)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear : algebraMap k[X] (RatFunc k) A0 =
      (algebraMap k[X] (RatFunc k) h0) ^ n * rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    A0.eval a = 0 := by
  obtain ⟨c, hc, hsingle, hscaleDeriv⟩ :=
    ratFuncAtHahn68_linearRoot_single_deriv h0 a hdegree hroot
  have hrhoBoundary := localHahn_coeff_neg_of_cleared a c h0 A0 rho n hc
    hsingle hclear
  have hderivBoundary := localHahn_deriv_coeff_neg_succ_of_cleared
    a c h0 A0 rho n hc hsingle hscaleDeriv hclear
  have hmapped := congrArg (ratFuncAtHahn46 a) hderiv
  have hne : (-(n : ℚ) - 1) ≠ -(1 : ℚ) := by
    intro h
    have : -(n : ℚ) = 0 := by linear_combination h
    exact hn (Nat.cast_eq_zero.mp (neg_eq_zero.mp this))
  have hderivFar :
      (ratFuncAtHahn46 a (Differential.deriv rho)).coeff
        (-(n : ℚ) - 1) = 0 := by
    have hcoeff := congrArg
      (fun z : HahnSeries ℚ k ↦ z.coeff (-(n : ℚ) - 1)) hmapped
    simpa only [div_eq_mul_inv, map_mul, map_inv₀, ratFuncAtHahn46_C,
      hsingle, HahnSeries.inv_single, HahnSeries.C_mul_eq_smul,
      HahnSeries.coeff_smul, HahnSeries.coeff_single_of_ne hne,
      smul_zero] using hcoeff
  have hrhoZero : (ratFuncAtHahn46 a rho).coeff (-(n : ℚ)) = 0 := by
    have hnC : (n : k) ≠ 0 := Nat.cast_ne_zero.mpr hn
    rw [hderivFar, neg_mul] at hderivBoundary
    have hprod :
        (n : k) * (ratFuncAtHahn46 a rho).coeff (-(n : ℚ)) = 0 :=
      neg_eq_zero.mp hderivBoundary.symm
    exact (mul_eq_zero.mp hprod).resolve_left hnC
  rw [hrhoZero] at hrhoBoundary
  have hcinv : (c ^ n)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero n hc)
  exact (mul_eq_zero.mp hrhoBoundary.symm).resolve_left hcinv

/-- Order-`21` specialisation matching the MixedPair remaining pole. -/
theorem alignedSquare_poleTwentyOne_head_eval_zero610
    (a j : k) (h0 A0 : k[X]) (rho : RatFunc k)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear : algebraMap k[X] (RatFunc k) A0 =
      (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
        rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    A0.eval a = 0 :=
  alignedSquare_localLinearPole_head_eval_zero610
    alignedSquareRemainingPole610 (by decide) a j h0 A0 rho hdegree
    hroot hclear hderiv

/-- If the remaining order-`21` numerator is the MixedPair jet quotient,
the obstruction forces the base-order head to vanish at `a`. -/
theorem alignedSquare_poleTwentyOne_baseHead_eval_zero610
    (a j : k) (h0 Q : k[X]) (rho : RatFunc k)
    (w1 b8 : k)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hQ : Q.eval a = alignedSquareBaseHead610 b8 w1)
    (hclear : algebraMap k[X] (RatFunc k) Q =
      (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
        rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    alignedSquareBaseHead610 b8 w1 = 0 := by
  have hA0 :=
    alignedSquare_poleTwentyOne_head_eval_zero610 a j h0 Q rho hdegree
      hroot hclear hderiv
  exact hQ.symm.trans hA0

/-- On `w₁(a) ≠ 0` the order-`21` obstruction forces `q₈(a) = 0`.
This is a new `q`-side peel, not a Keller collision. -/
theorem alignedSquare_poleTwentyOne_q8_eval_zero610
    (a j : k) (h0 Q : k[X]) (rho : RatFunc k)
    (w1 b8 : k)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hw1 : w1 ≠ 0)
    (hQ : Q.eval a = alignedSquareBaseHead610 b8 w1)
    (hclear : algebraMap k[X] (RatFunc k) Q =
      (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
        rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    b8 = 0 :=
  alignedSquareBaseHead610_q8_of_w1_ne_zero b8 w1 hw1
    (alignedSquare_poleTwentyOne_baseHead_eval_zero610 a j h0 Q rho w1
      b8 hdegree hroot hQ hclear hderiv)

end AlignedSquareLocalPole610

#print axioms alignedSquare_localLinearPole_head_eval_zero610
#print axioms alignedSquare_poleTwentyOne_head_eval_zero610
#print axioms alignedSquare_poleTwentyOne_baseHead_eval_zero610
#print axioms alignedSquare_poleTwentyOne_q8_eval_zero610

end Max11DegreeRoutes
