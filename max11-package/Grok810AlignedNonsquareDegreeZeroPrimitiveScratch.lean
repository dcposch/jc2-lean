import Grok610AlignedNonsquareDegreeZeroPrimitiveScratch
import Grok810AlignedSquareSourceWrapperScratch

/-! # Degree-zero primitive on the `(8,10)` aligned-nonsquare quadratic packet

Untracked working note. No tracked file was edited.

Target Prop: `PlaneKeller810AlignedNonsquareExclusion`
(`Grok810RemainingAlignedChambersScratch.lean:37`).  Model: the `(6,10)`
nonsquare route in `Grok610AlignedNonsquareDegreeZeroPrimitiveScratch`
(tracked, green).  The polynomial obstruction
`quadraticCoreOde_no_polynomial_solution610` is imported from that file:
it is generic in `H` and `j` (`H.natDegree = 2`, `j ≠ 0`).

Parents (tracked, green):
`Grok810DegreeZeroPrimitiveScratch` (`rhoResidual810`, weight 17) and
`rhoResidual810_deriv_eq_constant_of_monic_differentialJacobian`
(`:376`, stated over any `Field F` with an explicit `Derivation`).
Affine chain rule
`differentialJacobian_affineDepress_sourceToQuadratic68`
(`LowScale68ScaleTwoAlignedNonsquareBridge.lean:117`) is stated for
arbitrary `p q`, so it applies to `(8,10)`.
`alignedSquareL_eq_zero810` (`Grok810AlignedSquareSourceWrapperScratch`)
forces `L = 0` on the aligned face `5 a₇ h² = 4 b₉` at `λ = 0`.

Over `F = k(x)(√H) = AdjoinRoot (alignedQuadraticPolynomial46 H)` with
`quadraticDerivation46 H`:

1. the bracket via the generic affine chain rule;
2. `d ρ = j / √H` from the weight-seventeen primitive, with `L = 0`;
3. deck-odd part `ρ − σρ = Q · √H`;
4. transport `2 H Q' + Q H' = 4 j`;
5. the imported polynomial lemma, giving `False` for `j ≠ 0`.

Landed: `planeKeller810AlignedNonsquareExclusion_closed`, and the
conditional
`planeKeller810AlignedFaceExclusion_of_squareChamber`.  The aligned
square chamber (lanes C/T/Z, `Grok810AlignedSquareClearedNumeratorScratch`)
is not closed here.  Scale zero and the nonzero first-face remain
explicit premises.

FLAG: 810 ALIGNED-NONSQUARE CLOSED

No `sorry`, no new axioms, no finite-root shortcut, no closure
overclaim.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-! ## Quadratic field: derivative, odd descent, ODE -/

section AlignedNonsquarePrimitiveField810

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

local notation "F810" => AdjoinRoot (alignedQuadraticPolynomial46 H)

local instance quadraticPrimitiveCharZero810 : CharZero F810 :=
  charZero_of_injective_ringHom (algebraMap (RatFunc k) F810).injective

/-- Affine centre of the aligned `(8,10)` depression in `k(x)(√H)`. -/
def alignedNonsquareDepressionR810 (p : k[X][X]) : F810 :=
  octicDepressionR810
    (AdjoinRoot.root (alignedQuadraticPolynomial46 H))
    (quadraticCoefficientMap46 H (p.coeff 7))

/-- Depressed octic of an `(8,10)` source in the quadratic field. -/
def alignedNonsquareDepressedOctic810 (p : k[X][X]) : F810[X] :=
  affineDepress68
    (AdjoinRoot.root (alignedQuadraticPolynomial46 H))
    (alignedNonsquareDepressionR810 (H := H) p)
    (sourceToQuadratic46 H p)

/-- Depressed decic of an `(8,10)` source in the quadratic field. -/
def alignedNonsquareDepressedDecic810 (p q : k[X][X]) : F810[X] :=
  affineDepress68
    (AdjoinRoot.root (alignedQuadraticPolynomial46 H))
    (alignedNonsquareDepressionR810 (H := H) p)
    (sourceToQuadratic46 H q)

/-- Source-facing weight-seventeen primitive of an aligned nonsquare
`(8,10)` pair. -/
def alignedNonsquareDegreeZeroPrimitive810 (p q : k[X][X]) : F810 :=
  let f := alignedNonsquareDepressedOctic810 (H := H) p
  let g := alignedNonsquareDepressedDecic810 (H := H) p q
  rhoResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
    (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
    (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
    (g.coeff 3) (g.coeff 2) (g.coeff 1)

theorem alignedNonsquareDepressedOctic810_eq_raw
    (p : k[X][X]) (hp : p.natDegree = 8) (hp8 : p.coeff 8 = H ^ 4) :
    alignedNonsquareDepressedOctic810 (H := H) p =
      depressedOctic68
        (depressedL68
          (AdjoinRoot.root (alignedQuadraticPolynomial46 H))
          (alignedNonsquareDepressionR810 (H := H) p)
          (quadraticCoefficientMap46 H (p.coeff 7)))
        (depressedP68
          (AdjoinRoot.root (alignedQuadraticPolynomial46 H))
          (alignedNonsquareDepressionR810 (H := H) p)
          (quadraticCoefficientMap46 H (p.coeff 7))
          (quadraticCoefficientMap46 H (p.coeff 6)))
        (depressedQ68
          (AdjoinRoot.root (alignedQuadraticPolynomial46 H))
          (alignedNonsquareDepressionR810 (H := H) p)
          (quadraticCoefficientMap46 H (p.coeff 7))
          (quadraticCoefficientMap46 H (p.coeff 6))
          (quadraticCoefficientMap46 H (p.coeff 5)))
        (depressedR68
          (AdjoinRoot.root (alignedQuadraticPolynomial46 H))
          (alignedNonsquareDepressionR810 (H := H) p)
          (quadraticCoefficientMap46 H (p.coeff 7))
          (quadraticCoefficientMap46 H (p.coeff 6))
          (quadraticCoefficientMap46 H (p.coeff 5))
          (quadraticCoefficientMap46 H (p.coeff 4)))
        (depressedS68
          (AdjoinRoot.root (alignedQuadraticPolynomial46 H))
          (alignedNonsquareDepressionR810 (H := H) p)
          (quadraticCoefficientMap46 H (p.coeff 7))
          (quadraticCoefficientMap46 H (p.coeff 6))
          (quadraticCoefficientMap46 H (p.coeff 5))
          (quadraticCoefficientMap46 H (p.coeff 4))
          (quadraticCoefficientMap46 H (p.coeff 3)))
        (depressedT68
          (AdjoinRoot.root (alignedQuadraticPolynomial46 H))
          (alignedNonsquareDepressionR810 (H := H) p)
          (quadraticCoefficientMap46 H (p.coeff 7))
          (quadraticCoefficientMap46 H (p.coeff 6))
          (quadraticCoefficientMap46 H (p.coeff 5))
          (quadraticCoefficientMap46 H (p.coeff 4))
          (quadraticCoefficientMap46 H (p.coeff 3))
          (quadraticCoefficientMap46 H (p.coeff 2)))
        (depressedU68
          (AdjoinRoot.root (alignedQuadraticPolynomial46 H))
          (alignedNonsquareDepressionR810 (H := H) p)
          (quadraticCoefficientMap46 H (p.coeff 7))
          (quadraticCoefficientMap46 H (p.coeff 6))
          (quadraticCoefficientMap46 H (p.coeff 5))
          (quadraticCoefficientMap46 H (p.coeff 4))
          (quadraticCoefficientMap46 H (p.coeff 3))
          (quadraticCoefficientMap46 H (p.coeff 2))
          (quadraticCoefficientMap46 H (p.coeff 1)))
        (depressedV68
          (AdjoinRoot.root (alignedQuadraticPolynomial46 H))
          (alignedNonsquareDepressionR810 (H := H) p)
          (quadraticCoefficientMap46 H (p.coeff 7))
          (quadraticCoefficientMap46 H (p.coeff 6))
          (quadraticCoefficientMap46 H (p.coeff 5))
          (quadraticCoefficientMap46 H (p.coeff 4))
          (quadraticCoefficientMap46 H (p.coeff 3))
          (quadraticCoefficientMap46 H (p.coeff 2))
          (quadraticCoefficientMap46 H (p.coeff 1))
          (quadraticCoefficientMap46 H (p.coeff 0))) := by
  let h : F810 := AdjoinRoot.root (alignedQuadraticPolynomial46 H)
  have hh : h ≠ 0 := alignedNonsquareScale_ne_zero610 (H := H)
  have hpTop : quadraticCoefficientMap46 H (p.coeff 8) = h ^ 8 := by
    rw [hp8, map_pow, ← alignedNonsquareRoot_sq_eq_map610 (H := H)]
    ring
  have hraw := sourceToQuadratic68_eq_rawOctic (H := H) p h hp hpTop
  rw [alignedNonsquareDepressedOctic810, hraw]
  exact affineDepress_rawOctic68 h
    (alignedNonsquareDepressionR810 (H := H) p)
    (quadraticCoefficientMap46 H (p.coeff 7))
    (quadraticCoefficientMap46 H (p.coeff 6))
    (quadraticCoefficientMap46 H (p.coeff 5))
    (quadraticCoefficientMap46 H (p.coeff 4))
    (quadraticCoefficientMap46 H (p.coeff 3))
    (quadraticCoefficientMap46 H (p.coeff 2))
    (quadraticCoefficientMap46 H (p.coeff 1))
    (quadraticCoefficientMap46 H (p.coeff 0)) hh

theorem alignedNonsquareDepressedDecic810_high
    (p q : k[X][X]) (hq : q.natDegree = 10) (hq10 : q.coeff 10 = H ^ 5) :
    (alignedNonsquareDepressedDecic810 (H := H) p q).coeff 10 = 1 ∧
      (alignedNonsquareDepressedDecic810 (H := H) p q).coeff 9 =
        depressedL810
          (AdjoinRoot.root (alignedQuadraticPolynomial46 H))
          (alignedNonsquareDepressionR810 (H := H) p)
          (quadraticCoefficientMap46 H (q.coeff 9)) ∧
      (∀ n, 10 < n →
        (alignedNonsquareDepressedDecic810 (H := H) p q).coeff n = 0) := by
  let h : F810 := AdjoinRoot.root (alignedQuadraticPolynomial46 H)
  let r : F810 := alignedNonsquareDepressionR810 (H := H) p
  let src := sourceToQuadratic46 H q
  have hh : h ≠ 0 := alignedNonsquareScale_ne_zero610 (H := H)
  have hp10 : src.coeff 10 = h ^ 10 := by
    simp only [src, sourceToQuadratic46, coeff_map, hq10, map_pow]
    rw [← alignedNonsquareRoot_sq_eq_map610 (H := H)]
    ring
  have hp_high : ∀ n, 10 < n → src.coeff n = 0 := by
    intro n hn
    simp [src, sourceToQuadratic46, coeff_map,
      Polynomial.coeff_eq_zero_of_natDegree_lt
        (show q.natDegree < n by omega)]
  obtain ⟨hg10, hg9, hg_high⟩ :=
    affineDepress_degreeTen_highCoeffs610 src h r hh hp10 hp_high
  have hdef : alignedNonsquareDepressedDecic810 (H := H) p q =
      affineDepress68 h r src := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hdef]
    exact hg10
  · have hL :
        -10 * r + src.coeff 9 / h ^ 9 =
          depressedL810 h r (quadraticCoefficientMap46 H (q.coeff 9)) := by
      simp [depressedL810, src, sourceToQuadratic46, coeff_map]
    rw [hdef, hg9, hL]
  · intro n hn
    rw [hdef]
    exact hg_high n hn

theorem alignedNonsquareL_eq_zero810
    (p q : k[X][X])
    (hq : q.natDegree = 10) (hq10 : q.coeff 10 = H ^ 5)
    (haligned : (5 : k[X]) * p.coeff 7 * H -
      (4 : k[X]) * q.coeff 9 = 0) :
    (alignedNonsquareDepressedDecic810 (H := H) p q).coeff 9 = 0 := by
  let h : F810 := AdjoinRoot.root (alignedQuadraticPolynomial46 H)
  let a7 : F810 := quadraticCoefficientMap46 H (p.coeff 7)
  let b9 : F810 := quadraticCoefficientMap46 H (q.coeff 9)
  have hh : h ≠ 0 := alignedNonsquareScale_ne_zero610 (H := H)
  have hNrat : (5 : F810) * a7 * h ^ 2 - (4 : F810) * b9 = 0 := by
    have hmapped := congrArg (quadraticCoefficientMap46 H) haligned
    simp only [map_sub, map_mul, map_ofNat, map_zero] at hmapped
    have hH : quadraticCoefficientMap46 H H = h ^ 2 :=
      (alignedNonsquareRoot_sq_eq_map610 (H := H)).symm
    simpa [a7, b9, hH] using hmapped
  have hLval :
      depressedL810 h (octicDepressionR810 h a7) b9 = 0 :=
    alignedSquareL_eq_zero810 h a7 b9 hh hNrat
  have hgHigh :=
    alignedNonsquareDepressedDecic810_high (H := H) p q hq hq10
  have hg9 :
      (alignedNonsquareDepressedDecic810 (H := H) p q).coeff 9 =
        depressedL810 h (alignedNonsquareDepressionR810 (H := H) p) b9 :=
    hgHigh.2.1
  have hr : alignedNonsquareDepressionR810 (H := H) p =
      octicDepressionR810 h a7 := rfl
  rw [hg9, hr, hLval]

/-- Step 1: the monic bridge realises `d ρ = j / √H`. -/
theorem alignedNonsquareDegreeZeroPrimitive810_deriv
    (p q : k[X][X]) (j : k)
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (haligned : (5 : k[X]) * p.coeff 7 * H -
      (4 : k[X]) * q.coeff 9 = 0)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q = C (C j)) :
    quadraticDerivation46 H
        (alignedNonsquareDegreeZeroPrimitive810 (H := H) p q) =
      algebraMap k F810 j /
        AdjoinRoot.root (alignedQuadraticPolynomial46 H) := by
  let h : F810 := AdjoinRoot.root (alignedQuadraticPolynomial46 H)
  let r : F810 := alignedNonsquareDepressionR810 (H := H) p
  let f := alignedNonsquareDepressedOctic810 (H := H) p
  let g := alignedNonsquareDepressedDecic810 (H := H) p q
  have hh : h ≠ 0 := alignedNonsquareScale_ne_zero610 (H := H)
  have hfEq :=
    alignedNonsquareDepressedOctic810_eq_raw (H := H) p hp hp8
  have hgHigh :=
    alignedNonsquareDepressedDecic810_high (H := H) p q hq hq10
  have hL0 : depressedL68 h r
      (quadraticCoefficientMap46 H (p.coeff 7)) = 0 :=
    depressedL68_eq_zero_of_octicCenter h
      (quadraticCoefficientMap46 H (p.coeff 7)) hh
  have hf8 : f.coeff 8 = 1 := by
    dsimp [f]
    rw [hfEq, coeff_depressedOctic68_eight]
  have hf7 : f.coeff 7 = 0 := by
    dsimp [f]
    rw [hfEq, coeff_depressedOctic68_seven, hL0]
  have hf_high : ∀ n, 8 < n → f.coeff n = 0 := by
    intro n hn
    dsimp [f]
    rw [hfEq, coeff_depressedOctic68_of_gt_eight _ _ _ _ _ _ _ _ hn]
  have hg10 : g.coeff 10 = 1 := by
    dsimp [g]
    exact hgHigh.1
  have hg_high : ∀ n, 10 < n → g.coeff n = 0 := by
    intro n hn
    dsimp [g]
    exact hgHigh.2.2 n hn
  have hLval : g.coeff 9 = 0 := by
    dsimp [g]
    exact alignedNonsquareL_eq_zero810 (H := H) p q hq hq10 haligned
  have hL : quadraticDerivation46 H (g.coeff 9) = 0 := by
    rw [hLval]
    simp [quadraticDerivation46_apply]
  have hbracket :=
    differentialJacobian_affineDepress_sourceToQuadratic68 (H := H)
      p q j h r hh hD
  have hjac :
      differentialJacobian (quadraticDerivation46 H) f g =
        C (algebraMap k F810 j / h) := by
    simpa [f, g, alignedNonsquareDepressedOctic810,
      alignedNonsquareDepressedDecic810] using hbracket
  simpa [alignedNonsquareDegreeZeroPrimitive810, f, g] using
    rhoResidual810_deriv_eq_constant_of_monic_differentialJacobian
      (quadraticDerivation46 H) f g (algebraMap k F810 j / h)
      hf_high hf8 hf7 hg_high hg10 hL hjac

/-- Odd part of the weight-seventeen primitive: `ρ − σρ` is deck-odd. -/
theorem alignedNonsquareDegreeZeroPrimitive810_oddPart
    (p q : k[X][X]) :
    alignedQuadraticDeck46 H
        (alignedNonsquareDegreeZeroPrimitive810 (H := H) p q -
          alignedQuadraticDeck46 H
            (alignedNonsquareDegreeZeroPrimitive810 (H := H) p q)) =
      - (alignedNonsquareDegreeZeroPrimitive810 (H := H) p q -
          alignedQuadraticDeck46 H
            (alignedNonsquareDegreeZeroPrimitive810 (H := H) p q)) := by
  simp only [map_sub, alignedQuadraticDeck46_involutive610]
  ring

/-- Odd descent of the odd part: `ρ − σρ = Q · √H`. -/
theorem alignedNonsquareDegreeZeroPrimitive810_eq_mul_root
    (p q : k[X][X]) :
    ∃ Q : RatFunc k,
      alignedNonsquareDegreeZeroPrimitive810 (H := H) p q -
          alignedQuadraticDeck46 H
            (alignedNonsquareDegreeZeroPrimitive810 (H := H) p q) =
        algebraMap (RatFunc k) F810 Q *
          AdjoinRoot.root (alignedQuadraticPolynomial46 H) :=
  alignedQuadratic_odd_eq_mul_root68 (H := H)
    (alignedNonsquareDegreeZeroPrimitive810 (H := H) p q -
      alignedQuadraticDeck46 H
        (alignedNonsquareDegreeZeroPrimitive810 (H := H) p q))
    (alignedNonsquareDegreeZeroPrimitive810_oddPart (H := H) p q)

/-- Transport `d(Q · √H) = 2 j / √H` for the odd part. -/
theorem alignedNonsquareDegreeZeroPrimitive810_ratFuncOde
    (p q : k[X][X]) (j : k) (Q : RatFunc k)
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (haligned : (5 : k[X]) * p.coeff 7 * H -
      (4 : k[X]) * q.coeff 9 = 0)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q = C (C j))
    (hQ : alignedNonsquareDegreeZeroPrimitive810 (H := H) p q -
        alignedQuadraticDeck46 H
          (alignedNonsquareDegreeZeroPrimitive810 (H := H) p q) =
      algebraMap (RatFunc k) F810 Q *
        AdjoinRoot.root (alignedQuadraticPolynomial46 H)) :
    (2 : RatFunc k) * algebraMap k[X] (RatFunc k) H *
        Differential.deriv Q +
      Q * algebraMap k[X] (RatFunc k) H.derivative =
      (4 : RatFunc k) * algebraMap k (RatFunc k) j := by
  set rt := AdjoinRoot.root (alignedQuadraticPolynomial46 H)
  have hrt : rt ≠ 0 := alignedNonsquareScale_ne_zero610 (H := H)
  have hφ : Function.Injective (algebraMap (RatFunc k) F810) :=
    (algebraMap (RatFunc k) F810).injective
  have hsq := alignedQuadraticRoot_sq46 H
  have hderρ := alignedNonsquareDegreeZeroPrimitive810_deriv (H := H)
    p q j hp hq hp8 hq10 haligned hD
  have hder :
      quadraticDerivation46 H
          (alignedNonsquareDegreeZeroPrimitive810 (H := H) p q -
            alignedQuadraticDeck46 H
              (alignedNonsquareDegreeZeroPrimitive810 (H := H) p q)) =
        (2 : F810) * algebraMap k F810 j / rt := by
    have hcomm := alignedQuadraticDeck46_deriv610 (H := H)
      (alignedNonsquareDegreeZeroPrimitive810 (H := H) p q)
    have hdeckpole :
        alignedQuadraticDeck46 H (algebraMap k F810 j / rt) =
          -(algebraMap k F810 j / rt) := by
      have hmap :
          alignedQuadraticDeck46 H (algebraMap k F810 j / rt) =
            algebraMap k F810 j / alignedQuadraticDeck46 H rt := by
        simp only [map_div₀, alignedQuadraticDeck46_ground]
      rw [hmap, alignedQuadraticDeck46_root, div_neg]
    have hsub :=
      map_sub (quadraticDerivation46 H)
        (alignedNonsquareDegreeZeroPrimitive810 (H := H) p q)
        (alignedQuadraticDeck46 H
          (alignedNonsquareDegreeZeroPrimitive810 (H := H) p q))
    rw [hsub, hcomm, hderρ, hdeckpole]
    ring
  have hroot := quadraticDerivation46_root68 (H := H)
  have hQder := quadraticDerivation46_algebraMap_ratFunc68 H Q
  have hleibniz :
      quadraticDerivation46 H (algebraMap (RatFunc k) F810 Q * rt) =
        algebraMap (RatFunc k) F810 (Differential.deriv Q) * rt +
          algebraMap (RatFunc k) F810 Q *
            quadraticDerivation46 H rt := by
    have hmul := Derivation.leibniz (quadraticDerivation46 H)
      (algebraMap (RatFunc k) F810 Q) rt
    simp only [smul_eq_mul] at hmul
    rw [hmul, hQder]
    ring
  have hprim :
      quadraticDerivation46 H (algebraMap (RatFunc k) F810 Q * rt) =
        (2 : F810) * algebraMap k F810 j / rt := by
    rw [← hQ]
    exact hder
  have hsum :
      algebraMap (RatFunc k) F810 (Differential.deriv Q) * rt +
        algebraMap (RatFunc k) F810 Q *
          (algebraMap (RatFunc k) F810
            (algebraMap k[X] (RatFunc k) H.derivative) / (2 * rt)) =
        (2 : F810) * algebraMap k F810 j / rt := by
    have h := hleibniz.symm.trans hprim
    rw [hroot] at h
    exact h
  have h2ne : (2 : F810) ≠ 0 := two_ne_zero
  have h2rt : (2 : F810) * rt ≠ 0 := mul_ne_zero h2ne hrt
  have hcleared :
      (2 : F810) * algebraMap (RatFunc k) F810 (Differential.deriv Q) *
          (rt * rt) +
        algebraMap (RatFunc k) F810 Q *
          algebraMap (RatFunc k) F810
            (algebraMap k[X] (RatFunc k) H.derivative) =
        (4 : F810) * algebraMap k F810 j := by
    have := congrArg (fun z : F810 => (2 * rt) * z) hsum
    field_simp [h2ne, hrt, h2rt] at this
    linear_combination this
  have hleft :
      (2 : F810) * algebraMap (RatFunc k) F810 (Differential.deriv Q) *
          (rt * rt) +
        algebraMap (RatFunc k) F810 Q *
          algebraMap (RatFunc k) F810
            (algebraMap k[X] (RatFunc k) H.derivative) =
        algebraMap (RatFunc k) F810
          ((2 : RatFunc k) * algebraMap k[X] (RatFunc k) H *
            Differential.deriv Q +
            Q * algebraMap k[X] (RatFunc k) H.derivative) := by
    have hrt2 : rt * rt =
        algebraMap (RatFunc k) F810 (algebraMap k[X] (RatFunc k) H) := by
      simpa [pow_two] using hsq
    rw [hrt2]
    simp only [map_add, map_mul, map_ofNat]
    ring
  have hright :
      (4 : F810) * algebraMap k F810 j =
        algebraMap (RatFunc k) F810
          ((4 : RatFunc k) * algebraMap k (RatFunc k) j) := by
    rw [IsScalarTower.algebraMap_apply k (RatFunc k) F810, map_mul, map_ofNat]
  exact hφ (by rw [← hleft, hcleared, hright])

/-- The odd descent of the weight-seventeen primitive yields a polynomial
solution of the cleared ODE. -/
theorem alignedNonsquareDegreeZeroPrimitive810_clearedOde
    (p q : k[X][X]) (j : k)
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (haligned : (5 : k[X]) * p.coeff 7 * H -
      (4 : k[X]) * q.coeff 9 = 0)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q = C (C j)) :
    ∃ n d : k[X], d ≠ 0 ∧
      quadraticOdeCleared610 H n d (2 * j) := by
  obtain ⟨Q, hQ⟩ :=
    alignedNonsquareDegreeZeroPrimitive810_eq_mul_root (H := H) p q
  have hode := alignedNonsquareDegreeZeroPrimitive810_ratFuncOde
    (H := H) p q j Q hp hq hp8 hq10 haligned hD hQ
  have hode' :
      (2 : RatFunc k) * algebraMap k[X] (RatFunc k) H *
          Differential.deriv Q +
        Q * algebraMap k[X] (RatFunc k) H.derivative =
        (2 : RatFunc k) * algebraMap k (RatFunc k) (2 * j) := by
    have hrhs : (4 : RatFunc k) * algebraMap k (RatFunc k) j =
        (2 : RatFunc k) * algebraMap k (RatFunc k) (2 * j) := by
      rw [map_mul, map_ofNat]
      ring
    rw [hode, hrhs]
  have hide := ratFuncOde_to_polynomial610 (H := H) Q (2 * j) hode'
  exact ⟨Q.num, Q.denom, Q.denom_ne_zero, hide⟩

/-- Source-facing ODE kill on a quadratic nonsquare core. -/
theorem alignedNonsquareDegreeZeroPrimitive810_false
    (p q : k[X][X]) (j : k)
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (haligned : (5 : k[X]) * p.coeff 7 * H -
      (4 : k[X]) * q.coeff 9 = 0)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q = C (C j))
    (hj : j ≠ 0) (hdeg : H.natDegree = 2) : False := by
  obtain ⟨n, d, hd, hide⟩ :=
    alignedNonsquareDegreeZeroPrimitive810_clearedOde (H := H)
      p q j hp hq hp8 hq10 haligned hD
  have h2j : (2 : k) * j ≠ 0 := mul_ne_zero (by norm_num) hj
  exact quadraticCoreOde_no_polynomial_solution610 H n d (2 * j) hdeg hd h2j hide

end AlignedNonsquarePrimitiveField810

/-! ## Chamber exclusion and aligned-face conditional -/

section AlignedNonsquareChamber810

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- **CLOSED.** The remaining aligned-nonsquare exclusion of the
normalized `(8,10)` scale-two route. -/
theorem planeKeller810AlignedNonsquareExclusion_closed :
    PlaneKeller810AlignedNonsquareExclusion (K := K) := by
  intro P Q H hsource hnonsquare hN
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  letI : NonsquarePolynomial46 H := ⟨hnonsquare⟩
  rcases hsource with
    ⟨_hHne, hHdegree, hPdegree, hQdegree, hp8src, hq10src, hKeller⟩
  have hp : p.natDegree = 8 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  have hp8 : p.coeff 8 = H ^ 4 := by simpa only [p] using hp8src
  have hq10 : q.coeff 10 = H ^ 5 := by simpa only [q] using hq10src
  have haligned : (5 : K[X]) * p.coeff 7 * H -
      (4 : K[X]) * q.coeff 9 = 0 := by
    simpa only [p, q] using hN
  obtain ⟨j, hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q = C (C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hjac
  exact alignedNonsquareDegreeZeroPrimitive810_false (H := H)
    p q j hp hq hp8 hq10 haligned hD hj hHdegree

/-- The aligned first-face exclusion, modulo the remaining aligned-square
chamber.  Lanes C/T/Z (`Grok810AlignedSquareClearedNumeratorScratch`) are
not discharged here. -/
theorem planeKeller810AlignedFaceExclusion_of_squareChamber
    (hsquare : PlaneKeller810AlignedSquareExclusion (K := K)) :
    PlaneKeller810AlignedFaceExclusion (K := K) :=
  planeKeller810AlignedFaceExclusion_of_chambers hsquare
    planeKeller810AlignedNonsquareExclusion_closed

end AlignedNonsquareChamber810

#print axioms alignedNonsquareDegreeZeroPrimitive810_deriv
#print axioms alignedNonsquareDegreeZeroPrimitive810_eq_mul_root
#print axioms alignedNonsquareDegreeZeroPrimitive810_false
#print axioms planeKeller810AlignedNonsquareExclusion_closed
#print axioms planeKeller810AlignedFaceExclusion_of_squareChamber

end Max11DegreeRoutes
