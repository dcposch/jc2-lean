import Grok810DegreeZeroPrimitiveScratch
import Grok810DegreeZeroSourceWrapperScratch
import Grok810RemainingAlignedChambersScratch

/-! # Aligned-square source wrapper for the `(8,10)` weight-seventeen primitive

Lane W of `Grok810AlignedFaceTowerPlanScratch.md`.  Untracked working
note.  No tracked file was edited.

Parents (tracked, green):

* `Grok810DegreeZeroSourceWrapperScratch`
  (`sourceRhoResidual810_deriv_eq_simplePole_of_source`, which does
  **not** assume `lambda ≠ 0` and does **not** assume `h0` linear);
* `Grok810DegreeZeroPrimitiveScratch` (`rhoResidual810`);
* `Grok810RemainingAlignedChambersScratch`
  (`PlaneKeller810AlignedSquareExclusion`,
  `alignedSquare810_h0_natDegree_eq_one`).

The `(8,10)` aligned face `N = 0` on the square chamber `H = h0^2`
closes by the same degree-zero primitive as the nonzero face, at
`lambda = 0`, with **no peel**.  Depression step is
`octicDepressionR810 h a7 = a7 / (8 h^7)` (centre depth `7`); weight
is `17`; clearing is `7 · 17 = 119`; base order is `0`; remaining pole
is `119`; native ceiling is `119`.  These are **not** the nonzero-face
Pi-tower numbers `102 / 17 / 118`.

On `N = 0` the depressed `z⁹` coefficient is the field constant
`L = 0` (`depressedL810_eq_of_ninthPower` at `lambda = 0`; cf.
`alignedSquareL_eq_zero610`).  AffineBracket still divides by exactly
one power of `h`, so `ρ' = C(j) / h0` is a genuine simple pole.

The source-facing form unpacks `Normalized810LeadingCoreSource P Q H 2`
as in `Grok810RouteAdapterScratch` and takes `j ≠ 0` from
`bivariateJacobian_eq_C_of_keller`.  No clearing identity, pole-tower
order, or chamber closure is claimed.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## Bookkeeping: weight, native clearing, no-peel remaining pole -/

/-- Weighted degree of the `(8,10)` degree-zero primitive. -/
def alignedSquarePrimitiveWeight810 : ℕ := 17

/-- Source `h`-adic step of one octic depression depth: the centre is
`a₇/(8 h⁷)`. -/
def alignedSquareCoordinateClearingStep810 : ℕ := 7

/-- Source-homogeneous clearing of a weight-`17` polynomial in
coordinates of denominator `h^{7d}`.  Instantiated from the same
primitive as the nonzero-face wrapper; not a claim that the aligned
vanishing order is `102`. -/
def alignedSquareSourceClearingPower810 : ℕ := 119

/-- Ordinary pole of `ρ'` supplied by AffineBracket: `ρ' = C(j)/h₀`. -/
def alignedSquareDerivativePoleOrder810 : ℕ := 1

/-- Lowest surviving power of `h` in the unpeeled aligned-square
numerator.  Not the nonzero-face Pi-tower base order `102`. -/
def alignedSquareBaseOrder810 : ℕ := 0

/-- Remaining pole of `ρ` with no peel: `119 - 0 = 119`.  Not the
nonzero-face remaining pole `17`. -/
def alignedSquareRemainingPole810 : ℕ := 119

/-- Native tower ceiling of the weight-seventeen primitive on the
aligned square (no peel). -/
def alignedSquareTowerCeiling810 : ℕ := 119

theorem alignedSquarePrimitiveWeight810_eq :
    alignedSquarePrimitiveWeight810 = 17 :=
  rfl

theorem alignedSquareCoordinateClearingStep810_eq :
    alignedSquareCoordinateClearingStep810 = 7 :=
  rfl

theorem alignedSquareSourceClearingPower810_eq :
    alignedSquareSourceClearingPower810 = 119 :=
  rfl

theorem alignedSquareDerivativePoleOrder810_eq :
    alignedSquareDerivativePoleOrder810 = 1 :=
  rfl

theorem alignedSquareBaseOrder810_eq :
    alignedSquareBaseOrder810 = 0 :=
  rfl

theorem alignedSquareRemainingPole810_eq :
    alignedSquareRemainingPole810 = 119 :=
  rfl

theorem alignedSquareTowerCeiling810_eq :
    alignedSquareTowerCeiling810 = 119 :=
  rfl

theorem alignedSquareSourceClearingPower810_eq_mul :
    alignedSquareSourceClearingPower810 =
      alignedSquareCoordinateClearingStep810 *
        alignedSquarePrimitiveWeight810 :=
  rfl

theorem alignedSquareRemainingPole810_eq_sub :
    alignedSquareRemainingPole810 =
      alignedSquareSourceClearingPower810 - alignedSquareBaseOrder810 :=
  rfl

theorem alignedSquareTowerCeiling810_eq_clearing :
    alignedSquareTowerCeiling810 = alignedSquareSourceClearingPower810 :=
  rfl

theorem alignedSquareBaseOrder810_ne_oneHundredTwo :
    alignedSquareBaseOrder810 ≠ 102 := by
  decide

theorem alignedSquareRemainingPole810_ne_seventeen :
    alignedSquareRemainingPole810 ≠ 17 := by
  decide

#print axioms alignedSquareSourceClearingPower810_eq_mul
#print axioms alignedSquareRemainingPole810_eq_sub
#print axioms alignedSquareBaseOrder810_ne_oneHundredTwo
#print axioms alignedSquareRemainingPole810_ne_seventeen

/-! ## Depressed `z⁹` coefficient on the aligned face -/

section AlignedSquareL810

variable {F : Type*} [Field F] [CharZero F]

/-- On the aligned face `5 a₇ h² = 4 b₉` the depressed decic `z⁹`
coefficient is the field constant `0`. -/
theorem alignedSquareL_eq_zero810
    (h a7 b9 : F) (hh : h ≠ 0)
    (hN : (5 : F) * a7 * h ^ 2 - (4 : F) * b9 = 0) :
    depressedL810 h (octicDepressionR810 h a7) b9 = 0 := by
  have hL := depressedL810_eq_of_ninthPower h a7 b9 (0 : F) hh
    (by simpa using hN)
  simpa using hL

end AlignedSquareL810

#print axioms alignedSquareL_eq_zero810

/-! ## Source primitive on the aligned depression -/

section AlignedSquareSourcePrimitive810

variable {F : Type*} [Field F] [CharZero F]

/-- The weight-seventeen primitive on the octic-decic depression of a
literal aligned `(8,10)` source.  The ninth-power scalar is specialised
to `λ = 0` only in the derivative lemma below; `b₉` is kept free, as
`alignedSquareSourcePrimitive610` does. -/
def alignedSquareSourcePrimitive810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b9 b8 b7 b6 b5 b4 b3 b2 b1 : F) : F :=
  sourceRhoResidual810 h a7 a6 a5 a4 a3 a2 a1 a0 b9 b8 b7 b6 b5 b4 b3
    b2 b1

end AlignedSquareSourcePrimitive810

/-! ## Affine source wrapper: `ρ' = C(j)/h₀` at `λ = 0` -/

section AlignedSquareSourceWrapper810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 800000000 in
/-- The weight-seventeen primitive, on a literal aligned `(8,10)`
source with square core `H = h₀²` and `N = 0`, has the ordinary
simple-pole derivative supplied by the affine source Jacobian.
AffineBracket divides by exactly one power of `h`, independently of
the inner degrees, and `N = 0` makes `L` a field constant, so the
derivative pole is `1`.  This is not the remaining pole `119` of `ρ`
itself, and it is not the nonzero-face remaining pole `17`. -/
theorem alignedSquarePrimitive810_deriv_eq_simplePole_of_source
    (p q : k[X][X]) (H h0 : k[X]) (j : k)
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 = 0)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j)) :
    Differential.deriv
        (alignedSquareSourcePrimitive810
          (algebraMap k[X] (RatFunc k) h0)
          (algebraMap k[X] (RatFunc k) (p.coeff 7))
          (algebraMap k[X] (RatFunc k) (p.coeff 6))
          (algebraMap k[X] (RatFunc k) (p.coeff 5))
          (algebraMap k[X] (RatFunc k) (p.coeff 4))
          (algebraMap k[X] (RatFunc k) (p.coeff 3))
          (algebraMap k[X] (RatFunc k) (p.coeff 2))
          (algebraMap k[X] (RatFunc k) (p.coeff 1))
          (algebraMap k[X] (RatFunc k) (p.coeff 0))
          (algebraMap k[X] (RatFunc k) (q.coeff 9))
          (algebraMap k[X] (RatFunc k) (q.coeff 8))
          (algebraMap k[X] (RatFunc k) (q.coeff 7))
          (algebraMap k[X] (RatFunc k) (q.coeff 6))
          (algebraMap k[X] (RatFunc k) (q.coeff 5))
          (algebraMap k[X] (RatFunc k) (q.coeff 4))
          (algebraMap k[X] (RatFunc k) (q.coeff 3))
          (algebraMap k[X] (RatFunc k) (q.coeff 2))
          (algebraMap k[X] (RatFunc k) (q.coeff 1))) =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0 := by
  simpa [alignedSquareSourcePrimitive810] using
    sourceRhoResidual810_deriv_eq_simplePole_of_source p q H h0 j
      (0 : k) hp hq hh0 hH hp8 hq10 (by simpa using haligned) hD

#print axioms alignedSquarePrimitive810_deriv_eq_simplePole_of_source

/-- Source-facing form of the aligned-square simple pole on a
normalized scale-two `(8,10)` source with square core `H = h₀²`.
Unpacks `Normalized810LeadingCoreSource` as in
`normalized810ScaleTwo_nonzeroFace_false_of_linearRootFalse`; the
residue `j ≠ 0` is the Keller constant from
`bivariateJacobian_eq_C_of_keller`.  The chamber is not claimed
empty. -/
theorem alignedSquarePrimitive810_deriv_eq_simplePole_of_normalizedSource
    {P Q : MvPolynomial (Fin 2) k} {H h0 : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 2)
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    ∃ j : k, j ≠ 0 ∧
      Differential.deriv
          (alignedSquareSourcePrimitive810
            (algebraMap k[X] (RatFunc k) h0)
            (algebraMap k[X] (RatFunc k) (p.coeff 7))
            (algebraMap k[X] (RatFunc k) (p.coeff 6))
            (algebraMap k[X] (RatFunc k) (p.coeff 5))
            (algebraMap k[X] (RatFunc k) (p.coeff 4))
            (algebraMap k[X] (RatFunc k) (p.coeff 3))
            (algebraMap k[X] (RatFunc k) (p.coeff 2))
            (algebraMap k[X] (RatFunc k) (p.coeff 1))
            (algebraMap k[X] (RatFunc k) (p.coeff 0))
            (algebraMap k[X] (RatFunc k) (q.coeff 9))
            (algebraMap k[X] (RatFunc k) (q.coeff 8))
            (algebraMap k[X] (RatFunc k) (q.coeff 7))
            (algebraMap k[X] (RatFunc k) (q.coeff 6))
            (algebraMap k[X] (RatFunc k) (q.coeff 5))
            (algebraMap k[X] (RatFunc k) (q.coeff 4))
            (algebraMap k[X] (RatFunc k) (q.coeff 3))
            (algebraMap k[X] (RatFunc k) (q.coeff 2))
            (algebraMap k[X] (RatFunc k) (q.coeff 1))) =
        RatFunc.C j / algebraMap k[X] (RatFunc k) h0 := by
  dsimp only at haligned
  rcases hsource with
    ⟨_hHne, _hHdegree, hPdegree, hQdegree, hp8, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
  have hp : p.natDegree = 8 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  have hp8' : p.coeff 8 = H ^ 4 := by simpa only [p] using hp8
  have hq10' : q.coeff 10 = H ^ 5 := by simpa only [q] using hq10
  have hN' : (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 = 0 := by
    simpa only [p, q] using haligned
  obtain ⟨j, hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hjac
  refine ⟨j, hj, ?_⟩
  simpa [p, q] using
    alignedSquarePrimitive810_deriv_eq_simplePole_of_source p q H h0 j
      hp hq hh0 hHsq hp8' hq10' hN' hD

#print axioms alignedSquarePrimitive810_deriv_eq_simplePole_of_normalizedSource

end AlignedSquareSourceWrapper810

end Max11DegreeRoutes
