import Grok410ScaleZeroRouteAdapterScratch
import Grok410ScaleTwoCascadeEndgameScratch
import Sol410ScaleTwoAlignedFinalKellerRowScratch
import Sol410ScaleTwoAlignedSquareClosureScratch
import Sol410ScaleTwoAlignedNonsquareTransverseEliminatedScratch

/-! # LEAF CLOSURE of the normalized `(4,10)` low-scale route

Untracked working note.  No tracked file was edited.

The scale-two discriminator splits every normalized `(4,10)` source into
the aligned face `N = 5 p₃ H³ - 2 q₉ = 0` and the nonzero face `N ≠ 0`.
The nonzero face was already emptied by
`normalized410ScaleTwo_nonzeroFace_false` (iota polar collapse, then the
supplied valuation exhaustion `h⁴ ∣ (h⁴)'`).  This file empties the
aligned face by the same two-step pattern — jet exhaustion, then a
valuation/degree kill — and composes the two faces with the committed
scale-zero adapter.

## Jet exhaustion

The Fable aligned tower (`Fable410ScaleTwoAlignedFaceScratch` through
`Fable410ScaleTwoAlignedEleventhFaceScratch`) consumes the degree-`11`
through degree-`1` Jacobian coefficients of a normalized aligned source
into the chamber-free first-integral ladder

`M = κ H⁴`, `M₄ = κ₃ H⁶`, `M₈ = κ₅ H⁹`, `M₁₂ = κ₇ H¹²`,
`M₁₆ = κ₉ H¹⁵`, `M₂₀ = κ₁₁ H¹⁸`

together with the odd-square companions.  The only remaining coefficient
is the degree-`0` Keller row `p₀' q₁ - p₁ q₀' = C j`, recorded on the
same source by `normalized410ScaleTwo_alignedFinalKellerRow`.  There is
no unused Jacobian coefficient below degree `0`.

## Valuation/degree kill

On that exhausted jet the square/nonsquare chambers are already closed,
with the original source and the original linear factor preserved:

* square chamber `H = h₀²`: after the complement limb and the `h₀ ∣ p₁`
  allocation are killed against the same Keller row, the surviving
  deep-divisor allocation `u = h₀² g₁`, `p₂ = h₀³ r₂` reduces the ninth
  quotient at the supplied root to `327680 p₁(root)³ = 0`, contradicting
  `p₁(root) ≠ 0` (`normalized410ScaleTwo_alignedSquare_false`);
* nonsquare chamber: every remaining transverse orientation contradicts
  the exact ninth row at a `g = 0` root
  (`normalized410ScaleTwo_alignedNonsquare_false`).

The aligned face is therefore empty.  Together with the nonzero-face
exclusion this discharges `PlaneKellerNormalized410ScaleTwoRoute`, and
the committed adapter `planeKellerNormalized410LowScaleRoute_of_scaleTwo`
upgrades that to the full normalized low-scale `(4,10)` route — the
`h410` premise of `Max11PlaneKellerGenerationWithFiveNormalizedLowScaleRoutes`.

No total-degree or twice-prime theorem is used.  No new axiom is
introduced.  No finite-root shortcut is taken: every kill is on the
supplied source, the supplied scale, and the supplied root of that scale.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## Exhausted aligned packet (twelfth jet plus the last Keller row) -/

section AlignedExhaustedPacket410

/-- Source-facing exhausted aligned packet: the twelfth-face first-integral
ladder together with the last Keller coefficient.  No unused Jacobian row
remains. -/
theorem normalized410ScaleTwo_alignedFace_exhaustedPacket
    {K : Type*} [Field K] [CharZero K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    (∃ κ κ₂ κ₃ κ₄ κ₅ κ₆ κ₇ κ₈ κ₉ κ₁₀ κ₁₁ : K,
      q.coeff 9 = Polynomial.C (5 / 2 : K) * p.coeff 3 * H ^ 3 ∧
        (8 : K[X]) * q.coeff 8 =
          H * ((15 : K[X]) * p.coeff 3 ^ 2 +
            (20 : K[X]) * p.coeff 2 * H ^ 2 +
            Polynomial.C κ * H ^ 3) ∧
        alignedThirdDefect410 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
            (q.coeff 7) κ ^ 2 = Polynomial.C κ₂ * H ^ 9 ∧
        alignedFourthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₃ * H ^ 6 ∧
        alignedFifthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ ^ 2 =
          Polynomial.C κ₄ * H ^ 15 ∧
        alignedSixthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7)
            κ = Polynomial.C κ₅ * H ^ 9 ∧
        alignedSeventhDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6)
            (q.coeff 7) κ ^ 2 = Polynomial.C κ₆ * H ^ 21 ∧
        alignedEighthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
            (q.coeff 6) (q.coeff 7) κ = Polynomial.C κ₇ * H ^ 12 ∧
        alignedNinthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
            (q.coeff 5) (q.coeff 6) (q.coeff 7) κ ^ 2 =
          Polynomial.C κ₈ * H ^ 27 ∧
        alignedTenthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 0) (q.coeff 1) (q.coeff 2) (q.coeff 3)
            (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₉ * H ^ 15 ∧
        alignedEleventhDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
            (q.coeff 5) (q.coeff 6) (q.coeff 7) κ ^ 2 =
          Polynomial.C κ₁₀ * H ^ 33 ∧
        alignedTwelfthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
            (q.coeff 5) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₁₁ * H ^ 18 ∧
        ∀ a : K, H.eval a = 0 →
          (p.coeff 3).eval a = 0 ∧
            (q.coeff 8).derivative.eval a = 0) ∧
      ∃ j : K, j ≠ 0 ∧
        (p.coeff 0).derivative * q.coeff 1 -
            p.coeff 1 * (q.coeff 0).derivative = Polynomial.C j := by
  dsimp only at haligned ⊢
  refine ⟨?jet, ?row⟩
  · exact normalized410ScaleTwo_alignedTwelfthRow_packet hsource haligned
  · exact normalized410ScaleTwo_alignedFinalKellerRow hsource haligned

end AlignedExhaustedPacket410

/-! ## Valuation/degree kill of the aligned face -/

section AlignedEndgame410

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- Square and nonsquare chambers of a normalized aligned scale-two
`(4,10)` source are both empty.  The square kill is the ninth-load
valuation residual on the surviving deep-divisor allocation; the
nonsquare kill is the transverse ninth-row contradiction. -/
theorem alignedFace410_endgameContradiction
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0) :
    False := by
  dsimp only at haligned
  by_cases hsquare : ∃ h0 : K[X], H = h0 ^ 2
  · obtain ⟨h0, hH⟩ := hsquare
    have hh0 : h0 ≠ 0 := by
      intro hzero
      apply hsource.1
      rw [hH, hzero]
      simp
    exact normalized410ScaleTwo_alignedSquare_false hsource hh0 hH
      haligned
  · have hnonsquare : ∀ h0 : K[X], H ≠ h0 ^ 2 := by
      intro h0 hH
      exact hsquare ⟨h0, hH⟩
    exact normalized410ScaleTwo_alignedNonsquare_false hsource hnonsquare
      haligned

/-- Source-facing exclusion of a normalized scale-two `(4,10)` aligned
face.  The nonzero face `N ≠ 0` is not reopened. -/
theorem normalized410ScaleTwo_alignedFace_false
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0) :
    False :=
  alignedFace410_endgameContradiction hsource haligned

end AlignedEndgame410

/-! ## LEAF CLOSURE: scale-two route, then the full low-scale `(4,10)` leaf -/

section ScaleTwoLeaf410

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- Every normalized scale-two `(4,10)` source generates: both discriminator
faces are empty, so the implication is discharged by elimination. -/
theorem proved_planeKellerNormalized410ScaleTwoRoute :
    PlaneKellerNormalized410ScaleTwoRoute (k := K) := by
  intro P Q H hsource
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  by_cases hN :
    (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0
  · exact (normalized410ScaleTwo_alignedFace_false hsource hN).elim
  · exact (normalized410ScaleTwo_nonzeroFace_false hsource hN).elim

/-- LEAF CLOSURE.  Scale zero is already impossible, and both scale-two
faces are now empty.  The committed adapter therefore supplies the full
normalized `(4,10)` low-scale route — discharging the `h410` premise of
`Max11PlaneKellerGenerationWithFiveNormalizedLowScaleRoutes` in
`Max11Assembly`. -/
theorem proved_planeKellerNormalized410LowScaleRoute :
    PlaneKellerNormalized410LowScaleRoute (K := K) :=
  planeKellerNormalized410LowScaleRoute_of_scaleTwo
    proved_planeKellerNormalized410ScaleTwoRoute

end ScaleTwoLeaf410

#print axioms normalized410ScaleTwo_alignedFace_exhaustedPacket
#print axioms alignedFace410_endgameContradiction
#print axioms normalized410ScaleTwo_alignedFace_false
#print axioms proved_planeKellerNormalized410ScaleTwoRoute
#print axioms proved_planeKellerNormalized410LowScaleRoute

end Max11DegreeRoutes
