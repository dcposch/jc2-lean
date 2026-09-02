import Sol68ScaleTwoAlignedSquareBoundaryGSignedRayLinearDZeroLowerRowOneNegFiveScratch

/-! # Normalized square inventory after the lower-row-one deletion

The old normalized inventory is preserved literally.  Its `G[-2] != 0`
leaf now records that the exact deep signed-ray/B7 packet is impossible;
coordinate, nonsingular, earlier-selector, and local-final siblings remain.
-/

noncomputable section

open Polynomial
open scoped Polynomial.Bivariate

namespace Max11DegreeRoutes

section AlignedSquareNormalizedFinalInventoryLowerRowOne68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- Source-facing deletion of the B7 packet.  The B8 transport is derived,
not assumed, before applying the structural lower-row-one contradiction. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_signedRay_lowerRowOne_B7_impossible68
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (Q : RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u)
    (R : RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalPlusOneB7Isolation68 T) :
    False := by
  have R8 := T.rhoOne_boundaryG_terminal_plus_one_B8_transport68
    hp hH hp6 hp5 hp4 Q R
  exact T.rhoOne_boundaryG_signedRay_lowerRowOne_impossible68
    hp hH hp6 hp5 hp4 Q R8

/-- Literal remaining normalized inventory.  Only the exact deep B7 child
is deleted from the broad `G[-2] != 0` selector. -/
def RhoOneAlignedSquareNormalizedLocalFinalInventoryAfterLowerRowOne68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (g u : k[X]) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C0 := ratFuncAtHahn46 T.root T.source.C0
  let D := ratFuncAtHahn46 T.root T.source.D
  let E := ratFuncAtHahn46 T.root T.source.E
  let C := rhoOneCDefectHahn68 A C0
  let F := rhoOneTangentDDefectHahn68 A B D
  let G := rhoOneTangentEDefectHahn68 A C (rhoOneEDefectHahn68 A E)
  (h0 ^ 5 ∣ p.coeff 5 ∧ h0 ^ 3 ∣ p.coeff 4 ∧ h0 ∣ p.coeff 3) ∨
  RhoOneZeroLNoncubicSourcePacket68 T g u ∨
  RhoOneAlignedSquareEarlyCubicSibling68 T g u ∨
  RhoOneAlignedSquareExceptionalPreDoubleZeroSibling68 T ∨
  RhoOneAlignedSquareExceptionalGBoxBoundarySibling68 T ∨
  F.coeff (-1 : ℚ) ≠ 0 ∨
  (G.coeff (-2 : ℚ) ≠ 0 ∧
    ¬ (RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u ∧
      RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalPlusOneB7Isolation68 T)) ∨
  RhoOneAlignedSquareLocalFinalResidual68 T g u

/-- Refine the old normalized inventory without changing any sibling. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_alignedSquare_normalizedLocalFinalInventory_after_lowerRowOne68
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (R : RhoOneAlignedSquareNormalizedLocalFinalInventory68 T g u) :
    RhoOneAlignedSquareNormalizedLocalFinalInventoryAfterLowerRowOne68 T g u := by
  dsimp only [RhoOneAlignedSquareNormalizedLocalFinalInventory68] at R
  dsimp only [RhoOneAlignedSquareNormalizedLocalFinalInventoryAfterLowerRowOne68]
  rcases R with hdesc | hnoncubic | hearly | hpre | hgbox | hFne | hGne | hfinal
  · exact Or.inl hdesc
  · exact Or.inr (Or.inl hnoncubic)
  · exact Or.inr (Or.inr (Or.inl hearly))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hpre)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hgbox))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hFne)))))
  · right
    right
    right
    right
    right
    right
    left
    refine ⟨hGne, ?_⟩
    rintro ⟨Q, R7⟩
    exact T.rhoOne_boundaryG_signedRay_lowerRowOne_B7_impossible68
      hp hH hp6 hp5 hp4 Q R7
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr hfinal))))))

/-- Normalized aligned-square source wrapper with the two deep signed-ray
affine cells removed. -/
theorem normalized68ScaleTwo_alignedSquare_finalInventory_after_lowerRowOne
    {P Q : MvPolynomial (Fin 2) k} {H h0 : k[X]}
    (hsource : Normalized68LeadingCoreSource P Q H 2)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      (4 : k[X]) * p.coeff 5 * H - (3 : k[X]) * q.coeff 7 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    ∃ (j : k) (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
        (g u : k[X]),
      p.coeff 5 = h0 ^ 4 * g ∧ p.coeff 4 = h0 ^ 2 * u ∧
      RhoOneAlignedSquareNormalizedLocalFinalInventoryAfterLowerRowOne68 T g u := by
  let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
  have hp : p.natDegree = 6 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hsource.2.2.1
  have hp6 : p.coeff 6 = H ^ 3 := by
    simpa only [p] using hsource.2.2.2.2.1
  obtain ⟨j, T, g, u, hp5, hp4, R⟩ :=
    normalized68ScaleTwo_alignedSquare_finalInventory
      hsource hh0 hH haligned
  exact ⟨j, T, g, u, hp5, hp4,
    T.rhoOne_alignedSquare_normalizedLocalFinalInventory_after_lowerRowOne68
      hp hH hp6 hp5 hp4 R⟩

end AlignedSquareNormalizedFinalInventoryLowerRowOne68

end Max11DegreeRoutes
