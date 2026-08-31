import Sol68ScaleTwoAlignedSquareNormalizedFinalInventoryLowerRowOneScratch

/-! # Inventory continuation after the lower-row-one B7 deletion

Untracked working note. No tracked file was edited.

The last selector on the signed-ray linear `D=0` path is
`I4SevenCross`.  Every later module is an unconditional refinement of
that packet through terminal zero, the `B[6]` slope wall, the
`I3/I4(9)` `K[11]` cluster, and terminal-plus-one `B7` isolation.  The
already landed lower-row-one identity then kills `B7`, hence kills the
whole `I4SevenCross` child.

This file only composes those landed constructors.  It does not reopen
the Hahn algebra, consume a new Keller row, or claim the full local-root
exclusion `PlaneKeller68AlignedSquareLocalRootExclusion`.

Exact gain: the quadratic `G[-2]` chamber loses its signed-ray linear
`D=0` child.  The remaining quadratic residual is the coordinate-gain
cell, the alternative-determinant QR factor, and the nonsingular
transport.  The inventory `G[-2] != 0` selector that has not yet entered
the quadratic residual is retained literally.

Next unused row: the coordinate-gain `I4(4)` face already recorded on
`RhoOneAlignedSquareGNegTwoCoordinateGain68`, and the unused `I3(3)`
alternative-determinant row on `RhoOneAlignedSquareGNegTwoSignedRayQRResidual68`.
-/

noncomputable section

open Polynomial
open scoped Polynomial.Bivariate

namespace Max11DegreeRoutes

section AlignedSquareInventoryContinuation68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- Quadratic `G[-2]` residual after deleting the signed-ray linear `D=0`
child.  The three surviving cells are already inventoried. -/
def RhoOneAlignedSquareGNegTwoQuadraticChamberAfterSignedRayLinearDZero68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (g u : k[X]) : Prop :=
  RhoOneAlignedSquareGNegTwoCoordinateGain68 T g u ∨
    (RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u ∧
      RhoOneAlignedSquareGNegTwoSignedRayQRResidual68 T) ∨
    (RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u ∧
      let A := ratFuncAtHahn46 T.root T.source.A
      let B := ratFuncAtHahn46 T.root T.source.B
      let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
      let G := rhoOneTangentEDefectHahn68 A C
        (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
      A.coeff (-2) ^ 3 * B.coeff 2 ^ 2 + 27 * G.coeff (-1) ^ 2 ≠ 0)

/-- Literal `G[-2]` inventory residual: either the selector has not yet
entered the quadratic residual, or it has and the signed-ray linear
`D=0` child is gone. -/
def RhoOneAlignedSquareGNegTwoInventoryResidualAfterSignedRayLinearDZero68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (g u : k[X]) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  (G.coeff (-2 : ℚ) ≠ 0 ∧
    ¬ RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u) ∨
  RhoOneAlignedSquareGNegTwoQuadraticChamberAfterSignedRayLinearDZero68 T g u

/-- Normalized inventory with the signed-ray linear `D=0` child removed
from the quadratic `G[-2]` chamber.  Every other sibling is preserved
verbatim. -/
def RhoOneAlignedSquareNormalizedLocalFinalInventoryAfterSignedRayLinearDZero68
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
  (h0 ^ 5 ∣ p.coeff 5 ∧ h0 ^ 3 ∣ p.coeff 4 ∧ h0 ∣ p.coeff 3) ∨
  RhoOneZeroLNoncubicSourcePacket68 T g u ∨
  RhoOneAlignedSquareEarlyCubicSibling68 T g u ∨
  RhoOneAlignedSquareExceptionalPreDoubleZeroSibling68 T ∨
  RhoOneAlignedSquareExceptionalGBoxBoundarySibling68 T ∨
  F.coeff (-1 : ℚ) ≠ 0 ∨
  RhoOneAlignedSquareGNegTwoInventoryResidualAfterSignedRayLinearDZero68 T g u ∨
  RhoOneAlignedSquareLocalFinalResidual68 T g u

set_option maxHeartbeats 800000 in
/-- The inventoried `I4SevenCross` packet refines unconditionally to `B7`
isolation, which lower-row-one already contradicts. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_signedRay_linear_dZero_i4seven_cross_impossible68
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (Q : RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u)
    (R : RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroI4SevenCross68 T) :
    False := by
  have hI3eight :=
    T.rhoOne_boundaryG_signedRay_linear_dZero_i3eight_reduction68 Q R
  have hI4eight :=
    T.rhoOne_boundaryG_signedRay_linear_dZero_i4eight_cross68 Q hI3eight
  have hTerm0 :=
    T.rhoOne_boundaryG_signedRay_linear_dZero_terminal_zero68 Q hI4eight
  have hExp0 :=
    T.rhoOne_boundaryG_signedRay_linear_dZero_terminal_zero_expansion68
      Q hTerm0
  have hB6cells :=
    T.rhoOne_boundaryG_signedRay_linear_dZero_terminal_zero_B6_cells68
      hp hH hp6 hp5 hp4 Q hExp0
  have hSlopeSplit :=
    T.rhoOne_boundaryG_signedRay_linear_dZero_terminal_zero_B6_slope_split68
      hB6cells
  have hSlopeWall :=
    T.rhoOne_boundaryG_signedRay_linear_dZero_terminal_zero_B6_slope_wall68
      hp hH hp6 hp5 hp4 Q hSlopeSplit
  have hI3nine :=
    T.rhoOne_boundaryG_signedRay_linear_dZero_terminal_zero_B6_slope_wall_i3nine68
      Q hSlopeWall
  have hI3nineRed :=
    T.rhoOne_boundaryG_signedRay_linear_dZero_terminal_zero_B6_slope_wall_i3nine_reduction68
      Q hI3nine
  have hI3nineDet :=
    T.rhoOne_boundaryG_signedRay_linear_dZero_terminal_zero_B6_slope_wall_i3nine_cell_determinants68
      hI3nineRed
  have hI3nineJet :=
    T.rhoOne_boundaryG_signedRay_linear_dZero_terminal_zero_B6_slope_wall_i3nine_slope_jet68
      Q hI3nineDet
  have hI4nine :=
    T.rhoOne_boundaryG_signedRay_linear_dZero_terminal_zero_B6_slope_wall_i4nine68
      Q hI3nineJet
  have hI4nineDet :=
    T.rhoOne_boundaryG_signedRay_linear_dZero_terminal_zero_B6_slope_wall_i4nine_determinant68
      hI4nine
  have hB11 :=
    T.rhoOne_boundaryG_signedRay_linear_dZero_terminal_zero_B6_slope_wall_i4nine_B11_reduction68
      Q hI4nineDet
  have hK11 :=
    T.rhoOne_boundaryG_signedRay_linear_dZero_terminal_zero_B6_slope_wall_i4nine_K11_factor68
      Q hB11
  have hK11N :=
    T.rhoOne_boundaryG_signedRay_linear_dZero_terminal_zero_B6_slope_wall_i4nine_K11_normalized68
      hK11
  have hK11T :=
    T.rhoOne_boundaryG_signedRay_linear_dZero_terminal_zero_B6_slope_wall_i4nine_K11_normalized_determinant_transport68
      hK11N
  have hSlope0 :=
    T.rhoOne_boundaryG_signedRay_linear_dZero_terminal_zero_B6_slope_wall_i4nine_K11_normalized_slope_zero68
      hK11T
  have hObst :=
    T.rhoOne_boundaryG_signedRay_linear_dZero_terminal_zero_B6_slope_wall_i4nine_K11_normalized_slope_zero_obstruction68
      hSlope0
  have hAff :=
    T.rhoOne_boundaryG_signedRay_linear_dZero_terminal_zero_B6_slope_wall_i4nine_K11_normalized_slope_zero_Base_affine68
      hObst
  have hWall :=
    T.rhoOne_boundaryG_signedRay_linear_dZero_terminal_zero_B6_slope_wall_i4nine_K11_normalized_slope_zero_Base_coeff_wall68
      hAff
  have hTrans :=
    T.rhoOne_boundaryG_signedRay_linear_dZero_terminal_zero_B6_slope_wall_i4nine_K11_normalized_slope_zero_Base_coeff_transport68
      hWall
  have hI3ten :=
    T.rhoOne_boundaryG_signedRay_linear_dZero_terminal_zero_B6_slope_wall_i4nine_K11_normalized_slope_zero_Base_coeff_i3ten_source68
      Q hTrans
  have hI3tenC :=
    T.rhoOne_boundaryG_signedRay_linear_dZero_terminal_zero_B6_slope_wall_i4nine_K11_normalized_slope_zero_Base_coeff_i3ten_C12_transport68
      Q hI3ten
  have hI4ten :=
    T.rhoOne_boundaryG_signedRay_linear_dZero_terminal_zero_B6_slope_wall_i4nine_K11_normalized_slope_zero_Base_coeff_i4ten_source68
      Q hI3tenC
  have hI4tenB :=
    T.rhoOne_boundaryG_signedRay_linear_dZero_terminal_zero_B6_slope_wall_i4nine_K11_normalized_slope_zero_Base_coeff_i4ten_B12_transport68
      Q hI4ten
  have hI3eleven :=
    T.rhoOne_boundaryG_signedRay_linear_dZero_terminal_zero_B6_slope_wall_i4nine_K11_normalized_slope_zero_Base_coeff_i3eleven_source68
      Q hI4tenB
  have hI3elevenC :=
    T.rhoOne_boundaryG_signedRay_linear_dZero_terminal_zero_B6_slope_wall_i4nine_K11_normalized_slope_zero_Base_coeff_i3eleven_C13_transport68
      Q hI3eleven
  have hI4eleven :=
    T.rhoOne_boundaryG_signedRay_linear_dZero_terminal_zero_B6_slope_wall_i4nine_K11_normalized_slope_zero_Base_coeff_i4eleven_source68
      Q hI3elevenC
  have hI4elevenB :=
    T.rhoOne_boundaryG_signedRay_linear_dZero_terminal_zero_B6_slope_wall_i4nine_K11_normalized_slope_zero_Base_coeff_i4eleven_B13_transport68
      Q hI4eleven
  have hCells :=
    T.rhoOne_boundaryG_signedRay_linear_dZero_i3i4eleven_affine_cells68
      hI4elevenB
  have hAudit :=
    T.rhoOne_boundaryG_baseCoeff_structural_audit68 hCells
  have hPlus1 :=
    T.rhoOne_boundaryG_terminal_plus_one_backwire68 Q hAudit
  have hPlus1E :=
    T.rhoOne_boundaryG_terminal_plus_one_expanded_backwire68 hPlus1
  have hB7 :=
    T.rhoOne_boundaryG_terminal_plus_one_B7_isolation68 hPlus1E
  exact T.rhoOne_boundaryG_signedRay_lowerRowOne_B7_impossible68
    hp hH hp6 hp5 hp4 Q hB7

/-- Source-facing quadratic selector with the signed-ray linear `D=0`
child deleted. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_signedRay_linear_dZero_after_i4seven_selector68
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (Q : RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u) :
    RhoOneAlignedSquareGNegTwoQuadraticChamberAfterSignedRayLinearDZero68
      T g u := by
  rcases T.rhoOne_boundaryG_signedRay_linear_dZero_i4seven_cross_selector68
      hp hH hp6 hp5 hp4 Q with hcoord | hsigned | hnon
  · exact Or.inl hcoord
  · rcases hsigned.2 with hseven | hqr
    · exact (T.rhoOne_boundaryG_signedRay_linear_dZero_i4seven_cross_impossible68
        hp hH hp6 hp5 hp4 hsigned.1 hseven).elim
    · exact Or.inr (Or.inl ⟨hsigned.1, hqr⟩)
  · exact Or.inr (Or.inr hnon)

/-- The old `G[-2] != 0` selector, after deleting `B7`, splits into the
pre-quadratic remainder and the three surviving quadratic cells. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_signedRay_GnegTwo_inventory_after_i4seven68
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (hG :
      let A := ratFuncAtHahn46 T.root T.source.A
      let B := ratFuncAtHahn46 T.root T.source.B
      let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
      let G := rhoOneTangentEDefectHahn68 A C
        (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
      G.coeff (-2 : ℚ) ≠ 0 ∧
        ¬ (RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u ∧
          RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalPlusOneB7Isolation68 T)) :
    RhoOneAlignedSquareGNegTwoInventoryResidualAfterSignedRayLinearDZero68
      T g u := by
  dsimp only [RhoOneAlignedSquareGNegTwoInventoryResidualAfterSignedRayLinearDZero68]
  by_cases hQ :
      RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u
  · exact Or.inr
      (T.rhoOne_boundaryG_signedRay_linear_dZero_after_i4seven_selector68
        hp hH hp6 hp5 hp4 hQ)
  · exact Or.inl ⟨hG.1, hQ⟩

/-- Refine the after-lower-row-one inventory by assembling the quadratic
`G[-2]` chamber.  No other sibling is touched. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_alignedSquare_normalizedLocalFinalInventory_after_signedRayLinearDZero68
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (R : RhoOneAlignedSquareNormalizedLocalFinalInventoryAfterLowerRowOne68
      T g u) :
    RhoOneAlignedSquareNormalizedLocalFinalInventoryAfterSignedRayLinearDZero68
      T g u := by
  dsimp only [RhoOneAlignedSquareNormalizedLocalFinalInventoryAfterLowerRowOne68] at R
  dsimp only [RhoOneAlignedSquareNormalizedLocalFinalInventoryAfterSignedRayLinearDZero68]
  rcases R with hdesc | hnoncubic | hearly | hpre | hgbox | hFne | hGne | hfinal
  · exact Or.inl hdesc
  · exact Or.inr (Or.inl hnoncubic)
  · exact Or.inr (Or.inr (Or.inl hearly))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hpre)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hgbox))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hFne)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (T.rhoOne_boundaryG_signedRay_GnegTwo_inventory_after_i4seven68
        hp hH hp6 hp5 hp4 hGne)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr hfinal))))))

/-- Normalized aligned-square source wrapper after the signed-ray linear
`D=0` assembly. -/
theorem normalized68ScaleTwo_alignedSquare_finalInventory_after_signedRayLinearDZero
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
      RhoOneAlignedSquareNormalizedLocalFinalInventoryAfterSignedRayLinearDZero68
        T g u := by
  let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
  have hp : p.natDegree = 6 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hsource.2.2.1
  have hp6 : p.coeff 6 = H ^ 3 := by
    simpa only [p] using hsource.2.2.2.2.1
  obtain ⟨j, T, g, u, hp5, hp4, R⟩ :=
    normalized68ScaleTwo_alignedSquare_finalInventory_after_lowerRowOne
      hsource hh0 hH haligned
  exact ⟨j, T, g, u, hp5, hp4,
    T.rhoOne_alignedSquare_normalizedLocalFinalInventory_after_signedRayLinearDZero68
      hp hH hp6 hp5 hp4 R⟩

end AlignedSquareInventoryContinuation68

end Max11DegreeRoutes
