import Sol68ScaleTwoAlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZeroBaseAffineBackwireScratch

/-! # Explicit coefficient-zero wall in the affine terminal base -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZeroBaseCoeffZeroWall68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

def rhoOne_boundaryG_terminalZeroB6DeltaCoeffExpandedSource68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : k :=
  let A : RatFunc k := T.source.A
  let B : RatFunc k := T.source.B
  let C : RatFunc k := T.source.C0 - RatFunc.C (1 / 3 : k) * A ^ 2
  let F : RatFunc k := T.source.D - RatFunc.C (1 / 3 : k) * A * B
  let E : RatFunc k := T.source.E - RatFunc.C (1 / 27 : k) * A ^ 3
  let G : RatFunc k := E - RatFunc.C (1 / 3 : k) * A * C
  rhoOne_boundaryG_terminalZeroB6DeltaCoeffExpanded68
    T.source.gamma T.source.epsilon
    (ratFuncAtLaurent46 T.root A) (ratFuncAtLaurent46 T.root B)
    (ratFuncAtLaurent46 T.root C) (ratFuncAtLaurent46 T.root F)
    (ratFuncAtLaurent46 T.root G)

omit [IsAlgClosed k] in
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_terminal_zero_B6_DeltaCoeff_expanded68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) :
    rhoOne_boundaryG_terminalZeroB6DeltaCoeffSource68 T =
      rhoOne_boundaryG_terminalZeroB6DeltaCoeffExpandedSource68 T := by
  dsimp only [rhoOne_boundaryG_terminalZeroB6DeltaCoeffSource68,
    rhoOne_boundaryG_terminalZeroB6DeltaCoeffExpandedSource68]
  exact rhoOne_boundaryG_terminalZeroB6DeltaCoeff_expanded68 _ _ _ _ _ _ _

def rhoOne_boundaryG_signedRayLinearDZeroI4NineK11NormalizedSlopeZeroBaseCoeffWallCells68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (sigmaCell rCell sigma r : k) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  let D0 := 3 * F.coeff 1 - A.coeff (-1) * B.coeff 2
  let Slope := rhoOne_boundaryG_terminalZeroB6SlopeSource68 T
  let J90 := rhoOne_boundaryG_i3nineAtB6_68 T 0
  let N9 := rhoOne_boundaryG_i3nineB6SlopeExpanded68 T
  let G3 := G.coeff 3
  let Wall := rhoOne_boundaryG_i4nineK11NormalizedWall68 T r
  let DeltaA := rhoOne_boundaryG_terminalZeroB6DeltaASource68 T
  let CoeffX := rhoOne_boundaryG_terminalZeroB6DeltaCoeffExpandedSource68 T
  let Const := rhoOne_boundaryG_terminalZeroB6DeltaConstantSource68 T
  D0 = 0 →
    rhoOne_boundaryG_signedRayLinearDZeroI4NineK11NormalizedSlopeZeroBaseAffineCells68
      T sigmaCell rCell sigma r ∧
    (N9 ≠ 0 ∧ G3 ≠ 0 ∧
      (8 : k) * G3 * J90 - 3 * N9 * rhoOne_boundaryG_i4nineAtB6_68 T 0 = 0 →
      Wall = 0 → Slope = 0 →
      ((CoeffX = 0 ∧ Const = 0) ∨
       (CoeffX ≠ 0 ∧ Const ≠ 0 ∧ DeltaA = -Const / CoeffX)))

def RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZeroBaseCoeffWall68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : Prop :=
  RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZeroBaseAffine68 T ∧
  ∃ sigmaCell rCell sigma r : k,
    rCell ≠ 0 ∧
    rCell ^ 2 = -3 * (ratFuncAtHahn46 T.root T.source.A).coeff (-2) ∧
    sigma ^ 2 = 1 ∧ r ≠ 0 ∧
    (ratFuncAtHahn46 T.root T.source.B).coeff 2 ≠ 0 ∧
    (rhoOneTangentEDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0))
      (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.E))).coeff (-2) ≠ 0 ∧
    27 * (rhoOneTangentEDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0))
      (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.E))).coeff (-1) =
      sigma * r ^ 3 * (ratFuncAtHahn46 T.root T.source.B).coeff 2 ∧
    rhoOne_boundaryG_signedRayLinearDZeroI4NineK11NormalizedSlopeZeroBaseCoeffWallCells68
      T sigmaCell rCell sigma r

theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_signedRay_linear_dZero_terminal_zero_B6_slope_wall_i4nine_K11_normalized_slope_zero_Base_coeff_wall68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (R : RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZeroBaseAffine68 T) :
    RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZeroBaseCoeffWall68 T := by
  have Rc := R
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZeroBaseAffine68] at Rc
  rcases Rc.2 with ⟨sigmaCell, rCell, sigma, r, hrCell0, hrCell,
    hsigma, hr0, hb, hgm2, hray, hPrevCells⟩
  have hcells :
      rhoOne_boundaryG_signedRayLinearDZeroI4NineK11NormalizedSlopeZeroBaseCoeffWallCells68
        T sigmaCell rCell sigma r := by
    dsimp only [rhoOne_boundaryG_signedRayLinearDZeroI4NineK11NormalizedSlopeZeroBaseCoeffWallCells68]
    intro hD
    have hPrev := hPrevCells hD
    refine ⟨hPrevCells, ?_⟩
    intro hdbl hWall hSlope
    have hchild := hPrev.2 hdbl hWall hSlope
    have hCoeff := T.rhoOne_boundaryG_terminal_zero_B6_DeltaCoeff_expanded68
    rcases hchild.2.2.2 with hz | hn
    · left
      exact ⟨hCoeff ▸ hz.1, hz.2⟩
    · right
      simpa only [hCoeff] using hn
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZeroBaseCoeffWall68]
  exact ⟨R, sigmaCell, rCell, sigma, r, hrCell0, hrCell, hsigma, hr0,
    hb, hgm2, hray, hcells⟩

end AlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZeroBaseCoeffZeroWall68

end Max11DegreeRoutes
