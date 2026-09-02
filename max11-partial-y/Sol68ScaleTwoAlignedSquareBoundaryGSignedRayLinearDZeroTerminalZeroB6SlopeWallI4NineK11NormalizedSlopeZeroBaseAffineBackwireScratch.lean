import Sol68ScaleTwoAlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZeroBaseAffineScratch

/-! # Source backwire for the affine `dA[-2]` packet -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZeroBaseAffineBackwire68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

def rhoOne_boundaryG_terminalZeroB6DeltaASource68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : k :=
  let A : RatFunc k := T.source.A
  let AL := ratFuncAtLaurent46 T.root A
  let dAL := ratFuncAtLaurent46 T.root (Differential.deriv A)
  dAL.coeff (-2) - 2 * AL.coeff (-1)

def rhoOne_boundaryG_terminalZeroB6DeltaCoeffSource68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : k :=
  let A : RatFunc k := T.source.A
  let B : RatFunc k := T.source.B
  let C : RatFunc k := T.source.C0 - RatFunc.C (1 / 3 : k) * A ^ 2
  let F : RatFunc k := T.source.D - RatFunc.C (1 / 3 : k) * A * B
  let E : RatFunc k := T.source.E - RatFunc.C (1 / 27 : k) * A ^ 3
  let G : RatFunc k := E - RatFunc.C (1 / 3 : k) * A * C
  rhoOne_boundaryG_terminalZeroB6DeltaCoeff68 T.source.gamma T.source.epsilon
    (ratFuncAtLaurent46 T.root A) (ratFuncAtLaurent46 T.root B)
    (ratFuncAtLaurent46 T.root C) (ratFuncAtLaurent46 T.root F)
    (ratFuncAtLaurent46 T.root G)

def rhoOne_boundaryG_terminalZeroB6DeltaConstantSource68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : k :=
  let A : RatFunc k := T.source.A
  let B : RatFunc k := T.source.B
  let C : RatFunc k := T.source.C0 - RatFunc.C (1 / 3 : k) * A ^ 2
  let F : RatFunc k := T.source.D - RatFunc.C (1 / 3 : k) * A * B
  let E : RatFunc k := T.source.E - RatFunc.C (1 / 27 : k) * A ^ 3
  let G : RatFunc k := E - RatFunc.C (1 / 3 : k) * A * C
  rhoOne_boundaryG_terminalZeroB6DeltaConstant68 T.source.gamma T.source.epsilon
    (ratFuncAtLaurent46 T.root A) (ratFuncAtLaurent46 T.root B)
    (ratFuncAtLaurent46 T.root C) (ratFuncAtLaurent46 T.root F)
    (ratFuncAtLaurent46 T.root G)
    (ratFuncAtLaurent46 T.root (Differential.deriv A))
    (ratFuncAtLaurent46 T.root (Differential.deriv B))
    (ratFuncAtLaurent46 T.root (Differential.deriv C))
    (ratFuncAtLaurent46 T.root (Differential.deriv F))
    (ratFuncAtLaurent46 T.root (Differential.deriv G))

omit [IsAlgClosed k] in
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_terminal_zero_B6_Base_affine_DeltaA68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) :
    rhoOne_boundaryG_terminalZeroB6BaseSource68 T =
      rhoOne_boundaryG_terminalZeroB6DeltaConstantSource68 T +
        rhoOne_boundaryG_terminalZeroB6DeltaCoeffSource68 T *
          rhoOne_boundaryG_terminalZeroB6DeltaASource68 T := by
  dsimp only [rhoOne_boundaryG_terminalZeroB6BaseSource68,
    rhoOne_boundaryG_terminalZeroB6DeltaConstantSource68,
    rhoOne_boundaryG_terminalZeroB6DeltaCoeffSource68,
    rhoOne_boundaryG_terminalZeroB6DeltaASource68]
  exact rhoOne_boundaryG_terminalZeroB6Base_affine_DeltaA68
    _ _ _ _ _ _ _ _ _ _ _ _

omit [IsAlgClosed k] in
theorem rhoOne_boundaryG_terminalZeroB6Base_zero_nonzero_DeltaA_split68
    (gamma epsilon : k)
    (A B C F G dA dB dC dF dG : LaurentSeries k)
    (hBase : rhoOne_boundaryG_terminalZeroB6Base68 gamma epsilon A B C F G
      dA dB dC dF dG = 0)
    (hDelta : dA.coeff (-2) - 2 * A.coeff (-1) ≠ 0) :
    let DeltaA := dA.coeff (-2) - 2 * A.coeff (-1)
    let Coeff := rhoOne_boundaryG_terminalZeroB6DeltaCoeff68 gamma epsilon A B C F G
    let Const := rhoOne_boundaryG_terminalZeroB6DeltaConstant68 gamma epsilon
      A B C F G dA dB dC dF dG
    Const + Coeff * DeltaA = 0 ∧
      ((Coeff = 0 ∧ Const = 0) ∨
       (Coeff ≠ 0 ∧ Const ≠ 0 ∧ DeltaA = -Const / Coeff)) := by
  dsimp only
  have hs := rhoOne_boundaryG_terminalZeroB6Base_zero_affine_split68 gamma epsilon
    A B C F G dA dB dC dF dG hBase
  refine ⟨hs.1, ?_⟩
  rcases hs.2 with hz | hn
  · exact Or.inl hz
  · right
    refine ⟨hn.1, ?_, hn.2⟩
    intro hConst
    have hzEq := hs.1
    rw [hConst, zero_add] at hzEq
    exact hDelta (mul_eq_zero.mp hzEq |>.resolve_left hn.1)

def rhoOne_boundaryG_signedRayLinearDZeroI4NineK11NormalizedSlopeZeroBaseAffineCells68
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
  let Coeff := rhoOne_boundaryG_terminalZeroB6DeltaCoeffSource68 T
  let Const := rhoOne_boundaryG_terminalZeroB6DeltaConstantSource68 T
  D0 = 0 →
    rhoOne_boundaryG_signedRayLinearDZeroI4NineK11NormalizedSlopeZeroObstructionCells68
      T sigmaCell rCell sigma r ∧
    (N9 ≠ 0 ∧ G3 ≠ 0 ∧
      (8 : k) * G3 * J90 - 3 * N9 * rhoOne_boundaryG_i4nineAtB6_68 T 0 = 0 →
      Wall = 0 → Slope = 0 →
      DeltaA ≠ 0 ∧
      rhoOne_boundaryG_terminalZeroB6BaseSource68 T = Const + Coeff * DeltaA ∧
      Const + Coeff * DeltaA = 0 ∧
      ((Coeff = 0 ∧ Const = 0) ∨
       (Coeff ≠ 0 ∧ Const ≠ 0 ∧ DeltaA = -Const / Coeff)))

def RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZeroBaseAffine68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : Prop :=
  RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZeroObstruction68 T ∧
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
    rhoOne_boundaryG_signedRayLinearDZeroI4NineK11NormalizedSlopeZeroBaseAffineCells68
      T sigmaCell rCell sigma r

theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_signedRay_linear_dZero_terminal_zero_B6_slope_wall_i4nine_K11_normalized_slope_zero_Base_affine68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (R : RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZeroObstruction68 T) :
    RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZeroBaseAffine68 T := by
  have Rc := R
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZeroObstruction68] at Rc
  rcases Rc.2 with ⟨sigmaCell, rCell, sigma, r, hrCell0, hrCell,
    hsigma, hr0, hb, hgm2, hray, hPrevCells⟩
  have hcells :
      rhoOne_boundaryG_signedRayLinearDZeroI4NineK11NormalizedSlopeZeroBaseAffineCells68
        T sigmaCell rCell sigma r := by
    dsimp only [rhoOne_boundaryG_signedRayLinearDZeroI4NineK11NormalizedSlopeZeroBaseAffineCells68]
    intro hD
    have hPrev := hPrevCells hD
    refine ⟨hPrevCells, ?_⟩
    intro hdbl hWall hSlope
    have hchild := hPrev.2 hdbl hWall hSlope
    have hDelta := hchild.2.2
    have htoL (X : RatFunc k) (n : ℤ) :
        (ratFuncAtLaurent46 T.root X).coeff n =
          (ratFuncAtHahn46 T.root X).coeff n := by
      rw [ratFuncAtHahn46_coeff_int68]
    have hDeltaL : rhoOne_boundaryG_terminalZeroB6DeltaASource68 T ≠ 0 := by
      dsimp only [rhoOne_boundaryG_terminalZeroB6DeltaASource68]
      rw [htoL (Differential.deriv T.source.A) (-2),
        htoL T.source.A (-1)]
      exact hDelta
    have hAff := T.rhoOne_boundaryG_terminal_zero_B6_Base_affine_DeltaA68
    have hBaseSplit :
        let DeltaA := rhoOne_boundaryG_terminalZeroB6DeltaASource68 T
        let Coeff := rhoOne_boundaryG_terminalZeroB6DeltaCoeffSource68 T
        let Const := rhoOne_boundaryG_terminalZeroB6DeltaConstantSource68 T
        Const + Coeff * DeltaA = 0 ∧
          ((Coeff = 0 ∧ Const = 0) ∨
           (Coeff ≠ 0 ∧ Const ≠ 0 ∧ DeltaA = -Const / Coeff)) := by
      dsimp only [rhoOne_boundaryG_terminalZeroB6DeltaASource68,
        rhoOne_boundaryG_terminalZeroB6DeltaCoeffSource68,
        rhoOne_boundaryG_terminalZeroB6DeltaConstantSource68,
        rhoOne_boundaryG_terminalZeroB6BaseSource68] at hchild ⊢
      exact rhoOne_boundaryG_terminalZeroB6Base_zero_nonzero_DeltaA_split68
        _ _ _ _ _ _ _ _ _ _ _ _ hchild.1 hDeltaL
    exact ⟨hDeltaL, hAff, hBaseSplit⟩
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZeroBaseAffine68]
  exact ⟨R, sigmaCell, rCell, sigma, r, hrCell0, hrCell, hsigma, hr0,
    hb, hgm2, hray, hcells⟩

end AlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZeroBaseAffineBackwire68

end Max11DegreeRoutes
