import Sol68ScaleTwoAlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZeroBaseCoeffZeroWallScratch

/-! # Denominator-free transport on the nonzero affine coefficient cell -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZeroBaseCoeffNonzeroTransport68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

omit [IsAlgClosed k] in
theorem rhoOne_boundaryG_terminalZeroB6_affine_transport_cross68
    (sigma r a b gm2 gm1 coeff const delta : k)
    (hgm2 : gm2 ≠ 0)
    (hray : 27 * gm1 = sigma * r ^ 3 * b)
    (htransport : delta = (2 * a * sigma * r ^ 3 * b) / (27 * gm2))
    (haffine : const + coeff * delta = 0) :
    gm2 * const + 2 * a * gm1 * coeff = 0 := by
  have hden : (27 : k) * gm2 ≠ 0 := mul_ne_zero (by norm_num) hgm2
  have htransportClear :
      delta * (27 * gm2) - 2 * a * sigma * r ^ 3 * b = 0 := by
    have ht := (eq_div_iff hden).mp htransport
    linear_combination ht
  have hDeltaClear : gm2 * delta - 2 * a * gm1 = 0 := by
    linear_combination (1 / 27 : k) * htransportClear -
      (2 * a / 27 : k) * (hray)
  linear_combination gm2 * haffine - coeff * hDeltaClear

def rhoOne_boundaryG_signedRayLinearDZeroI4NineK11NormalizedSlopeZeroBaseCoeffTransportCells68
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
    rhoOne_boundaryG_signedRayLinearDZeroI4NineK11NormalizedSlopeZeroBaseCoeffWallCells68
      T sigmaCell rCell sigma r ∧
    (N9 ≠ 0 ∧ G3 ≠ 0 ∧
      (8 : k) * G3 * J90 - 3 * N9 * rhoOne_boundaryG_i4nineAtB6_68 T 0 = 0 →
      Wall = 0 → Slope = 0 →
      ((CoeffX = 0 ∧ Const = 0) ∨
       (CoeffX ≠ 0 ∧ Const ≠ 0 ∧ DeltaA = -Const / CoeffX ∧
        G.coeff (-2) * Const +
          2 * A.coeff (-2) * G.coeff (-1) * CoeffX = 0)))

def RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZeroBaseCoeffTransport68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : Prop :=
  RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZeroBaseCoeffWall68 T ∧
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
    rhoOne_boundaryG_signedRayLinearDZeroI4NineK11NormalizedSlopeZeroBaseCoeffTransportCells68
      T sigmaCell rCell sigma r

theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_signedRay_linear_dZero_terminal_zero_B6_slope_wall_i4nine_K11_normalized_slope_zero_Base_coeff_transport68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (R : RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZeroBaseCoeffWall68 T) :
    RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZeroBaseCoeffTransport68 T := by
  have Rc := R
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZeroBaseCoeffWall68] at Rc
  rcases Rc.2 with ⟨sigmaCell, rCell, sigma, r, hrCell0, hrCell,
    hsigma, hr0, hb, hgm2, hray, hPrevCells⟩
  have hcells :
      rhoOne_boundaryG_signedRayLinearDZeroI4NineK11NormalizedSlopeZeroBaseCoeffTransportCells68
        T sigmaCell rCell sigma r := by
    dsimp only [rhoOne_boundaryG_signedRayLinearDZeroI4NineK11NormalizedSlopeZeroBaseCoeffTransportCells68]
    intro hD
    have hPrev := hPrevCells hD
    refine ⟨hPrevCells, ?_⟩
    intro hdbl hWall hSlope
    have hRefined := hPrev.2 hdbl hWall hSlope
    rcases hRefined with hz | hn
    · exact Or.inl hz
    · right
      have hBaseAffine := hPrev.1 hD
      have hAffineLeaf := hBaseAffine.2 hdbl hWall hSlope
      have hObstruction := hBaseAffine.1 hD
      have hTransportLeaf := hObstruction.2 hdbl hWall hSlope
      have hCoeff := T.rhoOne_boundaryG_terminal_zero_B6_DeltaCoeff_expanded68
      have hEq := hAffineLeaf.2.2.1
      rw [hCoeff] at hEq
      have htoL (X : RatFunc k) (n : ℤ) :
          (ratFuncAtLaurent46 T.root X).coeff n =
            (ratFuncAtHahn46 T.root X).coeff n := by
        rw [ratFuncAtHahn46_coeff_int68]
      have hDeltaTransport :
          rhoOne_boundaryG_terminalZeroB6DeltaASource68 T =
            (2 * (ratFuncAtHahn46 T.root T.source.A).coeff (-2) * sigma * r ^ 3 *
              (ratFuncAtHahn46 T.root T.source.B).coeff 2) /
              (27 * (rhoOneTangentEDefectHahn68
                (ratFuncAtHahn46 T.root T.source.A)
                (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                  (ratFuncAtHahn46 T.root T.source.C0))
                (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                  (ratFuncAtHahn46 T.root T.source.E))).coeff (-2)) := by
        dsimp only [rhoOne_boundaryG_terminalZeroB6DeltaASource68]
        rw [htoL (Differential.deriv T.source.A) (-2),
          htoL T.source.A (-1)]
        exact hTransportLeaf.2.1
      have hCross := rhoOne_boundaryG_terminalZeroB6_affine_transport_cross68
        sigma r
        ((ratFuncAtHahn46 T.root T.source.A).coeff (-2))
        ((ratFuncAtHahn46 T.root T.source.B).coeff 2)
        ((rhoOneTangentEDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.C0))
          (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.E))).coeff (-2))
        ((rhoOneTangentEDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.C0))
          (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.E))).coeff (-1))
        (rhoOne_boundaryG_terminalZeroB6DeltaCoeffExpandedSource68 T)
        (rhoOne_boundaryG_terminalZeroB6DeltaConstantSource68 T)
        (rhoOne_boundaryG_terminalZeroB6DeltaASource68 T)
        hgm2 hray hDeltaTransport hEq
      exact ⟨hn.1, hn.2.1, hn.2.2, hCross⟩
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZeroBaseCoeffTransport68]
  exact ⟨R, sigmaCell, rCell, sigma, r, hrCell0, hrCell, hsigma, hr0,
    hb, hgm2, hray, hcells⟩

end AlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZeroBaseCoeffNonzeroTransport68

end Max11DegreeRoutes
