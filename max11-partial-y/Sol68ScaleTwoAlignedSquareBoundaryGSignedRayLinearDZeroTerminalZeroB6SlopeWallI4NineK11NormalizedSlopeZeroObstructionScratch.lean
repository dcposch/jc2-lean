import Sol68ScaleTwoAlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZeroScratch

/-! # Nonzero derivative obstruction on the normalized zero-slope cell -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZeroObstruction68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

omit [IsAlgClosed k] in
theorem rhoOne_boundaryG_K11_slope_transport_nonzero68
    (sigma r a am1 b gm2 da2 : k)
    (hsigma : sigma ^ 2 = 1) (hr : r ≠ 0) (ha : a ≠ 0)
    (hb : b ≠ 0) (hgm2 : gm2 ≠ 0)
    (htransport : da2 - 2 * am1 =
      (2 * a * sigma * r ^ 3 * b) / (27 * gm2)) :
    da2 - 2 * am1 ≠ 0 := by
  have hsigma0 : sigma ≠ 0 := by
    intro hz
    rw [hz] at hsigma
    norm_num at hsigma
  have hnum : (2 : k) * a * sigma * r ^ 3 * b ≠ 0 :=
    mul_ne_zero
      (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) ha) hsigma0)
        (pow_ne_zero 3 hr)) hb
  have hden : (27 : k) * gm2 ≠ 0 := mul_ne_zero (by norm_num) hgm2
  rw [htransport]
  exact div_ne_zero hnum hden

def rhoOne_boundaryG_signedRayLinearDZeroI4NineK11NormalizedSlopeZeroObstructionCells68
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
  let dA := ratFuncAtHahn46 T.root (Differential.deriv T.source.A)
  let D0 := 3 * F.coeff 1 - A.coeff (-1) * B.coeff 2
  let Base := rhoOne_boundaryG_terminalZeroB6BaseSource68 T
  let Slope := rhoOne_boundaryG_terminalZeroB6SlopeSource68 T
  let J90 := rhoOne_boundaryG_i3nineAtB6_68 T 0
  let N9 := rhoOne_boundaryG_i3nineB6SlopeExpanded68 T
  let G3 := G.coeff 3
  let Wall := rhoOne_boundaryG_i4nineK11NormalizedWall68 T r
  D0 = 0 →
    rhoOne_boundaryG_signedRayLinearDZeroI4NineK11NormalizedSlopeZeroCells68
      T sigmaCell rCell sigma r ∧
    (N9 ≠ 0 ∧ G3 ≠ 0 ∧
      (8 : k) * G3 * J90 - 3 * N9 * rhoOne_boundaryG_i4nineAtB6_68 T 0 = 0 →
      Wall = 0 → Slope = 0 →
      Base = 0 ∧
      dA.coeff (-2) - 2 * A.coeff (-1) =
        (2 * A.coeff (-2) * sigma * r ^ 3 * B.coeff 2) /
          (27 * G.coeff (-2)) ∧
      dA.coeff (-2) - 2 * A.coeff (-1) ≠ 0)

def RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZeroObstruction68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : Prop :=
  RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZero68 T ∧
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
    rhoOne_boundaryG_signedRayLinearDZeroI4NineK11NormalizedSlopeZeroObstructionCells68
      T sigmaCell rCell sigma r

theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_signedRay_linear_dZero_terminal_zero_B6_slope_wall_i4nine_K11_normalized_slope_zero_obstruction68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (R : RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZero68 T) :
    RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZeroObstruction68 T := by
  have Rc := R
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZero68] at Rc
  rcases Rc.2 with ⟨sigmaCell, rCell, sigma, r, hrCell0, hrCell,
    hsigma, hr0, hb, hgm2, hray, hPrevCells⟩
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  let dA := ratFuncAtHahn46 T.root (Differential.deriv T.source.A)
  have ha : A.coeff (-2) ≠ 0 := by
    intro ha0
    have hrz : rCell ^ 2 = 0 := by rw [hrCell, ha0]; ring
    exact (pow_ne_zero 2 hrCell0) hrz
  have hcells :
      rhoOne_boundaryG_signedRayLinearDZeroI4NineK11NormalizedSlopeZeroObstructionCells68
        T sigmaCell rCell sigma r := by
    dsimp only [rhoOne_boundaryG_signedRayLinearDZeroI4NineK11NormalizedSlopeZeroObstructionCells68]
    intro hD
    have hPrev := hPrevCells hD
    refine ⟨hPrevCells, ?_⟩
    intro hdbl hWall hSlope
    have hchild := hPrev.2 hdbl hWall hSlope
    have hnonzero := rhoOne_boundaryG_K11_slope_transport_nonzero68 sigma r
      (A.coeff (-2)) (A.coeff (-1)) (B.coeff 2) (G.coeff (-2))
      (dA.coeff (-2)) hsigma hr0 ha hb hgm2 hchild.2.2
    exact ⟨hchild.1, hchild.2.2, hnonzero⟩
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZeroObstruction68]
  exact ⟨R, sigmaCell, rCell, sigma, r, hrCell0, hrCell, hsigma, hr0,
    hb, hgm2, hray, hcells⟩

end AlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZeroObstruction68

end Max11DegreeRoutes
