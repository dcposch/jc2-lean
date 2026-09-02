import Sol68ScaleTwoAlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedScratch

/-! # Independent lower-row transports on the normalized `K11` zero wall -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedDeterminantTransport68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

omit [IsAlgClosed k] in
theorem rhoOne_boundaryG_K11_normalized_wall_two_transports68
    (r b g3 n gm2 j80 n8 j90 v0 g2 : k)
    (hr : r ≠ 0) (hb : b ≠ 0) (hg3 : g3 ≠ 0)
    (hWall : 8 * r ^ 4 * b * g3 - 243 * n * gm2 = 0)
    (hJ : n * j80 - n8 * j90 = 0)
    (hV : n * v0 - g2 * j90 = 0) :
    j80 = (243 * gm2 * n8 * j90) / (8 * r ^ 4 * b * g3) ∧
      v0 = (243 * gm2 * g2 * j90) / (8 * r ^ 4 * b * g3) := by
  have hden : (8 : k) * r ^ 4 * b * g3 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 4 hr)) hb) hg3
  constructor
  · apply (eq_div_iff hden).2
    linear_combination j80 * hWall + (243 * gm2) * hJ
  · apply (eq_div_iff hden).2
    linear_combination v0 * hWall + (243 * gm2) * hV

omit [IsAlgClosed k] in
theorem rhoOne_boundaryG_K11_normalized_wall_one_transport68
    (r b g3 n gm2 k0 m j90 : k)
    (hr : r ≠ 0) (hb : b ≠ 0) (hg3 : g3 ≠ 0)
    (hWall : 8 * r ^ 4 * b * g3 - 243 * n * gm2 = 0)
    (hK : n * k0 - m * j90 = 0) :
    k0 = (243 * gm2 * m * j90) / (8 * r ^ 4 * b * g3) := by
  have hden : (8 : k) * r ^ 4 * b * g3 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 4 hr)) hb) hg3
  apply (eq_div_iff hden).2
  linear_combination k0 * hWall + (243 * gm2) * hK

def rhoOne_boundaryG_signedRayLinearDZeroI4NineK11NormalizedDeterminantTransportCells68
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
  let M := G.coeff 0 + (3 / 4 : k) * T.source.epsilon
  let Slope := rhoOne_boundaryG_terminalZeroB6SlopeSource68 T
  let J80 := rhoOne_boundaryG_signedRayLinearDZeroI3EightAtB6_68 T sigmaCell rCell 0
  let N8 := rhoOne_boundaryG_signedRayLinearDZeroI3EightSlope68 T rCell
  let V0 := rhoOne_boundaryG_signedRayLinearDZeroI4EightAtB6_68 T sigmaCell rCell 0
  let G2 := G.coeff 2
  let K0 := rhoOne_boundaryG_signedRayLinearDZeroI4SixAtB6_68 T sigmaCell rCell 0
  let J90 := rhoOne_boundaryG_i3nineAtB6_68 T 0
  let N9 := rhoOne_boundaryG_i3nineB6SlopeExpanded68 T
  let G3 := G.coeff 3
  let Wall := rhoOne_boundaryG_i4nineK11NormalizedWall68 T r
  D0 = 0 →
    rhoOne_boundaryG_signedRayLinearDZeroI4NineK11NormalizedCells68
      T sigmaCell rCell sigma r ∧
    (N9 ≠ 0 ∧ G3 ≠ 0 ∧
      (8 : k) * G3 * J90 - 3 * N9 * rhoOne_boundaryG_i4nineAtB6_68 T 0 = 0 →
      Wall = 0 →
      (Slope = 0 ∨
       (Slope ≠ 0 ∧
        ((M = 0 ∧
          J80 = (243 * G.coeff (-2) * N8 * J90) /
            ((8 : k) * r ^ 4 * B.coeff 2 * G3) ∧
          V0 = (243 * G.coeff (-2) * G2 * J90) /
            ((8 : k) * r ^ 4 * B.coeff 2 * G3)) ∨
         (M ≠ 0 ∧
          K0 = (243 * G.coeff (-2) * M * J90) /
            ((8 : k) * r ^ 4 * B.coeff 2 * G3))))))

def RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedDeterminantTransport68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : Prop :=
  RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11Normalized68 T ∧
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
    rhoOne_boundaryG_signedRayLinearDZeroI4NineK11NormalizedDeterminantTransportCells68
      T sigmaCell rCell sigma r

theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_signedRay_linear_dZero_terminal_zero_B6_slope_wall_i4nine_K11_normalized_determinant_transport68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (R : RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11Normalized68 T) :
    RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedDeterminantTransport68 T := by
  have Rc := R
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11Normalized68] at Rc
  rcases Rc.2 with ⟨sigmaCell, rCell, sigma, r, hrCell0, hrCell,
    hsigma, hr0, hb, hgm2, hray, hNormCells⟩
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  have hcells :
      rhoOne_boundaryG_signedRayLinearDZeroI4NineK11NormalizedDeterminantTransportCells68
        T sigmaCell rCell sigma r := by
    dsimp only [rhoOne_boundaryG_signedRayLinearDZeroI4NineK11NormalizedDeterminantTransportCells68]
    intro hD
    have hNorm := hNormCells hD
    have hB11 := hNorm.1 hD
    have hDet := hB11.1 hD
    have hI4 := hDet.1 hD
    have hJet := hI4.1 hD
    have hI3Det := hJet.1 hD
    have hMSplit := hI3Det.2
    dsimp only [rhoOne_boundaryG_signedRayLinearDZeroI3NineCellDeterminantMSplit68] at hMSplit
    refine ⟨hNormCells, ?_⟩
    intro hdbl hWall
    by_cases hSlope : rhoOne_boundaryG_terminalZeroB6SlopeSource68 T = 0
    · exact Or.inl hSlope
    · right
      refine ⟨hSlope, ?_⟩
      by_cases hM : G.coeff 0 + (3 / 4 : k) * T.source.epsilon = 0
      · left
        have hrows := hMSplit.2.2.1 hM hSlope
        rw [hJet.2.1] at hrows
        have htransport := rhoOne_boundaryG_K11_normalized_wall_two_transports68 r
          (B.coeff 2) (G.coeff 3)
          (rhoOne_boundaryG_i3nineB6SlopeExpanded68 T) (G.coeff (-2))
          (rhoOne_boundaryG_signedRayLinearDZeroI3EightAtB6_68 T sigmaCell rCell 0)
          (rhoOne_boundaryG_signedRayLinearDZeroI3EightSlope68 T rCell)
          (rhoOne_boundaryG_i3nineAtB6_68 T 0)
          (rhoOne_boundaryG_signedRayLinearDZeroI4EightAtB6_68 T sigmaCell rCell 0)
          (G.coeff 2) hr0 hb hdbl.2.1 hWall hrows.1 hrows.2
        exact ⟨hM, htransport.1, htransport.2⟩
      · right
        have hrow := hMSplit.2.2.2 hM hSlope
        rw [hJet.2.1] at hrow
        have htransport := rhoOne_boundaryG_K11_normalized_wall_one_transport68 r
          (B.coeff 2) (G.coeff 3)
          (rhoOne_boundaryG_i3nineB6SlopeExpanded68 T) (G.coeff (-2))
          (rhoOne_boundaryG_signedRayLinearDZeroI4SixAtB6_68 T sigmaCell rCell 0)
          (G.coeff 0 + (3 / 4 : k) * T.source.epsilon)
          (rhoOne_boundaryG_i3nineAtB6_68 T 0) hr0 hb hdbl.2.1 hWall hrow
        exact ⟨hM, htransport⟩
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedDeterminantTransport68]
  exact ⟨R, sigmaCell, rCell, sigma, r, hrCell0, hrCell, hsigma, hr0,
    hb, hgm2, hray, hcells⟩

end AlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedDeterminantTransport68

end Max11DegreeRoutes
