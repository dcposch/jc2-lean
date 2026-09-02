import Sol68ScaleTwoAlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedDeterminantTransportScratch

/-! # The zero-terminal-slope child of the normalized `K11` wall -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZero68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

omit [IsAlgClosed k] in
theorem rhoOne_boundaryG_K11_slope_wall_transport68
    (sigma r a am1 b gm2 gm1 da2 : k) (hgm2 : gm2 ≠ 0)
    (hray : 27 * gm1 = sigma * r ^ 3 * b)
    (hWall : gm2 * da2 - 2 * a * gm1 - 2 * am1 * gm2 = 0) :
    da2 - 2 * am1 =
      (2 * a * sigma * r ^ 3 * b) / (27 * gm2) := by
  have hden : (27 : k) * gm2 ≠ 0 := mul_ne_zero (by norm_num) hgm2
  apply (eq_div_iff hden).2
  linear_combination 27 * hWall + (2 * a) * hray

def rhoOne_boundaryG_signedRayLinearDZeroI4NineK11NormalizedSlopeZeroCells68
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
  let TerminalWall := rhoOne_boundaryG_terminalZeroB6SlopeWallSource68 T
  let J90 := rhoOne_boundaryG_i3nineAtB6_68 T 0
  let N9 := rhoOne_boundaryG_i3nineB6SlopeExpanded68 T
  let G3 := G.coeff 3
  let Wall := rhoOne_boundaryG_i4nineK11NormalizedWall68 T r
  D0 = 0 →
    rhoOne_boundaryG_signedRayLinearDZeroI4NineK11NormalizedDeterminantTransportCells68
      T sigmaCell rCell sigma r ∧
    (N9 ≠ 0 ∧ G3 ≠ 0 ∧
      (8 : k) * G3 * J90 - 3 * N9 * rhoOne_boundaryG_i4nineAtB6_68 T 0 = 0 →
      Wall = 0 → Slope = 0 →
      Base = 0 ∧ TerminalWall = 0 ∧
      dA.coeff (-2) - 2 * A.coeff (-1) =
        (2 * A.coeff (-2) * sigma * r ^ 3 * B.coeff 2) /
          (27 * G.coeff (-2)))

def RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZero68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : Prop :=
  RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedDeterminantTransport68 T ∧
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
    rhoOne_boundaryG_signedRayLinearDZeroI4NineK11NormalizedSlopeZeroCells68
      T sigmaCell rCell sigma r

theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_signedRay_linear_dZero_terminal_zero_B6_slope_wall_i4nine_K11_normalized_slope_zero68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (R : RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedDeterminantTransport68 T) :
    RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZero68 T := by
  have Rc := R
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedDeterminantTransport68] at Rc
  rcases Rc.2 with ⟨sigmaCell, rCell, sigma, r, hrCell0, hrCell,
    hsigma, hr0, hb, hgm2, hray, hPrevCells⟩
  let Ar : RatFunc k := T.source.A
  let Br : RatFunc k := T.source.B
  let Cr : RatFunc k := T.source.C0 - RatFunc.C (1 / 3 : k) * Ar ^ 2
  let Er : RatFunc k := T.source.E - RatFunc.C (1 / 27 : k) * Ar ^ 3
  let Gr : RatFunc k := Er - RatFunc.C (1 / 3 : k) * Ar * Cr
  let A := ratFuncAtHahn46 T.root Ar
  let B := ratFuncAtHahn46 T.root Br
  let C := ratFuncAtHahn46 T.root Cr
  let G := ratFuncAtHahn46 T.root Gr
  let dA := ratFuncAtHahn46 T.root (Differential.deriv Ar)
  have hCmap : C = rhoOneCDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.C0) := by
    dsimp only [C, Cr, Ar, rhoOneCDefectHahn68]
    simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
  have hEmap : ratFuncAtHahn46 T.root Er = rhoOneEDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.E) := by
    dsimp only [Er, Ar, rhoOneEDefectHahn68]
    simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
  have hGmap : G = rhoOneTangentEDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0))
      (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.E)) := by
    dsimp only [G, Gr, rhoOneTangentEDefectHahn68]
    rw [map_sub, map_mul, hEmap, map_mul, ratFuncAtHahn46_C]
    rw [show ratFuncAtHahn46 T.root Cr =
        rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0) by
      simpa only [C] using hCmap]
  have hcells :
      rhoOne_boundaryG_signedRayLinearDZeroI4NineK11NormalizedSlopeZeroCells68
        T sigmaCell rCell sigma r := by
    dsimp only [rhoOne_boundaryG_signedRayLinearDZeroI4NineK11NormalizedSlopeZeroCells68]
    intro hD
    have hPrev := hPrevCells hD
    have hNorm := hPrev.1 hD
    have hB11 := hNorm.1 hD
    have hDet := hB11.1 hD
    have hI4 := hDet.1 hD
    have hJet := hI4.1 hD
    have hI3Det := hJet.1 hD
    have hMSplit := hI3Det.2
    dsimp only [rhoOne_boundaryG_signedRayLinearDZeroI3NineCellDeterminantMSplit68] at hMSplit
    have hSlopeWallSplit := hMSplit.1
    dsimp only [rhoOne_boundaryG_signedRayLinearDZeroI3NineSlopeWallMSplit68] at hSlopeWallSplit
    refine ⟨hPrevCells, ?_⟩
    intro hdbl hWall hSlope
    have hBaseWall : rhoOne_boundaryG_terminalZeroB6BaseSource68 T = 0 ∧
        rhoOne_boundaryG_terminalZeroB6SlopeWallSource68 T = 0 := by
      rcases hSlopeWallSplit.2 with hm | hm
      · rcases hm.2 with hz | hn
        · exact ⟨hz.2.1, hz.2.2.1⟩
        · exact False.elim (hn.1 hSlope)
      · rcases hm.2 with hz | hn
        · exact ⟨hz.2.1, hz.2.2.1⟩
        · exact False.elim (hn.1 hSlope)
    have hWallH : G.coeff (-2) * dA.coeff (-2) -
        2 * A.coeff (-2) * G.coeff (-1) -
        2 * A.coeff (-1) * G.coeff (-2) = 0 := by
      have hw := hBaseWall.2
      dsimp only [rhoOne_boundaryG_terminalZeroB6SlopeWallSource68,
        rhoOne_boundaryG_terminalZeroB6SlopeWall68] at hw
      have htoL (X : RatFunc k) (n : ℤ) :
          (ratFuncAtLaurent46 T.root X).coeff n =
            (ratFuncAtHahn46 T.root X).coeff n := by
        rw [ratFuncAtHahn46_coeff_int68]
      rw [htoL Gr (-2), htoL (Differential.deriv Ar) (-2),
        htoL Ar (-2), htoL Gr (-1), htoL Ar (-1)] at hw
      norm_num at hw ⊢
      simpa only [A, G, dA, Ar, Cr, Er, Gr] using hw
    have htransport := rhoOne_boundaryG_K11_slope_wall_transport68 sigma r
      (A.coeff (-2)) (A.coeff (-1)) (B.coeff 2)
      (G.coeff (-2)) (G.coeff (-1)) (dA.coeff (-2))
      (by simpa only [G, hGmap] using hgm2)
      (by simpa only [B, Br, G, hGmap] using hray) hWallH
    refine ⟨hBaseWall.1, hBaseWall.2, ?_⟩
    simpa only [A, B, Br, G, dA, hGmap] using htransport
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZero68]
  exact ⟨R, sigmaCell, rCell, sigma, r, hrCell0, hrCell, hsigma, hr0,
    hb, hgm2, hray, hcells⟩

end AlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZero68

end Max11DegreeRoutes
