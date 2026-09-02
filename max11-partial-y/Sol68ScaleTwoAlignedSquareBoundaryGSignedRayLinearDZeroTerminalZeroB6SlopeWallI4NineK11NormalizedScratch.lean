import Sol68ScaleTwoAlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11FactorScratch

/-! # Sigma-free normalization of the ninth-row `B[11]` slope wall -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11Normalized68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

omit [IsAlgClosed k] in
theorem rhoOne_boundaryG_K11_wall_normalize68
    (sigma r b gm1 gm2 g3 n : k) (hsigma : sigma ^ 2 = 1)
    (hray : 27 * gm1 = sigma * r ^ 3 * b) :
    27 * (8 * sigma * r * g3 * gm1 - 9 * n * gm2) =
      8 * r ^ 4 * b * g3 - 243 * n * gm2 := by
  linear_combination (8 * sigma * r * g3) * hray +
    (8 * r ^ 4 * b * g3) * hsigma

omit [IsAlgClosed k] in
theorem rhoOne_boundaryG_K11_normalized_split68
    (D K Wall b : k) (hfac : K = (8 / 243 : k) * Wall)
    (hsplit : (K = 0 ∧ D = 0) ∨ (K ≠ 0 ∧ b = -D / K)) :
    (Wall = 0 ∧ D = 0) ∨
      (Wall ≠ 0 ∧ b = -(243 : k) * D / ((8 : k) * Wall)) := by
  have h8243 : (8 / 243 : k) ≠ 0 := by norm_num
  rcases hsplit with hz | hn
  · left
    refine ⟨?_, hz.2⟩
    have hm : (8 / 243 : k) * Wall = 0 := by rw [← hfac]; exact hz.1
    exact (mul_eq_zero.mp hm).resolve_left h8243
  · right
    have hWall : Wall ≠ 0 := by
      intro hw
      apply hn.1
      rw [hfac, hw, mul_zero]
    refine ⟨hWall, ?_⟩
    rw [hn.2, hfac]
    field_simp [hWall]

omit [IsAlgClosed k] in
theorem rhoOne_boundaryG_K11_normalized_wall_transports68
    (r b g3 n gm2 : k) (hr : r ≠ 0) (hb : b ≠ 0) (hgm2 : gm2 ≠ 0)
    (hWall : 8 * r ^ 4 * b * g3 - 243 * n * gm2 = 0) :
    g3 = (243 * n * gm2) / (8 * r ^ 4 * b) ∧
      n = (8 * r ^ 4 * b * g3) / (243 * gm2) := by
  have hdenG : (8 : k) * r ^ 4 * b ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 4 hr)) hb
  have hdenN : (243 : k) * gm2 ≠ 0 := mul_ne_zero (by norm_num) hgm2
  constructor
  · apply (eq_div_iff hdenG).2
    linear_combination hWall
  · apply (eq_div_iff hdenN).2
    linear_combination -hWall

omit [IsAlgClosed k] in
def rhoOne_boundaryG_i4nineK11NormalizedWall68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (r : k) : k :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  8 * r ^ 4 * B.coeff 2 * G.coeff 3 -
    243 * rhoOne_boundaryG_i3nineB6SlopeExpanded68 T * G.coeff (-2)

def rhoOne_boundaryG_signedRayLinearDZeroI4NineK11NormalizedCells68
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
  let J90 := rhoOne_boundaryG_i3nineAtB6_68 T 0
  let N9 := rhoOne_boundaryG_i3nineB6SlopeExpanded68 T
  let W90 := rhoOne_boundaryG_i4nineAtB6_68 T 0
  let G3 := G.coeff 3
  let J110 := rhoOne_boundaryG_i3nineAtB6B11_68 T 0
  let W110 := rhoOne_boundaryG_i4nineAtB6B11_68 T 0
  let D11 := (8 : k) * G3 * J110 - 3 * N9 * W110
  let K11 := (8 : k) * G3 * ((-(8 / 9 : k)) * (A * F).coeff (-2)) -
    3 * N9 * ((8 / 3 : k) * G.coeff (-2))
  let Wall := rhoOne_boundaryG_i4nineK11NormalizedWall68 T r
  D0 = 0 →
    rhoOne_boundaryG_signedRayLinearDZeroI4NineB11Cells68 T sigmaCell rCell ∧
    K11 = (8 / 243 : k) * Wall ∧
    (N9 ≠ 0 ∧ G3 ≠ 0 ∧
      (8 : k) * G3 * J90 - 3 * N9 * W90 = 0 →
      (Wall = 0 ∧ D11 = 0 ∧
        G3 = (243 * N9 * G.coeff (-2)) /
          ((8 : k) * r ^ 4 * B.coeff 2) ∧
        N9 = ((8 : k) * r ^ 4 * B.coeff 2 * G3) /
          (243 * G.coeff (-2))) ∨
      (Wall ≠ 0 ∧
        B.coeff 11 = -(243 : k) * D11 / ((8 : k) * Wall)))

def RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11Normalized68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : Prop :=
  RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11Factor68 T ∧
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
    rhoOne_boundaryG_signedRayLinearDZeroI4NineK11NormalizedCells68
      T sigmaCell rCell sigma r

theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_signedRay_linear_dZero_terminal_zero_B6_slope_wall_i4nine_K11_normalized68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (R : RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11Factor68 T) :
    RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11Normalized68 T := by
  have Rc := R
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11Factor68] at Rc
  rcases Rc.2 with ⟨sigmaOldCell, rOldCell, sigmaOld, rOld,
    hrOldCell0, hrOldCell, hsigmaOld, hrOld0, hrOld, hrfOld,
    hFactorCellsOld⟩
  have RB11 := Rc.1
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineB11Reduction68] at RB11
  rcases RB11.2 with ⟨sigmaCell, rCell, hrCell0, hrCell, hB11Cells⟩
  have Rdet := RB11.1
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineDeterminant68] at Rdet
  have Ri4 := Rdet.1
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4Nine68] at Ri4
  have Rjet := Ri4.1
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI3NineSlopeJet68] at Rjet
  have Rcells := Rjet.1
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI3NineCellDeterminants68] at Rcells
  have Rred := Rcells.1
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI3NineReduction68] at Rred
  have Ri3 := Rred.1
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI3Nine68] at Ri3
  have Rwall := Ri3.1
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWall68] at Rwall
  have Rsplit := Rwall.1
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeSplit68] at Rsplit
  rcases Rsplit.2 with ⟨sigma, r, hsigma, hr0, hb, hgm2, hr, hray,
    hrf, hlinear, hb3, hwitness, hsourceCells⟩
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  have hcells : rhoOne_boundaryG_signedRayLinearDZeroI4NineK11NormalizedCells68
      T sigmaCell rCell sigma r := by
    dsimp only [rhoOne_boundaryG_signedRayLinearDZeroI4NineK11NormalizedCells68]
    intro hD
    have hOld := hB11Cells hD
    have hFactorOld := hFactorCellsOld hD
    have hAF := hFactorOld.2.1
    have hfacSigned :
        (8 : k) * G.coeff 3 * ((-(8 / 9 : k)) * (A * F).coeff (-2)) -
            3 * rhoOne_boundaryG_i3nineB6SlopeExpanded68 T *
              ((8 / 3 : k) * G.coeff (-2)) =
          (8 / 9 : k) * rhoOne_boundaryG_i4nineK11Wall68 T sigma r := by
      rw [hAF]
      dsimp only [rhoOne_boundaryG_i4nineK11Wall68, A, B, C, F, G]
      simpa only [mul_assoc] using rhoOne_boundaryG_K11_signed_factor68 sigma r
        ((ratFuncAtHahn46 T.root T.source.A).coeff (-2))
        ((rhoOneTangentDDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.B)
          (ratFuncAtHahn46 T.root T.source.D)).coeff 0)
        ((rhoOneTangentEDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.C0))
          (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.E))).coeff (-1))
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
            (ratFuncAtHahn46 T.root T.source.E))).coeff 3)
        (rhoOne_boundaryG_i3nineB6SlopeExpanded68 T) hr0 hr hrf
    have hnorm := rhoOne_boundaryG_K11_wall_normalize68 sigma r
      (B.coeff 2) (G.coeff (-1)) (G.coeff (-2)) (G.coeff 3)
      (rhoOne_boundaryG_i3nineB6SlopeExpanded68 T) hsigma hray
    have hfac :
        (8 : k) * G.coeff 3 * ((-(8 / 9 : k)) * (A * F).coeff (-2)) -
            3 * rhoOne_boundaryG_i3nineB6SlopeExpanded68 T *
              ((8 / 3 : k) * G.coeff (-2)) =
          (8 / 243 : k) * rhoOne_boundaryG_i4nineK11NormalizedWall68 T r := by
      rw [hfacSigned]
      have hwallEq :
          27 * rhoOne_boundaryG_i4nineK11Wall68 T sigma r =
            rhoOne_boundaryG_i4nineK11NormalizedWall68 T r := by
        dsimp only [rhoOne_boundaryG_i4nineK11Wall68,
          rhoOne_boundaryG_i4nineK11NormalizedWall68, A, B, C, F, G]
        exact hnorm
      calc
        (8 / 9 : k) * rhoOne_boundaryG_i4nineK11Wall68 T sigma r =
            (8 / 243 : k) *
              (27 * rhoOne_boundaryG_i4nineK11Wall68 T sigma r) := by ring
        _ = (8 / 243 : k) * rhoOne_boundaryG_i4nineK11NormalizedWall68 T r := by
          rw [hwallEq]
    refine ⟨hB11Cells, hfac, ?_⟩
    intro hdbl
    have hsplit := hOld.2 hdbl
    have hnormSplit := rhoOne_boundaryG_K11_normalized_split68
      ((8 : k) * G.coeff 3 * rhoOne_boundaryG_i3nineAtB6B11_68 T 0 -
        3 * rhoOne_boundaryG_i3nineB6SlopeExpanded68 T *
          rhoOne_boundaryG_i4nineAtB6B11_68 T 0)
      ((8 : k) * G.coeff 3 * ((-(8 / 9 : k)) * (A * F).coeff (-2)) -
        3 * rhoOne_boundaryG_i3nineB6SlopeExpanded68 T *
          ((8 / 3 : k) * G.coeff (-2)))
      (rhoOne_boundaryG_i4nineK11NormalizedWall68 T r)
      (B.coeff 11) hfac hsplit.2.2.2
    rcases hnormSplit with hzero | hnonzero
    · left
      refine ⟨hzero.1, hzero.2, ?_⟩
      dsimp only [rhoOne_boundaryG_i4nineK11NormalizedWall68] at hzero
      exact rhoOne_boundaryG_K11_normalized_wall_transports68 r
        (B.coeff 2) (G.coeff 3)
        (rhoOne_boundaryG_i3nineB6SlopeExpanded68 T) (G.coeff (-2))
        hr0 hb hgm2 hzero.1
    · exact Or.inr hnonzero
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11Normalized68]
  exact ⟨R, sigmaCell, rCell, sigma, r, hrCell0, hrCell, hsigma, hr0,
    hb, hgm2, hray, hcells⟩

end AlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11Normalized68

end Max11DegreeRoutes
