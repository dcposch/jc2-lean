import Sol68ScaleTwoAlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineScratch

/-! # Exact finite determinant cells for the paired `I3(9)`/`I4(9)` rows -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineDeterminant68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

omit [IsAlgClosed k] in
theorem rhoOne_boundaryG_i3_i4_nine_cell_reduction68
    (J N W G b : k)
    (hN : (N = 0 ∧ J = 0) ∨ (N ≠ 0 ∧ b = -J / N))
    (hL : (((8 / 3 : k) * G = 0 ∧ W = 0) ∨
      ((8 / 3 : k) * G ≠ 0 ∧ b = -W / ((8 / 3 : k) * G))))
    (hdet : (8 / 3 : k) * G * J - N * W = 0) :
    (N = 0 ∧ J = 0 ∧
      ((G = 0 ∧ W = 0) ∨
       (G ≠ 0 ∧ b = -(3 : k) * W / ((8 : k) * G)))) ∨
    (N ≠ 0 ∧ b = -J / N ∧
      ((G = 0 ∧ W = 0) ∨
       (G ≠ 0 ∧
        (8 : k) * G * J - 3 * N * W = 0 ∧
        b = -(3 : k) * W / ((8 : k) * G)))) := by
  have h83 : (8 / 3 : k) ≠ 0 := by norm_num
  have htransport (hG : G ≠ 0)
      (hb : b = -W / ((8 / 3 : k) * G)) :
      b = -(3 : k) * W / ((8 : k) * G) := by
    rw [hb]
    field_simp [hG]
  rcases hN with hN0 | hNn
  · left
    refine ⟨hN0.1, hN0.2, ?_⟩
    rcases hL with hL0 | hLn
    · left
      refine ⟨?_, hL0.2⟩
      exact (mul_eq_zero.mp hL0.1).resolve_left h83
    · right
      have hG : G ≠ 0 := by
        intro hG0
        apply hLn.1
        simp [hG0]
      exact ⟨hG, htransport hG hLn.2⟩
  · right
    refine ⟨hNn.1, hNn.2, ?_⟩
    rcases hL with hL0 | hLn
    · left
      refine ⟨?_, hL0.2⟩
      exact (mul_eq_zero.mp hL0.1).resolve_left h83
    · right
      have hG : G ≠ 0 := by
        intro hG0
        apply hLn.1
        simp [hG0]
      refine ⟨hG, ?_, htransport hG hLn.2⟩
      field_simp at hdet
      simpa using hdet

def rhoOne_boundaryG_signedRayLinearDZeroI4NineDeterminantCells68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (sigma r : k) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A
    (rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0))
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  let D0 := 3 * F.coeff 1 - A.coeff (-1) * B.coeff 2
  let J90 := rhoOne_boundaryG_i3nineAtB6_68 T 0
  let N9 := rhoOne_boundaryG_i3nineB6SlopeExpanded68 T
  let W90 := rhoOne_boundaryG_i4nineAtB6_68 T 0
  let G3 := G.coeff 3
  D0 = 0 →
    rhoOne_boundaryG_signedRayLinearDZeroI4NineCells68 T sigma r ∧
    ((N9 = 0 ∧ J90 = 0 ∧
      ((G3 = 0 ∧ W90 = 0) ∨
       (G3 ≠ 0 ∧ B.coeff 6 = -(3 : k) * W90 / ((8 : k) * G3)))) ∨
     (N9 ≠ 0 ∧ B.coeff 6 = -J90 / N9 ∧
      ((G3 = 0 ∧ W90 = 0) ∨
       (G3 ≠ 0 ∧
        (8 : k) * G3 * J90 - 3 * N9 * W90 = 0 ∧
        B.coeff 6 = -(3 : k) * W90 / ((8 : k) * G3)))))

def RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineDeterminant68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : Prop :=
  RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4Nine68 T ∧
  ∃ sigma r : k, r ≠ 0 ∧
    r ^ 2 = -3 * (ratFuncAtHahn46 T.root T.source.A).coeff (-2) ∧
    rhoOne_boundaryG_signedRayLinearDZeroI4NineDeterminantCells68 T sigma r

theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_signedRay_linear_dZero_terminal_zero_B6_slope_wall_i4nine_determinant68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (R : RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4Nine68 T) :
    RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineDeterminant68 T := by
  have Rc := R
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4Nine68] at Rc
  rcases Rc.2.2 with ⟨sigma, r, hr0, hr, hcellsOld⟩
  have hcells : rhoOne_boundaryG_signedRayLinearDZeroI4NineDeterminantCells68
      T sigma r := by
    dsimp only [rhoOne_boundaryG_signedRayLinearDZeroI4NineDeterminantCells68]
    intro hD
    have hold := hcellsOld hD
    have hNold := hold.1 hD
    have hN := hNold.2.2
    have hslope := hNold.2.1
    have hL := hold.2.2.2.2
    have hdet := hold.2.2.2.1
    rw [hslope] at hdet
    dsimp only [rhoOne_boundaryG_i4nineB6Slope68] at hL hdet
    have hred := rhoOne_boundaryG_i3_i4_nine_cell_reduction68
      (rhoOne_boundaryG_i3nineAtB6_68 T 0)
      (rhoOne_boundaryG_i3nineB6SlopeExpanded68 T)
      (rhoOne_boundaryG_i4nineAtB6_68 T 0)
      ((rhoOneTangentEDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0))
        (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.E))).coeff 3)
      ((ratFuncAtHahn46 T.root T.source.B).coeff 6)
      hN hL hdet
    exact ⟨hcellsOld, hred⟩
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineDeterminant68]
  exact ⟨R, sigma, r, hr0, hr, hcells⟩

end AlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineDeterminant68

end Max11DegreeRoutes
