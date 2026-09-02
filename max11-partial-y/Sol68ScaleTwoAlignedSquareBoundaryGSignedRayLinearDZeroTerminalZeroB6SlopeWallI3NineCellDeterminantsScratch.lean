import Sol68ScaleTwoAlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6SlopeWallI3NineReductionScratch

/-! # Determinant reductions on the exact `I3(9)` slope cells -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6SlopeWallI3NineCellDeterminants68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

omit [IsAlgClosed k] in
theorem rhoOne_boundaryG_i3nine_equation_of_terminal_transport68
    (J N Base Slope b : k) (hSlope : Slope ≠ 0)
    (hb : b = -Base / Slope)
    (hdet : N * Base - Slope * J = 0) :
    J + N * b = 0 := by
  have hJ := affine_nonzero_slope_transport68 Base Slope N J hSlope hdet
  rw [hb, hJ]
  field_simp [hSlope]
  ring

omit [IsAlgClosed k] in
theorem rhoOne_boundaryG_i3nine_transport_cross68
    (Base Slope X Y U V : k) (hSlope : Slope ≠ 0)
    (hY : Y = X * Base / Slope)
    (hV : U * Base - Slope * V = 0) :
    U * Y - X * V = 0 := by
  have hV' := affine_nonzero_slope_transport68 Base Slope U V hSlope hV
  rw [hY, hV']
  ring

def rhoOne_boundaryG_signedRayLinearDZeroI3NineCellDeterminantMSplit68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (sigma r : k) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  let K0 := rhoOne_boundaryG_signedRayLinearDZeroI4SixAtB6_68 T sigma r 0
  let M := G.coeff 0 + (3 / 4 : k) * T.source.epsilon
  let J80 := rhoOne_boundaryG_signedRayLinearDZeroI3EightAtB6_68 T sigma r 0
  let N8 := rhoOne_boundaryG_signedRayLinearDZeroI3EightSlope68 T r
  let V0 := rhoOne_boundaryG_signedRayLinearDZeroI4EightAtB6_68 T sigma r 0
  let G2 := G.coeff 2
  let Slope := rhoOne_boundaryG_terminalZeroB6SlopeSource68 T
  let J90 := rhoOne_boundaryG_i3nineAtB6_68 T 0
  let N9 := rhoOne_boundaryG_i3nineB6Slope68 T
  rhoOne_boundaryG_signedRayLinearDZeroI3NineSlopeWallMSplit68 T sigma r ∧
  ((N9 = 0 ∧ J90 = 0) ∨
   (N9 ≠ 0 ∧ B.coeff 6 = -J90 / N9)) ∧
  (M = 0 → Slope ≠ 0 →
    N9 * J80 - N8 * J90 = 0 ∧
    N9 * V0 - G2 * J90 = 0) ∧
  (M ≠ 0 → Slope ≠ 0 →
    N9 * K0 - M * J90 = 0)

def rhoOne_boundaryG_signedRayLinearDZeroI3NineCellDeterminantCells68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (sigma r : k) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let D0 := 3 * F.coeff 1 - A.coeff (-1) * B.coeff 2
  D0 = 0 →
    rhoOne_boundaryG_signedRayLinearDZeroI3NineSlopeWallCells68 T sigma r ∧
    rhoOne_boundaryG_signedRayLinearDZeroI3NineCellDeterminantMSplit68 T sigma r

def RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI3NineCellDeterminants68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : Prop :=
  RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI3NineReduction68 T ∧
  ∃ sigma r : k, r ≠ 0 ∧
    r ^ 2 = -3 * (ratFuncAtHahn46 T.root T.source.A).coeff (-2) ∧
    rhoOne_boundaryG_signedRayLinearDZeroI3NineCellDeterminantCells68 T sigma r

theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_signedRay_linear_dZero_terminal_zero_B6_slope_wall_i3nine_cell_determinants68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (R : RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI3NineReduction68 T) :
    RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI3NineCellDeterminants68 T := by
  have Rc := R
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI3NineReduction68] at Rc
  rcases Rc.2 with ⟨sigma, r, hr0, hr, hcellsOld⟩
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  let K0 := rhoOne_boundaryG_signedRayLinearDZeroI4SixAtB6_68 T sigma r 0
  let M := G.coeff 0 + (3 / 4 : k) * T.source.epsilon
  let J80 := rhoOne_boundaryG_signedRayLinearDZeroI3EightAtB6_68 T sigma r 0
  let N8 := rhoOne_boundaryG_signedRayLinearDZeroI3EightSlope68 T r
  let V0 := rhoOne_boundaryG_signedRayLinearDZeroI4EightAtB6_68 T sigma r 0
  let G2 := G.coeff 2
  let Base := rhoOne_boundaryG_terminalZeroB6BaseSource68 T
  let Slope := rhoOne_boundaryG_terminalZeroB6SlopeSource68 T
  let J90 := rhoOne_boundaryG_i3nineAtB6_68 T 0
  let N9 := rhoOne_boundaryG_i3nineB6Slope68 T
  have hcells : rhoOne_boundaryG_signedRayLinearDZeroI3NineCellDeterminantCells68
      T sigma r := by
    dsimp only [rhoOne_boundaryG_signedRayLinearDZeroI3NineCellDeterminantCells68]
    intro hD
    have hold := hcellsOld hD
    have hs := hold.2
    have hsc := hs
    dsimp only [rhoOne_boundaryG_signedRayLinearDZeroI3NineSlopeWallMSplit68] at hsc
    have hNsplit : (N9 = 0 ∧ J90 = 0) ∨
        (N9 ≠ 0 ∧ B.coeff 6 = -J90 / N9) := by
      rcases hsc.2 with hm | hm
      · rcases hm.2 with hz | hn
        · exact hz.2.2.2
        · have hJ : J90 + N9 * B.coeff 6 = 0 :=
            rhoOne_boundaryG_i3nine_equation_of_terminal_transport68
              J90 N9 Base Slope (B.coeff 6) hn.1 hn.2.1 hn.2.2.2.2
          exact rhoOne_boundaryG_i3nine_zero_slope_split68 J90 N9
            (B.coeff 6) hJ
      · rcases hm.2 with hz | hn
        · exact hz.2.2.2
        · have hJ : J90 + N9 * B.coeff 6 = 0 :=
            rhoOne_boundaryG_i3nine_equation_of_terminal_transport68
              J90 N9 Base Slope (B.coeff 6) hn.1 hn.2.1 hn.2.2.2
          exact rhoOne_boundaryG_i3nine_zero_slope_split68 J90 N9
            (B.coeff 6) hJ
    have hMzero : M = 0 → Slope ≠ 0 →
        N9 * J80 - N8 * J90 = 0 ∧
        N9 * V0 - G2 * J90 = 0 := by
      intro hM hSlope
      rcases hsc.2 with hm | hm
      · rcases hm.2 with hz | hn
        · exact False.elim (hSlope hz.1)
        · exact ⟨
            rhoOne_boundaryG_i3nine_transport_cross68 Base Slope N8 J80
              N9 J90 hSlope hn.2.2.1 hn.2.2.2.2,
            rhoOne_boundaryG_i3nine_transport_cross68 Base Slope G2 V0
              N9 J90 hSlope hn.2.2.2.1 hn.2.2.2.2⟩
      · exact False.elim (hm.1 hM)
    have hMnonzero : M ≠ 0 → Slope ≠ 0 →
        N9 * K0 - M * J90 = 0 := by
      intro hM hSlope
      rcases hsc.2 with hm | hm
      · exact False.elim (hM hm.1)
      · rcases hm.2 with hz | hn
        · exact False.elim (hSlope hz.1)
        · exact rhoOne_boundaryG_i3nine_transport_cross68 Base Slope M K0
            N9 J90 hSlope hn.2.2.1 hn.2.2.2
    have hnew : rhoOne_boundaryG_signedRayLinearDZeroI3NineCellDeterminantMSplit68
        T sigma r := by
      dsimp only [rhoOne_boundaryG_signedRayLinearDZeroI3NineCellDeterminantMSplit68]
      exact ⟨hs, hNsplit, hMzero, hMnonzero⟩
    have hold' : rhoOne_boundaryG_signedRayLinearDZeroI3NineSlopeWallCells68
        T sigma r := hcellsOld
    exact ⟨hold', hnew⟩
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI3NineCellDeterminants68]
  exact ⟨R, sigma, r, hr0, hr, hcells⟩

end AlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6SlopeWallI3NineCellDeterminants68

end Max11DegreeRoutes
