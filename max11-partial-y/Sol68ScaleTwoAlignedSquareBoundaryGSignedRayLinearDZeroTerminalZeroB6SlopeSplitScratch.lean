import Sol68ScaleTwoAlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6CellsScratch

/-! # Zero/nonzero split of the isolated terminal `B[6]` slope -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6SlopeSplit68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

omit [IsAlgClosed k] in
theorem affine_zero_slope_cells68 (Base Slope b : k)
    (h : Base + Slope * b = 0) :
    (Slope = 0 ∧ Base = 0) ∨
      (Slope ≠ 0 ∧ b = -Base / Slope) := by
  by_cases hs : Slope = 0
  · left
    constructor
    · exact hs
    · rw [hs] at h
      simpa using h
  · right
    refine ⟨hs, ?_⟩
    field_simp
    linear_combination h

omit [IsAlgClosed k] in
theorem affine_nonzero_slope_transport68 (Base Slope X Y : k)
    (hSlope : Slope ≠ 0) (h : X * Base - Slope * Y = 0) :
    Y = X * Base / Slope := by
  field_simp
  linear_combination -h

def rhoOne_boundaryG_signedRayLinearDZeroTerminalZeroB6SlopeMSplit68
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
  let Base := rhoOne_boundaryG_terminalZeroB6BaseSource68 T
  let Slope := rhoOne_boundaryG_terminalZeroB6SlopeSource68 T
  rhoOne_boundaryG_signedRayLinearDZeroTerminalZeroB6MSplit68 T sigma r ∧
  ((M = 0 ∧
      ((Slope = 0 ∧ Base = 0) ∨
       (Slope ≠ 0 ∧ B.coeff 6 = -Base / Slope ∧
        J80 = N8 * Base / Slope ∧ V0 = G2 * Base / Slope))) ∨
   (M ≠ 0 ∧
      ((Slope = 0 ∧ Base = 0) ∨
       (Slope ≠ 0 ∧ B.coeff 6 = -Base / Slope ∧
        K0 = M * Base / Slope))))

def rhoOne_boundaryG_signedRayLinearDZeroTerminalZeroB6SlopeCells68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (sigma r : k) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let D0 := 3 * F.coeff 1 - A.coeff (-1) * B.coeff 2
  D0 = 0 →
    rhoOne_boundaryG_signedRayLinearDZeroTerminalZeroB6Cells68 T sigma r ∧
    rhoOne_boundaryG_signedRayLinearDZeroTerminalZeroB6SlopeMSplit68 T sigma r

def RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeSplit68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6Cells68 T ∧
  ∃ sigma r : k, sigma ^ 2 = 1 ∧ r ≠ 0 ∧ B.coeff 2 ≠ 0 ∧
    G.coeff (-2) ≠ 0 ∧ r ^ 2 = -3 * A.coeff (-2) ∧
    27 * G.coeff (-1) = sigma * r ^ 3 * B.coeff 2 ∧
    r * F.coeff 0 = 3 * sigma * G.coeff (-1) ∧
    3 * C.coeff 1 + sigma * r * B.coeff 2 = 0 ∧ B.coeff 3 = 0 ∧
    rhoOne_boundaryG_signedRayLinearDZeroKWallWitness68 T sigma r ∧
    rhoOne_boundaryG_signedRayLinearDZeroTerminalZeroB6SlopeCells68 T sigma r

theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_signedRay_linear_dZero_terminal_zero_B6_slope_split68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (R : RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6Cells68 T) :
    RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeSplit68 T := by
  have Rc := R
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6Cells68] at Rc
  rcases Rc with ⟨Rold, hsource, sigma, r, hsigma, hr0, hb, hgm2,
    hr, hray, hrf, hlinear, hb3, hwitness, hcellsOld⟩
  have hcells : rhoOne_boundaryG_signedRayLinearDZeroTerminalZeroB6SlopeCells68
      T sigma r := by
    dsimp only [rhoOne_boundaryG_signedRayLinearDZeroTerminalZeroB6SlopeCells68]
    intro hD
    have hold := hcellsOld hD
    have hs := hold.2
    have hrow := hs.2.1
    have haff := T.rhoOne_boundaryG_terminal_zero_B6_affine68
    have hT : rhoOne_boundaryG_terminalZeroB6BaseSource68 T +
        rhoOne_boundaryG_terminalZeroB6SlopeSource68 T *
          (ratFuncAtHahn46 T.root T.source.B).coeff 6 = 0 := by
      rw [← haff]; exact hrow
    have hbasic := affine_zero_slope_cells68
      (rhoOne_boundaryG_terminalZeroB6BaseSource68 T)
      (rhoOne_boundaryG_terminalZeroB6SlopeSource68 T)
      ((ratFuncAtHahn46 T.root T.source.B).coeff 6) hT
    have hnew : rhoOne_boundaryG_signedRayLinearDZeroTerminalZeroB6SlopeMSplit68
        T sigma r := by
      have hsc := hs
      dsimp only [rhoOne_boundaryG_signedRayLinearDZeroTerminalZeroB6MSplit68] at hsc
      rcases hsc.2.2 with hm | hm
      · rcases hbasic with hz | hn
        · dsimp only [rhoOne_boundaryG_signedRayLinearDZeroTerminalZeroB6SlopeMSplit68]
          exact ⟨hs, Or.inl ⟨hm.1, Or.inl hz⟩⟩
        · have hJ := affine_nonzero_slope_transport68
            (rhoOne_boundaryG_terminalZeroB6BaseSource68 T)
            (rhoOne_boundaryG_terminalZeroB6SlopeSource68 T)
            (rhoOne_boundaryG_signedRayLinearDZeroI3EightSlope68 T r)
            (rhoOne_boundaryG_signedRayLinearDZeroI3EightAtB6_68 T sigma r 0)
            hn.1 hm.2.1
          have hV := affine_nonzero_slope_transport68
            (rhoOne_boundaryG_terminalZeroB6BaseSource68 T)
            (rhoOne_boundaryG_terminalZeroB6SlopeSource68 T)
            ((rhoOneTangentEDefectHahn68
              (ratFuncAtHahn46 T.root T.source.A)
              (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                (ratFuncAtHahn46 T.root T.source.C0))
              (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                (ratFuncAtHahn46 T.root T.source.E))).coeff 2)
            (rhoOne_boundaryG_signedRayLinearDZeroI4EightAtB6_68 T sigma r 0)
            hn.1 hm.2.2
          dsimp only [rhoOne_boundaryG_signedRayLinearDZeroTerminalZeroB6SlopeMSplit68]
          exact ⟨hs, Or.inl ⟨hm.1, Or.inr ⟨hn.1, hn.2, hJ, hV⟩⟩⟩
      · rcases hbasic with hz | hn
        · dsimp only [rhoOne_boundaryG_signedRayLinearDZeroTerminalZeroB6SlopeMSplit68]
          exact ⟨hs, Or.inr ⟨hm.1, Or.inl hz⟩⟩
        · have hK := affine_nonzero_slope_transport68
            (rhoOne_boundaryG_terminalZeroB6BaseSource68 T)
            (rhoOne_boundaryG_terminalZeroB6SlopeSource68 T)
            ((rhoOneTangentEDefectHahn68
              (ratFuncAtHahn46 T.root T.source.A)
              (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                (ratFuncAtHahn46 T.root T.source.C0))
              (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                (ratFuncAtHahn46 T.root T.source.E))).coeff 0 +
                (3 / 4 : k) * T.source.epsilon)
            (rhoOne_boundaryG_signedRayLinearDZeroI4SixAtB6_68 T sigma r 0)
            hn.1 hm.2
          dsimp only [rhoOne_boundaryG_signedRayLinearDZeroTerminalZeroB6SlopeMSplit68]
          exact ⟨hs, Or.inr ⟨hm.1, Or.inr ⟨hn.1, hn.2, hK⟩⟩⟩
    exact ⟨hcellsOld, hnew⟩
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeSplit68]
  exact ⟨R, sigma, r, hsigma, hr0, hb, hgm2, hr, hray, hrf,
    hlinear, hb3, hwitness, hcells⟩

end AlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6SlopeSplit68

end Max11DegreeRoutes
