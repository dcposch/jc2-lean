import Sol68ScaleTwoAlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6BackwireScratch

/-! # The terminal-zero `B[6]` row on the frozen `K/M` cells -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6Cells68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

def rhoOne_boundaryG_terminalZeroB6BaseSource68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : k :=
  let A : RatFunc k := T.source.A
  let B : RatFunc k := T.source.B
  let C : RatFunc k := T.source.C0 - RatFunc.C (1 / 3 : k) * A ^ 2
  let F : RatFunc k := T.source.D - RatFunc.C (1 / 3 : k) * A * B
  let E : RatFunc k := T.source.E - RatFunc.C (1 / 27 : k) * A ^ 3
  let G : RatFunc k := E - RatFunc.C (1 / 3 : k) * A * C
  rhoOne_boundaryG_terminalZeroB6Base68 T.source.gamma T.source.epsilon
    (ratFuncAtLaurent46 T.root A) (ratFuncAtLaurent46 T.root B)
    (ratFuncAtLaurent46 T.root C) (ratFuncAtLaurent46 T.root F)
    (ratFuncAtLaurent46 T.root G)
    (ratFuncAtLaurent46 T.root (Differential.deriv A))
    (ratFuncAtLaurent46 T.root (Differential.deriv B))
    (ratFuncAtLaurent46 T.root (Differential.deriv C))
    (ratFuncAtLaurent46 T.root (Differential.deriv F))
    (ratFuncAtLaurent46 T.root (Differential.deriv G))

def rhoOne_boundaryG_terminalZeroB6SlopeSource68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : k :=
  let A : RatFunc k := T.source.A
  let C : RatFunc k := T.source.C0 - RatFunc.C (1 / 3 : k) * A ^ 2
  let E : RatFunc k := T.source.E - RatFunc.C (1 / 27 : k) * A ^ 3
  let G : RatFunc k := E - RatFunc.C (1 / 3 : k) * A * C
  rhoOne_boundaryG_terminalZeroB6Slope68
    (ratFuncAtLaurent46 T.root A) (ratFuncAtLaurent46 T.root G)
    (ratFuncAtLaurent46 T.root (Differential.deriv A))

omit [IsAlgClosed k] in
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_terminal_zero_B6_affine68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) :
    rhoOne_boundaryG_terminalZeroB6SourceRow68 T =
      rhoOne_boundaryG_terminalZeroB6BaseSource68 T +
        rhoOne_boundaryG_terminalZeroB6SlopeSource68 T *
          (ratFuncAtHahn46 T.root T.source.B).coeff 6 := by
  have hcs := ratFuncAtHahn46_coeff_int68 T.root T.source.B 6
  norm_num at hcs
  dsimp only [rhoOne_boundaryG_terminalZeroB6SourceRow68,
    rhoOne_boundaryG_terminalZeroB6BaseSource68,
    rhoOne_boundaryG_terminalZeroB6SlopeSource68,
    rhoOne_boundaryG_terminalZeroAtB6_68]
  rw [hcs]

def rhoOne_boundaryG_signedRayLinearDZeroTerminalZeroB6MSplit68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (sigma r : k) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
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
  rhoOne_boundaryG_signedRayLinearDZeroTerminalZeroExpandedMSplit68 T sigma r ∧
  rhoOne_boundaryG_terminalZeroB6SourceRow68 T = 0 ∧
  ((M = 0 ∧ N8 * Base - Slope * J80 = 0 ∧
      G2 * Base - Slope * V0 = 0) ∨
   (M ≠ 0 ∧ M * Base - Slope * K0 = 0))

def rhoOne_boundaryG_signedRayLinearDZeroTerminalZeroB6Cells68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (sigma r : k) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let D0 := 3 * F.coeff 1 - A.coeff (-1) * B.coeff 2
  D0 = 0 →
    rhoOne_boundaryG_signedRayLinearDZeroTerminalZeroExpandedCells68 T sigma r ∧
    rhoOne_boundaryG_signedRayLinearDZeroTerminalZeroB6MSplit68 T sigma r

def RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6Cells68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroExpansion68 T ∧
  rhoOne_boundaryG_terminalZeroB6SourceRow68 T = 0 ∧
  ∃ sigma r : k, sigma ^ 2 = 1 ∧ r ≠ 0 ∧ B.coeff 2 ≠ 0 ∧
    G.coeff (-2) ≠ 0 ∧ r ^ 2 = -3 * A.coeff (-2) ∧
    27 * G.coeff (-1) = sigma * r ^ 3 * B.coeff 2 ∧
    r * F.coeff 0 = 3 * sigma * G.coeff (-1) ∧
    3 * C.coeff 1 + sigma * r * B.coeff 2 = 0 ∧ B.coeff 3 = 0 ∧
    rhoOne_boundaryG_signedRayLinearDZeroKWallWitness68 T sigma r ∧
    rhoOne_boundaryG_signedRayLinearDZeroTerminalZeroB6Cells68 T sigma r

theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_signedRay_linear_dZero_terminal_zero_B6_cells68
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (Q : RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u)
    (R : RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroExpansion68 T) :
    RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6Cells68 T := by
  have Rc := R
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroExpansion68] at Rc
  rcases Rc with ⟨Rold, hright, hexpanded, sigma, r, hsigma, hr0, hb, hgm2,
    hr, hray, hrf, hlinear, hb3, hwitness, hcellsOld⟩
  have hsource := T.rhoOne_boundaryG_terminal_zero_B6_source68
    hp hH hp6 hp5 hp4 Q hexpanded
  have hcells : rhoOne_boundaryG_signedRayLinearDZeroTerminalZeroB6Cells68
      T sigma r := by
    dsimp only [rhoOne_boundaryG_signedRayLinearDZeroTerminalZeroB6Cells68]
    intro hD
    have hold := hcellsOld hD
    have hs := hold.2
    have hterminalSplit := hs.1
    have hi4split := hterminalSplit.1
    have hi3split := hi4split.1
    have hi4seven := hi3split.1
    have hJactual := hi3split.2.1
    have hVactual := hi4split.2.1
    have hJaff := rhoOne_boundaryG_signedRayLinear_dZero_i3eight_affine68
      T sigma r ((ratFuncAtHahn46 T.root T.source.B).coeff 6)
    have hVaff := rhoOne_boundaryG_signedRayLinear_dZero_i4eight_affine68
      T sigma r ((ratFuncAtHahn46 T.root T.source.B).coeff 6)
    dsimp only at hJaff hVaff
    have hJ : rhoOne_boundaryG_signedRayLinearDZeroI3EightAtB6_68
          T sigma r 0 + rhoOne_boundaryG_signedRayLinearDZeroI3EightSlope68
            T r * (ratFuncAtHahn46 T.root T.source.B).coeff 6 = 0 := by
      rw [← hJaff]; exact hJactual
    have hV : rhoOne_boundaryG_signedRayLinearDZeroI4EightAtB6_68
          T sigma r 0 + (rhoOneTangentEDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.C0))
            (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.E))).coeff 2 *
            (ratFuncAtHahn46 T.root T.source.B).coeff 6 = 0 := by
      rw [← hVaff]; exact hVactual
    have haff := T.rhoOne_boundaryG_terminal_zero_B6_affine68
    have hT : rhoOne_boundaryG_terminalZeroB6BaseSource68 T +
        rhoOne_boundaryG_terminalZeroB6SlopeSource68 T *
          (ratFuncAtHahn46 T.root T.source.B).coeff 6 = 0 := by
      rw [← haff]; exact hsource
    have hnew : rhoOne_boundaryG_signedRayLinearDZeroTerminalZeroB6MSplit68
        T sigma r := by
      dsimp only [rhoOne_boundaryG_signedRayLinearDZeroI4SevenMSplit68] at hi4seven
      rcases hi4seven with hm | hm
      · have hdJ := rhoOne_boundaryG_signedRayLinear_i4eight_cross68
          (rhoOne_boundaryG_terminalZeroB6BaseSource68 T)
          (rhoOne_boundaryG_terminalZeroB6SlopeSource68 T)
          (rhoOne_boundaryG_signedRayLinearDZeroI3EightAtB6_68 T sigma r 0)
          (rhoOne_boundaryG_signedRayLinearDZeroI3EightSlope68 T r)
          ((ratFuncAtHahn46 T.root T.source.B).coeff 6) hT hJ
        have hdV := rhoOne_boundaryG_signedRayLinear_i4eight_cross68
          (rhoOne_boundaryG_terminalZeroB6BaseSource68 T)
          (rhoOne_boundaryG_terminalZeroB6SlopeSource68 T)
          (rhoOne_boundaryG_signedRayLinearDZeroI4EightAtB6_68 T sigma r 0)
          ((rhoOneTangentEDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.C0))
            (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.E))).coeff 2)
          ((ratFuncAtHahn46 T.root T.source.B).coeff 6) hT hV
        dsimp only [rhoOne_boundaryG_signedRayLinearDZeroTerminalZeroB6MSplit68]
        exact ⟨hs, hsource, Or.inl ⟨hm.1, hdJ, hdV⟩⟩
      · have ht := rhoOne_boundaryG_signedRayLinear_dZero_i3seven_M_transport68
          ((rhoOneTangentEDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.C0))
            (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.E))).coeff 0 +
              (3 / 4 : k) * T.source.epsilon)
          (rhoOne_boundaryG_signedRayLinearDZeroI4SixAtB6_68 T sigma r 0)
          (rhoOne_boundaryG_terminalZeroB6BaseSource68 T)
          (rhoOne_boundaryG_terminalZeroB6SlopeSource68 T)
          ((ratFuncAtHahn46 T.root T.source.B).coeff 6)
          hm.1 hm.2.1 hT
        dsimp only [rhoOne_boundaryG_signedRayLinearDZeroTerminalZeroB6MSplit68]
        exact ⟨hs, hsource, Or.inr ⟨hm.1, ht⟩⟩
    exact ⟨hcellsOld, hnew⟩
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6Cells68]
  exact ⟨R, hsource, sigma, r, hsigma, hr0, hb, hgm2, hr, hray,
    hrf, hlinear, hb3, hwitness, hcells⟩

end AlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6Cells68

end Max11DegreeRoutes
