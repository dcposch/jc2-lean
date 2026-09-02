import Sol68ScaleTwoAlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroScratch

/-! # Product expansion of terminal coefficient zero and its quotient endpoint -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroExpansion68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

omit [IsAlgClosed k] in
def rhoOne_boundaryG_terminalZeroProductRow68
    (gamma epsilon : k)
    (A B C F G dA dB dC dF dG : HahnSeries ℚ k) : k :=
  (-(2 / 3 : k) * gamma) * (F * dC).coeff 0 +
  (-(1 / 3 : k) * epsilon) * (F * dA).coeff 0 +
  (-(4 / 9 : k)) * (F * G * dA).coeff 0 +
  (-(4 / 9 : k)) * (F * F * dB).coeff 0 +
  (-(4 / 9 : k)) * (C * F * dC).coeff 0 +
  ((2 / 3 : k) * gamma) * (B * dG).coeff 0 +
  (-(4 / 9 : k)) * (B * F * dF).coeff 0 +
  (4 / 9 : k) * (B * C * dG).coeff 0 +
  ((2 / 9 : k) * gamma) * (B * C * dA).coeff 0 +
  (4 / 27 : k) * (B * C * C * dA).coeff 0 +
  (-(2 / 9 : k) * gamma) * (A * F * dA).coeff 0 +
  (-(4 / 27 : k)) * (A * F * dA * C).coeff 0 +
  (-(1 / 9 : k) * epsilon) * (A * B * dA).coeff 0 +
  (-(4 / 27 : k)) * (A * B * G * dA).coeff 0 +
  (-(4 / 27 : k)) * (A * B * F * dB).coeff 0 +
  (-(4 / 27 : k)) * (A * B * B * dF).coeff 0

omit [IsAlgClosed k] in
theorem rhoOneMainTangentTerminal_coeff_zero_product68
    (gamma epsilon : k)
    (A B C F G dA dB dC dF dG : HahnSeries ℚ k) :
    (rhoOneMainTangentTerminal68 (HahnSeries.C gamma)
      (HahnSeries.C epsilon) A B C F G dA dB dC dF dG).coeff 0 =
      rhoOne_boundaryG_terminalZeroProductRow68 gamma epsilon
        A B C F G dA dB dC dF dG := by
  have hscale (s : k) (X : HahnSeries ℚ k) (n : ℚ) :
      (HahnSeries.C s * X).coeff n = s * X.coeff n := by
    rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]
  have hrewrite :
      rhoOneMainTangentTerminal68 (HahnSeries.C gamma)
        (HahnSeries.C epsilon) A B C F G dA dB dC dF dG =
      HahnSeries.C (-(2 / 3 : k) * gamma) * (F * dC) +
      HahnSeries.C (-(1 / 3 : k) * epsilon) * (F * dA) +
      HahnSeries.C (-(4 / 9 : k)) * (F * G * dA) +
      HahnSeries.C (-(4 / 9 : k)) * (F * F * dB) +
      HahnSeries.C (-(4 / 9 : k)) * (C * F * dC) +
      HahnSeries.C ((2 / 3 : k) * gamma) * (B * dG) +
      HahnSeries.C (-(4 / 9 : k)) * (B * F * dF) +
      HahnSeries.C (4 / 9 : k) * (B * C * dG) +
      HahnSeries.C ((2 / 9 : k) * gamma) * (B * C * dA) +
      HahnSeries.C (4 / 27 : k) * (B * C * C * dA) +
      HahnSeries.C (-(2 / 9 : k) * gamma) * (A * F * dA) +
      HahnSeries.C (-(4 / 27 : k)) * (A * F * dA * C) +
      HahnSeries.C (-(1 / 9 : k) * epsilon) * (A * B * dA) +
      HahnSeries.C (-(4 / 27 : k)) * (A * B * G * dA) +
      HahnSeries.C (-(4 / 27 : k)) * (A * B * F * dB) +
      HahnSeries.C (-(4 / 27 : k)) * (A * B * B * dF) := by
    simp only [rhoOneMainTangentTerminal68, HahnSeries.C_eq_algebraMap,
      map_mul, map_add, map_neg, map_div₀, map_ofNat, map_one]
    ring
  rw [hrewrite]
  simp only [HahnSeries.coeff_add, hscale,
    rhoOne_boundaryG_terminalZeroProductRow68]

def rhoOne_boundaryG_terminalZeroExpandedSourceRow68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : k :=
  let A : RatFunc k := T.source.A
  let B : RatFunc k := T.source.B
  let C : RatFunc k := T.source.C0 - RatFunc.C (1 / 3 : k) * A ^ 2
  let F : RatFunc k := T.source.D - RatFunc.C (1 / 3 : k) * A * B
  let E : RatFunc k := T.source.E - RatFunc.C (1 / 27 : k) * A ^ 3
  let G : RatFunc k := E - RatFunc.C (1 / 3 : k) * A * C
  rhoOne_boundaryG_terminalZeroProductRow68
    T.source.gamma T.source.epsilon
    (ratFuncAtHahn46 T.root A) (ratFuncAtHahn46 T.root B)
    (ratFuncAtHahn46 T.root C) (ratFuncAtHahn46 T.root F)
    (ratFuncAtHahn46 T.root G)
    (ratFuncAtHahn46 T.root (Differential.deriv A))
    (ratFuncAtHahn46 T.root (Differential.deriv B))
    (ratFuncAtHahn46 T.root (Differential.deriv C))
    (ratFuncAtHahn46 T.root (Differential.deriv F))
    (ratFuncAtHahn46 T.root (Differential.deriv G))

omit [IsAlgClosed k] in
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_terminal_zero_quotient68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) :
    rhoOne_boundaryG_terminalZeroRight68 T = 0 := by
  obtain ⟨c, hc, hsingle, hderiv⟩ :=
    ratFuncAtHahn68_linearRoot_single_deriv
      h0 T.root T.scale_degree T.root_eq
  dsimp only [rhoOne_boundaryG_terminalZeroRight68]
  rw [map_div₀, ratFuncAtHahn46_C, hsingle, div_eq_mul_inv,
    HahnSeries.inv_single, HahnSeries.C_apply,
    HahnSeries.single_mul_single]
  norm_num

omit [IsAlgClosed k] in
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_terminal_zero_expanded68
    {p q : k[X][X]} {j : k} {h0 g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (Q : RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u) :
    rhoOne_boundaryG_terminalZeroExpandedSourceRow68 T = 0 := by
  have hsource := T.rhoOne_boundaryG_terminal_zero_source68 Q
  have hright := T.rhoOne_boundaryG_terminal_zero_quotient68
  have hleft : rhoOne_boundaryG_terminalZeroLeft68 T = 0 := by
    dsimp only [rhoOne_boundaryG_terminalZeroSourceRow68] at hsource
    linear_combination hsource + hright
  dsimp only [rhoOne_boundaryG_terminalZeroExpandedSourceRow68]
  dsimp only [rhoOne_boundaryG_terminalZeroLeft68] at hleft
  rw [rhoOneMainTangentTerminal_coeff_zero_product68] at hleft
  exact hleft

def rhoOne_boundaryG_signedRayLinearDZeroTerminalZeroExpandedMSplit68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (sigma r : k) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  let M := G.coeff 0 + (3 / 4 : k) * T.source.epsilon
  rhoOne_boundaryG_signedRayLinearDZeroTerminalZeroMSplit68 T sigma r ∧
  rhoOne_boundaryG_terminalZeroRight68 T = 0 ∧
  rhoOne_boundaryG_terminalZeroExpandedSourceRow68 T = 0 ∧
  ((M = 0 ∧ rhoOne_boundaryG_terminalZeroLeft68 T = 0) ∨
   (M ≠ 0 ∧ rhoOne_boundaryG_terminalZeroLeft68 T = 0))

def rhoOne_boundaryG_signedRayLinearDZeroTerminalZeroExpandedCells68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (sigma r : k) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let D0 := 3 * F.coeff 1 - A.coeff (-1) * B.coeff 2
  D0 = 0 →
    rhoOne_boundaryG_signedRayLinearDZeroTerminalZeroCells68 T sigma r ∧
    rhoOne_boundaryG_signedRayLinearDZeroTerminalZeroExpandedMSplit68 T sigma r

def RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroExpansion68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZero68 T ∧
  rhoOne_boundaryG_terminalZeroRight68 T = 0 ∧
  rhoOne_boundaryG_terminalZeroExpandedSourceRow68 T = 0 ∧
  ∃ sigma r : k, sigma ^ 2 = 1 ∧ r ≠ 0 ∧ B.coeff 2 ≠ 0 ∧
    G.coeff (-2) ≠ 0 ∧ r ^ 2 = -3 * A.coeff (-2) ∧
    27 * G.coeff (-1) = sigma * r ^ 3 * B.coeff 2 ∧
    r * F.coeff 0 = 3 * sigma * G.coeff (-1) ∧
    3 * C.coeff 1 + sigma * r * B.coeff 2 = 0 ∧ B.coeff 3 = 0 ∧
    rhoOne_boundaryG_signedRayLinearDZeroKWallWitness68 T sigma r ∧
    rhoOne_boundaryG_signedRayLinearDZeroTerminalZeroExpandedCells68 T sigma r

theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_signedRay_linear_dZero_terminal_zero_expansion68
    {p q : k[X][X]} {j : k} {h0 g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (Q : RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u)
    (R : RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZero68 T) :
    RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroExpansion68 T := by
  have hright := T.rhoOne_boundaryG_terminal_zero_quotient68
  have hexpanded := T.rhoOne_boundaryG_terminal_zero_expanded68 Q
  have Rc := R
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZero68] at Rc
  rcases Rc with ⟨Rold, hsource, sigma, r, hsigma, hr0, hb, hgm2,
    hr, hray, hrf, hlinear, hb3, hwitness, hcellsOld⟩
  have hleft : rhoOne_boundaryG_terminalZeroLeft68 T = 0 := by
    dsimp only [rhoOne_boundaryG_terminalZeroSourceRow68] at hsource
    linear_combination hsource + hright
  have hcells : rhoOne_boundaryG_signedRayLinearDZeroTerminalZeroExpandedCells68
      T sigma r := by
    dsimp only [rhoOne_boundaryG_signedRayLinearDZeroTerminalZeroExpandedCells68]
    intro hD
    have hold := hcellsOld hD
    have hsplit := hold.2
    have hnew : rhoOne_boundaryG_signedRayLinearDZeroTerminalZeroExpandedMSplit68
        T sigma r := by
      have hc := hsplit
      dsimp only [rhoOne_boundaryG_signedRayLinearDZeroTerminalZeroMSplit68] at hc
      rcases hc.2.2 with hm | hm
      · dsimp only [rhoOne_boundaryG_signedRayLinearDZeroTerminalZeroExpandedMSplit68]
        exact ⟨hsplit, hright, hexpanded, Or.inl ⟨hm.1, hleft⟩⟩
      · dsimp only [rhoOne_boundaryG_signedRayLinearDZeroTerminalZeroExpandedMSplit68]
        exact ⟨hsplit, hright, hexpanded, Or.inr ⟨hm.1, hleft⟩⟩
    exact ⟨hcellsOld, hnew⟩
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroExpansion68]
  exact ⟨R, hright, hexpanded, sigma, r, hsigma, hr0, hb, hgm2,
    hr, hray, hrf, hlinear, hb3, hwitness, hcells⟩

end AlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroExpansion68

end Max11DegreeRoutes
