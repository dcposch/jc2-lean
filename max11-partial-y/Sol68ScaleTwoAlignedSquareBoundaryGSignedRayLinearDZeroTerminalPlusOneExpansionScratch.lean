import Sol68ScaleTwoAlignedSquareBoundaryGSignedRayLinearDZeroTerminalPlusOneSourceScratch

/-! # Product expansion of terminal coefficient plus one and its quotient endpoint -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareBoundaryGSignedRayLinearDZeroTerminalPlusOneExpansion68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

omit [IsAlgClosed k] in
def rhoOne_boundaryG_terminalPlusOneProductRow68
    (gamma epsilon : k)
    (A B C F G dA dB dC dF dG : HahnSeries ℚ k) : k :=
  (-(2 / 3 : k) * gamma) * (F * dC).coeff 1 +
  (-(1 / 3 : k) * epsilon) * (F * dA).coeff 1 +
  (-(4 / 9 : k)) * (F * G * dA).coeff 1 +
  (-(4 / 9 : k)) * (F * F * dB).coeff 1 +
  (-(4 / 9 : k)) * (C * F * dC).coeff 1 +
  ((2 / 3 : k) * gamma) * (B * dG).coeff 1 +
  (-(4 / 9 : k)) * (B * F * dF).coeff 1 +
  (4 / 9 : k) * (B * C * dG).coeff 1 +
  ((2 / 9 : k) * gamma) * (B * C * dA).coeff 1 +
  (4 / 27 : k) * (B * C * C * dA).coeff 1 +
  (-(2 / 9 : k) * gamma) * (A * F * dA).coeff 1 +
  (-(4 / 27 : k)) * (A * F * dA * C).coeff 1 +
  (-(1 / 9 : k) * epsilon) * (A * B * dA).coeff 1 +
  (-(4 / 27 : k)) * (A * B * G * dA).coeff 1 +
  (-(4 / 27 : k)) * (A * B * F * dB).coeff 1 +
  (-(4 / 27 : k)) * (A * B * B * dF).coeff 1

omit [IsAlgClosed k] in
theorem rhoOneMainTangentTerminal_coeff_plus_one_product68
    (gamma epsilon : k)
    (A B C F G dA dB dC dF dG : HahnSeries ℚ k) :
    (rhoOneMainTangentTerminal68 (HahnSeries.C gamma)
      (HahnSeries.C epsilon) A B C F G dA dB dC dF dG).coeff 1 =
      rhoOne_boundaryG_terminalPlusOneProductRow68 gamma epsilon
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
    rhoOne_boundaryG_terminalPlusOneProductRow68]


def rhoOne_boundaryG_terminalPlusOneExpandedSourceRow68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : k :=
  let A : RatFunc k := T.source.A
  let B : RatFunc k := T.source.B
  let C : RatFunc k := T.source.C0 - RatFunc.C (1 / 3 : k) * A ^ 2
  let F : RatFunc k := T.source.D - RatFunc.C (1 / 3 : k) * A * B
  let E : RatFunc k := T.source.E - RatFunc.C (1 / 27 : k) * A ^ 3
  let G : RatFunc k := E - RatFunc.C (1 / 3 : k) * A * C
  rhoOne_boundaryG_terminalPlusOneProductRow68
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
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_terminal_plus_one_expanded_eq_left68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) :
    rhoOne_boundaryG_terminalPlusOneExpandedSourceRow68 T =
      rhoOne_boundaryG_terminalPlusOneLeft68 T := by
  dsimp only [rhoOne_boundaryG_terminalPlusOneExpandedSourceRow68,
    rhoOne_boundaryG_terminalPlusOneLeft68]
  rw [rhoOneMainTangentTerminal_coeff_plus_one_product68]

def RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalPlusOneExpanded68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : Prop :=
  RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalPlusOneSource68 T ∧
  rhoOne_boundaryG_terminalPlusOneExpandedSourceRow68 T = 0

theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_terminal_plus_one_expanded_backwire68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (R : RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalPlusOneSource68 T) :
    RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalPlusOneExpanded68 T := by
  have heq := T.rhoOne_boundaryG_terminal_plus_one_expanded_eq_left68
  have hrow : rhoOne_boundaryG_terminalPlusOneExpandedSourceRow68 T = 0 := by
    rw [heq]
    exact R.2.2.2
  exact ⟨R, hrow⟩

end AlignedSquareBoundaryGSignedRayLinearDZeroTerminalPlusOneExpansion68

end Max11DegreeRoutes
