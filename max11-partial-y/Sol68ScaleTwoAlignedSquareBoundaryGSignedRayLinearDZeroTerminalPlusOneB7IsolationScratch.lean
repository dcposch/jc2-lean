import Sol68ScaleTwoAlignedSquareBoundaryGSignedRayLinearDZeroTerminalPlusOneExpansionScratch

/-! # Exact `B[7]` reduction of terminal coefficient plus one

The coefficient-plus-one product row is retained verbatim.  We separate its
`B[7]` multiple with exactly the already verified terminal-zero `B[6]` slope.
Consequently the frozen zero-slope cells acquire one genuinely new scalar row.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareBoundaryGSignedRayLinearDZeroTerminalPlusOneB7Isolation68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

def rhoOne_boundaryG_terminalPlusOneB7Source68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : k :=
  (ratFuncAtHahn46 T.root T.source.B).coeff 7

def rhoOne_boundaryG_terminalPlusOneB7BaseSource68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : k :=
  rhoOne_boundaryG_terminalPlusOneExpandedSourceRow68 T -
    rhoOne_boundaryG_terminalZeroB6SlopeSource68 T *
      rhoOne_boundaryG_terminalPlusOneB7Source68 T

omit [IsAlgClosed k] in
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_terminal_plus_one_B7_affine68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) :
    rhoOne_boundaryG_terminalPlusOneExpandedSourceRow68 T =
      rhoOne_boundaryG_terminalPlusOneB7BaseSource68 T +
        rhoOne_boundaryG_terminalZeroB6SlopeSource68 T *
          rhoOne_boundaryG_terminalPlusOneB7Source68 T := by
  dsimp only [rhoOne_boundaryG_terminalPlusOneB7BaseSource68]
  ring

omit [IsAlgClosed k] in
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_terminal_plus_one_B7_base_zero68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hrow : rhoOne_boundaryG_terminalPlusOneExpandedSourceRow68 T = 0)
    (hslope : rhoOne_boundaryG_terminalZeroB6SlopeSource68 T = 0) :
    rhoOne_boundaryG_terminalPlusOneB7BaseSource68 T = 0 := by
  have haffine := T.rhoOne_boundaryG_terminal_plus_one_B7_affine68
  rw [hslope] at haffine
  linear_combination hrow - haffine

def rhoOne_boundaryG_terminalPlusOneB7AffineCellReduction68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : Prop :=
  let Slope := rhoOne_boundaryG_terminalZeroB6SlopeSource68 T
  let CoeffX := rhoOne_boundaryG_terminalZeroB6DeltaCoeffExpandedSource68 T
  let Const := rhoOne_boundaryG_terminalZeroB6DeltaConstantSource68 T
  let DeltaA := rhoOne_boundaryG_terminalZeroB6DeltaASource68 T
  let BasePlusOne := rhoOne_boundaryG_terminalPlusOneB7BaseSource68 T
  (Slope = 0 -> CoeffX = 0 -> Const = 0 ->
    CoeffX = 0 ∧ Const = 0 ∧ BasePlusOne = 0) ∧
  (Slope = 0 -> CoeffX ≠ 0 -> Const ≠ 0 ->
    DeltaA = -Const / CoeffX ->
    CoeffX ≠ 0 ∧ Const ≠ 0 ∧ DeltaA = -Const / CoeffX ∧
      BasePlusOne = 0)

def RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalPlusOneB7Isolation68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : Prop :=
  RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalPlusOneExpanded68 T ∧
  rhoOne_boundaryG_terminalPlusOneExpandedSourceRow68 T =
    rhoOne_boundaryG_terminalPlusOneB7BaseSource68 T +
      rhoOne_boundaryG_terminalZeroB6SlopeSource68 T *
        rhoOne_boundaryG_terminalPlusOneB7Source68 T ∧
  (rhoOne_boundaryG_terminalZeroB6SlopeSource68 T = 0 ->
    rhoOne_boundaryG_terminalPlusOneB7BaseSource68 T = 0) ∧
  rhoOne_boundaryG_terminalPlusOneB7AffineCellReduction68 T

theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_terminal_plus_one_B7_isolation68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (R : RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalPlusOneExpanded68 T) :
    RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalPlusOneB7Isolation68 T := by
  have haffine := T.rhoOne_boundaryG_terminal_plus_one_B7_affine68
  have hbase (hslope : rhoOne_boundaryG_terminalZeroB6SlopeSource68 T = 0) :
      rhoOne_boundaryG_terminalPlusOneB7BaseSource68 T = 0 :=
    T.rhoOne_boundaryG_terminal_plus_one_B7_base_zero68 R.2 hslope
  refine ⟨R, haffine, hbase, ?_⟩
  dsimp only [rhoOne_boundaryG_terminalPlusOneB7AffineCellReduction68]
  constructor
  · intro hslope hcoeff hconst
    exact ⟨hcoeff, hconst, hbase hslope⟩
  · intro hslope hcoeff hconst hdelta
    exact ⟨hcoeff, hconst, hdelta, hbase hslope⟩

end AlignedSquareBoundaryGSignedRayLinearDZeroTerminalPlusOneB7Isolation68

end Max11DegreeRoutes
