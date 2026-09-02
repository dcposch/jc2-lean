import Sol68ScaleTwoAlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZeroBaseCoeffI4ElevenB13TransportScratch

/-! # The invertible I3(11) / I4(11) high-jet extension

The old zero/nonzero base-affine cells do not enter these two rows. Both rows
have the same nonzero leading slope (8/3) G[-2], so they uniquely transport
C[13] and B[13] on either old cell.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareBoundaryGSignedRayLinearDZeroI3I4ElevenAffineCells68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

def rhoOne_boundaryG_i3i4elevenHighJetDeterminant68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : k :=
  rhoOne_boundaryG_i3elevenC13Slope68 T *
    rhoOne_boundaryG_i4elevenB13Slope68 T

def rhoOne_boundaryG_i3i4elevenHighJetSolution68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  rhoOne_boundaryG_i3i4elevenHighJetDeterminant68 T ≠ 0 ∧
    C.coeff 13 =
      -rhoOne_boundaryG_i3elevenAtC13_68 T 0 /
        rhoOne_boundaryG_i3elevenC13Slope68 T ∧
    B.coeff 13 =
      -rhoOne_boundaryG_i4elevenAtB13_68 T 0 /
        rhoOne_boundaryG_i4elevenB13Slope68 T

def RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZeroBaseCoeffI3I4ElevenAffineCells68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : Prop :=
  RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZeroBaseCoeffTransport68 T ∧
  rhoOne_boundaryG_i3i4elevenHighJetSolution68 T

theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_signedRay_linear_dZero_i3i4eleven_affine_cells68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (R :
      RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZeroBaseCoeffI4ElevenB13Transport68 T) :
    RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZeroBaseCoeffI3I4ElevenAffineCells68 T := by
  have hBase :
      RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZeroBaseCoeffTransport68 T :=
    R.1.1.1.1.1.1.1.1
  have hC :
      rhoOne_boundaryG_i3elevenC13Transport68 T := R.1.1.2
  have hB :
      rhoOne_boundaryG_i4elevenB13Transport68 T := R.2
  have hdet :
      rhoOne_boundaryG_i3i4elevenHighJetDeterminant68 T ≠ 0 := by
    dsimp only [rhoOne_boundaryG_i3i4elevenHighJetDeterminant68]
    exact mul_ne_zero hC.2.1 hB.2.1
  refine ⟨hBase, ?_⟩
  dsimp only [rhoOne_boundaryG_i3i4elevenHighJetSolution68]
  exact ⟨hdet, hC.2.2, hB.2.2⟩

end AlignedSquareBoundaryGSignedRayLinearDZeroI3I4ElevenAffineCells68

end Max11DegreeRoutes
