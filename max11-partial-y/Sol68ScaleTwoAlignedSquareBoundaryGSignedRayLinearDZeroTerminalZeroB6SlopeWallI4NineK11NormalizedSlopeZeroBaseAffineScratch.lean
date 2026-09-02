import Sol68ScaleTwoAlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZeroObstructionScratch

/-! # The exact affine `dA[-2]` packet on the normalized zero-slope cell -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZeroBaseAffine68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

omit [IsAlgClosed k] in
def rhoOne_boundaryG_terminalZeroB6DeltaCoeff68
    (gamma epsilon : k) (A B C F G : LaurentSeries k) : k :=
  rhoOne_boundaryG_terminalZeroB6Base68 gamma epsilon A B C F G
    (HahnSeries.single (-2 : ℤ) (1 : k)) 0 0 0 0

omit [IsAlgClosed k] in
def rhoOne_boundaryG_terminalZeroB6DeltaConstant68
    (gamma epsilon : k)
    (A B C F G dA dB dC dF dG : LaurentSeries k) : k :=
  let DeltaA := dA.coeff (-2) - 2 * A.coeff (-1)
  rhoOne_boundaryG_terminalZeroB6Base68 gamma epsilon A B C F G
    (dA - HahnSeries.single (-2 : ℤ) DeltaA) dB dC dF dG

omit [IsAlgClosed k] in
def rhoOne_boundaryG_terminalZeroB6DeltaCoeffExpanded68
    (gamma epsilon : k) (A B C F G : LaurentSeries k) : k :=
  (-(1 / 3 : k) * epsilon) * F.coeff 2 +
  (-(4 / 9 : k)) * (F * G).coeff 2 +
  ((2 / 9 : k) * gamma) * (B.coeff 2 * C.coeff 0) +
  (4 / 27 : k) * (B.coeff 2 * C.coeff 0 * C.coeff 0) +
  (-(2 / 9 : k) * gamma) * (A * F).coeff 2 +
  (-(4 / 27 : k)) * (A * F * C).coeff 2 +
  (-(1 / 9 : k) * epsilon) *
    (A.coeff (-2) * B.coeff 4 + A.coeff (-1) * B.coeff 3 +
      A.coeff 0 * B.coeff 2) +
  (-(4 / 27 : k)) *
    (A.coeff (-2) * B.coeff 2 * G.coeff 2 +
     A.coeff (-2) * B.coeff 3 * G.coeff 1 +
     A.coeff (-2) * B.coeff 4 * G.coeff 0 +
     A.coeff (-2) * B.coeff 5 * G.coeff (-1) +
     A.coeff (-1) * B.coeff 2 * G.coeff 1 +
     A.coeff (-1) * B.coeff 3 * G.coeff 0 +
     A.coeff (-1) * B.coeff 4 * G.coeff (-1) +
     A.coeff (-1) * B.coeff 5 * G.coeff (-2) +
     A.coeff 0 * B.coeff 2 * G.coeff 0 +
     A.coeff 0 * B.coeff 3 * G.coeff (-1) +
     A.coeff 0 * B.coeff 4 * G.coeff (-2) +
     A.coeff 1 * B.coeff 2 * G.coeff (-1) +
     A.coeff 1 * B.coeff 3 * G.coeff (-2) +
     A.coeff 2 * B.coeff 2 * G.coeff (-2))

omit [IsAlgClosed k] in
theorem rhoOne_boundaryG_terminalZeroB6DeltaCoeff_expanded68
    (gamma epsilon : k) (A B C F G : LaurentSeries k) :
    rhoOne_boundaryG_terminalZeroB6DeltaCoeff68 gamma epsilon A B C F G =
      rhoOne_boundaryG_terminalZeroB6DeltaCoeffExpanded68 gamma epsilon A B C F G := by
  have hAFC :
      (A * F * HahnSeries.single (-2 : ℤ) (1 : k) * C).coeff 0 =
        (A * F * C).coeff 2 := by
    rw [show A * F * HahnSeries.single (-2 : ℤ) (1 : k) * C =
        (A * F * C) * HahnSeries.single (-2 : ℤ) (1 : k) by ring,
      HahnSeries.coeff_mul_single]
    norm_num
  dsimp only [rhoOne_boundaryG_terminalZeroB6DeltaCoeff68,
    rhoOne_boundaryG_terminalZeroB6DeltaCoeffExpanded68,
    rhoOne_boundaryG_terminalZeroB6Base68,
    laurentFourLowerFiveWithoutYFour68, laurentFourLowerFiveJet68]
  simp only [mul_zero, zero_mul, HahnSeries.coeff_zero, add_zero,
    HahnSeries.coeff_mul_single, HahnSeries.coeff_single_same,
    hAFC]
  norm_num
  ring

omit [IsAlgClosed k] in
theorem rhoOne_boundaryG_terminalZeroB6Base_add_dA68
    (gamma epsilon : k)
    (A B C F G dA e dB dC dF dG : LaurentSeries k) :
    rhoOne_boundaryG_terminalZeroB6Base68 gamma epsilon A B C F G
        (dA + e) dB dC dF dG =
      rhoOne_boundaryG_terminalZeroB6Base68 gamma epsilon A B C F G
          dA dB dC dF dG +
        rhoOne_boundaryG_terminalZeroB6Base68 gamma epsilon A B C F G
          e 0 0 0 0 := by
  dsimp only [rhoOne_boundaryG_terminalZeroB6Base68,
    laurentFourLowerFiveWithoutYFour68, laurentFourLowerFiveJet68]
  simp only [mul_add, add_mul, HahnSeries.coeff_add, mul_zero, zero_mul,
    HahnSeries.coeff_zero]
  ring

omit [IsAlgClosed k] in
theorem rhoOne_boundaryG_terminalZeroB6Base_single68
    (gamma epsilon t : k) (A B C F G : LaurentSeries k) :
    rhoOne_boundaryG_terminalZeroB6Base68 gamma epsilon A B C F G
        (HahnSeries.single (-2 : ℤ) t) 0 0 0 0 =
      rhoOne_boundaryG_terminalZeroB6DeltaCoeff68 gamma epsilon A B C F G * t := by
  have hAFC :
      (A * F * HahnSeries.single (-2 : ℤ) t * C).coeff 0 =
        (A * F * C).coeff 2 * t := by
    rw [show A * F * HahnSeries.single (-2 : ℤ) t * C =
        (A * F * C) * HahnSeries.single (-2 : ℤ) t by ring,
      HahnSeries.coeff_mul_single]
    norm_num
  rw [rhoOne_boundaryG_terminalZeroB6DeltaCoeff_expanded68]
  dsimp only [rhoOne_boundaryG_terminalZeroB6DeltaCoeffExpanded68,
    rhoOne_boundaryG_terminalZeroB6Base68,
    laurentFourLowerFiveWithoutYFour68, laurentFourLowerFiveJet68]
  simp only [mul_zero, zero_mul, HahnSeries.coeff_zero, add_zero,
    HahnSeries.coeff_mul_single, HahnSeries.coeff_single_same,
    hAFC]
  norm_num
  ring

omit [IsAlgClosed k] in
theorem rhoOne_boundaryG_terminalZeroB6Base_affine_DeltaA68
    (gamma epsilon : k)
    (A B C F G dA dB dC dF dG : LaurentSeries k) :
    rhoOne_boundaryG_terminalZeroB6Base68 gamma epsilon A B C F G
        dA dB dC dF dG =
      rhoOne_boundaryG_terminalZeroB6DeltaConstant68 gamma epsilon
          A B C F G dA dB dC dF dG +
        rhoOne_boundaryG_terminalZeroB6DeltaCoeff68 gamma epsilon A B C F G *
          (dA.coeff (-2) - 2 * A.coeff (-1)) := by
  let DeltaA := dA.coeff (-2) - 2 * A.coeff (-1)
  let dA0 := dA - HahnSeries.single (-2 : ℤ) DeltaA
  have hdA : dA = dA0 + HahnSeries.single (-2 : ℤ) DeltaA := by
    dsimp only [dA0]
    abel
  calc
    rhoOne_boundaryG_terminalZeroB6Base68 gamma epsilon A B C F G
        dA dB dC dF dG =
      rhoOne_boundaryG_terminalZeroB6Base68 gamma epsilon A B C F G
        (dA0 + HahnSeries.single (-2 : ℤ) DeltaA) dB dC dF dG := by
          rw [← hdA]
    _ = rhoOne_boundaryG_terminalZeroB6Base68 gamma epsilon A B C F G
          dA0 dB dC dF dG +
        rhoOne_boundaryG_terminalZeroB6DeltaCoeff68 gamma epsilon A B C F G *
          DeltaA := by
      rw [rhoOne_boundaryG_terminalZeroB6Base_add_dA68,
        rhoOne_boundaryG_terminalZeroB6Base_single68]
    _ = rhoOne_boundaryG_terminalZeroB6DeltaConstant68 gamma epsilon
          A B C F G dA dB dC dF dG +
        rhoOne_boundaryG_terminalZeroB6DeltaCoeff68 gamma epsilon A B C F G *
          (dA.coeff (-2) - 2 * A.coeff (-1)) := by
      rfl

omit [IsAlgClosed k] in
theorem rhoOne_boundaryG_terminalZeroB6Base_zero_affine_split68
    (gamma epsilon : k)
    (A B C F G dA dB dC dF dG : LaurentSeries k)
    (hBase : rhoOne_boundaryG_terminalZeroB6Base68 gamma epsilon A B C F G
      dA dB dC dF dG = 0) :
    let DeltaA := dA.coeff (-2) - 2 * A.coeff (-1)
    let Coeff := rhoOne_boundaryG_terminalZeroB6DeltaCoeff68 gamma epsilon A B C F G
    let Const := rhoOne_boundaryG_terminalZeroB6DeltaConstant68 gamma epsilon
      A B C F G dA dB dC dF dG
    Const + Coeff * DeltaA = 0 ∧
      ((Coeff = 0 ∧ Const = 0) ∨
       (Coeff ≠ 0 ∧ DeltaA = -Const / Coeff)) := by
  dsimp only
  have haff := rhoOne_boundaryG_terminalZeroB6Base_affine_DeltaA68 gamma epsilon
    A B C F G dA dB dC dF dG
  have hz : rhoOne_boundaryG_terminalZeroB6DeltaConstant68 gamma epsilon
      A B C F G dA dB dC dF dG +
      rhoOne_boundaryG_terminalZeroB6DeltaCoeff68 gamma epsilon A B C F G *
        (dA.coeff (-2) - 2 * A.coeff (-1)) = 0 := by
    rw [← haff]
    exact hBase
  refine ⟨hz, ?_⟩
  by_cases hc : rhoOne_boundaryG_terminalZeroB6DeltaCoeff68 gamma epsilon A B C F G = 0
  · left
    refine ⟨hc, ?_⟩
    rw [hc, zero_mul, add_zero] at hz
    exact hz
  · right
    refine ⟨hc, ?_⟩
    apply (eq_div_iff hc).2
    linear_combination hz

end AlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6SlopeWallI4NineK11NormalizedSlopeZeroBaseAffine68

end Max11DegreeRoutes
