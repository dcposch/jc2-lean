import Sol68ScaleTwoAlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroExpansionScratch

/-! # Finite terminal-zero convolution and the explicit `B[6]` face -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6Convolution68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

omit [IsAlgClosed k] in
def laurentFourLowerFiveJet68
    (X Y Z W : LaurentSeries k) (m n r s : ℤ) : k :=
  X.coeff (m + 0) * Y.coeff (n + 0) * Z.coeff (r + 0) * W.coeff (s + 5) +
  X.coeff (m + 0) * Y.coeff (n + 0) * Z.coeff (r + 1) * W.coeff (s + 4) +
  X.coeff (m + 0) * Y.coeff (n + 0) * Z.coeff (r + 2) * W.coeff (s + 3) +
  X.coeff (m + 0) * Y.coeff (n + 0) * Z.coeff (r + 3) * W.coeff (s + 2) +
  X.coeff (m + 0) * Y.coeff (n + 0) * Z.coeff (r + 4) * W.coeff (s + 1) +
  X.coeff (m + 0) * Y.coeff (n + 0) * Z.coeff (r + 5) * W.coeff (s + 0) +
  X.coeff (m + 0) * Y.coeff (n + 1) * Z.coeff (r + 0) * W.coeff (s + 4) +
  X.coeff (m + 0) * Y.coeff (n + 1) * Z.coeff (r + 1) * W.coeff (s + 3) +
  X.coeff (m + 0) * Y.coeff (n + 1) * Z.coeff (r + 2) * W.coeff (s + 2) +
  X.coeff (m + 0) * Y.coeff (n + 1) * Z.coeff (r + 3) * W.coeff (s + 1) +
  X.coeff (m + 0) * Y.coeff (n + 1) * Z.coeff (r + 4) * W.coeff (s + 0) +
  X.coeff (m + 0) * Y.coeff (n + 2) * Z.coeff (r + 0) * W.coeff (s + 3) +
  X.coeff (m + 0) * Y.coeff (n + 2) * Z.coeff (r + 1) * W.coeff (s + 2) +
  X.coeff (m + 0) * Y.coeff (n + 2) * Z.coeff (r + 2) * W.coeff (s + 1) +
  X.coeff (m + 0) * Y.coeff (n + 2) * Z.coeff (r + 3) * W.coeff (s + 0) +
  X.coeff (m + 0) * Y.coeff (n + 3) * Z.coeff (r + 0) * W.coeff (s + 2) +
  X.coeff (m + 0) * Y.coeff (n + 3) * Z.coeff (r + 1) * W.coeff (s + 1) +
  X.coeff (m + 0) * Y.coeff (n + 3) * Z.coeff (r + 2) * W.coeff (s + 0) +
  X.coeff (m + 0) * Y.coeff (n + 4) * Z.coeff (r + 0) * W.coeff (s + 1) +
  X.coeff (m + 0) * Y.coeff (n + 4) * Z.coeff (r + 1) * W.coeff (s + 0) +
  X.coeff (m + 0) * Y.coeff (n + 5) * Z.coeff (r + 0) * W.coeff (s + 0) +
  X.coeff (m + 1) * Y.coeff (n + 0) * Z.coeff (r + 0) * W.coeff (s + 4) +
  X.coeff (m + 1) * Y.coeff (n + 0) * Z.coeff (r + 1) * W.coeff (s + 3) +
  X.coeff (m + 1) * Y.coeff (n + 0) * Z.coeff (r + 2) * W.coeff (s + 2) +
  X.coeff (m + 1) * Y.coeff (n + 0) * Z.coeff (r + 3) * W.coeff (s + 1) +
  X.coeff (m + 1) * Y.coeff (n + 0) * Z.coeff (r + 4) * W.coeff (s + 0) +
  X.coeff (m + 1) * Y.coeff (n + 1) * Z.coeff (r + 0) * W.coeff (s + 3) +
  X.coeff (m + 1) * Y.coeff (n + 1) * Z.coeff (r + 1) * W.coeff (s + 2) +
  X.coeff (m + 1) * Y.coeff (n + 1) * Z.coeff (r + 2) * W.coeff (s + 1) +
  X.coeff (m + 1) * Y.coeff (n + 1) * Z.coeff (r + 3) * W.coeff (s + 0) +
  X.coeff (m + 1) * Y.coeff (n + 2) * Z.coeff (r + 0) * W.coeff (s + 2) +
  X.coeff (m + 1) * Y.coeff (n + 2) * Z.coeff (r + 1) * W.coeff (s + 1) +
  X.coeff (m + 1) * Y.coeff (n + 2) * Z.coeff (r + 2) * W.coeff (s + 0) +
  X.coeff (m + 1) * Y.coeff (n + 3) * Z.coeff (r + 0) * W.coeff (s + 1) +
  X.coeff (m + 1) * Y.coeff (n + 3) * Z.coeff (r + 1) * W.coeff (s + 0) +
  X.coeff (m + 1) * Y.coeff (n + 4) * Z.coeff (r + 0) * W.coeff (s + 0) +
  X.coeff (m + 2) * Y.coeff (n + 0) * Z.coeff (r + 0) * W.coeff (s + 3) +
  X.coeff (m + 2) * Y.coeff (n + 0) * Z.coeff (r + 1) * W.coeff (s + 2) +
  X.coeff (m + 2) * Y.coeff (n + 0) * Z.coeff (r + 2) * W.coeff (s + 1) +
  X.coeff (m + 2) * Y.coeff (n + 0) * Z.coeff (r + 3) * W.coeff (s + 0) +
  X.coeff (m + 2) * Y.coeff (n + 1) * Z.coeff (r + 0) * W.coeff (s + 2) +
  X.coeff (m + 2) * Y.coeff (n + 1) * Z.coeff (r + 1) * W.coeff (s + 1) +
  X.coeff (m + 2) * Y.coeff (n + 1) * Z.coeff (r + 2) * W.coeff (s + 0) +
  X.coeff (m + 2) * Y.coeff (n + 2) * Z.coeff (r + 0) * W.coeff (s + 1) +
  X.coeff (m + 2) * Y.coeff (n + 2) * Z.coeff (r + 1) * W.coeff (s + 0) +
  X.coeff (m + 2) * Y.coeff (n + 3) * Z.coeff (r + 0) * W.coeff (s + 0) +
  X.coeff (m + 3) * Y.coeff (n + 0) * Z.coeff (r + 0) * W.coeff (s + 2) +
  X.coeff (m + 3) * Y.coeff (n + 0) * Z.coeff (r + 1) * W.coeff (s + 1) +
  X.coeff (m + 3) * Y.coeff (n + 0) * Z.coeff (r + 2) * W.coeff (s + 0) +
  X.coeff (m + 3) * Y.coeff (n + 1) * Z.coeff (r + 0) * W.coeff (s + 1) +
  X.coeff (m + 3) * Y.coeff (n + 1) * Z.coeff (r + 1) * W.coeff (s + 0) +
  X.coeff (m + 3) * Y.coeff (n + 2) * Z.coeff (r + 0) * W.coeff (s + 0) +
  X.coeff (m + 4) * Y.coeff (n + 0) * Z.coeff (r + 0) * W.coeff (s + 1) +
  X.coeff (m + 4) * Y.coeff (n + 0) * Z.coeff (r + 1) * W.coeff (s + 0) +
  X.coeff (m + 4) * Y.coeff (n + 1) * Z.coeff (r + 0) * W.coeff (s + 0) +
  X.coeff (m + 5) * Y.coeff (n + 0) * Z.coeff (r + 0) * W.coeff (s + 0)

omit [IsAlgClosed k] in
theorem laurent_coeff_mul_four_lower_five_boundary68
    (X Y Z W : LaurentSeries k) (m n r s : ℤ)
    (hX : (↑m : WithTop ℤ) ≤ X.orderTop)
    (hY : (↑n : WithTop ℤ) ≤ Y.orderTop)
    (hZ : (↑r : WithTop ℤ) ≤ Z.orderTop)
    (hW : (↑s : WithTop ℤ) ≤ W.orderTop) :
    (X * Y * Z * W).coeff (m + n + r + s + 5) =
      laurentFourLowerFiveJet68 X Y Z W m n r s := by
  have hXY : (↑(m + n) : WithTop ℤ) ≤ (X * Y).orderTop :=
    le_trans (by simpa using add_le_add hX hY) HahnSeries.orderTop_add_le_mul
  have hXYZ : (↑(m + n + r) : WithTop ℤ) ≤ (X * Y * Z).orderTop :=
    le_trans (by simpa using add_le_add hXY hZ) HahnSeries.orderTop_add_le_mul
  have h := laurent_coeff_mul_lower_five68 (X * Y * Z) W
    (m + n + r) s hXYZ hW
  have h0 := laurent_coeff_mul_three_lower_terminal68 X Y Z m n r hX hY hZ
  have h1 := laurent_coeff_mul_three_lower_succ68 X Y Z m n r hX hY hZ
  have h2 := laurent_coeff_mul_three_lower_two68 X Y Z m n r hX hY hZ
  have h3 := laurent_coeff_mul_three_lower_three68 X Y Z m n r hX hY hZ
  have h4 := laurent_coeff_mul_three_lower_four_boundary68 X Y Z m n r hX hY hZ
  have h5 := laurent_coeff_mul_three_lower_five_boundary68 X Y Z m n r hX hY hZ
  rw [h0, h1, h2, h3, h4, h5] at h
  dsimp only [laurentFourLowerFiveJet68]
  convert h using 1 <;> ring

omit [IsAlgClosed k] in
def laurentFourLowerFiveWithoutYFour68
    (X Y Z W : LaurentSeries k) (m n r s : ℤ) : k :=
  laurentFourLowerFiveJet68 X Y Z W m n r s -
    Y.coeff (n + 4) *
      (X.coeff (m + 0) * Z.coeff (r + 0) * W.coeff (s + 1) +
       X.coeff (m + 0) * Z.coeff (r + 1) * W.coeff (s + 0) +
       X.coeff (m + 1) * Z.coeff (r + 0) * W.coeff (s + 0))

omit [IsAlgClosed k] in
def laurentFourLowerFiveYSlope68
    (X Z W : LaurentSeries k) (m r s : ℤ) : k :=
  X.coeff (m + 0) * Z.coeff (r + 0) * W.coeff (s + 1) +
  X.coeff (m + 0) * Z.coeff (r + 1) * W.coeff (s + 0) +
  X.coeff (m + 1) * Z.coeff (r + 0) * W.coeff (s + 0)

omit [IsAlgClosed k] in
theorem laurentFourLowerFive_isolate_YFour68
    (X Y Z W : LaurentSeries k) (m n r s : ℤ) :
    laurentFourLowerFiveJet68 X Y Z W m n r s =
      laurentFourLowerFiveWithoutYFour68 X Y Z W m n r s +
        laurentFourLowerFiveYSlope68 X Z W m r s * Y.coeff (n + 4) := by
  dsimp only [laurentFourLowerFiveWithoutYFour68,
    laurentFourLowerFiveYSlope68]
  ring

end AlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6Convolution68

end Max11DegreeRoutes
