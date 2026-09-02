import Sol68ScaleTwoAlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6ConvolutionScratch

/-! # Exact `B[6]` isolation in the terminal-zero product row -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6Isolation68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

omit [IsAlgClosed k] in
def rhoOne_boundaryG_terminalZeroProductLaurentRow68
    (gamma epsilon : k)
    (A B C F G dA dB dC dF dG : LaurentSeries k) : k :=
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
def rhoOne_boundaryG_terminalZeroB6Slope68
    (A G dA : LaurentSeries k) : k :=
  (-(4 / 27 : k)) * laurentFourLowerFiveYSlope68 A G dA (-2) (-2) (-3)

omit [IsAlgClosed k] in
def rhoOne_boundaryG_terminalZeroB6Base68
    (gamma epsilon : k)
    (A B C F G dA dB dC dF dG : LaurentSeries k) : k :=
  (-(2 / 3 : k) * gamma) * (F * dC).coeff 0 +
  (-(1 / 3 : k) * epsilon) * (F * dA).coeff 0 +
  (-(4 / 9 : k)) * (F * G * dA).coeff 0 +
  (-(4 / 9 : k)) * (F * F * dB).coeff 0 +
  (-(4 / 9 : k)) * (C * F * dC).coeff 0 +
  ((2 / 3 : k) * gamma) *
    (B.coeff 2 * dG.coeff (-2) + B.coeff 3 * dG.coeff (-3)) +
  (4 / 9 : k) *
    (B.coeff 2 * C.coeff 0 * dG.coeff (-2) +
     B.coeff 2 * C.coeff 1 * dG.coeff (-3) +
     B.coeff 3 * C.coeff 0 * dG.coeff (-3)) +
  ((2 / 9 : k) * gamma) *
    (B.coeff 2 * C.coeff 0 * dA.coeff (-2) +
     B.coeff 2 * C.coeff 1 * dA.coeff (-3) +
     B.coeff 3 * C.coeff 0 * dA.coeff (-3)) +
  (4 / 27 : k) *
    (B.coeff 3 * C.coeff 0 * C.coeff 0 * dA.coeff (-3) +
     B.coeff 2 * C.coeff 1 * C.coeff 0 * dA.coeff (-3) +
     B.coeff 2 * C.coeff 0 * C.coeff 1 * dA.coeff (-3) +
     B.coeff 2 * C.coeff 0 * C.coeff 0 * dA.coeff (-2)) +
  (-(2 / 9 : k) * gamma) * (A * F * dA).coeff 0 +
  (-(4 / 27 : k)) * (A * F * dA * C).coeff 0 +
  (-(1 / 9 : k) * epsilon) *
    (A.coeff (-2) * B.coeff 2 * dA.coeff 0 +
     A.coeff (-2) * B.coeff 3 * dA.coeff (-1) +
     A.coeff (-2) * B.coeff 4 * dA.coeff (-2) +
     A.coeff (-2) * B.coeff 5 * dA.coeff (-3) +
     A.coeff (-1) * B.coeff 2 * dA.coeff (-1) +
     A.coeff (-1) * B.coeff 3 * dA.coeff (-2) +
     A.coeff (-1) * B.coeff 4 * dA.coeff (-3) +
     A.coeff 0 * B.coeff 2 * dA.coeff (-2) +
     A.coeff 0 * B.coeff 3 * dA.coeff (-3) +
     A.coeff 1 * B.coeff 2 * dA.coeff (-3)) +
  (-(4 / 27 : k)) *
    laurentFourLowerFiveWithoutYFour68 A B G dA (-2) 2 (-2) (-3) +
  (-(4 / 27 : k)) *
    (A.coeff (-2) * B.coeff 2 * F.coeff 0 * dB.coeff 0)

omit [IsAlgClosed k] in
def rhoOne_boundaryG_terminalZeroAtB6_68
    (gamma epsilon b6 : k)
    (A B C F G dA dB dC dF dG : LaurentSeries k) : k :=
  rhoOne_boundaryG_terminalZeroB6Base68 gamma epsilon
    A B C F G dA dB dC dF dG +
  rhoOne_boundaryG_terminalZeroB6Slope68 A G dA * b6

omit [IsAlgClosed k] in
theorem rhoOne_boundaryG_terminal_zero_B6_convolution68
    (gamma epsilon : k)
    (A B C F G dA dB dC dF dG : LaurentSeries k)
    (hA : (↑(-2 : ℤ) : WithTop ℤ) ≤ A.orderTop)
    (hB : (↑(2 : ℤ) : WithTop ℤ) ≤ B.orderTop)
    (hC : (0 : WithTop ℤ) ≤ C.orderTop)
    (hF : (0 : WithTop ℤ) ≤ F.orderTop)
    (hG : (↑(-2 : ℤ) : WithTop ℤ) ≤ G.orderTop)
    (hdA : (↑(-3 : ℤ) : WithTop ℤ) ≤ dA.orderTop)
    (hdB : (0 : WithTop ℤ) ≤ dB.orderTop)
    (hdC : (0 : WithTop ℤ) ≤ dC.orderTop)
    (hdF : (0 : WithTop ℤ) ≤ dF.orderTop)
    (hdG : (↑(-3 : ℤ) : WithTop ℤ) ≤ dG.orderTop) :
    rhoOne_boundaryG_terminalZeroProductLaurentRow68 gamma epsilon
      A B C F G dA dB dC dF dG =
    rhoOne_boundaryG_terminalZeroAtB6_68 gamma epsilon (B.coeff 6)
      A B C F G dA dB dC dF dG := by
  have lower2 (X Y : LaurentSeries k) (m n : ℤ)
      (hX : (↑m : WithTop ℤ) ≤ X.orderTop)
      (hY : (↑n : WithTop ℤ) ≤ Y.orderTop) :
      (↑(m + n) : WithTop ℤ) ≤ (X * Y).orderTop :=
    le_trans (by simpa using add_le_add hX hY) HahnSeries.orderTop_add_le_mul
  have lower3 (X Y Z : LaurentSeries k) (m n r : ℤ)
      (hX : (↑m : WithTop ℤ) ≤ X.orderTop)
      (hY : (↑n : WithTop ℤ) ≤ Y.orderTop)
      (hZ : (↑r : WithTop ℤ) ≤ Z.orderTop) :
      (↑(m + n + r) : WithTop ℤ) ≤ (X * Y * Z).orderTop :=
    lower2 (X * Y) Z (m + n) r (lower2 X Y m n hX hY) hZ
  have lower4 (X Y Z W : LaurentSeries k) (m n r s : ℤ)
      (hX : (↑m : WithTop ℤ) ≤ X.orderTop)
      (hY : (↑n : WithTop ℤ) ≤ Y.orderTop)
      (hZ : (↑r : WithTop ℤ) ≤ Z.orderTop)
      (hW : (↑s : WithTop ℤ) ≤ W.orderTop) :
      (↑(m + n + r + s) : WithTop ℤ) ≤ (X * Y * Z * W).orderTop :=
    lower2 (X * Y * Z) W (m + n + r) s
      (lower3 X Y Z m n r hX hY hZ) hW
  have zero_of_lower (X : LaurentSeries k) (n : ℤ)
      (hX : (↑n : WithTop ℤ) ≤ X.orderTop) (hn : 0 < n) :
      X.coeff 0 = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr hn) hX)
  have hBDG := laurent_coeff_mul_lower_succ68 B dG 2 (-3) hB hdG
  have hBFD := zero_of_lower (B * F * dF) 2
    (lower3 B F dF 2 0 0 hB hF hdF) (by omega)
  have hBCDG := laurent_coeff_mul_three_lower_succ68 B C dG 2 0 (-3)
    hB hC hdG
  have hBCDA := laurent_coeff_mul_three_lower_succ68 B C dA 2 0 (-3)
    hB hC hdA
  have hBCCDA := laurent_coeff_mul_four_lower_succ_terminal68 B C C dA
    2 0 0 (-3) hB hC hC hdA
  have hABDA := laurent_coeff_mul_three_lower_three68 A B dA (-2) 2 (-3)
    hA hB hdA
  have hABGDA := laurent_coeff_mul_four_lower_five_boundary68 A B G dA
    (-2) 2 (-2) (-3) hA hB hG hdA
  have hABF : (A * B * F).coeff 0 =
      A.coeff (-2) * B.coeff 2 * F.coeff 0 := by
    have ht := laurent_coeff_mul_three_lower_terminal68 A B F (-2) 2 0
      hA hB hF
    norm_num at ht
    exact ht
  have hABFord : (0 : WithTop ℤ) ≤ (A * B * F).orderTop :=
    lower3 A B F (-2) 2 0 hA hB hF
  have hABFDB := laurent_coeff_mul_lower68 (A * B * F) dB 0 0 hABFord hdB
  rw [hABF] at hABFDB
  have hABBD := zero_of_lower (A * B * B * dF) 2
    (lower4 A B B dF (-2) 2 2 0 hA hB hB hdF) (by omega)
  norm_num at hBDG hBCDG hBCDA hBCCDA hABDA hABGDA hABFDB
  rw [laurentFourLowerFive_isolate_YFour68] at hABGDA
  dsimp only [rhoOne_boundaryG_terminalZeroProductLaurentRow68,
    rhoOne_boundaryG_terminalZeroAtB6_68,
    rhoOne_boundaryG_terminalZeroB6Base68,
    rhoOne_boundaryG_terminalZeroB6Slope68]
  rw [hBDG, hBFD, hBCDG, hBCDA, hBCCDA, hABDA, hABGDA,
    hABFDB, hABBD]
  ring

end AlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6Isolation68

end Max11DegreeRoutes
