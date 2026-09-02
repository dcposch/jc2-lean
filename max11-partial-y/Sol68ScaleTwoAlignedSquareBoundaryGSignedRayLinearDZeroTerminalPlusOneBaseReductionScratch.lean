import Sol68ScaleTwoAlignedSquareBoundaryGSignedRayLinearDZeroTerminalPlusOneB7IsolationScratch

/-! # Source-local reduction of the terminal-plus-one base

After the verified `B[7]` slope vanishes, the next row is affine in `B[8]`.
This file proves that statement from the literal sixteen-product row, rather
than introducing another coefficient identity.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareBoundaryGSignedRayLinearDZeroTerminalPlusOneBaseReduction68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

omit [IsAlgClosed k] in
def rhoOne_boundaryG_replaceB8_68 (B : HahnSeries ℚ k) (b8 : k) :
    HahnSeries ℚ k :=
  B - HahnSeries.single 8 (B.coeff 8) + HahnSeries.single 8 b8

omit [IsAlgClosed k] in
theorem rhoOne_boundaryG_replaceB8_self68 (B : HahnSeries ℚ k) :
    rhoOne_boundaryG_replaceB8_68 B (B.coeff 8) = B := by
  dsimp only [rhoOne_boundaryG_replaceB8_68]
  abel

omit [IsAlgClosed k] in
def rhoOne_boundaryG_terminalPlusOneB8Slope68
    (A G dA : HahnSeries ℚ k) : k :=
  (-(4 / 27 : k)) * (A * G * dA).coeff (-7)

omit [IsAlgClosed k] in
def rhoOne_boundaryG_terminalPlusOneB8Base68
    (gamma epsilon : k)
    (A B C F G dA dB dC dF dG : HahnSeries ℚ k) : k :=
  rhoOne_boundaryG_terminalPlusOneProductRow68 gamma epsilon
    A (rhoOne_boundaryG_replaceB8_68 B 0) C F G dA dB dC dF dG

omit [IsAlgClosed k] in
theorem rhoOne_boundaryG_terminalPlusOne_B8_affine68
    (gamma epsilon b8 : k)
    (A B C F G dA dB dC dF dG : HahnSeries ℚ k)
    (hA : (↑(-2 : ℚ) : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(2 : ℚ) : WithTop ℚ) ≤ B.orderTop)
    (hC : (0 : WithTop ℚ) ≤ C.orderTop)
    (hF : (0 : WithTop ℚ) ≤ F.orderTop)
    (hdA : (↑(-3 : ℚ) : WithTop ℚ) ≤ dA.orderTop)
    (hdB : (0 : WithTop ℚ) ≤ dB.orderTop)
    (hdF : (0 : WithTop ℚ) ≤ dF.orderTop)
    (hdG : (↑(-3 : ℚ) : WithTop ℚ) ≤ dG.orderTop) :
    rhoOne_boundaryG_terminalPlusOneProductRow68 gamma epsilon
        A (rhoOne_boundaryG_replaceB8_68 B b8) C F G
        dA dB dC dF dG =
      rhoOne_boundaryG_terminalPlusOneB8Base68 gamma epsilon
          A B C F G dA dB dC dF dG +
        rhoOne_boundaryG_terminalPlusOneB8Slope68 A G dA * b8 := by
  let B0 := rhoOne_boundaryG_replaceB8_68 B 0
  let s : HahnSeries ℚ k := HahnSeries.single 8 b8
  have hform : rhoOne_boundaryG_replaceB8_68 B b8 = B0 + s := by
    dsimp only [B0, s, rhoOne_boundaryG_replaceB8_68]
    simp
  have hs8 : (↑(2 : ℚ) : WithTop ℚ) ≤
      (HahnSeries.single (8 : ℚ) (B.coeff 8) : HahnSeries ℚ k).orderTop := by
    by_cases hb : B.coeff 8 = 0
    · simp [hb]
    · rw [HahnSeries.orderTop_single hb]
      exact WithTop.coe_le_coe.mpr (by norm_num)
  have hB0 : (↑(2 : ℚ) : WithTop ℚ) ≤ B0.orderTop := by
    dsimp only [B0, rhoOne_boundaryG_replaceB8_68]
    rw [show (HahnSeries.single (8 : ℚ) (0 : k) : HahnSeries ℚ k) = 0 by
      simp, add_zero]
    exact le_trans (min_le_min hB hs8) HahnSeries.min_orderTop_le_orderTop_sub
  have lower2 (X Y : HahnSeries ℚ k) (m n : ℚ)
      (hX : (↑m : WithTop ℚ) ≤ X.orderTop)
      (hY : (↑n : WithTop ℚ) ≤ Y.orderTop) :
      (↑(m + n) : WithTop ℚ) ≤ (X * Y).orderTop :=
    le_trans (by simpa using add_le_add hX hY) HahnSeries.orderTop_add_le_mul
  have lower3 (X Y Z : HahnSeries ℚ k) (m n r : ℚ)
      (hX : (↑m : WithTop ℚ) ≤ X.orderTop)
      (hY : (↑n : WithTop ℚ) ≤ Y.orderTop)
      (hZ : (↑r : WithTop ℚ) ≤ Z.orderTop) :
      (↑(m + n + r) : WithTop ℚ) ≤ (X * Y * Z).orderTop :=
    lower2 (X * Y) Z (m + n) r (lower2 X Y m n hX hY) hZ
  have coeff_zero (X : HahnSeries ℚ k) (m n : ℚ)
      (hX : (↑m : WithTop ℚ) ≤ X.orderTop) (hn : n < m) :
      X.coeff n = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr hn) hX)
  have single_zero (X : HahnSeries ℚ k) (m : ℚ)
      (hX : (↑m : WithTop ℚ) ≤ X.orderTop) (hn : (-7 : ℚ) < m) :
      (s * X).coeff 1 = 0 := by
    dsimp only [s]
    rw [HahnSeries.coeff_single_mul]
    norm_num
    simp [coeff_zero X m (-7) hX hn]
  have hsdG : (s * dG).coeff 1 = 0 :=
    single_zero dG (-3) hdG (by norm_num)
  have hsFdF : (s * F * dF).coeff 1 = 0 := by
    rw [show s * F * dF = s * (F * dF) by ring]
    apply single_zero (F * dF) 0 (by
      convert lower2 F dF 0 0 hF hdF using 1 <;> norm_num)
    norm_num
  have hsCdG : (s * C * dG).coeff 1 = 0 := by
    rw [show s * C * dG = s * (C * dG) by ring]
    apply single_zero (C * dG) (-3) (by
      convert lower2 C dG 0 (-3) hC hdG using 1 <;> norm_num)
    norm_num
  have hsCdA : (s * C * dA).coeff 1 = 0 := by
    rw [show s * C * dA = s * (C * dA) by ring]
    apply single_zero (C * dA) (-3) (by
      convert lower2 C dA 0 (-3) hC hdA using 1 <;> norm_num)
    norm_num
  have hsCCdA : (s * C * C * dA).coeff 1 = 0 := by
    rw [show s * C * C * dA = s * (C * C * dA) by ring]
    apply single_zero (C * C * dA) (-3) (by
      convert lower3 C C dA 0 0 (-3) hC hC hdA using 1 <;> norm_num)
    norm_num
  have hAsdA : (A * s * dA).coeff 1 = 0 := by
    rw [show A * s * dA = s * (A * dA) by ring]
    apply single_zero (A * dA) (-5) (by
      convert lower2 A dA (-2) (-3) hA hdA using 1 <;> norm_num)
    norm_num
  have hAsGdA : (A * s * G * dA).coeff 1 =
      b8 * (A * G * dA).coeff (-7) := by
    rw [show A * s * G * dA = s * (A * G * dA) by ring]
    dsimp only [s]
    rw [HahnSeries.coeff_single_mul]
    norm_num
  have hAsFdB : (A * s * F * dB).coeff 1 = 0 := by
    rw [show A * s * F * dB = s * (A * F * dB) by ring]
    apply single_zero (A * F * dB) (-2) (by
      convert lower3 A F dB (-2) 0 0 hA hF hdB using 1 <;> norm_num)
    norm_num
  have hsABdF : (s * (A * B0 * dF)).coeff 1 = 0 :=
    single_zero (A * B0 * dF) 0 (by
      convert lower3 A B0 dF (-2) 2 0 hA hB0 hdF using 1 <;> norm_num)
      (by norm_num)
  have hs2AdF : (s ^ 2 * (A * dF)).coeff 1 = 0 := by
    dsimp only [s]
    rw [HahnSeries.single_pow, HahnSeries.coeff_single_mul]
    norm_num
    have hz := coeff_zero (A * dF) (-2) (-15)
      (by convert lower2 A dF (-2) 0 hA hdF using 1 <;> norm_num)
      (by norm_num)
    simp [hz]
  have hAB0sdF : (A * B0 * s * dF).coeff 1 = 0 := by
    rw [show A * B0 * s * dF = s * (A * B0 * dF) by ring, hsABdF]
  have hAsB0dF : (A * s * B0 * dF).coeff 1 = 0 := by
    rw [show A * s * B0 * dF = s * (A * B0 * dF) by ring, hsABdF]
  have hAssdF : (A * s * s * dF).coeff 1 = 0 := by
    rw [show A * s * s * dF = s ^ 2 * (A * dF) by ring, hs2AdF]
  rw [hform]
  dsimp only [rhoOne_boundaryG_terminalPlusOneProductRow68]
  simp only [mul_add, add_mul, HahnSeries.coeff_add]
  rw [hsdG, hsFdF, hsCdG, hsCdA, hsCCdA, hAsdA, hAsGdA,
    hAsFdB, hAB0sdF, hAsB0dF, hAssdF]
  dsimp only [rhoOne_boundaryG_terminalPlusOneB8Base68,
    rhoOne_boundaryG_terminalPlusOneB8Slope68,
    rhoOne_boundaryG_terminalPlusOneProductRow68]
  ring

end AlignedSquareBoundaryGSignedRayLinearDZeroTerminalPlusOneBaseReduction68

end Max11DegreeRoutes
