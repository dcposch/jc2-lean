import Sol68ScaleTwoAlignedSquareTerminalGBoundaryCapSourceFactorGainsScratch

/-! # Coordinate-row realization of endpoint T₅ -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareTerminalGBoundaryCapEndpointRows68

variable {k : Type*} [Field k] [CharZero k]

local instance alignedSquareTerminalGBoundaryCapEndpointRowsHahnCharZero68 :
    CharZero (LaurentSeries k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℤ))

theorem rhoOneCap_coordinate_defect_t5_of_rows68
    (epsilon : k) (B C F G : LaurentSeries k)
    (hB : (↑(11 : ℤ) : WithTop ℤ) ≤ B.orderTop)
    (hC : (↑(7 : ℤ) : WithTop ℤ) ≤ C.orderTop)
    (hF : (↑(3 : ℤ) : WithTop ℤ) ≤ F.orderTop)
    (hf3 : F.coeff 3 ≠ 0)
    (hR3 : (↑(12 : ℤ) : WithTop ℤ) ≤
      (rhoOneCapReducedI3Series68 epsilon C F G).orderTop)
    (hR4 : (↑(16 : ℤ) : WithTop ℤ) ≤
      (rhoOneCapReducedI4Series68 epsilon B C F G).orderTop)
    (hT0 : 2 * C.coeff 7 ^ 2 - B.coeff 11 * F.coeff 3 = 0)
    (hT1 : 4 * C.coeff 7 * C.coeff 8 - B.coeff 12 * F.coeff 3 -
      B.coeff 11 * F.coeff 4 = 0)
    (hT2 : 2 * C.coeff 8 ^ 2 + 4 * C.coeff 7 * C.coeff 9 -
      B.coeff 13 * F.coeff 3 - B.coeff 12 * F.coeff 4 -
      B.coeff 11 * F.coeff 5 = 0)
    (hT3 : 4 * C.coeff 7 * C.coeff 10 + 4 * C.coeff 8 * C.coeff 9 -
      B.coeff 14 * F.coeff 3 - B.coeff 13 * F.coeff 4 -
      B.coeff 12 * F.coeff 5 - B.coeff 11 * F.coeff 6 = 0)
    (hT4 : 4 * C.coeff 7 * C.coeff 11 + 4 * C.coeff 8 * C.coeff 10 +
      2 * C.coeff 9 ^ 2 - B.coeff 15 * F.coeff 3 -
      B.coeff 14 * F.coeff 4 - B.coeff 13 * F.coeff 5 -
      B.coeff 12 * F.coeff 6 - B.coeff 11 * F.coeff 7 = 0) :
    4 * C.coeff 7 * C.coeff 12 + 4 * C.coeff 8 * C.coeff 11 +
      4 * C.coeff 9 * C.coeff 10 - B.coeff 16 * F.coeff 3 -
      B.coeff 15 * F.coeff 4 - B.coeff 14 * F.coeff 5 -
      B.coeff 13 * F.coeff 6 - B.coeff 12 * F.coeff 7 -
      B.coeff 11 * F.coeff 8 = 0 := by
  let H := rhoOneCapCoordinateDefectSeries68 B C F
  have hCC0 := laurent_coeff_mul_lower68 C C 7 7 hC hC
  have hBF0 := laurent_coeff_mul_lower68 B F 11 3 hB hF
  have hCC1 := laurent_coeff_mul_lower_succ68 C C 7 7 hC hC
  have hBF1 := laurent_coeff_mul_lower_succ68 B F 11 3 hB hF
  have hCC2 := laurent_coeff_mul_lower_two68 C C 7 7 hC hC
  have hBF2 := laurent_coeff_mul_lower_two68 B F 11 3 hB hF
  have hCC3 := laurent_coeff_mul_lower_three68 C C 7 7 hC hC
  have hBF3 := laurent_coeff_mul_lower_three68 B F 11 3 hB hF
  have hCC4 := laurent_coeff_mul_lower_four68 C C 7 7 hC hC
  have hBF4 := laurent_coeff_mul_lower_four68 B F 11 3 hB hF
  have hCC5 := laurent_coeff_mul_lower_five68 C C 7 7 hC hC
  have hBF5 := laurent_coeff_mul_lower_five68 B F 11 3 hB hF
  norm_num at hCC0 hBF0 hCC1 hBF1 hCC2 hBF2 hCC3 hBF3 hCC4 hBF4 hCC5 hBF5
  have hscale (s : k) (X : LaurentSeries k) (r : ℤ) :
      (HahnSeries.C s * X).coeff r = s * X.coeff r := by
    rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]
  have htwo : (2 : LaurentSeries k) = HahnSeries.C (2 : k) := by
    rw [HahnSeries.C_eq_algebraMap, map_ofNat]
  have hH14 : H.coeff 14 = 0 := by
    dsimp only [H, rhoOneCapCoordinateDefectSeries68]
    rw [pow_two, htwo, HahnSeries.coeff_sub, hscale, hCC0, hBF0]
    linear_combination hT0
  have hH15 : H.coeff 15 = 0 := by
    dsimp only [H, rhoOneCapCoordinateDefectSeries68]
    rw [pow_two, htwo, HahnSeries.coeff_sub, hscale, hCC1, hBF1]
    linear_combination hT1
  have hH16 : H.coeff 16 = 0 := by
    dsimp only [H, rhoOneCapCoordinateDefectSeries68]
    rw [pow_two, htwo, HahnSeries.coeff_sub, hscale, hCC2, hBF2]
    linear_combination hT2
  have hH17 : H.coeff 17 = 0 := by
    dsimp only [H, rhoOneCapCoordinateDefectSeries68]
    rw [pow_two, htwo, HahnSeries.coeff_sub, hscale, hCC3, hBF3]
    linear_combination hT3
  have hH18 : H.coeff 18 = 0 := by
    dsimp only [H, rhoOneCapCoordinateDefectSeries68]
    rw [pow_two, htwo, HahnSeries.coeff_sub, hscale, hCC4, hBF4]
    linear_combination hT4
  have hCCorder : (↑(14 : ℤ) : WithTop ℤ) ≤ (C ^ 2).orderTop := by
    rw [pow_two]
    exact le_trans (add_le_add hC hC) HahnSeries.orderTop_add_le_mul
  have h2CC := laurent_orderTop_ge_const_mul68 (2 : k) (C ^ 2) 14 hCCorder
  have hBForder : (↑(14 : ℤ) : WithTop ℤ) ≤ (B * F).orderTop := by
    exact le_trans (add_le_add hB hF) HahnSeries.orderTop_add_le_mul
  have hHbase : (↑(14 : ℤ) : WithTop ℤ) ≤ H.orderTop := by
    dsimp only [H, rhoOneCapCoordinateDefectSeries68]
    rw [htwo]
    exact le_trans (by simpa using min_le_min h2CC hBForder)
      HahnSeries.min_orderTop_le_orderTop_sub
  have hHorder := laurent_orderTop_gain_fourteen_to_nineteen68
    H hHbase hH14 hH15 hH16 hH17 hH18
  have hT5raw := rhoOneCap_coordinate_defect_endpoint_five68
    epsilon B C F G hB hC hF hR3 hR4 (by simpa only [H] using hHorder) hf3
  dsimp only [rhoOneCapCoordinateDefectSeries68] at hT5raw
  rw [pow_two, htwo, HahnSeries.coeff_sub, hscale, hCC5, hBF5] at hT5raw
  linear_combination hT5raw

end AlignedSquareTerminalGBoundaryCapEndpointRows68

end Max11DegreeRoutes
