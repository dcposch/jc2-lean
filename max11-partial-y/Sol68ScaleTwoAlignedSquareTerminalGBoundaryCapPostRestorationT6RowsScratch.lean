import Sol68ScaleTwoAlignedSquareTerminalGBoundaryCapPostRestorationT6Scratch

/-! # Corrected T₆ from the six coordinate rows and restored integral rows -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareTerminalGBoundaryCapPostRestorationT6Rows68

variable {k : Type*} [Field k] [CharZero k]

local instance alignedSquareCapPostRestorationT6RowsHahnCharZero68 :
    CharZero (LaurentSeries k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℤ))

theorem rhoOneCap_post_restoration_t6_of_rows68
    (a epsilon : k) (B C F G : LaurentSeries k)
    (hB : (↑(11 : ℤ) : WithTop ℤ) ≤ B.orderTop)
    (hC : (↑(7 : ℤ) : WithTop ℤ) ≤ C.orderTop)
    (hF : (↑(3 : ℤ) : WithTop ℤ) ≤ F.orderTop)
    (hG : (↑(-1 : ℤ) : WithTop ℤ) ≤ G.orderTop)
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
      B.coeff 12 * F.coeff 6 - B.coeff 11 * F.coeff 7 = 0)
    (hT5 : 4 * C.coeff 7 * C.coeff 12 + 4 * C.coeff 8 * C.coeff 11 +
      4 * C.coeff 9 * C.coeff 10 - B.coeff 16 * F.coeff 3 -
      B.coeff 15 * F.coeff 4 - B.coeff 14 * F.coeff 5 -
      B.coeff 13 * F.coeff 6 - B.coeff 12 * F.coeff 7 -
      B.coeff 11 * F.coeff 8 = 0)
    (hI3 : -(4 / 3 : k) * a * B.coeff 11 * F.coeff 3 +
      4 * rhoOneI3CapTwelveReducedLaurentCore68 C F G +
      3 * epsilon * C.coeff 12 = 0)
    (hI4 : 4 * rhoOneI4CapSixteenLaurentCore68 B C F G +
      3 * epsilon * B.coeff 16 = 0) :
    rhoOneCapCoordinateDefectT6LaurentCore68 B C F =
      -(2 / 3 : k) * a * B.coeff 11 ^ 2 := by
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
    rw [pow_two, HahnSeries.coeff_sub, htwo, hscale, hCC0, hBF0]
    linear_combination hT0
  have hH15 : H.coeff 15 = 0 := by
    dsimp only [H, rhoOneCapCoordinateDefectSeries68]
    rw [pow_two, HahnSeries.coeff_sub, htwo, hscale, hCC1, hBF1]
    linear_combination hT1
  have hH16 : H.coeff 16 = 0 := by
    dsimp only [H, rhoOneCapCoordinateDefectSeries68]
    rw [pow_two, HahnSeries.coeff_sub, htwo, hscale, hCC2, hBF2]
    linear_combination hT2
  have hH17 : H.coeff 17 = 0 := by
    dsimp only [H, rhoOneCapCoordinateDefectSeries68]
    rw [pow_two, HahnSeries.coeff_sub, htwo, hscale, hCC3, hBF3]
    linear_combination hT3
  have hH18 : H.coeff 18 = 0 := by
    dsimp only [H, rhoOneCapCoordinateDefectSeries68]
    rw [pow_two, HahnSeries.coeff_sub, htwo, hscale, hCC4, hBF4]
    linear_combination hT4
  have hH19 : H.coeff 19 = 0 := by
    dsimp only [H, rhoOneCapCoordinateDefectSeries68]
    rw [pow_two, HahnSeries.coeff_sub, htwo, hscale, hCC5, hBF5]
    linear_combination hT5
  have hHorder := rhoOneCap_coordinate_defect_order_twenty_of_coeff_rows68
    B C F hB hC hF (by simpa only [H] using hH14)
    (by simpa only [H] using hH15) (by simpa only [H] using hH16)
    (by simpa only [H] using hH17) (by simpa only [H] using hH18)
    (by simpa only [H] using hH19)
  have hR3core := rhoOneCap_reduced_i3_coeff_twelve_core68
    epsilon C F G hC hF hG
  have hR312 : (rhoOneCapReducedI3Series68 epsilon C F G).coeff 12 =
      (4 / 3 : k) * a * B.coeff 11 * F.coeff 3 := by
    linear_combination hR3core + hI3
  have hR4core := rhoOneCap_reduced_i4_coeff_sixteen_core68
    epsilon B C F G hB hC hF hG
  have hR416 : (rhoOneCapReducedI4Series68 epsilon B C F G).coeff 16 = 0 := by
    linear_combination hR4core + hI4
  have htransport := rhoOneCap_post_restoration_transport68 a epsilon B C F G
    hB hC hF hf3 hR3 hR4 hHorder hR312 hR416
  have hT6core := rhoOneCap_coordinate_defect_coeff_twenty_core68
    B C F hB hC hF
  rw [hT6core] at htransport
  exact htransport

end AlignedSquareTerminalGBoundaryCapPostRestorationT6Rows68

end Max11DegreeRoutes
