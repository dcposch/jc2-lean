import Sol68ScaleTwoAlignedSquareTerminalGBoundaryCapI4SixteenClassificationScratch

/-! # Corrected convolution transport after the restored I₃[12] face -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareTerminalGBoundaryCapPostRestorationTransport68

variable {k : Type*} [Field k] [CharZero k]

local instance alignedSquareCapPostRestorationHahnCharZero68 :
    CharZero (LaurentSeries k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℤ))

/-- Six coordinate rows raise the defect order through the verified endpoint. -/
theorem rhoOneCap_coordinate_defect_order_twenty_of_coeff_rows68
    (B C F : LaurentSeries k)
    (hB : (↑(11 : ℤ) : WithTop ℤ) ≤ B.orderTop)
    (hC : (↑(7 : ℤ) : WithTop ℤ) ≤ C.orderTop)
    (hF : (↑(3 : ℤ) : WithTop ℤ) ≤ F.orderTop)
    (h14 : (rhoOneCapCoordinateDefectSeries68 B C F).coeff 14 = 0)
    (h15 : (rhoOneCapCoordinateDefectSeries68 B C F).coeff 15 = 0)
    (h16 : (rhoOneCapCoordinateDefectSeries68 B C F).coeff 16 = 0)
    (h17 : (rhoOneCapCoordinateDefectSeries68 B C F).coeff 17 = 0)
    (h18 : (rhoOneCapCoordinateDefectSeries68 B C F).coeff 18 = 0)
    (h19 : (rhoOneCapCoordinateDefectSeries68 B C F).coeff 19 = 0) :
    (↑(20 : ℤ) : WithTop ℤ) ≤
      (rhoOneCapCoordinateDefectSeries68 B C F).orderTop := by
  let H := rhoOneCapCoordinateDefectSeries68 B C F
  have hCC : (↑(14 : ℤ) : WithTop ℤ) ≤ (C ^ 2).orderTop := by
    rw [pow_two]
    exact le_trans (add_le_add hC hC) HahnSeries.orderTop_add_le_mul
  have h2CC := laurent_orderTop_ge_const_mul68 (2 : k) (C ^ 2) 14 hCC
  have hBF : (↑(14 : ℤ) : WithTop ℤ) ≤ (B * F).orderTop :=
    le_trans (add_le_add hB hF) HahnSeries.orderTop_add_le_mul
  have h14base : (↑(14 : ℤ) : WithTop ℤ) ≤ H.orderTop := by
    dsimp only [H, rhoOneCapCoordinateDefectSeries68]
    have htwo : (2 : LaurentSeries k) = HahnSeries.C (2 : k) := by
      rw [HahnSeries.C_eq_algebraMap, map_ofNat]
    rw [htwo]
    exact le_trans (by simpa using min_le_min h2CC hBF)
      HahnSeries.min_orderTop_le_orderTop_sub
  have h19order := laurent_orderTop_gain_fourteen_to_nineteen68 H h14base
    (by simpa only [H] using h14) (by simpa only [H] using h15)
    (by simpa only [H] using h16) (by simpa only [H] using h17)
    (by simpa only [H] using h18)
  have h20 := laurent_orderTop_ge_succ_of_coeff_zero68 H 19 h19order
    (by simpa only [H] using h19)
  change (↑(20 : ℤ) : WithTop ℤ) ≤ H.orderTop
  convert h20 using 1 <;> norm_num

/-- The coefficient-23 convolution is the first corrected recurrence.  The
restored `ABF` face makes `H[20]` a prescribed nonzero-scale scalar rather
than another zero row. -/
theorem rhoOneCap_post_restoration_transport68
    (a epsilon : k) (B C F G : LaurentSeries k)
    (hB : (↑(11 : ℤ) : WithTop ℤ) ≤ B.orderTop)
    (hC : (↑(7 : ℤ) : WithTop ℤ) ≤ C.orderTop)
    (hF : (↑(3 : ℤ) : WithTop ℤ) ≤ F.orderTop)
    (hf3 : F.coeff 3 ≠ 0)
    (hR3 : (↑(12 : ℤ) : WithTop ℤ) ≤
      (rhoOneCapReducedI3Series68 epsilon C F G).orderTop)
    (hR4 : (↑(16 : ℤ) : WithTop ℤ) ≤
      (rhoOneCapReducedI4Series68 epsilon B C F G).orderTop)
    (hH : (↑(20 : ℤ) : WithTop ℤ) ≤
      (rhoOneCapCoordinateDefectSeries68 B C F).orderTop)
    (hR312 : (rhoOneCapReducedI3Series68 epsilon C F G).coeff 12 =
      (4 / 3 : k) * a * B.coeff 11 * F.coeff 3)
    (hR416 : (rhoOneCapReducedI4Series68 epsilon B C F G).coeff 16 = 0) :
    (rhoOneCapCoordinateDefectSeries68 B C F).coeff 20 =
      -(2 / 3 : k) * a * B.coeff 11 ^ 2 := by
  let R3 := rhoOneCapReducedI3Series68 epsilon C F G
  let R4 := rhoOneCapReducedI4Series68 epsilon B C F G
  let H := rhoOneCapCoordinateDefectSeries68 B C F
  have hR417 := laurent_orderTop_ge_succ_of_coeff_zero68 R4 16
    (by simpa only [R4] using hR4) (by simpa only [R4] using hR416)
  have hBR3 := laurent_coeff_mul_lower68 B R3 11 12 hB
    (by simpa only [R3] using hR3)
  have hCR4order : (↑(24 : ℤ) : WithTop ℤ) ≤ (C * R4).orderTop := by
    have h := le_trans (add_le_add hC hR417) HahnSeries.orderTop_add_le_mul
    convert h using 1 <;> norm_num
  have hCR4 : (C * R4).coeff 23 = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hCR4order)
  have hFH := laurent_coeff_mul_lower68 F H 3 20 hF
    (by simpa only [H] using hH)
  norm_num at hBR3 hFH
  have hc := rhoOneCap_reduced_convolution_coeff68 23 epsilon B C F G
  dsimp only [R3, R4, H] at hBR3 hCR4 hFH ⊢
  rw [HahnSeries.coeff_sub, hBR3, hR312, hCR4] at hc
  have hminusTwo : (-2 : LaurentSeries k) = HahnSeries.C (-2 : k) := by
    rw [HahnSeries.C_eq_algebraMap, map_neg, map_ofNat]
  rw [hminusTwo, HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul,
    hFH] at hc
  have hfactor : F.coeff 3 *
      ((4 / 3 : k) * a * B.coeff 11 ^ 2 + 2 * H.coeff 20) = 0 := by
    linear_combination hc
  have hscalar := (mul_eq_zero.mp hfactor).resolve_left hf3
  linear_combination (1 / 2 : k) * hscalar

/-- The explicit seventh coordinate jet (`H[20]`). -/
def rhoOneCapCoordinateDefectT6Core68
    (B C F : HahnSeries ℚ k) : k :=
  4 * C.coeff 7 * C.coeff 13 + 4 * C.coeff 8 * C.coeff 12 +
    4 * C.coeff 9 * C.coeff 11 + 2 * C.coeff 10 ^ 2 -
    B.coeff 17 * F.coeff 3 - B.coeff 16 * F.coeff 4 -
    B.coeff 15 * F.coeff 5 - B.coeff 14 * F.coeff 6 -
    B.coeff 13 * F.coeff 7 - B.coeff 12 * F.coeff 8 -
    B.coeff 11 * F.coeff 9

end AlignedSquareTerminalGBoundaryCapPostRestorationTransport68

end Max11DegreeRoutes
