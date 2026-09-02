import Sol68ScaleTwoAlignedSquareTerminalGBoundaryCapPostRestorationEightBackwireScratch

/-! # Finite clean-source audit and the post-restoration T₉ row -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareTerminalGBoundaryCapPostRestorationNine68

variable {k : Type*} [Field k] [CharZero k]

local instance alignedSquareCapPostRestorationNineHahnCharZero68 :
    CharZero (LaurentSeries k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℤ))

/-- The restored clean `ABF` window is finite.  `ABF` starts in degree
12, the next I₃ source monomials start in degree 22, and the I₄ source
`B³` starts in degree 33.  Thus clean coordinate rows are T₆ through
T₁₅; after T₈ exactly seven such rows T₉,...,T₁₅ remain. -/
theorem rhoOneCap_restored_clean_source_window_after_eight68 :
    ((-2 : ℤ) + 11 + 3 = 12) ∧
    ((11 : ℤ) + 11 + 0 = 22) ∧
    ((11 : ℤ) + 11 + 11 = 33) ∧
    ((15 : ℤ) < 22) ∧ ((19 : ℤ) < 33) ∧
    ((15 : ℤ) - 9 + 1 = 7) := by
  norm_num

/-- Degree fifteen remains strictly inside the clean `ABF` source
window, so the reduced I₃ row is the third `ABF` jet. -/
theorem rhoOneCap_reduced_i3_coeff_fifteen_of_source_factor68
    (gamma epsilon i3 : k) (A B C CT F G : LaurentSeries k)
    (hA : (↑(-2 : ℤ) : WithTop ℤ) ≤ A.orderTop)
    (hB : (↑(11 : ℤ) : WithTop ℤ) ≤ B.orderTop)
    (hC : (0 : WithTop ℤ) ≤ C.orderTop)
    (hCT : (↑(7 : ℤ) : WithTop ℤ) ≤ CT.orderTop)
    (hF : (↑(3 : ℤ) : WithTop ℤ) ≤ F.orderTop)
    (hG : (↑(-1 : ℤ) : WithTop ℤ) ≤ G.orderTop)
    (hCTeq : CT = C + HahnSeries.C ((3 / 2 : k) * gamma))
    (hfactor : rhoOneI3CapFactored68 (HahnSeries.C gamma)
      (HahnSeries.C epsilon) A B C F G = HahnSeries.C i3) :
    (rhoOneCapReducedI3Series68 epsilon CT F G).coeff 15 =
      (4 / 3 : k) *
        (A.coeff (-2) * B.coeff 11 * F.coeff 6 +
          A.coeff (-2) * B.coeff 12 * F.coeff 5 +
          A.coeff (-2) * B.coeff 13 * F.coeff 4 +
          A.coeff (-2) * B.coeff 14 * F.coeff 3 +
          A.coeff (-1) * B.coeff 11 * F.coeff 5 +
          A.coeff (-1) * B.coeff 12 * F.coeff 4 +
          A.coeff (-1) * B.coeff 13 * F.coeff 3 +
          A.coeff 0 * B.coeff 11 * F.coeff 4 +
          A.coeff 0 * B.coeff 12 * F.coeff 3 +
          A.coeff 1 * B.coeff 11 * F.coeff 3) := by
  let N : LaurentSeries k :=
    HahnSeries.C (4 / 3 : k) * (A * B * F) +
      HahnSeries.C (4 / 3 : k) * (B ^ 2 * C) +
      HahnSeries.C gamma * B ^ 2
  let c : k := (3 / 2 : k) * i3 + (9 / 2 : k) * epsilon * gamma
  have heq : rhoOneCapReducedI3Series68 epsilon CT F G =
      HahnSeries.C c + N := by
    dsimp only [rhoOneCapReducedI3Series68, N, c]
    rw [hCTeq]
    rw [rhoOneI3CapFactored68] at hfactor
    have hC32 : HahnSeries.C (3 / 2 : k) = (3 / 2 : LaurentSeries k) := by
      rw [map_div₀, map_ofNat, map_ofNat]
    have hC92 : HahnSeries.C (9 / 2 : k) = (9 / 2 : LaurentSeries k) := by
      rw [map_div₀, map_ofNat, map_ofNat]
    have hgamma : HahnSeries.C ((3 / 2 : k) * gamma) =
        (3 / 2 : LaurentSeries k) * HahnSeries.C gamma := by
      rw [map_mul, hC32]
    rw [hgamma]
    have hcmap : HahnSeries.C c =
        (3 / 2 : LaurentSeries k) * HahnSeries.C i3 +
          (9 / 2 : LaurentSeries k) * HahnSeries.C epsilon *
            HahnSeries.C gamma := by
      dsimp only [c]
      rw [map_add, map_mul, map_mul, map_mul, hC32, hC92]
    rw [hcmap]
    have h43 : HahnSeries.C (4 / 3 : k) = (4 / 3 : LaurentSeries k) := by
      rw [HahnSeries.C_eq_algebraMap, map_div₀, map_ofNat, map_ofNat]
    rw [h43]
    linear_combination (3 / 2 : LaurentSeries k) * hfactor
  have hABF := laurent_coeff_mul_three_lower_three68 A B F (-2) 11 3 hA hB hF
  norm_num at hABF
  have hBB : (↑(22 : ℤ) : WithTop ℤ) ≤ (B ^ 2).orderTop := by
    rw [pow_two]
    exact le_trans (add_le_add hB hB) HahnSeries.orderTop_add_le_mul
  have hBBC : (↑(22 : ℤ) : WithTop ℤ) ≤ (B ^ 2 * C).orderTop :=
    le_trans (add_le_add hBB hC) HahnSeries.orderTop_add_le_mul
  have hBBC15 : (B ^ 2 * C).coeff 15 = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hBBC)
  have hBB15 : (B ^ 2).coeff 15 = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hBB)
  have hscale (s : k) (X : LaurentSeries k) (r : ℤ) :
      (HahnSeries.C s * X).coeff r = s * X.coeff r := by
    rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]
  have hc15 : (HahnSeries.C c : LaurentSeries k).coeff 15 = 0 := by
    simp [HahnSeries.C_apply]
  have hc := congrArg (fun X : LaurentSeries k => X.coeff 15) heq
  dsimp only [N] at hc
  rw [HahnSeries.coeff_add, HahnSeries.coeff_add, HahnSeries.coeff_add,
    hc15, hscale, hABF, hscale, hBBC15, hscale, hBB15] at hc
  simp only [zero_add, mul_zero, add_zero] at hc
  calc
    (rhoOneCapReducedI3Series68 epsilon CT F G).coeff 15 =
        (4 / 3 : k) *
          (A.coeff (-2) * B.coeff 11 * F.coeff 6 +
            A.coeff (-2) * B.coeff 12 * F.coeff 5 +
            A.coeff (-1) * B.coeff 11 * F.coeff 5 +
            A.coeff (-2) * B.coeff 13 * F.coeff 4 +
            A.coeff (-1) * B.coeff 12 * F.coeff 4 +
            A.coeff 0 * B.coeff 11 * F.coeff 4 +
            A.coeff (-2) * B.coeff 14 * F.coeff 3 +
            A.coeff (-1) * B.coeff 13 * F.coeff 3 +
            A.coeff 0 * B.coeff 12 * F.coeff 3 +
            A.coeff 1 * B.coeff 11 * F.coeff 3) := hc
    _ = _ := by ring

/-- I₄[19] is still below the degree-33 `B³` source endpoint. -/
theorem rhoOneCap_reduced_i4_coeff_nineteen_of_source_factor68
    (gamma epsilon : k) (B C CT F G : LaurentSeries k)
    (hB : (↑(11 : ℤ) : WithTop ℤ) ≤ B.orderTop)
    (hCTeq : CT = C + HahnSeries.C ((3 / 2 : k) * gamma))
    (hfactor : rhoOneI4ZeroFactored68 (HahnSeries.C gamma)
      (HahnSeries.C epsilon) B C F G = 0) :
    (rhoOneCapReducedI4Series68 epsilon B CT F G).coeff 19 = 0 := by
  have heq : rhoOneCapReducedI4Series68 epsilon B CT F G =
      HahnSeries.C (4 / 9 : k) * B ^ 3 := by
    dsimp only [rhoOneCapReducedI4Series68]
    rw [hCTeq]
    rw [rhoOneI4ZeroFactored68] at hfactor
    have hC32 : HahnSeries.C (3 / 2 : k) = (3 / 2 : LaurentSeries k) := by
      rw [map_div₀, map_ofNat, map_ofNat]
    have hgamma : HahnSeries.C ((3 / 2 : k) * gamma) =
        (3 / 2 : LaurentSeries k) * HahnSeries.C gamma := by
      rw [map_mul, hC32]
    rw [hgamma]
    have h49 : HahnSeries.C (4 / 9 : k) = (4 / 9 : LaurentSeries k) := by
      rw [HahnSeries.C_eq_algebraMap, map_div₀, map_ofNat, map_ofNat]
    rw [h49]
    linear_combination (3 / 2 : LaurentSeries k) * hfactor
  have hBB : (↑(22 : ℤ) : WithTop ℤ) ≤ (B ^ 2).orderTop := by
    rw [pow_two]
    exact le_trans (add_le_add hB hB) HahnSeries.orderTop_add_le_mul
  have hBBB : (↑(33 : ℤ) : WithTop ℤ) ≤ (B ^ 3).orderTop := by
    rw [show B ^ 3 = B ^ 2 * B by ring]
    exact le_trans (add_le_add hBB hB) HahnSeries.orderTop_add_le_mul
  have hzero : (B ^ 3).coeff 19 = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hBBB)
  have hscale (s : k) (X : LaurentSeries k) (r : ℤ) :
      (HahnSeries.C s * X).coeff r = s * X.coeff r := by
    rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]
  rw [heq, hscale, hzero, mul_zero]

/-- Coefficient twenty-six transports the third `ABF` source jet to T₉. -/
theorem rhoOneCap_post_restoration_transport_nine68
    (a0 a1 a2 a3 epsilon : k) (B C F G : LaurentSeries k)
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
      (4 / 3 : k) * a0 * B.coeff 11 * F.coeff 3)
    (hR313 : (rhoOneCapReducedI3Series68 epsilon C F G).coeff 13 =
      (4 / 3 : k) * (a0 * B.coeff 11 * F.coeff 4 +
        a0 * B.coeff 12 * F.coeff 3 + a1 * B.coeff 11 * F.coeff 3))
    (hR314 : (rhoOneCapReducedI3Series68 epsilon C F G).coeff 14 =
      (4 / 3 : k) *
        (a0 * B.coeff 11 * F.coeff 5 + a0 * B.coeff 12 * F.coeff 4 +
          a0 * B.coeff 13 * F.coeff 3 + a1 * B.coeff 11 * F.coeff 4 +
          a1 * B.coeff 12 * F.coeff 3 + a2 * B.coeff 11 * F.coeff 3))
    (hR315 : (rhoOneCapReducedI3Series68 epsilon C F G).coeff 15 =
      (4 / 3 : k) *
        (a0 * B.coeff 11 * F.coeff 6 + a0 * B.coeff 12 * F.coeff 5 +
          a0 * B.coeff 13 * F.coeff 4 + a0 * B.coeff 14 * F.coeff 3 +
          a1 * B.coeff 11 * F.coeff 5 + a1 * B.coeff 12 * F.coeff 4 +
          a1 * B.coeff 13 * F.coeff 3 + a2 * B.coeff 11 * F.coeff 4 +
          a2 * B.coeff 12 * F.coeff 3 + a3 * B.coeff 11 * F.coeff 3))
    (hR416 : (rhoOneCapReducedI4Series68 epsilon B C F G).coeff 16 = 0)
    (hR417 : (rhoOneCapReducedI4Series68 epsilon B C F G).coeff 17 = 0)
    (hR418 : (rhoOneCapReducedI4Series68 epsilon B C F G).coeff 18 = 0)
    (hR419 : (rhoOneCapReducedI4Series68 epsilon B C F G).coeff 19 = 0)
    (hH20 : (rhoOneCapCoordinateDefectSeries68 B C F).coeff 20 =
      -(2 / 3 : k) * a0 * B.coeff 11 ^ 2)
    (hH21 : (rhoOneCapCoordinateDefectSeries68 B C F).coeff 21 =
      -(4 / 3 : k) * a0 * B.coeff 11 * B.coeff 12 -
        (2 / 3 : k) * a1 * B.coeff 11 ^ 2)
    (hH22 : (rhoOneCapCoordinateDefectSeries68 B C F).coeff 22 =
      -(4 / 3 : k) * a0 * B.coeff 11 * B.coeff 13 -
        (2 / 3 : k) * a0 * B.coeff 12 ^ 2 -
        (4 / 3 : k) * a1 * B.coeff 11 * B.coeff 12 -
        (2 / 3 : k) * a2 * B.coeff 11 ^ 2) :
    (rhoOneCapCoordinateDefectSeries68 B C F).coeff 23 =
      -(4 / 3 : k) * a0 * B.coeff 11 * B.coeff 14 -
        (4 / 3 : k) * a0 * B.coeff 12 * B.coeff 13 -
        (4 / 3 : k) * a1 * B.coeff 11 * B.coeff 13 -
        (2 / 3 : k) * a1 * B.coeff 12 ^ 2 -
        (4 / 3 : k) * a2 * B.coeff 11 * B.coeff 12 -
        (2 / 3 : k) * a3 * B.coeff 11 ^ 2 := by
  let R3 := rhoOneCapReducedI3Series68 epsilon C F G
  let R4 := rhoOneCapReducedI4Series68 epsilon B C F G
  let H := rhoOneCapCoordinateDefectSeries68 B C F
  have hR417ord := laurent_orderTop_ge_succ_of_coeff_zero68 R4 16
    (by simpa only [R4] using hR4) (by simpa only [R4] using hR416)
  have hR418ord := laurent_orderTop_ge_succ_of_coeff_zero68 R4 17 hR417ord
    (by simpa only [R4] using hR417)
  have hR419ord := laurent_orderTop_ge_succ_of_coeff_zero68 R4 18 hR418ord
    (by simpa only [R4] using hR418)
  have hR420ord := laurent_orderTop_ge_succ_of_coeff_zero68 R4 19 hR419ord
    (by simpa only [R4] using hR419)
  have hBR3 := laurent_coeff_mul_lower_three68 B R3 11 12 hB
    (by simpa only [R3] using hR3)
  have hCR4order : (↑(27 : ℤ) : WithTop ℤ) ≤ (C * R4).orderTop := by
    have h := le_trans (add_le_add hC hR420ord) HahnSeries.orderTop_add_le_mul
    convert h using 1 <;> norm_num
  have hCR4 : (C * R4).coeff 26 = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hCR4order)
  have hFH := laurent_coeff_mul_lower_three68 F H 3 20 hF
    (by simpa only [H] using hH)
  norm_num at hBR3 hFH
  have hc := rhoOneCap_reduced_convolution_coeff68 26 epsilon B C F G
  dsimp only [R3, R4, H] at hBR3 hCR4 hFH ⊢
  rw [HahnSeries.coeff_sub, hBR3, hR312, hR313, hR314, hR315, hCR4] at hc
  have hminusTwo : (-2 : LaurentSeries k) = HahnSeries.C (-2 : k) := by
    rw [HahnSeries.C_eq_algebraMap, map_neg, map_ofNat]
  rw [hminusTwo, HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul,
    hFH, hH20, hH21, hH22] at hc
  have hfactor : F.coeff 3 *
      ((8 / 3 : k) * a0 * B.coeff 11 * B.coeff 14 +
        (8 / 3 : k) * a0 * B.coeff 12 * B.coeff 13 +
        (8 / 3 : k) * a1 * B.coeff 11 * B.coeff 13 +
        (4 / 3 : k) * a1 * B.coeff 12 ^ 2 +
        (8 / 3 : k) * a2 * B.coeff 11 * B.coeff 12 +
        (4 / 3 : k) * a3 * B.coeff 11 ^ 2 + 2 * H.coeff 23) = 0 := by
    linear_combination hc
  have hscalar := (mul_eq_zero.mp hfactor).resolve_left hf3
  linear_combination (1 / 2 : k) * hscalar

end AlignedSquareTerminalGBoundaryCapPostRestorationNine68

end Max11DegreeRoutes
