import Sol68ScaleTwoAlignedSquareTerminalGBoundaryCapPostRestorationBackwireScratch

/-! # First source-sensitive jet after the restored T₆ row -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareTerminalGBoundaryCapPostRestorationNextSource68

variable {k : Type*} [Field k] [CharZero k]

local instance alignedSquareCapPostRestorationNextSourceHahnCharZero68 :
    CharZero (LaurentSeries k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℤ))

/-- At source degree thirteen, the only surviving nonconstant correction to
the reduced I₃ series is the first higher jet of `ABF`. -/
theorem rhoOneCap_reduced_i3_coeff_thirteen_of_source_factor68
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
    (rhoOneCapReducedI3Series68 epsilon CT F G).coeff 13 =
      (4 / 3 : k) *
        (A.coeff (-2) * B.coeff 11 * F.coeff 4 +
          A.coeff (-2) * B.coeff 12 * F.coeff 3 +
          A.coeff (-1) * B.coeff 11 * F.coeff 3) := by
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
  have hABF := laurent_coeff_mul_three_lower_succ68 A B F (-2) 11 3 hA hB hF
  norm_num at hABF
  have hBB : (↑(22 : ℤ) : WithTop ℤ) ≤ (B ^ 2).orderTop := by
    rw [pow_two]
    exact le_trans (add_le_add hB hB) HahnSeries.orderTop_add_le_mul
  have hBBC : (↑(22 : ℤ) : WithTop ℤ) ≤ (B ^ 2 * C).orderTop :=
    le_trans (add_le_add hBB hC) HahnSeries.orderTop_add_le_mul
  have hBBC13 : (B ^ 2 * C).coeff 13 = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hBBC)
  have hBB13 : (B ^ 2).coeff 13 = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hBB)
  have hscale (s : k) (X : LaurentSeries k) (r : ℤ) :
      (HahnSeries.C s * X).coeff r = s * X.coeff r := by
    rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]
  have hc13 : (HahnSeries.C c : LaurentSeries k).coeff 13 = 0 := by
    simp [HahnSeries.C_apply]
  have hc := congrArg (fun X : LaurentSeries k => X.coeff 13) heq
  dsimp only [N] at hc
  rw [HahnSeries.coeff_add, HahnSeries.coeff_add, HahnSeries.coeff_add,
    hc13, hscale, hABF, hscale, hBBC13, hscale, hBB13] at hc
  simp only [zero_add, mul_zero, add_zero] at hc
  calc
    (rhoOneCapReducedI3Series68 epsilon CT F G).coeff 13 =
        (4 / 3 : k) *
          (A.coeff (-1) * B.coeff 11 * F.coeff 3 +
            A.coeff (-2) * B.coeff 12 * F.coeff 3 +
            A.coeff (-2) * B.coeff 11 * F.coeff 4) := hc
    _ = _ := by ring

/-- The source I₄ factor has no coefficient at seventeen: its remaining
right side is a cubic in `B`, of order at least thirty-three. -/
theorem rhoOneCap_reduced_i4_coeff_seventeen_of_source_factor68
    (gamma epsilon : k) (B C CT F G : LaurentSeries k)
    (hB : (↑(11 : ℤ) : WithTop ℤ) ≤ B.orderTop)
    (hCTeq : CT = C + HahnSeries.C ((3 / 2 : k) * gamma))
    (hfactor : rhoOneI4ZeroFactored68 (HahnSeries.C gamma)
      (HahnSeries.C epsilon) B C F G = 0) :
    (rhoOneCapReducedI4Series68 epsilon B CT F G).coeff 17 = 0 := by
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
  have hzero : (B ^ 3).coeff 17 = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hBBB)
  have hscale (s : k) (X : LaurentSeries k) (r : ℤ) :
      (HahnSeries.C s * X).coeff r = s * X.coeff r := by
    rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]
  rw [heq, hscale, hzero, mul_zero]

/-- Coefficient twenty-four of the corrected convolution.  The terms in
`F[4] H[20]` cancel the matching first `ABF` jet, leaving a clean T₇ row. -/
theorem rhoOneCap_post_restoration_transport_seven68
    (a a1 epsilon : k) (B C F G : LaurentSeries k)
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
    (hR313 : (rhoOneCapReducedI3Series68 epsilon C F G).coeff 13 =
      (4 / 3 : k) * (a * B.coeff 11 * F.coeff 4 +
        a * B.coeff 12 * F.coeff 3 + a1 * B.coeff 11 * F.coeff 3))
    (hR416 : (rhoOneCapReducedI4Series68 epsilon B C F G).coeff 16 = 0)
    (hR417 : (rhoOneCapReducedI4Series68 epsilon B C F G).coeff 17 = 0)
    (hH20 : (rhoOneCapCoordinateDefectSeries68 B C F).coeff 20 =
      -(2 / 3 : k) * a * B.coeff 11 ^ 2) :
    (rhoOneCapCoordinateDefectSeries68 B C F).coeff 21 =
      -(4 / 3 : k) * a * B.coeff 11 * B.coeff 12 -
        (2 / 3 : k) * a1 * B.coeff 11 ^ 2 := by
  let R3 := rhoOneCapReducedI3Series68 epsilon C F G
  let R4 := rhoOneCapReducedI4Series68 epsilon B C F G
  let H := rhoOneCapCoordinateDefectSeries68 B C F
  have hR417ord := laurent_orderTop_ge_succ_of_coeff_zero68 R4 16
    (by simpa only [R4] using hR4) (by simpa only [R4] using hR416)
  have hR418ord := laurent_orderTop_ge_succ_of_coeff_zero68 R4 17 hR417ord
    (by simpa only [R4] using hR417)
  have hBR3 := laurent_coeff_mul_lower_succ68 B R3 11 12 hB
    (by simpa only [R3] using hR3)
  have hCR4order : (↑(25 : ℤ) : WithTop ℤ) ≤ (C * R4).orderTop := by
    have h := le_trans (add_le_add hC hR418ord) HahnSeries.orderTop_add_le_mul
    convert h using 1 <;> norm_num
  have hCR4 : (C * R4).coeff 24 = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hCR4order)
  have hFH := laurent_coeff_mul_lower_succ68 F H 3 20 hF
    (by simpa only [H] using hH)
  norm_num at hBR3 hFH
  have hc := rhoOneCap_reduced_convolution_coeff68 24 epsilon B C F G
  dsimp only [R3, R4, H] at hBR3 hCR4 hFH ⊢
  rw [HahnSeries.coeff_sub, hBR3, hR312, hR313, hCR4] at hc
  have hminusTwo : (-2 : LaurentSeries k) = HahnSeries.C (-2 : k) := by
    rw [HahnSeries.C_eq_algebraMap, map_neg, map_ofNat]
  rw [hminusTwo, HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul,
    hFH, hH20] at hc
  have hfactor : F.coeff 3 *
      ((8 / 3 : k) * a * B.coeff 11 * B.coeff 12 +
        (4 / 3 : k) * a1 * B.coeff 11 ^ 2 + 2 * H.coeff 21) = 0 := by
    linear_combination hc
  have hscalar := (mul_eq_zero.mp hfactor).resolve_left hf3
  linear_combination (1 / 2 : k) * hscalar

end AlignedSquareTerminalGBoundaryCapPostRestorationNextSource68

end Max11DegreeRoutes
