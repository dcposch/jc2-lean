import Sol68ScaleTwoAlignedSquareTerminalGBoundaryCapI3TwelveBackwireScratch

/-! # Exact I₄[16] and its restored-I₃ cross -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareTerminalGBoundaryCapI4Sixteen68

variable {k : Type*} [Field k] [CharZero k]

local instance alignedSquareTerminalGBoundaryCapI4SixteenHahnCharZero68 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

theorem rhoOneI4ZeroFactored_cap_coeff_sixteen68
    (root gamma epsilon : k) (B C F G : RatFunc k)
    (hB : (↑(11 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root B).orderTop)
    (hF : (↑(3 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root F).orderTop)
    (hG : (↑(-1 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root G).orderTop)
    (hS : (↑(7 : ℚ) : WithTop ℚ) ≤
      (2 * ratFuncAtHahn46 root C + HahnSeries.C (3 * gamma)).orderTop)
    (hfactor : rhoOneI4ZeroFactored68
      (RatFunc.C gamma) (RatFunc.C epsilon) B C F G = 0) :
    4 * ((ratFuncAtHahn46 root B).coeff 11 * (ratFuncAtHahn46 root G).coeff 5 +
        (ratFuncAtHahn46 root B).coeff 12 * (ratFuncAtHahn46 root G).coeff 4 +
        (ratFuncAtHahn46 root B).coeff 13 * (ratFuncAtHahn46 root G).coeff 3 +
        (ratFuncAtHahn46 root B).coeff 14 * (ratFuncAtHahn46 root G).coeff 2 +
        (ratFuncAtHahn46 root B).coeff 15 * (ratFuncAtHahn46 root G).coeff 1 +
        (ratFuncAtHahn46 root B).coeff 16 * (ratFuncAtHahn46 root G).coeff 0 +
        (ratFuncAtHahn46 root B).coeff 17 * (ratFuncAtHahn46 root G).coeff (-1 : ℚ)) +
      4 * ((ratFuncAtHahn46 root C).coeff 7 * (ratFuncAtHahn46 root F).coeff 9 +
        (ratFuncAtHahn46 root C).coeff 8 * (ratFuncAtHahn46 root F).coeff 8 +
        (ratFuncAtHahn46 root C).coeff 9 * (ratFuncAtHahn46 root F).coeff 7 +
        (ratFuncAtHahn46 root C).coeff 10 * (ratFuncAtHahn46 root F).coeff 6 +
        (ratFuncAtHahn46 root C).coeff 11 * (ratFuncAtHahn46 root F).coeff 5 +
        (ratFuncAtHahn46 root C).coeff 12 * (ratFuncAtHahn46 root F).coeff 4 +
        (ratFuncAtHahn46 root C).coeff 13 * (ratFuncAtHahn46 root F).coeff 3) +
      3 * epsilon * (ratFuncAtHahn46 root B).coeff 16 = 0 := by
  let BL : LaurentSeries k := ratFuncAtLaurent46 root B
  let CL : LaurentSeries k := ratFuncAtLaurent46 root C
  let FL : LaurentSeries k := ratFuncAtLaurent46 root F
  let Gser : LaurentSeries k := ratFuncAtLaurent46 root G
  let SR : RatFunc k := 2 * C + RatFunc.C (3 * gamma)
  let SL : LaurentSeries k := 2 * CL + HahnSeries.C (3 * gamma)
  have hBL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root B 11 hB
  have hFL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root F 3 hF
  have hGL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root G (-1) hG
  have hSRH : ratFuncAtHahn46 root SR =
      2 * ratFuncAtHahn46 root C + HahnSeries.C (3 * gamma) := by
    dsimp only [SR]
    simp only [map_add, map_mul, map_ofNat, ratFuncAtHahn46_C]
  have hSRL : ratFuncAtLaurent46 root SR = SL := by
    dsimp only [SR, SL, CL]
    simp only [map_add, map_mul, map_ofNat, ratFuncAtLaurent46_C68]
  have hSL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root SR 7 (by
    rw [hSRH]
    exact hS)
  rw [hSRL] at hSL
  have hBG := laurent_coeff_mul_lower_six68 BL Gser 11 (-1) hBL hGL
  have hSF := laurent_coeff_mul_lower_six68 SL FL 7 3 hSL hFL
  norm_num at hBG hSF
  have hBcubeOrder : (↑(33 : ℤ) : WithTop ℤ) ≤ (BL ^ 3).orderTop := by
    have hp := HahnSeries.orderTop_nsmul_le_orderTop_pow (x := BL) (n := 3)
    have htriple := nsmul_le_nsmul_right hBL 3
    norm_num at htriple
    exact le_trans htriple hp
  have hBcube : (BL ^ 3).coeff (16 : ℤ) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hBcubeOrder)
  have hfactorL := congrArg (ratFuncAtLaurent46 root) hfactor
  have hfactorL' : rhoOneI4ZeroFactored68
      (HahnSeries.C gamma) (HahnSeries.C epsilon) BL CL FL Gser = 0 := by
    simpa only [rhoOneI4ZeroFactored68, BL, CL, FL, Gser, map_add,
      map_mul, map_pow, map_neg, map_div₀, map_ofNat, map_zero, map_one,
      ratFuncAtLaurent46_C68] using hfactorL
  have hSLform : 2 * CL + 3 * HahnSeries.C gamma = SL := by
    dsimp only [SL]
    congr 1
    rw [HahnSeries.C_eq_algebraMap, map_mul, map_ofNat]
  rw [rhoOneI4ZeroFactored68, hSLform] at hfactorL'
  have hc := congrArg (fun X : LaurentSeries k => X.coeff (16 : ℤ)) hfactorL'
  simp only [HahnSeries.coeff_add, HahnSeries.coeff_zero] at hc
  have hscale (s : k) (X : LaurentSeries k) (r : ℤ) :
      (HahnSeries.C s * X).coeff r = s * X.coeff r := by
    rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]
  have hsc1 : ((-8 / 27 : LaurentSeries k) * BL ^ 3).coeff 16 = 0 := by
    have hcst : (-8 / 27 : LaurentSeries k) = HahnSeries.C (-8 / 27 : k) := by
      rw [HahnSeries.C_eq_algebraMap, map_div₀, map_neg, map_ofNat, map_ofNat]
    rw [hcst, hscale, hBcube, mul_zero]
  have hsc2 : ((8 / 3 : LaurentSeries k) * BL * Gser).coeff 16 =
      (8 / 3 : k) * (BL * Gser).coeff 16 := by
    have hcst : (8 / 3 : LaurentSeries k) = HahnSeries.C (8 / 3 : k) := by
      rw [HahnSeries.C_eq_algebraMap, map_div₀, map_ofNat, map_ofNat]
    rw [mul_assoc, hcst, hscale]
  have hsc3 : ((4 / 3 : LaurentSeries k) * SL * FL).coeff 16 =
      (4 / 3 : k) * (SL * FL).coeff 16 := by
    have hcst : (4 / 3 : LaurentSeries k) = HahnSeries.C (4 / 3 : k) := by
      rw [HahnSeries.C_eq_algebraMap, map_div₀, map_ofNat, map_ofNat]
    rw [mul_assoc, hcst, hscale]
  have hsc4 : ((2 : LaurentSeries k) * HahnSeries.C epsilon * BL).coeff 16 =
      (2 * epsilon) * BL.coeff 16 := by
    have h2 : (2 : LaurentSeries k) = HahnSeries.C (2 : k) := by
      rw [HahnSeries.C_eq_algebraMap, map_ofNat]
    rw [h2, ← map_mul, hscale]
  rw [hsc1, hsc2, hsc3, hsc4, hBG, hSF] at hc
  have hSLpos (n : ℤ) (hn : n ≠ 0) : SL.coeff n = 2 * CL.coeff n := by
    dsimp only [SL]
    simp [HahnSeries.C_apply, hn, two_mul]
  have hs7 := hSLpos 7 (by norm_num)
  have hs8 := hSLpos 8 (by norm_num)
  have hs9 := hSLpos 9 (by norm_num)
  have hs10 := hSLpos 10 (by norm_num)
  have hs11 := hSLpos 11 (by norm_num)
  have hs12 := hSLpos 12 (by norm_num)
  have hs13 := hSLpos 13 (by norm_num)
  rw [hs7, hs8, hs9, hs10, hs11, hs12, hs13] at hc
  have hB11 := ratFuncAtHahn46_coeff_int68 root B 11
  have hB12 := ratFuncAtHahn46_coeff_int68 root B 12
  have hB13 := ratFuncAtHahn46_coeff_int68 root B 13
  have hB14 := ratFuncAtHahn46_coeff_int68 root B 14
  have hB15 := ratFuncAtHahn46_coeff_int68 root B 15
  have hB16 := ratFuncAtHahn46_coeff_int68 root B 16
  have hB17 := ratFuncAtHahn46_coeff_int68 root B 17
  have hC7 := ratFuncAtHahn46_coeff_int68 root C 7
  have hC8 := ratFuncAtHahn46_coeff_int68 root C 8
  have hC9 := ratFuncAtHahn46_coeff_int68 root C 9
  have hC10 := ratFuncAtHahn46_coeff_int68 root C 10
  have hC11 := ratFuncAtHahn46_coeff_int68 root C 11
  have hC12 := ratFuncAtHahn46_coeff_int68 root C 12
  have hC13 := ratFuncAtHahn46_coeff_int68 root C 13
  have hF3 := ratFuncAtHahn46_coeff_int68 root F 3
  have hF4 := ratFuncAtHahn46_coeff_int68 root F 4
  have hF5 := ratFuncAtHahn46_coeff_int68 root F 5
  have hF6 := ratFuncAtHahn46_coeff_int68 root F 6
  have hF7 := ratFuncAtHahn46_coeff_int68 root F 7
  have hF8 := ratFuncAtHahn46_coeff_int68 root F 8
  have hF9 := ratFuncAtHahn46_coeff_int68 root F 9
  have hGm1 := ratFuncAtHahn46_coeff_int68 root G (-1)
  have hG0 := ratFuncAtHahn46_coeff_int68 root G 0
  have hG1 := ratFuncAtHahn46_coeff_int68 root G 1
  have hG2 := ratFuncAtHahn46_coeff_int68 root G 2
  have hG3 := ratFuncAtHahn46_coeff_int68 root G 3
  have hG4 := ratFuncAtHahn46_coeff_int68 root G 4
  have hG5 := ratFuncAtHahn46_coeff_int68 root G 5
  norm_num at hB11 hB12 hB13 hB14 hB15 hB16 hB17 hC7 hC8 hC9 hC10 hC11 hC12 hC13 hF3 hF4 hF5 hF6 hF7 hF8 hF9 hGm1 hG0 hG1 hG2 hG3 hG4 hG5
  dsimp only [BL, CL, FL, Gser] at hc
  rw [← hB11, ← hB12, ← hB13, ← hB14, ← hB15, ← hB16, ← hB17,
    ← hC7, ← hC8, ← hC9, ← hC10, ← hC11, ← hC12, ← hC13,
    ← hF3, ← hF4, ← hF5, ← hF6, ← hF7, ← hF8, ← hF9,
    ← hGm1, ← hG0, ← hG1, ← hG2, ← hG3, ← hG4, ← hG5] at hc
  linear_combination (3 / 2 : k) * hc

def rhoOneI4CapSixteenCore68 (B C F G : HahnSeries ℚ k) : k :=
  B.coeff 11 * G.coeff 5 + B.coeff 12 * G.coeff 4 +
    B.coeff 13 * G.coeff 3 + B.coeff 14 * G.coeff 2 +
    B.coeff 15 * G.coeff 1 + B.coeff 16 * G.coeff 0 +
    B.coeff 17 * G.coeff (-1 : ℚ) + C.coeff 7 * F.coeff 9 +
    C.coeff 8 * F.coeff 8 + C.coeff 9 * F.coeff 7 +
    C.coeff 10 * F.coeff 6 + C.coeff 11 * F.coeff 5 +
    C.coeff 12 * F.coeff 4 + C.coeff 13 * F.coeff 3

theorem rhoOneI3I4_cap_sixteen_restored_cross68
    (a b f x y epsilon c12 b16 : k)
    (h3 : -(4 / 3 : k) * a * b * f + 4 * x + 3 * epsilon * c12 = 0)
    (h4 : 4 * y + 3 * epsilon * b16 = 0) :
    b16 * (-(4 / 3 : k) * a * b * f + 4 * x) -
      4 * c12 * y = 0 := by
  linear_combination b16 * h3 - c12 * h4

end AlignedSquareTerminalGBoundaryCapI4Sixteen68

end Max11DegreeRoutes
