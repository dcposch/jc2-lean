import Sol68ScaleTwoAlignedSquareTerminalGBoundaryCapConvolutionInductionScratch

/-! # Exact I₃[11], the last pure reduced third-integral row -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareTerminalGBoundaryCapI3Eleven68

variable {k : Type*} [Field k] [CharZero k]

local instance alignedSquareTerminalGBoundaryCapI3ElevenHahnCharZero68 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

theorem laurent_coeff_mul_lower_five68
    (X Y : LaurentSeries k) (m n : ℤ)
    (hX : (↑m : WithTop ℤ) ≤ X.orderTop)
    (hY : (↑n : WithTop ℤ) ≤ Y.orderTop) :
    (X * Y).coeff (m + n + 5) =
      X.coeff m * Y.coeff (n + 5) +
      X.coeff (m + 1) * Y.coeff (n + 4) +
      X.coeff (m + 2) * Y.coeff (n + 3) +
      X.coeff (m + 3) * Y.coeff (n + 2) +
      X.coeff (m + 4) * Y.coeff (n + 1) +
      X.coeff (m + 5) * Y.coeff n := by
  let Xt : LaurentSeries k := X - HahnSeries.single m (X.coeff m)
  have hsm : (↑m : WithTop ℤ) ≤
      (HahnSeries.single m (X.coeff m) : LaurentSeries k).orderTop := by
    by_cases hx : X.coeff m = 0
    · simp [hx]
    · rw [HahnSeries.orderTop_single hx]
  have hXt0 : Xt.coeff m = 0 := by simp [Xt]
  have hXtBase : (↑m : WithTop ℤ) ≤ Xt.orderTop :=
    le_trans (by simpa using min_le_min hX hsm)
      HahnSeries.min_orderTop_le_orderTop_sub
  have hXt := laurent_orderTop_ge_succ_of_coeff_zero68 Xt m hXtBase hXt0
  have htail := laurent_coeff_mul_lower_four68 Xt Y (m + 1) n hXt hY
  have htail' : (Xt * Y).coeff (m + n + 5) =
      Xt.coeff (m + 1) * Y.coeff (n + 4) +
      Xt.coeff (m + 2) * Y.coeff (n + 3) +
      Xt.coeff (m + 3) * Y.coeff (n + 2) +
      Xt.coeff (m + 4) * Y.coeff (n + 1) +
      Xt.coeff (m + 5) * Y.coeff n := by
    convert htail using 1 <;> ring
  have hXt1 : Xt.coeff (m + 1) = X.coeff (m + 1) := by
    simp only [Xt, HahnSeries.coeff_sub, HahnSeries.coeff_single]
    rw [if_neg (by omega)]
    ring
  have hXt2 : Xt.coeff (m + 2) = X.coeff (m + 2) := by
    simp only [Xt, HahnSeries.coeff_sub, HahnSeries.coeff_single]
    rw [if_neg (by omega)]
    ring
  have hXt3 : Xt.coeff (m + 3) = X.coeff (m + 3) := by
    simp only [Xt, HahnSeries.coeff_sub, HahnSeries.coeff_single]
    rw [if_neg (by omega)]
    ring
  have hXt4 : Xt.coeff (m + 4) = X.coeff (m + 4) := by
    simp only [Xt, HahnSeries.coeff_sub, HahnSeries.coeff_single]
    rw [if_neg (by omega)]
    ring
  have hXt5 : Xt.coeff (m + 5) = X.coeff (m + 5) := by
    simp only [Xt, HahnSeries.coeff_sub, HahnSeries.coeff_single]
    rw [if_neg (by omega)]
    ring
  have hlead :
      ((HahnSeries.single m (X.coeff m) : LaurentSeries k) * Y).coeff
          (m + n + 5) = X.coeff m * Y.coeff (n + 5) := by
    rw [HahnSeries.coeff_single_mul]
    have hi : m + n + 5 - m = n + 5 := by omega
    rw [hi]
  have hXdec : X = HahnSeries.single m (X.coeff m) + Xt := by simp [Xt]
  calc
    (X * Y).coeff (m + n + 5) =
        ((HahnSeries.single m (X.coeff m) + Xt) * Y).coeff
          (m + n + 5) := by rw [← hXdec]
    _ = _ := by
      rw [add_mul, HahnSeries.coeff_add, hlead, htail', hXt1, hXt2,
        hXt3, hXt4, hXt5]
      ring

theorem rhoOneI3CapFactored_cap_coeff_eleven68
    (root gamma epsilon i3 : k) (A B C F G : RatFunc k)
    (hA : (↑(-2 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root A).orderTop)
    (hB : (↑(11 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root B).orderTop)
    (hC : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 root C).orderTop)
    (hF : (↑(3 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root F).orderTop)
    (hG : (↑(-1 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root G).orderTop)
    (hS : (↑(7 : ℚ) : WithTop ℚ) ≤
      (2 * ratFuncAtHahn46 root C + HahnSeries.C (3 * gamma)).orderTop)
    (hfactor : rhoOneI3CapFactored68 (RatFunc.C gamma)
      (RatFunc.C epsilon) A B C F G = RatFunc.C i3) :
    4 * ((ratFuncAtHahn46 root C).coeff 7 * (ratFuncAtHahn46 root G).coeff 4 +
        (ratFuncAtHahn46 root C).coeff 8 * (ratFuncAtHahn46 root G).coeff 3 +
        (ratFuncAtHahn46 root C).coeff 9 * (ratFuncAtHahn46 root G).coeff 2 +
        (ratFuncAtHahn46 root C).coeff 10 * (ratFuncAtHahn46 root G).coeff 1 +
        (ratFuncAtHahn46 root C).coeff 11 * (ratFuncAtHahn46 root G).coeff 0 +
        (ratFuncAtHahn46 root C).coeff 12 * (ratFuncAtHahn46 root G).coeff (-1 : ℚ) +
        (ratFuncAtHahn46 root F).coeff 3 * (ratFuncAtHahn46 root F).coeff 8 +
        (ratFuncAtHahn46 root F).coeff 4 * (ratFuncAtHahn46 root F).coeff 7 +
        (ratFuncAtHahn46 root F).coeff 5 * (ratFuncAtHahn46 root F).coeff 6) +
      3 * epsilon * (ratFuncAtHahn46 root C).coeff 11 = 0 := by
  let AL : LaurentSeries k := ratFuncAtLaurent46 root A
  let BL : LaurentSeries k := ratFuncAtLaurent46 root B
  let CL : LaurentSeries k := ratFuncAtLaurent46 root C
  let FL : LaurentSeries k := ratFuncAtLaurent46 root F
  let Gser : LaurentSeries k := ratFuncAtLaurent46 root G
  let SR : RatFunc k := 2 * C + RatFunc.C (3 * gamma)
  let SL : LaurentSeries k := 2 * CL + HahnSeries.C (3 * gamma)
  have hAL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root A (-2) hA
  have hBL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root B 11 hB
  have hCL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root C 0 hC
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
  have hSG := laurent_coeff_mul_lower_five68 SL Gser 7 (-1) hSL hGL
  have hFF := laurent_coeff_mul_lower_five68 FL FL 3 3 hFL hFL
  norm_num at hSG hFF
  have hAB : (↑(9 : ℤ) : WithTop ℤ) ≤ (AL * BL).orderTop := by
    have h := le_trans (add_le_add hAL hBL) HahnSeries.orderTop_add_le_mul
    norm_num at h ⊢
    exact h
  have hABF : (↑(12 : ℤ) : WithTop ℤ) ≤ (AL * BL * FL).orderTop := by
    have h := le_trans (add_le_add hAB hFL) HahnSeries.orderTop_add_le_mul
    convert h using 1 <;> norm_num
  have hzABF : (AL * BL * FL).coeff (11 : ℤ) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hABF)
  have hzABF' : (AL * (BL * FL)).coeff (11 : ℤ) = 0 := by
    rw [← mul_assoc]
    exact hzABF
  have hBB : (↑(22 : ℤ) : WithTop ℤ) ≤ (BL * BL).orderTop := by
    have h := le_trans (add_le_add hBL hBL) HahnSeries.orderTop_add_le_mul
    convert h using 1 <;> norm_num
  have hBBC : (↑(22 : ℤ) : WithTop ℤ) ≤ (BL * BL * CL).orderTop :=
    le_trans (add_le_add hBB hCL) HahnSeries.orderTop_add_le_mul
  have hzBBC : (BL * BL * CL).coeff (11 : ℤ) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hBBC)
  have hzBBC' : (BL * (BL * CL)).coeff (11 : ℤ) = 0 := by
    rw [← mul_assoc]
    exact hzBBC
  have hzBB : (BL ^ 2).coeff (11 : ℤ) = 0 := by
    rw [pow_two]
    exact HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hBB)
  have hfactorL := congrArg (ratFuncAtLaurent46 root) hfactor
  have hfactorL' : rhoOneI3CapFactored68
      (HahnSeries.C gamma) (HahnSeries.C epsilon) AL BL CL FL Gser =
        HahnSeries.C i3 := by
    simpa only [rhoOneI3CapFactored68, AL, BL, CL, FL, Gser, map_add,
      map_sub, map_mul, map_pow, map_neg, map_div₀, map_ofNat, map_one,
      ratFuncAtLaurent46_C68] using hfactorL
  have hSLform : 2 * CL + 3 * HahnSeries.C gamma = SL := by
    dsimp only [SL]
    congr 1
    rw [HahnSeries.C_eq_algebraMap, map_mul, map_ofNat]
  rw [rhoOneI3CapFactored68, hSLform] at hfactorL'
  have hc := congrArg (fun X : LaurentSeries k => X.coeff (11 : ℤ)) hfactorL'
  simp only [HahnSeries.coeff_add, HahnSeries.coeff_sub] at hc
  have hscale (s : k) (X : LaurentSeries k) (r : ℤ) :
      (HahnSeries.C s * X).coeff r = s * X.coeff r := by
    rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]
  have hs1 : ((-8 / 9 : LaurentSeries k) * AL * BL * FL).coeff 11 = 0 := by
    have hcst : (-8 / 9 : LaurentSeries k) = HahnSeries.C (-8 / 9 : k) := by
      rw [HahnSeries.C_eq_algebraMap, map_div₀, map_neg, map_ofNat, map_ofNat]
    rw [mul_assoc, mul_assoc, hcst, hscale, hzABF', mul_zero]
  have hs2 : ((8 / 9 : LaurentSeries k) * BL ^ 2 * CL).coeff 11 = 0 := by
    have hcst : (8 / 9 : LaurentSeries k) = HahnSeries.C (8 / 9 : k) := by
      rw [HahnSeries.C_eq_algebraMap, map_div₀, map_ofNat, map_ofNat]
    rw [pow_two, mul_assoc, mul_assoc, hcst, hscale, hzBBC', mul_zero]
  have hs3 : ((4 / 3 : LaurentSeries k) * SL * Gser).coeff 11 =
      (4 / 3 : k) * (SL * Gser).coeff 11 := by
    have hcst : (4 / 3 : LaurentSeries k) = HahnSeries.C (4 / 3 : k) := by
      rw [HahnSeries.C_eq_algebraMap, map_div₀, map_ofNat, map_ofNat]
    rw [mul_assoc, hcst, hscale]
  have hs4 : ((4 / 3 : LaurentSeries k) * FL ^ 2).coeff 11 =
      (4 / 3 : k) * (FL * FL).coeff 11 := by
    have hcst : (4 / 3 : LaurentSeries k) = HahnSeries.C (4 / 3 : k) := by
      rw [HahnSeries.C_eq_algebraMap, map_div₀, map_ofNat, map_ofNat]
    rw [pow_two, hcst, hscale]
  have hs5 : ((2 / 3 : LaurentSeries k) * HahnSeries.C gamma * BL ^ 2).coeff 11 = 0 := by
    have hcst : (2 / 3 : LaurentSeries k) * HahnSeries.C gamma =
        HahnSeries.C ((2 / 3 : k) * gamma) := by
      have h23 : (2 / 3 : LaurentSeries k) = HahnSeries.C (2 / 3 : k) := by
        rw [HahnSeries.C_eq_algebraMap, map_div₀, map_ofNat, map_ofNat]
      rw [h23, ← map_mul]
    rw [hcst, hscale, hzBB, mul_zero]
  have hs6 : ((2 : LaurentSeries k) * HahnSeries.C epsilon * CL).coeff 11 =
      (2 * epsilon) * CL.coeff 11 := by
    have hcst : (2 : LaurentSeries k) * HahnSeries.C epsilon =
        HahnSeries.C (2 * epsilon) := by
      have h2 : (2 : LaurentSeries k) = HahnSeries.C (2 : k) := by
        rw [HahnSeries.C_eq_algebraMap, map_ofNat]
      rw [h2, ← map_mul]
    rw [hcst, hscale]
  have hright : (HahnSeries.C i3 : LaurentSeries k).coeff 11 = 0 := by
    simp [HahnSeries.C_apply]
  rw [hs1, hs2, hs3, hs4, hs5, hs6, hright, hSG, hFF] at hc
  have hSL7 : SL.coeff 7 = 2 * CL.coeff 7 := by
    dsimp only [SL]
    simp [HahnSeries.C_apply, two_mul]
  have hSL8 : SL.coeff 8 = 2 * CL.coeff 8 := by
    dsimp only [SL]
    simp [HahnSeries.C_apply, two_mul]
  have hSL9 : SL.coeff 9 = 2 * CL.coeff 9 := by
    dsimp only [SL]
    simp [HahnSeries.C_apply, two_mul]
  have hSL10 : SL.coeff 10 = 2 * CL.coeff 10 := by
    dsimp only [SL]
    simp [HahnSeries.C_apply, two_mul]
  have hSL11 : SL.coeff 11 = 2 * CL.coeff 11 := by
    dsimp only [SL]
    simp [HahnSeries.C_apply, two_mul]
  have hSL12 : SL.coeff 12 = 2 * CL.coeff 12 := by
    dsimp only [SL]
    simp [HahnSeries.C_apply, two_mul]
  rw [hSL7, hSL8, hSL9, hSL10, hSL11, hSL12] at hc
  have hC7 := ratFuncAtHahn46_coeff_int68 root C 7
  have hC8 := ratFuncAtHahn46_coeff_int68 root C 8
  have hC9 := ratFuncAtHahn46_coeff_int68 root C 9
  have hC10 := ratFuncAtHahn46_coeff_int68 root C 10
  have hC11 := ratFuncAtHahn46_coeff_int68 root C 11
  have hC12 := ratFuncAtHahn46_coeff_int68 root C 12
  have hF3 := ratFuncAtHahn46_coeff_int68 root F 3
  have hF4 := ratFuncAtHahn46_coeff_int68 root F 4
  have hF5 := ratFuncAtHahn46_coeff_int68 root F 5
  have hF6 := ratFuncAtHahn46_coeff_int68 root F 6
  have hF7 := ratFuncAtHahn46_coeff_int68 root F 7
  have hF8 := ratFuncAtHahn46_coeff_int68 root F 8
  have hGm1 := ratFuncAtHahn46_coeff_int68 root G (-1)
  have hG0 := ratFuncAtHahn46_coeff_int68 root G 0
  have hG1 := ratFuncAtHahn46_coeff_int68 root G 1
  have hG2 := ratFuncAtHahn46_coeff_int68 root G 2
  have hG3 := ratFuncAtHahn46_coeff_int68 root G 3
  have hG4 := ratFuncAtHahn46_coeff_int68 root G 4
  norm_num at hC7 hC8 hC9 hC10 hC11 hC12 hF3 hF4 hF5 hF6 hF7 hF8 hGm1 hG0 hG1 hG2 hG3 hG4
  dsimp only [CL, FL, Gser] at hc
  rw [← hC7, ← hC8, ← hC9, ← hC10, ← hC11, ← hC12, ← hF3, ← hF4,
    ← hF5, ← hF6, ← hF7, ← hF8, ← hGm1, ← hG0, ← hG1,
    ← hG2, ← hG3, ← hG4] at hc
  linear_combination (3 / 2 : k) * hc

def rhoOneI3CapElevenCore68 (C F G : HahnSeries ℚ k) : k :=
  C.coeff 7 * G.coeff 4 + C.coeff 8 * G.coeff 3 +
    C.coeff 9 * G.coeff 2 + C.coeff 10 * G.coeff 1 +
    C.coeff 11 * G.coeff 0 + C.coeff 12 * G.coeff (-1 : ℚ) +
    F.coeff 3 * F.coeff 8 + F.coeff 4 * F.coeff 7 +
    F.coeff 5 * F.coeff 6

def RhoOneDoubleZeroTerminalGBoundaryCapI3ElevenPacket68
    (gamma epsilon i3 sold cs source0 source1 source2 : k)
    (A B C F G dA : HahnSeries ℚ k) : Prop :=
  RhoOneDoubleZeroTerminalGBoundaryCapFourthTransportPacket68
      gamma epsilon i3 sold cs source0 source1 source2 A B C F G dA ∧
    4 * rhoOneI3CapElevenCore68 C F G + 3 * epsilon * C.coeff 11 = 0

end AlignedSquareTerminalGBoundaryCapI3Eleven68

end Max11DegreeRoutes
