import Sol68ScaleTwoAlignedSquareTerminalGBoundaryCapCI3InductionScratch

/-! # The first integral jets above the nonzero `C₇/B₁₁` cap -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareTerminalGBoundaryCapNextJet68

variable {k : Type*} [Field k] [CharZero k]

local instance alignedSquareTerminalGBoundaryCapNextJetHahnCharZero68 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-- The two cap rows already normalize the two surviving top scalars. -/
theorem rhoOneI3I4_coordinate_cap_scalar68
    (b c f g : k) (hf : f ≠ 0)
    (hi3 : 2 * c * g + f ^ 2 = 0)
    (hi4 : b * g + c * f = 0) :
    b * f = 2 * c ^ 2 := by
  have hprod : f * (2 * c ^ 2 - b * f) = 0 := by
    calc
      f * (2 * c ^ 2 - b * f) =
          2 * c * (b * g + c * f) - b * (2 * c * g + f ^ 2) := by ring
      _ = 0 := by rw [hi3, hi4]; ring
  exact (sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left hf)).symm

/-- Coefficient seven of the global third first integral at the cap. -/
theorem rhoOneI3CapFactored_cap_coeff_seven68
    (root gamma epsilon i3 : k) (A B C F G : RatFunc k)
    (hA : (↑(-2 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 root A).orderTop)
    (hB : (↑(11 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 root B).orderTop)
    (hC : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 root C).orderTop)
    (hF : (↑(3 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 root F).orderTop)
    (hG : (↑(-1 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 root G).orderTop)
    (hS : (↑(7 : ℚ) : WithTop ℚ) ≤
      (2 * ratFuncAtHahn46 root C + HahnSeries.C (3 * gamma)).orderTop)
    (hfactor : rhoOneI3CapFactored68 (RatFunc.C gamma)
      (RatFunc.C epsilon) A B C F G = RatFunc.C i3) :
    4 * ((ratFuncAtHahn46 root C).coeff (7 : ℚ) *
          (ratFuncAtHahn46 root G).coeff (0 : ℚ) +
        (ratFuncAtHahn46 root C).coeff (8 : ℚ) *
          (ratFuncAtHahn46 root G).coeff (-1 : ℚ) +
        (ratFuncAtHahn46 root F).coeff (3 : ℚ) *
          (ratFuncAtHahn46 root F).coeff (4 : ℚ)) +
      3 * epsilon * (ratFuncAtHahn46 root C).coeff (7 : ℚ) = 0 := by
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
  have hSG := laurent_coeff_mul_lower_succ68 SL Gser 7 (-1) hSL hGL
  have hFF := laurent_coeff_mul_lower_succ68 FL FL 3 3 hFL hFL
  norm_num at hSG hFF
  have hAB : (↑(9 : ℤ) : WithTop ℤ) ≤ (AL * BL).orderTop := by
    have h := le_trans (add_le_add hAL hBL) HahnSeries.orderTop_add_le_mul
    norm_num at h ⊢
    exact h
  have hABF : (↑(12 : ℤ) : WithTop ℤ) ≤ (AL * BL * FL).orderTop := by
    have h := le_trans (add_le_add hAB hFL) HahnSeries.orderTop_add_le_mul
    convert h using 1 <;> norm_num
  have hzABF : (AL * BL * FL).coeff (7 : ℤ) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hABF)
  have hzABF' : (AL * (BL * FL)).coeff (7 : ℤ) = 0 := by
    rw [← mul_assoc]
    exact hzABF
  have hBB : (↑(22 : ℤ) : WithTop ℤ) ≤ (BL * BL).orderTop := by
    have h := le_trans (add_le_add hBL hBL) HahnSeries.orderTop_add_le_mul
    convert h using 1 <;> norm_num
  have hBBC : (↑(22 : ℤ) : WithTop ℤ) ≤ (BL * BL * CL).orderTop := by
    have h := le_trans (add_le_add hBB hCL) HahnSeries.orderTop_add_le_mul
    convert h using 1 <;> norm_num
  have hzBBC : (BL * BL * CL).coeff (7 : ℤ) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hBBC)
  have hzBBC' : (BL * (BL * CL)).coeff (7 : ℤ) = 0 := by
    rw [← mul_assoc]
    exact hzBBC
  have hzBB : (BL ^ 2).coeff (7 : ℤ) = 0 := by
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
  have hc := congrArg (fun X : LaurentSeries k => X.coeff (7 : ℤ)) hfactorL'
  simp only [HahnSeries.coeff_add, HahnSeries.coeff_sub] at hc
  have hscale (s : k) (X : LaurentSeries k) (r : ℤ) :
      (HahnSeries.C s * X).coeff r = s * X.coeff r := by
    rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]
  have hs1 :
      ((-8 / 9 : LaurentSeries k) * AL * BL * FL).coeff 7 = 0 := by
    have hcst : (-8 / 9 : LaurentSeries k) = HahnSeries.C (-8 / 9 : k) := by
      rw [HahnSeries.C_eq_algebraMap, map_div₀, map_neg, map_ofNat, map_ofNat]
    rw [mul_assoc, mul_assoc, hcst, hscale, hzABF', mul_zero]
  have hs2 :
      ((8 / 9 : LaurentSeries k) * BL ^ 2 * CL).coeff 7 = 0 := by
    have hcst : (8 / 9 : LaurentSeries k) = HahnSeries.C (8 / 9 : k) := by
      rw [HahnSeries.C_eq_algebraMap, map_div₀, map_ofNat, map_ofNat]
    rw [pow_two, mul_assoc, mul_assoc, hcst, hscale, hzBBC', mul_zero]
  have hs3 :
      ((4 / 3 : LaurentSeries k) * SL * Gser).coeff 7 =
        (4 / 3 : k) * (SL * Gser).coeff 7 := by
    have hcst : (4 / 3 : LaurentSeries k) = HahnSeries.C (4 / 3 : k) := by
      rw [HahnSeries.C_eq_algebraMap, map_div₀, map_ofNat, map_ofNat]
    rw [mul_assoc, hcst, hscale]
  have hs4 :
      ((4 / 3 : LaurentSeries k) * FL ^ 2).coeff 7 =
        (4 / 3 : k) * (FL * FL).coeff 7 := by
    have hcst : (4 / 3 : LaurentSeries k) = HahnSeries.C (4 / 3 : k) := by
      rw [HahnSeries.C_eq_algebraMap, map_div₀, map_ofNat, map_ofNat]
    rw [pow_two, hcst, hscale]
  have hs5 :
      ((2 / 3 : LaurentSeries k) * HahnSeries.C gamma * BL ^ 2).coeff 7 = 0 := by
    have hcst : (2 / 3 : LaurentSeries k) * HahnSeries.C gamma =
        HahnSeries.C ((2 / 3 : k) * gamma) := by
      have h23 : (2 / 3 : LaurentSeries k) =
          HahnSeries.C (2 / 3 : k) := by
        rw [HahnSeries.C_eq_algebraMap, map_div₀, map_ofNat, map_ofNat]
      rw [h23, ← map_mul]
    rw [hcst, hscale, hzBB, mul_zero]
  have hs6 :
      ((2 : LaurentSeries k) * HahnSeries.C epsilon * CL).coeff 7 =
        (2 * epsilon) * CL.coeff 7 := by
    have hcst : (2 : LaurentSeries k) * HahnSeries.C epsilon =
        HahnSeries.C (2 * epsilon) := by
      have h2 : (2 : LaurentSeries k) = HahnSeries.C (2 : k) := by
        rw [HahnSeries.C_eq_algebraMap, map_ofNat]
      rw [h2, ← map_mul]
    rw [hcst, hscale]
  have hright : (HahnSeries.C i3 : LaurentSeries k).coeff 7 = 0 := by
    simp [HahnSeries.C_apply]
  rw [hs1, hs2, hs3, hs4, hs5, hs6, hright, hSG, hFF] at hc
  have hSL7 : SL.coeff 7 = 2 * CL.coeff 7 := by
    dsimp only [SL]
    simp [HahnSeries.C_apply, two_mul]
  have hSL8 : SL.coeff 8 = 2 * CL.coeff 8 := by
    dsimp only [SL]
    simp [HahnSeries.C_apply, two_mul]
  rw [hSL7, hSL8] at hc
  have hC7 := ratFuncAtHahn46_coeff_int68 root C 7
  have hC8 := ratFuncAtHahn46_coeff_int68 root C 8
  have hF3 := ratFuncAtHahn46_coeff_int68 root F 3
  have hF4 := ratFuncAtHahn46_coeff_int68 root F 4
  have hGm1 := ratFuncAtHahn46_coeff_int68 root G (-1)
  have hG0 := ratFuncAtHahn46_coeff_int68 root G 0
  norm_num at hC7 hC8 hF3 hF4 hGm1 hG0
  dsimp only [CL, FL, Gser] at hc
  rw [← hC7, ← hC8, ← hF3, ← hF4, ← hGm1, ← hG0] at hc
  linear_combination (3 / 2 : k) * hc

/-- Coefficient eleven of the global fourth first integral at the cap. -/
theorem rhoOneI4ZeroFactored_cap_coeff_eleven68
    (root gamma epsilon : k) (B C F G : RatFunc k)
    (hB : (↑(11 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 root B).orderTop)
    (hF : (↑(3 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 root F).orderTop)
    (hG : (↑(-1 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 root G).orderTop)
    (hS : (↑(7 : ℚ) : WithTop ℚ) ≤
      (2 * ratFuncAtHahn46 root C + HahnSeries.C (3 * gamma)).orderTop)
    (hfactor : rhoOneI4ZeroFactored68
      (RatFunc.C gamma) (RatFunc.C epsilon) B C F G = 0) :
    4 * ((ratFuncAtHahn46 root B).coeff (11 : ℚ) *
          (ratFuncAtHahn46 root G).coeff (0 : ℚ) +
        (ratFuncAtHahn46 root B).coeff (12 : ℚ) *
          (ratFuncAtHahn46 root G).coeff (-1 : ℚ)) +
      4 * ((ratFuncAtHahn46 root C).coeff (7 : ℚ) *
          (ratFuncAtHahn46 root F).coeff (4 : ℚ) +
        (ratFuncAtHahn46 root C).coeff (8 : ℚ) *
          (ratFuncAtHahn46 root F).coeff (3 : ℚ)) +
      3 * epsilon * (ratFuncAtHahn46 root B).coeff (11 : ℚ) = 0 := by
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
  have hBG := laurent_coeff_mul_lower_succ68 BL Gser 11 (-1) hBL hGL
  have hSF := laurent_coeff_mul_lower_succ68 SL FL 7 3 hSL hFL
  norm_num at hBG hSF
  have hBcubeOrder : (↑(33 : ℤ) : WithTop ℤ) ≤ (BL ^ 3).orderTop := by
    have hp := HahnSeries.orderTop_nsmul_le_orderTop_pow
      (x := BL) (n := 3)
    have htriple := nsmul_le_nsmul_right hBL 3
    norm_num at htriple
    exact le_trans htriple hp
  have hBcube : (BL ^ 3).coeff (11 : ℤ) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hBcubeOrder)
  have hfactorL := congrArg (ratFuncAtLaurent46 root) hfactor
  have hfactorL' : rhoOneI4ZeroFactored68
      (HahnSeries.C gamma) (HahnSeries.C epsilon) BL CL FL Gser = 0 := by
    simpa only [rhoOneI4ZeroFactored68, BL, CL, FL, Gser, map_add, map_mul,
      map_pow, map_neg, map_div₀, map_ofNat, map_zero, map_one,
      ratFuncAtLaurent46_C68] using hfactorL
  have hSLform : 2 * CL + 3 * HahnSeries.C gamma = SL := by
    dsimp only [SL]
    congr 1
    rw [HahnSeries.C_eq_algebraMap, map_mul, map_ofNat]
  rw [rhoOneI4ZeroFactored68, hSLform] at hfactorL'
  have hc := congrArg (fun X : LaurentSeries k => X.coeff (11 : ℤ))
    hfactorL'
  simp only [HahnSeries.coeff_add, HahnSeries.coeff_zero] at hc
  have hscale (s : k) (X : LaurentSeries k) (r : ℤ) :
      (HahnSeries.C s * X).coeff r = s * X.coeff r := by
    rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]
  have hc827 : (-8 / 27 : LaurentSeries k) =
      HahnSeries.C (-8 / 27 : k) := by
    rw [HahnSeries.C_eq_algebraMap, map_div₀, map_neg, map_ofNat, map_ofNat]
  have hc83 : (8 / 3 : LaurentSeries k) = HahnSeries.C (8 / 3 : k) := by
    rw [HahnSeries.C_eq_algebraMap, map_div₀, map_ofNat, map_ofNat]
  have hc43 : (4 / 3 : LaurentSeries k) = HahnSeries.C (4 / 3 : k) := by
    rw [HahnSeries.C_eq_algebraMap, map_div₀, map_ofNat, map_ofNat]
  have hc2 : (2 : LaurentSeries k) = HahnSeries.C (2 : k) := by
    rw [HahnSeries.C_eq_algebraMap, map_ofNat]
  have hsc1 :
      ((-8 / 27 : LaurentSeries k) * BL ^ 3).coeff 11 =
        (-8 / 27 : k) * (BL ^ 3).coeff 11 := by
    rw [hc827, hscale]
  have hsc2 :
      ((8 / 3 : LaurentSeries k) * BL * Gser).coeff 11 =
        (8 / 3 : k) * (BL * Gser).coeff 11 := by
    rw [mul_assoc, hc83, hscale]
  have hsc3 :
      ((4 / 3 : LaurentSeries k) * SL * FL).coeff 11 =
        (4 / 3 : k) * (SL * FL).coeff 11 := by
    rw [mul_assoc, hc43, hscale]
  have hsc4 :
      ((2 : LaurentSeries k) * HahnSeries.C epsilon * BL).coeff 11 =
        (2 * epsilon) * BL.coeff 11 := by
    rw [hc2, ← map_mul, hscale]
  rw [hsc1, hsc2, hsc3, hsc4] at hc
  have hSL7 : SL.coeff 7 = 2 * CL.coeff 7 := by
    dsimp only [SL]
    simp [HahnSeries.C_apply, two_mul]
  have hSL8 : SL.coeff 8 = 2 * CL.coeff 8 := by
    dsimp only [SL]
    simp [HahnSeries.C_apply, two_mul]
  rw [hBcube, hBG, hSF, hSL7, hSL8] at hc
  have hB11 := ratFuncAtHahn46_coeff_int68 root B 11
  have hB12 := ratFuncAtHahn46_coeff_int68 root B 12
  have hC7 := ratFuncAtHahn46_coeff_int68 root C 7
  have hC8 := ratFuncAtHahn46_coeff_int68 root C 8
  have hF3 := ratFuncAtHahn46_coeff_int68 root F 3
  have hF4 := ratFuncAtHahn46_coeff_int68 root F 4
  have hGm1 := ratFuncAtHahn46_coeff_int68 root G (-1)
  have hG0 := ratFuncAtHahn46_coeff_int68 root G 0
  norm_num at hB11 hB12 hC7 hC8 hF3 hF4 hGm1 hG0
  dsimp only [BL, CL, FL, Gser] at hc
  rw [← hB11, ← hB12, ← hC7, ← hC8, ← hF3, ← hF4,
    ← hGm1, ← hG0] at hc
  linear_combination (3 / 2 : k) * hc

/-- Eliminating the shared `G[0]`, `F[4]`, epsilon terms from the two next
jets leaves a scale-free transport equation. -/
theorem rhoOneI3I4_coordinate_cap_next_transport68
    (b b' c c' f f' g g' epsilon : k) (hc : c ≠ 0)
    (hscalar : b * f = 2 * c ^ 2)
    (hcap : b * g + c * f = 0)
    (hi3 : 4 * (c * g' + c' * g + f * f') + 3 * epsilon * c = 0)
    (hi4 : 4 * (b * g' + b' * g) + 4 * (c * f' + c' * f) +
      3 * epsilon * b = 0) :
    c * f' - b' * g - 2 * c' * f = 0 := by
  have hprod : 4 * c * (c * f' - b' * g - 2 * c' * f) = 0 := by
    linear_combination b * hi3 - c * hi4 - 4 * c' * hcap -
      4 * f' * (hscalar)
  have hfour : (4 : k) ≠ 0 := by norm_num
  rcases mul_eq_zero.mp hprod with h4c | hgoal
  · exact (hc ((mul_eq_zero.mp h4c).resolve_left hfour)).elim
  · exact hgoal

/-- The honest first-jet classification above the nonzero cap. -/
def RhoOneDoubleZeroTerminalGBoundaryCapNextJetPacket68
    (gamma epsilon i3 : k) (A B C F G : HahnSeries ℚ k) : Prop :=
  RhoOneDoubleZeroTerminalGBoundaryCI3CapPacket68
      gamma epsilon i3 A B C F G ∧
    B.coeff (11 : ℚ) * F.coeff (3 : ℚ) =
      2 * C.coeff (7 : ℚ) ^ 2 ∧
    4 * (C.coeff (7 : ℚ) * G.coeff (0 : ℚ) +
          C.coeff (8 : ℚ) * G.coeff (-1 : ℚ) +
          F.coeff (3 : ℚ) * F.coeff (4 : ℚ)) +
        3 * epsilon * C.coeff (7 : ℚ) = 0 ∧
    4 * (B.coeff (11 : ℚ) * G.coeff (0 : ℚ) +
          B.coeff (12 : ℚ) * G.coeff (-1 : ℚ)) +
        4 * (C.coeff (7 : ℚ) * F.coeff (4 : ℚ) +
          C.coeff (8 : ℚ) * F.coeff (3 : ℚ)) +
        3 * epsilon * B.coeff (11 : ℚ) = 0 ∧
    C.coeff (7 : ℚ) * F.coeff (4 : ℚ) -
      B.coeff (12 : ℚ) * G.coeff (-1 : ℚ) -
      2 * C.coeff (8 : ℚ) * F.coeff (3 : ℚ) = 0

/-- Source residual refined only on the `C[1]=C[2]=0` cap child. -/
def RhoOneDoubleZeroTerminalGBoundaryCapNextJetResidual68
    (root j gamma epsilon : k) (h0R BR CR FR GR : RatFunc k)
    (A B C F G : HahnSeries ℚ k) : Prop :=
  RhoOneDoubleZeroTerminalGBoundaryCapCI3InductionResidual68
      root j gamma epsilon h0R BR CR FR GR A B C F G ∧
    ((B.coeff (1 : ℚ) = 0 ∧
        2 * C.coeff (0 : ℚ) + 3 * gamma = 0) →
      C.coeff (1 : ℚ) = 0 → C.coeff (2 : ℚ) = 0 →
      ∃ i3 : k, RhoOneDoubleZeroTerminalGBoundaryCapNextJetPacket68
        gamma epsilon i3 A B C F G)

/-- Literal source backwire of the two first-integral jets above the cap. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_exceptional_doubleZero_refinedGZero_terminalGBoundaryCapNextJetResidual
    [IsAlgClosed k]
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (P : RhoOneZeroLCubicNextSourcePacket68 T g u)
    (hB : (↑(1 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root T.source.B).orderTop)
    (hC : (0 : WithTop ℚ) ≤
      (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0)).orderTop)
    (hF : (0 : WithTop ℚ) ≤
      (rhoOneTangentDDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.B)
        (ratFuncAtHahn46 T.root T.source.D)).orderTop)
    (hG : (↑(-1 : ℚ) : WithTop ℚ) ≤
      (rhoOneTangentEDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0))
        (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.E))).orderTop)
    (hbeta : T.source.beta = 0) (hdelta : T.source.delta = 0)
    (hzeta : T.source.zeta = 0) :
    let AR : RatFunc k := T.source.A
    let BR : RatFunc k := T.source.B
    let CR : RatFunc k := T.source.C0 - RatFunc.C (1 / 3 : k) * AR ^ 2
    let FR : RatFunc k := T.source.D - RatFunc.C (1 / 3 : k) * AR * BR
    let GR : RatFunc k :=
      (T.source.E - RatFunc.C (1 / 27 : k) * AR ^ 3) -
        RatFunc.C (1 / 3 : k) * AR * CR
    let A := ratFuncAtHahn46 T.root T.source.A
    let B := ratFuncAtHahn46 T.root T.source.B
    let C := rhoOneCDefectHahn68 A
      (ratFuncAtHahn46 T.root T.source.C0)
    let F := rhoOneTangentDDefectHahn68 A B
      (ratFuncAtHahn46 T.root T.source.D)
    let G := rhoOneTangentEDefectHahn68 A C
      (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
    RhoOneDoubleZeroTerminalGBoundaryCapNextJetResidual68
        T.root j T.source.gamma T.source.epsilon
        (algebraMap k[X] (RatFunc k) h0) BR CR FR GR A B C F G ∨
      (G.coeff (-1 : ℚ) = 0 ∧ (0 : WithTop ℚ) ≤ G.orderTop ∧
        (RhoOneDoubleZeroRefinedGZeroTerminalBGainChild68
            T.source.gamma B C F ∨
         RhoOneDoubleZeroRefinedGZeroTerminalFGainChild68
            T.source.gamma B C F)) := by
  dsimp only [RhoOneDoubleZeroTerminalGBoundaryCapNextJetResidual68]
  have hnext := T.rhoOne_exceptional_doubleZero_refined_gZero
    P hB hC hF hG hbeta hdelta hzeta
  dsimp only at hnext
  rcases hnext with ⟨_, _, _, _, _, _, hsplit⟩
  rcases hsplit with hGne | ⟨hGzero, hG0, htail⟩
  · have hprev :=
      T.rhoOne_exceptional_doubleZero_refinedGZero_terminalGBoundaryCapCI3InductionResidual
        hp hH hp6 hp5 hp4 P hB hC hF hG hbeta hdelta hzeta
    rcases hprev with hcapResidual | hbad
    · left
      refine ⟨hcapResidual, ?_⟩
      intro hcoord hc1 hc2
      obtain ⟨i3, hpacket⟩ := hcapResidual.2 hcoord hc1 hc2
      have hpacket' := hpacket
      dsimp only [RhoOneDoubleZeroTerminalGBoundaryCI3CapPacket68] at hpacket'
      rcases hpacket' with ⟨hi3H, hc3, hc4, hc5, hc6, hb7, hb8, hb9,
        hb10, hS7, hB11, hcap3, hc7ne, hcap4, hb11ne, hBexact⟩
      have hfinite := hcapResidual.1.1.1
      dsimp only [RhoOneDoubleZeroTerminalGBoundaryFiniteResidual68] at hfinite
      rcases hfinite with ⟨hfact, hboundary | hrays⟩
      · rcases hboundary with ⟨hcurrent, hf2, hF3, hb4, hB5,
          hi4three, hf3ne⟩
        let AR : RatFunc k := T.source.A
        let BR : RatFunc k := T.source.B
        let CR : RatFunc k :=
          T.source.C0 - RatFunc.C (1 / 3 : k) * AR ^ 2
        let FR : RatFunc k :=
          T.source.D - RatFunc.C (1 / 3 : k) * AR * BR
        let GR : RatFunc k :=
          (T.source.E - RatFunc.C (1 / 27 : k) * AR ^ 3) -
            RatFunc.C (1 / 3 : k) * AR * CR
        have hCRmap : ratFuncAtHahn46 T.root CR =
            rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.C0) := by
          dsimp only [CR, AR, rhoOneCDefectHahn68]
          simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
        have hFRmap : ratFuncAtHahn46 T.root FR =
            rhoOneTangentDDefectHahn68
              (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.B)
              (ratFuncAtHahn46 T.root T.source.D) := by
          dsimp only [FR, AR, BR, rhoOneTangentDDefectHahn68]
          simp only [map_sub, map_mul, ratFuncAtHahn46_C]
        have hGRmap : ratFuncAtHahn46 T.root GR =
            rhoOneTangentEDefectHahn68
              (ratFuncAtHahn46 T.root T.source.A)
              (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                (ratFuncAtHahn46 T.root T.source.C0))
              (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                (ratFuncAtHahn46 T.root T.source.E)) := by
          dsimp only [GR, CR, AR, rhoOneTangentEDefectHahn68,
            rhoOneCDefectHahn68, rhoOneEDefectHahn68]
          simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
        have hbounds := P.2.1
        dsimp only [RhoOneZeroLCubicImprovedHahnBounds68] at hbounds
        have hAH : (↑(-2 : ℚ) : WithTop ℚ) ≤
            (ratFuncAtHahn46 T.root AR).orderTop := by
          simpa only [AR] using hbounds.1
        have hi3R : rhoOneI3CapFactored68
            (RatFunc.C T.source.gamma) (RatFunc.C T.source.epsilon)
            AR BR CR FR GR = RatFunc.C i3 := by
          apply ratFuncAtHahn46_injective T.root
          simpa only [rhoOneI3CapFactored68, map_add, map_sub, map_mul,
            map_pow, map_neg, map_div₀, map_ofNat, map_one,
            ratFuncAtHahn46_C, hCRmap, hFRmap, hGRmap, AR, BR] using hi3H
        change rhoOneI4ZeroFactored68
          (RatFunc.C T.source.gamma) (RatFunc.C T.source.epsilon)
          BR CR FR GR = 0 at hfact
        have hrow3raw := rhoOneI3CapFactored_cap_coeff_seven68
          T.root T.source.gamma T.source.epsilon i3 AR BR CR FR GR
          hAH (by simpa only [BR] using hB11)
          (by rw [hCRmap]; exact hC) (by rw [hFRmap]; exact hF3)
          (by rw [hGRmap]; exact hG) (by rw [hCRmap]; exact hS7) hi3R
        have hrow4raw := rhoOneI4ZeroFactored_cap_coeff_eleven68
          T.root T.source.gamma T.source.epsilon BR CR FR GR
          (by simpa only [BR] using hB11) (by rw [hFRmap]; exact hF3)
          (by rw [hGRmap]; exact hG) (by rw [hCRmap]; exact hS7) hfact
        rw [hCRmap, hFRmap, hGRmap] at hrow3raw hrow4raw
        have hrow3 := by simpa only [AR, BR] using hrow3raw
        have hrow4 := by simpa only [AR, BR] using hrow4raw
        have hscalar := rhoOneI3I4_coordinate_cap_scalar68
          ((ratFuncAtHahn46 T.root T.source.B).coeff (11 : ℚ))
          ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.C0)).coeff (7 : ℚ))
          ((rhoOneTangentDDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.B)
            (ratFuncAtHahn46 T.root T.source.D)).coeff (3 : ℚ))
          ((rhoOneTangentEDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.C0))
            (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.E))).coeff (-1 : ℚ))
          hf3ne hcap3 hcap4
        have htransport := rhoOneI3I4_coordinate_cap_next_transport68
          ((ratFuncAtHahn46 T.root T.source.B).coeff (11 : ℚ))
          ((ratFuncAtHahn46 T.root T.source.B).coeff (12 : ℚ))
          ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.C0)).coeff (7 : ℚ))
          ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.C0)).coeff (8 : ℚ))
          ((rhoOneTangentDDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.B)
            (ratFuncAtHahn46 T.root T.source.D)).coeff (3 : ℚ))
          ((rhoOneTangentDDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.B)
            (ratFuncAtHahn46 T.root T.source.D)).coeff (4 : ℚ))
          ((rhoOneTangentEDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.C0))
            (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.E))).coeff (-1 : ℚ))
          ((rhoOneTangentEDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.C0))
            (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.E))).coeff (0 : ℚ))
          T.source.epsilon hc7ne hscalar hcap4 hrow3 hrow4
        refine ⟨i3, ?_⟩
        dsimp only [RhoOneDoubleZeroTerminalGBoundaryCapNextJetPacket68]
        exact ⟨hpacket, hscalar, hrow3, hrow4, htransport⟩
      · exact (hrays.1 hcoord.1).elim
    · exact (hGne hbad.1).elim
  · right
    refine ⟨hGzero, hG0, ?_⟩
    have hres :=
      T.rhoOne_exceptional_doubleZero_refinedGZero_terminalBGainResidual
        hp hH hp6 hp5 hp4 P hB hC hF hG hbeta hdelta hzeta
    dsimp only [RhoOneDoubleZeroRefinedGZeroTerminalBGainResidual68] at hres
    rcases hres with hbad | ⟨_, _, htail'⟩
    · exact (hbad hGzero).elim
    · exact htail'

end AlignedSquareTerminalGBoundaryCapNextJet68

end Max11DegreeRoutes
