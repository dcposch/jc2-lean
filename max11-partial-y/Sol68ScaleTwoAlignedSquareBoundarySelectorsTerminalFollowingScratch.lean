import Sol68ScaleTwoAlignedSquareBoundarySelectorsTerminalNextScratch

/-! # Selective next rows on the aligned-square boundary residuals -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareBoundarySelectorsTerminalFollowing68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

local instance boundarySelectorsTerminalFollowingLaurentCharZero68 :
    CharZero (LaurentSeries k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℤ))

omit [IsAlgClosed k] in
/-- Coefficient one of `I4` on the `F[-1]` limb. -/
theorem rhoOne_boundaryF_i4one_laurent68
    (gamma epsilon i4 : k) (B C F G : LaurentSeries k)
    (hB : (↑(1 : ℤ) : WithTop ℤ) ≤ B.orderTop)
    (hC : (0 : WithTop ℤ) ≤ C.orderTop)
    (hF : (↑(-1 : ℤ) : WithTop ℤ) ≤ F.orderTop)
    (hG : (↑(-1 : ℤ) : WithTop ℤ) ≤ G.orderTop)
    (hS0 : 2 * C.coeff 0 + 3 * gamma = 0)
    (hi4 : rhoOneI4ZeroFactored68 (HahnSeries.C gamma)
      (HahnSeries.C epsilon) B C F G = HahnSeries.C i4) :
    B.coeff 1 * G.coeff 0 + B.coeff 2 * G.coeff (-1) +
      C.coeff 1 * F.coeff 0 + C.coeff 2 * F.coeff (-1) +
      (3 / 4 : k) * epsilon * B.coeff 1 = 0 := by
  let S : LaurentSeries k := 2 * C + HahnSeries.C (3 * gamma)
  have hSbase : (0 : WithTop ℤ) ≤ S.orderTop := by
    dsimp only [S]
    apply (le_min ?_ ?_).trans HahnSeries.min_orderTop_le_orderTop_add
    · rw [two_mul]
      exact (le_min hC hC).trans HahnSeries.min_orderTop_le_orderTop_add
    · by_cases hx : 3 * gamma = 0
      · rw [hx, HahnSeries.C_zero]
        simp
      · rw [HahnSeries.C_apply, HahnSeries.orderTop_single hx]
        simp
  have hSco0 : S.coeff 0 = 0 := by
    dsimp only [S]
    rw [HahnSeries.coeff_add]
    simp only [two_mul, HahnSeries.coeff_add, HahnSeries.C_apply,
      HahnSeries.coeff_single_same]
    linear_combination hS0
  have hS := laurent_orderTop_ge_succ_of_coeff_zero68 S 0 hSbase hSco0
  have hSco (n : ℤ) (hn : n ≠ 0) : S.coeff n = 2 * C.coeff n := by
    dsimp only [S]
    rw [HahnSeries.coeff_add]
    simp only [two_mul, HahnSeries.coeff_add, HahnSeries.C_apply,
      HahnSeries.coeff_single]
    rw [if_neg hn]
    ring
  have hBG := laurent_coeff_mul_lower_succ68 B G 1 (-1) hB hG
  have hSF := laurent_coeff_mul_lower_succ68 S F 1 (-1) hS hF
  norm_num at hBG hSF
  rw [hSco 1 (by norm_num), hSco 2 (by norm_num)] at hSF
  have hBB : (↑(2 : ℤ) : WithTop ℤ) ≤ (B * B).orderTop := by
    apply le_trans _ HahnSeries.orderTop_add_le_mul
    have ht := add_le_add hB hB
    norm_num at ht ⊢
    exact ht
  have hB3ord : (↑(3 : ℤ) : WithTop ℤ) ≤ (B ^ 3).orderTop := by
    rw [pow_succ, pow_two]
    apply le_trans _ HahnSeries.orderTop_add_le_mul
    have ht := add_le_add hBB hB
    norm_num at ht ⊢
    exact ht
  have hB3z : (B ^ 3).coeff 1 = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hB3ord)
  have hi4rhs : (HahnSeries.C i4 : LaurentSeries k).coeff 1 = 0 := by
    simp [HahnSeries.C_apply]
  have hscale (s : k) (X : LaurentSeries k) (n : ℤ) :
      (HahnSeries.C s * X).coeff n = s * X.coeff n := by
    rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]
  have hi4rewrite : rhoOneI4ZeroFactored68 (HahnSeries.C gamma)
      (HahnSeries.C epsilon) B C F G =
      HahnSeries.C (-(8 / 27 : k)) * (B ^ 3) +
        HahnSeries.C (8 / 3 : k) * (B * G) +
        HahnSeries.C (4 / 3 : k) * (S * F) +
        HahnSeries.C (2 * epsilon) * B := by
    simp only [rhoOneI4ZeroFactored68, S, HahnSeries.C_eq_algebraMap,
      map_mul, map_add, map_neg, map_div₀, map_ofNat, map_one]
    ring
  have hi4c := congrArg (fun X : LaurentSeries k => X.coeff 1) hi4
  rw [hi4rewrite] at hi4c
  simp only [HahnSeries.coeff_add, hscale] at hi4c
  rw [hB3z, hBG, hSF, hi4rhs] at hi4c
  linear_combination (3 / 8 : k) * hi4c

omit [IsAlgClosed k] in
theorem ratFunc_boundaryF_i4one68
    (root gamma epsilon i4 : k) (B C F G : RatFunc k)
    (hB : (↑(1 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root B).orderTop)
    (hC : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 root C).orderTop)
    (hF : (↑(-1 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root F).orderTop)
    (hG : (↑(-1 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root G).orderTop)
    (hS0 : 2 * (ratFuncAtHahn46 root C).coeff 0 + 3 * gamma = 0)
    (hi4 : rhoOneI4ZeroFactored68 (RatFunc.C gamma)
      (RatFunc.C epsilon) B C F G = RatFunc.C i4) :
    (ratFuncAtHahn46 root B).coeff 1 * (ratFuncAtHahn46 root G).coeff 0 +
      (ratFuncAtHahn46 root B).coeff 2 * (ratFuncAtHahn46 root G).coeff (-1) +
      (ratFuncAtHahn46 root C).coeff 1 * (ratFuncAtHahn46 root F).coeff 0 +
      (ratFuncAtHahn46 root C).coeff 2 * (ratFuncAtHahn46 root F).coeff (-1) +
      (3 / 4 : k) * epsilon * (ratFuncAtHahn46 root B).coeff 1 = 0 := by
  let BL := ratFuncAtLaurent46 root B
  let CL := ratFuncAtLaurent46 root C
  let FL := ratFuncAtLaurent46 root F
  let GLa := ratFuncAtLaurent46 root G
  have hBL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root B 1 hB
  have hCL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root C 0 hC
  have hFL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root F (-1) hF
  have hGL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root G (-1) hG
  have hi4L := congrArg (ratFuncAtLaurent46 root) hi4
  have hi4L' : rhoOneI4ZeroFactored68 (HahnSeries.C gamma)
      (HahnSeries.C epsilon) BL CL FL GLa = HahnSeries.C i4 := by
    simpa only [BL, CL, FL, GLa, rhoOneI4ZeroFactored68,
      map_add, map_mul, map_pow, map_neg, map_div₀, map_ofNat,
      ratFuncAtLaurent46_C68] using hi4L
  have hcs (R : RatFunc k) (n : ℤ) := ratFuncAtHahn46_coeff_int68 root R n
  have hS0L : 2 * CL.coeff 0 + 3 * gamma = 0 := by
    rw [← hcs C 0]
    exact hS0
  have hf := rhoOne_boundaryF_i4one_laurent68 gamma epsilon i4
    BL CL FL GLa hBL hCL hFL hGL hS0L hi4L'
  have hf' := hf
  simp only [BL, CL, FL, GLa, ← hcs B 1, ← hcs B 2,
    ← hcs C 1, ← hcs C 2, ← hcs F (-1), ← hcs F 0,
    ← hcs G (-1), ← hcs G 0] at hf'
  convert hf' using 1 <;> norm_num

omit [IsAlgClosed k] in
/-- The `I4(1)` face after clearing the three preceding ground-load
identities. -/
theorem rhoOne_boundaryF_i4one_cross68
    (a a1 b b2 fm f0 gm gp c1 c2 epsilon i4 : k)
    (hrow : b * gp + b2 * gm + c1 * f0 + c2 * fm +
      (3 / 4 : k) * epsilon * b = 0)
    (hfollowing : 3 * f0 = 2 * (a1 * b + a * b2))
    (hs1 : 27 * i4 = 32 * a * b * c1)
    (hs2 : 3 * i4 + 16 * b * gm = 0) :
    16 * a * b ^ 2 * gp + 6 * a * b2 * i4 + 9 * a1 * b * i4 +
      16 * a * b * c2 * fm + 12 * a * epsilon * b ^ 2 = 0 := by
  linear_combination
    16 * a * b * hrow - a * b2 * hs2 -
    (16 / 3 : k) * a * b * c1 * hfollowing +
    (1 / 3 : k) * (a1 * b + a * b2) * hs1

omit [IsAlgClosed k] in
/-- Coefficient two of `I3` on the `G[-2]` limb. -/
theorem rhoOne_boundaryG_i3two_laurent68
    (gamma epsilon i3 : k) (A B C F G : LaurentSeries k)
    (hA : (↑(-2 : ℤ) : WithTop ℤ) ≤ A.orderTop)
    (hB : (↑(2 : ℤ) : WithTop ℤ) ≤ B.orderTop)
    (hC : (0 : WithTop ℤ) ≤ C.orderTop)
    (hF : (0 : WithTop ℤ) ≤ F.orderTop)
    (hG : (↑(-2 : ℤ) : WithTop ℤ) ≤ G.orderTop)
    (hS0 : 2 * C.coeff 0 + 3 * gamma = 0)
    (hi3 : rhoOneI3CapFactored68 (HahnSeries.C gamma)
      (HahnSeries.C epsilon) A B C F G = HahnSeries.C i3) :
    (-(8 / 9 : k)) *
        (A.coeff (-2) * B.coeff 2 * F.coeff 2 +
          (A.coeff (-2) * B.coeff 3 + A.coeff (-1) * B.coeff 2) *
            F.coeff 1 +
          (A.coeff (-2) * B.coeff 4 + A.coeff (-1) * B.coeff 3 +
            A.coeff 0 * B.coeff 2) * F.coeff 0) +
      (8 / 3 : k) *
        (C.coeff 1 * G.coeff 1 + C.coeff 2 * G.coeff 0 +
          C.coeff 3 * G.coeff (-1) + C.coeff 4 * G.coeff (-2)) +
      (4 / 3 : k) *
        (2 * F.coeff 0 * F.coeff 2 + F.coeff 1 ^ 2) +
      2 * epsilon * C.coeff 2 = 0 := by
  let S : LaurentSeries k := 2 * C + HahnSeries.C (3 * gamma)
  have hSbase : (0 : WithTop ℤ) ≤ S.orderTop := by
    dsimp only [S]
    apply (le_min ?_ ?_).trans HahnSeries.min_orderTop_le_orderTop_add
    · rw [two_mul]
      exact (le_min hC hC).trans HahnSeries.min_orderTop_le_orderTop_add
    · by_cases hx : 3 * gamma = 0
      · rw [hx, HahnSeries.C_zero]
        simp
      · rw [HahnSeries.C_apply, HahnSeries.orderTop_single hx]
        simp
  have hSco0 : S.coeff 0 = 0 := by
    dsimp only [S]
    rw [HahnSeries.coeff_add]
    simp only [two_mul, HahnSeries.coeff_add, HahnSeries.C_apply,
      HahnSeries.coeff_single_same]
    linear_combination hS0
  have hS := laurent_orderTop_ge_succ_of_coeff_zero68 S 0 hSbase hSco0
  have hSco (n : ℤ) (hn : n ≠ 0) : S.coeff n = 2 * C.coeff n := by
    dsimp only [S]
    rw [HahnSeries.coeff_add]
    simp only [two_mul, HahnSeries.coeff_add, HahnSeries.C_apply,
      HahnSeries.coeff_single]
    rw [if_neg hn]
    ring
  have hAB : (0 : WithTop ℤ) ≤ (A * B).orderTop :=
    le_trans (by
      have ht := add_le_add hA hB
      norm_num at ht ⊢
      exact ht) HahnSeries.orderTop_add_le_mul
  have hAB0 := laurent_coeff_mul_lower68 A B (-2) 2 hA hB
  have hAB1 := laurent_coeff_mul_lower_succ68 A B (-2) 2 hA hB
  have hAB2 := laurent_coeff_mul_lower_two68 A B (-2) 2 hA hB
  have hABF := laurent_coeff_mul_lower_two68 (A * B) F 0 0 hAB hF
  norm_num at hAB0 hAB1 hAB2 hABF
  rw [hAB0, hAB1, hAB2] at hABF
  have hSG := laurent_coeff_mul_lower_three68 S G 1 (-2) hS hG
  norm_num at hSG
  rw [hSco 1 (by norm_num), hSco 2 (by norm_num),
    hSco 3 (by norm_num), hSco 4 (by norm_num)] at hSG
  have hFF := laurent_coeff_mul_lower_two68 F F 0 0 hF hF
  norm_num at hFF
  have hBB : (↑(4 : ℤ) : WithTop ℤ) ≤ (B ^ 2).orderTop := by
    rw [pow_two]
    apply le_trans _ HahnSeries.orderTop_add_le_mul
    have ht := add_le_add hB hB
    norm_num at ht ⊢
    exact ht
  have hB2C : (↑(4 : ℤ) : WithTop ℤ) ≤ (B ^ 2 * C).orderTop :=
    le_trans (by simpa using add_le_add hBB hC) HahnSeries.orderTop_add_le_mul
  have hB2Cz : (B ^ 2 * C).coeff 2 = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hB2C)
  have hB2z : (B ^ 2).coeff 2 = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hBB)
  have hi3rhs : (HahnSeries.C i3 : LaurentSeries k).coeff 2 = 0 := by
    simp [HahnSeries.C_apply]
  have hscale (s : k) (X : LaurentSeries k) (n : ℤ) :
      (HahnSeries.C s * X).coeff n = s * X.coeff n := by
    rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]
  have hi3rewrite : rhoOneI3CapFactored68 (HahnSeries.C gamma)
      (HahnSeries.C epsilon) A B C F G =
      HahnSeries.C (-(8 / 9 : k)) * (A * B * F) +
        HahnSeries.C (-(8 / 9 : k)) * (B ^ 2 * C) +
        HahnSeries.C (4 / 3 : k) * (S * G) +
        HahnSeries.C (4 / 3 : k) * (F * F) +
        HahnSeries.C (-(2 / 3 : k) * gamma) * (B ^ 2) +
        HahnSeries.C (2 * epsilon) * C := by
    simp only [rhoOneI3CapFactored68, S, HahnSeries.C_eq_algebraMap,
      map_mul, map_add, map_neg, map_div₀, map_ofNat, map_one]
    ring
  have hi3c := congrArg (fun X : LaurentSeries k => X.coeff 2) hi3
  rw [hi3rewrite] at hi3c
  simp only [HahnSeries.coeff_add, hscale] at hi3c
  rw [hABF, hB2Cz, hSG, hFF, hB2z, hi3rhs] at hi3c
  linear_combination hi3c

omit [IsAlgClosed k] in
/-- Coefficient three of `I4`; together with `I3(2)` it is the first
pair whose two-by-two minor removes both `B[4]` and `C[3]`. -/
theorem rhoOne_boundaryG_i4three_laurent68
    (gamma epsilon i4 : k) (B C F G : LaurentSeries k)
    (hB : (↑(2 : ℤ) : WithTop ℤ) ≤ B.orderTop)
    (hC : (0 : WithTop ℤ) ≤ C.orderTop)
    (hF : (0 : WithTop ℤ) ≤ F.orderTop)
    (hG : (↑(-2 : ℤ) : WithTop ℤ) ≤ G.orderTop)
    (hS0 : 2 * C.coeff 0 + 3 * gamma = 0)
    (hi4 : rhoOneI4ZeroFactored68 (HahnSeries.C gamma)
      (HahnSeries.C epsilon) B C F G = HahnSeries.C i4) :
    B.coeff 2 * G.coeff 1 + B.coeff 3 * G.coeff 0 +
      B.coeff 4 * G.coeff (-1) + B.coeff 5 * G.coeff (-2) +
      C.coeff 1 * F.coeff 2 + C.coeff 2 * F.coeff 1 +
      C.coeff 3 * F.coeff 0 + (3 / 4 : k) * epsilon * B.coeff 3 = 0 := by
  let S : LaurentSeries k := 2 * C + HahnSeries.C (3 * gamma)
  have hSbase : (0 : WithTop ℤ) ≤ S.orderTop := by
    dsimp only [S]
    apply (le_min ?_ ?_).trans HahnSeries.min_orderTop_le_orderTop_add
    · rw [two_mul]
      exact (le_min hC hC).trans HahnSeries.min_orderTop_le_orderTop_add
    · by_cases hx : 3 * gamma = 0
      · rw [hx, HahnSeries.C_zero]
        simp
      · rw [HahnSeries.C_apply, HahnSeries.orderTop_single hx]
        simp
  have hSco0 : S.coeff 0 = 0 := by
    dsimp only [S]
    rw [HahnSeries.coeff_add]
    simp only [two_mul, HahnSeries.coeff_add, HahnSeries.C_apply,
      HahnSeries.coeff_single_same]
    linear_combination hS0
  have hS := laurent_orderTop_ge_succ_of_coeff_zero68 S 0 hSbase hSco0
  have hSco (n : ℤ) (hn : n ≠ 0) : S.coeff n = 2 * C.coeff n := by
    dsimp only [S]
    rw [HahnSeries.coeff_add]
    simp only [two_mul, HahnSeries.coeff_add, HahnSeries.C_apply,
      HahnSeries.coeff_single]
    rw [if_neg hn]
    ring
  have hBG := laurent_coeff_mul_lower_three68 B G 2 (-2) hB hG
  have hSF := laurent_coeff_mul_lower_two68 S F 1 0 hS hF
  norm_num at hBG hSF
  rw [hSco 1 (by norm_num), hSco 2 (by norm_num),
    hSco 3 (by norm_num)] at hSF
  have hBB : (↑(4 : ℤ) : WithTop ℤ) ≤ (B * B).orderTop := by
    apply le_trans _ HahnSeries.orderTop_add_le_mul
    have ht := add_le_add hB hB
    norm_num at ht ⊢
    exact ht
  have hB3ord : (↑(6 : ℤ) : WithTop ℤ) ≤ (B ^ 3).orderTop := by
    rw [pow_succ, pow_two]
    apply le_trans _ HahnSeries.orderTop_add_le_mul
    have ht := add_le_add hBB hB
    norm_num at ht ⊢
    exact ht
  have hB3z : (B ^ 3).coeff 3 = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hB3ord)
  have hi4rhs : (HahnSeries.C i4 : LaurentSeries k).coeff 3 = 0 := by
    simp [HahnSeries.C_apply]
  have hscale (s : k) (X : LaurentSeries k) (n : ℤ) :
      (HahnSeries.C s * X).coeff n = s * X.coeff n := by
    rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]
  have hi4rewrite : rhoOneI4ZeroFactored68 (HahnSeries.C gamma)
      (HahnSeries.C epsilon) B C F G =
      HahnSeries.C (-(8 / 27 : k)) * (B ^ 3) +
        HahnSeries.C (8 / 3 : k) * (B * G) +
        HahnSeries.C (4 / 3 : k) * (S * F) +
        HahnSeries.C (2 * epsilon) * B := by
    simp only [rhoOneI4ZeroFactored68, S, HahnSeries.C_eq_algebraMap,
      map_mul, map_add, map_neg, map_div₀, map_ofNat, map_one]
    ring
  have hi4c := congrArg (fun X : LaurentSeries k => X.coeff 3) hi4
  rw [hi4rewrite] at hi4c
  simp only [HahnSeries.coeff_add, hscale] at hi4c
  rw [hB3z, hBG, hSF, hi4rhs] at hi4c
  linear_combination (3 / 8 : k) * hi4c

omit [IsAlgClosed k] in
theorem ratFunc_boundaryG_i3two68
    (root gamma epsilon i3 : k) (A B C F G : RatFunc k)
    (hA : (↑(-2 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root A).orderTop)
    (hB : (↑(2 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root B).orderTop)
    (hC : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 root C).orderTop)
    (hF : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 root F).orderTop)
    (hG : (↑(-2 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root G).orderTop)
    (hS0 : 2 * (ratFuncAtHahn46 root C).coeff 0 + 3 * gamma = 0)
    (hi3 : rhoOneI3CapFactored68 (RatFunc.C gamma)
      (RatFunc.C epsilon) A B C F G = RatFunc.C i3) :
    (-(8 / 9 : k)) *
        ((ratFuncAtHahn46 root A).coeff (-2) *
            (ratFuncAtHahn46 root B).coeff 2 *
              (ratFuncAtHahn46 root F).coeff 2 +
          ((ratFuncAtHahn46 root A).coeff (-2) *
              (ratFuncAtHahn46 root B).coeff 3 +
            (ratFuncAtHahn46 root A).coeff (-1) *
              (ratFuncAtHahn46 root B).coeff 2) *
                (ratFuncAtHahn46 root F).coeff 1 +
          ((ratFuncAtHahn46 root A).coeff (-2) *
              (ratFuncAtHahn46 root B).coeff 4 +
            (ratFuncAtHahn46 root A).coeff (-1) *
              (ratFuncAtHahn46 root B).coeff 3 +
            (ratFuncAtHahn46 root A).coeff 0 *
              (ratFuncAtHahn46 root B).coeff 2) *
                (ratFuncAtHahn46 root F).coeff 0) +
      (8 / 3 : k) *
        ((ratFuncAtHahn46 root C).coeff 1 * (ratFuncAtHahn46 root G).coeff 1 +
          (ratFuncAtHahn46 root C).coeff 2 * (ratFuncAtHahn46 root G).coeff 0 +
          (ratFuncAtHahn46 root C).coeff 3 * (ratFuncAtHahn46 root G).coeff (-1) +
          (ratFuncAtHahn46 root C).coeff 4 * (ratFuncAtHahn46 root G).coeff (-2)) +
      (4 / 3 : k) *
        (2 * (ratFuncAtHahn46 root F).coeff 0 *
            (ratFuncAtHahn46 root F).coeff 2 +
          (ratFuncAtHahn46 root F).coeff 1 ^ 2) +
      2 * epsilon * (ratFuncAtHahn46 root C).coeff 2 = 0 := by
  let AL := ratFuncAtLaurent46 root A
  let BL := ratFuncAtLaurent46 root B
  let CL := ratFuncAtLaurent46 root C
  let FL := ratFuncAtLaurent46 root F
  let GLa := ratFuncAtLaurent46 root G
  have hAL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root A (-2) hA
  have hBL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root B 2 hB
  have hCL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root C 0 hC
  have hFL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root F 0 hF
  have hGL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root G (-2) hG
  have hi3L := congrArg (ratFuncAtLaurent46 root) hi3
  have hi3L' : rhoOneI3CapFactored68 (HahnSeries.C gamma)
      (HahnSeries.C epsilon) AL BL CL FL GLa = HahnSeries.C i3 := by
    simpa only [AL, BL, CL, FL, GLa, rhoOneI3CapFactored68,
      map_add, map_sub, map_mul, map_pow, map_neg, map_div₀, map_ofNat,
      ratFuncAtLaurent46_C68] using hi3L
  have hcs (R : RatFunc k) (n : ℤ) := ratFuncAtHahn46_coeff_int68 root R n
  have hS0L : 2 * CL.coeff 0 + 3 * gamma = 0 := by
    rw [← hcs C 0]
    exact hS0
  have hf := rhoOne_boundaryG_i3two_laurent68 gamma epsilon i3
    AL BL CL FL GLa hAL hBL hCL hFL hGL hS0L hi3L'
  have hf' := hf
  simp only [AL, BL, CL, FL, GLa, ← hcs A (-2), ← hcs A (-1),
    ← hcs A 0, ← hcs B 2, ← hcs B 3, ← hcs B 4,
    ← hcs C 1, ← hcs C 2, ← hcs C 3, ← hcs C 4,
    ← hcs F 0, ← hcs F 1, ← hcs F 2,
    ← hcs G (-2), ← hcs G (-1), ← hcs G 0, ← hcs G 1] at hf'
  convert hf' using 1 <;> norm_num

omit [IsAlgClosed k] in
theorem ratFunc_boundaryG_i4three68
    (root gamma epsilon i4 : k) (B C F G : RatFunc k)
    (hB : (↑(2 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root B).orderTop)
    (hC : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 root C).orderTop)
    (hF : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 root F).orderTop)
    (hG : (↑(-2 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root G).orderTop)
    (hS0 : 2 * (ratFuncAtHahn46 root C).coeff 0 + 3 * gamma = 0)
    (hi4 : rhoOneI4ZeroFactored68 (RatFunc.C gamma)
      (RatFunc.C epsilon) B C F G = RatFunc.C i4) :
    (ratFuncAtHahn46 root B).coeff 2 * (ratFuncAtHahn46 root G).coeff 1 +
      (ratFuncAtHahn46 root B).coeff 3 * (ratFuncAtHahn46 root G).coeff 0 +
      (ratFuncAtHahn46 root B).coeff 4 * (ratFuncAtHahn46 root G).coeff (-1) +
      (ratFuncAtHahn46 root B).coeff 5 * (ratFuncAtHahn46 root G).coeff (-2) +
      (ratFuncAtHahn46 root C).coeff 1 * (ratFuncAtHahn46 root F).coeff 2 +
      (ratFuncAtHahn46 root C).coeff 2 * (ratFuncAtHahn46 root F).coeff 1 +
      (ratFuncAtHahn46 root C).coeff 3 * (ratFuncAtHahn46 root F).coeff 0 +
      (3 / 4 : k) * epsilon * (ratFuncAtHahn46 root B).coeff 3 = 0 := by
  let BL := ratFuncAtLaurent46 root B
  let CL := ratFuncAtLaurent46 root C
  let FL := ratFuncAtLaurent46 root F
  let GLa := ratFuncAtLaurent46 root G
  have hBL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root B 2 hB
  have hCL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root C 0 hC
  have hFL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root F 0 hF
  have hGL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root G (-2) hG
  have hi4L := congrArg (ratFuncAtLaurent46 root) hi4
  have hi4L' : rhoOneI4ZeroFactored68 (HahnSeries.C gamma)
      (HahnSeries.C epsilon) BL CL FL GLa = HahnSeries.C i4 := by
    simpa only [BL, CL, FL, GLa, rhoOneI4ZeroFactored68,
      map_add, map_mul, map_pow, map_neg, map_div₀, map_ofNat,
      ratFuncAtLaurent46_C68] using hi4L
  have hcs (R : RatFunc k) (n : ℤ) := ratFuncAtHahn46_coeff_int68 root R n
  have hS0L : 2 * CL.coeff 0 + 3 * gamma = 0 := by
    rw [← hcs C 0]
    exact hS0
  have hf := rhoOne_boundaryG_i4three_laurent68 gamma epsilon i4
    BL CL FL GLa hBL hCL hFL hGL hS0L hi4L'
  have hf' := hf
  simp only [BL, CL, FL, GLa, ← hcs B 2, ← hcs B 3, ← hcs B 4,
    ← hcs B 5, ← hcs C 1, ← hcs C 2, ← hcs C 3,
    ← hcs F 0, ← hcs F 1, ← hcs F 2,
    ← hcs G (-2), ← hcs G (-1), ← hcs G 0, ← hcs G 1] at hf'
  convert hf' using 1 <;> norm_num

omit [IsAlgClosed k] in
/-- The compatibility determinant of the previous scalar with `I3(2)`
and `I4(3)`.  It contains neither `B[4]` nor `C[3]`. -/
theorem rhoOne_boundaryG_b4c3_determinant68
    (x y p0 q0 r0 px py qx qy rx ry : k)
    (hp : p0 + px * x + py * y = 0)
    (hq : q0 + qx * x + qy * y = 0)
    (hr : r0 + rx * x + ry * y = 0) :
    p0 * (qx * ry - qy * rx) - px * (q0 * ry - qy * r0) +
      py * (q0 * rx - qx * r0) = 0 := by
  linear_combination
    (qx * ry - qy * rx) * hp + (-px * ry + py * rx) * hq +
      (px * qy - py * qx) * hr

def RhoOneAlignedSquareFNegOneBoundaryTerminalFollowing68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) (g u : k[X]) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  RhoOneAlignedSquareFNegOneBoundaryTerminalNext68 T g u ∧
  ∃ i4 : k,
    firstIntegralFour68 0 T.source.A T.source.B T.source.C0
      T.source.D T.source.E (RatFunc.C (0 : k))
      (RatFunc.C T.source.gamma) (RatFunc.C (0 : k))
      (RatFunc.C T.source.epsilon) (RatFunc.C (0 : k)) = RatFunc.C i4 ∧
    B.coeff 1 * G.coeff 0 + B.coeff 2 * G.coeff (-1) +
      C.coeff 1 * F.coeff 0 + C.coeff 2 * F.coeff (-1) +
      (3 / 4 : k) * T.source.epsilon * B.coeff 1 = 0 ∧
    16 * A.coeff (-2) * B.coeff 1 ^ 2 * G.coeff 0 +
      6 * A.coeff (-2) * B.coeff 2 * i4 +
      9 * A.coeff (-1) * B.coeff 1 * i4 +
      16 * A.coeff (-2) * B.coeff 1 * C.coeff 2 * F.coeff (-1) +
      12 * A.coeff (-2) * T.source.epsilon * B.coeff 1 ^ 2 = 0

def RhoOneAlignedSquareGNegTwoBoundaryTerminalFollowing68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) (g u : k[X]) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  let P0 := A.coeff (-2) ^ 3 * B.coeff 2 ^ 3 * C.coeff 1 -
      9 * A.coeff (-2) ^ 2 * B.coeff 2 ^ 3 * G.coeff (-1) +
      9 * A.coeff (-2) * A.coeff (-1) * B.coeff 2 ^ 3 * G.coeff (-2) -
      18 * A.coeff (-2) * B.coeff 2 * C.coeff 1 ^ 2 * G.coeff (-1) +
      9 * A.coeff (-2) * B.coeff 2 * C.coeff 1 * C.coeff 2 * G.coeff (-2) +
      9 * A.coeff (-1) * B.coeff 2 * C.coeff 1 ^ 2 * G.coeff (-2) +
      27 * B.coeff 2 * C.coeff 1 * G.coeff (-1) ^ 2 +
      27 * B.coeff 2 * C.coeff 2 * G.coeff (-2) * G.coeff (-1)
  let Q0 := (-(8 / 9 : k)) *
      (A.coeff (-2) * B.coeff 2 * F.coeff 2 +
        (A.coeff (-2) * B.coeff 3 + A.coeff (-1) * B.coeff 2) *
          F.coeff 1 +
        (A.coeff (-1) * B.coeff 3 + A.coeff 0 * B.coeff 2) * F.coeff 0) +
    (8 / 3 : k) *
      (C.coeff 1 * G.coeff 1 + C.coeff 2 * G.coeff 0 +
        C.coeff 4 * G.coeff (-2)) +
    (4 / 3 : k) * (2 * F.coeff 0 * F.coeff 2 + F.coeff 1 ^ 2) +
    2 * T.source.epsilon * C.coeff 2
  let R0 := B.coeff 2 * G.coeff 1 + B.coeff 3 * G.coeff 0 +
      B.coeff 5 * G.coeff (-2) + C.coeff 1 * F.coeff 2 +
      C.coeff 2 * F.coeff 1 + (3 / 4 : k) * T.source.epsilon * B.coeff 3
  RhoOneAlignedSquareGNegTwoBoundaryTerminalNext68 T g u ∧
  ∃ i3 i4 : k,
    firstIntegralThree68 0 T.source.A T.source.B T.source.C0
      T.source.D T.source.E (RatFunc.C (0 : k))
      (RatFunc.C T.source.gamma) (RatFunc.C (0 : k))
      (RatFunc.C T.source.epsilon) (RatFunc.C (0 : k)) = RatFunc.C i3 ∧
    firstIntegralFour68 0 T.source.A T.source.B T.source.C0
      T.source.D T.source.E (RatFunc.C (0 : k))
      (RatFunc.C T.source.gamma) (RatFunc.C (0 : k))
      (RatFunc.C T.source.epsilon) (RatFunc.C (0 : k)) = RatFunc.C i4 ∧
    (P0 *
        ((-(8 / 9 : k)) * A.coeff (-2) * F.coeff 0 ^ 2 -
          (8 / 3 : k) * G.coeff (-1) ^ 2) -
      (-27 * C.coeff 1 * G.coeff (-2) ^ 2) *
        (Q0 * F.coeff 0 - (8 / 3 : k) * G.coeff (-1) * R0) +
      (27 * B.coeff 2 * G.coeff (-2) ^ 2) *
        (Q0 * G.coeff (-1) -
          (-(8 / 9 : k)) * A.coeff (-2) * F.coeff 0 * R0) = 0)

theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryF_terminal_following
    {p q : k[X][X]} {j : k} {h0 g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (R : RhoOneAlignedSquareFNegOneBoundaryTerminalNext68 T g u) :
    RhoOneAlignedSquareFNegOneBoundaryTerminalFollowing68 T g u := by
  have Rc := R
  dsimp only [RhoOneAlignedSquareFNegOneBoundaryTerminalNext68] at Rc
  rcases Rc with ⟨Rt, i4old, hi4srcOld, hs1old, hs2old, hs3old⟩
  have Rtc := Rt
  dsimp only [RhoOneAlignedSquareFNegOneBoundaryTerminal68] at Rtc
  rcases Rtc with ⟨Rf, hterminal⟩
  have Rfc := Rf
  dsimp only [RhoOneAlignedSquareFNegOneBoundaryFollowing68] at Rfc
  rcases Rfc with ⟨Rn, hfollowing⟩
  have Rnc := Rn
  dsimp only [RhoOneAlignedSquareFNegOneBoundaryNext68] at Rnc
  rcases Rnc with ⟨R0, i4base, hi4srcBase, hi4faceBase, hnext⟩
  have R0c := R0
  dsimp only [RhoOneAlignedSquareFNegOneBoundaryResidual68] at R0c
  rcases R0c with ⟨P, hbeta, hdelta, hzeta, hB, hC, hF, hG,
    hf, hg, hS, hb, hrel⟩
  let A : RatFunc k := T.source.A
  let B : RatFunc k := T.source.B
  let C : RatFunc k := T.source.C0 - RatFunc.C (1 / 3 : k) * A ^ 2
  let F : RatFunc k := T.source.D - RatFunc.C (1 / 3 : k) * A * B
  let E : RatFunc k := T.source.E - RatFunc.C (1 / 27 : k) * A ^ 3
  let G : RatFunc k := E - RatFunc.C (1 / 3 : k) * A * C
  have hCmap : ratFuncAtHahn46 T.root C =
      rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0) := by
    dsimp only [C, A, rhoOneCDefectHahn68]
    simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
  have hFmap : ratFuncAtHahn46 T.root F =
      rhoOneTangentDDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.B)
        (ratFuncAtHahn46 T.root T.source.D) := by
    dsimp only [F, A, B, rhoOneTangentDDefectHahn68]
    simp only [map_sub, map_mul, ratFuncAtHahn46_C]
  have hEmap : ratFuncAtHahn46 T.root E =
      rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.E) := by
    dsimp only [E, A, rhoOneEDefectHahn68]
    simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
  have hGmap : ratFuncAtHahn46 T.root G =
      rhoOneTangentEDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0))
        (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.E)) := by
    dsimp only [G, rhoOneTangentEDefectHahn68]
    rw [map_sub, map_mul, hEmap, hCmap]
    rw [map_mul, ratFuncAtHahn46_C]
  have hAH : (↑(-2 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root A).orderTop := by simpa only [A] using P.2.1.1
  have hBH : (↑(1 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root B).orderTop := by simpa only [B] using hB
  have hCH : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root C).orderTop := by
    rw [hCmap]; exact hC
  have hFH : (↑(-1 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root F).orderTop := by rw [hFmap]; exact hF
  have hGH : (↑(-1 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root G).orderTop := by rw [hGmap]; exact hG
  obtain ⟨i4, i3, hi4f, hi3f, hi4src, hi3src⟩ :=
    T.rhoOne_boundary_integral_factors P hbeta hdelta hzeta
  have hfaces := ratFunc_boundaryF_next_integral_faces68
    T.root T.source.gamma T.source.epsilon i4 i3 A B C F G hAH hBH hCH
      hFH hGH (by rw [hCmap]; exact hS)
      (by rw [hFmap]; simpa only [A, B] using hrel) hi4f hi3f
  have hrowR := ratFunc_boundaryF_i4one68 T.root T.source.gamma
    T.source.epsilon i4 B C F G hBH hCH hFH hGH
      (by rw [hCmap]; exact hS) hi4f
  have hrow := hrowR
  rw [hCmap, hFmap, hGmap] at hrow
  have hface := hfaces.1
  rw [hCmap, hFmap, hGmap] at hface
  have hs := rhoOne_boundaryF_i4_terminal_cross68
    ((ratFuncAtHahn46 T.root T.source.A).coeff (-2 : ℚ))
    ((ratFuncAtHahn46 T.root T.source.B).coeff 1)
    ((rhoOneTangentDDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.B)
      (ratFuncAtHahn46 T.root T.source.D)).coeff (-1))
    ((rhoOneTangentEDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0))
      (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.E))).coeff (-1))
    ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.C0)).coeff 1)
    i4 (by simpa only [A, B] using hface) hrel hterminal
  have hcross := rhoOne_boundaryF_i4one_cross68
    ((ratFuncAtHahn46 T.root T.source.A).coeff (-2 : ℚ))
    ((ratFuncAtHahn46 T.root T.source.A).coeff (-1 : ℚ))
    ((ratFuncAtHahn46 T.root T.source.B).coeff 1)
    ((ratFuncAtHahn46 T.root T.source.B).coeff 2)
    ((rhoOneTangentDDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.B)
      (ratFuncAtHahn46 T.root T.source.D)).coeff (-1))
    ((rhoOneTangentDDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.B)
      (ratFuncAtHahn46 T.root T.source.D)).coeff 0)
    ((rhoOneTangentEDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0))
      (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.E))).coeff (-1))
    ((rhoOneTangentEDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0))
      (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.E))).coeff 0)
    ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.C0)).coeff 1)
    ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.C0)).coeff 2)
    T.source.epsilon i4 hrow hfollowing hs.1 hs.2.1
  dsimp only [RhoOneAlignedSquareFNegOneBoundaryTerminalFollowing68]
  exact ⟨R, i4, hi4src, hrow, hcross⟩

theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_terminal_following
    {p q : k[X][X]} {j : k} {h0 g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (R : RhoOneAlignedSquareGNegTwoBoundaryTerminalNext68 T g u) :
    RhoOneAlignedSquareGNegTwoBoundaryTerminalFollowing68 T g u := by
  have Rc := R
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryTerminalNext68] at Rc
  rcases Rc with ⟨Rt, i4old, hi4srcOld, hi4twoOld, hprev⟩
  have Rtc := Rt
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryTerminal68] at Rtc
  rcases Rtc with ⟨Rf, i3old, hi3srcOld, hi3oneOld, hprevOld⟩
  have Rfc := Rf
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryFollowing68] at Rfc
  rcases Rfc with ⟨Rn, i4base, hi4srcBase, hi4one, hterminal⟩
  have Rnc := Rn
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryNext68] at Rnc
  rcases Rnc with ⟨R0, hi3zeroOld, hterminalOld⟩
  have R0c := R0
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryResidual68] at R0c
  rcases R0c with ⟨P, hbeta, hdelta, hzeta, hB, hC, hF, hG,
    hf, hg, hb1, hS, hscalar, hi4oldFace⟩
  let A : RatFunc k := T.source.A
  let B : RatFunc k := T.source.B
  let C : RatFunc k := T.source.C0 - RatFunc.C (1 / 3 : k) * A ^ 2
  let F : RatFunc k := T.source.D - RatFunc.C (1 / 3 : k) * A * B
  let E : RatFunc k := T.source.E - RatFunc.C (1 / 27 : k) * A ^ 3
  let G : RatFunc k := E - RatFunc.C (1 / 3 : k) * A * C
  have hCmap : ratFuncAtHahn46 T.root C =
      rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0) := by
    dsimp only [C, A, rhoOneCDefectHahn68]
    simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
  have hFmap : ratFuncAtHahn46 T.root F =
      rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.B)
        (ratFuncAtHahn46 T.root T.source.D) := by
    dsimp only [F, A, B, rhoOneTangentDDefectHahn68]
    simp only [map_sub, map_mul, ratFuncAtHahn46_C]
  have hEmap : ratFuncAtHahn46 T.root E =
      rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.E) := by
    dsimp only [E, A, rhoOneEDefectHahn68]
    simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
  have hGmap : ratFuncAtHahn46 T.root G =
      rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0))
        (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.E)) := by
    dsimp only [G, rhoOneTangentEDefectHahn68]
    rw [map_sub, map_mul, hEmap, hCmap, map_mul, ratFuncAtHahn46_C]
  have hAH : (↑(-2 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root A).orderTop := by simpa only [A] using P.2.1.1
  have hBH : (↑(2 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root B).orderTop := by simpa only [B] using hB
  have hCH : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root C).orderTop := by
    rw [hCmap]; exact hC
  have hFH : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root F).orderTop := by
    rw [hFmap]; exact hF
  have hGH : (↑(-2 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root G).orderTop := by rw [hGmap]; exact hG
  obtain ⟨i4, i3, hi4f, hi3f, hi4src, hi3src⟩ :=
    T.rhoOne_boundary_integral_factors P hbeta hdelta hzeta
  have hqR := ratFunc_boundaryG_i3two68 T.root T.source.gamma
    T.source.epsilon i3 A B C F G hAH hBH hCH hFH hGH
      (by rw [hCmap]; exact hS) hi3f
  have hrR := ratFunc_boundaryG_i4three68 T.root T.source.gamma
    T.source.epsilon i4 B C F G hBH hCH hFH hGH
      (by rw [hCmap]; exact hS) hi4f
  have hq := hqR
  have hr := hrR
  rw [hCmap, hFmap, hGmap] at hq hr
  let AH := ratFuncAtHahn46 T.root T.source.A
  let BH := ratFuncAtHahn46 T.root T.source.B
  let CH := rhoOneCDefectHahn68 AH (ratFuncAtHahn46 T.root T.source.C0)
  let FH := rhoOneTangentDDefectHahn68 AH BH
    (ratFuncAtHahn46 T.root T.source.D)
  let GH := rhoOneTangentEDefectHahn68 AH CH
    (rhoOneEDefectHahn68 AH (ratFuncAtHahn46 T.root T.source.E))
  let P0 := AH.coeff (-2) ^ 3 * BH.coeff 2 ^ 3 * CH.coeff 1 -
      9 * AH.coeff (-2) ^ 2 * BH.coeff 2 ^ 3 * GH.coeff (-1) +
      9 * AH.coeff (-2) * AH.coeff (-1) * BH.coeff 2 ^ 3 * GH.coeff (-2) -
      18 * AH.coeff (-2) * BH.coeff 2 * CH.coeff 1 ^ 2 * GH.coeff (-1) +
      9 * AH.coeff (-2) * BH.coeff 2 * CH.coeff 1 * CH.coeff 2 * GH.coeff (-2) +
      9 * AH.coeff (-1) * BH.coeff 2 * CH.coeff 1 ^ 2 * GH.coeff (-2) +
      27 * BH.coeff 2 * CH.coeff 1 * GH.coeff (-1) ^ 2 +
      27 * BH.coeff 2 * CH.coeff 2 * GH.coeff (-2) * GH.coeff (-1)
  let Q0 := (-(8 / 9 : k)) *
      (AH.coeff (-2) * BH.coeff 2 * FH.coeff 2 +
        (AH.coeff (-2) * BH.coeff 3 + AH.coeff (-1) * BH.coeff 2) * FH.coeff 1 +
        (AH.coeff (-1) * BH.coeff 3 + AH.coeff 0 * BH.coeff 2) * FH.coeff 0) +
    (8 / 3 : k) * (CH.coeff 1 * GH.coeff 1 + CH.coeff 2 * GH.coeff 0 +
      CH.coeff 4 * GH.coeff (-2)) +
    (4 / 3 : k) * (2 * FH.coeff 0 * FH.coeff 2 + FH.coeff 1 ^ 2) +
    2 * T.source.epsilon * CH.coeff 2
  let R0 := BH.coeff 2 * GH.coeff 1 + BH.coeff 3 * GH.coeff 0 +
    BH.coeff 5 * GH.coeff (-2) + CH.coeff 1 * FH.coeff 2 +
    CH.coeff 2 * FH.coeff 1 + (3 / 4 : k) * T.source.epsilon * BH.coeff 3
  have hp' : P0 + (-27 * CH.coeff 1 * GH.coeff (-2) ^ 2) * BH.coeff 4 +
      (27 * BH.coeff 2 * GH.coeff (-2) ^ 2) * CH.coeff 3 = 0 := by
    dsimp only [P0, AH, BH, CH, FH, GH]
    linear_combination hprev
  have hq' : Q0 + (-(8 / 9 : k) * AH.coeff (-2) * FH.coeff 0) *
      BH.coeff 4 + (8 / 3 : k) * GH.coeff (-1) * CH.coeff 3 = 0 := by
    dsimp only [Q0, AH, BH, CH, FH, GH]
    linear_combination hq
  have hr' : R0 + GH.coeff (-1) * BH.coeff 4 +
      FH.coeff 0 * CH.coeff 3 = 0 := by
    dsimp only [R0, AH, BH, CH, FH, GH]
    linear_combination hr
  have hdet := rhoOne_boundaryG_b4c3_determinant68
    (BH.coeff 4) (CH.coeff 3) P0 Q0 R0
    (-27 * CH.coeff 1 * GH.coeff (-2) ^ 2)
    (27 * BH.coeff 2 * GH.coeff (-2) ^ 2)
    (-(8 / 9 : k) * AH.coeff (-2) * FH.coeff 0)
    ((8 / 3 : k) * GH.coeff (-1)) (GH.coeff (-1)) (FH.coeff 0)
    hp' hq' hr'
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryTerminalFollowing68]
  refine ⟨R, i3, i4, hi3src, hi4src, ?_⟩
  dsimp only [P0, Q0, R0, AH, BH, CH, FH, GH] at hdet
  convert hdet using 1 <;> ring

theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundarySelectors_terminal_following
    {p q : k[X][X]} {j : k} {h0 g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (R : RhoOneAlignedSquareFNegOneBoundaryTerminalNext68 T g u ∨
      RhoOneAlignedSquareGNegTwoBoundaryTerminalNext68 T g u ∨
      (RhoOneAlignedSquareFinalOrderBox68 T ∧ T.source.zeta = 0)) :
    RhoOneAlignedSquareFNegOneBoundaryTerminalFollowing68 T g u ∨
      RhoOneAlignedSquareGNegTwoBoundaryTerminalFollowing68 T g u ∨
      (RhoOneAlignedSquareFinalOrderBox68 T ∧ T.source.zeta = 0) := by
  rcases R with hF | hG | hbox
  · exact Or.inl (T.rhoOne_boundaryF_terminal_following hF)
  · exact Or.inr (Or.inl (T.rhoOne_boundaryG_terminal_following hG))
  · exact Or.inr (Or.inr hbox)

end AlignedSquareBoundarySelectorsTerminalFollowing68

end Max11DegreeRoutes
