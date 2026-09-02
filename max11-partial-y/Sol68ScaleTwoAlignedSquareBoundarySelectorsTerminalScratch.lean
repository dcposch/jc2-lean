import Sol68ScaleTwoAlignedSquareBoundarySelectorsFollowingScratch

/-! # Terminal and I3 reductions on the two aligned-square boundary limbs -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareBoundarySelectorsTerminal68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

local instance boundarySelectorsTerminalHahnCharZero68 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

local instance boundarySelectorsTerminalLaurentCharZero68 :
    CharZero (LaurentSeries k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℤ))

omit [IsAlgClosed k] in
/-- On the `F[-1]` limb the terminal coefficient `-5` has only three
surviving monomials once `2C[0]+3γ=0` raises the affine factor. -/
theorem rhoOneMainTangentTerminal_coeff_negFive_fNegOne68
    (gamma epsilon : k)
    (A B C F G dA dB dC dF dG : LaurentSeries k)
    (hA : (↑(-2 : ℤ) : WithTop ℤ) ≤ A.orderTop)
    (hB : (↑(1 : ℤ) : WithTop ℤ) ≤ B.orderTop)
    (hC : (0 : WithTop ℤ) ≤ C.orderTop)
    (hF : (↑(-1 : ℤ) : WithTop ℤ) ≤ F.orderTop)
    (hG : (↑(-1 : ℤ) : WithTop ℤ) ≤ G.orderTop)
    (hdA : (↑(-3 : ℤ) : WithTop ℤ) ≤ dA.orderTop)
    (hdB : (0 : WithTop ℤ) ≤ dB.orderTop)
    (hdC : (0 : WithTop ℤ) ≤ dC.orderTop)
    (hdF : (↑(-2 : ℤ) : WithTop ℤ) ≤ dF.orderTop)
    (hdG : (↑(-2 : ℤ) : WithTop ℤ) ≤ dG.orderTop)
    (hdAco : dA.coeff (-3 : ℤ) = (-2 : k) * A.coeff (-2 : ℤ))
    (hS0 : 2 * C.coeff 0 + 3 * gamma = 0) :
    (rhoOneMainTangentTerminal68 (HahnSeries.C gamma)
      (HahnSeries.C epsilon) A B C F G dA dB dC dF dG).coeff (-5 : ℤ) =
      (8 / 27 : k) * A.coeff (-2 : ℤ) *
        (3 * F.coeff (-1 : ℤ) * G.coeff (-1 : ℤ) +
          A.coeff (-2 : ℤ) * F.coeff (-1 : ℤ) * C.coeff (1 : ℤ) +
          A.coeff (-2 : ℤ) * B.coeff (1 : ℤ) * G.coeff (-1 : ℤ)) := by
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
  have hSco1 : S.coeff 1 = 2 * C.coeff 1 := by
    dsimp only [S]
    simp [two_mul, HahnSeries.C_apply, HahnSeries.coeff_single]
  have lower2 (X Y : LaurentSeries k) (m n : ℤ)
      (hX : (↑m : WithTop ℤ) ≤ X.orderTop)
      (hY : (↑n : WithTop ℤ) ≤ Y.orderTop) :
      (↑(m + n) : WithTop ℤ) ≤ (X * Y).orderTop :=
    le_trans (by simpa using add_le_add hX hY) HahnSeries.orderTop_add_le_mul
  have lower3 (X Y Z : LaurentSeries k) (m n r : ℤ)
      (hX : (↑m : WithTop ℤ) ≤ X.orderTop)
      (hY : (↑n : WithTop ℤ) ≤ Y.orderTop)
      (hZ : (↑r : WithTop ℤ) ≤ Z.orderTop) :
      (↑(m + n + r) : WithTop ℤ) ≤ (X * Y * Z).orderTop :=
    lower2 (X * Y) Z (m + n) r (lower2 X Y m n hX hY) hZ
  have lower4 (X Y Z W : LaurentSeries k) (m n r s : ℤ)
      (hX : (↑m : WithTop ℤ) ≤ X.orderTop)
      (hY : (↑n : WithTop ℤ) ≤ Y.orderTop)
      (hZ : (↑r : WithTop ℤ) ≤ Z.orderTop)
      (hW : (↑s : WithTop ℤ) ≤ W.orderTop) :
      (↑(m + n + r + s) : WithTop ℤ) ≤ (X * Y * Z * W).orderTop :=
    lower2 (X * Y * Z) W (m + n + r) s
      (lower3 X Y Z m n r hX hY hZ) hW
  have zero_of_lower (X : LaurentSeries k) (n : ℤ)
      (hX : (↑n : WithTop ℤ) ≤ X.orderTop) (hlt : (-5 : ℤ) < n) :
      X.coeff (-5) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr hlt) hX)
  have h1 := zero_of_lower (F * dC) (-1) (lower2 F dC (-1) 0 hF hdC) (by omega)
  have h2 := zero_of_lower (F * dA) (-4) (lower2 F dA (-1) (-3) hF hdA) (by omega)
  have h3 := laurent_coeff_mul_three_lower_terminal68 F G dA (-1) (-1) (-3) hF hG hdA
  norm_num at h3
  have h4 := zero_of_lower (F * F * dB) (-2) (lower3 F F dB (-1) (-1) 0 hF hF hdB) (by omega)
  have h5 := zero_of_lower (C * F * dC) (-1) (lower3 C F dC 0 (-1) 0 hC hF hdC) (by omega)
  have h6 := zero_of_lower (B * dG) (-1) (lower2 B dG 1 (-2) hB hdG) (by omega)
  have h7 := zero_of_lower (B * F * dF) (-2) (lower3 B F dF 1 (-1) (-2) hB hF hdF) (by omega)
  have h8 := zero_of_lower (B * C * dG) (-1) (lower3 B C dG 1 0 (-2) hB hC hdG) (by omega)
  have h9 := zero_of_lower (B * C * dA) (-2) (lower3 B C dA 1 0 (-3) hB hC hdA) (by omega)
  have h10 := zero_of_lower (B * C * C * dA) (-2) (lower4 B C C dA 1 0 0 (-3) hB hC hC hdA) (by omega)
  have hAFdAord := lower3 A F dA (-2) (-1) (-3) hA hF hdA
  have hAFdAco := laurent_coeff_mul_three_lower_terminal68 A F dA (-2) (-1) (-3) hA hF hdA
  have h11 := laurent_coeff_mul_lower68 (A * F * dA) S (-6) 1
    (by convert hAFdAord using 1 <;> norm_num) hS
  norm_num at hAFdAco h11
  rw [hAFdAco] at h11
  have h12 := zero_of_lower (A * B * dA) (-4) (lower3 A B dA (-2) 1 (-3) hA hB hdA) (by omega)
  have hABGord := lower3 A B G (-2) 1 (-1) hA hB hG
  have hABGco := laurent_coeff_mul_three_lower_terminal68 A B G (-2) 1 (-1) hA hB hG
  have h13 := laurent_coeff_mul_lower68 (A * B * G) dA (-2) (-3)
    (by convert hABGord using 1 <;> norm_num) hdA
  norm_num at hABGco h13
  rw [hABGco] at h13
  have h14 := zero_of_lower (A * B * F * dB) (-2) (lower4 A B F dB (-2) 1 (-1) 0 hA hB hF hdB) (by omega)
  have h15 := zero_of_lower (A * B * B * dF) (-2) (lower4 A B B dF (-2) 1 1 (-2) hA hB hB hdF) (by omega)
  have hscale (s : k) (X : LaurentSeries k) (n : ℤ) :
      (HahnSeries.C s * X).coeff n = s * X.coeff n := by
    rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]
  have hrewrite : rhoOneMainTangentTerminal68 (HahnSeries.C gamma)
      (HahnSeries.C epsilon) A B C F G dA dB dC dF dG =
      HahnSeries.C (-(2 / 3 : k) * gamma) * (F * dC) +
      HahnSeries.C (-(1 / 3 : k) * epsilon) * (F * dA) +
      HahnSeries.C (-(4 / 9 : k)) * (F * G * dA) +
      HahnSeries.C (-(4 / 9 : k)) * (F * F * dB) +
      HahnSeries.C (-(4 / 9 : k)) * (C * F * dC) +
      HahnSeries.C ((2 / 3 : k) * gamma) * (B * dG) +
      HahnSeries.C (-(4 / 9 : k)) * (B * F * dF) +
      HahnSeries.C (4 / 9 : k) * (B * C * dG) +
      HahnSeries.C ((2 / 9 : k) * gamma) * (B * C * dA) +
      HahnSeries.C (4 / 27 : k) * (B * C * C * dA) +
      HahnSeries.C (-(2 / 27 : k)) * (A * F * dA * S) +
      HahnSeries.C (-(1 / 9 : k) * epsilon) * (A * B * dA) +
      HahnSeries.C (-(4 / 27 : k)) * (A * B * G * dA) +
      HahnSeries.C (-(4 / 27 : k)) * (A * B * F * dB) +
      HahnSeries.C (-(4 / 27 : k)) * (A * B * B * dF) := by
    simp only [rhoOneMainTangentTerminal68, S, HahnSeries.C_eq_algebraMap,
      map_mul, map_add, map_neg, map_div₀, map_ofNat, map_one]
    ring
  rw [hrewrite]
  simp only [HahnSeries.coeff_add, hscale]
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
    h14, h15, hdAco, hSco1]
  ring

omit [IsAlgClosed k] in
/-- The terminal factor, the old leading relation, and nonvanishing of
`A[-2]` and `F[-1]` reduce to one short scalar. -/
theorem rhoOne_boundaryF_terminal_scalar68
    (a b fm gm c1 : k) (ha : a ≠ 0) (hf : fm ≠ 0)
    (hrel : 3 * fm = 2 * a * b)
    (hterminal : (8 / 27 : k) * a *
      (3 * fm * gm + a * fm * c1 + a * b * gm) = 0) :
    2 * a * c1 + 9 * gm = 0 := by
  have hc : (8 / 27 : k) ≠ 0 := by norm_num
  have hi : 3 * fm * gm + a * fm * c1 + a * b * gm = 0 := by
    rcases mul_eq_zero.mp hterminal with hca | hi
    · rcases mul_eq_zero.mp hca with hc0 | ha0
      · exact (hc hc0).elim
      · exact (ha ha0).elim
    · exact hi
  have hp : fm * (2 * a * c1 + 9 * gm) = 0 := by
    linear_combination 2 * hi + gm * hrel
  exact (mul_eq_zero.mp hp).resolve_left hf

omit [IsAlgClosed k] in
/-- Exact coefficient one of the arbitrary-ground `I3` factor on the
`G[-2]` limb. -/
theorem rhoOne_boundaryG_i3one_laurent68
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
        (A.coeff (-2) * B.coeff 2 * F.coeff 1 +
          (A.coeff (-2) * B.coeff 3 + A.coeff (-1) * B.coeff 2) * F.coeff 0) +
      (8 / 3 : k) *
        (C.coeff 1 * G.coeff 0 + C.coeff 2 * G.coeff (-1) +
          C.coeff 3 * G.coeff (-2)) +
      (8 / 3 : k) * F.coeff 0 * F.coeff 1 +
      2 * epsilon * C.coeff 1 = 0 := by
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
  have hABF := laurent_coeff_mul_lower_succ68 (A * B) F 0 0 hAB hF
  norm_num at hAB0 hAB1 hABF
  rw [hAB0, hAB1] at hABF
  have hSG := laurent_coeff_mul_lower_two68 S G 1 (-2) hS hG
  norm_num at hSG
  rw [hSco 1 (by norm_num), hSco 2 (by norm_num), hSco 3 (by norm_num)] at hSG
  have hFF := laurent_coeff_mul_lower_succ68 F F 0 0 hF hF
  norm_num at hFF
  have hBB : (↑(4 : ℤ) : WithTop ℤ) ≤ (B ^ 2).orderTop := by
    rw [pow_two]
    apply le_trans _ HahnSeries.orderTop_add_le_mul
    have ht := add_le_add hB hB
    norm_num at ht ⊢
    exact ht
  have hB2C : (↑(4 : ℤ) : WithTop ℤ) ≤ (B ^ 2 * C).orderTop :=
    le_trans (by simpa using add_le_add hBB hC) HahnSeries.orderTop_add_le_mul
  have hB2Cz : (B ^ 2 * C).coeff 1 = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hB2C)
  have hB2z : (B ^ 2).coeff 1 = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hBB)
  have hi3rhs : (HahnSeries.C i3 : LaurentSeries k).coeff 1 = 0 := by
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
  have hi3c := congrArg (fun X : LaurentSeries k => X.coeff 1) hi3
  rw [hi3rewrite] at hi3c
  simp only [HahnSeries.coeff_add, hscale] at hi3c
  rw [hABF, hB2Cz, hSG, hFF, hB2z, hi3rhs] at hi3c
  linear_combination hi3c

omit [IsAlgClosed k] in
/-- Rational transport of the `I3(1)` row. -/
theorem ratFunc_boundaryG_i3one68
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
            (ratFuncAtHahn46 root B).coeff 2 * (ratFuncAtHahn46 root F).coeff 1 +
          ((ratFuncAtHahn46 root A).coeff (-2) * (ratFuncAtHahn46 root B).coeff 3 +
            (ratFuncAtHahn46 root A).coeff (-1) * (ratFuncAtHahn46 root B).coeff 2) *
              (ratFuncAtHahn46 root F).coeff 0) +
      (8 / 3 : k) *
        ((ratFuncAtHahn46 root C).coeff 1 * (ratFuncAtHahn46 root G).coeff 0 +
          (ratFuncAtHahn46 root C).coeff 2 * (ratFuncAtHahn46 root G).coeff (-1) +
          (ratFuncAtHahn46 root C).coeff 3 * (ratFuncAtHahn46 root G).coeff (-2)) +
      (8 / 3 : k) * (ratFuncAtHahn46 root F).coeff 0 *
        (ratFuncAtHahn46 root F).coeff 1 +
      2 * epsilon * (ratFuncAtHahn46 root C).coeff 1 = 0 := by
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
  have hf := rhoOne_boundaryG_i3one_laurent68 gamma epsilon i3
    AL BL CL FL GLa hAL hBL hCL hFL hGL hS0L hi3L'
  have hf' := hf
  simp only [AL, BL, CL, FL, GLa, ← hcs A (-2), ← hcs A (-1),
    ← hcs B 2, ← hcs B 3, ← hcs C 1, ← hcs C 2, ← hcs C 3,
    ← hcs F 0, ← hcs F 1, ← hcs G (-2), ← hcs G (-1),
    ← hcs G 0] at hf'
  convert hf' using 1 <;> norm_num

omit [IsAlgClosed k] in
/-- Polynomial cross-elimination of `B3`, `F0`, and `F1` from the new
`I3(1)` row using the scalar, `I4(1)`, and terminal transport. -/
theorem rhoOne_boundaryG_i3_cross68
    (a a1 b b3 f f1 g gm gp c1 c2 c3 epsilon : k)
    (hscalar : 3 * f + a * b = 0)
    (hi4 : b * gm + b3 * g + c1 * f = 0)
    (hterm : g * (3 * f1 + a1 * b) = a * b * gm)
    (hi3 : (-(8 / 9 : k)) *
        (a * b * f1 + (a * b3 + a1 * b) * f) +
      (8 / 3 : k) * (c1 * gp + c2 * gm + c3 * g) +
      (8 / 3 : k) * f * f1 + 2 * epsilon * c1 = 0) :
    4 * a ^ 3 * b ^ 2 * c1 - 36 * a ^ 2 * b ^ 2 * gm +
      36 * a * a1 * b ^ 2 * g + 81 * c1 * epsilon * g +
      108 * c1 * g * gp + 108 * c2 * g * gm + 108 * c3 * g ^ 2 = 0 := by
  linear_combination
    (81 / 2 : k) * g * hi3 +
    24 * a * b * hterm -
    12 * a ^ 2 * b * hi4 +
    4 * (a ^ 2 * b * c1 + 3 * a * b3 * g + 3 * a1 * b * g -
      9 * f1 * g) * hscalar

def RhoOneAlignedSquareFNegOneBoundaryTerminal68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) (g u : k[X]) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  RhoOneAlignedSquareFNegOneBoundaryFollowing68 T g u ∧
  2 * A.coeff (-2) * C.coeff 1 + 9 * G.coeff (-1) = 0

def RhoOneAlignedSquareGNegTwoBoundaryTerminal68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) (g u : k[X]) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  RhoOneAlignedSquareGNegTwoBoundaryFollowing68 T g u ∧
  ∃ i3 : k,
    firstIntegralThree68 0 T.source.A T.source.B T.source.C0
      T.source.D T.source.E (RatFunc.C (0 : k))
      (RatFunc.C T.source.gamma) (RatFunc.C (0 : k))
      (RatFunc.C T.source.epsilon) (RatFunc.C (0 : k)) = RatFunc.C i3 ∧
    (-(8 / 9 : k)) *
        (A.coeff (-2) * B.coeff 2 * F.coeff 1 +
          (A.coeff (-2) * B.coeff 3 + A.coeff (-1) * B.coeff 2) *
            F.coeff 0) +
      (8 / 3 : k) *
        (C.coeff 1 * G.coeff 0 + C.coeff 2 * G.coeff (-1) +
          C.coeff 3 * G.coeff (-2)) +
      (8 / 3 : k) * F.coeff 0 * F.coeff 1 +
      2 * T.source.epsilon * C.coeff 1 = 0 ∧
    4 * A.coeff (-2) ^ 3 * B.coeff 2 ^ 2 * C.coeff 1 -
        36 * A.coeff (-2) ^ 2 * B.coeff 2 ^ 2 * G.coeff (-1) +
      36 * A.coeff (-2) * A.coeff (-1) * B.coeff 2 ^ 2 * G.coeff (-2) +
      81 * C.coeff 1 * T.source.epsilon * G.coeff (-2) +
      108 * C.coeff 1 * G.coeff (-2) * G.coeff 0 +
      108 * C.coeff 2 * G.coeff (-2) * G.coeff (-1) +
      108 * C.coeff 3 * G.coeff (-2) ^ 2 = 0

/-- The next terminal face on the `F[-1]` boundary, transported all the
way from the integrated source bracket. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryF_terminal
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (R : RhoOneAlignedSquareFNegOneBoundaryFollowing68 T g u) :
    RhoOneAlignedSquareFNegOneBoundaryTerminal68 T g u := by
  have Rc := R
  dsimp only [RhoOneAlignedSquareFNegOneBoundaryFollowing68] at Rc
  rcases Rc with ⟨Rn, hfollow⟩
  have Rnc := Rn
  dsimp only [RhoOneAlignedSquareFNegOneBoundaryNext68] at Rnc
  rcases Rnc with ⟨R0, i4, hi4src, hi4face, hnext⟩
  have R0c := R0
  dsimp only [RhoOneAlignedSquareFNegOneBoundaryResidual68] at R0c
  rcases R0c with ⟨P, hbeta, hdelta, hzeta, hB, hC, hF, hG,
    hf, hg, hS, hb, hrel⟩
  obtain ⟨c, t, v, z, hc, hsingle, ht, hv, hzdef, hz, hvcore, htcore⟩ := P.1
  let A : RatFunc k := T.source.A
  let B : RatFunc k := T.source.B
  let C : RatFunc k := T.source.C0 - RatFunc.C (1 / 3 : k) * A ^ 2
  let F : RatFunc k := T.source.D - RatFunc.C (1 / 3 : k) * A * B
  let E : RatFunc k := T.source.E - RatFunc.C (1 / 27 : k) * A ^ 3
  let G : RatFunc k := E - RatFunc.C (1 / 3 : k) * A * C
  let A0 := localClearedA68RhoOne g u
  have hAclear := (T.source.clearedCoordinatesRhoOne hp T.scale_ne_zero
    hH hp6 hp5 hp4).1
  change algebraMap k[X] (RatFunc k) A0 =
    (algebraMap k[X] (RatFunc k) h0) ^ 2 * A at hAclear
  obtain ⟨c', hc', hsingle', hderiv'⟩ :=
    ratFuncAtHahn68_linearRoot_single_deriv h0 T.root T.scale_degree T.root_eq
  have hcEq : c' = c := by
    have heq := congrArg (fun X : HahnSeries ℚ k => X.coeff 1)
      (hsingle'.symm.trans hsingle)
    simpa only [HahnSeries.coeff_single_same] using heq
  subst c'
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
  have hAne : (ratFuncAtHahn46 T.root A).coeff (-2) ≠ 0 := by
    simpa only [A] using P.2.2.1
  have hBH : (↑(1 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root B).orderTop := by simpa only [B] using hB
  have hCH : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root C).orderTop := by
    rw [hCmap]; exact hC
  have hFH : (↑(-1 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root F).orderTop := by rw [hFmap]; exact hF
  have hGH : (↑(-1 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root G).orderTop := by rw [hGmap]; exact hG
  have hconst (x : k) : ratFuncDerivation68 (RatFunc.C x) = 0 := by
    have hx := GCD369RatFuncDerivative (Polynomial.C x)
    simpa [ratFuncDerivation68, RatFunc.algebraMap_C] using hx
  have hlow := constantBracket_integrated68_lowerSystem
    ratFuncDerivation68 (RatFunc.C 0) T.source.A T.source.B
      T.source.C0 T.source.D T.source.E (RatFunc.C T.source.alpha)
      (RatFunc.C T.source.beta) (RatFunc.C T.source.gamma)
      (RatFunc.C T.source.delta) (RatFunc.C T.source.epsilon)
      (RatFunc.C T.source.zeta) (RatFunc.C T.source.eta)
      (RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
      (hconst 0) (hconst T.source.alpha) (hconst T.source.beta)
      (hconst T.source.gamma) (hconst T.source.delta)
      (hconst T.source.epsilon) (hconst T.source.zeta)
      (hconst T.source.eta) T.source.bracket_eq
  rw [hbeta, hdelta, hzeta] at hlow
  have hCrec : A ^ 2 / 3 + C = T.source.C0 := by
    dsimp only [C, A]
    simp only [map_div₀, map_one, map_ofNat]
    ring
  have hDrec : A * B / 3 + F = T.source.D := by
    dsimp only [F, A, B]
    simp only [map_div₀, map_one, map_ofNat]
    ring
  have hErec : A ^ 3 / 27 + A * C / 3 + G = T.source.E := by
    dsimp only [G, E, C, A]
    simp only [map_div₀, map_one, map_ofNat]
    ring
  have hfactor := integratedTerminal_mainTangent_factorization68
    ratFuncDerivation68 (RatFunc.C T.source.alpha)
      (RatFunc.C T.source.gamma) (RatFunc.C T.source.epsilon)
      (RatFunc.C T.source.eta) A B C F G
      (hconst T.source.alpha) (hconst T.source.gamma)
      (hconst T.source.epsilon) (hconst T.source.eta)
  have hsparseR : rhoOneMainTangentTerminal68 (RatFunc.C T.source.gamma)
      (RatFunc.C T.source.epsilon) A B C F G
      (ratFuncDerivation68 A) (ratFuncDerivation68 B) (ratFuncDerivation68 C)
      (ratFuncDerivation68 F) (ratFuncDerivation68 G) =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0 := by
    rw [← hfactor, hCrec, hDrec, hErec]
    simpa only [map_zero] using hlow.2.2.2.2
  have hdAH : (↑(-3 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root (Differential.deriv A)).orderTop := by
    dsimp only [A]
    convert localHahn_deriv_orderTop_ge_of_cleared T.root h0 A0
      T.source.A 2 T.scale_order hAclear using 1 <;> norm_num
  have hdAcoH :
      (ratFuncAtHahn46 T.root (Differential.deriv A)).coeff (-3) =
        (-2 : k) * (ratFuncAtHahn46 T.root A).coeff (-2) := by
    dsimp only [A]
    convert localHahn_deriv_coeff_neg_succ_of_cleared T.root c h0 A0
      T.source.A 2 hc hsingle hderiv' hAclear using 1 <;> norm_num
  have hdBH : (0 : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root (Differential.deriv B)).orderTop :=
    ratFuncAtHahn46_deriv_orderTop_nonneg_of_nonneg T.root B
      (le_trans (WithTop.coe_le_coe.mpr (by norm_num)) hBH)
  have hdCH : (0 : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root (Differential.deriv C)).orderTop :=
    ratFuncAtHahn46_deriv_orderTop_nonneg_of_nonneg T.root C hCH
  have hdFH : (↑(-2 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root (Differential.deriv F)).orderTop :=
    ratFuncAtHahn68_deriv_orderTop_ge_negTwo_of_ge_negOne
      T.root h0 F T.scale_order hFH
  have hdGH : (↑(-2 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root (Differential.deriv G)).orderTop :=
    ratFuncAtHahn68_deriv_orderTop_ge_negTwo_of_ge_negOne
      T.root h0 G T.scale_order hGH
  let AL := ratFuncAtLaurent46 T.root A
  let BL := ratFuncAtLaurent46 T.root B
  let CL := ratFuncAtLaurent46 T.root C
  let FL := ratFuncAtLaurent46 T.root F
  let GLa := ratFuncAtLaurent46 T.root G
  let dAL := ratFuncAtLaurent46 T.root (Differential.deriv A)
  let dBL := ratFuncAtLaurent46 T.root (Differential.deriv B)
  let dCL := ratFuncAtLaurent46 T.root (Differential.deriv C)
  let dFL := ratFuncAtLaurent46 T.root (Differential.deriv F)
  let dGL := ratFuncAtLaurent46 T.root (Differential.deriv G)
  have hAL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root A (-2) hAH
  have hBL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root B 1 hBH
  have hCL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root C 0 hCH
  have hFL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root F (-1) hFH
  have hGL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root G (-1) hGH
  have hdAL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root
    (Differential.deriv A) (-3) hdAH
  have hdBL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root
    (Differential.deriv B) 0 hdBH
  have hdCL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root
    (Differential.deriv C) 0 hdCH
  have hdFL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root
    (Differential.deriv F) (-2) hdFH
  have hdGL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root
    (Differential.deriv G) (-2) hdGH
  have hcs (R0 : RatFunc k) (n : ℤ) := ratFuncAtHahn46_coeff_int68 T.root R0 n
  have hdAcoL : dAL.coeff (-3) = (-2 : k) * AL.coeff (-2) := by
    rw [← hcs (Differential.deriv A) (-3), ← hcs A (-2)]
    exact hdAcoH
  have hS0L : 2 * CL.coeff 0 + 3 * T.source.gamma = 0 := by
    rw [← hcs C 0, hCmap]
    exact hS
  have htermL := rhoOneMainTangentTerminal_coeff_negFive_fNegOne68
    T.source.gamma T.source.epsilon AL BL CL FL GLa dAL dBL dCL dFL dGL
      hAL hBL hCL hFL hGL hdAL hdBL hdCL hdFL hdGL hdAcoL hS0L
  have hsparseL := congrArg (ratFuncAtLaurent46 T.root) hsparseR
  have hsparseL' : rhoOneMainTangentTerminal68 (HahnSeries.C T.source.gamma)
      (HahnSeries.C T.source.epsilon) AL BL CL FL GLa dAL dBL dCL dFL dGL =
      ratFuncAtLaurent46 T.root
        (RatFunc.C j / algebraMap k[X] (RatFunc k) h0) := by
    simpa only [AL, BL, CL, FL, GLa, dAL, dBL, dCL, dFL, dGL,
      rhoOneMainTangentTerminal68, ratFuncDerivation68,
      ratFuncDerivation46_apply, map_add, map_mul, map_pow, map_neg,
      map_div₀, map_ofNat, map_one, ratFuncAtLaurent46_C68] using hsparseL
  have hterminalH : (ratFuncAtHahn46 T.root
      (RatFunc.C j / algebraMap k[X] (RatFunc k) h0)).coeff (-5) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop (by
      rw [T.terminal_order]
      exact WithTop.coe_lt_coe.mpr (by norm_num))
  have hterminalL : (ratFuncAtLaurent46 T.root
      (RatFunc.C j / algebraMap k[X] (RatFunc k) h0)).coeff (-5) = 0 := by
    rw [← hcs (RatFunc.C j / algebraMap k[X] (RatFunc k) h0) (-5)]
    exact hterminalH
  have hleft := congrArg (fun X : LaurentSeries k => X.coeff (-5)) hsparseL'
  rw [htermL, hterminalL] at hleft
  have hfm : (ratFuncAtHahn46 T.root F).coeff (-1) ≠ 0 := by
    rw [hFmap]
    exact hf
  have hscalarL := rhoOne_boundaryF_terminal_scalar68
    (AL.coeff (-2)) (BL.coeff 1) (FL.coeff (-1)) (GLa.coeff (-1))
      (CL.coeff 1)
      (by rw [← hcs A (-2)]; exact hAne)
      (by rw [← hcs F (-1)]; exact hfm)
      (by
        rw [← hcs F (-1), ← hcs A (-2), ← hcs B 1]
        have hr := hrel
        rw [← hFmap] at hr
        change 3 * (ratFuncAtHahn46 T.root F).coeff (-1) =
          2 * (ratFuncAtHahn46 T.root A).coeff (-2) *
            (ratFuncAtHahn46 T.root B).coeff 1 at hr
        exact hr)
      hleft
  have hscalar := hscalarL
  simp only [AL, CL, GLa, ← hcs A (-2), ← hcs C 1, ← hcs G (-1)] at hscalar
  dsimp only [RhoOneAlignedSquareFNegOneBoundaryTerminal68]
  refine ⟨R, ?_⟩
  rw [hCmap, hGmap] at hscalar
  dsimp only [A] at hscalar
  norm_num at hscalar ⊢
  exact hscalar

/-- The next arbitrary-ground `I3` row on the `G[-2]` boundary, crossed
with the already verified `I4(1)` and terminal reductions. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_terminal
    {p q : k[X][X]} {j : k} {h0 g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (R : RhoOneAlignedSquareGNegTwoBoundaryFollowing68 T g u) :
    RhoOneAlignedSquareGNegTwoBoundaryTerminal68 T g u := by
  have Rc := R
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryFollowing68] at Rc
  rcases Rc with ⟨Rn, i4old, hi4srcOld, hi4face, hterminal⟩
  have Rnc := Rn
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryNext68] at Rnc
  rcases Rnc with ⟨R0, hi3old, hterminalOld⟩
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
  have hrow := ratFunc_boundaryG_i3one68 T.root T.source.gamma
    T.source.epsilon i3 A B C F G hAH hBH hCH hFH hGH
      (by rw [hCmap]; exact hS) hi3f
  have hrowC := hrow
  rw [hCmap, hFmap, hGmap] at hrowC
  have hcross := rhoOne_boundaryG_i3_cross68
    ((ratFuncAtHahn46 T.root T.source.A).coeff (-2 : ℚ))
    ((ratFuncAtHahn46 T.root T.source.A).coeff (-1 : ℚ))
    ((ratFuncAtHahn46 T.root T.source.B).coeff (2 : ℚ))
    ((ratFuncAtHahn46 T.root T.source.B).coeff (3 : ℚ))
    ((rhoOneTangentDDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.B)
      (ratFuncAtHahn46 T.root T.source.D)).coeff 0)
    ((rhoOneTangentDDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.B)
      (ratFuncAtHahn46 T.root T.source.D)).coeff 1)
    ((rhoOneTangentEDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0))
      (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.E))).coeff (-2))
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
    ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.C0)).coeff 3)
    T.source.epsilon hscalar hi4face hterminal hrowC
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryTerminal68]
  refine ⟨R, i3, hi3src, ?_, ?_⟩
  · simpa only [A, B] using hrowC
  · exact hcross

/-- Both boundary limbs receive one strict new terminal/invariant reduction;
the final-order-box sibling is unchanged. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundarySelectors_terminal
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (R : RhoOneAlignedSquareFNegOneBoundaryFollowing68 T g u ∨
      RhoOneAlignedSquareGNegTwoBoundaryFollowing68 T g u ∨
      (RhoOneAlignedSquareFinalOrderBox68 T ∧ T.source.zeta = 0)) :
    RhoOneAlignedSquareFNegOneBoundaryTerminal68 T g u ∨
      RhoOneAlignedSquareGNegTwoBoundaryTerminal68 T g u ∨
      (RhoOneAlignedSquareFinalOrderBox68 T ∧ T.source.zeta = 0) := by
  rcases R with hF | hG | hbox
  · exact Or.inl (T.rhoOne_boundaryF_terminal hp hH hp6 hp5 hp4 hF)
  · exact Or.inr (Or.inl (T.rhoOne_boundaryG_terminal hG))
  · exact Or.inr (Or.inr hbox)

end AlignedSquareBoundarySelectorsTerminal68

end Max11DegreeRoutes
