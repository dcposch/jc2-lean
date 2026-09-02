import Sol68ScaleTwoAlignedSquareBoundarySelectorsConsumerScratch

/-! # Next invariant and terminal jets on the two boundary packets -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareBoundarySelectorsNext68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

local instance boundarySelectorsNextLaurentCharZero68 :
    CharZero (LaurentSeries k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℤ))

omit [IsAlgClosed k] in
/-- The fourth first integral in the depressed zero-load coordinates,
with its arbitrary ground constant retained. -/
theorem firstIntegralFour_factor_eq68
    (gamma epsilon A B C F G i4 : k)
    (hi4 : firstIntegralFour68 0 A B (A ^ 2 / 3 + C)
      (A * B / 3 + F) (A ^ 3 / 27 + A * C / 3 + G)
      0 gamma 0 epsilon 0 = i4) :
    rhoOneI4ZeroFactored68 gamma epsilon B C F G = i4 := by
  rw [firstIntegralFour_mainTangent_decomposition68] at hi4
  simp only [firstIntegralFourMainTangentTop68,
    firstIntegralFourMainTangentLower68, rhoOneI4ZeroFactored68] at hi4 ⊢
  linear_combination hi4

/-- Exact next `I4(0)` and `I3(-1)` faces on the `F[-1]` packet. -/
theorem rhoOne_boundaryF_next_integral_faces_laurent68
    (gamma epsilon i4 i3 : k)
    (A B C F G : LaurentSeries k)
    (hA : (↑(-2 : ℤ) : WithTop ℤ) ≤ A.orderTop)
    (hB : (↑(1 : ℤ) : WithTop ℤ) ≤ B.orderTop)
    (hC : (0 : WithTop ℤ) ≤ C.orderTop)
    (hF : (↑(-1 : ℤ) : WithTop ℤ) ≤ F.orderTop)
    (hG : (↑(-1 : ℤ) : WithTop ℤ) ≤ G.orderTop)
    (hS0 : 2 * C.coeff 0 + 3 * gamma = 0)
    (hrel : 3 * F.coeff (-1) =
      2 * A.coeff (-2) * B.coeff 1)
    (hi4 : rhoOneI4ZeroFactored68 (HahnSeries.C gamma)
      (HahnSeries.C epsilon) B C F G = HahnSeries.C i4)
    (hi3 : rhoOneI3CapFactored68 (HahnSeries.C gamma)
      (HahnSeries.C epsilon) A B C F G = HahnSeries.C i3) :
    i4 = (8 / 3 : k) *
        (B.coeff 1 * G.coeff (-1) + C.coeff 1 * F.coeff (-1)) ∧
    A.coeff (-2) * B.coeff 1 * F.coeff 0 =
      F.coeff (-1) *
        (A.coeff (-1) * B.coeff 1 + A.coeff (-2) * B.coeff 2) := by
  let S : LaurentSeries k := 2 * C + HahnSeries.C (3 * gamma)
  have hSbase : (0 : WithTop ℤ) ≤ S.orderTop := by
    dsimp only [S]
    apply (le_min ?_ ?_).trans HahnSeries.min_orderTop_le_orderTop_add
    · have h2C : (0 : WithTop ℤ) ≤ (2 * C).orderTop := by
        rw [two_mul]
        exact (le_min hC hC).trans HahnSeries.min_orderTop_le_orderTop_add
      exact h2C
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
    rw [HahnSeries.coeff_add]
    simp only [two_mul, HahnSeries.coeff_add, HahnSeries.C_apply,
      HahnSeries.coeff_single]
    rw [if_neg (by omega)]
    ring
  have hBG := laurent_coeff_mul_lower68 B G 1 (-1) hB hG
  have hSF := laurent_coeff_mul_lower68 S F 1 (-1) hS hF
  norm_num at hBG hSF
  have hB3ord : (↑(3 : ℤ) : WithTop ℤ) ≤ (B ^ 3).orderTop := by
    rw [pow_succ, pow_two]
    have hBB : (↑(2 : ℤ) : WithTop ℤ) ≤ (B * B).orderTop :=
      le_trans (by
        have ht := add_le_add hB hB
        norm_num at ht ⊢
        exact ht) HahnSeries.orderTop_add_le_mul
    exact le_trans (by
      have ht := add_le_add hBB hB
      norm_num at ht ⊢
      exact ht) HahnSeries.orderTop_add_le_mul
  have hB3z : (B ^ 3).coeff 0 = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by omega)) hB3ord)
  have hBz : B.coeff 0 = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by omega)) hB)
  have hi4c := congrArg (fun X : LaurentSeries k => X.coeff 0) hi4
  have hi4rhs : (HahnSeries.C i4 : LaurentSeries k).coeff 0 = i4 := by
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
  rw [hi4rewrite] at hi4c
  simp only [HahnSeries.coeff_add, hscale] at hi4c
  rw [hB3z, hBG, hSF, hBz, hSco1, hi4rhs] at hi4c
  have hAB : (↑(-1 : ℤ) : WithTop ℤ) ≤ (A * B).orderTop :=
    le_trans (by
      have ht := add_le_add hA hB
      norm_num at ht ⊢
      exact ht) HahnSeries.orderTop_add_le_mul
  have hABF := laurent_coeff_mul_lower_succ68 (A * B) F (-1) (-1) hAB hF
  have hAB0 := laurent_coeff_mul_lower68 A B (-2) 1 hA hB
  have hAB1 := laurent_coeff_mul_lower_succ68 A B (-2) 1 hA hB
  norm_num at hABF hAB0 hAB1
  rw [hAB0, hAB1] at hABF
  have hF2 := laurent_coeff_sq_lower_succ68 F (-1) hF
  norm_num at hF2
  have hFF : (F * F).coeff (-1) =
      2 * F.coeff (-1) * F.coeff 0 := by
    simpa only [pow_two] using hF2
  have hSGz : (S * G).coeff (-1) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop (by
      have hSG : (0 : WithTop ℤ) ≤ (S * G).orderTop :=
        le_trans (by simpa using add_le_add hS hG)
          HahnSeries.orderTop_add_le_mul
      exact lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by omega)) hSG)
  have hB2ord : (↑(2 : ℤ) : WithTop ℤ) ≤ (B ^ 2).orderTop := by
    rw [pow_two]
    exact le_trans (by
      have ht := add_le_add hB hB
      norm_num at ht ⊢
      exact ht) HahnSeries.orderTop_add_le_mul
  have hB2Cord : (↑(2 : ℤ) : WithTop ℤ) ≤ (B ^ 2 * C).orderTop := by
    exact le_trans (by simpa using add_le_add hB2ord hC)
      HahnSeries.orderTop_add_le_mul
  have hB2Cz : (B ^ 2 * C).coeff (-1) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by omega)) hB2Cord)
  have hB2z : (B ^ 2).coeff (-1) = 0 := by
    apply HahnSeries.coeff_eq_zero_of_lt_orderTop
    exact lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hB2ord
  have hCz : C.coeff (-1) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by omega)) hC)
  have hi3c := congrArg (fun X : LaurentSeries k => X.coeff (-1)) hi3
  have hi3rhs : (HahnSeries.C i3 : LaurentSeries k).coeff (-1) = 0 := by
    simp [HahnSeries.C_apply]
  have hscale3 (s : k) (X : LaurentSeries k) (n : ℤ) :
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
  rw [hi3rewrite] at hi3c
  simp only [HahnSeries.coeff_add, hscale3] at hi3c
  rw [hABF, hB2Cz, hSGz, hFF, hB2z, hCz, hi3rhs] at hi3c
  constructor
  · linear_combination -hi4c
  · linear_combination (9 / 8 : k) * hi3c +
      -(F.coeff 0) * hrel

/-- Exact `I3(0)` load on the `G[-2]` packet. -/
theorem rhoOne_boundaryG_i3zero_laurent68
    (gamma epsilon i3 : k) (A B C F G : LaurentSeries k)
    (hA : (↑(-2 : ℤ) : WithTop ℤ) ≤ A.orderTop)
    (hB : (↑(2 : ℤ) : WithTop ℤ) ≤ B.orderTop)
    (hC : (0 : WithTop ℤ) ≤ C.orderTop)
    (hF : (0 : WithTop ℤ) ≤ F.orderTop)
    (hG : (↑(-2 : ℤ) : WithTop ℤ) ≤ G.orderTop)
    (hS0 : 2 * C.coeff 0 + 3 * gamma = 0)
    (hscalar : 3 * F.coeff 0 + A.coeff (-2) * B.coeff 2 = 0)
    (hi3 : rhoOneI3CapFactored68 (HahnSeries.C gamma)
      (HahnSeries.C epsilon) A B C F G = HahnSeries.C i3) :
    i3 = (2 / 3 : k) *
      (6 * F.coeff 0 ^ 2 +
        4 * (C.coeff 1 * G.coeff (-1) + C.coeff 2 * G.coeff (-2)) +
        3 * epsilon * C.coeff 0) := by
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
  have hSco2 : S.coeff 2 = 2 * C.coeff 2 := by
    dsimp only [S]
    simp [two_mul, HahnSeries.C_apply, HahnSeries.coeff_single]
  have hAB : (0 : WithTop ℤ) ≤ (A * B).orderTop :=
    le_trans (by simpa using add_le_add hA hB) HahnSeries.orderTop_add_le_mul
  have hABF := laurent_coeff_mul_lower68 (A * B) F 0 0 hAB hF
  have hAB0 := laurent_coeff_mul_lower68 A B (-2) 2 hA hB
  norm_num at hABF hAB0
  rw [hAB0] at hABF
  have hSG := laurent_coeff_mul_lower_succ68 S G 1 (-2) hS hG
  norm_num at hSG
  rw [hSco1, hSco2] at hSG
  have hF2 := laurent_coeff_mul_lower68 F F 0 0 hF hF
  norm_num at hF2
  have hB2Cord : (↑(4 : ℤ) : WithTop ℤ) ≤ (B ^ 2 * C).orderTop := by
    have hBB : (↑(4 : ℤ) : WithTop ℤ) ≤ (B ^ 2).orderTop := by
      rw [pow_two]
      exact le_trans (by
        have ht := add_le_add hB hB
        norm_num at ht ⊢
        exact ht) HahnSeries.orderTop_add_le_mul
    exact le_trans (by simpa using add_le_add hBB hC)
      HahnSeries.orderTop_add_le_mul
  have hB2Cz : (B ^ 2 * C).coeff 0 = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by omega)) hB2Cord)
  have hB2z : (B ^ 2).coeff 0 = 0 := by
    apply HahnSeries.coeff_eq_zero_of_lt_orderTop
    rw [pow_two]
    have ht := add_le_add hB hB
    norm_num at ht
    exact lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num))
      (le_trans ht HahnSeries.orderTop_add_le_mul)
  have hi3c := congrArg (fun X : LaurentSeries k => X.coeff 0) hi3
  have hi3rhs : (HahnSeries.C i3 : LaurentSeries k).coeff 0 = i3 := by
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
  rw [hi3rewrite] at hi3c
  simp only [HahnSeries.coeff_add, hscale] at hi3c
  rw [hABF, hB2Cz, hSG, hF2, hB2z, hi3rhs] at hi3c
  linear_combination -hi3c - (8 / 9 : k) * F.coeff 0 * hscalar

/-- Terminal coefficient `-4` after the new `G[-2]` scalar.  The unknown
next derivative coefficient of `A` cancels against
`3F[0]+A[-2]B[2]=0`. -/
theorem rhoOneMainTangentTerminal_coeff_negFour_gNegTwo68
    (gamma epsilon : k)
    (A B C F G dA dB dC dF dG : LaurentSeries k)
    (hA : (↑(-2 : ℤ) : WithTop ℤ) ≤ A.orderTop)
    (hB : (↑(2 : ℤ) : WithTop ℤ) ≤ B.orderTop)
    (hC : (0 : WithTop ℤ) ≤ C.orderTop)
    (hF : (0 : WithTop ℤ) ≤ F.orderTop)
    (hG : (↑(-2 : ℤ) : WithTop ℤ) ≤ G.orderTop)
    (hdA : (↑(-3 : ℤ) : WithTop ℤ) ≤ dA.orderTop)
    (hdB : (0 : WithTop ℤ) ≤ dB.orderTop)
    (hdC : (0 : WithTop ℤ) ≤ dC.orderTop)
    (hdF : (0 : WithTop ℤ) ≤ dF.orderTop)
    (hdG : (↑(-3 : ℤ) : WithTop ℤ) ≤ dG.orderTop)
    (hdAco : dA.coeff (-3) = (-2 : k) * A.coeff (-2))
    (hS0 : 2 * C.coeff 0 + 3 * gamma = 0)
    (hscalar : 3 * F.coeff 0 + A.coeff (-2) * B.coeff 2 = 0) :
    (rhoOneMainTangentTerminal68 (HahnSeries.C gamma)
      (HahnSeries.C epsilon) A B C F G dA dB dC dF dG).coeff (-4) =
      (8 / 27 : k) * A.coeff (-2) *
        (G.coeff (-2) *
            (3 * F.coeff 1 + A.coeff (-1) * B.coeff 2 +
              A.coeff (-2) * B.coeff 3) +
          A.coeff (-2) * F.coeff 0 * C.coeff 1) := by
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
      (hX : (↑n : WithTop ℤ) ≤ X.orderTop) (hlt : (-4 : ℤ) < n) :
      X.coeff (-4) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr hlt) hX)
  have h1 := zero_of_lower (F * dC) 0 (lower2 F dC 0 0 hF hdC) (by omega)
  have h2 := zero_of_lower (F * dA) (-3)
    (lower2 F dA 0 (-3) hF hdA) (by omega)
  have h3 := laurent_coeff_mul_three_lower_succ68
    F G dA 0 (-2) (-3) hF hG hdA
  have h4 := zero_of_lower (F * F * dB) 0
    (lower3 F F dB 0 0 0 hF hF hdB) (by omega)
  have h5 := zero_of_lower (C * F * dC) 0
    (lower3 C F dC 0 0 0 hC hF hdC) (by omega)
  have h6 := zero_of_lower (B * dG) (-1)
    (lower2 B dG 2 (-3) hB hdG) (by omega)
  have h7 := zero_of_lower (B * F * dF) 2
    (lower3 B F dF 2 0 0 hB hF hdF) (by omega)
  have h8 := zero_of_lower (B * C * dG) (-1)
    (lower3 B C dG 2 0 (-3) hB hC hdG) (by omega)
  have h9 := zero_of_lower (B * C * dA) (-1)
    (lower3 B C dA 2 0 (-3) hB hC hdA) (by omega)
  have h10 := zero_of_lower (B * C * C * dA) (-1)
    (lower4 B C C dA 2 0 0 (-3) hB hC hC hdA) (by omega)
  have hAFdAord0 := lower3 A F dA (-2) 0 (-3) hA hF hdA
  have hAFdAord : (↑(-5 : ℤ) : WithTop ℤ) ≤
      (A * F * dA).orderTop := by
    convert hAFdAord0 using 1 <;> norm_num
  have hAFdA0 := laurent_coeff_mul_three_lower_terminal68
    A F dA (-2) 0 (-3) hA hF hdA
  have hAFdA : (A * F * dA).coeff (-5) =
      A.coeff (-2) * F.coeff 0 * dA.coeff (-3) := by
    convert hAFdA0 using 1 <;> norm_num
  have h11 := laurent_coeff_mul_lower68 (A * F * dA) S (-5) 1 hAFdAord hS
  norm_num at h11
  rw [hAFdA] at h11
  have h12 := zero_of_lower (A * B * dA) (-3)
    (lower3 A B dA (-2) 2 (-3) hA hB hdA) (by omega)
  have h13 := laurent_coeff_mul_four_lower_succ_terminal68
    A B G dA (-2) 2 (-2) (-3) hA hB hG hdA
  have h14 := zero_of_lower (A * B * F * dB) 0
    (lower4 A B F dB (-2) 2 0 0 hA hB hF hdB) (by omega)
  have h15 := zero_of_lower (A * B * B * dF) 2
    (lower4 A B B dF (-2) 2 2 0 hA hB hB hdF) (by omega)
  norm_num at h3 h13
  have hscale (s : k) (X : LaurentSeries k) (n : ℤ) :
      (HahnSeries.C s * X).coeff n = s * X.coeff n := by
    rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]
  have hrewrite :
      rhoOneMainTangentTerminal68 (HahnSeries.C gamma)
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
  linear_combination
    -(4 / 27 : k) * G.coeff (-2) * dA.coeff (-2) * hscalar +
    (8 / 27 : k) * A.coeff (-2) * G.coeff (-1) * hscalar

/-- Rational transport of the two next `F[-1]` invariant faces. -/
theorem ratFunc_boundaryF_next_integral_faces68
    (root gamma epsilon i4 i3 : k) (A B C F G : RatFunc k)
    (hA : (↑(-2 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root A).orderTop)
    (hB : (↑(1 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root B).orderTop)
    (hC : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 root C).orderTop)
    (hF : (↑(-1 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root F).orderTop)
    (hG : (↑(-1 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root G).orderTop)
    (hS0 : 2 * (ratFuncAtHahn46 root C).coeff 0 + 3 * gamma = 0)
    (hrel : 3 * (ratFuncAtHahn46 root F).coeff (-1) =
      2 * (ratFuncAtHahn46 root A).coeff (-2) *
        (ratFuncAtHahn46 root B).coeff 1)
    (hi4 : rhoOneI4ZeroFactored68 (RatFunc.C gamma)
      (RatFunc.C epsilon) B C F G = RatFunc.C i4)
    (hi3 : rhoOneI3CapFactored68 (RatFunc.C gamma)
      (RatFunc.C epsilon) A B C F G = RatFunc.C i3) :
    i4 = (8 / 3 : k) *
        ((ratFuncAtHahn46 root B).coeff 1 *
            (ratFuncAtHahn46 root G).coeff (-1) +
          (ratFuncAtHahn46 root C).coeff 1 *
            (ratFuncAtHahn46 root F).coeff (-1)) ∧
    (ratFuncAtHahn46 root A).coeff (-2) *
        (ratFuncAtHahn46 root B).coeff 1 *
          (ratFuncAtHahn46 root F).coeff 0 =
      (ratFuncAtHahn46 root F).coeff (-1) *
        ((ratFuncAtHahn46 root A).coeff (-1) *
            (ratFuncAtHahn46 root B).coeff 1 +
          (ratFuncAtHahn46 root A).coeff (-2) *
            (ratFuncAtHahn46 root B).coeff 2) := by
  let AL := ratFuncAtLaurent46 root A
  let BL := ratFuncAtLaurent46 root B
  let CL := ratFuncAtLaurent46 root C
  let FL := ratFuncAtLaurent46 root F
  let GLa := ratFuncAtLaurent46 root G
  have hAL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root A (-2) hA
  have hBL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root B 1 hB
  have hCL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root C 0 hC
  have hFL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root F (-1) hF
  have hGL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root G (-1) hG
  have hi4L := congrArg (ratFuncAtLaurent46 root) hi4
  have hi3L := congrArg (ratFuncAtLaurent46 root) hi3
  have hi4L' : rhoOneI4ZeroFactored68 (HahnSeries.C gamma)
      (HahnSeries.C epsilon) BL CL FL GLa = HahnSeries.C i4 := by
    simpa only [AL, BL, CL, FL, GLa, rhoOneI4ZeroFactored68,
      map_add, map_mul, map_pow, map_neg, map_div₀, map_ofNat,
      ratFuncAtLaurent46_C68] using hi4L
  have hi3L' : rhoOneI3CapFactored68 (HahnSeries.C gamma)
      (HahnSeries.C epsilon) AL BL CL FL GLa = HahnSeries.C i3 := by
    simpa only [AL, BL, CL, FL, GLa, rhoOneI3CapFactored68,
      map_add, map_sub, map_mul, map_pow, map_neg, map_div₀, map_ofNat,
      ratFuncAtLaurent46_C68] using hi3L
  have hcs (R : RatFunc k) (n : ℤ) := ratFuncAtHahn46_coeff_int68 root R n
  have hS0L : 2 * CL.coeff 0 + 3 * gamma = 0 := by
    rw [← hcs C 0]
    exact hS0
  have hrelL : 3 * FL.coeff (-1) = 2 * AL.coeff (-2) * BL.coeff 1 := by
    rw [← hcs F (-1), ← hcs A (-2), ← hcs B 1]
    exact hrel
  have hf := rhoOne_boundaryF_next_integral_faces_laurent68
    gamma epsilon i4 i3 AL BL CL FL GLa hAL hBL hCL hFL hGL
      hS0L hrelL hi4L' hi3L'
  have hf' := hf
  simp only [AL, BL, CL, FL, GLa, ← hcs A (-2), ← hcs A (-1),
    ← hcs B 1, ← hcs B 2, ← hcs C 1, ← hcs F (-1), ← hcs F 0,
    ← hcs G (-1)] at hf'
  convert hf' using 1 <;> norm_num

/-- Rational transport of the `G[-2]` `I3(0)` load. -/
theorem ratFunc_boundaryG_i3zero68
    (root gamma epsilon i3 : k) (A B C F G : RatFunc k)
    (hA : (↑(-2 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root A).orderTop)
    (hB : (↑(2 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root B).orderTop)
    (hC : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 root C).orderTop)
    (hF : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 root F).orderTop)
    (hG : (↑(-2 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root G).orderTop)
    (hS0 : 2 * (ratFuncAtHahn46 root C).coeff 0 + 3 * gamma = 0)
    (hscalar : 3 * (ratFuncAtHahn46 root F).coeff 0 +
      (ratFuncAtHahn46 root A).coeff (-2) *
        (ratFuncAtHahn46 root B).coeff 2 = 0)
    (hi3 : rhoOneI3CapFactored68 (RatFunc.C gamma)
      (RatFunc.C epsilon) A B C F G = RatFunc.C i3) :
    i3 = (2 / 3 : k) *
      (6 * (ratFuncAtHahn46 root F).coeff 0 ^ 2 +
        4 * ((ratFuncAtHahn46 root C).coeff 1 *
              (ratFuncAtHahn46 root G).coeff (-1) +
            (ratFuncAtHahn46 root C).coeff 2 *
              (ratFuncAtHahn46 root G).coeff (-2)) +
        3 * epsilon * (ratFuncAtHahn46 root C).coeff 0) := by
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
  have hscalarL : 3 * FL.coeff 0 + AL.coeff (-2) * BL.coeff 2 = 0 := by
    rw [← hcs F 0, ← hcs A (-2), ← hcs B 2]
    exact hscalar
  have hf := rhoOne_boundaryG_i3zero_laurent68 gamma epsilon i3
    AL BL CL FL GLa hAL hBL hCL hFL hGL hS0L hscalarL hi3L'
  have hf' := hf
  simp only [AL, BL, CL, FL, GLa, ← hcs A (-2), ← hcs B 2,
    ← hcs C 0, ← hcs C 1, ← hcs C 2, ← hcs F 0,
    ← hcs G (-2), ← hcs G (-1)] at hf'
  convert hf' using 1 <;> norm_num

/-- Common source construction of the two arbitrary-ground invariant
constants in depressed coordinates. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundary_integral_factors
    {p q : k[X][X]} {j : k} {h0 g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (P : RhoOneZeroLCubicNextSourcePacket68 T g u)
    (hbeta : T.source.beta = 0) (hdelta : T.source.delta = 0)
    (hzeta : T.source.zeta = 0) :
    let A := T.source.A
    let B := T.source.B
    let C := T.source.C0 - RatFunc.C (1 / 3 : k) * A ^ 2
    let F := T.source.D - RatFunc.C (1 / 3 : k) * A * B
    let E := T.source.E - RatFunc.C (1 / 27 : k) * A ^ 3
    let G := E - RatFunc.C (1 / 3 : k) * A * C
    ∃ i4 i3 : k,
      rhoOneI4ZeroFactored68 (RatFunc.C T.source.gamma)
        (RatFunc.C T.source.epsilon) B C F G = RatFunc.C i4 ∧
      rhoOneI3CapFactored68 (RatFunc.C T.source.gamma)
        (RatFunc.C T.source.epsilon) A B C F G = RatFunc.C i3 ∧
      firstIntegralFour68 0 T.source.A T.source.B T.source.C0
        T.source.D T.source.E (RatFunc.C (0 : k))
        (RatFunc.C T.source.gamma) (RatFunc.C (0 : k))
        (RatFunc.C T.source.epsilon) (RatFunc.C (0 : k)) = RatFunc.C i4 ∧
      firstIntegralThree68 0 T.source.A T.source.B T.source.C0
        T.source.D T.source.E (RatFunc.C (0 : k))
        (RatFunc.C T.source.gamma) (RatFunc.C (0 : k))
        (RatFunc.C T.source.epsilon) (RatFunc.C (0 : k)) = RatFunc.C i3 := by
  dsimp only
  obtain ⟨i4, i3, hi4, hi3⟩ := integratedFirstIntegrals_exist_ground68
    T.source.A T.source.B T.source.C0 T.source.D T.source.E
      (RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
      0 T.source.alpha T.source.beta T.source.gamma T.source.delta
      T.source.epsilon T.source.zeta T.source.eta (by
        simpa only [RatFunc.algebraMap_eq_C] using T.source.bracket_eq)
  rw [hbeta, hdelta, hzeta] at hi4 hi3
  let A : RatFunc k := T.source.A
  let B : RatFunc k := T.source.B
  let C : RatFunc k := T.source.C0 - RatFunc.C (1 / 3 : k) * A ^ 2
  let F : RatFunc k := T.source.D - RatFunc.C (1 / 3 : k) * A * B
  let E : RatFunc k := T.source.E - RatFunc.C (1 / 27 : k) * A ^ 3
  let G : RatFunc k := E - RatFunc.C (1 / 3 : k) * A * C
  have hCrec : A ^ 2 / 3 + C = T.source.C0 := by
    dsimp only [C, A]
    simp only [RatFunc.algebraMap_eq_C, map_div₀, map_one, map_ofNat]
    ring
  have hDrec : A * B / 3 + F = T.source.D := by
    dsimp only [F, A, B]
    simp only [RatFunc.algebraMap_eq_C, map_div₀, map_one, map_ofNat]
    ring
  have hErec : A ^ 3 / 27 + A * C / 3 + G = T.source.E := by
    dsimp only [G, E, C, A]
    simp only [RatFunc.algebraMap_eq_C, map_div₀, map_one, map_ofNat]
    ring
  have hi4T : firstIntegralFour68 0 A B (A ^ 2 / 3 + C)
      (A * B / 3 + F) (A ^ 3 / 27 + A * C / 3 + G)
      (RatFunc.C (0 : k)) (RatFunc.C T.source.gamma) (RatFunc.C (0 : k))
      (RatFunc.C T.source.epsilon) (RatFunc.C (0 : k)) = RatFunc.C i4 := by
    rw [hCrec, hDrec, hErec]
    simpa only [A, B, RatFunc.algebraMap_eq_C, RatFunc.C.map_zero] using hi4
  have hi3T : firstIntegralThree68 0 A B (A ^ 2 / 3 + C)
      (A * B / 3 + F) (A ^ 3 / 27 + A * C / 3 + G)
      (RatFunc.C (0 : k)) (RatFunc.C T.source.gamma) (RatFunc.C (0 : k))
      (RatFunc.C T.source.epsilon) (RatFunc.C (0 : k)) = RatFunc.C i3 := by
    rw [hCrec, hDrec, hErec]
    simpa only [A, B, RatFunc.algebraMap_eq_C, RatFunc.C.map_zero] using hi3
  have h4f := firstIntegralFour_factor_eq68 (RatFunc.C T.source.gamma)
    (RatFunc.C T.source.epsilon) A B C F G (RatFunc.C i4)
      (by simpa only [map_zero] using hi4T)
  have h3f := firstIntegralThree_cap_factor68 (RatFunc.C T.source.gamma)
    (RatFunc.C T.source.epsilon) A B C F G (RatFunc.C i3)
      (by simpa only [map_zero] using hi3T)
  exact ⟨i4, i3, h4f, h3f,
    (by simpa only [RatFunc.algebraMap_eq_C, RatFunc.C.map_zero] using hi4),
    (by simpa only [RatFunc.algebraMap_eq_C, RatFunc.C.map_zero] using hi3)⟩

def RhoOneAlignedSquareFNegOneBoundaryNext68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) (g u : k[X]) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  RhoOneAlignedSquareFNegOneBoundaryResidual68 T g u ∧
  ∃ i4 : k,
    firstIntegralFour68 0 T.source.A T.source.B T.source.C0
      T.source.D T.source.E (RatFunc.C (0 : k))
      (RatFunc.C T.source.gamma) (RatFunc.C (0 : k))
      (RatFunc.C T.source.epsilon) (RatFunc.C (0 : k)) = RatFunc.C i4 ∧
    i4 = (8 / 3 : k) *
      (B.coeff 1 * G.coeff (-1) + C.coeff 1 * F.coeff (-1)) ∧
    A.coeff (-2) * B.coeff 1 * F.coeff 0 =
      F.coeff (-1) * (A.coeff (-1) * B.coeff 1 +
        A.coeff (-2) * B.coeff 2)

def RhoOneAlignedSquareGNegTwoBoundaryNext68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) (g u : k[X]) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  RhoOneAlignedSquareGNegTwoBoundaryResidual68 T g u ∧
  (∃ i3 : k,
    firstIntegralThree68 0 T.source.A T.source.B T.source.C0
      T.source.D T.source.E (RatFunc.C (0 : k))
      (RatFunc.C T.source.gamma) (RatFunc.C (0 : k))
      (RatFunc.C T.source.epsilon) (RatFunc.C (0 : k)) = RatFunc.C i3 ∧
    i3 = (2 / 3 : k) *
      (6 * F.coeff 0 ^ 2 +
        4 * (C.coeff 1 * G.coeff (-1) + C.coeff 2 * G.coeff (-2)) +
        3 * T.source.epsilon * C.coeff 0)) ∧
  G.coeff (-2) *
      (3 * F.coeff 1 + A.coeff (-1) * B.coeff 2 +
        A.coeff (-2) * B.coeff 3) +
    A.coeff (-2) * F.coeff 0 * C.coeff 1 = 0

theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryF_next
    {p q : k[X][X]} {j : k} {h0 g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (R : RhoOneAlignedSquareFNegOneBoundaryResidual68 T g u) :
    RhoOneAlignedSquareFNegOneBoundaryNext68 T g u := by
  have Rcopy := R
  dsimp only [RhoOneAlignedSquareFNegOneBoundaryResidual68] at Rcopy
  rcases Rcopy with ⟨P, hbeta, hdelta, hzeta, hB, hC, hF, hG,
    hf, hg2, hS, hb, hrel⟩
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
  obtain ⟨i4, i3, hi4f, hi3f, hi4src, hi3src⟩ :=
    T.rhoOne_boundary_integral_factors P hbeta hdelta hzeta
  have hA : (↑(-2 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root A).orderTop := by
    simpa only [A] using P.2.1.1
  have hfaces := ratFunc_boundaryF_next_integral_faces68
    T.root T.source.gamma T.source.epsilon i4 i3 A B C F G hA
      (by simpa only [B] using hB) (by rw [hCmap]; exact hC)
      (by rw [hFmap]; exact hF) (by rw [hGmap]; exact hG)
      (by rw [hCmap]; exact hS)
      (by rw [hFmap]; simpa only [A, B] using hrel) hi4f hi3f
  dsimp only [RhoOneAlignedSquareFNegOneBoundaryNext68]
  refine ⟨R, i4, hi4src, ?_, ?_⟩
  · rw [← hGmap, ← hCmap, ← hFmap]
    simpa only [B] using hfaces.1
  · rw [← hFmap]
    simpa only [A, B] using hfaces.2

theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_next
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (R : RhoOneAlignedSquareGNegTwoBoundaryResidual68 T g u) :
    RhoOneAlignedSquareGNegTwoBoundaryNext68 T g u := by
  have Rcopy := R
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryResidual68] at Rcopy
  rcases Rcopy with ⟨P, hbeta, hdelta, hzeta, hB, hC, hF, hG,
    hf, hg, hb1, hS, hscalar, hi4old⟩
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
    ratFuncAtHahn68_linearRoot_single_deriv
      h0 T.root T.scale_degree T.root_eq
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
  have hi3face := ratFunc_boundaryG_i3zero68 T.root T.source.gamma
    T.source.epsilon i3 A B C F G hAH hBH hCH hFH hGH
      (by rw [hCmap]; exact hS)
      (by rw [hFmap]; simpa only [A, B] using hscalar) hi3f
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
  have hdFH : (0 : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root (Differential.deriv F)).orderTop :=
    ratFuncAtHahn46_deriv_orderTop_nonneg_of_nonneg T.root F hFH
  have hdGH : (↑(-3 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root (Differential.deriv G)).orderTop :=
    ratFuncAtHahn68_deriv_orderTop_ge_negThree_of_ge_negTwo
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
  have hBL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root B 2 hBH
  have hCL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root C 0 hCH
  have hFL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root F 0 hFH
  have hGL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root G (-2) hGH
  have hdAL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root
    (Differential.deriv A) (-3) hdAH
  have hdBL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root
    (Differential.deriv B) 0 hdBH
  have hdCL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root
    (Differential.deriv C) 0 hdCH
  have hdFL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root
    (Differential.deriv F) 0 hdFH
  have hdGL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root
    (Differential.deriv G) (-3) hdGH
  have hcs (R0 : RatFunc k) (n : ℤ) := ratFuncAtHahn46_coeff_int68 T.root R0 n
  have hdAcoL : dAL.coeff (-3) = (-2 : k) * AL.coeff (-2) := by
    rw [← hcs (Differential.deriv A) (-3), ← hcs A (-2)]
    exact hdAcoH
  have hS0L : 2 * CL.coeff 0 + 3 * T.source.gamma = 0 := by
    rw [← hcs C 0, hCmap]
    exact hS
  have hscalarL : 3 * FL.coeff 0 + AL.coeff (-2) * BL.coeff 2 = 0 := by
    rw [← hcs F 0, ← hcs A (-2), ← hcs B 2]
    have hs : 3 * (ratFuncAtHahn46 T.root F).coeff 0 +
        (ratFuncAtHahn46 T.root A).coeff (-2) *
          (ratFuncAtHahn46 T.root B).coeff 2 = 0 := by
      simpa only [A, B, hFmap] using hscalar
    convert hs using 1 <;> norm_num
  have htermL := rhoOneMainTangentTerminal_coeff_negFour_gNegTwo68
    T.source.gamma T.source.epsilon AL BL CL FL GLa dAL dBL dCL dFL dGL
      hAL hBL hCL hFL hGL hdAL hdBL hdCL hdFL hdGL hdAcoL hS0L hscalarL
  have hsparseL := congrArg (ratFuncAtLaurent46 T.root) hsparseR
  have hsparseL' : rhoOneMainTangentTerminal68 (HahnSeries.C T.source.gamma)
      (HahnSeries.C T.source.epsilon) AL BL CL FL GLa dAL dBL dCL dFL dGL =
      ratFuncAtLaurent46 T.root
        (RatFunc.C j / algebraMap k[X] (RatFunc k) h0) := by
    simpa only [AL, BL, CL, FL, GLa, dAL, dBL, dCL, dFL, dGL,
      rhoOneMainTangentTerminal68, ratFuncDerivation68,
      ratFuncDerivation46_apply, map_add, map_mul, map_pow, map_neg,
      map_div₀, map_ofNat, map_one, ratFuncAtLaurent46_C68] using hsparseL
  have hterminal4H :
      (ratFuncAtHahn46 T.root
        (RatFunc.C j / algebraMap k[X] (RatFunc k) h0)).coeff (-4) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop (by
      rw [T.terminal_order]
      exact WithTop.coe_lt_coe.mpr (by norm_num))
  have hterminal4L :
      (ratFuncAtLaurent46 T.root
        (RatFunc.C j / algebraMap k[X] (RatFunc k) h0)).coeff (-4) = 0 := by
    rw [← hcs (RatFunc.C j / algebraMap k[X] (RatFunc k) h0) (-4)]
    exact hterminal4H
  have hleft4 := congrArg (fun X : LaurentSeries k => X.coeff (-4)) hsparseL'
  rw [htermL, hterminal4L] at hleft4
  have hterminalScalarL : GLa.coeff (-2) *
        (3 * FL.coeff 1 + AL.coeff (-1) * BL.coeff 2 +
          AL.coeff (-2) * BL.coeff 3) +
      AL.coeff (-2) * FL.coeff 0 * CL.coeff 1 = 0 := by
    have hc : (8 / 27 : k) ≠ 0 := by norm_num
    rcases mul_eq_zero.mp hleft4 with hca | hs
    · rcases mul_eq_zero.mp hca with hc0 | ha0
      · exact (hc hc0).elim
      · apply (hAne ?_).elim
        have ha := hcs A (-2)
        norm_num at ha
        rw [ha]
        exact ha0
    · exact hs
  have hterminalScalar :
      (ratFuncAtHahn46 T.root G).coeff (-2) *
          (3 * (ratFuncAtHahn46 T.root F).coeff 1 +
            (ratFuncAtHahn46 T.root A).coeff (-1) *
              (ratFuncAtHahn46 T.root B).coeff 2 +
            (ratFuncAtHahn46 T.root A).coeff (-2) *
              (ratFuncAtHahn46 T.root B).coeff 3) +
        (ratFuncAtHahn46 T.root A).coeff (-2) *
          (ratFuncAtHahn46 T.root F).coeff 0 *
            (ratFuncAtHahn46 T.root C).coeff 1 = 0 := by
    have ht := hterminalScalarL
    simp only [GLa, FL, AL, BL, CL, ← hcs G (-2), ← hcs F 1,
      ← hcs A (-1), ← hcs B 2,
      ← hcs A (-2), ← hcs B 3, ← hcs F 0, ← hcs C 1] at ht
    convert ht using 1 <;> norm_num
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryNext68]
  refine ⟨R, ⟨i3, hi3src, ?_⟩, ?_⟩
  · have ht := hi3face
    rw [hFmap, hCmap, hGmap] at ht
    simpa only [A, B] using ht
  · have ht := hterminalScalar
    rw [hGmap, hFmap, hCmap] at ht
    simpa only [A, B] using ht

/-- Two-branch refinement; the final order box is preserved literally. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundarySelectors_next
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (R : RhoOneAlignedSquareFNegOneBoundaryResidual68 T g u ∨
      RhoOneAlignedSquareGNegTwoBoundaryResidual68 T g u ∨
      (RhoOneAlignedSquareFinalOrderBox68 T ∧ T.source.zeta = 0)) :
    RhoOneAlignedSquareFNegOneBoundaryNext68 T g u ∨
      RhoOneAlignedSquareGNegTwoBoundaryNext68 T g u ∨
      (RhoOneAlignedSquareFinalOrderBox68 T ∧ T.source.zeta = 0) := by
  rcases R with hF | hG | hbox
  · exact Or.inl (T.rhoOne_boundaryF_next hF)
  · exact Or.inr (Or.inl
      (T.rhoOne_boundaryG_next hp hH hp6 hp5 hp4 hG))
  · exact Or.inr (Or.inr hbox)

end AlignedSquareBoundarySelectorsNext68

end Max11DegreeRoutes
