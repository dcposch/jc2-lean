import Sol68ScaleTwoAlignedSquareTerminalGBoundaryCapEndpointFiveScratch

/-! # Source-factor proofs of the two reduced-integral order gains -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareTerminalGBoundaryCapSourceOrderGains68

variable {k : Type*} [Field k] [CharZero k]

local instance alignedSquareTerminalGBoundaryCapSourceOrderGainsHahnCharZero68 :
    CharZero (LaurentSeries k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℤ))

theorem laurent_orderTop_ge_const_mul68
    (a : k) (X : LaurentSeries k) (m : ℤ)
    (hX : (↑m : WithTop ℤ) ≤ X.orderTop) :
    (↑m : WithTop ℤ) ≤ (HahnSeries.C a * X).orderTop := by
  have ha : (0 : WithTop ℤ) ≤ (HahnSeries.C a : LaurentSeries k).orderTop := by
    by_cases hz : a = 0
    · simp [hz]
    · rw [HahnSeries.C_apply, HahnSeries.orderTop_single hz]
      exact le_rfl
  have h := le_trans (add_le_add ha hX) HahnSeries.orderTop_add_le_mul
  simpa using h

theorem laurent_orderTop_ge_add68
    (X Y : LaurentSeries k) (m : ℤ)
    (hX : (↑m : WithTop ℤ) ≤ X.orderTop)
    (hY : (↑m : WithTop ℤ) ≤ Y.orderTop) :
    (↑m : WithTop ℤ) ≤ (X + Y).orderTop :=
  le_trans (by simpa using min_le_min hX hY)
    HahnSeries.min_orderTop_le_orderTop_add

theorem rhoOneCap_reduced_i3_base_order68
    (epsilon : k) (C F G : LaurentSeries k)
    (hC : (↑(7 : ℤ) : WithTop ℤ) ≤ C.orderTop)
    (hF : (↑(3 : ℤ) : WithTop ℤ) ≤ F.orderTop)
    (hG : (↑(-1 : ℤ) : WithTop ℤ) ≤ G.orderTop) :
    (↑(6 : ℤ) : WithTop ℤ) ≤
      (rhoOneCapReducedI3Series68 epsilon C F G).orderTop := by
  have hCG : (↑(6 : ℤ) : WithTop ℤ) ≤ (C * G).orderTop := by
    have h := le_trans (add_le_add hC hG) HahnSeries.orderTop_add_le_mul
    norm_num at h ⊢
    exact h
  have h4CG := laurent_orderTop_ge_const_mul68 (4 : k) (C * G) 6 hCG
  have hFF : (↑(6 : ℤ) : WithTop ℤ) ≤ (F ^ 2).orderTop := by
    rw [pow_two]
    exact le_trans (add_le_add hF hF) HahnSeries.orderTop_add_le_mul
  have h2FF := laurent_orderTop_ge_const_mul68 (2 : k) (F ^ 2) 6 hFF
  have heC0 := laurent_orderTop_ge_const_mul68 epsilon C 7 hC
  have h3eC := laurent_orderTop_ge_const_mul68 (3 : k)
    (HahnSeries.C epsilon * C) 7 heC0
  dsimp only [rhoOneCapReducedI3Series68]
  have h4CG' : (↑(6 : ℤ) : WithTop ℤ) ≤ (4 * C * G).orderTop := by
    have h4 : (4 : LaurentSeries k) = HahnSeries.C (4 : k) := by
      rw [HahnSeries.C_eq_algebraMap, map_ofNat]
    rw [h4, mul_assoc]
    exact h4CG
  have h2FF' : (↑(6 : ℤ) : WithTop ℤ) ≤ (2 * F ^ 2).orderTop := by
    have h2 : (2 : LaurentSeries k) = HahnSeries.C (2 : k) := by
      rw [HahnSeries.C_eq_algebraMap, map_ofNat]
    rw [h2]
    exact h2FF
  have h3eC' : (↑(6 : ℤ) : WithTop ℤ) ≤
      (3 * HahnSeries.C epsilon * C).orderTop := by
    have h3 : (3 : LaurentSeries k) = HahnSeries.C (3 : k) := by
      rw [HahnSeries.C_eq_algebraMap, map_ofNat]
    rw [h3, mul_assoc]
    exact le_trans (WithTop.coe_le_coe.mpr (by norm_num)) h3eC
  have hfirst := laurent_orderTop_ge_add68
    (4 * C * G) (2 * F ^ 2) 6 h4CG' h2FF'
  exact laurent_orderTop_ge_add68
    (4 * C * G + 2 * F ^ 2) (3 * HahnSeries.C epsilon * C) 6
    hfirst h3eC'

theorem rhoOneCap_reduced_i4_base_order68
    (epsilon : k) (B C F G : LaurentSeries k)
    (hB : (↑(11 : ℤ) : WithTop ℤ) ≤ B.orderTop)
    (hC : (↑(7 : ℤ) : WithTop ℤ) ≤ C.orderTop)
    (hF : (↑(3 : ℤ) : WithTop ℤ) ≤ F.orderTop)
    (hG : (↑(-1 : ℤ) : WithTop ℤ) ≤ G.orderTop) :
    (↑(10 : ℤ) : WithTop ℤ) ≤
      (rhoOneCapReducedI4Series68 epsilon B C F G).orderTop := by
  have hBG : (↑(10 : ℤ) : WithTop ℤ) ≤ (B * G).orderTop := by
    exact le_trans (add_le_add hB hG) HahnSeries.orderTop_add_le_mul
  have hCF : (↑(10 : ℤ) : WithTop ℤ) ≤ (C * F).orderTop := by
    exact le_trans (add_le_add hC hF) HahnSeries.orderTop_add_le_mul
  have h4BG := laurent_orderTop_ge_const_mul68 (4 : k) (B * G) 10 hBG
  have h4CF := laurent_orderTop_ge_const_mul68 (4 : k) (C * F) 10 hCF
  have heB := laurent_orderTop_ge_const_mul68 epsilon B 11 hB
  have h3eB := laurent_orderTop_ge_const_mul68 (3 : k)
    (HahnSeries.C epsilon * B) 11 heB
  dsimp only [rhoOneCapReducedI4Series68]
  have h4BG' : (↑(10 : ℤ) : WithTop ℤ) ≤ (4 * B * G).orderTop := by
    have h4 : (4 : LaurentSeries k) = HahnSeries.C (4 : k) := by
      rw [HahnSeries.C_eq_algebraMap, map_ofNat]
    rw [h4, mul_assoc]
    exact h4BG
  have h4CF' : (↑(10 : ℤ) : WithTop ℤ) ≤ (4 * C * F).orderTop := by
    have h4 : (4 : LaurentSeries k) = HahnSeries.C (4 : k) := by
      rw [HahnSeries.C_eq_algebraMap, map_ofNat]
    rw [h4, mul_assoc]
    exact h4CF
  have h3eB' : (↑(10 : ℤ) : WithTop ℤ) ≤
      (3 * HahnSeries.C epsilon * B).orderTop := by
    have h3 : (3 : LaurentSeries k) = HahnSeries.C (3 : k) := by
      rw [HahnSeries.C_eq_algebraMap, map_ofNat]
    rw [h3, mul_assoc]
    exact le_trans (WithTop.coe_le_coe.mpr (by norm_num)) h3eB
  have hfirst := laurent_orderTop_ge_add68
    (4 * B * G) (4 * C * F) 10 h4BG' h4CF'
  exact laurent_orderTop_ge_add68
    (4 * B * G + 4 * C * F) (3 * HahnSeries.C epsilon * B) 10
    hfirst h3eB'

/-- A constant plus a series of order at least twelve cannot equal a
series already known to start in degree six unless the constant vanishes. -/
theorem laurent_constant_plus_order_twelve_gain68
    (R N : LaurentSeries k) (c : k)
    (hR6 : (↑(6 : ℤ) : WithTop ℤ) ≤ R.orderTop)
    (hN12 : (↑(12 : ℤ) : WithTop ℤ) ≤ N.orderTop)
    (heq : R = HahnSeries.C c + N) :
    (↑(12 : ℤ) : WithTop ℤ) ≤ R.orderTop := by
  have hR0 : R.coeff 0 = 0 := HahnSeries.coeff_eq_zero_of_lt_orderTop
    (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hR6)
  have hN0 : N.coeff 0 = 0 := HahnSeries.coeff_eq_zero_of_lt_orderTop
    (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hN12)
  have hc := congrArg (fun X : LaurentSeries k => X.coeff 0) heq
  rw [hR0, HahnSeries.coeff_add, hN0] at hc
  simp [HahnSeries.C_apply] at hc
  subst c
  rw [heq]
  simpa using hN12

end AlignedSquareTerminalGBoundaryCapSourceOrderGains68

end Max11DegreeRoutes
