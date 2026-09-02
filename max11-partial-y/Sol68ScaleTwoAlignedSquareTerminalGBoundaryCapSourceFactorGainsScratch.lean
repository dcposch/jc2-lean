import Sol68ScaleTwoAlignedSquareTerminalGBoundaryCapSourceOrderGainsScratch

/-! # Global source-factor realizations of the reduced-integral gains -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareTerminalGBoundaryCapSourceFactorGains68

variable {k : Type*} [Field k] [CharZero k]

local instance alignedSquareTerminalGBoundaryCapSourceFactorGainsHahnCharZero68 :
    CharZero (LaurentSeries k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℤ))

theorem rhoOneCap_reduced_i3_order_twelve_of_source_factor68
    (gamma epsilon i3 : k)
    (A B C CT F G : LaurentSeries k)
    (hA : (↑(-2 : ℤ) : WithTop ℤ) ≤ A.orderTop)
    (hB : (↑(11 : ℤ) : WithTop ℤ) ≤ B.orderTop)
    (hC : (0 : WithTop ℤ) ≤ C.orderTop)
    (hCT : (↑(7 : ℤ) : WithTop ℤ) ≤ CT.orderTop)
    (hF : (↑(3 : ℤ) : WithTop ℤ) ≤ F.orderTop)
    (hG : (↑(-1 : ℤ) : WithTop ℤ) ≤ G.orderTop)
    (hCTeq : CT = C + HahnSeries.C ((3 / 2 : k) * gamma))
    (hfactor : rhoOneI3CapFactored68 (HahnSeries.C gamma)
      (HahnSeries.C epsilon) A B C F G = HahnSeries.C i3) :
    (↑(12 : ℤ) : WithTop ℤ) ≤
      (rhoOneCapReducedI3Series68 epsilon CT F G).orderTop := by
  let N : LaurentSeries k :=
    HahnSeries.C (4 / 3 : k) * (A * B * F) +
      HahnSeries.C (4 / 3 : k) * (B ^ 2 * C) +
      HahnSeries.C gamma * B ^ 2
  let c : k := (3 / 2 : k) * i3 + (9 / 2 : k) * epsilon * gamma
  have hAB : (↑(9 : ℤ) : WithTop ℤ) ≤ (A * B).orderTop := by
    have h := le_trans (add_le_add hA hB) HahnSeries.orderTop_add_le_mul
    norm_num at h ⊢
    exact h
  have hABF : (↑(12 : ℤ) : WithTop ℤ) ≤ (A * B * F).orderTop := by
    exact le_trans (add_le_add hAB hF) HahnSeries.orderTop_add_le_mul
  have hBB : (↑(22 : ℤ) : WithTop ℤ) ≤ (B ^ 2).orderTop := by
    rw [pow_two]
    exact le_trans (add_le_add hB hB) HahnSeries.orderTop_add_le_mul
  have hBBC : (↑(22 : ℤ) : WithTop ℤ) ≤ (B ^ 2 * C).orderTop := by
    exact le_trans (add_le_add hBB hC) HahnSeries.orderTop_add_le_mul
  have hN1 := laurent_orderTop_ge_const_mul68 (4 / 3 : k) (A * B * F) 12 hABF
  have hN2high := laurent_orderTop_ge_const_mul68 (4 / 3 : k) (B ^ 2 * C) 22 hBBC
  have hN2 : (↑(12 : ℤ) : WithTop ℤ) ≤
      (HahnSeries.C (4 / 3 : k) * (B ^ 2 * C)).orderTop :=
    le_trans (WithTop.coe_le_coe.mpr (by norm_num)) hN2high
  have hN3high := laurent_orderTop_ge_const_mul68 gamma (B ^ 2) 22 hBB
  have hN3 : (↑(12 : ℤ) : WithTop ℤ) ≤
      (HahnSeries.C gamma * B ^ 2).orderTop :=
    le_trans (WithTop.coe_le_coe.mpr (by norm_num)) hN3high
  have hN12 : (↑(12 : ℤ) : WithTop ℤ) ≤ N.orderTop := by
    dsimp only [N]
    exact laurent_orderTop_ge_add68 _ _ 12
      (laurent_orderTop_ge_add68 _ _ 12 hN1 hN2) hN3
  have hR6 := rhoOneCap_reduced_i3_base_order68 epsilon CT F G hCT hF hG
  have heq : rhoOneCapReducedI3Series68 epsilon CT F G =
      HahnSeries.C c + N := by
    dsimp only [rhoOneCapReducedI3Series68, N, c]
    rw [hCTeq]
    rw [rhoOneI3CapFactored68] at hfactor
    have hC32 : HahnSeries.C (3 / 2 : k) =
        (3 / 2 : LaurentSeries k) := by
      rw [map_div₀, map_ofNat, map_ofNat]
    have hC92 : HahnSeries.C (9 / 2 : k) =
        (9 / 2 : LaurentSeries k) := by
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
    have h43 : HahnSeries.C (4 / 3 : k) =
        (4 / 3 : LaurentSeries k) := by
      rw [HahnSeries.C_eq_algebraMap, map_div₀, map_ofNat, map_ofNat]
    rw [h43]
    linear_combination (3 / 2 : LaurentSeries k) * hfactor
  exact laurent_constant_plus_order_twelve_gain68 _ N c hR6 hN12 heq

theorem rhoOneCap_reduced_i4_order_sixteen_of_source_factor68
    (gamma epsilon : k) (B C CT F G : LaurentSeries k)
    (hB : (↑(11 : ℤ) : WithTop ℤ) ≤ B.orderTop)
    (hCT : (↑(7 : ℤ) : WithTop ℤ) ≤ CT.orderTop)
    (hF : (↑(3 : ℤ) : WithTop ℤ) ≤ F.orderTop)
    (hG : (↑(-1 : ℤ) : WithTop ℤ) ≤ G.orderTop)
    (hCTeq : CT = C + HahnSeries.C ((3 / 2 : k) * gamma))
    (hfactor : rhoOneI4ZeroFactored68 (HahnSeries.C gamma)
      (HahnSeries.C epsilon) B C F G = 0) :
    (↑(16 : ℤ) : WithTop ℤ) ≤
      (rhoOneCapReducedI4Series68 epsilon B CT F G).orderTop := by
  have hBB : (↑(22 : ℤ) : WithTop ℤ) ≤ (B ^ 2).orderTop := by
    rw [pow_two]
    exact le_trans (add_le_add hB hB) HahnSeries.orderTop_add_le_mul
  have hBBB : (↑(33 : ℤ) : WithTop ℤ) ≤ (B ^ 3).orderTop := by
    rw [show B ^ 3 = B ^ 2 * B by ring]
    exact le_trans (add_le_add hBB hB) HahnSeries.orderTop_add_le_mul
  have hscaledHigh := laurent_orderTop_ge_const_mul68 (4 / 9 : k) (B ^ 3) 33 hBBB
  have hscaled : (↑(16 : ℤ) : WithTop ℤ) ≤
      (HahnSeries.C (4 / 9 : k) * B ^ 3).orderTop :=
    le_trans (WithTop.coe_le_coe.mpr (by norm_num)) hscaledHigh
  have heq : rhoOneCapReducedI4Series68 epsilon B CT F G =
      HahnSeries.C (4 / 9 : k) * B ^ 3 := by
    dsimp only [rhoOneCapReducedI4Series68]
    rw [hCTeq]
    rw [rhoOneI4ZeroFactored68] at hfactor
    have hC32 : HahnSeries.C (3 / 2 : k) =
        (3 / 2 : LaurentSeries k) := by
      rw [map_div₀, map_ofNat, map_ofNat]
    have hgamma : HahnSeries.C ((3 / 2 : k) * gamma) =
        (3 / 2 : LaurentSeries k) * HahnSeries.C gamma := by
      rw [map_mul, hC32]
    rw [hgamma]
    have h49 : HahnSeries.C (4 / 9 : k) =
        (4 / 9 : LaurentSeries k) := by
      rw [HahnSeries.C_eq_algebraMap, map_div₀, map_ofNat, map_ofNat]
    rw [h49]
    linear_combination (3 / 2 : LaurentSeries k) * hfactor
  rw [heq]
  exact hscaled

end AlignedSquareTerminalGBoundaryCapSourceFactorGains68

end Max11DegreeRoutes
