import Sol68ScaleTwoAlignedSquareTerminalGBoundaryCapPostRestorationNineBackwireScratch

/-! # Indexed clean-window recurrence and its first nonlinear correction -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareTerminalGBoundaryCapCleanWindowIndexed68

variable {k : Type*} [Field k] [CharZero k]

local instance alignedSquareCapCleanWindowIndexedHahnCharZero68 :
    CharZero (LaurentSeries k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℤ))

/-- The exact reduced-I₃ source identity after its order-twelve gain has
deleted the otherwise possible constant term. -/
theorem rhoOneCap_reduced_i3_exact_of_source_factor68
    (gamma epsilon i3 : k) (A B C CT F G : LaurentSeries k)
    (hA : (↑(-2 : ℤ) : WithTop ℤ) ≤ A.orderTop)
    (hB : (↑(11 : ℤ) : WithTop ℤ) ≤ B.orderTop)
    (hC : (0 : WithTop ℤ) ≤ C.orderTop)
    (hF : (↑(3 : ℤ) : WithTop ℤ) ≤ F.orderTop)
    (hR3 : (↑(12 : ℤ) : WithTop ℤ) ≤
      (rhoOneCapReducedI3Series68 epsilon CT F G).orderTop)
    (hCTeq : CT = C + HahnSeries.C ((3 / 2 : k) * gamma))
    (hfactor : rhoOneI3CapFactored68 (HahnSeries.C gamma)
      (HahnSeries.C epsilon) A B C F G = HahnSeries.C i3) :
    rhoOneCapReducedI3Series68 epsilon CT F G =
      HahnSeries.C (4 / 3 : k) * (A * B * F) +
        HahnSeries.C (4 / 3 : k) * (B ^ 2 * C) +
        HahnSeries.C gamma * B ^ 2 := by
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
  have hAB : (↑(9 : ℤ) : WithTop ℤ) ≤ (A * B).orderTop :=
    le_trans (by
      have h := add_le_add hA hB
      norm_num at h
      exact h) HahnSeries.orderTop_add_le_mul
  have hABFraw := le_trans (add_le_add hAB hF)
    (HahnSeries.orderTop_add_le_mul (x := A * B) (y := F))
  have hABF : (↑(12 : ℤ) : WithTop ℤ) ≤ (A * B * F).orderTop := by
    convert hABFraw using 1 <;> norm_num
  have hBB : (↑(22 : ℤ) : WithTop ℤ) ≤ (B ^ 2).orderTop := by
    rw [pow_two]
    exact le_trans (add_le_add hB hB) HahnSeries.orderTop_add_le_mul
  have hBBC : (↑(22 : ℤ) : WithTop ℤ) ≤ (B ^ 2 * C).orderTop :=
    le_trans (add_le_add hBB hC) HahnSeries.orderTop_add_le_mul
  have hN1 := laurent_orderTop_ge_const_mul68 (4 / 3 : k) (A * B * F) 12 hABF
  have hN2high := laurent_orderTop_ge_const_mul68 (4 / 3 : k) (B ^ 2 * C) 22 hBBC
  have hN2 : (↑(12 : ℤ) : WithTop ℤ) ≤
      (HahnSeries.C (4 / 3 : k) * (B ^ 2 * C)).orderTop :=
    le_trans (WithTop.coe_le_coe.mpr (by norm_num)) hN2high
  have hN3high := laurent_orderTop_ge_const_mul68 gamma (B ^ 2) 22 hBB
  have hN3 : (↑(12 : ℤ) : WithTop ℤ) ≤
      (HahnSeries.C gamma * B ^ 2).orderTop :=
    le_trans (WithTop.coe_le_coe.mpr (by norm_num)) hN3high
  have hNorder : (↑(12 : ℤ) : WithTop ℤ) ≤ N.orderTop := by
    dsimp only [N]
    exact laurent_orderTop_ge_add68 _ _ 12
      (laurent_orderTop_ge_add68 _ _ 12 hN1 hN2) hN3
  have hR30 : (rhoOneCapReducedI3Series68 epsilon CT F G).coeff 0 = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hR3)
  have hN0 : N.coeff 0 = 0 := HahnSeries.coeff_eq_zero_of_lt_orderTop
    (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hNorder)
  have hc0 : (HahnSeries.C c : LaurentSeries k).coeff 0 = c := by
    simp [HahnSeries.C_apply]
  have heq0 := congrArg (fun X : LaurentSeries k => X.coeff 0) heq
  rw [HahnSeries.coeff_add, hR30, hc0, hN0] at heq0
  have hc : c = 0 := by simpa using heq0.symm
  rw [hc] at heq
  simp only [map_zero, zero_add] at heq
  simpa only [N] using heq

/-- Exact reduced-I₄ source identity, retained globally rather than one
coefficient at a time. -/
theorem rhoOneCap_reduced_i4_exact_of_source_factor68
    (gamma epsilon : k) (B C CT F G : LaurentSeries k)
    (hCTeq : CT = C + HahnSeries.C ((3 / 2 : k) * gamma))
    (hfactor : rhoOneI4ZeroFactored68 (HahnSeries.C gamma)
      (HahnSeries.C epsilon) B C F G = 0) :
    rhoOneCapReducedI4Series68 epsilon B CT F G =
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

/-- Global corrected transport.  This is the indexed replacement for the
six manual T₁₀,...,T₁₅ packets. -/
theorem rhoOneCap_corrected_transport_global68
    (gamma epsilon : k) (A B C CT F G : LaurentSeries k)
    (hCTeq : CT = C + HahnSeries.C ((3 / 2 : k) * gamma))
    (hR3eq : rhoOneCapReducedI3Series68 epsilon CT F G =
      HahnSeries.C (4 / 3 : k) * (A * B * F) +
        HahnSeries.C (4 / 3 : k) * (B ^ 2 * C) +
        HahnSeries.C gamma * B ^ 2)
    (hR4eq : rhoOneCapReducedI4Series68 epsilon B CT F G =
      HahnSeries.C (4 / 9 : k) * B ^ 3) :
    F * (rhoOneCapCoordinateDefectSeries68 B CT F +
        HahnSeries.C (2 / 3 : k) * (A * B ^ 2)) =
      HahnSeries.C (1 / 2 * gamma) * B ^ 3 -
        HahnSeries.C (4 / 9 : k) * (CT * B ^ 3) := by
  have hc := rhoOneCap_reduced_convolution_identity68 epsilon B CT F G
  rw [hR3eq, hR4eq] at hc
  rw [hCTeq] at hc ⊢
  have h43 : HahnSeries.C (4 / 3 : k) = (4 / 3 : LaurentSeries k) := by
    rw [HahnSeries.C_eq_algebraMap, map_div₀, map_ofNat, map_ofNat]
  have h49 : HahnSeries.C (4 / 9 : k) = (4 / 9 : LaurentSeries k) := by
    rw [HahnSeries.C_eq_algebraMap, map_div₀, map_ofNat, map_ofNat]
  have h23 : HahnSeries.C (2 / 3 : k) = (2 / 3 : LaurentSeries k) := by
    rw [HahnSeries.C_eq_algebraMap, map_div₀, map_ofNat, map_ofNat]
  have h32g : HahnSeries.C ((3 / 2 : k) * gamma) =
      (3 / 2 : LaurentSeries k) * HahnSeries.C gamma := by
    rw [map_mul]
    congr 1
    rw [map_div₀, map_ofNat, map_ofNat]
  have h12g : HahnSeries.C ((1 / 2 : k) * gamma) =
      (1 / 2 : LaurentSeries k) * HahnSeries.C gamma := by
    rw [map_mul]
    congr 1
    rw [map_div₀, map_one, map_ofNat]
  rw [h43, h49, h32g] at hc
  rw [h49, h23, h32g, h12g]
  simp only [rhoOneCapCoordinateDefectSeries68] at hc ⊢
  linear_combination (1 / 2 : LaurentSeries k) * hc

/-- Indexed clean-window gain.  All coefficients T₆,...,T₁₅ of the
corrected defect vanish at once. -/
theorem rhoOneCap_corrected_transport_order_thirty68
    (gamma : k) (A B CT F : LaurentSeries k)
    (hA : (↑(-2 : ℤ) : WithTop ℤ) ≤ A.orderTop)
    (hB : (↑(11 : ℤ) : WithTop ℤ) ≤ B.orderTop)
    (hCT : (↑(7 : ℤ) : WithTop ℤ) ≤ CT.orderTop)
    (hF : (↑(3 : ℤ) : WithTop ℤ) ≤ F.orderTop)
    (hf3 : F.coeff 3 ≠ 0)
    (hH : (↑(20 : ℤ) : WithTop ℤ) ≤
      (rhoOneCapCoordinateDefectSeries68 B CT F).orderTop)
    (hglobal : F * (rhoOneCapCoordinateDefectSeries68 B CT F +
        HahnSeries.C (2 / 3 : k) * (A * B ^ 2)) =
      HahnSeries.C (1 / 2 * gamma) * B ^ 3 -
        HahnSeries.C (4 / 9 : k) * (CT * B ^ 3)) :
    (↑(30 : ℤ) : WithTop ℤ) ≤
      (rhoOneCapCoordinateDefectSeries68 B CT F +
        HahnSeries.C (2 / 3 : k) * (A * B ^ 2)).orderTop := by
  let K := rhoOneCapCoordinateDefectSeries68 B CT F +
    HahnSeries.C (2 / 3 : k) * (A * B ^ 2)
  let R := HahnSeries.C (1 / 2 * gamma) * B ^ 3 -
    HahnSeries.C (4 / 9 : k) * (CT * B ^ 3)
  have hBB : (↑(22 : ℤ) : WithTop ℤ) ≤ (B ^ 2).orderTop := by
    rw [pow_two]
    exact le_trans (add_le_add hB hB) HahnSeries.orderTop_add_le_mul
  have hAB2 : (↑(20 : ℤ) : WithTop ℤ) ≤ (A * B ^ 2).orderTop :=
    le_trans (by
      have h := add_le_add hA hBB
      norm_num at h
      exact h) HahnSeries.orderTop_add_le_mul
  have hscaled := laurent_orderTop_ge_const_mul68 (2 / 3 : k) (A * B ^ 2) 20 hAB2
  have hK20 : (↑(20 : ℤ) : WithTop ℤ) ≤ K.orderTop := by
    dsimp only [K]
    exact laurent_orderTop_ge_add68 _ _ 20 hH hscaled
  have hBBB : (↑(33 : ℤ) : WithTop ℤ) ≤ (B ^ 3).orderTop := by
    rw [show B ^ 3 = B ^ 2 * B by ring]
    exact le_trans (by
      have h := add_le_add hBB hB
      norm_num at h
      exact h) HahnSeries.orderTop_add_le_mul
  have hfirst := laurent_orderTop_ge_const_mul68 (1 / 2 * gamma) (B ^ 3) 33 hBBB
  have hCTBBB : (↑(40 : ℤ) : WithTop ℤ) ≤ (CT * B ^ 3).orderTop :=
    le_trans (by
      have h := add_le_add hCT hBBB
      norm_num at h
      exact h) HahnSeries.orderTop_add_le_mul
  have hsecondHigh := laurent_orderTop_ge_const_mul68 (4 / 9 : k)
    (CT * B ^ 3) 40 hCTBBB
  have hsecond : (↑(33 : ℤ) : WithTop ℤ) ≤
      (HahnSeries.C (4 / 9 : k) * (CT * B ^ 3)).orderTop :=
    le_trans (WithTop.coe_le_coe.mpr (by norm_num)) hsecondHigh
  have hR33 : (↑(33 : ℤ) : WithTop ℤ) ≤ R.orderTop := by
    dsimp only [R]
    exact le_trans (by simpa using min_le_min hfirst hsecond)
      HahnSeries.min_orderTop_le_orderTop_sub
  have hgain : ∀ r : ℕ, r ≤ 10 →
      (↑(20 + (r : ℤ)) : WithTop ℤ) ≤ K.orderTop := by
    intro r hr
    induction r with
    | zero => simpa using hK20
    | succ r ih =>
        have hr9 : r ≤ 9 := by omega
        have hKr := ih (by omega)
        have hFK := laurent_coeff_mul_lower68 F K 3 (20 + (r : ℤ)) hF hKr
        have hRzero : R.coeff (23 + (r : ℤ)) = 0 :=
          HahnSeries.coeff_eq_zero_of_lt_orderTop
            (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by omega)) hR33)
        have hc : (F * K).coeff (23 + (r : ℤ)) =
            R.coeff (23 + (r : ℤ)) := by
          simpa only [K, R] using
            congrArg (fun X : LaurentSeries k => X.coeff (23 + (r : ℤ))) hglobal
        rw [hRzero] at hc
        have hindex : 3 + (20 + (r : ℤ)) = 23 + (r : ℤ) := by omega
        rw [hindex] at hFK
        rw [hFK] at hc
        have hkzero : K.coeff (20 + (r : ℤ)) = 0 := by
          exact (mul_eq_zero.mp hc).resolve_left hf3
        have hnext := laurent_orderTop_ge_succ_of_coeff_zero68 K
          (20 + (r : ℤ)) hKr hkzero
        simpa only [Nat.cast_succ, add_assoc] using hnext
  exact hgain 10 (by norm_num)

/-- Terminal clean endpoint T₁₅, obtained by one indexed induction. -/
theorem rhoOneCap_corrected_transport_endpoint_fifteen68
    (gamma : k) (A B CT F : LaurentSeries k)
    (hA : (↑(-2 : ℤ) : WithTop ℤ) ≤ A.orderTop)
    (hB : (↑(11 : ℤ) : WithTop ℤ) ≤ B.orderTop)
    (hCT : (↑(7 : ℤ) : WithTop ℤ) ≤ CT.orderTop)
    (hF : (↑(3 : ℤ) : WithTop ℤ) ≤ F.orderTop)
    (hf3 : F.coeff 3 ≠ 0)
    (hH : (↑(20 : ℤ) : WithTop ℤ) ≤
      (rhoOneCapCoordinateDefectSeries68 B CT F).orderTop)
    (hglobal : F * (rhoOneCapCoordinateDefectSeries68 B CT F +
        HahnSeries.C (2 / 3 : k) * (A * B ^ 2)) =
      HahnSeries.C (1 / 2 * gamma) * B ^ 3 -
        HahnSeries.C (4 / 9 : k) * (CT * B ^ 3)) :
    (rhoOneCapCoordinateDefectSeries68 B CT F).coeff 29 =
      -(2 / 3 : k) * (A * B ^ 2).coeff 29 := by
  have horder := rhoOneCap_corrected_transport_order_thirty68 gamma A B CT F
    hA hB hCT hF hf3 hH hglobal
  have hz : (rhoOneCapCoordinateDefectSeries68 B CT F +
      HahnSeries.C (2 / 3 : k) * (A * B ^ 2)).coeff 29 = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
    (show (↑(29 : ℤ) : WithTop ℤ) < _ from
      lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) horder)
  rw [HahnSeries.coeff_add, HahnSeries.C_apply,
    HahnSeries.coeff_single_zero_mul] at hz
  linear_combination hz

/-- The first nonlinear row T₁₆.  Its correction is exactly the degree-33
`gamma B³` face; the `CT B³` face still starts in degree forty. -/
theorem rhoOneCap_corrected_transport_first_nonlinear_sixteen68
    (gamma : k) (A B CT F : LaurentSeries k)
    (hA : (↑(-2 : ℤ) : WithTop ℤ) ≤ A.orderTop)
    (hB : (↑(11 : ℤ) : WithTop ℤ) ≤ B.orderTop)
    (hCT : (↑(7 : ℤ) : WithTop ℤ) ≤ CT.orderTop)
    (hF : (↑(3 : ℤ) : WithTop ℤ) ≤ F.orderTop)
    (hf3 : F.coeff 3 ≠ 0)
    (hH : (↑(20 : ℤ) : WithTop ℤ) ≤
      (rhoOneCapCoordinateDefectSeries68 B CT F).orderTop)
    (hglobal : F * (rhoOneCapCoordinateDefectSeries68 B CT F +
        HahnSeries.C (2 / 3 : k) * (A * B ^ 2)) =
      HahnSeries.C (1 / 2 * gamma) * B ^ 3 -
        HahnSeries.C (4 / 9 : k) * (CT * B ^ 3)) :
    2 * F.coeff 3 *
        ((rhoOneCapCoordinateDefectSeries68 B CT F).coeff 30 +
          (2 / 3 : k) * (A * B ^ 2).coeff 30) =
      gamma * B.coeff 11 ^ 3 := by
  let K := rhoOneCapCoordinateDefectSeries68 B CT F +
    HahnSeries.C (2 / 3 : k) * (A * B ^ 2)
  have hK := rhoOneCap_corrected_transport_order_thirty68 gamma A B CT F
    hA hB hCT hF hf3 hH hglobal
  have hK' : (↑(30 : ℤ) : WithTop ℤ) ≤ K.orderTop := by
    simpa only [K] using hK
  have hFK := laurent_coeff_mul_lower68 F K 3 30 hF hK'
  norm_num at hFK
  have hBB : (↑(22 : ℤ) : WithTop ℤ) ≤ (B ^ 2).orderTop := by
    rw [pow_two]
    exact le_trans (add_le_add hB hB) HahnSeries.orderTop_add_le_mul
  have hBBlead := laurent_coeff_mul_lower68 B B 11 11 hB hB
  norm_num at hBBlead
  have hBBBlead := laurent_coeff_mul_lower68 (B ^ 2) B 22 11 hBB hB
  norm_num at hBBBlead
  rw [pow_two, hBBlead] at hBBBlead
  have hBBBlead' : (B ^ 3).coeff 33 = B.coeff 11 ^ 3 := by
    rw [show B ^ 3 = B * B * B by ring]
    rw [hBBBlead]
    ring
  have hCTBBB : (↑(40 : ℤ) : WithTop ℤ) ≤ (CT * B ^ 3).orderTop := by
    have hBBB : (↑(33 : ℤ) : WithTop ℤ) ≤ (B ^ 3).orderTop := by
      rw [show B ^ 3 = B ^ 2 * B by ring]
      exact le_trans (by
        have h := add_le_add hBB hB
        norm_num at h
        exact h) HahnSeries.orderTop_add_le_mul
    exact le_trans (by
      have h := add_le_add hCT hBBB
      norm_num at h
      exact h)
      HahnSeries.orderTop_add_le_mul
  have hCTzero : (CT * B ^ 3).coeff 33 = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hCTBBB)
  have hc := congrArg (fun X : LaurentSeries k => X.coeff 33) hglobal
  have hscale (s : k) (X : LaurentSeries k) (r : ℤ) :
      (HahnSeries.C s * X).coeff r = s * X.coeff r := by
    rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]
  rw [hFK, HahnSeries.coeff_sub, hscale, hBBBlead', hscale, hCTzero,
    mul_zero] at hc
  dsimp only [K] at hc
  rw [HahnSeries.coeff_add, HahnSeries.C_apply,
    HahnSeries.coeff_single_zero_mul] at hc
  linear_combination 2 * hc

end AlignedSquareTerminalGBoundaryCapCleanWindowIndexed68

end Max11DegreeRoutes
