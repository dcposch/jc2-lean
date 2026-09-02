import Sol68ScaleTwoAlignedSquareTerminalGBoundaryCapCleanEndpointBackwireScratch

/-! # Exact split at the first nonlinear corrected-defect row -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareTerminalGBoundaryCapT16Split68

variable {k : Type*} [Field k] [CharZero k]

local instance alignedSquareCapT16SplitHahnCharZero68 :
    CharZero (LaurentSeries k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℤ))

def rhoOneCapCorrectedDefect68
    (A B CT F : LaurentSeries k) : LaurentSeries k :=
  rhoOneCapCoordinateDefectSeries68 B CT F +
    HahnSeries.C (2 / 3 : k) * (A * B ^ 2)

/-- On the nonzero-gamma side, T₁₆ is nonzero and the corrected defect
has exact order thirty. -/
theorem rhoOneCap_corrected_transport_gamma_ne_zero68
    (gamma : k) (A B CT F : LaurentSeries k)
    (hK30 : (↑(30 : ℤ) : WithTop ℤ) ≤
      (rhoOneCapCorrectedDefect68 A B CT F).orderTop)
    (hf3 : F.coeff 3 ≠ 0) (hb11 : B.coeff 11 ≠ 0)
    (hgamma : gamma ≠ 0)
    (hT16 : 2 * F.coeff 3 *
        ((rhoOneCapCoordinateDefectSeries68 B CT F).coeff 30 +
          (2 / 3 : k) * (A * B ^ 2).coeff 30) =
      gamma * B.coeff 11 ^ 3) :
    (rhoOneCapCorrectedDefect68 A B CT F).coeff 30 ≠ 0 ∧
      (rhoOneCapCorrectedDefect68 A B CT F).orderTop =
        (↑(30 : ℤ) : WithTop ℤ) := by
  have hrhs : gamma * B.coeff 11 ^ 3 ≠ 0 :=
    mul_ne_zero hgamma (pow_ne_zero 3 hb11)
  have hKcoeff : (rhoOneCapCorrectedDefect68 A B CT F).coeff 30 ≠ 0 := by
    intro hz
    have hz' : (rhoOneCapCoordinateDefectSeries68 B CT F).coeff 30 +
        (2 / 3 : k) * (A * B ^ 2).coeff 30 = 0 := by
      simpa only [rhoOneCapCorrectedDefect68, HahnSeries.coeff_add,
        HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul] using hz
    rw [hz', mul_zero] at hT16
    exact hrhs hT16.symm
  refine ⟨hKcoeff, le_antisymm ?_ hK30⟩
  exact HahnSeries.orderTop_le_of_coeff_ne_zero hKcoeff

/-- If gamma vanishes, the degree-33 face disappears and the same indexed
argument raises the corrected defect from order thirty to order thirty-seven,+just before `CT B³` enters at degree forty. -/
theorem rhoOneCap_corrected_transport_gamma_zero_order_thirty_seven68
    (A B CT F : LaurentSeries k)
    (hB : (↑(11 : ℤ) : WithTop ℤ) ≤ B.orderTop)
    (hCT : (↑(7 : ℤ) : WithTop ℤ) ≤ CT.orderTop)
    (hF : (↑(3 : ℤ) : WithTop ℤ) ≤ F.orderTop)
    (hf3 : F.coeff 3 ≠ 0)
    (hK30 : (↑(30 : ℤ) : WithTop ℤ) ≤
      (rhoOneCapCorrectedDefect68 A B CT F).orderTop)
    (hglobal : F * rhoOneCapCorrectedDefect68 A B CT F =
      -HahnSeries.C (4 / 9 : k) * (CT * B ^ 3)) :
    (↑(37 : ℤ) : WithTop ℤ) ≤
      (rhoOneCapCorrectedDefect68 A B CT F).orderTop := by
  let K := rhoOneCapCorrectedDefect68 A B CT F
  let R := -HahnSeries.C (4 / 9 : k) * (CT * B ^ 3)
  have hBB : (↑(22 : ℤ) : WithTop ℤ) ≤ (B ^ 2).orderTop := by
    rw [pow_two]
    exact le_trans (add_le_add hB hB) HahnSeries.orderTop_add_le_mul
  have hBBB : (↑(33 : ℤ) : WithTop ℤ) ≤ (B ^ 3).orderTop := by
    rw [show B ^ 3 = B ^ 2 * B by ring]
    have h := add_le_add hBB hB
    norm_num at h
    exact le_trans h HahnSeries.orderTop_add_le_mul
  have hCTBBB : (↑(40 : ℤ) : WithTop ℤ) ≤ (CT * B ^ 3).orderTop := by
    have h := add_le_add hCT hBBB
    norm_num at h
    exact le_trans h HahnSeries.orderTop_add_le_mul
  have hR40 : (↑(40 : ℤ) : WithTop ℤ) ≤ R.orderTop := by
    dsimp only [R]
    have hs := laurent_orderTop_ge_const_mul68 (-(4 / 9 : k))
      (CT * B ^ 3) 40 hCTBBB
    simpa only [map_neg, HahnSeries.C_apply, neg_mul] using hs
  have hgain : ∀ r : ℕ, r ≤ 7 →
      (↑(30 + (r : ℤ)) : WithTop ℤ) ≤ K.orderTop := by
    intro r hr
    induction r with
    | zero =>
        dsimp only [K]
        convert hK30 using 1 <;> norm_num
    | succ r ih =>
        have hr6 : r ≤ 6 := by omega
        have hKr := ih (by omega)
        have hFK := laurent_coeff_mul_lower68 F K 3 (30 + (r : ℤ)) hF hKr
        have hRzero : R.coeff (33 + (r : ℤ)) = 0 :=
          HahnSeries.coeff_eq_zero_of_lt_orderTop
            (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by omega)) hR40)
        have hc : (F * K).coeff (33 + (r : ℤ)) =
            R.coeff (33 + (r : ℤ)) := by
          simpa only [K, R] using
            congrArg (fun X : LaurentSeries k => X.coeff (33 + (r : ℤ))) hglobal
        rw [hRzero] at hc
        have hindex : 3 + (30 + (r : ℤ)) = 33 + (r : ℤ) := by omega
        rw [hindex] at hFK
        rw [hFK] at hc
        have hkzero : K.coeff (30 + (r : ℤ)) = 0 :=
          (mul_eq_zero.mp hc).resolve_left hf3
        have hnext := laurent_orderTop_ge_succ_of_coeff_zero68 K
          (30 + (r : ℤ)) hKr hkzero
        simpa only [Nat.cast_succ, add_assoc] using hnext
  exact hgain 7 (by norm_num)

/-- The first surviving row on the gamma-zero side is the degree-40
`CT B³` face. -/
theorem rhoOneCap_corrected_transport_gamma_zero_CT_correction68
    (A B CT F : LaurentSeries k)
    (hB : (↑(11 : ℤ) : WithTop ℤ) ≤ B.orderTop)
    (hCT : (↑(7 : ℤ) : WithTop ℤ) ≤ CT.orderTop)
    (hF : (↑(3 : ℤ) : WithTop ℤ) ≤ F.orderTop)
    (hK37 : (↑(37 : ℤ) : WithTop ℤ) ≤
      (rhoOneCapCorrectedDefect68 A B CT F).orderTop)
    (hglobal : F * rhoOneCapCorrectedDefect68 A B CT F =
      -HahnSeries.C (4 / 9 : k) * (CT * B ^ 3)) :
    9 * F.coeff 3 * (rhoOneCapCorrectedDefect68 A B CT F).coeff 37 =
      -4 * CT.coeff 7 * B.coeff 11 ^ 3 := by
  let K := rhoOneCapCorrectedDefect68 A B CT F
  have hK37' : (↑(37 : ℤ) : WithTop ℤ) ≤ K.orderTop := by
    simpa only [K] using hK37
  have hFK := laurent_coeff_mul_lower68 F K 3 37 hF hK37'
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
    rw [show B ^ 3 = B * B * B by ring, hBBBlead]
    ring
  have hBBB : (↑(33 : ℤ) : WithTop ℤ) ≤ (B ^ 3).orderTop := by
    rw [show B ^ 3 = B ^ 2 * B by ring]
    have h := add_le_add hBB hB
    norm_num at h
    exact le_trans h HahnSeries.orderTop_add_le_mul
  have hCTB := laurent_coeff_mul_lower68 CT (B ^ 3) 7 33 hCT hBBB
  norm_num at hCTB
  have hc := congrArg (fun X : LaurentSeries k => X.coeff 40) hglobal
  have hscale (s : k) (X : LaurentSeries k) (r : ℤ) :
      (HahnSeries.C s * X).coeff r = s * X.coeff r := by
    rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]
  have hneg : (-HahnSeries.C (4 / 9 : k) : LaurentSeries k) =
      HahnSeries.C (-(4 / 9 : k)) := by rw [map_neg]
  rw [hFK, hneg, hscale, hCTB, hBBBlead'] at hc
  dsimp only [K] at hc
  linear_combination 9 * hc

/-- With nonzero CT[7], B[11], and F[3], the gamma-zero corrected defect
has exact order thirty-seven. -/
theorem rhoOneCap_corrected_transport_gamma_zero_exact_order68
    (A B CT F : LaurentSeries k)
    (hK37 : (↑(37 : ℤ) : WithTop ℤ) ≤
      (rhoOneCapCorrectedDefect68 A B CT F).orderTop)
    (hf3 : F.coeff 3 ≠ 0) (hct7 : CT.coeff 7 ≠ 0)
    (hb11 : B.coeff 11 ≠ 0)
    (hrow : 9 * F.coeff 3 * (rhoOneCapCorrectedDefect68 A B CT F).coeff 37 =
      -4 * CT.coeff 7 * B.coeff 11 ^ 3) :
    (rhoOneCapCorrectedDefect68 A B CT F).coeff 37 ≠ 0 ∧
      (rhoOneCapCorrectedDefect68 A B CT F).orderTop =
        (↑(37 : ℤ) : WithTop ℤ) := by
  have hrhs : -4 * CT.coeff 7 * B.coeff 11 ^ 3 ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) hct7) (pow_ne_zero 3 hb11)
  have hk : (rhoOneCapCorrectedDefect68 A B CT F).coeff 37 ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hrow
    exact hrhs hrow.symm
  exact ⟨hk, le_antisymm (HahnSeries.orderTop_le_of_coeff_ne_zero hk) hK37⟩

end AlignedSquareTerminalGBoundaryCapT16Split68

end Max11DegreeRoutes
