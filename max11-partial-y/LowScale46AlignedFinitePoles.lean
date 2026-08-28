import LowScale46FinitePoles

/-! # Finite-pole exclusion for the aligned `(4,6)` chart

This module instantiates the exact eliminated aligned rows on rational-
exponent Hahn series.  It connects their literal higher-order terms to the
exhaustive Newton-face arithmetic proved in `LowScale46NewtonFaces`.
-/

noncomputable section

namespace Max11DegreeRoutes

section HahnLeadingFaces

variable {k : Type*} [Field k]

/-- If three exact finite-order terms and a remainder sum to zero, and the
remainder lies strictly above the least of the three displayed orders, then
the displayed minimum is attained at least twice. -/
theorem tripleMinimumTied_of_hahn_sum_add_higher_eq_zero46
    (x y z r : HahnSeries ℚ k) (a b c : ℚ)
    (hx : x.orderTop = (↑a : WithTop ℚ))
    (hy : y.orderTop = (↑b : WithTop ℚ))
    (hz : z.orderTop = (↑c : WithTop ℚ))
    (hr : (↑(min a (min b c)) : WithTop ℚ) < r.orderTop)
    (hsum : x + y + z + r = 0) : TripleMinimumTied a b c := by
  by_contra hnot
  have hunique :
      (a < b ∧ a < c) ∨ (b < a ∧ b < c) ∨ (c < a ∧ c < b) := by
    simp only [TripleMinimumTied, not_or, not_and_or, not_le] at hnot
    grind
  rcases hunique with ha | hb | hc
  · have hy0 : y.coeff a = 0 := HahnSeries.coeff_eq_zero_of_lt_orderTop (by
      rw [hy]
      exact WithTop.coe_lt_coe.mpr ha.1)
    have hz0 : z.coeff a = 0 := HahnSeries.coeff_eq_zero_of_lt_orderTop (by
      rw [hz]
      exact WithTop.coe_lt_coe.mpr ha.2)
    have hr' : (↑a : WithTop ℚ) < r.orderTop := by
      have hmin : min a (min b c) = a := by
        rw [min_eq_left]
        exact le_min (le_of_lt ha.1) (le_of_lt ha.2)
      rwa [hmin] at hr
    have hr0 : r.coeff a = 0 := HahnSeries.coeff_eq_zero_of_lt_orderTop hr'
    have hcoeff := congrArg (fun t : HahnSeries ℚ k => t.coeff a) hsum
    simp only [HahnSeries.coeff_add, HahnSeries.coeff_zero, hy0, hz0, hr0,
      add_zero] at hcoeff
    exact HahnSeries.coeff_orderTop_ne hx hcoeff
  · have hx0 : x.coeff b = 0 := HahnSeries.coeff_eq_zero_of_lt_orderTop (by
      rw [hx]
      exact WithTop.coe_lt_coe.mpr hb.1)
    have hz0 : z.coeff b = 0 := HahnSeries.coeff_eq_zero_of_lt_orderTop (by
      rw [hz]
      exact WithTop.coe_lt_coe.mpr hb.2)
    have hr' : (↑b : WithTop ℚ) < r.orderTop := by
      have hmin : min a (min b c) = b := by
        calc
          min a (min b c) = min b c := min_eq_right (by
            exact (min_le_left b c).trans (le_of_lt hb.1))
          _ = b := min_eq_left (le_of_lt hb.2)
      rwa [hmin] at hr
    have hr0 : r.coeff b = 0 := HahnSeries.coeff_eq_zero_of_lt_orderTop hr'
    have hcoeff := congrArg (fun t : HahnSeries ℚ k => t.coeff b) hsum
    simp only [HahnSeries.coeff_add, HahnSeries.coeff_zero, hx0, hz0, hr0,
      zero_add, add_zero] at hcoeff
    exact HahnSeries.coeff_orderTop_ne hy hcoeff
  · have hx0 : x.coeff c = 0 := HahnSeries.coeff_eq_zero_of_lt_orderTop (by
      rw [hx]
      exact WithTop.coe_lt_coe.mpr hc.1)
    have hy0 : y.coeff c = 0 := HahnSeries.coeff_eq_zero_of_lt_orderTop (by
      rw [hy]
      exact WithTop.coe_lt_coe.mpr hc.2)
    have hr' : (↑c : WithTop ℚ) < r.orderTop := by
      have hmin : min a (min b c) = c := by
        calc
          min a (min b c) = min a c := by
            rw [min_eq_right (le_of_lt hc.2)]
          _ = c := min_eq_right (le_of_lt hc.1)
      rwa [hmin] at hr
    have hr0 : r.coeff c = 0 := HahnSeries.coeff_eq_zero_of_lt_orderTop hr'
    have hcoeff := congrArg (fun t : HahnSeries ℚ k => t.coeff c) hsum
    simp only [HahnSeries.coeff_add, HahnSeries.coeff_zero, hx0, hy0, hr0,
      zero_add] at hcoeff
    exact HahnSeries.coeff_orderTop_ne hz (by simpa using hcoeff)

/-- A nonzero term of exact finite order cannot be cancelled by a remainder
strictly above that order. -/
theorem hahnExactAddHigher_impossible46
    (x r : HahnSeries ℚ k) (a : ℚ)
    (hx : x.orderTop = (↑a : WithTop ℚ))
    (hr : (↑a : WithTop ℚ) < r.orderTop)
    (hsum : x + r = 0) : False := by
  have hr0 : r.coeff a = 0 := HahnSeries.coeff_eq_zero_of_lt_orderTop hr
  have hcoeff := congrArg (fun t : HahnSeries ℚ k => t.coeff a) hsum
  simp only [HahnSeries.coeff_add, HahnSeries.coeff_zero, hr0, add_zero] at hcoeff
  exact HahnSeries.coeff_orderTop_ne hx hcoeff

end HahnLeadingFaces

section AlignedBetaFinitePoles

variable {k : Type*} [Field k]

/-- Terms of the aligned `G₀` row strictly above its `Q³,Y²,beta*s³`
Newton face in the `beta ≠ 0` stratum. -/
def alignedBetaGHigher46
    (beta gamma delta d0 e0 : k)
    (s Q Y : HahnSeries ℚ k) : HahnSeries ℚ k :=
  HahnSeries.C (-12 * beta) * (Q * s ^ 3) +
    HahnSeries.C (-6 * beta) * (Y * s ^ 3) +
    HahnSeries.C (-(8 * gamma + 12 * d0)) * (Q * s ^ 4) +
    HahnSeries.C (-(8 * delta)) * s ^ 5 +
    HahnSeries.C (8 * e0) * s ^ 6

/-- Literal decomposition of the full aligned boundary row at the beta
Newton face. -/
theorem alignedLocalG46_eq_beta_faces
    (beta gamma delta d0 e0 : k)
    (s Q Y : HahnSeries ℚ k) :
    alignedLocalG46 s Q Y (HahnSeries.C beta) (HahnSeries.C gamma)
        (HahnSeries.C delta) (HahnSeries.C d0) (HahnSeries.C e0) =
      HahnSeries.C (4 : k) * Q ^ 3 +
        HahnSeries.C (-3 : k) * Y ^ 2 +
        HahnSeries.C (4 * beta) * s ^ 3 +
        alignedBetaGHigher46 beta gamma delta d0 e0 s Q Y := by
  simp only [alignedLocalG46, alignedBetaGHigher46]
  simp only [map_mul, map_add, map_neg, map_ofNat]
  ring

/-- Every omitted term in the beta-stratum `G₀` row has order strictly
above three. -/
theorem alignedBetaGHigher46_order_gt_three
    (beta gamma delta d0 e0 : k) (s Q Y : HahnSeries ℚ k)
    (a b : ℚ) (ha : 0 < a) (hb : 0 < b)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hQ : Q.orderTop = (↑a : WithTop ℚ))
    (hY : Y.orderTop = (↑b : WithTop ℚ)) :
    (↑(3 : ℚ) : WithTop ℚ) <
      (alignedBetaGHigher46 beta gamma delta d0 e0 s Q Y).orderTop := by
  have hs3 := hahnOrderTop_pow_eq46 s 1 3 hs
  have hs4 := hahnOrderTop_pow_eq46 s 1 4 hs
  have hs5 := hahnOrderTop_pow_eq46 s 1 5 hs
  have hs6 := hahnOrderTop_pow_eq46 s 1 6 hs
  have hQs3 := hahnOrderTop_mul_eq46 Q (s ^ 3) a 3 hQ (by simpa using hs3)
  have hYs3 := hahnOrderTop_mul_eq46 Y (s ^ 3) b 3 hY (by simpa using hs3)
  have hQs4 := hahnOrderTop_mul_eq46 Q (s ^ 4) a 4 hQ (by simpa using hs4)
  have h1 := hahnOrderTop_C_mul_gt46 (-12 * beta) (Q * s ^ 3)
    3 (a + 3) hQs3 (by linarith)
  have h2 := hahnOrderTop_C_mul_gt46 (-6 * beta) (Y * s ^ 3)
    3 (b + 3) hYs3 (by linarith)
  have h3 := hahnOrderTop_C_mul_gt46 (-(8 * gamma + 12 * d0)) (Q * s ^ 4)
    3 (a + 4) hQs4 (by linarith)
  have h4 := hahnOrderTop_C_mul_gt46 (-(8 * delta)) (s ^ 5)
    3 5 (by simpa using hs5) (by norm_num)
  have h5 := hahnOrderTop_C_mul_gt46 (8 * e0) (s ^ 6)
    3 6 (by simpa using hs6) (by norm_num)
  dsimp only [alignedBetaGHigher46]
  have h12 := hahnOrderTop_add_gt46 3 _ _ h1 h2
  have h123 := hahnOrderTop_add_gt46 3 _ _ h12 h3
  have h1234 := hahnOrderTop_add_gt46 3 _ _ h123 h4
  exact hahnOrderTop_add_gt46 3 _ _ h1234 h5

/-- The exact aligned `G₀` equation in the `beta ≠ 0` stratum forces the
reviewed lowest-order tie `(3a,2b,3)`. -/
theorem alignedBetaG46_forces_Newton_tie
    [CharZero k]
    (beta gamma delta d0 e0 : k) (s Q Y : HahnSeries ℚ k)
    (a b : ℚ) (ha : 0 < a) (hb : 0 < b) (hbeta : beta ≠ 0)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hQ : Q.orderTop = (↑a : WithTop ℚ))
    (hY : Y.orderTop = (↑b : WithTop ℚ))
    (hG : alignedLocalG46 s Q Y (HahnSeries.C beta) (HahnSeries.C gamma)
      (HahnSeries.C delta) (HahnSeries.C d0) (HahnSeries.C e0) = 0) :
    TripleMinimumTied (3 * a) (2 * b) 3 := by
  let p : HahnSeries ℚ k := HahnSeries.C (4 : k) * Q ^ 3
  let q : HahnSeries ℚ k := HahnSeries.C (-3 : k) * Y ^ 2
  let z : HahnSeries ℚ k := HahnSeries.C (4 * beta) * s ^ 3
  let r := alignedBetaGHigher46 beta gamma delta d0 e0 s Q Y
  have hQ3 := hahnOrderTop_pow_eq46 Q a 3 hQ
  have hY2 := hahnOrderTop_pow_eq46 Y b 2 hY
  have hs3 := hahnOrderTop_pow_eq46 s 1 3 hs
  have hp : p.orderTop = (↑(3 * a) : WithTop ℚ) := by
    dsimp [p]
    exact hahnOrderTop_C_mul_eq46 _ _ (3 * a) (by norm_num)
      (by simpa using hQ3)
  have hq : q.orderTop = (↑(2 * b) : WithTop ℚ) := by
    dsimp [q]
    exact hahnOrderTop_C_mul_eq46 _ _ (2 * b) (by norm_num)
      (by simpa using hY2)
  have hz : z.orderTop = (↑(3 : ℚ) : WithTop ℚ) := by
    dsimp [z]
    exact hahnOrderTop_C_mul_eq46 _ _ 3 (mul_ne_zero (by norm_num) hbeta)
      (by simpa using hs3)
  have hr3 := alignedBetaGHigher46_order_gt_three
    beta gamma delta d0 e0 s Q Y a b ha hb hs hQ hY
  have hm : min (3 * a) (min (2 * b) 3) ≤ 3 :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hr : (↑(min (3 * a) (min (2 * b) 3)) : WithTop ℚ) < r.orderTop :=
    (WithTop.coe_le_coe.mpr hm).trans_lt hr3
  have hsum : p + q + z + r = 0 := by
    rw [← alignedLocalG46_eq_beta_faces beta gamma delta d0 e0 s Q Y]
    exact hG
  exact tripleMinimumTied_of_hahn_sum_add_higher_eq_zero46
    p q z r (3 * a) (2 * b) 3 hp hq hz hr hsum

/-- The full aligned `H₂` row with its `-6Y²` face removed. -/
def alignedBetaH2ExceptY46
    (beta gamma delta d0 k2 : k)
    (s Q Y : HahnSeries ℚ k) : HahnSeries ℚ k :=
  HahnSeries.C (-6 : k) * (Q ^ 2 * Y) +
    HahnSeries.C (3 * beta) * s ^ 3 +
    HahnSeries.C (-6 * beta) * (Q * s ^ 3) +
    HahnSeries.C (-3 * beta) * (Q ^ 2 * s ^ 3) +
    HahnSeries.C (-6 * beta) * (Y * s ^ 3) +
    HahnSeries.C (4 * gamma + 6 * d0) * (Y * s ^ 4) +
    HahnSeries.C (-4 * delta) * s ^ 5 +
    HahnSeries.C (4 * delta) * (Q * s ^ 5) +
    HahnSeries.C (6 * beta * d0 - 2 * k2) * s ^ 7

/-- Exact `H₂=-6Y²+remainder` decomposition. -/
theorem alignedLocalJTwo46_eq_beta_Y_face
    (beta gamma delta d0 k2 : k) (s Q Y : HahnSeries ℚ k) :
    alignedLocalJTwo46 s Q Y (HahnSeries.C beta) (HahnSeries.C gamma)
        (HahnSeries.C delta) (HahnSeries.C d0) (HahnSeries.C k2) =
      HahnSeries.C (-6 : k) * Y ^ 2 +
        alignedBetaH2ExceptY46 beta gamma delta d0 k2 s Q Y := by
  simp only [alignedLocalJTwo46, alignedBetaH2ExceptY46]
  simp only [map_mul, map_add, map_sub, map_neg, map_ofNat]
  ring

/-- If `2b` is below the other displayed `H₂` face orders, every term in
the literal remainder is strictly above `2b`. -/
theorem alignedBetaH2ExceptY46_order_gt
    (beta gamma delta d0 k2 : k) (s Q Y : HahnSeries ℚ k)
    (a b : ℚ) (_ha : 0 < a) (_hb : 0 < b)
    (hface : 2 * b < 2 * a + b ∧ 2 * b < 3)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hQ : Q.orderTop = (↑a : WithTop ℚ))
    (hY : Y.orderTop = (↑b : WithTop ℚ)) :
    (↑(2 * b) : WithTop ℚ) <
      (alignedBetaH2ExceptY46 beta gamma delta d0 k2 s Q Y).orderTop := by
  have hs3 := hahnOrderTop_pow_eq46 s 1 3 hs
  have hs4 := hahnOrderTop_pow_eq46 s 1 4 hs
  have hs5 := hahnOrderTop_pow_eq46 s 1 5 hs
  have hs7 := hahnOrderTop_pow_eq46 s 1 7 hs
  have hQ2 := hahnOrderTop_pow_eq46 Q a 2 hQ
  have hQ2Y := hahnOrderTop_mul_eq46 (Q ^ 2) Y (2 * a) b
    (by simpa using hQ2) hY
  have hQs3 := hahnOrderTop_mul_eq46 Q (s ^ 3) a 3 hQ (by simpa using hs3)
  have hQ2s3 := hahnOrderTop_mul_eq46 (Q ^ 2) (s ^ 3) (2 * a) 3
    (by simpa using hQ2) (by simpa using hs3)
  have hYs3 := hahnOrderTop_mul_eq46 Y (s ^ 3) b 3 hY (by simpa using hs3)
  have hYs4 := hahnOrderTop_mul_eq46 Y (s ^ 4) b 4 hY (by simpa using hs4)
  have hQs5 := hahnOrderTop_mul_eq46 Q (s ^ 5) a 5 hQ (by simpa using hs5)
  have h1 := hahnOrderTop_C_mul_gt46 (-6 : k) (Q ^ 2 * Y)
    (2 * b) (2 * a + b) hQ2Y hface.1
  have h2 := hahnOrderTop_C_mul_gt46 (3 * beta) (s ^ 3)
    (2 * b) 3 (by simpa using hs3) hface.2
  have h3 := hahnOrderTop_C_mul_gt46 (-6 * beta) (Q * s ^ 3)
    (2 * b) (a + 3) hQs3 (by linarith)
  have h4 := hahnOrderTop_C_mul_gt46 (-3 * beta) (Q ^ 2 * s ^ 3)
    (2 * b) (2 * a + 3) hQ2s3 (by linarith)
  have h5 := hahnOrderTop_C_mul_gt46 (-6 * beta) (Y * s ^ 3)
    (2 * b) (b + 3) hYs3 (by linarith)
  have h6 := hahnOrderTop_C_mul_gt46 (4 * gamma + 6 * d0) (Y * s ^ 4)
    (2 * b) (b + 4) hYs4 (by linarith)
  have h7 := hahnOrderTop_C_mul_gt46 (-4 * delta) (s ^ 5)
    (2 * b) 5 (by simpa using hs5) (by linarith)
  have h8 := hahnOrderTop_C_mul_gt46 (4 * delta) (Q * s ^ 5)
    (2 * b) (a + 5) hQs5 (by linarith)
  have h9 := hahnOrderTop_C_mul_gt46 (6 * beta * d0 - 2 * k2) (s ^ 7)
    (2 * b) 7 (by simpa using hs7) (by linarith)
  dsimp only [alignedBetaH2ExceptY46]
  have h12 := hahnOrderTop_add_gt46 (2 * b) _ _ h1 h2
  have h123 := hahnOrderTop_add_gt46 (2 * b) _ _ h12 h3
  have h1234 := hahnOrderTop_add_gt46 (2 * b) _ _ h123 h4
  have h12345 := hahnOrderTop_add_gt46 (2 * b) _ _ h1234 h5
  have h123456 := hahnOrderTop_add_gt46 (2 * b) _ _ h12345 h6
  have h1234567 := hahnOrderTop_add_gt46 (2 * b) _ _ h123456 h7
  have h12345678 := hahnOrderTop_add_gt46 (2 * b) _ _ h1234567 h8
  exact hahnOrderTop_add_gt46 (2 * b) _ _ h12345678 h9

/-- The full aligned `H₂` row with its nonzero `3 beta s³` face removed. -/
def alignedBetaH2ExceptS346
    (beta gamma delta d0 k2 : k)
    (s Q Y : HahnSeries ℚ k) : HahnSeries ℚ k :=
  HahnSeries.C (-6 : k) * (Q ^ 2 * Y) +
    HahnSeries.C (-6 : k) * Y ^ 2 +
    HahnSeries.C (-6 * beta) * (Q * s ^ 3) +
    HahnSeries.C (-3 * beta) * (Q ^ 2 * s ^ 3) +
    HahnSeries.C (-6 * beta) * (Y * s ^ 3) +
    HahnSeries.C (4 * gamma + 6 * d0) * (Y * s ^ 4) +
    HahnSeries.C (-4 * delta) * s ^ 5 +
    HahnSeries.C (4 * delta) * (Q * s ^ 5) +
    HahnSeries.C (6 * beta * d0 - 2 * k2) * s ^ 7

/-- Exact `H₂=3 beta s³+remainder` decomposition. -/
theorem alignedLocalJTwo46_eq_beta_s3_face
    (beta gamma delta d0 k2 : k) (s Q Y : HahnSeries ℚ k) :
    alignedLocalJTwo46 s Q Y (HahnSeries.C beta) (HahnSeries.C gamma)
        (HahnSeries.C delta) (HahnSeries.C d0) (HahnSeries.C k2) =
      HahnSeries.C (3 * beta) * s ^ 3 +
        alignedBetaH2ExceptS346 beta gamma delta d0 k2 s Q Y := by
  simp only [alignedLocalJTwo46, alignedBetaH2ExceptS346]
  simp only [map_mul, map_add, map_sub, map_neg, map_ofNat]
  ring

/-- If order three is below the other displayed `H₂` face orders, its
literal complement is strictly higher. -/
theorem alignedBetaH2ExceptS346_order_gt
    (beta gamma delta d0 k2 : k) (s Q Y : HahnSeries ℚ k)
    (a b : ℚ) (ha : 0 < a) (_hb : 0 < b)
    (hface : 3 < 2 * a + b ∧ 3 < 2 * b)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hQ : Q.orderTop = (↑a : WithTop ℚ))
    (hY : Y.orderTop = (↑b : WithTop ℚ)) :
    (↑(3 : ℚ) : WithTop ℚ) <
      (alignedBetaH2ExceptS346 beta gamma delta d0 k2 s Q Y).orderTop := by
  have hs3 := hahnOrderTop_pow_eq46 s 1 3 hs
  have hs4 := hahnOrderTop_pow_eq46 s 1 4 hs
  have hs5 := hahnOrderTop_pow_eq46 s 1 5 hs
  have hs7 := hahnOrderTop_pow_eq46 s 1 7 hs
  have hQ2 := hahnOrderTop_pow_eq46 Q a 2 hQ
  have hY2 := hahnOrderTop_pow_eq46 Y b 2 hY
  have hQ2Y := hahnOrderTop_mul_eq46 (Q ^ 2) Y (2 * a) b
    (by simpa using hQ2) hY
  have hQs3 := hahnOrderTop_mul_eq46 Q (s ^ 3) a 3 hQ (by simpa using hs3)
  have hQ2s3 := hahnOrderTop_mul_eq46 (Q ^ 2) (s ^ 3) (2 * a) 3
    (by simpa using hQ2) (by simpa using hs3)
  have hYs3 := hahnOrderTop_mul_eq46 Y (s ^ 3) b 3 hY (by simpa using hs3)
  have hYs4 := hahnOrderTop_mul_eq46 Y (s ^ 4) b 4 hY (by simpa using hs4)
  have hQs5 := hahnOrderTop_mul_eq46 Q (s ^ 5) a 5 hQ (by simpa using hs5)
  have h1 := hahnOrderTop_C_mul_gt46 (-6 : k) (Q ^ 2 * Y)
    3 (2 * a + b) hQ2Y hface.1
  have h2 := hahnOrderTop_C_mul_gt46 (-6 : k) (Y ^ 2)
    3 (2 * b) (by simpa using hY2) hface.2
  have h3 := hahnOrderTop_C_mul_gt46 (-6 * beta) (Q * s ^ 3)
    3 (a + 3) hQs3 (by linarith)
  have h4 := hahnOrderTop_C_mul_gt46 (-3 * beta) (Q ^ 2 * s ^ 3)
    3 (2 * a + 3) hQ2s3 (by linarith)
  have h5 := hahnOrderTop_C_mul_gt46 (-6 * beta) (Y * s ^ 3)
    3 (b + 3) hYs3 (by linarith)
  have h6 := hahnOrderTop_C_mul_gt46 (4 * gamma + 6 * d0) (Y * s ^ 4)
    3 (b + 4) hYs4 (by linarith)
  have h7 := hahnOrderTop_C_mul_gt46 (-4 * delta) (s ^ 5)
    3 5 (by simpa using hs5) (by norm_num)
  have h8 := hahnOrderTop_C_mul_gt46 (4 * delta) (Q * s ^ 5)
    3 (a + 5) hQs5 (by linarith)
  have h9 := hahnOrderTop_C_mul_gt46 (6 * beta * d0 - 2 * k2) (s ^ 7)
    3 7 (by simpa using hs7) (by norm_num)
  dsimp only [alignedBetaH2ExceptS346]
  have h12 := hahnOrderTop_add_gt46 3 _ _ h1 h2
  have h123 := hahnOrderTop_add_gt46 3 _ _ h12 h3
  have h1234 := hahnOrderTop_add_gt46 3 _ _ h123 h4
  have h12345 := hahnOrderTop_add_gt46 3 _ _ h1234 h5
  have h123456 := hahnOrderTop_add_gt46 3 _ _ h12345 h6
  have h1234567 := hahnOrderTop_add_gt46 3 _ _ h123456 h7
  have h12345678 := hahnOrderTop_add_gt46 3 _ _ h1234567 h8
  exact hahnOrderTop_add_gt46 3 _ _ h12345678 h9

/-- The full aligned `H₁` row with its `6Y²` face removed. -/
def alignedBetaH1ExceptY46
    (beta gamma delta d0 k1 : k)
    (s Q Y : HahnSeries ℚ k) : HahnSeries ℚ k :=
  HahnSeries.C (3 : k) * Q ^ 4 +
    HahnSeries.C (6 : k) * (Q ^ 2 * Y) +
    HahnSeries.C (-3 : k) * (Q * Y ^ 2) +
    HahnSeries.C (3 * beta) * (Y * s ^ 3) +
    HahnSeries.C (-3 * beta) * (Q * Y * s ^ 3) +
    HahnSeries.C (-(4 * gamma + 6 * d0)) * (Q ^ 2 * s ^ 4) +
    HahnSeries.C (-(4 * gamma + 6 * d0)) * (Y * s ^ 4) +
    HahnSeries.C (2 * delta) * (Y * s ^ 5) +
    HahnSeries.C (4 * gamma * d0 + 3 * d0 ^ 2 - 2 * k1) * s ^ 8

/-- Exact `H₁=6Y²+remainder` decomposition. -/
theorem alignedLocalJOne46_eq_beta_Y_face
    (beta gamma delta d0 k1 : k) (s Q Y : HahnSeries ℚ k) :
    alignedLocalJOne46 s Q Y (HahnSeries.C beta) (HahnSeries.C gamma)
        (HahnSeries.C delta) (HahnSeries.C d0) (HahnSeries.C k1) =
      HahnSeries.C (6 : k) * Y ^ 2 +
        alignedBetaH1ExceptY46 beta gamma delta d0 k1 s Q Y := by
  simp only [alignedLocalJOne46, alignedBetaH1ExceptY46]
  simp only [map_mul, map_add, map_sub, map_neg, map_ofNat, map_pow]
  ring

/-- In the final beta-face alternative, the `G₀` tie bounds the literal
`H₁` tail while the arithmetic table puts every displayed face above `2b`. -/
theorem alignedBetaH1ExceptY46_order_gt
    (beta gamma delta d0 k1 : k) (s Q Y : HahnSeries ℚ k)
    (a b : ℚ) (_ha : 0 < a) (_hb : 0 < b)
    (hGface : TripleMinimumTied (3 * a) (2 * b) 3)
    (hface : 2 * b < 4 * a ∧ 2 * b < 2 * a + b ∧
      2 * b < a + 2 * b)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hQ : Q.orderTop = (↑a : WithTop ℚ))
    (hY : Y.orderTop = (↑b : WithTop ℚ)) :
    (↑(2 * b) : WithTop ℚ) <
      (alignedBetaH1ExceptY46 beta gamma delta d0 k1 s Q Y).orderTop := by
  have hb2 : b < 2 := by
    rcases hGface with h | h | h
    · rcases h with ⟨heq, hle⟩
      linarith
    · rcases h with ⟨heq, hle⟩
      linarith [hface.1]
    · rcases h with ⟨heq, hle⟩
      linarith
  have hs3 := hahnOrderTop_pow_eq46 s 1 3 hs
  have hs4 := hahnOrderTop_pow_eq46 s 1 4 hs
  have hs5 := hahnOrderTop_pow_eq46 s 1 5 hs
  have hs8 := hahnOrderTop_pow_eq46 s 1 8 hs
  have hQ2 := hahnOrderTop_pow_eq46 Q a 2 hQ
  have hQ4 := hahnOrderTop_pow_eq46 Q a 4 hQ
  have hY2 := hahnOrderTop_pow_eq46 Y b 2 hY
  have hQ2Y := hahnOrderTop_mul_eq46 (Q ^ 2) Y (2 * a) b
    (by simpa using hQ2) hY
  have hQY2 := hahnOrderTop_mul_eq46 Q (Y ^ 2) a (2 * b) hQ
    (by simpa using hY2)
  have hYs3 := hahnOrderTop_mul_eq46 Y (s ^ 3) b 3 hY (by simpa using hs3)
  have hQY := hahnOrderTop_mul_eq46 Q Y a b hQ hY
  have hQYs3 := hahnOrderTop_mul_eq46 (Q * Y) (s ^ 3) (a + b) 3 hQY
    (by simpa using hs3)
  have hQ2s4 := hahnOrderTop_mul_eq46 (Q ^ 2) (s ^ 4) (2 * a) 4
    (by simpa using hQ2) (by simpa using hs4)
  have hYs4 := hahnOrderTop_mul_eq46 Y (s ^ 4) b 4 hY (by simpa using hs4)
  have hYs5 := hahnOrderTop_mul_eq46 Y (s ^ 5) b 5 hY (by simpa using hs5)
  have h1 := hahnOrderTop_C_mul_gt46 (3 : k) (Q ^ 4)
    (2 * b) (4 * a) (by simpa using hQ4) hface.1
  have h2 := hahnOrderTop_C_mul_gt46 (6 : k) (Q ^ 2 * Y)
    (2 * b) (2 * a + b) hQ2Y hface.2.1
  have h3 := hahnOrderTop_C_mul_gt46 (-3 : k) (Q * Y ^ 2)
    (2 * b) (a + 2 * b) hQY2 hface.2.2
  have h4 := hahnOrderTop_C_mul_gt46 (3 * beta) (Y * s ^ 3)
    (2 * b) (b + 3) hYs3 (by linarith)
  have h5 := hahnOrderTop_C_mul_gt46 (-3 * beta) (Q * Y * s ^ 3)
    (2 * b) (a + b + 3) (by simpa [mul_assoc] using hQYs3) (by linarith)
  have h6 := hahnOrderTop_C_mul_gt46 (-(4 * gamma + 6 * d0)) (Q ^ 2 * s ^ 4)
    (2 * b) (2 * a + 4) hQ2s4 (by linarith)
  have h7 := hahnOrderTop_C_mul_gt46 (-(4 * gamma + 6 * d0)) (Y * s ^ 4)
    (2 * b) (b + 4) hYs4 (by linarith)
  have h8 := hahnOrderTop_C_mul_gt46 (2 * delta) (Y * s ^ 5)
    (2 * b) (b + 5) hYs5 (by linarith)
  have h9 := hahnOrderTop_C_mul_gt46
    (4 * gamma * d0 + 3 * d0 ^ 2 - 2 * k1) (s ^ 8)
    (2 * b) 8 (by simpa using hs8) (by linarith)
  dsimp only [alignedBetaH1ExceptY46]
  have h12 := hahnOrderTop_add_gt46 (2 * b) _ _ h1 h2
  have h123 := hahnOrderTop_add_gt46 (2 * b) _ _ h12 h3
  have h1234 := hahnOrderTop_add_gt46 (2 * b) _ _ h123 h4
  have h12345 := hahnOrderTop_add_gt46 (2 * b) _ _ h1234 h5
  have h123456 := hahnOrderTop_add_gt46 (2 * b) _ _ h12345 h6
  have h1234567 := hahnOrderTop_add_gt46 (2 * b) _ _ h123456 h7
  have h12345678 := hahnOrderTop_add_gt46 (2 * b) _ _ h1234567 h8
  exact hahnOrderTop_add_gt46 (2 * b) _ _ h12345678 h9

/-- No aligned beta-stratum finite-pole branch exists when `Q,Y` have
finite positive order. -/
theorem alignedBetaFinitePole46_impossible
    [CharZero k]
    (beta gamma delta d0 e0 k2 k1 : k)
    (s Q Y : HahnSeries ℚ k) (a b : ℚ)
    (ha : 0 < a) (hb : 0 < b) (hbeta : beta ≠ 0)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hQ : Q.orderTop = (↑a : WithTop ℚ))
    (hY : Y.orderTop = (↑b : WithTop ℚ))
    (hG : alignedLocalG46 s Q Y (HahnSeries.C beta) (HahnSeries.C gamma)
      (HahnSeries.C delta) (HahnSeries.C d0) (HahnSeries.C e0) = 0)
    (hJ2 : alignedLocalJTwo46 s Q Y (HahnSeries.C beta) (HahnSeries.C gamma)
      (HahnSeries.C delta) (HahnSeries.C d0) (HahnSeries.C k2) = 0)
    (hJ1 : alignedLocalJOne46 s Q Y (HahnSeries.C beta) (HahnSeries.C gamma)
      (HahnSeries.C delta) (HahnSeries.C d0) (HahnSeries.C k1) = 0) : False := by
  have hGface := alignedBetaG46_forces_Newton_tie
    beta gamma delta d0 e0 s Q Y a b ha hb hbeta hs hQ hY hG
  rcases alignedBetaNewtonFace46 a b ha hb hGface with hYface | hs3face | hYface
  · let p : HahnSeries ℚ k := HahnSeries.C (-6 : k) * Y ^ 2
    let r := alignedBetaH2ExceptY46 beta gamma delta d0 k2 s Q Y
    have hY2 := hahnOrderTop_pow_eq46 Y b 2 hY
    have hp : p.orderTop = (↑(2 * b) : WithTop ℚ) := by
      dsimp [p]
      exact hahnOrderTop_C_mul_eq46 _ _ (2 * b) (by norm_num)
        (by simpa using hY2)
    have hr := alignedBetaH2ExceptY46_order_gt
      beta gamma delta d0 k2 s Q Y a b ha hb hYface hs hQ hY
    have hsum : p + r = 0 := by
      rw [← alignedLocalJTwo46_eq_beta_Y_face beta gamma delta d0 k2 s Q Y]
      exact hJ2
    exact hahnExactAddHigher_impossible46 p r (2 * b) hp hr hsum
  · let p : HahnSeries ℚ k := HahnSeries.C (3 * beta) * s ^ 3
    let r := alignedBetaH2ExceptS346 beta gamma delta d0 k2 s Q Y
    have hs3 := hahnOrderTop_pow_eq46 s 1 3 hs
    have hp : p.orderTop = (↑(3 : ℚ) : WithTop ℚ) := by
      dsimp [p]
      exact hahnOrderTop_C_mul_eq46 _ _ 3 (mul_ne_zero (by norm_num) hbeta)
        (by simpa using hs3)
    have hr := alignedBetaH2ExceptS346_order_gt
      beta gamma delta d0 k2 s Q Y a b ha hb hs3face hs hQ hY
    have hsum : p + r = 0 := by
      rw [← alignedLocalJTwo46_eq_beta_s3_face beta gamma delta d0 k2 s Q Y]
      exact hJ2
    exact hahnExactAddHigher_impossible46 p r 3 hp hr hsum
  · let p : HahnSeries ℚ k := HahnSeries.C (6 : k) * Y ^ 2
    let r := alignedBetaH1ExceptY46 beta gamma delta d0 k1 s Q Y
    have hY2 := hahnOrderTop_pow_eq46 Y b 2 hY
    have hp : p.orderTop = (↑(2 * b) : WithTop ℚ) := by
      dsimp [p]
      exact hahnOrderTop_C_mul_eq46 _ _ (2 * b) (by norm_num)
        (by simpa using hY2)
    have hr := alignedBetaH1ExceptY46_order_gt
      beta gamma delta d0 k1 s Q Y a b ha hb hGface hYface hs hQ hY
    have hsum : p + r = 0 := by
      rw [← alignedLocalJOne46_eq_beta_Y_face beta gamma delta d0 k1 s Q Y]
      exact hJ1
    exact hahnExactAddHigher_impossible46 p r (2 * b) hp hr hsum

end AlignedBetaFinitePoles

section AlignedDeltaFinitePoles

variable {k : Type*} [Field k]

/-- Terms above the `Q³,Y²,delta*s⁵` face of the aligned `G₀` row after
specializing `beta=0`. -/
def alignedDeltaGHigher46
    (gamma d0 e0 : k) (s Q : HahnSeries ℚ k) : HahnSeries ℚ k :=
  HahnSeries.C (-(8 * gamma + 12 * d0)) * (Q * s ^ 4) +
    HahnSeries.C (8 * e0) * s ^ 6

/-- Literal delta-stratum decomposition of the full aligned `G₀` row. -/
theorem alignedLocalG46_eq_delta_faces
    (gamma delta d0 e0 : k) (s Q Y : HahnSeries ℚ k) :
    alignedLocalG46 s Q Y 0 (HahnSeries.C gamma)
        (HahnSeries.C delta) (HahnSeries.C d0) (HahnSeries.C e0) =
      HahnSeries.C (4 : k) * Q ^ 3 +
        HahnSeries.C (-3 : k) * Y ^ 2 +
        HahnSeries.C (-8 * delta) * s ^ 5 +
        alignedDeltaGHigher46 gamma d0 e0 s Q := by
  simp only [alignedLocalG46, alignedDeltaGHigher46]
  simp only [map_mul, map_add, map_neg, map_ofNat, zero_mul, mul_zero,
    add_zero]
  ring

/-- The literal delta-stratum `G₀` remainder lies above the least of the
three possible face orders `(3a,2b,5)`. -/
theorem alignedDeltaGHigher46_order_gt_min
    (gamma d0 e0 : k) (s Q : HahnSeries ℚ k)
    (a b : ℚ) (_ha : 0 < a)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hQ : Q.orderTop = (↑a : WithTop ℚ)) :
    (↑(min (3 * a) (min (2 * b) 5)) : WithTop ℚ) <
      (alignedDeltaGHigher46 gamma d0 e0 s Q).orderTop := by
  let m := min (3 * a) (min (2 * b) 5)
  have hs4 := hahnOrderTop_pow_eq46 s 1 4 hs
  have hs6 := hahnOrderTop_pow_eq46 s 1 6 hs
  have hQs4 := hahnOrderTop_mul_eq46 Q (s ^ 4) a 4 hQ (by simpa using hs4)
  have hmQa : m < a + 4 := by
    by_cases ha2 : a < 2
    · have hm : m ≤ 3 * a := by
        dsimp [m]
        exact min_le_left _ _
      linarith
    · have hm : m ≤ 5 := by
        dsimp [m]
        exact (min_le_right _ _).trans (min_le_right _ _)
      linarith
  have hm6 : m < 6 := by
    have hm : m ≤ 5 := by
      dsimp [m]
      exact (min_le_right _ _).trans (min_le_right _ _)
    linarith
  have h1 := hahnOrderTop_C_mul_gt46 (-(8 * gamma + 12 * d0)) (Q * s ^ 4)
    m (a + 4) hQs4 hmQa
  have h2 := hahnOrderTop_C_mul_gt46 (8 * e0) (s ^ 6)
    m 6 (by simpa using hs6) hm6
  dsimp only [alignedDeltaGHigher46]
  exact hahnOrderTop_add_gt46 m _ _ h1 h2

/-- The exact delta-stratum `G₀` equation forces the reviewed face tie
`(3a,2b,5)`. -/
theorem alignedDeltaG46_forces_Newton_tie
    [CharZero k]
    (gamma delta d0 e0 : k) (s Q Y : HahnSeries ℚ k)
    (a b : ℚ) (ha : 0 < a) (hdelta : delta ≠ 0)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hQ : Q.orderTop = (↑a : WithTop ℚ))
    (hY : Y.orderTop = (↑b : WithTop ℚ))
    (hG : alignedLocalG46 s Q Y 0 (HahnSeries.C gamma)
      (HahnSeries.C delta) (HahnSeries.C d0) (HahnSeries.C e0) = 0) :
    TripleMinimumTied (3 * a) (2 * b) 5 := by
  let p : HahnSeries ℚ k := HahnSeries.C (4 : k) * Q ^ 3
  let q : HahnSeries ℚ k := HahnSeries.C (-3 : k) * Y ^ 2
  let z : HahnSeries ℚ k := HahnSeries.C (-8 * delta) * s ^ 5
  let r := alignedDeltaGHigher46 gamma d0 e0 s Q
  have hQ3 := hahnOrderTop_pow_eq46 Q a 3 hQ
  have hY2 := hahnOrderTop_pow_eq46 Y b 2 hY
  have hs5 := hahnOrderTop_pow_eq46 s 1 5 hs
  have hp : p.orderTop = (↑(3 * a) : WithTop ℚ) := by
    dsimp [p]
    exact hahnOrderTop_C_mul_eq46 _ _ (3 * a) (by norm_num)
      (by simpa using hQ3)
  have hq : q.orderTop = (↑(2 * b) : WithTop ℚ) := by
    dsimp [q]
    exact hahnOrderTop_C_mul_eq46 _ _ (2 * b) (by norm_num)
      (by simpa using hY2)
  have hz : z.orderTop = (↑(5 : ℚ) : WithTop ℚ) := by
    dsimp [z]
    exact hahnOrderTop_C_mul_eq46 _ _ 5 (mul_ne_zero (by norm_num) hdelta)
      (by simpa using hs5)
  have hr := alignedDeltaGHigher46_order_gt_min gamma d0 e0 s Q a b ha hs hQ
  have hsum : p + q + z + r = 0 := by
    rw [← alignedLocalG46_eq_delta_faces gamma delta d0 e0 s Q Y]
    exact hG
  exact tripleMinimumTied_of_hahn_sum_add_higher_eq_zero46
    p q z r (3 * a) (2 * b) 5 hp hq hz hr hsum

/-- A tie among `(3a,2b,5)` induces the four-candidate tie consumed by the
existing delta Newton table; the extra order `4+a` can never be least. -/
theorem alignedDeltaQuadrupleTie_of_triple46
    (a b : ℚ) (_ha : 0 < a)
    (h : TripleMinimumTied (3 * a) (2 * b) 5) :
    QuadrupleMinimumTied (3 * a) (2 * b) (4 + a) 5 := by
  rcases h with h | h | h
  · left
    exact ⟨h.1, by linarith [h.2], h.2⟩
  · right
    right
    left
    exact ⟨h.1, h.2, by linarith [h.1]⟩
  · right
    right
    right
    right
    left
    exact ⟨h.1, h.2, by linarith [h.1, h.2]⟩

/-- The delta-stratum `H₂` row with its `-6Y²` face removed. -/
def alignedDeltaH2ExceptY46
    (gamma delta d0 k2 : k)
    (s Q Y : HahnSeries ℚ k) : HahnSeries ℚ k :=
  HahnSeries.C (-6 : k) * (Q ^ 2 * Y) +
    HahnSeries.C (4 * gamma + 6 * d0) * (Y * s ^ 4) +
    HahnSeries.C (-4 * delta) * s ^ 5 +
    HahnSeries.C (4 * delta) * (Q * s ^ 5) +
    HahnSeries.C (-2 * k2) * s ^ 7

/-- Exact delta-stratum decomposition `H₂=-6Y²+remainder`. -/
theorem alignedLocalJTwo46_eq_delta_Y_face
    (gamma delta d0 k2 : k) (s Q Y : HahnSeries ℚ k) :
    alignedLocalJTwo46 s Q Y 0 (HahnSeries.C gamma)
        (HahnSeries.C delta) (HahnSeries.C d0) (HahnSeries.C k2) =
      HahnSeries.C (-6 : k) * Y ^ 2 +
        alignedDeltaH2ExceptY46 gamma delta d0 k2 s Q Y := by
  simp only [alignedLocalJTwo46, alignedDeltaH2ExceptY46]
  simp only [map_mul, map_add, map_neg, map_ofNat, zero_mul,
    mul_zero, add_zero]
  ring

/-- Under the first delta-table exit, the full complement of `-6Y²` in
`H₂` lies strictly above order `2b`. -/
theorem alignedDeltaH2ExceptY46_order_gt
    (gamma delta d0 k2 : k) (s Q Y : HahnSeries ℚ k)
    (a b : ℚ)
    (hface : 2 * b < 2 * a + b ∧ 2 * b < 4 + b ∧ 2 * b < 5)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hQ : Q.orderTop = (↑a : WithTop ℚ))
    (hY : Y.orderTop = (↑b : WithTop ℚ)) :
    (↑(2 * b) : WithTop ℚ) <
      (alignedDeltaH2ExceptY46 gamma delta d0 k2 s Q Y).orderTop := by
  have hs4 := hahnOrderTop_pow_eq46 s 1 4 hs
  have hs5 := hahnOrderTop_pow_eq46 s 1 5 hs
  have hs7 := hahnOrderTop_pow_eq46 s 1 7 hs
  have hQ2 := hahnOrderTop_pow_eq46 Q a 2 hQ
  have hQ2Y := hahnOrderTop_mul_eq46 (Q ^ 2) Y (2 * a) b
    (by simpa using hQ2) hY
  have hYs4 := hahnOrderTop_mul_eq46 Y (s ^ 4) b 4 hY (by simpa using hs4)
  have hQs5 := hahnOrderTop_mul_eq46 Q (s ^ 5) a 5 hQ (by simpa using hs5)
  have h1 := hahnOrderTop_C_mul_gt46 (-6 : k) (Q ^ 2 * Y)
    (2 * b) (2 * a + b) hQ2Y hface.1
  have h2 := hahnOrderTop_C_mul_gt46 (4 * gamma + 6 * d0) (Y * s ^ 4)
    (2 * b) (b + 4) hYs4 (by linarith [hface.2.1])
  have h3 := hahnOrderTop_C_mul_gt46 (-4 * delta) (s ^ 5)
    (2 * b) 5 (by simpa using hs5) hface.2.2
  have h4 := hahnOrderTop_C_mul_gt46 (4 * delta) (Q * s ^ 5)
    (2 * b) (a + 5) hQs5 (by linarith [hface.2.2])
  have h5 := hahnOrderTop_C_mul_gt46 (-2 * k2) (s ^ 7)
    (2 * b) 7 (by simpa using hs7) (by linarith [hface.2.2])
  dsimp only [alignedDeltaH2ExceptY46]
  have h12 := hahnOrderTop_add_gt46 (2 * b) _ _ h1 h2
  have h123 := hahnOrderTop_add_gt46 (2 * b) _ _ h12 h3
  have h1234 := hahnOrderTop_add_gt46 (2 * b) _ _ h123 h4
  exact hahnOrderTop_add_gt46 (2 * b) _ _ h1234 h5

/-- The delta-stratum `H₂` row with its nonzero `-4delta*s⁵` face removed. -/
def alignedDeltaH2ExceptS546
    (gamma delta d0 k2 : k)
    (s Q Y : HahnSeries ℚ k) : HahnSeries ℚ k :=
  HahnSeries.C (-6 : k) * (Q ^ 2 * Y) +
    HahnSeries.C (-6 : k) * Y ^ 2 +
    HahnSeries.C (4 * gamma + 6 * d0) * (Y * s ^ 4) +
    HahnSeries.C (4 * delta) * (Q * s ^ 5) +
    HahnSeries.C (-2 * k2) * s ^ 7

/-- Exact delta-stratum decomposition `H₂=-4delta*s⁵+remainder`. -/
theorem alignedLocalJTwo46_eq_delta_s5_face
    (gamma delta d0 k2 : k) (s Q Y : HahnSeries ℚ k) :
    alignedLocalJTwo46 s Q Y 0 (HahnSeries.C gamma)
        (HahnSeries.C delta) (HahnSeries.C d0) (HahnSeries.C k2) =
      HahnSeries.C (-4 * delta) * s ^ 5 +
        alignedDeltaH2ExceptS546 gamma delta d0 k2 s Q Y := by
  simp only [alignedLocalJTwo46, alignedDeltaH2ExceptS546]
  simp only [map_mul, map_add, map_neg, map_ofNat, zero_mul,
    mul_zero, add_zero]
  ring

/-- Under the second delta-table exit, the full complement of
`-4delta*s⁵` lies strictly above order five. -/
theorem alignedDeltaH2ExceptS546_order_gt
    (gamma delta d0 k2 : k) (s Q Y : HahnSeries ℚ k)
    (a b : ℚ) (ha : 0 < a)
    (hface : 5 < 2 * a + b ∧ 5 < 2 * b ∧ 5 < 4 + b)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hQ : Q.orderTop = (↑a : WithTop ℚ))
    (hY : Y.orderTop = (↑b : WithTop ℚ)) :
    (↑(5 : ℚ) : WithTop ℚ) <
      (alignedDeltaH2ExceptS546 gamma delta d0 k2 s Q Y).orderTop := by
  have hs4 := hahnOrderTop_pow_eq46 s 1 4 hs
  have hs5 := hahnOrderTop_pow_eq46 s 1 5 hs
  have hs7 := hahnOrderTop_pow_eq46 s 1 7 hs
  have hQ2 := hahnOrderTop_pow_eq46 Q a 2 hQ
  have hY2 := hahnOrderTop_pow_eq46 Y b 2 hY
  have hQ2Y := hahnOrderTop_mul_eq46 (Q ^ 2) Y (2 * a) b
    (by simpa using hQ2) hY
  have hYs4 := hahnOrderTop_mul_eq46 Y (s ^ 4) b 4 hY (by simpa using hs4)
  have hQs5 := hahnOrderTop_mul_eq46 Q (s ^ 5) a 5 hQ (by simpa using hs5)
  have h1 := hahnOrderTop_C_mul_gt46 (-6 : k) (Q ^ 2 * Y)
    5 (2 * a + b) hQ2Y hface.1
  have h2 := hahnOrderTop_C_mul_gt46 (-6 : k) (Y ^ 2)
    5 (2 * b) (by simpa using hY2) hface.2.1
  have h3 := hahnOrderTop_C_mul_gt46 (4 * gamma + 6 * d0) (Y * s ^ 4)
    5 (b + 4) hYs4 (by linarith [hface.2.2])
  have h4 := hahnOrderTop_C_mul_gt46 (4 * delta) (Q * s ^ 5)
    5 (a + 5) hQs5 (by linarith)
  have h5 := hahnOrderTop_C_mul_gt46 (-2 * k2) (s ^ 7)
    5 7 (by simpa using hs7) (by norm_num)
  dsimp only [alignedDeltaH2ExceptS546]
  have h12 := hahnOrderTop_add_gt46 5 _ _ h1 h2
  have h123 := hahnOrderTop_add_gt46 5 _ _ h12 h3
  have h1234 := hahnOrderTop_add_gt46 5 _ _ h123 h4
  exact hahnOrderTop_add_gt46 5 _ _ h1234 h5

/-- The delta-stratum `H₁` row with its `6Y²` face removed. -/
def alignedDeltaH1ExceptY46
    (gamma delta d0 k1 : k)
    (s Q Y : HahnSeries ℚ k) : HahnSeries ℚ k :=
  HahnSeries.C (3 : k) * Q ^ 4 +
    HahnSeries.C (6 : k) * (Q ^ 2 * Y) +
    HahnSeries.C (-3 : k) * (Q * Y ^ 2) +
    HahnSeries.C (-(4 * gamma + 6 * d0)) * (Q ^ 2 * s ^ 4) +
    HahnSeries.C (-(4 * gamma + 6 * d0)) * (Y * s ^ 4) +
    HahnSeries.C (2 * delta) * (Y * s ^ 5) +
    HahnSeries.C (4 * gamma * d0 + 3 * d0 ^ 2 - 2 * k1) * s ^ 8

/-- Exact delta-stratum decomposition `H₁=6Y²+remainder`. -/
theorem alignedLocalJOne46_eq_delta_Y_face
    (gamma delta d0 k1 : k) (s Q Y : HahnSeries ℚ k) :
    alignedLocalJOne46 s Q Y 0 (HahnSeries.C gamma)
        (HahnSeries.C delta) (HahnSeries.C d0) (HahnSeries.C k1) =
      HahnSeries.C (6 : k) * Y ^ 2 +
        alignedDeltaH1ExceptY46 gamma delta d0 k1 s Q Y := by
  simp only [alignedLocalJOne46, alignedDeltaH1ExceptY46]
  simp only [map_mul, map_add, map_sub, map_neg, map_ofNat, map_pow,
    zero_mul, mul_zero, add_zero]
  ring

/-- Under the terminal delta-table exit, every literal complement of
`6Y²` in `H₁` lies strictly above order `2b`. -/
theorem alignedDeltaH1ExceptY46_order_gt
    (gamma delta d0 k1 : k) (s Q Y : HahnSeries ℚ k)
    (a b : ℚ)
    (hface : 2 * b < 4 * a ∧ 2 * b < 2 * a + b ∧
      2 * b < a + 2 * b ∧ 2 * b < 4 + 2 * a ∧
      2 * b < 4 + b ∧ 2 * b < 5 + b ∧ 2 * b < 8)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hQ : Q.orderTop = (↑a : WithTop ℚ))
    (hY : Y.orderTop = (↑b : WithTop ℚ)) :
    (↑(2 * b) : WithTop ℚ) <
      (alignedDeltaH1ExceptY46 gamma delta d0 k1 s Q Y).orderTop := by
  have hs4 := hahnOrderTop_pow_eq46 s 1 4 hs
  have hs5 := hahnOrderTop_pow_eq46 s 1 5 hs
  have hs8 := hahnOrderTop_pow_eq46 s 1 8 hs
  have hQ2 := hahnOrderTop_pow_eq46 Q a 2 hQ
  have hQ4 := hahnOrderTop_pow_eq46 Q a 4 hQ
  have hY2 := hahnOrderTop_pow_eq46 Y b 2 hY
  have hQ2Y := hahnOrderTop_mul_eq46 (Q ^ 2) Y (2 * a) b
    (by simpa using hQ2) hY
  have hQY2 := hahnOrderTop_mul_eq46 Q (Y ^ 2) a (2 * b) hQ
    (by simpa using hY2)
  have hQ2s4 := hahnOrderTop_mul_eq46 (Q ^ 2) (s ^ 4) (2 * a) 4
    (by simpa using hQ2) (by simpa using hs4)
  have hYs4 := hahnOrderTop_mul_eq46 Y (s ^ 4) b 4 hY (by simpa using hs4)
  have hYs5 := hahnOrderTop_mul_eq46 Y (s ^ 5) b 5 hY (by simpa using hs5)
  have h1 := hahnOrderTop_C_mul_gt46 (3 : k) (Q ^ 4)
    (2 * b) (4 * a) (by simpa using hQ4) hface.1
  have h2 := hahnOrderTop_C_mul_gt46 (6 : k) (Q ^ 2 * Y)
    (2 * b) (2 * a + b) hQ2Y hface.2.1
  have h3 := hahnOrderTop_C_mul_gt46 (-3 : k) (Q * Y ^ 2)
    (2 * b) (a + 2 * b) hQY2 hface.2.2.1
  have h4 := hahnOrderTop_C_mul_gt46 (-(4 * gamma + 6 * d0)) (Q ^ 2 * s ^ 4)
    (2 * b) (2 * a + 4) hQ2s4 (by linarith [hface.2.2.2.1])
  have h5 := hahnOrderTop_C_mul_gt46 (-(4 * gamma + 6 * d0)) (Y * s ^ 4)
    (2 * b) (b + 4) hYs4 (by linarith [hface.2.2.2.2.1])
  have h6 := hahnOrderTop_C_mul_gt46 (2 * delta) (Y * s ^ 5)
    (2 * b) (b + 5) hYs5 (by linarith [hface.2.2.2.2.2.1])
  have h7 := hahnOrderTop_C_mul_gt46
    (4 * gamma * d0 + 3 * d0 ^ 2 - 2 * k1) (s ^ 8)
    (2 * b) 8 (by simpa using hs8) hface.2.2.2.2.2.2
  dsimp only [alignedDeltaH1ExceptY46]
  have h12 := hahnOrderTop_add_gt46 (2 * b) _ _ h1 h2
  have h123 := hahnOrderTop_add_gt46 (2 * b) _ _ h12 h3
  have h1234 := hahnOrderTop_add_gt46 (2 * b) _ _ h123 h4
  have h12345 := hahnOrderTop_add_gt46 (2 * b) _ _ h1234 h5
  have h123456 := hahnOrderTop_add_gt46 (2 * b) _ _ h12345 h6
  exact hahnOrderTop_add_gt46 (2 * b) _ _ h123456 h7

/-- No aligned delta-stratum finite-pole branch exists when `Q,Y` have
finite positive order. -/
theorem alignedDeltaFinitePole46_impossible
    [CharZero k]
    (gamma delta d0 e0 k2 k1 : k)
    (s Q Y : HahnSeries ℚ k) (a b : ℚ)
    (ha : 0 < a) (hb : 0 < b) (hdelta : delta ≠ 0)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hQ : Q.orderTop = (↑a : WithTop ℚ))
    (hY : Y.orderTop = (↑b : WithTop ℚ))
    (hG : alignedLocalG46 s Q Y 0 (HahnSeries.C gamma)
      (HahnSeries.C delta) (HahnSeries.C d0) (HahnSeries.C e0) = 0)
    (hJ2 : alignedLocalJTwo46 s Q Y 0 (HahnSeries.C gamma)
      (HahnSeries.C delta) (HahnSeries.C d0) (HahnSeries.C k2) = 0)
    (hJ1 : alignedLocalJOne46 s Q Y 0 (HahnSeries.C gamma)
      (HahnSeries.C delta) (HahnSeries.C d0) (HahnSeries.C k1) = 0) : False := by
  have hGtriple := alignedDeltaG46_forces_Newton_tie
    gamma delta d0 e0 s Q Y a b ha hdelta hs hQ hY hG
  have hGquad := alignedDeltaQuadrupleTie_of_triple46 a b ha hGtriple
  rcases alignedDeltaNewtonFace46 a b ha hb hGquad with hYface | hs5face | hYface
  · let p : HahnSeries ℚ k := HahnSeries.C (-6 : k) * Y ^ 2
    let r := alignedDeltaH2ExceptY46 gamma delta d0 k2 s Q Y
    have hY2 := hahnOrderTop_pow_eq46 Y b 2 hY
    have hp : p.orderTop = (↑(2 * b) : WithTop ℚ) := by
      dsimp [p]
      exact hahnOrderTop_C_mul_eq46 _ _ (2 * b) (by norm_num)
        (by simpa using hY2)
    have hr := alignedDeltaH2ExceptY46_order_gt
      gamma delta d0 k2 s Q Y a b hYface hs hQ hY
    have hsum : p + r = 0 := by
      rw [← alignedLocalJTwo46_eq_delta_Y_face gamma delta d0 k2 s Q Y]
      exact hJ2
    exact hahnExactAddHigher_impossible46 p r (2 * b) hp hr hsum
  · let p : HahnSeries ℚ k := HahnSeries.C (-4 * delta) * s ^ 5
    let r := alignedDeltaH2ExceptS546 gamma delta d0 k2 s Q Y
    have hs5 := hahnOrderTop_pow_eq46 s 1 5 hs
    have hp : p.orderTop = (↑(5 : ℚ) : WithTop ℚ) := by
      dsimp [p]
      exact hahnOrderTop_C_mul_eq46 _ _ 5 (mul_ne_zero (by norm_num) hdelta)
        (by simpa using hs5)
    have hr := alignedDeltaH2ExceptS546_order_gt
      gamma delta d0 k2 s Q Y a b ha hs5face hs hQ hY
    have hsum : p + r = 0 := by
      rw [← alignedLocalJTwo46_eq_delta_s5_face gamma delta d0 k2 s Q Y]
      exact hJ2
    exact hahnExactAddHigher_impossible46 p r 5 hp hr hsum
  · let p : HahnSeries ℚ k := HahnSeries.C (6 : k) * Y ^ 2
    let r := alignedDeltaH1ExceptY46 gamma delta d0 k1 s Q Y
    have hY2 := hahnOrderTop_pow_eq46 Y b 2 hY
    have hp : p.orderTop = (↑(2 * b) : WithTop ℚ) := by
      dsimp [p]
      exact hahnOrderTop_C_mul_eq46 _ _ (2 * b) (by norm_num)
        (by simpa using hY2)
    have hr := alignedDeltaH1ExceptY46_order_gt
      gamma delta d0 k1 s Q Y a b hYface hs hQ hY
    have hsum : p + r = 0 := by
      rw [← alignedLocalJOne46_eq_delta_Y_face gamma delta d0 k1 s Q Y]
      exact hJ1
    exact hahnExactAddHigher_impossible46 p r (2 * b) hp hr hsum

end AlignedDeltaFinitePoles

section AlignedDegenerateFinitePoles

variable {k : Type*} [Field k]

/-- After `Q=0`, the literal complement of `6Y²` in the aligned `H₁` row. -/
def alignedQZeroH1Higher46
    (beta gamma delta d0 k1 : k)
    (s Y : HahnSeries ℚ k) : HahnSeries ℚ k :=
  HahnSeries.C (3 * beta) * (Y * s ^ 3) +
    HahnSeries.C (-(4 * gamma + 6 * d0)) * (Y * s ^ 4) +
    HahnSeries.C (2 * delta) * (Y * s ^ 5) +
    HahnSeries.C (4 * gamma * d0 + 3 * d0 ^ 2 - 2 * k1) * s ^ 8

/-- Exact `Q=0` specialization of the full aligned `H₁` row. -/
theorem alignedLocalJOne46_Q_zero_eq
    (beta gamma delta d0 k1 : k) (s Y : HahnSeries ℚ k) :
    alignedLocalJOne46 s 0 Y (HahnSeries.C beta) (HahnSeries.C gamma)
        (HahnSeries.C delta) (HahnSeries.C d0) (HahnSeries.C k1) =
      HahnSeries.C (6 : k) * Y ^ 2 +
        alignedQZeroH1Higher46 beta gamma delta d0 k1 s Y := by
  simp only [alignedLocalJOne46, alignedQZeroH1Higher46]
  simp only [map_mul, map_add, map_sub, map_neg, map_ofNat, map_pow,
    zero_mul, mul_zero]
  ring

/-- If `b<3` and `2b<8`, every term outside `6Y²` in the `Q=0` aligned
`H₁` row lies strictly above order `2b`. -/
theorem alignedQZeroH1Higher46_order_gt
    (beta gamma delta d0 k1 : k) (s Y : HahnSeries ℚ k)
    (b : ℚ) (hb3 : b < 3) (hb8 : 2 * b < 8)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hY : Y.orderTop = (↑b : WithTop ℚ)) :
    (↑(2 * b) : WithTop ℚ) <
      (alignedQZeroH1Higher46 beta gamma delta d0 k1 s Y).orderTop := by
  have hs3 := hahnOrderTop_pow_eq46 s 1 3 hs
  have hs4 := hahnOrderTop_pow_eq46 s 1 4 hs
  have hs5 := hahnOrderTop_pow_eq46 s 1 5 hs
  have hs8 := hahnOrderTop_pow_eq46 s 1 8 hs
  have hYs3 := hahnOrderTop_mul_eq46 Y (s ^ 3) b 3 hY (by simpa using hs3)
  have hYs4 := hahnOrderTop_mul_eq46 Y (s ^ 4) b 4 hY (by simpa using hs4)
  have hYs5 := hahnOrderTop_mul_eq46 Y (s ^ 5) b 5 hY (by simpa using hs5)
  have h1 := hahnOrderTop_C_mul_gt46 (3 * beta) (Y * s ^ 3)
    (2 * b) (b + 3) hYs3 (by linarith)
  have h2 := hahnOrderTop_C_mul_gt46 (-(4 * gamma + 6 * d0)) (Y * s ^ 4)
    (2 * b) (b + 4) hYs4 (by linarith)
  have h3 := hahnOrderTop_C_mul_gt46 (2 * delta) (Y * s ^ 5)
    (2 * b) (b + 5) hYs5 (by linarith)
  have h4 := hahnOrderTop_C_mul_gt46
    (4 * gamma * d0 + 3 * d0 ^ 2 - 2 * k1) (s ^ 8)
    (2 * b) 8 (by simpa using hs8) hb8
  dsimp only [alignedQZeroH1Higher46]
  have h12 := hahnOrderTop_add_gt46 (2 * b) _ _ h1 h2
  have h123 := hahnOrderTop_add_gt46 (2 * b) _ _ h12 h3
  exact hahnOrderTop_add_gt46 (2 * b) _ _ h123 h4

/-- Higher terms in the beta-stratum `G₀` row after setting `Q=0`. -/
def alignedBetaQZeroGHigher46
    (beta delta e0 : k) (s Y : HahnSeries ℚ k) : HahnSeries ℚ k :=
  HahnSeries.C (-6 * beta) * (Y * s ^ 3) +
    HahnSeries.C (-8 * delta) * s ^ 5 +
    HahnSeries.C (8 * e0) * s ^ 6

/-- Exact beta-stratum `G₀` equation on `Q=0`. -/
theorem alignedLocalG46_beta_Q_zero_eq
    (beta gamma delta d0 e0 : k) (s Y : HahnSeries ℚ k) :
    alignedLocalG46 s 0 Y (HahnSeries.C beta) (HahnSeries.C gamma)
        (HahnSeries.C delta) (HahnSeries.C d0) (HahnSeries.C e0) =
      HahnSeries.C (-3 : k) * Y ^ 2 +
        HahnSeries.C (4 * beta) * s ^ 3 +
        alignedBetaQZeroGHigher46 beta delta e0 s Y := by
  simp only [alignedLocalG46, alignedBetaQZeroGHigher46]
  simp only [map_mul, map_neg, map_ofNat, zero_mul, mul_zero]
  ring

/-- The beta-stratum `Q=0` boundary remainder lies above order three. -/
theorem alignedBetaQZeroGHigher46_order_gt_three
    (beta delta e0 : k) (s Y : HahnSeries ℚ k)
    (b : ℚ) (hb : 0 < b)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hY : Y.orderTop = (↑b : WithTop ℚ)) :
    (↑(3 : ℚ) : WithTop ℚ) <
      (alignedBetaQZeroGHigher46 beta delta e0 s Y).orderTop := by
  have hs3 := hahnOrderTop_pow_eq46 s 1 3 hs
  have hs5 := hahnOrderTop_pow_eq46 s 1 5 hs
  have hs6 := hahnOrderTop_pow_eq46 s 1 6 hs
  have hYs3 := hahnOrderTop_mul_eq46 Y (s ^ 3) b 3 hY (by simpa using hs3)
  have h1 := hahnOrderTop_C_mul_gt46 (-6 * beta) (Y * s ^ 3)
    3 (b + 3) hYs3 (by linarith)
  have h2 := hahnOrderTop_C_mul_gt46 (-8 * delta) (s ^ 5)
    3 5 (by simpa using hs5) (by norm_num)
  have h3 := hahnOrderTop_C_mul_gt46 (8 * e0) (s ^ 6)
    3 6 (by simpa using hs6) (by norm_num)
  dsimp only [alignedBetaQZeroGHigher46]
  have h12 := hahnOrderTop_add_gt46 3 _ _ h1 h2
  exact hahnOrderTop_add_gt46 3 _ _ h12 h3

/-- In the beta stratum, the `Q=0`, finite-positive-order `Y` locus is
inconsistent: `G₀` forces `2b=3`, then `H₁` has isolated `6Y²`. -/
theorem alignedBetaQZeroFinitePole46_impossible
    [CharZero k]
    (beta gamma delta d0 e0 k1 : k) (s Q Y : HahnSeries ℚ k)
    (b : ℚ) (hb : 0 < b) (hbeta : beta ≠ 0)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hY : Y.orderTop = (↑b : WithTop ℚ)) (hQzero : Q = 0)
    (hG : alignedLocalG46 s Q Y (HahnSeries.C beta) (HahnSeries.C gamma)
      (HahnSeries.C delta) (HahnSeries.C d0) (HahnSeries.C e0) = 0)
    (hJ1 : alignedLocalJOne46 s Q Y (HahnSeries.C beta) (HahnSeries.C gamma)
      (HahnSeries.C delta) (HahnSeries.C d0) (HahnSeries.C k1) = 0) : False := by
  have hGzero : alignedLocalG46 s 0 Y (HahnSeries.C beta) (HahnSeries.C gamma)
      (HahnSeries.C delta) (HahnSeries.C d0) (HahnSeries.C e0) = 0 := by
    simpa [hQzero] using hG
  let p : HahnSeries ℚ k := HahnSeries.C (-3 : k) * Y ^ 2
  let q : HahnSeries ℚ k := HahnSeries.C (4 * beta) * s ^ 3
  let r := alignedBetaQZeroGHigher46 beta delta e0 s Y
  have hY2 := hahnOrderTop_pow_eq46 Y b 2 hY
  have hs3 := hahnOrderTop_pow_eq46 s 1 3 hs
  have hp : p.orderTop = (↑(2 * b) : WithTop ℚ) := by
    dsimp [p]
    exact hahnOrderTop_C_mul_eq46 _ _ (2 * b) (by norm_num)
      (by simpa using hY2)
  have hq : q.orderTop = (↑(3 : ℚ) : WithTop ℚ) := by
    dsimp [q]
    exact hahnOrderTop_C_mul_eq46 _ _ 3 (mul_ne_zero (by norm_num) hbeta)
      (by simpa using hs3)
  have hr := alignedBetaQZeroGHigher46_order_gt_three
    beta delta e0 s Y b hb hs hY
  have hsum : p + q + r = 0 := by
    rw [← alignedLocalG46_beta_Q_zero_eq beta gamma delta d0 e0 s Y]
    exact hGzero
  have h2b : 2 * b = 3 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hq0 : q.coeff (2 * b) = 0 := HahnSeries.coeff_eq_zero_of_lt_orderTop (by
        rw [hq]
        exact WithTop.coe_lt_coe.mpr hlt)
      have hr0 : r.coeff (2 * b) = 0 := HahnSeries.coeff_eq_zero_of_lt_orderTop
        ((WithTop.coe_lt_coe.mpr hlt).trans hr)
      have hcoeff := congrArg (fun t : HahnSeries ℚ k => t.coeff (2 * b)) hsum
      simp only [HahnSeries.coeff_add, HahnSeries.coeff_zero, hq0, hr0,
        add_zero] at hcoeff
      exact HahnSeries.coeff_orderTop_ne hp hcoeff
    · have hp0 : p.coeff 3 = 0 := HahnSeries.coeff_eq_zero_of_lt_orderTop (by
        rw [hp]
        exact WithTop.coe_lt_coe.mpr hgt)
      have hr0 : r.coeff 3 = 0 := HahnSeries.coeff_eq_zero_of_lt_orderTop hr
      have hcoeff := congrArg (fun t : HahnSeries ℚ k => t.coeff 3) hsum
      simp only [HahnSeries.coeff_add, HahnSeries.coeff_zero, hp0, hr0,
        zero_add, add_zero] at hcoeff
      exact HahnSeries.coeff_orderTop_ne hq hcoeff
  have hbhalf : b = 3 / 2 := by linarith
  have hJ1zero : alignedLocalJOne46 s 0 Y (HahnSeries.C beta)
      (HahnSeries.C gamma) (HahnSeries.C delta) (HahnSeries.C d0)
      (HahnSeries.C k1) = 0 := by
    simpa [hQzero] using hJ1
  let p1 : HahnSeries ℚ k := HahnSeries.C (6 : k) * Y ^ 2
  let r1 := alignedQZeroH1Higher46 beta gamma delta d0 k1 s Y
  have hp1 : p1.orderTop = (↑(2 * b) : WithTop ℚ) := by
    dsimp [p1]
    exact hahnOrderTop_C_mul_eq46 _ _ (2 * b) (by norm_num)
      (by simpa using hY2)
  have hr1 := alignedQZeroH1Higher46_order_gt
    beta gamma delta d0 k1 s Y b (by linarith) (by linarith) hs hY
  have hsum1 : p1 + r1 = 0 := by
    rw [← alignedLocalJOne46_Q_zero_eq beta gamma delta d0 k1 s Y]
    exact hJ1zero
  exact hahnExactAddHigher_impossible46 p1 r1 (2 * b) hp1 hr1 hsum1

/-- Higher terms in beta-stratum `H₂` after setting `Y=0`. -/
def alignedBetaYZeroH2Higher46
    (beta delta d0 k2 : k) (s Q : HahnSeries ℚ k) : HahnSeries ℚ k :=
  HahnSeries.C (-6 * beta) * (Q * s ^ 3) +
    HahnSeries.C (-3 * beta) * (Q ^ 2 * s ^ 3) +
    HahnSeries.C (-4 * delta) * s ^ 5 +
    HahnSeries.C (4 * delta) * (Q * s ^ 5) +
    HahnSeries.C (6 * beta * d0 - 2 * k2) * s ^ 7

/-- Exact beta-stratum `H₂` equation on `Y=0`. -/
theorem alignedLocalJTwo46_beta_Y_zero_eq
    (beta gamma delta d0 k2 : k) (s Q : HahnSeries ℚ k) :
    alignedLocalJTwo46 s Q 0 (HahnSeries.C beta) (HahnSeries.C gamma)
        (HahnSeries.C delta) (HahnSeries.C d0) (HahnSeries.C k2) =
      HahnSeries.C (3 * beta) * s ^ 3 +
        alignedBetaYZeroH2Higher46 beta delta d0 k2 s Q := by
  simp only [alignedLocalJTwo46, alignedBetaYZeroH2Higher46]
  simp only [map_mul, map_sub, map_neg, map_ofNat, zero_mul, mul_zero,
    add_zero]
  ring

/-- The beta-stratum `Y=0` `H₂` remainder lies above order three even when
`Q` itself vanishes. -/
theorem alignedBetaYZeroH2Higher46_order_gt_three
    (beta delta d0 k2 : k) (s Q : HahnSeries ℚ k)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hQ : (↑(0 : ℚ) : WithTop ℚ) < Q.orderTop) :
    (↑(3 : ℚ) : WithTop ℚ) <
      (alignedBetaYZeroH2Higher46 beta delta d0 k2 s Q).orderTop := by
  have hs3 := hahnOrderTop_pow_eq46 s 1 3 hs
  have hs5 := hahnOrderTop_pow_eq46 s 1 5 hs
  have hs7 := hahnOrderTop_pow_eq46 s 1 7 hs
  have hQ2 : (↑(0 : ℚ) : WithTop ℚ) < (Q ^ 2).orderTop := by
    simpa [pow_two] using hahnOrderTop_mul_pos46 Q Q hQ hQ
  have hQs3 := hahnOrderTop_pos_mul_exact_gt46 Q (s ^ 3) 3 hQ
    (by simpa using hs3)
  have hQ2s3 := hahnOrderTop_pos_mul_exact_gt46 (Q ^ 2) (s ^ 3) 3 hQ2
    (by simpa using hs3)
  have hQs5raw := hahnOrderTop_pos_mul_exact_gt46 Q (s ^ 5) 5 hQ
    (by simpa using hs5)
  have hQs5 : (↑(3 : ℚ) : WithTop ℚ) < (Q * s ^ 5).orderTop :=
    (WithTop.coe_lt_coe.mpr (by norm_num)).trans hQs5raw
  have h1 := hahnOrderTop_C_mul_gt_of_gt46 (-6 * beta) (Q * s ^ 3) 3 hQs3
  have h2 := hahnOrderTop_C_mul_gt_of_gt46 (-3 * beta) (Q ^ 2 * s ^ 3) 3 hQ2s3
  have h3 := hahnOrderTop_C_mul_gt46 (-4 * delta) (s ^ 5)
    3 5 (by simpa using hs5) (by norm_num)
  have h4 := hahnOrderTop_C_mul_gt_of_gt46 (4 * delta) (Q * s ^ 5) 3 hQs5
  have h5 := hahnOrderTop_C_mul_gt46 (6 * beta * d0 - 2 * k2) (s ^ 7)
    3 7 (by simpa using hs7) (by norm_num)
  dsimp only [alignedBetaYZeroH2Higher46]
  have h12 := hahnOrderTop_add_gt46 3 _ _ h1 h2
  have h123 := hahnOrderTop_add_gt46 3 _ _ h12 h3
  have h1234 := hahnOrderTop_add_gt46 3 _ _ h123 h4
  exact hahnOrderTop_add_gt46 3 _ _ h1234 h5

/-- The beta-stratum `Y=0` locus is killed by its isolated `3 beta s³`
term in the full `H₂` row. -/
theorem alignedBetaYZeroFinitePole46_impossible
    [CharZero k]
    (beta gamma delta d0 k2 : k) (s Q Y : HahnSeries ℚ k)
    (hbeta : beta ≠ 0) (hYzero : Y = 0)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hQ : (↑(0 : ℚ) : WithTop ℚ) < Q.orderTop)
    (hJ2 : alignedLocalJTwo46 s Q Y (HahnSeries.C beta) (HahnSeries.C gamma)
      (HahnSeries.C delta) (HahnSeries.C d0) (HahnSeries.C k2) = 0) : False := by
  let p : HahnSeries ℚ k := HahnSeries.C (3 * beta) * s ^ 3
  let r := alignedBetaYZeroH2Higher46 beta delta d0 k2 s Q
  have hs3 := hahnOrderTop_pow_eq46 s 1 3 hs
  have hp : p.orderTop = (↑(3 : ℚ) : WithTop ℚ) := by
    dsimp [p]
    exact hahnOrderTop_C_mul_eq46 _ _ 3 (mul_ne_zero (by norm_num) hbeta)
      (by simpa using hs3)
  have hr := alignedBetaYZeroH2Higher46_order_gt_three
    beta delta d0 k2 s Q hs hQ
  have hsum : p + r = 0 := by
    rw [← alignedLocalJTwo46_beta_Y_zero_eq beta gamma delta d0 k2 s Q]
    simpa [hYzero] using hJ2
  exact hahnExactAddHigher_impossible46 p r 3 hp hr hsum

/-- Higher terms in the delta-stratum `H₂` row after setting `Y=0`. -/
def alignedDeltaYZeroH2Higher46
    (delta k2 : k) (s Q : HahnSeries ℚ k) : HahnSeries ℚ k :=
  HahnSeries.C (4 * delta) * (Q * s ^ 5) +
    HahnSeries.C (-2 * k2) * s ^ 7

/-- Exact delta-stratum `H₂` equation on `Y=0`. -/
theorem alignedLocalJTwo46_delta_Y_zero_eq
    (gamma delta d0 k2 : k) (s Q : HahnSeries ℚ k) :
    alignedLocalJTwo46 s Q 0 0 (HahnSeries.C gamma)
        (HahnSeries.C delta) (HahnSeries.C d0) (HahnSeries.C k2) =
      HahnSeries.C (-4 * delta) * s ^ 5 +
        alignedDeltaYZeroH2Higher46 delta k2 s Q := by
  simp only [alignedLocalJTwo46, alignedDeltaYZeroH2Higher46]
  simp only [map_mul, map_neg, map_ofNat, zero_mul, mul_zero, add_zero]
  ring

/-- The delta-stratum `Y=0` remainder lies above order five, including when
`Q=0`. -/
theorem alignedDeltaYZeroH2Higher46_order_gt_five
    (delta k2 : k) (s Q : HahnSeries ℚ k)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hQ : (↑(0 : ℚ) : WithTop ℚ) < Q.orderTop) :
    (↑(5 : ℚ) : WithTop ℚ) <
      (alignedDeltaYZeroH2Higher46 delta k2 s Q).orderTop := by
  have hs5 := hahnOrderTop_pow_eq46 s 1 5 hs
  have hs7 := hahnOrderTop_pow_eq46 s 1 7 hs
  have hQs5 := hahnOrderTop_pos_mul_exact_gt46 Q (s ^ 5) 5 hQ
    (by simpa using hs5)
  have h1 := hahnOrderTop_C_mul_gt_of_gt46 (4 * delta) (Q * s ^ 5) 5 hQs5
  have h2 := hahnOrderTop_C_mul_gt46 (-2 * k2) (s ^ 7)
    5 7 (by simpa using hs7) (by norm_num)
  dsimp only [alignedDeltaYZeroH2Higher46]
  exact hahnOrderTop_add_gt46 5 _ _ h1 h2

/-- The delta-stratum `Y=0` locus is killed by its isolated
`-4 delta s⁵` term. -/
theorem alignedDeltaYZeroFinitePole46_impossible
    [CharZero k]
    (gamma delta d0 k2 : k) (s Q Y : HahnSeries ℚ k)
    (hdelta : delta ≠ 0) (hYzero : Y = 0)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hQ : (↑(0 : ℚ) : WithTop ℚ) < Q.orderTop)
    (hJ2 : alignedLocalJTwo46 s Q Y 0 (HahnSeries.C gamma)
      (HahnSeries.C delta) (HahnSeries.C d0) (HahnSeries.C k2) = 0) : False := by
  let p : HahnSeries ℚ k := HahnSeries.C (-4 * delta) * s ^ 5
  let r := alignedDeltaYZeroH2Higher46 delta k2 s Q
  have hs5 := hahnOrderTop_pow_eq46 s 1 5 hs
  have hp : p.orderTop = (↑(5 : ℚ) : WithTop ℚ) := by
    dsimp [p]
    exact hahnOrderTop_C_mul_eq46 _ _ 5 (mul_ne_zero (by norm_num) hdelta)
      (by simpa using hs5)
  have hr := alignedDeltaYZeroH2Higher46_order_gt_five delta k2 s Q hs hQ
  have hsum : p + r = 0 := by
    rw [← alignedLocalJTwo46_delta_Y_zero_eq gamma delta d0 k2 s Q]
    simpa [hYzero] using hJ2
  exact hahnExactAddHigher_impossible46 p r 5 hp hr hsum

/-- Exact delta-stratum `G₀` equation after setting `Q=0`. -/
theorem alignedLocalG46_delta_Q_zero_eq
    (gamma delta d0 e0 : k) (s Y : HahnSeries ℚ k) :
    alignedLocalG46 s 0 Y 0 (HahnSeries.C gamma)
        (HahnSeries.C delta) (HahnSeries.C d0) (HahnSeries.C e0) =
      HahnSeries.C (-3 : k) * Y ^ 2 +
        HahnSeries.C (-8 * delta) * s ^ 5 +
        HahnSeries.C (8 * e0) * s ^ 6 := by
  simp only [alignedLocalG46]
  simp only [map_mul, map_neg, map_ofNat, zero_mul, mul_zero, add_zero]
  ring

/-- In the delta stratum, the `Q=0`, finite-positive-order `Y` locus is
inconsistent: `G₀` forces `2b=5`, then `H₁` has isolated `6Y²`. -/
theorem alignedDeltaQZeroFinitePole46_impossible
    [CharZero k]
    (gamma delta d0 e0 k1 : k) (s Q Y : HahnSeries ℚ k)
    (b : ℚ) (_hb : 0 < b) (hdelta : delta ≠ 0)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hY : Y.orderTop = (↑b : WithTop ℚ)) (hQzero : Q = 0)
    (hG : alignedLocalG46 s Q Y 0 (HahnSeries.C gamma)
      (HahnSeries.C delta) (HahnSeries.C d0) (HahnSeries.C e0) = 0)
    (hJ1 : alignedLocalJOne46 s Q Y 0 (HahnSeries.C gamma)
      (HahnSeries.C delta) (HahnSeries.C d0) (HahnSeries.C k1) = 0) : False := by
  have hGzero : alignedLocalG46 s 0 Y 0 (HahnSeries.C gamma)
      (HahnSeries.C delta) (HahnSeries.C d0) (HahnSeries.C e0) = 0 := by
    simpa [hQzero] using hG
  let p : HahnSeries ℚ k := HahnSeries.C (-3 : k) * Y ^ 2
  let q : HahnSeries ℚ k := HahnSeries.C (-8 * delta) * s ^ 5
  let r : HahnSeries ℚ k := HahnSeries.C (8 * e0) * s ^ 6
  have hY2 := hahnOrderTop_pow_eq46 Y b 2 hY
  have hs5 := hahnOrderTop_pow_eq46 s 1 5 hs
  have hs6 := hahnOrderTop_pow_eq46 s 1 6 hs
  have hp : p.orderTop = (↑(2 * b) : WithTop ℚ) := by
    dsimp [p]
    exact hahnOrderTop_C_mul_eq46 _ _ (2 * b) (by norm_num)
      (by simpa using hY2)
  have hq : q.orderTop = (↑(5 : ℚ) : WithTop ℚ) := by
    dsimp [q]
    exact hahnOrderTop_C_mul_eq46 _ _ 5 (mul_ne_zero (by norm_num) hdelta)
      (by simpa using hs5)
  have hr : (↑(5 : ℚ) : WithTop ℚ) < r.orderTop := by
    dsimp [r]
    exact hahnOrderTop_C_mul_gt46 (8 * e0) (s ^ 6)
      5 6 (by simpa using hs6) (by norm_num)
  have hsum : p + q + r = 0 := by
    rw [← alignedLocalG46_delta_Q_zero_eq gamma delta d0 e0 s Y]
    exact hGzero
  have h2b : 2 * b = 5 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hq0 : q.coeff (2 * b) = 0 := HahnSeries.coeff_eq_zero_of_lt_orderTop (by
        rw [hq]
        exact WithTop.coe_lt_coe.mpr hlt)
      have hr0 : r.coeff (2 * b) = 0 := HahnSeries.coeff_eq_zero_of_lt_orderTop
        ((WithTop.coe_lt_coe.mpr hlt).trans hr)
      have hcoeff := congrArg (fun t : HahnSeries ℚ k => t.coeff (2 * b)) hsum
      simp only [HahnSeries.coeff_add, HahnSeries.coeff_zero, hq0, hr0,
        add_zero] at hcoeff
      exact HahnSeries.coeff_orderTop_ne hp hcoeff
    · have hp0 : p.coeff 5 = 0 := HahnSeries.coeff_eq_zero_of_lt_orderTop (by
        rw [hp]
        exact WithTop.coe_lt_coe.mpr hgt)
      have hr0 : r.coeff 5 = 0 := HahnSeries.coeff_eq_zero_of_lt_orderTop hr
      have hcoeff := congrArg (fun t : HahnSeries ℚ k => t.coeff 5) hsum
      simp only [HahnSeries.coeff_add, HahnSeries.coeff_zero, hp0, hr0,
        zero_add, add_zero] at hcoeff
      exact HahnSeries.coeff_orderTop_ne hq hcoeff
  have hbhalf : b = 5 / 2 := by linarith
  have hJ1zero : alignedLocalJOne46 s 0 Y 0 (HahnSeries.C gamma)
      (HahnSeries.C delta) (HahnSeries.C d0) (HahnSeries.C k1) = 0 := by
    simpa [hQzero] using hJ1
  let p1 : HahnSeries ℚ k := HahnSeries.C (6 : k) * Y ^ 2
  let r1 := alignedQZeroH1Higher46 0 gamma delta d0 k1 s Y
  have hp1 : p1.orderTop = (↑(2 * b) : WithTop ℚ) := by
    dsimp [p1]
    exact hahnOrderTop_C_mul_eq46 _ _ (2 * b) (by norm_num)
      (by simpa using hY2)
  have hr1 := alignedQZeroH1Higher46_order_gt
    0 gamma delta d0 k1 s Y b (by linarith) (by linarith) hs hY
  have hsum1 : p1 + r1 = 0 := by
    rw [← alignedLocalJOne46_Q_zero_eq 0 gamma delta d0 k1 s Y]
    simpa using hJ1zero
  exact hahnExactAddHigher_impossible46 p1 r1 (2 * b) hp1 hr1 hsum1

/-- Exhaustive finite-pole exclusion for the aligned `beta ≠ 0` stratum,
allowing `Q` and `Y` independently to vanish identically. -/
theorem alignedBetaFinitePole46_exhaustive
    [CharZero k]
    (beta gamma delta d0 e0 k2 k1 : k)
    (s Q Y : HahnSeries ℚ k) (hbeta : beta ≠ 0)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hQcase : PositiveFiniteOrZero46 Q)
    (hYcase : PositiveFiniteOrZero46 Y)
    (hG : alignedLocalG46 s Q Y (HahnSeries.C beta) (HahnSeries.C gamma)
      (HahnSeries.C delta) (HahnSeries.C d0) (HahnSeries.C e0) = 0)
    (hJ2 : alignedLocalJTwo46 s Q Y (HahnSeries.C beta) (HahnSeries.C gamma)
      (HahnSeries.C delta) (HahnSeries.C d0) (HahnSeries.C k2) = 0)
    (hJ1 : alignedLocalJOne46 s Q Y (HahnSeries.C beta) (HahnSeries.C gamma)
      (HahnSeries.C delta) (HahnSeries.C d0) (HahnSeries.C k1) = 0) : False := by
  have hQpos := orderTop_pos_of_positiveFiniteOrZero46 Q hQcase
  rcases hYcase with hYzero | ⟨b, hb, hY⟩
  · exact alignedBetaYZeroFinitePole46_impossible
      beta gamma delta d0 k2 s Q Y hbeta hYzero hs hQpos hJ2
  rcases hQcase with hQzero | ⟨a, ha, hQ⟩
  · exact alignedBetaQZeroFinitePole46_impossible
      beta gamma delta d0 e0 k1 s Q Y b hb hbeta hs hY hQzero hG hJ1
  · exact alignedBetaFinitePole46_impossible
      beta gamma delta d0 e0 k2 k1 s Q Y a b ha hb hbeta hs hQ hY
      hG hJ2 hJ1

/-- Exhaustive finite-pole exclusion for the aligned
`beta=0, delta ≠ 0` stratum, again including both identically-zero loci. -/
theorem alignedDeltaFinitePole46_exhaustive
    [CharZero k]
    (gamma delta d0 e0 k2 k1 : k)
    (s Q Y : HahnSeries ℚ k) (hdelta : delta ≠ 0)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hQcase : PositiveFiniteOrZero46 Q)
    (hYcase : PositiveFiniteOrZero46 Y)
    (hG : alignedLocalG46 s Q Y 0 (HahnSeries.C gamma)
      (HahnSeries.C delta) (HahnSeries.C d0) (HahnSeries.C e0) = 0)
    (hJ2 : alignedLocalJTwo46 s Q Y 0 (HahnSeries.C gamma)
      (HahnSeries.C delta) (HahnSeries.C d0) (HahnSeries.C k2) = 0)
    (hJ1 : alignedLocalJOne46 s Q Y 0 (HahnSeries.C gamma)
      (HahnSeries.C delta) (HahnSeries.C d0) (HahnSeries.C k1) = 0) : False := by
  have hQpos := orderTop_pos_of_positiveFiniteOrZero46 Q hQcase
  rcases hYcase with hYzero | ⟨b, hb, hY⟩
  · exact alignedDeltaYZeroFinitePole46_impossible
      gamma delta d0 k2 s Q Y hdelta hYzero hs hQpos hJ2
  rcases hQcase with hQzero | ⟨a, ha, hQ⟩
  · exact alignedDeltaQZeroFinitePole46_impossible
      gamma delta d0 e0 k1 s Q Y b hb hdelta hs hY hQzero hG hJ1
  · exact alignedDeltaFinitePole46_impossible
      gamma delta d0 e0 k2 k1 s Q Y a b ha hb hdelta hs hQ hY
      hG hJ2 hJ1

end AlignedDegenerateFinitePoles

end Max11DegreeRoutes
