import LowScale46RegularLoads
import LowScale46AlignedZeroFinitePoles

/-! # Regular-load finite-pole exclusions in the aligned `(4,6)` chart

The aligned finite-pole arguments were first proved for scalar boundary
loads.  A translated polynomial supplies arbitrary Hahn-series loads of
nonnegative order.  This module shows that their extra terms occur strictly
above every Newton face used by the scalar proofs.
-/

noncomputable section

namespace Max11DegreeRoutes

section RegularOrderHelpers

variable {k : Type*} [Field k]

/-- Multiplication by a regular Hahn coefficient preserves every strict
lower bound on the order of an exact-order factor. -/
theorem regularHahn_mul_exact_orderTop_gt46
    (A X : HahnSeries ℚ k) (c e : ℚ)
    (hA : (0 : WithTop ℚ) ≤ A.orderTop)
    (hX : X.orderTop = (↑c : WithTop ℚ)) (he : e < c) :
    (↑e : WithTop ℚ) < (A * X).orderTop := by
  rw [HahnSeries.orderTop_mul, hX]
  exact lt_of_lt_of_le (WithTop.coe_lt_coe.mpr he)
    (by simpa [add_comm] using
      add_le_add_right hA (↑c : WithTop ℚ))

/-- A scalar multiple of a regular Hahn series remains regular. -/
theorem hahnOrderTop_C_mul_nonneg46
    (c : k) (A : HahnSeries ℚ k)
    (hA : (0 : WithTop ℚ) ≤ A.orderTop) :
    (0 : WithTop ℚ) ≤ (HahnSeries.C c * A).orderTop := by
  exact hahnOrderTop_mul_nonneg46 _ _ (hahnOrderTop_C_nonneg46 c) hA

end RegularOrderHelpers

section AlignedBetaRegularLoads

variable {k : Type*} [Field k] [CharZero k]

/-- The beta-face remainder with arbitrary regular boundary loads. -/
def alignedBetaGHigherRegular46
    (beta gamma delta : k) (D E : HahnSeries ℚ k)
    (s Q Y : HahnSeries ℚ k) : HahnSeries ℚ k :=
  alignedBetaGHigher46 beta gamma delta 0 0 s Q Y +
    HahnSeries.C (-12 : k) * (D * (Q * s ^ 4)) +
    HahnSeries.C (8 : k) * (E * s ^ 6)

theorem alignedLocalG46_eq_beta_faces_regular
    (beta gamma delta : k) (D E : HahnSeries ℚ k)
    (s Q Y : HahnSeries ℚ k) :
    alignedLocalG46 s Q Y (HahnSeries.C beta) (HahnSeries.C gamma)
        (HahnSeries.C delta) D E =
      HahnSeries.C (4 : k) * Q ^ 3 +
        HahnSeries.C (-3 : k) * Y ^ 2 +
        HahnSeries.C (4 * beta) * s ^ 3 +
        alignedBetaGHigherRegular46 beta gamma delta D E s Q Y := by
  simp only [alignedLocalG46, alignedBetaGHigherRegular46,
    alignedBetaGHigher46]
  simp only [map_mul, map_add, map_neg, map_ofNat, map_zero, mul_zero,
    add_zero]
  ring

theorem alignedBetaGHigherRegular46_order_gt_three
    (beta gamma delta : k) (D E : HahnSeries ℚ k)
    (s Q Y : HahnSeries ℚ k) (a b : ℚ)
    (hD : (0 : WithTop ℚ) ≤ D.orderTop)
    (hE : (0 : WithTop ℚ) ≤ E.orderTop)
    (ha : 0 < a) (hb : 0 < b)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hQ : Q.orderTop = (↑a : WithTop ℚ))
    (hY : Y.orderTop = (↑b : WithTop ℚ)) :
    (↑(3 : ℚ) : WithTop ℚ) <
      (alignedBetaGHigherRegular46 beta gamma delta D E s Q Y).orderTop := by
  have hbase := alignedBetaGHigher46_order_gt_three
    beta gamma delta 0 0 s Q Y a b ha hb hs hQ hY
  have hs4 := hahnOrderTop_pow_eq46 s 1 4 hs
  have hs6 := hahnOrderTop_pow_eq46 s 1 6 hs
  have hQs4 := hahnOrderTop_mul_eq46 Q (s ^ 4) a 4 hQ
    (by simpa using hs4)
  have hDQs4 : (↑(3 : ℚ) : WithTop ℚ) <
      (D * (Q * s ^ 4)).orderTop :=
    regularHahn_mul_exact_orderTop_gt46 D (Q * s ^ 4) (a + 4) 3
      hD hQs4 (by linarith)
  have hDterm : (↑(3 : ℚ) : WithTop ℚ) <
      (HahnSeries.C (-12 : k) * (D * (Q * s ^ 4))).orderTop :=
    hahnOrderTop_C_mul_gt_of_gt46 _ _ _ hDQs4
  have hEs6 : (↑(3 : ℚ) : WithTop ℚ) < (E * s ^ 6).orderTop :=
    regularHahn_mul_exact_orderTop_gt46 E (s ^ 6) 6 3 hE
      (by simpa using hs6) (by norm_num)
  have hEterm : (↑(3 : ℚ) : WithTop ℚ) <
      (HahnSeries.C (8 : k) * (E * s ^ 6)).orderTop :=
    hahnOrderTop_C_mul_gt_of_gt46 _ _ _ hEs6
  dsimp only [alignedBetaGHigherRegular46]
  exact hahnOrderTop_add_gt46 3 _ _
    (hahnOrderTop_add_gt46 3 _ _ hbase hDterm) hEterm

theorem alignedBetaG46_forces_Newton_tie_regular
    (beta gamma delta : k) (D E : HahnSeries ℚ k)
    (s Q Y : HahnSeries ℚ k) (a b : ℚ)
    (hD : (0 : WithTop ℚ) ≤ D.orderTop)
    (hE : (0 : WithTop ℚ) ≤ E.orderTop)
    (ha : 0 < a) (hb : 0 < b) (hbeta : beta ≠ 0)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hQ : Q.orderTop = (↑a : WithTop ℚ))
    (hY : Y.orderTop = (↑b : WithTop ℚ))
    (hG : alignedLocalG46 s Q Y (HahnSeries.C beta) (HahnSeries.C gamma)
      (HahnSeries.C delta) D E = 0) :
    TripleMinimumTied (3 * a) (2 * b) 3 := by
  let p : HahnSeries ℚ k := HahnSeries.C (4 : k) * Q ^ 3
  let q : HahnSeries ℚ k := HahnSeries.C (-3 : k) * Y ^ 2
  let z : HahnSeries ℚ k := HahnSeries.C (4 * beta) * s ^ 3
  let r := alignedBetaGHigherRegular46 beta gamma delta D E s Q Y
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
  have hr3 := alignedBetaGHigherRegular46_order_gt_three
    beta gamma delta D E s Q Y a b hD hE ha hb hs hQ hY
  have hm : min (3 * a) (min (2 * b) 3) ≤ 3 :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hr : (↑(min (3 * a) (min (2 * b) 3)) : WithTop ℚ) < r.orderTop :=
    (WithTop.coe_le_coe.mpr hm).trans_lt hr3
  have hsum : p + q + z + r = 0 := by
    rw [← alignedLocalG46_eq_beta_faces_regular beta gamma delta D E s Q Y]
    exact hG
  exact tripleMinimumTied_of_hahn_sum_add_higher_eq_zero46
    p q z r (3 * a) (2 * b) 3 hp hq hz hr hsum

/-- The beta `J₂` complement of `-6Y²`, with the regular-load
perturbations separated from the scalar-load remainder. -/
def alignedBetaH2ExceptYRegular46
    (beta gamma delta k2 : k) (D : HahnSeries ℚ k)
    (s Q Y : HahnSeries ℚ k) : HahnSeries ℚ k :=
  alignedBetaH2ExceptY46 beta gamma delta 0 k2 s Q Y +
    HahnSeries.C (6 : k) * (D * (Y * s ^ 4)) +
    HahnSeries.C (6 * beta) * (D * s ^ 7)

theorem alignedLocalJTwo46_eq_beta_Y_face_regular
    (beta gamma delta k2 : k) (D : HahnSeries ℚ k)
    (s Q Y : HahnSeries ℚ k) :
    alignedLocalJTwo46 s Q Y (HahnSeries.C beta) (HahnSeries.C gamma)
        (HahnSeries.C delta) D (HahnSeries.C k2) =
      HahnSeries.C (-6 : k) * Y ^ 2 +
        alignedBetaH2ExceptYRegular46 beta gamma delta k2 D s Q Y := by
  simp only [alignedLocalJTwo46, alignedBetaH2ExceptYRegular46,
    alignedBetaH2ExceptY46]
  simp only [map_mul, map_add, map_sub, map_neg, map_ofNat, map_zero,
    mul_zero, add_zero]
  ring

theorem alignedBetaH2ExceptYRegular46_order_gt
    (beta gamma delta k2 : k) (D : HahnSeries ℚ k)
    (s Q Y : HahnSeries ℚ k) (a b : ℚ)
    (hD : (0 : WithTop ℚ) ≤ D.orderTop)
    (ha : 0 < a) (hb : 0 < b)
    (hface : 2 * b < 2 * a + b ∧ 2 * b < 3)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hQ : Q.orderTop = (↑a : WithTop ℚ))
    (hY : Y.orderTop = (↑b : WithTop ℚ)) :
    (↑(2 * b) : WithTop ℚ) <
      (alignedBetaH2ExceptYRegular46 beta gamma delta k2 D s Q Y).orderTop := by
  have hbase := alignedBetaH2ExceptY46_order_gt
    beta gamma delta 0 k2 s Q Y a b ha hb hface hs hQ hY
  have hs4 := hahnOrderTop_pow_eq46 s 1 4 hs
  have hs7 := hahnOrderTop_pow_eq46 s 1 7 hs
  have hYs4 := hahnOrderTop_mul_eq46 Y (s ^ 4) b 4 hY
    (by simpa using hs4)
  have hDYs4 := regularHahn_mul_exact_orderTop_gt46 D (Y * s ^ 4)
    (b + 4) (2 * b) hD hYs4 (by linarith [hface.2])
  have hDterm := hahnOrderTop_C_mul_gt_of_gt46 (6 : k) _ _ hDYs4
  have hDs7 := regularHahn_mul_exact_orderTop_gt46 D (s ^ 7) 7 (2 * b)
    hD (by simpa using hs7) (by linarith [hface.2])
  have hDterm7 := hahnOrderTop_C_mul_gt_of_gt46 (6 * beta) _ _ hDs7
  dsimp only [alignedBetaH2ExceptYRegular46]
  exact hahnOrderTop_add_gt46 (2 * b) _ _
    (hahnOrderTop_add_gt46 (2 * b) _ _ hbase hDterm) hDterm7

/-- The beta `J₂` complement of `3βs³` with a regular load. -/
def alignedBetaH2ExceptS3Regular46
    (beta gamma delta k2 : k) (D : HahnSeries ℚ k)
    (s Q Y : HahnSeries ℚ k) : HahnSeries ℚ k :=
  alignedBetaH2ExceptS346 beta gamma delta 0 k2 s Q Y +
    HahnSeries.C (6 : k) * (D * (Y * s ^ 4)) +
    HahnSeries.C (6 * beta) * (D * s ^ 7)

theorem alignedLocalJTwo46_eq_beta_s3_face_regular
    (beta gamma delta k2 : k) (D : HahnSeries ℚ k)
    (s Q Y : HahnSeries ℚ k) :
    alignedLocalJTwo46 s Q Y (HahnSeries.C beta) (HahnSeries.C gamma)
        (HahnSeries.C delta) D (HahnSeries.C k2) =
      HahnSeries.C (3 * beta) * s ^ 3 +
        alignedBetaH2ExceptS3Regular46 beta gamma delta k2 D s Q Y := by
  simp only [alignedLocalJTwo46, alignedBetaH2ExceptS3Regular46,
    alignedBetaH2ExceptS346]
  simp only [map_mul, map_add, map_sub, map_neg, map_ofNat, map_zero,
    mul_zero, add_zero]
  ring

theorem alignedBetaH2ExceptS3Regular46_order_gt
    (beta gamma delta k2 : k) (D : HahnSeries ℚ k)
    (s Q Y : HahnSeries ℚ k) (a b : ℚ)
    (hD : (0 : WithTop ℚ) ≤ D.orderTop)
    (ha : 0 < a) (hb : 0 < b)
    (hface : 3 < 2 * a + b ∧ 3 < 2 * b)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hQ : Q.orderTop = (↑a : WithTop ℚ))
    (hY : Y.orderTop = (↑b : WithTop ℚ)) :
    (↑(3 : ℚ) : WithTop ℚ) <
      (alignedBetaH2ExceptS3Regular46 beta gamma delta k2 D s Q Y).orderTop := by
  have hbase := alignedBetaH2ExceptS346_order_gt
    beta gamma delta 0 k2 s Q Y a b ha hb hface hs hQ hY
  have hs4 := hahnOrderTop_pow_eq46 s 1 4 hs
  have hs7 := hahnOrderTop_pow_eq46 s 1 7 hs
  have hYs4 := hahnOrderTop_mul_eq46 Y (s ^ 4) b 4 hY
    (by simpa using hs4)
  have hDYs4 := regularHahn_mul_exact_orderTop_gt46 D (Y * s ^ 4)
    (b + 4) 3 hD hYs4 (by linarith)
  have hDterm := hahnOrderTop_C_mul_gt_of_gt46 (6 : k) _ _ hDYs4
  have hDs7 := regularHahn_mul_exact_orderTop_gt46 D (s ^ 7) 7 3 hD
    (by simpa using hs7) (by norm_num)
  have hDterm7 := hahnOrderTop_C_mul_gt_of_gt46 (6 * beta) _ _ hDs7
  dsimp only [alignedBetaH2ExceptS3Regular46]
  exact hahnOrderTop_add_gt46 3 _ _
    (hahnOrderTop_add_gt46 3 _ _ hbase hDterm) hDterm7

/-- The beta `J₁` complement of `6Y²` with a regular load. -/
def alignedBetaH1ExceptYRegular46
    (beta gamma delta k1 : k) (D : HahnSeries ℚ k)
    (s Q Y : HahnSeries ℚ k) : HahnSeries ℚ k :=
  alignedBetaH1ExceptY46 beta gamma delta 0 k1 s Q Y +
    HahnSeries.C (-6 : k) * (D * (Q ^ 2 * s ^ 4)) +
    HahnSeries.C (-6 : k) * (D * (Y * s ^ 4)) +
    HahnSeries.C (4 * gamma) * (D * s ^ 8) +
    HahnSeries.C (3 : k) * (D ^ 2 * s ^ 8)

theorem alignedLocalJOne46_eq_beta_Y_face_regular
    (beta gamma delta k1 : k) (D : HahnSeries ℚ k)
    (s Q Y : HahnSeries ℚ k) :
    alignedLocalJOne46 s Q Y (HahnSeries.C beta) (HahnSeries.C gamma)
        (HahnSeries.C delta) D (HahnSeries.C k1) =
      HahnSeries.C (6 : k) * Y ^ 2 +
        alignedBetaH1ExceptYRegular46 beta gamma delta k1 D s Q Y := by
  simp only [alignedLocalJOne46, alignedBetaH1ExceptYRegular46,
    alignedBetaH1ExceptY46]
  simp only [map_mul, map_add, map_sub, map_neg, map_ofNat, map_zero,
    map_pow, mul_zero, zero_mul, add_zero]
  ring

theorem alignedBetaH1ExceptYRegular46_order_gt
    (beta gamma delta k1 : k) (D : HahnSeries ℚ k)
    (s Q Y : HahnSeries ℚ k) (a b : ℚ)
    (hD : (0 : WithTop ℚ) ≤ D.orderTop)
    (ha : 0 < a) (hb : 0 < b)
    (hGface : TripleMinimumTied (3 * a) (2 * b) 3)
    (hface : 2 * b < 4 * a ∧ 2 * b < 2 * a + b ∧
      2 * b < a + 2 * b)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hQ : Q.orderTop = (↑a : WithTop ℚ))
    (hY : Y.orderTop = (↑b : WithTop ℚ)) :
    (↑(2 * b) : WithTop ℚ) <
      (alignedBetaH1ExceptYRegular46 beta gamma delta k1 D s Q Y).orderTop := by
  have hbase := alignedBetaH1ExceptY46_order_gt
    beta gamma delta 0 k1 s Q Y a b ha hb hGface hface hs hQ hY
  have hb2 : b < 2 := by
    rcases hGface with h | h | h
    · rcases h with ⟨heq, hle⟩
      linarith
    · rcases h with ⟨heq, hle⟩
      linarith [hface.1]
    · rcases h with ⟨heq, hle⟩
      linarith
  have hs4 := hahnOrderTop_pow_eq46 s 1 4 hs
  have hs8 := hahnOrderTop_pow_eq46 s 1 8 hs
  have hQ2 := hahnOrderTop_pow_eq46 Q a 2 hQ
  have hQ2s4 := hahnOrderTop_mul_eq46 (Q ^ 2) (s ^ 4) (2 * a) 4
    (by simpa using hQ2) (by simpa using hs4)
  have hYs4 := hahnOrderTop_mul_eq46 Y (s ^ 4) b 4 hY
    (by simpa using hs4)
  have hDQ := regularHahn_mul_exact_orderTop_gt46 D (Q ^ 2 * s ^ 4)
    (2 * a + 4) (2 * b) hD hQ2s4 (by linarith [hface.2.1])
  have hDQ' := hahnOrderTop_C_mul_gt_of_gt46 (-6 : k) _ _ hDQ
  have hDY := regularHahn_mul_exact_orderTop_gt46 D (Y * s ^ 4)
    (b + 4) (2 * b) hD hYs4 (by linarith [hb2])
  have hDY' := hahnOrderTop_C_mul_gt_of_gt46 (-6 : k) _ _ hDY
  have hDs8 := regularHahn_mul_exact_orderTop_gt46 D (s ^ 8) 8 (2 * b)
    hD (by simpa using hs8) (by linarith [hb2])
  have hDg := hahnOrderTop_C_mul_gt_of_gt46 (4 * gamma) _ _ hDs8
  have hD2 : (0 : WithTop ℚ) ≤ (D ^ 2).orderTop :=
    hahnOrderTop_pow_nonneg46 D 2 hD
  have hD2s8 := regularHahn_mul_exact_orderTop_gt46 (D ^ 2) (s ^ 8)
    8 (2 * b) hD2 (by simpa using hs8) (by linarith [hb2])
  have hD2term := hahnOrderTop_C_mul_gt_of_gt46 (3 : k) _ _ hD2s8
  dsimp only [alignedBetaH1ExceptYRegular46]
  have h12 := hahnOrderTop_add_gt46 (2 * b) _ _ hbase hDQ'
  have h123 := hahnOrderTop_add_gt46 (2 * b) _ _ h12 hDY'
  have h1234 := hahnOrderTop_add_gt46 (2 * b) _ _ h123 hDg
  exact hahnOrderTop_add_gt46 (2 * b) _ _ h1234 hD2term

/-- Nondegenerate beta-stratum exclusion with arbitrary regular loads. -/
theorem alignedBetaFinitePole46_impossible_regular
    (beta gamma delta k2 k1 : k) (D E : HahnSeries ℚ k)
    (s Q Y : HahnSeries ℚ k) (a b : ℚ)
    (hD : (0 : WithTop ℚ) ≤ D.orderTop)
    (hE : (0 : WithTop ℚ) ≤ E.orderTop)
    (ha : 0 < a) (hb : 0 < b) (hbeta : beta ≠ 0)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hQ : Q.orderTop = (↑a : WithTop ℚ))
    (hY : Y.orderTop = (↑b : WithTop ℚ))
    (hG : alignedLocalG46 s Q Y (HahnSeries.C beta) (HahnSeries.C gamma)
      (HahnSeries.C delta) D E = 0)
    (hJ2 : alignedLocalJTwo46 s Q Y (HahnSeries.C beta) (HahnSeries.C gamma)
      (HahnSeries.C delta) D (HahnSeries.C k2) = 0)
    (hJ1 : alignedLocalJOne46 s Q Y (HahnSeries.C beta) (HahnSeries.C gamma)
      (HahnSeries.C delta) D (HahnSeries.C k1) = 0) : False := by
  have hGface := alignedBetaG46_forces_Newton_tie_regular
    beta gamma delta D E s Q Y a b hD hE ha hb hbeta hs hQ hY hG
  rcases alignedBetaNewtonFace46 a b ha hb hGface with hYface | hs3face | hYface
  · let p : HahnSeries ℚ k := HahnSeries.C (-6 : k) * Y ^ 2
    let r := alignedBetaH2ExceptYRegular46 beta gamma delta k2 D s Q Y
    have hY2 := hahnOrderTop_pow_eq46 Y b 2 hY
    have hp : p.orderTop = (↑(2 * b) : WithTop ℚ) := by
      dsimp [p]
      exact hahnOrderTop_C_mul_eq46 _ _ (2 * b) (by norm_num)
        (by simpa using hY2)
    have hr := alignedBetaH2ExceptYRegular46_order_gt
      beta gamma delta k2 D s Q Y a b hD ha hb hYface hs hQ hY
    have hsum : p + r = 0 := by
      rw [← alignedLocalJTwo46_eq_beta_Y_face_regular
        beta gamma delta k2 D s Q Y]
      exact hJ2
    exact hahnExactAddHigher_impossible46 p r (2 * b) hp hr hsum
  · let p : HahnSeries ℚ k := HahnSeries.C (3 * beta) * s ^ 3
    let r := alignedBetaH2ExceptS3Regular46 beta gamma delta k2 D s Q Y
    have hs3 := hahnOrderTop_pow_eq46 s 1 3 hs
    have hp : p.orderTop = (↑(3 : ℚ) : WithTop ℚ) := by
      dsimp [p]
      exact hahnOrderTop_C_mul_eq46 _ _ 3 (mul_ne_zero (by norm_num) hbeta)
        (by simpa using hs3)
    have hr := alignedBetaH2ExceptS3Regular46_order_gt
      beta gamma delta k2 D s Q Y a b hD ha hb hs3face hs hQ hY
    have hsum : p + r = 0 := by
      rw [← alignedLocalJTwo46_eq_beta_s3_face_regular
        beta gamma delta k2 D s Q Y]
      exact hJ2
    exact hahnExactAddHigher_impossible46 p r 3 hp hr hsum
  · let p : HahnSeries ℚ k := HahnSeries.C (6 : k) * Y ^ 2
    let r := alignedBetaH1ExceptYRegular46 beta gamma delta k1 D s Q Y
    have hY2 := hahnOrderTop_pow_eq46 Y b 2 hY
    have hp : p.orderTop = (↑(2 * b) : WithTop ℚ) := by
      dsimp [p]
      exact hahnOrderTop_C_mul_eq46 _ _ (2 * b) (by norm_num)
        (by simpa using hY2)
    have hr := alignedBetaH1ExceptYRegular46_order_gt
      beta gamma delta k1 D s Q Y a b hD ha hb hGface hYface hs hQ hY
    have hsum : p + r = 0 := by
      rw [← alignedLocalJOne46_eq_beta_Y_face_regular
        beta gamma delta k1 D s Q Y]
      exact hJ1
    exact hahnExactAddHigher_impossible46 p r (2 * b) hp hr hsum

end AlignedBetaRegularLoads

section AlignedDeltaRegularLoads

variable {k : Type*} [Field k] [CharZero k]

/-- The delta-face remainder with arbitrary regular boundary loads. -/
def alignedDeltaGHigherRegular46
    (gamma : k) (D E : HahnSeries ℚ k)
    (s Q : HahnSeries ℚ k) : HahnSeries ℚ k :=
  alignedDeltaGHigher46 gamma 0 0 s Q +
    HahnSeries.C (-12 : k) * (D * (Q * s ^ 4)) +
    HahnSeries.C (8 : k) * (E * s ^ 6)

theorem alignedLocalG46_eq_delta_faces_regular
    (gamma delta : k) (D E : HahnSeries ℚ k)
    (s Q Y : HahnSeries ℚ k) :
    alignedLocalG46 s Q Y 0 (HahnSeries.C gamma)
        (HahnSeries.C delta) D E =
      HahnSeries.C (4 : k) * Q ^ 3 +
        HahnSeries.C (-3 : k) * Y ^ 2 +
        HahnSeries.C (-8 * delta) * s ^ 5 +
        alignedDeltaGHigherRegular46 gamma D E s Q := by
  simp only [alignedLocalG46, alignedDeltaGHigherRegular46,
    alignedDeltaGHigher46]
  simp only [map_mul, map_add, map_neg, map_ofNat, map_zero, mul_zero,
    zero_mul, add_zero]
  ring

theorem alignedDeltaGHigherRegular46_order_gt_min
    (gamma : k) (D E : HahnSeries ℚ k)
    (s Q : HahnSeries ℚ k) (a b : ℚ)
    (hD : (0 : WithTop ℚ) ≤ D.orderTop)
    (hE : (0 : WithTop ℚ) ≤ E.orderTop)
    (ha : 0 < a)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hQ : Q.orderTop = (↑a : WithTop ℚ)) :
    (↑(min (3 * a) (min (2 * b) 5)) : WithTop ℚ) <
      (alignedDeltaGHigherRegular46 gamma D E s Q).orderTop := by
  let m := min (3 * a) (min (2 * b) 5)
  have hbase := alignedDeltaGHigher46_order_gt_min gamma 0 0 s Q a b ha hs hQ
  have hs4 := hahnOrderTop_pow_eq46 s 1 4 hs
  have hs6 := hahnOrderTop_pow_eq46 s 1 6 hs
  have hQs4 := hahnOrderTop_mul_eq46 Q (s ^ 4) a 4 hQ
    (by simpa using hs4)
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
  have hDQs4 := regularHahn_mul_exact_orderTop_gt46 D (Q * s ^ 4)
    (a + 4) m hD hQs4 hmQa
  have hDterm := hahnOrderTop_C_mul_gt_of_gt46 (-12 : k) _ _ hDQs4
  have hEs6 := regularHahn_mul_exact_orderTop_gt46 E (s ^ 6) 6 m hE
    (by simpa using hs6) hm6
  have hEterm := hahnOrderTop_C_mul_gt_of_gt46 (8 : k) _ _ hEs6
  dsimp only [alignedDeltaGHigherRegular46]
  exact hahnOrderTop_add_gt46 m _ _
    (hahnOrderTop_add_gt46 m _ _ hbase hDterm) hEterm

theorem alignedDeltaG46_forces_Newton_tie_regular
    (gamma delta : k) (D E : HahnSeries ℚ k)
    (s Q Y : HahnSeries ℚ k) (a b : ℚ)
    (hD : (0 : WithTop ℚ) ≤ D.orderTop)
    (hE : (0 : WithTop ℚ) ≤ E.orderTop)
    (ha : 0 < a) (hdelta : delta ≠ 0)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hQ : Q.orderTop = (↑a : WithTop ℚ))
    (hY : Y.orderTop = (↑b : WithTop ℚ))
    (hG : alignedLocalG46 s Q Y 0 (HahnSeries.C gamma)
      (HahnSeries.C delta) D E = 0) :
    TripleMinimumTied (3 * a) (2 * b) 5 := by
  let p : HahnSeries ℚ k := HahnSeries.C (4 : k) * Q ^ 3
  let q : HahnSeries ℚ k := HahnSeries.C (-3 : k) * Y ^ 2
  let z : HahnSeries ℚ k := HahnSeries.C (-8 * delta) * s ^ 5
  let r := alignedDeltaGHigherRegular46 gamma D E s Q
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
  have hr := alignedDeltaGHigherRegular46_order_gt_min
    gamma D E s Q a b hD hE ha hs hQ
  have hsum : p + q + z + r = 0 := by
    rw [← alignedLocalG46_eq_delta_faces_regular gamma delta D E s Q Y]
    exact hG
  exact tripleMinimumTied_of_hahn_sum_add_higher_eq_zero46
    p q z r (3 * a) (2 * b) 5 hp hq hz hr hsum

def alignedDeltaH2ExceptYRegular46
    (gamma delta k2 : k) (D : HahnSeries ℚ k)
    (s Q Y : HahnSeries ℚ k) : HahnSeries ℚ k :=
  alignedDeltaH2ExceptY46 gamma delta 0 k2 s Q Y +
    HahnSeries.C (6 : k) * (D * (Y * s ^ 4))

theorem alignedLocalJTwo46_eq_delta_Y_face_regular
    (gamma delta k2 : k) (D : HahnSeries ℚ k)
    (s Q Y : HahnSeries ℚ k) :
    alignedLocalJTwo46 s Q Y 0 (HahnSeries.C gamma)
        (HahnSeries.C delta) D (HahnSeries.C k2) =
      HahnSeries.C (-6 : k) * Y ^ 2 +
        alignedDeltaH2ExceptYRegular46 gamma delta k2 D s Q Y := by
  simp only [alignedLocalJTwo46, alignedDeltaH2ExceptYRegular46,
    alignedDeltaH2ExceptY46]
  simp only [map_mul, map_add, map_neg, map_ofNat, map_zero, mul_zero,
    zero_mul, add_zero]
  ring

theorem alignedDeltaH2ExceptYRegular46_order_gt
    (gamma delta k2 : k) (D : HahnSeries ℚ k)
    (s Q Y : HahnSeries ℚ k) (a b : ℚ)
    (hD : (0 : WithTop ℚ) ≤ D.orderTop)
    (hface : 2 * b < 2 * a + b ∧ 2 * b < 4 + b ∧ 2 * b < 5)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hQ : Q.orderTop = (↑a : WithTop ℚ))
    (hY : Y.orderTop = (↑b : WithTop ℚ)) :
    (↑(2 * b) : WithTop ℚ) <
      (alignedDeltaH2ExceptYRegular46 gamma delta k2 D s Q Y).orderTop := by
  have hbase := alignedDeltaH2ExceptY46_order_gt
    gamma delta 0 k2 s Q Y a b hface hs hQ hY
  have hs4 := hahnOrderTop_pow_eq46 s 1 4 hs
  have hYs4 := hahnOrderTop_mul_eq46 Y (s ^ 4) b 4 hY
    (by simpa using hs4)
  have hDY := regularHahn_mul_exact_orderTop_gt46 D (Y * s ^ 4)
    (b + 4) (2 * b) hD hYs4 (by linarith [hface.2.1])
  have hDY' := hahnOrderTop_C_mul_gt_of_gt46 (6 : k) _ _ hDY
  dsimp only [alignedDeltaH2ExceptYRegular46]
  exact hahnOrderTop_add_gt46 (2 * b) _ _ hbase hDY'

def alignedDeltaH2ExceptS5Regular46
    (gamma delta k2 : k) (D : HahnSeries ℚ k)
    (s Q Y : HahnSeries ℚ k) : HahnSeries ℚ k :=
  alignedDeltaH2ExceptS546 gamma delta 0 k2 s Q Y +
    HahnSeries.C (6 : k) * (D * (Y * s ^ 4))

theorem alignedLocalJTwo46_eq_delta_s5_face_regular
    (gamma delta k2 : k) (D : HahnSeries ℚ k)
    (s Q Y : HahnSeries ℚ k) :
    alignedLocalJTwo46 s Q Y 0 (HahnSeries.C gamma)
        (HahnSeries.C delta) D (HahnSeries.C k2) =
      HahnSeries.C (-4 * delta) * s ^ 5 +
        alignedDeltaH2ExceptS5Regular46 gamma delta k2 D s Q Y := by
  simp only [alignedLocalJTwo46, alignedDeltaH2ExceptS5Regular46,
    alignedDeltaH2ExceptS546]
  simp only [map_mul, map_add, map_neg, map_ofNat, map_zero, mul_zero,
    zero_mul, add_zero]
  ring

theorem alignedDeltaH2ExceptS5Regular46_order_gt
    (gamma delta k2 : k) (D : HahnSeries ℚ k)
    (s Q Y : HahnSeries ℚ k) (a b : ℚ)
    (hD : (0 : WithTop ℚ) ≤ D.orderTop)
    (ha : 0 < a)
    (hface : 5 < 2 * a + b ∧ 5 < 2 * b ∧ 5 < 4 + b)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hQ : Q.orderTop = (↑a : WithTop ℚ))
    (hY : Y.orderTop = (↑b : WithTop ℚ)) :
    (↑(5 : ℚ) : WithTop ℚ) <
      (alignedDeltaH2ExceptS5Regular46 gamma delta k2 D s Q Y).orderTop := by
  have hbase := alignedDeltaH2ExceptS546_order_gt
    gamma delta 0 k2 s Q Y a b ha hface hs hQ hY
  have hs4 := hahnOrderTop_pow_eq46 s 1 4 hs
  have hYs4 := hahnOrderTop_mul_eq46 Y (s ^ 4) b 4 hY
    (by simpa using hs4)
  have hDY := regularHahn_mul_exact_orderTop_gt46 D (Y * s ^ 4)
    (b + 4) 5 hD hYs4 (by linarith [hface.2.2])
  have hDY' := hahnOrderTop_C_mul_gt_of_gt46 (6 : k) _ _ hDY
  dsimp only [alignedDeltaH2ExceptS5Regular46]
  exact hahnOrderTop_add_gt46 5 _ _ hbase hDY'

def alignedDeltaH1ExceptYRegular46
    (gamma delta k1 : k) (D : HahnSeries ℚ k)
    (s Q Y : HahnSeries ℚ k) : HahnSeries ℚ k :=
  alignedDeltaH1ExceptY46 gamma delta 0 k1 s Q Y +
    HahnSeries.C (-6 : k) * (D * (Q ^ 2 * s ^ 4)) +
    HahnSeries.C (-6 : k) * (D * (Y * s ^ 4)) +
    HahnSeries.C (4 * gamma) * (D * s ^ 8) +
    HahnSeries.C (3 : k) * (D ^ 2 * s ^ 8)

theorem alignedLocalJOne46_eq_delta_Y_face_regular
    (gamma delta k1 : k) (D : HahnSeries ℚ k)
    (s Q Y : HahnSeries ℚ k) :
    alignedLocalJOne46 s Q Y 0 (HahnSeries.C gamma)
        (HahnSeries.C delta) D (HahnSeries.C k1) =
      HahnSeries.C (6 : k) * Y ^ 2 +
        alignedDeltaH1ExceptYRegular46 gamma delta k1 D s Q Y := by
  simp only [alignedLocalJOne46, alignedDeltaH1ExceptYRegular46,
    alignedDeltaH1ExceptY46]
  simp only [map_mul, map_add, map_sub, map_neg, map_ofNat, map_zero,
    map_pow, mul_zero, zero_mul, add_zero]
  ring

theorem alignedDeltaH1ExceptYRegular46_order_gt
    (gamma delta k1 : k) (D : HahnSeries ℚ k)
    (s Q Y : HahnSeries ℚ k) (a b : ℚ)
    (hD : (0 : WithTop ℚ) ≤ D.orderTop)
    (hface : 2 * b < 4 * a ∧ 2 * b < 2 * a + b ∧
      2 * b < a + 2 * b ∧ 2 * b < 4 + 2 * a ∧
      2 * b < 4 + b ∧ 2 * b < 5 + b ∧ 2 * b < 8)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hQ : Q.orderTop = (↑a : WithTop ℚ))
    (hY : Y.orderTop = (↑b : WithTop ℚ)) :
    (↑(2 * b) : WithTop ℚ) <
      (alignedDeltaH1ExceptYRegular46 gamma delta k1 D s Q Y).orderTop := by
  have hbase := alignedDeltaH1ExceptY46_order_gt
    gamma delta 0 k1 s Q Y a b hface hs hQ hY
  have hs4 := hahnOrderTop_pow_eq46 s 1 4 hs
  have hs8 := hahnOrderTop_pow_eq46 s 1 8 hs
  have hQ2 := hahnOrderTop_pow_eq46 Q a 2 hQ
  have hQ2s4 := hahnOrderTop_mul_eq46 (Q ^ 2) (s ^ 4) (2 * a) 4
    (by simpa using hQ2) (by simpa using hs4)
  have hYs4 := hahnOrderTop_mul_eq46 Y (s ^ 4) b 4 hY
    (by simpa using hs4)
  have hDQ := regularHahn_mul_exact_orderTop_gt46 D (Q ^ 2 * s ^ 4)
    (2 * a + 4) (2 * b) hD hQ2s4 (by linarith [hface.2.2.2.1])
  have hDQ' := hahnOrderTop_C_mul_gt_of_gt46 (-6 : k) _ _ hDQ
  have hDY := regularHahn_mul_exact_orderTop_gt46 D (Y * s ^ 4)
    (b + 4) (2 * b) hD hYs4 (by linarith [hface.2.2.2.2.1])
  have hDY' := hahnOrderTop_C_mul_gt_of_gt46 (-6 : k) _ _ hDY
  have hDs8 := regularHahn_mul_exact_orderTop_gt46 D (s ^ 8) 8 (2 * b)
    hD (by simpa using hs8) hface.2.2.2.2.2.2
  have hDg := hahnOrderTop_C_mul_gt_of_gt46 (4 * gamma) _ _ hDs8
  have hD2 : (0 : WithTop ℚ) ≤ (D ^ 2).orderTop :=
    hahnOrderTop_pow_nonneg46 D 2 hD
  have hD2s8 := regularHahn_mul_exact_orderTop_gt46 (D ^ 2) (s ^ 8)
    8 (2 * b) hD2 (by simpa using hs8) hface.2.2.2.2.2.2
  have hD2term := hahnOrderTop_C_mul_gt_of_gt46 (3 : k) _ _ hD2s8
  dsimp only [alignedDeltaH1ExceptYRegular46]
  have h12 := hahnOrderTop_add_gt46 (2 * b) _ _ hbase hDQ'
  have h123 := hahnOrderTop_add_gt46 (2 * b) _ _ h12 hDY'
  have h1234 := hahnOrderTop_add_gt46 (2 * b) _ _ h123 hDg
  exact hahnOrderTop_add_gt46 (2 * b) _ _ h1234 hD2term

/-- Nondegenerate delta-stratum exclusion with arbitrary regular loads. -/
theorem alignedDeltaFinitePole46_impossible_regular
    (gamma delta k2 k1 : k) (D E : HahnSeries ℚ k)
    (s Q Y : HahnSeries ℚ k) (a b : ℚ)
    (hD : (0 : WithTop ℚ) ≤ D.orderTop)
    (hE : (0 : WithTop ℚ) ≤ E.orderTop)
    (ha : 0 < a) (hb : 0 < b) (hdelta : delta ≠ 0)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hQ : Q.orderTop = (↑a : WithTop ℚ))
    (hY : Y.orderTop = (↑b : WithTop ℚ))
    (hG : alignedLocalG46 s Q Y 0 (HahnSeries.C gamma)
      (HahnSeries.C delta) D E = 0)
    (hJ2 : alignedLocalJTwo46 s Q Y 0 (HahnSeries.C gamma)
      (HahnSeries.C delta) D (HahnSeries.C k2) = 0)
    (hJ1 : alignedLocalJOne46 s Q Y 0 (HahnSeries.C gamma)
      (HahnSeries.C delta) D (HahnSeries.C k1) = 0) : False := by
  have hGtriple := alignedDeltaG46_forces_Newton_tie_regular
    gamma delta D E s Q Y a b hD hE ha hdelta hs hQ hY hG
  have hGquad := alignedDeltaQuadrupleTie_of_triple46 a b ha hGtriple
  rcases alignedDeltaNewtonFace46 a b ha hb hGquad with hYface | hs5face | hYface
  · let p : HahnSeries ℚ k := HahnSeries.C (-6 : k) * Y ^ 2
    let r := alignedDeltaH2ExceptYRegular46 gamma delta k2 D s Q Y
    have hY2 := hahnOrderTop_pow_eq46 Y b 2 hY
    have hp : p.orderTop = (↑(2 * b) : WithTop ℚ) := by
      dsimp [p]
      exact hahnOrderTop_C_mul_eq46 _ _ (2 * b) (by norm_num)
        (by simpa using hY2)
    have hr := alignedDeltaH2ExceptYRegular46_order_gt
      gamma delta k2 D s Q Y a b hD hYface hs hQ hY
    have hsum : p + r = 0 := by
      rw [← alignedLocalJTwo46_eq_delta_Y_face_regular
        gamma delta k2 D s Q Y]
      exact hJ2
    exact hahnExactAddHigher_impossible46 p r (2 * b) hp hr hsum
  · let p : HahnSeries ℚ k := HahnSeries.C (-4 * delta) * s ^ 5
    let r := alignedDeltaH2ExceptS5Regular46 gamma delta k2 D s Q Y
    have hs5 := hahnOrderTop_pow_eq46 s 1 5 hs
    have hp : p.orderTop = (↑(5 : ℚ) : WithTop ℚ) := by
      dsimp [p]
      exact hahnOrderTop_C_mul_eq46 _ _ 5 (mul_ne_zero (by norm_num) hdelta)
        (by simpa using hs5)
    have hr := alignedDeltaH2ExceptS5Regular46_order_gt
      gamma delta k2 D s Q Y a b hD ha hs5face hs hQ hY
    have hsum : p + r = 0 := by
      rw [← alignedLocalJTwo46_eq_delta_s5_face_regular
        gamma delta k2 D s Q Y]
      exact hJ2
    exact hahnExactAddHigher_impossible46 p r 5 hp hr hsum
  · let p : HahnSeries ℚ k := HahnSeries.C (6 : k) * Y ^ 2
    let r := alignedDeltaH1ExceptYRegular46 gamma delta k1 D s Q Y
    have hY2 := hahnOrderTop_pow_eq46 Y b 2 hY
    have hp : p.orderTop = (↑(2 * b) : WithTop ℚ) := by
      dsimp [p]
      exact hahnOrderTop_C_mul_eq46 _ _ (2 * b) (by norm_num)
        (by simpa using hY2)
    have hr := alignedDeltaH1ExceptYRegular46_order_gt
      gamma delta k1 D s Q Y a b hD hYface hs hQ hY
    have hsum : p + r = 0 := by
      rw [← alignedLocalJOne46_eq_delta_Y_face_regular
        gamma delta k1 D s Q Y]
      exact hJ1
    exact hahnExactAddHigher_impossible46 p r (2 * b) hp hr hsum

end AlignedDeltaRegularLoads

section AlignedDegenerateRegularLoads

variable {k : Type*} [Field k] [CharZero k]

/-- The `Q=0` complement of `6Y²`, split into its scalar part and the
terms contributed by a regular first boundary load. -/
def alignedQZeroH1HigherRegular46
    (beta gamma delta k1 : k) (D : HahnSeries ℚ k)
    (s Y : HahnSeries ℚ k) : HahnSeries ℚ k :=
  alignedQZeroH1Higher46 beta gamma delta 0 k1 s Y +
    HahnSeries.C (-6 : k) * (D * (Y * s ^ 4)) +
    HahnSeries.C (4 * gamma) * (D * s ^ 8) +
    HahnSeries.C (3 : k) * (D ^ 2 * s ^ 8)

theorem alignedLocalJOne46_Q_zero_eq_regular
    (beta gamma delta k1 : k) (D : HahnSeries ℚ k)
    (s Y : HahnSeries ℚ k) :
    alignedLocalJOne46 s 0 Y (HahnSeries.C beta) (HahnSeries.C gamma)
        (HahnSeries.C delta) D (HahnSeries.C k1) =
      HahnSeries.C (6 : k) * Y ^ 2 +
        alignedQZeroH1HigherRegular46 beta gamma delta k1 D s Y := by
  simp only [alignedLocalJOne46, alignedQZeroH1HigherRegular46,
    alignedQZeroH1Higher46]
  simp only [map_mul, map_add, map_sub, map_neg, map_ofNat, map_zero,
    map_pow, zero_mul, mul_zero, add_zero]
  ring

theorem alignedQZeroH1HigherRegular46_order_gt
    (beta gamma delta k1 : k) (D : HahnSeries ℚ k)
    (s Y : HahnSeries ℚ k) (b : ℚ)
    (hD : (0 : WithTop ℚ) ≤ D.orderTop)
    (hb3 : b < 3) (hb8 : 2 * b < 8)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hY : Y.orderTop = (↑b : WithTop ℚ)) :
    (↑(2 * b) : WithTop ℚ) <
      (alignedQZeroH1HigherRegular46 beta gamma delta k1 D s Y).orderTop := by
  have hbase := alignedQZeroH1Higher46_order_gt
    beta gamma delta 0 k1 s Y b hb3 hb8 hs hY
  have hs4 := hahnOrderTop_pow_eq46 s 1 4 hs
  have hs8 := hahnOrderTop_pow_eq46 s 1 8 hs
  have hYs4 := hahnOrderTop_mul_eq46 Y (s ^ 4) b 4 hY
    (by simpa using hs4)
  have hDY := regularHahn_mul_exact_orderTop_gt46 D (Y * s ^ 4)
    (b + 4) (2 * b) hD hYs4 (by linarith [hb3])
  have hDY' := hahnOrderTop_C_mul_gt_of_gt46 (-6 : k) _ _ hDY
  have hDs8 := regularHahn_mul_exact_orderTop_gt46 D (s ^ 8) 8 (2 * b)
    hD (by simpa using hs8) hb8
  have hDg := hahnOrderTop_C_mul_gt_of_gt46 (4 * gamma) _ _ hDs8
  have hD2 : (0 : WithTop ℚ) ≤ (D ^ 2).orderTop :=
    hahnOrderTop_pow_nonneg46 D 2 hD
  have hD2s8 := regularHahn_mul_exact_orderTop_gt46 (D ^ 2) (s ^ 8)
    8 (2 * b) hD2 (by simpa using hs8) hb8
  have hD2term := hahnOrderTop_C_mul_gt_of_gt46 (3 : k) _ _ hD2s8
  dsimp only [alignedQZeroH1HigherRegular46]
  have h12 := hahnOrderTop_add_gt46 (2 * b) _ _ hbase hDY'
  have h123 := hahnOrderTop_add_gt46 (2 * b) _ _ h12 hDg
  exact hahnOrderTop_add_gt46 (2 * b) _ _ h123 hD2term

def alignedBetaQZeroGHigherRegular46
    (beta delta : k) (E : HahnSeries ℚ k)
    (s Y : HahnSeries ℚ k) : HahnSeries ℚ k :=
  alignedBetaQZeroGHigher46 beta delta 0 s Y +
    HahnSeries.C (8 : k) * (E * s ^ 6)

theorem alignedLocalG46_beta_Q_zero_eq_regular
    (beta gamma delta : k) (D E : HahnSeries ℚ k)
    (s Y : HahnSeries ℚ k) :
    alignedLocalG46 s 0 Y (HahnSeries.C beta) (HahnSeries.C gamma)
        (HahnSeries.C delta) D E =
      HahnSeries.C (-3 : k) * Y ^ 2 +
        HahnSeries.C (4 * beta) * s ^ 3 +
        alignedBetaQZeroGHigherRegular46 beta delta E s Y := by
  simp only [alignedLocalG46, alignedBetaQZeroGHigherRegular46,
    alignedBetaQZeroGHigher46]
  simp only [map_mul, map_add, map_neg, map_ofNat, map_zero, zero_mul,
    mul_zero, add_zero]
  ring

theorem alignedBetaQZeroGHigherRegular46_order_gt_three
    (beta delta : k) (E : HahnSeries ℚ k)
    (s Y : HahnSeries ℚ k) (b : ℚ)
    (hE : (0 : WithTop ℚ) ≤ E.orderTop) (hb : 0 < b)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hY : Y.orderTop = (↑b : WithTop ℚ)) :
    (↑(3 : ℚ) : WithTop ℚ) <
      (alignedBetaQZeroGHigherRegular46 beta delta E s Y).orderTop := by
  have hbase := alignedBetaQZeroGHigher46_order_gt_three
    beta delta 0 s Y b hb hs hY
  have hs6 := hahnOrderTop_pow_eq46 s 1 6 hs
  have hEs6 := regularHahn_mul_exact_orderTop_gt46 E (s ^ 6) 6 3 hE
    (by simpa using hs6) (by norm_num)
  have hEterm := hahnOrderTop_C_mul_gt_of_gt46 (8 : k) _ _ hEs6
  dsimp only [alignedBetaQZeroGHigherRegular46]
  exact hahnOrderTop_add_gt46 3 _ _ hbase hEterm

theorem alignedBetaQZeroFinitePole46_impossible_regular
    (beta gamma delta k1 : k) (D E : HahnSeries ℚ k)
    (s Q Y : HahnSeries ℚ k) (b : ℚ)
    (hD : (0 : WithTop ℚ) ≤ D.orderTop)
    (hE : (0 : WithTop ℚ) ≤ E.orderTop)
    (hb : 0 < b) (hbeta : beta ≠ 0)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hY : Y.orderTop = (↑b : WithTop ℚ)) (hQzero : Q = 0)
    (hG : alignedLocalG46 s Q Y (HahnSeries.C beta) (HahnSeries.C gamma)
      (HahnSeries.C delta) D E = 0)
    (hJ1 : alignedLocalJOne46 s Q Y (HahnSeries.C beta) (HahnSeries.C gamma)
      (HahnSeries.C delta) D (HahnSeries.C k1) = 0) : False := by
  have hGzero : alignedLocalG46 s 0 Y (HahnSeries.C beta)
      (HahnSeries.C gamma) (HahnSeries.C delta) D E = 0 := by
    simpa [hQzero] using hG
  let p : HahnSeries ℚ k := HahnSeries.C (-3 : k) * Y ^ 2
  let q : HahnSeries ℚ k := HahnSeries.C (4 * beta) * s ^ 3
  let r := alignedBetaQZeroGHigherRegular46 beta delta E s Y
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
  have hr := alignedBetaQZeroGHigherRegular46_order_gt_three
    beta delta E s Y b hE hb hs hY
  have hsum : p + q + r = 0 := by
    rw [← alignedLocalG46_beta_Q_zero_eq_regular
      beta gamma delta D E s Y]
    exact hGzero
  have h2b : 2 * b = 3 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hq0 : q.coeff (2 * b) = 0 :=
        HahnSeries.coeff_eq_zero_of_lt_orderTop (by
          rw [hq]
          exact WithTop.coe_lt_coe.mpr hlt)
      have hr0 : r.coeff (2 * b) = 0 :=
        HahnSeries.coeff_eq_zero_of_lt_orderTop
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
  have hJ1zero : alignedLocalJOne46 s 0 Y (HahnSeries.C beta)
      (HahnSeries.C gamma) (HahnSeries.C delta) D (HahnSeries.C k1) = 0 := by
    simpa [hQzero] using hJ1
  let p1 : HahnSeries ℚ k := HahnSeries.C (6 : k) * Y ^ 2
  let r1 := alignedQZeroH1HigherRegular46 beta gamma delta k1 D s Y
  have hp1 : p1.orderTop = (↑(2 * b) : WithTop ℚ) := by
    dsimp [p1]
    exact hahnOrderTop_C_mul_eq46 _ _ (2 * b) (by norm_num)
      (by simpa using hY2)
  have hr1 := alignedQZeroH1HigherRegular46_order_gt
    beta gamma delta k1 D s Y b hD (by linarith) (by linarith) hs hY
  have hsum1 : p1 + r1 = 0 := by
    rw [← alignedLocalJOne46_Q_zero_eq_regular
      beta gamma delta k1 D s Y]
    exact hJ1zero
  exact hahnExactAddHigher_impossible46 p1 r1 (2 * b) hp1 hr1 hsum1

def alignedBetaYZeroH2HigherRegular46
    (beta delta k2 : k) (D : HahnSeries ℚ k)
    (s Q : HahnSeries ℚ k) : HahnSeries ℚ k :=
  alignedBetaYZeroH2Higher46 beta delta 0 k2 s Q +
    HahnSeries.C (6 * beta) * (D * s ^ 7)

theorem alignedLocalJTwo46_beta_Y_zero_eq_regular
    (beta gamma delta k2 : k) (D : HahnSeries ℚ k)
    (s Q : HahnSeries ℚ k) :
    alignedLocalJTwo46 s Q 0 (HahnSeries.C beta) (HahnSeries.C gamma)
        (HahnSeries.C delta) D (HahnSeries.C k2) =
      HahnSeries.C (3 * beta) * s ^ 3 +
        alignedBetaYZeroH2HigherRegular46 beta delta k2 D s Q := by
  simp only [alignedLocalJTwo46, alignedBetaYZeroH2HigherRegular46,
    alignedBetaYZeroH2Higher46]
  simp only [map_mul, map_add, map_sub, map_neg, map_ofNat, map_zero,
    zero_mul, mul_zero, add_zero]
  ring

theorem alignedBetaYZeroH2HigherRegular46_order_gt_three
    (beta delta k2 : k) (D : HahnSeries ℚ k)
    (s Q : HahnSeries ℚ k)
    (hD : (0 : WithTop ℚ) ≤ D.orderTop)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hQ : (↑(0 : ℚ) : WithTop ℚ) < Q.orderTop) :
    (↑(3 : ℚ) : WithTop ℚ) <
      (alignedBetaYZeroH2HigherRegular46 beta delta k2 D s Q).orderTop := by
  have hbase := alignedBetaYZeroH2Higher46_order_gt_three
    beta delta 0 k2 s Q hs hQ
  have hs7 := hahnOrderTop_pow_eq46 s 1 7 hs
  have hDs7 := regularHahn_mul_exact_orderTop_gt46 D (s ^ 7) 7 3 hD
    (by simpa using hs7) (by norm_num)
  have hDterm := hahnOrderTop_C_mul_gt_of_gt46 (6 * beta) _ _ hDs7
  dsimp only [alignedBetaYZeroH2HigherRegular46]
  exact hahnOrderTop_add_gt46 3 _ _ hbase hDterm

theorem alignedBetaYZeroFinitePole46_impossible_regular
    (beta gamma delta k2 : k) (D : HahnSeries ℚ k)
    (s Q Y : HahnSeries ℚ k)
    (hD : (0 : WithTop ℚ) ≤ D.orderTop)
    (hbeta : beta ≠ 0) (hYzero : Y = 0)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hQ : (↑(0 : ℚ) : WithTop ℚ) < Q.orderTop)
    (hJ2 : alignedLocalJTwo46 s Q Y (HahnSeries.C beta) (HahnSeries.C gamma)
      (HahnSeries.C delta) D (HahnSeries.C k2) = 0) : False := by
  let p : HahnSeries ℚ k := HahnSeries.C (3 * beta) * s ^ 3
  let r := alignedBetaYZeroH2HigherRegular46 beta delta k2 D s Q
  have hs3 := hahnOrderTop_pow_eq46 s 1 3 hs
  have hp : p.orderTop = (↑(3 : ℚ) : WithTop ℚ) := by
    dsimp [p]
    exact hahnOrderTop_C_mul_eq46 _ _ 3 (mul_ne_zero (by norm_num) hbeta)
      (by simpa using hs3)
  have hr := alignedBetaYZeroH2HigherRegular46_order_gt_three
    beta delta k2 D s Q hD hs hQ
  have hsum : p + r = 0 := by
    rw [← alignedLocalJTwo46_beta_Y_zero_eq_regular
      beta gamma delta k2 D s Q]
    simpa [hYzero] using hJ2
  exact hahnExactAddHigher_impossible46 p r 3 hp hr hsum

/-- The delta `Y=0` equation is independent of the first load. -/
theorem alignedDeltaYZeroFinitePole46_impossible_regular
    (gamma delta k2 : k) (D : HahnSeries ℚ k)
    (s Q Y : HahnSeries ℚ k)
    (hdelta : delta ≠ 0) (hYzero : Y = 0)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hQ : (↑(0 : ℚ) : WithTop ℚ) < Q.orderTop)
    (hJ2 : alignedLocalJTwo46 s Q Y 0 (HahnSeries.C gamma)
      (HahnSeries.C delta) D (HahnSeries.C k2) = 0) : False := by
  apply alignedDeltaYZeroFinitePole46_impossible
    gamma delta 0 k2 s Q Y hdelta hYzero hs hQ
  simpa [alignedLocalJTwo46, hYzero] using hJ2

theorem alignedDeltaQZeroFinitePole46_impossible_regular
    (gamma delta k1 : k) (D E : HahnSeries ℚ k)
    (s Q Y : HahnSeries ℚ k) (b : ℚ)
    (hD : (0 : WithTop ℚ) ≤ D.orderTop)
    (hE : (0 : WithTop ℚ) ≤ E.orderTop)
    (hb : 0 < b) (hdelta : delta ≠ 0)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hY : Y.orderTop = (↑b : WithTop ℚ)) (hQzero : Q = 0)
    (hG : alignedLocalG46 s Q Y 0 (HahnSeries.C gamma)
      (HahnSeries.C delta) D E = 0)
    (hJ1 : alignedLocalJOne46 s Q Y 0 (HahnSeries.C gamma)
      (HahnSeries.C delta) D (HahnSeries.C k1) = 0) : False := by
  have hGzero : alignedLocalG46 s 0 Y 0 (HahnSeries.C gamma)
      (HahnSeries.C delta) D E = 0 := by simpa [hQzero] using hG
  let p : HahnSeries ℚ k := HahnSeries.C (-3 : k) * Y ^ 2
  let q : HahnSeries ℚ k := HahnSeries.C (-8 * delta) * s ^ 5
  let r : HahnSeries ℚ k := HahnSeries.C (8 : k) * (E * s ^ 6)
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
  have hEs6 := regularHahn_mul_exact_orderTop_gt46 E (s ^ 6) 6 5 hE
    (by simpa using hs6) (by norm_num)
  have hr : (↑(5 : ℚ) : WithTop ℚ) < r.orderTop := by
    dsimp [r]
    exact hahnOrderTop_C_mul_gt_of_gt46 (8 : k) _ _ hEs6
  have hsum : p + q + r = 0 := by
    dsimp [p, q, r]
    simp only [alignedLocalG46, mul_zero, zero_mul, add_zero, sub_zero]
      at hGzero
    simp only [map_mul, map_add, map_neg, map_ofNat]
    rw [← hGzero]
    ring
  have h2b : 2 * b = 5 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hq0 : q.coeff (2 * b) = 0 :=
        HahnSeries.coeff_eq_zero_of_lt_orderTop (by
          rw [hq]
          exact WithTop.coe_lt_coe.mpr hlt)
      have hr0 : r.coeff (2 * b) = 0 :=
        HahnSeries.coeff_eq_zero_of_lt_orderTop
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
  have hJ1zero : alignedLocalJOne46 s 0 Y 0 (HahnSeries.C gamma)
      (HahnSeries.C delta) D (HahnSeries.C k1) = 0 := by
    simpa [hQzero] using hJ1
  let p1 : HahnSeries ℚ k := HahnSeries.C (6 : k) * Y ^ 2
  let r1 := alignedQZeroH1HigherRegular46 0 gamma delta k1 D s Y
  have hp1 : p1.orderTop = (↑(2 * b) : WithTop ℚ) := by
    dsimp [p1]
    exact hahnOrderTop_C_mul_eq46 _ _ (2 * b) (by norm_num)
      (by simpa using hY2)
  have hr1 := alignedQZeroH1HigherRegular46_order_gt
    0 gamma delta k1 D s Y b hD (by linarith) (by linarith) hs hY
  have hsum1 : p1 + r1 = 0 := by
    rw [← alignedLocalJOne46_Q_zero_eq_regular 0 gamma delta k1 D s Y]
    simpa using hJ1zero
  exact hahnExactAddHigher_impossible46 p1 r1 (2 * b) hp1 hr1 hsum1

/-- Exhaustive beta-stratum exclusion with arbitrary regular loads. -/
theorem alignedBetaFinitePole46_exhaustive_regular
    (beta gamma delta k2 k1 : k) (D E : HahnSeries ℚ k)
    (s Q Y : HahnSeries ℚ k) (hbeta : beta ≠ 0)
    (hD : (0 : WithTop ℚ) ≤ D.orderTop)
    (hE : (0 : WithTop ℚ) ≤ E.orderTop)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hQcase : PositiveFiniteOrZero46 Q)
    (hYcase : PositiveFiniteOrZero46 Y)
    (hG : alignedLocalG46 s Q Y (HahnSeries.C beta) (HahnSeries.C gamma)
      (HahnSeries.C delta) D E = 0)
    (hJ2 : alignedLocalJTwo46 s Q Y (HahnSeries.C beta) (HahnSeries.C gamma)
      (HahnSeries.C delta) D (HahnSeries.C k2) = 0)
    (hJ1 : alignedLocalJOne46 s Q Y (HahnSeries.C beta) (HahnSeries.C gamma)
      (HahnSeries.C delta) D (HahnSeries.C k1) = 0) : False := by
  have hQpos := orderTop_pos_of_positiveFiniteOrZero46 Q hQcase
  rcases hYcase with hYzero | ⟨b, hb, hY⟩
  · exact alignedBetaYZeroFinitePole46_impossible_regular
      beta gamma delta k2 D s Q Y hD hbeta hYzero hs hQpos hJ2
  rcases hQcase with hQzero | ⟨a, ha, hQ⟩
  · exact alignedBetaQZeroFinitePole46_impossible_regular
      beta gamma delta k1 D E s Q Y b hD hE hb hbeta hs hY hQzero hG hJ1
  · exact alignedBetaFinitePole46_impossible_regular
      beta gamma delta k2 k1 D E s Q Y a b hD hE ha hb hbeta hs hQ hY
      hG hJ2 hJ1

/-- Exhaustive delta-stratum exclusion with arbitrary regular loads. -/
theorem alignedDeltaFinitePole46_exhaustive_regular
    (gamma delta k2 k1 : k) (D E : HahnSeries ℚ k)
    (s Q Y : HahnSeries ℚ k) (hdelta : delta ≠ 0)
    (hD : (0 : WithTop ℚ) ≤ D.orderTop)
    (hE : (0 : WithTop ℚ) ≤ E.orderTop)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hQcase : PositiveFiniteOrZero46 Q)
    (hYcase : PositiveFiniteOrZero46 Y)
    (hG : alignedLocalG46 s Q Y 0 (HahnSeries.C gamma)
      (HahnSeries.C delta) D E = 0)
    (hJ2 : alignedLocalJTwo46 s Q Y 0 (HahnSeries.C gamma)
      (HahnSeries.C delta) D (HahnSeries.C k2) = 0)
    (hJ1 : alignedLocalJOne46 s Q Y 0 (HahnSeries.C gamma)
      (HahnSeries.C delta) D (HahnSeries.C k1) = 0) : False := by
  have hQpos := orderTop_pos_of_positiveFiniteOrZero46 Q hQcase
  rcases hYcase with hYzero | ⟨b, hb, hY⟩
  · exact alignedDeltaYZeroFinitePole46_impossible_regular
      gamma delta k2 D s Q Y hdelta hYzero hs hQpos hJ2
  rcases hQcase with hQzero | ⟨a, ha, hQ⟩
  · exact alignedDeltaQZeroFinitePole46_impossible_regular
      gamma delta k1 D E s Q Y b hD hE hb hdelta hs hY hQzero hG hJ1
  · exact alignedDeltaFinitePole46_impossible_regular
      gamma delta k2 k1 D E s Q Y a b hD hE ha hb hdelta hs hQ hY
      hG hJ2 hJ1

end AlignedDegenerateRegularLoads

section AlignedZeroRegularLoads

variable {k : Type*} [Field k] [CharZero k]

/-- A regular order-four boundary coefficient cannot cancel a strictly
lower `Q²` face. -/
theorem alignedZeroBoundary_Qsq_lower_impossible_regular46
    (A : HahnSeries ℚ k) (s Q Y W : HahnSeries ℚ k) (q : ℚ)
    (hA : (0 : WithTop ℚ) ≤ A.orderTop)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hQ : Q.orderTop = (↑q : WithTop ℚ))
    (hlt : 2 * q < 7 / 2)
    (hY : Y.orderTop = (↑(7 / 2 : ℚ) : WithTop ℚ))
    (hW : W.orderTop = (↑(7 / 2 : ℚ) : WithTop ℚ))
    (hboundary : W = HahnSeries.C (4 : k) * Y +
        HahnSeries.C (4 : k) * Q ^ 2 - A * s ^ 4) : False := by
  let p : HahnSeries ℚ k := HahnSeries.C (-4 : k) * Q ^ 2
  let r : HahnSeries ℚ k := W - HahnSeries.C (4 : k) * Y + A * s ^ 4
  have hQ2 := hahnOrderTop_pow_eq46 Q q 2 hQ
  have hp : p.orderTop = (↑(2 * q) : WithTop ℚ) := by
    dsimp [p]
    exact hahnOrderTop_C_mul_eq46 _ _ (2 * q) (by norm_num)
      (by simpa using hQ2)
  have hWgt : (↑(2 * q) : WithTop ℚ) < W.orderTop := by
    rw [hW, WithTop.coe_lt_coe]
    exact hlt
  have hYgt : (↑(2 * q) : WithTop ℚ) <
      (HahnSeries.C (4 : k) * Y).orderTop := by
    have h := hahnOrderTop_C_mul_eq46 (4 : k) Y (7 / 2) (by norm_num) hY
    rw [h, WithTop.coe_lt_coe]
    exact hlt
  have hs4 := hahnOrderTop_pow_eq46 s 1 4 hs
  have hs4gt : (↑(2 * q) : WithTop ℚ) < (A * s ^ 4).orderTop :=
    regularHahn_mul_exact_orderTop_gt46 A (s ^ 4) 4 (2 * q) hA
      (by simpa using hs4) (by linarith)
  have hsubgt : (↑(2 * q) : WithTop ℚ) <
      (W - HahnSeries.C (4 : k) * Y).orderTop := by
    rw [sub_eq_add_neg]
    exact hahnOrderTop_add_gt46 _ _ _ hWgt (by simpa using hYgt)
  have hr : (↑(2 * q) : WithTop ℚ) < r.orderTop := by
    dsimp [r]
    exact hahnOrderTop_add_gt46 _ _ _ hsubgt hs4gt
  have hsum : p + r = 0 := by
    dsimp [p, r]
    rw [hboundary]
    simp only [map_neg, map_ofNat]
    ring
  exact hahnExactAddHigher_impossible46 p r (2 * q) hp hr hsum

/-- Above the `7/2` face, a regular order-four boundary coefficient has no
effect on the incompatible leading-coefficient system. -/
theorem alignedZeroBoundary_Qsq_higher_impossible_regular46
    (A : HahnSeries ℚ k) (gamma k1 : k)
    (s Q Y W : HahnSeries ℚ k)
    (hA : (0 : WithTop ℚ) ≤ A.orderTop)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hQ : (↑(0 : ℚ) : WithTop ℚ) < Q.orderTop)
    (hQ2 : (↑(7 / 2 : ℚ) : WithTop ℚ) < (Q ^ 2).orderTop)
    (hY : Y.orderTop = (↑(7 / 2 : ℚ) : WithTop ℚ))
    (hW : W.orderTop = (↑(7 / 2 : ℚ) : WithTop ℚ))
    (hboundary : W = HahnSeries.C (4 : k) * Y +
        HahnSeries.C (4 : k) * Q ^ 2 - A * s ^ 4)
    (hcurve1 : W ^ 2 =
      HahnSeries.C (16 : k) * ((Q - 1) * Y ^ 2) +
        HahnSeries.C ((32 / 3 : k) *
          (k1 + (2 / 3 : k) * gamma ^ 2)) * s ^ 8) : False := by
  let p : HahnSeries ℚ k := W
  let qterm : HahnSeries ℚ k := HahnSeries.C (-4 : k) * Y
  let r : HahnSeries ℚ k := HahnSeries.C (-4 : k) * Q ^ 2 + A * s ^ 4
  have hp : p.orderTop = (↑(7 / 2 : ℚ) : WithTop ℚ) := hW
  have hqterm : qterm.orderTop = (↑(7 / 2 : ℚ) : WithTop ℚ) := by
    dsimp [qterm]
    exact hahnOrderTop_C_mul_eq46 _ _ (7 / 2) (by norm_num) hY
  have hQ2gt : (↑(7 / 2 : ℚ) : WithTop ℚ) <
      (HahnSeries.C (-4 : k) * Q ^ 2).orderTop :=
    hahnOrderTop_C_mul_gt_of_gt46 _ _ _ hQ2
  have hs4 := hahnOrderTop_pow_eq46 s 1 4 hs
  have hs4gt : (↑(7 / 2 : ℚ) : WithTop ℚ) < (A * s ^ 4).orderTop :=
    regularHahn_mul_exact_orderTop_gt46 A (s ^ 4) 4 (7 / 2) hA
      (by simpa using hs4) (by norm_num)
  have hr : (↑(7 / 2 : ℚ) : WithTop ℚ) < r.orderTop := by
    dsimp [r]
    exact hahnOrderTop_add_gt46 _ _ _ hQ2gt hs4gt
  have hsum : p + qterm + r = 0 := by
    dsimp [p, qterm, r]
    rw [hboundary]
    simp only [map_neg, map_ofNat]
    ring
  have hleadBoundary := hahnLeadingCoeffs_cancel_of_add_higher_eq_zero46
    p qterm r (7 / 2) hp hqterm hr hsum
  have hqlead : qterm.leadingCoeff = -4 * Y.leadingCoeff := by
    dsimp [qterm]
    rw [HahnSeries.leadingCoeff_mul,
      hahnLeadingCoeff_C46 (-4 : k) (by norm_num)]
  have hWY : W.leadingCoeff = 4 * Y.leadingCoeff := by
    dsimp [p] at hleadBoundary
    rw [hqlead] at hleadBoundary
    linear_combination hleadBoundary
  let p1 : HahnSeries ℚ k := W ^ 2
  let q1 : HahnSeries ℚ k := HahnSeries.C (16 : k) * Y ^ 2
  let r1 : HahnSeries ℚ k :=
    -(HahnSeries.C (16 : k) * (Q * Y ^ 2)) -
      HahnSeries.C ((32 / 3 : k) *
        (k1 + (2 / 3 : k) * gamma ^ 2)) * s ^ 8
  have hW2 := hahnOrderTop_pow_eq46 W (7 / 2) 2 hW
  have hY2 := hahnOrderTop_pow_eq46 Y (7 / 2) 2 hY
  have hp1 : p1.orderTop = (↑(7 : ℚ) : WithTop ℚ) := by
    dsimp [p1]
    norm_num at hW2 ⊢
    exact hW2
  have hq1 : q1.orderTop = (↑(7 : ℚ) : WithTop ℚ) := by
    dsimp [q1]
    have hY2' : (Y ^ 2).orderTop = (↑(7 : ℚ) : WithTop ℚ) := by
      norm_num at hY2 ⊢
      exact hY2
    exact hahnOrderTop_C_mul_eq46 _ _ 7 (by norm_num) hY2'
  have hQY2gt : (↑(7 : ℚ) : WithTop ℚ) < (Q * Y ^ 2).orderTop :=
    hahnOrderTop_pos_mul_exact_gt46 Q (Y ^ 2) 7 hQ (by
      norm_num at hY2 ⊢
      exact hY2)
  have hfirstgt : (↑(7 : ℚ) : WithTop ℚ) <
      (-(HahnSeries.C (16 : k) * (Q * Y ^ 2))).orderTop := by
    rw [HahnSeries.orderTop_neg]
    exact hahnOrderTop_C_mul_gt_of_gt46 _ _ _ hQY2gt
  have hs8 := hahnOrderTop_pow_eq46 s 1 8 hs
  have hsecondgt : (↑(7 : ℚ) : WithTop ℚ) <
      (-(HahnSeries.C ((32 / 3 : k) *
        (k1 + (2 / 3 : k) * gamma ^ 2)) * s ^ 8)).orderTop := by
    rw [HahnSeries.orderTop_neg]
    exact hahnOrderTop_C_mul_gt46 _ _ 7 8 (by simpa using hs8) (by norm_num)
  have hr1 : (↑(7 : ℚ) : WithTop ℚ) < r1.orderTop := by
    dsimp [r1]
    rw [sub_eq_add_neg]
    exact hahnOrderTop_add_gt46 _ _ _ hfirstgt hsecondgt
  have hsum1 : p1 + q1 + r1 = 0 := by
    dsimp [p1, q1, r1]
    rw [hcurve1]
    ring
  have hleadCurve := hahnLeadingCoeffs_cancel_of_add_higher_eq_zero46
    p1 q1 r1 7 hp1 hq1 hr1 hsum1
  have hp1lead : p1.leadingCoeff = W.leadingCoeff ^ 2 := by
    dsimp [p1]
    simp [pow_two, HahnSeries.leadingCoeff_mul]
  have hq1lead : q1.leadingCoeff = 16 * Y.leadingCoeff ^ 2 := by
    dsimp [q1]
    rw [HahnSeries.leadingCoeff_mul,
      hahnLeadingCoeff_C46 (16 : k) (by norm_num),
      pow_two, HahnSeries.leadingCoeff_mul]
    ring
  rw [hp1lead, hq1lead, hWY] at hleadCurve
  have hYne := hahn_ne_zero_of_orderTop_eq_coe46 Y (7 / 2) hY
  have hYlead : Y.leadingCoeff ≠ 0 := HahnSeries.leadingCoeff_ne_zero.mpr hYne
  have hYsq : Y.leadingCoeff ^ 2 = 0 := by
    linear_combination (1 / 32 : k) * hleadCurve
  exact pow_ne_zero 2 hYlead hYsq

/-- At `v(Q)=7/4`, arbitrary regular loads remain above the isolated
`4Q³` face of the second boundary row. -/
theorem alignedZeroBoundary_Q_tie_impossible_regular46
    (gamma : k) (D E : HahnSeries ℚ k) (s Q Y : HahnSeries ℚ k)
    (hD : (0 : WithTop ℚ) ≤ D.orderTop)
    (hE : (0 : WithTop ℚ) ≤ E.orderTop)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hQ : Q.orderTop = (↑(7 / 4 : ℚ) : WithTop ℚ))
    (hY : Y.orderTop = (↑(7 / 2 : ℚ) : WithTop ℚ))
    (hG : alignedLocalG46 s Q Y 0 (HahnSeries.C gamma) 0 D E = 0) : False := by
  let p : HahnSeries ℚ k := HahnSeries.C (4 : k) * Q ^ 3
  let r : HahnSeries ℚ k := HahnSeries.C (-3 : k) * Y ^ 2 -
      HahnSeries.C (8 * gamma) * (Q * s ^ 4) -
      HahnSeries.C (12 : k) * (D * (Q * s ^ 4)) +
      HahnSeries.C (8 : k) * (E * s ^ 6)
  have hQ3 := hahnOrderTop_pow_eq46 Q (7 / 4) 3 hQ
  have hp : p.orderTop = (↑(21 / 4 : ℚ) : WithTop ℚ) := by
    dsimp [p]
    have hQ3' : (Q ^ 3).orderTop = (↑(21 / 4 : ℚ) : WithTop ℚ) := by
      norm_num at hQ3 ⊢
      exact hQ3
    exact hahnOrderTop_C_mul_eq46 _ _ (21 / 4) (by norm_num) hQ3'
  have hY2 := hahnOrderTop_pow_eq46 Y (7 / 2) 2 hY
  have hYgt : (↑(21 / 4 : ℚ) : WithTop ℚ) <
      (HahnSeries.C (-3 : k) * Y ^ 2).orderTop := by
    have hY2' : (Y ^ 2).orderTop = (↑(7 : ℚ) : WithTop ℚ) := by
      norm_num at hY2 ⊢
      exact hY2
    exact hahnOrderTop_C_mul_gt46 _ _ (21 / 4) 7 hY2' (by norm_num)
  have hs4 := hahnOrderTop_pow_eq46 s 1 4 hs
  have hQs4 := hahnOrderTop_mul_eq46 Q (s ^ 4) (7 / 4) 4 hQ
    (by simpa using hs4)
  have hQs4' : (Q * s ^ 4).orderTop =
      (↑(23 / 4 : ℚ) : WithTop ℚ) := by
    norm_num at hQs4 ⊢
    exact hQs4
  have hgterm : (↑(21 / 4 : ℚ) : WithTop ℚ) <
      (-(HahnSeries.C (8 * gamma) * (Q * s ^ 4))).orderTop := by
    rw [HahnSeries.orderTop_neg]
    exact hahnOrderTop_C_mul_gt46 _ _ (21 / 4) (23 / 4) hQs4' (by norm_num)
  have hDQs4 := regularHahn_mul_exact_orderTop_gt46 D (Q * s ^ 4)
    (23 / 4) (21 / 4) hD hQs4' (by norm_num)
  have hDterm : (↑(21 / 4 : ℚ) : WithTop ℚ) <
      (-(HahnSeries.C (12 : k) * (D * (Q * s ^ 4)))).orderTop := by
    rw [HahnSeries.orderTop_neg]
    exact hahnOrderTop_C_mul_gt_of_gt46 _ _ _ hDQs4
  have hs6 := hahnOrderTop_pow_eq46 s 1 6 hs
  have hEs6 := regularHahn_mul_exact_orderTop_gt46 E (s ^ 6) 6 (21 / 4)
    hE (by simpa using hs6) (by norm_num)
  have hEterm := hahnOrderTop_C_mul_gt_of_gt46 (8 : k) _ _ hEs6
  have hr : (↑(21 / 4 : ℚ) : WithTop ℚ) < r.orderTop := by
    dsimp [r]
    have h12 := hahnOrderTop_add_gt46 (21 / 4) _ _ hYgt hgterm
    have h123 := hahnOrderTop_add_gt46 (21 / 4) _ _ h12 hDterm
    apply hahnOrderTop_add_gt46 (21 / 4) _ _
    · simpa [sub_eq_add_neg, add_assoc] using h123
    · exact hEterm
  have hsum : p + r = 0 := by
    dsimp [p, r]
    simp only [alignedLocalG46, mul_zero, zero_mul, add_zero, sub_zero] at hG
    simp only [map_add, map_mul, map_neg, map_ofNat]
    rw [← hG]
    ring
  exact hahnExactAddHigher_impossible46 p r (21 / 4) hp hr hsum

/-- Complete final aligned-stratum exclusion with arbitrary regular loads. -/
theorem alignedZeroFinitePole46_exhaustive_regular
    (gamma k2 k1 : k) (D E : HahnSeries ℚ k)
    (s Q Y : HahnSeries ℚ k) (hk2 : k2 ≠ 0)
    (hD : (0 : WithTop ℚ) ≤ D.orderTop)
    (hE : (0 : WithTop ℚ) ≤ E.orderTop)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hQcases : PositiveFiniteOrZero46 Q)
    (hYcases : PositiveFiniteOrZero46 Y)
    (hG : alignedLocalG46 s Q Y 0 (HahnSeries.C gamma) 0 D E = 0)
    (hJ2 : alignedLocalJTwo46 s Q Y 0 (HahnSeries.C gamma) 0 D
      (HahnSeries.C k2) = 0)
    (hJ1 : alignedLocalJOne46 s Q Y 0 (HahnSeries.C gamma) 0 D
      (HahnSeries.C k1) = 0) : False := by
  let _ : CharZero (HahnSeries ℚ k) := by
    constructor
    intro m n h
    apply Nat.cast_injective (R := k)
    apply HahnSeries.C_injective (Γ := ℚ)
    simpa using h
  let W : HahnSeries ℚ k :=
    alignedZeroLocalVNumerator46 s Q Y (HahnSeries.C gamma) D
  let A : HahnSeries ℚ k := HahnSeries.C (4 : k) * D +
    HahnSeries.C ((8 / 3 : k) * gamma)
  have hA : (0 : WithTop ℚ) ≤ A.orderTop := by
    dsimp [A]
    exact hahnOrderTop_add_nonneg46 _ _
      (hahnOrderTop_C_mul_nonneg46 (4 : k) D hD)
      (hahnOrderTop_C_nonneg46 ((8 / 3 : k) * gamma))
  have hQpos := orderTop_pos_of_positiveFiniteOrZero46 Q hQcases
  have hYpos := orderTop_pos_of_positiveFiniteOrZero46 Y hYcases
  have hboundary : W = HahnSeries.C (4 : k) * Y +
      HahnSeries.C (4 : k) * Q ^ 2 - A * s ^ 4 := by
    dsimp [W, A]
    have h := alignedZeroLocalVNumerator46_eq s Q Y
      (HahnSeries.C gamma) D
    simp only [map_mul, map_div₀, map_ofNat]
    rw [h]
  have hcurve2 : Y * W =
      HahnSeries.C ((-4 / 3 : k) * k2) * s ^ 7 := by
    dsimp [W]
    have h := alignedZeroLocal_curveTwo_eq46 s Q Y (HahnSeries.C gamma)
      D (HahnSeries.C k2) hJ2
    simpa only [map_mul, map_neg, map_div₀, map_ofNat] using h
  have hcurve1 : W ^ 2 =
      HahnSeries.C (16 : k) * ((Q - 1) * Y ^ 2) +
        HahnSeries.C ((32 / 3 : k) *
          (k1 + (2 / 3 : k) * gamma ^ 2)) * s ^ 8 := by
    dsimp [W]
    have h := alignedZeroLocal_curveOne_eq46 s Q Y (HahnSeries.C gamma)
      D (HahnSeries.C k1) hJ1
    simpa only [map_add, map_mul, map_pow, map_div₀, map_ofNat, mul_assoc]
      using h
  have hsne := hahn_ne_zero_of_orderTop_eq_coe46 s 1 hs
  have hc : (-4 / 3 : k) * k2 ≠ 0 := mul_ne_zero (by norm_num) hk2
  have hCne : (HahnSeries.C ((-4 / 3 : k) * k2) : HahnSeries ℚ k) ≠ 0 := by
    intro h
    apply hc
    apply HahnSeries.C_injective (Γ := ℚ)
    simpa using h
  have hproduct : Y * W ≠ 0 := by
    rw [hcurve2]
    exact mul_ne_zero hCne (pow_ne_zero 7 hsne)
  have hYne : Y ≠ 0 := by
    intro h
    rw [h, zero_mul] at hproduct
    exact hproduct rfl
  have hWne : W ≠ 0 := by
    intro h
    rw [h, mul_zero] at hproduct
    exact hproduct rfl
  obtain ⟨y, hy, hYord⟩ : ∃ y : ℚ, 0 < y ∧
      Y.orderTop = (↑y : WithTop ℚ) := by
    rcases hYcases with hYzero | hYfinite
    · exact (hYne hYzero).elim
    · exact hYfinite
  have hQ2pos : (↑(0 : ℚ) : WithTop ℚ) < (Q ^ 2).orderTop := by
    rw [pow_two]
    exact hahnOrderTop_mul_pos46 Q Q hQpos hQpos
  have hYtermPos : (↑(0 : ℚ) : WithTop ℚ) <
      (HahnSeries.C (4 : k) * Y).orderTop :=
    hahnOrderTop_C_mul_gt_of_gt46 _ _ _ hYpos
  have hQtermPos : (↑(0 : ℚ) : WithTop ℚ) <
      (HahnSeries.C (4 : k) * Q ^ 2).orderTop :=
    hahnOrderTop_C_mul_gt_of_gt46 _ _ _ hQ2pos
  have hs4 := hahnOrderTop_pow_eq46 s 1 4 hs
  have hs4pos : (↑(0 : ℚ) : WithTop ℚ) < (A * s ^ 4).orderTop :=
    regularHahn_mul_exact_orderTop_gt46 A (s ^ 4) 4 0 hA
      (by simpa using hs4) (by norm_num)
  have haddPos : (↑(0 : ℚ) : WithTop ℚ) <
      (HahnSeries.C (4 : k) * Y + HahnSeries.C (4 : k) * Q ^ 2).orderTop :=
    hahnOrderTop_add_gt46 _ _ _ hYtermPos hQtermPos
  have hWpos : (↑(0 : ℚ) : WithTop ℚ) < W.orderTop := by
    rw [hboundary, sub_eq_add_neg]
    exact hahnOrderTop_add_gt46 _ _ _ haddPos (by simpa using hs4pos)
  let w : ℚ := W.order
  have hWord : W.orderTop = (↑w : WithTop ℚ) :=
    (HahnSeries.order_eq_orderTop_of_ne_zero hWne).symm
  have hw : 0 < w := by
    rw [hWord, WithTop.coe_lt_coe] at hWpos
    exact hWpos
  have horders := alignedZeroCurveOrders46 gamma k2 k1 s Q Y W y w hk2 hs
    hQpos hy hYord hw hWord hcurve2 hcurve1
  have hYhalf : Y.orderTop = (↑(7 / 2 : ℚ) : WithTop ℚ) := by
    rw [← horders.1]
    exact hYord
  have hWhalf : W.orderTop = (↑(7 / 2 : ℚ) : WithTop ℚ) := by
    rw [← horders.2]
    exact hWord
  rcases hQcases with hQzero | ⟨q, hq, hQord⟩
  · have hQ2gt : (↑(7 / 2 : ℚ) : WithTop ℚ) < (Q ^ 2).orderTop := by
      simp [hQzero]
    exact alignedZeroBoundary_Qsq_higher_impossible_regular46
      A gamma k1 s Q Y W hA hs hQpos hQ2gt hYhalf hWhalf hboundary hcurve1
  · rcases lt_trichotomy (2 * q) (7 / 2) with hlt | heq | hgt
    · exact alignedZeroBoundary_Qsq_lower_impossible_regular46
        A s Q Y W q hA hs hQord hlt hYhalf hWhalf hboundary
    · have hqeq : q = 7 / 4 := by linarith
      subst q
      exact alignedZeroBoundary_Q_tie_impossible_regular46
        gamma D E s Q Y hD hE hs hQord hYhalf hG
    · have hQ2ord := hahnOrderTop_pow_eq46 Q q 2 hQord
      have hQ2gt : (↑(7 / 2 : ℚ) : WithTop ℚ) < (Q ^ 2).orderTop := by
        rw [hQ2ord, WithTop.coe_lt_coe]
        simpa using hgt
      exact alignedZeroBoundary_Qsq_higher_impossible_regular46
        A gamma k1 s Q Y W hA hs hQpos hQ2gt hYhalf hWhalf hboundary hcurve1

end AlignedZeroRegularLoads

end Max11DegreeRoutes
