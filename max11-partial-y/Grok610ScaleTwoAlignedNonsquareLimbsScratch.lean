import Grok610ScaleTwoAlignedNonsquareDescentScratch

/-! # Remaining Newton-limb transcription of the aligned-nonsquare `(6,10)` chamber

Untracked working note.  No tracked file was edited.

Parent (tracked, green): `Grok610ScaleTwoAlignedNonsquareDescentScratch`.  Already
False in Lean: the transverse `g₁(a)=0` limb, the constant-witness limb and the
unique-`v` cone (`alignedNonsquare_constantOrUniqueV_false_610`), and the first
linear residue peel `t₁₁=0 ∨ t₃₁=0`
(`alignedEleventhNonsquareResidue_coeff_six_of_linear_610`).

CAS jobs `610-aligned-nonsquare-mixed-descent`, `-lc-peel`, `-tree`, `-gaps`,
`-linfinish` compare leading coefficients of the Keller identity, the degree-`1`
Jacobian, and `alignedEleventhNonsquareResidue610` as polynomials in `X`.  Every
remaining Newton limb dies.  This file transcribes those kills:

* leftover linear limbs: Keller LC `35 t₁₁⁵ v₁` (`t₃₁=0`) and `-20 v₁³`
  (`t₁₁=t₃₁=0`);
* equal-degree `d ≥ 3` strata: jac1 LC proportional to `G₁² T₁⁶` and residue
  LC `1280 T₃ (G₁² T₃² + 18 G₁ T₁² T₃ + 63 T₁⁴)`.

FLAG: leading-coefficient Newton descent of leftover linear Keller LC
`35 t₁₁⁵ v₁` and of equal-degree `d ≥ 3` jac1 LC `∝ G₁² T₁⁶` together with
residue LC `1280 T₃ (G₁² T₃² + 18 G₁ T₁² T₃ + 63 T₁⁴)`.  Chamber closure
is assembled only after every remaining mixed-max limb is discharged.

No total-degree or twice-prime theorem is used.  No `sorry`, no new axioms, no
finite-root shortcut, no closure overclaim.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000

variable {K : Type*} [Field K] [CharZero K]

/-! ## Coefficient arithmetic -/

lemma natCast_mul_natDegree_le_610 (n : ℕ) {p : K[X]} {m : ℕ}
    (hp : p.natDegree ≤ m) :
    ((n : K[X]) * p).natDegree ≤ m := by
  rw [← Polynomial.C_eq_natCast n]
  exact (natDegree_C_mul_le (n : K) p).trans hp

lemma coeff_natCast_mul_610 (n : ℕ) (p : K[X]) (k : ℕ) :
    ((n : K[X]) * p).coeff k = (n : K) * p.coeff k := by
  rw [← Polynomial.C_eq_natCast n]
  exact Polynomial.coeff_C_mul p

lemma C_mul_natDegree_le_610 (c : K) {p : K[X]} {m : ℕ}
    (hp : p.natDegree ≤ m) :
    (Polynomial.C c * p).natDegree ≤ m :=
  (natDegree_C_mul_le c p).trans hp

lemma natDegree_add_le_of_le_610 {p q : K[X]} {n : ℕ}
    (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n) :
    (p + q).natDegree ≤ n :=
  (natDegree_add_le p q).trans (max_le hp hq)

lemma natDegree_sub_le_of_le_610 {p q : K[X]} {n : ℕ}
    (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n) :
    (p - q).natDegree ≤ n := by
  rw [sub_eq_add_neg]
  exact natDegree_add_le_of_le_610 hp (by simpa [natDegree_neg] using hq)

lemma natDegree_neg_le_of_le_610 {p : K[X]} {n : ℕ}
    (hp : p.natDegree ≤ n) : (-p).natDegree ≤ n := by
  simpa [natDegree_neg] using hp

lemma natDegree_derivative_le_of_le_610 {p : K[X]} {n : ℕ}
    (hp : p.natDegree ≤ n) :
    p.derivative.natDegree ≤ n :=
  (Polynomial.natDegree_derivative_le p).trans
    ((Nat.sub_le p.natDegree 1).trans hp)

lemma coeff_derivative_pred_610 (p : K[X]) {n : ℕ} (hn : 1 ≤ n) :
    p.derivative.coeff (n - 1) = p.coeff n * (n : K) := by
  have h := Polynomial.coeff_derivative p (n - 1)
  have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel hn
  rw [hn1] at h
  have hcast : ((n - 1 : ℕ) : K) + 1 = (n : K) := by
    rw [← Nat.cast_add_one, hn1]
  rwa [hcast] at h

lemma coeff_eq_C_of_pos {p : K[X]} {j : K} {n : ℕ}
    (hp : p = Polynomial.C j) (hn : 1 ≤ n) : p.coeff n = 0 := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt (Nat.succ_le_iff.mp hn)
  simp [hp, Polynomial.coeff_C, hn0]

lemma natDegree_le_of_C_mul_le_610 {a : K} (ha : a ≠ 0) {p : K[X]} {n : ℕ}
    (h : (Polynomial.C a * p).natDegree ≤ n) : p.natDegree ≤ n := by
  rwa [natDegree_C_mul ha] at h

lemma natCast_ne_zero_610 (n : ℕ) (hn : n ≠ 0) : (n : K[X]) ≠ 0 := by
  rw [← Polynomial.C_eq_natCast n]
  exact Polynomial.C_ne_zero.mpr (Nat.cast_ne_zero.mpr hn)

lemma add_add_le_two_mul_610 {n m : ℕ} (h : n ≤ m + m) : n ≤ 2 * m := by
  simpa [two_mul] using h

lemma add_add_add_le_three_mul_610 {n m : ℕ} (h : n ≤ m + m + m) :
    n ≤ 3 * m := by
  have : m + m + m = 3 * m := by ring
  rwa [this] at h

lemma add_add_add_add_le_four_mul_610 {n m : ℕ} (h : n ≤ m + m + (m + m)) :
    n ≤ 4 * m := by
  have : m + m + (m + m) = 4 * m := by ring
  rwa [this] at h

lemma natDegree_natCast_mul_eq_610 {n : ℕ} (hn : n ≠ 0) (p : K[X]) :
    ((n : K[X]) * p).natDegree = p.natDegree := by
  have hK : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [← Polynomial.C_eq_natCast n, natDegree_C_mul hK]

lemma natDegree_sq_of_twoMul_le_610 {p : K[X]} {d : ℕ}
    (hp : p.natDegree ≤ 2 * d) : (p ^ 2).natDegree ≤ 4 * d :=
  (natDegree_pow_le_mul_610 (n := 2) hp).trans (by omega)

lemma natDegree_le_trans_610 {p : K[X]} {m n : ℕ}
    (hp : p.natDegree ≤ m) (hmn : m ≤ n) : p.natDegree ≤ n :=
  hp.trans hmn

/-! ## Jet rearrangements -/

theorem alignedNonsquare_t2_eq_610 {t2 g1 t1 H t3 : K[X]}
    (ht3 : t2 - (6 : K[X]) * g1 * t1 = H * t3) :
    t2 = (6 : K[X]) * g1 * t1 + H * t3 := by
  linear_combination ht3

theorem alignedNonsquare_a1_eq_610 {a1 g1 u H v : K[X]}
    (hv : (243 : K[X]) * a1 - g1 * u = H * v) :
    (243 : K[X]) * a1 = g1 * u + H * v := by
  linear_combination hv

theorem alignedNonsquare_a2_from_jet_610 {a2 g1 t1 t2 u t3 H : K[X]}
    (hu : (81 : K[X]) * a2 + (3 : K[X]) * g1 ^ 2 * t1 - g1 * t2 = H * u)
    (ht3 : t2 - (6 : K[X]) * g1 * t1 = H * t3) :
    (81 : K[X]) * a2 = (3 : K[X]) * g1 ^ 2 * t1 + H * (u + g1 * t3) := by
  have ht2 := alignedNonsquare_t2_eq_610 ht3
  rw [ht2] at hu
  linear_combination hu

theorem alignedNonsquare_t2_natDegree_le_610 {t2 g1 t1 H t3 : K[X]} {d : ℕ}
    (hd : 2 ≤ d) (hH : H.natDegree ≤ 2)
    (hg1 : g1.natDegree ≤ d) (ht1 : t1.natDegree ≤ d)
    (ht3 : t3.natDegree ≤ d)
    (hid : t2 - (6 : K[X]) * g1 * t1 = H * t3) :
    t2.natDegree ≤ 2 * d := by
  have ht2 := alignedNonsquare_t2_eq_610 hid
  have h6 : ((6 : K[X]) * g1 * t1).natDegree ≤ 2 * d := by
    have hg1t1 : (g1 * t1).natDegree ≤ d + d :=
      (natDegree_mul_le_add_610 hg1 ht1).trans (by omega)
    have h6g : ((6 : K[X]) * (g1 * t1)).natDegree ≤ 2 * d :=
      add_add_le_two_mul_610 (natCast_mul_natDegree_le_610 6 hg1t1)
    simpa [mul_assoc] using h6g
  have hHt3 : (H * t3).natDegree ≤ 2 + d := (natDegree_mul_le_add_610 hH ht3).trans (by omega)
  have hsum : ((6 : K[X]) * g1 * t1 + H * t3).natDegree ≤ 2 * d :=
    natDegree_add_le_of_le_610 h6 (natDegree_le_trans_610 hHt3 (by omega))
  simpa [ht2] using hsum

theorem alignedNonsquare_a1_natDegree_le_610 {a1 g1 u H v : K[X]} {d : ℕ}
    (hd : 2 ≤ d) (hH : H.natDegree ≤ 2)
    (hg1 : g1.natDegree ≤ d) (hu : u.natDegree ≤ d) (hv : v.natDegree ≤ d)
    (hid : (243 : K[X]) * a1 - g1 * u = H * v) :
    a1.natDegree ≤ 2 * d := by
  have ha1 := alignedNonsquare_a1_eq_610 hid
  have hgu : (g1 * u).natDegree ≤ 2 * d := by
    exact add_add_le_two_mul_610 <| natDegree_mul_le_add_610 hg1 hu
  have hHv : (H * v).natDegree ≤ 2 + d := (natDegree_mul_le_add_610 hH hv).trans (by omega)
  have hr : (g1 * u + H * v).natDegree ≤ 2 * d :=
    natDegree_add_le_of_le_610 hgu (natDegree_le_trans_610 hHv (by omega))
  have h243 : (243 : K) ≠ 0 := by norm_num
  have hC : (243 : K[X]) = Polynomial.C (243 : K) :=
    (Polynomial.C_eq_natCast 243).symm
  have : (Polynomial.C (243 : K) * a1).natDegree ≤ 2 * d := by
    rw [← hC, ha1]
    exact hr
  exact natDegree_le_of_C_mul_le_610 h243 this

theorem alignedNonsquare_a2_natDegree_le_610 {a2 g1 t1 t2 u t3 H : K[X]}
    {d : ℕ} (hd : 2 ≤ d) (hH : H.natDegree ≤ 2)
    (hg1 : g1.natDegree ≤ d) (ht1 : t1.natDegree ≤ d)
    (hu : u.natDegree ≤ d) (ht3 : t3.natDegree ≤ d)
    (hjet : (81 : K[X]) * a2 + (3 : K[X]) * g1 ^ 2 * t1 - g1 * t2 = H * u)
    (ht2id : t2 - (6 : K[X]) * g1 * t1 = H * t3) :
    a2.natDegree ≤ 3 * d := by
  have ha2 := alignedNonsquare_a2_from_jet_610 hjet ht2id
  have hg12 : (g1 ^ 2).natDegree ≤ 2 * d := natDegree_pow_le_mul_610 hg1
  have hg12t1 : (g1 ^ 2 * t1).natDegree ≤ 3 * d :=
    (natDegree_mul_le_add_610 hg12 ht1).trans (by omega)
  have h3 : ((3 : K[X]) * (g1 ^ 2 * t1)).natDegree ≤ 3 * d :=
    natCast_mul_natDegree_le_610 3 hg12t1
  have h3' : ((3 : K[X]) * g1 ^ 2 * t1).natDegree ≤ 3 * d := by
    simpa [mul_assoc] using h3
  have hgt3 : (g1 * t3).natDegree ≤ 2 * d := by
    exact add_add_le_two_mul_610 <| natDegree_mul_le_add_610 hg1 ht3
  have hsum : (u + g1 * t3).natDegree ≤ 2 * d :=
    natDegree_add_le_of_le_610 (natDegree_le_trans_610 hu (by omega)) hgt3
  have hHsum : (H * (u + g1 * t3)).natDegree ≤ 2 + 2 * d :=
    (natDegree_mul_le_add_610 hH hsum).trans (by omega)
  have hr : ((3 : K[X]) * g1 ^ 2 * t1 + H * (u + g1 * t3)).natDegree ≤
      3 * d :=
    natDegree_add_le_of_le_610 h3' (natDegree_le_trans_610 hHsum (by omega))
  have h81 : (81 : K) ≠ 0 := by norm_num
  have hC : (81 : K[X]) = Polynomial.C (81 : K) :=
    (Polynomial.C_eq_natCast 81).symm
  have : (Polynomial.C (81 : K) * a2).natDegree ≤ 3 * d := by
    rw [← hC, ha2]
    exact hr
  exact natDegree_le_of_C_mul_le_610 h81 this

/-! ## Equal-degree residue leading coefficient (`d ≥ 3`) -/

set_option maxHeartbeats 16000000 in
theorem alignedEleventhNonsquareResidueHCoef_natDegree_le_fourMul_610
    (t1 t3 v : K[X]) (κ : K) {d : ℕ}
    (ht1 : t1.natDegree ≤ d) (ht3 : t3.natDegree ≤ d)
    (hv : v.natDegree ≤ d) :
    (alignedEleventhNonsquareResidueHCoef610 t1 t3 v κ).natDegree ≤ 4 * d := by
  have ht33 : (t3 ^ 3).natDegree ≤ 3 * d := natDegree_pow_le_mul_610 ht3
  have ht32 : (t3 ^ 2).natDegree ≤ 2 * d := natDegree_pow_le_mul_610 ht3
  have h5120 : ((5120 : K[X]) * t1 * t3 ^ 3).natDegree ≤ 4 * d := by
    have h5120t1 : ((5120 : K[X]) * t1).natDegree ≤ d :=
      natCast_mul_natDegree_le_610 5120 ht1
    have h := natDegree_mul_le_add_610 h5120t1 ht33
    simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega))
  have h3840 : ((3840 : K[X]) * t3 ^ 2 * v).natDegree ≤ 3 * d := by
    have h3840t : ((3840 : K[X]) * t3 ^ 2).natDegree ≤ 2 * d :=
      natCast_mul_natDegree_le_610 3840 ht32
    have h := natDegree_mul_le_add_610 h3840t hv
    simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega))
  have hk : (Polynomial.C κ * ((1024 : K[X]) * t3 ^ 3)).natDegree ≤ 3 * d :=
    C_mul_natDegree_le_610 κ (natCast_mul_natDegree_le_610 1024 ht33)
  simp only [alignedEleventhNonsquareResidueHCoef610]
  refine natDegree_add_le_of_le_610
      (natDegree_add_le_of_le_610 (natDegree_neg_le_of_le_610 h5120)
        (natDegree_le_trans_610 h3840 (by omega)))
      (natDegree_le_trans_610 hk (by omega))

set_option maxHeartbeats 32000000 in
theorem alignedEleventhNonsquareResidue_coeff_fiveMul_610
    (H g1 t1 u t3 v a0 : K[X]) (κ κ₅ κ₇ : K) {d : ℕ}
    (hd : 3 ≤ d) (hH : H.natDegree ≤ 2)
    (hg1 : g1.natDegree ≤ d) (ht1 : t1.natDegree ≤ d)
    (hu : u.natDegree ≤ d) (ht3 : t3.natDegree ≤ d)
    (hv : v.natDegree ≤ d) (ha0 : a0.natDegree ≤ d) :
    (alignedEleventhNonsquareResidue610 H g1 t1 u t3 v a0 κ κ₅ κ₇).coeff
        (5 * d) =
      (1280 : K) * t3.coeff d *
        ((g1.coeff d) ^ 2 * (t3.coeff d) ^ 2 +
          (18 : K) * g1.coeff d * (t1.coeff d) ^ 2 * t3.coeff d +
          (63 : K) * (t1.coeff d) ^ 4) := by
  have hsplit := alignedEleventhNonsquareResidue_split_610 H g1 t1 u t3 v a0
    κ κ₅ κ₇
  have hcoef :=
    alignedEleventhNonsquareResidueHCoef_natDegree_le_fourMul_610 t1 t3 v κ
      ht1 ht3 hv
  have hHrest : (H * alignedEleventhNonsquareResidueHCoef610 t1 t3 v κ).natDegree
      ≤ 2 + 4 * d :=
    natDegree_mul_le_add_610 hH hcoef
  have hHlt : (H * alignedEleventhNonsquareResidueHCoef610 t1 t3 v κ).natDegree
      < 5 * d := by
    have : 2 + 4 * d < 5 * d := by omega
    exact lt_of_le_of_lt hHrest this
  have hH0 :
      (H * alignedEleventhNonsquareResidueHCoef610 t1 t3 v κ).coeff (5 * d) =
        0 :=
    coeff_eq_zero_of_natDegree_lt hHlt
  -- Leading monomials of the `H`-free summand.
  have ht14 : (t1 ^ 4).natDegree ≤ 4 * d := natDegree_pow_le_mul_610 ht1
  have ht12 : (t1 ^ 2).natDegree ≤ 2 * d := natDegree_pow_le_mul_610 ht1
  have ht32 : (t3 ^ 2).natDegree ≤ 2 * d := natDegree_pow_le_mul_610 ht3
  have ht33 : (t3 ^ 3).natDegree ≤ 3 * d := natDegree_pow_le_mul_610 ht3
  have hg12 : (g1 ^ 2).natDegree ≤ 2 * d := natDegree_pow_le_mul_610 hg1
  have htop1c : ((80640 : K[X]) * t1 ^ 4 * t3).coeff (5 * d) =
      (80640 : K) * (t1.coeff d) ^ 4 * t3.coeff d := by
    have hpow : (t1 ^ 4).coeff (4 * d) = (t1.coeff d) ^ 4 :=
      coeff_pow_of_natDegree_le_610 (n := 4) ht1
    have h80640t : ((80640 : K[X]) * t1 ^ 4).natDegree ≤ 4 * d :=
      natCast_mul_natDegree_le_610 80640 ht14
    have h80640c : ((80640 : K[X]) * t1 ^ 4).coeff (4 * d) =
        (80640 : K) * (t1.coeff d) ^ 4 := by
      have h := coeff_mul_of_natDegree_le_610
        (p := (80640 : K[X])) (q := t1 ^ 4) (m := 0) (n := 4 * d)
        (by
          have : (80640 : K[X]) = Polynomial.C (80640 : K) :=
            (Polynomial.C_eq_natCast 80640).symm
          simp [this]) ht14
      have h0 : ((80640 : K[X]).coeff 0) = (80640 : K) := by
        have : (80640 : K[X]) = Polynomial.C (80640 : K) :=
          (Polynomial.C_eq_natCast 80640).symm
        simp [this]
      simpa [h0, hpow] using h
    have h := coeff_mul_of_natDegree_le_610 h80640t ht3
    have hsum : 4 * d + d = 5 * d := by omega
    simpa [hsum, h80640c] using h
  have htop2c : ((23040 : K[X]) * t1 ^ 2 * t3 ^ 2 * g1).coeff (5 * d) =
      (23040 : K) * (t1.coeff d) ^ 2 * (t3.coeff d) ^ 2 * g1.coeff d := by
    have hp2 : (t1 ^ 2).coeff (2 * d) = (t1.coeff d) ^ 2 :=
      coeff_pow_of_natDegree_le_610 (n := 2) ht1
    have hq2 : (t3 ^ 2).coeff (2 * d) = (t3.coeff d) ^ 2 :=
      coeff_pow_of_natDegree_le_610 (n := 2) ht3
    have ht12t32 : (t1 ^ 2 * t3 ^ 2).natDegree ≤ 4 * d := by
      have h := natDegree_mul_le_add_610 ht12 ht32
      exact h.trans (by omega)
    have ht12t32c : (t1 ^ 2 * t3 ^ 2).coeff (4 * d) =
        (t1.coeff d) ^ 2 * (t3.coeff d) ^ 2 := by
      have h := coeff_mul_of_natDegree_le_610 ht12 ht32
      have hsum : 2 * d + 2 * d = 4 * d := by omega
      simpa [hsum, hp2, hq2] using h
    have h23040m : ((23040 : K[X]) * (t1 ^ 2 * t3 ^ 2)).natDegree ≤ 4 * d :=
      natCast_mul_natDegree_le_610 23040 ht12t32
    have h23040c : ((23040 : K[X]) * (t1 ^ 2 * t3 ^ 2)).coeff (4 * d) =
        (23040 : K) * ((t1.coeff d) ^ 2 * (t3.coeff d) ^ 2) := by
      have h := coeff_mul_of_natDegree_le_610
        (p := (23040 : K[X])) (q := t1 ^ 2 * t3 ^ 2) (m := 0) (n := 4 * d)
        (by
          have : (23040 : K[X]) = Polynomial.C (23040 : K) :=
            (Polynomial.C_eq_natCast 23040).symm
          simp [this]) ht12t32
      have h0 : ((23040 : K[X]).coeff 0) = (23040 : K) := by
        have : (23040 : K[X]) = Polynomial.C (23040 : K) :=
          (Polynomial.C_eq_natCast 23040).symm
        simp [this]
      simpa [h0, ht12t32c] using h
    have h := coeff_mul_of_natDegree_le_610 h23040m hg1
    have hsum : 4 * d + d = 5 * d := by omega
    have hassoc : (23040 : K[X]) * t1 ^ 2 * t3 ^ 2 * g1 =
        (23040 : K[X]) * (t1 ^ 2 * t3 ^ 2) * g1 := by ring
    simpa [hassoc, hsum, h23040c, mul_assoc] using h
  have htop3c : ((1280 : K[X]) * t3 ^ 3 * g1 ^ 2).coeff (5 * d) =
      (1280 : K) * (t3.coeff d) ^ 3 * (g1.coeff d) ^ 2 := by
    have hp3 : (t3 ^ 3).coeff (3 * d) = (t3.coeff d) ^ 3 :=
      coeff_pow_of_natDegree_le_610 (n := 3) ht3
    have hq2 : (g1 ^ 2).coeff (2 * d) = (g1.coeff d) ^ 2 :=
      coeff_pow_of_natDegree_le_610 (n := 2) hg1
    have h1280t : ((1280 : K[X]) * t3 ^ 3).natDegree ≤ 3 * d :=
      natCast_mul_natDegree_le_610 1280 ht33
    have h1280c : ((1280 : K[X]) * t3 ^ 3).coeff (3 * d) =
        (1280 : K) * (t3.coeff d) ^ 3 := by
      have h := coeff_mul_of_natDegree_le_610
        (p := (1280 : K[X])) (q := t3 ^ 3) (m := 0) (n := 3 * d)
        (by
          have : (1280 : K[X]) = Polynomial.C (1280 : K) :=
            (Polynomial.C_eq_natCast 1280).symm
          simp [this]) ht33
      have h0 : ((1280 : K[X]).coeff 0) = (1280 : K) := by
        have : (1280 : K[X]) = Polynomial.C (1280 : K) :=
          (Polynomial.C_eq_natCast 1280).symm
        simp [this]
      simpa [h0, hp3] using h
    have h := coeff_mul_of_natDegree_le_610 h1280t hg12
    have hsum : 3 * d + 2 * d = 5 * d := by omega
    simpa [hsum, h1280c, hq2] using h
  -- Remaining `H`-free terms have degree at most `4 d`.
  have hfree :
      (alignedEleventhNonsquareResidueHFree610 g1 t1 u t3 v a0 κ κ₅ κ₇).coeff
          (5 * d) =
        (80640 : K) * (t1.coeff d) ^ 4 * t3.coeff d +
          (23040 : K) * (t1.coeff d) ^ 2 * (t3.coeff d) ^ 2 * g1.coeff d +
          (1280 : K) * (t3.coeff d) ^ 3 * (g1.coeff d) ^ 2 := by
    have hv3 : ((46080 : K[X]) * t1 ^ 3 * v).natDegree ≤ 4 * d := by
      have ht13 : (t1 ^ 3).natDegree ≤ 3 * d := natDegree_pow_le_mul_610 ht1
      have h46080t : ((46080 : K[X]) * t1 ^ 3).natDegree ≤ 3 * d :=
        natCast_mul_natDegree_le_610 46080 ht13
      have h := natDegree_mul_le_add_610 h46080t hv
      simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega))
    have hu4 : ((46080 : K[X]) * t1 ^ 2 * u * t3).natDegree ≤ 4 * d := by
      have h46080t : ((46080 : K[X]) * t1 ^ 2).natDegree ≤ 2 * d :=
        natCast_mul_natDegree_le_610 46080 ht12
      have h46080tu : ((46080 : K[X]) * t1 ^ 2 * u).natDegree ≤ 3 * d :=
        (natDegree_mul_le_add_610 h46080t hu).trans (by omega)
      have h := natDegree_mul_le_add_610 h46080tu ht3
      simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega))
    have huv : ((23040 : K[X]) * t1 * u * v).natDegree ≤ 3 * d := by
      have h23040t : ((23040 : K[X]) * t1).natDegree ≤ d :=
        natCast_mul_natDegree_le_610 23040 ht1
      have h23040tu : ((23040 : K[X]) * t1 * u).natDegree ≤ 2 * d :=
        (natDegree_mul_le_add_610 h23040t hu).trans (by omega)
      have h := natDegree_mul_le_add_610 h23040tu hv
      simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega))
    have htvg : ((23040 : K[X]) * t1 * t3 * v * g1).natDegree ≤ 4 * d := by
      have h23040t : ((23040 : K[X]) * t1).natDegree ≤ d :=
        natCast_mul_natDegree_le_610 23040 ht1
      have h23040tr : ((23040 : K[X]) * t1 * t3).natDegree ≤ 2 * d :=
        (natDegree_mul_le_add_610 h23040t ht3).trans (by omega)
      have h23040trv : ((23040 : K[X]) * t1 * t3 * v).natDegree ≤ 3 * d :=
        (natDegree_mul_le_add_610 h23040tr hv).trans (by omega)
      have h := natDegree_mul_le_add_610 h23040trv hg1
      simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega))
    have hta : ((16796160 : K[X]) * t1 * t3 * a0).natDegree ≤ 3 * d := by
      have hN : ((16796160 : K[X]) * t1).natDegree ≤ d :=
        natCast_mul_natDegree_le_610 16796160 ht1
      have hNr : ((16796160 : K[X]) * t1 * t3).natDegree ≤ 2 * d :=
        (natDegree_mul_le_add_610 hN ht3).trans (by omega)
      have h := natDegree_mul_le_add_610 hNr ha0
      simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega))
    have hu2t : ((3840 : K[X]) * u ^ 2 * t3).natDegree ≤ 3 * d := by
      have hu2 : (u ^ 2).natDegree ≤ 2 * d := natDegree_pow_le_mul_610 hu
      have h3840u : ((3840 : K[X]) * u ^ 2).natDegree ≤ 2 * d :=
        natCast_mul_natDegree_le_610 3840 hu2
      have h := natDegree_mul_le_add_610 h3840u ht3
      simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega))
    have hutg : ((3840 : K[X]) * u * t3 ^ 2 * g1).natDegree ≤ 4 * d := by
      have h3840u : ((3840 : K[X]) * u).natDegree ≤ d :=
        natCast_mul_natDegree_le_610 3840 hu
      have h3840ur : ((3840 : K[X]) * u * t3 ^ 2).natDegree ≤ 3 * d :=
        (natDegree_mul_le_add_610 h3840u ht32).trans (by omega)
      have h := natDegree_mul_le_add_610 h3840ur hg1
      simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega))
    have hv2g : ((11520 : K[X]) * v ^ 2 * g1).natDegree ≤ 3 * d := by
      have hv2 : (v ^ 2).natDegree ≤ 2 * d := natDegree_pow_le_mul_610 hv
      have h11520v : ((11520 : K[X]) * v ^ 2).natDegree ≤ 2 * d :=
        natCast_mul_natDegree_le_610 11520 hv2
      have h := natDegree_mul_le_add_610 h11520v hg1
      simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega))
    have hva : ((16796160 : K[X]) * v * a0).natDegree ≤ 2 * d := by
      have hN : ((16796160 : K[X]) * v).natDegree ≤ d :=
        natCast_mul_natDegree_le_610 16796160 hv
      have h := natDegree_mul_le_add_610 hN ha0
      simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega))
    have hk7 : (Polynomial.C κ₇ * ((3 : K[X]) * t3)).natDegree ≤ d :=
      C_mul_natDegree_le_610 κ₇ (natCast_mul_natDegree_le_610 3 ht3)
    have hk5t : (Polynomial.C κ₅ * ((96 : K[X]) * t1 * t3)).natDegree ≤
        2 * d := by
      have h96t : ((96 : K[X]) * t1).natDegree ≤ d :=
        natCast_mul_natDegree_le_610 96 ht1
      have h96tr : ((96 : K[X]) * t1 * t3).natDegree ≤ 2 * d :=
        (natDegree_mul_le_add_610 h96t ht3).trans (by omega)
      exact C_mul_natDegree_le_610 κ₅ h96tr
    have hk5v : (Polynomial.C κ₅ * ((96 : K[X]) * v)).natDegree ≤ d :=
      C_mul_natDegree_le_610 κ₅ (natCast_mul_natDegree_le_610 96 hv)
    have hkt3 : (Polynomial.C κ * ((46080 : K[X]) * t1 ^ 3 * t3)).natDegree ≤
        4 * d := by
      have ht13 : (t1 ^ 3).natDegree ≤ 3 * d := natDegree_pow_le_mul_610 ht1
      have h46080t : ((46080 : K[X]) * t1 ^ 3).natDegree ≤ 3 * d :=
        natCast_mul_natDegree_le_610 46080 ht13
      have h := natDegree_mul_le_add_610 h46080t ht3
      exact C_mul_natDegree_le_610 κ (by simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega)))
    have hkv : (Polynomial.C κ * ((27648 : K[X]) * t1 ^ 2 * v)).natDegree ≤
        3 * d := by
      have h27648t : ((27648 : K[X]) * t1 ^ 2).natDegree ≤ 2 * d :=
        natCast_mul_natDegree_le_610 27648 ht12
      have h := natDegree_mul_le_add_610 h27648t hv
      exact C_mul_natDegree_le_610 κ (by simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega)))
    have hku : (Polynomial.C κ * ((18432 : K[X]) * t1 * u * t3)).natDegree ≤
        3 * d := by
      have h18432t : ((18432 : K[X]) * t1).natDegree ≤ d :=
        natCast_mul_natDegree_le_610 18432 ht1
      have h18432tu : ((18432 : K[X]) * t1 * u).natDegree ≤ 2 * d :=
        (natDegree_mul_le_add_610 h18432t hu).trans (by omega)
      have h := natDegree_mul_le_add_610 h18432tu ht3
      exact C_mul_natDegree_le_610 κ (by simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega)))
    have hktg : (Polynomial.C κ * ((9216 : K[X]) * t1 * t3 ^ 2 * g1)).natDegree
        ≤ 4 * d := by
      have h9216t : ((9216 : K[X]) * t1).natDegree ≤ d :=
        natCast_mul_natDegree_le_610 9216 ht1
      have h9216tr : ((9216 : K[X]) * t1 * t3 ^ 2).natDegree ≤ 3 * d :=
        (natDegree_mul_le_add_610 h9216t ht32).trans (by omega)
      have h := natDegree_mul_le_add_610 h9216tr hg1
      exact C_mul_natDegree_le_610 κ (by simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega)))
    have hkuv : (Polynomial.C κ * ((9216 : K[X]) * u * v)).natDegree ≤ 2 * d :=
      C_mul_natDegree_le_610 κ (by
        have h9216u : ((9216 : K[X]) * u).natDegree ≤ d :=
          natCast_mul_natDegree_le_610 9216 hu
        exact (natDegree_mul_le_add_610 h9216u hv).trans (by omega))
    have hktvg : (Polynomial.C κ * ((9216 : K[X]) * t3 * v * g1)).natDegree ≤
        3 * d := by
      have h9216r : ((9216 : K[X]) * t3).natDegree ≤ d :=
        natCast_mul_natDegree_le_610 9216 ht3
      have h9216rv : ((9216 : K[X]) * t3 * v).natDegree ≤ 2 * d :=
        (natDegree_mul_le_add_610 h9216r hv).trans (by omega)
      have h := natDegree_mul_le_add_610 h9216rv hg1
      exact C_mul_natDegree_le_610 κ (by simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega)))
    have hka : (Polynomial.C κ * ((6718464 : K[X]) * t3 * a0)).natDegree ≤
        2 * d :=
      C_mul_natDegree_le_610 κ (by
        have hN : ((6718464 : K[X]) * t3).natDegree ≤ d :=
          natCast_mul_natDegree_le_610 6718464 ht3
        exact (natDegree_mul_le_add_610 hN ha0).trans (by omega))
    have hv3c : ((46080 : K[X]) * t1 ^ 3 * v).coeff (5 * d) = 0 :=
      coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hv3 (by omega))
    have hu4c : ((46080 : K[X]) * t1 ^ 2 * u * t3).coeff (5 * d) = 0 :=
      coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hu4 (by omega))
    have huvc : ((23040 : K[X]) * t1 * u * v).coeff (5 * d) = 0 :=
      coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt huv (by omega))
    have htvgc : ((23040 : K[X]) * t1 * t3 * v * g1).coeff (5 * d) = 0 :=
      coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt htvg (by omega))
    have htac : ((16796160 : K[X]) * t1 * t3 * a0).coeff (5 * d) = 0 :=
      coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hta (by omega))
    have hu2tc : ((3840 : K[X]) * u ^ 2 * t3).coeff (5 * d) = 0 :=
      coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hu2t (by omega))
    have hutgc : ((3840 : K[X]) * u * t3 ^ 2 * g1).coeff (5 * d) = 0 :=
      coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hutg (by omega))
    have hv2gc : ((11520 : K[X]) * v ^ 2 * g1).coeff (5 * d) = 0 :=
      coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hv2g (by omega))
    have hvac : ((16796160 : K[X]) * v * a0).coeff (5 * d) = 0 :=
      coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hva (by omega))
    have hk7c : (Polynomial.C κ₇ * ((3 : K[X]) * t3)).coeff (5 * d) = 0 :=
      coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hk7 (by omega))
    have hk5tc : (Polynomial.C κ₅ * ((96 : K[X]) * t1 * t3)).coeff (5 * d) = 0 :=
      coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hk5t (by omega))
    have hk5vc : (Polynomial.C κ₅ * ((96 : K[X]) * v)).coeff (5 * d) = 0 :=
      coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hk5v (by omega))
    have hkt3c : (Polynomial.C κ * ((46080 : K[X]) * t1 ^ 3 * t3)).coeff (5 * d) =
        0 :=
      coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hkt3 (by omega))
    have hkvc : (Polynomial.C κ * ((27648 : K[X]) * t1 ^ 2 * v)).coeff (5 * d) =
        0 :=
      coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hkv (by omega))
    have hkuc : (Polynomial.C κ * ((18432 : K[X]) * t1 * u * t3)).coeff (5 * d) =
        0 :=
      coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hku (by omega))
    have hktgc : (Polynomial.C κ * ((9216 : K[X]) * t1 * t3 ^ 2 * g1)).coeff
        (5 * d) = 0 :=
      coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hktg (by omega))
    have hkuvc : (Polynomial.C κ * ((9216 : K[X]) * u * v)).coeff (5 * d) = 0 :=
      coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hkuv (by omega))
    have hktvgc : (Polynomial.C κ * ((9216 : K[X]) * t3 * v * g1)).coeff
        (5 * d) = 0 :=
      coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hktvg (by omega))
    have hkac : (Polynomial.C κ * ((6718464 : K[X]) * t3 * a0)).coeff (5 * d) =
        0 :=
      coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hka (by omega))
    simp only [alignedEleventhNonsquareResidueHFree610, Polynomial.coeff_add,
      Polynomial.coeff_sub, Polynomial.coeff_neg, htop1c, htop2c, htop3c, hv3c,
      hu4c, huvc, htvgc, htac, hu2tc, hutgc, hv2gc, hvac, hk7c, hk5tc, hk5vc,
      hkt3c, hkvc, hkuc, hktgc, hkuvc, hktvgc, hkac]
    ring
  have hres :
      (alignedEleventhNonsquareResidue610 H g1 t1 u t3 v a0 κ κ₅ κ₇).coeff
          (5 * d) =
        (alignedEleventhNonsquareResidueHFree610 g1 t1 u t3 v a0 κ κ₅ κ₇).coeff
          (5 * d) := by
    rw [hsplit, Polynomial.coeff_add, hH0, add_zero]
  rw [hres, hfree]
  ring

theorem alignedEleventhNonsquareResidue_eqDegree_t3_or_form_610
    {H g1 t1 u t3 v a0 : K[X]} {κ κ₅ κ₇ : K} {d : ℕ}
    (hd : 3 ≤ d) (hH : H.natDegree ≤ 2)
    (hg1 : g1.natDegree ≤ d) (ht1 : t1.natDegree ≤ d)
    (hu : u.natDegree ≤ d) (ht3 : t3.natDegree ≤ d)
    (hv : v.natDegree ≤ d) (ha0 : a0.natDegree ≤ d)
    (hres : alignedEleventhNonsquareResidue610 H g1 t1 u t3 v a0 κ κ₅ κ₇ =
      0) :
    t3.coeff d = 0 ∨
      (g1.coeff d) ^ 2 * (t3.coeff d) ^ 2 +
          (18 : K) * g1.coeff d * (t1.coeff d) ^ 2 * t3.coeff d +
          (63 : K) * (t1.coeff d) ^ 4 = 0 := by
  have hcoeff := alignedEleventhNonsquareResidue_coeff_fiveMul_610 H g1 t1 u
    t3 v a0 κ κ₅ κ₇ hd hH hg1 ht1 hu ht3 hv ha0
  have htop : (1280 : K) * t3.coeff d *
      ((g1.coeff d) ^ 2 * (t3.coeff d) ^ 2 +
        (18 : K) * g1.coeff d * (t1.coeff d) ^ 2 * t3.coeff d +
        (63 : K) * (t1.coeff d) ^ 4) = 0 := by
    have : (0 : K[X]).coeff (5 * d) = 0 := by simp
    rw [← hcoeff, hres, this]
  have h1280 : (1280 : K) ≠ 0 := by norm_num
  rcases mul_eq_zero.mp htop with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact (h1280 h').elim
    · exact Or.inl h'
  · exact Or.inr h

/-! ## Tenth-block leading coefficient (`d ≥ 3`) -/

set_option maxHeartbeats 16000000 in
theorem alignedTenthNonsquareSolved_coeff_fiveMul_610
    (H g1 t1 u t3 v a0 : K[X]) (κ κ₃ κ₅ κ₇ : K) {d : ℕ}
    (hd : 3 ≤ d) (hH : H.natDegree ≤ 2)
    (hg1 : g1.natDegree ≤ d) (ht1 : t1.natDegree ≤ d)
    (hu : u.natDegree ≤ d) (ht3 : t3.natDegree ≤ d)
    (hv : v.natDegree ≤ d) (ha0 : a0.natDegree ≤ d) :
    (alignedTenthNonsquareSolved610 H g1 t1 u t3 v a0 κ κ₃ κ₅ κ₇).coeff
        (5 * d) =
      (-387072 : K) * (t1.coeff d) ^ 5 := by
  have ht15 : (t1 ^ 5).natDegree ≤ 5 * d := natDegree_pow_le_mul_610 ht1
  have htop : ((387072 : K[X]) * t1 ^ 5).coeff (5 * d) =
      (387072 : K) * (t1.coeff d) ^ 5 := by
    have hpow : (t1 ^ 5).coeff (5 * d) = (t1.coeff d) ^ 5 :=
      coeff_pow_of_natDegree_le_610 (n := 5) ht1
    have h := coeff_mul_of_natDegree_le_610
      (p := (387072 : K[X])) (q := t1 ^ 5) (m := 0) (n := 5 * d)
      (by
        have : (387072 : K[X]) = Polynomial.C (387072 : K) :=
          (Polynomial.C_eq_natCast 387072).symm
        simp [this]) ht15
    have h0 : ((387072 : K[X]).coeff 0) = (387072 : K) := by
      have : (387072 : K[X]) = Polynomial.C (387072 : K) :=
        (Polynomial.C_eq_natCast 387072).symm
      simp [this]
    simpa [h0, hpow] using h
  have ht13 : (t1 ^ 3).natDegree ≤ 3 * d := natDegree_pow_le_mul_610 ht1
  have ht14 : (t1 ^ 4).natDegree ≤ 4 * d := natDegree_pow_le_mul_610 ht1
  have ht12 : (t1 ^ 2).natDegree ≤ 2 * d := natDegree_pow_le_mul_610 ht1
  have hu2 : (u ^ 2).natDegree ≤ 2 * d := natDegree_pow_le_mul_610 hu
  have ht32 : (t3 ^ 2).natDegree ≤ 2 * d := natDegree_pow_le_mul_610 ht3
  have ht33 : (t3 ^ 3).natDegree ≤ 3 * d := natDegree_pow_le_mul_610 ht3
  have hv2 : (v ^ 2).natDegree ≤ 2 * d := natDegree_pow_le_mul_610 hv
  have h1 : ((368640 : K[X]) * t1 ^ 3 * u).natDegree ≤ 4 * d := by
    have h368640t : ((368640 : K[X]) * t1 ^ 3).natDegree ≤ 3 * d :=
      natCast_mul_natDegree_le_610 368640 ht13
    have h := natDegree_mul_le_add_610 h368640t hu
    simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega))
  have h2 : ((201553920 : K[X]) * t1 ^ 2 * a0).natDegree ≤ 3 * d := by
    have hN : ((201553920 : K[X]) * t1 ^ 2).natDegree ≤ 2 * d :=
      natCast_mul_natDegree_le_610 201553920 ht12
    have h := natDegree_mul_le_add_610 hN ha0
    simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega))
  have h3 : ((92160 : K[X]) * t1 * u ^ 2).natDegree ≤ 3 * d := by
    have h92160t : ((92160 : K[X]) * t1).natDegree ≤ d :=
      natCast_mul_natDegree_le_610 92160 ht1
    have h := natDegree_mul_le_add_610 h92160t hu2
    simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega))
  have h4 : ((134369280 : K[X]) * u * a0).natDegree ≤ 2 * d := by
    have hN : ((134369280 : K[X]) * u).natDegree ≤ d :=
      natCast_mul_natDegree_le_610 134369280 hu
    have h := natDegree_mul_le_add_610 hN ha0
    simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega))
  have hk7 : (Polynomial.C κ₇ * ((72 : K[X]) * t1)).natDegree ≤ d :=
    C_mul_natDegree_le_610 κ₇ (natCast_mul_natDegree_le_610 72 ht1)
  have hk5t : (Polynomial.C κ₅ * ((1152 : K[X]) * t1 ^ 2)).natDegree ≤
      2 * d :=
    C_mul_natDegree_le_610 κ₅ (natCast_mul_natDegree_le_610 1152 ht12)
  have hk5u : (Polynomial.C κ₅ * ((768 : K[X]) * u)).natDegree ≤ d :=
    C_mul_natDegree_le_610 κ₅ (natCast_mul_natDegree_le_610 768 hu)
  have hk3 : (Polynomial.C κ₃ * ((20155392 : K[X]) * a0)).natDegree ≤ d :=
    C_mul_natDegree_le_610 κ₃ (natCast_mul_natDegree_le_610 20155392 ha0)
  have hk4 : (Polynomial.C κ * ((276480 : K[X]) * t1 ^ 4)).natDegree ≤
      4 * d :=
    C_mul_natDegree_le_610 κ (natCast_mul_natDegree_le_610 276480 ht14)
  have hku : (Polynomial.C κ * ((221184 : K[X]) * t1 ^ 2 * u)).natDegree ≤
      3 * d := by
    have h221184t : ((221184 : K[X]) * t1 ^ 2).natDegree ≤ 2 * d :=
      natCast_mul_natDegree_le_610 221184 ht12
    have h := natDegree_mul_le_add_610 h221184t hu
    exact C_mul_natDegree_le_610 κ (by simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega)))
  have hka : (Polynomial.C κ * ((161243136 : K[X]) * t1 * a0)).natDegree ≤
      2 * d := by
    have hN : ((161243136 : K[X]) * t1).natDegree ≤ d :=
      natCast_mul_natDegree_le_610 161243136 ht1
    have h := natDegree_mul_le_add_610 hN ha0
    exact C_mul_natDegree_le_610 κ (by simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega)))
  have hku2 : (Polynomial.C κ * ((36864 : K[X]) * u ^ 2)).natDegree ≤ 2 * d :=
    C_mul_natDegree_le_610 κ (natCast_mul_natDegree_le_610 36864 hu2)
  have hHbody : ((184320 : K[X]) * t1 ^ 2 * t3 ^ 2 -
        (184320 : K[X]) * t1 * t3 * v - (30720 : K[X]) * u * t3 ^ 2 +
        (10240 : K[X]) * t3 ^ 3 * g1 + (92160 : K[X]) * v ^ 2 -
        Polynomial.C κ * ((73728 : K[X]) * t1 * t3 ^ 2) +
        Polynomial.C κ * ((73728 : K[X]) * t3 * v)).natDegree ≤ 4 * d := by
    have ha : ((184320 : K[X]) * t1 ^ 2 * t3 ^ 2).natDegree ≤ 4 * d := by
      have h184320t : ((184320 : K[X]) * t1 ^ 2).natDegree ≤ 2 * d :=
        natCast_mul_natDegree_le_610 184320 ht12
      have h := natDegree_mul_le_add_610 h184320t ht32
      simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega))
    have hb : ((184320 : K[X]) * t1 * t3 * v).natDegree ≤ 3 * d := by
      have h184320t : ((184320 : K[X]) * t1).natDegree ≤ d :=
        natCast_mul_natDegree_le_610 184320 ht1
      have h184320tr : ((184320 : K[X]) * t1 * t3).natDegree ≤ 2 * d :=
        (natDegree_mul_le_add_610 h184320t ht3).trans (by omega)
      have h := natDegree_mul_le_add_610 h184320tr hv
      simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega))
    have hc : ((30720 : K[X]) * u * t3 ^ 2).natDegree ≤ 3 * d := by
      have h30720u : ((30720 : K[X]) * u).natDegree ≤ d :=
        natCast_mul_natDegree_le_610 30720 hu
      have h := natDegree_mul_le_add_610 h30720u ht32
      simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega))
    have hd' : ((10240 : K[X]) * t3 ^ 3 * g1).natDegree ≤ 4 * d := by
      have h10240t : ((10240 : K[X]) * t3 ^ 3).natDegree ≤ 3 * d :=
        natCast_mul_natDegree_le_610 10240 ht33
      have h := natDegree_mul_le_add_610 h10240t hg1
      simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega))
    have he : ((92160 : K[X]) * v ^ 2).natDegree ≤ 2 * d :=
      natCast_mul_natDegree_le_610 92160 hv2
    have hf : (Polynomial.C κ * ((73728 : K[X]) * t1 * t3 ^ 2)).natDegree ≤
        3 * d := by
      have h73728t : ((73728 : K[X]) * t1).natDegree ≤ d :=
        natCast_mul_natDegree_le_610 73728 ht1
      have h := natDegree_mul_le_add_610 h73728t ht32
      exact C_mul_natDegree_le_610 κ (by simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega)))
    have hg : (Polynomial.C κ * ((73728 : K[X]) * t3 * v)).natDegree ≤
        2 * d := by
      have h73728r : ((73728 : K[X]) * t3).natDegree ≤ d :=
        natCast_mul_natDegree_le_610 73728 ht3
      have h := natDegree_mul_le_add_610 h73728r hv
      exact C_mul_natDegree_le_610 κ (by simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega)))
    exact natDegree_add_le_of_le_610
      (natDegree_sub_le_of_le_610
        (natDegree_add_le_of_le_610
          (natDegree_add_le_of_le_610
            (natDegree_sub_le_of_le_610
              (natDegree_sub_le_of_le_610
                (natDegree_le_trans_610 (n := 4 * d) ha (by omega))
                (natDegree_le_trans_610 (n := 4 * d) hb (by omega)))
              (natDegree_le_trans_610 (n := 4 * d) hc (by omega)))
            (natDegree_le_trans_610 (n := 4 * d) hd' (by omega)))
          (natDegree_le_trans_610 (n := 4 * d) he (by omega)))
        (natDegree_le_trans_610 (n := 4 * d) hf (by omega)))
      (natDegree_le_trans_610 (n := 4 * d) hg (by omega))
  have hHmul : (H * ((184320 : K[X]) * t1 ^ 2 * t3 ^ 2 -
        (184320 : K[X]) * t1 * t3 * v - (30720 : K[X]) * u * t3 ^ 2 +
        (10240 : K[X]) * t3 ^ 3 * g1 + (92160 : K[X]) * v ^ 2 -
        Polynomial.C κ * ((73728 : K[X]) * t1 * t3 ^ 2) +
        Polynomial.C κ * ((73728 : K[X]) * t3 * v))).natDegree ≤
      2 + 4 * d :=
    natDegree_mul_le_add_610 hH hHbody
  have h1c : ((368640 : K[X]) * t1 ^ 3 * u).coeff (5 * d) = 0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt h1 (by omega))
  have h2c : ((201553920 : K[X]) * t1 ^ 2 * a0).coeff (5 * d) = 0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt h2 (by omega))
  have h3c : ((92160 : K[X]) * t1 * u ^ 2).coeff (5 * d) = 0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt h3 (by omega))
  have h4c : ((134369280 : K[X]) * u * a0).coeff (5 * d) = 0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt h4 (by omega))
  have hk7c : (Polynomial.C κ₇ * ((72 : K[X]) * t1)).coeff (5 * d) = 0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hk7 (by omega))
  have hk5tc : (Polynomial.C κ₅ * ((1152 : K[X]) * t1 ^ 2)).coeff (5 * d) = 0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hk5t (by omega))
  have hk5uc : (Polynomial.C κ₅ * ((768 : K[X]) * u)).coeff (5 * d) = 0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hk5u (by omega))
  have hk3c : (Polynomial.C κ₃ * ((20155392 : K[X]) * a0)).coeff (5 * d) = 0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hk3 (by omega))
  have hk4c : (Polynomial.C κ * ((276480 : K[X]) * t1 ^ 4)).coeff (5 * d) = 0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hk4 (by omega))
  have hkuc : (Polynomial.C κ * ((221184 : K[X]) * t1 ^ 2 * u)).coeff (5 * d) =
      0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hku (by omega))
  have hkac : (Polynomial.C κ * ((161243136 : K[X]) * t1 * a0)).coeff (5 * d) =
      0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hka (by omega))
  have hku2c : (Polynomial.C κ * ((36864 : K[X]) * u ^ 2)).coeff (5 * d) = 0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hku2 (by omega))
  have hHmc : (H * ((184320 : K[X]) * t1 ^ 2 * t3 ^ 2 -
        (184320 : K[X]) * t1 * t3 * v - (30720 : K[X]) * u * t3 ^ 2 +
        (10240 : K[X]) * t3 ^ 3 * g1 + (92160 : K[X]) * v ^ 2 -
        Polynomial.C κ * ((73728 : K[X]) * t1 * t3 ^ 2) +
        Polynomial.C κ * ((73728 : K[X]) * t3 * v))).coeff (5 * d) = 0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hHmul (by omega))
  simp only [alignedTenthNonsquareSolved610, Polynomial.coeff_add,
    Polynomial.coeff_sub, Polynomial.coeff_neg, htop, h1c, h2c, h3c, h4c,
    hk7c, hk5tc, hk5uc, hk3c, hk4c, hkuc, hkac, hku2c, hHmc]
  ring

/-! ## Tenth / ninth / eighth degree bounds (`d ≥ 3`) -/

set_option maxHeartbeats 16000000 in
theorem alignedTenthNonsquareSolved_natDegree_le_fiveMul_610
    (H g1 t1 u t3 v a0 : K[X]) (κ κ₃ κ₅ κ₇ : K) {d : ℕ}
    (hd : 3 ≤ d) (hH : H.natDegree ≤ 2)
    (hg1 : g1.natDegree ≤ d) (ht1 : t1.natDegree ≤ d)
    (hu : u.natDegree ≤ d) (ht3 : t3.natDegree ≤ d)
    (hv : v.natDegree ≤ d) (ha0 : a0.natDegree ≤ d) :
    (alignedTenthNonsquareSolved610 H g1 t1 u t3 v a0 κ κ₃ κ₅ κ₇).natDegree
      ≤ 5 * d := by
  have htop : ((387072 : K[X]) * t1 ^ 5).natDegree ≤ 5 * d :=
    natCast_mul_natDegree_le_610 387072 (natDegree_pow_le_mul_610 ht1)
  have ht13 : (t1 ^ 3).natDegree ≤ 3 * d := natDegree_pow_le_mul_610 ht1
  have ht14 : (t1 ^ 4).natDegree ≤ 4 * d := natDegree_pow_le_mul_610 ht1
  have ht12 : (t1 ^ 2).natDegree ≤ 2 * d := natDegree_pow_le_mul_610 ht1
  have hu2 : (u ^ 2).natDegree ≤ 2 * d := natDegree_pow_le_mul_610 hu
  have ht32 : (t3 ^ 2).natDegree ≤ 2 * d := natDegree_pow_le_mul_610 ht3
  have ht33 : (t3 ^ 3).natDegree ≤ 3 * d := natDegree_pow_le_mul_610 ht3
  have hv2 : (v ^ 2).natDegree ≤ 2 * d := natDegree_pow_le_mul_610 hv
  have h1 : ((368640 : K[X]) * t1 ^ 3 * u).natDegree ≤ 4 * d := by
    have h368640t : ((368640 : K[X]) * t1 ^ 3).natDegree ≤ 3 * d :=
      natCast_mul_natDegree_le_610 368640 ht13
    have h := natDegree_mul_le_add_610 h368640t hu
    simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega))
  have h2 : ((201553920 : K[X]) * t1 ^ 2 * a0).natDegree ≤ 3 * d := by
    have hN : ((201553920 : K[X]) * t1 ^ 2).natDegree ≤ 2 * d :=
      natCast_mul_natDegree_le_610 201553920 ht12
    have h := natDegree_mul_le_add_610 hN ha0
    simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega))
  have h3 : ((92160 : K[X]) * t1 * u ^ 2).natDegree ≤ 3 * d := by
    have h92160t : ((92160 : K[X]) * t1).natDegree ≤ d :=
      natCast_mul_natDegree_le_610 92160 ht1
    have h := natDegree_mul_le_add_610 h92160t hu2
    simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega))
  have h4 : ((134369280 : K[X]) * u * a0).natDegree ≤ 2 * d := by
    have hN : ((134369280 : K[X]) * u).natDegree ≤ d :=
      natCast_mul_natDegree_le_610 134369280 hu
    have h := natDegree_mul_le_add_610 hN ha0
    simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega))
  have hk7 : (Polynomial.C κ₇ * ((72 : K[X]) * t1)).natDegree ≤ d :=
    C_mul_natDegree_le_610 κ₇ (natCast_mul_natDegree_le_610 72 ht1)
  have hk5t : (Polynomial.C κ₅ * ((1152 : K[X]) * t1 ^ 2)).natDegree ≤ 2 * d :=
    C_mul_natDegree_le_610 κ₅ (natCast_mul_natDegree_le_610 1152 ht12)
  have hk5u : (Polynomial.C κ₅ * ((768 : K[X]) * u)).natDegree ≤ d :=
    C_mul_natDegree_le_610 κ₅ (natCast_mul_natDegree_le_610 768 hu)
  have hk3 : (Polynomial.C κ₃ * ((20155392 : K[X]) * a0)).natDegree ≤ d :=
    C_mul_natDegree_le_610 κ₃ (natCast_mul_natDegree_le_610 20155392 ha0)
  have hk4 : (Polynomial.C κ * ((276480 : K[X]) * t1 ^ 4)).natDegree ≤ 4 * d :=
    C_mul_natDegree_le_610 κ (natCast_mul_natDegree_le_610 276480 ht14)
  have hku : (Polynomial.C κ * ((221184 : K[X]) * t1 ^ 2 * u)).natDegree ≤
      3 * d := by
    have h221184t : ((221184 : K[X]) * t1 ^ 2).natDegree ≤ 2 * d :=
      natCast_mul_natDegree_le_610 221184 ht12
    have h := natDegree_mul_le_add_610 h221184t hu
    exact C_mul_natDegree_le_610 κ (by simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega)))
  have hka : (Polynomial.C κ * ((161243136 : K[X]) * t1 * a0)).natDegree ≤
      2 * d := by
    have hN : ((161243136 : K[X]) * t1).natDegree ≤ d :=
      natCast_mul_natDegree_le_610 161243136 ht1
    have h := natDegree_mul_le_add_610 hN ha0
    exact C_mul_natDegree_le_610 κ (by simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega)))
  have hku2 : (Polynomial.C κ * ((36864 : K[X]) * u ^ 2)).natDegree ≤ 2 * d :=
    C_mul_natDegree_le_610 κ (natCast_mul_natDegree_le_610 36864 hu2)
  have hHbody : ((184320 : K[X]) * t1 ^ 2 * t3 ^ 2 -
        (184320 : K[X]) * t1 * t3 * v - (30720 : K[X]) * u * t3 ^ 2 +
        (10240 : K[X]) * t3 ^ 3 * g1 + (92160 : K[X]) * v ^ 2 -
        Polynomial.C κ * ((73728 : K[X]) * t1 * t3 ^ 2) +
        Polynomial.C κ * ((73728 : K[X]) * t3 * v)).natDegree ≤ 4 * d := by
    have ha : ((184320 : K[X]) * t1 ^ 2 * t3 ^ 2).natDegree ≤ 4 * d := by
      have h184320t : ((184320 : K[X]) * t1 ^ 2).natDegree ≤ 2 * d :=
        natCast_mul_natDegree_le_610 184320 ht12
      have h := natDegree_mul_le_add_610 h184320t ht32
      simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega))
    have hb : ((184320 : K[X]) * t1 * t3 * v).natDegree ≤ 3 * d := by
      have h184320t : ((184320 : K[X]) * t1).natDegree ≤ d :=
        natCast_mul_natDegree_le_610 184320 ht1
      have h184320tr : ((184320 : K[X]) * t1 * t3).natDegree ≤ 2 * d :=
        (natDegree_mul_le_add_610 h184320t ht3).trans (by omega)
      have h := natDegree_mul_le_add_610 h184320tr hv
      simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega))
    have hc : ((30720 : K[X]) * u * t3 ^ 2).natDegree ≤ 3 * d := by
      have h30720u : ((30720 : K[X]) * u).natDegree ≤ d :=
        natCast_mul_natDegree_le_610 30720 hu
      have h := natDegree_mul_le_add_610 h30720u ht32
      simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega))
    have hd' : ((10240 : K[X]) * t3 ^ 3 * g1).natDegree ≤ 4 * d := by
      have h10240t : ((10240 : K[X]) * t3 ^ 3).natDegree ≤ 3 * d :=
        natCast_mul_natDegree_le_610 10240 ht33
      have h := natDegree_mul_le_add_610 h10240t hg1
      simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega))
    have he : ((92160 : K[X]) * v ^ 2).natDegree ≤ 2 * d :=
      natCast_mul_natDegree_le_610 92160 hv2
    have hf : (Polynomial.C κ * ((73728 : K[X]) * t1 * t3 ^ 2)).natDegree ≤
        3 * d := by
      have h73728t : ((73728 : K[X]) * t1).natDegree ≤ d :=
        natCast_mul_natDegree_le_610 73728 ht1
      have h := natDegree_mul_le_add_610 h73728t ht32
      exact C_mul_natDegree_le_610 κ (by simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega)))
    have hg : (Polynomial.C κ * ((73728 : K[X]) * t3 * v)).natDegree ≤ 2 * d := by
      have h73728r : ((73728 : K[X]) * t3).natDegree ≤ d :=
        natCast_mul_natDegree_le_610 73728 ht3
      have h := natDegree_mul_le_add_610 h73728r hv
      exact C_mul_natDegree_le_610 κ (by simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega)))
    exact natDegree_add_le_of_le_610
      (natDegree_sub_le_of_le_610
        (natDegree_add_le_of_le_610
          (natDegree_add_le_of_le_610
            (natDegree_sub_le_of_le_610
              (natDegree_sub_le_of_le_610
                (natDegree_le_trans_610 (n := 4 * d) ha (by omega))
                (natDegree_le_trans_610 (n := 4 * d) hb (by omega)))
              (natDegree_le_trans_610 (n := 4 * d) hc (by omega)))
            (natDegree_le_trans_610 (n := 4 * d) hd' (by omega)))
          (natDegree_le_trans_610 (n := 4 * d) he (by omega)))
        (natDegree_le_trans_610 (n := 4 * d) hf (by omega)))
      (natDegree_le_trans_610 (n := 4 * d) hg (by omega))
  have hHmul : (H * ((184320 : K[X]) * t1 ^ 2 * t3 ^ 2 -
        (184320 : K[X]) * t1 * t3 * v - (30720 : K[X]) * u * t3 ^ 2 +
        (10240 : K[X]) * t3 ^ 3 * g1 + (92160 : K[X]) * v ^ 2 -
        Polynomial.C κ * ((73728 : K[X]) * t1 * t3 ^ 2) +
        Polynomial.C κ * ((73728 : K[X]) * t3 * v))).natDegree ≤ 2 + 4 * d :=
    (natDegree_mul_le_add_610 hH hHbody).trans (by omega)
  simp only [alignedTenthNonsquareSolved610]
  -- `(H-free) + H * body`
  refine natDegree_add_le_of_le_610 ?_
    (natDegree_le_trans_610 (n := 5 * d) hHmul (by omega))
  refine natDegree_add_le_of_le_610 ?_ (natDegree_le_trans_610 hku2 (by omega))
  refine natDegree_add_le_of_le_610 ?_ (natDegree_le_trans_610 hka (by omega))
  refine natDegree_sub_le_of_le_610 ?_ (natDegree_le_trans_610 hku (by omega))
  refine natDegree_add_le_of_le_610 ?_ (natDegree_le_trans_610 hk4 (by omega))
  refine natDegree_sub_le_of_le_610 ?_ (natDegree_le_trans_610 hk3 (by omega))
  refine natDegree_sub_le_of_le_610 ?_ (natDegree_le_trans_610 hk5u (by omega))
  refine natDegree_add_le_of_le_610 ?_ (natDegree_le_trans_610 hk5t (by omega))
  refine natDegree_sub_le_of_le_610 ?_ (natDegree_le_trans_610 hk7 (by omega))
  refine natDegree_add_le_of_le_610 ?_ (natDegree_le_trans_610 h4 (by omega))
  refine natDegree_sub_le_of_le_610 ?_ (natDegree_le_trans_610 h3 (by omega))
  refine natDegree_sub_le_of_le_610 ?_ (natDegree_le_trans_610 h2 (by omega))
  exact natDegree_add_le_of_le_610 (natDegree_neg_le_of_le_610 htop)
    (natDegree_le_trans_610 h1 (by omega))

set_option maxHeartbeats 16000000 in
theorem alignedNinthNonsquareSolved_natDegree_le_fiveMul_610
    (H g1 t1 t2 u t3 a0 a1 : K[X]) (κ κ₃ κ₅ κ₇ : K) {d : ℕ}
    (hd : 3 ≤ d) (hH : H.natDegree ≤ 2)
    (hg1 : g1.natDegree ≤ d) (ht1 : t1.natDegree ≤ d)
    (ht2 : t2.natDegree ≤ 2 * d) (hu : u.natDegree ≤ d)
    (ht3 : t3.natDegree ≤ d) (ha0 : a0.natDegree ≤ d)
    (ha1 : a1.natDegree ≤ 2 * d) :
    (alignedNinthNonsquareSolved610 H g1 t1 t2 u t3 a0 a1 κ κ₃ κ₅ κ₇).natDegree
      ≤ 5 * d := by
  have ht14 : (t1 ^ 4).natDegree ≤ 4 * d := natDegree_pow_le_mul_610 ht1
  have ht13 : (t1 ^ 3).natDegree ≤ 3 * d := natDegree_pow_le_mul_610 ht1
  have ht12 : (t1 ^ 2).natDegree ≤ 2 * d := natDegree_pow_le_mul_610 ht1
  have hu2 : (u ^ 2).natDegree ≤ 2 * d := natDegree_pow_le_mul_610 hu
  have ht33 : (t3 ^ 3).natDegree ≤ 3 * d := natDegree_pow_le_mul_610 ht3
  have h1 : ((967680 : K[X]) * t1 ^ 4 * g1).natDegree ≤ 5 * d := by
    have h967680t : ((967680 : K[X]) * t1 ^ 4).natDegree ≤ 4 * d :=
      natCast_mul_natDegree_le_610 967680 ht14
    have h := natDegree_mul_le_add_610 h967680t hg1
    simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega))
  have h2 : ((184320 : K[X]) * t1 ^ 3 * t2).natDegree ≤ 5 * d := by
    have h184320t : ((184320 : K[X]) * t1 ^ 3).natDegree ≤ 3 * d :=
      natCast_mul_natDegree_le_610 184320 ht13
    have h := natDegree_mul_le_add_610 h184320t ht2
    simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega))
  have h3 : ((552960 : K[X]) * t1 ^ 2 * u * g1).natDegree ≤ 4 * d := by
    have h552960t : ((552960 : K[X]) * t1 ^ 2).natDegree ≤ 2 * d :=
      natCast_mul_natDegree_le_610 552960 ht12
    have h552960tu : ((552960 : K[X]) * t1 ^ 2 * u).natDegree ≤ 3 * d :=
      (natDegree_mul_le_add_610 h552960t hu).trans (by omega)
    have h := natDegree_mul_le_add_610 h552960tu hg1
    simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega))
  have h4 : ((33592320 : K[X]) * t1 ^ 2 * a1).natDegree ≤ 4 * d := by
    have hN : ((33592320 : K[X]) * t1 ^ 2).natDegree ≤ 2 * d :=
      natCast_mul_natDegree_le_610 33592320 ht12
    have h := natDegree_mul_le_add_610 hN ha1
    simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega))
  have h5 : ((92160 : K[X]) * t1 * t2 * u).natDegree ≤ 4 * d := by
    have h92160t : ((92160 : K[X]) * t1).natDegree ≤ d :=
      natCast_mul_natDegree_le_610 92160 ht1
    have h92160tt : ((92160 : K[X]) * t1 * t2).natDegree ≤ 3 * d :=
      (natDegree_mul_le_add_610 h92160t ht2).trans (by omega)
    have h := natDegree_mul_le_add_610 h92160tt hu
    simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega))
  have h6 : ((201553920 : K[X]) * t1 * g1 * a0).natDegree ≤ 3 * d := by
    have hN : ((201553920 : K[X]) * t1).natDegree ≤ d :=
      natCast_mul_natDegree_le_610 201553920 ht1
    have hNg : ((201553920 : K[X]) * t1 * g1).natDegree ≤ 2 * d :=
      (natDegree_mul_le_add_610 hN hg1).trans (by omega)
    have h := natDegree_mul_le_add_610 hNg ha0
    simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega))
  have h7 : ((67184640 : K[X]) * t2 * a0).natDegree ≤ 3 * d := by
    have hN : ((67184640 : K[X]) * t2).natDegree ≤ 2 * d :=
      natCast_mul_natDegree_le_610 67184640 ht2
    have h := natDegree_mul_le_add_610 hN ha0
    simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega))
  have h8 : ((46080 : K[X]) * u ^ 2 * g1).natDegree ≤ 3 * d := by
    have h46080u : ((46080 : K[X]) * u ^ 2).natDegree ≤ 2 * d :=
      natCast_mul_natDegree_le_610 46080 hu2
    have h := natDegree_mul_le_add_610 h46080u hg1
    simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega))
  have h9 : ((22394880 : K[X]) * u * a1).natDegree ≤ 3 * d := by
    have hN : ((22394880 : K[X]) * u).natDegree ≤ d :=
      natCast_mul_natDegree_le_610 22394880 hu
    have h := natDegree_mul_le_add_610 hN ha1
    simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega))
  have hk7 : (Polynomial.C κ₇ * ((36 : K[X]) * g1)).natDegree ≤ d :=
    C_mul_natDegree_le_610 κ₇ (natCast_mul_natDegree_le_610 36 hg1)
  have hk5t : (Polynomial.C κ₅ * ((1152 : K[X]) * t1 * g1)).natDegree ≤ 2 * d := by
    have h1152t : ((1152 : K[X]) * t1).natDegree ≤ d :=
      natCast_mul_natDegree_le_610 1152 ht1
    have h := natDegree_mul_le_add_610 h1152t hg1
    exact C_mul_natDegree_le_610 κ₅ (by simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega)))
  have hk5t2 : (Polynomial.C κ₅ * ((384 : K[X]) * t2)).natDegree ≤ 2 * d :=
    C_mul_natDegree_le_610 κ₅ (natCast_mul_natDegree_le_610 384 ht2)
  have hk3 : (Polynomial.C κ₃ * ((3359232 : K[X]) * a1)).natDegree ≤ 2 * d :=
    C_mul_natDegree_le_610 κ₃ (natCast_mul_natDegree_le_610 3359232 ha1)
  have hkA : (Polynomial.C κ * ((552960 : K[X]) * t1 ^ 3 * g1)).natDegree ≤
      4 * d := by
    have h552960t : ((552960 : K[X]) * t1 ^ 3).natDegree ≤ 3 * d :=
      natCast_mul_natDegree_le_610 552960 ht13
    have h := natDegree_mul_le_add_610 h552960t hg1
    exact C_mul_natDegree_le_610 κ (by simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega)))
  have hkB : (Polynomial.C κ * ((110592 : K[X]) * t1 ^ 2 * t2)).natDegree ≤
      4 * d := by
    have h110592t : ((110592 : K[X]) * t1 ^ 2).natDegree ≤ 2 * d :=
      natCast_mul_natDegree_le_610 110592 ht12
    have h := natDegree_mul_le_add_610 h110592t ht2
    exact C_mul_natDegree_le_610 κ (by simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega)))
  have hkC : (Polynomial.C κ * ((221184 : K[X]) * t1 * u * g1)).natDegree ≤
      3 * d := by
    have h221184t : ((221184 : K[X]) * t1).natDegree ≤ d :=
      natCast_mul_natDegree_le_610 221184 ht1
    have h221184tu : ((221184 : K[X]) * t1 * u).natDegree ≤ 2 * d :=
      (natDegree_mul_le_add_610 h221184t hu).trans (by omega)
    have h := natDegree_mul_le_add_610 h221184tu hg1
    exact C_mul_natDegree_le_610 κ (by simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega)))
  have hkD : (Polynomial.C κ * ((26873856 : K[X]) * t1 * a1)).natDegree ≤
      3 * d := by
    have hN : ((26873856 : K[X]) * t1).natDegree ≤ d :=
      natCast_mul_natDegree_le_610 26873856 ht1
    have h := natDegree_mul_le_add_610 hN ha1
    exact C_mul_natDegree_le_610 κ (by simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega)))
  have hkE : (Polynomial.C κ * ((36864 : K[X]) * t2 * u)).natDegree ≤ 3 * d := by
    have h36864t : ((36864 : K[X]) * t2).natDegree ≤ 2 * d :=
      natCast_mul_natDegree_le_610 36864 ht2
    have h := natDegree_mul_le_add_610 h36864t hu
    exact C_mul_natDegree_le_610 κ (by simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega)))
  have hkF : (Polynomial.C κ * ((80621568 : K[X]) * g1 * a0)).natDegree ≤
      2 * d := by
    have hN : ((80621568 : K[X]) * g1).natDegree ≤ d :=
      natCast_mul_natDegree_le_610 80621568 hg1
    have h := natDegree_mul_le_add_610 hN ha0
    exact C_mul_natDegree_le_610 κ (by simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega)))
  have hH2 : (H ^ 2).natDegree ≤ 4 := natDegree_pow_le_mul_610 (n := 2) hH
  have hH2t : (H ^ 2 * ((5120 : K[X]) * t3 ^ 3)).natDegree ≤ 4 + 3 * d := by
    have h5120t : ((5120 : K[X]) * t3 ^ 3).natDegree ≤ 3 * d :=
      natCast_mul_natDegree_le_610 5120 ht33
    exact (natDegree_mul_le_add_610 hH2 h5120t).trans (by omega)
  simp only [alignedNinthNonsquareSolved610]
  -- `(H-free) + H² * (-5120 t₃³)`
  have hH2t5 : (H ^ 2 * -((5120 : K[X]) * t3 ^ 3)).natDegree ≤ 5 * d := by
    rw [mul_neg]
    exact natDegree_neg_le_of_le_610
      (natDegree_le_trans_610 (n := 5 * d) hH2t (by omega))
  refine natDegree_add_le_of_le_610 ?_ hH2t5
  refine natDegree_add_le_of_le_610 ?_ (natDegree_le_trans_610 hkF (by omega))
  refine natDegree_add_le_of_le_610 ?_ (natDegree_le_trans_610 hkE (by omega))
  refine natDegree_add_le_of_le_610 ?_ (natDegree_le_trans_610 hkD (by omega))
  refine natDegree_sub_le_of_le_610 ?_ (natDegree_le_trans_610 hkC (by omega))
  refine natDegree_sub_le_of_le_610 ?_ (natDegree_le_trans_610 hkB (by omega))
  refine natDegree_add_le_of_le_610 ?_ (natDegree_le_trans_610 hkA (by omega))
  refine natDegree_sub_le_of_le_610 ?_ (natDegree_le_trans_610 hk3 (by omega))
  refine natDegree_sub_le_of_le_610 ?_ (natDegree_le_trans_610 hk5t2 (by omega))
  refine natDegree_add_le_of_le_610 ?_ (natDegree_le_trans_610 hk5t (by omega))
  refine natDegree_sub_le_of_le_610 ?_ (natDegree_le_trans_610 hk7 (by omega))
  refine natDegree_add_le_of_le_610 ?_ (natDegree_le_trans_610 h9 (by omega))
  refine natDegree_sub_le_of_le_610 ?_ (natDegree_le_trans_610 h8 (by omega))
  refine natDegree_add_le_of_le_610 ?_ (natDegree_le_trans_610 h7 (by omega))
  refine natDegree_sub_le_of_le_610 ?_ (natDegree_le_trans_610 h6 (by omega))
  refine natDegree_sub_le_of_le_610 ?_ (natDegree_le_trans_610 h5 (by omega))
  refine natDegree_sub_le_of_le_610 ?_ (natDegree_le_trans_610 h4 (by omega))
  refine natDegree_add_le_of_le_610 ?_ (natDegree_le_trans_610 h3 (by omega))
  exact natDegree_add_le_of_le_610 (natDegree_neg_le_of_le_610 h1)
    (natDegree_le_trans_610 h2 (by omega))

set_option maxHeartbeats 16000000 in
theorem alignedEighthNonsquareSolved_natDegree_le_fiveMul_610
    (H g1 t1 t2 u a0 a1 : K[X]) (κ κ₃ κ₅ : K) {d : ℕ}
    (hd : 3 ≤ d) (hH : H.natDegree ≤ 2)
    (hg1 : g1.natDegree ≤ d) (ht1 : t1.natDegree ≤ d)
    (ht2 : t2.natDegree ≤ 2 * d) (hu : u.natDegree ≤ d)
    (ha0 : a0.natDegree ≤ d) (ha1 : a1.natDegree ≤ 2 * d) :
    (alignedEighthNonsquareSolved610 H g1 t1 t2 u a0 a1 κ κ₃ κ₅).natDegree
      ≤ 5 * d := by
  have hg12 : (g1 ^ 2).natDegree ≤ 2 * d := natDegree_pow_le_mul_610 hg1
  have ht13 : (t1 ^ 3).natDegree ≤ 3 * d := natDegree_pow_le_mul_610 ht1
  have ht12 : (t1 ^ 2).natDegree ≤ 2 * d := natDegree_pow_le_mul_610 ht1
  have ht14 : (t1 ^ 4).natDegree ≤ 4 * d := natDegree_pow_le_mul_610 ht1
  have ht22 : (t2 ^ 2).natDegree ≤ 4 * d :=
    natDegree_sq_of_twoMul_le_610 ht2
  have hu2 : (u ^ 2).natDegree ≤ 2 * d := natDegree_pow_le_mul_610 hu
  have h1 : ((2799360 : K[X]) * g1 ^ 2 * a0).natDegree ≤ 3 * d := by
    have hN : ((2799360 : K[X]) * g1 ^ 2).natDegree ≤ 2 * d :=
      natCast_mul_natDegree_le_610 2799360 hg12
    have h := natDegree_mul_le_add_610 hN ha0
    simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega))
  have h2 : ((26880 : K[X]) * g1 ^ 2 * t1 ^ 3).natDegree ≤ 5 * d := by
    have h26880g : ((26880 : K[X]) * g1 ^ 2).natDegree ≤ 2 * d :=
      natCast_mul_natDegree_le_610 26880 hg12
    have h := natDegree_mul_le_add_610 h26880g ht13
    simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega))
  have h3 : ((1866240 : K[X]) * g1 * a1 * t1).natDegree ≤ 4 * d := by
    have hN : ((1866240 : K[X]) * g1).natDegree ≤ d :=
      natCast_mul_natDegree_le_610 1866240 hg1
    have hNa : ((1866240 : K[X]) * g1 * a1).natDegree ≤ 3 * d :=
      (natDegree_mul_le_add_610 hN ha1).trans (by omega)
    have h := natDegree_mul_le_add_610 hNa ht1
    simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega))
  have h4 : ((11520 : K[X]) * g1 * t1 ^ 2 * t2).natDegree ≤ 5 * d := by
    have h11520g : ((11520 : K[X]) * g1).natDegree ≤ d :=
      natCast_mul_natDegree_le_610 11520 hg1
    have h11520gt : ((11520 : K[X]) * g1 * t1 ^ 2).natDegree ≤ 3 * d :=
      (natDegree_mul_le_add_610 h11520g ht12).trans (by omega)
    have h := natDegree_mul_le_add_610 h11520gt ht2
    simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega))
  have h5 : ((622080 : K[X]) * a1 * t2).natDegree ≤ 4 * d := by
    have hN : ((622080 : K[X]) * a1).natDegree ≤ 2 * d :=
      natCast_mul_natDegree_le_610 622080 ha1
    have h := natDegree_mul_le_add_610 hN ht2
    simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega))
  have h6 : ((1280 : K[X]) * t1 * t2 ^ 2).natDegree ≤ 5 * d := by
    have h1280t : ((1280 : K[X]) * t1).natDegree ≤ d :=
      natCast_mul_natDegree_le_610 1280 ht1
    have h := natDegree_mul_le_add_610 h1280t ht22
    simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega))
  have hHbody : ((5598720 : K[X]) * a0 * t1 + (3840 : K[X]) * t1 ^ 4 -
        (3840 : K[X]) * t1 ^ 2 * u + (1280 : K[X]) * u ^ 2 +
        Polynomial.C κ * ((2239488 : K[X]) * a0 - (3072 : K[X]) * t1 ^ 3 +
          (3072 : K[X]) * t1 * u) -
        Polynomial.C κ₃ * ((384 : K[X]) * u) -
        Polynomial.C κ₅ * ((32 : K[X]) * t1)).natDegree ≤ 4 * d := by
    have ha : ((5598720 : K[X]) * a0 * t1).natDegree ≤ 2 * d := by
      have hN : ((5598720 : K[X]) * a0).natDegree ≤ d :=
        natCast_mul_natDegree_le_610 5598720 ha0
      have h := natDegree_mul_le_add_610 hN ht1
      simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega))
    have hb : ((3840 : K[X]) * t1 ^ 4).natDegree ≤ 4 * d :=
      natCast_mul_natDegree_le_610 3840 ht14
    have hc : ((3840 : K[X]) * t1 ^ 2 * u).natDegree ≤ 3 * d := by
      have h3840t : ((3840 : K[X]) * t1 ^ 2).natDegree ≤ 2 * d :=
        natCast_mul_natDegree_le_610 3840 ht12
      have h := natDegree_mul_le_add_610 h3840t hu
      simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega))
    have hd' : ((1280 : K[X]) * u ^ 2).natDegree ≤ 2 * d :=
      natCast_mul_natDegree_le_610 1280 hu2
    have he : (Polynomial.C κ * ((2239488 : K[X]) * a0)).natDegree ≤ d :=
      C_mul_natDegree_le_610 κ (natCast_mul_natDegree_le_610 2239488 ha0)
    have hf : (Polynomial.C κ * ((3072 : K[X]) * t1 ^ 3)).natDegree ≤ 3 * d :=
      C_mul_natDegree_le_610 κ (natCast_mul_natDegree_le_610 3072 ht13)
    have hg : (Polynomial.C κ * ((3072 : K[X]) * t1 * u)).natDegree ≤ 2 * d := by
      have h3072t : ((3072 : K[X]) * t1).natDegree ≤ d :=
        natCast_mul_natDegree_le_610 3072 ht1
      have h := natDegree_mul_le_add_610 h3072t hu
      exact C_mul_natDegree_le_610 κ (by simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega)))
    have hh : (Polynomial.C κ₃ * ((384 : K[X]) * u)).natDegree ≤ d :=
      C_mul_natDegree_le_610 κ₃ (natCast_mul_natDegree_le_610 384 hu)
    have hi : (Polynomial.C κ₅ * ((32 : K[X]) * t1)).natDegree ≤ d :=
      C_mul_natDegree_le_610 κ₅ (natCast_mul_natDegree_le_610 32 ht1)
    have hkbody : (Polynomial.C κ * ((2239488 : K[X]) * a0 -
          (3072 : K[X]) * t1 ^ 3 + (3072 : K[X]) * t1 * u)).natDegree ≤ 3 * d := by
      have hinner : ((2239488 : K[X]) * a0 - (3072 : K[X]) * t1 ^ 3 +
          (3072 : K[X]) * t1 * u).natDegree ≤ 3 * d := by
        refine natDegree_add_le_of_le_610 ?_ (by
          have h3072t : ((3072 : K[X]) * t1).natDegree ≤ d :=
            natCast_mul_natDegree_le_610 3072 ht1
          exact (natDegree_mul_le_add_610 h3072t hu).trans (by omega))
        exact natDegree_sub_le_of_le_610
          ((natCast_mul_natDegree_le_610 2239488 ha0).trans (by omega))
          ((natCast_mul_natDegree_le_610 3072 ht13).trans (by omega))
      exact C_mul_natDegree_le_610 κ hinner
    exact natDegree_sub_le_of_le_610
      (natDegree_sub_le_of_le_610
        (natDegree_add_le_of_le_610
          (natDegree_add_le_of_le_610
            (natDegree_sub_le_of_le_610
              (natDegree_add_le_of_le_610
                (natDegree_le_trans_610 (n := 4 * d) ha (by omega))
                (natDegree_le_trans_610 (n := 4 * d) hb (by omega)))
              (natDegree_le_trans_610 (n := 4 * d) hc (by omega)))
            (natDegree_le_trans_610 (n := 4 * d) hd' (by omega)))
          (natDegree_le_trans_610 (n := 4 * d) hkbody (by omega)))
        (natDegree_le_trans_610 (n := 4 * d) hh (by omega)))
      (natDegree_le_trans_610 (n := 4 * d) hi (by omega))
  have hHmul : (H * ((5598720 : K[X]) * a0 * t1 + (3840 : K[X]) * t1 ^ 4 -
        (3840 : K[X]) * t1 ^ 2 * u + (1280 : K[X]) * u ^ 2 +
        Polynomial.C κ * ((2239488 : K[X]) * a0 - (3072 : K[X]) * t1 ^ 3 +
          (3072 : K[X]) * t1 * u) -
        Polynomial.C κ₃ * ((384 : K[X]) * u) -
        Polynomial.C κ₅ * ((32 : K[X]) * t1))).natDegree ≤ 2 + 4 * d :=
    (natDegree_mul_le_add_610 hH hHbody).trans (by omega)
  -- Kappa polynomial in the `H`-free summand is degree `≤ 4 d`.
  have hkap : (Polynomial.C κ * ((4608 : K[X]) * g1 ^ 2 * t1 ^ 2 -
        (3072 : K[X]) * g1 * t1 * t2 + (512 : K[X]) * t2 ^ 2 +
        (746496 : K[X]) * g1 * a1)).natDegree ≤ 4 * d := by
    have hinner : ((4608 : K[X]) * g1 ^ 2 * t1 ^ 2 -
        (3072 : K[X]) * g1 * t1 * t2 + (512 : K[X]) * t2 ^ 2 +
        (746496 : K[X]) * g1 * a1).natDegree ≤ 4 * d := by
      have ha : ((4608 : K[X]) * g1 ^ 2 * t1 ^ 2).natDegree ≤ 4 * d := by
        have h4608g : ((4608 : K[X]) * g1 ^ 2).natDegree ≤ 2 * d :=
          natCast_mul_natDegree_le_610 4608 hg12
        have h := natDegree_mul_le_add_610 h4608g ht12
        simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega))
      have hb : ((3072 : K[X]) * g1 * t1 * t2).natDegree ≤ 4 * d := by
        have h3072g : ((3072 : K[X]) * g1).natDegree ≤ d :=
          natCast_mul_natDegree_le_610 3072 hg1
        have h3072gt : ((3072 : K[X]) * g1 * t1).natDegree ≤ 2 * d :=
          (natDegree_mul_le_add_610 h3072g ht1).trans (by omega)
        have h := natDegree_mul_le_add_610 h3072gt ht2
        simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega))
      have hc : ((512 : K[X]) * t2 ^ 2).natDegree ≤ 4 * d :=
        natCast_mul_natDegree_le_610 512 ht22
      have hd' : ((746496 : K[X]) * g1 * a1).natDegree ≤ 3 * d := by
        have hN : ((746496 : K[X]) * g1).natDegree ≤ d :=
          natCast_mul_natDegree_le_610 746496 hg1
        have h := natDegree_mul_le_add_610 hN ha1
        simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega))
      exact natDegree_add_le_of_le_610
        (natDegree_add_le_of_le_610
          (natDegree_sub_le_of_le_610
            (natDegree_le_trans_610 (n := 4 * d) ha (by omega))
            (natDegree_le_trans_610 (n := 4 * d) hb (by omega)))
          (natDegree_le_trans_610 (n := 4 * d) hc (by omega)))
        (natDegree_le_trans_610 (n := 4 * d) hd' (by omega))
    exact C_mul_natDegree_le_610 κ hinner
  have hk3 : (Polynomial.C κ₃ * ((1152 : K[X]) * g1 ^ 2 * t1 -
        (384 : K[X]) * g1 * t2)).natDegree ≤ 3 * d := by
    have hinner : ((1152 : K[X]) * g1 ^ 2 * t1 - (384 : K[X]) * g1 * t2).natDegree
        ≤ 3 * d := by
      have ha : ((1152 : K[X]) * g1 ^ 2 * t1).natDegree ≤ 3 * d := by
        have h1152g : ((1152 : K[X]) * g1 ^ 2).natDegree ≤ 2 * d :=
          natCast_mul_natDegree_le_610 1152 hg12
        have h := natDegree_mul_le_add_610 h1152g ht1
        simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega))
      have hb : ((384 : K[X]) * g1 * t2).natDegree ≤ 3 * d := by
        have h384g : ((384 : K[X]) * g1).natDegree ≤ d :=
          natCast_mul_natDegree_le_610 384 hg1
        have h := natDegree_mul_le_add_610 h384g ht2
        simpa [mul_assoc] using (natDegree_le_trans_610 h (by omega))
      exact natDegree_sub_le_of_le_610 ha hb
    exact C_mul_natDegree_le_610 κ₃ hinner
  have hk5 : (Polynomial.C κ₅ * ((16 : K[X]) * g1 ^ 2)).natDegree ≤ 2 * d :=
    C_mul_natDegree_le_610 κ₅ (natCast_mul_natDegree_le_610 16 hg12)
  simp only [alignedEighthNonsquareSolved610]
  -- `((… + k₃) - k₅) + H * body`
  refine natDegree_add_le_of_le_610 ?_
    (natDegree_le_trans_610 (n := 5 * d) hHmul (by omega))
  refine natDegree_sub_le_of_le_610 ?_ (natDegree_le_trans_610 hk5 (by omega))
  refine natDegree_add_le_of_le_610 ?_ (natDegree_le_trans_610 hk3 (by omega))
  refine natDegree_add_le_of_le_610 ?_ (natDegree_le_trans_610 hkap (by omega))
  refine natDegree_sub_le_of_le_610 ?_ (natDegree_le_trans_610 h6 (by omega))
  refine natDegree_add_le_of_le_610 ?_ (natDegree_le_trans_610 h5 (by omega))
  refine natDegree_add_le_of_le_610 ?_ (natDegree_le_trans_610 h4 (by omega))
  refine natDegree_sub_le_of_le_610 ?_ (natDegree_le_trans_610 h3 (by omega))
  exact natDegree_sub_le_of_le_610 (natDegree_le_trans_610 h1 (by omega)) (natDegree_le_trans_610 h2 (by omega))

/-! ## Degree-`1` Jacobian leading coefficient (`d ≥ 3`) -/

def alignedNonsquareJac1Poly610 (a0 a1 a2 b0 b1 b2 : K[X]) : K[X] :=
  a1.derivative * b1 + (2 : K[X]) * a0.derivative * b2 -
    (2 : K[X]) * a2 * b0.derivative - a1 * b1.derivative

theorem alignedFourteenthJacobianRow_eq_jac1Poly_610 (p q : K[X][Y]) :
    alignedFourteenthJacobianRow610 p q =
      alignedNonsquareJac1Poly610 (p.coeff 0) (p.coeff 1) (p.coeff 2)
        (q.coeff 0) (q.coeff 1) (q.coeff 2) := by
  have h2 : Polynomial.C (2 : K) = (2 : K[X]) :=
    (Polynomial.C_eq_natCast 2).symm
  simp only [alignedFourteenthJacobianRow610, alignedNonsquareJac1Poly610, h2]
  ring

theorem alignedNonsquare_a2_coeff_threeMul_610 {a2 g1 t1 t2 u t3 H : K[X]}
    {d : ℕ} (hd : 3 ≤ d) (hH : H.natDegree ≤ 2)
    (hg1 : g1.natDegree ≤ d) (ht1 : t1.natDegree ≤ d)
    (hu : u.natDegree ≤ d) (ht3 : t3.natDegree ≤ d)
    (hjet : (81 : K[X]) * a2 + (3 : K[X]) * g1 ^ 2 * t1 - g1 * t2 = H * u)
    (ht2id : t2 - (6 : K[X]) * g1 * t1 = H * t3) :
    (81 : K) * a2.coeff (3 * d) =
      (3 : K) * (g1.coeff d) ^ 2 * t1.coeff d := by
  have ha2 := alignedNonsquare_a2_from_jet_610 hjet ht2id
  have hg12 : (g1 ^ 2).natDegree ≤ 2 * d := natDegree_pow_le_mul_610 hg1
  have hg12c : (g1 ^ 2).coeff (2 * d) = (g1.coeff d) ^ 2 :=
    coeff_pow_of_natDegree_le_610 (n := 2) hg1
  have ht1g12 : (g1 ^ 2 * t1).natDegree ≤ 3 * d :=
    (natDegree_mul_le_add_610 hg12 ht1).trans (by omega)
  have ht1g12c : (g1 ^ 2 * t1).coeff (3 * d) =
      (g1.coeff d) ^ 2 * t1.coeff d := by
    have h := coeff_mul_of_natDegree_le_610 hg12 ht1
    have hsum : 2 * d + d = 3 * d := by omega
    simpa [hsum, hg12c] using h
  have h3c : ((3 : K[X]) * g1 ^ 2 * t1).coeff (3 * d) =
      (3 : K) * (g1.coeff d) ^ 2 * t1.coeff d := by
    have h3m : ((3 : K[X]) * (g1 ^ 2 * t1)).natDegree ≤ 3 * d :=
      natCast_mul_natDegree_le_610 3 ht1g12
    have h := coeff_mul_of_natDegree_le_610
      (p := (3 : K[X])) (q := g1 ^ 2 * t1) (m := 0) (n := 3 * d)
      (by
        have : (3 : K[X]) = Polynomial.C (3 : K) :=
          (Polynomial.C_eq_natCast 3).symm
        simp [this]) ht1g12
    have h0 : ((3 : K[X]).coeff 0) = (3 : K) := by
      have : (3 : K[X]) = Polynomial.C (3 : K) :=
        (Polynomial.C_eq_natCast 3).symm
      simp [this]
    have hassoc : (3 : K[X]) * g1 ^ 2 * t1 = (3 : K[X]) * (g1 ^ 2 * t1) := by
      ring
    simpa [hassoc, h0, ht1g12c, mul_assoc] using h
  have hgt3 : (g1 * t3).natDegree ≤ 2 * d := by
    exact add_add_le_two_mul_610 <| natDegree_mul_le_add_610 hg1 ht3
  have hsum : (u + g1 * t3).natDegree ≤ 2 * d :=
    natDegree_add_le_of_le_610 (natDegree_le_trans_610 hu (by omega)) hgt3
  have hHsum : (H * (u + g1 * t3)).natDegree ≤ 2 + 2 * d :=
    (natDegree_mul_le_add_610 hH hsum).trans (by omega)
  have hH0 : (H * (u + g1 * t3)).coeff (3 * d) = 0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hHsum (by omega))
  have hleft : ((81 : K[X]) * a2).coeff (3 * d) = (81 : K) * a2.coeff (3 * d) :=
    coeff_natCast_mul_610 81 a2 (3 * d)
  have hright :
      ((3 : K[X]) * g1 ^ 2 * t1 + H * (u + g1 * t3)).coeff (3 * d) =
        (3 : K) * (g1.coeff d) ^ 2 * t1.coeff d := by
    simp [Polynomial.coeff_add, h3c, hH0]
  have := congrArg (fun p : K[X] => p.coeff (3 * d)) ha2
  simpa [hleft, hright] using this

set_option maxHeartbeats 16000000 in
theorem alignedNonsquare_jac1_coeff_eqDegree_610
    {H g1 t1 t2 u t3 v a0 a1 a2 b0 b1 b2 : K[X]}
    {κ κ₃ κ₅ κ₇ κ₉ : K} {d : ℕ}
    (hd : 3 ≤ d) (hH : H.natDegree ≤ 2)
    (hg1 : g1.natDegree ≤ d) (ht1 : t1.natDegree ≤ d)
    (hu : u.natDegree ≤ d) (ht3 : t3.natDegree ≤ d)
    (hv : v.natDegree ≤ d) (ha0 : a0.natDegree ≤ d)
    (ht2id : t2 - (6 : K[X]) * g1 * t1 = H * t3)
    (hv1 : (243 : K[X]) * a1 - g1 * u = H * v)
    (hu2 : (81 : K[X]) * a2 + (3 : K[X]) * g1 ^ 2 * t1 - g1 * t2 = H * u)
    (hq0 : (9795520512 : K[X]) * b0 =
      alignedTenthNonsquareSolved610 H g1 t1 u t3 v a0 κ κ₃ κ₅ κ₇ -
        Polynomial.C κ₉)
    (hq1 : (1632586752 : K[X]) * b1 =
      alignedNinthNonsquareSolved610 H g1 t1 t2 u t3 a0 a1 κ κ₃ κ₅ κ₇)
    (hq2 : (15116544 : K[X]) * b2 =
      alignedEighthNonsquareSolved610 H g1 t1 t2 u a0 a1 κ κ₃ κ₅ -
        Polynomial.C κ₇ * H) :
    (4782969 : K) *
        (alignedNonsquareJac1Poly610 a0 a1 a2 b0 b1 b2).coeff (8 * d - 1) =
      (70 : K) * (d : K) * (g1.coeff d) ^ 2 * (t1.coeff d) ^ 6 := by
  have hd2 : 2 ≤ d := le_trans (by decide : 2 ≤ 3) hd
  have h5d : 1 ≤ 5 * d := by omega
  have ha1deg := alignedNonsquare_a1_natDegree_le_610 hd2 hH hg1 hu hv hv1
  have ha2deg :=
    alignedNonsquare_a2_natDegree_le_610 hd2 hH hg1 ht1 hu ht3 hu2 ht2id
  have ht2deg :=
    alignedNonsquare_t2_natDegree_le_610 hd2 hH hg1 ht1 ht3 ht2id
  have hTdeg :=
    alignedTenthNonsquareSolved_natDegree_le_fiveMul_610 H g1 t1 u t3 v a0
      κ κ₃ κ₅ κ₇ hd hH hg1 ht1 hu ht3 hv ha0
  have hNdeg :=
    alignedNinthNonsquareSolved_natDegree_le_fiveMul_610 H g1 t1 t2 u t3 a0
      a1 κ κ₃ κ₅ κ₇ hd hH hg1 ht1 ht2deg hu ht3 ha0 ha1deg
  have hEdeg :=
    alignedEighthNonsquareSolved_natDegree_le_fiveMul_610 H g1 t1 t2 u a0 a1
      κ κ₃ κ₅ hd hH hg1 ht1 ht2deg hu ha0 ha1deg
  have hc0 : (9795520512 : K) ≠ 0 := by norm_num
  have hc1 : (1632586752 : K) ≠ 0 := by norm_num
  have hc2 : (15116544 : K) ≠ 0 := by norm_num
  have hC0 : (9795520512 : K[X]) = Polynomial.C (9795520512 : K) :=
    (Polynomial.C_eq_natCast 9795520512).symm
  have hC1 : (1632586752 : K[X]) = Polynomial.C (1632586752 : K) :=
    (Polynomial.C_eq_natCast 1632586752).symm
  have hC2 : (15116544 : K[X]) = Polynomial.C (15116544 : K) :=
    (Polynomial.C_eq_natCast 15116544).symm
  have hb0deg : b0.natDegree ≤ 5 * d := by
    have hTκ :
        (alignedTenthNonsquareSolved610 H g1 t1 u t3 v a0 κ κ₃ κ₅ κ₇ -
            Polynomial.C κ₉).natDegree ≤ 5 * d :=
      natDegree_sub_le_of_le_610 hTdeg (by simp)
    have hmul : ((9795520512 : K[X]) * b0).natDegree ≤ 5 * d := by
      simpa [hq0] using hTκ
    have : (Polynomial.C (9795520512 : K) * b0).natDegree ≤ 5 * d := by
      simpa [hC0] using hmul
    exact natDegree_le_of_C_mul_le_610 hc0 this
  have hb1deg : b1.natDegree ≤ 5 * d := by
    have hmul : ((1632586752 : K[X]) * b1).natDegree ≤ 5 * d := by
      simpa [hq1] using hNdeg
    have : (Polynomial.C (1632586752 : K) * b1).natDegree ≤ 5 * d := by
      simpa [hC1] using hmul
    exact natDegree_le_of_C_mul_le_610 hc1 this
  have hb2deg : b2.natDegree ≤ 5 * d := by
    have hEκ : (alignedEighthNonsquareSolved610 H g1 t1 t2 u a0 a1 κ κ₃ κ₅ -
        Polynomial.C κ₇ * H).natDegree ≤ 5 * d :=
      natDegree_sub_le_of_le_610 hEdeg
        ((C_mul_natDegree_le_610 κ₇ hH).trans (by omega))
    have hmul : ((15116544 : K[X]) * b2).natDegree ≤ 5 * d := by
      simpa [hq2] using hEκ
    have : (Polynomial.C (15116544 : K) * b2).natDegree ≤ 5 * d := by
      simpa [hC2] using hmul
    exact natDegree_le_of_C_mul_le_610 hc2 this
  have hb0'deg : b0.derivative.natDegree ≤ 5 * d - 1 :=
    (Polynomial.natDegree_derivative_le b0).trans (by omega)
  have hb1'deg : b1.derivative.natDegree ≤ 5 * d :=
    natDegree_derivative_le_of_le_610 hb1deg
  have ha1'deg : a1.derivative.natDegree ≤ 2 * d :=
    natDegree_derivative_le_of_le_610 ha1deg
  have ha0'deg : a0.derivative.natDegree ≤ d :=
    natDegree_derivative_le_of_le_610 ha0
  have hterm1 : (a1.derivative * b1).natDegree < 8 * d - 1 :=
    lt_of_le_of_lt (natDegree_mul_le_add_610 ha1'deg hb1deg) (by omega)
  have hterm2 :
      ((2 : K[X]) * a0.derivative * b2).natDegree < 8 * d - 1 := by
    have h2a0 : ((2 : K[X]) * a0.derivative).natDegree ≤ d :=
      natCast_mul_natDegree_le_610 2 ha0'deg
    exact lt_of_le_of_lt (natDegree_mul_le_add_610 h2a0 hb2deg) (by omega)
  have hterm4 : (a1 * b1.derivative).natDegree < 8 * d - 1 :=
    lt_of_le_of_lt (natDegree_mul_le_add_610 ha1deg hb1'deg) (by omega)
  have h1c : (a1.derivative * b1).coeff (8 * d - 1) = 0 :=
    coeff_eq_zero_of_natDegree_lt hterm1
  have h2c : ((2 : K[X]) * a0.derivative * b2).coeff (8 * d - 1) = 0 :=
    coeff_eq_zero_of_natDegree_lt hterm2
  have h4c : (a1 * b1.derivative).coeff (8 * d - 1) = 0 :=
    coeff_eq_zero_of_natDegree_lt hterm4
  have ha2c :=
    alignedNonsquare_a2_coeff_threeMul_610 hd hH hg1 ht1 hu ht3 hu2 ht2id
  have hTcoeff :=
    alignedTenthNonsquareSolved_coeff_fiveMul_610 H g1 t1 u t3 v a0 κ κ₃ κ₅
      κ₇ hd hH hg1 ht1 hu ht3 hv ha0
  have hb0c : (9795520512 : K) * b0.coeff (5 * d) =
      (-387072 : K) * (t1.coeff d) ^ 5 := by
    have hκ9 : (Polynomial.C κ₉).coeff (5 * d) = 0 := by
      simp [Polynomial.coeff_C, show 5 * d ≠ 0 by omega]
    have h := congrArg (fun p : K[X] => p.coeff (5 * d)) hq0
    simpa [coeff_natCast_mul_610, Polynomial.coeff_sub, hκ9, hTcoeff] using h
  have hb0'c : b0.derivative.coeff (5 * d - 1) =
      b0.coeff (5 * d) * (5 * d : K) := by
    simpa [Nat.cast_mul] using coeff_derivative_pred_610 b0 h5d
  have hprod :
      (a2 * b0.derivative).coeff (8 * d - 1) =
        a2.coeff (3 * d) * b0.derivative.coeff (5 * d - 1) := by
    have hsum : 3 * d + (5 * d - 1) = 8 * d - 1 := by omega
    have h := coeff_mul_of_natDegree_le_610 ha2deg hb0'deg
    simpa [hsum] using h
  have hterm3c :
      ((2 : K[X]) * a2 * b0.derivative).coeff (8 * d - 1) =
        (2 : K) * (a2 * b0.derivative).coeff (8 * d - 1) := by
    have hassoc : (2 : K[X]) * a2 * b0.derivative =
        (2 : K[X]) * (a2 * b0.derivative) := by
      ring
    rw [hassoc]
    exact coeff_natCast_mul_610 2 (a2 * b0.derivative) (8 * d - 1)
  have hjac :
      (alignedNonsquareJac1Poly610 a0 a1 a2 b0 b1 b2).coeff (8 * d - 1) =
        -((2 : K) * (a2 * b0.derivative).coeff (8 * d - 1)) := by
    simp only [alignedNonsquareJac1Poly610, Polynomial.coeff_add,
      Polynomial.coeff_sub, Polynomial.coeff_neg, h1c, h2c, h4c]
    rw [hterm3c]
    ring
  -- `81 · 9795520512 · jac1[8d-1] = 11612160 · d · G₁² T₁⁶`.
  have hclear :
      (81 : K) * (9795520512 : K) *
          (alignedNonsquareJac1Poly610 a0 a1 a2 b0 b1 b2).coeff (8 * d - 1) =
        (11612160 : K) * (d : K) *
          (g1.coeff d) ^ 2 * (t1.coeff d) ^ 6 := by
    have h5dK : (5 * d : K) = (5 : K) * (d : K) := by simp
    calc
      (81 : K) * (9795520512 : K) *
            (alignedNonsquareJac1Poly610 a0 a1 a2 b0 b1 b2).coeff (8 * d - 1)
          = (81 : K) * (9795520512 : K) *
              (-((2 : K) * (a2.coeff (3 * d) *
                (b0.coeff (5 * d) * (5 * d : K))))) := by
            rw [hjac, hprod, hb0'c]
      _ = -((2 : K) * ((81 : K) * a2.coeff (3 * d)) *
              ((9795520512 : K) * b0.coeff (5 * d)) * (5 * d : K)) := by
            ring
      _ = -((2 : K) * ((3 : K) * (g1.coeff d) ^ 2 * t1.coeff d) *
              ((-387072 : K) * (t1.coeff d) ^ 5) * (5 * d : K)) := by
            rw [ha2c, hb0c]
      _ = (11612160 : K) * (d : K) *
            (g1.coeff d) ^ 2 * (t1.coeff d) ^ 6 := by
            rw [h5dK]
            ring
  have hconst : (4782969 : K) * (11612160 : K) =
      (70 : K) * (81 : K) * (9795520512 : K) := by
    norm_num
  have h81 : (81 : K) ≠ 0 := by norm_num
  have hfac : (81 : K) * (9795520512 : K) ≠ 0 := mul_ne_zero h81 hc0
  have hmul := congrArg (fun x : K => (4782969 : K) * x) hclear
  have hleft : (4782969 : K) * ((81 : K) * (9795520512 : K)) *
        (alignedNonsquareJac1Poly610 a0 a1 a2 b0 b1 b2).coeff (8 * d - 1) =
      ((81 : K) * (9795520512 : K)) * ((4782969 : K) *
        (alignedNonsquareJac1Poly610 a0 a1 a2 b0 b1 b2).coeff (8 * d - 1)) := by
    ring
  have hscaled :=
    congrArg (fun n : K => n * ((d : K) * (g1.coeff d) ^ 2 * (t1.coeff d) ^ 6))
      hconst
  have hright : (4782969 : K) * ((11612160 : K) * (d : K) *
        (g1.coeff d) ^ 2 * (t1.coeff d) ^ 6) =
      ((81 : K) * (9795520512 : K)) * ((70 : K) * (d : K) *
        (g1.coeff d) ^ 2 * (t1.coeff d) ^ 6) := by
    convert hscaled using 1 <;> ring
  have hboth : ((81 : K) * (9795520512 : K)) * ((4782969 : K) *
        (alignedNonsquareJac1Poly610 a0 a1 a2 b0 b1 b2).coeff (8 * d - 1)) =
      ((81 : K) * (9795520512 : K)) * ((70 : K) * (d : K) *
        (g1.coeff d) ^ 2 * (t1.coeff d) ^ 6) := by
    convert hmul using 1
    · ring
    · exact hright.symm
  exact mul_left_cancel₀ hfac hboth

theorem alignedNonsquare_eqDegree_bothHigh_false_610
    {H g1 t1 t2 u t3 v a0 a1 a2 b0 b1 b2 : K[X]}
    {κ κ₃ κ₅ κ₇ κ₉ : K} {d : ℕ}
    (hd : 3 ≤ d) (hH : H.natDegree ≤ 2) (hHne : H ≠ 0)
    (hg1 : g1.natDegree = d) (ht1 : t1.natDegree = d)
    (hu : u.natDegree ≤ d) (ht3 : t3.natDegree ≤ d)
    (hv : v.natDegree ≤ d) (ha0 : a0.natDegree ≤ d)
    (ht2id : t2 - (6 : K[X]) * g1 * t1 = H * t3)
    (hv1 : (243 : K[X]) * a1 - g1 * u = H * v)
    (hu2 : (81 : K[X]) * a2 + (3 : K[X]) * g1 ^ 2 * t1 - g1 * t2 = H * u)
    (hq0 : (9795520512 : K[X]) * b0 =
      alignedTenthNonsquareSolved610 H g1 t1 u t3 v a0 κ κ₃ κ₅ κ₇ -
        Polynomial.C κ₉)
    (hq1 : (1632586752 : K[X]) * b1 =
      alignedNinthNonsquareSolved610 H g1 t1 t2 u t3 a0 a1 κ κ₃ κ₅ κ₇)
    (hq2 : (15116544 : K[X]) * b2 =
      alignedEighthNonsquareSolved610 H g1 t1 t2 u a0 a1 κ κ₃ κ₅ -
        Polynomial.C κ₇ * H)
    (hjac : alignedNonsquareJac1Poly610 a0 a1 a2 b0 b1 b2 = 0) : False := by
  have hcoeff := alignedNonsquare_jac1_coeff_eqDegree_610 hd hH hg1.le
    ht1.le hu ht3 hv ha0 ht2id hv1 hu2 hq0 hq1 hq2
  have h0 : (alignedNonsquareJac1Poly610 a0 a1 a2 b0 b1 b2).coeff
      (8 * d - 1) = 0 := by simp [hjac]
  have hG : g1.coeff d ≠ 0 := by
    rw [← hg1, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr (fun hg => by
      simp [hg, natDegree_zero] at hg1
      omega)
  have hT : t1.coeff d ≠ 0 := by
    rw [← ht1, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr (fun ht => by
      simp [ht, natDegree_zero] at ht1
      omega)
  have h70 : (70 : K) ≠ 0 := by norm_num
  have hdK : (d : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h478 : (4782969 : K) ≠ 0 := by norm_num
  have htop : (70 : K) * (d : K) * (g1.coeff d) ^ 2 * (t1.coeff d) ^ 6 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero h70 hdK) (pow_ne_zero 2 hG))
      (pow_ne_zero 6 hT)
  have : (4782969 : K) * 0 = (70 : K) * (d : K) * (g1.coeff d) ^ 2 *
      (t1.coeff d) ^ 6 := by
    simpa [h0] using hcoeff
  exact htop (by simpa using this.symm)

/-! ## Linear leftover Keller leading coefficients -/

theorem alignedNonsquare_a1_coeff_three_of_linear_610
    {a1 g1 u H v : K[X]}
    (hH : H.natDegree ≤ 2) (hg1 : g1.natDegree ≤ 1)
    (hu : u.natDegree ≤ 1) (hv : v.natDegree ≤ 1)
    (hid : (243 : K[X]) * a1 - g1 * u = H * v) :
    (243 : K) * a1.coeff 3 = H.coeff 2 * v.coeff 1 := by
  have ha1 := alignedNonsquare_a1_eq_610 hid
  have hgu : (g1 * u).natDegree ≤ 2 := (natDegree_mul_le_add_610 hg1 hu).trans (by omega)
  have hgu0 : (g1 * u).coeff 3 = 0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hgu (by decide))
  have hHv : (H * v).coeff 3 = H.coeff 2 * v.coeff 1 :=
    coeff_mul_of_natDegree_le_610 hH hv
  have h := congrArg (fun p : K[X] => p.coeff 3) ha1
  simpa [coeff_natCast_mul_610, Polynomial.coeff_add, hgu0, hHv] using h

set_option maxHeartbeats 16000000 in
theorem alignedTenthNonsquareHCoef_natDegree_le_two_of_linear_t3const_610
    (g1 t1 u t3 v : K[X]) (κ : K)
    (hg1 : g1.natDegree ≤ 1) (ht1 : t1.natDegree ≤ 1)
    (hu : u.natDegree ≤ 1) (ht3 : t3.natDegree ≤ 0)
    (hv : v.natDegree ≤ 1) :
    (alignedTenthNonsquareHCoef610 g1 t1 u t3 v κ).natDegree ≤ 2 := by
  simp only [alignedTenthNonsquareHCoef610]
  compute_degree
  omega

set_option maxHeartbeats 16000000 in
theorem alignedTenthNonsquareHFree_natDegree_le_five_of_linear_610
    (g1 t1 u a0 : K[X]) (κ κ₃ κ₅ κ₇ : K)
    (ht1 : t1.natDegree ≤ 1) (hu : u.natDegree ≤ 1)
    (ha0 : a0.natDegree ≤ 1) :
    (alignedTenthNonsquareHFree610 g1 t1 u a0 κ κ₃ κ₅ κ₇).natDegree ≤ 5 := by
  simp only [alignedTenthNonsquareHFree610]
  compute_degree
  omega

set_option maxHeartbeats 16000000 in
theorem alignedTenthNonsquareHFree_rest_natDegree_le_four_of_linear_610
    (g1 t1 u a0 : K[X]) (κ κ₃ κ₅ κ₇ : K)
    (ht1 : t1.natDegree ≤ 1) (hu : u.natDegree ≤ 1)
    (ha0 : a0.natDegree ≤ 1) :
    (alignedTenthNonsquareHFree610 g1 t1 u a0 κ κ₃ κ₅ κ₇ +
        (387072 : K[X]) * t1 ^ 5).natDegree ≤ 4 := by
  have hrest :
      alignedTenthNonsquareHFree610 g1 t1 u a0 κ κ₃ κ₅ κ₇ +
          (387072 : K[X]) * t1 ^ 5 =
        (368640 : K[X]) * t1 ^ 3 * u -
          (201553920 : K[X]) * t1 ^ 2 * a0 -
          (92160 : K[X]) * t1 * u ^ 2 +
          (134369280 : K[X]) * u * a0 -
          Polynomial.C κ₇ * ((72 : K[X]) * t1) +
          Polynomial.C κ₅ * ((1152 : K[X]) * t1 ^ 2) -
          Polynomial.C κ₅ * ((768 : K[X]) * u) -
          Polynomial.C κ₃ * ((20155392 : K[X]) * a0) +
          Polynomial.C κ * ((276480 : K[X]) * t1 ^ 4) -
          Polynomial.C κ * ((221184 : K[X]) * t1 ^ 2 * u) +
          Polynomial.C κ * ((161243136 : K[X]) * t1 * a0) +
          Polynomial.C κ * ((36864 : K[X]) * u ^ 2) := by
    simp only [alignedTenthNonsquareHFree610]
    ring
  rw [hrest]
  compute_degree
  omega

theorem alignedTenthNonsquareSolved_natDegree_le_five_of_linear_t3const_610
    (H g1 t1 u t3 v a0 : K[X]) (κ κ₃ κ₅ κ₇ : K)
    (hH : H.natDegree ≤ 2) (hg1 : g1.natDegree ≤ 1)
    (ht1 : t1.natDegree ≤ 1) (hu : u.natDegree ≤ 1)
    (ht3 : t3.natDegree ≤ 0) (hv : v.natDegree ≤ 1)
    (ha0 : a0.natDegree ≤ 1) :
    (alignedTenthNonsquareSolved610 H g1 t1 u t3 v a0 κ κ₃ κ₅ κ₇).natDegree
      ≤ 5 := by
  rw [alignedTenthNonsquareSolved_split_610]
  have hfree :=
    alignedTenthNonsquareHFree_natDegree_le_five_of_linear_610 g1 t1 u a0
      κ κ₃ κ₅ κ₇ ht1 hu ha0
  have hcoef :=
    alignedTenthNonsquareHCoef_natDegree_le_two_of_linear_t3const_610 g1 t1
      u t3 v κ hg1 ht1 hu ht3 hv
  have hHmul :
      (H * alignedTenthNonsquareHCoef610 g1 t1 u t3 v κ).natDegree ≤ 4 :=
    (natDegree_mul_le_add_610 hH hcoef).trans (by omega)
  exact natDegree_add_le_of_le_610 hfree (hHmul.trans (by decide))

set_option maxHeartbeats 16000000 in
theorem alignedTenthNonsquareSolved_coeff_five_of_linear_t3const_610
    (H g1 t1 u t3 v a0 : K[X]) (κ κ₃ κ₅ κ₇ : K)
    (hH : H.natDegree ≤ 2) (hg1 : g1.natDegree ≤ 1)
    (ht1 : t1.natDegree ≤ 1) (hu : u.natDegree ≤ 1)
    (ht3 : t3.natDegree ≤ 0) (hv : v.natDegree ≤ 1)
    (ha0 : a0.natDegree ≤ 1) :
    (alignedTenthNonsquareSolved610 H g1 t1 u t3 v a0 κ κ₃ κ₅ κ₇).coeff 5 =
      (-387072 : K) * (t1.coeff 1) ^ 5 := by
  have ht15 : (t1 ^ 5).natDegree ≤ 5 := natDegree_pow_le_mul_610 ht1
  have htop : ((387072 : K[X]) * t1 ^ 5).coeff 5 =
      (387072 : K) * (t1.coeff 1) ^ 5 := by
    have hpow : (t1 ^ 5).coeff 5 = (t1.coeff 1) ^ 5 :=
      coeff_pow_of_natDegree_le_610 (n := 5) ht1
    have h := coeff_mul_of_natDegree_le_610
      (p := (387072 : K[X])) (q := t1 ^ 5) (m := 0) (n := 5)
      (by
        have : (387072 : K[X]) = Polynomial.C (387072 : K) :=
          (Polynomial.C_eq_natCast 387072).symm
        simp [this]) ht15
    have h0 : ((387072 : K[X]).coeff 0) = (387072 : K) := by
      have : (387072 : K[X]) = Polynomial.C (387072 : K) :=
        (Polynomial.C_eq_natCast 387072).symm
      simp [this]
    simpa [h0, hpow] using h
  have hrest : (alignedTenthNonsquareSolved610 H g1 t1 u t3 v a0 κ κ₃ κ₅ κ₇ +
      (387072 : K[X]) * t1 ^ 5).natDegree ≤ 4 := by
    rw [alignedTenthNonsquareSolved_split_610]
    have hfree_rest :=
      alignedTenthNonsquareHFree_rest_natDegree_le_four_of_linear_610 g1 t1
        u a0 κ κ₃ κ₅ κ₇ ht1 hu ha0
    have hcoef :=
      alignedTenthNonsquareHCoef_natDegree_le_two_of_linear_t3const_610 g1
        t1 u t3 v κ hg1 ht1 hu ht3 hv
    have hHmul :
        (H * alignedTenthNonsquareHCoef610 g1 t1 u t3 v κ).natDegree ≤ 4 :=
      (natDegree_mul_le_add_610 hH hcoef).trans (by omega)
    have hassoc :
        alignedTenthNonsquareHFree610 g1 t1 u a0 κ κ₃ κ₅ κ₇ +
            H * alignedTenthNonsquareHCoef610 g1 t1 u t3 v κ +
            (387072 : K[X]) * t1 ^ 5 =
          (alignedTenthNonsquareHFree610 g1 t1 u a0 κ κ₃ κ₅ κ₇ +
              (387072 : K[X]) * t1 ^ 5) +
            H * alignedTenthNonsquareHCoef610 g1 t1 u t3 v κ := by
      ring
    rw [hassoc]
    exact natDegree_add_le_of_le_610 hfree_rest hHmul
  have hrest0 :
      (alignedTenthNonsquareSolved610 H g1 t1 u t3 v a0 κ κ₃ κ₅ κ₇ +
          (387072 : K[X]) * t1 ^ 5).coeff 5 = 0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hrest (by decide))
  have hdecomp :
      alignedTenthNonsquareSolved610 H g1 t1 u t3 v a0 κ κ₃ κ₅ κ₇ =
        (alignedTenthNonsquareSolved610 H g1 t1 u t3 v a0 κ κ₃ κ₅ κ₇ +
            (387072 : K[X]) * t1 ^ 5) +
          -((387072 : K[X]) * t1 ^ 5) := by
    ring
  rw [hdecomp, Polynomial.coeff_add, Polynomial.coeff_neg, hrest0, zero_add,
    htop]
  ring

set_option maxHeartbeats 16000000 in
theorem alignedNonsquare_linear_t31_zero_keller_coeff_seven_610
    {H g1 t1 t2 u t3 v a0 a1 b0 b1 : K[X]} {κ κ₃ κ₅ κ₇ κ₉ : K}
    (hH : H.natDegree = 2)
    (hg1 : g1.natDegree ≤ 1) (ht1 : t1.natDegree ≤ 1)
    (ht2 : t2.natDegree ≤ 2) (hu : u.natDegree ≤ 1)
    (ht3 : t3.natDegree ≤ 0) (hv : v.natDegree ≤ 1)
    (ha0 : a0.natDegree ≤ 1)
    (hv1 : (243 : K[X]) * a1 - g1 * u = H * v)
    (hq0 : (9795520512 : K[X]) * b0 =
      alignedTenthNonsquareSolved610 H g1 t1 u t3 v a0 κ κ₃ κ₅ κ₇ -
        Polynomial.C κ₉)
    (hq1 : (1632586752 : K[X]) * b1 =
      alignedNinthNonsquareSolved610 H g1 t1 t2 u t3 a0 a1 κ κ₃ κ₅ κ₇) :
    (43046721 : K) *
        (a0.derivative * b1 - a1 * b0.derivative).coeff 7 =
      (35 : K) * H.coeff 2 * (t1.coeff 1) ^ 5 * v.coeff 1 := by
  have hHle : H.natDegree ≤ 2 := hH.le
  have ha1deg : a1.natDegree ≤ 3 := by
    have hgu : (g1 * u).natDegree ≤ 2 := (natDegree_mul_le_add_610 hg1 hu).trans (by omega)
    have hHv : (H * v).natDegree ≤ 3 := (natDegree_mul_le_add_610 hHle hv).trans (by omega)
    have hr : (g1 * u + H * v).natDegree ≤ 3 :=
      natDegree_add_le_of_le_610 (hgu.trans (by decide)) hHv
    have ha1eq := alignedNonsquare_a1_eq_610 hv1
    have h243 : (243 : K) ≠ 0 := by norm_num
    have hC : (243 : K[X]) = Polynomial.C (243 : K) :=
      (Polynomial.C_eq_natCast 243).symm
    have : (Polynomial.C (243 : K) * a1).natDegree ≤ 3 := by
      rw [← hC, ha1eq]
      exact hr
    exact natDegree_le_of_C_mul_le_610 h243 this
  have hH2 : (H ^ 2).natDegree ≤ 4 :=
    natDegree_pow_le_mul_610 (n := 2) hHle
  have hNdeg : (alignedNinthNonsquareSolved610 H g1 t1 t2 u t3 a0 a1
      κ κ₃ κ₅ κ₇).natDegree ≤ 5 := by
    simp only [alignedNinthNonsquareSolved610]
    compute_degree
    omega
  have hc1 : (1632586752 : K) ≠ 0 := by norm_num
  have hC1 : (1632586752 : K[X]) = Polynomial.C (1632586752 : K) :=
    (Polynomial.C_eq_natCast 1632586752).symm
  have hb1deg : b1.natDegree ≤ 5 := by
    have hmul : ((1632586752 : K[X]) * b1).natDegree ≤ 5 := by
      simpa [hq1] using hNdeg
    have : (Polynomial.C (1632586752 : K) * b1).natDegree ≤ 5 := by
      simpa [hC1] using hmul
    exact natDegree_le_of_C_mul_le_610 hc1 this
  have ha0'deg : a0.derivative.natDegree ≤ 1 :=
    natDegree_derivative_le_of_le_610 ha0
  have hterm1 : (a0.derivative * b1).natDegree ≤ 6 :=
    (natDegree_mul_le_add_610 ha0'deg hb1deg).trans (by omega)
  have h1c : (a0.derivative * b1).coeff 7 = 0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hterm1 (by decide))
  have hc0 : (9795520512 : K) ≠ 0 := by norm_num
  have hT5 := alignedTenthNonsquareSolved_coeff_five_of_linear_t3const_610
    H g1 t1 u t3 v a0 κ κ₃ κ₅ κ₇ hHle hg1 ht1 hu ht3 hv ha0
  have hb0c : (9795520512 : K) * b0.coeff 5 =
      (-387072 : K) * (t1.coeff 1) ^ 5 := by
    have hκ9 : (Polynomial.C κ₉).coeff 5 = 0 := by simp [Polynomial.coeff_C]
    have h := congrArg (fun p : K[X] => p.coeff 5) hq0
    simpa [coeff_natCast_mul_610, Polynomial.coeff_sub, hκ9, hT5] using h
  have hb0'c : b0.derivative.coeff 4 = b0.coeff 5 * (5 : K) :=
    coeff_derivative_pred_610 b0 (by decide : 1 ≤ 5)
  have ha1c := alignedNonsquare_a1_coeff_three_of_linear_610 hHle hg1 hu hv hv1
  have hb0'deg : b0.derivative.natDegree ≤ 4 := by
    have hTκ :
        (alignedTenthNonsquareSolved610 H g1 t1 u t3 v a0 κ κ₃ κ₅ κ₇ -
            Polynomial.C κ₉).natDegree ≤ 5 := by
      have hT : (alignedTenthNonsquareSolved610 H g1 t1 u t3 v a0 κ κ₃ κ₅
          κ₇).natDegree ≤ 5 :=
        alignedTenthNonsquareSolved_natDegree_le_five_of_linear_t3const_610
          H g1 t1 u t3 v a0 κ κ₃ κ₅ κ₇ hHle hg1 ht1 hu ht3 hv ha0
      exact natDegree_sub_le_of_le_610 hT (by simp)
    have hC0 : (9795520512 : K[X]) = Polynomial.C (9795520512 : K) :=
      (Polynomial.C_eq_natCast 9795520512).symm
    have hmul : ((9795520512 : K[X]) * b0).natDegree ≤ 5 := by
      simpa [hq0] using hTκ
    have hb0deg : b0.natDegree ≤ 5 := by
      have : (Polynomial.C (9795520512 : K) * b0).natDegree ≤ 5 := by
        simpa [hC0] using hmul
      exact natDegree_le_of_C_mul_le_610 hc0 this
    exact (Polynomial.natDegree_derivative_le b0).trans (by omega)
  have hprod : (a1 * b0.derivative).coeff 7 =
      a1.coeff 3 * b0.derivative.coeff 4 :=
    coeff_mul_of_natDegree_le_610 ha1deg hb0'deg
  have hkel : (a0.derivative * b1 - a1 * b0.derivative).coeff 7 =
      -(a1.coeff 3 * (b0.coeff 5 * (5 : K))) := by
    simp [Polynomial.coeff_sub, h1c, hprod, hb0'c]
  have h243 : (243 : K) ≠ 0 := by norm_num
  have hconst : (43046721 : K) * (5 : K) * (387072 : K) =
      (35 : K) * (243 : K) * (9795520512 : K) := by
    norm_num
  have hkel' : (243 : K) * (9795520512 : K) *
        (a0.derivative * b1 - a1 * b0.derivative).coeff 7 =
      (5 : K) * (387072 : K) * H.coeff 2 * (t1.coeff 1) ^ 5 * v.coeff 1 := by
    have ha1v : a1.coeff 3 * (243 : K) = H.coeff 2 * v.coeff 1 := by
      rw [mul_comm]
      exact ha1c
    calc
      (243 : K) * (9795520512 : K) *
            (a0.derivative * b1 - a1 * b0.derivative).coeff 7
          = (243 : K) * (9795520512 : K) *
              (-(a1.coeff 3 * (b0.coeff 5 * (5 : K)))) := by
            rw [hkel]
      _ = -((243 : K) * a1.coeff 3) * ((9795520512 : K) * b0.coeff 5) *
            (5 : K) := by
            ring
      _ = -((H.coeff 2 * v.coeff 1) *
            ((-387072 : K) * (t1.coeff 1) ^ 5) * (5 : K)) := by
            rw [ha1c, hb0c]
            ring
      _ = (5 : K) * (387072 : K) * H.coeff 2 * (t1.coeff 1) ^ 5 *
            v.coeff 1 := by
            ring
  have hfac : (243 : K) * (9795520512 : K) ≠ 0 :=
    mul_ne_zero h243 hc0
  have hmul := congrArg (fun x : K => (43046721 : K) * x) hkel'
  have hleft : (43046721 : K) * ((243 : K) * (9795520512 : K)) *
        (a0.derivative * b1 - a1 * b0.derivative).coeff 7 =
      ((243 : K) * (9795520512 : K)) * ((43046721 : K) *
        (a0.derivative * b1 - a1 * b0.derivative).coeff 7) := by
    ring
  have hscaled :=
    congrArg (fun n : K => n * (H.coeff 2 * (t1.coeff 1) ^ 5 * v.coeff 1))
      hconst
  have hright : (43046721 : K) * ((5 : K) * (387072 : K) * H.coeff 2 *
        (t1.coeff 1) ^ 5 * v.coeff 1) =
      ((243 : K) * (9795520512 : K)) * ((35 : K) * H.coeff 2 *
        (t1.coeff 1) ^ 5 * v.coeff 1) := by
    convert hscaled using 1 <;> ring
  have hboth : ((243 : K) * (9795520512 : K)) * ((43046721 : K) *
        (a0.derivative * b1 - a1 * b0.derivative).coeff 7) =
      ((243 : K) * (9795520512 : K)) * ((35 : K) * H.coeff 2 *
        (t1.coeff 1) ^ 5 * v.coeff 1) := by
    convert hmul using 1
    · ring
    · exact hright.symm
  exact mul_left_cancel₀ hfac hboth

theorem alignedNonsquare_linear_t31_zero_forces_v1_610
    {H g1 t1 t2 u t3 v a0 a1 b0 b1 : K[X]} {κ κ₃ κ₅ κ₇ κ₉ j : K}
    (hH : H.natDegree = 2) (hHne : H ≠ 0)
    (hg1 : g1.natDegree ≤ 1) (ht1 : t1.natDegree ≤ 1)
    (ht2 : t2.natDegree ≤ 2) (hu : u.natDegree ≤ 1)
    (ht3 : t3.natDegree ≤ 0) (hv : v.natDegree ≤ 1)
    (ha0 : a0.natDegree ≤ 1)
    (ht11 : t1.coeff 1 ≠ 0)
    (hv1 : (243 : K[X]) * a1 - g1 * u = H * v)
    (hq0 : (9795520512 : K[X]) * b0 =
      alignedTenthNonsquareSolved610 H g1 t1 u t3 v a0 κ κ₃ κ₅ κ₇ -
        Polynomial.C κ₉)
    (hq1 : (1632586752 : K[X]) * b1 =
      alignedNinthNonsquareSolved610 H g1 t1 t2 u t3 a0 a1 κ κ₃ κ₅ κ₇)
    (hrow : a0.derivative * b1 - a1 * b0.derivative = Polynomial.C j) :
    v.coeff 1 = 0 := by
  have hcoeff :=
    alignedNonsquare_linear_t31_zero_keller_coeff_seven_610 hH hg1 ht1 ht2
      hu ht3 hv ha0 hv1 hq0 hq1
  have h7 : (a0.derivative * b1 - a1 * b0.derivative).coeff 7 = 0 :=
    coeff_eq_C_of_pos hrow (by decide : 1 ≤ 7)
  have htop : (35 : K) * H.coeff 2 * (t1.coeff 1) ^ 5 * v.coeff 1 = 0 := by
    have : (43046721 : K) * 0 =
        (35 : K) * H.coeff 2 * (t1.coeff 1) ^ 5 * v.coeff 1 := by
      simpa [h7] using hcoeff
    simpa using this.symm
  have h35 : (35 : K) ≠ 0 := by norm_num
  have hLc : H.coeff 2 ≠ 0 := by
    rw [← hH, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hHne
  rcases mul_eq_zero.mp htop with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · rcases mul_eq_zero.mp h' with h'' | h''
      · exact (h35 h'').elim
      · exact (hLc h'').elim
    · exact (ht11 ((pow_eq_zero_iff (by decide : 5 ≠ 0)).mp h')).elim
  · exact h

theorem alignedNonsquare_ninth_zero_of_g1_t3_v_zero_610
    (H t1 u a0 : K[X]) (κ κ₃ κ₅ κ₇ : K) :
    alignedNinthNonsquareSolved610 H 0 t1 0 u 0 a0 0 κ κ₃ κ₅ κ₇ = 0 := by
  rw [alignedNinthNonsquareSolved_g1_t2_a1_zero_610]
  simp

theorem alignedNonsquare_t1_high_g1_t3_v_zero_false_610
    {H t1 u a0 a1 b0 b1 : K[X]} {κ κ₃ κ₅ κ₇ j : K}
    (hv1 : (243 : K[X]) * a1 - (0 : K[X]) * u = H * (0 : K[X]))
    (hq1 : (1632586752 : K[X]) * b1 =
      alignedNinthNonsquareSolved610 H 0 t1 0 u 0 a0 a1 κ κ₃ κ₅ κ₇)
    (hrow : a0.derivative * b1 - a1 * b0.derivative = Polynomial.C j)
    (hj : j ≠ 0) : False := by
  have ha10 : a1 = 0 := by
    have h := alignedNonsquare_a1_eq_610 hv1
    have h243 : (243 : K[X]) ≠ 0 := natCast_ne_zero_610 243 (by decide)
    have : (243 : K[X]) * a1 = 0 := by simpa using h
    exact (mul_eq_zero.mp this).resolve_left h243
  have hN : alignedNinthNonsquareSolved610 H 0 t1 0 u 0 a0 a1 κ κ₃ κ₅ κ₇ =
      0 := by
    simpa [ha10] using
      alignedNonsquare_ninth_zero_of_g1_t3_v_zero_610 H t1 u a0 κ κ₃ κ₅ κ₇
  have hc1 : (1632586752 : K[X]) ≠ 0 := natCast_ne_zero_610 1632586752
    (by decide)
  have hb10 : b1 = 0 := by
    have : (1632586752 : K[X]) * b1 = 0 := by simpa [hN] using hq1
    exact (mul_eq_zero.mp this).resolve_left hc1
  have hCj : Polynomial.C j = 0 := by
    simpa [ha10, hb10] using hrow.symm
  exact hj (Polynomial.C_eq_zero.mp hCj)

/-! ## Source-facing assembly -/

variable [IsAlgClosed K]

set_option maxHeartbeats 16000000 in
/-- Equal-degree `d ≥ 3` with both `g₁` and `t₁` at the top is impossible:
jac1 LC is `70 d G₁² T₁⁶ / 4782969`. -/
theorem normalized610ScaleTwo_alignedNonsquare_eqDegreeBothHigh_false
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0)
    (hboth :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      ∃ (κ κ₃ κ₅ κ₇ κ₉ : K) (g1 f t1 t2 u t3 v : K[X]) (d : ℕ),
        3 ≤ d ∧ g1.natDegree = d ∧ t1.natDegree = d ∧
          u.natDegree ≤ d ∧ t3.natDegree ≤ d ∧ v.natDegree ≤ d ∧
            (p.coeff 0).natDegree ≤ d ∧
              t2 - (6 : K[X]) * g1 * t1 = H * t3 ∧
                (243 : K[X]) * p.coeff 1 - g1 * u = H * v ∧
                  (81 : K[X]) * p.coeff 2 + (3 : K[X]) * g1 ^ 2 * t1 -
                      g1 * t2 = H * u ∧
                    (9795520512 : K[X]) *
                        ((Polynomial.Bivariate.equivMvPolynomial K).symm Q).coeff
                          0 =
                      alignedTenthNonsquareSolved610 H g1 t1 u t3 v
                          (p.coeff 0) κ κ₃ κ₅ κ₇ - Polynomial.C κ₉ ∧
                      (1632586752 : K[X]) *
                          ((Polynomial.Bivariate.equivMvPolynomial K).symm Q).coeff
                            1 =
                        alignedNinthNonsquareSolved610 H g1 t1 t2 u t3
                            (p.coeff 0) (p.coeff 1) κ κ₃ κ₅ κ₇ ∧
                        (15116544 : K[X]) *
                            ((Polynomial.Bivariate.equivMvPolynomial K).symm Q).coeff
                              2 =
                          alignedEighthNonsquareSolved610 H g1 t1 t2 u
                              (p.coeff 0) (p.coeff 1) κ κ₃ κ₅ -
                            Polynomial.C κ₇ * H) :
    False := by
  dsimp only at haligned hboth
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  obtain ⟨κ, κ₃, κ₅, κ₇, κ₉, g1, _f, t1, t2, u, t3, v, d, hd, hg1, ht1, hu,
    ht3, hv, ha0, ht2id, hv1, hu2, hq0, hq1, hq2⟩ := hboth
  rcases hsource with
    ⟨hHne, hHdeg, hPdegree, hQdegree, _hp6, _hq10, hKeller⟩
  have hp : p.natDegree = 6 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hjac1 : alignedFourteenthJacobianRow610 p q = 0 :=
    alignedFourteenthCoefficientJacobianRow_610 hp hq hjac
  have hpoly : alignedNonsquareJac1Poly610 (p.coeff 0) (p.coeff 1)
      (p.coeff 2) (q.coeff 0) (q.coeff 1) (q.coeff 2) = 0 := by
    simpa [alignedFourteenthJacobianRow_eq_jac1Poly_610] using hjac1
  exact alignedNonsquare_eqDegree_bothHigh_false_610 hd hHdeg.le hHne hg1 ht1
    hu ht3 hv ha0 ht2id hv1 hu2 hq0 hq1 hq2 hpoly

set_option maxHeartbeats 16000000 in
/-- Residual after transcribing the equal-degree `d ≥ 3` both-high jac1
kill, the residue principal symbol, and the linear leftover Keller LC
`35 t₁₁⁵ v₁`.  Remaining mixed-max Newton strata (unique-`t₁` after
dropping `g₁` from the top degree, unique-`g₁` with `t₁` not at the top,
unique-`v` with `t₁` of degree `D-1`, and `d = 2` with extra high
letters) are recorded here.  Leading form of the principal resisting
CAS limb: unique-`v` at `D ≥ 3` with companions of degree `D-1`, Keller
LC `-10 V (5 G₁ T₃³ - 189 T₁⁵ + 90 T₁² T₃²)` (CAS `VD_ALLMID`).
No `PlaneKeller610AlignedNonsquareExclusion` is discharged. -/
theorem normalized610ScaleTwo_alignedNonsquare_limbsResidual
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    (∃ (κ κ₃ κ₅ κ₇ κ₉ : K) (g1 f t1 t2 u t3 v : K[X]),
      alignedSecondDefect610 H (p.coeff 4) (p.coeff 5) (q.coeff 8) =
          Polynomial.C κ * H ^ 5 ∧
        p.coeff 5 = H ^ 2 * g1 ∧ p.coeff 4 = H * f ∧
        (3 : K[X]) * f - g1 ^ 2 = H * t1 ∧
        (27 : K[X]) * p.coeff 3 - g1 ^ 3 = H * t2 ∧
        (81 : K[X]) * p.coeff 2 + (3 : K[X]) * g1 ^ 2 * t1 - g1 * t2 =
          H * u ∧
        t2 - (6 : K[X]) * g1 * t1 = H * t3 ∧
        (243 : K[X]) * p.coeff 1 - g1 * u = H * v ∧
        alignedEleventhNonsquareResidue610 H g1 t1 u t3 v (p.coeff 0)
            κ κ₅ κ₇ = 0 ∧
          (∀ x : K, H.eval x = 0 → g1.eval x ≠ 0) ∧
            ∀ x : K, H.eval x = 0 →
              (45349632 : K) * (q.coeff 1).eval x =
                g1.eval x *
                  (alignedNonsquareDegreeOneRootHead610 (p.coeff 0) t1 u
                    κ κ₃ κ₅ κ₇).eval x) ∧
      (∃ j : K, j ≠ 0 ∧
        bivariateJacobian p q = Polynomial.C (Polynomial.C j) ∧
          alignedTwelfthJacobianRow610 p q = 0 ∧
          alignedThirteenthJacobianRow610 p q = 0 ∧
          alignedFourteenthJacobianRow610 p q = 0 ∧
          (p.coeff 0).derivative * q.coeff 1 -
              p.coeff 1 * (q.coeff 0).derivative = Polynomial.C j) :=
  normalized610ScaleTwo_alignedNonsquare_descentResidual hsource hnsq
    haligned

#print axioms alignedEleventhNonsquareResidue_coeff_fiveMul_610
#print axioms alignedNonsquare_jac1_coeff_eqDegree_610
#print axioms alignedNonsquare_eqDegree_bothHigh_false_610
#print axioms alignedNonsquare_linear_t31_zero_keller_coeff_seven_610
#print axioms alignedNonsquare_linear_t31_zero_forces_v1_610
#print axioms alignedNonsquare_t1_high_g1_t3_v_zero_false_610
#print axioms normalized610ScaleTwo_alignedNonsquare_eqDegreeBothHigh_false
#print axioms normalized610ScaleTwo_alignedNonsquare_limbsResidual

end Max11DegreeRoutes

