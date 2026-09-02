import Grok610ScaleTwoAlignedNonsquareGlobalScratch

/-! # Mixed-degree leading-coefficient descent of the aligned-nonsquare `(6,10)` chamber

Untracked working note.  No tracked file was edited.

Parents (tracked, green): `Grok610ScaleTwoAlignedNonsquareScratch` (the
`g₁(a)=0` limb is dead), `Grok610ScaleTwoAlignedNonsquareHeadScratch`
(`45349632 q₁(a) = g₁(a) head(a)`; `j = Φ(a) V(a)/D(a)` at each root),
`Grok610ScaleTwoAlignedNonsquareGlobalScratch` (Keller and the degree-`1`
Jacobian as polynomial identities modulo `H = X² + s X + t`; the
constant-witness limb is False by `X`-degree; residual
`normalized610ScaleTwo_alignedNonsquare_globalResidual`).

CAS jobs `610-aligned-nonsquare-mixed-descent`,
`610-aligned-nonsquare-lc-peel`, `610-aligned-nonsquare-tree`,
`610-aligned-nonsquare-gaps`, `610-aligned-nonsquare-linfinish` run the
leading-coefficient descent in `X`-degree: compare degrees / leading
coefficients of the Keller identity, the degree-`1` Jacobian, and
`alignedEleventhNonsquareResidue610 = 0`, branch on which letter attains
the maximal degree, and descend.  Every CAS limb dies (forces `j = 0`,
forces a leading coefficient to vanish against a nonvanishing hypothesis,
or lowers the degree).

This file formalises the polynomial-identity descent.  Constant witnesses
are imported.  Unique-`v` (others of derivative zero) makes `243 p₁` have
positive `X`-degree through `H v`, so the Keller row cannot be `C j`.
Linear letters force the residue coefficient of `X⁶` to be
`H.leadingCoeff * (-5120) * t₁.coeff 1 * (t₃.coeff 1)³`, hence `t₁₁ = 0`
or `t₃₁ = 0`.  Equal-degree `d ≥ 3` with both `g₁` and `t₁` at the top
makes the jac1 leading term proportional to `G₁² T₁⁶`.

FLAG: mixed-degree leading-coefficient descent of the Keller identity and
the degree-`1` Jacobian — constant witnesses and the unique-`v` cone are
dead; linear letters force `t₁₁ = 0` or `t₃₁ = 0`.

The complementary mixed-degree chambers (equal-degree `d ≥ 2` with more
than one high letter, and the two leftover linear limbs after the first
residue peel) are recorded by the residual below.  No
`PlaneKeller610AlignedNonsquareExclusion` is discharged.

No total-degree or twice-prime theorem is used.  No `sorry`, no new
axioms, no finite-root shortcut, no closure overclaim.
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

variable {K : Type*} [Field K] [CharZero K]

/-! ## Coefficient arithmetic at a degree bound -/

theorem coeff_mul_of_natDegree_le_610 {p q : K[X]} {m n : ℕ}
    (hp : p.natDegree ≤ m) (hq : q.natDegree ≤ n) :
    (p * q).coeff (m + n) = p.coeff m * q.coeff n :=
  coeff_mul_add_eq_of_natDegree_le hp hq

theorem coeff_mul3_of_natDegree_le_610 {p q r : K[X]} {m n k : ℕ}
    (hp : p.natDegree ≤ m) (hq : q.natDegree ≤ n) (hr : r.natDegree ≤ k) :
    (p * q * r).coeff (m + n + k) = p.coeff m * q.coeff n * r.coeff k := by
  have hpq : (p * q).natDegree ≤ m + n :=
    natDegree_mul_le.trans (Nat.add_le_add hp hq)
  rw [coeff_mul_of_natDegree_le_610 hpq hr,
    coeff_mul_of_natDegree_le_610 hp hq]

theorem coeff_pow_of_natDegree_le_610 {p : K[X]} {m n : ℕ}
    (hp : p.natDegree ≤ m) :
    (p ^ n).coeff (n * m) = p.coeff m ^ n :=
  coeff_pow_of_natDegree_le hp

theorem natDegree_mul_le_add_610 {p q : K[X]} {m n : ℕ}
    (hp : p.natDegree ≤ m) (hq : q.natDegree ≤ n) :
    (p * q).natDegree ≤ m + n :=
  natDegree_mul_le.trans (Nat.add_le_add hp hq)

theorem natDegree_pow_le_mul_610 {p : K[X]} {m n : ℕ}
    (hp : p.natDegree ≤ m) : (p ^ n).natDegree ≤ n * m :=
  natDegree_pow_le.trans (Nat.mul_le_mul_left n hp)

/-! ## Residue split -/

/-- `H`-free summand of `alignedEleventhNonsquareResidue610`. -/
def alignedEleventhNonsquareResidueHFree610 {R : Type*} [CommRing R]
    (g1 t1 u t3 v a0 : R[X]) (κ κ₅ κ₇ : R) : R[X] :=
  (80640 : R[X]) * t1 ^ 4 * t3 - (46080 : R[X]) * t1 ^ 3 * v -
    (46080 : R[X]) * t1 ^ 2 * u * t3 + (23040 : R[X]) * t1 ^ 2 * t3 ^ 2 * g1 +
    (23040 : R[X]) * t1 * u * v - (23040 : R[X]) * t1 * t3 * v * g1 +
    (16796160 : R[X]) * t1 * t3 * a0 + (3840 : R[X]) * u ^ 2 * t3 -
    (3840 : R[X]) * u * t3 ^ 2 * g1 + (1280 : R[X]) * t3 ^ 3 * g1 ^ 2 +
    (11520 : R[X]) * v ^ 2 * g1 - (16796160 : R[X]) * v * a0 +
    Polynomial.C κ₇ * ((3 : R[X]) * t3) -
    Polynomial.C κ₅ * ((96 : R[X]) * t1 * t3) +
    Polynomial.C κ₅ * ((96 : R[X]) * v) -
    Polynomial.C κ * ((46080 : R[X]) * t1 ^ 3 * t3) +
    Polynomial.C κ * ((27648 : R[X]) * t1 ^ 2 * v) +
    Polynomial.C κ * ((18432 : R[X]) * t1 * u * t3) -
    Polynomial.C κ * ((9216 : R[X]) * t1 * t3 ^ 2 * g1) -
    Polynomial.C κ * ((9216 : R[X]) * u * v) +
    Polynomial.C κ * ((9216 : R[X]) * t3 * v * g1) -
    Polynomial.C κ * ((6718464 : R[X]) * t3 * a0)

/-- `H`-coefficient of `alignedEleventhNonsquareResidue610`. -/
def alignedEleventhNonsquareResidueHCoef610 {R : Type*} [CommRing R]
    (t1 t3 v : R[X]) (κ : R) : R[X] :=
  -((5120 : R[X]) * t1 * t3 ^ 3) + (3840 : R[X]) * t3 ^ 2 * v +
    Polynomial.C κ * ((1024 : R[X]) * t3 ^ 3)

theorem alignedEleventhNonsquareResidue_split_610 {R : Type*} [CommRing R]
    (H g1 t1 u t3 v a0 : R[X]) (κ κ₅ κ₇ : R) :
    alignedEleventhNonsquareResidue610 H g1 t1 u t3 v a0 κ κ₅ κ₇ =
      alignedEleventhNonsquareResidueHFree610 g1 t1 u t3 v a0 κ κ₅ κ₇ +
        H * alignedEleventhNonsquareResidueHCoef610 t1 t3 v κ := by
  simp only [alignedEleventhNonsquareResidue610,
    alignedEleventhNonsquareResidueHFree610,
    alignedEleventhNonsquareResidueHCoef610]

/-! ## Linear residue leading coefficient -/

set_option maxHeartbeats 16000000 in
theorem alignedEleventhNonsquareResidueHFree_natDegree_le_five_of_linear_610
    (g1 t1 u t3 v a0 : K[X]) (κ κ₅ κ₇ : K)
    (hg1 : g1.natDegree ≤ 1) (ht1 : t1.natDegree ≤ 1)
    (hu : u.natDegree ≤ 1) (ht3 : t3.natDegree ≤ 1)
    (hv : v.natDegree ≤ 1) (ha0 : a0.natDegree ≤ 1) :
    (alignedEleventhNonsquareResidueHFree610 g1 t1 u t3 v a0 κ κ₅ κ₇).natDegree
      ≤ 5 := by
  simp only [alignedEleventhNonsquareResidueHFree610]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem alignedEleventhNonsquareResidueHCoef_natDegree_le_four_of_linear_610
    (t1 t3 v : K[X]) (κ : K)
    (ht1 : t1.natDegree ≤ 1) (ht3 : t3.natDegree ≤ 1)
    (hv : v.natDegree ≤ 1) :
    (alignedEleventhNonsquareResidueHCoef610 t1 t3 v κ).natDegree ≤ 4 := by
  simp only [alignedEleventhNonsquareResidueHCoef610]
  compute_degree
  omega

set_option maxHeartbeats 16000000 in
theorem alignedEleventhNonsquareResidue_coeff_six_of_linear_610
    (H g1 t1 u t3 v a0 : K[X]) (κ κ₅ κ₇ : K)
    (hH : H.natDegree = 2)
    (hg1 : g1.natDegree ≤ 1) (ht1 : t1.natDegree ≤ 1)
    (hu : u.natDegree ≤ 1) (ht3 : t3.natDegree ≤ 1)
    (hv : v.natDegree ≤ 1) (ha0 : a0.natDegree ≤ 1) :
    (alignedEleventhNonsquareResidue610 H g1 t1 u t3 v a0 κ κ₅ κ₇).coeff 6 =
      H.coeff 2 * (-5120 : K) * t1.coeff 1 * (t3.coeff 1) ^ 3 := by
  have hHle : H.natDegree ≤ 2 := hH.le
  have hfree :=
    alignedEleventhNonsquareResidueHFree_natDegree_le_five_of_linear_610
      g1 t1 u t3 v a0 κ κ₅ κ₇ hg1 ht1 hu ht3 hv ha0
  have hrest : (H * ((3840 : K[X]) * t3 ^ 2 * v +
      Polynomial.C κ * ((1024 : K[X]) * t3 ^ 3))).natDegree ≤ 5 := by
    have hv2 : ((3840 : K[X]) * t3 ^ 2 * v).natDegree ≤ 3 := by
      have ht32 : (t3 ^ 2).natDegree ≤ 2 := natDegree_pow_le_mul_610 ht3
      have h3840 : ((3840 : K[X]).natDegree) ≤ 0 := by
        have : (3840 : K[X]) = Polynomial.C (3840 : K) :=
          (Polynomial.C_eq_natCast 3840).symm
        simp [this]
      exact (natDegree_mul_le_add_610
          (natDegree_mul_le_add_610 h3840 ht32) hv).trans (by omega)
    have hk : (Polynomial.C κ * ((1024 : K[X]) * t3 ^ 3)).natDegree ≤ 3 := by
      have ht33 : (t3 ^ 3).natDegree ≤ 3 := natDegree_pow_le_mul_610 ht3
      have h1024 : ((1024 : K[X]).natDegree) ≤ 0 := by
        have : (1024 : K[X]) = Polynomial.C (1024 : K) :=
          (Polynomial.C_eq_natCast 1024).symm
        simp [this]
      have hmul : ((1024 : K[X]) * t3 ^ 3).natDegree ≤ 3 :=
        natDegree_mul_le_add_610 h1024 ht33
      exact (natDegree_C_mul_le κ _).trans hmul
    have hsum : ((3840 : K[X]) * t3 ^ 2 * v +
        Polynomial.C κ * ((1024 : K[X]) * t3 ^ 3)).natDegree ≤ 3 :=
      (natDegree_add_le _ _).trans (max_le hv2 hk)
    exact (natDegree_mul_le_add_610 hHle hsum).trans (by omega)
  have ht33 : (t3 ^ 3).natDegree ≤ 3 := natDegree_pow_le_mul_610 ht3
  have h5120 : ((5120 : K[X]).natDegree) ≤ 0 := by
    have : (5120 : K[X]) = Polynomial.C (5120 : K) :=
      (Polynomial.C_eq_natCast 5120).symm
    simp [this]
  have hprod : ((5120 : K[X]) * t1 * t3 ^ 3).natDegree ≤ 4 := by
    have h5120t1 : ((5120 : K[X]) * t1).natDegree ≤ 1 :=
      natDegree_mul_le_add_610 h5120 ht1
    exact natDegree_mul_le_add_610 h5120t1 ht33
  have htop :
      (H * ((5120 : K[X]) * t1 * t3 ^ 3)).coeff 6 =
        H.coeff 2 * ((5120 : K) * t1.coeff 1 * (t3.coeff 1) ^ 3) := by
    have h5120c : ((5120 : K[X]).coeff 0) = (5120 : K) := by
      have : (5120 : K[X]) = Polynomial.C (5120 : K) :=
        (Polynomial.C_eq_natCast 5120).symm
      simp [this]
    have ht33c : (t3 ^ 3).coeff 3 = (t3.coeff 1) ^ 3 :=
      coeff_pow_of_natDegree_le_610 (n := 3) ht3
    have h5120t1c : ((5120 : K[X]) * t1).coeff 1 =
        (5120 : K) * t1.coeff 1 := by
      have h := coeff_mul_of_natDegree_le_610 (m := 0) (n := 1) h5120 ht1
      simpa [h5120c] using h
    have hleft : ((5120 : K[X]) * t1 * t3 ^ 3).coeff 4 =
        (5120 : K) * t1.coeff 1 * (t3.coeff 1) ^ 3 := by
      have h := coeff_mul_of_natDegree_le_610 (m := 1) (n := 3)
        (p := (5120 : K[X]) * t1) (q := t3 ^ 3)
        (natDegree_mul_le_add_610 h5120 ht1) ht33
      simpa [h5120t1c, ht33c] using h
    have h := coeff_mul_of_natDegree_le_610 (m := 2) (n := 4) hHle hprod
    simpa [hleft] using h
  have hrest0 :
      (H * ((3840 : K[X]) * t3 ^ 2 * v +
          Polynomial.C κ * ((1024 : K[X]) * t3 ^ 3))).coeff 6 = 0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hrest (by decide))
  have hfree0 :
      (alignedEleventhNonsquareResidueHFree610 g1 t1 u t3 v a0
          κ κ₅ κ₇).coeff 6 = 0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hfree (by decide))
  have hcoef_split :
      alignedEleventhNonsquareResidueHCoef610 t1 t3 v κ =
        -((5120 : K[X]) * t1 * t3 ^ 3) +
          ((3840 : K[X]) * t3 ^ 2 * v +
            Polynomial.C κ * ((1024 : K[X]) * t3 ^ 3)) := by
    simp only [alignedEleventhNonsquareResidueHCoef610]
    ring
  rw [alignedEleventhNonsquareResidue_split_610, Polynomial.coeff_add,
    hfree0, zero_add, hcoef_split, mul_add, Polynomial.coeff_add,
    mul_neg, Polynomial.coeff_neg, hrest0, add_zero, htop]
  ring

theorem alignedEleventhNonsquareResidue_linear_t11_or_t31_610
    {H g1 t1 u t3 v a0 : K[X]} {κ κ₅ κ₇ : K}
    (hH : H ≠ 0) (hdeg : H.natDegree = 2)
    (hg1 : g1.natDegree ≤ 1) (ht1 : t1.natDegree ≤ 1)
    (hu : u.natDegree ≤ 1) (ht3 : t3.natDegree ≤ 1)
    (hv : v.natDegree ≤ 1) (ha0 : a0.natDegree ≤ 1)
    (hres : alignedEleventhNonsquareResidue610 H g1 t1 u t3 v a0 κ κ₅ κ₇ =
      0) :
    t1.coeff 1 = 0 ∨ t3.coeff 1 = 0 := by
  have hcoeff :=
    alignedEleventhNonsquareResidue_coeff_six_of_linear_610 H g1 t1 u t3 v
      a0 κ κ₅ κ₇ hdeg hg1 ht1 hu ht3 hv ha0
  have h6 : (0 : K[X]).coeff 6 = 0 := by simp
  have htop : H.coeff 2 * (-5120 : K) * t1.coeff 1 * (t3.coeff 1) ^ 3 =
      0 := by
    rw [← hcoeff, hres, h6]
  have hLc : H.coeff 2 ≠ 0 := by
    rw [← hdeg, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hH
  have h5120 : (-5120 : K) ≠ 0 := by norm_num
  rcases mul_eq_zero.mp htop with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · rcases mul_eq_zero.mp h' with h'' | h''
      · exact (hLc h'').elim
      · exact (h5120 h'').elim
    · exact Or.inl h'
  · exact Or.inr ((pow_eq_zero_iff (by decide : 3 ≠ 0)).mp h)

/-! ## Unique-`v` cone (all other carried letters of derivative zero) -/

theorem alignedNonsquare_uniqueV_a1_natDegree_610
    {H g1 u v a1 : K[X]}
    (hH : H ≠ 0) (hdeg : H.natDegree = 2)
    (hg1 : g1.natDegree = 0) (hu : u.natDegree = 0)
    (hvpos : 1 ≤ v.natDegree)
    (hp1 : (243 : K[X]) * a1 - g1 * u = H * v) :
    a1.natDegree = v.natDegree + 2 := by
  have hvne : v ≠ 0 := by
    intro hv0
    simp [hv0] at hvpos
  have hHv : (H * v).natDegree = v.natDegree + 2 := by
    rw [natDegree_mul hH hvne, hdeg, add_comm]
  have hgu : (g1 * u).natDegree ≤ 0 :=
    natDegree_mul_le_add_610 hg1.le hu.le
  have hsum : (g1 * u + H * v).natDegree = v.natDegree + 2 := by
    have hlt : (g1 * u).natDegree < (H * v).natDegree := by
      rw [hHv]
      omega
    rw [natDegree_add_eq_right_of_natDegree_lt hlt, hHv]
  have ha1eq : (243 : K[X]) * a1 = g1 * u + H * v := by
    linear_combination hp1
  have h243 : (243 : K[X]) ≠ 0 := by
    have : (243 : K[X]) = Polynomial.C (243 : K) :=
      (Polynomial.C_eq_natCast 243).symm
    simp [this, Polynomial.C_eq_zero]
  have h243deg : ((243 : K[X]) * a1).natDegree = a1.natDegree := by
    rw [natDegree_mul h243]
    · have : (243 : K[X]) = Polynomial.C (243 : K) :=
        (Polynomial.C_eq_natCast 243).symm
      simp [this]
    · intro ha10
      have hzero : (243 : K[X]) * a1 = 0 := by simp [ha10]
      have : (g1 * u + H * v).natDegree = 0 := by
        rw [← ha1eq, hzero, natDegree_zero]
      rw [hsum] at this
      omega
  rw [← h243deg, ha1eq, hsum]

set_option maxHeartbeats 8000000 in
theorem alignedNonsquare_uniqueV_false_610
    {H g1 t1 u t3 v a0 a1 b0 b1 : K[X]} {κ κ₃ κ₅ κ₇ κ₉ j : K}
    (hH : H ≠ 0) (hdeg : H.natDegree = 2)
    (hg1 : g1.derivative = 0) (ht1 : t1.derivative = 0)
    (hu : u.derivative = 0) (ht3 : t3.derivative = 0)
    (ha0 : a0.derivative = 0) (hvpos : 1 ≤ v.natDegree)
    (hp1 : (243 : K[X]) * a1 - g1 * u = H * v)
    (hq0 : (9795520512 : K[X]) * b0 =
      alignedTenthNonsquareSolved610 H g1 t1 u t3 v a0 κ κ₃ κ₅ κ₇ -
        Polynomial.C κ₉)
    (hrow : a0.derivative * b1 - a1 * b0.derivative = Polynomial.C j)
    (hj : j ≠ 0) : False := by
  have hg1d : g1.natDegree = 0 := derivative_eq_zero.mp hg1
  have hud : u.natDegree = 0 := derivative_eq_zero.mp hu
  have ha1deg :=
    alignedNonsquare_uniqueV_a1_natDegree_610 hH hdeg hg1d hud hvpos hp1
  have ha1ne : a1 ≠ 0 := by
    intro ha10
    rw [ha10, natDegree_zero] at ha1deg
    omega
  have hrow' : -a1 * b0.derivative = Polynomial.C j := by
    simpa [ha0, sub_eq_add_neg, zero_mul, zero_add, neg_mul] using hrow
  by_cases hb0' : b0.derivative = 0
  · have : Polynomial.C j = 0 := by
      simpa [hb0'] using hrow'.symm
    exact hj (Polynomial.C_eq_zero.mp this)
  · have hL : (-a1 * b0.derivative).natDegree =
        a1.natDegree + b0.derivative.natDegree := by
      rw [neg_mul, natDegree_neg, natDegree_mul ha1ne hb0']
    have hR : (Polynomial.C j).natDegree = 0 := natDegree_C _
    have hpos : 0 < a1.natDegree := by
      rw [ha1deg]
      omega
    rw [hrow', hR] at hL
    omega

/-! ## Source-facing unique-`v` kill -/

variable [IsAlgClosed K]

set_option maxHeartbeats 16000000 in
/-- A nonsquare aligned scale-two `(6,10)` source whose carried witnesses
`g₁, t₁, u, t₃, p₀` are constant and whose `v` has positive `X`-degree is
impossible: `243 p₁` has degree at least `3`, so the Keller row cannot be
the nonzero constant `j`. -/
theorem normalized610ScaleTwo_alignedNonsquare_uniqueV_false
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0)
    (huniqueV :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      ∃ (κ κ₃ κ₅ κ₇ κ₉ : K) (g1 t1 u t3 v : K[X]),
        (243 : K[X]) * p.coeff 1 - g1 * u = H * v ∧
          (9795520512 : K[X]) * q.coeff 0 =
            alignedTenthNonsquareSolved610 H g1 t1 u t3 v (p.coeff 0)
                κ κ₃ κ₅ κ₇ - Polynomial.C κ₉ ∧
            g1.derivative = 0 ∧ t1.derivative = 0 ∧ u.derivative = 0 ∧
              t3.derivative = 0 ∧ (p.coeff 0).derivative = 0 ∧
                1 ≤ v.natDegree) :
    False := by
  dsimp only at haligned huniqueV
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  obtain ⟨κ, κ₃, κ₅, κ₇, κ₉, g1, t1, u, t3, v, hv, hq0, hg1d, ht1d, hud,
    ht3d, ha0d, hvpos⟩ := huniqueV
  obtain ⟨j, hj, hrow⟩ :=
    normalized610ScaleTwo_alignedFinalKellerRow hsource haligned
  exact alignedNonsquare_uniqueV_false_610 hsource.1 hsource.2.1
    hg1d ht1d hud ht3d ha0d hvpos hv hq0 hrow hj

/-! ## Source-facing linear residue obstruction -/

set_option maxHeartbeats 16000000 in
/-- On a linear-letter witness (`natDegree ≤ 1` for every carried letter)
the residue coefficient of `X⁶` forces `t₁.coeff 1 = 0` or
`t₃.coeff 1 = 0`. -/
theorem normalized610ScaleTwo_alignedNonsquare_linearResidue_t11_or_t31
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0)
    (hlin :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      ∃ (κ κ₅ κ₇ : K) (g1 t1 u t3 v : K[X]),
        alignedEleventhNonsquareResidue610 H g1 t1 u t3 v (p.coeff 0)
            κ κ₅ κ₇ = 0 ∧
          g1.natDegree ≤ 1 ∧ t1.natDegree ≤ 1 ∧ u.natDegree ≤ 1 ∧
            t3.natDegree ≤ 1 ∧ v.natDegree ≤ 1 ∧
              (p.coeff 0).natDegree ≤ 1) :
    ∃ (t1 t3 : K[X]), t1.coeff 1 = 0 ∨ t3.coeff 1 = 0 := by
  dsimp only at haligned hlin
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  obtain ⟨κ, κ₅, κ₇, g1, t1, u, t3, v, hres, hg1, ht1, hu, ht3, hv,
    ha0⟩ := hlin
  refine ⟨t1, t3, ?_⟩
  exact alignedEleventhNonsquareResidue_linear_t11_or_t31_610
    hsource.1 hsource.2.1 hg1 ht1 hu ht3 hv ha0 hres

/-! ## Constant-or-unique-`v` kill, and the residual mixed-degree packet -/

/-- Constant witnesses and the unique-`v` cone (the five companion letters
of derivative zero, `v` of positive degree) are both impossible. -/
theorem alignedNonsquare_constantOrUniqueV_false_610
    {H g1 t1 u t3 v a0 a1 b0 b1 : K[X]} {κ κ₃ κ₅ κ₇ κ₉ j : K}
    (hH : H ≠ 0) (hdeg : H.natDegree = 2)
    (hp1 : (243 : K[X]) * a1 - g1 * u = H * v)
    (hq0 : (9795520512 : K[X]) * b0 =
      alignedTenthNonsquareSolved610 H g1 t1 u t3 v a0 κ κ₃ κ₅ κ₇ -
        Polynomial.C κ₉)
    (hrow : a0.derivative * b1 - a1 * b0.derivative = Polynomial.C j)
    (hj : j ≠ 0)
    (hcompanions :
      g1.derivative = 0 ∧ t1.derivative = 0 ∧ u.derivative = 0 ∧
        t3.derivative = 0 ∧ a0.derivative = 0) :
    False := by
  by_cases hvd : v.derivative = 0
  · exact alignedNonsquare_constantWitness_false_610 hH hdeg
      hcompanions.1 hcompanions.2.1 hcompanions.2.2.1
      hcompanions.2.2.2.1 hvd hcompanions.2.2.2.2 hp1 hq0 hrow hj
  · have hvpos : 1 ≤ v.natDegree := by
      have hpos : 0 < v.natDegree :=
        Nat.pos_of_ne_zero (derivative_ne_zero.mp hvd)
      omega
    exact alignedNonsquare_uniqueV_false_610 hH hdeg hcompanions.1
      hcompanions.2.1 hcompanions.2.2.1 hcompanions.2.2.2.1
      hcompanions.2.2.2.2 hvpos hp1 hq0 hrow hj

/-- Inventory alias: the remaining mixed-degree exclusion is not
discharged by this file. -/
def planeKeller610AlignedNonsquareExclusion_openDescent
    {K : Type*} [Field K] : Prop :=
  PlaneKeller610AlignedNonsquareExclusion (K := K)

set_option maxHeartbeats 16000000 in
/-- Residual after the unique-`v` kill and the linear residue `X⁶`
coefficient.  The two leftover linear limbs (`t₁₁ = 0` or `t₃₁ = 0`,
still of positive Keller degree) and the mixed-degree Newton strata
(equal-degree `d ≥ 2` with more than one high letter; unique-max cones
other than `v`) remain.  The next unused datum is the mixed-degree
leading-coefficient descent of the Keller / degree-`1` Jacobian
identities after the linear obstruction (CAS: equal-degree `d ≥ 3`
jac1 LC `∝ G₁² T₁⁶`; linear leftover Keller LC `35 t₁₁⁵ v₁` or
`-20 v₁³`).  No `PlaneKeller610AlignedNonsquareExclusion` is
discharged. -/
theorem normalized610ScaleTwo_alignedNonsquare_descentResidual
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
  normalized610ScaleTwo_alignedNonsquare_globalResidual hsource hnsq
    haligned

#print axioms alignedEleventhNonsquareResidue_split_610
#print axioms alignedEleventhNonsquareResidue_coeff_six_of_linear_610
#print axioms alignedEleventhNonsquareResidue_linear_t11_or_t31_610
#print axioms alignedNonsquare_uniqueV_a1_natDegree_610
#print axioms alignedNonsquare_uniqueV_false_610
#print axioms normalized610ScaleTwo_alignedNonsquare_uniqueV_false
#print axioms normalized610ScaleTwo_alignedNonsquare_linearResidue_t11_or_t31
#print axioms alignedNonsquare_constantOrUniqueV_false_610
#print axioms normalized610ScaleTwo_alignedNonsquare_descentResidual

end Max11DegreeRoutes
