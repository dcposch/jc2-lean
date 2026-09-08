import LowScale68CubicDescent

/-! # Secondary radius below the `(6,8)` cubic boundary

After the first weighted boundary, the four transverse coordinates can drop by
different amounts.  This file therefore uses their minimum *actual* degree
deficit rather than imposing an equal secondary weight.  A sentinel larger
than every possible nonzero deficit removes identically-zero coordinates from
the minimum.  The exact-cubic contradiction proves that the minimum is always
attained by a genuine nonzero defect.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section SecondaryRadius68

variable {k : Type*} [Field k] [CharZero k]

/-- Degree deficit of one transverse coordinate.  Zero polynomials receive a
sentinel strictly above all four possible nonzero deficits. -/
def polynomialGap68 (n weight : ℕ) (p : k[X]) : ℕ :=
  by
    classical
    exact if p = 0 then 6 * n + 1 else weight * n - p.natDegree

/-- Minimum actual deficit among `B`, the translated `C`, `D`, and the
translated `E`. -/
def cubicDefectGap68 (n : ℕ) (B c D e : k[X]) : ℕ :=
  min (polynomialGap68 n 3 B)
    (min (polynomialGap68 n 4 c)
      (min (polynomialGap68 n 5 D) (polynomialGap68 n 6 e)))

theorem polynomialGap68_pos (n weight : ℕ) (p : k[X])
    (hdeg : p.natDegree < weight * n) :
    0 < polynomialGap68 n weight p := by
  by_cases hp : p = 0
  · simp [polynomialGap68, hp]
  · simp only [polynomialGap68, if_neg hp]
    omega

theorem polynomialGap68_lt_sentinel_of_ne_zero
    (n weight : ℕ) (p : k[X]) (hweight : weight ≤ 6) (hp : p ≠ 0) :
    polynomialGap68 n weight p < 6 * n + 1 := by
  simp only [polynomialGap68, if_neg hp]
  calc
    weight * n - p.natDegree ≤ weight * n := Nat.sub_le _ _
    _ ≤ 6 * n := Nat.mul_le_mul_right n hweight
    _ < 6 * n + 1 := Nat.lt_succ_self _

theorem cubicDefectGap68_pos (n : ℕ) (B c D e : k[X])
    (hB : B.natDegree < 3 * n) (hc : c.natDegree < 4 * n)
    (hD : D.natDegree < 5 * n) (he : e.natDegree < 6 * n) :
    0 < cubicDefectGap68 n B c D e := by
  exact lt_min (polynomialGap68_pos n 3 B hB)
    (lt_min (polynomialGap68_pos n 4 c hc)
      (lt_min (polynomialGap68_pos n 5 D hD)
        (polynomialGap68_pos n 6 e he)))

theorem cubicDefectGap68_lt_sentinel (n : ℕ) (B c D e : k[X])
    (hnotall : ¬ (B = 0 ∧ c = 0 ∧ D = 0 ∧ e = 0)) :
    cubicDefectGap68 n B c D e < 6 * n + 1 := by
  have hsome : B ≠ 0 ∨ c ≠ 0 ∨ D ≠ 0 ∨ e ≠ 0 := by
    tauto
  rcases hsome with hB | hc | hD | he
  · exact lt_of_le_of_lt (Nat.min_le_left _ _)
      (polynomialGap68_lt_sentinel_of_ne_zero n 3 B (by omega) hB)
  · exact lt_of_le_of_lt
      (le_trans (Nat.min_le_right _ _) (Nat.min_le_left _ _))
      (polynomialGap68_lt_sentinel_of_ne_zero n 4 c (by omega) hc)
  · exact lt_of_le_of_lt
      (le_trans (Nat.min_le_right _ _)
        (le_trans (Nat.min_le_right _ _) (Nat.min_le_left _ _)))
      (polynomialGap68_lt_sentinel_of_ne_zero n 5 D (by omega) hD)
  · exact lt_of_le_of_lt
      (le_trans (Nat.min_le_right _ _)
        (le_trans (Nat.min_le_right _ _) (Nat.min_le_right _ _)))
      (polynomialGap68_lt_sentinel_of_ne_zero n 6 e (by omega) he)

/-- Every transverse coordinate lies below its old bound by at least the
secondary gap. -/
theorem cubicDefectGap68_degreeBounds (n : ℕ) (B c D e : k[X])
    (hB : B.natDegree < 3 * n) (hc : c.natDegree < 4 * n)
    (hD : D.natDegree < 5 * n) (he : e.natDegree < 6 * n) :
    B.natDegree ≤ 3 * n - cubicDefectGap68 n B c D e ∧
    c.natDegree ≤ 4 * n - cubicDefectGap68 n B c D e ∧
    D.natDegree ≤ 5 * n - cubicDefectGap68 n B c D e ∧
    e.natDegree ≤ 6 * n - cubicDefectGap68 n B c D e := by
  have hBmin : cubicDefectGap68 n B c D e ≤ polynomialGap68 n 3 B :=
    Nat.min_le_left _ _
  have hcmin : cubicDefectGap68 n B c D e ≤ polynomialGap68 n 4 c :=
    le_trans (Nat.min_le_right _ _) (Nat.min_le_left _ _)
  have hDmin : cubicDefectGap68 n B c D e ≤ polynomialGap68 n 5 D :=
    le_trans (Nat.min_le_right _ _)
      (le_trans (Nat.min_le_right _ _) (Nat.min_le_left _ _))
  have hemin : cubicDefectGap68 n B c D e ≤ polynomialGap68 n 6 e :=
    le_trans (Nat.min_le_right _ _)
      (le_trans (Nat.min_le_right _ _) (Nat.min_le_right _ _))
  constructor
  · by_cases hzero : B = 0
    · simp [hzero]
    · simp only [polynomialGap68, if_neg hzero] at hBmin
      omega
  constructor
  · by_cases hzero : c = 0
    · simp [hzero]
    · simp only [polynomialGap68, if_neg hzero] at hcmin
      omega
  constructor
  · by_cases hzero : D = 0
    · simp [hzero]
    · simp only [polynomialGap68, if_neg hzero] at hDmin
      omega
  · by_cases hzero : e = 0
    · simp [hzero]
    · simp only [polynomialGap68, if_neg hzero] at hemin
      omega

private theorem coeff_gap_ne_zero68 (n weight gap : ℕ) (p : k[X])
    (hp : p ≠ 0) (hdeg : p.natDegree < weight * n)
    (hgap : gap = polynomialGap68 n weight p) :
    p.coeff (weight * n - gap) ≠ 0 := by
  simp only [polynomialGap68, if_neg hp] at hgap
  have hindex : weight * n - gap = p.natDegree := by omega
  rw [hindex, coeff_natDegree]
  exact leadingCoeff_ne_zero.mpr hp

/-- At least one genuine defect attains the secondary boundary. -/
theorem cubicDefectGap68_boundary_attained (n : ℕ) (B c D e : k[X])
    (hBdeg : B.natDegree < 3 * n) (hcdeg : c.natDegree < 4 * n)
    (hDdeg : D.natDegree < 5 * n) (hedeg : e.natDegree < 6 * n)
    (hnotall : ¬ (B = 0 ∧ c = 0 ∧ D = 0 ∧ e = 0)) :
    B.coeff (3 * n - cubicDefectGap68 n B c D e) ≠ 0 ∨
    c.coeff (4 * n - cubicDefectGap68 n B c D e) ≠ 0 ∨
    D.coeff (5 * n - cubicDefectGap68 n B c D e) ≠ 0 ∨
    e.coeff (6 * n - cubicDefectGap68 n B c D e) ≠ 0 := by
  have hlt := cubicDefectGap68_lt_sentinel n B c D e hnotall
  rcases min_choice (polynomialGap68 n 3 B)
      (min (polynomialGap68 n 4 c)
        (min (polynomialGap68 n 5 D) (polynomialGap68 n 6 e))) with hB | hrest
  · left
    have hselected : cubicDefectGap68 n B c D e = polynomialGap68 n 3 B := by
      simpa only [cubicDefectGap68] using hB
    have hBne : B ≠ 0 := by
      intro hzero
      simp only [hselected, polynomialGap68, if_pos hzero] at hlt
      omega
    exact coeff_gap_ne_zero68 n 3 (cubicDefectGap68 n B c D e) B hBne
      hBdeg hselected
  · rcases min_choice (polynomialGap68 n 4 c)
        (min (polynomialGap68 n 5 D) (polynomialGap68 n 6 e)) with hc | hrest2
    · right; left
      have hselected : cubicDefectGap68 n B c D e = polynomialGap68 n 4 c :=
        hrest.trans hc
      have hcne : c ≠ 0 := by
        intro hzero
        simp only [hselected, polynomialGap68, if_pos hzero] at hlt
        omega
      exact coeff_gap_ne_zero68 n 4 (cubicDefectGap68 n B c D e) c hcne
        hcdeg hselected
    · rcases min_choice (polynomialGap68 n 5 D)
          (polynomialGap68 n 6 e) with hD | he
      · right; right; left
        have hselected :
            cubicDefectGap68 n B c D e = polynomialGap68 n 5 D :=
          hrest.trans (hrest2.trans hD)
        have hDne : D ≠ 0 := by
          intro hzero
          simp only [hselected, polynomialGap68, if_pos hzero] at hlt
          omega
        exact coeff_gap_ne_zero68 n 5 (cubicDefectGap68 n B c D e) D hDne
          hDdeg hselected
      · right; right; right
        have hselected :
            cubicDefectGap68 n B c D e = polynomialGap68 n 6 e :=
          hrest.trans (hrest2.trans he)
        have hene : e ≠ 0 := by
          intro hzero
          simp only [hselected, polynomialGap68, if_pos hzero] at hlt
          omega
        exact coeff_gap_ne_zero68 n 6 (cubicDefectGap68 n B c D e) e hene
          hedeg hselected

theorem expand_cubicCDefectPolynomial68 (m : ℕ) (A C0 : k[X]) :
    cubicCDefectPolynomial68 (expand k m A) (expand k m C0) =
      expand k m (cubicCDefectPolynomial68 A C0) := by
  simp only [cubicCDefectPolynomial68, map_sub, map_smul, map_pow]

theorem expand_cubicEDefectPolynomial68 (m : ℕ) (A C0 E : k[X]) :
    cubicEDefectPolynomial68 (expand k m A) (expand k m C0)
        (expand k m E) =
      expand k m (cubicEDefectPolynomial68 A C0 E) := by
  simp only [cubicEDefectPolynomial68, map_add, map_sub, map_smul, map_mul,
    map_pow]

set_option maxHeartbeats 3000000 in
/-- The canonical expanded lower system has a positive, attained secondary
defect radius with all four corresponding degree bounds. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_secondaryRadius68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E) :
    let n := weightedRadius68 A B C0 D E
    let Ae := expand k 60 A
    let Be := expand k 60 B
    let ce := cubicCDefectPolynomial68 Ae (expand k 60 C0)
    let De := expand k 60 D
    let ee := cubicEDefectPolynomial68 Ae (expand k 60 C0) (expand k 60 E)
    let g := cubicDefectGap68 n Be ce De ee
    0 < g ∧
    Be.natDegree ≤ 3 * n - g ∧
    ce.natDegree ≤ 4 * n - g ∧
    De.natDegree ≤ 5 * n - g ∧
    ee.natDegree ≤ 6 * n - g ∧
    (Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0 ∨
      De.coeff (5 * n - g) ≠ 0 ∨ ee.coeff (6 * n - g) ≠ 0) := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  have hdrop := maximalExpandedIntegratedPolynomialLowerSystem_degreeDrop68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have hn : 0 < n := by simpa only [n] using
    (maximalExpandedIntegratedPolynomialLowerSystem_cubicCore68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys).1
  have hnotall : ¬ (Be = 0 ∧ ce = 0 ∧ De = 0 ∧ ee = 0) := by
    rintro ⟨hBe, hce, hDe, hee⟩
    have hB0 : B = 0 := (expand_eq_zero (R := k) (p := 60) (by norm_num)).mp
      (by simpa only [Be] using hBe)
    have hD0 : D = 0 := (expand_eq_zero (R := k) (p := 60) (by norm_num)).mp
      (by simpa only [De] using hDe)
    have hc0 : cubicCDefectPolynomial68 A C0 = 0 :=
      (expand_eq_zero (R := k) (p := 60) (by norm_num)).mp (by
        rw [← expand_cubicCDefectPolynomial68]
        simpa only [Ae, Ce, ce] using hce)
    have he0 : cubicEDefectPolynomial68 A C0 E = 0 :=
      (expand_eq_zero (R := k) (p := 60) (by norm_num)).mp (by
        rw [← expand_cubicEDefectPolynomial68]
        simpa only [Ae, Ce, Ee, ee] using hee)
    have hC0 : C0 = (1 / 3 : k) • A ^ 2 := by
      rw [cubicCDefectPolynomial68_reconstruct A C0, hc0]
      simp
    have hE0 : E = (1 / 27 : k) • A ^ 3 := by
      rw [cubicEDefectPolynomial68_reconstruct A C0 E, he0, hC0]
      rw [mul_smul_comm (1 / 3 : k) A (A ^ 2)]
      simp only [add_zero, smul_smul]
      norm_num
      have hA3 : A * A ^ 2 = A ^ 3 := by ring
      rw [hA3]
      module
    have hApos : 0 < A.natDegree := by
      have hAdegree : Ae.natDegree = 2 * n := by simpa only [n, Ae] using hdrop.1
      simp only [Ae, natDegree_expand] at hAdegree
      omega
    exact exactCubicIntegratedPolynomialLowerSystem_impossible68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hApos hsys hB0 hC0 hD0 hE0
  have hBdeg : Be.natDegree < 3 * n := by simpa only [n, Be] using hdrop.2.1
  have hcdeg : ce.natDegree < 4 * n := by
    simpa only [n, Ae, Ce, ce] using hdrop.2.2.1
  have hDdeg : De.natDegree < 5 * n := by
    simpa only [n, De] using hdrop.2.2.2.1
  have hedeg : ee.natDegree < 6 * n := by
    simpa only [n, Ae, Ce, Ee, ee] using hdrop.2.2.2.2
  have hbounds := cubicDefectGap68_degreeBounds n Be ce De ee
    hBdeg hcdeg hDdeg hedeg
  have hpos : 0 < g := by
    exact cubicDefectGap68_pos n Be ce De ee hBdeg hcdeg hDdeg hedeg
  exact ⟨hpos, hbounds.1, hbounds.2.1, hbounds.2.2.1,
    hbounds.2.2.2, cubicDefectGap68_boundary_attained n Be ce De ee
      hBdeg hcdeg hDdeg hedeg hnotall⟩

end SecondaryRadius68

#print axioms polynomialGap68_pos
#print axioms cubicDefectGap68_pos
#print axioms cubicDefectGap68_degreeBounds
#print axioms cubicDefectGap68_boundary_attained
#print axioms expand_cubicCDefectPolynomial68
#print axioms expand_cubicEDefectPolynomial68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_secondaryRadius68

end Max11DegreeRoutes
