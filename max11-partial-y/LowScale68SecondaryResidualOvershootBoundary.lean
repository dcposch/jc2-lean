import LowScale68SecondaryResidualDoubleLoadWallCanonical

/-! # Canonical residual overshoot on the wall `n = 3g`, `h > 2g`

The tracked overshoot extraction needs `n < 3g` because residual `B^3`
lives at `9n-3g`, and `9n-3g < 8n` iff `n < 3g`.  On `n = 3g` that
term ties the Jacobian load `l A^4` at degree `8n`.  Overshoot
`n < g+h` (equivalently `h > 2g`) still drops `Be` and `cd` strictly
below `8n`, so the I4 coefficient is the mixed two-term form
`(35/1728) l a^4 - (8/27) b^3`.  I3 at `9n` is load-free and reduces
to `-b^2 c`.  The remaining fibre `b ≠ 0`, `c = 0` is killed by the
tracked residual-double row-two coefficient.  Thus `l = 0`, and the
load-zero endgame closes `2g < n`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Chamber arithmetic -/

theorem residualOvershootBoundary_twoGap
    (n g : ℕ) (hg : 0 < g) (hwall : 3 * g = n) : 2 * g < n := by
  omega

theorem residualOvershootBoundary_hover_iff
    (n g h : ℕ) (hwall : 3 * g = n) : n < g + h ↔ 2 * g < h := by
  omega

theorem residualOvershootBoundary_gt_twoGap
    (n g h : ℕ) (hwall : 3 * g = n) (hover : n < g + h) : 2 * g < h :=
  (residualOvershootBoundary_hover_iff n g h hwall).mp hover

theorem residualOvershootBoundary_gap_lt
    (n g h : ℕ) (hg : 0 < g) (hwall : 3 * g = n) (hover : n < g + h) :
    g < h := by
  have : 2 * g < h := residualOvershootBoundary_gt_twoGap n g h hwall hover
  omega

theorem residualOvershootBoundary_fourIndex
    (n g : ℕ) (hwall : 3 * g = n) : 9 * n - 3 * g = 8 * n := by
  omega

theorem residualOvershootBoundary_B3Index
    (n g : ℕ) (hwall : 3 * g = n) : 3 * (3 * n - g) = 8 * n := by
  omega

theorem residualOvershootBoundary_threeIndex
    (n g : ℕ) (hwall : 3 * g = n) : 10 * n - 3 * g = 9 * n := by
  omega

theorem residualOvershootBoundary_B2cIndex
    (n g : ℕ) (hwall : 3 * g = n) :
    2 * (3 * n - g) + (4 * n - g) = 9 * n := by
  omega

theorem residualOvershootBoundary_Be_lt_eightRadius
    (n g h : ℕ) (hg : 0 < g) (hwall : 3 * g = n) (hover : n < g + h) :
    (3 * n - g) + (6 * n - h) < 8 * n := by
  have : 2 * g < h := residualOvershootBoundary_gt_twoGap n g h hwall hover
  omega

theorem residualOvershootBoundary_cd_lt_eightRadius
    (n g h : ℕ) (hg : 0 < g) (hwall : 3 * g = n) (hover : n < g + h) :
    (4 * n - g) + (5 * n - h) < 8 * n := by
  have : 2 * g < h := residualOvershootBoundary_gt_twoGap n g h hwall hover
  omega

theorem residualOvershootBoundary_ABd_lt_nineRadius
    (n g h : ℕ) (hg : 0 < g) (hwall : 3 * g = n) (hover : n < g + h) :
    2 * n + (3 * n - g) + (5 * n - h) < 9 * n := by
  have : 2 * g < h := residualOvershootBoundary_gt_twoGap n g h hwall hover
  omega

theorem residualOvershootBoundary_ce_lt_nineRadius
    (n g h : ℕ) (hg : 0 < g) (hwall : 3 * g = n) (hover : n < g + h) :
    (4 * n - g) + (6 * n - h) < 9 * n := by
  have : 2 * g < h := residualOvershootBoundary_gt_twoGap n g h hwall hover
  omega

theorem residualOvershootBoundary_d2_lt_nineRadius
    (n g h : ℕ) (hg : 0 < g) (hwall : 3 * g = n) (hover : n < g + h) :
    2 * (5 * n - h) < 9 * n := by
  have : 2 * g < h := residualOvershootBoundary_gt_twoGap n g h hwall hover
  omega

theorem residualOvershootBoundary_doubleDBound
    {d : k[X]} (n g h : ℕ) (hg : 0 < g)
    (hwall : 3 * g = n) (hover : n < g + h)
    (hd : d.natDegree ≤ 5 * n - h) :
    d.natDegree ≤ 5 * n - 2 * g := by
  have : 2 * g < h := residualOvershootBoundary_gt_twoGap n g h hwall hover
  exact hd.trans (by omega)

theorem residualOvershootBoundary_doubleEBound
    {e : k[X]} (n g h : ℕ) (hg : 0 < g)
    (hwall : 3 * g = n) (hover : n < g + h)
    (he : e.natDegree ≤ 6 * n - h) :
    e.natDegree ≤ 6 * n - 2 * g := by
  have : 2 * g < h := residualOvershootBoundary_gt_twoGap n g h hwall hover
  exact he.trans (by omega)

theorem residualOvershootBoundary_d_coeff_double_eq_zero
    {d : k[X]} (n g h : ℕ) (hg : 0 < g)
    (hwall : 3 * g = n) (hover : n < g + h)
    (hd : d.natDegree ≤ 5 * n - h) :
    d.coeff (5 * n - 2 * g) = 0 := by
  have : 2 * g < h := residualOvershootBoundary_gt_twoGap n g h hwall hover
  exact coeff_eq_zero_of_natDegree_lt (hd.trans_lt (by omega))

theorem residualOvershootBoundary_e_coeff_double_eq_zero
    {e : k[X]} (n g h : ℕ) (hg : 0 < g)
    (hwall : 3 * g = n) (hover : n < g + h)
    (he : e.natDegree ≤ 6 * n - h) :
    e.coeff (6 * n - 2 * g) = 0 := by
  have : 2 * g < h := residualOvershootBoundary_gt_twoGap n g h hwall hover
  exact coeff_eq_zero_of_natDegree_lt (he.trans_lt (by omega))

/-! ## Residual I4 on the wall: `B^3` ties, `Be` and `cd` drop -/

theorem secondaryResidualInvariantFourPolynomial68_Be_degree_lt_eightRadius_of_overshootBoundary
    (B e : k[X]) (n g h : ℕ) (hg : 0 < g)
    (hwall : 3 * g = n) (hover : n < g + h)
    (hB : B.natDegree ≤ 3 * n - g)
    (he : e.natDegree ≤ 6 * n - h) :
    (B * e).natDegree < 8 * n :=
  natDegree_mul_le.trans_lt <|
    (Nat.add_le_add hB he).trans_lt
      (residualOvershootBoundary_Be_lt_eightRadius n g h hg hwall hover)

theorem secondaryResidualInvariantFourPolynomial68_cd_degree_lt_eightRadius_of_overshootBoundary
    (c d : k[X]) (n g h : ℕ) (hg : 0 < g)
    (hwall : 3 * g = n) (hover : n < g + h)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h) :
    (c * d).natDegree < 8 * n :=
  natDegree_mul_le.trans_lt <|
    (Nat.add_le_add hc hd).trans_lt
      (residualOvershootBoundary_cd_lt_eightRadius n g h hg hwall hover)

set_option maxHeartbeats 2000000 in
/-- On `n = 3g` and `n < g+h`, residual I4 at `8n` is exactly the tied
`B^3` coefficient.  The original `degree_lt_eightRadius` fails here
because `9n-3g = 8n`. -/
theorem secondaryResidualInvariantFourPolynomial68_coeff_eightRadius_of_overshootBoundary
    (B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hwall : 3 * g = n) (hover : n < g + h)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (secondaryResidualInvariantFourPolynomial68 B c d e).coeff (8 * n) =
      (-8 / 27 : k) * B.coeff (3 * n - g) ^ 3 := by
  have hB3 := coeff_pow_at_bound68 B (3 * n - g) 3 hB
  have hB3i : 3 * (3 * n - g) = 8 * n :=
    residualOvershootBoundary_B3Index n g hwall
  rw [hB3i] at hB3
  have hBe : (B * e).natDegree < 8 * n :=
    secondaryResidualInvariantFourPolynomial68_Be_degree_lt_eightRadius_of_overshootBoundary
      B e n g h hg hwall hover hB he
  have hcd : (c * d).natDegree < 8 * n :=
    secondaryResidualInvariantFourPolynomial68_cd_degree_lt_eightRadius_of_overshootBoundary
      c d n g h hg hwall hover hc hd
  simp only [secondaryResidualInvariantFourPolynomial68, coeff_add,
    coeff_smul, smul_eq_mul]
  rw [hB3, coeff_eq_zero_of_natDegree_lt hBe,
    coeff_eq_zero_of_natDegree_lt hcd]
  ring

set_option maxHeartbeats 2000000 in
theorem cubicFirstIntegralFourPolynomial68_coeff_eightRadius_of_overshootBoundary
    (l beta gamma delta epsilon zeta : k) (A B c d e : k[X])
    (n g h : ℕ) (hn : 0 < n) (hg : 0 < g)
    (hwall : 3 * g = n) (hover : n < g + h)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (cubicFirstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff (8 * n) =
      (35 / 1728 : k) * l * A.coeff (2 * n) ^ 4 +
        (-8 / 27 : k) * B.coeff (3 * n - g) ^ 3 := by
  let D := (1 / 3 : k) • (A * B) + d
  have hD : D.natDegree ≤ 5 * n - g := by
    simp only [D]
    compute_degree
    omega
  have hgh : g < h := residualOvershootBoundary_gap_lt n g h hg hwall hover
  have he' : e.natDegree ≤ 6 * n - g := he.trans (by omega)
  have hhom :
      (secondaryResidualInvariantFourPolynomial68 B c d e).coeff (8 * n) =
        (-8 / 27 : k) * B.coeff (3 * n - g) ^ 3 :=
    secondaryResidualInvariantFourPolynomial68_coeff_eightRadius_of_overshootBoundary
      B c d e n g h hg hwall hover hB hc hd he
  have hload := secondaryLoadInvariantFourPolynomial68_coeff_eightRadius
    l beta gamma delta epsilon zeta A B c D e n g hn hg hA hB hc hD he'
  rw [cubicFirstIntegralFourPolynomial68_secondaryLoadSplit, coeff_add,
    show cubicFirstIntegralFourPolynomial68 0 0 0 0 0 0 A B c D e =
        secondaryResidualInvariantFourPolynomial68 B c d e by
      simpa only [D] using
        cubicFirstIntegralFourPolynomial68_residualCoordinates A B c d e,
    hhom, hload]
  ring

/-! ## Residual I3 on the wall: `B^2 c` ties, remaining terms drop -/

theorem secondaryResidualInvariantThreePolynomial68_ABd_degree_lt_nineRadius_of_overshootBoundary
    (A B d : k[X]) (n g h : ℕ) (hg : 0 < g)
    (hwall : 3 * g = n) (hover : n < g + h)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hd : d.natDegree ≤ 5 * n - h) :
    (A * B * d).natDegree < 9 * n :=
  calc
    (A * B * d).natDegree ≤ (A * B).natDegree + d.natDegree :=
      natDegree_mul_le
    _ ≤ A.natDegree + B.natDegree + d.natDegree :=
      Nat.add_le_add natDegree_mul_le le_rfl
    _ ≤ 2 * n + (3 * n - g) + (5 * n - h) :=
      Nat.add_le_add (Nat.add_le_add hA hB) hd
    _ < 9 * n :=
      residualOvershootBoundary_ABd_lt_nineRadius n g h hg hwall hover

theorem secondaryResidualInvariantThreePolynomial68_ce_degree_lt_nineRadius_of_overshootBoundary
    (c e : k[X]) (n g h : ℕ) (hg : 0 < g)
    (hwall : 3 * g = n) (hover : n < g + h)
    (hc : c.natDegree ≤ 4 * n - g)
    (he : e.natDegree ≤ 6 * n - h) :
    (c * e).natDegree < 9 * n :=
  natDegree_mul_le.trans_lt <|
    (Nat.add_le_add hc he).trans_lt
      (residualOvershootBoundary_ce_lt_nineRadius n g h hg hwall hover)

theorem secondaryResidualInvariantThreePolynomial68_d2_degree_lt_nineRadius_of_overshootBoundary
    (d : k[X]) (n g h : ℕ) (hg : 0 < g)
    (hwall : 3 * g = n) (hover : n < g + h)
    (hd : d.natDegree ≤ 5 * n - h) :
    (d ^ 2).natDegree < 9 * n :=
  (natDegree_pow_le.trans (Nat.mul_le_mul_left 2 hd)).trans_lt
    (residualOvershootBoundary_d2_lt_nineRadius n g h hg hwall hover)

set_option maxHeartbeats 2000000 in
theorem secondaryResidualInvariantThreePolynomial68_coeff_nineRadius_of_overshootBoundary
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hwall : 3 * g = n) (hover : n < g + h)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (secondaryResidualInvariantThreePolynomial68 A B c d e).coeff (9 * n) =
      (-8 / 9 : k) * B.coeff (3 * n - g) ^ 2 * c.coeff (4 * n - g) := by
  have hB2 := coeff_pow_at_bound68 B (3 * n - g) 2 hB
  have hB2deg : (B ^ 2).natDegree ≤ 2 * (3 * n - g) :=
    natDegree_pow_le.trans (Nat.mul_le_mul_left 2 hB)
  have hB2c := coeff_mul_at_bounds68 (B ^ 2) c (2 * (3 * n - g))
    (4 * n - g) hB2deg hc
  have hB2ci : 2 * (3 * n - g) + (4 * n - g) = 9 * n :=
    residualOvershootBoundary_B2cIndex n g hwall
  rw [hB2ci, hB2] at hB2c
  have hABd :
      (A * B * d).natDegree < 9 * n :=
    secondaryResidualInvariantThreePolynomial68_ABd_degree_lt_nineRadius_of_overshootBoundary
      A B d n g h hg hwall hover hA hB hd
  have hce :
      (c * e).natDegree < 9 * n :=
    secondaryResidualInvariantThreePolynomial68_ce_degree_lt_nineRadius_of_overshootBoundary
      c e n g h hg hwall hover hc he
  have hd2 :
      (d ^ 2).natDegree < 9 * n :=
    secondaryResidualInvariantThreePolynomial68_d2_degree_lt_nineRadius_of_overshootBoundary
      d n g h hg hwall hover hd
  simp only [secondaryResidualInvariantThreePolynomial68, coeff_add,
    coeff_sub, coeff_smul, smul_eq_mul]
  rw [coeff_eq_zero_of_natDegree_lt hABd,
    coeff_eq_zero_of_natDegree_lt hce,
    coeff_eq_zero_of_natDegree_lt hd2, hB2c]
  ring

set_option maxHeartbeats 2000000 in
theorem cubicFirstIntegralThreePolynomial68_coeff_nineRadius_of_overshootBoundary
    (l beta gamma delta epsilon zeta : k) (A B c d e : k[X])
    (n g h : ℕ) (hg : 0 < g)
    (hwall : 3 * g = n) (hover : n < g + h)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (cubicFirstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff (9 * n) =
      (-8 / 9 : k) * B.coeff (3 * n - g) ^ 2 * c.coeff (4 * n - g) := by
  let D := (1 / 3 : k) • (A * B) + d
  have hD : D.natDegree ≤ 5 * n - g := by
    simp only [D]
    compute_degree
    omega
  have hsmall : 2 * g < n := residualOvershootBoundary_twoGap n g hg hwall
  have he' : e.natDegree ≤ 6 * n - 2 * g :=
    residualOvershootBoundary_doubleEBound (e := e) n g h hg hwall hover he
  have hload := secondaryLoadInvariantThreePolynomial68_degree_lt_double_of_twoGap
    l beta gamma delta epsilon zeta A B c D e n g hg hsmall
    hA hB hc hD he'
  have hidx : 10 * n - 3 * g = 9 * n :=
    residualOvershootBoundary_threeIndex n g hwall
  have hhom :=
    secondaryResidualInvariantThreePolynomial68_coeff_nineRadius_of_overshootBoundary
      A B c d e n g h hg hwall hover hA hB hc hd he
  rw [cubicFirstIntegralThreePolynomial68_secondaryLoadSplit, coeff_add,
    show cubicFirstIntegralThreePolynomial68 0 0 0 0 0 0 A B c D e =
        secondaryResidualInvariantThreePolynomial68 A B c d e by
      simpa only [D] using
        cubicFirstIntegralThreePolynomial68_residualCoordinates A B c d e,
    hhom, ← hidx, coeff_eq_zero_of_natDegree_lt hload, add_zero]

/-! ## Polynomial-level `l = 0` -/

set_option maxHeartbeats 4000000 in
theorem cubicFirstIntegralFourPolynomial68_imp_loadL_eq_zero_of_overshootBoundary
    (l alpha beta gamma delta epsilon zeta eta i4 i3 : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g)
    (hwall : 3 * g = n) (hover : n < g + h)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (ha : A.coeff (2 * n) ≠ 0)
    (hi4 : cubicFirstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hi3 : cubicFirstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e = C i3)
    (hrowTwo : lowerRowTwoPolynomial68
      (integratedSPolynomial68 l alpha beta delta A B
        ((1 / 3 : k) • A ^ 2 + c) ((1 / 3 : k) • (A * B) + d))
      (integratedTPolynomial68 l alpha beta gamma epsilon A B
        ((1 / 3 : k) • A ^ 2 + c) ((1 / 3 : k) • (A * B) + d)
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      (integratedUPolynomial68 l alpha beta gamma delta zeta A B
        ((1 / 3 : k) • A ^ 2 + c) ((1 / 3 : k) • (A * B) + d)
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta A B
        ((1 / 3 : k) • A ^ 2 + c) ((1 / 3 : k) • (A * B) + d)
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      B ((1 / 3 : k) • A ^ 2 + c) ((1 / 3 : k) • (A * B) + d)
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e) = 0) :
    l = 0 := by
  let a := A.coeff (2 * n)
  let b := B.coeff (3 * n - g)
  let ctop := c.coeff (4 * n - g)
  have hz4 := congrArg (fun p : k[X] => p.coeff (8 * n)) hi4
  rw [cubicFirstIntegralFourPolynomial68_coeff_eightRadius_of_overshootBoundary
    l beta gamma delta epsilon zeta A B c d e n g h hn hg hwall hover
    hA hB hc hd he] at hz4
  have hindex4 : 8 * n ≠ 0 := by omega
  simp only [coeff_C, ite_eq_right hindex4] at hz4
  have hz4' :
      (35 / 1728 : k) * l * a ^ 4 + (-8 / 27 : k) * b ^ 3 = 0 := by
    simpa [a, b] using hz4
  have hz3 := congrArg (fun p : k[X] => p.coeff (9 * n)) hi3
  rw [cubicFirstIntegralThreePolynomial68_coeff_nineRadius_of_overshootBoundary
    l beta gamma delta epsilon zeta A B c d e n g h hg hwall hover
    hA hB hc hd he] at hz3
  have hindex3 : 9 * n ≠ 0 := by omega
  simp only [coeff_C, ite_eq_right hindex3] at hz3
  have hz3' : (-8 / 9 : k) * b ^ 2 * ctop = 0 := by
    simpa [b, ctop] using hz3
  have hb2c : b ^ 2 * ctop = 0 := by
    have hprod : (-8 / 9 : k) * (b ^ 2 * ctop) = 0 := by
      linear_combination hz3'
    exact (mul_eq_zero.mp hprod).resolve_left (by norm_num)
  by_cases hb : b = 0
  · have hprod : (35 / 1728 : k) * (l * a ^ 4) = 0 := by
      have hz4b := hz4'
      simp only [hb, zero_pow (Nat.succ_ne_zero 2), mul_zero, add_zero] at hz4b
      linear_combination hz4b
    have hla : l * a ^ 4 = 0 :=
      (mul_eq_zero.mp hprod).resolve_left (by norm_num)
    exact (mul_eq_zero.mp hla).resolve_right (pow_ne_zero 4 ha)
  · have hc0 : ctop = 0 :=
      (mul_eq_zero.mp hb2c).resolve_left (pow_ne_zero 2 hb)
    have hd' : d.natDegree ≤ 5 * n - 2 * g :=
      residualOvershootBoundary_doubleDBound (d := d) n g h hg hwall hover hd
    have he' : e.natDegree ≤ 6 * n - 2 * g :=
      residualOvershootBoundary_doubleEBound (e := e) n g h hg hwall hover he
    have hdt : d.coeff (5 * n - 2 * g) = 0 :=
      residualOvershootBoundary_d_coeff_double_eq_zero (d := d) n g h hg
        hwall hover hd
    have het : e.coeff (6 * n - 2 * g) = 0 :=
      residualOvershootBoundary_e_coeff_double_eq_zero (e := e) n g h hg
        hwall hover he
    have htwo := congrArg (fun p : k[X] => p.coeff (10 * n - 1)) hrowTwo
    rw [integratedLowerRowTwoPolynomial68_coeff_residualDoubleLoadWall
      l alpha beta gamma delta epsilon zeta eta A B c d e n g
      hn hg hwall hA hB hc hd' he'] at htwo
    simp only [coeff_zero] at htwo
    have hncast : (n : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
    have hnum : residualDoubleLoadWallTwoNumerator68 a b ctop
        (d.coeff (5 * n - 2 * g)) (e.coeff (6 * n - 2 * g)) l = 0 := by
      simp only [residualDoubleLoadWallTwoScalar68] at htwo
      have hdiv := div_eq_zero_iff.mp htwo
      have hprod : (n : k) *
          residualDoubleLoadWallTwoNumerator68 a b ctop
            (d.coeff (5 * n - 2 * g)) (e.coeff (6 * n - 2 * g)) l = 0 :=
        hdiv.resolve_right (by norm_num)
      exact (mul_eq_zero.mp hprod).resolve_left hncast
    have hnum' : (35 : k) * l * a ^ 5 + (96 : k) * a * b ^ 3 = 0 := by
      simp only [residualDoubleLoadWallTwoNumerator68, hc0, hdt, het,
        zero_pow (Nat.succ_ne_zero 1), mul_zero, add_zero, sub_zero] at hnum
      exact hnum
    have hfour : (35 : k) * l * a ^ 4 - (512 : k) * b ^ 3 = 0 := by
      have := congrArg (fun x => (1728 : k) * x) hz4'
      simp only [mul_zero] at this
      convert this using 1
      ring
    have hcomb : (608 : k) * a * b ^ 3 = 0 := by
      linear_combination hnum' - a * hfour
    have h608a : (608 : k) * a ≠ 0 :=
      mul_ne_zero (by norm_num) ha
    have hb3 : b ^ 3 = 0 := (mul_eq_zero.mp hcomb).resolve_left h608a
    exact False.elim (pow_ne_zero 3 hb hb3)

/-! ## Canonical expanded wrapper -/

set_option maxHeartbeats 4000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_residualOvershootBoundaryWall_loadL_eq_zero68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hwall :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      n = 3 * g)
    (hover :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      let d := secondaryDDefectPolynomial68 Ae Be De
      let h := secondaryResidualGap68 n d ee
      n < g + h) :
    l = 0 := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  let d := secondaryDDefectPolynomial68 Ae Be De
  let h := secondaryResidualGap68 n d ee
  change n = 3 * g at hwall
  change n < g + h at hover
  have hwall' : 3 * g = n := hwall.symm
  have hcore := maximalExpandedIntegratedPolynomialLowerSystem_cubicCore68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have hdrop := maximalExpandedIntegratedPolynomialLowerSystem_degreeDrop68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have hsecondary :=
    maximalExpandedIntegratedPolynomialLowerSystem_secondaryRadius68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  have hn : 0 < n := by simpa only [n] using hcore.1
  have hg : 0 < g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.1
  have hsmall : 2 * g < n := residualOvershootBoundary_twoGap n g hg hwall'
  have hA : Ae.natDegree ≤ 2 * n := by
    have hAe : Ae.natDegree = 2 * n := by
      simpa only [n, Ae, Be, Ce, De, Ee] using hdrop.1
    omega
  have hB : Be.natDegree ≤ 3 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.2.1
  have hc : ce.natDegree ≤ 4 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
      hsecondary.2.2.1
  have ha : Ae.coeff (2 * n) ≠ 0 := by
    simpa only [n, Ae] using hcore.2.2.2.2.2
  have hdrops :=
    maximalExpandedIntegratedPolynomialLowerSystem_secondaryResidualDegreeDrops68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsmall)
  change d.natDegree < 5 * n - g ∧ ee.natDegree < 6 * n - g at hdrops
  have hdbase : d.natDegree < 5 * n := by omega
  have hebase : ee.natDegree < 6 * n := by omega
  have hbounds : d.natDegree ≤ 5 * n - h ∧
      ee.natDegree ≤ 6 * n - h := by
    simpa only [h] using secondaryResidualGap68_degreeBounds n d ee
      hdbase hebase
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec :
      Ee = (1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using
      cubicEDefectPolynomial68_eq_cubicCoordinates Ae Ce Ee
  have hDrec : De = (1 / 3 : k) • (Ae * Be) + d := by
    simpa only [d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
  obtain ⟨i4, hi4⟩ := hsys.firstFour
  obtain ⟨i3, hi3⟩ := hsys.firstThree
  have hi4e : firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i4 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_firstIntegralFourPolynomial68_of_eq
        l beta gamma delta epsilon zeta i4 A B C0 D E hi4
  have hi3e : firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i3 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_firstIntegralThreePolynomial68_of_eq
        l beta gamma delta epsilon zeta i3 A B C0 D E hi3
  have hi4c := hi4e
  rw [hCrec, hErec, firstIntegralFourPolynomial68_cubicCoordinates,
    hDrec] at hi4c
  have hi3c := hi3e
  rw [hCrec, hErec, firstIntegralThreePolynomial68_cubicCoordinates,
    hDrec] at hi3c
  have h2e : lowerRowTwoPolynomial68
      (integratedSPolynomial68 l alpha beta delta Ae Be Ce De)
      (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) Be Ce De Ee = 0 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_lowerRowTwoPolynomial68_of_system
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
  have hrowTwo :
      lowerRowTwoPolynomial68
        (integratedSPolynomial68 l alpha beta delta Ae Be
          ((1 / 3 : k) • Ae ^ 2 + ce) ((1 / 3 : k) • (Ae * Be) + d))
        (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be
          ((1 / 3 : k) • Ae ^ 2 + ce) ((1 / 3 : k) • (Ae * Be) + d)
          ((1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee))
        (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be
          ((1 / 3 : k) • Ae ^ 2 + ce) ((1 / 3 : k) • (Ae * Be) + d)
          ((1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee))
        (integratedVPolynomial68 l alpha beta gamma delta epsilon eta Ae Be
          ((1 / 3 : k) • Ae ^ 2 + ce) ((1 / 3 : k) • (Ae * Be) + d)
          ((1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee))
        Be ((1 / 3 : k) • Ae ^ 2 + ce) ((1 / 3 : k) • (Ae * Be) + d)
          ((1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee) = 0 := by
    simpa only [← hCrec, ← hDrec, ← hErec] using h2e
  exact cubicFirstIntegralFourPolynomial68_imp_loadL_eq_zero_of_overshootBoundary
    l alpha beta gamma delta epsilon zeta eta i4 i3
    Ae Be ce d ee n g h hn hg hwall' hover hA hB hc
    hbounds.1 hbounds.2 ha hi4c hi3c hrowTwo

set_option maxHeartbeats 4000000 in
/-- The residual overshoot wall `n = 3g` and `n < g+h` (equivalently
`h > 2g`) is empty on a canonical expanded source: mixed I4/I3 plus the
tracked residual-double row two force `l = 0`, and `g > 0` yields
`2g < n`, so the residual load-zero endgame applies. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_residualOvershootBoundaryWall_impossible68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hwall :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      n = 3 * g)
    (hover :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      let d := secondaryDDefectPolynomial68 Ae Be De
      let h := secondaryResidualGap68 n d ee
      n < g + h) :
    False := by
  have hl0 :=
    maximalExpandedIntegratedPolynomialLowerSystem_residualOvershootBoundaryWall_loadL_eq_zero68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys hwall hover
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  have hg : 0 < g := by
    have hsecondary :=
      maximalExpandedIntegratedPolynomialLowerSystem_secondaryRadius68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.1
  have hwall' : n = 3 * g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall
  have hsmall : 2 * g < n := by
    rw [hwall']
    omega
  exact
    maximalExpandedIntegratedPolynomialLowerSystem_secondaryResidualLoadZero_impossible68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys hl0 (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsmall)

#print axioms residualOvershootBoundary_twoGap
#print axioms secondaryResidualInvariantFourPolynomial68_coeff_eightRadius_of_overshootBoundary
#print axioms cubicFirstIntegralFourPolynomial68_coeff_eightRadius_of_overshootBoundary
#print axioms cubicFirstIntegralThreePolynomial68_coeff_nineRadius_of_overshootBoundary
#print axioms cubicFirstIntegralFourPolynomial68_imp_loadL_eq_zero_of_overshootBoundary
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_residualOvershootBoundaryWall_loadL_eq_zero68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_residualOvershootBoundaryWall_impossible68

end Max11DegreeRoutes
