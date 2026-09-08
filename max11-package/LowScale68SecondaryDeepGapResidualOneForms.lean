import LowScale68SecondaryDeepGapCascade

/-! # Residual I4/I3 one-forms on `n < 2g` and `2g < 3n`

After the deep-gap first face and residual drops, the selected gap
`h := secondaryResidualGap68 n d ee` is a middle window `g < h < 2g` or a
double window `h ≥ 2g`.  I3 remains the ordinary residual face.  I4 keeps
the load `(5/72) beta A^3` at `6n`, which may lie below, on, or above the
homogeneous residual index.  This module extracts the exact faces in every
case, including the two mixed walls, and packages them as a canonical
selector.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section DeepGapResidualOneForms68

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Residual I4/I3 scalar system on the deep-gap chamber, including the
`beta A^3` load at `6n`.  Middle equations use residual tops at gap `h`;
double equations use tops at gap `2g`. -/
structure DeepGapResidualInvariants68
    (n g h : ℕ) (a b c dh eh d2 e2 beta : k) : Prop where
  three_middle :
    h < 2 * g → -a * b * dh + 3 * c * eh = 0
  four_middle_below :
    h < 2 * g → g + h < 3 * n → b * eh + c * dh = 0
  four_middle_mixed :
    h < 2 * g → g + h = 3 * n →
      (8 / 3 : k) * (b * eh + c * dh) +
        (5 / 72 : k) * beta * a ^ 3 = 0
  four_middle_above :
    h < 2 * g → 3 * n < g + h →
      beta = 0 ∧ b * eh + c * dh = 0
  three_double :
    ¬ h < 2 * g →
      -a * b * d2 - b ^ 2 * c + 3 * c * e2 = 0
  four_double_below :
    ¬ h < 2 * g → g < n →
      -b ^ 3 + 9 * b * e2 + 9 * c * d2 = 0
  four_double_mixed :
    ¬ h < 2 * g → g = n →
      (8 / 27 : k) * (-b ^ 3 + 9 * b * e2 + 9 * c * d2) +
        (5 / 72 : k) * beta * a ^ 3 = 0
  four_double_above :
    ¬ h < 2 * g → n < g →
      beta = 0 ∧ -b ^ 3 + 9 * b * e2 + 9 * c * d2 = 0

/-! ## Chamber arithmetic -/

theorem deepGap_middle_sum_lt_three_of_gap_le_radius
    (n g h : ℕ) (hg_le : g ≤ n) (hh : h < 2 * g) :
    g + h < 3 * n := by
  omega

theorem deepGap_three_sub_gap_of_strict
    (n g : ℕ) (hrel : 2 * g < 3 * n) (hg_lt : n < g) :
    g < 3 * n - g ∧ 3 * n - g < 2 * g := by
  omega

/-! ## Residual gap and support after the deep-gap first face -/

theorem maximalExpandedIntegratedPolynomialLowerSystem_deepGapBoundary68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hchamber :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      n < 2 * g ∧ 2 * g < 3 * n) :
    let n := weightedRadius68 A B C0 D E
    let Ae := expand k 60 A
    let Be := expand k 60 B
    let Ce := expand k 60 C0
    let ce := cubicCDefectPolynomial68 Ae Ce
    let De := expand k 60 D
    let Ee := expand k 60 E
    let ee := cubicEDefectPolynomial68 Ae Ce Ee
    let g := cubicDefectGap68 n Be ce De ee
    l = 0 ∧ ee.coeff (6 * n - g) = 0 ∧
      Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
        3 * De.coeff (5 * n - g) ∧
      (Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0) := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  change n < 2 * g ∧ 2 * g < 3 * n at hchamber
  change l = 0 ∧ ee.coeff (6 * n - g) = 0 ∧
    Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
      3 * De.coeff (5 * n - g) ∧
    (Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0)
  have hclass :=
    maximalExpandedIntegratedPolynomialLowerSystem_deepGapClassified68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hchamber)
  change l = 0 ∧ ee.coeff (6 * n - g) = 0 ∧
    Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
      3 * De.coeff (5 * n - g) at hclass
  have hsecondary :=
    maximalExpandedIntegratedPolynomialLowerSystem_secondaryRadius68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  have hattained :
      Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0 ∨
        De.coeff (5 * n - g) ≠ 0 ∨ ee.coeff (6 * n - g) ≠ 0 := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
      hsecondary.2.2.2.2.2
  refine ⟨hclass.1, hclass.2.1, hclass.2.2, ?_⟩
  rcases hattained with hb | hc | hd | he
  · exact Or.inl hb
  · exact Or.inr hc
  · left
    intro hb0
    have hrel := hclass.2.2
    rw [hb0, mul_zero] at hrel
    have hd0 : De.coeff (5 * n - g) = 0 :=
      (mul_eq_zero.mp hrel.symm).resolve_left (by norm_num)
    exact hd hd0
  · exact (he hclass.2.1).elim

theorem maximalExpandedIntegratedPolynomialLowerSystem_deepGapResidualGap68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hchamber :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      n < 2 * g ∧ 2 * g < 3 * n) :
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
    l = 0 ∧
      (Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0) ∧
      d.natDegree < 5 * n - g ∧ ee.natDegree < 6 * n - g ∧
      g < h ∧
      d.natDegree ≤ 5 * n - h ∧ ee.natDegree ≤ 6 * n - h := by
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
  change n < 2 * g ∧ 2 * g < 3 * n at hchamber
  change l = 0 ∧
    (Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0) ∧
    d.natDegree < 5 * n - g ∧ ee.natDegree < 6 * n - g ∧
    g < h ∧
    d.natDegree ≤ 5 * n - h ∧ ee.natDegree ≤ 6 * n - h
  have hboundary :=
    maximalExpandedIntegratedPolynomialLowerSystem_deepGapBoundary68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hchamber)
  change l = 0 ∧ ee.coeff (6 * n - g) = 0 ∧
    Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
      3 * De.coeff (5 * n - g) ∧
    (Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0) at hboundary
  have hdrops :=
    maximalExpandedIntegratedPolynomialLowerSystem_deepGapResidualDrops68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hchamber)
  change l = 0 ∧ d.natDegree < 5 * n - g ∧
    ee.natDegree < 6 * n - g at hdrops
  have hgh : g < h := by
    simpa only [h] using secondaryResidualGap68_gt_of_strictDrops n g d ee
      hdrops.2.1 hdrops.2.2
  have hdbase : d.natDegree < 5 * n := by omega
  have hebase : ee.natDegree < 6 * n := by omega
  have hbounds : d.natDegree ≤ 5 * n - h ∧
      ee.natDegree ≤ 6 * n - h := by
    simpa only [h] using secondaryResidualGap68_degreeBounds n d ee
      hdbase hebase
  exact ⟨hboundary.1, hboundary.2.2.2, hdrops.2.1, hdrops.2.2, hgh,
    hbounds⟩

/-! ## Load `(5/72) beta A^3` at `6n` after `l = 0` -/

set_option maxHeartbeats 2000000 in
theorem secondaryLoadInvariantFourPolynomial68_coeff_sixRadius_of_l_eq_zero
    (beta gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g : ℕ) (hn : 0 < n) (hg : 0 < g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (secondaryLoadInvariantFourPolynomial68
      0 beta gamma delta epsilon zeta A B c D e).coeff (6 * n) =
      (5 / 72 * beta : k) * A.coeff (2 * n) ^ 3 := by
  let loadRest := zeta • A + (2 * epsilon : k) • B +
    (1 / 4 * delta : k) • A ^ 2 + (3 * delta : k) • c +
    (4 * gamma : k) • D - (4 / 3 * gamma : k) • (A * B) +
    (5 * beta : k) • e + (5 / 6 * beta : k) • (A * c) -
    (5 / 12 * beta : k) • B ^ 2
  have hloadRest : loadRest.natDegree < 6 * n := by
    simp only [loadRest]
    compute_degree
    omega
  have hA3 := coeff_pow_at_bound68 A (2 * n) 3 hA
  have hi : 3 * (2 * n) = 6 * n := by omega
  rw [hi] at hA3
  have hsplit :
      secondaryLoadInvariantFourPolynomial68
          0 beta gamma delta epsilon zeta A B c D e =
        loadRest + (5 / 72 * beta : k) • A ^ 3 := by
    simp only [loadRest, secondaryLoadInvariantFourPolynomial68,
      zero_mul, mul_zero, zero_smul, smul_zero, add_zero, sub_zero]
  rw [hsplit, coeff_add, coeff_eq_zero_of_natDegree_lt hloadRest, zero_add,
    coeff_smul, hA3, smul_eq_mul]

set_option maxHeartbeats 2000000 in
theorem secondaryLoadInvariantFourPolynomial68_degree_lt_sixRadius_of_l_beta
    (gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g : ℕ) (hn : 0 < n) (hg : 0 < g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (secondaryLoadInvariantFourPolynomial68
      0 0 gamma delta epsilon zeta A B c D e).natDegree < 6 * n := by
  simp only [secondaryLoadInvariantFourPolynomial68, zero_mul, mul_zero,
    zero_smul, smul_zero, add_zero, sub_zero]
  compute_degree
  omega

/-! ## Homogeneous residual coefficients on `2g < 3n` -/

set_option maxHeartbeats 2000000 in
theorem secondaryResidualInvariantFourPolynomial68_coeff_middle_of_deepGap
    (B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g) (hrel : 2 * g < 3 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (secondaryResidualInvariantFourPolynomial68 B c d e).coeff
        (9 * n - g - h) =
      (8 / 3 : k) *
        (B.coeff (3 * n - g) * e.coeff (6 * n - h) +
          c.coeff (4 * n - g) * d.coeff (5 * n - h)) := by
  have hB3 : (B ^ 3).natDegree < 9 * n - g - h := by
    compute_degree
    omega
  have hBe := coeff_mul_at_bounds68 B e (3 * n - g) (6 * n - h) hB he
  have hBei : (3 * n - g) + (6 * n - h) = 9 * n - g - h := by omega
  rw [hBei] at hBe
  have hcd := coeff_mul_at_bounds68 c d (4 * n - g) (5 * n - h) hc hd
  have hcdi : (4 * n - g) + (5 * n - h) = 9 * n - g - h := by omega
  rw [hcdi] at hcd
  simp only [secondaryResidualInvariantFourPolynomial68, coeff_add,
    coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hB3, hBe, hcd]
  ring

set_option maxHeartbeats 2000000 in
theorem secondaryResidualInvariantThreePolynomial68_coeff_middle_of_deepGap
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g) (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (secondaryResidualInvariantThreePolynomial68 A B c d e).coeff
        (10 * n - g - h) =
      (8 / 9 : k) *
        (-(A.coeff (2 * n) * B.coeff (3 * n - g) *
            d.coeff (5 * n - h)) +
          3 * c.coeff (4 * n - g) * e.coeff (6 * n - h)) := by
  have hABd := coeff_mul_mul_at_bounds68 A B d (2 * n)
    (3 * n - g) (5 * n - h) hA hB hd
  have hABdi : 2 * n + (3 * n - g) + (5 * n - h) =
      10 * n - g - h := by omega
  rw [hABdi] at hABd
  have hB2c : (B ^ 2 * c).natDegree < 10 * n - g - h := by
    compute_degree
    omega
  have hce := coeff_mul_at_bounds68 c e (4 * n - g) (6 * n - h) hc he
  have hcei : (4 * n - g) + (6 * n - h) = 10 * n - g - h := by omega
  rw [hcei] at hce
  have hd2 : (d ^ 2).natDegree < 10 * n - g - h := by
    compute_degree
    omega
  simp only [secondaryResidualInvariantThreePolynomial68, coeff_add,
    coeff_sub, coeff_smul, smul_eq_mul, hABd,
    coeff_eq_zero_of_natDegree_lt hB2c, hce,
    coeff_eq_zero_of_natDegree_lt hd2]
  ring

set_option maxHeartbeats 2000000 in
theorem secondaryResidualInvariantFourPolynomial68_coeff_double_of_deepGap
    (B c d e : k[X]) (n g : ℕ) (hg : 0 < g) (hrel : 2 * g < 3 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - 2 * g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (secondaryResidualInvariantFourPolynomial68 B c d e).coeff
        (9 * n - 3 * g) =
      (8 / 27 : k) *
        (-(B.coeff (3 * n - g) ^ 3) +
          9 * B.coeff (3 * n - g) * e.coeff (6 * n - 2 * g) +
          9 * c.coeff (4 * n - g) * d.coeff (5 * n - 2 * g)) := by
  have hB3 := coeff_pow_at_bound68 B (3 * n - g) 3 hB
  have hB3i : 3 * (3 * n - g) = 9 * n - 3 * g := by omega
  rw [hB3i] at hB3
  have hBe := coeff_mul_at_bounds68 B e (3 * n - g)
    (6 * n - 2 * g) hB he
  have hBei : (3 * n - g) + (6 * n - 2 * g) =
      9 * n - 3 * g := by omega
  rw [hBei] at hBe
  have hcd := coeff_mul_at_bounds68 c d (4 * n - g)
    (5 * n - 2 * g) hc hd
  have hcdi : (4 * n - g) + (5 * n - 2 * g) =
      9 * n - 3 * g := by omega
  rw [hcdi] at hcd
  simp only [secondaryResidualInvariantFourPolynomial68, coeff_add,
    coeff_smul, smul_eq_mul, hB3, hBe, hcd]
  ring

set_option maxHeartbeats 2000000 in
theorem secondaryResidualInvariantThreePolynomial68_coeff_double_of_deepGap
    (A B c d e : k[X]) (n g : ℕ) (hg : 0 < g) (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - 2 * g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (secondaryResidualInvariantThreePolynomial68 A B c d e).coeff
        (10 * n - 3 * g) =
      (8 / 9 : k) *
        (-(A.coeff (2 * n) * B.coeff (3 * n - g) *
            d.coeff (5 * n - 2 * g)) -
          B.coeff (3 * n - g) ^ 2 * c.coeff (4 * n - g) +
          3 * c.coeff (4 * n - g) * e.coeff (6 * n - 2 * g)) := by
  have hABd := coeff_mul_mul_at_bounds68 A B d (2 * n)
    (3 * n - g) (5 * n - 2 * g) hA hB hd
  have hABdi : 2 * n + (3 * n - g) + (5 * n - 2 * g) =
      10 * n - 3 * g := by omega
  rw [hABdi] at hABd
  have hBBc := coeff_mul_mul_at_bounds68 B B c (3 * n - g)
    (3 * n - g) (4 * n - g) hB hB hc
  have hBBci : (3 * n - g) + (3 * n - g) + (4 * n - g) =
      10 * n - 3 * g := by omega
  rw [hBBci] at hBBc
  have hB2c : (B ^ 2 * c).coeff (10 * n - 3 * g) =
      B.coeff (3 * n - g) ^ 2 * c.coeff (4 * n - g) := by
    simpa only [pow_two] using hBBc
  have hce := coeff_mul_at_bounds68 c e (4 * n - g)
    (6 * n - 2 * g) hc he
  have hcei : (4 * n - g) + (6 * n - 2 * g) =
      10 * n - 3 * g := by omega
  rw [hcei] at hce
  have hd2 : (d ^ 2).natDegree < 10 * n - 3 * g := by
    compute_degree
    omega
  simp only [secondaryResidualInvariantThreePolynomial68, coeff_add,
    coeff_sub, coeff_smul, smul_eq_mul, hABd, hB2c, hce,
    coeff_eq_zero_of_natDegree_lt hd2]
  ring

/-! ## I3 is load-free; I4 load cutoffs and the `6n` obstruction -/

set_option maxHeartbeats 2000000 in
theorem secondaryLoadInvariantThreePolynomial68_degree_lt_middle_of_deepGap
    (beta gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g h : ℕ) (hg : 0 < g) (hh : h < 2 * g) (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - h) :
    (secondaryLoadInvariantThreePolynomial68
      0 beta gamma delta epsilon zeta A B c D e).natDegree <
        10 * n - g - h := by
  simp only [secondaryLoadInvariantThreePolynomial68, zero_mul, mul_zero,
    zero_smul, smul_zero, add_zero, sub_zero]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
theorem secondaryLoadInvariantThreePolynomial68_degree_lt_double_of_deepGap
    (beta gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g : ℕ) (hg : 0 < g) (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (secondaryLoadInvariantThreePolynomial68
      0 beta gamma delta epsilon zeta A B c D e).natDegree <
        10 * n - 3 * g := by
  simp only [secondaryLoadInvariantThreePolynomial68, zero_mul, mul_zero,
    zero_smul, smul_zero, add_zero, sub_zero]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
theorem secondaryLoadInvariantFourPolynomial68_degree_lt_middle_of_sum_lt_three
    (beta gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g h : ℕ) (hg : 0 < g) (hsum : g + h < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - h) :
    (secondaryLoadInvariantFourPolynomial68
      0 beta gamma delta epsilon zeta A B c D e).natDegree <
        9 * n - g - h := by
  simp only [secondaryLoadInvariantFourPolynomial68, zero_mul, mul_zero,
    zero_smul, smul_zero, add_zero, sub_zero]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
theorem secondaryLoadInvariantFourPolynomial68_degree_lt_double_of_gap_lt_radius
    (beta gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g : ℕ) (hg : 0 < g) (hg_lt : g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (secondaryLoadInvariantFourPolynomial68
      0 beta gamma delta epsilon zeta A B c D e).natDegree <
        9 * n - 3 * g := by
  simp only [secondaryLoadInvariantFourPolynomial68, zero_mul, mul_zero,
    zero_smul, smul_zero, add_zero, sub_zero]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
theorem secondaryLoadInvariantFourPolynomial68_degree_lt_middle_of_l_beta
    (gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g h : ℕ) (hg : 0 < g) (hh : h < 2 * g) (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - h) :
    (secondaryLoadInvariantFourPolynomial68
      0 0 gamma delta epsilon zeta A B c D e).natDegree <
        9 * n - g - h := by
  simp only [secondaryLoadInvariantFourPolynomial68, zero_mul, mul_zero,
    zero_smul, smul_zero, add_zero, sub_zero]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
theorem secondaryLoadInvariantFourPolynomial68_degree_lt_double_of_l_beta
    (gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g : ℕ) (hg : 0 < g) (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (secondaryLoadInvariantFourPolynomial68
      0 0 gamma delta epsilon zeta A B c D e).natDegree <
        9 * n - 3 * g := by
  simp only [secondaryLoadInvariantFourPolynomial68, zero_mul, mul_zero,
    zero_smul, smul_zero, add_zero, sub_zero]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
theorem secondaryResidualInvariantFourPolynomial68_degree_lt_sixRadius_of_sum_gt_three
    (B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hsum : 3 * n < g + h) (hrel : 2 * g < 3 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (secondaryResidualInvariantFourPolynomial68 B c d e).natDegree <
      6 * n := by
  simp only [secondaryResidualInvariantFourPolynomial68]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
theorem secondaryResidualInvariantFourPolynomial68_degree_lt_sixRadius_of_gap_gt_radius
    (B c d e : k[X]) (n g : ℕ) (hg : 0 < g) (hg_gt : n < g)
    (hrel : 2 * g < 3 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - 2 * g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (secondaryResidualInvariantFourPolynomial68 B c d e).natDegree <
      6 * n := by
  simp only [secondaryResidualInvariantFourPolynomial68]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
theorem cubicFirstIntegralFourPolynomial68_forces_beta_eq_zero_of_residualBelowSix
    (beta gamma delta epsilon zeta i4 : k) (A B c d e : k[X])
    (n g : ℕ) (hn : 0 < n) (hg : 0 < g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hdD : ((1 / 3 : k) • (A * B) + d).natDegree ≤ 5 * n - g)
    (he' : e.natDegree ≤ 6 * n - g)
    (ha : A.coeff (2 * n) ≠ 0)
    (hhom : (secondaryResidualInvariantFourPolynomial68 B c d e).natDegree <
      6 * n)
    (hi4 : cubicFirstIntegralFourPolynomial68
      0 beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4) :
    beta = 0 := by
  let D := (1 / 3 : k) • (A * B) + d
  have hload :=
    secondaryLoadInvariantFourPolynomial68_coeff_sixRadius_of_l_eq_zero
      beta gamma delta epsilon zeta A B c D e n g hn hg
      hA hB hc hdD he'
  have hcoeff := congrArg (fun p : k[X] => p.coeff (6 * n)) hi4
  rw [cubicFirstIntegralFourPolynomial68_secondaryLoadSplit,
    show cubicFirstIntegralFourPolynomial68 0 0 0 0 0 0 A B c D e =
        secondaryResidualInvariantFourPolynomial68 B c d e by
      simpa only [D] using
        cubicFirstIntegralFourPolynomial68_residualCoordinates A B c d e,
    coeff_add, coeff_eq_zero_of_natDegree_lt hhom, zero_add] at hcoeff
  have hi : 6 * n ≠ 0 := by omega
  simp only [coeff_C, if_neg hi] at hcoeff
  have hpow : A.coeff (2 * n) ^ 3 ≠ 0 := pow_ne_zero 3 ha
  have hsb : (5 / 72 * beta : k) = 0 :=
    (mul_eq_zero.mp (hload ▸ hcoeff)).resolve_right hpow
  exact (mul_eq_zero.mp hsb).resolve_left (by norm_num)

/-! ## Combined residual faces -/

set_option maxHeartbeats 2000000 in
theorem cubicFirstIntegralThreePolynomial68_coeff_residualMiddle_of_deepGap
    (beta gamma delta epsilon zeta : k) (A B c d e : k[X])
    (n g h : ℕ) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (cubicFirstIntegralThreePolynomial68 0 beta gamma delta epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff
        (10 * n - g - h) =
      (8 / 9 : k) *
        (-(A.coeff (2 * n) * B.coeff (3 * n - g) *
            d.coeff (5 * n - h)) +
          3 * c.coeff (4 * n - g) * e.coeff (6 * n - h)) := by
  let D := (1 / 3 : k) • (A * B) + d
  have hD : D.natDegree ≤ 5 * n - g := by
    simp only [D]
    compute_degree
    omega
  have hload :=
    secondaryLoadInvariantThreePolynomial68_degree_lt_middle_of_deepGap
      beta gamma delta epsilon zeta A B c D e n g h hg hh hrel
      hA hB hc hD he
  rw [cubicFirstIntegralThreePolynomial68_secondaryLoadSplit,
    show cubicFirstIntegralThreePolynomial68 0 0 0 0 0 0 A B c D e =
        secondaryResidualInvariantThreePolynomial68 A B c d e by
      simpa only [D] using
        cubicFirstIntegralThreePolynomial68_residualCoordinates A B c d e,
    coeff_add,
    secondaryResidualInvariantThreePolynomial68_coeff_middle_of_deepGap
      A B c d e n g h hg hgh hh hrel hA hB hc hd he,
    coeff_eq_zero_of_natDegree_lt hload, add_zero]

set_option maxHeartbeats 2000000 in
theorem cubicFirstIntegralThreePolynomial68_coeff_residualDouble_of_deepGap
    (beta gamma delta epsilon zeta : k) (A B c d e : k[X])
    (n g : ℕ) (hg : 0 < g) (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - 2 * g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (cubicFirstIntegralThreePolynomial68 0 beta gamma delta epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff
        (10 * n - 3 * g) =
      (8 / 9 : k) *
        (-(A.coeff (2 * n) * B.coeff (3 * n - g) *
            d.coeff (5 * n - 2 * g)) -
          B.coeff (3 * n - g) ^ 2 * c.coeff (4 * n - g) +
          3 * c.coeff (4 * n - g) * e.coeff (6 * n - 2 * g)) := by
  let D := (1 / 3 : k) • (A * B) + d
  have hD : D.natDegree ≤ 5 * n - g := by
    simp only [D]
    compute_degree
    omega
  have hload :=
    secondaryLoadInvariantThreePolynomial68_degree_lt_double_of_deepGap
      beta gamma delta epsilon zeta A B c D e n g hg hrel
      hA hB hc hD he
  rw [cubicFirstIntegralThreePolynomial68_secondaryLoadSplit,
    show cubicFirstIntegralThreePolynomial68 0 0 0 0 0 0 A B c D e =
        secondaryResidualInvariantThreePolynomial68 A B c d e by
      simpa only [D] using
        cubicFirstIntegralThreePolynomial68_residualCoordinates A B c d e,
    coeff_add,
    secondaryResidualInvariantThreePolynomial68_coeff_double_of_deepGap
      A B c d e n g hg hrel hA hB hc hd he,
    coeff_eq_zero_of_natDegree_lt hload, add_zero]

set_option maxHeartbeats 2000000 in
theorem cubicFirstIntegralFourPolynomial68_coeff_residualMiddle_of_sum_lt_three
    (beta gamma delta epsilon zeta : k) (A B c d e : k[X])
    (n g h : ℕ) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hrel : 2 * g < 3 * n) (hsum : g + h < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (cubicFirstIntegralFourPolynomial68 0 beta gamma delta epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff
        (9 * n - g - h) =
      (8 / 3 : k) *
        (B.coeff (3 * n - g) * e.coeff (6 * n - h) +
          c.coeff (4 * n - g) * d.coeff (5 * n - h)) := by
  let D := (1 / 3 : k) • (A * B) + d
  have hD : D.natDegree ≤ 5 * n - g := by
    simp only [D]
    compute_degree
    omega
  have hload :=
    secondaryLoadInvariantFourPolynomial68_degree_lt_middle_of_sum_lt_three
      beta gamma delta epsilon zeta A B c D e n g h hg hsum
      hA hB hc hD he
  rw [cubicFirstIntegralFourPolynomial68_secondaryLoadSplit,
    show cubicFirstIntegralFourPolynomial68 0 0 0 0 0 0 A B c D e =
        secondaryResidualInvariantFourPolynomial68 B c d e by
      simpa only [D] using
        cubicFirstIntegralFourPolynomial68_residualCoordinates A B c d e,
    coeff_add,
    secondaryResidualInvariantFourPolynomial68_coeff_middle_of_deepGap
      B c d e n g h hg hgh hh hrel hB hc hd he,
    coeff_eq_zero_of_natDegree_lt hload, add_zero]

set_option maxHeartbeats 2000000 in
theorem cubicFirstIntegralFourPolynomial68_coeff_residualMiddle_of_l_beta
    (gamma delta epsilon zeta : k) (A B c d e : k[X])
    (n g h : ℕ) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (cubicFirstIntegralFourPolynomial68 0 0 gamma delta epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff
        (9 * n - g - h) =
      (8 / 3 : k) *
        (B.coeff (3 * n - g) * e.coeff (6 * n - h) +
          c.coeff (4 * n - g) * d.coeff (5 * n - h)) := by
  let D := (1 / 3 : k) • (A * B) + d
  have hD : D.natDegree ≤ 5 * n - g := by
    simp only [D]
    compute_degree
    omega
  have hload :=
    secondaryLoadInvariantFourPolynomial68_degree_lt_middle_of_l_beta
      gamma delta epsilon zeta A B c D e n g h hg hh hrel
      hA hB hc hD he
  rw [cubicFirstIntegralFourPolynomial68_secondaryLoadSplit,
    show cubicFirstIntegralFourPolynomial68 0 0 0 0 0 0 A B c D e =
        secondaryResidualInvariantFourPolynomial68 B c d e by
      simpa only [D] using
        cubicFirstIntegralFourPolynomial68_residualCoordinates A B c d e,
    coeff_add,
    secondaryResidualInvariantFourPolynomial68_coeff_middle_of_deepGap
      B c d e n g h hg hgh hh hrel hB hc hd he,
    coeff_eq_zero_of_natDegree_lt hload, add_zero]

set_option maxHeartbeats 2000000 in
theorem cubicFirstIntegralFourPolynomial68_coeff_residualDouble_of_gap_lt_radius
    (beta gamma delta epsilon zeta : k) (A B c d e : k[X])
    (n g : ℕ) (hg : 0 < g) (hrel : 2 * g < 3 * n) (hg_lt : g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - 2 * g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (cubicFirstIntegralFourPolynomial68 0 beta gamma delta epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff
        (9 * n - 3 * g) =
      (8 / 27 : k) *
        (-(B.coeff (3 * n - g) ^ 3) +
          9 * B.coeff (3 * n - g) * e.coeff (6 * n - 2 * g) +
          9 * c.coeff (4 * n - g) * d.coeff (5 * n - 2 * g)) := by
  let D := (1 / 3 : k) • (A * B) + d
  have hD : D.natDegree ≤ 5 * n - g := by
    simp only [D]
    compute_degree
    omega
  have hload :=
    secondaryLoadInvariantFourPolynomial68_degree_lt_double_of_gap_lt_radius
      beta gamma delta epsilon zeta A B c D e n g hg hg_lt
      hA hB hc hD he
  rw [cubicFirstIntegralFourPolynomial68_secondaryLoadSplit,
    show cubicFirstIntegralFourPolynomial68 0 0 0 0 0 0 A B c D e =
        secondaryResidualInvariantFourPolynomial68 B c d e by
      simpa only [D] using
        cubicFirstIntegralFourPolynomial68_residualCoordinates A B c d e,
    coeff_add,
    secondaryResidualInvariantFourPolynomial68_coeff_double_of_deepGap
      B c d e n g hg hrel hB hc hd he,
    coeff_eq_zero_of_natDegree_lt hload, add_zero]

set_option maxHeartbeats 2000000 in
theorem cubicFirstIntegralFourPolynomial68_coeff_residualDouble_of_l_beta
    (gamma delta epsilon zeta : k) (A B c d e : k[X])
    (n g : ℕ) (hg : 0 < g) (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - 2 * g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (cubicFirstIntegralFourPolynomial68 0 0 gamma delta epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff
        (9 * n - 3 * g) =
      (8 / 27 : k) *
        (-(B.coeff (3 * n - g) ^ 3) +
          9 * B.coeff (3 * n - g) * e.coeff (6 * n - 2 * g) +
          9 * c.coeff (4 * n - g) * d.coeff (5 * n - 2 * g)) := by
  let D := (1 / 3 : k) • (A * B) + d
  have hD : D.natDegree ≤ 5 * n - g := by
    simp only [D]
    compute_degree
    omega
  have hload :=
    secondaryLoadInvariantFourPolynomial68_degree_lt_double_of_l_beta
      gamma delta epsilon zeta A B c D e n g hg hrel
      hA hB hc hD he
  rw [cubicFirstIntegralFourPolynomial68_secondaryLoadSplit,
    show cubicFirstIntegralFourPolynomial68 0 0 0 0 0 0 A B c D e =
        secondaryResidualInvariantFourPolynomial68 B c d e by
      simpa only [D] using
        cubicFirstIntegralFourPolynomial68_residualCoordinates A B c d e,
    coeff_add,
    secondaryResidualInvariantFourPolynomial68_coeff_double_of_deepGap
      B c d e n g hg hrel hB hc hd he,
    coeff_eq_zero_of_natDegree_lt hload, add_zero]

set_option maxHeartbeats 2000000 in
theorem cubicFirstIntegralFourPolynomial68_coeff_residualMiddle_mixed
    (beta gamma delta epsilon zeta : k) (A B c d e : k[X])
    (n g h : ℕ) (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hrel : 2 * g < 3 * n) (hmixed : g + h = 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (he' : e.natDegree ≤ 6 * n - g) :
    (cubicFirstIntegralFourPolynomial68 0 beta gamma delta epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff (6 * n) =
      (8 / 3 : k) *
          (B.coeff (3 * n - g) * e.coeff (6 * n - h) +
            c.coeff (4 * n - g) * d.coeff (5 * n - h)) +
        (5 / 72 * beta : k) * A.coeff (2 * n) ^ 3 := by
  let D := (1 / 3 : k) • (A * B) + d
  have hD : D.natDegree ≤ 5 * n - g := by
    simp only [D]
    compute_degree
    omega
  have hidx : 9 * n - g - h = 6 * n := by omega
  have hload :=
    secondaryLoadInvariantFourPolynomial68_coeff_sixRadius_of_l_eq_zero
      beta gamma delta epsilon zeta A B c D e n g hn hg
      hA hB hc hD he'
  have hhom :=
    secondaryResidualInvariantFourPolynomial68_coeff_middle_of_deepGap
      B c d e n g h hg hgh hh hrel hB hc hd he
  rw [cubicFirstIntegralFourPolynomial68_secondaryLoadSplit,
    show cubicFirstIntegralFourPolynomial68 0 0 0 0 0 0 A B c D e =
        secondaryResidualInvariantFourPolynomial68 B c d e by
      simpa only [D] using
        cubicFirstIntegralFourPolynomial68_residualCoordinates A B c d e,
    coeff_add, ← hidx, hhom, hidx, hload]

set_option maxHeartbeats 2000000 in
theorem cubicFirstIntegralFourPolynomial68_coeff_residualDouble_mixed
    (beta gamma delta epsilon zeta : k) (A B c d e : k[X])
    (n g : ℕ) (hn : 0 < n) (hg : 0 < g) (hrel : 2 * g < 3 * n)
    (hwall : g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - 2 * g)
    (he : e.natDegree ≤ 6 * n - 2 * g)
    (he' : e.natDegree ≤ 6 * n - g) :
    (cubicFirstIntegralFourPolynomial68 0 beta gamma delta epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff (6 * n) =
      (8 / 27 : k) *
          (-(B.coeff (3 * n - g) ^ 3) +
            9 * B.coeff (3 * n - g) * e.coeff (6 * n - 2 * g) +
            9 * c.coeff (4 * n - g) * d.coeff (5 * n - 2 * g)) +
        (5 / 72 * beta : k) * A.coeff (2 * n) ^ 3 := by
  let D := (1 / 3 : k) • (A * B) + d
  have hD : D.natDegree ≤ 5 * n - g := by
    simp only [D]
    compute_degree
    omega
  have hidx : 9 * n - 3 * g = 6 * n := by omega
  have hload :=
    secondaryLoadInvariantFourPolynomial68_coeff_sixRadius_of_l_eq_zero
      beta gamma delta epsilon zeta A B c D e n g hn hg
      hA hB hc hD he'
  have hhom :=
    secondaryResidualInvariantFourPolynomial68_coeff_double_of_deepGap
      B c d e n g hg hrel hB hc hd he
  rw [cubicFirstIntegralFourPolynomial68_secondaryLoadSplit,
    show cubicFirstIntegralFourPolynomial68 0 0 0 0 0 0 A B c D e =
        secondaryResidualInvariantFourPolynomial68 B c d e by
      simpa only [D] using
        cubicFirstIntegralFourPolynomial68_residualCoordinates A B c d e,
    coeff_add, ← hidx, hhom, hidx, hload]

theorem polynomialSecondaryResidualThreeMiddle_eq_zero68_of_deepGap
    (beta gamma delta epsilon zeta i3 : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hi3 : cubicFirstIntegralThreePolynomial68
      0 beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i3) :
    -A.coeff (2 * n) * B.coeff (3 * n - g) * d.coeff (5 * n - h) +
      3 * c.coeff (4 * n - g) * e.coeff (6 * n - h) = 0 := by
  have hz := congrArg (fun p : k[X] => p.coeff (10 * n - g - h)) hi3
  rw [cubicFirstIntegralThreePolynomial68_coeff_residualMiddle_of_deepGap
    beta gamma delta epsilon zeta A B c d e n g h hg hgh hh
    hrel hA hB hc hd he] at hz
  have hindex : 10 * n - g - h ≠ 0 := by omega
  simp only [coeff_C, if_neg hindex] at hz
  have hzero := (mul_eq_zero.mp hz).resolve_left (by norm_num)
  linear_combination hzero

theorem polynomialSecondaryResidualThreeDouble_eq_zero68_of_deepGap
    (beta gamma delta epsilon zeta i3 : k)
    (A B c d e : k[X]) (n g : ℕ)
    (hg : 0 < g) (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - 2 * g)
    (he : e.natDegree ≤ 6 * n - 2 * g)
    (hi3 : cubicFirstIntegralThreePolynomial68
      0 beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i3) :
    -A.coeff (2 * n) * B.coeff (3 * n - g) * d.coeff (5 * n - 2 * g) -
        B.coeff (3 * n - g) ^ 2 * c.coeff (4 * n - g) +
        3 * c.coeff (4 * n - g) * e.coeff (6 * n - 2 * g) = 0 := by
  have hz := congrArg (fun p : k[X] => p.coeff (10 * n - 3 * g)) hi3
  rw [cubicFirstIntegralThreePolynomial68_coeff_residualDouble_of_deepGap
    beta gamma delta epsilon zeta A B c d e n g hg hrel
    hA hB hc hd he] at hz
  have hindex : 10 * n - 3 * g ≠ 0 := by omega
  simp only [coeff_C, if_neg hindex] at hz
  have hzero := (mul_eq_zero.mp hz).resolve_left (by norm_num)
  linear_combination hzero

theorem polynomialSecondaryResidualBetweenFace68_of_deepGap_low
    (beta gamma delta epsilon zeta i4 i3 : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hrel : 2 * g < 3 * n) (hsum : g + h < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hi4 : cubicFirstIntegralFourPolynomial68
      0 beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hi3 : cubicFirstIntegralThreePolynomial68
      0 beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i3) :
    SecondaryResidualBetweenFace68
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (d.coeff (5 * n - h))
      (e.coeff (6 * n - h)) := by
  constructor
  · have hz := congrArg (fun p : k[X] => p.coeff (9 * n - g - h)) hi4
    rw [cubicFirstIntegralFourPolynomial68_coeff_residualMiddle_of_sum_lt_three
      beta gamma delta epsilon zeta A B c d e n g h hg hgh hh
      hrel hsum hA hB hc hd he] at hz
    have hindex : 9 * n - g - h ≠ 0 := by omega
    simp only [coeff_C, if_neg hindex] at hz
    exact (mul_eq_zero.mp hz).resolve_left (by norm_num)
  · have hz := congrArg (fun p : k[X] => p.coeff (10 * n - g - h)) hi3
    rw [cubicFirstIntegralThreePolynomial68_coeff_residualMiddle_of_deepGap
      beta gamma delta epsilon zeta A B c d e n g h hg hgh hh
      hrel hA hB hc hd he] at hz
    have hindex : 10 * n - g - h ≠ 0 := by omega
    simp only [coeff_C, if_neg hindex] at hz
    have hzero := (mul_eq_zero.mp hz).resolve_left (by norm_num)
    linear_combination hzero

theorem polynomialSecondaryResidualBetweenFace68_of_deepGap_high
    (beta gamma delta epsilon zeta i4 i3 : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hrel : 2 * g < 3 * n) (hsum : 3 * n < g + h)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (he' : e.natDegree ≤ 6 * n - g)
    (ha : A.coeff (2 * n) ≠ 0)
    (hi4 : cubicFirstIntegralFourPolynomial68
      0 beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hi3 : cubicFirstIntegralThreePolynomial68
      0 beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i3) :
    beta = 0 ∧
      SecondaryResidualBetweenFace68
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (d.coeff (5 * n - h))
        (e.coeff (6 * n - h)) := by
  let D := (1 / 3 : k) • (A * B) + d
  have hD : D.natDegree ≤ 5 * n - g := by
    simp only [D]
    compute_degree
    omega
  have hhom :=
    secondaryResidualInvariantFourPolynomial68_degree_lt_sixRadius_of_sum_gt_three
      B c d e n g h hg hgh hh hsum hrel hB hc hd he
  have hbeta :=
    cubicFirstIntegralFourPolynomial68_forces_beta_eq_zero_of_residualBelowSix
      beta gamma delta epsilon zeta i4 A B c d e n g hn hg
      hA hB hc hD he' ha hhom hi4
  refine ⟨hbeta, ?_⟩
  constructor
  · have hz := congrArg (fun p : k[X] => p.coeff (9 * n - g - h)) hi4
    rw [hbeta] at hz
    rw [cubicFirstIntegralFourPolynomial68_coeff_residualMiddle_of_l_beta
      gamma delta epsilon zeta A B c d e n g h hg hgh hh
      hrel hA hB hc hd he] at hz
    have hindex : 9 * n - g - h ≠ 0 := by omega
    simp only [coeff_C, if_neg hindex] at hz
    exact (mul_eq_zero.mp hz).resolve_left (by norm_num)
  · have hz := congrArg (fun p : k[X] => p.coeff (10 * n - g - h)) hi3
    rw [cubicFirstIntegralThreePolynomial68_coeff_residualMiddle_of_deepGap
      beta gamma delta epsilon zeta A B c d e n g h hg hgh hh
      hrel hA hB hc hd he] at hz
    have hindex : 10 * n - g - h ≠ 0 := by omega
    simp only [coeff_C, if_neg hindex] at hz
    have hzero := (mul_eq_zero.mp hz).resolve_left (by norm_num)
    linear_combination hzero

theorem polynomialSecondaryResidualDoubleInvariants68_of_deepGap_low
    (beta gamma delta epsilon zeta i4 i3 : k)
    (A B c d e : k[X]) (n g : ℕ)
    (hg : 0 < g) (hrel : 2 * g < 3 * n) (hg_lt : g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - 2 * g)
    (he : e.natDegree ≤ 6 * n - 2 * g)
    (hi4 : cubicFirstIntegralFourPolynomial68
      0 beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hi3 : cubicFirstIntegralThreePolynomial68
      0 beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i3) :
    -(B.coeff (3 * n - g) ^ 3) +
        9 * B.coeff (3 * n - g) * e.coeff (6 * n - 2 * g) +
        9 * c.coeff (4 * n - g) * d.coeff (5 * n - 2 * g) = 0 ∧
      -(A.coeff (2 * n) * B.coeff (3 * n - g) *
          d.coeff (5 * n - 2 * g)) -
        B.coeff (3 * n - g) ^ 2 * c.coeff (4 * n - g) +
        3 * c.coeff (4 * n - g) * e.coeff (6 * n - 2 * g) = 0 := by
  constructor
  · have hz := congrArg (fun p : k[X] => p.coeff (9 * n - 3 * g)) hi4
    rw [cubicFirstIntegralFourPolynomial68_coeff_residualDouble_of_gap_lt_radius
      beta gamma delta epsilon zeta A B c d e n g hg hrel hg_lt
      hA hB hc hd he] at hz
    have hindex : 9 * n - 3 * g ≠ 0 := by omega
    simp only [coeff_C, if_neg hindex] at hz
    exact (mul_eq_zero.mp hz).resolve_left (by norm_num)
  · have hz := congrArg (fun p : k[X] => p.coeff (10 * n - 3 * g)) hi3
    rw [cubicFirstIntegralThreePolynomial68_coeff_residualDouble_of_deepGap
      beta gamma delta epsilon zeta A B c d e n g hg hrel
      hA hB hc hd he] at hz
    have hindex : 10 * n - 3 * g ≠ 0 := by omega
    simp only [coeff_C, if_neg hindex] at hz
    have hzero := (mul_eq_zero.mp hz).resolve_left (by norm_num)
    linear_combination hzero

theorem polynomialSecondaryResidualDoubleInvariants68_of_deepGap_high
    (beta gamma delta epsilon zeta i4 i3 : k)
    (A B c d e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hrel : 2 * g < 3 * n) (hg_gt : n < g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - 2 * g)
    (he : e.natDegree ≤ 6 * n - 2 * g)
    (he' : e.natDegree ≤ 6 * n - g)
    (ha : A.coeff (2 * n) ≠ 0)
    (hi4 : cubicFirstIntegralFourPolynomial68
      0 beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hi3 : cubicFirstIntegralThreePolynomial68
      0 beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i3) :
    beta = 0 ∧
      (-(B.coeff (3 * n - g) ^ 3) +
          9 * B.coeff (3 * n - g) * e.coeff (6 * n - 2 * g) +
          9 * c.coeff (4 * n - g) * d.coeff (5 * n - 2 * g) = 0) ∧
      (-(A.coeff (2 * n) * B.coeff (3 * n - g) *
            d.coeff (5 * n - 2 * g)) -
          B.coeff (3 * n - g) ^ 2 * c.coeff (4 * n - g) +
          3 * c.coeff (4 * n - g) * e.coeff (6 * n - 2 * g) = 0) := by
  let D := (1 / 3 : k) • (A * B) + d
  have hD : D.natDegree ≤ 5 * n - g := by
    simp only [D]
    compute_degree
    omega
  have hhom :=
    secondaryResidualInvariantFourPolynomial68_degree_lt_sixRadius_of_gap_gt_radius
      B c d e n g hg hg_gt hrel hB hc hd he
  have hbeta :=
    cubicFirstIntegralFourPolynomial68_forces_beta_eq_zero_of_residualBelowSix
      beta gamma delta epsilon zeta i4 A B c d e n g hn hg
      hA hB hc hD he' ha hhom hi4
  refine ⟨hbeta, ?_⟩
  constructor
  · have hz := congrArg (fun p : k[X] => p.coeff (9 * n - 3 * g)) hi4
    rw [hbeta] at hz
    rw [cubicFirstIntegralFourPolynomial68_coeff_residualDouble_of_l_beta
      gamma delta epsilon zeta A B c d e n g hg hrel
      hA hB hc hd he] at hz
    have hindex : 9 * n - 3 * g ≠ 0 := by omega
    simp only [coeff_C, if_neg hindex] at hz
    exact (mul_eq_zero.mp hz).resolve_left (by norm_num)
  · have hz := congrArg (fun p : k[X] => p.coeff (10 * n - 3 * g)) hi3
    rw [cubicFirstIntegralThreePolynomial68_coeff_residualDouble_of_deepGap
      beta gamma delta epsilon zeta A B c d e n g hg hrel
      hA hB hc hd he] at hz
    have hindex : 10 * n - 3 * g ≠ 0 := by omega
    simp only [coeff_C, if_neg hindex] at hz
    have hzero := (mul_eq_zero.mp hz).resolve_left (by norm_num)
    linear_combination hzero

/-! ## Canonical selector -/

set_option maxHeartbeats 8000000 in
/-- On the canonical expanded system throughout `n < 2g` and `2g < 3n`,
the residual gap is selected and the exact I4/I3 faces are extracted,
including the `beta A^3` load at `6n`. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_deepGapResidualSelect68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hchamber :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      n < 2 * g ∧ 2 * g < 3 * n) :
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
    l = 0 ∧
      (Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0) ∧
      d.natDegree < 5 * n - g ∧ ee.natDegree < 6 * n - g ∧
      g < h ∧
      d.natDegree ≤ 5 * n - h ∧ ee.natDegree ≤ 6 * n - h ∧
      DeepGapResidualInvariants68 n g h
        (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
        (ce.coeff (4 * n - g))
        (d.coeff (5 * n - h)) (ee.coeff (6 * n - h))
        (d.coeff (5 * n - 2 * g)) (ee.coeff (6 * n - 2 * g))
        beta := by
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
  change n < 2 * g ∧ 2 * g < 3 * n at hchamber
  have hgap :=
    maximalExpandedIntegratedPolynomialLowerSystem_deepGapResidualGap68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hchamber)
  change l = 0 ∧
    (Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0) ∧
    d.natDegree < 5 * n - g ∧ ee.natDegree < 6 * n - g ∧
    g < h ∧
    d.natDegree ≤ 5 * n - h ∧ ee.natDegree ≤ 6 * n - h at hgap
  have hl : l = 0 := hgap.1
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
  have hg0 : 0 < g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.1
  have ha : Ae.coeff (2 * n) ≠ 0 := by
    simpa only [n, Ae] using hcore.2.2.2.2.2
  have hA : Ae.natDegree ≤ 2 * n := by
    have hAe : Ae.natDegree = 2 * n := by
      simpa only [n, Ae, Be, Ce, De, Ee] using hdrop.1
    omega
  have hB : Be.natDegree ≤ 3 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.2.1
  have hc : ce.natDegree ≤ 4 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
      hsecondary.2.2.1
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
    hDrec, hl] at hi4c
  have hi3c := hi3e
  rw [hCrec, hErec, firstIntegralThreePolynomial68_cubicCoordinates,
    hDrec, hl] at hi3c
  have he' : ee.natDegree ≤ 6 * n - g :=
    (hgap.2.2.2.1).le
  have hd2_of : ¬ h < 2 * g → d.natDegree ≤ 5 * n - 2 * g := by
    intro hnot
    have hge : 2 * g ≤ h := not_lt.mp hnot
    exact (hgap.2.2.2.2.2.1).trans (Nat.sub_le_sub_left hge (5 * n))
  have he2_of : ¬ h < 2 * g → ee.natDegree ≤ 6 * n - 2 * g := by
    intro hnot
    have hge : 2 * g ≤ h := not_lt.mp hnot
    exact (hgap.2.2.2.2.2.2).trans (Nat.sub_le_sub_left hge (6 * n))
  refine ⟨hgap.1, hgap.2.1, hgap.2.2.1, hgap.2.2.2.1, hgap.2.2.2.2.1,
    hgap.2.2.2.2.2.1, hgap.2.2.2.2.2.2, ?_⟩
  refine
    { three_middle := ?_
      four_middle_below := ?_
      four_middle_mixed := ?_
      four_middle_above := ?_
      three_double := ?_
      four_double_below := ?_
      four_double_mixed := ?_
      four_double_above := ?_ }
  · intro hh
    exact polynomialSecondaryResidualThreeMiddle_eq_zero68_of_deepGap
      beta gamma delta epsilon zeta i3 Ae Be ce d ee n g h
      hg0 hgap.2.2.2.2.1 hh hchamber.2
      hA hB hc hgap.2.2.2.2.2.1 hgap.2.2.2.2.2.2 hi3c
  · intro hh hsum
    have hface :=
      polynomialSecondaryResidualBetweenFace68_of_deepGap_low
        beta gamma delta epsilon zeta i4 i3 Ae Be ce d ee n g h
        hg0 hgap.2.2.2.2.1 hh hchamber.2 hsum
        hA hB hc hgap.2.2.2.2.2.1 hgap.2.2.2.2.2.2 hi4c hi3c
    exact hface.four
  · intro hh hmixed
    have hz := congrArg (fun p : k[X] => p.coeff (6 * n)) hi4c
    rw [cubicFirstIntegralFourPolynomial68_coeff_residualMiddle_mixed
      beta gamma delta epsilon zeta Ae Be ce d ee n g h
      hn hg0 hgap.2.2.2.2.1 hh hchamber.2 hmixed
      hA hB hc hgap.2.2.2.2.2.1 hgap.2.2.2.2.2.2 he'] at hz
    have hindex : 6 * n ≠ 0 := Nat.ne_of_gt (Nat.mul_pos (by decide : 0 < 6) hn)
    simp only [coeff_C, if_neg hindex] at hz
    exact hz
  · intro hh hsum
    have hface :=
      polynomialSecondaryResidualBetweenFace68_of_deepGap_high
        beta gamma delta epsilon zeta i4 i3 Ae Be ce d ee n g h
        hn hg0 hgap.2.2.2.2.1 hh hchamber.2 hsum
        hA hB hc hgap.2.2.2.2.2.1 hgap.2.2.2.2.2.2 he' ha hi4c hi3c
    exact ⟨hface.1, hface.2.four⟩
  · intro hnot
    exact polynomialSecondaryResidualThreeDouble_eq_zero68_of_deepGap
      beta gamma delta epsilon zeta i3 Ae Be ce d ee n g
      hg0 hchamber.2 hA hB hc (hd2_of hnot) (he2_of hnot) hi3c
  · intro hnot hg_lt
    exact (polynomialSecondaryResidualDoubleInvariants68_of_deepGap_low
      beta gamma delta epsilon zeta i4 i3 Ae Be ce d ee n g
      hg0 hchamber.2 hg_lt hA hB hc (hd2_of hnot) (he2_of hnot)
      hi4c hi3c).1
  · intro hnot hwall
    have hz := congrArg (fun p : k[X] => p.coeff (6 * n)) hi4c
    rw [cubicFirstIntegralFourPolynomial68_coeff_residualDouble_mixed
      beta gamma delta epsilon zeta Ae Be ce d ee n g
      hn hg0 hchamber.2 hwall hA hB hc (hd2_of hnot) (he2_of hnot) he'] at hz
    have hindex : 6 * n ≠ 0 := Nat.ne_of_gt (Nat.mul_pos (by decide : 0 < 6) hn)
    simp only [coeff_C, if_neg hindex] at hz
    exact hz
  · intro hnot hg_gt
    have hface :=
      polynomialSecondaryResidualDoubleInvariants68_of_deepGap_high
        beta gamma delta epsilon zeta i4 i3 Ae Be ce d ee n g
        hn hg0 hchamber.2 hg_gt hA hB hc (hd2_of hnot) (he2_of hnot)
        he' ha hi4c hi3c
    exact ⟨hface.1, hface.2.1⟩

end DeepGapResidualOneForms68

#print axioms maximalExpandedIntegratedPolynomialLowerSystem_deepGapResidualGap68
#print axioms cubicFirstIntegralFourPolynomial68_forces_beta_eq_zero_of_residualBelowSix
#print axioms polynomialSecondaryResidualBetweenFace68_of_deepGap_low
#print axioms polynomialSecondaryResidualBetweenFace68_of_deepGap_high
#print axioms polynomialSecondaryResidualDoubleInvariants68_of_deepGap_low
#print axioms polynomialSecondaryResidualDoubleInvariants68_of_deepGap_high
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_deepGapResidualSelect68

end Max11DegreeRoutes
