import LowScale68SecondaryResidualExtraction

/-! # Relaxed first `(6,8)` secondary face after `l = 0`

The tracked extraction in `LowScale68SecondaryExtraction` and
`LowScale68SecondaryOneForms` uses the chamber `2g < n` because the Jacobian
load `l A^4` and the `l`-pieces of the integrated coefficients sit on or
above the first secondary face once `2g ≥ n`.  In the complementary
large-gap chamber the quartic invariant forces `l = 0`.  With that
hypothesis the same leading coefficients can be re-extracted under the
weaker old-weight cutoff `2g < 3n`, except the second one-form row, whose
`alpha A^2` load meets the face as soon as `g ≥ n`.

Exact chambers, remaining loads otherwise arbitrary:

* invariants `F₄`, `F₃` and one-forms `F₂`, `F₀`: `2g < 3n`
* one-form `F₁`: `g < n` (or `2g < 3n` after the extra vanishing `alpha = 0`)
* full five-face classification `e = 0 ∧ a*b = 3*d`: needs `F₁`
* four-equation classification without `F₁`, under `2g < 3n`:
  `(e = 0 ∧ a*b = 3*d) ∨ (e = 0 ∧ c = 0 ∧ a*b = d) ∨ (b = c = d = 0)`
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section RelaxedSecondaryFace68

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Abstract classification under the relaxed radius gap -/

theorem firstSecondaryFace68_gap_ne_six_radius
    (n g : ℕ) (hn : 0 < n) (hrel : 2 * g < 3 * n) :
    (g : k) - 6 * (n : k) ≠ 0 := by
  intro hzero
  have heq : (g : k) = 6 * (n : k) := sub_eq_zero.mp hzero
  have hnat : g = 6 * n := by exact_mod_cast heq
  omega

theorem firstSecondaryFace68_classify_of_two_mul_gap_lt_three_mul_radius
    (n g : ℕ) (a b c d e : k) (ha : a ≠ 0)
    (hn : 0 < n) (hrel : 2 * g < 3 * n)
    (hface : FirstSecondaryFace68 (n : k) (g : k) a b c d e) :
    e = 0 ∧ a * b = 3 * d := by
  exact firstSecondaryFace68_classify (n : k) (g : k) a b c d e ha
    (firstSecondaryFace68_gap_ne_six_radius n g hn hrel) hface

/-- The two invariants and the terminal one-form, without `F₁`, leave three
algebraic families.  The middle family `e = 0`, `c = 0`, `a*b = d` is killed
only by `F₁`. -/
theorem firstSecondaryFourThreeZero68_classify
    (a b c d e : k) (ha : a ≠ 0)
    (hfour : firstSecondaryFour68 a b c d e = 0)
    (hthree : firstSecondaryThree68 a b c d e = 0)
    (hzero : firstSecondaryZero68 a b c d e = 0) :
    (e = 0 ∧ a * b = 3 * d) ∨
      (e = 0 ∧ c = 0 ∧ a * b = d) ∨
      (b = 0 ∧ c = 0 ∧ d = 0) := by
  have heFactor : e * (a * b - 3 * d) = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left (by norm_num : (-3 : k) ≠ 0)
    calc
      (-3 : k) * (e * (a * b - 3 * d)) =
          a * firstSecondaryFour68 a b c d e -
            firstSecondaryZero68 a b c d e := by
        simp only [firstSecondaryFour68, firstSecondaryZero68]
        ring
      _ = 0 := by rw [hfour, hzero]; ring
  rcases mul_eq_zero.mp heFactor with he0 | hab3
  · have hcFactor : c * (a * b - 3 * d) = 0 := by
      calc
        c * (a * b - 3 * d) = firstSecondaryFour68 a b c d e := by
          simp only [firstSecondaryFour68, he0, mul_zero, sub_zero]
          ring
        _ = 0 := hfour
    rcases mul_eq_zero.mp hcFactor with hc0 | hab3'
    · have hbd : (a * b - d) * (a * b - 3 * d) = 0 := by
        calc
          (a * b - d) * (a * b - 3 * d) =
              firstSecondaryThree68 a b c d e := by
            simp only [firstSecondaryThree68, he0, hc0, mul_zero, add_zero]
            ring
          _ = 0 := hthree
      rcases mul_eq_zero.mp hbd with habd | hab3''
      · exact Or.inr (Or.inl ⟨he0, hc0, sub_eq_zero.mp habd⟩)
      · exact Or.inl ⟨he0, sub_eq_zero.mp hab3''⟩
    · exact Or.inl ⟨he0, sub_eq_zero.mp hab3'⟩
  · have hab3' : a * b = 3 * d := sub_eq_zero.mp hab3
    by_cases he : e = 0
    · exact Or.inl ⟨he, hab3'⟩
    · have hce : c * e = 0 := by
        apply (mul_eq_zero.mp ?_).resolve_left (by norm_num : (6 : k) ≠ 0)
        calc
          (6 : k) * (c * e) = firstSecondaryThree68 a b c d e -
              (a * b - d) * (a * b - 3 * d) := by
            simp only [firstSecondaryThree68]
            ring
          _ = 0 := by rw [hthree, hab3']; ring
      have hc0 : c = 0 := (mul_eq_zero.mp hce).resolve_right he
      have hde : d * e = 0 := by
        apply (mul_eq_zero.mp ?_).resolve_left (by norm_num : (-9 : k) ≠ 0)
        calc
          (-9 : k) * (d * e) = firstSecondaryZero68 a b c d e := by
            simp [firstSecondaryZero68, hc0]
            ring
          _ = 0 := hzero
      have hd0 : d = 0 := (mul_eq_zero.mp hde).resolve_right he
      have hb0 : b = 0 := by
        have hab0 : a * b = 0 := by simpa [hd0] using hab3'
        exact (mul_eq_zero.mp hab0).resolve_left ha
      exact Or.inr (Or.inr ⟨hb0, hc0, hd0⟩)

/-! ## Load degree cutoffs after `l = 0` -/

set_option maxHeartbeats 2000000 in
theorem cubicLoadSPolynomial68_degreeBound_of_loadL
    (l alpha beta delta : k) (A B c : k[X]) (n g : ℕ)
    (hl : l = 0)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g) :
    (cubicLoadSPolynomial68 l alpha beta delta A B c).natDegree ≤
      max (2 * n) (3 * n - g) := by
  have heq : cubicLoadSPolynomial68 l alpha beta delta A B c =
      alpha • B + (5 / 6 * beta : k) • A + C delta := by
    simp [cubicLoadSPolynomial68, hl, mul_zero, zero_smul, add_zero]
  rw [heq]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
theorem cubicLoadTPolynomial68_degreeBound_of_loadL
    (l alpha beta gamma epsilon : k) (A B c D : k[X]) (n g : ℕ)
    (hl : l = 0)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g) :
    (cubicLoadTPolynomial68 l alpha beta gamma epsilon A B c D).natDegree ≤
      4 * n := by
  have heq : cubicLoadTPolynomial68 l alpha beta gamma epsilon A B c D =
      (1 / 3 * alpha : k) • A ^ 2 + alpha • c +
        (5 / 6 * beta : k) • B + (2 / 3 * gamma : k) • A + C epsilon := by
    simp [cubicLoadTPolynomial68, hl, mul_zero, zero_smul, add_zero]
  rw [heq]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
theorem cubicLoadUPolynomial68_degreeBound_of_loadL
    (l alpha beta gamma delta zeta : k) (A B c D e : k[X]) (n g : ℕ)
    (hl : l = 0)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadUPolynomial68 l alpha beta gamma delta zeta A B c D e).natDegree ≤
      max (4 * n) (5 * n - g) := by
  have heq : cubicLoadUPolynomial68 l alpha beta gamma delta zeta A B c D e =
      alpha • D + (5 / 24 * beta : k) • A ^ 2 +
        (5 / 6 * beta : k) • c + (2 / 3 * gamma : k) • B +
        (1 / 2 * delta : k) • A + C zeta := by
    simp [cubicLoadUPolynomial68, hl, mul_zero, zero_smul, add_zero]
  rw [heq]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
theorem cubicLoadVPolynomial68_degreeBound_of_loadL
    (l alpha beta gamma delta epsilon eta : k) (A B c D e : k[X])
    (n g : ℕ) (hl : l = 0)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadVPolynomial68 l alpha beta gamma delta epsilon eta
      A B c D e).natDegree ≤ 6 * n := by
  have heq : cubicLoadVPolynomial68 l alpha beta gamma delta epsilon eta
        A B c D e =
      (1 / 27 * alpha : k) • A ^ 3 + (1 / 3 * alpha : k) • (A * c) +
        alpha • e - (5 / 36 * beta : k) • (A * B) +
        (5 / 6 * beta : k) • D + (1 / 9 * gamma : k) • A ^ 2 +
        (2 / 3 * gamma : k) • c + (1 / 2 * delta : k) • B +
        (1 / 3 * epsilon : k) • A + C eta := by
    simp [cubicLoadVPolynomial68, hl, mul_zero, zero_smul, add_zero, sub_zero]
  rw [heq]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
theorem cubicLoadTPolynomial68_degreeBound_of_loadL_alpha
    (l alpha beta gamma epsilon : k) (A B c D : k[X]) (n g : ℕ)
    (hl : l = 0) (halpha : alpha = 0)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g) :
    (cubicLoadTPolynomial68 l alpha beta gamma epsilon A B c D).natDegree ≤
      max (2 * n) (3 * n - g) := by
  have heq : cubicLoadTPolynomial68 l alpha beta gamma epsilon A B c D =
      (5 / 6 * beta : k) • B + (2 / 3 * gamma : k) • A + C epsilon := by
    simp [cubicLoadTPolynomial68, hl, halpha, mul_zero, zero_smul, add_zero]
  rw [heq]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
theorem cubicLoadUPolynomial68_degreeBound_of_loadL_alpha
    (l alpha beta gamma delta zeta : k) (A B c D e : k[X]) (n g : ℕ)
    (hl : l = 0) (halpha : alpha = 0)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadUPolynomial68 l alpha beta gamma delta zeta A B c D e).natDegree ≤
      4 * n := by
  have heq : cubicLoadUPolynomial68 l alpha beta gamma delta zeta A B c D e =
      (5 / 24 * beta : k) • A ^ 2 + (5 / 6 * beta : k) • c +
        (2 / 3 * gamma : k) • B + (1 / 2 * delta : k) • A + C zeta := by
    simp [cubicLoadUPolynomial68, hl, halpha, mul_zero, zero_smul, add_zero]
  rw [heq]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
theorem cubicLoadVPolynomial68_degreeBound_of_loadL_alpha
    (l alpha beta gamma delta epsilon eta : k) (A B c D e : k[X])
    (n g : ℕ) (hl : l = 0) (halpha : alpha = 0)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadVPolynomial68 l alpha beta gamma delta epsilon eta
      A B c D e).natDegree ≤ max (4 * n) (5 * n - g) := by
  have heq : cubicLoadVPolynomial68 l alpha beta gamma delta epsilon eta
        A B c D e =
      -(5 / 36 * beta : k) • (A * B) + (5 / 6 * beta : k) • D +
        (1 / 9 * gamma : k) • A ^ 2 + (2 / 3 * gamma : k) • c +
        (1 / 2 * delta : k) • B + (1 / 3 * epsilon : k) • A + C eta := by
    simp [cubicLoadVPolynomial68, hl, halpha, mul_zero, zero_smul, add_zero,
      sub_zero]
  rw [heq]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
/-- After `l = 0`, every remaining quartic-invariant load is at most the
old weight of `beta A^3`. -/
theorem secondaryLoadInvariantFourPolynomial68_degree_le_sixRadius_of_loadL
    (l beta gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g : ℕ) (hl : l = 0)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (secondaryLoadInvariantFourPolynomial68 l beta gamma delta epsilon zeta
      A B c D e).natDegree ≤ 6 * n := by
  have heq : secondaryLoadInvariantFourPolynomial68 l beta gamma delta
        epsilon zeta A B c D e =
      zeta • A + (2 * epsilon : k) • B +
        (1 / 4 * delta : k) • A ^ 2 + (3 * delta : k) • c +
        (4 * gamma : k) • D - (4 / 3 * gamma : k) • (A * B) +
        (5 * beta : k) • e + (5 / 6 * beta : k) • (A * c) -
        (5 / 12 * beta : k) • B ^ 2 + (5 / 72 * beta : k) • A ^ 3 := by
    simp [secondaryLoadInvariantFourPolynomial68, hl, mul_zero, zero_smul,
      add_zero, sub_zero]
  rw [heq]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
theorem secondaryLoadInvariantFourPolynomial68_degree_lt_firstFace_of_loadL
    (l beta gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g : ℕ) (hl : l = 0) (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (secondaryLoadInvariantFourPolynomial68 l beta gamma delta epsilon zeta
      A B c D e).natDegree < 9 * n - 2 * g := by
  have hle := secondaryLoadInvariantFourPolynomial68_degree_le_sixRadius_of_loadL
    l beta gamma delta epsilon zeta A B c D e n g hl hA hB hc hD he
  exact hle.trans_lt (by omega)

set_option maxHeartbeats 2000000 in
/-- After `l = 0`, every remaining cubic-invariant load is at most the old
weight of `beta A² B`. -/
theorem secondaryLoadInvariantThreePolynomial68_degree_le_of_loadL
    (l beta gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g : ℕ) (hl : l = 0)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (secondaryLoadInvariantThreePolynomial68 l beta gamma delta epsilon zeta
      A B c D e).natDegree ≤ 7 * n := by
  have heq : secondaryLoadInvariantThreePolynomial68 l beta gamma delta
        epsilon zeta A B c D e =
      zeta • B + (2 * epsilon : k) • c + (4 * gamma : k) • e -
        (2 / 3 * gamma : k) • B ^ 2 + (3 * delta : k) • D -
        (3 / 2 * delta : k) • (A * B) +
        (5 / 24 * beta : k) • (A ^ 2 * B) -
        (5 / 6 * beta : k) • (A * D) -
        (5 / 6 * beta : k) • (B * c) := by
    simp [secondaryLoadInvariantThreePolynomial68, hl, mul_zero, zero_smul,
      add_zero, sub_zero]
  rw [heq]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
theorem secondaryLoadInvariantThreePolynomial68_degree_lt_firstFace_of_loadL
    (l beta gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g : ℕ) (hn : 0 < n) (hl : l = 0) (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (secondaryLoadInvariantThreePolynomial68 l beta gamma delta epsilon zeta
      A B c D e).natDegree < 10 * n - 2 * g := by
  have hle := secondaryLoadInvariantThreePolynomial68_degree_le_of_loadL
    l beta gamma delta epsilon zeta A B c D e n g hl hA hB hc hD he
  exact hle.trans_lt (by omega)

/-! ## Homogeneous invariant coefficients under `2g < 3n` -/

set_option maxHeartbeats 2000000 in
theorem cubicHomogeneousFirstIntegralFourPolynomial68_secondaryCoeff
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicFirstIntegralFourPolynomial68 0 0 0 0 0 0 A B c D e).coeff
        (9 * n - 2 * g) =
      (-8 / 9 : k) * firstSecondaryFour68
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
        (e.coeff (6 * n - g)) := by
  have lower (p : k[X]) (hp : p.natDegree < 9 * n - 2 * g) :
      p.coeff (9 * n - 2 * g) = 0 :=
    coeff_eq_zero_of_natDegree_lt hp
  have hABC : (A * B * c).coeff (9 * n - 2 * g) =
      A.coeff (2 * n) * B.coeff (3 * n - g) *
        c.coeff (4 * n - g) := by
    have h := coeff_mul_mul_at_bounds68 A B c (2 * n)
      (3 * n - g) (4 * n - g) hA hB hc
    have hi : 2 * n + (3 * n - g) + (4 * n - g) =
        9 * n - 2 * g := by omega
    simpa only [hi] using h
  have hBe : (B * e).coeff (9 * n - 2 * g) =
      B.coeff (3 * n - g) * e.coeff (6 * n - g) := by
    have h := coeff_mul_at_bounds68 B e (3 * n - g) (6 * n - g) hB he
    have hi : (3 * n - g) + (6 * n - g) = 9 * n - 2 * g := by omega
    simpa only [hi] using h
  have hDc : (D * c).coeff (9 * n - 2 * g) =
      D.coeff (5 * n - g) * c.coeff (4 * n - g) := by
    have h := coeff_mul_at_bounds68 D c (5 * n - g) (4 * n - g) hD hc
    have hi : (5 * n - g) + (4 * n - g) = 9 * n - 2 * g := by omega
    simpa only [hi] using h
  have hB3 : (B ^ 3).coeff (9 * n - 2 * g) = 0 :=
    lower _ (by compute_degree; omega)
  simp only [cubicFirstIntegralFourPolynomial68, zero_mul, zero_smul,
    add_zero, sub_zero, coeff_add, coeff_sub, coeff_smul, hABC, hBe, hDc,
    hB3, smul_eq_mul, mul_zero, add_zero, sub_zero]
  simp only [firstSecondaryFour68]
  ring

set_option maxHeartbeats 2000000 in
theorem cubicHomogeneousFirstIntegralThreePolynomial68_secondaryCoeff
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicFirstIntegralThreePolynomial68 0 0 0 0 0 0 A B c D e).coeff
        (10 * n - 2 * g) =
      (4 / 9 : k) * firstSecondaryThree68
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
        (e.coeff (6 * n - g)) := by
  have lower (p : k[X]) (hp : p.natDegree < 10 * n - 2 * g) :
      p.coeff (10 * n - 2 * g) = 0 :=
    coeff_eq_zero_of_natDegree_lt hp
  have hA2deg : (A ^ 2).natDegree ≤ 4 * n := by
    compute_degree
    omega
  have hB2deg : (B ^ 2).natDegree ≤ 6 * n - 2 * g := by
    compute_degree
    omega
  have hA2coeff : (A ^ 2).coeff (4 * n) = A.coeff (2 * n) ^ 2 := by
    have h := coeff_pow_at_bound68 A (2 * n) 2 hA
    have hi : 2 * (2 * n) = 4 * n := by omega
    simpa only [hi] using h
  have hB2coeff : (B ^ 2).coeff (6 * n - 2 * g) =
      B.coeff (3 * n - g) ^ 2 := by
    have h := coeff_pow_at_bound68 B (3 * n - g) 2 hB
    have hi : 2 * (3 * n - g) = 6 * n - 2 * g := by omega
    simpa only [hi] using h
  have hA2B2 : (A ^ 2 * B ^ 2).coeff (10 * n - 2 * g) =
      A.coeff (2 * n) ^ 2 * B.coeff (3 * n - g) ^ 2 := by
    have h := coeff_mul_at_bounds68 (A ^ 2) (B ^ 2) (4 * n)
      (6 * n - 2 * g) hA2deg hB2deg
    have hi : 4 * n + (6 * n - 2 * g) = 10 * n - 2 * g := by omega
    rw [hi, hA2coeff, hB2coeff] at h
    exact h
  have hABD : (A * B * D).coeff (10 * n - 2 * g) =
      A.coeff (2 * n) * B.coeff (3 * n - g) *
        D.coeff (5 * n - g) := by
    have h := coeff_mul_mul_at_bounds68 A B D (2 * n)
      (3 * n - g) (5 * n - g) hA hB hD
    have hi : 2 * n + (3 * n - g) + (5 * n - g) =
        10 * n - 2 * g := by omega
    simpa only [hi] using h
  have hD2 : (D ^ 2).coeff (10 * n - 2 * g) =
      D.coeff (5 * n - g) ^ 2 := by
    have h := coeff_pow_at_bound68 D (5 * n - g) 2 hD
    have hi : 2 * (5 * n - g) = 10 * n - 2 * g := by omega
    simpa only [hi] using h
  have hce : (c * e).coeff (10 * n - 2 * g) =
      c.coeff (4 * n - g) * e.coeff (6 * n - g) := by
    have h := coeff_mul_at_bounds68 c e (4 * n - g) (6 * n - g) hc he
    have hi : (4 * n - g) + (6 * n - g) = 10 * n - 2 * g := by omega
    simpa only [hi] using h
  have hB2c : (B ^ 2 * c).coeff (10 * n - 2 * g) = 0 :=
    lower _ (by compute_degree; omega)
  simp only [cubicFirstIntegralThreePolynomial68, zero_mul, zero_smul,
    add_zero, sub_zero, coeff_add, coeff_sub, coeff_smul, hA2B2, hABD,
    hB2c, hD2, hce, smul_eq_mul, mul_zero, add_zero, sub_zero]
  simp only [firstSecondaryThree68]
  ring

set_option maxHeartbeats 2000000 in
theorem cubicFirstIntegralFourPolynomial68_secondaryCoeff_of_loadL
    (l beta gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g : ℕ) (hn : 0 < n) (hg : 0 < g) (hl : l = 0)
    (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicFirstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
        A B c D e).coeff (9 * n - 2 * g) =
      (-8 / 9 : k) * firstSecondaryFour68
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
        (e.coeff (6 * n - g)) := by
  rw [cubicFirstIntegralFourPolynomial68_secondaryLoadSplit, coeff_add,
    coeff_eq_zero_of_natDegree_lt
      (secondaryLoadInvariantFourPolynomial68_degree_lt_firstFace_of_loadL
        l beta gamma delta epsilon zeta A B c D e n g hl hrel
        hA hB hc hD he), add_zero]
  simpa [hl] using
    cubicHomogeneousFirstIntegralFourPolynomial68_secondaryCoeff A B c D e
      n g hn hg hrel hA hB hc hD he

set_option maxHeartbeats 2000000 in
theorem cubicFirstIntegralThreePolynomial68_secondaryCoeff_of_loadL
    (l beta gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g : ℕ) (hn : 0 < n) (hg : 0 < g) (hl : l = 0)
    (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicFirstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
        A B c D e).coeff (10 * n - 2 * g) =
      (4 / 9 : k) * firstSecondaryThree68
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
        (e.coeff (6 * n - g)) := by
  rw [cubicFirstIntegralThreePolynomial68_secondaryLoadSplit, coeff_add,
    coeff_eq_zero_of_natDegree_lt
      (secondaryLoadInvariantThreePolynomial68_degree_lt_firstFace_of_loadL
        l beta gamma delta epsilon zeta A B c D e n g hn hl hrel
        hA hB hc hD he), add_zero]
  simpa [hl] using
    cubicHomogeneousFirstIntegralThreePolynomial68_secondaryCoeff A B c D e
      n g hn hg hrel hA hB hc hD he

set_option maxHeartbeats 2000000 in
theorem polynomialSecondaryInvariantEquations68_of_loadL
    (l beta gamma delta epsilon zeta i4 i3 : k)
    (A B C0 c D E e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hl : l = 0) (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (hC0 : C0 = (1 / 3 : k) • A ^ 2 + c)
    (hE0 : E = (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)
    (hI4 : firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
      A B C0 D E = C i4)
    (hI3 : firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
      A B C0 D E = C i3) :
    firstSecondaryFour68 (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
        (e.coeff (6 * n - g)) = 0 ∧
      firstSecondaryThree68 (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
        (e.coeff (6 * n - g)) = 0 := by
  have ht4 : 9 * n - 2 * g ≠ 0 := by omega
  have ht3 : 10 * n - 2 * g ≠ 0 := by omega
  have hfour := congrArg (fun p : k[X] => p.coeff (9 * n - 2 * g)) hI4
  rw [hC0, hE0, firstIntegralFourPolynomial68_cubicCoordinates,
    cubicFirstIntegralFourPolynomial68_secondaryCoeff_of_loadL
      l beta gamma delta epsilon zeta A B c D e n g hn hg hl hrel
      hA hB hc hD he] at hfour
  simp only [coeff_C, if_neg ht4] at hfour
  have hthree := congrArg (fun p : k[X] => p.coeff (10 * n - 2 * g)) hI3
  rw [hC0, hE0, firstIntegralThreePolynomial68_cubicCoordinates,
    cubicFirstIntegralThreePolynomial68_secondaryCoeff_of_loadL
      l beta gamma delta epsilon zeta A B c D e n g hn hg hl hrel
      hA hB hc hD he] at hthree
  simp only [coeff_C, if_neg ht3] at hthree
  constructor
  · exact (mul_eq_zero.mp hfour).resolve_left (by norm_num)
  · exact (mul_eq_zero.mp hthree).resolve_left (by norm_num)

/-! ## One-form load cutoffs after `l = 0` -/

private theorem cubicC0_degreeBound68 (A c : k[X]) (n g : ℕ)
    (hA : A.natDegree ≤ 2 * n) (hc : c.natDegree ≤ 4 * n - g) :
    ((1 / 3 : k) • A ^ 2 + c).natDegree ≤ 4 * n := by
  compute_degree
  omega

private theorem cubicE_degreeBound68 (A c e : k[X]) (n g : ℕ)
    (hA : A.natDegree ≤ 2 * n) (hc : c.natDegree ≤ 4 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e).natDegree ≤ 6 * n := by
  compute_degree
  omega

set_option maxHeartbeats 3000000 in
theorem cubicLoadRowTwoPolynomial68_degree_lt_of_loadL
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hl : l = 0) (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadRowTwoPolynomial68 l alpha beta gamma delta epsilon zeta eta
      A B c D e).natDegree < 11 * n - 2 * g - 1 := by
  let C0 := (1 / 3 : k) • A ^ 2 + c
  let E := (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
  let Sl := cubicLoadSPolynomial68 l alpha beta delta A B c
  let Tl := cubicLoadTPolynomial68 l alpha beta gamma epsilon A B c D
  let Ul := cubicLoadUPolynomial68 l alpha beta gamma delta zeta A B c D e
  let Vl := cubicLoadVPolynomial68 l alpha beta gamma delta epsilon eta
    A B c D e
  have hT : Tl.natDegree ≤ 4 * n :=
    cubicLoadTPolynomial68_degreeBound_of_loadL l alpha beta gamma epsilon
      A B c D n g hl hA hB hc hD
  have hV : Vl.natDegree ≤ 6 * n :=
    cubicLoadVPolynomial68_degreeBound_of_loadL l alpha beta gamma delta
      epsilon eta A B c D e n g hl hA hB hc hD he
  have hC0 : C0.natDegree ≤ 4 * n := cubicC0_degreeBound68 A c n g hA hc
  have hE : E.natDegree ≤ 6 * n := cubicE_degreeBound68 A c e n g hA hc he
  rcases le_total g n with hgle | hnge
  · have hS : Sl.natDegree ≤ 3 * n - g :=
      (cubicLoadSPolynomial68_degreeBound_of_loadL l alpha beta delta A B c
        n g hl hA hB hc).trans (by rw [max_eq_right (by omega)])
    have hU : Ul.natDegree ≤ 5 * n - g :=
      (cubicLoadUPolynomial68_degreeBound_of_loadL l alpha beta gamma delta
        zeta A B c D e n g hl hA hB hc hD he).trans
        (by rw [max_eq_right (by omega)])
    have hUlC : (Ul * derivative C0).natDegree < 11 * n - 2 * g - 1 := by
      compute_degree; omega
    have hTlD : (Tl * derivative D).natDegree < 11 * n - 2 * g - 1 := by
      compute_degree; omega
    have hSlE : (Sl * derivative E).natDegree < 11 * n - 2 * g - 1 := by
      compute_degree; omega
    have hBVl : (B * derivative Vl).natDegree < 11 * n - 2 * g - 1 := by
      compute_degree; omega
    have hC0Ul : (C0 * derivative Ul).natDegree < 11 * n - 2 * g - 1 := by
      compute_degree; omega
    have hDTl : (D * derivative Tl).natDegree < 11 * n - 2 * g - 1 := by
      compute_degree; omega
    change (Ul * derivative C0 + (2 : k) • (Tl * derivative D) +
      (3 : k) • (Sl * derivative E) - (3 : k) • (B * derivative Vl) -
      (2 : k) • (C0 * derivative Ul) - D * derivative Tl).natDegree < _
    compute_degree
    omega
  · have hS : Sl.natDegree ≤ 2 * n :=
      (cubicLoadSPolynomial68_degreeBound_of_loadL l alpha beta delta A B c
        n g hl hA hB hc).trans (by rw [max_eq_left (by omega)])
    have hU : Ul.natDegree ≤ 4 * n :=
      (cubicLoadUPolynomial68_degreeBound_of_loadL l alpha beta gamma delta
        zeta A B c D e n g hl hA hB hc hD he).trans
        (by rw [max_eq_left (by omega)])
    have hUlC : (Ul * derivative C0).natDegree < 11 * n - 2 * g - 1 := by
      compute_degree; omega
    have hTlD : (Tl * derivative D).natDegree < 11 * n - 2 * g - 1 := by
      compute_degree; omega
    have hSlE : (Sl * derivative E).natDegree < 11 * n - 2 * g - 1 := by
      compute_degree; omega
    have hBVl : (B * derivative Vl).natDegree < 11 * n - 2 * g - 1 := by
      compute_degree; omega
    have hC0Ul : (C0 * derivative Ul).natDegree < 11 * n - 2 * g - 1 := by
      compute_degree; omega
    have hDTl : (D * derivative Tl).natDegree < 11 * n - 2 * g - 1 := by
      compute_degree; omega
    change (Ul * derivative C0 + (2 : k) • (Tl * derivative D) +
      (3 : k) • (Sl * derivative E) - (3 : k) • (B * derivative Vl) -
      (2 : k) • (C0 * derivative Ul) - D * derivative Tl).natDegree < _
    compute_degree
    omega

set_option maxHeartbeats 3000000 in
/-- The second one-form load is below the first secondary face once `l = 0`
and `g < n`.  The `alpha A^2` piece of `T` times `E'` reaches the face as
soon as `g ≥ n`. -/
theorem cubicLoadRowOnePolynomial68_degree_lt_of_loadL
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hl : l = 0) (hg_lt : g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadRowOnePolynomial68 l alpha beta gamma delta epsilon zeta eta
      A B c D e).natDegree < 12 * n - 2 * g - 1 := by
  let C0 := (1 / 3 : k) • A ^ 2 + c
  let E := (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
  let Tl := cubicLoadTPolynomial68 l alpha beta gamma epsilon A B c D
  let Ul := cubicLoadUPolynomial68 l alpha beta gamma delta zeta A B c D e
  let Vl := cubicLoadVPolynomial68 l alpha beta gamma delta epsilon eta
    A B c D e
  have hT : Tl.natDegree ≤ 4 * n :=
    cubicLoadTPolynomial68_degreeBound_of_loadL l alpha beta gamma epsilon
      A B c D n g hl hA hB hc hD
  have hU : Ul.natDegree ≤ 5 * n - g :=
    (cubicLoadUPolynomial68_degreeBound_of_loadL l alpha beta gamma delta
      zeta A B c D e n g hl hA hB hc hD he).trans
      (by rw [max_eq_right (by omega)])
  have hV : Vl.natDegree ≤ 6 * n :=
    cubicLoadVPolynomial68_degreeBound_of_loadL l alpha beta gamma delta
      epsilon eta A B c D e n g hl hA hB hc hD he
  have hC0 : C0.natDegree ≤ 4 * n := cubicC0_degreeBound68 A c n g hA hc
  have hE : E.natDegree ≤ 6 * n := cubicE_degreeBound68 A c e n g hA hc he
  have hUlD : (Ul * derivative D).natDegree < 12 * n - 2 * g - 1 := by
    compute_degree; omega
  have hTlE : (Tl * derivative E).natDegree < 12 * n - 2 * g - 1 := by
    compute_degree; omega
  have hC0Vl : (C0 * derivative Vl).natDegree < 12 * n - 2 * g - 1 := by
    compute_degree; omega
  have hDUl : (D * derivative Ul).natDegree < 12 * n - 2 * g - 1 := by
    compute_degree; omega
  change (Ul * derivative D + (2 : k) • (Tl * derivative E) -
    (2 : k) • (C0 * derivative Vl) - D * derivative Ul).natDegree < _
  compute_degree
  omega

set_option maxHeartbeats 3000000 in
/-- After the extra vanishing `alpha = 0`, the second one-form load is
below the first secondary face throughout `2g < 3n`. -/
theorem cubicLoadRowOnePolynomial68_degree_lt_of_loadL_alpha
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hl : l = 0) (halpha : alpha = 0)
    (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadRowOnePolynomial68 l alpha beta gamma delta epsilon zeta eta
      A B c D e).natDegree < 12 * n - 2 * g - 1 := by
  let C0 := (1 / 3 : k) • A ^ 2 + c
  let E := (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
  let Tl := cubicLoadTPolynomial68 l alpha beta gamma epsilon A B c D
  let Ul := cubicLoadUPolynomial68 l alpha beta gamma delta zeta A B c D e
  let Vl := cubicLoadVPolynomial68 l alpha beta gamma delta epsilon eta
    A B c D e
  have hU : Ul.natDegree ≤ 4 * n :=
    cubicLoadUPolynomial68_degreeBound_of_loadL_alpha l alpha beta gamma
      delta zeta A B c D e n g hl halpha hA hB hc hD he
  have hC0 : C0.natDegree ≤ 4 * n := cubicC0_degreeBound68 A c n g hA hc
  have hE : E.natDegree ≤ 6 * n := cubicE_degreeBound68 A c e n g hA hc he
  rcases le_total g n with hgle | hnge
  · have hT : Tl.natDegree ≤ 3 * n - g :=
      (cubicLoadTPolynomial68_degreeBound_of_loadL_alpha l alpha beta gamma
        epsilon A B c D n g hl halpha hA hB hc hD).trans
        (by rw [max_eq_right (by omega)])
    have hV : Vl.natDegree ≤ 5 * n - g :=
      (cubicLoadVPolynomial68_degreeBound_of_loadL_alpha l alpha beta gamma
        delta epsilon eta A B c D e n g hl halpha hA hB hc hD he).trans
        (by rw [max_eq_right (by omega)])
    have hUlD : (Ul * derivative D).natDegree < 12 * n - 2 * g - 1 := by
      compute_degree; omega
    have hTlE : (Tl * derivative E).natDegree < 12 * n - 2 * g - 1 := by
      compute_degree; omega
    have hC0Vl : (C0 * derivative Vl).natDegree < 12 * n - 2 * g - 1 := by
      compute_degree; omega
    have hDUl : (D * derivative Ul).natDegree < 12 * n - 2 * g - 1 := by
      compute_degree; omega
    change (Ul * derivative D + (2 : k) • (Tl * derivative E) -
      (2 : k) • (C0 * derivative Vl) - D * derivative Ul).natDegree < _
    compute_degree
    omega
  · have hT : Tl.natDegree ≤ 2 * n :=
      (cubicLoadTPolynomial68_degreeBound_of_loadL_alpha l alpha beta gamma
        epsilon A B c D n g hl halpha hA hB hc hD).trans
        (by rw [max_eq_left (by omega)])
    have hV : Vl.natDegree ≤ 4 * n :=
      (cubicLoadVPolynomial68_degreeBound_of_loadL_alpha l alpha beta gamma
        delta epsilon eta A B c D e n g hl halpha hA hB hc hD he).trans
        (by rw [max_eq_left (by omega)])
    have hUlD : (Ul * derivative D).natDegree < 12 * n - 2 * g - 1 := by
      compute_degree; omega
    have hTlE : (Tl * derivative E).natDegree < 12 * n - 2 * g - 1 := by
      compute_degree; omega
    have hC0Vl : (C0 * derivative Vl).natDegree < 12 * n - 2 * g - 1 := by
      compute_degree; omega
    have hDUl : (D * derivative Ul).natDegree < 12 * n - 2 * g - 1 := by
      compute_degree; omega
    change (Ul * derivative D + (2 : k) • (Tl * derivative E) -
      (2 : k) • (C0 * derivative Vl) - D * derivative Ul).natDegree < _
    compute_degree
    omega

set_option maxHeartbeats 3000000 in
theorem cubicLoadRowZeroPolynomial68_degree_lt_of_loadL
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hl : l = 0) (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadRowZeroPolynomial68 l alpha beta gamma delta epsilon zeta eta
      A B c D e).natDegree < 13 * n - 2 * g - 1 := by
  let E := (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
  let Ul := cubicLoadUPolynomial68 l alpha beta gamma delta zeta A B c D e
  let Vl := cubicLoadVPolynomial68 l alpha beta gamma delta epsilon eta
    A B c D e
  have hV : Vl.natDegree ≤ 6 * n :=
    cubicLoadVPolynomial68_degreeBound_of_loadL l alpha beta gamma delta
      epsilon eta A B c D e n g hl hA hB hc hD he
  have hE : E.natDegree ≤ 6 * n := cubicE_degreeBound68 A c e n g hA hc he
  rcases le_total g n with hgle | hnge
  · have hU : Ul.natDegree ≤ 5 * n - g :=
      (cubicLoadUPolynomial68_degreeBound_of_loadL l alpha beta gamma delta
        zeta A B c D e n g hl hA hB hc hD he).trans
        (by rw [max_eq_right (by omega)])
    have hUlE : (Ul * derivative E).natDegree < 13 * n - 2 * g - 1 := by
      compute_degree; omega
    have hDVl : (D * derivative Vl).natDegree < 13 * n - 2 * g - 1 := by
      compute_degree; omega
    change (Ul * derivative E - D * derivative Vl).natDegree < _
    compute_degree
    omega
  · have hU : Ul.natDegree ≤ 4 * n :=
      (cubicLoadUPolynomial68_degreeBound_of_loadL l alpha beta gamma delta
        zeta A B c D e n g hl hA hB hc hD he).trans
        (by rw [max_eq_left (by omega)])
    have hUlE : (Ul * derivative E).natDegree < 13 * n - 2 * g - 1 := by
      compute_degree; omega
    have hDVl : (D * derivative Vl).natDegree < 13 * n - 2 * g - 1 := by
      compute_degree; omega
    change (Ul * derivative E - D * derivative Vl).natDegree < _
    compute_degree
    omega

end RelaxedSecondaryFace68

section RelaxedSecondaryOneForms68

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Homogeneous one-form coefficients under `2g < 3n` -/

set_option maxHeartbeats 2000000 in
theorem firstSecondaryCoreRowTwoPolynomial68_coeff_of_two_mul_gap_lt_three
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (firstSecondaryCoreRowTwoPolynomial68 A B c D e).coeff
        (11 * n - 2 * g - 1) =
      (8 / 27 : k) * firstSecondaryTwo68 (n : k) (g : k)
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
        (e.coeff (6 * n - g)) := by
  have hA2deg : (A ^ 2).natDegree ≤ 4 * n := by
    compute_degree
    omega
  have hA2coeff : (A ^ 2).coeff (4 * n) = A.coeff (2 * n) ^ 2 := by
    have h := coeff_pow_at_bound68 A (2 * n) 2 hA
    have hi : 2 * (2 * n) = 4 * n := by omega
    simpa only [hi] using h
  have h1 : (A ^ 2 * B * derivative c).coeff
      (11 * n - 2 * g - 1) =
      A.coeff (2 * n) ^ 2 * B.coeff (3 * n - g) *
        c.coeff (4 * n - g) * ((4 * n - g : ℕ) : k) := by
    have h := coeff_mul_mul_derivative_at_bounds68 (A ^ 2) B c
      (4 * n) (3 * n - g) (4 * n - g) (by omega) hA2deg hB hc
    have hi : 4 * n + (3 * n - g) + (4 * n - g) - 1 =
        11 * n - 2 * g - 1 := by omega
    rw [hi, hA2coeff] at h
    exact h
  have h2 : (A ^ 2 * c * derivative B).coeff
      (11 * n - 2 * g - 1) =
      A.coeff (2 * n) ^ 2 * c.coeff (4 * n - g) *
        B.coeff (3 * n - g) * ((3 * n - g : ℕ) : k) := by
    have h := coeff_mul_mul_derivative_at_bounds68 (A ^ 2) c B
      (4 * n) (4 * n - g) (3 * n - g) (by omega) hA2deg hc hB
    have hi : 4 * n + (4 * n - g) + (3 * n - g) - 1 =
        11 * n - 2 * g - 1 := by omega
    rw [hi, hA2coeff] at h
    exact h
  have h3 : (A * B * c * derivative A).coeff
      (11 * n - 2 * g - 1) =
      A.coeff (2 * n) * B.coeff (3 * n - g) *
        c.coeff (4 * n - g) * A.coeff (2 * n) * ((2 * n : ℕ) : k) := by
    have h := coeff_mul_mul_mul_derivative_at_bounds68 A B c A
      (2 * n) (3 * n - g) (4 * n - g) (2 * n) (by omega)
      hA hB hc hA
    have hi : 2 * n + (3 * n - g) + (4 * n - g) + 2 * n - 1 =
        11 * n - 2 * g - 1 := by omega
    simpa only [hi] using h
  have h4 : (A * D * derivative c).coeff (11 * n - 2 * g - 1) =
      A.coeff (2 * n) * D.coeff (5 * n - g) *
        c.coeff (4 * n - g) * ((4 * n - g : ℕ) : k) := by
    have h := coeff_mul_mul_derivative_at_bounds68 A D c
      (2 * n) (5 * n - g) (4 * n - g) (by omega) hA hD hc
    have hi : 2 * n + (5 * n - g) + (4 * n - g) - 1 =
        11 * n - 2 * g - 1 := by omega
    simpa only [hi] using h
  have h5 : (A * c * derivative D).coeff (11 * n - 2 * g - 1) =
      A.coeff (2 * n) * c.coeff (4 * n - g) *
        D.coeff (5 * n - g) * ((5 * n - g : ℕ) : k) := by
    have h := coeff_mul_mul_derivative_at_bounds68 A c D
      (2 * n) (4 * n - g) (5 * n - g) (by omega) hA hc hD
    have hi : 2 * n + (4 * n - g) + (5 * n - g) - 1 =
        11 * n - 2 * g - 1 := by omega
    simpa only [hi] using h
  have h6 : (B * e * derivative A).coeff (11 * n - 2 * g - 1) =
      B.coeff (3 * n - g) * e.coeff (6 * n - g) *
        A.coeff (2 * n) * ((2 * n : ℕ) : k) := by
    have h := coeff_mul_mul_derivative_at_bounds68 B e A
      (3 * n - g) (6 * n - g) (2 * n) (by omega) hB he hA
    have hi : (3 * n - g) + (6 * n - g) + 2 * n - 1 =
        11 * n - 2 * g - 1 := by omega
    simpa only [hi] using h
  have h7 : (D * c * derivative A).coeff (11 * n - 2 * g - 1) =
      D.coeff (5 * n - g) * c.coeff (4 * n - g) *
        A.coeff (2 * n) * ((2 * n : ℕ) : k) := by
    have h := coeff_mul_mul_derivative_at_bounds68 D c A
      (5 * n - g) (4 * n - g) (2 * n) (by omega) hD hc hA
    have hi : (5 * n - g) + (4 * n - g) + 2 * n - 1 =
        11 * n - 2 * g - 1 := by omega
    simpa only [hi] using h
  have h8 : (D * derivative e).coeff (11 * n - 2 * g - 1) =
      D.coeff (5 * n - g) * e.coeff (6 * n - g) *
        ((6 * n - g : ℕ) : k) := by
    have h := coeff_mul_derivative_at_bounds68 D e
      (5 * n - g) (6 * n - g) (by omega) hD he
    have hi : (5 * n - g) + (6 * n - g) - 1 =
        11 * n - 2 * g - 1 := by omega
    simpa only [hi] using h
  have h9 : (e * derivative D).coeff (11 * n - 2 * g - 1) =
      e.coeff (6 * n - g) * D.coeff (5 * n - g) *
        ((5 * n - g : ℕ) : k) := by
    have h := coeff_mul_derivative_at_bounds68 e D
      (6 * n - g) (5 * n - g) (by omega) he hD
    have hi : (6 * n - g) + (5 * n - g) - 1 =
        11 * n - 2 * g - 1 := by omega
    simpa only [hi] using h
  simp only [firstSecondaryCoreRowTwoPolynomial68, coeff_smul, coeff_add,
    coeff_sub, h1, h2, h3, h4, h5, h6, h7, h8, h9, smul_eq_mul]
  have hg3 : g ≤ 3 * n := by omega
  have hg4 : g ≤ 4 * n := by omega
  have hg5 : g ≤ 5 * n := by omega
  have hg6 : g ≤ 6 * n := by omega
  have hcast3 : (((3 * n - g : ℕ) : k)) = (n : k) * 3 - (g : k) := by
    rw [Nat.cast_sub hg3]
    push_cast
    ring
  have hcast4 : (((4 * n - g : ℕ) : k)) = (n : k) * 4 - (g : k) := by
    rw [Nat.cast_sub hg4]
    push_cast
    ring
  have hcast5 : (((5 * n - g : ℕ) : k)) = (n : k) * 5 - (g : k) := by
    rw [Nat.cast_sub hg5]
    push_cast
    ring
  have hcast6 : (((6 * n - g : ℕ) : k)) = (n : k) * 6 - (g : k) := by
    rw [Nat.cast_sub hg6]
    push_cast
    ring
  rw [hcast3, hcast4, hcast5, hcast6]
  push_cast
  simp only [firstSecondaryTwo68]
  ring

set_option maxHeartbeats 2000000 in
theorem cubicHomogeneousRowTwoPolynomial68_secondaryCoeff_of_two_mul_gap_lt_three
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicHomogeneousRowTwoPolynomial68 A B c D e).coeff
        (11 * n - 2 * g - 1) =
      (8 / 27 : k) * firstSecondaryTwo68 (n : k) (g : k)
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
        (e.coeff (6 * n - g)) := by
  have hrem : (cubicRemainderRowTwoPolynomial68 A B c D).natDegree <
      11 * n - 2 * g - 1 := by
    simp only [cubicRemainderRowTwoPolynomial68]
    compute_degree
    omega
  rw [cubicHomogeneousRowTwoPolynomial68_eq_expanded,
    cubicHomogeneousRowTwoExpandedPolynomial68_split, coeff_add,
    coeff_eq_zero_of_natDegree_lt hrem, add_zero]
  exact firstSecondaryCoreRowTwoPolynomial68_coeff_of_two_mul_gap_lt_three
    A B c D e n g hn hg hrel hA hB hc hD he

set_option maxHeartbeats 3000000 in
theorem integratedLowerRowTwoPolynomial68_secondaryCoeff_of_loadL
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hl : l = 0) (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (lowerRowTwoPolynomial68
      (integratedSPolynomial68 l alpha beta delta A B
        ((1 / 3 : k) • A ^ 2 + c) D)
      (integratedTPolynomial68 l alpha beta gamma epsilon A B
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      (integratedUPolynomial68 l alpha beta gamma delta zeta A B
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta A B
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      B ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)).coeff
          (11 * n - 2 * g - 1) =
      (8 / 27 : k) * firstSecondaryTwo68 (n : k) (g : k)
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
        (e.coeff (6 * n - g)) := by
  have hcoords := integratedPolynomial68_cubicCoordinates
    l alpha beta gamma delta epsilon zeta eta A B c D e
  rw [hcoords.s_eq, hcoords.t_eq, hcoords.u_eq, hcoords.v_eq,
    cubicRowTwoPolynomial68_split, coeff_add,
    coeff_eq_zero_of_natDegree_lt
      (cubicLoadRowTwoPolynomial68_degree_lt_of_loadL
        l alpha beta gamma delta epsilon zeta eta A B c D e n g
        hn hg hl hrel hA hB hc hD he), add_zero]
  exact cubicHomogeneousRowTwoPolynomial68_secondaryCoeff_of_two_mul_gap_lt_three
    A B c D e n g hn hg hrel hA hB hc hD he

set_option maxHeartbeats 2000000 in
theorem firstSecondaryCoreRowOnePolynomial68_coeff_of_two_mul_gap_lt_three
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (firstSecondaryCoreRowOnePolynomial68 A B c D e).coeff
        (12 * n - 2 * g - 1) =
      (-8 / 81 : k) * firstSecondaryOne68 (n : k) (g : k)
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
        (e.coeff (6 * n - g)) := by
  have hA2deg : (A ^ 2).natDegree ≤ 4 * n := by
    compute_degree
    omega
  have hA3deg : (A ^ 3).natDegree ≤ 6 * n := by
    compute_degree
    omega
  have hB2deg : (B ^ 2).natDegree ≤ 6 * n - 2 * g := by
    compute_degree
    omega
  have hD2deg : (D ^ 2).natDegree ≤ 10 * n - 2 * g := by
    compute_degree
    omega
  have hA2 : (A ^ 2).coeff (4 * n) = A.coeff (2 * n) ^ 2 := by
    have h := coeff_pow_at_bound68 A (2 * n) 2 hA
    have hi : 2 * (2 * n) = 4 * n := by omega
    simpa only [hi] using h
  have hA3 : (A ^ 3).coeff (6 * n) = A.coeff (2 * n) ^ 3 := by
    have h := coeff_pow_at_bound68 A (2 * n) 3 hA
    have hi : 3 * (2 * n) = 6 * n := by omega
    simpa only [hi] using h
  have hB2 : (B ^ 2).coeff (6 * n - 2 * g) =
      B.coeff (3 * n - g) ^ 2 := by
    have h := coeff_pow_at_bound68 B (3 * n - g) 2 hB
    have hi : 2 * (3 * n - g) = 6 * n - 2 * g := by omega
    simpa only [hi] using h
  have hD2 : (D ^ 2).coeff (10 * n - 2 * g) =
      D.coeff (5 * n - g) ^ 2 := by
    have h := coeff_pow_at_bound68 D (5 * n - g) 2 hD
    have hi : 2 * (5 * n - g) = 10 * n - 2 * g := by omega
    simpa only [hi] using h
  have h1 : (A ^ 3 * B * derivative B).coeff (12 * n - 2 * g - 1) =
      A.coeff (2 * n) ^ 3 * B.coeff (3 * n - g) ^ 2 *
        ((3 * n - g : ℕ) : k) := by
    have h := coeff_mul_mul_derivative_at_bounds68 (A ^ 3) B B
      (6 * n) (3 * n - g) (3 * n - g) (by omega) hA3deg hB hB
    have hi : 6 * n + (3 * n - g) + (3 * n - g) - 1 =
        12 * n - 2 * g - 1 := by omega
    rw [hi, hA3] at h
    ring_nf at h ⊢
    exact h
  have h2 : (A ^ 2 * B ^ 2 * derivative A).coeff
      (12 * n - 2 * g - 1) =
      A.coeff (2 * n) ^ 2 * B.coeff (3 * n - g) ^ 2 *
        A.coeff (2 * n) * ((2 * n : ℕ) : k) := by
    have h := coeff_mul_mul_derivative_at_bounds68 (A ^ 2) (B ^ 2) A
      (4 * n) (6 * n - 2 * g) (2 * n) (by omega)
      hA2deg hB2deg hA
    have hi : 4 * n + (6 * n - 2 * g) + 2 * n - 1 =
        12 * n - 2 * g - 1 := by omega
    rw [hi, hA2, hB2] at h
    exact h
  have h3 : (A ^ 2 * B * derivative D).coeff
      (12 * n - 2 * g - 1) =
      A.coeff (2 * n) ^ 2 * B.coeff (3 * n - g) *
        D.coeff (5 * n - g) * ((5 * n - g : ℕ) : k) := by
    have h := coeff_mul_mul_derivative_at_bounds68 (A ^ 2) B D
      (4 * n) (3 * n - g) (5 * n - g) (by omega) hA2deg hB hD
    have hi : 4 * n + (3 * n - g) + (5 * n - g) - 1 =
        12 * n - 2 * g - 1 := by omega
    rw [hi, hA2] at h
    exact h
  have h4 : (A ^ 2 * D * derivative B).coeff
      (12 * n - 2 * g - 1) =
      A.coeff (2 * n) ^ 2 * D.coeff (5 * n - g) *
        B.coeff (3 * n - g) * ((3 * n - g : ℕ) : k) := by
    have h := coeff_mul_mul_derivative_at_bounds68 (A ^ 2) D B
      (4 * n) (5 * n - g) (3 * n - g) (by omega) hA2deg hD hB
    have hi : 4 * n + (5 * n - g) + (3 * n - g) - 1 =
        12 * n - 2 * g - 1 := by omega
    rw [hi, hA2] at h
    exact h
  have h5 : (A * c * derivative e).coeff (12 * n - 2 * g - 1) =
      A.coeff (2 * n) * c.coeff (4 * n - g) *
        e.coeff (6 * n - g) * ((6 * n - g : ℕ) : k) := by
    have h := coeff_mul_mul_derivative_at_bounds68 A c e
      (2 * n) (4 * n - g) (6 * n - g) (by omega) hA hc he
    have hi : 2 * n + (4 * n - g) + (6 * n - g) - 1 =
        12 * n - 2 * g - 1 := by omega
    simpa only [hi] using h
  have h6 : (A * e * derivative c).coeff (12 * n - 2 * g - 1) =
      A.coeff (2 * n) * e.coeff (6 * n - g) *
        c.coeff (4 * n - g) * ((4 * n - g : ℕ) : k) := by
    have h := coeff_mul_mul_derivative_at_bounds68 A e c
      (2 * n) (6 * n - g) (4 * n - g) (by omega) hA he hc
    have hi : 2 * n + (6 * n - g) + (4 * n - g) - 1 =
        12 * n - 2 * g - 1 := by omega
    simpa only [hi] using h
  have h7 : (D ^ 2 * derivative A).coeff (12 * n - 2 * g - 1) =
      D.coeff (5 * n - g) ^ 2 * A.coeff (2 * n) *
        ((2 * n : ℕ) : k) := by
    have h := coeff_mul_derivative_at_bounds68 (D ^ 2) A
      (10 * n - 2 * g) (2 * n) (by omega) hD2deg hA
    have hi : (10 * n - 2 * g) + 2 * n - 1 =
        12 * n - 2 * g - 1 := by omega
    rw [hi, hD2] at h
    exact h
  have h8 : (e * derivative e).coeff (12 * n - 2 * g - 1) =
      e.coeff (6 * n - g) ^ 2 * ((6 * n - g : ℕ) : k) := by
    have h := coeff_mul_derivative_at_bounds68 e e
      (6 * n - g) (6 * n - g) (by omega) he he
    have hi : (6 * n - g) + (6 * n - g) - 1 =
        12 * n - 2 * g - 1 := by omega
    rw [hi] at h
    ring_nf at h ⊢
    exact h
  simp only [firstSecondaryCoreRowOnePolynomial68, coeff_smul, coeff_add,
    coeff_sub, h1, h2, h3, h4, h5, h6, h7, h8, smul_eq_mul]
  have hg3 : g ≤ 3 * n := by omega
  have hg4 : g ≤ 4 * n := by omega
  have hg5 : g ≤ 5 * n := by omega
  have hg6 : g ≤ 6 * n := by omega
  have hcast3 : (((3 * n - g : ℕ) : k)) = 3 * (n : k) - (g : k) := by
    rw [Nat.cast_sub hg3]
    push_cast
    rfl
  have hcast4 : (((4 * n - g : ℕ) : k)) = 4 * (n : k) - (g : k) := by
    rw [Nat.cast_sub hg4]
    push_cast
    rfl
  have hcast5 : (((5 * n - g : ℕ) : k)) = 5 * (n : k) - (g : k) := by
    rw [Nat.cast_sub hg5]
    push_cast
    rfl
  have hcast6 : (((6 * n - g : ℕ) : k)) = 6 * (n : k) - (g : k) := by
    rw [Nat.cast_sub hg6]
    push_cast
    rfl
  rw [hcast3, hcast4, hcast5, hcast6]
  push_cast
  simp only [firstSecondaryOne68]
  ring

set_option maxHeartbeats 2000000 in
theorem cubicHomogeneousRowOnePolynomial68_secondaryCoeff_of_two_mul_gap_lt_three
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicHomogeneousRowOnePolynomial68 A B c D e).coeff
        (12 * n - 2 * g - 1) =
      (-8 / 81 : k) * firstSecondaryOne68 (n : k) (g : k)
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
        (e.coeff (6 * n - g)) := by
  have hrem : (cubicRemainderRowOnePolynomial68 A B c D e).natDegree <
      12 * n - 2 * g - 1 := by
    simp only [cubicRemainderRowOnePolynomial68]
    compute_degree
    omega
  rw [cubicHomogeneousRowOnePolynomial68_eq_expanded,
    cubicHomogeneousRowOneExpandedPolynomial68, coeff_add,
    coeff_eq_zero_of_natDegree_lt hrem, add_zero]
  exact firstSecondaryCoreRowOnePolynomial68_coeff_of_two_mul_gap_lt_three
    A B c D e n g hn hg hrel hA hB hc hD he

set_option maxHeartbeats 3000000 in
theorem integratedLowerRowOnePolynomial68_secondaryCoeff_of_loadL
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hl : l = 0) (hg_lt : g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (lowerRowOnePolynomial68
      (integratedTPolynomial68 l alpha beta gamma epsilon A B
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      (integratedUPolynomial68 l alpha beta gamma delta zeta A B
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta A B
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)).coeff
          (12 * n - 2 * g - 1) =
      (-8 / 81 : k) * firstSecondaryOne68 (n : k) (g : k)
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
        (e.coeff (6 * n - g)) := by
  have hrel : 2 * g < 3 * n := by omega
  have hcoords := integratedPolynomial68_cubicCoordinates
    l alpha beta gamma delta epsilon zeta eta A B c D e
  rw [hcoords.t_eq, hcoords.u_eq, hcoords.v_eq,
    cubicRowOnePolynomial68_split, coeff_add,
    coeff_eq_zero_of_natDegree_lt
      (cubicLoadRowOnePolynomial68_degree_lt_of_loadL
        l alpha beta gamma delta epsilon zeta eta A B c D e n g
        hn hg hl hg_lt hA hB hc hD he), add_zero]
  exact cubicHomogeneousRowOnePolynomial68_secondaryCoeff_of_two_mul_gap_lt_three
    A B c D e n g hn hg hrel hA hB hc hD he

set_option maxHeartbeats 3000000 in
theorem integratedLowerRowOnePolynomial68_secondaryCoeff_of_loadL_alpha
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hl : l = 0) (halpha : alpha = 0)
    (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (lowerRowOnePolynomial68
      (integratedTPolynomial68 l alpha beta gamma epsilon A B
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      (integratedUPolynomial68 l alpha beta gamma delta zeta A B
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta A B
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)).coeff
          (12 * n - 2 * g - 1) =
      (-8 / 81 : k) * firstSecondaryOne68 (n : k) (g : k)
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
        (e.coeff (6 * n - g)) := by
  have hcoords := integratedPolynomial68_cubicCoordinates
    l alpha beta gamma delta epsilon zeta eta A B c D e
  rw [hcoords.t_eq, hcoords.u_eq, hcoords.v_eq,
    cubicRowOnePolynomial68_split, coeff_add,
    coeff_eq_zero_of_natDegree_lt
      (cubicLoadRowOnePolynomial68_degree_lt_of_loadL_alpha
        l alpha beta gamma delta epsilon zeta eta A B c D e n g
        hn hg hl halpha hrel hA hB hc hD he), add_zero]
  exact cubicHomogeneousRowOnePolynomial68_secondaryCoeff_of_two_mul_gap_lt_three
    A B c D e n g hn hg hrel hA hB hc hD he

set_option maxHeartbeats 2000000 in
theorem firstSecondaryCoreRowZeroPolynomial68_coeff_of_two_mul_gap_lt_three
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (firstSecondaryCoreRowZeroPolynomial68 A B c D e).coeff
        (13 * n - 2 * g - 1) =
      (8 / 81 : k) * (n : k) * A.coeff (2 * n) *
        firstSecondaryZero68
          (A.coeff (2 * n)) (B.coeff (3 * n - g))
          (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
          (e.coeff (6 * n - g)) := by
  have hA2deg : (A ^ 2).natDegree ≤ 4 * n := by
    compute_degree
    omega
  have hA2 : (A ^ 2).coeff (4 * n) = A.coeff (2 * n) ^ 2 := by
    have h := coeff_pow_at_bound68 A (2 * n) 2 hA
    have hi : 2 * (2 * n) = 4 * n := by omega
    simpa only [hi] using h
  have h1 : (A ^ 2 * B * c * derivative A).coeff
      (13 * n - 2 * g - 1) =
      A.coeff (2 * n) ^ 2 * B.coeff (3 * n - g) *
        c.coeff (4 * n - g) * A.coeff (2 * n) *
          ((2 * n : ℕ) : k) := by
    have h := coeff_mul_mul_mul_derivative_at_bounds68 (A ^ 2) B c A
      (4 * n) (3 * n - g) (4 * n - g) (2 * n) (by omega)
      hA2deg hB hc hA
    have hi : 4 * n + (3 * n - g) + (4 * n - g) + 2 * n - 1 =
        13 * n - 2 * g - 1 := by omega
    rw [hi, hA2] at h
    exact h
  have h2 : (A * D * c * derivative A).coeff
      (13 * n - 2 * g - 1) =
      A.coeff (2 * n) * D.coeff (5 * n - g) *
        c.coeff (4 * n - g) * A.coeff (2 * n) *
          ((2 * n : ℕ) : k) := by
    have h := coeff_mul_mul_mul_derivative_at_bounds68 A D c A
      (2 * n) (5 * n - g) (4 * n - g) (2 * n) (by omega)
      hA hD hc hA
    have hi : 2 * n + (5 * n - g) + (4 * n - g) + 2 * n - 1 =
        13 * n - 2 * g - 1 := by omega
    simpa only [hi] using h
  have h3 : (D * e * derivative A).coeff (13 * n - 2 * g - 1) =
      D.coeff (5 * n - g) * e.coeff (6 * n - g) *
        A.coeff (2 * n) * ((2 * n : ℕ) : k) := by
    have h := coeff_mul_mul_derivative_at_bounds68 D e A
      (5 * n - g) (6 * n - g) (2 * n) (by omega) hD he hA
    have hi : (5 * n - g) + (6 * n - g) + 2 * n - 1 =
        13 * n - 2 * g - 1 := by omega
    simpa only [hi] using h
  simp only [firstSecondaryCoreRowZeroPolynomial68, coeff_smul, coeff_sub,
    h1, h2, h3, smul_eq_mul]
  push_cast
  simp only [firstSecondaryZero68]
  ring

set_option maxHeartbeats 2000000 in
theorem cubicHomogeneousRowZeroPolynomial68_secondaryCoeff_of_two_mul_gap_lt_three
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicHomogeneousRowZeroPolynomial68 A B c D e).coeff
        (13 * n - 2 * g - 1) =
      (8 / 81 : k) * (n : k) * A.coeff (2 * n) *
        firstSecondaryZero68
          (A.coeff (2 * n)) (B.coeff (3 * n - g))
          (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
          (e.coeff (6 * n - g)) := by
  have hrem : (cubicRemainderRowZeroPolynomial68 A B c D e).natDegree <
      13 * n - 2 * g - 1 := by
    simp only [cubicRemainderRowZeroPolynomial68]
    compute_degree
    omega
  rw [cubicHomogeneousRowZeroPolynomial68_eq_expanded,
    cubicHomogeneousRowZeroExpandedPolynomial68, coeff_add,
    coeff_eq_zero_of_natDegree_lt hrem, add_zero]
  exact firstSecondaryCoreRowZeroPolynomial68_coeff_of_two_mul_gap_lt_three
    A B c D e n g hn hg hrel hA hB hc hD he

set_option maxHeartbeats 3000000 in
theorem integratedLowerRowZeroPolynomial68_secondaryCoeff_of_loadL
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hl : l = 0) (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (lowerRowZeroPolynomial68
      (integratedUPolynomial68 l alpha beta gamma delta zeta A B
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta A B
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      D ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)).coeff
        (13 * n - 2 * g - 1) =
      (8 / 81 : k) * (n : k) * A.coeff (2 * n) *
        firstSecondaryZero68
          (A.coeff (2 * n)) (B.coeff (3 * n - g))
          (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
          (e.coeff (6 * n - g)) := by
  have hcoords := integratedPolynomial68_cubicCoordinates
    l alpha beta gamma delta epsilon zeta eta A B c D e
  rw [hcoords.u_eq, hcoords.v_eq, cubicRowZeroPolynomial68_split, coeff_add,
    coeff_eq_zero_of_natDegree_lt
      (cubicLoadRowZeroPolynomial68_degree_lt_of_loadL
        l alpha beta gamma delta epsilon zeta eta A B c D e n g
        hn hg hl hrel hA hB hc hD he), add_zero]
  exact cubicHomogeneousRowZeroPolynomial68_secondaryCoeff_of_two_mul_gap_lt_three
    A B c D e n g hn hg hrel hA hB hc hD he

/-! ## Packaged face and classification -/

set_option maxHeartbeats 3000000 in
theorem integratedPolynomialLowerSystem_firstSecondaryFace68_of_loadL
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 c D E e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hl : l = 0) (hg_lt : g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (ha : A.coeff (2 * n) ≠ 0)
    (hC0 : C0 = (1 / 3 : k) • A ^ 2 + c)
    (hE0 : E = (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E) :
    FirstSecondaryFace68 (n : k) (g : k)
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
      (e.coeff (6 * n - g)) := by
  have hrel : 2 * g < 3 * n := by omega
  obtain ⟨i4, hI4⟩ := hsys.firstFour
  obtain ⟨i3, hI3⟩ := hsys.firstThree
  have hinv := polynomialSecondaryInvariantEquations68_of_loadL
    l beta gamma delta epsilon zeta i4 i3 A B C0 c D E e n g
    hn hg hl hrel hA hB hc hD he hC0 hE0 hI4 hI3
  have hrowTwo := hsys.rowTwo
  rw [hC0, hE0] at hrowTwo
  have htwo := congrArg
    (fun p : k[X] => p.coeff (11 * n - 2 * g - 1)) hrowTwo
  rw [integratedLowerRowTwoPolynomial68_secondaryCoeff_of_loadL
    l alpha beta gamma delta epsilon zeta eta A B c D e n g
    hn hg hl hrel hA hB hc hD he] at htwo
  simp only [coeff_zero] at htwo
  have htwo0 : firstSecondaryTwo68 (n : k) (g : k)
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
      (e.coeff (6 * n - g)) = 0 :=
    (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  have hrowOne := hsys.rowOne
  rw [hC0, hE0] at hrowOne
  have hone := congrArg
    (fun p : k[X] => p.coeff (12 * n - 2 * g - 1)) hrowOne
  rw [integratedLowerRowOnePolynomial68_secondaryCoeff_of_loadL
    l alpha beta gamma delta epsilon zeta eta A B c D e n g
    hn hg hl hg_lt hA hB hc hD he] at hone
  simp only [coeff_zero] at hone
  have hone0 : firstSecondaryOne68 (n : k) (g : k)
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
      (e.coeff (6 * n - g)) = 0 :=
    (mul_eq_zero.mp hone).resolve_left (by norm_num)
  have hrowZero := hsys.rowZero
  rw [hC0, hE0] at hrowZero
  have hzero := congrArg
    (fun p : k[X] => p.coeff (13 * n - 2 * g - 1)) hrowZero
  rw [integratedLowerRowZeroPolynomial68_secondaryCoeff_of_loadL
    l alpha beta gamma delta epsilon zeta eta A B c D e n g
    hn hg hl hrel hA hB hc hD he] at hzero
  have hindex : 13 * n - 2 * g - 1 ≠ 0 := by omega
  simp only [coeff_C, if_neg hindex] at hzero
  have hncast : (n : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hfactor : (8 / 81 : k) * (n : k) * A.coeff (2 * n) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hncast) ha
  have hzero0 : firstSecondaryZero68
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
      (e.coeff (6 * n - g)) = 0 :=
    (mul_eq_zero.mp hzero).resolve_left hfactor
  exact ⟨hinv.1, hinv.2, htwo0, hone0, hzero0⟩

/-- Full five-face classification after `l = 0` in the sharper chamber
`g < n` needed by the second one-form. -/
theorem integratedPolynomialLowerSystem_firstSecondaryClassified68_of_loadL
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 c D E e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hl : l = 0) (hg_lt : g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (ha : A.coeff (2 * n) ≠ 0)
    (hC0 : C0 = (1 / 3 : k) • A ^ 2 + c)
    (hE0 : E = (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E) :
    e.coeff (6 * n - g) = 0 ∧
      A.coeff (2 * n) * B.coeff (3 * n - g) =
        3 * D.coeff (5 * n - g) := by
  have hrel : 2 * g < 3 * n := by omega
  exact firstSecondaryFace68_classify_of_two_mul_gap_lt_three_mul_radius n g
    (A.coeff (2 * n)) (B.coeff (3 * n - g))
    (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
    (e.coeff (6 * n - g)) ha hn hrel
    (integratedPolynomialLowerSystem_firstSecondaryFace68_of_loadL
      l alpha beta gamma delta epsilon zeta eta terminal
      A B C0 c D E e n g hn hg hl hg_lt hA hB hc hD he ha hC0 hE0 hsys)

set_option maxHeartbeats 3000000 in
/-- After `l = 0` and `alpha = 0`, the five-face is available throughout
the relaxed chamber `2g < 3n`. -/
theorem integratedPolynomialLowerSystem_firstSecondaryFace68_of_loadL_alpha
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 c D E e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hl : l = 0) (halpha : alpha = 0)
    (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (ha : A.coeff (2 * n) ≠ 0)
    (hC0 : C0 = (1 / 3 : k) • A ^ 2 + c)
    (hE0 : E = (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E) :
    FirstSecondaryFace68 (n : k) (g : k)
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
      (e.coeff (6 * n - g)) := by
  obtain ⟨i4, hI4⟩ := hsys.firstFour
  obtain ⟨i3, hI3⟩ := hsys.firstThree
  have hinv := polynomialSecondaryInvariantEquations68_of_loadL
    l beta gamma delta epsilon zeta i4 i3 A B C0 c D E e n g
    hn hg hl hrel hA hB hc hD he hC0 hE0 hI4 hI3
  have hrowTwo := hsys.rowTwo
  rw [hC0, hE0] at hrowTwo
  have htwo := congrArg
    (fun p : k[X] => p.coeff (11 * n - 2 * g - 1)) hrowTwo
  rw [integratedLowerRowTwoPolynomial68_secondaryCoeff_of_loadL
    l alpha beta gamma delta epsilon zeta eta A B c D e n g
    hn hg hl hrel hA hB hc hD he] at htwo
  simp only [coeff_zero] at htwo
  have htwo0 : firstSecondaryTwo68 (n : k) (g : k)
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
      (e.coeff (6 * n - g)) = 0 :=
    (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  have hrowOne := hsys.rowOne
  rw [hC0, hE0] at hrowOne
  have hone := congrArg
    (fun p : k[X] => p.coeff (12 * n - 2 * g - 1)) hrowOne
  rw [integratedLowerRowOnePolynomial68_secondaryCoeff_of_loadL_alpha
    l alpha beta gamma delta epsilon zeta eta A B c D e n g
    hn hg hl halpha hrel hA hB hc hD he] at hone
  simp only [coeff_zero] at hone
  have hone0 : firstSecondaryOne68 (n : k) (g : k)
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
      (e.coeff (6 * n - g)) = 0 :=
    (mul_eq_zero.mp hone).resolve_left (by norm_num)
  have hrowZero := hsys.rowZero
  rw [hC0, hE0] at hrowZero
  have hzero := congrArg
    (fun p : k[X] => p.coeff (13 * n - 2 * g - 1)) hrowZero
  rw [integratedLowerRowZeroPolynomial68_secondaryCoeff_of_loadL
    l alpha beta gamma delta epsilon zeta eta A B c D e n g
    hn hg hl hrel hA hB hc hD he] at hzero
  have hindex : 13 * n - 2 * g - 1 ≠ 0 := by omega
  simp only [coeff_C, if_neg hindex] at hzero
  have hncast : (n : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hfactor : (8 / 81 : k) * (n : k) * A.coeff (2 * n) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hncast) ha
  have hzero0 : firstSecondaryZero68
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
      (e.coeff (6 * n - g)) = 0 :=
    (mul_eq_zero.mp hzero).resolve_left hfactor
  exact ⟨hinv.1, hinv.2, htwo0, hone0, hzero0⟩

theorem integratedPolynomialLowerSystem_firstSecondaryClassified68_of_loadL_alpha
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 c D E e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hl : l = 0) (halpha : alpha = 0)
    (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (ha : A.coeff (2 * n) ≠ 0)
    (hC0 : C0 = (1 / 3 : k) • A ^ 2 + c)
    (hE0 : E = (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E) :
    e.coeff (6 * n - g) = 0 ∧
      A.coeff (2 * n) * B.coeff (3 * n - g) =
        3 * D.coeff (5 * n - g) := by
  exact firstSecondaryFace68_classify_of_two_mul_gap_lt_three_mul_radius n g
    (A.coeff (2 * n)) (B.coeff (3 * n - g))
    (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
    (e.coeff (6 * n - g)) ha hn hrel
    (integratedPolynomialLowerSystem_firstSecondaryFace68_of_loadL_alpha
      l alpha beta gamma delta epsilon zeta eta terminal
      A B C0 c D E e n g hn hg hl halpha hrel hA hB hc hD he ha hC0 hE0 hsys)

set_option maxHeartbeats 3000000 in
/-- Without `F₁`, the relaxed chamber `2g < 3n` after `l = 0` still
supplies `F₄`, `F₃`, `F₂`, and `F₀`, leaving three algebraic families. -/
theorem polynomialSecondaryFourThreeZeroEquations68_of_loadL
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 c D E e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hl : l = 0) (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (ha : A.coeff (2 * n) ≠ 0)
    (hC0 : C0 = (1 / 3 : k) • A ^ 2 + c)
    (hE0 : E = (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E) :
    (e.coeff (6 * n - g) = 0 ∧
        A.coeff (2 * n) * B.coeff (3 * n - g) =
          3 * D.coeff (5 * n - g)) ∨
      (e.coeff (6 * n - g) = 0 ∧
        c.coeff (4 * n - g) = 0 ∧
        A.coeff (2 * n) * B.coeff (3 * n - g) =
          D.coeff (5 * n - g)) ∨
      (B.coeff (3 * n - g) = 0 ∧
        c.coeff (4 * n - g) = 0 ∧
        D.coeff (5 * n - g) = 0) := by
  obtain ⟨i4, hI4⟩ := hsys.firstFour
  obtain ⟨i3, hI3⟩ := hsys.firstThree
  have hinv := polynomialSecondaryInvariantEquations68_of_loadL
    l beta gamma delta epsilon zeta i4 i3 A B C0 c D E e n g
    hn hg hl hrel hA hB hc hD he hC0 hE0 hI4 hI3
  have hrowZero := hsys.rowZero
  rw [hC0, hE0] at hrowZero
  have hzero := congrArg
    (fun p : k[X] => p.coeff (13 * n - 2 * g - 1)) hrowZero
  rw [integratedLowerRowZeroPolynomial68_secondaryCoeff_of_loadL
    l alpha beta gamma delta epsilon zeta eta A B c D e n g
    hn hg hl hrel hA hB hc hD he] at hzero
  have hindex : 13 * n - 2 * g - 1 ≠ 0 := by omega
  simp only [coeff_C, if_neg hindex] at hzero
  have hncast : (n : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hfactor : (8 / 81 : k) * (n : k) * A.coeff (2 * n) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hncast) ha
  have hzero0 : firstSecondaryZero68
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
      (e.coeff (6 * n - g)) = 0 :=
    (mul_eq_zero.mp hzero).resolve_left hfactor
  exact firstSecondaryFourThreeZero68_classify
    (A.coeff (2 * n)) (B.coeff (3 * n - g))
    (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
    (e.coeff (6 * n - g)) ha hinv.1 hinv.2 hzero0

end RelaxedSecondaryOneForms68

#print axioms firstSecondaryFace68_classify_of_two_mul_gap_lt_three_mul_radius
#print axioms firstSecondaryFourThreeZero68_classify
#print axioms cubicLoadSPolynomial68_degreeBound_of_loadL
#print axioms cubicLoadTPolynomial68_degreeBound_of_loadL
#print axioms cubicLoadUPolynomial68_degreeBound_of_loadL
#print axioms cubicLoadVPolynomial68_degreeBound_of_loadL
#print axioms cubicLoadTPolynomial68_degreeBound_of_loadL_alpha
#print axioms cubicLoadUPolynomial68_degreeBound_of_loadL_alpha
#print axioms cubicLoadVPolynomial68_degreeBound_of_loadL_alpha
#print axioms secondaryLoadInvariantFourPolynomial68_degree_lt_firstFace_of_loadL
#print axioms secondaryLoadInvariantThreePolynomial68_degree_lt_firstFace_of_loadL
#print axioms cubicFirstIntegralFourPolynomial68_secondaryCoeff_of_loadL
#print axioms cubicFirstIntegralThreePolynomial68_secondaryCoeff_of_loadL
#print axioms polynomialSecondaryInvariantEquations68_of_loadL
#print axioms cubicLoadRowTwoPolynomial68_degree_lt_of_loadL
#print axioms cubicLoadRowOnePolynomial68_degree_lt_of_loadL
#print axioms cubicLoadRowOnePolynomial68_degree_lt_of_loadL_alpha
#print axioms cubicLoadRowZeroPolynomial68_degree_lt_of_loadL
#print axioms integratedLowerRowTwoPolynomial68_secondaryCoeff_of_loadL
#print axioms integratedLowerRowOnePolynomial68_secondaryCoeff_of_loadL
#print axioms integratedLowerRowOnePolynomial68_secondaryCoeff_of_loadL_alpha
#print axioms integratedLowerRowZeroPolynomial68_secondaryCoeff_of_loadL
#print axioms integratedPolynomialLowerSystem_firstSecondaryFace68_of_loadL
#print axioms integratedPolynomialLowerSystem_firstSecondaryClassified68_of_loadL
#print axioms integratedPolynomialLowerSystem_firstSecondaryFace68_of_loadL_alpha
#print axioms integratedPolynomialLowerSystem_firstSecondaryClassified68_of_loadL_alpha
#print axioms polynomialSecondaryFourThreeZeroEquations68_of_loadL

end Max11DegreeRoutes
