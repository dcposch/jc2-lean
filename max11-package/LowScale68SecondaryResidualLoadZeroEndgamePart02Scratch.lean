import LowScale68SecondaryResidualLoadZeroEndgamePart01Scratch

/-! # Residual endgame on the `(6,8)` strip `2g<n` after `l=0`

The tracked residual selector/endgame closes `3g<n`.  After `l=0` every
`A^4`/`A^5` Jacobian load vanishes, so the residual walls `8n<9n-3g` and
`10n<11n-3g` hold throughout `g<n`.  This module replays the precise
invariant/load and row-two/row-one degree cutoffs needed by the tracked
middle/selector/descent/row-two/balanced/row-one/endgame chain under the
weaker chamber `l=0` and `2g<n`, then excludes that whole strip.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section ResidualLoadZeroEndgame68

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Shared derivative degree helper -/

/-! ## Load cutoffs after `l=0` -/

private theorem speedTLoadZero_add_lt {p q : k[X]} {b : ℕ}
    (hp : p.natDegree < b) (hq : q.natDegree < b) : (p + q).natDegree < b :=
  (natDegree_add_le p q).trans_lt (max_lt hp hq)

private theorem speedTLoadZero_sub_lt {p q : k[X]} {b : ℕ}
    (hp : p.natDegree < b) (hq : q.natDegree < b) : (p - q).natDegree < b :=
  (natDegree_sub_le p q).trans_lt (max_lt hp hq)

private theorem speedTLoadZero_smul_lt (a : k) {p : k[X]} {b : ℕ}
    (hp : p.natDegree < b) : (a • p).natDegree < b :=
  (natDegree_smul_le a p).trans_lt hp

set_option maxHeartbeats 64000000 in
theorem secondaryLoadInvariantFourPolynomial68_degree_lt_cubicFace_of_l_eq_zero
    (beta gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g h : ℕ) (hg : 0 < g) (hgh : g < h) (hsmall : 2 * g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - h) :
    (secondaryLoadInvariantFourPolynomial68
      0 beta gamma delta epsilon zeta A B c D e).natDegree <
        9 * n - 3 * g := by
  simp only [secondaryLoadInvariantFourPolynomial68, zero_mul, mul_zero,
    zero_smul, smul_zero, add_zero, sub_zero]
  have hA2 : (A ^ 2).natDegree ≤ 2 * A.natDegree := natDegree_pow_le
  have hA3 : (A ^ 3).natDegree ≤ 3 * A.natDegree := natDegree_pow_le
  have hB2 : (B ^ 2).natDegree ≤ 2 * B.natDegree := natDegree_pow_le
  have hB3 : (B ^ 3).natDegree ≤ 3 * B.natDegree := natDegree_pow_le
  have hAB : (A * B).natDegree ≤ A.natDegree + B.natDegree := natDegree_mul_le
  have hAc : (A * c).natDegree ≤ A.natDegree + c.natDegree := natDegree_mul_le
  have hA2B : (A ^ 2 * B).natDegree ≤ 2 * A.natDegree + B.natDegree :=
    natDegree_mul_le.trans (Nat.add_le_add hA2 (le_refl _))
  have hAD : (A * D).natDegree ≤ A.natDegree + D.natDegree := natDegree_mul_le
  have hBc : (B * c).natDegree ≤ B.natDegree + c.natDegree := natDegree_mul_le
  have hA3B : (A ^ 3 * B).natDegree ≤ 3 * A.natDegree + B.natDegree :=
    natDegree_mul_le.trans (Nat.add_le_add hA3 (le_refl _))
  have hA2D : (A ^ 2 * D).natDegree ≤ 2 * A.natDegree + D.natDegree :=
    natDegree_mul_le.trans (Nat.add_le_add hA2 (le_refl _))
  have hABc : (A * B * c).natDegree ≤ A.natDegree + B.natDegree + c.natDegree :=
    natDegree_mul_le.trans (Nat.add_le_add hAB (le_refl _))
  have hBe : (B * e).natDegree ≤ B.natDegree + e.natDegree := natDegree_mul_le
  have hDc : (D * c).natDegree ≤ D.natDegree + c.natDegree := natDegree_mul_le
  repeat' first
    | with_reducible apply speedTLoadZero_add_lt
    | with_reducible apply speedTLoadZero_sub_lt
    | with_reducible apply speedTLoadZero_smul_lt
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Cubic-invariant loads already sit below the residual middle even with
the `l A^3 B` term, once `2g<n` and `h<2g`. -/
theorem secondaryLoadInvariantThreePolynomial68_degree_lt_middle_of_twoGap
    (l beta gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g h : ℕ) (hg : 0 < g) (hsmall : 2 * g < n) (hh : h < 2 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - h) :
    (secondaryLoadInvariantThreePolynomial68
      l beta gamma delta epsilon zeta A B c D e).natDegree <
        10 * n - g - h := by
  simp only [secondaryLoadInvariantThreePolynomial68]
  have hA2 : (A ^ 2).natDegree ≤ 2 * A.natDegree := natDegree_pow_le
  have hA3 : (A ^ 3).natDegree ≤ 3 * A.natDegree := natDegree_pow_le
  have hB2 : (B ^ 2).natDegree ≤ 2 * B.natDegree := natDegree_pow_le
  have hB3 : (B ^ 3).natDegree ≤ 3 * B.natDegree := natDegree_pow_le
  have hAB : (A * B).natDegree ≤ A.natDegree + B.natDegree := natDegree_mul_le
  have hAc : (A * c).natDegree ≤ A.natDegree + c.natDegree := natDegree_mul_le
  have hA2B : (A ^ 2 * B).natDegree ≤ 2 * A.natDegree + B.natDegree :=
    natDegree_mul_le.trans (Nat.add_le_add hA2 (le_refl _))
  have hAD : (A * D).natDegree ≤ A.natDegree + D.natDegree := natDegree_mul_le
  have hBc : (B * c).natDegree ≤ B.natDegree + c.natDegree := natDegree_mul_le
  have hA3B : (A ^ 3 * B).natDegree ≤ 3 * A.natDegree + B.natDegree :=
    natDegree_mul_le.trans (Nat.add_le_add hA3 (le_refl _))
  have hA2D : (A ^ 2 * D).natDegree ≤ 2 * A.natDegree + D.natDegree :=
    natDegree_mul_le.trans (Nat.add_le_add hA2 (le_refl _))
  have hABc : (A * B * c).natDegree ≤ A.natDegree + B.natDegree + c.natDegree :=
    natDegree_mul_le.trans (Nat.add_le_add hAB (le_refl _))
  have hBe : (B * e).natDegree ≤ B.natDegree + e.natDegree := natDegree_mul_le
  have hDc : (D * c).natDegree ≤ D.natDegree + c.natDegree := natDegree_mul_le
  repeat' first
    | with_reducible apply speedTLoadZero_add_lt
    | with_reducible apply speedTLoadZero_sub_lt
    | with_reducible apply speedTLoadZero_smul_lt
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem secondaryLoadInvariantThreePolynomial68_degree_lt_double_of_twoGap
    (l beta gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g : ℕ) (hg : 0 < g) (hsmall : 2 * g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (secondaryLoadInvariantThreePolynomial68
      l beta gamma delta epsilon zeta A B c D e).natDegree <
        10 * n - 3 * g := by
  simp only [secondaryLoadInvariantThreePolynomial68]
  have hA2 : (A ^ 2).natDegree ≤ 2 * A.natDegree := natDegree_pow_le
  have hA3 : (A ^ 3).natDegree ≤ 3 * A.natDegree := natDegree_pow_le
  have hB2 : (B ^ 2).natDegree ≤ 2 * B.natDegree := natDegree_pow_le
  have hB3 : (B ^ 3).natDegree ≤ 3 * B.natDegree := natDegree_pow_le
  have hAB : (A * B).natDegree ≤ A.natDegree + B.natDegree := natDegree_mul_le
  have hAc : (A * c).natDegree ≤ A.natDegree + c.natDegree := natDegree_mul_le
  have hA2B : (A ^ 2 * B).natDegree ≤ 2 * A.natDegree + B.natDegree :=
    natDegree_mul_le.trans (Nat.add_le_add hA2 (le_refl _))
  have hAD : (A * D).natDegree ≤ A.natDegree + D.natDegree := natDegree_mul_le
  have hBc : (B * c).natDegree ≤ B.natDegree + c.natDegree := natDegree_mul_le
  have hA3B : (A ^ 3 * B).natDegree ≤ 3 * A.natDegree + B.natDegree :=
    natDegree_mul_le.trans (Nat.add_le_add hA3 (le_refl _))
  have hA2D : (A ^ 2 * D).natDegree ≤ 2 * A.natDegree + D.natDegree :=
    natDegree_mul_le.trans (Nat.add_le_add hA2 (le_refl _))
  have hABc : (A * B * c).natDegree ≤ A.natDegree + B.natDegree + c.natDegree :=
    natDegree_mul_le.trans (Nat.add_le_add hAB (le_refl _))
  have hBe : (B * e).natDegree ≤ B.natDegree + e.natDegree := natDegree_mul_le
  have hDc : (D * c).natDegree ≤ D.natDegree + c.natDegree := natDegree_mul_le
  repeat' first
    | with_reducible apply speedTLoadZero_add_lt
    | with_reducible apply speedTLoadZero_sub_lt
    | with_reducible apply speedTLoadZero_smul_lt
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem secondaryLoadInvariantThreePolynomial68_degree_lt_cubicFace_of_twoGap
    (l beta gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g h : ℕ) (hg : 0 < g) (hgh : g < h) (hsmall : 2 * g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - h) :
    (secondaryLoadInvariantThreePolynomial68
      l beta gamma delta epsilon zeta A B c D e).natDegree <
        10 * n - 3 * g := by
  simp only [secondaryLoadInvariantThreePolynomial68]
  have hA2 : (A ^ 2).natDegree ≤ 2 * A.natDegree := natDegree_pow_le
  have hA3 : (A ^ 3).natDegree ≤ 3 * A.natDegree := natDegree_pow_le
  have hB2 : (B ^ 2).natDegree ≤ 2 * B.natDegree := natDegree_pow_le
  have hB3 : (B ^ 3).natDegree ≤ 3 * B.natDegree := natDegree_pow_le
  have hAB : (A * B).natDegree ≤ A.natDegree + B.natDegree := natDegree_mul_le
  have hAc : (A * c).natDegree ≤ A.natDegree + c.natDegree := natDegree_mul_le
  have hA2B : (A ^ 2 * B).natDegree ≤ 2 * A.natDegree + B.natDegree :=
    natDegree_mul_le.trans (Nat.add_le_add hA2 (le_refl _))
  have hAD : (A * D).natDegree ≤ A.natDegree + D.natDegree := natDegree_mul_le
  have hBc : (B * c).natDegree ≤ B.natDegree + c.natDegree := natDegree_mul_le
  have hA3B : (A ^ 3 * B).natDegree ≤ 3 * A.natDegree + B.natDegree :=
    natDegree_mul_le.trans (Nat.add_le_add hA3 (le_refl _))
  have hA2D : (A ^ 2 * D).natDegree ≤ 2 * A.natDegree + D.natDegree :=
    natDegree_mul_le.trans (Nat.add_le_add hA2 (le_refl _))
  have hABc : (A * B * c).natDegree ≤ A.natDegree + B.natDegree + c.natDegree :=
    natDegree_mul_le.trans (Nat.add_le_add hAB (le_refl _))
  have hBe : (B * e).natDegree ≤ B.natDegree + e.natDegree := natDegree_mul_le
  have hDc : (D * c).natDegree ≤ D.natDegree + c.natDegree := natDegree_mul_le
  repeat' first
    | with_reducible apply speedTLoadZero_add_lt
    | with_reducible apply speedTLoadZero_sub_lt
    | with_reducible apply speedTLoadZero_smul_lt
  all_goals omega

end ResidualLoadZeroEndgame68
end Max11DegreeRoutes
