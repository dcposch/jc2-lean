import LowScale68SecondaryResidualLoadZeroEndgamePart101Scratch

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

private theorem leaf68_natDegree_mulDeriv_lt {p q : k[X]} {u v bound : ℕ}
    (hp : p.natDegree ≤ u) (hq : q.natDegree ≤ v) (h : u + (v - 1) < bound) :
    (p * derivative q).natDegree < bound :=
  natDegree_mul_le.trans_lt
    (lt_of_le_of_lt
      (Nat.add_le_add hp ((natDegree_derivative_le q).trans (Nat.sub_le_sub_right hq 1))) h)

private theorem leaf68_natDegree_smul_lt (r : k) {p : k[X]} {bound : ℕ}
    (h : p.natDegree < bound) : (r • p).natDegree < bound :=
  (natDegree_smul_le r p).trans_lt h

private theorem leaf68_natDegree_add_lt {p q : k[X]} {bound : ℕ}
    (hp : p.natDegree < bound) (hq : q.natDegree < bound) :
    (p + q).natDegree < bound :=
  (natDegree_add_le p q).trans_lt (max_lt hp hq)

private theorem leaf68_natDegree_sub_lt {p q : k[X]} {bound : ℕ}
    (hp : p.natDegree < bound) (hq : q.natDegree < bound) :
    (p - q).natDegree < bound :=
  (natDegree_sub_le p q).trans_lt (max_lt hp hq)


/-! ## Shared derivative degree helper -/

/-! ## Load cutoffs after `l=0` -/

/-! ## Homogeneous residual coefficients under `2g<n` -/

set_option maxHeartbeats 3000000 in
/-- Coefficient of the residual second one-form on the tied double face. -/
theorem secondaryResidualRowOnePolynomial68_coeff_double_of_twoGap
    (A B c d e : k[X]) (n g : ℕ) (hg : 0 < g) (hsmall : 2 * g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - 2 * g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (secondaryResidualRowOnePolynomial68 A B c d e).coeff
        (12 * n - 3 * g - 1) =
      (8 / 27 : k) *
        (3 * A.coeff (2 * n) ^ 2 * B.coeff (3 * n - g) * (g : k) *
            d.coeff (5 * n - 2 * g) -
          10 * A.coeff (2 * n) ^ 2 * B.coeff (3 * n - g) * (n : k) *
            d.coeff (5 * n - 2 * g) +
          2 * A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 * (n : k) *
            c.coeff (4 * n - g) -
          9 * A.coeff (2 * n) * (g : k) * c.coeff (4 * n - g) *
            e.coeff (6 * n - 2 * g) +
          30 * A.coeff (2 * n) * (n : k) * c.coeff (4 * n - g) *
            e.coeff (6 * n - 2 * g) +
          3 * (g : k) * c.coeff (4 * n - g) ^ 3 -
          12 * (n : k) * c.coeff (4 * n - g) ^ 3) := by
  have hA2deg : (A ^ 2).natDegree ≤ 4 * n := by
    compute_degree
    omega
  have hB2deg : (B ^ 2).natDegree ≤ 6 * n - 2 * g := by
    compute_degree
    omega
  have hc2deg : (c ^ 2).natDegree ≤ 8 * n - 2 * g := by
    compute_degree
    omega
  have hA2 : (A ^ 2).coeff (4 * n) = A.coeff (2 * n) ^ 2 := by
    have h := coeff_pow_at_bound68 A (2 * n) 2 hA
    have hi : 2 * (2 * n) = 4 * n := by omega
    simpa only [hi] using h
  have hB2 : (B ^ 2).coeff (6 * n - 2 * g) =
      B.coeff (3 * n - g) ^ 2 := by
    have h := coeff_pow_at_bound68 B (3 * n - g) 2 hB
    have hi : 2 * (3 * n - g) = 6 * n - 2 * g := by omega
    simpa only [hi] using h
  have hc2 : (c ^ 2).coeff (8 * n - 2 * g) =
      c.coeff (4 * n - g) ^ 2 := by
    have h := coeff_pow_at_bound68 c (4 * n - g) 2 hc
    have hi : 2 * (4 * n - g) = 8 * n - 2 * g := by omega
    simpa only [hi] using h
  have h1 := coeff_mul_mul_derivative_at_bounds68 (A ^ 2) B d
    (4 * n) (3 * n - g) (5 * n - 2 * g) (by omega)
    hA2deg hB hd
  have hi1 : 4 * n + (3 * n - g) + (5 * n - 2 * g) - 1 =
      12 * n - 3 * g - 1 := by omega
  rw [hi1, hA2] at h1
  have h2 := coeff_mul_mul_derivative_at_bounds68 (A ^ 2) d B
    (4 * n) (5 * n - 2 * g) (3 * n - g) (by omega)
    hA2deg hd hB
  have hi2 : 4 * n + (5 * n - 2 * g) + (3 * n - g) - 1 =
      12 * n - 3 * g - 1 := by omega
  rw [hi2, hA2] at h2
  have h2' : (A ^ 2 * derivative B * d).coeff
      (12 * n - 3 * g - 1) =
      A.coeff (2 * n) ^ 2 * B.coeff (3 * n - g) *
        d.coeff (5 * n - 2 * g) * ((3 * n - g : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h2
  have h3 := coeff_mul_mul_mul_derivative_at_bounds68 A B d A
    (2 * n) (3 * n - g) (5 * n - 2 * g) (2 * n) (by omega)
    hA hB hd hA
  have hi3 : 2 * n + (3 * n - g) + (5 * n - 2 * g) + 2 * n - 1 =
      12 * n - 3 * g - 1 := by omega
  rw [hi3] at h3
  have h3' : (A * derivative A * B * d).coeff
      (12 * n - 3 * g - 1) =
      A.coeff (2 * n) * A.coeff (2 * n) * B.coeff (3 * n - g) *
        d.coeff (5 * n - 2 * g) * ((2 * n : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h3
  have h4 := coeff_mul_mul_derivative_at_bounds68 A c e
    (2 * n) (4 * n - g) (6 * n - 2 * g) (by omega) hA hc he
  have hi4 : 2 * n + (4 * n - g) + (6 * n - 2 * g) - 1 =
      12 * n - 3 * g - 1 := by omega
  rw [hi4] at h4
  have h5 := coeff_mul_mul_derivative_at_bounds68 A e c
    (2 * n) (6 * n - 2 * g) (4 * n - g) (by omega) hA he hc
  have hi5 : 2 * n + (6 * n - 2 * g) + (4 * n - g) - 1 =
      12 * n - 3 * g - 1 := by omega
  rw [hi5] at h5
  have h5' : (A * derivative c * e).coeff (12 * n - 3 * g - 1) =
      A.coeff (2 * n) * c.coeff (4 * n - g) *
        e.coeff (6 * n - 2 * g) * ((4 * n - g : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h5
  have h6 := coeff_mul_mul_derivative_at_bounds68 (B ^ 2) c A
    (6 * n - 2 * g) (4 * n - g) (2 * n) (by omega)
    hB2deg hc hA
  have hi6 : (6 * n - 2 * g) + (4 * n - g) + 2 * n - 1 =
      12 * n - 3 * g - 1 := by omega
  rw [hi6, hB2] at h6
  have h6' : (derivative A * B ^ 2 * c).coeff
      (12 * n - 3 * g - 1) =
      A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 *
        c.coeff (4 * n - g) * ((2 * n : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h6
  have h7 := coeff_mul_derivative_at_bounds68 (c ^ 2) c
    (8 * n - 2 * g) (4 * n - g) (by omega) hc2deg hc
  have hi7 : (8 * n - 2 * g) + (4 * n - g) - 1 =
      12 * n - 3 * g - 1 := by omega
  rw [hi7, hc2] at h7
  have hlowA : (derivative A * d ^ 2).natDegree <
      12 * n - 3 * g - 1 := by compute_degree; omega
  have hlowB : (B ^ 2 * derivative e).natDegree <
      12 * n - 3 * g - 1 := by compute_degree; omega
  have hlowC : (B * c * derivative d).natDegree <
      12 * n - 3 * g - 1 := by compute_degree; omega
  have hlowD : (B * derivative c * d).natDegree <
      12 * n - 3 * g - 1 := by compute_degree; omega
  have hlowE : (derivative B * c * d).natDegree <
      12 * n - 3 * g - 1 := by compute_degree; omega
  have hlowF : (e * derivative e).natDegree <
      12 * n - 3 * g - 1 :=
    leaf68_natDegree_mulDeriv_lt he he (by omega)
  have hcast3 : (((3 * n - g : ℕ) : k)) = 3 * (n : k) - (g : k) := by
    rw [Nat.cast_sub (by omega : g ≤ 3 * n)]
    push_cast
    rfl
  have hcast4 : (((4 * n - g : ℕ) : k)) = 4 * (n : k) - (g : k) := by
    rw [Nat.cast_sub (by omega : g ≤ 4 * n)]
    push_cast
    rfl
  have hcast5 : (((5 * n - 2 * g : ℕ) : k)) =
      5 * (n : k) - 2 * (g : k) := by
    rw [Nat.cast_sub (by omega : 2 * g ≤ 5 * n)]
    push_cast
    rfl
  have hcast6 : (((6 * n - 2 * g : ℕ) : k)) =
      6 * (n : k) - 2 * (g : k) := by
    rw [Nat.cast_sub (by omega : 2 * g ≤ 6 * n)]
    push_cast
    rfl
  simp only [secondaryResidualRowOnePolynomial68, coeff_smul, coeff_add,
    coeff_sub, h1, h2', h3', h4, h5', h6', h7,
    coeff_eq_zero_of_natDegree_lt hlowA,
    coeff_eq_zero_of_natDegree_lt hlowB,
    coeff_eq_zero_of_natDegree_lt hlowC,
    coeff_eq_zero_of_natDegree_lt hlowD,
    coeff_eq_zero_of_natDegree_lt hlowE,
    coeff_eq_zero_of_natDegree_lt hlowF, smul_eq_mul]
  rw [hcast3, hcast4, hcast5, hcast6]
  push_cast
  ring

end ResidualLoadZeroEndgame68
end Max11DegreeRoutes
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

/-! ## Homogeneous residual coefficients under `2g<n` -/

set_option maxHeartbeats 3000000 in
/-- Coefficient of the residual terminal one-form on the double face. -/
theorem secondaryResidualRowZeroPolynomial68_coeff_double_of_twoGap
    (A B c d e : k[X]) (n g : ℕ) (hg : 0 < g) (hsmall : 2 * g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - 2 * g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (secondaryResidualRowZeroPolynomial68 A B c d e).coeff
        (13 * n - 3 * g - 1) =
      (8 / 27 : k) * (n : k) * A.coeff (2 * n) *
        (-(A.coeff (2 * n) * B.coeff (3 * n - g) *
            e.coeff (6 * n - 2 * g)) -
          A.coeff (2 * n) * c.coeff (4 * n - g) *
            d.coeff (5 * n - 2 * g) +
          B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2) := by
  have h1 := coeff_mul_mul_mul_derivative_at_bounds68 A B e A
    (2 * n) (3 * n - g) (6 * n - 2 * g) (2 * n) (by omega)
    hA hB he hA
  have hi1 : 2 * n + (3 * n - g) + (6 * n - 2 * g) + 2 * n - 1 =
      13 * n - 3 * g - 1 := by omega
  rw [hi1] at h1
  have h1' : (A * derivative A * B * e).coeff (13 * n - 3 * g - 1) =
      A.coeff (2 * n) * A.coeff (2 * n) * B.coeff (3 * n - g) *
        e.coeff (6 * n - 2 * g) * ((2 * n : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h1
  have h2 := coeff_mul_mul_mul_derivative_at_bounds68 A c d A
    (2 * n) (4 * n - g) (5 * n - 2 * g) (2 * n) (by omega)
    hA hc hd hA
  have hi2 : 2 * n + (4 * n - g) + (5 * n - 2 * g) + 2 * n - 1 =
      13 * n - 3 * g - 1 := by omega
  rw [hi2] at h2
  have h2' : (A * derivative A * c * d).coeff (13 * n - 3 * g - 1) =
      A.coeff (2 * n) * A.coeff (2 * n) * c.coeff (4 * n - g) *
        d.coeff (5 * n - 2 * g) * ((2 * n : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h2
  have h3 := coeff_mul_mul_mul_derivative_at_bounds68 B c c A
    (3 * n - g) (4 * n - g) (4 * n - g) (2 * n) (by omega)
    hB hc hc hA
  have hi3 : (3 * n - g) + (4 * n - g) + (4 * n - g) + 2 * n - 1 =
      13 * n - 3 * g - 1 := by omega
  rw [hi3] at h3
  have h3' : (derivative A * B * c ^ 2).coeff (13 * n - 3 * g - 1) =
      A.coeff (2 * n) * B.coeff (3 * n - g) *
        c.coeff (4 * n - g) ^ 2 * ((2 * n : ℕ) : k) := by
    simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using h3
  have hlow1 : (A * B ^ 2 * derivative d).natDegree <
      13 * n - 3 * g - 1 := by compute_degree; omega
  have hlow2 : (A * B * derivative B * d).natDegree <
      13 * n - 3 * g - 1 := by compute_degree; omega
  have hlow3 : (derivative A * d * e).natDegree <
      13 * n - 3 * g - 1 := by compute_degree; omega
  have hlow4 : (B * c * derivative e).natDegree <
      13 * n - 3 * g - 1 := by compute_degree; omega
  have hlow5 : (B * d * derivative d).natDegree <
      13 * n - 3 * g - 1 := by compute_degree; omega
  have hlow6 : (derivative B * d ^ 2).natDegree <
      13 * n - 3 * g - 1 := by compute_degree; omega
  have hlow7 : (c * derivative c * d).natDegree <
      13 * n - 3 * g - 1 := by compute_degree; omega
  simp only [secondaryResidualRowZeroPolynomial68, coeff_smul, coeff_add,
    coeff_sub, h1', h2', h3',
    coeff_eq_zero_of_natDegree_lt hlow1,
    coeff_eq_zero_of_natDegree_lt hlow2,
    coeff_eq_zero_of_natDegree_lt hlow3,
    coeff_eq_zero_of_natDegree_lt hlow4,
    coeff_eq_zero_of_natDegree_lt hlow5,
    coeff_eq_zero_of_natDegree_lt hlow6,
    coeff_eq_zero_of_natDegree_lt hlow7, smul_eq_mul]
  push_cast
  ring

end ResidualLoadZeroEndgame68
end Max11DegreeRoutes
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

/-! ## Homogeneous residual coefficients under `2g<n` -/

/-! ## Double-face extraction and selector under `l=0`, `2g<n` -/

set_option maxHeartbeats 4000000 in
theorem polynomialSecondaryResidualDoubleFace68_of_l_eq_zero
    (alpha beta gamma delta epsilon zeta eta i4 i3 : k)
    (A B c d e : k[X]) (n g : ℕ)
    (hg : 0 < g) (hsmall : 2 * g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - 2 * g)
    (he : e.natDegree ≤ 6 * n - 2 * g)
    (ha : A.coeff (2 * n) ≠ 0)
    (hi4 : cubicFirstIntegralFourPolynomial68
      0 beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hi3 : cubicFirstIntegralThreePolynomial68
      0 beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i3)
    (hrowOne :
      let C0 := (1 / 3 : k) • A ^ 2 + c
      let D0 := (1 / 3 : k) • (A * B) + d
      let E0 := (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
      lowerRowOnePolynomial68
        (integratedTPolynomial68 0 alpha beta gamma epsilon A B C0 D0 E0)
        (integratedUPolynomial68 0 alpha beta gamma delta zeta A B C0 D0 E0)
        (integratedVPolynomial68 0 alpha beta gamma delta epsilon eta
          A B C0 D0 E0) C0 D0 E0 = 0)
    (hrowZero :
      let C0 := (1 / 3 : k) • A ^ 2 + c
      let D0 := (1 / 3 : k) • (A * B) + d
      let E0 := (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
      (lowerRowZeroPolynomial68
        (integratedUPolynomial68 0 alpha beta gamma delta zeta A B C0 D0 E0)
        (integratedVPolynomial68 0 alpha beta gamma delta epsilon eta
          A B C0 D0 E0) D0 E0).coeff (13 * n - 3 * g - 1) = 0) :
    SecondaryResidualTiedDoubleFace68 (n : k) (g : k)
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (d.coeff (5 * n - 2 * g))
      (e.coeff (6 * n - 2 * g)) := by
  let C0 := (1 / 3 : k) • A ^ 2 + c
  let D0 := (1 / 3 : k) • (A * B) + d
  let E0 := (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
  change lowerRowOnePolynomial68
    (integratedTPolynomial68 0 alpha beta gamma epsilon A B C0 D0 E0)
    (integratedUPolynomial68 0 alpha beta gamma delta zeta A B C0 D0 E0)
    (integratedVPolynomial68 0 alpha beta gamma delta epsilon eta
      A B C0 D0 E0) C0 D0 E0 = 0 at hrowOne
  change (lowerRowZeroPolynomial68
    (integratedUPolynomial68 0 alpha beta gamma delta zeta A B C0 D0 E0)
    (integratedVPolynomial68 0 alpha beta gamma delta epsilon eta
      A B C0 D0 E0) D0 E0).coeff (13 * n - 3 * g - 1) = 0 at hrowZero
  have hD : D0.natDegree ≤ 5 * n - g := by
    simp only [D0]
    compute_degree
    omega
  have hfour :
      -(B.coeff (3 * n - g) ^ 3) +
          9 * B.coeff (3 * n - g) * e.coeff (6 * n - 2 * g) +
          9 * c.coeff (4 * n - g) * d.coeff (5 * n - 2 * g) = 0 := by
    have hz := congrArg (fun p : k[X] => p.coeff (9 * n - 3 * g)) hi4
    rw [cubicFirstIntegralFourPolynomial68_coeff_residualDouble_of_l_eq_zero
      beta gamma delta epsilon zeta A B c d e n g hg hsmall
      hA hB hc hd he] at hz
    have hindex : 9 * n - 3 * g ≠ 0 := by omega
    simp only [coeff_C, if_neg hindex] at hz
    exact (mul_eq_zero.mp hz).resolve_left (by norm_num)
  have hthree :
      -(A.coeff (2 * n) * B.coeff (3 * n - g) *
          d.coeff (5 * n - 2 * g)) -
        B.coeff (3 * n - g) ^ 2 * c.coeff (4 * n - g) +
        3 * c.coeff (4 * n - g) * e.coeff (6 * n - 2 * g) = 0 := by
    have hz := congrArg (fun p : k[X] => p.coeff (10 * n - 3 * g)) hi3
    rw [cubicFirstIntegralThreePolynomial68_coeff_residualDouble_of_twoGap
      0 beta gamma delta epsilon zeta A B c d e n g hg hsmall
      hA hB hc hd he] at hz
    have hindex : 10 * n - 3 * g ≠ 0 := by omega
    simp only [coeff_C, if_neg hindex] at hz
    exact (mul_eq_zero.mp hz).resolve_left (by norm_num)
  have hcoords := integratedPolynomial68_cubicCoordinates
    0 alpha beta gamma delta epsilon zeta eta A B c D0 e
  have hone := congrArg
    (fun p : k[X] => p.coeff (12 * n - 3 * g - 1)) hrowOne
  rw [hcoords.t_eq, hcoords.u_eq, hcoords.v_eq,
    cubicRowOnePolynomial68_split, coeff_add,
    show cubicHomogeneousRowOnePolynomial68 A B c D0 e =
        secondaryResidualRowOnePolynomial68 A B c d e by
      simpa only [D0] using
        cubicHomogeneousRowOnePolynomial68_residualCoordinates A B c d e,
    secondaryResidualRowOnePolynomial68_coeff_double_of_twoGap A B c d e n g
      hg hsmall hA hB hc hd he,
    coeff_eq_zero_of_natDegree_lt
      (cubicLoadRowOnePolynomial68_degree_lt_residualDouble_of_twoGap
        0 alpha beta gamma delta epsilon zeta eta A B c D0 e n g
        hg hsmall hA hB hc hD he), add_zero, coeff_zero] at hone
  have hone0 := (mul_eq_zero.mp hone).resolve_left (by norm_num)
  rw [hcoords.u_eq, hcoords.v_eq, cubicRowZeroPolynomial68_split,
    coeff_add,
    show cubicHomogeneousRowZeroPolynomial68 A B c D0 e =
        secondaryResidualRowZeroPolynomial68 A B c d e by
      simpa only [D0] using
        cubicHomogeneousRowZeroPolynomial68_residualCoordinates A B c d e,
    secondaryResidualRowZeroPolynomial68_coeff_double_of_twoGap A B c d e n g
      hg hsmall hA hB hc hd he,
    coeff_eq_zero_of_natDegree_lt
      (cubicLoadRowZeroPolynomial68_degree_lt_residualDouble_of_l_eq_zero
        alpha beta gamma delta epsilon zeta eta A B c D0 e n g
        hg hsmall hA hB hc hD he), add_zero] at hrowZero
  have hncast : (n : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hfactor : (8 / 27 : k) * (n : k) * A.coeff (2 * n) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hncast) ha
  have hzero0 := (mul_eq_zero.mp hrowZero).resolve_left hfactor
  exact ⟨hfour, by linear_combination hthree,
    by linear_combination hzero0, by linear_combination hone0⟩

end ResidualLoadZeroEndgame68
end Max11DegreeRoutes
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

/-! ## Homogeneous residual coefficients under `2g<n` -/

/-! ## Double-face extraction and selector under `l=0`, `2g<n` -/

theorem secondaryResidualTiedDoubleFace68_impossible_of_twoGap
    (n g : ℕ) (a b c d e : k) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hsmall : 2 * g < n)
    (hface : SecondaryResidualTiedDoubleFace68
      (n : k) (g : k) a b c d e) : False := by
  have hcast := secondaryResidualTiedDoubleFace68_forces_gap_eq_four_radius
    (n : k) (g : k) a b c d e ha hb hc hface
  have hnat : g = 4 * n := by exact_mod_cast hcast
  omega

theorem secondaryResidualDoubleFace68_impossible_of_twoGap
    (n g : ℕ) (a b c d e : k)
    (ha : a ≠ 0) (hsupport : b ≠ 0 ∨ c ≠ 0) (hsmall : 2 * g < n)
    (hface : SecondaryResidualTiedDoubleFace68
      (n : k) (g : k) a b c d e) : False := by
  have hb : b ≠ 0 := by
    rcases hsupport with hb | hc
    · exact hb
    · intro hb0
      have hd0 : d = 0 := by
        have h := hface.four
        rw [hb0] at h
        have hcd : c * d = 0 := by linear_combination (1 / 9 : k) * h
        exact (mul_eq_zero.mp hcd).resolve_left hc
      have he0 : e = 0 := by
        have h := hface.three
        rw [hb0] at h
        have hce : c * e = 0 := by linear_combination (1 / 3 : k) * h
        exact (mul_eq_zero.mp hce).resolve_left hc
      have hone := hface.one
      rw [hb0, hd0, he0] at hone
      have hcoeff : (3 * (g : k) - 12 * (n : k)) ≠ 0 := by
        intro hz
        have hcast : (3 * g : k) = (12 * n : ℕ) := by
          push_cast
          linear_combination hz
        have hnat : 3 * g = 12 * n := by exact_mod_cast hcast
        omega
      have hc3 : c ^ 3 = 0 := by
        have hprod : (3 * (g : k) - 12 * (n : k)) * c ^ 3 = 0 := by
          linear_combination hone
        exact (mul_eq_zero.mp hprod).resolve_left hcoeff
      exact (pow_ne_zero 3 hc) hc3
  have hc : c ≠ 0 := by
    rcases hsupport with hb' | hc
    · intro hc0
      have hd0 : d = 0 := by
        have h := hface.three
        rw [hc0] at h
        have hab : a * b ≠ 0 := mul_ne_zero ha hb'
        have habd : a * b * d = 0 := by linear_combination -h
        exact (mul_eq_zero.mp habd).resolve_left hab
      have he0 : e = 0 := by
        have h := hface.zero
        rw [hc0] at h
        have hab : a * b ≠ 0 := mul_ne_zero ha hb'
        have habe : a * b * e = 0 := by linear_combination -h
        exact (mul_eq_zero.mp habe).resolve_left hab
      have h := hface.four
      rw [hc0, hd0, he0] at h
      have hb3 : b ^ 3 = 0 := by linear_combination -h
      exact (pow_ne_zero 3 hb') hb3
    · exact hc
  by_cases hd : d = 0
  · exact secondaryResidualEAtDoubleFace68_impossible b c e hb hc
      (secondaryResidualEAtDoubleFace68_of_tied
        (n : k) (g : k) a b c d e hb hc hd hface)
  by_cases he : e = 0
  · exact secondaryResidualDAtDoubleFace68_impossible a b c d hb hc
      (secondaryResidualDAtDoubleFace68_of_tied
        (n : k) (g : k) a b c d e hb hc he hface)
  exact secondaryResidualTiedDoubleFace68_impossible_of_twoGap
    n g a b c d e ha hb hc hsmall hface

end ResidualLoadZeroEndgame68
end Max11DegreeRoutes
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

/-! ## Homogeneous residual coefficients under `2g<n` -/

/-! ## Double-face extraction and selector under `l=0`, `2g<n` -/

set_option maxHeartbeats 4000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_secondaryResidualMiddleFace68_of_l_eq_zero
    (alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (h : ℕ) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      0 alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hsmall :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      2 * g < n)
    (hgh :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      g < h)
    (hh :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      h < 2 * g)
    (hmiddle :
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
      d.natDegree ≤ 5 * n - h ∧ ee.natDegree ≤ 6 * n - h) :
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
    SecondaryResidualBetweenFace68
      (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
      (ce.coeff (4 * n - g)) (d.coeff (5 * n - h))
      (ee.coeff (6 * n - h)) := by
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
  change 2 * g < n at hsmall
  change g < h at hgh
  change h < 2 * g at hh
  change d.natDegree ≤ 5 * n - h ∧
    ee.natDegree ≤ 6 * n - h at hmiddle
  have hdrop := maximalExpandedIntegratedPolynomialLowerSystem_degreeDrop68
    0 alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have hsecondary :=
    maximalExpandedIntegratedPolynomialLowerSystem_secondaryRadius68
      0 alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  have hg : 0 < g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.1
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
    calc
      Ee = (1 / 3 : k) • (Ae * Ce) - (2 / 27 : k) • Ae ^ 3 + ee := by
        simpa only [ee] using cubicEDefectPolynomial68_reconstruct Ae Ce Ee
      _ = (1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee := by
        rw [hCrec]
        apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
        simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
          map_pow, RatFunc.algebraMap_C]
        simp only [map_div₀, map_ofNat, map_one]
        ring
  have hDrec : De = (1 / 3 : k) • (Ae * Be) + d := by
    simpa only [d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
  obtain ⟨i4, hi4⟩ := hsys.firstFour
  obtain ⟨i3, hi3⟩ := hsys.firstThree
  have hi4e : firstIntegralFourPolynomial68 0 beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i4 := by
    have hx := congrArg (expand k 60) hi4
    simpa [Ae, Be, Ce, De, Ee, expand_firstIntegralFourPolynomial68] using hx
  have hi3e : firstIntegralThreePolynomial68 0 beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i3 := by
    have hx := congrArg (expand k 60) hi3
    simpa [Ae, Be, Ce, De, Ee, expand_firstIntegralThreePolynomial68] using hx
  have hi4c := hi4e
  rw [hCrec, hErec, firstIntegralFourPolynomial68_cubicCoordinates,
    hDrec] at hi4c
  have hi3c := hi3e
  rw [hCrec, hErec, firstIntegralThreePolynomial68_cubicCoordinates,
    hDrec] at hi3c
  exact polynomialSecondaryResidualBetweenFace68_of_l_eq_zero
    beta gamma delta epsilon zeta i4 i3 Ae Be ce d ee n g h
    hg hgh hh hsmall hA hB hc hmiddle.1 hmiddle.2 hi4c hi3c

end ResidualLoadZeroEndgame68
end Max11DegreeRoutes
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

/-! ## Homogeneous residual coefficients under `2g<n` -/

/-! ## Double-face extraction and selector under `l=0`, `2g<n` -/

set_option maxHeartbeats 5000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_secondaryResidualDouble68_of_l_eq_zero
    (alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      0 alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hsmall :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      2 * g < n)
    (hdouble :
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
      d.natDegree ≤ 5 * n - 2 * g ∧ ee.natDegree ≤ 6 * n - 2 * g) :
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
    SecondaryResidualTiedDoubleFace68 (n : k) (g : k)
      (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
      (ce.coeff (4 * n - g)) (d.coeff (5 * n - 2 * g))
      (ee.coeff (6 * n - 2 * g)) := by
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
  change 2 * g < n at hsmall
  change d.natDegree ≤ 5 * n - 2 * g ∧
    ee.natDegree ≤ 6 * n - 2 * g at hdouble
  have hcore := maximalExpandedIntegratedPolynomialLowerSystem_cubicCore68
    0 alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have hdrop := maximalExpandedIntegratedPolynomialLowerSystem_degreeDrop68
    0 alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have hsecondary :=
    maximalExpandedIntegratedPolynomialLowerSystem_secondaryRadius68
      0 alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  have hn : 0 < n := by simpa only [n] using hcore.1
  have hg : 0 < g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.1
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
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec :
      Ee = (1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee := by
    calc
      Ee = (1 / 3 : k) • (Ae * Ce) - (2 / 27 : k) • Ae ^ 3 + ee := by
        simpa only [ee] using cubicEDefectPolynomial68_reconstruct Ae Ce Ee
      _ = (1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee := by
        rw [hCrec]
        apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
        simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
          map_pow, RatFunc.algebraMap_C]
        simp only [map_div₀, map_ofNat, map_one]
        ring
  have hDrec : De = (1 / 3 : k) • (Ae * Be) + d := by
    simpa only [d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
  obtain ⟨i4, hi4⟩ := hsys.firstFour
  obtain ⟨i3, hi3⟩ := hsys.firstThree
  have hi4e : firstIntegralFourPolynomial68 0 beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i4 := by
    have hx := congrArg (expand k 60) hi4
    simpa [Ae, Be, Ce, De, Ee, expand_firstIntegralFourPolynomial68] using hx
  have hi3e : firstIntegralThreePolynomial68 0 beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i3 := by
    have hx := congrArg (expand k 60) hi3
    simpa [Ae, Be, Ce, De, Ee, expand_firstIntegralThreePolynomial68] using hx
  have hi4c := hi4e
  rw [hCrec, hErec, firstIntegralFourPolynomial68_cubicCoordinates,
    hDrec] at hi4c
  have hi3c := hi3e
  rw [hCrec, hErec, firstIntegralThreePolynomial68_cubicCoordinates,
    hDrec] at hi3c
  have h1e : lowerRowOnePolynomial68
      (integratedTPolynomial68 0 alpha beta gamma epsilon Ae Be Ce De Ee)
      (integratedUPolynomial68 0 alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 0 alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) Ce De Ee = 0 := by
    dsimp only [Ae, Be, Ce, De, Ee]
    rw [← expand_integratedTPolynomial68, ← expand_integratedUPolynomial68,
      ← expand_integratedVPolynomial68, lowerRowOnePolynomial68_expand,
      hsys.rowOne, map_zero, zero_mul]
  have h0e : lowerRowZeroPolynomial68
      (integratedUPolynomial68 0 alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 0 alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) De Ee = C terminal * (60 * (X ^ 59 : k[X])) := by
    dsimp only [Ae, Be, Ce, De, Ee]
    rw [← expand_integratedUPolynomial68, ← expand_integratedVPolynomial68,
      lowerRowZeroPolynomial68_expand, hsys.rowZero, expand_C]
    norm_num
  have h0target : (lowerRowZeroPolynomial68
      (integratedUPolynomial68 0 alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 0 alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) De Ee).coeff (13 * n - 3 * g - 1) = 0 := by
    rw [h0e]
    apply coeff_eq_zero_of_natDegree_lt
    have hdegree :
        (C terminal * (60 * (X ^ 59 : k[X]))).natDegree ≤ 59 := by
      compute_degree
    have hn10 : 10 ≤ n := by
      have hcases :
          n = 30 * A.natDegree ∨ n = 20 * B.natDegree ∨
            n = 15 * C0.natDegree ∨ n = 12 * D.natDegree ∨
              n = 10 * E.natDegree := by
        simp only [n, weightedRadius68]
        omega
      rcases hcases with hA | hB | hC | hD | hE
      · have : 0 < A.natDegree := by omega
        omega
      · have : 0 < B.natDegree := by omega
        omega
      · have : 0 < C0.natDegree := by omega
        omega
      · have : 0 < D.natDegree := by omega
        omega
      · have : 0 < E.natDegree := by omega
        omega
    have hidx : 59 < 13 * n - 3 * g - 1 := by
      have : 3 * g < 2 * n := by omega
      omega
    exact hdegree.trans_lt hidx
  have h1cubic := h1e
  rw [hCrec, hDrec, hErec] at h1cubic
  have h0cubic := h0target
  rw [hCrec, hDrec, hErec] at h0cubic
  exact polynomialSecondaryResidualDoubleFace68_of_l_eq_zero
    alpha beta gamma delta epsilon zeta eta i4 i3 Ae Be ce d ee n g
    hg hsmall hA hB hc hdouble.1 hdouble.2 ha hi4c hi3c h1cubic h0cubic

end ResidualLoadZeroEndgame68
end Max11DegreeRoutes
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

/-! ## Homogeneous residual coefficients under `2g<n` -/

/-! ## Double-face extraction and selector under `l=0`, `2g<n` -/

set_option maxHeartbeats 6000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_secondaryResidualSelect68_of_l_eq_zero
    (alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      0 alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hsmall :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      2 * g < n) :
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
    ∃ h : ℕ, g < h ∧ h < 2 * g ∧
      Be.coeff (3 * n - g) ≠ 0 ∧ ce.coeff (4 * n - g) ≠ 0 ∧
      d.coeff (5 * n - h) ≠ 0 ∧ ee.coeff (6 * n - h) ≠ 0 ∧
      Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 2 +
        3 * ce.coeff (4 * n - g) ^ 2 = 0 := by
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
  change 2 * g < n at hsmall
  have hcore := maximalExpandedIntegratedPolynomialLowerSystem_cubicCore68
    0 alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have ha : Ae.coeff (2 * n) ≠ 0 := by
    simpa only [n, Ae] using hcore.2.2.2.2.2
  have hboundary :=
    maximalExpandedIntegratedPolynomialLowerSystem_secondarySmallGapBoundary68
      0 alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsmall)
  change ee.coeff (6 * n - g) = 0 ∧
    Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
      3 * De.coeff (5 * n - g) ∧
    (Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0) at hboundary
  have hsupport := hboundary.2.2
  have hdrops :=
    maximalExpandedIntegratedPolynomialLowerSystem_secondaryResidualDegreeDrops68
      0 alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsmall)
  change d.natDegree < 5 * n - g ∧ ee.natDegree < 6 * n - g at hdrops
  have hnotboth : ¬ (d = 0 ∧ ee = 0) := by
    rintro ⟨hd0, he0⟩
    have hdouble : d.natDegree ≤ 5 * n - 2 * g ∧
        ee.natDegree ≤ 6 * n - 2 * g := by
      simp only [hd0, he0, natDegree_zero]
      omega
    have hface :=
      maximalExpandedIntegratedPolynomialLowerSystem_secondaryResidualDouble68_of_l_eq_zero
        alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys (by
          simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsmall)
        (by
          simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d] using hdouble)
    change SecondaryResidualTiedDoubleFace68 (n : k) (g : k)
      (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
      (ce.coeff (4 * n - g)) (d.coeff (5 * n - 2 * g))
      (ee.coeff (6 * n - 2 * g)) at hface
    exact secondaryResidualDoubleFace68_impossible_of_twoGap n g
      (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
      (ce.coeff (4 * n - g)) (d.coeff (5 * n - 2 * g))
      (ee.coeff (6 * n - 2 * g)) ha hsupport hsmall hface
  have hgh : g < h := by
    simpa only [h] using secondaryResidualGap68_gt_of_strictDrops n g d ee
      hdrops.1 hdrops.2
  have hdbase : d.natDegree < 5 * n := by omega
  have hebase : ee.natDegree < 6 * n := by omega
  have hbounds : d.natDegree ≤ 5 * n - h ∧
      ee.natDegree ≤ 6 * n - h := by
    simpa only [h] using secondaryResidualGap68_degreeBounds n d ee
      hdbase hebase
  have hattained : d.coeff (5 * n - h) ≠ 0 ∨
      ee.coeff (6 * n - h) ≠ 0 := by
    simpa only [h] using secondaryResidualGap68_boundary_attained n d ee
      hdbase hebase hnotboth
  by_cases hh : h < 2 * g
  · have hface :=
      maximalExpandedIntegratedPolynomialLowerSystem_secondaryResidualMiddleFace68_of_l_eq_zero
        alpha beta gamma delta epsilon zeta eta terminal A B C0 D E h
        hterminal hsys (by
          simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsmall)
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hgh)
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hh)
        (by
          simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d] using hbounds)
    change SecondaryResidualBetweenFace68
      (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
      (ce.coeff (4 * n - g)) (d.coeff (5 * n - h))
      (ee.coeff (6 * n - h)) at hface
    have hclass := secondaryResidualBetweenFace68_classify_of_support
      (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
      (ce.coeff (4 * n - g)) (d.coeff (5 * n - h))
      (ee.coeff (6 * n - h)) ha hsupport hattained hface
    exact ⟨h, hgh, hh, hclass.1, hclass.2.1, hclass.2.2.1,
      hclass.2.2.2.1, hclass.2.2.2.2⟩
  · have hdouble : d.natDegree ≤ 5 * n - 2 * g ∧
        ee.natDegree ≤ 6 * n - 2 * g := by
      constructor <;> omega
    have hface :=
      maximalExpandedIntegratedPolynomialLowerSystem_secondaryResidualDouble68_of_l_eq_zero
        alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys (by
          simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsmall)
        (by
          simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d] using hdouble)
    change SecondaryResidualTiedDoubleFace68 (n : k) (g : k)
      (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
      (ce.coeff (4 * n - g)) (d.coeff (5 * n - 2 * g))
      (ee.coeff (6 * n - 2 * g)) at hface
    exact (secondaryResidualDoubleFace68_impossible_of_twoGap n g
      (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
      (ce.coeff (4 * n - g)) (d.coeff (5 * n - 2 * g))
      (ee.coeff (6 * n - 2 * g)) ha hsupport hsmall hface).elim

end ResidualLoadZeroEndgame68
end Max11DegreeRoutes
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

/-! ## Homogeneous residual coefficients under `2g<n` -/

/-! ## Double-face extraction and selector under `l=0`, `2g<n` -/

private theorem loadZero_natDegree_mul_derivative_lt68
    (p q : k[X]) (u v : ℕ)
    (hu : p.natDegree ≤ u) (hv : 1 < v) (hq : q.natDegree < v) :
    (p * derivative q).natDegree < u + v - 1 := by
  have hq' : q.natDegree ≤ v - 1 := Nat.le_sub_one_of_lt hq
  have hd : (derivative q).natDegree ≤ v - 2 := by
    have h := natDegree_derivative_le q
    omega
  have hmul := natDegree_mul_le_of_le hu hd
  omega

private theorem loadZero_natDegree_derivative_mul_lt68
    (p q : k[X]) (u v : ℕ)
    (hu0 : 0 < u) (hu : p.natDegree ≤ u) (hq : q.natDegree < v) :
    (derivative p * q).natDegree < u + v - 1 := by
  have hd : (derivative p).natDegree ≤ u - 1 :=
    (natDegree_derivative_le p).trans (by omega)
  have hq' : q.natDegree ≤ v - 1 := Nat.le_sub_one_of_lt hq
  have hmul := natDegree_mul_le_of_le hd hq'
  omega

set_option maxHeartbeats 3000000 in
theorem secondaryResidualIncidenceDefectPolynomial68_degree_lt_cubicFace_of_l_eq_zero
    (beta gamma delta epsilon zeta i4 : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hsmall : 2 * g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hi4 : cubicFirstIntegralFourPolynomial68
      0 beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4) :
    (secondaryResidualIncidenceDefectPolynomial68 B c d e).natDegree <
      9 * n - 3 * g := by
  let D := (1 / 3 : k) • (A * B) + d
  let q := secondaryResidualIncidenceDefectPolynomial68 B c d e
  have hD : D.natDegree ≤ 5 * n - g := by
    simp only [D]
    compute_degree
    omega
  have hload := secondaryLoadInvariantFourPolynomial68_degree_lt_cubicFace_of_l_eq_zero
    beta gamma delta epsilon zeta A B c D e n g h hg hgh hsmall
    hA hB hc hD he
  have hsplit := hi4
  rw [cubicFirstIntegralFourPolynomial68_secondaryLoadSplit,
    cubicFirstIntegralFourPolynomial68_residualCoordinates,
    secondaryResidualInvariantFourPolynomial68_eq_incidenceDefect] at hsplit
  change (8 / 3 : k) • q +
    secondaryLoadInvariantFourPolynomial68
      0 beta gamma delta epsilon zeta A B c D e = C i4 at hsplit
  have hcore : (8 / 3 : k) • q =
      C i4 - secondaryLoadInvariantFourPolynomial68
        0 beta gamma delta epsilon zeta A B c D e :=
    eq_sub_iff_add_eq.mpr hsplit
  have hq : q = (3 / 8 : k) •
      (C i4 - secondaryLoadInvariantFourPolynomial68
        0 beta gamma delta epsilon zeta A B c D e) := by
    calc
      q = (3 / 8 : k) • ((8 / 3 : k) • q) := by
        rw [smul_smul]
        norm_num
      _ = (3 / 8 : k) •
          (C i4 - secondaryLoadInvariantFourPolynomial68
            0 beta gamma delta epsilon zeta A B c D e) := by rw [hcore]
  change q.natDegree < 9 * n - 3 * g
  rw [hq]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
theorem residualRowTwoInner_Q_degree_lt68_of_twoGap
    (A B c d e : k[X]) (n g : ℕ)
    (hsmall : 2 * g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hQ : (residualIncidenceQ68 B c d e).natDegree < 9 * n - 3 * g) :
    (A * derivative (residualIncidenceQ68 B c d e)).natDegree <
        11 * n - 3 * g - 1 ∧
      (derivative A * residualIncidenceQ68 B c d e).natDegree <
        11 * n - 3 * g - 1 := by
  have hv : 1 < 9 * n - 3 * g := by omega
  have h1 := loadZero_natDegree_mul_derivative_lt68 A
    (residualIncidenceQ68 B c d e) (2 * n) (9 * n - 3 * g) hA hv hQ
  have h2 := loadZero_natDegree_derivative_mul_lt68 A
    (residualIncidenceQ68 B c d e) (2 * n) (9 * n - 3 * g)
    (by omega) hA hQ
  have hi : 2 * n + (9 * n - 3 * g) - 1 = 11 * n - 3 * g - 1 := by omega
  exact ⟨by simpa only [hi] using h1, by simpa only [hi] using h2⟩

set_option maxHeartbeats 2000000 in
theorem residualRowTwoInner_Bd_degree_le68_of_twoGap
    (B d : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g) (hsmall : 2 * g < n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hd : d.natDegree ≤ 5 * n - h) :
    (derivative (B ^ 2 * d)).natDegree ≤ 11 * n - 2 * g - h - 1 := by
  have hB2 : (B ^ 2).natDegree ≤ 6 * n - 2 * g := by
    compute_degree
    omega
  have hprod := natDegree_mul_le_of_le hB2 hd
  have hsum : 6 * n - 2 * g + (5 * n - h) = 11 * n - 2 * g - h := by omega
  rw [hsum] at hprod
  have hder := natDegree_derivative_le (B ^ 2 * d)
  omega

end ResidualLoadZeroEndgame68
end Max11DegreeRoutes
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

/-! ## Homogeneous residual coefficients under `2g<n` -/

/-! ## Double-face extraction and selector under `l=0`, `2g<n` -/

set_option maxHeartbeats 2000000 in
theorem residualRowTwoInner_BcCore_degree_le68_of_twoGap
    (A B c : k[X]) (n g : ℕ)
    (hg : 0 < g) (hsmall : 2 * g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g) :
    (A * B ^ 2 * derivative B).natDegree ≤ 11 * n - 3 * g - 1 ∧
      (derivative A * B ^ 3).natDegree ≤ 11 * n - 3 * g - 1 ∧
      (derivative (B * c ^ 2)).natDegree ≤ 11 * n - 3 * g - 1 := by
  have hB2 : (B ^ 2).natDegree ≤ 6 * n - 2 * g := by
    compute_degree
    omega
  have hB3 : (B ^ 3).natDegree ≤ 9 * n - 3 * g := by
    compute_degree
    omega
  have hc2 : (c ^ 2).natDegree ≤ 8 * n - 2 * g := by
    compute_degree
    omega
  have hdB : (derivative B).natDegree ≤ 3 * n - g - 1 :=
    (natDegree_derivative_le B).trans (by omega)
  have hdA : (derivative A).natDegree ≤ 2 * n - 1 :=
    (natDegree_derivative_le A).trans (by omega)
  have hAB2 := natDegree_mul_le_of_le hA hB2
  have hAB2d := natDegree_mul_le_of_le hAB2 hdB
  have hA3 := natDegree_mul_le_of_le hdA hB3
  have hBc2 := natDegree_mul_le_of_le hB hc2
  have hdBc2 := natDegree_derivative_le (B * c ^ 2)
  refine ⟨by omega, by omega, by omega⟩

set_option maxHeartbeats 2000000 in
theorem residualRowTwoInner_de_degree_le68_of_twoGap
    (d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g) (hsmall : 2 * g < n)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (derivative (d * e)).natDegree ≤ 11 * n - 2 * h - 1 := by
  have hprod := natDegree_mul_le_of_le hd he
  have hsum : (5 * n - h) + (6 * n - h) = 11 * n - 2 * h := by omega
  rw [hsum] at hprod
  have hder := natDegree_derivative_le (d * e)
  omega

end ResidualLoadZeroEndgame68
end Max11DegreeRoutes
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

/-! ## Homogeneous residual coefficients under `2g<n` -/

/-! ## Double-face extraction and selector under `l=0`, `2g<n` -/

set_option maxHeartbeats 4000000 in
/-- On `2h<3g`, residual row two is dominated by `derivative(d*e)`. -/
theorem residualRowTwo_coeff_leftChamber68_of_twoGap
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hsmall : 2 * g < n) (hleft : 2 * h < 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualIncidenceQ68 B c d e).natDegree < 9 * n - 3 * g) :
    (secondaryResidualRowTwoPolynomial68 A B c d e).coeff
        (11 * n - 2 * h - 1) =
      (8 / 3 : k) * ((11 * n - 2 * h : ℕ) : k) *
        d.coeff (5 * n - h) * e.coeff (6 * n - h) := by
  let Q := residualIncidenceQ68 B c d e
  let inner := residualRowTwoInner68 A B c d e
  set idx := 11 * n - 2 * h - 1
  have hidx : 11 * n - 3 * g - 1 < idx := by
    dsimp [idx]
    omega
  have hQdeg := residualRowTwoInner_Q_degree_lt68_of_twoGap A B c d e n g hsmall hA hQ
  have hAQ : (A * derivative Q).natDegree < idx := hQdeg.1.trans hidx
  have hAQ' : (derivative A * Q).natDegree < idx := hQdeg.2.trans hidx
  have hcore := residualRowTwoInner_BcCore_degree_le68_of_twoGap A B c n g hg hsmall hA hB hc
  have hAB : (A * B ^ 2 * derivative B).natDegree < idx :=
    hcore.1.trans_lt hidx
  have hA3 : (derivative A * B ^ 3).natDegree < idx :=
    hcore.2.1.trans_lt hidx
  have hBc : (derivative (B * c ^ 2)).natDegree < idx :=
    hcore.2.2.trans_lt hidx
  have hBd := residualRowTwoInner_Bd_degree_le68_of_twoGap B d n g h hg hgh hh hsmall hB hd
  have hBd' : (derivative (B ^ 2 * d)).natDegree < idx := by
    dsimp [idx]
    omega
  have hdebound := natDegree_mul_le_of_le hd he
  have hide : (5 * n - h) + (6 * n - h) = 11 * n - 2 * h := by omega
  rw [hide] at hdebound
  have hdecoeff := coeff_mul_at_bounds68 d e (5 * n - h) (6 * n - h) hd he
  rw [hide] at hdecoeff
  have hder0 : 0 < 11 * n - 2 * h := by omega
  have hde := coeff_derivative_at_bound68 (d * e) (11 * n - 2 * h) hder0
  rw [hdecoeff] at hde
  have h0Q : ((-6 : k) • (A * derivative Q)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hAQ, mul_zero]
  have h0Q' : ((3 : k) • (derivative A * Q)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hAQ', mul_zero]
  have h0AB : ((-2 : k) • (A * B ^ 2 * derivative B)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hAB, mul_zero]
  have h0A3 : ((-2 / 3 : k) • (derivative A * B ^ 3)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hA3, mul_zero]
  have h0Bd : ((6 : k) • derivative (B ^ 2 * d)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hBd', mul_zero]
  have h0Bc : ((6 : k) • derivative (B * c ^ 2)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hBc, mul_zero]
  have hde' : ((-18 : k) • derivative (d * e)).coeff idx =
      (-18 : k) * (d.coeff (5 * n - h) * e.coeff (6 * n - h) *
        ((11 * n - 2 * h : ℕ) : k)) := by
    rw [coeff_smul, smul_eq_mul]
    dsimp [idx]
    rw [hde]
  have hinner : inner.coeff idx =
      (-18 : k) * (d.coeff (5 * n - h) * e.coeff (6 * n - h) *
        ((11 * n - 2 * h : ℕ) : k)) := by
    dsimp [inner, residualRowTwoInner68]
    simp only [coeff_add]
    rw [h0Q, h0Q', h0AB, h0A3, h0Bd, h0Bc, hde']
    ring
  rw [residualRowTwo_eq_inner68, coeff_smul, smul_eq_mul]
  change ((-4 / 27 : k) * inner.coeff idx) = _
  rw [hinner]
  ring

end ResidualLoadZeroEndgame68
end Max11DegreeRoutes
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

/-! ## Homogeneous residual coefficients under `2g<n` -/

/-! ## Double-face extraction and selector under `l=0`, `2g<n` -/

set_option maxHeartbeats 2000000 in
theorem residualRowTwo_leftChamber_ne_zero68_of_twoGap
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hsmall : 2 * g < n) (hleft : 2 * h < 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualIncidenceQ68 B c d e).natDegree < 9 * n - 3 * g)
    (hd0 : d.coeff (5 * n - h) ≠ 0)
    (he0 : e.coeff (6 * n - h) ≠ 0) :
    (secondaryResidualRowTwoPolynomial68 A B c d e).coeff
        (11 * n - 2 * h - 1) ≠ 0 := by
  rw [residualRowTwo_coeff_leftChamber68_of_twoGap A B c d e n g h hg hgh hh hsmall hleft
    hA hB hc hd he hQ]
  have hscalar : (8 / 3 : k) ≠ 0 := by norm_num
  have hN : ((11 * n - 2 * h : ℕ) : k) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by omega)
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hscalar hN) hd0) he0

end ResidualLoadZeroEndgame68
end Max11DegreeRoutes
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

/-! ## Homogeneous residual coefficients under `2g<n` -/

/-! ## Double-face extraction and selector under `l=0`, `2g<n` -/

set_option maxHeartbeats 4000000 in
/-- On `3g<2h`, residual row two is dominated by the `B,c` core. -/
theorem residualRowTwo_coeff_rightChamber68_of_twoGap
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hsmall : 2 * g < n) (hright : 3 * g < 2 * h)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualIncidenceQ68 B c d e).natDegree < 9 * n - 3 * g)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0) :
    (secondaryResidualRowTwoPolynomial68 A B c d e).coeff
        (11 * n - 3 * g - 1) =
      (32 / 81 : k) * ((11 * n - 3 * g : ℕ) : k) *
        A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 := by
  let Q := residualIncidenceQ68 B c d e
  let inner := residualRowTwoInner68 A B c d e
  set idx := 11 * n - 3 * g - 1
  have hQdeg := residualRowTwoInner_Q_degree_lt68_of_twoGap A B c d e n g hsmall hA hQ
  have hAQ : (A * derivative Q).natDegree < idx := by
    dsimp [idx]
    exact hQdeg.1
  have hAQ' : (derivative A * Q).natDegree < idx := by
    dsimp [idx]
    exact hQdeg.2
  have hBd := residualRowTwoInner_Bd_degree_le68_of_twoGap B d n g h hg hgh hh hsmall hB hd
  have hBd' : (derivative (B ^ 2 * d)).natDegree < idx := by
    dsimp [idx]
    omega
  have hde := residualRowTwoInner_de_degree_le68_of_twoGap d e n g h hg hgh hh hsmall hd he
  have hde' : (derivative (d * e)).natDegree < idx := by
    dsimp [idx]
    omega
  have hB2deg : (B ^ 2).natDegree ≤ 6 * n - 2 * g := by
    compute_degree
    omega
  have hB2 : (B ^ 2).coeff (6 * n - 2 * g) =
      B.coeff (3 * n - g) ^ 2 := by
    have h := coeff_pow_at_bound68 B (3 * n - g) 2 hB
    have hi : 2 * (3 * n - g) = 6 * n - 2 * g := by omega
    simpa only [hi] using h
  have hAB := coeff_mul_mul_derivative_at_bounds68 A (B ^ 2) B
    (2 * n) (6 * n - 2 * g) (3 * n - g) (by omega) hA hB2deg hB
  have hiAB : 2 * n + (6 * n - 2 * g) + (3 * n - g) - 1 = idx := by
    dsimp [idx]
    omega
  rw [hiAB, hB2] at hAB
  have hABpow : (A * B ^ 2 * derivative B).coeff idx =
      A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 *
        ((3 * n - g : ℕ) : k) := by
    rw [hAB]
    ring
  have hB3deg : (B ^ 3).natDegree ≤ 9 * n - 3 * g := by
    compute_degree
    omega
  have hB3 : (B ^ 3).coeff (9 * n - 3 * g) =
      B.coeff (3 * n - g) ^ 3 := by
    have h := coeff_pow_at_bound68 B (3 * n - g) 3 hB
    have hi : 3 * (3 * n - g) = 9 * n - 3 * g := by omega
    simpa only [hi] using h
  have hA3 := coeff_mul_derivative_at_bounds68 (B ^ 3) A
    (9 * n - 3 * g) (2 * n) (by omega) hB3deg hA
  have hiA3 : (9 * n - 3 * g) + 2 * n - 1 = idx := by
    dsimp [idx]
    omega
  rw [hiA3, hB3] at hA3
  have hA3' : (derivative A * B ^ 3).coeff idx =
      A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 *
        ((2 * n : ℕ) : k) := by
    rw [show (derivative A * B ^ 3).coeff idx =
        (B ^ 3 * derivative A).coeff idx by
      congr 1
      ring]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hA3
  have hc2deg : (c ^ 2).natDegree ≤ 8 * n - 2 * g := by
    compute_degree
    omega
  have hc2 : (c ^ 2).coeff (8 * n - 2 * g) =
      c.coeff (4 * n - g) ^ 2 := by
    have h := coeff_pow_at_bound68 c (4 * n - g) 2 hc
    have hi : 2 * (4 * n - g) = 8 * n - 2 * g := by omega
    simpa only [hi] using h
  have hBcdeg : (B * c ^ 2).natDegree ≤ 11 * n - 3 * g := by
    have h := natDegree_mul_le_of_le hB hc2deg
    have hi : (3 * n - g) + (8 * n - 2 * g) = 11 * n - 3 * g := by omega
    rwa [hi] at h
  have hBccoeff := coeff_mul_at_bounds68 B (c ^ 2)
    (3 * n - g) (8 * n - 2 * g) hB hc2deg
  have hiBc : (3 * n - g) + (8 * n - 2 * g) = 11 * n - 3 * g := by omega
  rw [hiBc, hc2] at hBccoeff
  have hBc := coeff_derivative_at_bound68 (B * c ^ 2)
    (11 * n - 3 * g) (by omega)
  rw [hBccoeff] at hBc
  have hcast3 : (((3 * n - g : ℕ) : k)) =
      (3 : k) * (n : k) - (g : k) := by
    rw [Nat.cast_sub (by omega : g ≤ 3 * n)]
    push_cast
    rfl
  have hcast2 : (((2 * n : ℕ) : k)) = (2 : k) * (n : k) := by
    push_cast
    rfl
  have hcast11 : (((11 * n - 3 * g : ℕ) : k)) =
      (11 : k) * (n : k) - (3 : k) * (g : k) := by
    rw [Nat.cast_sub (by omega : 3 * g ≤ 11 * n)]
    push_cast
    rfl
  have h0Q : ((-6 : k) • (A * derivative Q)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hAQ, mul_zero]
  have h0Q' : ((3 : k) • (derivative A * Q)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hAQ', mul_zero]
  have h0Bd : ((6 : k) • derivative (B ^ 2 * d)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hBd', mul_zero]
  have h0de : ((-18 : k) • derivative (d * e)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hde', mul_zero]
  have hABsm : ((-2 : k) • (A * B ^ 2 * derivative B)).coeff idx =
      (-2 : k) * (A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 *
        ((3 * n - g : ℕ) : k)) := by
    rw [coeff_smul, smul_eq_mul, hABpow]
  have hA3sm : ((-2 / 3 : k) • (derivative A * B ^ 3)).coeff idx =
      (-2 / 3 : k) * (A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 *
        ((2 * n : ℕ) : k)) := by
    rw [coeff_smul, smul_eq_mul, hA3']
  have hBcsm : ((6 : k) • derivative (B * c ^ 2)).coeff idx =
      (6 : k) * (B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 *
        ((11 * n - 3 * g : ℕ) : k)) := by
    rw [coeff_smul, smul_eq_mul]
    dsimp [idx]
    rw [hBc]
  have hinner : inner.coeff idx =
      (-8 / 3 : k) * ((11 * n - 3 * g : ℕ) : k) *
        A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 := by
    dsimp [inner, residualRowTwoInner68]
    simp only [coeff_add]
    rw [h0Q, h0Q', h0Bd, h0de, hABsm, hA3sm, hBcsm, hcast3, hcast2, hcast11]
    have hsc := residualRowTwoRightCoreScalar68_of_disc (n : k) (g : k)
      (A.coeff (2 * n)) (B.coeff (3 * n - g)) (c.coeff (4 * n - g)) hdisc
    convert hsc using 1
    ring
  rw [residualRowTwo_eq_inner68, coeff_smul, smul_eq_mul]
  change ((-4 / 27 : k) * inner.coeff idx) = _
  rw [hinner]
  ring

end ResidualLoadZeroEndgame68
end Max11DegreeRoutes
