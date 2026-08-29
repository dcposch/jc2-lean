import LowScale68SecondaryAlphaWallMixedEndgame

/-! # Mixed residual row zero on the alpha wall `g = n`

After `l = 0` the terminal one-form at `10n-1` has load
`(5 n / 108) beta a^5`.  Rewriting through `Q` produces the residual
scalar `(8 n / 27) a ((5/192) beta a^4 + X)` with
`X = b c^2 - a b^3/9 - 3 d e`.  Mixed row two is the same `X` with a
mismatched beta prefactor, so `beta a^4 = 0`, then first-face support
fails.  This closes `2h = 3g` and `h ≥ 2g`, hence the whole wall.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlphaWallBalancedRowZero68

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Mixed cubic residual row-zero load scalar on `g = n`. -/
def alphaWallRowZeroLoadScalar68 (N a beta : k) : k :=
  (5 / 108 : k) * N * beta * a ^ 5

private theorem residual_natDegree_mul_derivative_le68
    (p q : k[X]) (u v : ℕ)
    (hu : p.natDegree ≤ u) (hv : 0 < v) (hq : q.natDegree ≤ v) :
    (p * derivative q).natDegree ≤ u + v - 1 := by
  have hd : (derivative q).natDegree ≤ v - 1 :=
    (natDegree_derivative_le q).trans (by omega)
  have hmul := natDegree_mul_le_of_le hu hd
  omega

/-! ## Field algebra -/

theorem alphaWallRowZeroQInnerScalar68 (N a q0 b c d e : k) :
    (-(1 : k)) * (a * ((2 : k) * N) * a * q0) -
        (1 / 9 : k) * (a * ((2 : k) * N) * a * b ^ 3) +
        a * ((2 : k) * N) * b * c ^ 2 -
        (3 : k) * (a * ((2 : k) * N) * d * e) =
      (2 : k) * N * a *
        (-a * q0 - a * b ^ 3 / 9 + b * c ^ 2 - (3 : k) * d * e) := by
  ring

theorem alphaWallRowZeroResidualInner_of_I4load68
    (N a b c d e beta : k) :
    (2 : k) * N * a *
        (-a * (-((5 / 192 : k) * beta * a ^ 3)) -
          a * b ^ 3 / 9 + b * c ^ 2 - (3 : k) * d * e) =
      (2 : k) * N * a *
        ((5 / 192 : k) * beta * a ^ 4 + b * c ^ 2 -
          a * b ^ 3 / 9 - (3 : k) * d * e) := by
  ring

theorem alphaWallMixedRowZero_sum_eq_X
    (N a b c d e beta : k) :
    (4 / 27 : k) * ((2 : k) * N * a *
        ((5 / 192 : k) * beta * a ^ 4 + b * c ^ 2 -
          a * b ^ 3 / 9 - (3 : k) * d * e)) +
      (5 / 108 : k) * N * beta * a ^ 5 =
      (4 / 27 : k) * ((2 : k) * N * a) *
        (b * c ^ 2 - a * b ^ 3 / 9 - (3 : k) * d * e +
          (35 / 192 : k) * beta * a ^ 4) := by
  ring

theorem alphaWallMixedRowZeroRowTwo_X_eq_of_rowZero
    (N a b c d e beta : k) (hN : N ≠ 0) (ha : a ≠ 0)
    (hrow0 :
      (4 / 27 : k) * ((2 : k) * N * a *
          ((5 / 192 : k) * beta * a ^ 4 + b * c ^ 2 -
            a * b ^ 3 / 9 - (3 : k) * d * e)) +
        (5 / 108 : k) * N * beta * a ^ 5 = 0) :
    b * c ^ 2 - a * b ^ 3 / 9 - (3 : k) * d * e =
      -((35 / 192 : k) * beta * a ^ 4) := by
  have hpre : (4 / 27 : k) * ((2 : k) * N * a) ≠ 0 :=
    mul_ne_zero (by norm_num)
      (mul_ne_zero (mul_ne_zero (by norm_num) hN) ha)
  have heq := alphaWallMixedRowZero_sum_eq_X N a b c d e beta
  rw [heq] at hrow0
  have hsum := (mul_eq_zero.mp hrow0).resolve_left hpre
  linear_combination hsum

theorem alphaWallMixedRowTwo_sum_eq_X
    (N a b c d e beta : k) :
    (-4 / 27 : k) *
        ((25 / 32 : k) * N * beta * a ^ 4 +
          N * ((-16 / 3 : k) * a * b ^ 3 + (48 : k) * b * c ^ 2 -
            (144 : k) * d * e)) +
      (5 / 18 : k) * N * beta * a ^ 4 =
      (-4 / 27 : k) * N *
        ((48 : k) * (b * c ^ 2 - a * b ^ 3 / 9 - (3 : k) * d * e) -
          (35 / 32 : k) * beta * a ^ 4) := by
  ring_nf

theorem alphaWallMixedRowZeroRowTwo_X_eq_of_rowTwo
    (N a b c d e beta : k) (hN : N ≠ 0)
    (hrow2 :
      (-4 / 27 : k) *
          ((25 / 32 : k) * N * beta * a ^ 4 +
            N * ((-16 / 3 : k) * a * b ^ 3 + (48 : k) * b * c ^ 2 -
              (144 : k) * d * e)) +
        (5 / 18 : k) * N * beta * a ^ 4 = 0) :
    b * c ^ 2 - a * b ^ 3 / 9 - (3 : k) * d * e =
      (35 / 1536 : k) * beta * a ^ 4 := by
  have hpre : (-4 / 27 : k) * N ≠ 0 :=
    mul_ne_zero (by norm_num) hN
  have heq := alphaWallMixedRowTwo_sum_eq_X N a b c d e beta
  rw [heq] at hrow2
  have hsum := (mul_eq_zero.mp hrow2).resolve_left hpre
  have h48 : (48 : k) ≠ 0 := by norm_num
  have hX :
      (48 : k) * (b * c ^ 2 - a * b ^ 3 / 9 - (3 : k) * d * e) =
        (35 / 32 : k) * beta * a ^ 4 := by
    linear_combination hsum
  apply mul_left_cancel₀ h48
  rw [hX]
  ring

theorem alphaWallMixedRowZeroRowTwo_beta_eq_zero
    (N a b c d e beta : k) (hN : N ≠ 0) (ha : a ≠ 0)
    (hrow0 :
      (4 / 27 : k) * ((2 : k) * N * a *
          ((5 / 192 : k) * beta * a ^ 4 + b * c ^ 2 -
            a * b ^ 3 / 9 - (3 : k) * d * e)) +
        (5 / 108 : k) * N * beta * a ^ 5 = 0)
    (hrow2 :
      (-4 / 27 : k) *
          ((25 / 32 : k) * N * beta * a ^ 4 +
            N * ((-16 / 3 : k) * a * b ^ 3 + (48 : k) * b * c ^ 2 -
              (144 : k) * d * e)) +
        (5 / 18 : k) * N * beta * a ^ 4 = 0) :
    beta * a ^ 4 = 0 := by
  have hX0 := alphaWallMixedRowZeroRowTwo_X_eq_of_rowZero N a b c d e beta
    hN ha hrow0
  have hX2 := alphaWallMixedRowZeroRowTwo_X_eq_of_rowTwo N a b c d e beta
    hN hrow2
  have hcmp :
      -((35 / 192 : k) * beta * a ^ 4) = (35 / 1536 : k) * beta * a ^ 4 :=
    hX0.symm.trans hX2
  have hcoeff : (-315 / 1536 : k) * (beta * a ^ 4) = 0 := by
    linear_combination hcmp
  have hnz : (-315 / 1536 : k) ≠ 0 := by norm_num
  exact (mul_eq_zero.mp hcoeff).resolve_left hnz

theorem alphaWall_nat_lt_double_pred {n : ℕ} (hn : 1 < n) :
    n < 2 * n - 1 := by
  have h1 : 1 ≤ 2 * n := by omega
  have hsum : n + 1 < 2 * n := by omega
  have : n + 1 < (2 * n - 1) + 1 := by
    rwa [Nat.sub_add_cancel h1]
  exact Nat.lt_of_add_lt_add_right this

theorem alphaWall_nat_triple_lt_double_pred {n : ℕ} (hn : 2 < n) :
    3 * n < 2 * (2 * n - 1) := by
  have hmul : 2 * (2 * n - 1) = 4 * n - 2 := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_one, ← Nat.mul_assoc]
  rw [hmul]
  have h2 : 2 ≤ 4 * n := by omega
  have hsum : 3 * n + 2 < 4 * n := by omega
  have : 3 * n + 2 < (4 * n - 2) + 2 := by
    rwa [Nat.sub_add_cancel h2]
  exact Nat.lt_of_add_lt_add_right this

theorem alphaWall_sq_eq_zero {x : k} (h : x * x = 0) : x = 0 :=
  (mul_eq_zero.mp h).elim id id

theorem alphaWall_cube_eq_zero {x : k} (h : x * x * x = 0) : x = 0 := by
  rcases mul_eq_zero.mp h with hsq | hx
  · exact alphaWall_sq_eq_zero hsq
  · exact hx

theorem alphaWallMixedFibre_support_false
    (a b c : k) (ha : a ≠ 0) (hsupport : b ≠ 0 ∨ c ≠ 0)
    (hX : b * c ^ 2 - a * b ^ 3 / 9 = 0)
    (hrow1 : c * (c ^ 2 - a * b ^ 2) = 0) :
    False := by
  have hfact : b * ((9 : k) * c ^ 2 - a * b ^ 2) = 0 := by
    linear_combination (9 : k) * hX
  rcases mul_eq_zero.mp hfact with hb | hrel
  · have : c * c ^ 2 = 0 := by
      simpa [hb, sub_zero, mul_zero] using hrow1
    have hc0 : c = 0 :=
      alphaWall_cube_eq_zero (by simpa [pow_two] using this)
    rcases hsupport with hb' | hc'
    · exact hb' hb
    · exact hc' hc0
  · have hab : a * b ^ 2 = (9 : k) * c ^ 2 := by linear_combination -hrel
    rcases mul_eq_zero.mp hrow1 with hc0 | hsq
    · have : a * b ^ 2 = 0 := by
        simpa [hc0] using hab
      have hb : b = 0 :=
        alphaWall_sq_eq_zero (by
          simpa [pow_two] using (mul_eq_zero.mp this).resolve_left ha)
      rcases hsupport with hb' | hc'
      · exact hb' hb
      · exact hc' hc0
    · have hsq' : c ^ 2 = a * b ^ 2 := by linear_combination hsq
      have hab9 : a * b ^ 2 = (9 : k) * (a * b ^ 2) := by
        rw [hsq'] at hab
        exact hab
      have h8 : (8 : k) * (a * b ^ 2) = 0 := by
        linear_combination -(1 : k) * hab9
      have : a * b ^ 2 = 0 :=
        (mul_eq_zero.mp h8).resolve_left (by norm_num)
      have hb : b = 0 :=
        alphaWall_sq_eq_zero (by
          simpa [pow_two] using (mul_eq_zero.mp this).resolve_left ha)
      have hc0 : c = 0 :=
        alphaWall_sq_eq_zero (by
          rw [hb] at hsq'
          simpa using hsq')
      rcases hsupport with hb' | hc'
      · exact hb' hb
      · exact hc' hc0

/-! ## Load coefficient at `10n-1` -/

set_option maxHeartbeats 4000000 in
theorem cubicLoadRowZeroPolynomial68_coeff_tenRadius_of_alphaWall
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hl : l = 0) (hwall : g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadRowZeroPolynomial68 l alpha beta gamma delta epsilon zeta eta
      A B c D e).coeff (13 * n - 3 * g - 1) =
      alphaWallRowZeroLoadScalar68 (n : k) (A.coeff (2 * n)) beta := by
  let E := (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
  let Ul := cubicLoadUPolynomial68 l alpha beta gamma delta zeta A B c D e
  let Vl := cubicLoadVPolynomial68 l alpha beta gamma delta epsilon eta
    A B c D e
  have hUl : Ul.natDegree ≤ 4 * n := by
    have h := cubicLoadUPolynomial68_degreeBound_of_loadL l alpha beta gamma
      delta zeta A B c D e n g hl hA hB hc hD he
    have hmax : max (4 * n) (5 * n - g) = 4 * n := by omega
    rwa [hmax] at h
  have hVl : Vl.natDegree ≤ 6 * n :=
    cubicLoadVPolynomial68_degreeBound_of_loadL l alpha beta gamma delta
      epsilon eta A B c D e n g hl hA hB hc hD he
  have hE : E.natDegree ≤ 6 * n := by
    simp only [E]; compute_degree; omega
  have hDdeg : D.natDegree ≤ 4 * n := by omega
  have hA3 := coeff_pow_at_bound68 A (2 * n) 3 hA
  have hA3i : 3 * (2 * n) = 6 * n := by omega
  rw [hA3i] at hA3
  have hAclt : (A * c).natDegree < 6 * n := by compute_degree; omega
  have helt : e.natDegree < 6 * n := by omega
  have hEtop : E.coeff (6 * n) = (1 / 27 : k) * A.coeff (2 * n) ^ 3 := by
    simp only [E, coeff_add, coeff_smul, smul_eq_mul, hA3,
      coeff_eq_zero_of_natDegree_lt hAclt, coeff_eq_zero_of_natDegree_lt helt,
      mul_zero, add_zero]
  have hUltop : Ul.coeff (4 * n) =
      alpha * D.coeff (5 * n - g) +
        (5 / 24 * beta : k) * A.coeff (2 * n) ^ 2 := by
    simpa only [Ul] using
      cubicLoadUPolynomial68_coeff_fourRadius_of_alphaWall l alpha beta gamma
        delta zeta A B c D e n g hn hl hwall hA hB hc hD
  have hVltop : Vl.coeff (6 * n) =
      (1 / 27 * alpha : k) * A.coeff (2 * n) ^ 3 := by
    simpa only [Vl] using
      cubicLoadVPolynomial68_coeff_sixRadius_of_alphaWall l alpha beta gamma
        delta epsilon eta A B c D e n g hn hl hwall hA hB hc hD he
  have hDtop : D.coeff (4 * n) = D.coeff (5 * n - g) := by
    congr 1
    omega
  have h1 : (Ul * derivative E).coeff (13 * n - 3 * g - 1) =
      Ul.coeff (4 * n) * E.coeff (6 * n) * ((6 * n : ℕ) : k) := by
    have h := coeff_mul_derivative_at_bounds68 Ul E (4 * n) (6 * n)
      (by omega) hUl hE
    have hi : 4 * n + 6 * n - 1 = 13 * n - 3 * g - 1 := by omega
    rwa [hi] at h
  have h2 : (D * derivative Vl).coeff (13 * n - 3 * g - 1) =
      D.coeff (4 * n) * Vl.coeff (6 * n) * ((6 * n : ℕ) : k) := by
    have h := coeff_mul_derivative_at_bounds68 D Vl (4 * n) (6 * n)
      (by omega) hDdeg hVl
    have hi : 4 * n + 6 * n - 1 = 13 * n - 3 * g - 1 := by omega
    rwa [hi] at h
  have hcast6 : ((6 * n : ℕ) : k) = (6 : k) * (n : k) := by
    push_cast
    rfl
  change (Ul * derivative E - D * derivative Vl).coeff
      (13 * n - 3 * g - 1) = _
  rw [coeff_sub, h1, h2, hUltop, hEtop, hVltop, hDtop, hcast6]
  simp only [alphaWallRowZeroLoadScalar68, hwall]
  ring

/-! ## Residual row zero through `Q` -/

theorem residualRowZero_Be_cd_eq_Q (A B c d e : k[X]) :
    A * derivative A * B * e + A * derivative A * c * d =
      A * derivative A * residualIncidenceQ68 B c d e +
        (1 / 9 : k) • (A * derivative A * B ^ 3) := by
  have hsplit : B * e + c * d =
      residualIncidenceQ68 B c d e + (1 / 9 : k) • B ^ 3 := by
    simp only [residualIncidenceQ68]
    abel
  calc
    A * derivative A * B * e + A * derivative A * c * d
        = A * derivative A * (B * e + c * d) := by ring
    _ = A * derivative A *
          (residualIncidenceQ68 B c d e + (1 / 9 : k) • B ^ 3) := by
      rw [hsplit]
    _ = A * derivative A * residualIncidenceQ68 B c d e +
          (1 / 9 : k) • (A * derivative A * B ^ 3) := by
      simp only [mul_add, smul_add, Polynomial.smul_eq_C_mul]
      ring

set_option maxHeartbeats 4000000 in
theorem residualRowZero_coeff_Q_and_core_of_alphaWall
    (A B c d e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hwall : g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hQ : (residualIncidenceQ68 B c d e).natDegree ≤ 6 * n) :
    let Q := residualIncidenceQ68 B c d e
    (A * derivative A * Q).coeff (13 * n - 3 * g - 1) =
        A.coeff (2 * n) ^ 2 * Q.coeff (6 * n) * ((2 * n : ℕ) : k) ∧
      (A * derivative A * B ^ 3).coeff (13 * n - 3 * g - 1) =
        A.coeff (2 * n) ^ 2 * B.coeff (3 * n - g) ^ 3 *
          ((2 * n : ℕ) : k) ∧
      (derivative A * B * c ^ 2).coeff (13 * n - 3 * g - 1) =
        A.coeff (2 * n) * B.coeff (3 * n - g) *
          c.coeff (4 * n - g) ^ 2 * ((2 * n : ℕ) : k) := by
  let Q := residualIncidenceQ68 B c d e
  set idx := 13 * n - 3 * g - 1
  have hAQ := coeff_mul_mul_derivative_at_bounds68 A Q A
    (2 * n) (6 * n) (2 * n) (by omega) hA hQ hA
  have hiAQ : 2 * n + 6 * n + 2 * n - 1 = idx := by
    dsimp [idx]; omega
  rw [hiAQ] at hAQ
  have hAQ' : (A * derivative A * Q).coeff idx =
      A.coeff (2 * n) ^ 2 * Q.coeff (6 * n) * ((2 * n : ℕ) : k) := by
    rw [show (A * derivative A * Q).coeff idx =
        (A * Q * derivative A).coeff idx by
      congr 1
      ring]
    simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using hAQ
  have hB3deg : (B ^ 3).natDegree ≤ 9 * n - 3 * g := by
    compute_degree
    omega
  have hB3 : (B ^ 3).coeff (9 * n - 3 * g) =
      B.coeff (3 * n - g) ^ 3 := by
    have h := coeff_pow_at_bound68 B (3 * n - g) 3 hB
    have hi : 3 * (3 * n - g) = 9 * n - 3 * g := by omega
    simpa only [hi] using h
  have hAB3 := coeff_mul_mul_derivative_at_bounds68 A (B ^ 3) A
    (2 * n) (9 * n - 3 * g) (2 * n) (by omega) hA hB3deg hA
  have hiAB3 : 2 * n + (9 * n - 3 * g) + 2 * n - 1 = idx := by
    dsimp [idx]; omega
  rw [hiAB3, hB3] at hAB3
  have hAB3' : (A * derivative A * B ^ 3).coeff idx =
      A.coeff (2 * n) ^ 2 * B.coeff (3 * n - g) ^ 3 *
        ((2 * n : ℕ) : k) := by
    rw [show (A * derivative A * B ^ 3).coeff idx =
        (A * B ^ 3 * derivative A).coeff idx by
      congr 1
      ring]
    simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using hAB3
  have hc2deg : (c ^ 2).natDegree ≤ 8 * n - 2 * g := by
    compute_degree
    omega
  have hc2 : (c ^ 2).coeff (8 * n - 2 * g) =
      c.coeff (4 * n - g) ^ 2 := by
    have h := coeff_pow_at_bound68 c (4 * n - g) 2 hc
    have hi : 2 * (4 * n - g) = 8 * n - 2 * g := by omega
    simpa only [hi] using h
  have hBc2 := coeff_mul_mul_derivative_at_bounds68 B (c ^ 2) A
    (3 * n - g) (8 * n - 2 * g) (2 * n) (by omega) hB hc2deg hA
  have hiBc2 : (3 * n - g) + (8 * n - 2 * g) + 2 * n - 1 = idx := by
    dsimp [idx]; omega
  rw [hiBc2, hc2] at hBc2
  have hBc2' : (derivative A * B * c ^ 2).coeff idx =
      A.coeff (2 * n) * B.coeff (3 * n - g) *
        c.coeff (4 * n - g) ^ 2 * ((2 * n : ℕ) : k) := by
    rw [show (derivative A * B * c ^ 2).coeff idx =
        (B * c ^ 2 * derivative A).coeff idx by
      congr 1
      ring]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hBc2
  exact ⟨hAQ', hAB3', hBc2'⟩

set_option maxHeartbeats 4000000 in
theorem residualRowZero_lowTerms_degree_lt_of_right_of_alphaWall
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h ≤ 2 * g)
    (hwall : g = n) (hright : 3 * g < 2 * h)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (A * B ^ 2 * derivative d).natDegree < 13 * n - 3 * g - 1 ∧
      (A * B * derivative B * d).natDegree < 13 * n - 3 * g - 1 ∧
      (derivative A * d * e).natDegree < 13 * n - 3 * g - 1 ∧
      (B * c * derivative e).natDegree < 13 * n - 3 * g - 1 ∧
      (B * d * derivative d).natDegree < 13 * n - 3 * g - 1 ∧
      (derivative B * d ^ 2).natDegree < 13 * n - 3 * g - 1 ∧
      (c * derivative c * d).natDegree < 13 * n - 3 * g - 1 := by
  have hidx : 13 * n - 3 * g - 1 = 10 * n - 1 := by omega
  constructor
  · compute_degree; omega
  constructor
  · compute_degree; omega
  constructor
  · have hdA : (derivative A).natDegree ≤ 2 * n - 1 :=
      (natDegree_derivative_le A).trans (by omega)
    have hde := natDegree_mul_le_of_le hd he
    have hprod := natDegree_mul_le_of_le hdA hde
    have hsum : (2 * n - 1) + ((5 * n - h) + (6 * n - h)) =
        13 * n - 2 * h - 1 := by omega
    have hle : (derivative A * (d * e)).natDegree ≤
        13 * n - 2 * h - 1 := by
      simpa only [hsum] using hprod
    have hassoc : derivative A * (d * e) = derivative A * d * e := by ring
    rw [hassoc] at hle
    have hlt : 13 * n - 2 * h - 1 < 13 * n - 3 * g - 1 := by omega
    exact hle.trans_lt hlt
  constructor
  · compute_degree; omega
  constructor
  · compute_degree; omega
  constructor
  · compute_degree; omega
  · compute_degree; omega

set_option maxHeartbeats 4000000 in
theorem residualRowZero_lowTerms_degree_lt_of_balanced_of_alphaWall
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hwall : g = n) (hbalanced : 2 * h = 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (A * B ^ 2 * derivative d).natDegree < 13 * n - 3 * g - 1 ∧
      (A * B * derivative B * d).natDegree < 13 * n - 3 * g - 1 ∧
      (B * c * derivative e).natDegree < 13 * n - 3 * g - 1 ∧
      (B * d * derivative d).natDegree < 13 * n - 3 * g - 1 ∧
      (derivative B * d ^ 2).natDegree < 13 * n - 3 * g - 1 ∧
      (c * derivative c * d).natDegree < 13 * n - 3 * g - 1 := by
  constructor
  · compute_degree; omega
  constructor
  · compute_degree; omega
  constructor
  · compute_degree; omega
  constructor
  · compute_degree; omega
  constructor
  · compute_degree; omega
  · compute_degree; omega

set_option maxHeartbeats 6000000 in
/-- On `3g<2h` (right or double), residual row zero at `10n-1` is the
Q-feed plus the `B,c` core, with no `d e` summand. -/
theorem residualRowZero_coeff_rightChamber_of_alphaWall
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h ≤ 2 * g)
    (hwall : g = n) (hright : 3 * g < 2 * h)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualIncidenceQ68 B c d e).natDegree ≤ 6 * n)
    (beta : k)
    (hq0 : (residualIncidenceQ68 B c d e).coeff (6 * n) =
      -((5 / 192 : k) * beta * A.coeff (2 * n) ^ 3)) :
    (secondaryResidualRowZeroPolynomial68 A B c d e).coeff
        (13 * n - 3 * g - 1) =
      (4 / 27 : k) * ((2 : k) * (n : k) * A.coeff (2 * n) *
        ((5 / 192 : k) * beta * A.coeff (2 * n) ^ 4 +
          B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 -
          A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 / 9)) := by
  let Q := residualIncidenceQ68 B c d e
  set idx := 13 * n - 3 * g - 1
  have hcore := residualRowZero_coeff_Q_and_core_of_alphaWall A B c d e n g
    hn hg hwall hA hB hc hQ
  have hlow := residualRowZero_lowTerms_degree_lt_of_right_of_alphaWall
    A B c d e n g h hn hg hgh hh hwall hright hA hB hc hd he
  have hcast2 : ((2 * n : ℕ) : k) = (2 : k) * (n : k) := by
    push_cast
    rfl
  have h0d : (A * B ^ 2 * derivative d).coeff idx = 0 :=
    coeff_eq_zero_of_natDegree_lt hlow.1
  have h0Bd : (A * B * derivative B * d).coeff idx = 0 :=
    coeff_eq_zero_of_natDegree_lt hlow.2.1
  have h0Ade : (derivative A * d * e).coeff idx = 0 :=
    coeff_eq_zero_of_natDegree_lt hlow.2.2.1
  have h0Be : (B * c * derivative e).coeff idx = 0 :=
    coeff_eq_zero_of_natDegree_lt hlow.2.2.2.1
  have h0dd : (B * d * derivative d).coeff idx = 0 :=
    coeff_eq_zero_of_natDegree_lt hlow.2.2.2.2.1
  have h0Bd2 : (derivative B * d ^ 2).coeff idx = 0 :=
    coeff_eq_zero_of_natDegree_lt hlow.2.2.2.2.2.1
  have h0cc : (c * derivative c * d).coeff idx = 0 :=
    coeff_eq_zero_of_natDegree_lt hlow.2.2.2.2.2.2
  have hBe_cd := residualRowZero_Be_cd_eq_Q A B c d e
  have hAQsm : (A * derivative A * Q).coeff idx =
      A.coeff (2 * n) ^ 2 * Q.coeff (6 * n) * ((2 * n : ℕ) : k) :=
    hcore.1
  have hAB3sm : (A * derivative A * B ^ 3).coeff idx =
      A.coeff (2 * n) ^ 2 * B.coeff (3 * n - g) ^ 3 *
        ((2 * n : ℕ) : k) :=
    hcore.2.1
  have hBc2sm : (derivative A * B * c ^ 2).coeff idx =
      A.coeff (2 * n) * B.coeff (3 * n - g) *
        c.coeff (4 * n - g) ^ 2 * ((2 * n : ℕ) : k) :=
    hcore.2.2
  have hinner :
      (-(1 : k) • (A * derivative A * B * e) -
          A * derivative A * c * d -
          A * B ^ 2 * derivative d -
          A * B * derivative B * d +
          derivative A * B * c ^ 2 -
          (3 : k) • (derivative A * d * e) +
          (3 : k) • (B * c * derivative e) -
          (3 : k) • (B * d * derivative d) -
          (3 : k) • (derivative B * d ^ 2) -
          (3 : k) • (c * derivative c * d)).coeff idx =
        (2 : k) * (n : k) * A.coeff (2 * n) *
          ((5 / 192 : k) * beta * A.coeff (2 * n) ^ 4 +
            B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 -
            A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 / 9) := by
    have hBe :
        (A * derivative A * B * e + A * derivative A * c * d).coeff idx =
          (A * derivative A * Q).coeff idx +
            ((1 / 9 : k) • (A * derivative A * B ^ 3)).coeff idx := by
      have := congrArg (fun p : k[X] => p.coeff idx) hBe_cd
      simpa only [coeff_add, coeff_smul] using this
    simp only [coeff_add, coeff_sub, coeff_smul, smul_eq_mul, h0d, h0Bd,
      h0Ade, h0Be, h0dd, h0Bd2, h0cc, mul_zero]
    have hsum :
        -1 * (A * derivative A * B * e).coeff idx -
            (A * derivative A * c * d).coeff idx =
          -((A * derivative A * B * e + A * derivative A * c * d).coeff idx) := by
      rw [coeff_add]
      ring
    rw [hsum, hBe, coeff_smul, smul_eq_mul, hAQsm, hAB3sm, hBc2sm, hq0,
      hcast2]
    ring
  rw [secondaryResidualRowZeroPolynomial68, coeff_smul, smul_eq_mul, hinner]

set_option maxHeartbeats 6000000 in
/-- On `2h=3g`, residual row zero also sees `A' d e` at `10n-1`. -/
theorem residualRowZero_coeff_balancedChamber_of_alphaWall
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hwall : g = n) (hbalanced : 2 * h = 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualIncidenceQ68 B c d e).natDegree ≤ 6 * n)
    (beta : k)
    (hq0 : (residualIncidenceQ68 B c d e).coeff (6 * n) =
      -((5 / 192 : k) * beta * A.coeff (2 * n) ^ 3)) :
    (secondaryResidualRowZeroPolynomial68 A B c d e).coeff
        (13 * n - 3 * g - 1) =
      (4 / 27 : k) * ((2 : k) * (n : k) * A.coeff (2 * n) *
        ((5 / 192 : k) * beta * A.coeff (2 * n) ^ 4 +
          B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 -
          A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 / 9 -
          (3 : k) * d.coeff (5 * n - h) * e.coeff (6 * n - h))) := by
  let Q := residualIncidenceQ68 B c d e
  set idx := 13 * n - 3 * g - 1
  have hcore := residualRowZero_coeff_Q_and_core_of_alphaWall A B c d e n g
    hn hg hwall hA hB hc hQ
  have hlow := residualRowZero_lowTerms_degree_lt_of_balanced_of_alphaWall
    A B c d e n g h hn hg hgh hh hwall hbalanced hA hB hc hd he
  have hcast2 : ((2 * n : ℕ) : k) = (2 : k) * (n : k) := by
    push_cast
    rfl
  have hAde := coeff_mul_mul_derivative_at_bounds68 d e A
    (5 * n - h) (6 * n - h) (2 * n) (by omega) hd he hA
  have hiAde : (5 * n - h) + (6 * n - h) + 2 * n - 1 = idx := by
    dsimp [idx]; omega
  rw [hiAde] at hAde
  have hAde' : (derivative A * d * e).coeff idx =
      A.coeff (2 * n) * d.coeff (5 * n - h) * e.coeff (6 * n - h) *
        ((2 * n : ℕ) : k) := by
    rw [show (derivative A * d * e).coeff idx =
        (d * e * derivative A).coeff idx by
      congr 1
      ring]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hAde
  have h0d : (A * B ^ 2 * derivative d).coeff idx = 0 :=
    coeff_eq_zero_of_natDegree_lt hlow.1
  have h0Bd : (A * B * derivative B * d).coeff idx = 0 :=
    coeff_eq_zero_of_natDegree_lt hlow.2.1
  have h0Be : (B * c * derivative e).coeff idx = 0 :=
    coeff_eq_zero_of_natDegree_lt hlow.2.2.1
  have h0dd : (B * d * derivative d).coeff idx = 0 :=
    coeff_eq_zero_of_natDegree_lt hlow.2.2.2.1
  have h0Bd2 : (derivative B * d ^ 2).coeff idx = 0 :=
    coeff_eq_zero_of_natDegree_lt hlow.2.2.2.2.1
  have h0cc : (c * derivative c * d).coeff idx = 0 :=
    coeff_eq_zero_of_natDegree_lt hlow.2.2.2.2.2
  have hBe_cd := residualRowZero_Be_cd_eq_Q A B c d e
  have hinner :
      (-(1 : k) • (A * derivative A * B * e) -
          A * derivative A * c * d -
          A * B ^ 2 * derivative d -
          A * B * derivative B * d +
          derivative A * B * c ^ 2 -
          (3 : k) • (derivative A * d * e) +
          (3 : k) • (B * c * derivative e) -
          (3 : k) • (B * d * derivative d) -
          (3 : k) • (derivative B * d ^ 2) -
          (3 : k) • (c * derivative c * d)).coeff idx =
        (2 : k) * (n : k) * A.coeff (2 * n) *
          ((5 / 192 : k) * beta * A.coeff (2 * n) ^ 4 +
            B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 -
            A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 / 9 -
            (3 : k) * d.coeff (5 * n - h) * e.coeff (6 * n - h)) := by
    have hBe :
        (A * derivative A * B * e + A * derivative A * c * d).coeff idx =
          (A * derivative A * Q).coeff idx +
            ((1 / 9 : k) • (A * derivative A * B ^ 3)).coeff idx := by
      have := congrArg (fun p : k[X] => p.coeff idx) hBe_cd
      simpa only [coeff_add, coeff_smul] using this
    simp only [coeff_add, coeff_sub, coeff_smul, smul_eq_mul, h0d, h0Bd,
      h0Be, h0dd, h0Bd2, h0cc, mul_zero]
    have hsum :
        -1 * (A * derivative A * B * e).coeff idx -
            (A * derivative A * c * d).coeff idx =
          -((A * derivative A * B * e + A * derivative A * c * d).coeff idx) := by
      rw [coeff_add]
      ring
    rw [hsum, hBe, coeff_smul, smul_eq_mul, hcore.1, hcore.2.1, hcore.2.2,
      hAde', hq0, hcast2]
    ring
  rw [secondaryResidualRowZeroPolynomial68, coeff_smul, smul_eq_mul, hinner]

/-! ## Mixed row two at `8n-1` without a discriminant -/

set_option maxHeartbeats 8000000 in
theorem residualRowTwo_coeff_mixedCubic_of_alphaWall
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hwall : g = n) (hnotleft : ¬ 2 * h < 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualIncidenceQ68 B c d e).natDegree ≤ 6 * n)
    (beta : k)
    (hq0 : (residualIncidenceQ68 B c d e).coeff (6 * n) =
      -((5 / 192 : k) * beta * A.coeff (2 * n) ^ 3)) :
    (secondaryResidualRowTwoPolynomial68 A B c d e).coeff
        (11 * n - 3 * g - 1) =
      (-4 / 27 : k) *
        ((25 / 32 : k) * (n : k) * beta * A.coeff (2 * n) ^ 4 +
          (n : k) *
            ((-16 / 3 : k) * A.coeff (2 * n) *
                B.coeff (3 * n - g) ^ 3 +
              (48 : k) * B.coeff (3 * n - g) *
                c.coeff (4 * n - g) ^ 2 -
              (144 : k) *
                (if 2 * h = 3 * g then
                  d.coeff (5 * n - h) * e.coeff (6 * n - h)
                else 0))) := by
  let Q := residualIncidenceQ68 B c d e
  let inner := residualRowTwoInner68 A B c d e
  set idx := 11 * n - 3 * g - 1
  have hAQ := coeff_mul_derivative_at_bounds68 A Q (2 * n) (6 * n)
    (by omega) hA hQ
  have hiAQ : 2 * n + 6 * n - 1 = idx := by dsimp [idx]; omega
  rw [hiAQ] at hAQ
  have hQA := coeff_mul_derivative_at_bounds68 Q A (6 * n) (2 * n)
    (by omega) hQ hA
  have hiQA : 6 * n + 2 * n - 1 = idx := by dsimp [idx]; omega
  rw [hiQA] at hQA
  have hQA' : (derivative A * Q).coeff idx =
      A.coeff (2 * n) * Q.coeff (6 * n) * ((2 * n : ℕ) : k) := by
    rw [show (derivative A * Q).coeff idx = (Q * derivative A).coeff idx by
      congr 1
      ring]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hQA
  have hBd := residualRowTwoInner_Bd_degree_le68_of_alphaWall B d n g h
    hg hgh hh hwall hB hd
  have hBd' : (derivative (B ^ 2 * d)).natDegree < idx := by
    dsimp [idx]; omega
  have hB2deg : (B ^ 2).natDegree ≤ 6 * n - 2 * g := by
    compute_degree; omega
  have hB2 : (B ^ 2).coeff (6 * n - 2 * g) =
      B.coeff (3 * n - g) ^ 2 := by
    have h := coeff_pow_at_bound68 B (3 * n - g) 2 hB
    have hi : 2 * (3 * n - g) = 6 * n - 2 * g := by omega
    simpa only [hi] using h
  have hAB := coeff_mul_mul_derivative_at_bounds68 A (B ^ 2) B
    (2 * n) (6 * n - 2 * g) (3 * n - g) (by omega) hA hB2deg hB
  have hiAB : 2 * n + (6 * n - 2 * g) + (3 * n - g) - 1 = idx := by
    dsimp [idx]; omega
  rw [hiAB, hB2] at hAB
  have hABpow : (A * B ^ 2 * derivative B).coeff idx =
      A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 *
        ((3 * n - g : ℕ) : k) := by
    rw [hAB]; ring
  have hB3deg : (B ^ 3).natDegree ≤ 9 * n - 3 * g := by
    compute_degree; omega
  have hB3 : (B ^ 3).coeff (9 * n - 3 * g) =
      B.coeff (3 * n - g) ^ 3 := by
    have h := coeff_pow_at_bound68 B (3 * n - g) 3 hB
    have hi : 3 * (3 * n - g) = 9 * n - 3 * g := by omega
    simpa only [hi] using h
  have hA3B := coeff_mul_derivative_at_bounds68 (B ^ 3) A
    (9 * n - 3 * g) (2 * n) (by omega) hB3deg hA
  have hiA3B : (9 * n - 3 * g) + 2 * n - 1 = idx := by
    dsimp [idx]; omega
  rw [hiA3B, hB3] at hA3B
  have hA3B' : (derivative A * B ^ 3).coeff idx =
      A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 *
        ((2 * n : ℕ) : k) := by
    rw [show (derivative A * B ^ 3).coeff idx =
        (B ^ 3 * derivative A).coeff idx by
      congr 1
      ring]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hA3B
  have hc2deg : (c ^ 2).natDegree ≤ 8 * n - 2 * g := by
    compute_degree; omega
  have hc2 : (c ^ 2).coeff (8 * n - 2 * g) =
      c.coeff (4 * n - g) ^ 2 := by
    have h := coeff_pow_at_bound68 c (4 * n - g) 2 hc
    have hi : 2 * (4 * n - g) = 8 * n - 2 * g := by omega
    simpa only [hi] using h
  have hBccoeff := coeff_mul_at_bounds68 B (c ^ 2)
    (3 * n - g) (8 * n - 2 * g) hB hc2deg
  have hiBc : (3 * n - g) + (8 * n - 2 * g) = 11 * n - 3 * g := by omega
  rw [hiBc, hc2] at hBccoeff
  have hBc := coeff_derivative_at_bound68 (B * c ^ 2)
    (11 * n - 3 * g) (by omega)
  rw [hBccoeff] at hBc
  have hcast6 : ((6 * n : ℕ) : k) = (6 : k) * (n : k) := by push_cast; rfl
  have hcast2 : ((2 * n : ℕ) : k) = (2 : k) * (n : k) := by push_cast; rfl
  have hcast3 : ((3 * n - g : ℕ) : k) =
      (3 : k) * (n : k) - (g : k) := by
    rw [Nat.cast_sub (by omega : g ≤ 3 * n)]; push_cast; rfl
  have hcast11 : ((11 * n - 3 * g : ℕ) : k) =
      (11 : k) * (n : k) - (3 : k) * (g : k) := by
    rw [Nat.cast_sub (by omega : 3 * g ≤ 11 * n)]; push_cast; rfl
  have h0Bd : ((6 : k) • derivative (B ^ 2 * d)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hBd', mul_zero]
  have hQpart :
      ((-6 : k) • (A * derivative Q)).coeff idx +
        ((3 : k) • (derivative A * Q)).coeff idx =
        (25 / 32 : k) * (n : k) * beta * A.coeff (2 * n) ^ 4 := by
    rw [coeff_smul, coeff_smul, smul_eq_mul, smul_eq_mul, hAQ, hQA',
      hcast6, hcast2, hq0]
    trans ((-30 : k) * (n : k) * A.coeff (2 * n) *
      (-((5 / 192 : k) * beta * A.coeff (2 * n) ^ 3)))
    · ring
    exact alphaWallQInner_of_I4load68 (n : k) (A.coeff (2 * n)) beta
  have hcore :
      ((-2 : k) • (A * B ^ 2 * derivative B)).coeff idx +
        ((-2 / 3 : k) • (derivative A * B ^ 3)).coeff idx +
        ((6 : k) • derivative (B * c ^ 2)).coeff idx =
        (n : k) *
          ((-16 / 3 : k) * A.coeff (2 * n) *
              B.coeff (3 * n - g) ^ 3 +
            (48 : k) * B.coeff (3 * n - g) *
              c.coeff (4 * n - g) ^ 2) := by
    rw [coeff_smul, coeff_smul, coeff_smul, smul_eq_mul, smul_eq_mul,
      smul_eq_mul, hABpow, hA3B']
    dsimp [idx]
    rw [hBc, hcast3, hcast2, hcast11]
    simp only [hwall]
    ring
  have hdepart :
      ((-18 : k) • derivative (d * e)).coeff idx =
        (n : k) * (-(144 : k) *
          (if 2 * h = 3 * g then
            d.coeff (5 * n - h) * e.coeff (6 * n - h) else 0)) := by
    by_cases heq : 2 * h = 3 * g
    · have hide : (5 * n - h) + (6 * n - h) = 11 * n - 3 * g := by omega
      have hdecoeff := coeff_mul_at_bounds68 d e (5 * n - h) (6 * n - h)
        hd he
      rw [hide] at hdecoeff
      have hde := coeff_derivative_at_bound68 (d * e)
        (11 * n - 3 * g) (by omega)
      rw [hdecoeff] at hde
      rw [coeff_smul, smul_eq_mul, ite_eq_left heq]
      dsimp [idx]
      rw [hde, hcast11]
      simp only [hwall, heq]
      ring
    · have hright : 3 * g < 2 * h := by omega
      have hprod := natDegree_mul_le_of_le hd he
      have hsum : (5 * n - h) + (6 * n - h) = 11 * n - 2 * h := by omega
      rw [hsum] at hprod
      have hder := natDegree_derivative_le (d * e)
      have hle : (derivative (d * e)).natDegree ≤ 11 * n - 2 * h - 1 := by
        omega
      have hlt : 11 * n - 2 * h - 1 < idx := by
        dsimp [idx]; omega
      have hde' : (derivative (d * e)).natDegree < idx :=
        hle.trans_lt hlt
      rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hde',
        mul_zero, ite_eq_right heq, mul_zero]
      ring
  have hinner : inner.coeff idx =
      (25 / 32 : k) * (n : k) * beta * A.coeff (2 * n) ^ 4 +
        (n : k) *
          ((-16 / 3 : k) * A.coeff (2 * n) *
              B.coeff (3 * n - g) ^ 3 +
            (48 : k) * B.coeff (3 * n - g) *
              c.coeff (4 * n - g) ^ 2 -
            (144 : k) *
              (if 2 * h = 3 * g then
                d.coeff (5 * n - h) * e.coeff (6 * n - h) else 0)) := by
    dsimp [inner, residualRowTwoInner68]
    simp only [coeff_add]
    rw [h0Bd]
    linear_combination hQpart + hcore + hdepart
  rw [residualRowTwo_eq_inner68, coeff_smul, smul_eq_mul, hinner]

/-! ## Row-zero / row-two residual-plus-load equations -/

theorem cubicRowZeroPolynomial68_residualSplit
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c d e : k[X]) :
    let C0 := (1 / 3 : k) • A ^ 2 + c
    let D0 := (1 / 3 : k) • (A * B) + d
    let E0 := (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
    lowerRowZeroPolynomial68
      (integratedUPolynomial68 l alpha beta gamma delta zeta A B C0 D0 E0)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        A B C0 D0 E0) D0 E0 =
      secondaryResidualRowZeroPolynomial68 A B c d e +
        cubicLoadRowZeroPolynomial68 l alpha beta gamma delta epsilon zeta eta
          A B c ((1 / 3 : k) • (A * B) + d) e := by
  let C0 := (1 / 3 : k) • A ^ 2 + c
  let D0 := (1 / 3 : k) • (A * B) + d
  let E0 := (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
  have hcoords := integratedPolynomial68_cubicCoordinates
    l alpha beta gamma delta epsilon zeta eta A B c D0 e
  dsimp
  rw [hcoords.u_eq, hcoords.v_eq, cubicRowZeroPolynomial68_split]
  simpa only [D0] using
    congrArg (fun p => p + cubicLoadRowZeroPolynomial68 l alpha beta gamma
      delta epsilon zeta eta A B c D0 e)
      (cubicHomogeneousRowZeroPolynomial68_residualCoordinates A B c d e)

theorem weightedRadius68_ne_six (A B C0 D E : k[X]) :
    weightedRadius68 A B C0 D E ≠ 6 := by
  simp only [weightedRadius68]
  omega

/-! ## Chamber contradictions -/

set_option maxHeartbeats 4000000 in
theorem residualRowOne_coeff_double_of_alphaWall
    (A B c d e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hn2 : 2 < n) (hg : 0 < g) (hwall : g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - 2 * g)
    (he : e.natDegree ≤ 6 * n - 2 * g)
    (hI3 : (secondaryResidualInvariantThreePolynomial68 A B c d e).natDegree ≤
      6 * n) :
    (secondaryResidualRowOnePolynomial68 A B c d e).coeff
        (12 * n - 3 * g - 1) =
      (-4 / 27 : k) *
        ((-2 : k) * (A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 *
            c.coeff (4 * n - g) * ((9 * n : ℕ) : k)) +
          (6 : k) * (c.coeff (4 * n - g) ^ 3 * ((3 * n : ℕ) : k))) := by
  have hh' : 2 * n - 1 < 2 * g := by
    rw [hwall]
    exact Nat.sub_lt (Nat.mul_pos (by omega : 0 < 2) hn) (by omega : 0 < 1)
  have hgh' : g < 2 * n - 1 := by
    rw [hwall]
    exact alphaWall_nat_lt_double_pred (lt_trans (by omega : 1 < 2) hn2)
  have hright' : 3 * g < 2 * (2 * n - 1) := by
    rw [hwall]
    exact alphaWall_nat_triple_lt_double_pred hn2
  have hd' : d.natDegree ≤ 5 * n - (2 * n - 1) := by
    have : 2 * n - 1 ≤ 2 * g := by
      rw [hwall]
      exact Nat.sub_le _ _
    exact hd.trans (Nat.sub_le_sub_left this (5 * n))
  have he' : e.natDegree ≤ 6 * n - (2 * n - 1) := by
    have : 2 * n - 1 ≤ 2 * g := by
      rw [hwall]
      exact Nat.sub_le _ _
    exact he.trans (Nat.sub_le_sub_left this (6 * n))
  simpa using
    residualRowOne_coeff_rightChamber_of_alphaWall A B c d e n g (2 * n - 1)
      hn hg hgh' hh' hwall hright' hA hB hc hd' he' hI3

theorem residualRowOne_double_c_mul_of_alphaWall
    (A B c d e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hn2 : 2 < n) (hg : 0 < g) (hwall : g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hcdeg : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - 2 * g)
    (he : e.natDegree ≤ 6 * n - 2 * g)
    (hI3 : (secondaryResidualInvariantThreePolynomial68 A B c d e).natDegree ≤
      6 * n)
    (hrow : (secondaryResidualRowOnePolynomial68 A B c d e).coeff
        (12 * n - 3 * g - 1) = 0) :
    c.coeff (4 * n - g) *
        (c.coeff (4 * n - g) ^ 2 -
          A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2) = 0 := by
  have h := residualRowOne_coeff_double_of_alphaWall A B c d e n g
    hn hn2 hg hwall hA hB hcdeg hd he hI3
  rw [h] at hrow
  have hcast9 : ((9 * n : ℕ) : k) = (9 : k) * (n : k) := by push_cast; rfl
  have hcast3 : ((3 * n : ℕ) : k) = (3 : k) * (n : k) := by push_cast; rfl
  rw [hcast9, hcast3] at hrow
  have hpre : (-4 / 27 : k) * ((18 : k) * (n : k)) ≠ 0 :=
    mul_ne_zero (by norm_num) (mul_ne_zero (by norm_num)
      (Nat.cast_ne_zero.mpr (by omega)))
  have h' :
      (-2 : k) * (A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 *
          c.coeff (4 * n - g) * ((9 : k) * (n : k))) +
        (6 : k) * (c.coeff (4 * n - g) ^ 3 * ((3 : k) * (n : k))) = 0 := by
    have hnz : (-4 / 27 : k) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp hrow).resolve_left hnz
  have : (18 : k) * (n : k) *
      (c.coeff (4 * n - g) ^ 3 -
        A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 *
          c.coeff (4 * n - g)) = 0 := by
    linear_combination h'
  have hN : (18 : k) * (n : k) ≠ 0 :=
    mul_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr (by omega))
  have := (mul_eq_zero.mp this).resolve_left hN
  linear_combination this

/-! ## Canonical expanded transport: the whole wall is empty -/

set_option maxHeartbeats 8000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_alphaWallBalancedImpossible68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (h : ℕ) (hterminal : terminal ≠ 0)
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
      g = n)
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
      d.natDegree ≤ 5 * n - h ∧ ee.natDegree ≤ 6 * n - h)
    (hbalanced :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      2 * h = 3 * g)
    (hattained :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let d := secondaryDDefectPolynomial68 Ae Be De
      d.coeff (5 * n - h) ≠ 0 ∨ ee.coeff (6 * n - h) ≠ 0) :
    False := by
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
  change g = n at hwall
  change g < h at hgh
  change h < 2 * g at hh
  change d.natDegree ≤ 5 * n - h ∧ ee.natDegree ≤ 6 * n - h at hmiddle
  change 2 * h = 3 * g at hbalanced
  change d.coeff (5 * n - h) ≠ 0 ∨ ee.coeff (6 * n - h) ≠ 0 at hattained
  have hclass :=
    maximalExpandedIntegratedPolynomialLowerSystem_alphaWallClassified68_of_wall
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
  have hl : l = 0 := hclass.1
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
  have ha : Ae.coeff (2 * n) ≠ 0 := by
    simpa only [n, Ae] using hcore.2.2.2.2.2
  have hg : 0 < g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.1
  have hA : Ae.natDegree ≤ 2 * n := by
    have hAe : Ae.natDegree = 2 * n := by
      simpa only [n, Ae, Be, Ce, De, Ee] using hdrop.1
    omega
  have hB : Be.natDegree ≤ 3 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.2.1
  have hc : ce.natDegree ≤ 4 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.2.2.1
  have hD : De.natDegree ≤ 5 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.2.2.2.1
  have he0 : ee.natDegree ≤ 6 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
      hsecondary.2.2.2.2.1
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec :
      Ee = (1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using
      cubicEDefectPolynomial68_eq_cubicCoordinates Ae Ce Ee
  have hDrec : De = (1 / 3 : k) • (Ae * Be) + d := by
    simpa only [d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
  have hboundary :=
    maximalExpandedIntegratedPolynomialLowerSystem_alphaWallBoundary68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
  have hsupport : Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0 :=
    hboundary.2.2.2
  obtain ⟨i4, hi4⟩ := hsys.firstFour
  have hi4e : firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i4 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_firstIntegralFourPolynomial68_of_eq
        l beta gamma delta epsilon zeta i4 A B C0 D E hi4
  have hi4c := hi4e
  rw [hCrec, hErec, firstIntegralFourPolynomial68_cubicCoordinates,
    hDrec, hl] at hi4c
  have hd_le : d.natDegree ≤ 5 * n - g := by omega
  have hQdeg :
      (residualIncidenceQ68 Be ce d ee).natDegree ≤ 6 * n :=
    residualIncidenceQ68_degree_le_sixRadius_of_alphaWall
      beta gamma delta epsilon zeta i4 Ae Be ce d ee n g hwall
      hA hB hc hd_le he0 hi4c
  have hq0 :
      (residualIncidenceQ68 Be ce d ee).coeff (6 * n) =
        -((5 / 192 : k) * beta * Ae.coeff (2 * n) ^ 3) :=
    residualIncidenceQ68_coeff_sixRadius_of_alphaWall
      beta gamma delta epsilon zeta i4 Ae Be ce d ee n g hn hwall
      hA hB hc (by simpa only [hDrec] using hD) he0 hi4c
  have hI3deg :
      (secondaryResidualInvariantThreePolynomial68 Ae Be ce d ee).natDegree ≤
        6 * n := by
    obtain ⟨i3, hi3⟩ := hsys.firstThree
    have hi3e : firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
        Ae Be Ce De Ee = C i3 := by
      simpa only [Ae, Be, Ce, De, Ee] using
        expand_firstIntegralThreePolynomial68_of_eq
          l beta gamma delta epsilon zeta i3 A B C0 D E hi3
    have hi3c := hi3e
    rw [hCrec, hErec, firstIntegralThreePolynomial68_cubicCoordinates,
      hDrec, hl] at hi3c
    exact secondaryResidualInvariantThreePolynomial68_degree_le_sixRadius_of_alphaWall
      beta gamma delta epsilon zeta i3 Ae Be ce d ee n g hwall
      hA hB hc hd_le he0 hi3c
  have hface :=
    maximalExpandedIntegratedPolynomialLowerSystem_alphaWallResidualMiddleFace68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E h
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hgh)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hh)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d] using hmiddle)
  have hclassif := secondaryResidualBetweenFace68_classify_of_support
    (Ae.coeff (2 * n)) (Be.coeff (3 * n - g)) (ce.coeff (4 * n - g))
    (d.coeff (5 * n - h)) (ee.coeff (6 * n - h))
    ha hsupport hattained hface.2
  have hc0 : ce.coeff (4 * n - g) ≠ 0 := hclassif.2.1
  have hdisc :
      Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 2 +
        (3 : k) * ce.coeff (4 * n - g) ^ 2 = 0 := hclassif.2.2.2.2
  have hinc := hface.2.four
  have h2e : lowerRowTwoPolynomial68
      (integratedSPolynomial68 l alpha beta delta Ae Be Ce De)
      (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) Be Ce De Ee = 0 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_lowerRowTwoPolynomial68_of_system
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
  rw [hCrec, hDrec, hErec] at h2e
  have hsum2 :
      secondaryResidualRowTwoPolynomial68 Ae Be ce d ee +
        cubicLoadRowTwoPolynomial68 l alpha beta gamma delta epsilon zeta eta
          Ae Be ce ((1 / 3 : k) • (Ae * Be) + d) ee = 0 := by
    simpa using (cubicRowTwoPolynomial68_residualSplit
      l alpha beta gamma delta epsilon zeta eta Ae Be ce d ee).symm.trans h2e
  have hload2 := cubicLoadRowTwoPolynomial68_coeff_cubicFace_of_alphaWall
    l alpha beta gamma delta epsilon zeta eta Ae Be ce De ee n g
    hn hg hl hwall hA hB hc hD he0
  have hres2 := congrArg
    (fun p : k[X] => p.coeff (11 * n - 3 * g - 1)) hsum2
  rw [coeff_add, coeff_zero] at hres2
  have hmix2 := residualRowTwo_coeff_mixedCubic_of_alphaWall
    Ae Be ce d ee n g h hn hg hgh hh hwall
    (by intro hlt; omega) hA hB hc hmiddle.1 hmiddle.2 hQdeg beta hq0
  have hrow2 :
      (-4 / 27 : k) *
          ((25 / 32 : k) * (n : k) * beta * Ae.coeff (2 * n) ^ 4 +
            (n : k) *
              ((-16 / 3 : k) * Ae.coeff (2 * n) *
                  Be.coeff (3 * n - g) ^ 3 +
                (48 : k) * Be.coeff (3 * n - g) *
                  ce.coeff (4 * n - g) ^ 2 -
                (144 : k) * d.coeff (5 * n - h) *
                  ee.coeff (6 * n - h))) +
        alphaWallRowTwoLoadScalar68 (n : k) (Ae.coeff (2 * n)) beta = 0 := by
    have hL := hload2
    rw [hDrec] at hL
    rw [hmix2, hL] at hres2
    simpa only [ite_eq_left hbalanced, mul_assoc, alphaWallRowTwoLoadScalar68]
      using hres2
  have h0e : lowerRowZeroPolynomial68
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) De Ee =
      C terminal * (60 * (X ^ 59 : k[X])) := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_lowerRowZeroPolynomial68_of_system
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
  rw [hCrec, hDrec, hErec] at h0e
  have hsplit0 := cubicRowZeroPolynomial68_residualSplit
    l alpha beta gamma delta epsilon zeta eta Ae Be ce d ee
  have hsum0 :
      secondaryResidualRowZeroPolynomial68 Ae Be ce d ee +
        cubicLoadRowZeroPolynomial68 l alpha beta gamma delta epsilon zeta eta
          Ae Be ce ((1 / 3 : k) • (Ae * Be) + d) ee =
        C terminal * (60 * (X ^ 59 : k[X])) := by
    simpa using hsplit0.symm.trans h0e
  have hidx : 13 * n - 3 * g - 1 ≠ 59 := by
    have hn6 : n ≠ 6 := by
      simpa only [n] using weightedRadius68_ne_six A B C0 D E
    omega
  have hterm :
      (C terminal * (60 * (X ^ 59 : k[X]))).coeff
          (13 * n - 3 * g - 1) = 0 := by
    simp [coeff_C_mul, coeff_X_pow, hidx]
  have hload0 := cubicLoadRowZeroPolynomial68_coeff_tenRadius_of_alphaWall
    l alpha beta gamma delta epsilon zeta eta Ae Be ce De ee n g
    hn hg hl hwall hA hB hc hD he0
  have hmix0 := residualRowZero_coeff_balancedChamber_of_alphaWall
    Ae Be ce d ee n g h hn hg hgh hh hwall hbalanced
    hA hB hc hmiddle.1 hmiddle.2 hQdeg beta hq0
  have hres0 := congrArg
    (fun p : k[X] => p.coeff (13 * n - 3 * g - 1)) hsum0
  rw [coeff_add, hmix0, hterm] at hres0
  have hrow0 :
      (4 / 27 : k) * ((2 : k) * (n : k) * Ae.coeff (2 * n) *
          ((5 / 192 : k) * beta * Ae.coeff (2 * n) ^ 4 +
            Be.coeff (3 * n - g) * ce.coeff (4 * n - g) ^ 2 -
            Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 3 / 9 -
            (3 : k) * d.coeff (5 * n - h) * ee.coeff (6 * n - h))) +
        alphaWallRowZeroLoadScalar68 (n : k) (Ae.coeff (2 * n)) beta = 0 := by
    have hL := hload0
    rw [hDrec] at hL
    rw [hL] at hres0
    exact hres0
  have hN : (n : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hbeta := alphaWallMixedRowZeroRowTwo_beta_eq_zero
    (n : k) (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
    (ce.coeff (4 * n - g)) (d.coeff (5 * n - h))
    (ee.coeff (6 * n - h)) beta hN ha
    (by simpa [alphaWallRowZeroLoadScalar68] using hrow0)
    (by simpa [alphaWallRowTwoLoadScalar68] using hrow2)
  have hrel :
      (4 : k) * Be.coeff (3 * n - g) * ce.coeff (4 * n - g) ^ 2 -
        (9 : k) * d.coeff (5 * n - h) * ee.coeff (6 * n - h) = 0 := by
    have hX := alphaWallMixedRowZeroRowTwo_X_eq_of_rowZero
      (n : k) (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
      (ce.coeff (4 * n - g)) (d.coeff (5 * n - h))
      (ee.coeff (6 * n - h)) beta hN ha
      (by simpa [alphaWallRowZeroLoadScalar68] using hrow0)
    have : beta * Ae.coeff (2 * n) ^ 4 = 0 := hbeta
    have hβ : (35 / 192 : k) * beta * Ae.coeff (2 * n) ^ 4 = 0 := by
      rw [show (35 / 192 : k) * beta * Ae.coeff (2 * n) ^ 4 =
          (35 / 192 : k) * (beta * Ae.coeff (2 * n) ^ 4) by ring, this,
        mul_zero]
    rw [hβ, neg_zero] at hX
    have hab : Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 2 =
        -((3 : k) * ce.coeff (4 * n - g) ^ 2) := by
      linear_combination hdisc
    have :
        (4 / 3 : k) * Be.coeff (3 * n - g) * ce.coeff (4 * n - g) ^ 2 -
          (3 : k) * d.coeff (5 * n - h) * ee.coeff (6 * n - h) = 0 := by
      have := hX
      have : Be.coeff (3 * n - g) * ce.coeff (4 * n - g) ^ 2 -
          Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 3 / 9 -
          (3 : k) * d.coeff (5 * n - h) * ee.coeff (6 * n - h) = 0 := this
      have hb3 :
          Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 3 =
            -((3 : k) * Be.coeff (3 * n - g) * ce.coeff (4 * n - g) ^ 2) := by
        linear_combination hab * Be.coeff (3 * n - g)
      rw [hb3] at this
      linear_combination this
    linear_combination (3 : k) * this
  have hrow1 :=
    maximalExpandedIntegratedPolynomialLowerSystem_alphaWallRowOneCubicFace68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
  exact residualRowOne_not_balancedChamber68_of_alphaWall
    Ae Be ce d ee n g h hn hg hgh hh hwall hbalanced
    hA hB hc hmiddle.1 hmiddle.2 hI3deg hc0 hdisc hinc hrel hrow1.2

set_option maxHeartbeats 8000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_alphaWallDoubleImpossible68
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
      g = n)
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
    False := by
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
  change g = n at hwall
  change d.natDegree ≤ 5 * n - 2 * g ∧
    ee.natDegree ≤ 6 * n - 2 * g at hdouble
  have hclass :=
    maximalExpandedIntegratedPolynomialLowerSystem_alphaWallClassified68_of_wall
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
  have hl : l = 0 := hclass.1
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
  have ha : Ae.coeff (2 * n) ≠ 0 := by
    simpa only [n, Ae] using hcore.2.2.2.2.2
  have hg : 0 < g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.1
  have hA : Ae.natDegree ≤ 2 * n := by
    have hAe : Ae.natDegree = 2 * n := by
      simpa only [n, Ae, Be, Ce, De, Ee] using hdrop.1
    omega
  have hB : Be.natDegree ≤ 3 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.2.1
  have hc : ce.natDegree ≤ 4 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.2.2.1
  have hD : De.natDegree ≤ 5 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.2.2.2.1
  have he0 : ee.natDegree ≤ 6 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
      hsecondary.2.2.2.2.1
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec :
      Ee = (1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using
      cubicEDefectPolynomial68_eq_cubicCoordinates Ae Ce Ee
  have hDrec : De = (1 / 3 : k) • (Ae * Be) + d := by
    simpa only [d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
  have hboundary :=
    maximalExpandedIntegratedPolynomialLowerSystem_alphaWallBoundary68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
  have hsupport : Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0 :=
    hboundary.2.2.2
  obtain ⟨i4, hi4⟩ := hsys.firstFour
  have hi4e : firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i4 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_firstIntegralFourPolynomial68_of_eq
        l beta gamma delta epsilon zeta i4 A B C0 D E hi4
  have hi4c := hi4e
  rw [hCrec, hErec, firstIntegralFourPolynomial68_cubicCoordinates,
    hDrec, hl] at hi4c
  have hd_le : d.natDegree ≤ 5 * n - g := by omega
  have hQdeg :
      (residualIncidenceQ68 Be ce d ee).natDegree ≤ 6 * n :=
    residualIncidenceQ68_degree_le_sixRadius_of_alphaWall
      beta gamma delta epsilon zeta i4 Ae Be ce d ee n g hwall
      hA hB hc hd_le he0 hi4c
  have hq0 :
      (residualIncidenceQ68 Be ce d ee).coeff (6 * n) =
        -((5 / 192 : k) * beta * Ae.coeff (2 * n) ^ 3) :=
    residualIncidenceQ68_coeff_sixRadius_of_alphaWall
      beta gamma delta epsilon zeta i4 Ae Be ce d ee n g hn hwall
      hA hB hc (by simpa only [hDrec] using hD) he0 hi4c
  have hI3deg :
      (secondaryResidualInvariantThreePolynomial68 Ae Be ce d ee).natDegree ≤
        6 * n := by
    obtain ⟨i3, hi3⟩ := hsys.firstThree
    have hi3e : firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
        Ae Be Ce De Ee = C i3 := by
      simpa only [Ae, Be, Ce, De, Ee] using
        expand_firstIntegralThreePolynomial68_of_eq
          l beta gamma delta epsilon zeta i3 A B C0 D E hi3
    have hi3c := hi3e
    rw [hCrec, hErec, firstIntegralThreePolynomial68_cubicCoordinates,
      hDrec, hl] at hi3c
    exact secondaryResidualInvariantThreePolynomial68_degree_le_sixRadius_of_alphaWall
      beta gamma delta epsilon zeta i3 Ae Be ce d ee n g hwall
      hA hB hc hd_le he0 hi3c
  have hnlarge : 10 ≤ n := by
    have hn' := hn
    dsimp only [n, weightedRadius68] at hn' ⊢
    omega
  have hn2 : 2 < n := Nat.lt_of_lt_of_le (by omega : 2 < 10) hnlarge
  have hproxy : 2 * g - 1 < 2 * g :=
    Nat.sub_lt (Nat.mul_pos (by omega : 0 < 2) hg) (by omega : 0 < 1)
  have hgh_proxy : g < 2 * g - 1 := by
    rw [hwall]
    exact alphaWall_nat_lt_double_pred (lt_trans (by omega : 1 < 2) hn2)
  have hd_proxy : d.natDegree ≤ 5 * n - (2 * g - 1) := by
    have : 2 * g - 1 ≤ 2 * g := Nat.sub_le _ _
    exact hdouble.1.trans (Nat.sub_le_sub_left this (5 * n))
  have he_proxy : ee.natDegree ≤ 6 * n - (2 * g - 1) := by
    have : 2 * g - 1 ≤ 2 * g := Nat.sub_le _ _
    exact hdouble.2.trans (Nat.sub_le_sub_left this (6 * n))
  have hright : 3 * g < 2 * (2 * g) := by omega
  have hnotleft_proxy : ¬ 2 * (2 * g - 1) < 3 * g := by
    have hmul : 2 * (2 * g - 1) = 4 * g - 2 := by
      rw [Nat.mul_sub_left_distrib, Nat.mul_one, ← Nat.mul_assoc]
    intro hlt
    rw [hmul] at hlt
    have : 2 < g := by
      rw [hwall]
      exact hn2
    omega
  have hgh2 : g < 2 * g := by omega
  have h2e : lowerRowTwoPolynomial68
      (integratedSPolynomial68 l alpha beta delta Ae Be Ce De)
      (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) Be Ce De Ee = 0 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_lowerRowTwoPolynomial68_of_system
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
  rw [hCrec, hDrec, hErec] at h2e
  have hsum2 :
      secondaryResidualRowTwoPolynomial68 Ae Be ce d ee +
        cubicLoadRowTwoPolynomial68 l alpha beta gamma delta epsilon zeta eta
          Ae Be ce ((1 / 3 : k) • (Ae * Be) + d) ee = 0 := by
    simpa using (cubicRowTwoPolynomial68_residualSplit
      l alpha beta gamma delta epsilon zeta eta Ae Be ce d ee).symm.trans h2e
  have hload2 := cubicLoadRowTwoPolynomial68_coeff_cubicFace_of_alphaWall
    l alpha beta gamma delta epsilon zeta eta Ae Be ce De ee n g
    hn hg hl hwall hA hB hc hD he0
  have hres2 := congrArg
    (fun p : k[X] => p.coeff (11 * n - 3 * g - 1)) hsum2
  rw [coeff_add, coeff_zero] at hres2
  have hmix2 := residualRowTwo_coeff_mixedCubic_of_alphaWall
    Ae Be ce d ee n g (2 * g - 1) hn hg hgh_proxy hproxy hwall hnotleft_proxy
    hA hB hc hd_proxy he_proxy hQdeg beta hq0
  have hrow2 :
      (-4 / 27 : k) *
          ((25 / 32 : k) * (n : k) * beta * Ae.coeff (2 * n) ^ 4 +
            (n : k) *
              ((-16 / 3 : k) * Ae.coeff (2 * n) *
                  Be.coeff (3 * n - g) ^ 3 +
                (48 : k) * Be.coeff (3 * n - g) *
                  ce.coeff (4 * n - g) ^ 2)) +
        alphaWallRowTwoLoadScalar68 (n : k) (Ae.coeff (2 * n)) beta = 0 := by
    have hne : ¬ 2 * (2 * g - 1) = 3 * g := by
      have hmul : 2 * (2 * g - 1) = 4 * g - 2 := by
        rw [Nat.mul_sub_left_distrib, Nat.mul_one, ← Nat.mul_assoc]
      rw [hmul]
      have : 2 < g := by
        rw [hwall]
        exact hn2
      omega
    have hL := hload2
    rw [hDrec] at hL
    rw [hmix2, hL] at hres2
    simpa only [ite_eq_right hne, sub_zero, mul_zero, alphaWallRowTwoLoadScalar68]
      using hres2
  have h0e : lowerRowZeroPolynomial68
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) De Ee =
      C terminal * (60 * (X ^ 59 : k[X])) := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_lowerRowZeroPolynomial68_of_system
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
  rw [hCrec, hDrec, hErec] at h0e
  have hsplit0 := cubicRowZeroPolynomial68_residualSplit
    l alpha beta gamma delta epsilon zeta eta Ae Be ce d ee
  have hsum0 :
      secondaryResidualRowZeroPolynomial68 Ae Be ce d ee +
        cubicLoadRowZeroPolynomial68 l alpha beta gamma delta epsilon zeta eta
          Ae Be ce ((1 / 3 : k) • (Ae * Be) + d) ee =
        C terminal * (60 * (X ^ 59 : k[X])) := by
    simpa using hsplit0.symm.trans h0e
  have hidx : 13 * n - 3 * g - 1 ≠ 59 := by
    have hn6 : n ≠ 6 := by
      simpa only [n] using weightedRadius68_ne_six A B C0 D E
    omega
  have hterm :
      (C terminal * (60 * (X ^ 59 : k[X]))).coeff
          (13 * n - 3 * g - 1) = 0 := by
    simp [coeff_C_mul, coeff_X_pow, hidx]
  have hload0 := cubicLoadRowZeroPolynomial68_coeff_tenRadius_of_alphaWall
    l alpha beta gamma delta epsilon zeta eta Ae Be ce De ee n g
    hn hg hl hwall hA hB hc hD he0
  have hmix0 := residualRowZero_coeff_rightChamber_of_alphaWall
    Ae Be ce d ee n g (2 * g) hn hg hgh2 (le_rfl) hwall hright
    hA hB hc hdouble.1 hdouble.2 hQdeg beta hq0
  have hres0 := congrArg
    (fun p : k[X] => p.coeff (13 * n - 3 * g - 1)) hsum0
  rw [coeff_add, hmix0, hterm] at hres0
  have hrow0 :
      (4 / 27 : k) * ((2 : k) * (n : k) * Ae.coeff (2 * n) *
          ((5 / 192 : k) * beta * Ae.coeff (2 * n) ^ 4 +
            Be.coeff (3 * n - g) * ce.coeff (4 * n - g) ^ 2 -
            Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 3 / 9)) +
        alphaWallRowZeroLoadScalar68 (n : k) (Ae.coeff (2 * n)) beta = 0 := by
    have hL := hload0
    rw [hDrec] at hL
    rw [hL] at hres0
    exact hres0
  have hN : (n : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hrow0' :
      (4 / 27 : k) * ((2 : k) * (n : k) * Ae.coeff (2 * n) *
          ((5 / 192 : k) * beta * Ae.coeff (2 * n) ^ 4 +
            Be.coeff (3 * n - g) * ce.coeff (4 * n - g) ^ 2 -
            Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 3 / 9 -
            (3 : k) * (0 : k) * (0 : k))) +
        alphaWallRowZeroLoadScalar68 (n : k) (Ae.coeff (2 * n)) beta = 0 := by
    simpa [mul_zero, sub_zero] using hrow0
  have hrow2' :
      (-4 / 27 : k) *
          ((25 / 32 : k) * (n : k) * beta * Ae.coeff (2 * n) ^ 4 +
            (n : k) *
              ((-16 / 3 : k) * Ae.coeff (2 * n) *
                  Be.coeff (3 * n - g) ^ 3 +
                (48 : k) * Be.coeff (3 * n - g) *
                  ce.coeff (4 * n - g) ^ 2 -
                (144 : k) * (0 : k) * (0 : k))) +
        alphaWallRowTwoLoadScalar68 (n : k) (Ae.coeff (2 * n)) beta = 0 := by
    simpa [mul_zero, sub_zero] using hrow2
  have hbeta := alphaWallMixedRowZeroRowTwo_beta_eq_zero
    (n : k) (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
    (ce.coeff (4 * n - g)) (0 : k) (0 : k) beta hN ha
    (by simpa [alphaWallRowZeroLoadScalar68] using hrow0')
    (by simpa [alphaWallRowTwoLoadScalar68] using hrow2')
  have hrow1c := residualRowOne_double_c_mul_of_alphaWall
    Ae Be ce d ee n g hn hn2 hg hwall hA hB hc hdouble.1 hdouble.2 hI3deg
    (by
      have hrow1 :=
        maximalExpandedIntegratedPolynomialLowerSystem_alphaWallRowOneCubicFace68
          l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
          hterminal hsys
          (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
      exact hrow1.2)
  have hX :
      Be.coeff (3 * n - g) * ce.coeff (4 * n - g) ^ 2 -
        Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 3 / 9 = 0 := by
    have hX0 := alphaWallMixedRowZeroRowTwo_X_eq_of_rowZero
      (n : k) (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
      (ce.coeff (4 * n - g)) (0 : k) (0 : k) beta hN ha
      (by simpa [alphaWallRowZeroLoadScalar68] using hrow0')
    have hβ : (35 / 192 : k) * beta * Ae.coeff (2 * n) ^ 4 = 0 := by
      rw [show (35 / 192 : k) * beta * Ae.coeff (2 * n) ^ 4 =
          (35 / 192 : k) * (beta * Ae.coeff (2 * n) ^ 4) by ring, hbeta,
        mul_zero]
    rw [hβ, neg_zero] at hX0
    simpa [mul_zero, sub_zero] using hX0
  exact alphaWallMixedFibre_support_false
    (Ae.coeff (2 * n)) (Be.coeff (3 * n - g)) (ce.coeff (4 * n - g))
    ha hsupport hX hrow1c

set_option maxHeartbeats 4000000 in
/-- On the canonical expanded system, `g = n` is impossible. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_alphaWallImpossible68
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
      g = n) :
    False := by
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
  change g = n at hwall
  have hgap :=
    maximalExpandedIntegratedPolynomialLowerSystem_alphaWallResidualGap68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
  change l = 0 ∧
    (Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0) ∧
    d.natDegree < 5 * n - g ∧ ee.natDegree < 6 * n - g ∧
    g < h ∧
    d.natDegree ≤ 5 * n - h ∧ ee.natDegree ≤ 6 * n - h at hgap
  by_cases hh : h < 2 * g
  · by_cases hbal : 2 * h = 3 * g
    · have hdbase : d.natDegree < 5 * n := by omega
      have hebase : ee.natDegree < 6 * n := by omega
      have hz : ¬ (d = 0 ∧ ee = 0) := by
        intro hboth
        have hgaph : h = 6 * n + 1 := by
          simp [h, secondaryResidualGap68, polynomialGap68, hboth.1, hboth.2]
        omega
      have hattained :=
        secondaryResidualGap68_boundary_attained n d ee hdbase hebase hz
      exact
        maximalExpandedIntegratedPolynomialLowerSystem_alphaWallBalancedImpossible68
          l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E h
          hterminal hsys
          (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
          (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, h] using hgap.2.2.2.2.1)
          (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, h] using hh)
          (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using
            hgap.2.2.2.2.2)
          (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, h] using hbal)
          (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using
            hattained)
    · exact
        maximalExpandedIntegratedPolynomialLowerSystem_alphaWallMixedEndgame68
          l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
          hterminal hsys
          (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
          (by
            refine ⟨hgap.2.2.2.2.1, hh, ?_⟩
            exact hbal)
  · have hle : 2 * g ≤ h := Nat.le_of_not_lt hh
    have hd' : d.natDegree ≤ 5 * n - 2 * g := by omega
    have he' : ee.natDegree ≤ 6 * n - 2 * g := by omega
    exact
      maximalExpandedIntegratedPolynomialLowerSystem_alphaWallDoubleImpossible68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d] using
          And.intro hd' he')

#print axioms cubicLoadRowZeroPolynomial68_coeff_tenRadius_of_alphaWall
#print axioms residualRowZero_coeff_rightChamber_of_alphaWall
#print axioms residualRowZero_coeff_balancedChamber_of_alphaWall
#print axioms alphaWallMixedRowZeroRowTwo_beta_eq_zero
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_alphaWallImpossible68

end AlphaWallBalancedRowZero68

end Max11DegreeRoutes
