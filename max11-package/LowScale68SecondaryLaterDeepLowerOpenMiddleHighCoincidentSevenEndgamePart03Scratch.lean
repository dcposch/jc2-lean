import LowScale68SecondaryLaterDeepLowerOpenMiddleHighCoincidentSevenEndgamePart02Scratch

/-! # Closure for the coincident seven wall `2h=3g=7n` -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerOpenMiddleHighCoincidentSevenEndgame68

variable {k : Type*} [Field k] [CharZero k]

private structure Leaf68Bound (p : k[X]) (u : ℕ) : Prop where
  le : p.natDegree ≤ u

private theorem leaf68_bd_of_le {p : k[X]} {u : ℕ} (h : p.natDegree ≤ u) :
    Leaf68Bound p u := ⟨h⟩

private theorem leaf68_bd_C (a : k) : Leaf68Bound (C a) 0 :=
  ⟨(natDegree_C a).le⟩

private theorem leaf68_bd_smul (r : k) {p : k[X]} {u : ℕ}
    (hp : Leaf68Bound p u) : Leaf68Bound (r • p) u :=
  ⟨(natDegree_smul_le r p).trans hp.le⟩

private theorem leaf68_bd_neg {p : k[X]} {u : ℕ}
    (hp : Leaf68Bound p u) : Leaf68Bound (-p) u :=
  ⟨(natDegree_neg p).le.trans hp.le⟩

private theorem leaf68_bd_add {p q : k[X]} {u v : ℕ}
    (hp : Leaf68Bound p u) (hq : Leaf68Bound q v) :
    Leaf68Bound (p + q) (max u v) :=
  ⟨(natDegree_add_le p q).trans (max_le_max hp.le hq.le)⟩

private theorem leaf68_bd_sub {p q : k[X]} {u v : ℕ}
    (hp : Leaf68Bound p u) (hq : Leaf68Bound q v) :
    Leaf68Bound (p - q) (max u v) :=
  ⟨(natDegree_sub_le p q).trans (max_le_max hp.le hq.le)⟩

private theorem leaf68_bd_mul {p q : k[X]} {u v : ℕ}
    (hp : Leaf68Bound p u) (hq : Leaf68Bound q v) :
    Leaf68Bound (p * q) (u + v) :=
  ⟨natDegree_mul_le.trans (Nat.add_le_add hp.le hq.le)⟩

private theorem leaf68_bd_pow {p : k[X]} {u : ℕ} (m : ℕ)
    (hp : Leaf68Bound p u) : Leaf68Bound (p ^ m) (m * u) :=
  ⟨natDegree_pow_le.trans (Nat.mul_le_mul (le_refl m) hp.le)⟩

private theorem leaf68_bd_deriv {p : k[X]} {u : ℕ}
    (hp : Leaf68Bound p u) : Leaf68Bound (derivative p) (u - 1) :=
  ⟨(natDegree_derivative_le p).trans (Nat.sub_le_sub_right hp.le 1)⟩

private theorem leaf68_lt_of_bd {p : k[X]} {u b : ℕ}
    (hp : Leaf68Bound p u) (h : u < b) : p.natDegree < b :=
  lt_of_le_of_lt hp.le h

private theorem leaf68_le_of_bd {p : k[X]} {u b : ℕ}
    (hp : Leaf68Bound p u) (h : u ≤ b) : p.natDegree ≤ b :=
  hp.le.trans h


set_option maxHeartbeats 24000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## The quartic incidence defect on the coincident wall -/

/-! ## Row zero at `6n-1` -/

set_option maxHeartbeats 12000000 in
theorem secondaryResidualRowZeroPolynomial68_coeff_coincidentSeven
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hwallH : 2 * h = 7 * n) (hwallG : 3 * g = 7 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualIncidenceQ68 B c d e).natDegree ≤ 2 * n) :
    (secondaryResidualRowZeroPolynomial68 A B c d e).coeff (6 * n - 1) =
      (4 / 27 : k) * ((2 : k) * (n : k) * A.coeff (2 * n) *
        (-(A.coeff (2 * n) *
            (residualIncidenceQ68 B c d e).coeff (2 * n)) -
          A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 / 9 +
          B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 -
          (3 : k) * d.coeff (5 * n - h) * e.coeff (6 * n - h))) := by
  let Q := residualIncidenceQ68 B c d e
  let idx := 6 * n - 1
  change (secondaryResidualRowZeroPolynomial68 A B c d e).coeff idx =
    (4 / 27 : k) * ((2 : k) * (n : k) * A.coeff (2 * n) *
      (-(A.coeff (2 * n) * Q.coeff (2 * n)) -
        A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 / 9 +
        B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 -
        (3 : k) * d.coeff (5 * n - h) * e.coeff (6 * n - h)))
  have hAQ := coeff_mul_mul_derivative_at_bounds68 A Q A
    (2 * n) (2 * n) (2 * n) (by omega) hA hQ hA
  have hiAQ : 2 * n + 2 * n + 2 * n - 1 = idx := by
    dsimp [idx]
    omega
  rw [hiAQ] at hAQ
  have hAQ' : (A * derivative A * Q).coeff idx =
      A.coeff (2 * n) ^ 2 * Q.coeff (2 * n) * ((2 * n : ℕ) : k) := by
    rw [show (A * derivative A * Q).coeff idx =
        (A * Q * derivative A).coeff idx by
      congr 1
      ring]
    simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using hAQ
  have hB3deg : (B ^ 3).natDegree ≤ 9 * n - 3 * g := by
    apply leaf68_le_of_bd
    repeat'
      first
      | with_reducible exact leaf68_bd_of_le hA
      | with_reducible exact leaf68_bd_of_le hB
      | with_reducible exact leaf68_bd_of_le hc
      | with_reducible exact leaf68_bd_of_le hd
      | with_reducible exact leaf68_bd_of_le he
      | with_reducible apply leaf68_bd_smul
      | with_reducible apply leaf68_bd_neg
      | with_reducible apply leaf68_bd_sub
      | with_reducible apply leaf68_bd_add
      | with_reducible apply leaf68_bd_pow
      | with_reducible apply leaf68_bd_deriv
      | with_reducible apply leaf68_bd_mul
      | with_reducible apply leaf68_bd_C
      | omega
  have hB3 : (B ^ 3).coeff (9 * n - 3 * g) =
      B.coeff (3 * n - g) ^ 3 := by
    have ht := coeff_pow_at_bound68 B (3 * n - g) 3 hB
    have hi : 3 * (3 * n - g) = 9 * n - 3 * g := by omega
    simpa only [hi] using ht
  have hAB3 := coeff_mul_mul_derivative_at_bounds68 A (B ^ 3) A
    (2 * n) (9 * n - 3 * g) (2 * n) (by omega) hA hB3deg hA
  have hiAB3 : 2 * n + (9 * n - 3 * g) + 2 * n - 1 = idx := by
    dsimp [idx]
    omega
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
    apply leaf68_le_of_bd
    repeat'
      first
      | with_reducible exact leaf68_bd_of_le hA
      | with_reducible exact leaf68_bd_of_le hB
      | with_reducible exact leaf68_bd_of_le hc
      | with_reducible exact leaf68_bd_of_le hd
      | with_reducible exact leaf68_bd_of_le he
      | with_reducible apply leaf68_bd_smul
      | with_reducible apply leaf68_bd_neg
      | with_reducible apply leaf68_bd_sub
      | with_reducible apply leaf68_bd_add
      | with_reducible apply leaf68_bd_pow
      | with_reducible apply leaf68_bd_deriv
      | with_reducible apply leaf68_bd_mul
      | with_reducible apply leaf68_bd_C
      | omega
  have hc2 : (c ^ 2).coeff (8 * n - 2 * g) =
      c.coeff (4 * n - g) ^ 2 := by
    have ht := coeff_pow_at_bound68 c (4 * n - g) 2 hc
    have hi : 2 * (4 * n - g) = 8 * n - 2 * g := by omega
    simpa only [hi] using ht
  have hBc2 := coeff_mul_mul_derivative_at_bounds68 B (c ^ 2) A
    (3 * n - g) (8 * n - 2 * g) (2 * n) (by omega) hB hc2deg hA
  have hiBc2 : (3 * n - g) + (8 * n - 2 * g) + 2 * n - 1 = idx := by
    dsimp [idx]
    omega
  rw [hiBc2, hc2] at hBc2
  have hBc2' : (derivative A * B * c ^ 2).coeff idx =
      A.coeff (2 * n) * B.coeff (3 * n - g) *
        c.coeff (4 * n - g) ^ 2 * ((2 * n : ℕ) : k) := by
    rw [show (derivative A * B * c ^ 2).coeff idx =
        (B * c ^ 2 * derivative A).coeff idx by
      congr 1
      ring]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hBc2
  have hAde := coeff_mul_mul_derivative_at_bounds68 d e A
    (5 * n - h) (6 * n - h) (2 * n) (by omega) hd he hA
  have hiAde : (5 * n - h) + (6 * n - h) + 2 * n - 1 = idx := by
    dsimp [idx]
    omega
  rw [hiAde] at hAde
  have hAde' : (derivative A * d * e).coeff idx =
      A.coeff (2 * n) * d.coeff (5 * n - h) * e.coeff (6 * n - h) *
        ((2 * n : ℕ) : k) := by
    rw [show (derivative A * d * e).coeff idx =
        (d * e * derivative A).coeff idx by
      congr 1
      ring]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hAde
  have h0d : (A * B ^ 2 * derivative d).natDegree < idx := by
    dsimp [idx]
    apply leaf68_lt_of_bd
    repeat'
      first
      | with_reducible exact leaf68_bd_of_le hA
      | with_reducible exact leaf68_bd_of_le hB
      | with_reducible exact leaf68_bd_of_le hc
      | with_reducible exact leaf68_bd_of_le hd
      | with_reducible exact leaf68_bd_of_le he
      | with_reducible apply leaf68_bd_smul
      | with_reducible apply leaf68_bd_neg
      | with_reducible apply leaf68_bd_sub
      | with_reducible apply leaf68_bd_add
      | with_reducible apply leaf68_bd_pow
      | with_reducible apply leaf68_bd_deriv
      | with_reducible apply leaf68_bd_mul
      | with_reducible apply leaf68_bd_C
      | omega
  have h0Bd : (A * B * derivative B * d).natDegree < idx := by
    dsimp [idx]
    apply leaf68_lt_of_bd
    repeat'
      first
      | with_reducible exact leaf68_bd_of_le hA
      | with_reducible exact leaf68_bd_of_le hB
      | with_reducible exact leaf68_bd_of_le hc
      | with_reducible exact leaf68_bd_of_le hd
      | with_reducible exact leaf68_bd_of_le he
      | with_reducible apply leaf68_bd_smul
      | with_reducible apply leaf68_bd_neg
      | with_reducible apply leaf68_bd_sub
      | with_reducible apply leaf68_bd_add
      | with_reducible apply leaf68_bd_pow
      | with_reducible apply leaf68_bd_deriv
      | with_reducible apply leaf68_bd_mul
      | with_reducible apply leaf68_bd_C
      | omega
  have h0Be : (B * c * derivative e).natDegree < idx := by
    dsimp [idx]
    apply leaf68_lt_of_bd
    repeat'
      first
      | with_reducible exact leaf68_bd_of_le hA
      | with_reducible exact leaf68_bd_of_le hB
      | with_reducible exact leaf68_bd_of_le hc
      | with_reducible exact leaf68_bd_of_le hd
      | with_reducible exact leaf68_bd_of_le he
      | with_reducible apply leaf68_bd_smul
      | with_reducible apply leaf68_bd_neg
      | with_reducible apply leaf68_bd_sub
      | with_reducible apply leaf68_bd_add
      | with_reducible apply leaf68_bd_pow
      | with_reducible apply leaf68_bd_deriv
      | with_reducible apply leaf68_bd_mul
      | with_reducible apply leaf68_bd_C
      | omega
  have h0dd : (B * d * derivative d).natDegree < idx := by
    dsimp [idx]
    apply leaf68_lt_of_bd
    repeat'
      first
      | with_reducible exact leaf68_bd_of_le hA
      | with_reducible exact leaf68_bd_of_le hB
      | with_reducible exact leaf68_bd_of_le hc
      | with_reducible exact leaf68_bd_of_le hd
      | with_reducible exact leaf68_bd_of_le he
      | with_reducible apply leaf68_bd_smul
      | with_reducible apply leaf68_bd_neg
      | with_reducible apply leaf68_bd_sub
      | with_reducible apply leaf68_bd_add
      | with_reducible apply leaf68_bd_pow
      | with_reducible apply leaf68_bd_deriv
      | with_reducible apply leaf68_bd_mul
      | with_reducible apply leaf68_bd_C
      | omega
  have h0Bd2 : (derivative B * d ^ 2).natDegree < idx := by
    dsimp [idx]
    apply leaf68_lt_of_bd
    repeat'
      first
      | with_reducible exact leaf68_bd_of_le hA
      | with_reducible exact leaf68_bd_of_le hB
      | with_reducible exact leaf68_bd_of_le hc
      | with_reducible exact leaf68_bd_of_le hd
      | with_reducible exact leaf68_bd_of_le he
      | with_reducible apply leaf68_bd_smul
      | with_reducible apply leaf68_bd_neg
      | with_reducible apply leaf68_bd_sub
      | with_reducible apply leaf68_bd_add
      | with_reducible apply leaf68_bd_pow
      | with_reducible apply leaf68_bd_deriv
      | with_reducible apply leaf68_bd_mul
      | with_reducible apply leaf68_bd_C
      | omega
  have h0cc : (c * derivative c * d).natDegree < idx := by
    dsimp [idx]
    apply leaf68_lt_of_bd
    repeat'
      first
      | with_reducible exact leaf68_bd_of_le hA
      | with_reducible exact leaf68_bd_of_le hB
      | with_reducible exact leaf68_bd_of_le hc
      | with_reducible exact leaf68_bd_of_le hd
      | with_reducible exact leaf68_bd_of_le he
      | with_reducible apply leaf68_bd_smul
      | with_reducible apply leaf68_bd_neg
      | with_reducible apply leaf68_bd_sub
      | with_reducible apply leaf68_bd_add
      | with_reducible apply leaf68_bd_pow
      | with_reducible apply leaf68_bd_deriv
      | with_reducible apply leaf68_bd_mul
      | with_reducible apply leaf68_bd_C
      | omega
  have hBe_cd := residualRowZero_Be_cd_eq_Q A B c d e
  have hBe :
      (A * derivative A * B * e + A * derivative A * c * d).coeff idx =
        (A * derivative A * Q).coeff idx +
          ((1 / 9 : k) • (A * derivative A * B ^ 3)).coeff idx := by
    have ht := congrArg (fun p : k[X] => p.coeff idx) hBe_cd
    simpa only [Q, coeff_add, coeff_smul] using ht
  have hcast2 : ((2 * n : ℕ) : k) = (2 : k) * (n : k) := by
    push_cast
    rfl
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
          (-(A.coeff (2 * n) * Q.coeff (2 * n)) -
            A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 / 9 +
            B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 -
            (3 : k) * d.coeff (5 * n - h) * e.coeff (6 * n - h)) := by
    simp only [coeff_smul, smul_eq_mul, coeff_add, coeff_sub,
      coeff_eq_zero_of_natDegree_lt h0d,
      coeff_eq_zero_of_natDegree_lt h0Bd,
      coeff_eq_zero_of_natDegree_lt h0Be,
      coeff_eq_zero_of_natDegree_lt h0dd,
      coeff_eq_zero_of_natDegree_lt h0Bd2,
      coeff_eq_zero_of_natDegree_lt h0cc, mul_zero]
    have hsum :
        -1 * (A * derivative A * B * e).coeff idx -
            (A * derivative A * c * d).coeff idx =
          -((A * derivative A * B * e +
            A * derivative A * c * d).coeff idx) := by
      rw [coeff_add]
      ring
    rw [hsum, hBe, coeff_smul, smul_eq_mul, hAQ', hAB3', hBc2', hAde',
      hcast2]
    ring
  rw [secondaryResidualRowZeroPolynomial68, coeff_smul, smul_eq_mul, hinner]

end LaterDeepLowerOpenMiddleHighCoincidentSevenEndgame68
end Max11DegreeRoutes
