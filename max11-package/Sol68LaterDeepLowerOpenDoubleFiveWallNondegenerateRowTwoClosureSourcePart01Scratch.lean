import Sol68LaterDeepLowerOpenDoubleFiveWallAlignedTerminalRowTwoClosureSourceScratch

/-! # Row-two closure of the nondegenerate double-five tangent -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerOpenDoubleFiveWallNondegenerateRowTwoClosureSource68

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


set_option maxHeartbeats 30000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option maxHeartbeats 10000000 in
theorem secondaryResidualRowTwoPolynomial68_coeff_sixRadius_of_nondegenerate_fiveWall
    (A B c d e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hwall : 3 * g = 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - 2 * g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (secondaryResidualRowTwoPolynomial68 A B c d e).coeff (6 * n - 1) =
      (8 / 27 : k) * (n : k) *
        (A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 +
          9 * A.coeff (2 * n) * B.coeff (3 * n - g) *
            e.coeff (6 * n - 2 * g) +
          9 * A.coeff (2 * n) * c.coeff (4 * n - g) *
            d.coeff (5 * n - 2 * g) -
          18 * B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2) := by
  have hB3deg : (B ^ 3).natDegree ≤ 9 * n - 3 * g := by
    first
    | with_reducible apply leaf68_lt_of_bd
    | with_reducible apply leaf68_le_of_bd
    repeat'
      first
      | with_reducible exact leaf68_bd_of_le hp
      | with_reducible exact leaf68_bd_of_le hq
      | with_reducible exact leaf68_bd_of_le hA
      | with_reducible exact leaf68_bd_of_le hB
      | with_reducible exact leaf68_bd_of_le hc
      | with_reducible exact leaf68_bd_of_le hd
      | with_reducible exact leaf68_bd_of_le he
      | exact leaf68_bd_of_le (by assumption)
      | with_reducible apply leaf68_bd_smul
      | with_reducible apply leaf68_bd_neg
      | with_reducible apply leaf68_bd_sub
      | with_reducible apply leaf68_bd_add
      | with_reducible apply leaf68_bd_pow
      | with_reducible apply leaf68_bd_deriv
      | with_reducible apply leaf68_bd_mul
      | with_reducible apply leaf68_bd_C
      | omega
  have hc2deg : (c ^ 2).natDegree ≤ 8 * n - 2 * g := by
    first
    | with_reducible apply leaf68_lt_of_bd
    | with_reducible apply leaf68_le_of_bd
    repeat'
      first
      | with_reducible exact leaf68_bd_of_le hp
      | with_reducible exact leaf68_bd_of_le hq
      | with_reducible exact leaf68_bd_of_le hA
      | with_reducible exact leaf68_bd_of_le hB
      | with_reducible exact leaf68_bd_of_le hc
      | with_reducible exact leaf68_bd_of_le hd
      | with_reducible exact leaf68_bd_of_le he
      | exact leaf68_bd_of_le (by assumption)
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
    have hp := coeff_pow_at_bound68 B (3 * n - g) 3 hB
    have hi : 3 * (3 * n - g) = 9 * n - 3 * g := by omega
    simpa only [hi] using hp
  have hc2 : (c ^ 2).coeff (8 * n - 2 * g) =
      c.coeff (4 * n - g) ^ 2 := by
    have hp := coeff_pow_at_bound68 c (4 * n - g) 2 hc
    have hi : 2 * (4 * n - g) = 8 * n - 2 * g := by omega
    simpa only [hi] using hp
  have h1 := coeff_mul_mul_derivative_at_bounds68 A B e
    (2 * n) (3 * n - g) (6 * n - 2 * g) (by omega) hA hB he
  have hi1 : 2 * n + (3 * n - g) + (6 * n - 2 * g) - 1 =
      6 * n - 1 := by omega
  rw [hi1] at h1
  have h2 := coeff_mul_mul_derivative_at_bounds68 A e B
    (2 * n) (6 * n - 2 * g) (3 * n - g) (by omega) hA he hB
  have hi2 : 2 * n + (6 * n - 2 * g) + (3 * n - g) - 1 =
      6 * n - 1 := by omega
  rw [hi2] at h2
  have h2' : (A * derivative B * e).coeff (6 * n - 1) =
      A.coeff (2 * n) * B.coeff (3 * n - g) *
        e.coeff (6 * n - 2 * g) * ((3 * n - g : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h2
  have h3 := coeff_mul_mul_derivative_at_bounds68 A c d
    (2 * n) (4 * n - g) (5 * n - 2 * g) (by omega) hA hc hd
  have hi3 : 2 * n + (4 * n - g) + (5 * n - 2 * g) - 1 =
      6 * n - 1 := by omega
  rw [hi3] at h3
  have h4 := coeff_mul_mul_derivative_at_bounds68 A d c
    (2 * n) (5 * n - 2 * g) (4 * n - g) (by omega) hA hd hc
  have hi4 : 2 * n + (5 * n - 2 * g) + (4 * n - g) - 1 =
      6 * n - 1 := by omega
  rw [hi4] at h4
  have h4' : (A * derivative c * d).coeff (6 * n - 1) =
      A.coeff (2 * n) * c.coeff (4 * n - g) *
        d.coeff (5 * n - 2 * g) * ((4 * n - g : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h4
  have h5 := coeff_mul_derivative_at_bounds68 (B ^ 3) A
    (9 * n - 3 * g) (2 * n) (by omega) hB3deg hA
  have hi5 : (9 * n - 3 * g) + 2 * n - 1 = 6 * n - 1 := by omega
  rw [hi5, hB3] at h5
  have h5' : (derivative A * B ^ 3).coeff (6 * n - 1) =
      A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 *
        ((2 * n : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h5
  have h6 := coeff_mul_mul_derivative_at_bounds68 B e A
    (3 * n - g) (6 * n - 2 * g) (2 * n) (by omega) hB he hA
  have hi6 : (3 * n - g) + (6 * n - 2 * g) + 2 * n - 1 =
      6 * n - 1 := by omega
  rw [hi6] at h6
  have h6' : (derivative A * B * e).coeff (6 * n - 1) =
      A.coeff (2 * n) * B.coeff (3 * n - g) *
        e.coeff (6 * n - 2 * g) * ((2 * n : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h6
  have h7 := coeff_mul_mul_derivative_at_bounds68 c d A
    (4 * n - g) (5 * n - 2 * g) (2 * n) (by omega) hc hd hA
  have hi7 : (4 * n - g) + (5 * n - 2 * g) + 2 * n - 1 =
      6 * n - 1 := by omega
  rw [hi7] at h7
  have h7' : (derivative A * c * d).coeff (6 * n - 1) =
      A.coeff (2 * n) * c.coeff (4 * n - g) *
        d.coeff (5 * n - 2 * g) * ((2 * n : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h7
  have h10 := coeff_mul_mul_derivative_at_bounds68 B c c
    (3 * n - g) (4 * n - g) (4 * n - g) (by omega) hB hc hc
  have hi10 : (3 * n - g) + (4 * n - g) + (4 * n - g) - 1 =
      6 * n - 1 := by omega
  rw [hi10] at h10
  have h11 := coeff_mul_derivative_at_bounds68 (c ^ 2) B
    (8 * n - 2 * g) (3 * n - g) (by omega) hc2deg hB
  have hi11 : (8 * n - 2 * g) + (3 * n - g) - 1 =
      6 * n - 1 := by omega
  rw [hi11, hc2] at h11
  have h11' : (derivative B * c ^ 2).coeff (6 * n - 1) =
      B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 *
        ((3 * n - g : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h11
  have hlow1 : (B ^ 2 * derivative d).natDegree < 6 * n - 1 := by
    first
    | with_reducible apply leaf68_lt_of_bd
    | with_reducible apply leaf68_le_of_bd
    repeat'
      first
      | with_reducible exact leaf68_bd_of_le hp
      | with_reducible exact leaf68_bd_of_le hq
      | with_reducible exact leaf68_bd_of_le hA
      | with_reducible exact leaf68_bd_of_le hB
      | with_reducible exact leaf68_bd_of_le hc
      | with_reducible exact leaf68_bd_of_le hd
      | with_reducible exact leaf68_bd_of_le he
      | exact leaf68_bd_of_le (by assumption)
      | with_reducible apply leaf68_bd_smul
      | with_reducible apply leaf68_bd_neg
      | with_reducible apply leaf68_bd_sub
      | with_reducible apply leaf68_bd_add
      | with_reducible apply leaf68_bd_pow
      | with_reducible apply leaf68_bd_deriv
      | with_reducible apply leaf68_bd_mul
      | with_reducible apply leaf68_bd_C
      | omega
  have hlow2 : (B * derivative B * d).natDegree < 6 * n - 1 := by
    first
    | with_reducible apply leaf68_lt_of_bd
    | with_reducible apply leaf68_le_of_bd
    repeat'
      first
      | with_reducible exact leaf68_bd_of_le hp
      | with_reducible exact leaf68_bd_of_le hq
      | with_reducible exact leaf68_bd_of_le hA
      | with_reducible exact leaf68_bd_of_le hB
      | with_reducible exact leaf68_bd_of_le hc
      | with_reducible exact leaf68_bd_of_le hd
      | with_reducible exact leaf68_bd_of_le he
      | exact leaf68_bd_of_le (by assumption)
      | with_reducible apply leaf68_bd_smul
      | with_reducible apply leaf68_bd_neg
      | with_reducible apply leaf68_bd_sub
      | with_reducible apply leaf68_bd_add
      | with_reducible apply leaf68_bd_pow
      | with_reducible apply leaf68_bd_deriv
      | with_reducible apply leaf68_bd_mul
      | with_reducible apply leaf68_bd_C
      | omega
  have hlow3 : (d * derivative e).natDegree < 6 * n - 1 :=
    leaf68_natDegree_mulDeriv_lt hd he (by omega)
  have hlow4 : (derivative d * e).natDegree < 6 * n - 1 := by
    first
    | with_reducible apply leaf68_lt_of_bd
    | with_reducible apply leaf68_le_of_bd
    repeat'
      first
      | with_reducible exact leaf68_bd_of_le hp
      | with_reducible exact leaf68_bd_of_le hq
      | with_reducible exact leaf68_bd_of_le hA
      | with_reducible exact leaf68_bd_of_le hB
      | with_reducible exact leaf68_bd_of_le hc
      | with_reducible exact leaf68_bd_of_le hd
      | with_reducible exact leaf68_bd_of_le he
      | exact leaf68_bd_of_le (by assumption)
      | with_reducible apply leaf68_bd_smul
      | with_reducible apply leaf68_bd_neg
      | with_reducible apply leaf68_bd_sub
      | with_reducible apply leaf68_bd_add
      | with_reducible apply leaf68_bd_pow
      | with_reducible apply leaf68_bd_deriv
      | with_reducible apply leaf68_bd_mul
      | with_reducible apply leaf68_bd_C
      | omega
  simp only [secondaryResidualRowTwoPolynomial68, coeff_smul, coeff_add,
    coeff_sub, h1, h2', h3, h4', h5', h6', h7', h10, h11',
    coeff_eq_zero_of_natDegree_lt hlow1,
    coeff_eq_zero_of_natDegree_lt hlow2,
    coeff_eq_zero_of_natDegree_lt hlow3,
    coeff_eq_zero_of_natDegree_lt hlow4, smul_eq_mul]
  have hcast2 : (((2 * n : ℕ) : k)) = 2 * (n : k) := by push_cast; rfl
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
  rw [hcast2, hcast3, hcast4, hcast5, hcast6]
  have hw : (3 : k) * (g : k) = 5 * (n : k) := by exact_mod_cast hwall
  linear_combination
    (-8 / 9 : k) *
      (A.coeff (2 * n) * B.coeff (3 * n - g) *
          e.coeff (6 * n - 2 * g) +
        A.coeff (2 * n) * c.coeff (4 * n - g) *
          d.coeff (5 * n - 2 * g) -
        B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2) * hw

end LaterDeepLowerOpenDoubleFiveWallNondegenerateRowTwoClosureSource68
end Max11DegreeRoutes
