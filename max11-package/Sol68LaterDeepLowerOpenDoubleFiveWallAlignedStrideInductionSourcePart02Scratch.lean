import Sol68LaterDeepLowerOpenDoubleFiveWallAlignedStrideInductionSourcePart01Scratch

/-! # Uniform aligned-stride induction on the degenerate double-five wall -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerOpenDoubleFiveWallAlignedStrideInductionSource68

variable {k : Type*} [Field k] [CharZero k]

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
theorem secondaryResidualRowOnePolynomial68_coeff_aligned_offset_of_fiveWall
    (A B c d e : k[X]) (n g s : ℕ)
    (hn : 0 < n) (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hwall : 3 * g = 5 * n) (hspos : 0 < s)
    (hs : s < 5 * n - 2 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g - s)
    (hd : d.natDegree ≤ 5 * n - 2 * g - s)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (secondaryResidualRowOnePolynomial68 A B c d e).coeff
        (12 * n - 3 * g - s - 1) =
      (-4 / 27 : k) *
        (2 * A.coeff (2 * n) ^ 2 * B.coeff (3 * n - g) *
            d.coeff (5 * n - 2 * g - s) * ((5 * n - s : ℕ) : k) -
          6 * A.coeff (2 * n) * c.coeff (4 * n - g - s) *
            e.coeff (6 * n - 2 * g) * ((5 * n - s : ℕ) : k) -
          4 * (n : k) * A.coeff (2 * n) *
            B.coeff (3 * n - g) ^ 2 * c.coeff (4 * n - g - s)) := by
  have hA2deg : (A ^ 2).natDegree ≤ 4 * n := by compute_degree; omega
  have hB2deg : (B ^ 2).natDegree ≤ 6 * n - 2 * g := by
    compute_degree
    omega
  have hA2 : (A ^ 2).coeff (4 * n) = A.coeff (2 * n) ^ 2 := by
    have hp := coeff_pow_at_bound68 A (2 * n) 2 hA
    have hi : 2 * (2 * n) = 4 * n := by omega
    simpa only [hi] using hp
  have hB2 : (B ^ 2).coeff (6 * n - 2 * g) =
      B.coeff (3 * n - g) ^ 2 := by
    have hp := coeff_pow_at_bound68 B (3 * n - g) 2 hB
    have hi : 2 * (3 * n - g) = 6 * n - 2 * g := by omega
    simpa only [hi] using hp
  have h1 := coeff_mul_mul_derivative_at_bounds68 (A ^ 2) B d
    (4 * n) (3 * n - g) (5 * n - 2 * g - s) (by omega)
    hA2deg hB hd
  have hi1 : 4 * n + (3 * n - g) + (5 * n - 2 * g - s) - 1 =
      12 * n - 3 * g - s - 1 := by omega
  rw [hi1, hA2] at h1
  have h2 := coeff_mul_mul_derivative_at_bounds68 (A ^ 2) d B
    (4 * n) (5 * n - 2 * g - s) (3 * n - g) (by omega)
    hA2deg hd hB
  have hi2 : 4 * n + (5 * n - 2 * g - s) + (3 * n - g) - 1 =
      12 * n - 3 * g - s - 1 := by omega
  rw [hi2, hA2] at h2
  have h2' : (A ^ 2 * derivative B * d).coeff
      (12 * n - 3 * g - s - 1) =
      A.coeff (2 * n) ^ 2 * B.coeff (3 * n - g) *
        d.coeff (5 * n - 2 * g - s) * ((3 * n - g : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h2
  have h3 := coeff_mul_mul_mul_derivative_at_bounds68 A B d A
    (2 * n) (3 * n - g) (5 * n - 2 * g - s) (2 * n)
    (by omega) hA hB hd hA
  have hi3 : 2 * n + (3 * n - g) + (5 * n - 2 * g - s) +
      2 * n - 1 = 12 * n - 3 * g - s - 1 := by omega
  rw [hi3] at h3
  have h3' : (A * derivative A * B * d).coeff
      (12 * n - 3 * g - s - 1) =
      A.coeff (2 * n) * A.coeff (2 * n) * B.coeff (3 * n - g) *
        d.coeff (5 * n - 2 * g - s) * ((2 * n : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h3
  have h4 := coeff_mul_mul_derivative_at_bounds68 A c e
    (2 * n) (4 * n - g - s) (6 * n - 2 * g) (by omega)
    hA hc he
  have hi4 : 2 * n + (4 * n - g - s) + (6 * n - 2 * g) - 1 =
      12 * n - 3 * g - s - 1 := by omega
  rw [hi4] at h4
  have h5 := coeff_mul_mul_derivative_at_bounds68 A e c
    (2 * n) (6 * n - 2 * g) (4 * n - g - s) (by omega)
    hA he hc
  have hi5 : 2 * n + (6 * n - 2 * g) + (4 * n - g - s) - 1 =
      12 * n - 3 * g - s - 1 := by omega
  rw [hi5] at h5
  have h5' : (A * derivative c * e).coeff
      (12 * n - 3 * g - s - 1) =
      A.coeff (2 * n) * c.coeff (4 * n - g - s) *
        e.coeff (6 * n - 2 * g) * ((4 * n - g - s : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h5
  have h6 := coeff_mul_mul_derivative_at_bounds68 (B ^ 2) c A
    (6 * n - 2 * g) (4 * n - g - s) (2 * n) (by omega)
    hB2deg hc hA
  have hi6 : (6 * n - 2 * g) + (4 * n - g - s) + 2 * n - 1 =
      12 * n - 3 * g - s - 1 := by omega
  rw [hi6, hB2] at h6
  have h6' : (derivative A * B ^ 2 * c).coeff
      (12 * n - 3 * g - s - 1) =
      A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 *
        c.coeff (4 * n - g - s) * ((2 * n : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h6
  have hlowA : (derivative A * d ^ 2).natDegree <
      12 * n - 3 * g - s - 1 := by compute_degree; omega
  have hlowB : (B ^ 2 * derivative e).natDegree <
      12 * n - 3 * g - s - 1 := by compute_degree; omega
  have hlowC : (B * c * derivative d).natDegree <
      12 * n - 3 * g - s - 1 := by compute_degree; omega
  have hlowD : (B * derivative c * d).natDegree <
      12 * n - 3 * g - s - 1 := by compute_degree; omega
  have hlowE : (derivative B * c * d).natDegree <
      12 * n - 3 * g - s - 1 := by compute_degree; omega
  have hlowF : (c ^ 2 * derivative c).natDegree <
      12 * n - 3 * g - s - 1 := by compute_degree; omega
  have hlowG : (e * derivative e).natDegree <
      12 * n - 3 * g - s - 1 :=
    leaf68_natDegree_mulDeriv_lt he he (by omega)
  have hcast3 : (((3 * n - g : ℕ) : k)) = 3 * (n : k) - (g : k) := by
    rw [Nat.cast_sub (by omega : g ≤ 3 * n)]
    push_cast
    rfl
  have hcast2 : (((2 * n : ℕ) : k)) = 2 * (n : k) := by
    push_cast
    rfl
  have hcast4 : (((4 * n - g - s : ℕ) : k)) =
      4 * (n : k) - (g : k) - (s : k) := by
    rw [Nat.cast_sub (by omega : s ≤ 4 * n - g),
      Nat.cast_sub (by omega : g ≤ 4 * n)]
    push_cast
    rfl
  have hcast5 : (((5 * n - 2 * g - s : ℕ) : k)) =
      5 * (n : k) - 2 * (g : k) - (s : k) := by
    rw [Nat.cast_sub (by omega : s ≤ 5 * n - 2 * g),
      Nat.cast_sub (by omega : 2 * g ≤ 5 * n)]
    push_cast
    rfl
  have hcast6 : (((6 * n - 2 * g : ℕ) : k)) =
      6 * (n : k) - 2 * (g : k) := by
    rw [Nat.cast_sub (by omega : 2 * g ≤ 6 * n)]
    push_cast
    rfl
  have hcastM : (((5 * n - s : ℕ) : k)) = 5 * (n : k) - (s : k) := by
    rw [Nat.cast_sub (by omega : s ≤ 5 * n)]
    push_cast
    rfl
  simp only [secondaryResidualRowOnePolynomial68, coeff_smul, coeff_add,
    coeff_sub, h1, h2', h3', h4, h5', h6',
    coeff_eq_zero_of_natDegree_lt hlowA,
    coeff_eq_zero_of_natDegree_lt hlowB,
    coeff_eq_zero_of_natDegree_lt hlowC,
    coeff_eq_zero_of_natDegree_lt hlowD,
    coeff_eq_zero_of_natDegree_lt hlowE,
    coeff_eq_zero_of_natDegree_lt hlowF,
    coeff_eq_zero_of_natDegree_lt hlowG, smul_eq_mul]
  rw [hcast2, hcast3, hcast4, hcast5, hcast6, hcastM]
  have hw : (3 : k) * (g : k) = 5 * (n : k) := by exact_mod_cast hwall
  have hgcast : (g : k) = (5 / 3 : k) * (n : k) := by
    linear_combination (1 / 3 : k) * hw
  rw [hgcast]
  ring

end LaterDeepLowerOpenDoubleFiveWallAlignedStrideInductionSource68
end Max11DegreeRoutes
