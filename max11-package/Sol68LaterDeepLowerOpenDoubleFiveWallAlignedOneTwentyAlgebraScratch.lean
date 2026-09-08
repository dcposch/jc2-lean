import Sol68LaterDeepLowerOpenDoubleFiveWallAlignedOneTwentySourceScratch

/-! # Residual coefficient algebra at aligned offset 120 -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerOpenDoubleFiveWallAlignedOneTwentyAlgebra68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 30000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option maxHeartbeats 4000000 in
theorem secondaryResidualInvariantThreePolynomial68_coeff_double_drop_oneTwenty_of_fiveWall
    (A B c d e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 120 < g) (hwall : 3 * g = 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g - 120)
    (hd : d.natDegree ≤ 5 * n - 2 * g - 120)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (secondaryResidualInvariantThreePolynomial68 A B c d e).coeff
        (10 * n - 3 * g - 120) =
      (8 / 9 : k) *
        (-(A.coeff (2 * n) * B.coeff (3 * n - g) *
            d.coeff (5 * n - 2 * g - 120)) -
          B.coeff (3 * n - g) ^ 2 * c.coeff (4 * n - g - 120) +
          3 * c.coeff (4 * n - g - 120) *
            e.coeff (6 * n - 2 * g)) := by
  have hABd := coeff_mul_mul_at_bounds68 A B d (2 * n)
    (3 * n - g) (5 * n - 2 * g - 120) hA hB hd
  have hABdi : 2 * n + (3 * n - g) + (5 * n - 2 * g - 120) =
      10 * n - 3 * g - 120 := by omega
  rw [hABdi] at hABd
  have hBBc := coeff_mul_mul_at_bounds68 B B c (3 * n - g)
    (3 * n - g) (4 * n - g - 120) hB hB hc
  have hBBci : (3 * n - g) + (3 * n - g) + (4 * n - g - 120) =
      10 * n - 3 * g - 120 := by omega
  rw [hBBci] at hBBc
  have hB2c : (B ^ 2 * c).coeff (10 * n - 3 * g - 120) =
      B.coeff (3 * n - g) ^ 2 * c.coeff (4 * n - g - 120) := by
    simpa only [pow_two] using hBBc
  have hce := coeff_mul_at_bounds68 c e (4 * n - g - 120)
    (6 * n - 2 * g) hc he
  have hcei : (4 * n - g - 120) + (6 * n - 2 * g) =
      10 * n - 3 * g - 120 := by omega
  rw [hcei] at hce
  have hd2 : (d ^ 2).natDegree < 10 * n - 3 * g - 120 := by
    compute_degree
    omega
  simp only [secondaryResidualInvariantThreePolynomial68, coeff_add,
    coeff_sub, coeff_smul, smul_eq_mul, hABd, hB2c, hce,
    coeff_eq_zero_of_natDegree_lt hd2]
  ring

set_option maxHeartbeats 10000000 in
theorem secondaryResidualRowOnePolynomial68_coeff_double_drop_oneTwenty_of_fiveWall
    (A B c d e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 120 < g) (hwall : 3 * g = 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g - 120)
    (hd : d.natDegree ≤ 5 * n - 2 * g - 120)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (secondaryResidualRowOnePolynomial68 A B c d e).coeff
        (12 * n - 3 * g - 121) =
      (-4 / 27 : k) *
        (2 * A.coeff (2 * n) ^ 2 * B.coeff (3 * n - g) *
            d.coeff (5 * n - 2 * g - 120) * ((5 * n - 120 : ℕ) : k) -
          6 * A.coeff (2 * n) * c.coeff (4 * n - g - 120) *
            e.coeff (6 * n - 2 * g) * ((5 * n - 120 : ℕ) : k) -
          4 * (n : k) * A.coeff (2 * n) *
            B.coeff (3 * n - g) ^ 2 * c.coeff (4 * n - g - 120)) := by
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
    (4 * n) (3 * n - g) (5 * n - 2 * g - 120) (by omega)
    hA2deg hB hd
  have hi1 : 4 * n + (3 * n - g) + (5 * n - 2 * g - 120) - 1 =
      12 * n - 3 * g - 121 := by omega
  rw [hi1, hA2] at h1
  have h2 := coeff_mul_mul_derivative_at_bounds68 (A ^ 2) d B
    (4 * n) (5 * n - 2 * g - 120) (3 * n - g) (by omega)
    hA2deg hd hB
  have hi2 : 4 * n + (5 * n - 2 * g - 120) + (3 * n - g) - 1 =
      12 * n - 3 * g - 121 := by omega
  rw [hi2, hA2] at h2
  have h2' : (A ^ 2 * derivative B * d).coeff
      (12 * n - 3 * g - 121) =
      A.coeff (2 * n) ^ 2 * B.coeff (3 * n - g) *
        d.coeff (5 * n - 2 * g - 120) * ((3 * n - g : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h2
  have h3 := coeff_mul_mul_mul_derivative_at_bounds68 A B d A
    (2 * n) (3 * n - g) (5 * n - 2 * g - 120) (2 * n)
    (by omega) hA hB hd hA
  have hi3 : 2 * n + (3 * n - g) + (5 * n - 2 * g - 120) +
      2 * n - 1 = 12 * n - 3 * g - 121 := by omega
  rw [hi3] at h3
  have h3' : (A * derivative A * B * d).coeff
      (12 * n - 3 * g - 121) =
      A.coeff (2 * n) * A.coeff (2 * n) * B.coeff (3 * n - g) *
        d.coeff (5 * n - 2 * g - 120) * ((2 * n : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h3
  have h4 := coeff_mul_mul_derivative_at_bounds68 A c e
    (2 * n) (4 * n - g - 120) (6 * n - 2 * g) (by omega)
    hA hc he
  have hi4 : 2 * n + (4 * n - g - 120) + (6 * n - 2 * g) - 1 =
      12 * n - 3 * g - 121 := by omega
  rw [hi4] at h4
  have h5 := coeff_mul_mul_derivative_at_bounds68 A e c
    (2 * n) (6 * n - 2 * g) (4 * n - g - 120) (by omega)
    hA he hc
  have hi5 : 2 * n + (6 * n - 2 * g) + (4 * n - g - 120) - 1 =
      12 * n - 3 * g - 121 := by omega
  rw [hi5] at h5
  have h5' : (A * derivative c * e).coeff
      (12 * n - 3 * g - 121) =
      A.coeff (2 * n) * c.coeff (4 * n - g - 120) *
        e.coeff (6 * n - 2 * g) * ((4 * n - g - 120 : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h5
  have h6 := coeff_mul_mul_derivative_at_bounds68 (B ^ 2) c A
    (6 * n - 2 * g) (4 * n - g - 120) (2 * n) (by omega)
    hB2deg hc hA
  have hi6 : (6 * n - 2 * g) + (4 * n - g - 120) + 2 * n - 1 =
      12 * n - 3 * g - 121 := by omega
  rw [hi6, hB2] at h6
  have h6' : (derivative A * B ^ 2 * c).coeff
      (12 * n - 3 * g - 121) =
      A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 *
        c.coeff (4 * n - g - 120) * ((2 * n : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h6
  have hlowA : (derivative A * d ^ 2).natDegree <
      12 * n - 3 * g - 121 := by compute_degree; omega
  have hlowB : (B ^ 2 * derivative e).natDegree <
      12 * n - 3 * g - 121 := by compute_degree; omega
  have hlowC : (B * c * derivative d).natDegree <
      12 * n - 3 * g - 121 := by compute_degree; omega
  have hlowD : (B * derivative c * d).natDegree <
      12 * n - 3 * g - 121 := by compute_degree; omega
  have hlowE : (derivative B * c * d).natDegree <
      12 * n - 3 * g - 121 := by compute_degree; omega
  have hlowF : (c ^ 2 * derivative c).natDegree <
      12 * n - 3 * g - 121 := by compute_degree; omega
  have hlowG : (e * derivative e).natDegree <
      12 * n - 3 * g - 121 := by compute_degree; omega
  have hcast3 : (((3 * n - g : ℕ) : k)) = 3 * (n : k) - (g : k) := by
    rw [Nat.cast_sub (by omega : g ≤ 3 * n)]
    push_cast
    rfl
  have hcast2 : (((2 * n : ℕ) : k)) = 2 * (n : k) := by
    push_cast
    rfl
  have hcast4 : (((4 * n - g - 120 : ℕ) : k)) =
      4 * (n : k) - (g : k) - 120 := by
    rw [Nat.cast_sub (by omega : 120 ≤ 4 * n - g),
      Nat.cast_sub (by omega : g ≤ 4 * n)]
    push_cast
    rfl
  have hcast5 : (((5 * n - 2 * g - 120 : ℕ) : k)) =
      5 * (n : k) - 2 * (g : k) - 120 := by
    rw [Nat.cast_sub (by omega : 120 ≤ 5 * n - 2 * g),
      Nat.cast_sub (by omega : 2 * g ≤ 5 * n)]
    push_cast
    rfl
  have hcast6 : (((6 * n - 2 * g : ℕ) : k)) =
      6 * (n : k) - 2 * (g : k) := by
    rw [Nat.cast_sub (by omega : 2 * g ≤ 6 * n)]
    push_cast
    rfl
  have hcastM : (((5 * n - 120 : ℕ) : k)) = 5 * (n : k) - 120 := by
    rw [Nat.cast_sub (by omega : 120 ≤ 5 * n)]
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

/-- In the aligned degenerate branch the first-stride I3 and row-one
equations force both new residual edge coefficients to vanish. -/
theorem laterDeepLowerOpenDoubleFiveWall_degenerate_offsetOneTwenty_edges_zero68
    (n : ℕ) (a b c₁ d₁ e : k) (hn : 0 < n) (ha : a ≠ 0) (hb : b ≠ 0)
    (hi3 : -a * b * d₁ - b ^ 2 * c₁ + 3 * c₁ * e = 0)
    (hrow :
      2 * a ^ 2 * b * d₁ * (5 * (n : k) - 120) -
        6 * a * c₁ * e * (5 * (n : k) - 120) -
        4 * (n : k) * a * b ^ 2 * c₁ = 0) : c₁ = 0 ∧ d₁ = 0 := by
  have hN : 7 * (n : k) - 120 ≠ 0 := by
    intro hz
    have hnat : 7 * n = 120 := by exact_mod_cast (sub_eq_zero.mp hz)
    omega
  have hcprod : a * b ^ 2 * c₁ * (7 * (n : k) - 120) = 0 := by
    linear_combination (-1 / 2 : k) * hrow -
      a * (5 * (n : k) - 120) * hi3
  have hc : c₁ = 0 := by
    rcases mul_eq_zero.mp hcprod with habc | hfac
    · rcases mul_eq_zero.mp habc with hab | hc
      · exact False.elim ((mul_ne_zero ha (pow_ne_zero 2 hb)) hab)
      · exact hc
    · exact False.elim (hN hfac)
  have hdprod : a * b * d₁ = 0 := by
    rw [hc] at hi3
    linear_combination -hi3
  have hd : d₁ = 0 :=
    (mul_eq_zero.mp hdprod).resolve_left (mul_ne_zero ha hb)
  exact ⟨hc, hd⟩

#print axioms secondaryResidualInvariantThreePolynomial68_coeff_double_drop_oneTwenty_of_fiveWall
#print axioms secondaryResidualRowOnePolynomial68_coeff_double_drop_oneTwenty_of_fiveWall
#print axioms laterDeepLowerOpenDoubleFiveWall_degenerate_offsetOneTwenty_edges_zero68

end LaterDeepLowerOpenDoubleFiveWallAlignedOneTwentyAlgebra68

end Max11DegreeRoutes

