import Sol68LaterDeepLowerOpenDoubleFiveWallAlignedOneEightySourceScratch

/-! # Uniform aligned-stride induction on the degenerate double-five wall -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerOpenDoubleFiveWallAlignedStrideInductionSource68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 30000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option maxHeartbeats 4000000 in
theorem secondaryResidualInvariantThreePolynomial68_coeff_aligned_offset_of_fiveWall
    (A B c d e : k[X]) (n g s : ℕ)
    (hn : 0 < n) (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hwall : 3 * g = 5 * n) (hs : s ≤ 5 * n - 2 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g - s)
    (hd : d.natDegree ≤ 5 * n - 2 * g - s)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (secondaryResidualInvariantThreePolynomial68 A B c d e).coeff
        (10 * n - 3 * g - s) =
      (8 / 9 : k) *
        (-(A.coeff (2 * n) * B.coeff (3 * n - g) *
            d.coeff (5 * n - 2 * g - s)) -
          B.coeff (3 * n - g) ^ 2 * c.coeff (4 * n - g - s) +
          3 * c.coeff (4 * n - g - s) *
            e.coeff (6 * n - 2 * g)) := by
  have hABd := coeff_mul_mul_at_bounds68 A B d (2 * n)
    (3 * n - g) (5 * n - 2 * g - s) hA hB hd
  have hABdi : 2 * n + (3 * n - g) + (5 * n - 2 * g - s) =
      10 * n - 3 * g - s := by omega
  rw [hABdi] at hABd
  have hBBc := coeff_mul_mul_at_bounds68 B B c (3 * n - g)
    (3 * n - g) (4 * n - g - s) hB hB hc
  have hBBci : (3 * n - g) + (3 * n - g) + (4 * n - g - s) =
      10 * n - 3 * g - s := by omega
  rw [hBBci] at hBBc
  have hB2c : (B ^ 2 * c).coeff (10 * n - 3 * g - s) =
      B.coeff (3 * n - g) ^ 2 * c.coeff (4 * n - g - s) := by
    simpa only [pow_two] using hBBc
  have hce := coeff_mul_at_bounds68 c e (4 * n - g - s)
    (6 * n - 2 * g) hc he
  have hcei : (4 * n - g - s) + (6 * n - 2 * g) =
      10 * n - 3 * g - s := by omega
  rw [hcei] at hce
  have hd2 : (d ^ 2).natDegree < 10 * n - 3 * g - s := by
    compute_degree
    omega
  simp only [secondaryResidualInvariantThreePolynomial68, coeff_add,
    coeff_sub, coeff_smul, smul_eq_mul, hABd, hB2c, hce,
    coeff_eq_zero_of_natDegree_lt hd2]
  ring

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
      12 * n - 3 * g - s - 1 := by compute_degree; omega
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

theorem laterDeepLowerOpenDoubleFiveWall_degenerate_aligned_offset_edges_zero68
    (n s : ℕ) (a b c₁ d₁ e : k)
    (hn : 0 < n) (hs : 3 * s < 5 * n) (ha : a ≠ 0) (hb : b ≠ 0)
    (hi3 : -a * b * d₁ - b ^ 2 * c₁ + 3 * c₁ * e = 0)
    (hrow :
      2 * a ^ 2 * b * d₁ * (5 * (n : k) - (s : k)) -
        6 * a * c₁ * e * (5 * (n : k) - (s : k)) -
        4 * (n : k) * a * b ^ 2 * c₁ = 0) : c₁ = 0 ∧ d₁ = 0 := by
  have hN : 7 * (n : k) - (s : k) ≠ 0 := by
    intro hz
    have hnat : 7 * n = s := by exact_mod_cast (sub_eq_zero.mp hz)
    omega
  have hcprod : a * b ^ 2 * c₁ * (7 * (n : k) - (s : k)) = 0 := by
    linear_combination (-1 / 2 : k) * hrow -
      a * (5 * (n : k) - (s : k)) * hi3
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

set_option maxHeartbeats 3000000 in
theorem secondaryLoadInvariantThreePolynomial68_degree_lt_aligned_offset_of_doubleFiveWall
    (gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g s : ℕ) (hn : 0 < n)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hwall : 3 * g = 5 * n) (hs : s < 5 * n - 2 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g - s)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (secondaryLoadInvariantThreePolynomial68
      0 0 gamma delta epsilon zeta A B c D e).natDegree <
        10 * n - 3 * g - s := by
  simp only [secondaryLoadInvariantThreePolynomial68, zero_mul, mul_zero,
    zero_smul, smul_zero, add_zero, sub_zero]
  compute_degree
  omega

set_option maxHeartbeats 10000000 in
theorem cubicLoadRowOnePolynomial68_degree_lt_aligned_offset_of_doubleFiveWall
    (alpha gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g s : ℕ)
    (hn : 0 < n) (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hwall : 3 * g = 5 * n) (hs : s < 5 * n - 2 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g - s)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (cubicLoadRowOnePolynomial68 0 alpha 0 gamma delta epsilon zeta eta
      A B c D e).natDegree < 12 * n - 3 * g - s - 1 := by
  rw [cubicLoadRowOnePolynomial68_eq_alphaRest 0 alpha 0 gamma delta
      epsilon zeta eta A B c D e rfl,
    cubicLoadRowOneAlphaRestPolynomial68_eq_deepGapRest']
  let Ur := cubicLoadUAlphaRestPolynomial68 0 gamma delta zeta A B c
  let Vr := cubicLoadVAlphaRestPolynomial68 alpha 0 gamma delta epsilon
    eta A B c D e
  let Vtail := (2 / 3 * gamma : k) • c +
    (1 / 2 * delta : k) • B + C eta
  let C0c := (1 / 3 : k) • A ^ 2
  let Er := (1 / 3 : k) • (A * c) + e
  have hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n := by omega
  have hgt : n < g := by omega
  have hgle : g ≤ 2 * n := by omega
  have hUr : Ur.natDegree ≤ 2 * n :=
    cubicLoadUAlphaRestPolynomial68_degree_le_of_beta gamma delta zeta
      A B c n g hgt hA hB (hc.trans (by omega))
  have hVr : Vr.natDegree ≤ 6 * n - g :=
    cubicLoadVAlphaRestPolynomial68_degree_le_of_laterDeepLower_le_two
      alpha 0 gamma delta epsilon eta A B c D e n g hn hwindow hgle
      hA hB (hc.trans (by omega)) hD (he.trans (by omega))
  have hVtail : Vtail.natDegree ≤
      max (4 * n - g - s) (3 * n - g) := by
    simp only [Vtail]
    compute_degree
    omega
  have hC0c : C0c.natDegree ≤ 4 * n := by
    simp only [C0c]
    compute_degree
    omega
  have hEr : Er.natDegree ≤ 6 * n - g - s := by
    simp only [Er]
    compute_degree
    omega
  have hdecomp :
      cubicLoadRowOneDeepGapRestPolynomial68 alpha 0 gamma delta epsilon
          zeta eta A B c D e =
        Ur * derivative D +
          (2 : k) • ((alpha • c) * derivative Er) +
          (2 : k) • (((2 / 3 * gamma : k) • A) * derivative Er) +
          (2 : k) • ((C epsilon : k[X]) * derivative Er) -
          (2 : k) • (C0c * derivative Vtail) -
          (2 : k) • (c * derivative Vr) -
          D * derivative Ur := by
    apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
    simp only [cubicLoadRowOneDeepGapRestPolynomial68, Ur, Vr, Vtail,
      C0c, Er, cubicLoadVAlphaLowPolynomial68, zero_mul, zero_smul,
      zero_add, add_zero, sub_zero, derivative_add, derivative_smul,
      derivative_pow, derivative_mul, derivative_C,
      Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow,
      map_zero, RatFunc.algebraMap_C]
    simp only [map_neg, map_div₀, map_ofNat, map_natCast, map_one]
    ring
  rw [hdecomp]
  have hbound (u v : ℕ) (hv : 0 < v)
      (hu : u + v - 1 < 12 * n - 3 * g - s - 1) :
      ∀ p q : k[X], p.natDegree ≤ u → q.natDegree ≤ v →
        (p * derivative q).natDegree < 12 * n - 3 * g - s - 1 :=
    fun p q hp hq => deepGap_natDegree_mul_derivative_lt68 p q u v
      (12 * n - 3 * g - s - 1) hv hp hq hu
  have h1 : (Ur * derivative D).natDegree < 12 * n - 3 * g - s - 1 :=
    hbound (2 * n) (5 * n - g) (by omega) (by omega) Ur D hUr hD
  have h2 : ((alpha • c) * derivative Er).natDegree <
      12 * n - 3 * g - s - 1 :=
    hbound (4 * n - g - s) (6 * n - g - s) (by omega) (by omega)
      (alpha • c) Er ((natDegree_smul_le alpha c).trans hc) hEr
  have h3 : (((2 / 3 * gamma : k) • A) * derivative Er).natDegree <
      12 * n - 3 * g - s - 1 :=
    hbound (2 * n) (6 * n - g - s) (by omega) (by omega) _ Er
      ((natDegree_smul_le _ A).trans hA) hEr
  have heps : (C epsilon : k[X]).natDegree ≤ 0 := by rw [natDegree_C]
  have h4 : ((C epsilon : k[X]) * derivative Er).natDegree <
      12 * n - 3 * g - s - 1 :=
    hbound 0 (6 * n - g - s) (by omega) (by omega) _ Er heps hEr
  have hVmax : max (4 * n - g - s) (3 * n - g) <
      8 * n - 3 * g - s := by
    apply max_lt
    · omega
    · omega
  have h5 : (C0c * derivative Vtail).natDegree <
      12 * n - 3 * g - s - 1 :=
    hbound (4 * n) (max (4 * n - g - s) (3 * n - g))
      (lt_of_lt_of_le (by omega : 0 < 3 * n - g) (le_max_right _ _))
      (by omega) C0c Vtail hC0c hVtail
  have h6 : (c * derivative Vr).natDegree < 12 * n - 3 * g - s - 1 :=
    hbound (4 * n - g - s) (6 * n - g) (by omega) (by omega)
      c Vr hc hVr
  have h7 : (D * derivative Ur).natDegree < 12 * n - 3 * g - s - 1 :=
    hbound (5 * n - g) (2 * n) (by omega) (by omega) D Ur hD hUr
  exact deepGap_natDegree_sub_lt
    (deepGap_natDegree_sub_lt
      (deepGap_natDegree_sub_lt
        (deepGap_natDegree_add_lt
          (deepGap_natDegree_add_lt
            (deepGap_natDegree_add_lt h1
              (deepGap_natDegree_smul_lt68 (2 : k) h2))
              (deepGap_natDegree_smul_lt68 (2 : k) h3))
            (deepGap_natDegree_smul_lt68 (2 : k) h4))
          (deepGap_natDegree_smul_lt68 (2 : k) h5))
        (deepGap_natDegree_smul_lt68 (2 : k) h6)) h7

set_option maxHeartbeats 30000000 in
theorem laterDeepLowerOpenDoubleFiveWall_aligned_offset_source_step68
    (alpha gamma delta epsilon zeta eta : k)
    (A B c d e : k[X]) (qc qd : k[X]) (i3 : k) (n g s : ℕ)
    (hn : 0 < n) (ha : A.coeff (2 * n) ≠ 0)
    (hb : B.coeff (3 * n - g) ≠ 0)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hwall : 3 * g = 5 * n) (hspos : 0 < s)
    (hs : s < 5 * n - 2 * g)
    (hsAlign : 60 ∣ s) (hcAlign : 60 ∣ 4 * n - g)
    (hdAlign : 60 ∣ 5 * n - 2 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g - s)
    (hd : d.natDegree ≤ 5 * n - 2 * g - s)
    (hD : ((1 / 3 : k) • (A * B) + d).natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - 2 * g)
    (hcexpand : c = expand k 60 qc) (hdexpand : d = expand k 60 qd)
    (hi3c : cubicFirstIntegralThreePolynomial68
      0 0 gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i3)
    (hrowPoly : secondaryResidualRowOnePolynomial68 A B c d e +
      cubicLoadRowOnePolynomial68 0 alpha 0 gamma delta epsilon zeta eta
        A B c ((1 / 3 : k) • (A * B) + d) e = 0) :
    c.natDegree ≤ 4 * n - g - (s + 60) ∧
      d.natDegree ≤ 5 * n - 2 * g - (s + 60) := by
  have hcoeff3 := congrArg
    (fun p : k[X] => p.coeff (10 * n - 3 * g - s)) hi3c
  rw [cubicFirstIntegralThreePolynomial68_secondaryLoadSplit, coeff_add,
    cubicFirstIntegralThreePolynomial68_residualCoordinates,
    secondaryResidualInvariantThreePolynomial68_coeff_aligned_offset_of_fiveWall
      A B c d e n g s hn hopen hwall (by omega) hA hB hc hd he,
    coeff_eq_zero_of_natDegree_lt
      (secondaryLoadInvariantThreePolynomial68_degree_lt_aligned_offset_of_doubleFiveWall
        gamma delta epsilon zeta A B c ((1 / 3 : k) • (A * B) + d) e
        n g s hn hopen hwall hs hA hB hc hD he), add_zero] at hcoeff3
  have hidx3 : 10 * n - 3 * g - s ≠ 0 := by omega
  simp only [coeff_C, if_neg hidx3] at hcoeff3
  have hi3scalar :
      -A.coeff (2 * n) * B.coeff (3 * n - g) *
          d.coeff (5 * n - 2 * g - s) -
        B.coeff (3 * n - g) ^ 2 * c.coeff (4 * n - g - s) +
        3 * c.coeff (4 * n - g - s) * e.coeff (6 * n - 2 * g) = 0 := by
    have ht := (mul_eq_zero.mp hcoeff3).resolve_left (by norm_num)
    linear_combination ht
  have hloadOne :=
    cubicLoadRowOnePolynomial68_degree_lt_aligned_offset_of_doubleFiveWall
      alpha gamma delta epsilon zeta eta A B c
      ((1 / 3 : k) • (A * B) + d) e n g s hn hopen hwall hs
      hA hB hc hD he
  have hcoeffOne := congrArg
    (fun p : k[X] => p.coeff (12 * n - 3 * g - s - 1)) hrowPoly
  rw [coeff_add, coeff_zero,
    coeff_eq_zero_of_natDegree_lt hloadOne, add_zero,
    secondaryResidualRowOnePolynomial68_coeff_aligned_offset_of_fiveWall
      A B c d e n g s hn hopen hwall hspos hs hA hB hc hd he]
    at hcoeffOne
  have hrowScalar :
      2 * A.coeff (2 * n) ^ 2 * B.coeff (3 * n - g) *
          d.coeff (5 * n - 2 * g - s) * (5 * (n : k) - (s : k)) -
        6 * A.coeff (2 * n) * c.coeff (4 * n - g - s) *
          e.coeff (6 * n - 2 * g) * (5 * (n : k) - (s : k)) -
        4 * (n : k) * A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 *
          c.coeff (4 * n - g - s) = 0 := by
    have ht := (mul_eq_zero.mp hcoeffOne).resolve_left (by norm_num)
    have hcastM : (((5 * n - s : ℕ) : k)) = 5 * (n : k) - (s : k) := by
      rw [Nat.cast_sub (by omega : s ≤ 5 * n)]
      push_cast
      rfl
    rw [hcastM] at ht
    exact ht
  have edges := laterDeepLowerOpenDoubleFiveWall_degenerate_aligned_offset_edges_zero68
    n s (A.coeff (2 * n)) (B.coeff (3 * n - g))
    (c.coeff (4 * n - g - s)) (d.coeff (5 * n - 2 * g - s))
    (e.coeff (6 * n - 2 * g)) hn (by omega) ha hb hi3scalar hrowScalar
  have hcAlignS : 60 ∣ 4 * n - g - s := by
    obtain ⟨u, hu⟩ := hcAlign
    obtain ⟨v, hv⟩ := hsAlign
    refine ⟨u - v, ?_⟩
    omega
  have hdAlignS : 60 ∣ 5 * n - 2 * g - s := by
    obtain ⟨u, hu⟩ := hdAlign
    obtain ⟨v, hv⟩ := hsAlign
    refine ⟨u - v, ?_⟩
    omega
  constructor
  · have ht : c.natDegree ≤ (4 * n - g - s) - 60 := by
      rw [hcexpand]
      apply natDegree_expand_le_sub_sixty_of_aligned_boundary_zero68
        qc (4 * n - g - s) hcAlignS (by omega)
      · simpa only [← hcexpand] using hc
      · rw [← hcexpand]
        exact edges.1
    omega
  · have ht : d.natDegree ≤ (5 * n - 2 * g - s) - 60 := by
      rw [hdexpand]
      apply natDegree_expand_le_sub_sixty_of_aligned_boundary_zero68
        qd (5 * n - 2 * g - s) hdAlignS (by omega)
      · simpa only [← hdexpand] using hd
      · rw [← hdexpand]
        exact edges.2
    omega

set_option maxHeartbeats 30000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleFiveWallDegenerateAlignedOffsetDescent68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (s : ℕ) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hopen :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      3 * n < 2 * g ∧ 2 * g < 5 * n)
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
      let h := secondaryResidualGap68 n d ee
      2 * g ≤ h)
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
      3 * g = 5 * n)
    (hdegenerate :
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
      ce.coeff (4 * n - g) = 0 ∧ Be.coeff (3 * n - g) ≠ 0 ∧
        d.coeff (5 * n - 2 * g) = 0 ∧ ee.coeff (6 * n - 2 * g) ≠ 0)
    (hcAlign :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      60 ∣ 4 * n - g)
    (hdAlign :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      60 ∣ 5 * n - 2 * g)
    (hsAlign : 60 ∣ s) (hs120 : 120 ≤ s)
    (hsTerminal :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      s ≤ 5 * n - 2 * g) :
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
    ce.natDegree ≤ 4 * n - g - s ∧
      d.natDegree ≤ 5 * n - 2 * g - s := by
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
  let Dtr := (1 / 3 : k) • (Ae * Be) + d
  change 3 * n < 2 * g ∧ 2 * g < 5 * n at hopen
  change 2 * g ≤ h at hdouble
  change 3 * g = 5 * n at hwall
  change ce.coeff (4 * n - g) = 0 ∧ Be.coeff (3 * n - g) ≠ 0 ∧
      d.coeff (5 * n - 2 * g) = 0 ∧ ee.coeff (6 * n - 2 * g) ≠ 0
    at hdegenerate
  change 60 ∣ 4 * n - g at hcAlign
  change 60 ∣ 5 * n - 2 * g at hdAlign
  change s ≤ 5 * n - 2 * g at hsTerminal
  have core := maximalExpandedIntegratedPolynomialLowerSystem_cubicCore68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have drop := maximalExpandedIntegratedPolynomialLowerSystem_degreeDrop68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have secondary := maximalExpandedIntegratedPolynomialLowerSystem_secondaryRadius68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  change 0 < g ∧ Be.natDegree ≤ 3 * n - g ∧ ce.natDegree ≤ 4 * n - g ∧
    De.natDegree ≤ 5 * n - g ∧ ee.natDegree ≤ 6 * n - g ∧ _ at secondary
  have hn : 0 < n := by simpa only [n] using core.1
  have ha : Ae.coeff (2 * n) ≠ 0 := by
    simpa only [n, Ae] using core.2.2.2.2.2
  have hA : Ae.natDegree ≤ 2 * n := by
    have hAe : Ae.natDegree = 2 * n := by
      simpa only [n, Ae, Be, Ce, De, Ee] using drop.1
    omega
  have base :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleFiveWallDegenerateAlignedDescent68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hdouble)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d] using hdegenerate)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hcAlign)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hdAlign)
  change ce.natDegree ≤ 4 * n - g - 120 ∧
      d.natDegree ≤ 5 * n - 2 * g - 120 at base
  have drops :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenResidualDrops68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
  change l = 0 ∧ beta = 0 ∧ ee.coeff (6 * n - g) = 0 ∧
      Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
        3 * De.coeff (5 * n - g) ∧
      d.natDegree < 5 * n - g ∧ ee.natDegree < 6 * n - g ∧ g < h at drops
  have hdbase : d.natDegree < 5 * n := drops.2.2.2.2.1.trans (by omega)
  have hebase : ee.natDegree < 6 * n := drops.2.2.2.2.2.1.trans (by omega)
  have bounds := secondaryResidualGap68_degreeBounds n d ee hdbase hebase
  have selector :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleFiveWallSelector68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hdouble)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
  change h = 2 * g ∧ _ at selector
  have he2 : ee.natDegree ≤ 6 * n - 2 * g := by
    have ht := bounds.2
    change ee.natDegree ≤ 6 * n - h at ht
    rw [selector.1] at ht
    exact ht
  have hceexpand : ce = expand k 60 (cubicCDefectPolynomial68 A C0) := by
    simpa only [ce, Ae, Ce] using expand_cubicCDefectPolynomial68 60 A C0
  have hdexpand : d = expand k 60 (secondaryDDefectPolynomial68 A B D) := by
    simp only [d, Ae, Be, De, secondaryDDefectPolynomial68,
      map_sub, expand_mul, Polynomial.smul_eq_C_mul, map_mul, expand_C]
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec : Ee = (1 / 27 : k) • Ae ^ 3 +
      (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using
      cubicEDefectPolynomial68_eq_cubicCoordinates Ae Ce Ee
  have hDrec : De = Dtr := by
    simpa only [Dtr, d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
  have hD : Dtr.natDegree ≤ 5 * n - g := by
    rw [← hDrec]
    exact secondary.2.2.2.1
  obtain ⟨i3, hi3⟩ := hsys.firstThree
  have hi3c : cubicFirstIntegralThreePolynomial68
      0 0 gamma delta epsilon zeta Ae Be ce Dtr ee = C i3 := by
    have hi3e : firstIntegralThreePolynomial68
        l beta gamma delta epsilon zeta Ae Be Ce De Ee = C i3 := by
      simpa only [Ae, Be, Ce, De, Ee] using
        expand_firstIntegralThreePolynomial68_of_eq
          l beta gamma delta epsilon zeta i3 A B C0 D E hi3
    rw [hCrec, hErec, firstIntegralThreePolynomial68_cubicCoordinates,
      hDrec, drops.1, drops.2.1] at hi3e
    exact hi3e
  have h1e : lowerRowOnePolynomial68
      (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) Ce De Ee = 0 := by
    dsimp only [Ae, Be, Ce, De, Ee]
    rw [← expand_integratedTPolynomial68, ← expand_integratedUPolynomial68,
      ← expand_integratedVPolynomial68, lowerRowOnePolynomial68_expand,
      hsys.rowOne, map_zero, zero_mul]
  have hrowPoly : secondaryResidualRowOnePolynomial68 Ae Be ce d ee +
      cubicLoadRowOnePolynomial68 0 alpha 0 gamma delta epsilon zeta eta
        Ae Be ce Dtr ee = 0 := by
    have hr := h1e
    rw [hCrec, hDrec, hErec, drops.1, drops.2.1] at hr
    exact polynomialSecondaryResidualRowOne68
      0 alpha 0 gamma delta epsilon zeta eta Ae Be ce d ee hr
  obtain ⟨q, hq⟩ := hsAlign
  have hq2 : 2 ≤ q := by omega
  let j := q - 2
  have hsform : s = 120 + 60 * j := by
    dsimp only [j]
    omega
  have hsteps : ∀ j : ℕ, 120 + 60 * j ≤ 5 * n - 2 * g →
      ce.natDegree ≤ 4 * n - g - (120 + 60 * j) ∧
        d.natDegree ≤ 5 * n - 2 * g - (120 + 60 * j) := by
    intro m
    induction m with
    | zero =>
        intro hm
        simpa using base
    | succ m ih =>
        intro hm
        have hprev := ih (by omega)
        have hstep := laterDeepLowerOpenDoubleFiveWall_aligned_offset_source_step68
          alpha gamma delta epsilon zeta eta Ae Be ce d ee
          (cubicCDefectPolynomial68 A C0)
          (secondaryDDefectPolynomial68 A B D) i3 n g (120 + 60 * m)
          hn ha hdegenerate.2.1 hopen hwall (by omega) (by omega)
          (by refine ⟨2 + m, ?_⟩; omega)
          hcAlign hdAlign hA secondary.2.1 hprev.1 hprev.2 hD he2
          hceexpand hdexpand hi3c hrowPoly
        constructor <;> omega
  rw [hsform] at hsTerminal ⊢
  exact hsteps j hsTerminal

set_option maxHeartbeats 5000000 in
theorem secondaryLoadInvariantThreePolynomial68_coeff_terminal_aligned_offset_of_fiveWall
    (gamma delta epsilon zeta : k) (A B c d e : k[X])
    (n g : ℕ) (hn : 0 < n)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hwall : 3 * g = 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g - (5 * n - 2 * g))
    (hd : d.natDegree ≤ 0)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (secondaryLoadInvariantThreePolynomial68 0 0 gamma delta epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff
        (10 * n - 3 * g - (5 * n - 2 * g)) =
      (-1 / 2 : k) * delta * A.coeff (2 * n) * B.coeff (3 * n - g) := by
  have htarget : 10 * n - 3 * g - (5 * n - 2 * g) = 5 * n - g := by
    omega
  have hAB := coeff_mul_at_bounds68 A B (2 * n) (3 * n - g) hA hB
  have hABi : 2 * n + (3 * n - g) = 5 * n - g := by omega
  rw [hABi] at hAB
  have hDcoeff : (((1 / 3 : k) • (A * B) + d).coeff (5 * n - g)) =
      (1 / 3 : k) * A.coeff (2 * n) * B.coeff (3 * n - g) := by
    rw [coeff_add, coeff_smul, hAB,
      coeff_eq_zero_of_natDegree_lt (hd.trans_lt (by omega))]
    ring
  have hzeta : (zeta • B).natDegree < 5 * n - g :=
    (natDegree_smul_le zeta B).trans_lt (hB.trans_lt (by omega))
  have heps : ((2 * epsilon : k) • c).natDegree < 5 * n - g :=
    (natDegree_smul_le _ c).trans_lt (hc.trans_lt (by omega))
  have hgammaE : ((4 * gamma : k) • e).natDegree < 5 * n - g :=
    (natDegree_smul_le _ e).trans_lt (he.trans_lt (by omega))
  have hB2 : ((2 / 3 * gamma : k) • B ^ 2).natDegree <
      5 * n - g := by
    compute_degree
    omega
  have hABcoeff : (A * B).coeff (5 * n - g) =
      A.coeff (2 * n) * B.coeff (3 * n - g) := hAB
  rw [htarget]
  simp only [secondaryLoadInvariantThreePolynomial68, zero_mul, zero_smul,
    zero_add, add_zero, sub_zero, coeff_add, coeff_sub, coeff_smul,
    coeff_eq_zero_of_natDegree_lt hzeta,
    coeff_eq_zero_of_natDegree_lt heps,
    coeff_eq_zero_of_natDegree_lt hgammaE,
    coeff_eq_zero_of_natDegree_lt hB2, hDcoeff, hABcoeff, smul_eq_mul]
  ring

set_option maxHeartbeats 30000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleFiveWallDegenerateAlignedTerminalLoad68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hopen :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      3 * n < 2 * g ∧ 2 * g < 5 * n)
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
      let h := secondaryResidualGap68 n d ee
      2 * g ≤ h)
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
      3 * g = 5 * n)
    (hdegenerate :
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
      ce.coeff (4 * n - g) = 0 ∧ Be.coeff (3 * n - g) ≠ 0 ∧
        d.coeff (5 * n - 2 * g) = 0 ∧ ee.coeff (6 * n - 2 * g) ≠ 0)
    (hcAlign :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      60 ∣ 4 * n - g)
    (hdAlign :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      60 ∣ 5 * n - 2 * g) :
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
    5 * n - 2 * g = g ∧
      ce.natDegree ≤ 4 * n - g - (5 * n - 2 * g) ∧
      d.natDegree ≤ 0 ∧
      (8 / 9 : k) *
        (-(Ae.coeff (2 * n) * Be.coeff (3 * n - g) * d.coeff 0) -
          Be.coeff (3 * n - g) ^ 2 *
            ce.coeff (4 * n - g - (5 * n - 2 * g)) +
          3 * ce.coeff (4 * n - g - (5 * n - 2 * g)) *
            ee.coeff (6 * n - 2 * g)) =
        (1 / 2 : k) * delta * Ae.coeff (2 * n) * Be.coeff (3 * n - g) := by
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
  let Dtr := (1 / 3 : k) • (Ae * Be) + d
  change 3 * n < 2 * g ∧ 2 * g < 5 * n at hopen
  change 2 * g ≤ h at hdouble
  change 3 * g = 5 * n at hwall
  change ce.coeff (4 * n - g) = 0 ∧ Be.coeff (3 * n - g) ≠ 0 ∧
      d.coeff (5 * n - 2 * g) = 0 ∧ ee.coeff (6 * n - 2 * g) ≠ 0
    at hdegenerate
  change 60 ∣ 4 * n - g at hcAlign
  change 60 ∣ 5 * n - 2 * g at hdAlign
  have hterminalEq : 5 * n - 2 * g = g := by omega
  have cutoff :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleFiveWallDegenerateAlignedOffsetOneTwentyLoadCutoff68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hdouble)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d] using hdegenerate)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hcAlign)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hdAlign)
  change 180 ∣ n ∧ _ at cutoff
  have hn180 : 180 ≤ n := by
    obtain ⟨u, hu⟩ := cutoff.1
    omega
  have hterminal120 : 120 ≤ 5 * n - 2 * g := by omega
  have terminalBounds :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleFiveWallDegenerateAlignedOffsetDescent68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      (5 * n - 2 * g) hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hdouble)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d] using hdegenerate)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hcAlign)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hdAlign)
      hdAlign hterminal120 (by rfl)
  change ce.natDegree ≤ 4 * n - g - (5 * n - 2 * g) ∧
      d.natDegree ≤ 5 * n - 2 * g - (5 * n - 2 * g) at terminalBounds
  have hd0 : d.natDegree ≤ 0 := by simpa using terminalBounds.2
  refine ⟨hterminalEq, terminalBounds.1, hd0, ?_⟩
  have core := maximalExpandedIntegratedPolynomialLowerSystem_cubicCore68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have drop := maximalExpandedIntegratedPolynomialLowerSystem_degreeDrop68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have secondary := maximalExpandedIntegratedPolynomialLowerSystem_secondaryRadius68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  change 0 < g ∧ Be.natDegree ≤ 3 * n - g ∧ ce.natDegree ≤ 4 * n - g ∧
    De.natDegree ≤ 5 * n - g ∧ ee.natDegree ≤ 6 * n - g ∧ _ at secondary
  have hn : 0 < n := by simpa only [n] using core.1
  have hA : Ae.natDegree ≤ 2 * n := by
    have hAe : Ae.natDegree = 2 * n := by
      simpa only [n, Ae, Be, Ce, De, Ee] using drop.1
    omega
  have drops :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenResidualDrops68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
  change l = 0 ∧ beta = 0 ∧ ee.coeff (6 * n - g) = 0 ∧
      Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
        3 * De.coeff (5 * n - g) ∧
      d.natDegree < 5 * n - g ∧ ee.natDegree < 6 * n - g ∧ g < h at drops
  have hdbase : d.natDegree < 5 * n := drops.2.2.2.2.1.trans (by omega)
  have hebase : ee.natDegree < 6 * n := drops.2.2.2.2.2.1.trans (by omega)
  have bounds := secondaryResidualGap68_degreeBounds n d ee hdbase hebase
  have selector :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleFiveWallSelector68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hdouble)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
  change h = 2 * g ∧ _ at selector
  have he2 : ee.natDegree ≤ 6 * n - 2 * g := by
    have ht := bounds.2
    change ee.natDegree ≤ 6 * n - h at ht
    rw [selector.1] at ht
    exact ht
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec : Ee = (1 / 27 : k) • Ae ^ 3 +
      (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using
      cubicEDefectPolynomial68_eq_cubicCoordinates Ae Ce Ee
  have hDrec : De = Dtr := by
    simpa only [Dtr, d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
  obtain ⟨i3, hi3⟩ := hsys.firstThree
  have hi3c : cubicFirstIntegralThreePolynomial68
      0 0 gamma delta epsilon zeta Ae Be ce Dtr ee = C i3 := by
    have hi3e : firstIntegralThreePolynomial68
        l beta gamma delta epsilon zeta Ae Be Ce De Ee = C i3 := by
      simpa only [Ae, Be, Ce, De, Ee] using
        expand_firstIntegralThreePolynomial68_of_eq
          l beta gamma delta epsilon zeta i3 A B C0 D E hi3
    rw [hCrec, hErec, firstIntegralThreePolynomial68_cubicCoordinates,
      hDrec, drops.1, drops.2.1] at hi3e
    exact hi3e
  have hcoeff := congrArg
    (fun p : k[X] => p.coeff
      (10 * n - 3 * g - (5 * n - 2 * g))) hi3c
  rw [cubicFirstIntegralThreePolynomial68_secondaryLoadSplit, coeff_add,
    cubicFirstIntegralThreePolynomial68_residualCoordinates,
    secondaryResidualInvariantThreePolynomial68_coeff_aligned_offset_of_fiveWall
      Ae Be ce d ee n g (5 * n - 2 * g) hn hopen hwall (by simp)
      hA secondary.2.1 terminalBounds.1 terminalBounds.2 he2,
    secondaryLoadInvariantThreePolynomial68_coeff_terminal_aligned_offset_of_fiveWall
      gamma delta epsilon zeta Ae Be ce d ee n g hn hopen hwall hA
      secondary.2.1 terminalBounds.1 hd0 he2] at hcoeff
  have hdidx : 5 * n - 2 * g - (5 * n - 2 * g) = 0 := by omega
  rw [hdidx] at hcoeff
  have hidx : 10 * n - 3 * g - (5 * n - 2 * g) ≠ 0 := by omega
  simp only [coeff_C, if_neg hidx] at hcoeff
  have hpacket := earliest_offsetOneFifty_deltaLoaded_scalar68
    (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
    (ce.coeff (4 * n - g - (5 * n - 2 * g))) (d.coeff 0)
    (ee.coeff (6 * n - 2 * g)) delta (by
      linear_combination hcoeff)
  linear_combination hpacket

#print axioms secondaryResidualInvariantThreePolynomial68_coeff_aligned_offset_of_fiveWall
#print axioms secondaryResidualRowOnePolynomial68_coeff_aligned_offset_of_fiveWall
#print axioms laterDeepLowerOpenDoubleFiveWall_degenerate_aligned_offset_edges_zero68
#print axioms secondaryLoadInvariantThreePolynomial68_degree_lt_aligned_offset_of_doubleFiveWall
#print axioms cubicLoadRowOnePolynomial68_degree_lt_aligned_offset_of_doubleFiveWall
#print axioms laterDeepLowerOpenDoubleFiveWall_aligned_offset_source_step68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleFiveWallDegenerateAlignedOffsetDescent68
#print axioms secondaryLoadInvariantThreePolynomial68_coeff_terminal_aligned_offset_of_fiveWall
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleFiveWallDegenerateAlignedTerminalLoad68

end LaterDeepLowerOpenDoubleFiveWallAlignedStrideInductionSource68

end Max11DegreeRoutes
