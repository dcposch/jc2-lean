import LowScale46AlignedChart

/-! # Finite degree cones in the `(4,6)` polynomial endgame

This module replaces the source report's finite integer scans by exact
Presburger proofs.  `MaxTie4` says that the maximum of four candidate degrees
is attained at least twice.  Applying it to the two coefficient-curve rows
gives the unique positive mismatch cone `(4n,5n,7n)`; the two aligned cones
are solved exactly as well.
-/

namespace Max11DegreeRoutes

open Polynomial

/-- Among four natural numbers, the maximum is attained at least twice. -/
def MaxTie4 (a b c d : ℕ) : Prop :=
  (a = b ∧ c ≤ a ∧ d ≤ a) ∨
  (a = c ∧ b ≤ a ∧ d ≤ a) ∨
  (a = d ∧ b ≤ a ∧ c ≤ a) ∨
  (b = c ∧ a ≤ b ∧ d ≤ b) ∨
  (b = d ∧ a ≤ b ∧ c ≤ b) ∨
  (c = d ∧ a ≤ c ∧ b ≤ c)

section PolynomialMaximum

variable {F : Type*} [Field F]

/-- Four nonzero polynomial terms summing to zero cannot have a unique
largest degree. -/
theorem maxTie4_of_polynomial_sum_eq_zero46
    (p q r s : Polynomial F) (hp : p ≠ 0) (hq : q ≠ 0)
    (hr : r ≠ 0) (hs : s ≠ 0) (hsum : p + q + r + s = 0) :
    MaxTie4 p.natDegree q.natDegree r.natDegree s.natDegree := by
  by_contra hnot
  have hunique :
      (q.natDegree < p.natDegree ∧ r.natDegree < p.natDegree ∧
        s.natDegree < p.natDegree) ∨
      (p.natDegree < q.natDegree ∧ r.natDegree < q.natDegree ∧
        s.natDegree < q.natDegree) ∨
      (p.natDegree < r.natDegree ∧ q.natDegree < r.natDegree ∧
        s.natDegree < r.natDegree) ∨
      (p.natDegree < s.natDegree ∧ q.natDegree < s.natDegree ∧
        r.natDegree < s.natDegree) := by
    simp only [MaxTie4, not_or, not_and_or, not_le] at hnot
    omega
  rcases hunique with hP | hQ | hR | hS
  · have hq0 := coeff_eq_zero_of_natDegree_lt hP.1
    have hr0 := coeff_eq_zero_of_natDegree_lt hP.2.1
    have hs0 := coeff_eq_zero_of_natDegree_lt hP.2.2
    have hcoeff := congrArg (fun t : Polynomial F => t.coeff p.natDegree) hsum
    simp only [coeff_add, coeff_zero, hq0, hr0, hs0, add_zero] at hcoeff
    have hp0 : p.coeff p.natDegree ≠ 0 := by
      rw [coeff_natDegree]
      exact leadingCoeff_ne_zero.mpr hp
    exact hp0 hcoeff
  · have hp0 := coeff_eq_zero_of_natDegree_lt hQ.1
    have hr0 := coeff_eq_zero_of_natDegree_lt hQ.2.1
    have hs0 := coeff_eq_zero_of_natDegree_lt hQ.2.2
    have hcoeff := congrArg (fun t : Polynomial F => t.coeff q.natDegree) hsum
    simp only [coeff_add, coeff_zero, hp0, hr0, hs0, zero_add, add_zero] at hcoeff
    have hq0 : q.coeff q.natDegree ≠ 0 := by
      rw [coeff_natDegree]
      exact leadingCoeff_ne_zero.mpr hq
    exact hq0 hcoeff
  · have hp0 := coeff_eq_zero_of_natDegree_lt hR.1
    have hq0 := coeff_eq_zero_of_natDegree_lt hR.2.1
    have hs0 := coeff_eq_zero_of_natDegree_lt hR.2.2
    have hcoeff := congrArg (fun t : Polynomial F => t.coeff r.natDegree) hsum
    simp only [coeff_add, coeff_zero, hp0, hq0, hs0, zero_add, add_zero] at hcoeff
    have hr0 : r.coeff r.natDegree ≠ 0 := by
      rw [coeff_natDegree]
      exact leadingCoeff_ne_zero.mpr hr
    exact hr0 hcoeff
  · have hp0 := coeff_eq_zero_of_natDegree_lt hS.1
    have hq0 := coeff_eq_zero_of_natDegree_lt hS.2.1
    have hr0 := coeff_eq_zero_of_natDegree_lt hS.2.2
    have hcoeff := congrArg (fun t : Polynomial F => t.coeff s.natDegree) hsum
    simp only [coeff_add, coeff_zero, hp0, hq0, hr0, zero_add] at hcoeff
    have hs0 : s.coeff s.natDegree ≠ 0 := by
      rw [coeff_natDegree]
      exact leadingCoeff_ne_zero.mpr hs
    exact hs0 hcoeff

/-- The same maximum-tie conclusion remains valid in the presence of a
remainder whose degree is below the maximum of the four displayed terms. -/
theorem maxTie4_of_polynomial_sum_add_lower_eq_zero46
    (p q r s t : Polynomial F) (hp : p ≠ 0) (hq : q ≠ 0)
    (hr : r ≠ 0) (hs : s ≠ 0)
    (ht : t.natDegree < max (max p.natDegree q.natDegree)
      (max r.natDegree s.natDegree))
    (hsum : p + q + r + s + t = 0) :
    MaxTie4 p.natDegree q.natDegree r.natDegree s.natDegree := by
  by_contra hnot
  have hunique :
      (q.natDegree < p.natDegree ∧ r.natDegree < p.natDegree ∧
        s.natDegree < p.natDegree) ∨
      (p.natDegree < q.natDegree ∧ r.natDegree < q.natDegree ∧
        s.natDegree < q.natDegree) ∨
      (p.natDegree < r.natDegree ∧ q.natDegree < r.natDegree ∧
        s.natDegree < r.natDegree) ∨
      (p.natDegree < s.natDegree ∧ q.natDegree < s.natDegree ∧
        r.natDegree < s.natDegree) := by
    simp only [MaxTie4, not_or, not_and_or, not_le] at hnot
    omega
  rcases hunique with hP | hQ | hR | hS
  · have hmax : max (max p.natDegree q.natDegree)
        (max r.natDegree s.natDegree) = p.natDegree := by omega
    rw [hmax] at ht
    have hq0 := coeff_eq_zero_of_natDegree_lt hP.1
    have hr0 := coeff_eq_zero_of_natDegree_lt hP.2.1
    have hs0 := coeff_eq_zero_of_natDegree_lt hP.2.2
    have ht0 := coeff_eq_zero_of_natDegree_lt ht
    have hcoeff := congrArg (fun u : Polynomial F => u.coeff p.natDegree) hsum
    simp only [coeff_add, coeff_zero, hq0, hr0, hs0, ht0, add_zero] at hcoeff
    have hpLead : p.coeff p.natDegree ≠ 0 := by
      rw [coeff_natDegree]
      exact leadingCoeff_ne_zero.mpr hp
    exact hpLead hcoeff
  · have hmax : max (max p.natDegree q.natDegree)
        (max r.natDegree s.natDegree) = q.natDegree := by omega
    rw [hmax] at ht
    have hp0 := coeff_eq_zero_of_natDegree_lt hQ.1
    have hr0 := coeff_eq_zero_of_natDegree_lt hQ.2.1
    have hs0 := coeff_eq_zero_of_natDegree_lt hQ.2.2
    have ht0 := coeff_eq_zero_of_natDegree_lt ht
    have hcoeff := congrArg (fun u : Polynomial F => u.coeff q.natDegree) hsum
    simp only [coeff_add, coeff_zero, hp0, hr0, hs0, ht0, zero_add,
      add_zero] at hcoeff
    have hqLead : q.coeff q.natDegree ≠ 0 := by
      rw [coeff_natDegree]
      exact leadingCoeff_ne_zero.mpr hq
    exact hqLead hcoeff
  · have hmax : max (max p.natDegree q.natDegree)
        (max r.natDegree s.natDegree) = r.natDegree := by omega
    rw [hmax] at ht
    have hp0 := coeff_eq_zero_of_natDegree_lt hR.1
    have hq0 := coeff_eq_zero_of_natDegree_lt hR.2.1
    have hs0 := coeff_eq_zero_of_natDegree_lt hR.2.2
    have ht0 := coeff_eq_zero_of_natDegree_lt ht
    have hcoeff := congrArg (fun u : Polynomial F => u.coeff r.natDegree) hsum
    simp only [coeff_add, coeff_zero, hp0, hq0, hs0, ht0, zero_add,
      add_zero] at hcoeff
    have hrLead : r.coeff r.natDegree ≠ 0 := by
      rw [coeff_natDegree]
      exact leadingCoeff_ne_zero.mpr hr
    exact hrLead hcoeff
  · have hmax : max (max p.natDegree q.natDegree)
        (max r.natDegree s.natDegree) = s.natDegree := by omega
    rw [hmax] at ht
    have hp0 := coeff_eq_zero_of_natDegree_lt hS.1
    have hq0 := coeff_eq_zero_of_natDegree_lt hS.2.1
    have hr0 := coeff_eq_zero_of_natDegree_lt hS.2.2
    have ht0 := coeff_eq_zero_of_natDegree_lt ht
    have hcoeff := congrArg (fun u : Polynomial F => u.coeff s.natDegree) hsum
    simp only [coeff_add, coeff_zero, hp0, hq0, hr0, ht0, zero_add,
      add_zero] at hcoeff
    have hsLead : s.coeff s.natDegree ≠ 0 := by
      rw [coeff_natDegree]
      exact leadingCoeff_ne_zero.mpr hs
    exact hsLead hcoeff

end PolynomialMaximum

/-- The two mismatch leading supports have the unique positive primitive
degree cone `(deg A,deg B,deg U)=(4n,5n,7n)`. -/
theorem mismatchDegreeCone46
    (a b u : ℕ) (ha : 0 < a) (hb : 0 < b) (hu : 0 < u)
    (hJ2 : MaxTie4 (3 * a) (a + u) (2 * b) (b + u))
    (hJ1 : MaxTie4 (2 * a + b) (a + 2 * b) (b + u) (2 * u)) :
    ∃ n : ℕ, 0 < n ∧ a = 4 * n ∧ b = 5 * n ∧ u = 7 * n := by
  have hratio : 5 * a = 4 * b ∧ 7 * a = 4 * u := by
    rcases hJ2 with h12 | h13 | h14 | h23 | h24 | h34 <;>
      rcases hJ1 with k12 | k13 | k14 | k23 | k24 | k34 <;>
      omega
  rcases hratio with ⟨hab, hau⟩
  have h4mul : 4 ∣ a * 5 := by
    refine ⟨b, ?_⟩
    omega
  have h4a : 4 ∣ a :=
    ((by norm_num : Nat.Coprime 4 5).dvd_mul_right).mp h4mul
  rcases h4a with ⟨n, hn⟩
  refine ⟨n, ?_, ?_, ?_, ?_⟩ <;> omega

/-- In the aligned `beta != 0` cone, the two leading equations force the
primitive degree ratio `(4,3,5)`. -/
theorem alignedBetaDegreeCone46
    (a x v : ℕ) (ha : 0 < a) (_hx : 0 < x) (_hv : 0 < v)
    (hPhi : x + v = 2 * a) (hR : 2 * v = a + 2 * x) :
    ∃ n : ℕ, 0 < n ∧ a = 4 * n ∧ x = 3 * n ∧ v = 5 * n := by
  have hratio : 3 * a = 4 * x := by omega
  have h4mul : 4 ∣ a * 3 := by
    refine ⟨x, ?_⟩
    omega
  have h4a : 4 ∣ a :=
    ((by norm_num : Nat.Coprime 4 3).dvd_mul_right).mp h4mul
  rcases h4a with ⟨n, hn⟩
  refine ⟨n, ?_, ?_, ?_, ?_⟩ <;> omega

/-- In the aligned `beta=0, delta != 0` cone, the two leading equations
force the primitive degree ratio `(4,1,3)`. -/
theorem alignedDeltaDegreeCone46
    (a x v : ℕ) (_ha : 0 < a) (hx : 0 < x) (_hv : 0 < v)
    (hPhi : x + v = a) (hR : 2 * v = a + 2 * x) :
    ∃ n : ℕ, 0 < n ∧ a = 4 * n ∧ x = n ∧ v = 3 * n := by
  refine ⟨x, hx, ?_, rfl, ?_⟩ <;> omega

/-- The mismatch cone's top one-form degree is strictly above every
competitor and is never zero. -/
theorem mismatchEtaDegreeGap46 (n : ℕ) (hn : 0 < n) :
    15 * n - 1 < 16 * n - 1 ∧ 0 < 16 * n - 1 := by
  omega

/-- The aligned `beta` cone's top one-form degree is strictly above the two
other shifted contributions and is never zero. -/
theorem alignedBetaEtaDegreeGap46 (n : ℕ) (hn : 0 < n) :
    9 * n - 1 < 12 * n - 1 ∧ 0 < 12 * n - 1 := by
  omega

/-- The aligned `delta` cone's top one-form degree is nonzero. -/
theorem alignedDeltaEtaDegreePositive46 (n : ℕ) (hn : 0 < n) :
    0 < 8 * n - 1 := by
  omega

section LeadingCoefficients

variable {F : Type*} [Field F] [CharZero F]

/-- The mismatch cone's two leading curve equations force the advertised
nonzero top coefficient of the pulled-back one-form. -/
theorem mismatch_leadingEtaCoefficient46
    (L a0 b0 u0 : F) (hL : L ≠ 0) (ha0 : a0 ≠ 0)
    (hlead : 5 * L * a0 ^ 3 = 24 * b0 * u0) :
    (15 / 64 : F) * L * a0 ^ 3 + (3 / 16 : F) * b0 * u0 =
        (35 / 128 : F) * L * a0 ^ 3 ∧
      (35 / 128 : F) * L * a0 ^ 3 ≠ 0 := by
  constructor
  · linear_combination (-1 / 128 : F) * hlead
  · exact mul_ne_zero (mul_ne_zero (by norm_num) hL) (pow_ne_zero 3 ha0)

/-- The unique top coefficient when only `B,U` vary in the mismatch branch
is nonzero in characteristic zero. -/
theorem mismatch_BU_leadingEtaCoefficient46
    (n : ℕ) (hn : 0 < n) (b0 : F) (hb0 : b0 ≠ 0) :
    (-3 / 4 : F) * (n : F) * b0 ^ 3 ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr hn.ne'))
    (pow_ne_zero 3 hb0)

end LeadingCoefficients

end Max11DegreeRoutes
