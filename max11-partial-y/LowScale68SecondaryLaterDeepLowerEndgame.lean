import LowScale68SecondaryLaterDeepLoadCascade
import LowScale68SecondaryDeepGapResidualEndgame

/-! # Later-deep lower `(6,8)` window `3n ≤ 2g ≤ 5n`

Tracked I4 already records the mixed walls `2g = 3n` and `2g = 5n` and
the ordinary `F₄` face between them.  This module extracts the matching
I3 face, proves that row-one is load-free after the extra `alpha`/`c`/`gamma`
cancellations, and closes the open interval `3n < 2g < 5n` to the ordinary
five-face `e = 0`, `a*b = 3d`.  The two walls keep mixed I4 together with
mixed `F₂`/`F₀`; they are not empty.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerEndgame68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Chamber arithmetic -/

theorem laterDeepLower_gap_lt_three_radius
    (n g : ℕ) (hn : 0 < n)
    (hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n) :
    g < 3 * n := by
  omega

theorem laterDeepLower_index_pos_three
    (n g : ℕ) (hn : 0 < n)
    (hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n) :
    0 < 3 * n - g := by
  omega

theorem laterDeepLower_index_pos_four
    (n g : ℕ) (hn : 0 < n)
    (hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n) :
    0 < 4 * n - g := by
  omega

theorem laterDeepLower_index_pos_five
    (n g : ℕ) (hn : 0 < n)
    (hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n) :
    0 < 5 * n - g := by
  omega

theorem laterDeepLower_index_pos_six
    (n g : ℕ) (hn : 0 < n)
    (hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n) :
    0 < 6 * n - g := by
  omega

theorem laterDeepLower_three_index_ne_zero
    (n g : ℕ) (hn : 0 < n)
    (hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n) :
    10 * n - 2 * g ≠ 0 := by
  omega

theorem laterDeepLower_rowZeroIndex_gt_fiftyNine
    (n g : ℕ) (hn : 10 ≤ n)
    (hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n) :
    59 < 13 * n - 2 * g - 1 := by
  omega

theorem laterDeepLower_gap_ne_six_radius
    (n g : ℕ) (hn : 0 < n)
    (hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n) :
    (g : k) - 6 * (n : k) ≠ 0 := by
  intro hzero
  have heq : (g : k) = 6 * (n : k) := sub_eq_zero.mp hzero
  have hnat : g = 6 * n := by exact_mod_cast heq
  omega

/-! ## I3 at `10n-2g` -/

set_option maxHeartbeats 2000000 in
theorem cubicHomogeneousFirstIntegralThreePolynomial68_laterDeepLowerCoeff
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g)
    (hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n)
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
theorem secondaryLoadInvariantThreePolynomial68_degree_lt_laterDeepLower
    (l beta gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g : ℕ) (hn : 0 < n) (hl : l = 0)
    (hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (secondaryLoadInvariantThreePolynomial68 l beta gamma delta epsilon zeta
      A B c D e).natDegree < 10 * n - 2 * g := by
  have hg3 : g < 3 * n := laterDeepLower_gap_lt_three_radius n g hn hwindow
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
theorem cubicFirstIntegralThreePolynomial68_laterDeepLowerCoeff
    (l beta gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g : ℕ) (hn : 0 < n) (hg : 0 < g) (hl : l = 0)
    (hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n)
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
      (secondaryLoadInvariantThreePolynomial68_degree_lt_laterDeepLower
        l beta gamma delta epsilon zeta A B c D e n g hn hl hwindow
        hA hB hc hD he), add_zero]
  simpa [hl] using
    cubicHomogeneousFirstIntegralThreePolynomial68_laterDeepLowerCoeff
      A B c D e n g hn hg hwindow hA hB hc hD he

theorem cubicFirstIntegralThreePolynomial68_laterDeepLower_forces_face
    (l beta gamma delta epsilon zeta i3 : k) (A B c D e : k[X])
    (n g : ℕ) (hn : 0 < n) (hg : 0 < g) (hl : l = 0)
    (hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (hI3 : cubicFirstIntegralThreePolynomial68
      l beta gamma delta epsilon zeta A B c D e = C i3) :
    firstSecondaryThree68
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
      (e.coeff (6 * n - g)) = 0 := by
  have hcoeff := congrArg (fun p : k[X] => p.coeff (10 * n - 2 * g)) hI3
  rw [cubicFirstIntegralThreePolynomial68_laterDeepLowerCoeff
    l beta gamma delta epsilon zeta A B c D e n g hn hg hl hwindow
    hA hB hc hD he] at hcoeff
  have hi : 10 * n - 2 * g ≠ 0 :=
    laterDeepLower_three_index_ne_zero n g hn hwindow
  simp only [coeff_C, if_neg hi] at hcoeff
  exact (mul_eq_zero.mp hcoeff).resolve_left (by norm_num)

/-! ## Degree bounds for the extra-cancelled one-forms -/

set_option maxHeartbeats 2000000 in
theorem cubicLoadVAlphaLowPolynomial68_degree_le_of_laterDeepLower
    (beta gamma delta epsilon eta : k)
    (A B c D : k[X]) (n g : ℕ)
    (hn : 0 < n) (hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g) :
    (cubicLoadVAlphaLowPolynomial68 beta gamma delta epsilon eta
      A B c D).natDegree ≤ 5 * n - g := by
  have hAB : ((-5 / 36 * beta : k) • (A * B)).natDegree ≤ 5 * n - g :=
    (natDegree_smul_le _ _).trans <|
      natDegree_mul_le.trans (by
        have := Nat.add_le_add hA hB
        omega)
  have hD' : ((5 / 6 * beta : k) • D).natDegree ≤ 5 * n - g :=
    (natDegree_smul_le _ _).trans hD
  have hc' : ((2 / 3 * gamma : k) • c).natDegree ≤ 5 * n - g :=
    (natDegree_smul_le _ _).trans (hc.trans (by omega))
  have hB' : ((1 / 2 * delta : k) • B).natDegree ≤ 5 * n - g :=
    (natDegree_smul_le _ _).trans (hB.trans (by omega))
  have hA' : ((1 / 3 * epsilon : k) • A).natDegree ≤ 5 * n - g :=
    (natDegree_smul_le _ _).trans (hA.trans (by omega))
  have hC : (C eta).natDegree ≤ 5 * n - g := by
    rw [natDegree_C]
    exact Nat.zero_le _
  simp only [cubicLoadVAlphaLowPolynomial68]
  refine (natDegree_add_le _ _).trans (max_le ?_ hC)
  refine (natDegree_add_le _ _).trans (max_le ?_ hA')
  refine (natDegree_add_le _ _).trans (max_le ?_ hB')
  refine (natDegree_add_le _ _).trans (max_le ?_ hc')
  exact (natDegree_add_le _ _).trans (max_le hAB hD')

set_option maxHeartbeats 2000000 in
theorem cubicLoadVAlphaRestPolynomial68_degree_le_of_laterDeepLower_le_two
    (alpha beta gamma delta epsilon eta : k) (A B c D e : k[X])
    (n g : ℕ) (hn : 0 < n)
    (hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n) (hgle : g ≤ 2 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadVAlphaRestPolynomial68 alpha beta gamma delta epsilon eta
      A B c D e).natDegree ≤ 6 * n - g := by
  have hAc : ((1 / 3 * alpha : k) • (A * c)).natDegree ≤ 6 * n - g :=
    (natDegree_smul_le _ _).trans <|
      natDegree_mul_le.trans (by
        have := Nat.add_le_add hA hc
        omega)
  have he' : (alpha • e).natDegree ≤ 6 * n - g :=
    (natDegree_smul_le _ _).trans he
  have hAB : ((5 / 36 * beta : k) • (A * B)).natDegree ≤ 6 * n - g :=
    (natDegree_smul_le _ _).trans <|
      natDegree_mul_le.trans (by
        have := Nat.add_le_add hA hB
        omega)
  have hD' : ((5 / 6 * beta : k) • D).natDegree ≤ 6 * n - g :=
    (natDegree_smul_le _ _).trans (hD.trans (by omega))
  have hA2 : ((1 / 9 * gamma : k) • A ^ 2).natDegree ≤ 6 * n - g :=
    (natDegree_smul_le _ _).trans <|
      (natDegree_pow_le (p := A) (n := 2)).trans (by
        have : A.natDegree * 2 ≤ (2 * n) * 2 := Nat.mul_le_mul_right 2 hA
        omega)
  have hc' : ((2 / 3 * gamma : k) • c).natDegree ≤ 6 * n - g :=
    (natDegree_smul_le _ _).trans (hc.trans (by omega))
  have hB' : ((1 / 2 * delta : k) • B).natDegree ≤ 6 * n - g :=
    (natDegree_smul_le _ _).trans (hB.trans (by omega))
  have hA' : ((1 / 3 * epsilon : k) • A).natDegree ≤ 6 * n - g :=
    (natDegree_smul_le _ _).trans (hA.trans (by omega))
  have hC : (C eta).natDegree ≤ 6 * n - g := by
    rw [natDegree_C]
    omega
  simp only [cubicLoadVAlphaRestPolynomial68]
  refine (natDegree_add_le _ _).trans (max_le ?_ hC)
  refine (natDegree_add_le _ _).trans (max_le ?_ hA')
  refine (natDegree_add_le _ _).trans (max_le ?_ hB')
  refine (natDegree_add_le _ _).trans (max_le ?_ hc')
  refine (natDegree_add_le _ _).trans (max_le ?_ hA2)
  refine (natDegree_add_le _ _).trans (max_le ?_ hD')
  refine (natDegree_sub_le _ _).trans (max_le ?_ hAB)
  exact (natDegree_add_le _ _).trans (max_le hAc he')

set_option maxHeartbeats 2000000 in
theorem cubicLoadVAlphaRestPolynomial68_degree_le_of_laterDeepLower_ge_two
    (alpha beta gamma delta epsilon eta : k) (A B c D e : k[X])
    (n g : ℕ) (hn : 0 < n)
    (hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n) (hgge : 2 * n ≤ g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadVAlphaRestPolynomial68 alpha beta gamma delta epsilon eta
      A B c D e).natDegree ≤ 4 * n := by
  have hAc : ((1 / 3 * alpha : k) • (A * c)).natDegree ≤ 4 * n :=
    (natDegree_smul_le _ _).trans <|
      natDegree_mul_le.trans (by
        have := Nat.add_le_add hA hc
        omega)
  have he' : (alpha • e).natDegree ≤ 4 * n :=
    (natDegree_smul_le _ _).trans (he.trans (by omega))
  have hAB : ((5 / 36 * beta : k) • (A * B)).natDegree ≤ 4 * n :=
    (natDegree_smul_le _ _).trans <|
      natDegree_mul_le.trans (by
        have := Nat.add_le_add hA hB
        omega)
  have hD' : ((5 / 6 * beta : k) • D).natDegree ≤ 4 * n :=
    (natDegree_smul_le _ _).trans (hD.trans (by omega))
  have hA2 : ((1 / 9 * gamma : k) • A ^ 2).natDegree ≤ 4 * n :=
    (natDegree_smul_le _ _).trans <|
      (natDegree_pow_le (p := A) (n := 2)).trans (by
        have : A.natDegree * 2 ≤ (2 * n) * 2 := Nat.mul_le_mul_right 2 hA
        omega)
  have hc' : ((2 / 3 * gamma : k) • c).natDegree ≤ 4 * n :=
    (natDegree_smul_le _ _).trans (hc.trans (by omega))
  have hB' : ((1 / 2 * delta : k) • B).natDegree ≤ 4 * n :=
    (natDegree_smul_le _ _).trans (hB.trans (by omega))
  have hA' : ((1 / 3 * epsilon : k) • A).natDegree ≤ 4 * n :=
    (natDegree_smul_le _ _).trans (hA.trans (by omega))
  have hC : (C eta).natDegree ≤ 4 * n := by
    rw [natDegree_C]
    exact Nat.zero_le _
  simp only [cubicLoadVAlphaRestPolynomial68]
  refine (natDegree_add_le _ _).trans (max_le ?_ hC)
  refine (natDegree_add_le _ _).trans (max_le ?_ hA')
  refine (natDegree_add_le _ _).trans (max_le ?_ hB')
  refine (natDegree_add_le _ _).trans (max_le ?_ hc')
  refine (natDegree_add_le _ _).trans (max_le ?_ hA2)
  refine (natDegree_add_le _ _).trans (max_le ?_ hD')
  refine (natDegree_sub_le _ _).trans (max_le ?_ hAB)
  exact (natDegree_add_le _ _).trans (max_le hAc he')

/-! ## Row-one load below `12n-2g-1` -/

set_option maxHeartbeats 6000000 in
theorem cubicLoadRowOneDeepGapRestPolynomial68_degree_lt_firstFace_of_laterDeepLower
    (alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g)
    (hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadRowOneDeepGapRestPolynomial68 alpha beta gamma delta
      epsilon zeta eta A B c D e).natDegree < 12 * n - 2 * g - 1 := by
  let Ur := cubicLoadUAlphaRestPolynomial68 beta gamma delta zeta A B c
  let Vr := cubicLoadVAlphaRestPolynomial68 alpha beta gamma delta epsilon
    eta A B c D e
  let Vlow := cubicLoadVAlphaLowPolynomial68 beta gamma delta epsilon eta
    A B c D
  let C0c := (1 / 3 : k) • A ^ 2
  let Ec := (1 / 27 : k) • A ^ 3
  let Er := (1 / 3 : k) • (A * c) + e
  let E := Ec + Er
  have hUr : Ur.natDegree ≤ 4 * n :=
    cubicLoadUAlphaRestPolynomial68_degree_le beta gamma delta zeta
      A B c n g hA hB hc
  have hVlow : Vlow.natDegree ≤ 5 * n - g :=
    cubicLoadVAlphaLowPolynomial68_degree_le_of_laterDeepLower
      beta gamma delta epsilon eta A B c D n g hn hwindow hA hB hc hD
  have hC0c : C0c.natDegree ≤ 4 * n := by
    simp only [C0c]
    compute_degree
    omega
  have hEc : Ec.natDegree ≤ 6 * n := by
    simp only [Ec]
    compute_degree
    omega
  have hEr : Er.natDegree ≤ 6 * n - g := by
    simp only [Er]
    compute_degree
    omega
  have hE : E.natDegree ≤ 6 * n :=
    (natDegree_add_le Ec Er).trans (max_le hEc (hEr.trans (by omega)))
  have hTrβ : (((5 / 6 * beta : k) • B + C epsilon)).natDegree ≤
      3 * n - g := by
    compute_degree
    omega
  have hbound (u v : ℕ) (hv : 0 < v)
      (hu : u + v - 1 < 12 * n - 2 * g - 1) :
      ∀ p q : k[X], p.natDegree ≤ u → q.natDegree ≤ v →
        (p * derivative q).natDegree < 12 * n - 2 * g - 1 :=
    fun p q hp hq =>
      deepGap_natDegree_mul_derivative_lt68 p q u v
        (12 * n - 2 * g - 1) hv hp hq hu
  have h1 : (Ur * derivative D).natDegree < 12 * n - 2 * g - 1 :=
    hbound (4 * n) (5 * n - g) (by omega) (by omega) Ur D hUr hD
  have h2 : ((alpha • c) * derivative Er).natDegree <
      12 * n - 2 * g - 1 :=
    hbound (4 * n - g) (6 * n - g) (by omega) (by omega)
      (alpha • c) Er ((natDegree_smul_le alpha c).trans hc) hEr
  have h3 : (((2 / 3 * gamma : k) • A) * derivative Er).natDegree <
      12 * n - 2 * g - 1 :=
    hbound (2 * n) (6 * n - g) (by omega) (by omega)
      ((2 / 3 * gamma : k) • A) Er
      ((natDegree_smul_le _ A).trans hA) hEr
  have h4 : (((5 / 6 * beta : k) • B + C epsilon) * derivative E).natDegree <
      12 * n - 2 * g - 1 :=
    hbound (3 * n - g) (6 * n) (by omega) (by omega)
      ((5 / 6 * beta : k) • B + C epsilon) E hTrβ hE
  have h5 : (C0c * derivative Vlow).natDegree < 12 * n - 2 * g - 1 :=
    hbound (4 * n) (5 * n - g) (by omega) (by omega) C0c Vlow hC0c hVlow
  have h6 : (c * derivative Vr).natDegree < 12 * n - 2 * g - 1 := by
    rcases le_total g (2 * n) with hgle | hnge
    · have hVr : Vr.natDegree ≤ 6 * n - g :=
        cubicLoadVAlphaRestPolynomial68_degree_le_of_laterDeepLower_le_two
          alpha beta gamma delta epsilon eta A B c D e n g hn hwindow
          hgle hA hB hc hD he
      exact hbound (4 * n - g) (6 * n - g) (by omega) (by omega) c Vr hc hVr
    · have hVr : Vr.natDegree ≤ 4 * n :=
        cubicLoadVAlphaRestPolynomial68_degree_le_of_laterDeepLower_ge_two
          alpha beta gamma delta epsilon eta A B c D e n g hn hwindow
          hnge hA hB hc hD he
      exact hbound (4 * n - g) (4 * n) (by omega) (by omega) c Vr hc hVr
  have h7 : (D * derivative Ur).natDegree < 12 * n - 2 * g - 1 :=
    hbound (5 * n - g) (4 * n) (by omega) (by omega) D Ur hD hUr
  have h2s := deepGap_natDegree_smul_lt68 (2 : k) h2
  have h3s := deepGap_natDegree_smul_lt68 (2 : k) h3
  have h4s := deepGap_natDegree_smul_lt68 (2 : k) h4
  have h5s := deepGap_natDegree_smul_lt68 (2 : k) h5
  have h6s := deepGap_natDegree_smul_lt68 (2 : k) h6
  change (Ur * derivative D +
      (2 : k) • ((alpha • c) * derivative Er) +
      (2 : k) • (((2 / 3 * gamma : k) • A) * derivative Er) +
      (2 : k) • (((5 / 6 * beta : k) • B + C epsilon) * derivative E) -
      (2 : k) • (C0c * derivative Vlow) -
      (2 : k) • (c * derivative Vr) -
      D * derivative Ur).natDegree < _
  exact deepGap_natDegree_sub_lt
    (deepGap_natDegree_sub_lt
      (deepGap_natDegree_sub_lt
        (deepGap_natDegree_add_lt
          (deepGap_natDegree_add_lt
            (deepGap_natDegree_add_lt h1 h2s) h3s) h4s) h5s) h6s) h7

set_option maxHeartbeats 2000000 in
theorem cubicLoadRowOnePolynomial68_degree_lt_firstFace_of_laterDeepLower
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hl : l = 0)
    (hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadRowOnePolynomial68 l alpha beta gamma delta epsilon zeta eta
      A B c D e).natDegree < 12 * n - 2 * g - 1 := by
  rw [cubicLoadRowOnePolynomial68_eq_alphaRest l alpha beta gamma delta
    epsilon zeta eta A B c D e hl,
    cubicLoadRowOneAlphaRestPolynomial68_eq_deepGapRest']
  exact cubicLoadRowOneDeepGapRestPolynomial68_degree_lt_firstFace_of_laterDeepLower
    alpha beta gamma delta epsilon zeta eta A B c D e n g
    hn hg hwindow hA hB hc hD he

/-! ## Row-two and row-zero loads after `beta = 0` on the open interval -/

set_option maxHeartbeats 2000000 in
theorem cubicLoadTAlphaRestPolynomial68_degree_le_of_laterDeepLower
    (alpha beta gamma epsilon : k) (A B c : k[X]) (n g : ℕ)
    (hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g) :
    (cubicLoadTAlphaRestPolynomial68 alpha beta gamma epsilon A B c).natDegree ≤
      max (4 * n - g) (2 * n) := by
  have hAc : (alpha • c).natDegree ≤ 4 * n - g :=
    (natDegree_smul_le alpha c).trans hc
  have hB' : ((5 / 6 * beta : k) • B).natDegree ≤ 4 * n - g :=
    (natDegree_smul_le _ B).trans (hB.trans (by omega))
  have hA' : ((2 / 3 * gamma : k) • A).natDegree ≤ 2 * n :=
    (natDegree_smul_le _ A).trans hA
  have hC : (C epsilon).natDegree ≤ 2 * n := by
    rw [natDegree_C]
    exact Nat.zero_le _
  have hleft : (alpha • c + (5 / 6 * beta : k) • B).natDegree ≤
      max (4 * n - g) (2 * n) :=
    ((natDegree_add_le _ _).trans (max_le hAc hB')).trans (le_max_left _ _)
  have hmid : ((2 / 3 * gamma : k) • A).natDegree ≤
      max (4 * n - g) (2 * n) :=
    hA'.trans (le_max_right _ _)
  have hC' : (C epsilon).natDegree ≤ max (4 * n - g) (2 * n) :=
    hC.trans (le_max_right _ _)
  simp only [cubicLoadTAlphaRestPolynomial68]
  refine (natDegree_add_le _ _).trans (max_le ?_ hC')
  exact (natDegree_add_le _ _).trans (max_le hleft hmid)

set_option maxHeartbeats 8000000 in
theorem cubicLoadRowTwoDeepGapRestPolynomial68_degree_lt_firstFace_of_laterDeepLower_open
    (alpha gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgt : n < g)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadRowTwoDeepGapRestPolynomial68 alpha gamma delta epsilon
      zeta eta A B c D e).natDegree < 11 * n - 2 * g - 1 := by
  have hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n :=
    ⟨le_of_lt hopen.1, le_of_lt hopen.2⟩
  let Uc := cubicLoadUAlphaCorePolynomial68 alpha D
  let Ur := cubicLoadUAlphaRestPolynomial68 0 gamma delta zeta A B c
  let Tr := cubicLoadTAlphaRestPolynomial68 alpha 0 gamma epsilon A B c
  let Sc := cubicLoadSAlphaCorePolynomial68 alpha B
  let Sr := (C delta : k[X])
  let Vr := cubicLoadVAlphaRestPolynomial68 alpha 0 gamma delta epsilon
    eta A B c D e
  let C0c := (1 / 3 : k) • A ^ 2
  let C0 := C0c + c
  let Ec := (1 / 27 : k) • A ^ 3
  let Er := (1 / 3 : k) • (A * c) + e
  let E := Ec + Er
  let U := Uc + Ur
  have hUc : Uc.natDegree ≤ 5 * n - g := by
    simp only [Uc, cubicLoadUAlphaCorePolynomial68]
    exact (natDegree_smul_le alpha D).trans hD
  have hUr : Ur.natDegree ≤ 2 * n :=
    cubicLoadUAlphaRestPolynomial68_degree_le_of_beta gamma delta zeta
      A B c n g hgt hA hB hc
  have hTr : Tr.natDegree ≤ max (4 * n - g) (2 * n) :=
    cubicLoadTAlphaRestPolynomial68_degree_le_of_laterDeepLower
      alpha 0 gamma epsilon A B c n g hwindow hA hB hc
  have hSc : Sc.natDegree ≤ 3 * n - g := by
    simp only [Sc, cubicLoadSAlphaCorePolynomial68]
    exact (natDegree_smul_le alpha B).trans hB
  have hSr : Sr.natDegree ≤ 0 := by
    simp [Sr, natDegree_C]
  have hC0c : C0c.natDegree ≤ 4 * n := by
    simp only [C0c]
    compute_degree
    omega
  have hC0 : C0.natDegree ≤ 4 * n := by
    simp only [C0]
    compute_degree
    omega
  have hU : U.natDegree ≤ 5 * n - g :=
    (natDegree_add_le Uc Ur).trans (max_le hUc (hUr.trans (by omega)))
  have hEc : Ec.natDegree ≤ 6 * n := by
    simp only [Ec]
    compute_degree
    omega
  have hEr : Er.natDegree ≤ 6 * n - g := by
    simp only [Er]
    compute_degree
    omega
  have hE : E.natDegree ≤ 6 * n :=
    (natDegree_add_le Ec Er).trans (max_le hEc (hEr.trans (by omega)))
  have hbound (u v : ℕ) (hv : 0 < v)
      (hu : u + v - 1 < 11 * n - 2 * g - 1) :
      ∀ p q : k[X], p.natDegree ≤ u → q.natDegree ≤ v →
        (p * derivative q).natDegree < 11 * n - 2 * g - 1 :=
    fun p q hp hq =>
      deepGap_natDegree_mul_derivative_lt68 p q u v
        (11 * n - 2 * g - 1) hv hp hq hu
  have h1 : (Ur * derivative C0).natDegree < 11 * n - 2 * g - 1 :=
    hbound (2 * n) (4 * n) (by omega) (by omega) Ur C0 hUr hC0
  have h2 : (Uc * derivative c).natDegree < 11 * n - 2 * g - 1 :=
    hbound (5 * n - g) (4 * n - g) (by omega) (by omega) Uc c hUc hc
  have h3 : (Tr * derivative D).natDegree < 11 * n - 2 * g - 1 := by
    rcases le_total g (2 * n) with hgle | hnge
    · have hTr' : Tr.natDegree ≤ 4 * n - g :=
        hTr.trans (by rw [max_eq_left (by omega)])
      exact hbound (4 * n - g) (5 * n - g) (by omega) (by omega) Tr D hTr' hD
    · have hTr' : Tr.natDegree ≤ 2 * n :=
        hTr.trans (by rw [max_eq_right (by omega)])
      exact hbound (2 * n) (5 * n - g) (by omega) (by omega) Tr D hTr' hD
  have h4 : (Sr * derivative E).natDegree < 11 * n - 2 * g - 1 :=
    hbound 0 (6 * n) (by omega) (by omega) Sr E hSr hE
  have h5 : (Sc * derivative Er).natDegree < 11 * n - 2 * g - 1 :=
    hbound (3 * n - g) (6 * n - g) (by omega) (by omega) Sc Er hSc hEr
  have h6 : (B * derivative Vr).natDegree < 11 * n - 2 * g - 1 := by
    rcases le_total g (2 * n) with hgle | hnge
    · have hVr : Vr.natDegree ≤ 6 * n - g :=
        cubicLoadVAlphaRestPolynomial68_degree_le_of_laterDeepLower_le_two
          alpha 0 gamma delta epsilon eta A B c D e n g hn hwindow
          hgle hA hB hc hD he
      exact hbound (3 * n - g) (6 * n - g) (by omega) (by omega) B Vr hB hVr
    · have hVr : Vr.natDegree ≤ 4 * n :=
        cubicLoadVAlphaRestPolynomial68_degree_le_of_laterDeepLower_ge_two
          alpha 0 gamma delta epsilon eta A B c D e n g hn hwindow
          hnge hA hB hc hD he
      exact hbound (3 * n - g) (4 * n) (by omega) (by omega) B Vr hB hVr
  have h7 : (c * derivative U).natDegree < 11 * n - 2 * g - 1 :=
    hbound (4 * n - g) (5 * n - g) (by omega) (by omega) c U hc hU
  have h8 : (C0c * derivative Ur).natDegree < 11 * n - 2 * g - 1 :=
    hbound (4 * n) (2 * n) (by omega) (by omega) C0c Ur hC0c hUr
  have h9 : (D * derivative Tr).natDegree < 11 * n - 2 * g - 1 := by
    rcases le_total g (2 * n) with hgle | hnge
    · have hTr' : Tr.natDegree ≤ 4 * n - g :=
        hTr.trans (by rw [max_eq_left (by omega)])
      exact hbound (5 * n - g) (4 * n - g) (by omega) (by omega) D Tr hD hTr'
    · have hTr' : Tr.natDegree ≤ 2 * n :=
        hTr.trans (by rw [max_eq_right (by omega)])
      exact hbound (5 * n - g) (2 * n) (by omega) (by omega) D Tr hD hTr'
  have h3s := deepGap_natDegree_smul_lt68 (2 : k) h3
  have h4s := deepGap_natDegree_smul_lt68 (3 : k) h4
  have h5s := deepGap_natDegree_smul_lt68 (3 : k) h5
  have h6s := deepGap_natDegree_smul_lt68 (3 : k) h6
  have h7s := deepGap_natDegree_smul_lt68 (2 : k) h7
  have h8s := deepGap_natDegree_smul_lt68 (2 : k) h8
  change (Ur * derivative C0 + Uc * derivative c +
      (2 : k) • (Tr * derivative D) +
      (3 : k) • (Sr * derivative E) +
      (3 : k) • (Sc * derivative Er) -
      (3 : k) • (B * derivative Vr) -
      (2 : k) • (c * derivative U) -
      (2 : k) • (C0c * derivative Ur) -
      D * derivative Tr).natDegree < _
  exact deepGap_natDegree_sub_lt
    (deepGap_natDegree_sub_lt
      (deepGap_natDegree_sub_lt
        (deepGap_natDegree_sub_lt
          (deepGap_natDegree_add_lt
            (deepGap_natDegree_add_lt
              (deepGap_natDegree_add_lt
                (deepGap_natDegree_add_lt h1 h2) h3s) h4s) h5s) h6s) h7s) h8s) h9

set_option maxHeartbeats 2000000 in
theorem cubicLoadRowTwoPolynomial68_degree_lt_firstFace_of_laterDeepLower_open
    (alpha gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgt : n < g)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadRowTwoPolynomial68 0 alpha 0 gamma delta epsilon zeta eta
      A B c D e).natDegree < 11 * n - 2 * g - 1 := by
  rw [cubicLoadRowTwoPolynomial68_eq_deepGapRest_of_beta']
  exact cubicLoadRowTwoDeepGapRestPolynomial68_degree_lt_firstFace_of_laterDeepLower_open
    alpha gamma delta epsilon zeta eta A B c D e n g
    hn hg hgt hopen hA hB hc hD he

set_option maxHeartbeats 4000000 in
theorem cubicLoadRowZeroDeepGapRestPolynomial68_degree_lt_firstFace_of_laterDeepLower_open
    (alpha gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgt : n < g)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadRowZeroDeepGapRestPolynomial68 alpha gamma delta epsilon
      zeta eta A B c D e).natDegree < 13 * n - 2 * g - 1 := by
  have hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n :=
    ⟨le_of_lt hopen.1, le_of_lt hopen.2⟩
  let Uc := cubicLoadUAlphaCorePolynomial68 alpha D
  let Ur := cubicLoadUAlphaRestPolynomial68 0 gamma delta zeta A B c
  let Vr := cubicLoadVAlphaRestPolynomial68 alpha 0 gamma delta epsilon
    eta A B c D e
  let Ec := (1 / 27 : k) • A ^ 3
  let Er := (1 / 3 : k) • (A * c) + e
  let E := Ec + Er
  have hUc : Uc.natDegree ≤ 5 * n - g := by
    simp only [Uc, cubicLoadUAlphaCorePolynomial68]
    exact (natDegree_smul_le alpha D).trans hD
  have hUr : Ur.natDegree ≤ 2 * n :=
    cubicLoadUAlphaRestPolynomial68_degree_le_of_beta gamma delta zeta
      A B c n g hgt hA hB hc
  have hEc : Ec.natDegree ≤ 6 * n := by
    simp only [Ec]
    compute_degree
    omega
  have hEr : Er.natDegree ≤ 6 * n - g := by
    simp only [Er]
    compute_degree
    omega
  have hE : E.natDegree ≤ 6 * n :=
    (natDegree_add_le Ec Er).trans (max_le hEc (hEr.trans (by omega)))
  have hbound (u v : ℕ) (hv : 0 < v)
      (hu : u + v - 1 < 13 * n - 2 * g - 1) :
      ∀ p q : k[X], p.natDegree ≤ u → q.natDegree ≤ v →
        (p * derivative q).natDegree < 13 * n - 2 * g - 1 :=
    fun p q hp hq =>
      deepGap_natDegree_mul_derivative_lt68 p q u v
        (13 * n - 2 * g - 1) hv hp hq hu
  have h1 : (Ur * derivative E).natDegree < 13 * n - 2 * g - 1 :=
    hbound (2 * n) (6 * n) (by omega) (by omega) Ur E hUr hE
  have h2 : (Uc * derivative Er).natDegree < 13 * n - 2 * g - 1 :=
    hbound (5 * n - g) (6 * n - g) (by omega) (by omega) Uc Er hUc hEr
  have h3 : (D * derivative Vr).natDegree < 13 * n - 2 * g - 1 := by
    rcases le_total g (2 * n) with hgle | hnge
    · have hVr : Vr.natDegree ≤ 6 * n - g :=
        cubicLoadVAlphaRestPolynomial68_degree_le_of_laterDeepLower_le_two
          alpha 0 gamma delta epsilon eta A B c D e n g hn hwindow
          hgle hA hB hc hD he
      exact hbound (5 * n - g) (6 * n - g) (by omega) (by omega) D Vr hD hVr
    · have hVr : Vr.natDegree ≤ 4 * n :=
        cubicLoadVAlphaRestPolynomial68_degree_le_of_laterDeepLower_ge_two
          alpha 0 gamma delta epsilon eta A B c D e n g hn hwindow
          hnge hA hB hc hD he
      exact hbound (5 * n - g) (4 * n) (by omega) (by omega) D Vr hD hVr
  change (Ur * derivative E + Uc * derivative Er -
      D * derivative Vr).natDegree < _
  exact deepGap_natDegree_sub_lt (deepGap_natDegree_add_lt h1 h2) h3

set_option maxHeartbeats 2000000 in
theorem cubicLoadRowZeroPolynomial68_degree_lt_firstFace_of_laterDeepLower_open
    (alpha gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgt : n < g)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadRowZeroPolynomial68 0 alpha 0 gamma delta epsilon zeta eta
      A B c D e).natDegree < 13 * n - 2 * g - 1 := by
  rw [cubicLoadRowZeroPolynomial68_eq_deepGapRest_of_beta']
  exact cubicLoadRowZeroDeepGapRestPolynomial68_degree_lt_firstFace_of_laterDeepLower_open
    alpha gamma delta epsilon zeta eta A B c D e n g
    hn hg hgt hopen hA hB hc hD he

/-! ## Homogeneous one-form coefficients on `3n ≤ 2g ≤ 5n` -/

set_option maxHeartbeats 2000000 in
theorem firstSecondaryCoreRowTwoPolynomial68_coeff_of_laterDeepLower
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g)
    (hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n)
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
  have hA2deg : (A ^ 2).natDegree ≤ 4 * n := by compute_degree; omega
  have hA2coeff : (A ^ 2).coeff (4 * n) = A.coeff (2 * n) ^ 2 := by
    have h := coeff_pow_at_bound68 A (2 * n) 2 hA
    have hi : 2 * (2 * n) = 4 * n := by omega
    simpa only [hi] using h
  have h1 : (A ^ 2 * B * derivative c).coeff (11 * n - 2 * g - 1) =
      A.coeff (2 * n) ^ 2 * B.coeff (3 * n - g) *
        c.coeff (4 * n - g) * ((4 * n - g : ℕ) : k) := by
    have h := coeff_mul_mul_derivative_at_bounds68 (A ^ 2) B c
      (4 * n) (3 * n - g) (4 * n - g) (by omega) hA2deg hB hc
    have hi : 4 * n + (3 * n - g) + (4 * n - g) - 1 =
        11 * n - 2 * g - 1 := by omega
    rw [hi, hA2coeff] at h
    exact h
  have h2 : (A ^ 2 * c * derivative B).coeff (11 * n - 2 * g - 1) =
      A.coeff (2 * n) ^ 2 * c.coeff (4 * n - g) *
        B.coeff (3 * n - g) * ((3 * n - g : ℕ) : k) := by
    have h := coeff_mul_mul_derivative_at_bounds68 (A ^ 2) c B
      (4 * n) (4 * n - g) (3 * n - g) (by omega) hA2deg hc hB
    have hi : 4 * n + (4 * n - g) + (3 * n - g) - 1 =
        11 * n - 2 * g - 1 := by omega
    rw [hi, hA2coeff] at h
    exact h
  have h3 : (A * B * c * derivative A).coeff (11 * n - 2 * g - 1) =
      A.coeff (2 * n) * B.coeff (3 * n - g) *
        c.coeff (4 * n - g) * A.coeff (2 * n) * ((2 * n : ℕ) : k) := by
    have h := coeff_mul_mul_mul_derivative_at_bounds68 A B c A
      (2 * n) (3 * n - g) (4 * n - g) (2 * n) (by omega) hA hB hc hA
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
    rw [Nat.cast_sub hg3]; push_cast; ring
  have hcast4 : (((4 * n - g : ℕ) : k)) = (n : k) * 4 - (g : k) := by
    rw [Nat.cast_sub hg4]; push_cast; ring
  have hcast5 : (((5 * n - g : ℕ) : k)) = (n : k) * 5 - (g : k) := by
    rw [Nat.cast_sub hg5]; push_cast; ring
  have hcast6 : (((6 * n - g : ℕ) : k)) = (n : k) * 6 - (g : k) := by
    rw [Nat.cast_sub hg6]; push_cast; ring
  rw [hcast3, hcast4, hcast5, hcast6]
  push_cast
  simp only [firstSecondaryTwo68]
  ring

set_option maxHeartbeats 2000000 in
theorem cubicHomogeneousRowTwoPolynomial68_secondaryCoeff_of_laterDeepLower
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g)
    (hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n)
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
  exact firstSecondaryCoreRowTwoPolynomial68_coeff_of_laterDeepLower
    A B c D e n g hn hg hwindow hA hB hc hD he

set_option maxHeartbeats 2000000 in
theorem firstSecondaryCoreRowOnePolynomial68_coeff_of_laterDeepLower
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g)
    (hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n)
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
  have hA2deg : (A ^ 2).natDegree ≤ 4 * n := by compute_degree; omega
  have hA3deg : (A ^ 3).natDegree ≤ 6 * n := by compute_degree; omega
  have hB2deg : (B ^ 2).natDegree ≤ 6 * n - 2 * g := by compute_degree; omega
  have hD2deg : (D ^ 2).natDegree ≤ 10 * n - 2 * g := by compute_degree; omega
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
  have h2 : (A ^ 2 * B ^ 2 * derivative A).coeff (12 * n - 2 * g - 1) =
      A.coeff (2 * n) ^ 2 * B.coeff (3 * n - g) ^ 2 *
        A.coeff (2 * n) * ((2 * n : ℕ) : k) := by
    have h := coeff_mul_mul_derivative_at_bounds68 (A ^ 2) (B ^ 2) A
      (4 * n) (6 * n - 2 * g) (2 * n) (by omega) hA2deg hB2deg hA
    have hi : 4 * n + (6 * n - 2 * g) + 2 * n - 1 =
        12 * n - 2 * g - 1 := by omega
    rw [hi, hA2, hB2] at h
    exact h
  have h3 : (A ^ 2 * B * derivative D).coeff (12 * n - 2 * g - 1) =
      A.coeff (2 * n) ^ 2 * B.coeff (3 * n - g) *
        D.coeff (5 * n - g) * ((5 * n - g : ℕ) : k) := by
    have h := coeff_mul_mul_derivative_at_bounds68 (A ^ 2) B D
      (4 * n) (3 * n - g) (5 * n - g) (by omega) hA2deg hB hD
    have hi : 4 * n + (3 * n - g) + (5 * n - g) - 1 =
        12 * n - 2 * g - 1 := by omega
    rw [hi, hA2] at h
    exact h
  have h4 : (A ^ 2 * D * derivative B).coeff (12 * n - 2 * g - 1) =
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
    rw [Nat.cast_sub hg3]; push_cast; rfl
  have hcast4 : (((4 * n - g : ℕ) : k)) = 4 * (n : k) - (g : k) := by
    rw [Nat.cast_sub hg4]; push_cast; rfl
  have hcast5 : (((5 * n - g : ℕ) : k)) = 5 * (n : k) - (g : k) := by
    rw [Nat.cast_sub hg5]; push_cast; rfl
  have hcast6 : (((6 * n - g : ℕ) : k)) = 6 * (n : k) - (g : k) := by
    rw [Nat.cast_sub hg6]; push_cast; rfl
  rw [hcast3, hcast4, hcast5, hcast6]
  push_cast
  simp only [firstSecondaryOne68]
  ring

set_option maxHeartbeats 2000000 in
theorem cubicHomogeneousRowOnePolynomial68_secondaryCoeff_of_laterDeepLower
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g)
    (hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n)
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
  exact firstSecondaryCoreRowOnePolynomial68_coeff_of_laterDeepLower
    A B c D e n g hn hg hwindow hA hB hc hD he

set_option maxHeartbeats 2000000 in
theorem firstSecondaryCoreRowZeroPolynomial68_coeff_of_laterDeepLower
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g)
    (hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n)
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
  have hA2deg : (A ^ 2).natDegree ≤ 4 * n := by compute_degree; omega
  have hA2 : (A ^ 2).coeff (4 * n) = A.coeff (2 * n) ^ 2 := by
    have h := coeff_pow_at_bound68 A (2 * n) 2 hA
    have hi : 2 * (2 * n) = 4 * n := by omega
    simpa only [hi] using h
  have h1 : (A ^ 2 * B * c * derivative A).coeff (13 * n - 2 * g - 1) =
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
  have h2 : (A * D * c * derivative A).coeff (13 * n - 2 * g - 1) =
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
theorem cubicHomogeneousRowZeroPolynomial68_secondaryCoeff_of_laterDeepLower
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g)
    (hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n)
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
  exact firstSecondaryCoreRowZeroPolynomial68_coeff_of_laterDeepLower
    A B c D e n g hn hg hwindow hA hB hc hD he

/-! ## Integrated one-form coefficients -/

set_option maxHeartbeats 3000000 in
theorem integratedLowerRowTwoPolynomial68_secondaryCoeff_of_laterDeepLower_open
    (alpha gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgt : n < g)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (lowerRowTwoPolynomial68
      (integratedSPolynomial68 0 alpha 0 delta A B
        ((1 / 3 : k) • A ^ 2 + c) D)
      (integratedTPolynomial68 0 alpha 0 gamma epsilon A B
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      (integratedUPolynomial68 0 alpha 0 gamma delta zeta A B
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      (integratedVPolynomial68 0 alpha 0 gamma delta epsilon eta A B
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      B ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)).coeff
          (11 * n - 2 * g - 1) =
      (8 / 27 : k) * firstSecondaryTwo68 (n : k) (g : k)
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
        (e.coeff (6 * n - g)) := by
  have hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n :=
    ⟨le_of_lt hopen.1, le_of_lt hopen.2⟩
  have hcoords := integratedPolynomial68_cubicCoordinates
    0 alpha 0 gamma delta epsilon zeta eta A B c D e
  rw [hcoords.s_eq, hcoords.t_eq, hcoords.u_eq, hcoords.v_eq,
    cubicRowTwoPolynomial68_split, coeff_add,
    coeff_eq_zero_of_natDegree_lt
      (cubicLoadRowTwoPolynomial68_degree_lt_firstFace_of_laterDeepLower_open
        alpha gamma delta epsilon zeta eta A B c D e n g
        hn hg hgt hopen hA hB hc hD he), add_zero]
  exact cubicHomogeneousRowTwoPolynomial68_secondaryCoeff_of_laterDeepLower
    A B c D e n g hn hg hwindow hA hB hc hD he

set_option maxHeartbeats 3000000 in
theorem integratedLowerRowOnePolynomial68_secondaryCoeff_of_laterDeepLower
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hl : l = 0)
    (hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n)
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
      (cubicLoadRowOnePolynomial68_degree_lt_firstFace_of_laterDeepLower
        l alpha beta gamma delta epsilon zeta eta A B c D e n g
        hn hg hl hwindow hA hB hc hD he), add_zero]
  exact cubicHomogeneousRowOnePolynomial68_secondaryCoeff_of_laterDeepLower
    A B c D e n g hn hg hwindow hA hB hc hD he

set_option maxHeartbeats 3000000 in
theorem integratedLowerRowZeroPolynomial68_secondaryCoeff_of_laterDeepLower_open
    (alpha gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgt : n < g)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (lowerRowZeroPolynomial68
      (integratedUPolynomial68 0 alpha 0 gamma delta zeta A B
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      (integratedVPolynomial68 0 alpha 0 gamma delta epsilon eta A B
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      D ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)).coeff
        (13 * n - 2 * g - 1) =
      (8 / 81 : k) * (n : k) * A.coeff (2 * n) *
        firstSecondaryZero68
          (A.coeff (2 * n)) (B.coeff (3 * n - g))
          (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
          (e.coeff (6 * n - g)) := by
  have hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n :=
    ⟨le_of_lt hopen.1, le_of_lt hopen.2⟩
  have hcoords := integratedPolynomial68_cubicCoordinates
    0 alpha 0 gamma delta epsilon zeta eta A B c D e
  rw [hcoords.u_eq, hcoords.v_eq, cubicRowZeroPolynomial68_split, coeff_add,
    coeff_eq_zero_of_natDegree_lt
      (cubicLoadRowZeroPolynomial68_degree_lt_firstFace_of_laterDeepLower_open
        alpha gamma delta epsilon zeta eta A B c D e n g
        hn hg hgt hopen hA hB hc hD he), add_zero]
  exact cubicHomogeneousRowZeroPolynomial68_secondaryCoeff_of_laterDeepLower
    A B c D e n g hn hg hwindow hA hB hc hD he

theorem laterDeepLower_radius_lt_gap
    (n g : ℕ) (hn : 0 < n)
    (hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n) :
    n < g := by
  omega

/-! ## Packaged five-face on the open interval -/

set_option maxHeartbeats 4000000 in
theorem polynomialSecondaryFace68_of_laterDeepLower_open
    (alpha gamma delta epsilon zeta eta i4 i3 : k)
    (A B C0 c D E e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (ha : A.coeff (2 * n) ≠ 0)
    (hC0 : C0 = (1 / 3 : k) • A ^ 2 + c)
    (hE0 : E = (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)
    (hI4 : firstIntegralFourPolynomial68 0 0 gamma delta epsilon zeta
      A B C0 D E = C i4)
    (hI3 : firstIntegralThreePolynomial68 0 0 gamma delta epsilon zeta
      A B C0 D E = C i3)
    (hrowTwo : lowerRowTwoPolynomial68
      (integratedSPolynomial68 0 alpha 0 delta A B C0 D)
      (integratedTPolynomial68 0 alpha 0 gamma epsilon A B C0 D E)
      (integratedUPolynomial68 0 alpha 0 gamma delta zeta A B C0 D E)
      (integratedVPolynomial68 0 alpha 0 gamma delta epsilon eta
        A B C0 D E) B C0 D E = 0)
    (hrowOne : lowerRowOnePolynomial68
      (integratedTPolynomial68 0 alpha 0 gamma epsilon A B C0 D E)
      (integratedUPolynomial68 0 alpha 0 gamma delta zeta A B C0 D E)
      (integratedVPolynomial68 0 alpha 0 gamma delta epsilon eta
        A B C0 D E) C0 D E = 0)
    (hrowZero : (lowerRowZeroPolynomial68
      (integratedUPolynomial68 0 alpha 0 gamma delta zeta A B C0 D E)
      (integratedVPolynomial68 0 alpha 0 gamma delta epsilon eta
        A B C0 D E) D E).coeff (13 * n - 2 * g - 1) = 0) :
    FirstSecondaryFace68 (n : k) (g : k)
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
      (e.coeff (6 * n - g)) := by
  have hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n :=
    ⟨le_of_lt hopen.1, le_of_lt hopen.2⟩
  have hgt : n < g := laterDeepLower_radius_lt_gap n g hn hwindow
  have hI4c : cubicFirstIntegralFourPolynomial68 0 0 gamma delta epsilon zeta
      A B c D e = C i4 := by
    rw [← hI4, hC0, hE0, firstIntegralFourPolynomial68_cubicCoordinates]
  have hI3c : cubicFirstIntegralThreePolynomial68 0 0 gamma delta epsilon zeta
      A B c D e = C i3 := by
    rw [← hI3, hC0, hE0, firstIntegralThreePolynomial68_cubicCoordinates]
  have hfour :=
    cubicFirstIntegralFourPolynomial68_laterSecondary_forces_face
      gamma delta epsilon zeta i4 A B c D e n g hn hg hopen
      hA hB hc hD he hI4c
  have hthree :=
    cubicFirstIntegralThreePolynomial68_laterDeepLower_forces_face
      0 0 gamma delta epsilon zeta i3 A B c D e n g hn hg rfl hwindow
      hA hB hc hD he hI3c
  have h2 := hrowTwo
  rw [hC0, hE0] at h2
  have htwo := congrArg
    (fun p : k[X] => p.coeff (11 * n - 2 * g - 1)) h2
  rw [integratedLowerRowTwoPolynomial68_secondaryCoeff_of_laterDeepLower_open
    alpha gamma delta epsilon zeta eta A B c D e n g
    hn hg hgt hopen hA hB hc hD he] at htwo
  simp only [coeff_zero] at htwo
  have htwo0 : firstSecondaryTwo68 (n : k) (g : k)
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
      (e.coeff (6 * n - g)) = 0 :=
    (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  have h1 := hrowOne
  rw [hC0, hE0] at h1
  have hone := congrArg
    (fun p : k[X] => p.coeff (12 * n - 2 * g - 1)) h1
  rw [integratedLowerRowOnePolynomial68_secondaryCoeff_of_laterDeepLower
    0 alpha 0 gamma delta epsilon zeta eta A B c D e n g
    hn hg rfl hwindow hA hB hc hD he] at hone
  simp only [coeff_zero] at hone
  have hone0 : firstSecondaryOne68 (n : k) (g : k)
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
      (e.coeff (6 * n - g)) = 0 :=
    (mul_eq_zero.mp hone).resolve_left (by norm_num)
  have h0 := hrowZero
  rw [hC0, hE0] at h0
  rw [integratedLowerRowZeroPolynomial68_secondaryCoeff_of_laterDeepLower_open
    alpha gamma delta epsilon zeta eta A B c D e n g
    hn hg hgt hopen hA hB hc hD he] at h0
  have hncast : (n : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hfactor : (8 / 81 : k) * (n : k) * A.coeff (2 * n) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hncast) ha
  have hzero0 : firstSecondaryZero68
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
      (e.coeff (6 * n - g)) = 0 :=
    (mul_eq_zero.mp h0).resolve_left hfactor
  exact ⟨hfour, hthree, htwo0, hone0, hzero0⟩

theorem polynomialSecondaryClassified68_of_laterDeepLower_open
    (alpha gamma delta epsilon zeta eta i4 i3 : k)
    (A B C0 c D E e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (ha : A.coeff (2 * n) ≠ 0)
    (hC0 : C0 = (1 / 3 : k) • A ^ 2 + c)
    (hE0 : E = (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)
    (hI4 : firstIntegralFourPolynomial68 0 0 gamma delta epsilon zeta
      A B C0 D E = C i4)
    (hI3 : firstIntegralThreePolynomial68 0 0 gamma delta epsilon zeta
      A B C0 D E = C i3)
    (hrowTwo : lowerRowTwoPolynomial68
      (integratedSPolynomial68 0 alpha 0 delta A B C0 D)
      (integratedTPolynomial68 0 alpha 0 gamma epsilon A B C0 D E)
      (integratedUPolynomial68 0 alpha 0 gamma delta zeta A B C0 D E)
      (integratedVPolynomial68 0 alpha 0 gamma delta epsilon eta
        A B C0 D E) B C0 D E = 0)
    (hrowOne : lowerRowOnePolynomial68
      (integratedTPolynomial68 0 alpha 0 gamma epsilon A B C0 D E)
      (integratedUPolynomial68 0 alpha 0 gamma delta zeta A B C0 D E)
      (integratedVPolynomial68 0 alpha 0 gamma delta epsilon eta
        A B C0 D E) C0 D E = 0)
    (hrowZero : (lowerRowZeroPolynomial68
      (integratedUPolynomial68 0 alpha 0 gamma delta zeta A B C0 D E)
      (integratedVPolynomial68 0 alpha 0 gamma delta epsilon eta
        A B C0 D E) D E).coeff (13 * n - 2 * g - 1) = 0) :
    e.coeff (6 * n - g) = 0 ∧
      A.coeff (2 * n) * B.coeff (3 * n - g) =
        3 * D.coeff (5 * n - g) := by
  have hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n :=
    ⟨le_of_lt hopen.1, le_of_lt hopen.2⟩
  exact firstSecondaryFace68_classify (n : k) (g : k)
    (A.coeff (2 * n)) (B.coeff (3 * n - g))
    (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
    (e.coeff (6 * n - g)) ha
    (laterDeepLower_gap_ne_six_radius n g hn hwindow)
    (polynomialSecondaryFace68_of_laterDeepLower_open
      alpha gamma delta epsilon zeta eta i4 i3
      A B C0 c D E e n g hn hg hopen hA hB hc hD he ha hC0 hE0
      hI4 hI3 hrowTwo hrowOne hrowZero)

theorem secondaryDDefectPolynomial68_degree_lt_of_laterDeepLower
    (A B D : k[X]) (n g : ℕ) (hn : 0 < n)
    (hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (hface : A.coeff (2 * n) * B.coeff (3 * n - g) =
      3 * D.coeff (5 * n - g)) :
    (secondaryDDefectPolynomial68 A B D).natDegree < 5 * n - g := by
  have hg3 : g ≤ 3 * n := by omega
  have hindex : 2 * n + (3 * n - g) = 5 * n - g := by
    rw [← Nat.add_sub_assoc hg3]
    omega
  have hdegree : (secondaryDDefectPolynomial68 A B D).natDegree ≤
      5 * n - g := by
    simp only [secondaryDDefectPolynomial68]
    refine (natDegree_sub_le _ _).trans ?_
    rw [sup_le_iff]
    constructor
    · exact hD
    · have hmul := (natDegree_mul_le (p := A) (q := B)).trans
        (Nat.add_le_add hA hB)
      have hsmul := (natDegree_smul_le (1 / 3 : k) (A * B)).trans hmul
      rwa [hindex] at hsmul
  have hAB := coeff_mul_at_bounds68 A B (2 * n) (3 * n - g) hA hB
  rw [hindex] at hAB
  have hcoeff : (secondaryDDefectPolynomial68 A B D).coeff
      (5 * n - g) = 0 := by
    simp only [secondaryDDefectPolynomial68, coeff_sub, coeff_smul,
      smul_eq_mul]
    rw [hAB]
    linear_combination (-1 / 3 : k) * hface
  exact natDegree_lt_of_le_of_coeff_eq_zero68 _
    (5 * n - g) (laterDeepLower_index_pos_five n g hn hwindow)
    hdegree hcoeff

/-! ## Canonical expanded endpoints -/

set_option maxHeartbeats 8000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLower_I3face68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hwindow :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n) :
    let n := weightedRadius68 A B C0 D E
    let Ae := expand k 60 A
    let Be := expand k 60 B
    let Ce := expand k 60 C0
    let ce := cubicCDefectPolynomial68 Ae Ce
    let De := expand k 60 D
    let Ee := expand k 60 E
    let ee := cubicEDefectPolynomial68 Ae Ce Ee
    let g := cubicDefectGap68 n Be ce De ee
    l = 0 ∧
      firstSecondaryThree68
        (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
        (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
        (ee.coeff (6 * n - g)) = 0 := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  change 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n at hwindow
  change l = 0 ∧ firstSecondaryThree68
    (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
    (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
    (ee.coeff (6 * n - g)) = 0
  have data :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLoadI4Data68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  change LaterDeepLoadI4Data68 l beta gamma delta epsilon zeta
    n g Ae Be ce De ee at data
  have hgt : n < 2 * g := by
    have hn : 0 < n := data.hn
    omega
  have hl :=
    maximalExpandedIntegratedPolynomialLowerSystem_l_eq_zero_of_radius_lt_twoGap68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hgt)
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec : Ee = (1 / 27 : k) • Ae ^ 3 +
      (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using cubicEDefectPolynomial68_eq_cubicCoordinates
      Ae Ce Ee
  obtain ⟨i3, hi3⟩ := hsys.firstThree
  have hi3e : firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i3 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_firstIntegralThreePolynomial68_of_eq
        l beta gamma delta epsilon zeta i3 A B C0 D E hi3
  rw [hCrec, hErec, firstIntegralThreePolynomial68_cubicCoordinates, hl]
    at hi3e
  exact ⟨hl,
    cubicFirstIntegralThreePolynomial68_laterDeepLower_forces_face
      0 beta gamma delta epsilon zeta i3 Ae Be ce De ee n g
      data.hn data.hg rfl hwindow data.hA data.hB data.hc data.hD data.he
      hi3e⟩

set_option maxHeartbeats 8000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLower_F1face68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hwindow :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n) :
    let n := weightedRadius68 A B C0 D E
    let Ae := expand k 60 A
    let Be := expand k 60 B
    let Ce := expand k 60 C0
    let ce := cubicCDefectPolynomial68 Ae Ce
    let De := expand k 60 D
    let Ee := expand k 60 E
    let ee := cubicEDefectPolynomial68 Ae Ce Ee
    let g := cubicDefectGap68 n Be ce De ee
    l = 0 ∧
      firstSecondaryOne68 (n : k) (g : k)
        (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
        (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
        (ee.coeff (6 * n - g)) = 0 := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  change 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n at hwindow
  change l = 0 ∧ firstSecondaryOne68 (n : k) (g : k)
    (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
    (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
    (ee.coeff (6 * n - g)) = 0
  have data :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLoadI4Data68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  change LaterDeepLoadI4Data68 l beta gamma delta epsilon zeta
    n g Ae Be ce De ee at data
  have hgt : n < 2 * g := by
    have hn : 0 < n := data.hn
    omega
  have hl :=
    maximalExpandedIntegratedPolynomialLowerSystem_l_eq_zero_of_radius_lt_twoGap68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hgt)
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec : Ee = (1 / 27 : k) • Ae ^ 3 +
      (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using cubicEDefectPolynomial68_eq_cubicCoordinates
      Ae Ce Ee
  have h1e : lowerRowOnePolynomial68
      (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) Ce De Ee = 0 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_lowerRowOnePolynomial68_of_system
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
  rw [hCrec, hErec] at h1e
  have hone := congrArg
    (fun p : k[X] => p.coeff (12 * n - 2 * g - 1)) h1e
  rw [integratedLowerRowOnePolynomial68_secondaryCoeff_of_laterDeepLower
    l alpha beta gamma delta epsilon zeta eta Ae Be ce De ee n g
    data.hn data.hg hl hwindow data.hA data.hB data.hc data.hD data.he]
    at hone
  simp only [coeff_zero] at hone
  exact ⟨hl, (mul_eq_zero.mp hone).resolve_left (by norm_num)⟩

set_option maxHeartbeats 10000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenClassified68
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
      3 * n < 2 * g ∧ 2 * g < 5 * n) :
    let n := weightedRadius68 A B C0 D E
    let Ae := expand k 60 A
    let Be := expand k 60 B
    let Ce := expand k 60 C0
    let ce := cubicCDefectPolynomial68 Ae Ce
    let De := expand k 60 D
    let Ee := expand k 60 E
    let ee := cubicEDefectPolynomial68 Ae Ce Ee
    let g := cubicDefectGap68 n Be ce De ee
    l = 0 ∧ beta = 0 ∧ ee.coeff (6 * n - g) = 0 ∧
      Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
        3 * De.coeff (5 * n - g) := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  change 3 * n < 2 * g ∧ 2 * g < 5 * n at hopen
  change l = 0 ∧ beta = 0 ∧ ee.coeff (6 * n - g) = 0 ∧
    Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
      3 * De.coeff (5 * n - g)
  have hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n :=
    ⟨le_of_lt hopen.1, le_of_lt hopen.2⟩
  have hlbeta :=
    maximalExpandedIntegratedPolynomialLowerSystem_l_beta_eq_zero_of_threeRadius_lt_twoGap68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen.1)
  have hl : l = 0 := hlbeta.1
  have hbeta : beta = 0 := hlbeta.2
  have data :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLoadI4Data68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  change LaterDeepLoadI4Data68 l beta gamma delta epsilon zeta
    n g Ae Be ce De ee at data
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec : Ee = (1 / 27 : k) • Ae ^ 3 +
      (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using cubicEDefectPolynomial68_eq_cubicCoordinates
      Ae Ce Ee
  obtain ⟨i4, hi4⟩ := hsys.firstFour
  obtain ⟨i3, hi3⟩ := hsys.firstThree
  have hi4e : firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i4 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_firstIntegralFourPolynomial68_of_eq
        l beta gamma delta epsilon zeta i4 A B C0 D E hi4
  have hi3e : firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i3 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_firstIntegralThreePolynomial68_of_eq
        l beta gamma delta epsilon zeta i3 A B C0 D E hi3
  rw [hl, hbeta] at hi4e hi3e
  have h2e : lowerRowTwoPolynomial68
      (integratedSPolynomial68 l alpha beta delta Ae Be Ce De)
      (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) Be Ce De Ee = 0 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_lowerRowTwoPolynomial68_of_system
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
  have h1e : lowerRowOnePolynomial68
      (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) Ce De Ee = 0 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_lowerRowOnePolynomial68_of_system
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
  have h0e : lowerRowZeroPolynomial68
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) De Ee = C terminal * (60 * (X ^ 59 : k[X])) := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_lowerRowZeroPolynomial68_of_system
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
  have hnlarge : 10 ≤ n := by
    simpa only [n] using weightedRadius68_ge_ten A B C0 D E
      (by simpa only [n] using data.hn)
  have h0target : (lowerRowZeroPolynomial68
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) De Ee).coeff (13 * n - 2 * g - 1) = 0 :=
    expand_lowerRowZeroPolynomial68_coeff_eq_zero_of_index_gt
      terminal _ _ _ _ _ h0e
      (laterDeepLower_rowZeroIndex_gt_fiftyNine n g hnlarge hwindow)
  rw [hl, hbeta] at h2e h1e h0target
  have hclass :=
    polynomialSecondaryClassified68_of_laterDeepLower_open
      alpha gamma delta epsilon zeta eta i4 i3
      Ae Be Ce ce De Ee ee n g data.hn data.hg hopen
      data.hA data.hB data.hc data.hD data.he data.ha
      hCrec hErec hi4e hi3e h2e h1e h0target
  exact ⟨hl, hbeta, hclass.1, hclass.2⟩

set_option maxHeartbeats 8000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerSplit68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hwindow :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n) :
    let n := weightedRadius68 A B C0 D E
    let Ae := expand k 60 A
    let Be := expand k 60 B
    let Ce := expand k 60 C0
    let ce := cubicCDefectPolynomial68 Ae Ce
    let De := expand k 60 D
    let Ee := expand k 60 E
    let ee := cubicEDefectPolynomial68 Ae Ce Ee
    let g := cubicDefectGap68 n Be ce De ee
    l = 0 ∧
      firstSecondaryThree68
        (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
        (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
        (ee.coeff (6 * n - g)) = 0 ∧
      firstSecondaryOne68 (n : k) (g : k)
        (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
        (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
        (ee.coeff (6 * n - g)) = 0 ∧
      ((2 * g = 3 * n ∧
          (-8 / 9 : k) * firstSecondaryFour68
              (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
              (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
              (ee.coeff (6 * n - g)) +
            (5 / 72 * beta : k) * Ae.coeff (2 * n) ^ 3 = 0) ∨
        (3 * n < 2 * g ∧ 2 * g < 5 * n ∧ beta = 0 ∧
          ee.coeff (6 * n - g) = 0 ∧
          Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
            3 * De.coeff (5 * n - g)) ∨
        (2 * g = 5 * n ∧ beta = 0 ∧
          (-8 / 9 : k) * firstSecondaryFour68
              (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
              (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
              (ee.coeff (6 * n - g)) +
            (1 / 4 * delta : k) * Ae.coeff (2 * n) ^ 2 = 0)) := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  change 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n at hwindow
  have hI3 :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLower_I3face68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwindow)
  have hF1 :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLower_F1face68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwindow)
  have hl : l = 0 := hI3.1
  refine ⟨hl, hI3.2, hF1.2, ?_⟩
  have hgt : n < 2 * g := by
    have hn : 0 < n := by
      have hcore := maximalExpandedIntegratedPolynomialLowerSystem_cubicCore68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys
      simpa only [n] using hcore.1
    omega
  have hsplit :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLoadSplit68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
          And.intro hgt hwindow.1)
  change l = 0 ∧ _ at hsplit
  rcases hsplit.2 with hwall3 | hopen | hwall5 | hdeep
  · exact Or.inl hwall3
  · refine Or.inr (Or.inl ?_)
    have hclass :=
      maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenClassified68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys (by
          simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
            And.intro hopen.1 hopen.2.1)
    exact ⟨hopen.1, hopen.2.1, hclass.2.1, hclass.2.2.1, hclass.2.2.2⟩
  · exact Or.inr (Or.inr hwall5)
  · have : 5 * n < 2 * g ∧ 2 * g ≤ 5 * n := ⟨hdeep.1, hwindow.2⟩
    omega

end LaterDeepLowerEndgame68

#print axioms laterDeepLower_gap_lt_three_radius
#print axioms cubicFirstIntegralThreePolynomial68_laterDeepLower_forces_face
#print axioms cubicLoadRowOnePolynomial68_degree_lt_firstFace_of_laterDeepLower
#print axioms cubicLoadRowTwoPolynomial68_degree_lt_firstFace_of_laterDeepLower_open
#print axioms cubicLoadRowZeroPolynomial68_degree_lt_firstFace_of_laterDeepLower_open
#print axioms polynomialSecondaryClassified68_of_laterDeepLower_open
#print axioms secondaryDDefectPolynomial68_degree_lt_of_laterDeepLower
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLower_I3face68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLower_F1face68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenClassified68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerSplit68

end Max11DegreeRoutes
