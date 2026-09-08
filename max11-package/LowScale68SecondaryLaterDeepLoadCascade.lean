import LowScale68SecondaryLargeGapLoads
import LowScale68SecondaryRelaxedFirstFace
import LowScale68SecondaryDeepGapResidualOneForms

/-! # The later `(6,8)` deep-load cascade

This module continues the canonical `n < 2g` branch after `l = 0`.
It records the two mixed walls `2g = 3n` and `2g = 5n`, the ordinary
transverse I4 face between them, and vanishing of `delta` beyond the second
wall.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLoadCascade68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## The transverse coefficient at `9n-2g` -/

/-- The homogeneous quartic invariant still has the usual first-secondary
coefficient at `9n-2g` throughout the larger range `2g ≤ 6n`. -/
theorem cubicHomogeneousFirstIntegralFourPolynomial68_laterSecondaryCoeff
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hupper : 2 * g ≤ 6 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicFirstIntegralFourPolynomial68 0 0 0 0 0 0 A B c D e).coeff
        (9 * n - 2 * g) =
      (-8 / 9 : k) * firstSecondaryFour68
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
        (e.coeff (6 * n - g)) := by
  have hg3 : g ≤ 3 * n := by omega
  have lower (p : k[X]) (hp : p.natDegree < 9 * n - 2 * g) :
      p.coeff (9 * n - 2 * g) = 0 :=
    coeff_eq_zero_of_natDegree_lt hp
  have hABC : (A * B * c).coeff (9 * n - 2 * g) =
      A.coeff (2 * n) * B.coeff (3 * n - g) *
        c.coeff (4 * n - g) := by
    have h := coeff_mul_mul_at_bounds68 A B c (2 * n)
      (3 * n - g) (4 * n - g) hA hB hc
    have hi : 2 * n + (3 * n - g) + (4 * n - g) =
        9 * n - 2 * g := by omega
    simpa only [hi] using h
  have hBe : (B * e).coeff (9 * n - 2 * g) =
      B.coeff (3 * n - g) * e.coeff (6 * n - g) := by
    have h := coeff_mul_at_bounds68 B e (3 * n - g) (6 * n - g) hB he
    have hi : (3 * n - g) + (6 * n - g) = 9 * n - 2 * g := by omega
    simpa only [hi] using h
  have hDc : (D * c).coeff (9 * n - 2 * g) =
      D.coeff (5 * n - g) * c.coeff (4 * n - g) := by
    have h := coeff_mul_at_bounds68 D c (5 * n - g) (4 * n - g) hD hc
    have hi : (5 * n - g) + (4 * n - g) = 9 * n - 2 * g := by omega
    simpa only [hi] using h
  have hB3 : (B ^ 3).coeff (9 * n - 2 * g) = 0 :=
    lower _ (by compute_degree; omega)
  simp only [cubicFirstIntegralFourPolynomial68, zero_mul, zero_smul,
    add_zero, sub_zero, coeff_add, coeff_sub, coeff_smul, hABC, hBe, hDc,
    hB3, smul_eq_mul, mul_zero, add_zero, sub_zero]
  simp only [firstSecondaryFour68]
  ring

/-- Once `l=beta=0`, every remaining old-weight I4 load is strictly below
`9n-2g` in the open interval `3n<2g<5n`. -/
theorem secondaryLoadInvariantFourPolynomial68_degree_lt_laterSecondary_of_l_beta
    (gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g : ℕ) (hn : 0 < n) (hwindow : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (secondaryLoadInvariantFourPolynomial68
      0 0 gamma delta epsilon zeta A B c D e).natDegree <
        9 * n - 2 * g := by
  simp only [secondaryLoadInvariantFourPolynomial68, zero_mul, mul_zero,
    zero_smul, smul_zero, add_zero, sub_zero]
  compute_degree
  omega

theorem cubicFirstIntegralFourPolynomial68_laterSecondaryCoeff_of_l_beta
    (gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g : ℕ) (hn : 0 < n) (hg : 0 < g)
    (hwindow : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicFirstIntegralFourPolynomial68 0 0 gamma delta epsilon zeta
      A B c D e).coeff (9 * n - 2 * g) =
      (-8 / 9 : k) * firstSecondaryFour68
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
        (e.coeff (6 * n - g)) := by
  rw [cubicFirstIntegralFourPolynomial68_secondaryLoadSplit, coeff_add,
    coeff_eq_zero_of_natDegree_lt
      (secondaryLoadInvariantFourPolynomial68_degree_lt_laterSecondary_of_l_beta
        gamma delta epsilon zeta A B c D e n g hn hwindow
        hA hB hc hD he), add_zero]
  exact cubicHomogeneousFirstIntegralFourPolynomial68_laterSecondaryCoeff
    A B c D e n g hn hg (by omega) hA hB hc hD he

/-! ## The two mixed walls and the next pure load -/

theorem cubicFirstIntegralFourPolynomial68_coeff_threeRadiusWall
    (beta gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g : ℕ) (hn : 0 < n) (hg : 0 < g) (hwall : 2 * g = 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicFirstIntegralFourPolynomial68 0 beta gamma delta epsilon zeta
      A B c D e).coeff (9 * n - 2 * g) =
      (-8 / 9 : k) * firstSecondaryFour68
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
        (e.coeff (6 * n - g)) +
      (5 / 72 * beta : k) * A.coeff (2 * n) ^ 3 := by
  rw [cubicFirstIntegralFourPolynomial68_secondaryLoadSplit, coeff_add]
  have hi : 9 * n - 2 * g = 6 * n := by omega
  rw [hi, secondaryLoadInvariantFourPolynomial68_coeff_sixRadius_of_l_eq_zero
    beta gamma delta epsilon zeta A B c D e n g hn hg hA hB hc hD he]
  have hhom :=
    cubicHomogeneousFirstIntegralFourPolynomial68_laterSecondaryCoeff
      A B c D e n g hn hg (by omega) hA hB hc hD he
  rw [hi] at hhom
  rw [hhom]

theorem secondaryLoadInvariantFourPolynomial68_coeff_fourRadius_of_l_beta
    (gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g : ℕ) (hn : 0 < n) (hdeep : 5 * n ≤ 2 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (secondaryLoadInvariantFourPolynomial68
      0 0 gamma delta epsilon zeta A B c D e).coeff (4 * n) =
      (1 / 4 * delta : k) * A.coeff (2 * n) ^ 2 := by
  let q := zeta • A + (2 * epsilon : k) • B +
    (3 * delta : k) • c + (4 * gamma : k) • D -
    (4 / 3 * gamma : k) • (A * B)
  have hq : q.natDegree < 4 * n := by
    simp only [q]
    compute_degree
    omega
  have hA2 := coeff_pow_at_bound68 A (2 * n) 2 hA
  have hi : 2 * (2 * n) = 4 * n := by omega
  rw [hi] at hA2
  have hsplit : secondaryLoadInvariantFourPolynomial68
      0 0 gamma delta epsilon zeta A B c D e =
      q + (1 / 4 * delta : k) • A ^ 2 := by
    simp only [q, secondaryLoadInvariantFourPolynomial68, zero_mul,
      mul_zero, zero_smul, smul_zero, add_zero, sub_zero]
    module
  rw [hsplit, coeff_add, coeff_eq_zero_of_natDegree_lt hq, zero_add,
    coeff_smul, hA2, smul_eq_mul]

theorem cubicFirstIntegralFourPolynomial68_coeff_fiveRadiusWall
    (gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g : ℕ) (hn : 0 < n) (hg : 0 < g) (hwall : 2 * g = 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicFirstIntegralFourPolynomial68 0 0 gamma delta epsilon zeta
      A B c D e).coeff (9 * n - 2 * g) =
      (-8 / 9 : k) * firstSecondaryFour68
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
        (e.coeff (6 * n - g)) +
      (1 / 4 * delta : k) * A.coeff (2 * n) ^ 2 := by
  rw [cubicFirstIntegralFourPolynomial68_secondaryLoadSplit, coeff_add]
  have hi : 9 * n - 2 * g = 4 * n := by omega
  rw [hi, secondaryLoadInvariantFourPolynomial68_coeff_fourRadius_of_l_beta
    gamma delta epsilon zeta A B c D e n g hn (by omega)
    hA hB hc hD he]
  have hhom :=
    cubicHomogeneousFirstIntegralFourPolynomial68_laterSecondaryCoeff
      A B c D e n g hn hg (by omega) hA hB hc hD he
  rw [hi] at hhom
  rw [hhom]

theorem cubicFirstIntegralFourPolynomial68_coeff_fourRadius_of_l_beta
    (gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g : ℕ) (hn : 0 < n) (hg : 0 < g) (hdeep : 5 * n < 2 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicFirstIntegralFourPolynomial68 0 0 gamma delta epsilon zeta
      A B c D e).coeff (4 * n) =
      (1 / 4 * delta : k) * A.coeff (2 * n) ^ 2 := by
  rw [cubicFirstIntegralFourPolynomial68_secondaryLoadSplit, coeff_add,
    secondaryLoadInvariantFourPolynomial68_coeff_fourRadius_of_l_beta
      gamma delta epsilon zeta A B c D e n g hn (Nat.le_of_lt hdeep)
      hA hB hc hD he]
  have hhom :
      (cubicFirstIntegralFourPolynomial68 0 0 0 0 0 0
        A B c D e).natDegree < 4 * n := by
    have hB3 : (B ^ 3).natDegree < 4 * n := by
      compute_degree
      omega
    have hABC : (A * B * c).natDegree < 4 * n := by
      compute_degree
      omega
    have hBe : (B * e).natDegree < 4 * n := by
      compute_degree
      omega
    have hDc : (D * c).natDegree < 4 * n := by
      compute_degree
      omega
    simp only [cubicFirstIntegralFourPolynomial68, zero_mul, mul_zero,
      zero_smul, smul_zero, add_zero, sub_zero]
    apply deepGap_natDegree_add_lt
    · apply deepGap_natDegree_add_lt
      · apply deepGap_natDegree_sub_lt
        · exact deepGap_natDegree_smul_lt68 (-8 / 27 : k) hB3
        · exact deepGap_natDegree_smul_lt68 (8 / 9 : k) hABC
      · exact deepGap_natDegree_smul_lt68 (8 / 3 : k) hBe
    · exact deepGap_natDegree_smul_lt68 (8 / 3 : k) hDc
  rw [coeff_eq_zero_of_natDegree_lt hhom, zero_add]

/-! ## Consequences of constancy -/

theorem cubicFirstIntegralFourPolynomial68_threeRadiusWall_relation
    (beta gamma delta epsilon zeta i4 : k) (A B c D e : k[X])
    (n g : ℕ) (hn : 0 < n) (hg : 0 < g) (hwall : 2 * g = 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (hI4 : cubicFirstIntegralFourPolynomial68
      0 beta gamma delta epsilon zeta A B c D e = C i4) :
    (-8 / 9 : k) * firstSecondaryFour68
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
        (e.coeff (6 * n - g)) +
      (5 / 72 * beta : k) * A.coeff (2 * n) ^ 3 = 0 := by
  have hcoeff := congrArg (fun p : k[X] => p.coeff (9 * n - 2 * g)) hI4
  rw [cubicFirstIntegralFourPolynomial68_coeff_threeRadiusWall
    beta gamma delta epsilon zeta A B c D e n g hn hg hwall
    hA hB hc hD he] at hcoeff
  have hi : 9 * n - 2 * g ≠ 0 := by omega
  simpa only [coeff_C, if_neg hi] using hcoeff

theorem cubicFirstIntegralFourPolynomial68_laterSecondary_forces_face
    (gamma delta epsilon zeta i4 : k) (A B c D e : k[X])
    (n g : ℕ) (hn : 0 < n) (hg : 0 < g)
    (hwindow : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (hI4 : cubicFirstIntegralFourPolynomial68
      0 0 gamma delta epsilon zeta A B c D e = C i4) :
    firstSecondaryFour68
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
      (e.coeff (6 * n - g)) = 0 := by
  have hcoeff := congrArg (fun p : k[X] => p.coeff (9 * n - 2 * g)) hI4
  rw [cubicFirstIntegralFourPolynomial68_laterSecondaryCoeff_of_l_beta
    gamma delta epsilon zeta A B c D e n g hn hg hwindow
    hA hB hc hD he] at hcoeff
  have hi : 9 * n - 2 * g ≠ 0 := by omega
  simp only [coeff_C, if_neg hi] at hcoeff
  exact (mul_eq_zero.mp hcoeff).resolve_left (by norm_num)

theorem cubicFirstIntegralFourPolynomial68_fiveRadiusWall_relation
    (gamma delta epsilon zeta i4 : k) (A B c D e : k[X])
    (n g : ℕ) (hn : 0 < n) (hg : 0 < g) (hwall : 2 * g = 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (hI4 : cubicFirstIntegralFourPolynomial68
      0 0 gamma delta epsilon zeta A B c D e = C i4) :
    (-8 / 9 : k) * firstSecondaryFour68
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
        (e.coeff (6 * n - g)) +
      (1 / 4 * delta : k) * A.coeff (2 * n) ^ 2 = 0 := by
  have hcoeff := congrArg (fun p : k[X] => p.coeff (9 * n - 2 * g)) hI4
  rw [cubicFirstIntegralFourPolynomial68_coeff_fiveRadiusWall
    gamma delta epsilon zeta A B c D e n g hn hg hwall
    hA hB hc hD he] at hcoeff
  have hi : 9 * n - 2 * g ≠ 0 := by omega
  simpa only [coeff_C, if_neg hi] using hcoeff

theorem cubicFirstIntegralFourPolynomial68_forces_delta_eq_zero_of_l_beta
    (gamma delta epsilon zeta i4 : k) (A B c D e : k[X])
    (n g : ℕ) (hn : 0 < n) (hg : 0 < g) (hdeep : 5 * n < 2 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (ha : A.coeff (2 * n) ≠ 0)
    (hI4 : cubicFirstIntegralFourPolynomial68
      0 0 gamma delta epsilon zeta A B c D e = C i4) :
    delta = 0 := by
  have hcoeff := congrArg (fun p : k[X] => p.coeff (4 * n)) hI4
  rw [cubicFirstIntegralFourPolynomial68_coeff_fourRadius_of_l_beta
    gamma delta epsilon zeta A B c D e n g hn hg hdeep
    hA hB hc hD he] at hcoeff
  have hi : 4 * n ≠ 0 := by omega
  simp only [coeff_C, if_neg hi] at hcoeff
  have hpow : A.coeff (2 * n) ^ 2 ≠ 0 := pow_ne_zero 2 ha
  have hs : (1 / 4 * delta : k) = 0 :=
    (mul_eq_zero.mp hcoeff).resolve_right hpow
  exact (mul_eq_zero.mp hs).resolve_left (by norm_num)

/-! ## The first post-`delta` interval -/

theorem secondaryLoadInvariantFourPolynomial68_degree_lt_postDeltaSecondary
    (gamma epsilon zeta : k) (A B c D e : k[X])
    (n g : ℕ) (hn : 0 < n)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (secondaryLoadInvariantFourPolynomial68
      0 0 gamma 0 epsilon zeta A B c D e).natDegree <
        9 * n - 2 * g := by
  simp only [secondaryLoadInvariantFourPolynomial68, zero_mul, mul_zero,
    zero_smul, smul_zero, add_zero, sub_zero]
  compute_degree
  omega

theorem cubicFirstIntegralFourPolynomial68_postDeltaSecondaryCoeff
    (gamma epsilon zeta : k) (A B c D e : k[X])
    (n g : ℕ) (hn : 0 < n) (hg : 0 < g)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon zeta
      A B c D e).coeff (9 * n - 2 * g) =
      (-8 / 9 : k) * firstSecondaryFour68
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
        (e.coeff (6 * n - g)) := by
  rw [cubicFirstIntegralFourPolynomial68_secondaryLoadSplit, coeff_add,
    coeff_eq_zero_of_natDegree_lt
      (secondaryLoadInvariantFourPolynomial68_degree_lt_postDeltaSecondary
        gamma epsilon zeta A B c D e n g hn hwindow hA hB hc hD he),
    add_zero]
  exact cubicHomogeneousFirstIntegralFourPolynomial68_laterSecondaryCoeff
    A B c D e n g hn hg hwindow.2 hA hB hc hD he

theorem cubicFirstIntegralFourPolynomial68_postDelta_forces_face
    (gamma epsilon zeta i4 : k) (A B c D e : k[X])
    (n g : ℕ) (hn : 0 < n) (hg : 0 < g)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (hI4 : cubicFirstIntegralFourPolynomial68
      0 0 gamma 0 epsilon zeta A B c D e = C i4) :
    firstSecondaryFour68
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
      (e.coeff (6 * n - g)) = 0 := by
  have hcoeff := congrArg (fun p : k[X] => p.coeff (9 * n - 2 * g)) hI4
  rw [cubicFirstIntegralFourPolynomial68_postDeltaSecondaryCoeff
    gamma epsilon zeta A B c D e n g hn hg hwindow hA hB hc hD he] at hcoeff
  have hi : 9 * n - 2 * g ≠ 0 := by omega
  simp only [coeff_C, if_neg hi] at hcoeff
  exact (mul_eq_zero.mp hcoeff).resolve_left (by norm_num)

/-! ## The clamped-`B` interval after `2g=6n` -/

theorem cubicFirstIntegralFourPolynomial68_clampedBSecondaryCoeff
    (gamma epsilon zeta : k) (A B c D e : k[X])
    (n g : ℕ) (hn : 0 < n) (hg : 0 < g)
    (hwindow : 6 * n < 2 * g ∧ 2 * g < 8 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon zeta
      A B c D e).coeff (6 * n - g) =
      (8 / 9 : k) * B.coeff 0 *
        (-A.coeff (2 * n) * c.coeff (4 * n - g) +
          3 * e.coeff (6 * n - g)) := by
  have hg3 : 3 * n ≤ g := by omega
  have hB0 : B.natDegree ≤ 0 := by omega
  have hABC : (A * B * c).coeff (6 * n - g) =
      A.coeff (2 * n) * B.coeff 0 * c.coeff (4 * n - g) := by
    have h := coeff_mul_mul_at_bounds68 A B c (2 * n) 0 (4 * n - g)
      hA hB0 hc
    have hi : 2 * n + 0 + (4 * n - g) = 6 * n - g := by omega
    simpa only [hi] using h
  have hBe : (B * e).coeff (6 * n - g) =
      B.coeff 0 * e.coeff (6 * n - g) := by
    have h := coeff_mul_at_bounds68 B e 0 (6 * n - g) hB0 he
    simpa only [zero_add] using h
  have hB3 : (B ^ 3).natDegree < 6 * n - g := by
    compute_degree
    omega
  have hDc : (D * c).natDegree < 6 * n - g := by
    compute_degree
    omega
  have hload : (secondaryLoadInvariantFourPolynomial68
      0 0 gamma 0 epsilon zeta A B c D e).natDegree < 6 * n - g := by
    simp only [secondaryLoadInvariantFourPolynomial68, zero_mul, mul_zero,
      zero_smul, smul_zero, add_zero, sub_zero]
    compute_degree
    omega
  rw [cubicFirstIntegralFourPolynomial68_secondaryLoadSplit, coeff_add,
    coeff_eq_zero_of_natDegree_lt hload, add_zero]
  simp only [cubicFirstIntegralFourPolynomial68, zero_mul, mul_zero,
    zero_smul, smul_zero, add_zero, sub_zero, coeff_add, coeff_sub,
    coeff_smul, hABC, hBe, coeff_eq_zero_of_natDegree_lt hB3,
    coeff_eq_zero_of_natDegree_lt hDc, smul_eq_mul]
  ring

theorem cubicFirstIntegralFourPolynomial68_clampedB_forces_face
    (gamma epsilon zeta i4 : k) (A B c D e : k[X])
    (n g : ℕ) (hn : 0 < n) (hg : 0 < g)
    (hwindow : 6 * n < 2 * g ∧ 2 * g < 8 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (hI4 : cubicFirstIntegralFourPolynomial68
      0 0 gamma 0 epsilon zeta A B c D e = C i4) :
    B.coeff 0 *
      (-A.coeff (2 * n) * c.coeff (4 * n - g) +
        3 * e.coeff (6 * n - g)) = 0 := by
  have hcoeff := congrArg (fun p : k[X] => p.coeff (6 * n - g)) hI4
  rw [cubicFirstIntegralFourPolynomial68_clampedBSecondaryCoeff
    gamma epsilon zeta A B c D e n g hn hg hwindow hA hB hc hD he] at hcoeff
  have hi : 6 * n - g ≠ 0 := by omega
  simp only [coeff_C, if_neg hi] at hcoeff
  rcases mul_eq_zero.mp hcoeff with hleft | hright
  · have hb : B.coeff 0 = 0 :=
      (mul_eq_zero.mp hleft).resolve_left (by norm_num)
    rw [hb, zero_mul]
  · rw [hright, mul_zero]

/-! ## Canonical expanded source data and exhaustive later split -/

structure LaterDeepLoadI4Data68
    (l beta gamma delta epsilon zeta : k) (n g : ℕ)
    (A B c D e : k[X]) : Prop where
  hn : 0 < n
  hg : 0 < g
  hA : A.natDegree ≤ 2 * n
  hB : B.natDegree ≤ 3 * n - g
  hc : c.natDegree ≤ 4 * n - g
  hD : D.natDegree ≤ 5 * n - g
  he : e.natDegree ≤ 6 * n - g
  ha : A.coeff (2 * n) ≠ 0
  invariant : ∃ i4 : k,
    cubicFirstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
      A B c D e = C i4

set_option maxHeartbeats 5000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLoadI4Data68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E) :
    let n := weightedRadius68 A B C0 D E
    let Ae := expand k 60 A
    let Be := expand k 60 B
    let Ce := expand k 60 C0
    let ce := cubicCDefectPolynomial68 Ae Ce
    let De := expand k 60 D
    let Ee := expand k 60 E
    let ee := cubicEDefectPolynomial68 Ae Ce Ee
    let g := cubicDefectGap68 n Be ce De ee
    LaterDeepLoadI4Data68 l beta gamma delta epsilon zeta
      n g Ae Be ce De ee := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
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
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
      hsecondary.2.2.2.1
  have he : ee.natDegree ≤ 6 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
      hsecondary.2.2.2.2.1
  have ha : Ae.coeff (2 * n) ≠ 0 := by
    simpa only [n, Ae] using hcore.2.2.2.2.2
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec :
      Ee = (1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using cubicEDefectPolynomial68_eq_cubicCoordinates
      Ae Ce Ee
  obtain ⟨i4, hi4⟩ := hsys.firstFour
  have hi4e : firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i4 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_firstIntegralFourPolynomial68_of_eq
        l beta gamma delta epsilon zeta i4 A B C0 D E hi4
  rw [hCrec, hErec, firstIntegralFourPolynomial68_cubicCoordinates] at hi4e
  exact ⟨hn, hg, hA, hB, hc, hD, he, ha, i4, hi4e⟩

set_option maxHeartbeats 6000000 in
/-- Exhaustive I4 load cascade after the first old load has vanished. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLoadSplit68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hchamber :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      n < 2 * g ∧ 3 * n ≤ 2 * g) :
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
      ((2 * g = 3 * n ∧
          (-8 / 9 : k) * firstSecondaryFour68
              (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
              (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
              (ee.coeff (6 * n - g)) +
            (5 / 72 * beta : k) * Ae.coeff (2 * n) ^ 3 = 0) ∨
        (3 * n < 2 * g ∧ 2 * g < 5 * n ∧ beta = 0 ∧
          firstSecondaryFour68
              (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
              (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
              (ee.coeff (6 * n - g)) = 0) ∨
        (2 * g = 5 * n ∧ beta = 0 ∧
          (-8 / 9 : k) * firstSecondaryFour68
              (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
              (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
              (ee.coeff (6 * n - g)) +
            (1 / 4 * delta : k) * Ae.coeff (2 * n) ^ 2 = 0) ∨
        (5 * n < 2 * g ∧ beta = 0 ∧ delta = 0 ∧
          (2 * g ≤ 6 * n →
            firstSecondaryFour68
              (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
              (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
              (ee.coeff (6 * n - g)) = 0) ∧
          (6 * n < 2 * g → 2 * g < 8 * n →
            Be.coeff 0 *
              (-Ae.coeff (2 * n) * ce.coeff (4 * n - g) +
                3 * ee.coeff (6 * n - g)) = 0))) := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  change n < 2 * g ∧ 3 * n ≤ 2 * g at hchamber
  change l = 0 ∧ _
  have hl :=
    maximalExpandedIntegratedPolynomialLowerSystem_l_eq_zero_of_radius_lt_twoGap68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hchamber.1)
  have data :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLoadI4Data68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  change LaterDeepLoadI4Data68 l beta gamma delta epsilon zeta
    n g Ae Be ce De ee at data
  obtain ⟨i4, hI4raw⟩ := data.invariant
  have hI4l := hI4raw
  rw [hl] at hI4l
  refine ⟨hl, ?_⟩
  rcases eq_or_lt_of_le hchamber.2 with hwall3 | hgt3
  · left
    exact ⟨hwall3.symm,
      cubicFirstIntegralFourPolynomial68_threeRadiusWall_relation
        beta gamma delta epsilon zeta i4 Ae Be ce De ee n g
        data.hn data.hg hwall3.symm data.hA data.hB data.hc data.hD data.he
        hI4l⟩
  · have hlbeta :=
      maximalExpandedIntegratedPolynomialLowerSystem_l_beta_eq_zero_of_threeRadius_lt_twoGap68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys (by
          simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hgt3)
    have hbeta : beta = 0 := hlbeta.2
    have hI4lb := hI4l
    rw [hbeta] at hI4lb
    rcases lt_trichotomy (2 * g) (5 * n) with hlt5 | hwall5 | hgt5
    · right; left
      exact ⟨hgt3, hlt5, hbeta,
        cubicFirstIntegralFourPolynomial68_laterSecondary_forces_face
          gamma delta epsilon zeta i4 Ae Be ce De ee n g
          data.hn data.hg ⟨hgt3, hlt5⟩ data.hA data.hB data.hc
          data.hD data.he hI4lb⟩
    · right; right; left
      exact ⟨hwall5, hbeta,
        cubicFirstIntegralFourPolynomial68_fiveRadiusWall_relation
          gamma delta epsilon zeta i4 Ae Be ce De ee n g
          data.hn data.hg hwall5 data.hA data.hB data.hc data.hD data.he
          hI4lb⟩
    · right; right; right
      have hdelta :=
        cubicFirstIntegralFourPolynomial68_forces_delta_eq_zero_of_l_beta
          gamma delta epsilon zeta i4 Ae Be ce De ee n g
          data.hn data.hg hgt5 data.hA data.hB data.hc data.hD data.he
          data.ha hI4lb
      have hI4lbd := hI4lb
      rw [hdelta] at hI4lbd
      refine ⟨hgt5, hbeta, hdelta, ?_, ?_⟩
      · intro hle6
        exact cubicFirstIntegralFourPolynomial68_postDelta_forces_face
          gamma epsilon zeta i4 Ae Be ce De ee n g data.hn data.hg
          ⟨hgt5, hle6⟩ data.hA data.hB data.hc data.hD data.he hI4lbd
      · intro hgt6 hlt8
        exact cubicFirstIntegralFourPolynomial68_clampedB_forces_face
          gamma epsilon zeta i4 Ae Be ce De ee n g data.hn data.hg
          ⟨hgt6, hlt8⟩ data.hA data.hB data.hc data.hD data.he hI4lbd

end LaterDeepLoadCascade68

#print axioms cubicHomogeneousFirstIntegralFourPolynomial68_laterSecondaryCoeff
#print axioms cubicFirstIntegralFourPolynomial68_coeff_threeRadiusWall
#print axioms cubicFirstIntegralFourPolynomial68_laterSecondary_forces_face
#print axioms cubicFirstIntegralFourPolynomial68_fiveRadiusWall_relation
#print axioms cubicFirstIntegralFourPolynomial68_forces_delta_eq_zero_of_l_beta
#print axioms cubicFirstIntegralFourPolynomial68_postDelta_forces_face
#print axioms cubicFirstIntegralFourPolynomial68_clampedB_forces_face
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLoadI4Data68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLoadSplit68

end Max11DegreeRoutes
