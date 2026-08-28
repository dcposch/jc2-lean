import LowScale68SecondaryResidualFace

/-! # First residual degree drop on the `(6,8)` secondary face

After the first secondary classifier gives `e_top=0` and
`A_top*B_top=3*D_top`, translate `D` by `A*B/3`.  This module turns those two
coefficient cancellations into strict polynomial degree drops and applies
them to the canonical expanded lower system.  Extraction of the next five
face equations is handled in the following module.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section SecondaryResidualExtraction68

variable {k : Type*} [Field k] [CharZero k]

/-- The first-face relation cancels the top coefficient of
`D-A*B/3`, so the translated odd defect lies strictly below its old bound. -/
theorem secondaryDDefectPolynomial68_degree_lt
    (A B D : k[X]) (n g : ℕ) (hsmall : 2 * g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (hrel : A.coeff (2 * n) * B.coeff (3 * n - g) =
      3 * D.coeff (5 * n - g)) :
    (secondaryDDefectPolynomial68 A B D).natDegree < 5 * n - g := by
  have hdegree : (secondaryDDefectPolynomial68 A B D).natDegree ≤
      5 * n - g := by
    simp only [secondaryDDefectPolynomial68]
    compute_degree
    omega
  have hindex : 2 * n + (3 * n - g) = 5 * n - g := by omega
  have hAB := coeff_mul_at_bounds68 A B (2 * n) (3 * n - g) hA hB
  rw [hindex] at hAB
  have hcoeff : (secondaryDDefectPolynomial68 A B D).coeff
      (5 * n - g) = 0 := by
    simp only [secondaryDDefectPolynomial68, coeff_sub, coeff_smul,
      smul_eq_mul]
    rw [hAB]
    linear_combination (-1 / 3 : k) * hrel
  have hpred := natDegree_le_pred hdegree hcoeff
  omega

/-- Both translated residual directions lie strictly below the first
secondary boundary after its two leading relations have been imposed. -/
theorem firstSecondaryResidualDegreeDrops68
    (A B D e : k[X]) (n g : ℕ) (hsmall : 2 * g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (hrel : A.coeff (2 * n) * B.coeff (3 * n - g) =
      3 * D.coeff (5 * n - g))
    (hetop : e.coeff (6 * n - g) = 0) :
    (secondaryDDefectPolynomial68 A B D).natDegree < 5 * n - g ∧
      e.natDegree < 6 * n - g := by
  refine ⟨secondaryDDefectPolynomial68_degree_lt A B D n g hsmall
    hA hB hD hrel, ?_⟩
  have hpred := natDegree_le_pred he hetop
  omega

/-- Load-free quartic invariant in the residual coordinates
`D=A*B/3+d`. -/
def secondaryResidualInvariantFourPolynomial68
    (B c d e : k[X]) : k[X] :=
  (-8 / 27 : k) • B ^ 3 + (8 / 3 : k) • (B * e) +
    (8 / 3 : k) • (c * d)

/-- Load-free cubic invariant in the residual coordinates. -/
def secondaryResidualInvariantThreePolynomial68
    (A B c d e : k[X]) : k[X] :=
  (-8 / 9 : k) • (A * B * d) - (8 / 9 : k) • (B ^ 2 * c) +
    (8 / 3 : k) • (c * e) + (4 / 3 : k) • d ^ 2

set_option maxHeartbeats 1000000 in
theorem cubicFirstIntegralFourPolynomial68_residualCoordinates
    (A B c d e : k[X]) :
    cubicFirstIntegralFourPolynomial68 0 0 0 0 0 0 A B c
        ((1 / 3 : k) • (A * B) + d) e =
      secondaryResidualInvariantFourPolynomial68 B c d e := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [cubicFirstIntegralFourPolynomial68,
    secondaryResidualInvariantFourPolynomial68, Polynomial.smul_eq_C_mul,
    map_add, map_sub, map_mul, map_pow, map_neg, map_zero,
    RatFunc.algebraMap_C]
  simp only [map_div₀, map_ofNat, map_one, zero_mul, add_zero, sub_zero]
  ring_nf

set_option maxHeartbeats 1000000 in
theorem cubicFirstIntegralThreePolynomial68_residualCoordinates
    (A B c d e : k[X]) :
    cubicFirstIntegralThreePolynomial68 0 0 0 0 0 0 A B c
        ((1 / 3 : k) • (A * B) + d) e =
      secondaryResidualInvariantThreePolynomial68 A B c d e := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [cubicFirstIntegralThreePolynomial68,
    secondaryResidualInvariantThreePolynomial68, Polynomial.smul_eq_C_mul,
    map_add, map_sub, map_mul, map_pow, map_zero, RatFunc.algebraMap_C]
  simp only [map_div₀, map_ofNat, map_one, zero_mul, add_zero, sub_zero]
  have hneg8 : RatFunc.C (-8 : k) = (-8 : RatFunc k) := by
    rw [show (-8 : k) = -(8 : k) by norm_num, map_neg, map_ofNat]
  rw [hneg8]
  ring

/-- Lower old-weight terms in the quartic invariant. -/
def secondaryLoadInvariantFourPolynomial68
    (l beta gamma delta epsilon zeta : k)
    (A B c D e : k[X]) : k[X] :=
  zeta • A + (2 * epsilon : k) • B +
    (1 / 4 * delta : k) • A ^ 2 + (3 * delta : k) • c +
    (4 * gamma : k) • D - (4 / 3 * gamma : k) • (A * B) +
    (5 * beta : k) • e + (5 / 6 * beta : k) • (A * c) -
    (5 / 12 * beta : k) • B ^ 2 +
    (5 / 72 * beta : k) • A ^ 3 +
    (35 / 1728 * l : k) • A ^ 4 +
    (7 / 24 * l : k) • (A ^ 2 * c) -
    (35 / 72 * l : k) • (A * B ^ 2) +
    (7 / 6 * l : k) • (A * e) +
    (7 / 6 * l : k) • (B * D) + (7 / 12 * l : k) • c ^ 2

/-- Lower old-weight terms in the cubic invariant. -/
def secondaryLoadInvariantThreePolynomial68
    (l beta gamma delta epsilon zeta : k)
    (A B c D e : k[X]) : k[X] :=
  zeta • B + (2 * epsilon : k) • c + (4 * gamma : k) • e -
    (2 / 3 * gamma : k) • B ^ 2 + (3 * delta : k) • D -
    (3 / 2 * delta : k) • (A * B) +
    (5 / 24 * beta : k) • (A ^ 2 * B) -
    (5 / 6 * beta : k) • (A * D) -
    (5 / 6 * beta : k) • (B * c) +
    (7 / 432 * l : k) • (A ^ 3 * B) -
    (7 / 72 * l : k) • (A ^ 2 * D) -
    (7 / 12 * l : k) • (A * B * c) -
    (35 / 216 * l : k) • B ^ 3 +
    (7 / 6 * l : k) • (B * e) + (7 / 6 * l : k) • (D * c)

theorem cubicFirstIntegralFourPolynomial68_secondaryLoadSplit
    (l beta gamma delta epsilon zeta : k) (A B c D e : k[X]) :
    cubicFirstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
        A B c D e =
      cubicFirstIntegralFourPolynomial68 0 0 0 0 0 0 A B c D e +
        secondaryLoadInvariantFourPolynomial68
          l beta gamma delta epsilon zeta A B c D e := by
  simp only [cubicFirstIntegralFourPolynomial68,
    secondaryLoadInvariantFourPolynomial68, zero_mul, zero_smul, add_zero,
    sub_zero]
  module

theorem cubicFirstIntegralThreePolynomial68_secondaryLoadSplit
    (l beta gamma delta epsilon zeta : k) (A B c D e : k[X]) :
    cubicFirstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
        A B c D e =
      cubicFirstIntegralThreePolynomial68 0 0 0 0 0 0 A B c D e +
        secondaryLoadInvariantThreePolynomial68
          l beta gamma delta epsilon zeta A B c D e := by
  simp only [cubicFirstIntegralThreePolynomial68,
    secondaryLoadInvariantThreePolynomial68, zero_mul, zero_smul, add_zero,
    sub_zero]
  module

set_option maxHeartbeats 2000000 in
/-- In `3g<n`, all load terms of the quartic invariant lie below every
middle residual face `g<h<2g`. -/
theorem secondaryLoadInvariantFourPolynomial68_degree_lt_middle
    (l beta gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g h : ℕ) (hg : 0 < g) (hsmall : 3 * g < n) (hh : h < 2 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - h) :
    (secondaryLoadInvariantFourPolynomial68
      l beta gamma delta epsilon zeta A B c D e).natDegree <
        9 * n - g - h := by
  simp only [secondaryLoadInvariantFourPolynomial68]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
/-- The corresponding load cutoff for the cubic invariant. -/
theorem secondaryLoadInvariantThreePolynomial68_degree_lt_middle
    (l beta gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g h : ℕ) (hg : 0 < g) (hsmall : 3 * g < n) (hh : h < 2 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - h) :
    (secondaryLoadInvariantThreePolynomial68
      l beta gamma delta epsilon zeta A B c D e).natDegree <
        10 * n - g - h := by
  simp only [secondaryLoadInvariantThreePolynomial68]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
/-- Leading coefficient of the quartic invariant on a middle residual face
`g<h<2g`. -/
theorem secondaryResidualInvariantFourPolynomial68_coeff_middle
    (B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g) (hsmall : 3 * g < n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (secondaryResidualInvariantFourPolynomial68 B c d e).coeff
        (9 * n - g - h) =
      (8 / 3 : k) *
        (B.coeff (3 * n - g) * e.coeff (6 * n - h) +
          c.coeff (4 * n - g) * d.coeff (5 * n - h)) := by
  have hB3 : (B ^ 3).natDegree < 9 * n - g - h := by
    compute_degree
    omega
  have hBe := coeff_mul_at_bounds68 B e (3 * n - g) (6 * n - h)
    hB he
  have hBei : (3 * n - g) + (6 * n - h) = 9 * n - g - h := by omega
  rw [hBei] at hBe
  have hcd := coeff_mul_at_bounds68 c d (4 * n - g) (5 * n - h)
    hc hd
  have hcdi : (4 * n - g) + (5 * n - h) = 9 * n - g - h := by omega
  rw [hcdi] at hcd
  simp only [secondaryResidualInvariantFourPolynomial68, coeff_add,
    coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hB3, hBe, hcd]
  ring

set_option maxHeartbeats 2000000 in
/-- Leading coefficient of the cubic invariant on the same middle face. -/
theorem secondaryResidualInvariantThreePolynomial68_coeff_middle
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g) (hsmall : 3 * g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (secondaryResidualInvariantThreePolynomial68 A B c d e).coeff
        (10 * n - g - h) =
      (8 / 9 : k) *
        (-(A.coeff (2 * n) * B.coeff (3 * n - g) *
            d.coeff (5 * n - h)) +
          3 * c.coeff (4 * n - g) * e.coeff (6 * n - h)) := by
  have hABd := coeff_mul_mul_at_bounds68 A B d (2 * n)
    (3 * n - g) (5 * n - h) hA hB hd
  have hABdi : 2 * n + (3 * n - g) + (5 * n - h) =
      10 * n - g - h := by omega
  rw [hABdi] at hABd
  have hB2c : (B ^ 2 * c).natDegree < 10 * n - g - h := by
    compute_degree
    omega
  have hce := coeff_mul_at_bounds68 c e (4 * n - g) (6 * n - h)
    hc he
  have hcei : (4 * n - g) + (6 * n - h) = 10 * n - g - h := by omega
  rw [hcei] at hce
  have hd2 : (d ^ 2).natDegree < 10 * n - g - h := by
    compute_degree
    omega
  simp only [secondaryResidualInvariantThreePolynomial68, coeff_add,
    coeff_sub, coeff_smul, smul_eq_mul, hABd,
    coeff_eq_zero_of_natDegree_lt hB2c, hce,
    coeff_eq_zero_of_natDegree_lt hd2]
  ring

set_option maxHeartbeats 2000000 in
/-- The literal quartic invariant has the same middle-face coefficient: all
constant-load terms are strictly lower in `3g<n`. -/
theorem cubicFirstIntegralFourPolynomial68_coeff_residualMiddle
    (l beta gamma delta epsilon zeta : k) (A B c d e : k[X])
    (n g h : ℕ) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hsmall : 3 * g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (cubicFirstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff
        (9 * n - g - h) =
      (8 / 3 : k) *
        (B.coeff (3 * n - g) * e.coeff (6 * n - h) +
          c.coeff (4 * n - g) * d.coeff (5 * n - h)) := by
  let D := (1 / 3 : k) • (A * B) + d
  have hD : D.natDegree ≤ 5 * n - g := by
    simp only [D]
    compute_degree
    omega
  have hload := secondaryLoadInvariantFourPolynomial68_degree_lt_middle
    l beta gamma delta epsilon zeta A B c D e n g h hg hsmall hh
    hA hB hc hD he
  rw [cubicFirstIntegralFourPolynomial68_secondaryLoadSplit,
    show cubicFirstIntegralFourPolynomial68 0 0 0 0 0 0 A B c D e =
        secondaryResidualInvariantFourPolynomial68 B c d e by
      simpa only [D] using
        cubicFirstIntegralFourPolynomial68_residualCoordinates A B c d e,
    coeff_add,
    secondaryResidualInvariantFourPolynomial68_coeff_middle B c d e
      n g h hg hgh hh hsmall hB hc hd he,
    coeff_eq_zero_of_natDegree_lt hload, add_zero]

set_option maxHeartbeats 2000000 in
/-- The corresponding literal cubic-invariant coefficient. -/
theorem cubicFirstIntegralThreePolynomial68_coeff_residualMiddle
    (l beta gamma delta epsilon zeta : k) (A B c d e : k[X])
    (n g h : ℕ) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hsmall : 3 * g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (cubicFirstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff
        (10 * n - g - h) =
      (8 / 9 : k) *
        (-(A.coeff (2 * n) * B.coeff (3 * n - g) *
            d.coeff (5 * n - h)) +
          3 * c.coeff (4 * n - g) * e.coeff (6 * n - h)) := by
  let D := (1 / 3 : k) • (A * B) + d
  have hD : D.natDegree ≤ 5 * n - g := by
    simp only [D]
    compute_degree
    omega
  have hload := secondaryLoadInvariantThreePolynomial68_degree_lt_middle
    l beta gamma delta epsilon zeta A B c D e n g h hg hsmall hh
    hA hB hc hD he
  rw [cubicFirstIntegralThreePolynomial68_secondaryLoadSplit,
    show cubicFirstIntegralThreePolynomial68 0 0 0 0 0 0 A B c D e =
        secondaryResidualInvariantThreePolynomial68 A B c d e by
      simpa only [D] using
        cubicFirstIntegralThreePolynomial68_residualCoordinates A B c d e,
    coeff_add,
    secondaryResidualInvariantThreePolynomial68_coeff_middle A B c d e
      n g h hg hgh hh hsmall hA hB hc hd he,
    coeff_eq_zero_of_natDegree_lt hload, add_zero]

set_option maxHeartbeats 2000000 in
/-- The two literal constant invariants select the abstract middle residual
face whenever the actual degree gaps satisfy `g<h<2g` in `3g<n`. -/
theorem polynomialSecondaryResidualBetweenFace68
    (l beta gamma delta epsilon zeta i4 i3 : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hsmall : 3 * g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hi4 : cubicFirstIntegralFourPolynomial68
      l beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hi3 : cubicFirstIntegralThreePolynomial68
      l beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i3) :
    SecondaryResidualBetweenFace68
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (d.coeff (5 * n - h))
      (e.coeff (6 * n - h)) := by
  constructor
  · have hz := congrArg (fun p : k[X] => p.coeff (9 * n - g - h)) hi4
    rw [cubicFirstIntegralFourPolynomial68_coeff_residualMiddle
      l beta gamma delta epsilon zeta A B c d e n g h hg hgh hh
      hsmall hA hB hc hd he] at hz
    have hindex : 9 * n - g - h ≠ 0 := by omega
    simp only [coeff_C, if_neg hindex] at hz
    have hscalar : (8 / 3 : k) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp hz).resolve_left hscalar
  · have hz := congrArg (fun p : k[X] => p.coeff (10 * n - g - h)) hi3
    rw [cubicFirstIntegralThreePolynomial68_coeff_residualMiddle
      l beta gamma delta epsilon zeta A B c d e n g h hg hgh hh
      hsmall hA hB hc hd he] at hz
    have hindex : 10 * n - g - h ≠ 0 := by omega
    simp only [coeff_C, if_neg hindex] at hz
    have hscalar : (8 / 9 : k) ≠ 0 := by norm_num
    have hzero := (mul_eq_zero.mp hz).resolve_left hscalar
    linear_combination hzero

/-- Direct literal-polynomial form of the abstract middle-face classifier. -/
theorem polynomialSecondaryResidualBetweenFace68_classify
    (l beta gamma delta epsilon zeta i4 i3 : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hsmall : 3 * g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hb : B.coeff (3 * n - g) ≠ 0)
    (hcn : c.coeff (4 * n - g) ≠ 0)
    (hattained : d.coeff (5 * n - h) ≠ 0 ∨
      e.coeff (6 * n - h) ≠ 0)
    (hi4 : cubicFirstIntegralFourPolynomial68
      l beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hi3 : cubicFirstIntegralThreePolynomial68
      l beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i3) :
    d.coeff (5 * n - h) ≠ 0 ∧ e.coeff (6 * n - h) ≠ 0 ∧
      A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
        3 * c.coeff (4 * n - g) ^ 2 = 0 := by
  exact secondaryResidualBetweenFace68_classify
    (A.coeff (2 * n)) (B.coeff (3 * n - g))
    (c.coeff (4 * n - g)) (d.coeff (5 * n - h))
    (e.coeff (6 * n - h)) hb hcn hattained
    (polynomialSecondaryResidualBetweenFace68
      l beta gamma delta epsilon zeta i4 i3 A B c d e n g h
      hg hgh hh hsmall hA hB hc hd he hi4 hi3)

/-- Load-free first one-form after translating `D=A*B/3+d`. -/
def secondaryResidualRowTwoPolynomial68
    (A B c d e : k[X]) : k[X] :=
  (-4 / 27 : k) •
    (-(6 : k) • (A * B * derivative e) -
      (6 : k) • (A * derivative B * e) -
      (6 : k) • (A * c * derivative d) -
      (6 : k) • (A * derivative c * d) -
      derivative A * B ^ 3 +
      (3 : k) • (derivative A * B * e) +
      (3 : k) • (derivative A * c * d) +
      (6 : k) • (B ^ 2 * derivative d) +
      (12 : k) • (B * derivative B * d) +
      (12 : k) • (B * c * derivative c) +
      (6 : k) • (derivative B * c ^ 2) -
      (18 : k) • (d * derivative e) -
      (18 : k) • (derivative d * e))

set_option maxHeartbeats 3000000 in
theorem cubicHomogeneousRowTwoPolynomial68_residualCoordinates
    (A B c d e : k[X]) :
    cubicHomogeneousRowTwoPolynomial68 A B c
        ((1 / 3 : k) • (A * B) + d) e =
      secondaryResidualRowTwoPolynomial68 A B c d e := by
  rw [cubicHomogeneousRowTwoPolynomial68_eq_expanded]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [cubicHomogeneousRowTwoExpandedPolynomial68,
    secondaryResidualRowTwoPolynomial68, derivative_add, derivative_mul,
    derivative_C, zero_mul, zero_add, Polynomial.smul_eq_C_mul, map_add,
    map_sub, map_mul, map_pow, map_neg, map_zero, RatFunc.algebraMap_C]
  simp only [map_div₀, map_ofNat, map_natCast, map_one]
  ring

/-- Load-free second one-form in the residual coordinates. -/
def secondaryResidualRowOnePolynomial68
    (A B c d e : k[X]) : k[X] :=
  (-4 / 27 : k) •
    ((2 : k) • (A ^ 2 * B * derivative d) +
      (2 : k) • (A ^ 2 * derivative B * d) +
      (2 : k) • (A * derivative A * B * d) -
      (6 : k) • (A * c * derivative e) -
      (6 : k) • (A * derivative c * e) -
      (2 : k) • (derivative A * B ^ 2 * c) +
      (3 : k) • (derivative A * d ^ 2) -
      (3 : k) • (B ^ 2 * derivative e) +
      (3 : k) • (B * c * derivative d) +
      (3 : k) • (B * derivative c * d) +
      (9 : k) • (derivative B * c * d) +
      (6 : k) • (c ^ 2 * derivative c) -
      (18 : k) • (e * derivative e))

set_option maxHeartbeats 3000000 in
theorem cubicHomogeneousRowOnePolynomial68_residualCoordinates
    (A B c d e : k[X]) :
    cubicHomogeneousRowOnePolynomial68 A B c
        ((1 / 3 : k) • (A * B) + d) e =
      secondaryResidualRowOnePolynomial68 A B c d e := by
  rw [cubicHomogeneousRowOnePolynomial68_eq_expanded]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [cubicHomogeneousRowOneExpandedPolynomial68,
    firstSecondaryCoreRowOnePolynomial68,
    cubicRemainderRowOnePolynomial68,
    secondaryResidualRowOnePolynomial68, derivative_add, derivative_mul,
    derivative_C, zero_mul, zero_add, Polynomial.smul_eq_C_mul, map_add,
    map_sub, map_mul, map_pow, map_neg, map_zero, RatFunc.algebraMap_C]
  simp only [map_div₀, map_ofNat, map_natCast, map_one]
  ring

/-- Load-free terminal one-form in the residual coordinates. -/
def secondaryResidualRowZeroPolynomial68
    (A B c d e : k[X]) : k[X] :=
  (4 / 27 : k) •
    (-(1 : k) • (A * derivative A * B * e) -
      A * derivative A * c * d -
      A * B ^ 2 * derivative d -
      A * B * derivative B * d +
      derivative A * B * c ^ 2 -
      (3 : k) • (derivative A * d * e) +
      (3 : k) • (B * c * derivative e) -
      (3 : k) • (B * d * derivative d) -
      (3 : k) • (derivative B * d ^ 2) -
      (3 : k) • (c * derivative c * d))

set_option maxHeartbeats 3000000 in
theorem cubicHomogeneousRowZeroPolynomial68_residualCoordinates
    (A B c d e : k[X]) :
    cubicHomogeneousRowZeroPolynomial68 A B c
        ((1 / 3 : k) • (A * B) + d) e =
      secondaryResidualRowZeroPolynomial68 A B c d e := by
  rw [cubicHomogeneousRowZeroPolynomial68_eq_expanded]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [cubicHomogeneousRowZeroExpandedPolynomial68,
    firstSecondaryCoreRowZeroPolynomial68,
    cubicRemainderRowZeroPolynomial68,
    secondaryResidualRowZeroPolynomial68, derivative_add, derivative_mul,
    derivative_C, zero_mul, zero_add, Polynomial.smul_eq_C_mul, map_add,
    map_sub, map_mul, map_pow, map_neg, map_zero, RatFunc.algebraMap_C]
  simp only [map_div₀, map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 2000000 in
/-- The canonical expanded lower system has genuine strict degree drop in
both new residual coordinates throughout the first small-gap chamber. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_secondaryResidualDegreeDrops68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
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
    (secondaryDDefectPolynomial68 Ae Be De).natDegree < 5 * n - g ∧
      ee.natDegree < 6 * n - g := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  change 2 * g < n at hsmall
  change (secondaryDDefectPolynomial68 Ae Be De).natDegree < 5 * n - g ∧
    ee.natDegree < 6 * n - g
  have hsecondary :=
    maximalExpandedIntegratedPolynomialLowerSystem_secondaryRadius68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  have hclass :=
    maximalExpandedIntegratedPolynomialLowerSystem_secondarySmallGap68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsmall)
  change ee.coeff (6 * n - g) = 0 ∧
    Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
      3 * De.coeff (5 * n - g) at hclass
  have hA : Ae.natDegree ≤ 2 * n := by
    have hdrop :=
      maximalExpandedIntegratedPolynomialLowerSystem_degreeDrop68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys
    have hAe : Ae.natDegree = 2 * n := by
      simpa only [n, Ae, Be, Ce, De, Ee] using hdrop.1
    omega
  have hB : Be.natDegree ≤ 3 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.2.1
  have hD : De.natDegree ≤ 5 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
      hsecondary.2.2.2.1
  have he : ee.natDegree ≤ 6 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
      hsecondary.2.2.2.2.1
  exact firstSecondaryResidualDegreeDrops68 Ae Be De ee n g hsmall
    hA hB hD he hclass.2 hclass.1

end SecondaryResidualExtraction68

#print axioms secondaryDDefectPolynomial68_degree_lt
#print axioms firstSecondaryResidualDegreeDrops68
#print axioms cubicFirstIntegralFourPolynomial68_residualCoordinates
#print axioms cubicFirstIntegralThreePolynomial68_residualCoordinates
#print axioms secondaryResidualInvariantFourPolynomial68_coeff_middle
#print axioms secondaryResidualInvariantThreePolynomial68_coeff_middle
#print axioms polynomialSecondaryResidualBetweenFace68
#print axioms polynomialSecondaryResidualBetweenFace68_classify
#print axioms cubicHomogeneousRowTwoPolynomial68_residualCoordinates
#print axioms cubicHomogeneousRowOnePolynomial68_residualCoordinates
#print axioms cubicHomogeneousRowZeroPolynomial68_residualCoordinates
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_secondaryResidualDegreeDrops68

end Max11DegreeRoutes
