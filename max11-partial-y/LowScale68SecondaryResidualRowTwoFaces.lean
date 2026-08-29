import LowScale68SecondaryResidualExtraction

/-! # Row-two faces in the strict chambers `2h<3g` and `3g<2h`

The residual first one-form rewrites through the incidence defect
`Q = B*e + c*d - B^3/9`.  After `Q.natDegree < 9*n - 3*g`, every `Q`
contribution lies strictly below the cubic face `11*n - 3*g - 1`.

The remaining Newton comparison is `2h` versus `3g`.

* Left chamber `2h < 3g`: `derivative(d*e)` dominates.  The coefficient at
  `11*n - 2*h - 1` is `(8/3)*(11*n-2*h)*d_top*e_top`.
* Right chamber `3g < 2h`: the `B,c` core
  `-2*A*B^2*B' - (2/3)*A'*B^3 + 6*(B*c^2)'` dominates.  The middle-face
  relation `a*b^2+3*c^2=0` collapses it to
  `-(8/3)*(11*n-3*g)*a*b^3` in the inner expression, hence
  `(32/81)*(11*n-3*g)*a*b^3` in row two.

Both scalars are nonzero in characteristic zero under the standing gap
inequalities.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section SecondaryResidualRowTwoFaces68

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- Incidence defect `Q` through which row two is rewritten.  This is the
same polynomial as `secondaryResidualIncidenceDefectPolynomial68` in the
descent module; it is restated here so the module does not depend on
that module compiling. -/
def residualIncidenceQ68 (B c d e : k[X]) : k[X] :=
  B * e + c * d - (1 / 9 : k) • B ^ 3

/-- Inner expression of the row-two incidence rewrite, before `-4/27`. -/
def residualRowTwoInner68 (A B c d e : k[X]) : k[X] :=
  let Q := residualIncidenceQ68 B c d e
  (-6 : k) • (A * derivative Q) +
    (3 : k) • (derivative A * Q) +
    (-2 : k) • (A * B ^ 2 * derivative B) +
    (-2 / 3 : k) • (derivative A * B ^ 3) +
    (6 : k) • derivative (B ^ 2 * d) +
    (6 : k) • derivative (B * c ^ 2) +
    (-18 : k) • derivative (d * e)

set_option maxHeartbeats 4000000 in
/-- The residual first one-form is the inner `Q`-rewrite scaled by `-4/27`. -/
theorem residualRowTwo_eq_inner68 (A B c d e : k[X]) :
    secondaryResidualRowTwoPolynomial68 A B c d e =
      (-4 / 27 : k) • residualRowTwoInner68 A B c d e := by
  simp only [secondaryResidualRowTwoPolynomial68, residualRowTwoInner68,
    residualIncidenceQ68, derivative_add, derivative_sub, derivative_mul,
    derivative_pow, derivative_C, zero_mul, zero_add,
    Polynomial.smul_eq_C_mul]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [map_add, map_sub, map_mul, map_pow, map_neg,
    RatFunc.algebraMap_C, map_div₀, map_ofNat, map_natCast, map_one]
  simp only [Nat.reduceSub, pow_one, Nat.cast_ofNat]
  ring

/-- Field identity isolating the right-face core against `a*b^2+3*c^2`. -/
theorem residualRowTwoRightCoreScalar68 (N G a b c : k) :
    (-2 : k) * (a * b ^ 3 * (3 * N - G)) -
      (2 / 3 : k) * (2 * N * a * b ^ 3) +
      (6 : k) * ((11 * N - 3 * G) * b * c ^ 2) =
      (2 : k) * (11 * N - 3 * G) * b *
          (a * b ^ 2 + (3 : k) * c ^ 2) -
        (8 / 3 : k) * (11 * N - 3 * G) * a * b ^ 3 := by
  ring

theorem residualRowTwoRightCoreScalar68_of_disc
    (N G a b c : k) (hdisc : a * b ^ 2 + (3 : k) * c ^ 2 = 0) :
    (-2 : k) * (a * b ^ 3 * (3 * N - G)) -
      (2 / 3 : k) * (2 * N * a * b ^ 3) +
      (6 : k) * ((11 * N - 3 * G) * b * c ^ 2) =
      (-8 / 3 : k) * (11 * N - 3 * G) * a * b ^ 3 := by
  rw [residualRowTwoRightCoreScalar68, hdisc]
  ring

private theorem residual_natDegree_mul_derivative_lt68
    (p q : k[X]) (u v : ℕ)
    (hu : p.natDegree ≤ u) (hv : 1 < v) (hq : q.natDegree < v) :
    (p * derivative q).natDegree < u + v - 1 := by
  have hq' : q.natDegree ≤ v - 1 := Nat.le_sub_one_of_lt hq
  have hd : (derivative q).natDegree ≤ v - 2 := by
    have h := natDegree_derivative_le q
    omega
  have hmul := natDegree_mul_le_of_le hu hd
  omega

private theorem residual_natDegree_derivative_mul_lt68
    (p q : k[X]) (u v : ℕ)
    (hu0 : 0 < u) (hu : p.natDegree ≤ u) (hq : q.natDegree < v) :
    (derivative p * q).natDegree < u + v - 1 := by
  have hd : (derivative p).natDegree ≤ u - 1 :=
    (natDegree_derivative_le p).trans (by omega)
  have hq' : q.natDegree ≤ v - 1 := Nat.le_sub_one_of_lt hq
  have hmul := natDegree_mul_le_of_le hd hq'
  omega

set_option maxHeartbeats 2000000 in
theorem residualRowTwoInner_Q_degree_lt68
    (A B c d e : k[X]) (n g : ℕ)
    (hsmall : 3 * g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hQ : (residualIncidenceQ68 B c d e).natDegree < 9 * n - 3 * g) :
    (A * derivative (residualIncidenceQ68 B c d e)).natDegree <
        11 * n - 3 * g - 1 ∧
      (derivative A * residualIncidenceQ68 B c d e).natDegree <
        11 * n - 3 * g - 1 := by
  have hv : 1 < 9 * n - 3 * g := by omega
  have h1 := residual_natDegree_mul_derivative_lt68 A
    (residualIncidenceQ68 B c d e) (2 * n) (9 * n - 3 * g) hA hv hQ
  have h2 := residual_natDegree_derivative_mul_lt68 A
    (residualIncidenceQ68 B c d e) (2 * n) (9 * n - 3 * g)
    (by omega) hA hQ
  have hi : 2 * n + (9 * n - 3 * g) - 1 = 11 * n - 3 * g - 1 := by omega
  exact ⟨by simpa only [hi] using h1, by simpa only [hi] using h2⟩

set_option maxHeartbeats 2000000 in
theorem residualRowTwoInner_Bd_degree_le68
    (B d : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g) (hsmall : 3 * g < n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hd : d.natDegree ≤ 5 * n - h) :
    (derivative (B ^ 2 * d)).natDegree ≤ 11 * n - 2 * g - h - 1 := by
  have hB2 : (B ^ 2).natDegree ≤ 6 * n - 2 * g := by
    compute_degree
    omega
  have hprod := natDegree_mul_le_of_le hB2 hd
  have hsum : 6 * n - 2 * g + (5 * n - h) = 11 * n - 2 * g - h := by omega
  rw [hsum] at hprod
  have hder := natDegree_derivative_le (B ^ 2 * d)
  omega

set_option maxHeartbeats 2000000 in
theorem residualRowTwoInner_BcCore_degree_le68
    (A B c : k[X]) (n g : ℕ)
    (hg : 0 < g) (hsmall : 3 * g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g) :
    (A * B ^ 2 * derivative B).natDegree ≤ 11 * n - 3 * g - 1 ∧
      (derivative A * B ^ 3).natDegree ≤ 11 * n - 3 * g - 1 ∧
      (derivative (B * c ^ 2)).natDegree ≤ 11 * n - 3 * g - 1 := by
  have hB2 : (B ^ 2).natDegree ≤ 6 * n - 2 * g := by
    compute_degree
    omega
  have hB3 : (B ^ 3).natDegree ≤ 9 * n - 3 * g := by
    compute_degree
    omega
  have hc2 : (c ^ 2).natDegree ≤ 8 * n - 2 * g := by
    compute_degree
    omega
  have hdB : (derivative B).natDegree ≤ 3 * n - g - 1 :=
    (natDegree_derivative_le B).trans (by omega)
  have hdA : (derivative A).natDegree ≤ 2 * n - 1 :=
    (natDegree_derivative_le A).trans (by omega)
  have hAB2 := natDegree_mul_le_of_le hA hB2
  have hAB2d := natDegree_mul_le_of_le hAB2 hdB
  have hA3 := natDegree_mul_le_of_le hdA hB3
  have hBc2 := natDegree_mul_le_of_le hB hc2
  have hdBc2 := natDegree_derivative_le (B * c ^ 2)
  refine ⟨by omega, by omega, by omega⟩

set_option maxHeartbeats 2000000 in
theorem residualRowTwoInner_de_degree_le68
    (d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g) (hsmall : 3 * g < n)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (derivative (d * e)).natDegree ≤ 11 * n - 2 * h - 1 := by
  have hprod := natDegree_mul_le_of_le hd he
  have hsum : (5 * n - h) + (6 * n - h) = 11 * n - 2 * h := by omega
  rw [hsum] at hprod
  have hder := natDegree_derivative_le (d * e)
  omega

set_option maxHeartbeats 4000000 in
/-- On `2h<3g`, residual row two is dominated by `derivative(d*e)`. -/
theorem residualRowTwo_coeff_leftChamber68
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hsmall : 3 * g < n) (hleft : 2 * h < 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualIncidenceQ68 B c d e).natDegree < 9 * n - 3 * g) :
    (secondaryResidualRowTwoPolynomial68 A B c d e).coeff
        (11 * n - 2 * h - 1) =
      (8 / 3 : k) * ((11 * n - 2 * h : ℕ) : k) *
        d.coeff (5 * n - h) * e.coeff (6 * n - h) := by
  let Q := residualIncidenceQ68 B c d e
  let inner := residualRowTwoInner68 A B c d e
  set idx := 11 * n - 2 * h - 1
  have hidx : 11 * n - 3 * g - 1 < idx := by
    dsimp [idx]
    omega
  have hQdeg := residualRowTwoInner_Q_degree_lt68 A B c d e n g hsmall hA hQ
  have hAQ : (A * derivative Q).natDegree < idx := hQdeg.1.trans hidx
  have hAQ' : (derivative A * Q).natDegree < idx := hQdeg.2.trans hidx
  have hcore := residualRowTwoInner_BcCore_degree_le68 A B c n g hg hsmall hA hB hc
  have hAB : (A * B ^ 2 * derivative B).natDegree < idx :=
    hcore.1.trans_lt hidx
  have hA3 : (derivative A * B ^ 3).natDegree < idx :=
    hcore.2.1.trans_lt hidx
  have hBc : (derivative (B * c ^ 2)).natDegree < idx :=
    hcore.2.2.trans_lt hidx
  have hBd := residualRowTwoInner_Bd_degree_le68 B d n g h hg hgh hh hsmall hB hd
  have hBd' : (derivative (B ^ 2 * d)).natDegree < idx := by
    dsimp [idx]
    omega
  have hdebound := natDegree_mul_le_of_le hd he
  have hide : (5 * n - h) + (6 * n - h) = 11 * n - 2 * h := by omega
  rw [hide] at hdebound
  have hdecoeff := coeff_mul_at_bounds68 d e (5 * n - h) (6 * n - h) hd he
  rw [hide] at hdecoeff
  have hder0 : 0 < 11 * n - 2 * h := by omega
  have hde := coeff_derivative_at_bound68 (d * e) (11 * n - 2 * h) hder0
  rw [hdecoeff] at hde
  have h0Q : ((-6 : k) • (A * derivative Q)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hAQ, mul_zero]
  have h0Q' : ((3 : k) • (derivative A * Q)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hAQ', mul_zero]
  have h0AB : ((-2 : k) • (A * B ^ 2 * derivative B)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hAB, mul_zero]
  have h0A3 : ((-2 / 3 : k) • (derivative A * B ^ 3)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hA3, mul_zero]
  have h0Bd : ((6 : k) • derivative (B ^ 2 * d)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hBd', mul_zero]
  have h0Bc : ((6 : k) • derivative (B * c ^ 2)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hBc, mul_zero]
  have hde' : ((-18 : k) • derivative (d * e)).coeff idx =
      (-18 : k) * (d.coeff (5 * n - h) * e.coeff (6 * n - h) *
        ((11 * n - 2 * h : ℕ) : k)) := by
    rw [coeff_smul, smul_eq_mul]
    dsimp [idx]
    rw [hde]
  have hinner : inner.coeff idx =
      (-18 : k) * (d.coeff (5 * n - h) * e.coeff (6 * n - h) *
        ((11 * n - 2 * h : ℕ) : k)) := by
    dsimp [inner, residualRowTwoInner68]
    simp only [coeff_add]
    rw [h0Q, h0Q', h0AB, h0A3, h0Bd, h0Bc, hde']
    ring
  rw [residualRowTwo_eq_inner68, coeff_smul, smul_eq_mul]
  change ((-4 / 27 : k) * inner.coeff idx) = _
  rw [hinner]
  ring

set_option maxHeartbeats 2000000 in
theorem residualRowTwo_leftChamber_ne_zero68
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hsmall : 3 * g < n) (hleft : 2 * h < 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualIncidenceQ68 B c d e).natDegree < 9 * n - 3 * g)
    (hd0 : d.coeff (5 * n - h) ≠ 0)
    (he0 : e.coeff (6 * n - h) ≠ 0) :
    (secondaryResidualRowTwoPolynomial68 A B c d e).coeff
        (11 * n - 2 * h - 1) ≠ 0 := by
  rw [residualRowTwo_coeff_leftChamber68 A B c d e n g h hg hgh hh hsmall hleft
    hA hB hc hd he hQ]
  have hscalar : (8 / 3 : k) ≠ 0 := by norm_num
  have hN : ((11 * n - 2 * h : ℕ) : k) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by omega)
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hscalar hN) hd0) he0

set_option maxHeartbeats 4000000 in
/-- On `3g<2h`, residual row two is dominated by the `B,c` core. -/
theorem residualRowTwo_coeff_rightChamber68
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hsmall : 3 * g < n) (hright : 3 * g < 2 * h)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualIncidenceQ68 B c d e).natDegree < 9 * n - 3 * g)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0) :
    (secondaryResidualRowTwoPolynomial68 A B c d e).coeff
        (11 * n - 3 * g - 1) =
      (32 / 81 : k) * ((11 * n - 3 * g : ℕ) : k) *
        A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 := by
  let Q := residualIncidenceQ68 B c d e
  let inner := residualRowTwoInner68 A B c d e
  set idx := 11 * n - 3 * g - 1
  have hQdeg := residualRowTwoInner_Q_degree_lt68 A B c d e n g hsmall hA hQ
  have hAQ : (A * derivative Q).natDegree < idx := by
    dsimp [idx]
    exact hQdeg.1
  have hAQ' : (derivative A * Q).natDegree < idx := by
    dsimp [idx]
    exact hQdeg.2
  have hBd := residualRowTwoInner_Bd_degree_le68 B d n g h hg hgh hh hsmall hB hd
  have hBd' : (derivative (B ^ 2 * d)).natDegree < idx := by
    dsimp [idx]
    omega
  have hde := residualRowTwoInner_de_degree_le68 d e n g h hg hgh hh hsmall hd he
  have hde' : (derivative (d * e)).natDegree < idx := by
    dsimp [idx]
    omega
  have hB2deg : (B ^ 2).natDegree ≤ 6 * n - 2 * g := by
    compute_degree
    omega
  have hB2 : (B ^ 2).coeff (6 * n - 2 * g) =
      B.coeff (3 * n - g) ^ 2 := by
    have h := coeff_pow_at_bound68 B (3 * n - g) 2 hB
    have hi : 2 * (3 * n - g) = 6 * n - 2 * g := by omega
    simpa only [hi] using h
  have hAB := coeff_mul_mul_derivative_at_bounds68 A (B ^ 2) B
    (2 * n) (6 * n - 2 * g) (3 * n - g) (by omega) hA hB2deg hB
  have hiAB : 2 * n + (6 * n - 2 * g) + (3 * n - g) - 1 = idx := by
    dsimp [idx]
    omega
  rw [hiAB, hB2] at hAB
  have hABpow : (A * B ^ 2 * derivative B).coeff idx =
      A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 *
        ((3 * n - g : ℕ) : k) := by
    rw [hAB]
    ring
  have hB3deg : (B ^ 3).natDegree ≤ 9 * n - 3 * g := by
    compute_degree
    omega
  have hB3 : (B ^ 3).coeff (9 * n - 3 * g) =
      B.coeff (3 * n - g) ^ 3 := by
    have h := coeff_pow_at_bound68 B (3 * n - g) 3 hB
    have hi : 3 * (3 * n - g) = 9 * n - 3 * g := by omega
    simpa only [hi] using h
  have hA3 := coeff_mul_derivative_at_bounds68 (B ^ 3) A
    (9 * n - 3 * g) (2 * n) (by omega) hB3deg hA
  have hiA3 : (9 * n - 3 * g) + 2 * n - 1 = idx := by
    dsimp [idx]
    omega
  rw [hiA3, hB3] at hA3
  have hA3' : (derivative A * B ^ 3).coeff idx =
      A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 *
        ((2 * n : ℕ) : k) := by
    rw [show (derivative A * B ^ 3).coeff idx =
        (B ^ 3 * derivative A).coeff idx by
      congr 1
      ring]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hA3
  have hc2deg : (c ^ 2).natDegree ≤ 8 * n - 2 * g := by
    compute_degree
    omega
  have hc2 : (c ^ 2).coeff (8 * n - 2 * g) =
      c.coeff (4 * n - g) ^ 2 := by
    have h := coeff_pow_at_bound68 c (4 * n - g) 2 hc
    have hi : 2 * (4 * n - g) = 8 * n - 2 * g := by omega
    simpa only [hi] using h
  have hBcdeg : (B * c ^ 2).natDegree ≤ 11 * n - 3 * g := by
    have h := natDegree_mul_le_of_le hB hc2deg
    have hi : (3 * n - g) + (8 * n - 2 * g) = 11 * n - 3 * g := by omega
    rwa [hi] at h
  have hBccoeff := coeff_mul_at_bounds68 B (c ^ 2)
    (3 * n - g) (8 * n - 2 * g) hB hc2deg
  have hiBc : (3 * n - g) + (8 * n - 2 * g) = 11 * n - 3 * g := by omega
  rw [hiBc, hc2] at hBccoeff
  have hBc := coeff_derivative_at_bound68 (B * c ^ 2)
    (11 * n - 3 * g) (by omega)
  rw [hBccoeff] at hBc
  have hcast3 : (((3 * n - g : ℕ) : k)) =
      (3 : k) * (n : k) - (g : k) := by
    rw [Nat.cast_sub (by omega : g ≤ 3 * n)]
    push_cast
    rfl
  have hcast2 : (((2 * n : ℕ) : k)) = (2 : k) * (n : k) := by
    push_cast
    rfl
  have hcast11 : (((11 * n - 3 * g : ℕ) : k)) =
      (11 : k) * (n : k) - (3 : k) * (g : k) := by
    rw [Nat.cast_sub (by omega : 3 * g ≤ 11 * n)]
    push_cast
    rfl
  have h0Q : ((-6 : k) • (A * derivative Q)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hAQ, mul_zero]
  have h0Q' : ((3 : k) • (derivative A * Q)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hAQ', mul_zero]
  have h0Bd : ((6 : k) • derivative (B ^ 2 * d)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hBd', mul_zero]
  have h0de : ((-18 : k) • derivative (d * e)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hde', mul_zero]
  have hABsm : ((-2 : k) • (A * B ^ 2 * derivative B)).coeff idx =
      (-2 : k) * (A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 *
        ((3 * n - g : ℕ) : k)) := by
    rw [coeff_smul, smul_eq_mul, hABpow]
  have hA3sm : ((-2 / 3 : k) • (derivative A * B ^ 3)).coeff idx =
      (-2 / 3 : k) * (A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 *
        ((2 * n : ℕ) : k)) := by
    rw [coeff_smul, smul_eq_mul, hA3']
  have hBcsm : ((6 : k) • derivative (B * c ^ 2)).coeff idx =
      (6 : k) * (B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 *
        ((11 * n - 3 * g : ℕ) : k)) := by
    rw [coeff_smul, smul_eq_mul]
    dsimp [idx]
    rw [hBc]
  have hinner : inner.coeff idx =
      (-8 / 3 : k) * ((11 * n - 3 * g : ℕ) : k) *
        A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 := by
    dsimp [inner, residualRowTwoInner68]
    simp only [coeff_add]
    rw [h0Q, h0Q', h0Bd, h0de, hABsm, hA3sm, hBcsm, hcast3, hcast2, hcast11]
    have hsc := residualRowTwoRightCoreScalar68_of_disc (n : k) (g : k)
      (A.coeff (2 * n)) (B.coeff (3 * n - g)) (c.coeff (4 * n - g)) hdisc
    convert hsc using 1
    ring
  rw [residualRowTwo_eq_inner68, coeff_smul, smul_eq_mul]
  change ((-4 / 27 : k) * inner.coeff idx) = _
  rw [hinner]
  ring

set_option maxHeartbeats 2000000 in
theorem residualRowTwo_rightChamber_ne_zero68
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hsmall : 3 * g < n) (hright : 3 * g < 2 * h)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualIncidenceQ68 B c d e).natDegree < 9 * n - 3 * g)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0)
    (ha0 : A.coeff (2 * n) ≠ 0)
    (hb0 : B.coeff (3 * n - g) ≠ 0) :
    (secondaryResidualRowTwoPolynomial68 A B c d e).coeff
        (11 * n - 3 * g - 1) ≠ 0 := by
  rw [residualRowTwo_coeff_rightChamber68 A B c d e n g h hg hgh hh hsmall hright
    hA hB hc hd he hQ hdisc]
  have hscalar : (32 / 81 : k) ≠ 0 := by norm_num
  have hN : ((11 * n - 3 * g : ℕ) : k) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by omega)
  exact mul_ne_zero
    (mul_ne_zero (mul_ne_zero hscalar hN) ha0) (pow_ne_zero 3 hb0)

end SecondaryResidualRowTwoFaces68

#print axioms residualRowTwo_eq_inner68
#print axioms residualRowTwoRightCoreScalar68_of_disc
#print axioms residualRowTwoInner_Q_degree_lt68
#print axioms residualRowTwo_coeff_leftChamber68
#print axioms residualRowTwo_leftChamber_ne_zero68
#print axioms residualRowTwo_coeff_rightChamber68
#print axioms residualRowTwo_rightChamber_ne_zero68

end Max11DegreeRoutes
