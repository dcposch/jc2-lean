import LowScale68SecondaryResidualExtraction

/-! # Row-two face on the balanced chamber `2h = 3g`

The residual first one-form rewrites through the incidence defect
`Q = B*e + c*d - B^3/9`.  After `Q.natDegree < 9*n - 3*g`, every `Q`
contribution lies strictly below the cubic face `11*n - 3*g - 1`.
The `B^2*d` derivative is likewise strictly below, because `g < h`
forces `11*n - 2*g - h - 1 < 11*n - 3*g - 1`.

On the balanced wall `2*h = 3*g` the remaining two Newton faces
coincide: `derivative(d*e)` and the `B,c` core
`-2*A*B^2*B' - (2/3)*A'*B^3 + 6*(B*c^2)'` both contribute at
`11*n - 3*g - 1`.  The middle-face discriminant `a*b^2+3*c^2=0`
collapses the core to `-(8/3)*(11*n-3*g)*a*b^3` in the inner
expression, equivalently `(8)*(11*n-3*g)*b*c^2`.  Adding the
`d*e` face `-(18)*(11*n-3*g)*d_top*e_top` yields the inner coefficient
`(2)*(11*n-3*g)*(4*b*c^2 - 9*d_top*e_top)`, hence the residual row-two
coefficient
`(-8/27)*(11*n-3*g)*(4*b*c^2 - 9*d_top*e_top)`.

In characteristic zero the prefactor is nonzero, so vanishing of row
two at this index is equivalent to the scalar relation
`4*b*c^2 - 9*d_top*e_top = 0`.  Constant-Jacobian loads may be omitted,
or supplied as an extra polynomial of degree strictly below the face.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section SecondaryResidualRowTwoBalanced68

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- Incidence defect `Q` through which row two is rewritten.  This is the
same polynomial as `secondaryResidualIncidenceDefectPolynomial68` in the
descent module; it is restated here so the module does not depend on
that module compiling. -/
def residualBalancedIncidenceQ68 (B c d e : k[X]) : k[X] :=
  B * e + c * d - (1 / 9 : k) • B ^ 3

/-- Inner expression of the row-two incidence rewrite, before `-4/27`. -/
def residualBalancedRowTwoInner68 (A B c d e : k[X]) : k[X] :=
  let Q := residualBalancedIncidenceQ68 B c d e
  (-6 : k) • (A * derivative Q) +
    (3 : k) • (derivative A * Q) +
    (-2 : k) • (A * B ^ 2 * derivative B) +
    (-2 / 3 : k) • (derivative A * B ^ 3) +
    (6 : k) • derivative (B ^ 2 * d) +
    (6 : k) • derivative (B * c ^ 2) +
    (-18 : k) • derivative (d * e)

set_option maxHeartbeats 4000000 in
/-- The residual first one-form is the inner `Q`-rewrite scaled by `-4/27`. -/
theorem residualBalancedRowTwo_eq_inner68 (A B c d e : k[X]) :
    secondaryResidualRowTwoPolynomial68 A B c d e =
      (-4 / 27 : k) • residualBalancedRowTwoInner68 A B c d e := by
  simp only [secondaryResidualRowTwoPolynomial68, residualBalancedRowTwoInner68,
    residualBalancedIncidenceQ68, derivative_add, derivative_sub, derivative_mul,
    derivative_pow, derivative_C, zero_mul, zero_add,
    Polynomial.smul_eq_C_mul]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [map_add, map_sub, map_mul, map_pow, map_neg,
    RatFunc.algebraMap_C, map_div₀, map_ofNat, map_natCast, map_one]
  simp only [Nat.reduceSub, pow_one, Nat.cast_ofNat]
  ring

/-- Field identity isolating the right-face core against `a*b^2+3*c^2`. -/
theorem residualBalancedRightCoreScalar68 (N G a b c : k) :
    (-2 : k) * (a * b ^ 3 * (3 * N - G)) -
      (2 / 3 : k) * (2 * N * a * b ^ 3) +
      (6 : k) * ((11 * N - 3 * G) * b * c ^ 2) =
      (2 : k) * (11 * N - 3 * G) * b *
          (a * b ^ 2 + (3 : k) * c ^ 2) -
        (8 / 3 : k) * (11 * N - 3 * G) * a * b ^ 3 := by
  ring

theorem residualBalancedRightCoreScalar68_of_disc
    (N G a b c : k) (hdisc : a * b ^ 2 + (3 : k) * c ^ 2 = 0) :
    (-2 : k) * (a * b ^ 3 * (3 * N - G)) -
      (2 / 3 : k) * (2 * N * a * b ^ 3) +
      (6 : k) * ((11 * N - 3 * G) * b * c ^ 2) =
      (-8 / 3 : k) * (11 * N - 3 * G) * a * b ^ 3 := by
  rw [residualBalancedRightCoreScalar68, hdisc]
  ring

/-- On the discriminant `a*b^2+3*c^2=0`, the coinciding core and `d*e`
faces combine as `2*M*(4*b*c^2-9*d*e)`. -/
theorem residualBalancedInnerScalar68 (M a b c d e : k)
    (hdisc : a * b ^ 2 + (3 : k) * c ^ 2 = 0) :
    (-8 / 3 : k) * M * a * b ^ 3 + (-18 : k) * M * d * e =
      (2 : k) * M * ((4 : k) * b * c ^ 2 - (9 : k) * d * e) := by
  linear_combination hdisc * ((-8 / 3 : k) * M * b)

/-- Scaling the inner identity by `-4/27` produces the residual row-two
prefactor `-8/27`. -/
theorem residualBalancedRowTwoScalar68 (M a b c d e : k)
    (hdisc : a * b ^ 2 + (3 : k) * c ^ 2 = 0) :
    (-4 / 27 : k) *
        ((-8 / 3 : k) * M * a * b ^ 3 + (-18 : k) * M * d * e) =
      (-8 / 27 : k) * M * ((4 : k) * b * c ^ 2 - (9 : k) * d * e) := by
  rw [residualBalancedInnerScalar68 M a b c d e hdisc]
  ring

private theorem residualBalanced_natDegree_mul_derivative_lt68
    (p q : k[X]) (u v : ℕ)
    (hu : p.natDegree ≤ u) (hv : 1 < v) (hq : q.natDegree < v) :
    (p * derivative q).natDegree < u + v - 1 := by
  have hq' : q.natDegree ≤ v - 1 := Nat.le_sub_one_of_lt hq
  have hd : (derivative q).natDegree ≤ v - 2 := by
    have h := natDegree_derivative_le q
    omega
  have hmul := natDegree_mul_le_of_le hu hd
  omega

private theorem residualBalanced_natDegree_derivative_mul_lt68
    (p q : k[X]) (u v : ℕ)
    (hu0 : 0 < u) (hu : p.natDegree ≤ u) (hq : q.natDegree < v) :
    (derivative p * q).natDegree < u + v - 1 := by
  have hd : (derivative p).natDegree ≤ u - 1 :=
    (natDegree_derivative_le p).trans (by omega)
  have hq' : q.natDegree ≤ v - 1 := Nat.le_sub_one_of_lt hq
  have hmul := natDegree_mul_le_of_le hd hq'
  omega

set_option maxHeartbeats 2000000 in
theorem residualBalancedRowTwoInner_Q_degree_lt68
    (A B c d e : k[X]) (n g : ℕ)
    (hsmall : 3 * g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hQ : (residualBalancedIncidenceQ68 B c d e).natDegree < 9 * n - 3 * g) :
    (A * derivative (residualBalancedIncidenceQ68 B c d e)).natDegree <
        11 * n - 3 * g - 1 ∧
      (derivative A * residualBalancedIncidenceQ68 B c d e).natDegree <
        11 * n - 3 * g - 1 := by
  have hv : 1 < 9 * n - 3 * g := by omega
  have h1 := residualBalanced_natDegree_mul_derivative_lt68 A
    (residualBalancedIncidenceQ68 B c d e) (2 * n) (9 * n - 3 * g) hA hv hQ
  have h2 := residualBalanced_natDegree_derivative_mul_lt68 A
    (residualBalancedIncidenceQ68 B c d e) (2 * n) (9 * n - 3 * g)
    (by omega) hA hQ
  have hi : 2 * n + (9 * n - 3 * g) - 1 = 11 * n - 3 * g - 1 := by omega
  exact ⟨by simpa only [hi] using h1, by simpa only [hi] using h2⟩

set_option maxHeartbeats 2000000 in
theorem residualBalancedRowTwoInner_Bd_degree_le68
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

set_option maxHeartbeats 6000000 in
/-- On `2h=3g`, residual row two has coefficient
`(-8/27)*(11n-3g)*(4*b*c_top^2-9*d_top*e_top)` at the common cubic face. -/
theorem residualRowTwo_coeff_balancedChamber68
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hsmall : 3 * g < n) (hbalanced : 2 * h = 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualBalancedIncidenceQ68 B c d e).natDegree < 9 * n - 3 * g)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0) :
    (secondaryResidualRowTwoPolynomial68 A B c d e).coeff
        (11 * n - 3 * g - 1) =
      (-8 / 27 : k) * ((11 * n - 3 * g : ℕ) : k) *
        ((4 : k) * B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 -
          (9 : k) * d.coeff (5 * n - h) * e.coeff (6 * n - h)) := by
  let Q := residualBalancedIncidenceQ68 B c d e
  let inner := residualBalancedRowTwoInner68 A B c d e
  set idx := 11 * n - 3 * g - 1
  have hface : 11 * n - 2 * h = 11 * n - 3 * g := by omega
  have hQdeg := residualBalancedRowTwoInner_Q_degree_lt68 A B c d e n g hsmall hA hQ
  have hAQ : (A * derivative Q).natDegree < idx := by
    dsimp [idx]
    exact hQdeg.1
  have hAQ' : (derivative A * Q).natDegree < idx := by
    dsimp [idx]
    exact hQdeg.2
  have hBd := residualBalancedRowTwoInner_Bd_degree_le68 B d n g h hg hgh hh hsmall hB hd
  have hBd' : (derivative (B ^ 2 * d)).natDegree < idx := by
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
  have hide : (5 * n - h) + (6 * n - h) = 11 * n - 2 * h := by omega
  have hdecoeff := coeff_mul_at_bounds68 d e (5 * n - h) (6 * n - h) hd he
  rw [hide] at hdecoeff
  have hder0 : 0 < 11 * n - 2 * h := by omega
  have hde := coeff_derivative_at_bound68 (d * e) (11 * n - 2 * h) hder0
  rw [hdecoeff] at hde
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
  have hde' : ((-18 : k) • derivative (d * e)).coeff idx =
      (-18 : k) * (d.coeff (5 * n - h) * e.coeff (6 * n - h) *
        ((11 * n - 3 * g : ℕ) : k)) := by
    rw [coeff_smul, smul_eq_mul]
    have hidx_de : 11 * n - 2 * h - 1 = idx := by
      dsimp [idx]
      omega
    rw [← hidx_de, hde, hface]
  have hcore :
      ((-2 : k) • (A * B ^ 2 * derivative B)).coeff idx +
        ((-2 / 3 : k) • (derivative A * B ^ 3)).coeff idx +
        ((6 : k) • derivative (B * c ^ 2)).coeff idx =
      (-8 / 3 : k) * ((11 * n - 3 * g : ℕ) : k) *
        A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 := by
    rw [hABsm, hA3sm, hBcsm, hcast3, hcast2, hcast11]
    have hsc := residualBalancedRightCoreScalar68_of_disc (n : k) (g : k)
      (A.coeff (2 * n)) (B.coeff (3 * n - g)) (c.coeff (4 * n - g)) hdisc
    convert hsc using 1
    ring
  have hinner : inner.coeff idx =
      (-8 / 3 : k) * ((11 * n - 3 * g : ℕ) : k) *
        A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 +
      (-18 : k) * ((11 * n - 3 * g : ℕ) : k) *
        d.coeff (5 * n - h) * e.coeff (6 * n - h) := by
    dsimp [inner, residualBalancedRowTwoInner68]
    simp only [coeff_add]
    rw [h0Q, h0Q', h0Bd, hde']
    linear_combination hcore
  rw [residualBalancedRowTwo_eq_inner68, coeff_smul, smul_eq_mul]
  change ((-4 / 27 : k) * inner.coeff idx) = _
  rw [hinner]
  exact residualBalancedRowTwoScalar68
    ((11 * n - 3 * g : ℕ) : k)
    (A.coeff (2 * n)) (B.coeff (3 * n - g)) (c.coeff (4 * n - g))
    (d.coeff (5 * n - h)) (e.coeff (6 * n - h)) hdisc

set_option maxHeartbeats 2000000 in
/-- Vanishing of the balanced cubic-face coefficient is equivalent to
`4*b*c_top^2 - 9*d_top*e_top = 0`. -/
theorem residualRowTwo_balanced_coeff_eq_zero_iff68
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hsmall : 3 * g < n) (hbalanced : 2 * h = 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualBalancedIncidenceQ68 B c d e).natDegree < 9 * n - 3 * g)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0) :
    (secondaryResidualRowTwoPolynomial68 A B c d e).coeff
        (11 * n - 3 * g - 1) = 0 ↔
      (4 : k) * B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 -
        (9 : k) * d.coeff (5 * n - h) * e.coeff (6 * n - h) = 0 := by
  rw [residualRowTwo_coeff_balancedChamber68 A B c d e n g h hg hgh hh hsmall
    hbalanced hA hB hc hd he hQ hdisc]
  constructor
  · intro h
    have hsc : (-8 / 27 : k) * ((11 * n - 3 * g : ℕ) : k) ≠ 0 :=
      mul_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr (by omega))
    exact (mul_eq_zero.mp h).resolve_left hsc
  · intro h
    rw [h, mul_zero]

/-- Residual row two identically zero implies the balanced scalar relation. -/
theorem residualRowTwo_eq_zero_imp_balancedRelation68
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hsmall : 3 * g < n) (hbalanced : 2 * h = 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualBalancedIncidenceQ68 B c d e).natDegree < 9 * n - 3 * g)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0)
    (hrow : secondaryResidualRowTwoPolynomial68 A B c d e = 0) :
    (4 : k) * B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 -
      (9 : k) * d.coeff (5 * n - h) * e.coeff (6 * n - h) = 0 := by
  have hcoeff :
      (secondaryResidualRowTwoPolynomial68 A B c d e).coeff
        (11 * n - 3 * g - 1) = 0 := by
    simp [hrow]
  exact (residualRowTwo_balanced_coeff_eq_zero_iff68 A B c d e n g h hg hgh hh
    hsmall hbalanced hA hB hc hd he hQ hdisc).1 hcoeff

/-- Same conclusion if residual row two cancels a load strictly below the
cubic face. -/
theorem residualRowTwo_add_load_eq_zero_imp_balancedRelation68
    (A B c d e load : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hsmall : 3 * g < n) (hbalanced : 2 * h = 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualBalancedIncidenceQ68 B c d e).natDegree < 9 * n - 3 * g)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0)
    (hload : load.natDegree < 11 * n - 3 * g - 1)
    (hsum : secondaryResidualRowTwoPolynomial68 A B c d e + load = 0) :
    (4 : k) * B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 -
      (9 : k) * d.coeff (5 * n - h) * e.coeff (6 * n - h) = 0 := by
  have hcoeff :
      (secondaryResidualRowTwoPolynomial68 A B c d e).coeff
        (11 * n - 3 * g - 1) = 0 := by
    have h := congrArg (fun p : k[X] => p.coeff (11 * n - 3 * g - 1)) hsum
    rw [coeff_add, coeff_zero,
      coeff_eq_zero_of_natDegree_lt hload, add_zero] at h
    exact h
  exact (residualRowTwo_balanced_coeff_eq_zero_iff68 A B c d e n g h hg hgh hh
    hsmall hbalanced hA hB hc hd he hQ hdisc).1 hcoeff

end SecondaryResidualRowTwoBalanced68

#print axioms residualBalancedRowTwo_eq_inner68
#print axioms residualBalancedRightCoreScalar68_of_disc
#print axioms residualBalancedInnerScalar68
#print axioms residualBalancedRowTwoScalar68
#print axioms residualBalancedRowTwoInner_Q_degree_lt68
#print axioms residualRowTwo_coeff_balancedChamber68
#print axioms residualRowTwo_balanced_coeff_eq_zero_iff68
#print axioms residualRowTwo_eq_zero_imp_balancedRelation68
#print axioms residualRowTwo_add_load_eq_zero_imp_balancedRelation68

end Max11DegreeRoutes
