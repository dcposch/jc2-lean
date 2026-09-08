import LowScale68SecondaryResidualExtraction

/-! # Balanced-chamber row-one and row-zero faces after `2h = 3g`

On the selected residual middle face the leading scalars satisfy
`b*e + c*d = 0` and `a*b^2 + 3*c^2 = 0`.  Residual row two on the
balanced wall `2*h = 3*g` then forces `4*b*c^2 - 9*d*e = 0`.

Row one rewrites through the cubic combination
`S = A*B*d - 3*c*e` and the residual cubic invariant `I3`.  The old
top `12*n - g - h - 1` is `(-8/27)*a*(10*n-g-h)*(a*b*d-3*c*e)` and
vanishes by the middle-face cubic relation.  After
`I3.natDegree < 10*n - 3*g`, `S` drops to the cubic face
`10*n - 3*g`, and `2*(A*S)'` meets `6*(c^3)'` and `-18*(e*e')` at
`12*n - 3*g - 1`.  The inner coefficient collapses to
`48*(4*n-g)*c_top^3`, hence residual row one has coefficient
`(-64/9)*(4*n-g)*c_top^3`.  In characteristic zero this is nonzero
on the attained middle face, so row one cannot vanish there.

Row zero rewrites through the incidence defect `Q`.  Its old top
`13*n - g - h - 1` vanishes by `b*e+c*d=0`.  After `Q.natDegree < 9*n-3*g`
the cubic face `13*n - 3*g - 1` has coefficient
`(8*n/81)*a*(4*b*c^2-9*d*e)`, which is zero by the row-two relation.
Row zero therefore yields no new obstruction at this index.

Constant-Jacobian loads and the system-level identification of `I3`
and `Q` with the first integrals are not discharged here.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section GrokBalancedLowerRows68

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- Cubic combination whose old top is the middle-face relation
`-a*b*d + 3*c*e = 0`. -/
def grokBalancedCubicS68 (A B c d e : k[X]) : k[X] :=
  A * B * d - (3 : k) • (c * e)

/-- Incidence defect, copied so this scratch does not import descent. -/
def grokBalancedIncidenceQ68 (B c d e : k[X]) : k[X] :=
  B * e + c * d - (1 / 9 : k) • B ^ 3

/-- Inner expression of residual row one after the `S`/`I3` rewrite,
before the overall factor `-4/27`. -/
def grokBalancedRowOneInner68 (A B c d e : k[X]) : k[X] :=
  (2 : k) • derivative (A * grokBalancedCubicS68 A B c d e) +
    (9 / 4 : k) •
      (derivative A * secondaryResidualInvariantThreePolynomial68 A B c d e) +
    (6 : k) • (c ^ 2 * derivative c) +
    (3 : k) • derivative (B * c * d) +
    (6 : k) • (derivative B * c * d) -
    (3 : k) • (B ^ 2 * derivative e) -
    (18 : k) • (e * derivative e)

/-- Inner expression of residual row zero after the `Q` rewrite,
before the overall factor `4/27`. -/
def grokBalancedRowZeroInner68 (A B c d e : k[X]) : k[X] :=
  let Q := grokBalancedIncidenceQ68 B c d e
  -(A * derivative A * Q) -
    (1 / 9 : k) • (A * derivative A * B ^ 3) +
    derivative A * B * c ^ 2 -
    (3 : k) • (derivative A * d * e) -
    A * B ^ 2 * derivative d -
    A * B * derivative B * d +
    (3 : k) • (B * c * derivative e) -
    (3 : k) • (B * d * derivative d) -
    (3 : k) • (derivative B * d ^ 2) -
    (3 : k) • (c * derivative c * d)

/-! ## Field algebra on the middle face plus `4*b*c^2-9*d*e=0` -/

theorem grokBalanced_disc_imp_b_ne_zero68
    (a b c : k) (hc : c ≠ 0)
    (hdisc : a * b ^ 2 + (3 : k) * c ^ 2 = 0) : b ≠ 0 := by
  intro hb
  have : (3 : k) * c ^ 2 = 0 := by simpa [hb] using hdisc
  have hc2 : c ^ 2 = 0 := (mul_eq_zero.mp this).resolve_left (by norm_num)
  exact hc (pow_eq_zero hc2)

theorem grokBalanced_nine_d_sq_of_relations68
    (a b c d e : k) (hc : c ≠ 0)
    (hdisc : a * b ^ 2 + (3 : k) * c ^ 2 = 0)
    (hinc : b * e + c * d = 0)
    (hrel : (4 : k) * b * c ^ 2 - (9 : k) * d * e = 0) :
    (9 : k) * d ^ 2 + (4 : k) * b ^ 2 * c = 0 := by
  have hprod : c * ((9 : k) * d ^ 2 + (4 : k) * b ^ 2 * c) = 0 := by
    have hcd : c * d = -b * e := by linear_combination hinc
    have h4 : (4 : k) * b * c ^ 2 = (9 : k) * d * e := by linear_combination hrel
    calc
      c * ((9 : k) * d ^ 2 + (4 : k) * b ^ 2 * c)
          = (9 : k) * c * d ^ 2 + (4 : k) * b ^ 2 * c ^ 2 := by ring
      _ = (9 : k) * d * (c * d) + b * ((4 : k) * b * c ^ 2) := by ring
      _ = (9 : k) * d * (-b * e) + b * ((9 : k) * d * e) := by rw [hcd, h4]
      _ = 0 := by ring
  exact (mul_eq_zero.mp hprod).resolve_left hc

theorem grokBalanced_nine_e_sq_of_relations68
    (a b c d e : k) (hc : c ≠ 0)
    (hdisc : a * b ^ 2 + (3 : k) * c ^ 2 = 0)
    (hinc : b * e + c * d = 0)
    (hrel : (4 : k) * b * c ^ 2 - (9 : k) * d * e = 0) :
    (9 : k) * e ^ 2 + (4 : k) * c ^ 3 = 0 := by
  have hb := grokBalanced_disc_imp_b_ne_zero68 a b c hc hdisc
  have hd := grokBalanced_nine_d_sq_of_relations68 a b c d e hc hdisc hinc hrel
  have hbe : b * e = -c * d := by linear_combination hinc
  have hprod : b ^ 2 * ((9 : k) * e ^ 2 + (4 : k) * c ^ 3) = 0 := by
    calc
      b ^ 2 * ((9 : k) * e ^ 2 + (4 : k) * c ^ 3)
          = (9 : k) * (b * e) ^ 2 + (4 : k) * b ^ 2 * c ^ 3 := by ring
      _ = (9 : k) * (-c * d) ^ 2 + (4 : k) * b ^ 2 * c ^ 3 := by rw [hbe]
      _ = c ^ 2 * ((9 : k) * d ^ 2 + (4 : k) * b ^ 2 * c) := by ring
      _ = 0 := by rw [hd, mul_zero]
  exact (mul_eq_zero.mp hprod).resolve_left (pow_ne_zero 2 hb)

/-- After discriminant, incidence, the row-two relation, and `2H=3G`,
the inner cubic-face combination of row one is `48*(4N-G)*c^3`. -/
theorem grokBalancedRowOneCubicInnerScalar68
    (N G H a b c d e : k) (hc : c ≠ 0)
    (hbal : (2 : k) * H = (3 : k) * G)
    (hdisc : a * b ^ 2 + (3 : k) * c ^ 2 = 0)
    (hinc : b * e + c * d = 0)
    (hrel : (4 : k) * b * c ^ 2 - (9 : k) * d * e = 0) :
    a * ((3 : k) * d ^ 2 - (2 : k) * b ^ 2 * c) * ((12 : k) * N - (3 : k) * G) +
        (6 : k) * ((4 : k) * N - G) * c ^ 3 -
        (18 : k) * ((6 : k) * N - H) * e ^ 2 =
      (48 : k) * ((4 : k) * N - G) * c ^ 3 := by
  have hb := grokBalanced_disc_imp_b_ne_zero68 a b c hc hdisc
  have hd := grokBalanced_nine_d_sq_of_relations68 a b c d e hc hdisc hinc hrel
  have he := grokBalanced_nine_e_sq_of_relations68 a b c d e hc hdisc hinc hrel
  have hab : a * b ^ 2 = -(3 : k) * c ^ 2 := by linear_combination hdisc
  have hd' : (3 : k) * d ^ 2 = -((4 : k) / 3) * b ^ 2 * c := by
    linear_combination (1 / 3 : k) * hd
  have hcore : (3 : k) * d ^ 2 - (2 : k) * b ^ 2 * c =
      -((10 : k) / 3) * b ^ 2 * c := by
    rw [hd']
    ring
  have hAterm : a * ((3 : k) * d ^ 2 - (2 : k) * b ^ 2 * c) =
      (10 : k) * c ^ 3 := by
    rw [hcore]
    have hclear : a * (-((10 : k) / 3) * b ^ 2 * c) =
        -((10 : k) / 3) * (a * b ^ 2) * c := by ring
    rw [hclear, hab]
    ring
  have he2 : e ^ 2 = -((4 : k) / 9) * c ^ 3 := by
    linear_combination (1 / 9 : k) * he
  rw [hAterm, he2, hbal]
  ring

/-- Scaling the inner cubic identity by `-4/27` produces the residual
row-one prefactor `-64/9`. -/
theorem grokBalancedRowOneCubicScalar68
    (N G H a b c d e : k) (hc : c ≠ 0)
    (hbal : (2 : k) * H = (3 : k) * G)
    (hdisc : a * b ^ 2 + (3 : k) * c ^ 2 = 0)
    (hinc : b * e + c * d = 0)
    (hrel : (4 : k) * b * c ^ 2 - (9 : k) * d * e = 0) :
    (-4 / 27 : k) *
        (a * ((3 : k) * d ^ 2 - (2 : k) * b ^ 2 * c) *
            ((12 : k) * N - (3 : k) * G) +
          (6 : k) * ((4 : k) * N - G) * c ^ 3 -
          (18 : k) * ((6 : k) * N - H) * e ^ 2) =
      (-64 / 9 : k) * ((4 : k) * N - G) * c ^ 3 := by
  rw [grokBalancedRowOneCubicInnerScalar68 N G H a b c d e hc hbal
    hdisc hinc hrel]
  ring

theorem grokBalancedRowOneCubic_ne_zero68
    (N G H a b c d e : k) (hc : c ≠ 0)
    (hNG : (4 : k) * N - G ≠ 0)
    (hbal : (2 : k) * H = (3 : k) * G)
    (hdisc : a * b ^ 2 + (3 : k) * c ^ 2 = 0)
    (hinc : b * e + c * d = 0)
    (hrel : (4 : k) * b * c ^ 2 - (9 : k) * d * e = 0) :
    (-64 / 9 : k) * ((4 : k) * N - G) * c ^ 3 ≠ 0 :=
  mul_ne_zero (mul_ne_zero (by norm_num) hNG) (pow_ne_zero 3 hc)

/-- Vanishing of the simplified row-one cubic coefficient is impossible
on a nontrivial middle face. -/
theorem grokBalancedRowOneCubic_scalarContradiction68
    (N G H a b c d e : k) (hc : c ≠ 0)
    (hNG : (4 : k) * N - G ≠ 0)
    (hbal : (2 : k) * H = (3 : k) * G)
    (hdisc : a * b ^ 2 + (3 : k) * c ^ 2 = 0)
    (hinc : b * e + c * d = 0)
    (hrel : (4 : k) * b * c ^ 2 - (9 : k) * d * e = 0)
    (hrow1 :
      a * ((3 : k) * d ^ 2 - (2 : k) * b ^ 2 * c) *
          ((12 : k) * N - (3 : k) * G) +
        (6 : k) * ((4 : k) * N - G) * c ^ 3 -
        (18 : k) * ((6 : k) * N - H) * e ^ 2 = 0) :
    False := by
  have hsc := grokBalancedRowOneCubicInnerScalar68 N G H a b c d e hc hbal
    hdisc hinc hrel
  have h0 : (48 : k) * ((4 : k) * N - G) * c ^ 3 = 0 := by
    rw [← hsc, hrow1]
  have hne : (48 : k) * ((4 : k) * N - G) * c ^ 3 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hNG) (pow_ne_zero 3 hc)
  exact hne h0

/-- After the discriminant, the cubic-face core of row zero is
`(2N/3)*a*(4*b*c^2-9*d*e)`. -/
theorem grokBalancedRowZeroCubicInnerScalar68
    (N a b c d e : k)
    (hdisc : a * b ^ 2 + (3 : k) * c ^ 2 = 0) :
    (2 : k) * N * a *
        (-((1 / 9 : k) * a * b ^ 3) + b * c ^ 2 - (3 : k) * d * e) =
      ((2 : k) / 3) * N * a *
        ((4 : k) * b * c ^ 2 - (9 : k) * d * e) := by
  have hab : a * b ^ 2 = -(3 : k) * c ^ 2 := by linear_combination hdisc
  have hB3 : a * b ^ 3 = -(3 : k) * b * c ^ 2 := by
    calc
      a * b ^ 3 = (a * b ^ 2) * b := by ring
      _ = (-(3 : k) * c ^ 2) * b := by rw [hab]
      _ = -(3 : k) * b * c ^ 2 := by ring
  rw [hB3]
  ring

theorem grokBalancedRowZeroCubicScalar68
    (N a b c d e : k)
    (hdisc : a * b ^ 2 + (3 : k) * c ^ 2 = 0) :
    (4 / 27 : k) * ((2 : k) * N * a *
        (-((1 / 9 : k) * a * b ^ 3) + b * c ^ 2 - (3 : k) * d * e)) =
      (8 / 81 : k) * N * a *
        ((4 : k) * b * c ^ 2 - (9 : k) * d * e) := by
  rw [grokBalancedRowZeroCubicInnerScalar68 N a b c d e hdisc]
  ring

theorem grokBalancedRowZeroCubic_of_rowTwo68
    (N a b c d e : k)
    (hdisc : a * b ^ 2 + (3 : k) * c ^ 2 = 0)
    (hrel : (4 : k) * b * c ^ 2 - (9 : k) * d * e = 0) :
    (4 / 27 : k) * ((2 : k) * N * a *
        (-((1 / 9 : k) * a * b ^ 3) + b * c ^ 2 - (3 : k) * d * e)) = 0 := by
  rw [grokBalancedRowZeroCubicScalar68 N a b c d e hdisc, hrel, mul_zero]

/-! ## Polynomial identities -/

set_option maxHeartbeats 2000000 in
theorem grokBalanced_S_I3_identity68 (A B c d e : k[X]) :
    (3 : k) • d ^ 2 - (2 : k) • (B ^ 2 * c) =
      (2 : k) • grokBalancedCubicS68 A B c d e +
        (9 / 4 : k) •
          secondaryResidualInvariantThreePolynomial68 A B c d e := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [grokBalancedCubicS68, secondaryResidualInvariantThreePolynomial68,
    Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow, map_neg,
    RatFunc.algebraMap_C]
  simp only [map_div₀, map_ofNat, map_one]
  ring

set_option maxHeartbeats 8000000 in
theorem grokBalancedRowOne_eq_inner68 (A B c d e : k[X]) :
    secondaryResidualRowOnePolynomial68 A B c d e =
      (-4 / 27 : k) • grokBalancedRowOneInner68 A B c d e := by
  simp only [secondaryResidualRowOnePolynomial68, grokBalancedRowOneInner68,
    grokBalancedCubicS68, secondaryResidualInvariantThreePolynomial68,
    derivative_add, derivative_sub, derivative_mul, derivative_smul,
    derivative_pow, derivative_C, zero_mul, zero_add, smul_add, smul_sub,
    Polynomial.smul_eq_C_mul]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_zero,
    RatFunc.algebraMap_C, map_div₀, map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 8000000 in
theorem grokBalancedRowZero_eq_inner68 (A B c d e : k[X]) :
    secondaryResidualRowZeroPolynomial68 A B c d e =
      (4 / 27 : k) • grokBalancedRowZeroInner68 A B c d e := by
  simp only [secondaryResidualRowZeroPolynomial68, grokBalancedRowZeroInner68,
    grokBalancedIncidenceQ68, derivative_add, derivative_sub, derivative_mul,
    derivative_pow, derivative_C, zero_mul, zero_add, smul_add, smul_sub,
    Polynomial.smul_eq_C_mul]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_zero,
    RatFunc.algebraMap_C, map_div₀, map_ofNat, map_natCast, map_one]
  ring

/-! ## Degree lemmas -/

private theorem grokBalanced_natDegree_mul_derivative_lt68
    (p q : k[X]) (u v : ℕ)
    (hu : p.natDegree ≤ u) (hv : 1 < v) (hq : q.natDegree < v) :
    (p * derivative q).natDegree < u + v - 1 := by
  have hq' : q.natDegree ≤ v - 1 := Nat.le_sub_one_of_lt hq
  have hd : (derivative q).natDegree ≤ v - 2 := by
    have h := natDegree_derivative_le q
    omega
  have hmul := natDegree_mul_le_of_le hu hd
  omega

private theorem grokBalanced_natDegree_derivative_mul_lt68
    (p q : k[X]) (u v : ℕ)
    (hu0 : 0 < u) (hu : p.natDegree ≤ u) (hq : q.natDegree < v) :
    (derivative p * q).natDegree < u + v - 1 := by
  have hd : (derivative p).natDegree ≤ u - 1 :=
    (natDegree_derivative_le p).trans (by omega)
  have hq' : q.natDegree ≤ v - 1 := Nat.le_sub_one_of_lt hq
  have hmul := natDegree_mul_le_of_le hd hq'
  omega

set_option maxHeartbeats 2000000 in
theorem grokBalancedCubicS68_degree_le_old68
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hsmall : 3 * g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (grokBalancedCubicS68 A B c d e).natDegree ≤ 10 * n - g - h := by
  simp only [grokBalancedCubicS68]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
theorem grokBalancedCubicS68_degree_le_cubicFace68
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hsmall : 3 * g < n)
    (hbalanced : 2 * h = 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hI3 : (secondaryResidualInvariantThreePolynomial68 A B c d e).natDegree <
      10 * n - 3 * g) :
    (grokBalancedCubicS68 A B c d e).natDegree ≤ 10 * n - 3 * g := by
  have hid := grokBalanced_S_I3_identity68 A B c d e
  have hS :
      grokBalancedCubicS68 A B c d e =
        (1 / 2 : k) •
          ((3 : k) • d ^ 2 - (2 : k) • (B ^ 2 * c) -
            (9 / 4 : k) •
              secondaryResidualInvariantThreePolynomial68 A B c d e) := by
    apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
    simp only [hid.symm, Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
      map_pow, map_neg, RatFunc.algebraMap_C, map_div₀, map_ofNat, map_one]
    ring
  rw [hS]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
theorem grokBalancedCubicS68_coeff_cubicFace68
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hsmall : 3 * g < n)
    (hbalanced : 2 * h = 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hI3 : (secondaryResidualInvariantThreePolynomial68 A B c d e).natDegree <
      10 * n - 3 * g) :
    (grokBalancedCubicS68 A B c d e).coeff (10 * n - 3 * g) =
      (3 / 2 : k) * d.coeff (5 * n - h) ^ 2 -
        B.coeff (3 * n - g) ^ 2 * c.coeff (4 * n - g) := by
  have hSdeg := grokBalancedCubicS68_degree_le_cubicFace68 A B c d e n g h
    hg hgh hsmall hbalanced hA hB hc hd he hI3
  have hid := grokBalanced_S_I3_identity68 A B c d e
  have hform :
      (3 : k) • d ^ 2 - (2 : k) • (B ^ 2 * c) -
          (9 / 4 : k) •
            secondaryResidualInvariantThreePolynomial68 A B c d e =
        (2 : k) • grokBalancedCubicS68 A B c d e := by
    linear_combination hid
  have hd2deg : (d ^ 2).natDegree ≤ 2 * (5 * n - h) := by
    compute_degree
    omega
  have hd2 := coeff_pow_at_bound68 d (5 * n - h) 2 hd
  have hB2deg : (B ^ 2).natDegree ≤ 6 * n - 2 * g := by
    compute_degree
    omega
  have hB2 := coeff_pow_at_bound68 B (3 * n - g) 2 hB
  have hiB2 : 2 * (3 * n - g) = 6 * n - 2 * g := by omega
  rw [hiB2] at hB2
  have hB2c := coeff_mul_at_bounds68 (B ^ 2) c (6 * n - 2 * g) (4 * n - g)
    hB2deg hc
  have hiB2c : (6 * n - 2 * g) + (4 * n - g) = 10 * n - 3 * g := by omega
  rw [hiB2c, hB2] at hB2c
  have hid2 : 2 * (5 * n - h) = 10 * n - 3 * g := by omega
  rw [hid2] at hd2
  have hI30 :
      (secondaryResidualInvariantThreePolynomial68 A B c d e).coeff
        (10 * n - 3 * g) = 0 :=
    coeff_eq_zero_of_natDegree_lt hI3
  have hcoeff := congrArg (fun p : k[X] => p.coeff (10 * n - 3 * g)) hform
  simp only [coeff_add, coeff_sub, coeff_smul, hd2, hB2c, hI30, smul_eq_mul,
    mul_zero] at hcoeff
  have h2S : ((2 : k) • grokBalancedCubicS68 A B c d e).coeff
      (10 * n - 3 * g) =
      (2 : k) * (grokBalancedCubicS68 A B c d e).coeff (10 * n - 3 * g) := by
    simp [coeff_smul, smul_eq_mul]
  rw [h2S] at hcoeff
  have hstep :
      (3 : k) * d.coeff (5 * n - h) ^ 2 -
          (2 : k) * (B.coeff (3 * n - g) ^ 2 * c.coeff (4 * n - g)) =
        (2 : k) * (grokBalancedCubicS68 A B c d e).coeff (10 * n - 3 * g) :=
    hcoeff
  linear_combination (1 / 2 : k) * hstep

/-! ## High-face coefficients (before the `I3` drop) -/

set_option maxHeartbeats 4000000 in
theorem grokRowOne_coeff_oldTop68
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hsmall : 3 * g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (secondaryResidualRowOnePolynomial68 A B c d e).coeff
        (12 * n - g - h - 1) =
      (-8 / 27 : k) * A.coeff (2 * n) * ((10 * n - g - h : ℕ) : k) *
        (A.coeff (2 * n) * B.coeff (3 * n - g) * d.coeff (5 * n - h) -
          (3 : k) * c.coeff (4 * n - g) * e.coeff (6 * n - h)) := by
  set idx := 12 * n - g - h - 1
  have hA2deg : (A ^ 2).natDegree ≤ 4 * n := by
    compute_degree
    omega
  have hA2 : (A ^ 2).coeff (4 * n) = A.coeff (2 * n) ^ 2 := by
    have h := coeff_pow_at_bound68 A (2 * n) 2 hA
    have hi : 2 * (2 * n) = 4 * n := by omega
    simpa only [hi] using h
  have h1 := coeff_mul_mul_derivative_at_bounds68 (A ^ 2) B d
    (4 * n) (3 * n - g) (5 * n - h) (by omega) hA2deg hB hd
  have hi1 : 4 * n + (3 * n - g) + (5 * n - h) - 1 = idx := by
    dsimp [idx]; omega
  rw [hi1, hA2] at h1
  have h2 := coeff_mul_mul_derivative_at_bounds68 (A ^ 2) d B
    (4 * n) (5 * n - h) (3 * n - g) (by omega) hA2deg hd hB
  have hi2 : 4 * n + (5 * n - h) + (3 * n - g) - 1 = idx := by
    dsimp [idx]; omega
  rw [hi2, hA2] at h2
  have h2' : (A ^ 2 * derivative B * d).coeff idx =
      A.coeff (2 * n) ^ 2 * B.coeff (3 * n - g) *
        d.coeff (5 * n - h) * ((3 * n - g : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h2
  have h3 := coeff_mul_mul_mul_derivative_at_bounds68 A B d A
    (2 * n) (3 * n - g) (5 * n - h) (2 * n) (by omega) hA hB hd hA
  have hi3 : 2 * n + (3 * n - g) + (5 * n - h) + 2 * n - 1 = idx := by
    dsimp [idx]; omega
  rw [hi3] at h3
  have h3' : (A * derivative A * B * d).coeff idx =
      A.coeff (2 * n) * A.coeff (2 * n) * B.coeff (3 * n - g) *
        d.coeff (5 * n - h) * ((2 * n : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h3
  have h4 := coeff_mul_mul_derivative_at_bounds68 A c e
    (2 * n) (4 * n - g) (6 * n - h) (by omega) hA hc he
  have hi4 : 2 * n + (4 * n - g) + (6 * n - h) - 1 = idx := by
    dsimp [idx]; omega
  rw [hi4] at h4
  have h5 := coeff_mul_mul_derivative_at_bounds68 A e c
    (2 * n) (6 * n - h) (4 * n - g) (by omega) hA he hc
  have hi5 : 2 * n + (6 * n - h) + (4 * n - g) - 1 = idx := by
    dsimp [idx]; omega
  rw [hi5] at h5
  have h5' : (A * derivative c * e).coeff idx =
      A.coeff (2 * n) * c.coeff (4 * n - g) *
        e.coeff (6 * n - h) * ((4 * n - g : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h5
  have hlowA : (derivative A * B ^ 2 * c).natDegree < idx := by
    compute_degree; omega
  have hlowAd : (derivative A * d ^ 2).natDegree < idx := by
    compute_degree; omega
  have hlowB : (B ^ 2 * derivative e).natDegree < idx := by
    compute_degree; omega
  have hlowC : (B * c * derivative d).natDegree < idx := by
    compute_degree; omega
  have hlowD : (B * derivative c * d).natDegree < idx := by
    compute_degree; omega
  have hlowE : (derivative B * c * d).natDegree < idx := by
    compute_degree; omega
  have hlowF : (c ^ 2 * derivative c).natDegree < idx := by
    compute_degree; omega
  have hlowG : (e * derivative e).natDegree < idx := by
    compute_degree; omega
  have hcast5 : (((5 * n - h : ℕ) : k)) = (5 : k) * (n : k) - (h : k) := by
    rw [Nat.cast_sub (by omega : h ≤ 5 * n)]; push_cast; rfl
  have hcast3 : (((3 * n - g : ℕ) : k)) = (3 : k) * (n : k) - (g : k) := by
    rw [Nat.cast_sub (by omega : g ≤ 3 * n)]; push_cast; rfl
  have hcast2 : (((2 * n : ℕ) : k)) = (2 : k) * (n : k) := by push_cast; rfl
  have hcast4 : (((4 * n - g : ℕ) : k)) = (4 : k) * (n : k) - (g : k) := by
    rw [Nat.cast_sub (by omega : g ≤ 4 * n)]; push_cast; rfl
  have hcast6 : (((6 * n - h : ℕ) : k)) = (6 : k) * (n : k) - (h : k) := by
    rw [Nat.cast_sub (by omega : h ≤ 6 * n)]; push_cast; rfl
  have hcast10 : (((10 * n - g - h : ℕ) : k)) =
      (10 : k) * (n : k) - (g : k) - (h : k) := by
    have hsum : g + h ≤ 10 * n := by omega
    rw [show 10 * n - g - h = 10 * n - (g + h) by omega]
    rw [Nat.cast_sub hsum]
    push_cast
    rfl
  simp only [secondaryResidualRowOnePolynomial68, coeff_smul, coeff_add,
    coeff_sub, h1, h2', h3', h4, h5',
    coeff_eq_zero_of_natDegree_lt hlowA,
    coeff_eq_zero_of_natDegree_lt hlowAd,
    coeff_eq_zero_of_natDegree_lt hlowB,
    coeff_eq_zero_of_natDegree_lt hlowC,
    coeff_eq_zero_of_natDegree_lt hlowD,
    coeff_eq_zero_of_natDegree_lt hlowE,
    coeff_eq_zero_of_natDegree_lt hlowF,
    coeff_eq_zero_of_natDegree_lt hlowG, smul_eq_mul]
  rw [hcast5, hcast3, hcast2, hcast4, hcast6, hcast10]
  push_cast
  ring

/-- Middle-face cubic relation kills the old row-one top. -/
theorem grokRowOne_oldTop_eq_zero_of_middleThree68
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hsmall : 3 * g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hthree : -A.coeff (2 * n) * B.coeff (3 * n - g) * d.coeff (5 * n - h) +
      (3 : k) * c.coeff (4 * n - g) * e.coeff (6 * n - h) = 0) :
    (secondaryResidualRowOnePolynomial68 A B c d e).coeff
        (12 * n - g - h - 1) = 0 := by
  rw [grokRowOne_coeff_oldTop68 A B c d e n g h hg hgh hh hsmall hA hB hc hd he]
  have hS0 : A.coeff (2 * n) * B.coeff (3 * n - g) * d.coeff (5 * n - h) -
      (3 : k) * c.coeff (4 * n - g) * e.coeff (6 * n - h) = 0 := by
    linear_combination -hthree
  rw [hS0, mul_zero]

/-! ## Cubic-face coefficients after `I3` and `Q` drops -/

set_option maxHeartbeats 6000000 in
theorem grokRowOne_coeff_balancedCubicFace68
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hsmall : 3 * g < n) (hbalanced : 2 * h = 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hI3 : (secondaryResidualInvariantThreePolynomial68 A B c d e).natDegree <
      10 * n - 3 * g) :
    (secondaryResidualRowOnePolynomial68 A B c d e).coeff
        (12 * n - 3 * g - 1) =
      (-4 / 27 : k) *
        (A.coeff (2 * n) *
            ((3 : k) * d.coeff (5 * n - h) ^ 2 -
              (2 : k) * B.coeff (3 * n - g) ^ 2 * c.coeff (4 * n - g)) *
            ((12 * n - 3 * g : ℕ) : k) +
          (6 : k) * ((4 * n - g : ℕ) : k) * c.coeff (4 * n - g) ^ 3 -
          (18 : k) * ((6 * n - h : ℕ) : k) *
            e.coeff (6 * n - h) ^ 2) := by
  set idx := 12 * n - 3 * g - 1
  let S := grokBalancedCubicS68 A B c d e
  let I3 := secondaryResidualInvariantThreePolynomial68 A B c d e
  have hSdeg := grokBalancedCubicS68_degree_le_cubicFace68 A B c d e n g h
    hg hgh hsmall hbalanced hA hB hc hd he hI3
  have hStop := grokBalancedCubicS68_coeff_cubicFace68 A B c d e n g h
    hg hgh hsmall hbalanced hA hB hc hd he hI3
  have hASdeg : (A * S).natDegree ≤ 12 * n - 3 * g := by
    have h := natDegree_mul_le_of_le hA hSdeg
    have hi : 2 * n + (10 * n - 3 * g) = 12 * n - 3 * g := by omega
    rwa [hi] at h
  have hAScoeff := coeff_mul_at_bounds68 A S (2 * n) (10 * n - 3 * g) hA hSdeg
  have hiAS : 2 * n + (10 * n - 3 * g) = 12 * n - 3 * g := by omega
  rw [hiAS, hStop] at hAScoeff
  have hder0 : 0 < 12 * n - 3 * g := by omega
  have hASder := coeff_derivative_at_bound68 (A * S) (12 * n - 3 * g) hder0
  rw [hAScoeff] at hASder
  have h2AS : ((2 : k) • derivative (A * S)).coeff idx =
      (2 : k) *
        (((3 / 2 : k) * d.coeff (5 * n - h) ^ 2 -
            B.coeff (3 * n - g) ^ 2 * c.coeff (4 * n - g)) *
          A.coeff (2 * n) * ((12 * n - 3 * g : ℕ) : k)) := by
    dsimp [idx, S]
    rw [coeff_smul, smul_eq_mul, hASder]
    ring
  have h2ASsimp : ((2 : k) • derivative (A * S)).coeff idx =
      A.coeff (2 * n) *
        ((3 : k) * d.coeff (5 * n - h) ^ 2 -
          (2 : k) * B.coeff (3 * n - g) ^ 2 * c.coeff (4 * n - g)) *
        ((12 * n - 3 * g : ℕ) : k) := by
    rw [h2AS]
    ring
  have hI3low : (derivative A * I3).natDegree < idx := by
    have h := grokBalanced_natDegree_derivative_mul_lt68 A I3
      (2 * n) (10 * n - 3 * g) (by omega) hA hI3
    have hi : 2 * n + (10 * n - 3 * g) - 1 = idx := by
      dsimp [idx]; omega
    simpa only [hi] using h
  have hc2deg : (c ^ 2).natDegree ≤ 8 * n - 2 * g := by
    compute_degree
    omega
  have hc2 : (c ^ 2).coeff (8 * n - 2 * g) =
      c.coeff (4 * n - g) ^ 2 := by
    have h := coeff_pow_at_bound68 c (4 * n - g) 2 hc
    have hi : 2 * (4 * n - g) = 8 * n - 2 * g := by omega
    simpa only [hi] using h
  have hc3 := coeff_mul_derivative_at_bounds68 (c ^ 2) c
    (8 * n - 2 * g) (4 * n - g) (by omega) hc2deg hc
  have hic3 : (8 * n - 2 * g) + (4 * n - g) - 1 = idx := by
    dsimp [idx]; omega
  rw [hic3, hc2] at hc3
  have hee := coeff_mul_derivative_at_bounds68 e e
    (6 * n - h) (6 * n - h) (by omega) he he
  have hiee : (6 * n - h) + (6 * n - h) - 1 = 12 * n - 2 * h - 1 := by omega
  rw [hiee] at hee
  have hidx_ee : 12 * n - 2 * h - 1 = idx := by
    dsimp [idx]; omega
  have hlowBcd : (derivative (B * c * d)).natDegree < idx := by
    compute_degree
    omega
  have hlowBp : (derivative B * c * d).natDegree < idx := by
    compute_degree
    omega
  have hlowBe : (B ^ 2 * derivative e).natDegree < idx := by
    compute_degree
    omega
  have h0I3 : ((9 / 4 : k) • (derivative A * I3)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hI3low, mul_zero]
  have h0Bcd : ((3 : k) • derivative (B * c * d)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hlowBcd,
      mul_zero]
  have h0Bp : ((6 : k) • (derivative B * c * d)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hlowBp, mul_zero]
  have h0Be : ((-3 : k) • (B ^ 2 * derivative e)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hlowBe, mul_zero]
  have hc3sm : ((6 : k) • (c ^ 2 * derivative c)).coeff idx =
      (6 : k) * (c.coeff (4 * n - g) ^ 2 * c.coeff (4 * n - g) *
        ((4 * n - g : ℕ) : k)) := by
    rw [coeff_smul, smul_eq_mul, hc3]
  have heesm : ((-18 : k) • (e * derivative e)).coeff idx =
      (-18 : k) * (e.coeff (6 * n - h) ^ 2 * ((6 * n - h : ℕ) : k)) := by
    rw [coeff_smul, smul_eq_mul, ← hidx_ee, hee]
    ring
  have hinner : (grokBalancedRowOneInner68 A B c d e).coeff idx =
      A.coeff (2 * n) *
          ((3 : k) * d.coeff (5 * n - h) ^ 2 -
            (2 : k) * B.coeff (3 * n - g) ^ 2 * c.coeff (4 * n - g)) *
          ((12 * n - 3 * g : ℕ) : k) +
        (6 : k) * ((4 * n - g : ℕ) : k) * c.coeff (4 * n - g) ^ 3 -
        (18 : k) * ((6 * n - h : ℕ) : k) * e.coeff (6 * n - h) ^ 2 := by
    dsimp [grokBalancedRowOneInner68]
    simp only [coeff_add, coeff_sub]
    rw [h2ASsimp, h0I3, h0Bcd, h0Bp, h0Be, hc3sm, heesm]
    ring
  rw [grokBalancedRowOne_eq_inner68, coeff_smul, smul_eq_mul, hinner]
  ring_nf
  simp [pow_three, pow_two]

set_option maxHeartbeats 2000000 in
theorem grokRowOne_coeff_balancedCubicFace_simplified68
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hsmall : 3 * g < n) (hbalanced : 2 * h = 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hcdeg : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hI3 : (secondaryResidualInvariantThreePolynomial68 A B c d e).natDegree <
      10 * n - 3 * g)
    (hc0 : c.coeff (4 * n - g) ≠ 0)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0)
    (hinc : B.coeff (3 * n - g) * e.coeff (6 * n - h) +
      c.coeff (4 * n - g) * d.coeff (5 * n - h) = 0)
    (hrel : (4 : k) * B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 -
      (9 : k) * d.coeff (5 * n - h) * e.coeff (6 * n - h) = 0) :
    (secondaryResidualRowOnePolynomial68 A B c d e).coeff
        (12 * n - 3 * g - 1) =
      (-64 / 9 : k) * ((4 * n - g : ℕ) : k) * c.coeff (4 * n - g) ^ 3 := by
  rw [grokRowOne_coeff_balancedCubicFace68 A B c d e n g h hg hgh hh hsmall
    hbalanced hA hB hcdeg hd he hI3]
  have hcast12 : (((12 * n - 3 * g : ℕ) : k)) =
      (12 : k) * (n : k) - (3 : k) * (g : k) := by
    rw [Nat.cast_sub (by omega : 3 * g ≤ 12 * n)]
    push_cast
    rfl
  have hcast4 : (((4 * n - g : ℕ) : k)) =
      (4 : k) * (n : k) - (g : k) := by
    rw [Nat.cast_sub (by omega : g ≤ 4 * n)]
    push_cast
    rfl
  have hcast6 : (((6 * n - h : ℕ) : k)) =
      (6 : k) * (n : k) - (h : k) := by
    rw [Nat.cast_sub (by omega : h ≤ 6 * n)]
    push_cast
    rfl
  have hbal : (2 : k) * (h : k) = (3 : k) * (g : k) := by
    have := congrArg (fun m : ℕ => (m : k)) hbalanced
    push_cast at this
    exact this
  rw [hcast12, hcast4, hcast6]
  exact grokBalancedRowOneCubicScalar68 (n : k) (g : k) (h : k)
    (A.coeff (2 * n)) (B.coeff (3 * n - g)) (c.coeff (4 * n - g))
    (d.coeff (5 * n - h)) (e.coeff (6 * n - h)) hc0 hbal hdisc hinc hrel

/-- Residual row one cannot vanish at the balanced cubic face. -/
theorem grokRowOne_balancedCubicFace_ne_zero68
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hsmall : 3 * g < n) (hbalanced : 2 * h = 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hcdeg : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hI3 : (secondaryResidualInvariantThreePolynomial68 A B c d e).natDegree <
      10 * n - 3 * g)
    (hc0 : c.coeff (4 * n - g) ≠ 0)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0)
    (hinc : B.coeff (3 * n - g) * e.coeff (6 * n - h) +
      c.coeff (4 * n - g) * d.coeff (5 * n - h) = 0)
    (hrel : (4 : k) * B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 -
      (9 : k) * d.coeff (5 * n - h) * e.coeff (6 * n - h) = 0) :
    (secondaryResidualRowOnePolynomial68 A B c d e).coeff
        (12 * n - 3 * g - 1) ≠ 0 := by
  rw [grokRowOne_coeff_balancedCubicFace_simplified68 A B c d e n g h hg hgh hh
    hsmall hbalanced hA hB hcdeg hd he hI3 hc0 hdisc hinc hrel]
  have hNG : ((4 * n - g : ℕ) : k) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by omega)
  exact grokBalancedRowOneCubic_ne_zero68 (n : k) (g : k) (h : k)
    (A.coeff (2 * n)) (B.coeff (3 * n - g)) (c.coeff (4 * n - g))
    (d.coeff (5 * n - h)) (e.coeff (6 * n - h)) hc0 (by
      rw [Nat.cast_sub (by omega : g ≤ 4 * n)]
      push_cast
      exact hNG)
    (by
      have := congrArg (fun m : ℕ => (m : k)) hbalanced
      push_cast at this
      exact this)
    hdisc hinc hrel

theorem grokRowOne_eq_zero_imp_false_balancedCubic68
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hsmall : 3 * g < n) (hbalanced : 2 * h = 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hcdeg : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hI3 : (secondaryResidualInvariantThreePolynomial68 A B c d e).natDegree <
      10 * n - 3 * g)
    (hc0 : c.coeff (4 * n - g) ≠ 0)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0)
    (hinc : B.coeff (3 * n - g) * e.coeff (6 * n - h) +
      c.coeff (4 * n - g) * d.coeff (5 * n - h) = 0)
    (hrel : (4 : k) * B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 -
      (9 : k) * d.coeff (5 * n - h) * e.coeff (6 * n - h) = 0)
    (hrow : secondaryResidualRowOnePolynomial68 A B c d e = 0) :
    False := by
  have hcoeff :
      (secondaryResidualRowOnePolynomial68 A B c d e).coeff
        (12 * n - 3 * g - 1) = 0 := by
    simp [hrow]
  exact grokRowOne_balancedCubicFace_ne_zero68 A B c d e n g h hg hgh hh
    hsmall hbalanced hA hB hcdeg hd he hI3 hc0 hdisc hinc hrel hcoeff

theorem grokRowOne_add_load_eq_zero_imp_false_balancedCubic68
    (A B c d e load : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hsmall : 3 * g < n) (hbalanced : 2 * h = 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hcdeg : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hI3 : (secondaryResidualInvariantThreePolynomial68 A B c d e).natDegree <
      10 * n - 3 * g)
    (hc0 : c.coeff (4 * n - g) ≠ 0)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0)
    (hinc : B.coeff (3 * n - g) * e.coeff (6 * n - h) +
      c.coeff (4 * n - g) * d.coeff (5 * n - h) = 0)
    (hrel : (4 : k) * B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 -
      (9 : k) * d.coeff (5 * n - h) * e.coeff (6 * n - h) = 0)
    (hload : load.natDegree < 12 * n - 3 * g - 1)
    (hsum : secondaryResidualRowOnePolynomial68 A B c d e + load = 0) :
    False := by
  have hcoeff :
      (secondaryResidualRowOnePolynomial68 A B c d e).coeff
        (12 * n - 3 * g - 1) = 0 := by
    have h := congrArg (fun p : k[X] => p.coeff (12 * n - 3 * g - 1)) hsum
    rw [coeff_add, coeff_zero, coeff_eq_zero_of_natDegree_lt hload,
      add_zero] at h
    exact h
  exact grokRowOne_balancedCubicFace_ne_zero68 A B c d e n g h hg hgh hh
    hsmall hbalanced hA hB hcdeg hd he hI3 hc0 hdisc hinc hrel hcoeff

set_option maxHeartbeats 6000000 in
theorem grokRowZero_coeff_balancedCubicFace68
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hsmall : 3 * g < n) (hbalanced : 2 * h = 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (grokBalancedIncidenceQ68 B c d e).natDegree < 9 * n - 3 * g) :
    (secondaryResidualRowZeroPolynomial68 A B c d e).coeff
        (13 * n - 3 * g - 1) =
      (4 / 27 : k) * ((2 * n : ℕ) : k) * A.coeff (2 * n) *
        (-((1 / 9 : k) * A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3) +
          B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 -
          (3 : k) * d.coeff (5 * n - h) * e.coeff (6 * n - h)) := by
  set idx := 13 * n - 3 * g - 1
  let Q := grokBalancedIncidenceQ68 B c d e
  have hQlow : (A * derivative A * Q).natDegree < idx := by
    have hdA : (derivative A).natDegree ≤ 2 * n - 1 :=
      (natDegree_derivative_le A).trans (by omega)
    have hAQ : (A * derivative A).natDegree ≤ 4 * n - 1 := by
      have h := natDegree_mul_le_of_le hA hdA
      have hi : 2 * n + (2 * n - 1) = 4 * n - 1 := by omega
      rwa [hi] at h
    have hq' : Q.natDegree ≤ 9 * n - 3 * g - 1 := Nat.le_sub_one_of_lt hQ
    have hmul := natDegree_mul_le_of_le hAQ hq'
    have hi : (4 * n - 1) + (9 * n - 3 * g - 1) < idx := by
      dsimp [idx]
      omega
    exact hmul.trans_lt hi
  have hB3deg : (B ^ 3).natDegree ≤ 9 * n - 3 * g := by
    compute_degree
    omega
  have hB3 : (B ^ 3).coeff (9 * n - 3 * g) =
      B.coeff (3 * n - g) ^ 3 := by
    have h := coeff_pow_at_bound68 B (3 * n - g) 3 hB
    have hi : 3 * (3 * n - g) = 9 * n - 3 * g := by omega
    simpa only [hi] using h
  have hAB3 := coeff_mul_mul_derivative_at_bounds68 A (B ^ 3) A
    (2 * n) (9 * n - 3 * g) (2 * n) (by omega) hA hB3deg hA
  have hiAB3 : 2 * n + (9 * n - 3 * g) + 2 * n - 1 = idx := by
    dsimp [idx]; omega
  rw [hiAB3, hB3] at hAB3
  have hAB3' : (A * derivative A * B ^ 3).coeff idx =
      A.coeff (2 * n) * A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 *
        ((2 * n : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hAB3
  have hBc2 := coeff_mul_mul_mul_derivative_at_bounds68 B c c A
    (3 * n - g) (4 * n - g) (4 * n - g) (2 * n) (by omega) hB hc hc hA
  have hiBc2 : (3 * n - g) + (4 * n - g) + (4 * n - g) + 2 * n - 1 =
      idx := by
    dsimp [idx]; omega
  rw [hiBc2] at hBc2
  have hBc2' : (derivative A * B * c ^ 2).coeff idx =
      A.coeff (2 * n) * B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 *
        ((2 * n : ℕ) : k) := by
    simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using hBc2
  have hAde := coeff_mul_mul_mul_derivative_at_bounds68 A d e A
    (2 * n) (5 * n - h) (6 * n - h) (2 * n) (by omega) hA hd he hA
  have hiAde : 2 * n + (5 * n - h) + (6 * n - h) + 2 * n - 1 =
      13 * n - 2 * h - 1 := by omega
  rw [hiAde] at hAde
  have hidx_de : 13 * n - 2 * h - 1 = idx := by
    dsimp [idx]; omega
  have hAde' : (derivative A * d * e).coeff idx =
      A.coeff (2 * n) * d.coeff (5 * n - h) * e.coeff (6 * n - h) *
        ((2 * n : ℕ) : k) := by
    have h := hAde
    rw [hidx_de] at h
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h
  have hlow1 : (A * B ^ 2 * derivative d).natDegree < idx := by
    compute_degree; omega
  have hlow2 : (A * B * derivative B * d).natDegree < idx := by
    compute_degree; omega
  have hlow3 : (B * c * derivative e).natDegree < idx := by
    compute_degree; omega
  have hlow4 : (B * d * derivative d).natDegree < idx := by
    compute_degree; omega
  have hlow5 : (derivative B * d ^ 2).natDegree < idx := by
    compute_degree; omega
  have hlow6 : (c * derivative c * d).natDegree < idx := by
    compute_degree; omega
  have hinner : (grokBalancedRowZeroInner68 A B c d e).coeff idx =
      ((2 * n : ℕ) : k) * A.coeff (2 * n) *
        (-((1 / 9 : k) * A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3) +
          B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 -
          (3 : k) * d.coeff (5 * n - h) * e.coeff (6 * n - h)) := by
    dsimp [grokBalancedRowZeroInner68]
    simp only [coeff_add, coeff_sub, coeff_neg, coeff_smul, smul_eq_mul]
    rw [coeff_eq_zero_of_natDegree_lt hQlow,
      coeff_eq_zero_of_natDegree_lt hlow1,
      coeff_eq_zero_of_natDegree_lt hlow2,
      coeff_eq_zero_of_natDegree_lt hlow3,
      coeff_eq_zero_of_natDegree_lt hlow4,
      coeff_eq_zero_of_natDegree_lt hlow5,
      coeff_eq_zero_of_natDegree_lt hlow6, hAB3', hBc2', hAde']
    ring
  rw [grokBalancedRowZero_eq_inner68, coeff_smul, smul_eq_mul, hinner]

/-- After the discriminant, row zero at the cubic face is proportional to
the row-two relation `4*b*c^2-9*d*e`. -/
theorem grokRowZero_coeff_balancedCubicFace_eq68
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hsmall : 3 * g < n) (hbalanced : 2 * h = 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (grokBalancedIncidenceQ68 B c d e).natDegree < 9 * n - 3 * g)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0) :
    (secondaryResidualRowZeroPolynomial68 A B c d e).coeff
        (13 * n - 3 * g - 1) =
      (8 / 81 : k) * (n : k) * A.coeff (2 * n) *
        ((4 : k) * B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 -
          (9 : k) * d.coeff (5 * n - h) * e.coeff (6 * n - h)) := by
  rw [grokRowZero_coeff_balancedCubicFace68 A B c d e n g h hg hgh hh hsmall
    hbalanced hA hB hc hd he hQ]
  have hcast2 : (((2 * n : ℕ) : k)) = (2 : k) * (n : k) := by
    push_cast
    rfl
  rw [hcast2]
  have hsc := grokBalancedRowZeroCubicScalar68 (n : k) (A.coeff (2 * n))
    (B.coeff (3 * n - g)) (c.coeff (4 * n - g)) (d.coeff (5 * n - h))
    (e.coeff (6 * n - h)) hdisc
  convert hsc using 1
  ring

theorem grokRowZero_balancedCubicFace_eq_zero_of_rowTwo68
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hsmall : 3 * g < n) (hbalanced : 2 * h = 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (grokBalancedIncidenceQ68 B c d e).natDegree < 9 * n - 3 * g)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0)
    (hrel : (4 : k) * B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 -
      (9 : k) * d.coeff (5 * n - h) * e.coeff (6 * n - h) = 0) :
    (secondaryResidualRowZeroPolynomial68 A B c d e).coeff
        (13 * n - 3 * g - 1) = 0 := by
  rw [grokRowZero_coeff_balancedCubicFace_eq68 A B c d e n g h hg hgh hh
    hsmall hbalanced hA hB hc hd he hQ hdisc, hrel, mul_zero]

end GrokBalancedLowerRows68

#print axioms grokBalancedRowOneCubicInnerScalar68
#print axioms grokBalancedRowOneCubicScalar68
#print axioms grokBalancedRowOneCubic_scalarContradiction68
#print axioms grokBalancedRowZeroCubic_of_rowTwo68
#print axioms grokBalanced_S_I3_identity68
#print axioms grokBalancedRowOne_eq_inner68
#print axioms grokBalancedRowZero_eq_inner68
#print axioms grokRowOne_coeff_oldTop68
#print axioms grokRowOne_oldTop_eq_zero_of_middleThree68
#print axioms grokRowOne_coeff_balancedCubicFace68
#print axioms grokRowOne_coeff_balancedCubicFace_simplified68
#print axioms grokRowOne_balancedCubicFace_ne_zero68
#print axioms grokRowOne_eq_zero_imp_false_balancedCubic68
#print axioms grokRowOne_add_load_eq_zero_imp_false_balancedCubic68
#print axioms grokRowZero_coeff_balancedCubicFace68
#print axioms grokRowZero_coeff_balancedCubicFace_eq68
#print axioms grokRowZero_balancedCubicFace_eq_zero_of_rowTwo68

end Max11DegreeRoutes
