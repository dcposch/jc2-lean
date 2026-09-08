import LowScale68SecondaryResidualExtraction

/-! # Balanced residual row-one cubic face after `2h = 3g`

On the selected residual middle face the leading scalars satisfy
`b*e + c*d = 0` and `a*b^2 + 3*c^2 = 0`.  Residual row two on the
balanced wall `2*h = 3*g` then forces `4*b*c^2 - 9*d*e = 0`.

Row one rewrites through the cubic combination `S = A*B*d - 3*c*e`
and the residual cubic invariant `I3`.  After `I3.natDegree < 10*n-3*g`,
`S` drops to the cubic face `10*n-3*g`, and `2*(A*S)'` meets
`6*(c^2*c')` and `-18*(e*e')` at `12*n-3*g-1`.  The inner coefficient
collapses to `48*(4*n-g)*c_top^3`, so residual row one has coefficient
`(-64/9)*(4*n-g)*c_top^3`.  In characteristic zero this is nonzero
whenever `c_top ≠ 0`.

This file does not identify `I3` with a first integral, does not treat
constant-Jacobian loads, and does not treat residual row zero.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section GrokRowOneEndgameAlt68

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- Cubic combination whose old top is the middle-face relation
`a*b*d - 3*c*e = 0`. -/
def grokRowOneEndgameS68 (A B c d e : k[X]) : k[X] :=
  A * B * d - (3 : k) • (c * e)

/-- Inner expression of residual row one after the `S`/`I3` rewrite,
before the overall factor `-4/27`. -/
def grokRowOneEndgameInner68 (A B c d e : k[X]) : k[X] :=
  (2 : k) • derivative (A * grokRowOneEndgameS68 A B c d e) +
    (9 / 4 : k) •
      (derivative A * secondaryResidualInvariantThreePolynomial68 A B c d e) +
    (6 : k) • (c ^ 2 * derivative c) +
    (3 : k) • derivative (B * c * d) +
    (6 : k) • (derivative B * c * d) -
    (3 : k) • (B ^ 2 * derivative e) -
    (18 : k) • (e * derivative e)

/-! ## Field algebra on the middle face plus `4*b*c^2-9*d*e=0` -/

theorem grokRowOneEndgame_disc_imp_b_ne_zero68
    (a b c : k) (hc : c ≠ 0)
    (hdisc : a * b ^ 2 + (3 : k) * c ^ 2 = 0) : b ≠ 0 := by
  intro hb
  have h3 : (3 : k) * c ^ 2 = 0 := by simpa [hb] using hdisc
  have hc2 : c ^ 2 = 0 := (mul_eq_zero.mp h3).resolve_left (by norm_num)
  exact hc (pow_eq_zero hc2)

theorem grokRowOneEndgame_nine_d_sq68
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

theorem grokRowOneEndgame_nine_e_sq68
    (a b c d e : k) (hc : c ≠ 0)
    (hdisc : a * b ^ 2 + (3 : k) * c ^ 2 = 0)
    (hinc : b * e + c * d = 0)
    (hrel : (4 : k) * b * c ^ 2 - (9 : k) * d * e = 0) :
    (9 : k) * e ^ 2 + (4 : k) * c ^ 3 = 0 := by
  have hb := grokRowOneEndgame_disc_imp_b_ne_zero68 a b c hc hdisc
  have hd := grokRowOneEndgame_nine_d_sq68 a b c d e hc hdisc hinc hrel
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
theorem grokRowOneEndgame_innerScalar68
    (N G H a b c d e : k) (hc : c ≠ 0)
    (hbal : (2 : k) * H = (3 : k) * G)
    (hdisc : a * b ^ 2 + (3 : k) * c ^ 2 = 0)
    (hinc : b * e + c * d = 0)
    (hrel : (4 : k) * b * c ^ 2 - (9 : k) * d * e = 0) :
    a * ((3 : k) * d ^ 2 - (2 : k) * b ^ 2 * c) * ((12 : k) * N - (3 : k) * G) +
        (6 : k) * ((4 : k) * N - G) * c ^ 3 -
        (18 : k) * ((6 : k) * N - H) * e ^ 2 =
      (48 : k) * ((4 : k) * N - G) * c ^ 3 := by
  have hd := grokRowOneEndgame_nine_d_sq68 a b c d e hc hdisc hinc hrel
  have he := grokRowOneEndgame_nine_e_sq68 a b c d e hc hdisc hinc hrel
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
  have hH : H = (3 / 2 : k) * G := by
    linear_combination (1 / 2 : k) * hbal
  rw [hAterm, he2, hH]
  ring

/-- Scaling the inner cubic identity by `-4/27` produces the residual
row-one prefactor `-64/9`. -/
theorem grokRowOneEndgame_scalar68
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
  rw [grokRowOneEndgame_innerScalar68 N G H a b c d e hc hbal
    hdisc hinc hrel]
  ring

theorem grokRowOneEndgame_scalar_ne_zero68
    (N G H a b c d e : k) (hc : c ≠ 0)
    (hNG : (4 : k) * N - G ≠ 0)
    (hbal : (2 : k) * H = (3 : k) * G)
    (hdisc : a * b ^ 2 + (3 : k) * c ^ 2 = 0)
    (hinc : b * e + c * d = 0)
    (hrel : (4 : k) * b * c ^ 2 - (9 : k) * d * e = 0) :
    (-64 / 9 : k) * ((4 : k) * N - G) * c ^ 3 ≠ 0 :=
  mul_ne_zero (mul_ne_zero (by norm_num) hNG) (pow_ne_zero 3 hc)

/-! ## Short `S`/`I3` rewrite and row-one inner form -/

set_option maxHeartbeats 2000000 in
theorem grokRowOneEndgame_S_I3_identity68 (A B c d e : k[X]) :
    (2 : k) • grokRowOneEndgameS68 A B c d e +
      (9 / 4 : k) • secondaryResidualInvariantThreePolynomial68 A B c d e =
      (3 : k) • d ^ 2 - (2 : k) • (B ^ 2 * c) := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [grokRowOneEndgameS68, secondaryResidualInvariantThreePolynomial68,
    Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow, map_neg,
    RatFunc.algebraMap_C]
  simp only [map_div₀, map_ofNat, map_one]
  have hneg8 : RatFunc.C (-8 : k) = (-8 : RatFunc k) := by
    rw [show (-8 : k) = -(8 : k) by norm_num, map_neg, map_ofNat]
  rw [hneg8]
  ring

set_option maxHeartbeats 8000000 in
theorem grokRowOneEndgame_eq_inner68 (A B c d e : k[X]) :
    secondaryResidualRowOnePolynomial68 A B c d e =
      (-4 / 27 : k) • grokRowOneEndgameInner68 A B c d e := by
  simp only [secondaryResidualRowOnePolynomial68, grokRowOneEndgameInner68,
    grokRowOneEndgameS68, secondaryResidualInvariantThreePolynomial68,
    derivative_add, derivative_sub, derivative_mul, derivative_smul,
    derivative_pow, derivative_C, zero_mul, zero_add, smul_add, smul_sub,
    Polynomial.smul_eq_C_mul]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_zero,
    RatFunc.algebraMap_C, map_div₀, map_ofNat, map_natCast, map_one]
  ring

/-! ## Degree and coefficient of `S` on the cubic face -/

private theorem grokRowOneEndgame_d_sq_degree_le68
    (d : k[X]) (n g h : ℕ)
    (hsmall : 3 * g < n) (hbalanced : 2 * h = 3 * g)
    (hd : d.natDegree ≤ 5 * n - h) :
    (d ^ 2).natDegree ≤ 10 * n - 3 * g := by
  have h1 : (d ^ 2).natDegree ≤ 2 * (5 * n - h) :=
    (natDegree_pow_le d 2).trans (Nat.mul_le_mul_left 2 hd)
  have hi : 2 * (5 * n - h) = 10 * n - 3 * g := by omega
  rwa [hi] at h1

private theorem grokRowOneEndgame_B2c_degree_le68
    (B c : k[X]) (n g : ℕ)
    (hsmall : 3 * g < n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g) :
    (B ^ 2 * c).natDegree ≤ 10 * n - 3 * g := by
  have hB2 : (B ^ 2).natDegree ≤ 6 * n - 2 * g := by
    have h1 := (natDegree_pow_le B 2).trans (Nat.mul_le_mul_left 2 hB)
    have hi : 2 * (3 * n - g) = 6 * n - 2 * g := by omega
    rwa [hi] at h1
  have h := natDegree_mul_le_of_le hB2 hc
  have hi : (6 * n - 2 * g) + (4 * n - g) = 10 * n - 3 * g := by omega
  rwa [hi] at h

theorem grokRowOneEndgame_S_degree_le_cubicFace68
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
    (grokRowOneEndgameS68 A B c d e).natDegree ≤ 10 * n - 3 * g := by
  have hform :
      (2 : k) • grokRowOneEndgameS68 A B c d e =
        (3 : k) • d ^ 2 - (2 : k) • (B ^ 2 * c) -
          (9 / 4 : k) •
            secondaryResidualInvariantThreePolynomial68 A B c d e :=
    eq_sub_of_add_eq (grokRowOneEndgame_S_I3_identity68 A B c d e)
  have h2S :
      ((2 : k) • grokRowOneEndgameS68 A B c d e).natDegree ≤
        10 * n - 3 * g := by
    rw [hform]
    have hd2 : ((3 : k) • d ^ 2).natDegree ≤ 10 * n - 3 * g :=
      (natDegree_smul_le (3 : k) (d ^ 2)).trans
        (grokRowOneEndgame_d_sq_degree_le68 d n g h hsmall hbalanced hd)
    have hB2c : ((2 : k) • (B ^ 2 * c)).natDegree ≤ 10 * n - 3 * g :=
      (natDegree_smul_le (2 : k) (B ^ 2 * c)).trans
        (grokRowOneEndgame_B2c_degree_le68 B c n g hsmall hB hc)
    have hI3sm :
        ((9 / 4 : k) •
            secondaryResidualInvariantThreePolynomial68 A B c d e).natDegree <
          10 * n - 3 * g :=
      Nat.lt_of_le_of_lt (natDegree_smul_le (9 / 4 : k) _) hI3
    have hcore :
        ((3 : k) • d ^ 2 - (2 : k) • (B ^ 2 * c)).natDegree ≤
          10 * n - 3 * g :=
      (natDegree_sub_le _ _).trans (max_le hd2 hB2c)
    exact (natDegree_sub_le _ _).trans (max_le hcore (Nat.le_of_lt hI3sm))
  have hne : (2 : k) ≠ 0 := by norm_num
  have hC :
      (2 : k) • grokRowOneEndgameS68 A B c d e =
        C (2 : k) * grokRowOneEndgameS68 A B c d e :=
    Polynomial.smul_eq_C_mul _ _
  rwa [hC, natDegree_C_mul hne] at h2S

theorem grokRowOneEndgame_S_coeff_cubicFace68
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
    (grokRowOneEndgameS68 A B c d e).coeff (10 * n - 3 * g) =
      (3 / 2 : k) * d.coeff (5 * n - h) ^ 2 -
        B.coeff (3 * n - g) ^ 2 * c.coeff (4 * n - g) := by
  have hform :
      (2 : k) • grokRowOneEndgameS68 A B c d e =
        (3 : k) • d ^ 2 - (2 : k) • (B ^ 2 * c) -
          (9 / 4 : k) •
            secondaryResidualInvariantThreePolynomial68 A B c d e :=
    eq_sub_of_add_eq (grokRowOneEndgame_S_I3_identity68 A B c d e)
  have hd2deg := grokRowOneEndgame_d_sq_degree_le68 d n g h hsmall hbalanced hd
  have hd2 := coeff_pow_at_bound68 d (5 * n - h) 2 hd
  have hid2 : 2 * (5 * n - h) = 10 * n - 3 * g := by omega
  rw [hid2] at hd2
  have hB2deg : (B ^ 2).natDegree ≤ 6 * n - 2 * g := by
    have h1 := (natDegree_pow_le B 2).trans (Nat.mul_le_mul_left 2 hB)
    have hi : 2 * (3 * n - g) = 6 * n - 2 * g := by omega
    rwa [hi] at h1
  have hB2 := coeff_pow_at_bound68 B (3 * n - g) 2 hB
  have hiB2 : 2 * (3 * n - g) = 6 * n - 2 * g := by omega
  rw [hiB2] at hB2
  have hB2c := coeff_mul_at_bounds68 (B ^ 2) c (6 * n - 2 * g) (4 * n - g)
    hB2deg hc
  have hiB2c : (6 * n - 2 * g) + (4 * n - g) = 10 * n - 3 * g := by omega
  rw [hiB2c, hB2] at hB2c
  have hI30 :
      (secondaryResidualInvariantThreePolynomial68 A B c d e).coeff
        (10 * n - 3 * g) = 0 :=
    coeff_eq_zero_of_natDegree_lt hI3
  have hcoeff :=
    congrArg (fun p : k[X] => p.coeff (10 * n - 3 * g)) hform
  simp only [coeff_add, coeff_sub, coeff_smul, hd2, hB2c, hI30, smul_eq_mul,
    mul_zero] at hcoeff
  linear_combination (1 / 2 : k) * hcoeff

/-! ## Strictly lower faces on `g < h` -/

private theorem grokRowOneEndgame_natDegree_derivative_mul_lt68
    (p q : k[X]) (u v : ℕ)
    (hu0 : 0 < u) (hu : p.natDegree ≤ u) (hq : q.natDegree < v) :
    (derivative p * q).natDegree < u + v - 1 := by
  have hd : (derivative p).natDegree ≤ u - 1 :=
    (natDegree_derivative_le p).trans (by omega)
  have hq' : q.natDegree ≤ v - 1 := Nat.le_sub_one_of_lt hq
  have hmul := natDegree_mul_le_of_le hd hq'
  omega

private theorem grokRowOneEndgame_Bcd_degree_lt68
    (B c d : k[X]) (n g h : ℕ)
    (hgh : g < h) (hsmall : 3 * g < n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h) :
    (B * c * d).natDegree ≤ 12 * n - 2 * g - h := by
  have hBc : (B * c).natDegree ≤ (3 * n - g) + (4 * n - g) :=
    natDegree_mul_le.trans (Nat.add_le_add hB hc)
  have h := natDegree_mul_le.trans (Nat.add_le_add hBc hd)
  have hi : (3 * n - g) + (4 * n - g) + (5 * n - h) = 12 * n - 2 * g - h := by
    omega
  rwa [hi] at h

private theorem grokRowOneEndgame_Bcd_der_degree_lt68
    (B c d : k[X]) (n g h : ℕ)
    (hgh : g < h) (hsmall : 3 * g < n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h) :
    (derivative (B * c * d)).natDegree < 12 * n - 3 * g - 1 := by
  have hprod := grokRowOneEndgame_Bcd_degree_lt68 B c d n g h hgh hsmall hB hc hd
  have hder :=
    (natDegree_derivative_le (B * c * d)).trans (Nat.sub_le_sub_right hprod 1)
  have hlt : 12 * n - 2 * g - h - 1 < 12 * n - 3 * g - 1 := by omega
  exact hder.trans_lt hlt

private theorem grokRowOneEndgame_Bp_cd_degree_lt68
    (B c d : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hsmall : 3 * g < n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h) :
    (derivative B * c * d).natDegree < 12 * n - 3 * g - 1 := by
  have hdB : (derivative B).natDegree ≤ 3 * n - g - 1 :=
    (natDegree_derivative_le B).trans (Nat.sub_le_sub_right hB 1)
  have hBc : (derivative B * c).natDegree ≤ (3 * n - g - 1) + (4 * n - g) :=
    natDegree_mul_le.trans (Nat.add_le_add hdB hc)
  have h := natDegree_mul_le.trans (Nat.add_le_add hBc hd)
  have hi : (3 * n - g - 1) + (4 * n - g) + (5 * n - h) =
      12 * n - 2 * g - h - 1 := by omega
  have hlt : 12 * n - 2 * g - h - 1 < 12 * n - 3 * g - 1 := by omega
  exact (by rwa [hi] at h).trans_lt hlt

private theorem grokRowOneEndgame_B2e_der_degree_lt68
    (B e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hsmall : 3 * g < n)
    (hB : B.natDegree ≤ 3 * n - g)
    (he : e.natDegree ≤ 6 * n - h) :
    (B ^ 2 * derivative e).natDegree < 12 * n - 3 * g - 1 := by
  have hB2 : (B ^ 2).natDegree ≤ 6 * n - 2 * g := by
    have h1 := (natDegree_pow_le B 2).trans (Nat.mul_le_mul_left 2 hB)
    have hi : 2 * (3 * n - g) = 6 * n - 2 * g := by omega
    rwa [hi] at h1
  have hde : (derivative e).natDegree ≤ 6 * n - h - 1 :=
    (natDegree_derivative_le e).trans (Nat.sub_le_sub_right he 1)
  have h := natDegree_mul_le_of_le hB2 hde
  have hi : (6 * n - 2 * g) + (6 * n - h - 1) = 12 * n - 2 * g - h - 1 := by
    omega
  have hlt : 12 * n - 2 * g - h - 1 < 12 * n - 3 * g - 1 := by omega
  exact (by rwa [hi] at h).trans_lt hlt

/-! ## Cubic-face coefficient -/

set_option maxHeartbeats 6000000 in
theorem grokRowOneEndgame_coeff_inner68
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
  set S := grokRowOneEndgameS68 A B c d e
  set I3 := secondaryResidualInvariantThreePolynomial68 A B c d e
  have hSdeg := grokRowOneEndgame_S_degree_le_cubicFace68 A B c d e n g h
    hg hgh hh hsmall hbalanced hA hB hc hd he hI3
  have hStop := grokRowOneEndgame_S_coeff_cubicFace68 A B c d e n g h
    hg hgh hh hsmall hbalanced hA hB hc hd he hI3
  have hASdeg : (A * S).natDegree ≤ 12 * n - 3 * g := by
    have h := natDegree_mul_le_of_le hA hSdeg
    have hi : 2 * n + (10 * n - 3 * g) = 12 * n - 3 * g := by omega
    rwa [hi] at h
  have hAScoeff := coeff_mul_at_bounds68 A S (2 * n) (10 * n - 3 * g) hA hSdeg
  have hiAS : 2 * n + (10 * n - 3 * g) = 12 * n - 3 * g := by omega
  rw [hiAS, hStop] at hAScoeff
  have hASder := coeff_derivative_at_bound68 (A * S) (12 * n - 3 * g) (by omega)
  rw [hAScoeff] at hASder
  have h2AS :
      ((2 : k) • derivative (A * S)).coeff idx =
        A.coeff (2 * n) *
          ((3 : k) * d.coeff (5 * n - h) ^ 2 -
            (2 : k) * B.coeff (3 * n - g) ^ 2 * c.coeff (4 * n - g)) *
          ((12 * n - 3 * g : ℕ) : k) := by
    rw [coeff_smul, hASder]
    ring
  have hI3low : (derivative A * I3).natDegree < idx := by
    have h := grokRowOneEndgame_natDegree_derivative_mul_lt68 A I3
      (2 * n) (10 * n - 3 * g) (by omega) hA hI3
    have hi : 2 * n + (10 * n - 3 * g) - 1 = idx := by
      dsimp [idx]
      omega
    simpa only [hi] using h
  have hc2deg : (c ^ 2).natDegree ≤ 8 * n - 2 * g := by
    have h1 := (natDegree_pow_le c 2).trans (Nat.mul_le_mul_left 2 hc)
    have hi : 2 * (4 * n - g) = 8 * n - 2 * g := by omega
    rwa [hi] at h1
  have hc2 : (c ^ 2).coeff (8 * n - 2 * g) = c.coeff (4 * n - g) ^ 2 := by
    have h := coeff_pow_at_bound68 c (4 * n - g) 2 hc
    have hi : 2 * (4 * n - g) = 8 * n - 2 * g := by omega
    simpa only [hi] using h
  have hc3 := coeff_mul_derivative_at_bounds68 (c ^ 2) c
    (8 * n - 2 * g) (4 * n - g) (by omega) hc2deg hc
  have hic3 : (8 * n - 2 * g) + (4 * n - g) - 1 = idx := by
    dsimp [idx]
    omega
  rw [hic3, hc2] at hc3
  have hee := coeff_mul_derivative_at_bounds68 e e
    (6 * n - h) (6 * n - h) (by omega) he he
  have hiee : (6 * n - h) + (6 * n - h) - 1 = 12 * n - 2 * h - 1 := by omega
  rw [hiee] at hee
  have hidx_ee : 12 * n - 2 * h - 1 = idx := by
    dsimp [idx]
    omega
  have hlowBcd : (derivative (B * c * d)).natDegree < idx := by
    dsimp [idx]
    exact grokRowOneEndgame_Bcd_der_degree_lt68 B c d n g h hgh hsmall hB hc hd
  have hlowBp : (derivative B * c * d).natDegree < idx := by
    dsimp [idx]
    exact grokRowOneEndgame_Bp_cd_degree_lt68 B c d n g h hg hgh hsmall hB hc hd
  have hlowBe : (B ^ 2 * derivative e).natDegree < idx := by
    dsimp [idx]
    exact grokRowOneEndgame_B2e_der_degree_lt68 B e n g h hg hgh hsmall hB he
  have h0I3 : ((9 / 4 : k) • (derivative A * I3)).coeff idx = 0 := by
    rw [coeff_smul, coeff_eq_zero_of_natDegree_lt hI3low, mul_zero]
  have h0Bcd : ((3 : k) • derivative (B * c * d)).coeff idx = 0 := by
    rw [coeff_smul, coeff_eq_zero_of_natDegree_lt hlowBcd, mul_zero]
  have h0Bp : ((6 : k) • (derivative B * c * d)).coeff idx = 0 := by
    rw [coeff_smul, coeff_eq_zero_of_natDegree_lt hlowBp, mul_zero]
  have h0Be : ((3 : k) • (B ^ 2 * derivative e)).coeff idx = 0 := by
    rw [coeff_smul, coeff_eq_zero_of_natDegree_lt hlowBe, mul_zero]
  have hc3sm : ((6 : k) • (c ^ 2 * derivative c)).coeff idx =
      (6 : k) * ((4 * n - g : ℕ) : k) * c.coeff (4 * n - g) ^ 3 := by
    rw [coeff_smul, hc3]
    ring
  have heesm : ((18 : k) • (e * derivative e)).coeff idx =
      (18 : k) * ((6 * n - h : ℕ) : k) * e.coeff (6 * n - h) ^ 2 := by
    rw [← hidx_ee, coeff_smul, hee]
    ring
  have hinner : (grokRowOneEndgameInner68 A B c d e).coeff idx =
      A.coeff (2 * n) *
          ((3 : k) * d.coeff (5 * n - h) ^ 2 -
            (2 : k) * B.coeff (3 * n - g) ^ 2 * c.coeff (4 * n - g)) *
          ((12 * n - 3 * g : ℕ) : k) +
        (6 : k) * ((4 * n - g : ℕ) : k) * c.coeff (4 * n - g) ^ 3 -
        (18 : k) * ((6 * n - h : ℕ) : k) * e.coeff (6 * n - h) ^ 2 := by
    dsimp [grokRowOneEndgameInner68]
    simp only [coeff_add, coeff_sub]
    rw [h2AS, h0I3, h0Bcd, h0Bp, h0Be, hc3sm, heesm]
    ring
  rw [grokRowOneEndgame_eq_inner68, coeff_smul, hinner]

/-- Residual row one at the balanced cubic face equals
`(-64/9)*(4n-g)*c_top^3`. -/
theorem grokRowOneEndgame_coeff_eq68
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
  rw [grokRowOneEndgame_coeff_inner68 A B c d e n g h hg hgh hh hsmall
    hbalanced hA hB hcdeg hd he hI3]
  have hcast12 : (((12 * n - 3 * g : ℕ) : k)) =
      (12 : k) * (n : k) - (3 : k) * (g : k) := by
    rw [Nat.cast_sub (by omega : 3 * g ≤ 12 * n), Nat.cast_mul, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_ofNat]
  have hcast4 : (((4 * n - g : ℕ) : k)) =
      (4 : k) * (n : k) - (g : k) := by
    rw [Nat.cast_sub (by omega : g ≤ 4 * n), Nat.cast_mul, Nat.cast_ofNat]
  have hcast6 : (((6 * n - h : ℕ) : k)) =
      (6 : k) * (n : k) - (h : k) := by
    rw [Nat.cast_sub (by omega : h ≤ 6 * n), Nat.cast_mul, Nat.cast_ofNat]
  have hbal : (2 : k) * (h : k) = (3 : k) * (g : k) := by
    have := congrArg (fun m : ℕ => (m : k)) hbalanced
    push_cast at this
    exact this
  rw [hcast12, hcast4, hcast6]
  exact grokRowOneEndgame_scalar68 (n : k) (g : k) (h : k)
    (A.coeff (2 * n)) (B.coeff (3 * n - g)) (c.coeff (4 * n - g))
    (d.coeff (5 * n - h)) (e.coeff (6 * n - h)) hc0 hbal hdisc hinc hrel

/-- Residual row one cannot vanish at the balanced cubic face. -/
theorem grokRowOneEndgame_coeff_ne_zero68
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
  rw [grokRowOneEndgame_coeff_eq68 A B c d e n g h hg hgh hh hsmall
    hbalanced hA hB hcdeg hd he hI3 hc0 hdisc hinc hrel]
  have hcast4 : (((4 * n - g : ℕ) : k)) =
      (4 : k) * (n : k) - (g : k) := by
    rw [Nat.cast_sub (by omega : g ≤ 4 * n), Nat.cast_mul, Nat.cast_ofNat]
  have hNG : (4 : k) * (n : k) - (g : k) ≠ 0 := by
    rw [← hcast4]
    exact Nat.cast_ne_zero.mpr (by omega : 4 * n - g ≠ 0)
  have hbal : (2 : k) * (h : k) = (3 : k) * (g : k) := by
    have := congrArg (fun m : ℕ => (m : k)) hbalanced
    push_cast at this
    exact this
  rw [hcast4]
  exact grokRowOneEndgame_scalar_ne_zero68 (n : k) (g : k) (h : k)
    (A.coeff (2 * n)) (B.coeff (3 * n - g)) (c.coeff (4 * n - g))
    (d.coeff (5 * n - h)) (e.coeff (6 * n - h)) hc0 hNG hbal hdisc hinc hrel

end GrokRowOneEndgameAlt68

#print axioms grokRowOneEndgame_S_I3_identity68
#print axioms grokRowOneEndgame_eq_inner68
#print axioms grokRowOneEndgame_S_degree_le_cubicFace68
#print axioms grokRowOneEndgame_S_coeff_cubicFace68
#print axioms grokRowOneEndgame_coeff_inner68
#print axioms grokRowOneEndgame_coeff_eq68
#print axioms grokRowOneEndgame_coeff_ne_zero68

end Max11DegreeRoutes
