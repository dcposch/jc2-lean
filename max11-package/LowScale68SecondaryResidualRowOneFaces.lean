import LowScale68SecondaryResidualRowTwoBalanced

/-! # Balanced residual row-one cubic face after `2h = 3g`

Row two on this wall is already rewritten through the incidence defect `Q`
in the tracked tower.  Residual row one is the companion one-form: it
rewrites through the cubic first integral `I3`, without an auxiliary cubic
combination `S`.

After `I3.natDegree < 10*n - 3*g`, the `A * I3'` contribution lies strictly
below `12*n - 3*g - 1`.  On `2*h = 3*g` the `B*c*d` and `B^2*e'` faces are
likewise strictly below.  The surviving inner coefficient is
`a*(3*d_top^2 - 2*b^2*c_top)*(12*n-3*g) + 6*(4*n-g)*c_top^3 - 18*(6*n-h)*e_top^2`.
Discriminant, incidence, and the balanced row-two relation collapse this to
`48*(4*n-g)*c_top^3`, hence residual row one has coefficient
`(-64/9)*(4*n-g)*c_top^3`.  In characteristic zero this is nonzero on a
nontrivial middle face.

Constant-Jacobian loads and the system-level identification of `I3` with a
first integral are not discharged here.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section ResidualRowOneEndgame68

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Inner expression of residual row one after the `I3` rewrite, before
`-4/27`. -/
def residualRowOneInner68 (A B c d e : k[X]) : k[X] :=
  let I3 := secondaryResidualInvariantThreePolynomial68 A B c d e
  (-9 / 4 : k) • (A * derivative I3) +
    (3 : k) • derivative (A * d ^ 2) +
    (-2 : k) • derivative (A * B ^ 2 * c) +
    (6 : k) • (c ^ 2 * derivative c) +
    (3 : k) • derivative (B * c * d) +
    (6 : k) • (derivative B * c * d) +
    (-3 : k) • (B ^ 2 * derivative e) +
    (-18 : k) • (e * derivative e)

set_option maxHeartbeats 8000000 in
/-- Residual row one is the inner `I3` rewrite scaled by `-4/27`. -/
theorem residualRowOne_eq_inner68 (A B c d e : k[X]) :
    secondaryResidualRowOnePolynomial68 A B c d e =
      (-4 / 27 : k) • residualRowOneInner68 A B c d e := by
  simp only [secondaryResidualRowOnePolynomial68, residualRowOneInner68,
    secondaryResidualInvariantThreePolynomial68,
    derivative_add, derivative_sub, derivative_mul, derivative_smul,
    derivative_pow, derivative_C, zero_mul, zero_add, smul_add, smul_sub,
    Polynomial.smul_eq_C_mul]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_zero,
    RatFunc.algebraMap_C, map_div₀, map_ofNat, map_natCast, map_one]
  ring

/-! ## Field algebra on the middle face plus `4*b*c^2-9*d*e=0` -/

theorem residualRowOne_disc_imp_b_ne_zero68
    (a b c : k) (hc : c ≠ 0)
    (hdisc : a * b ^ 2 + (3 : k) * c ^ 2 = 0) : b ≠ 0 := by
  intro hb
  have : (3 : k) * c ^ 2 = 0 := by simpa [hb] using hdisc
  have hc2 : c ^ 2 = 0 := (mul_eq_zero.mp this).resolve_left (by norm_num)
  exact hc (sq_eq_zero_iff.mp hc2)

theorem residualRowOne_nine_d_sq_of_relations68
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

theorem residualRowOne_nine_e_sq_of_relations68
    (a b c d e : k) (hc : c ≠ 0)
    (hdisc : a * b ^ 2 + (3 : k) * c ^ 2 = 0)
    (hinc : b * e + c * d = 0)
    (hrel : (4 : k) * b * c ^ 2 - (9 : k) * d * e = 0) :
    (9 : k) * e ^ 2 + (4 : k) * c ^ 3 = 0 := by
  have hb := residualRowOne_disc_imp_b_ne_zero68 a b c hc hdisc
  have hd := residualRowOne_nine_d_sq_of_relations68 a b c d e hc hdisc hinc hrel
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
theorem residualRowOneInnerScalar68
    (N G H a b c d e : k) (hc : c ≠ 0)
    (hbal : (2 : k) * H = (3 : k) * G)
    (hdisc : a * b ^ 2 + (3 : k) * c ^ 2 = 0)
    (hinc : b * e + c * d = 0)
    (hrel : (4 : k) * b * c ^ 2 - (9 : k) * d * e = 0) :
    a * ((3 : k) * d ^ 2 - (2 : k) * b ^ 2 * c) * ((12 : k) * N - (3 : k) * G) +
        (6 : k) * ((4 : k) * N - G) * c ^ 3 -
        (18 : k) * ((6 : k) * N - H) * e ^ 2 =
      (48 : k) * ((4 : k) * N - G) * c ^ 3 := by
  have hd := residualRowOne_nine_d_sq_of_relations68 a b c d e hc hdisc hinc hrel
  have he := residualRowOne_nine_e_sq_of_relations68 a b c d e hc hdisc hinc hrel
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
  have hH : H = ((3 : k) / 2) * G := by
    linear_combination (1 / 2 : k) * hbal
  rw [hAterm, he2, hH]
  ring

/-- Scaling the inner cubic identity by `-4/27` produces the residual
row-one prefactor `-64/9`. -/
theorem residualRowOneScalar68
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
  rw [residualRowOneInnerScalar68 N G H a b c d e hc hbal hdisc hinc hrel]
  ring

theorem residualRowOneScalar_ne_zero68
    (N G H a b c d e : k) (hc : c ≠ 0)
    (hNG : (4 : k) * N - G ≠ 0)
    (hbal : (2 : k) * H = (3 : k) * G)
    (hdisc : a * b ^ 2 + (3 : k) * c ^ 2 = 0)
    (hinc : b * e + c * d = 0)
    (hrel : (4 : k) * b * c ^ 2 - (9 : k) * d * e = 0) :
    (-64 / 9 : k) * ((4 : k) * N - G) * c ^ 3 ≠ 0 :=
  mul_ne_zero (mul_ne_zero (by norm_num) hNG) (pow_ne_zero 3 hc)

/-! ## Degree lemmas -/

private theorem residualRowOne_natDegree_mul_derivative_lt68
    (p q : k[X]) (u v : ℕ)
    (hu : p.natDegree ≤ u) (hv : 1 < v) (hq : q.natDegree < v) :
    (p * derivative q).natDegree < u + v - 1 := by
  have hq' : q.natDegree ≤ v - 1 := Nat.le_sub_one_of_lt hq
  have hd : (derivative q).natDegree ≤ v - 2 := by
    have h := natDegree_derivative_le q
    omega
  have hmul := natDegree_mul_le_of_le hu hd
  omega

/-! ## Cubic-face coefficient after the `I3` drop -/

set_option maxHeartbeats 6000000 in
/-- On `2h=3g`, residual row one has inner cubic-face coefficient
`a*(3*d_top^2-2*b^2*c_top)*(12n-3g)+6*(4n-g)*c_top^3-18*(6n-h)*e_top^2`. -/
theorem residualRowOne_coeff_balancedChamber68
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
  let I3 := secondaryResidualInvariantThreePolynomial68 A B c d e
  set idx := 12 * n - 3 * g - 1
  have hI3low : (A * derivative I3).natDegree < idx := by
    have hv : 1 < 10 * n - 3 * g := by omega
    have h := residualRowOne_natDegree_mul_derivative_lt68 A I3
      (2 * n) (10 * n - 3 * g) hA hv hI3
    have hi : 2 * n + (10 * n - 3 * g) - 1 = idx := by
      dsimp [idx]; omega
    simpa only [hi] using h
  have hd2deg : (d ^ 2).natDegree ≤ 10 * n - 3 * g := by
    compute_degree
    omega
  have hd2 : (d ^ 2).coeff (10 * n - 3 * g) =
      d.coeff (5 * n - h) ^ 2 := by
    have hd2pow := coeff_pow_at_bound68 d (5 * n - h) 2 hd
    have hi : 2 * (5 * n - h) = 10 * n - 3 * g := by omega
    simpa only [hi] using hd2pow
  have hAd2coeff := coeff_mul_at_bounds68 A (d ^ 2) (2 * n) (10 * n - 3 * g)
    hA hd2deg
  have hiAd2 : 2 * n + (10 * n - 3 * g) = 12 * n - 3 * g := by omega
  rw [hiAd2, hd2] at hAd2coeff
  have hAd2der := coeff_derivative_at_bound68 (A * d ^ 2)
    (12 * n - 3 * g) (by omega)
  rw [hAd2coeff] at hAd2der
  have hB2deg : (B ^ 2).natDegree ≤ 6 * n - 2 * g := by
    compute_degree
    omega
  have hB2 : (B ^ 2).coeff (6 * n - 2 * g) =
      B.coeff (3 * n - g) ^ 2 := by
    have hB2pow := coeff_pow_at_bound68 B (3 * n - g) 2 hB
    have hi : 2 * (3 * n - g) = 6 * n - 2 * g := by omega
    simpa only [hi] using hB2pow
  have hAB2ccoeff := coeff_mul_mul_at_bounds68 A (B ^ 2) c
    (2 * n) (6 * n - 2 * g) (4 * n - g) hA hB2deg hc
  have hiAB2c : 2 * n + (6 * n - 2 * g) + (4 * n - g) = 12 * n - 3 * g :=
    by omega
  rw [hiAB2c, hB2] at hAB2ccoeff
  have hAB2cder := coeff_derivative_at_bound68 (A * B ^ 2 * c)
    (12 * n - 3 * g) (by omega)
  rw [hAB2ccoeff] at hAB2cder
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
  have hlowFace : 12 * n - 2 * g - h - 1 < idx := by
    dsimp [idx]
    omega
  have hlowBcd : (derivative (B * c * d)).natDegree < idx := by
    have hBc : (B * c).natDegree ≤ (3 * n - g) + (4 * n - g) :=
      natDegree_mul_le_of_le hB hc
    have hprod := natDegree_mul_le_of_le hBc hd
    have hsum : (3 * n - g) + (4 * n - g) + (5 * n - h) =
        12 * n - 2 * g - h := by omega
    rw [hsum] at hprod
    have hder := natDegree_derivative_le (B * c * d)
    have hle : (derivative (B * c * d)).natDegree ≤
        12 * n - 2 * g - h - 1 := by omega
    exact hle.trans_lt hlowFace
  have hlowBp : (derivative B * c * d).natDegree < idx := by
    have hdB : (derivative B).natDegree ≤ 3 * n - g - 1 :=
      (natDegree_derivative_le B).trans (by omega)
    have hcd : (c * d).natDegree ≤ (4 * n - g) + (5 * n - h) :=
      natDegree_mul_le_of_le hc hd
    have hprod := natDegree_mul_le_of_le hdB hcd
    have hsum : (3 * n - g - 1) + ((4 * n - g) + (5 * n - h)) =
        12 * n - 2 * g - h - 1 := by omega
    have hle : (derivative B * (c * d)).natDegree ≤
        12 * n - 2 * g - h - 1 := by
      simpa only [hsum] using hprod
    have hassoc : derivative B * (c * d) = derivative B * c * d := by
      ring
    rw [hassoc] at hle
    exact hle.trans_lt hlowFace
  have hlowBe : (B ^ 2 * derivative e).natDegree < idx := by
    have hde : (derivative e).natDegree ≤ 6 * n - h - 1 :=
      (natDegree_derivative_le e).trans (by omega)
    have hprod := natDegree_mul_le_of_le hB2deg hde
    have hsum : (6 * n - 2 * g) + (6 * n - h - 1) =
        12 * n - 2 * g - h - 1 := by omega
    have hle : (B ^ 2 * derivative e).natDegree ≤
        12 * n - 2 * g - h - 1 := by
      simpa only [hsum] using hprod
    exact hle.trans_lt hlowFace
  have h0I3 : ((-9 / 4 : k) • (A * derivative I3)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hI3low, mul_zero]
  have h0Bcd : ((3 : k) • derivative (B * c * d)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hlowBcd, mul_zero]
  have h0Bp : ((6 : k) • (derivative B * c * d)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hlowBp, mul_zero]
  have h0Be : ((-3 : k) • (B ^ 2 * derivative e)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hlowBe, mul_zero]
  have hAd2sm : ((3 : k) • derivative (A * d ^ 2)).coeff idx =
      (3 : k) * (A.coeff (2 * n) * d.coeff (5 * n - h) ^ 2 *
        ((12 * n - 3 * g : ℕ) : k)) := by
    rw [coeff_smul, smul_eq_mul]
    dsimp [idx]
    rw [hAd2der]
  have hAB2csm : ((-2 : k) • derivative (A * B ^ 2 * c)).coeff idx =
      (-2 : k) * (A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 *
        c.coeff (4 * n - g) * ((12 * n - 3 * g : ℕ) : k)) := by
    rw [coeff_smul, smul_eq_mul]
    dsimp [idx]
    rw [hAB2cder]
  have hc3sm : ((6 : k) • (c ^ 2 * derivative c)).coeff idx =
      (6 : k) * (c.coeff (4 * n - g) ^ 2 * c.coeff (4 * n - g) *
        ((4 * n - g : ℕ) : k)) := by
    rw [coeff_smul, smul_eq_mul, hc3]
  have heesm : ((-18 : k) • (e * derivative e)).coeff idx =
      (-18 : k) * (e.coeff (6 * n - h) ^ 2 * ((6 * n - h : ℕ) : k)) := by
    rw [coeff_smul, smul_eq_mul, ← hidx_ee, hee]
    ring
  have hinner : (residualRowOneInner68 A B c d e).coeff idx =
      A.coeff (2 * n) *
          ((3 : k) * d.coeff (5 * n - h) ^ 2 -
            (2 : k) * B.coeff (3 * n - g) ^ 2 * c.coeff (4 * n - g)) *
          ((12 * n - 3 * g : ℕ) : k) +
        (6 : k) * ((4 * n - g : ℕ) : k) * c.coeff (4 * n - g) ^ 3 -
        (18 : k) * ((6 * n - h : ℕ) : k) * e.coeff (6 * n - h) ^ 2 := by
    dsimp [residualRowOneInner68]
    simp only [coeff_add]
    rw [h0I3, hAd2sm, hAB2csm, hc3sm, h0Bcd, h0Bp, h0Be, heesm]
    ring
  rw [residualRowOne_eq_inner68, coeff_smul, smul_eq_mul, hinner]

set_option maxHeartbeats 2000000 in
theorem residualRowOne_coeff_balancedChamber_eq68
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
  rw [residualRowOne_coeff_balancedChamber68 A B c d e n g h hg hgh hh hsmall
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
  exact residualRowOneScalar68 (n : k) (g : k) (h : k)
    (A.coeff (2 * n)) (B.coeff (3 * n - g)) (c.coeff (4 * n - g))
    (d.coeff (5 * n - h)) (e.coeff (6 * n - h)) hc0 hbal hdisc hinc hrel

/-- Residual row one cannot vanish at the balanced cubic face. -/
theorem residualRowOne_balanced_coeff_ne_zero68
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
  rw [residualRowOne_coeff_balancedChamber_eq68 A B c d e n g h hg hgh hh
    hsmall hbalanced hA hB hcdeg hd he hI3 hc0 hdisc hinc hrel]
  have hcast4 : (((4 * n - g : ℕ) : k)) =
      (4 : k) * (n : k) - (g : k) := by
    rw [Nat.cast_sub (by omega : g ≤ 4 * n)]
    push_cast
    rfl
  rw [hcast4]
  have hNG : (4 : k) * (n : k) - (g : k) ≠ 0 := by
    rw [← hcast4]
    exact Nat.cast_ne_zero.mpr (by omega)
  exact residualRowOneScalar_ne_zero68 (n : k) (g : k) (h : k)
    (A.coeff (2 * n)) (B.coeff (3 * n - g)) (c.coeff (4 * n - g))
    (d.coeff (5 * n - h)) (e.coeff (6 * n - h)) hc0 hNG
    (by
      have := congrArg (fun m : ℕ => (m : k)) hbalanced
      push_cast at this
      exact this)
    hdisc hinc hrel

theorem residualRowOne_eq_zero_imp_false68
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
  exact residualRowOne_balanced_coeff_ne_zero68 A B c d e n g h hg hgh hh
    hsmall hbalanced hA hB hcdeg hd he hI3 hc0 hdisc hinc hrel hcoeff

theorem residualRowOne_add_load_eq_zero_imp_false68
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
  exact residualRowOne_balanced_coeff_ne_zero68 A B c d e n g h hg hgh hh
    hsmall hbalanced hA hB hcdeg hd he hI3 hc0 hdisc hinc hrel hcoeff

end ResidualRowOneEndgame68

#print axioms residualRowOne_eq_inner68
#print axioms residualRowOneInnerScalar68
#print axioms residualRowOneScalar68
#print axioms residualRowOne_coeff_balancedChamber68
#print axioms residualRowOne_coeff_balancedChamber_eq68
#print axioms residualRowOne_balanced_coeff_ne_zero68
#print axioms residualRowOne_eq_zero_imp_false68
#print axioms residualRowOne_add_load_eq_zero_imp_false68

end Max11DegreeRoutes
