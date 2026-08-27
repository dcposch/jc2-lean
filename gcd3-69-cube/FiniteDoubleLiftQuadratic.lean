import FiniteDoubleLiftCoefficients
import FiniteDoubleSourceOrderLower

/-! # The quadratic stage of the moving double-root lift

Before the intrinsic cubic scale, the first two exact moving-root rows force
the two linear-kernel remainders to acquire a second copy of the common Hahn
monomial.  This is the divisibility input needed to expose the quadratic
third-row obstruction.
-/

noncomputable section

namespace GCD369CubeHahnRegular

/-- Coefficients commute with multiplication by an integer scalar. -/
theorem coeff_int_mul
    {k : Type*} [Field k] (z : ℤ) (x : GCD369CubeHahnRegular k)
    (e : ℚ) :
    ((z : GCD369CubeHahnRegular k) * x).1.coeff e =
      (z : k) * x.1.coeff e := by
  change (HahnSeries.C (z : k) * x.1).coeff e = _
  rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]

/-- A lower order bound on a product by a regular unit descends to the other
factor. -/
theorem orderTop_lower_of_unit_mul
    {k : Type*} [Field k]
    (u x : GCD369CubeHahnRegular k) (alpha : ℚ)
    (hu : constantCoeff u ≠ 0)
    (hux : (↑alpha : WithTop ℚ) ≤ (u * x).1.orderTop) :
    (↑alpha : WithTop ℚ) ≤ x.1.orderTop := by
  let ui : GCD369CubeHahnRegular k := invOfConstantCoeffNe u hu
  have hui : ui * u = 1 := by
    rw [mul_comm]
    exact mul_invOfConstantCoeffNe u hu
  have hx : x = ui * (u * x) := by
    rw [← mul_assoc, hui, one_mul]
  rw [hx]
  simpa only [zero_add] using
    (mul_orderTop_lower ui (u * x) 0 alpha ui.2 hux)

/-- If a monomial times a regular series has order at least twice the
monomial exponent, the remaining series has order at least one copy of that
exponent. -/
theorem orderTop_lower_of_monomial_mul_orderTop_lower
    {k : Type*} [Field k]
    (mu : ℚ) (hmu : 0 < mu) (x : GCD369CubeHahnRegular k)
    (hMx : (↑(2 * mu) : WithTop ℚ) ≤
      (monomial mu hmu.le * x).1.orderTop) :
    (↑mu : WithTop ℚ) ≤ x.1.orderTop := by
  rw [HahnSeries.le_orderTop_iff_forall]
  intro q hq
  have hq' : q < mu := WithTop.coe_lt_coe.mp hq
  have hlt : (↑(q + mu) : WithTop ℚ) < (↑(2 * mu) : WithTop ℚ) := by
    exact WithTop.coe_lt_coe.mpr (by linarith)
  have hz : (monomial mu hmu.le * x).1.coeff (q + mu) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop (hlt.trans_le hMx)
  have hs' : (monomial mu hmu.le * x).1.coeff (q + mu) = x.1.coeff q := by
    change (HahnSeries.single mu (1 : k) * x.1).coeff (q + mu) =
      x.1.coeff q
    rw [HahnSeries.coeff_single_mul]
    simp only [one_mul]
    congr 1
    ring
  rw [hs'] at hz
  exact hz

/-- A square of the positive monomial puts every regular multiple at order at
least twice the exponent. -/
theorem monomial_sq_mul_orderTop_lower
    {k : Type*} [Field k]
    (mu : ℚ) (hmu : 0 < mu) (x : GCD369CubeHahnRegular k) :
    (↑(2 * mu) : WithTop ℚ) ≤
      ((monomial mu hmu.le) ^ 2 * x).1.orderTop := by
  let M : GCD369CubeHahnRegular k := monomial mu hmu.le
  have hM : (↑mu : WithTop ℚ) ≤ M.1.orderTop := by
    exact (monomial_orderTop_and_leadingCoeff mu hmu.le).1.ge
  have hMx : (↑mu : WithTop ℚ) ≤ (M * x).1.orderTop :=
    monomial_mul_orderTop_lower mu hmu.le x
  have h := mul_orderTop_lower M (M * x) mu mu hM hMx
  rw [show M * (M * x) = M ^ 2 * x by ring] at h
  simpa only [show mu + mu = 2 * mu by ring, M] using h

/-- Order at least `2*mu` in the first two exact rows forces both normalized
linear-kernel remainders to be divisible by the common monomial. -/
theorem doubleBlowup_kernelRemainders_order_lower
    {k : Type*} [Field k] [CharZero k]
    (A r D B C : GCD369CubeHahnRegular k)
    (J : TripleScale D B C)
    (hA : constantCoeff A ≠ 0) (hr : constantCoeff r ≠ 0)
    (hR1 : (↑(2 * J.mu) : WithTop ℚ) ≤
      (A ^ 2 * D - 2 * A * B * r - B ^ 2 - 2 * A * C).1.orderTop)
    (hR2 : (↑(2 * J.mu) : WithTop ℚ) ≤
      (2 * A ^ 2 * r * D - 3 * A * B * r ^ 2 - 3 * A * C * r +
        3 * A * B * D - 3 * B * C).1.orderTop) :
    (↑J.mu : WithTop ℚ) ≤ J.Dn.1.orderTop ∧
      (↑J.mu : WithTop ℚ) ≤
        (J.Cn + r * J.Bn).1.orderTop := by
  let mu : ℚ := J.mu
  let M : GCD369CubeHahnRegular k := monomial mu J.hmu.le
  let Qn : GCD369CubeHahnRegular k := J.Cn + r * J.Bn
  let L1 : GCD369CubeHahnRegular k := A ^ 2 * J.Dn - 2 * A * Qn
  let L2 : GCD369CubeHahnRegular k :=
    2 * A ^ 2 * r * J.Dn - 3 * A * r * Qn
  let P2 : GCD369CubeHahnRegular k :=
    3 * A * J.Bn * J.Dn - 3 * J.Bn * J.Cn
  let R1 : GCD369CubeHahnRegular k :=
    A ^ 2 * D - 2 * A * B * r - B ^ 2 - 2 * A * C
  let R2 : GCD369CubeHahnRegular k :=
    2 * A ^ 2 * r * D - 3 * A * B * r ^ 2 - 3 * A * C * r +
      3 * A * B * D - 3 * B * C
  have hfac1 : R1 = M * L1 - M ^ 2 * J.Bn ^ 2 := by
    calc
      R1 = A ^ 2 * D - 2 * A * B * r - B ^ 2 - 2 * A * C := rfl
      _ = A ^ 2 * (M * J.Dn) - 2 * A * B * r - B ^ 2 - 2 * A * C :=
        congrArg
          (fun z : GCD369CubeHahnRegular k =>
            A ^ 2 * z - 2 * A * B * r - B ^ 2 - 2 * A * C) J.hD
      _ = A ^ 2 * (M * J.Dn) - 2 * A * (M * J.Bn) * r -
          (M * J.Bn) ^ 2 - 2 * A * C :=
        congrArg
          (fun z : GCD369CubeHahnRegular k =>
            A ^ 2 * (M * J.Dn) - 2 * A * z * r - z ^ 2 - 2 * A * C) J.hB
      _ = A ^ 2 * (M * J.Dn) - 2 * A * (M * J.Bn) * r -
          (M * J.Bn) ^ 2 - 2 * A * (M * J.Cn) :=
        congrArg
          (fun z : GCD369CubeHahnRegular k =>
            A ^ 2 * (M * J.Dn) - 2 * A * (M * J.Bn) * r -
              (M * J.Bn) ^ 2 - 2 * A * z) J.hC
      _ = M * L1 - M ^ 2 * J.Bn ^ 2 := by
        dsimp only [L1, Qn]
        ring
  have hfac2 : R2 = M * L2 + M ^ 2 * P2 := by
    calc
      R2 = 2 * A ^ 2 * r * D - 3 * A * B * r ^ 2 - 3 * A * C * r +
          3 * A * B * D - 3 * B * C := rfl
      _ = 2 * A ^ 2 * r * (M * J.Dn) - 3 * A * B * r ^ 2 -
          3 * A * C * r + 3 * A * B * (M * J.Dn) - 3 * B * C :=
        congrArg
          (fun z : GCD369CubeHahnRegular k =>
            2 * A ^ 2 * r * z - 3 * A * B * r ^ 2 - 3 * A * C * r +
              3 * A * B * z - 3 * B * C) J.hD
      _ = 2 * A ^ 2 * r * (M * J.Dn) - 3 * A * (M * J.Bn) * r ^ 2 -
          3 * A * C * r + 3 * A * (M * J.Bn) * (M * J.Dn) -
          3 * (M * J.Bn) * C :=
        congrArg
          (fun z : GCD369CubeHahnRegular k =>
            2 * A ^ 2 * r * (M * J.Dn) - 3 * A * z * r ^ 2 -
              3 * A * C * r + 3 * A * z * (M * J.Dn) - 3 * z * C) J.hB
      _ = 2 * A ^ 2 * r * (M * J.Dn) - 3 * A * (M * J.Bn) * r ^ 2 -
          3 * A * (M * J.Cn) * r +
          3 * A * (M * J.Bn) * (M * J.Dn) -
          3 * (M * J.Bn) * (M * J.Cn) :=
        congrArg
          (fun z : GCD369CubeHahnRegular k =>
            2 * A ^ 2 * r * (M * J.Dn) - 3 * A * (M * J.Bn) * r ^ 2 -
              3 * A * z * r + 3 * A * (M * J.Bn) * (M * J.Dn) -
              3 * (M * J.Bn) * z) J.hC
      _ = M * L2 + M ^ 2 * P2 := by
        dsimp only [L2, Qn, P2]
        ring
  have htail1 : (↑(2 * mu) : WithTop ℚ) ≤
      (M ^ 2 * J.Bn ^ 2).1.orderTop := by
    simpa only [M] using monomial_sq_mul_orderTop_lower mu J.hmu (J.Bn ^ 2)
  have htail2 : (↑(2 * mu) : WithTop ℚ) ≤
      (M ^ 2 * P2).1.orderTop := by
    simpa only [M] using monomial_sq_mul_orderTop_lower mu J.hmu P2
  have hML1 : (↑(2 * mu) : WithTop ℚ) ≤ (M * L1).1.orderTop := by
    have hsum := add_orderTop_lower R1 (M ^ 2 * J.Bn ^ 2) (2 * mu)
      (by simpa only [R1, mu] using hR1) htail1
    rw [show M * L1 = R1 + M ^ 2 * J.Bn ^ 2 by
      rw [hfac1]
      ring]
    exact hsum
  have hML2 : (↑(2 * mu) : WithTop ℚ) ≤ (M * L2).1.orderTop := by
    have hneg : (↑(2 * mu) : WithTop ℚ) ≤
        (- (M ^ 2 * P2)).1.orderTop := by
      change (↑(2 * mu) : WithTop ℚ) ≤
        (- (M ^ 2 * P2).1).orderTop
      rw [HahnSeries.orderTop_neg]
      exact htail2
    have hsum := add_orderTop_lower R2 (- (M ^ 2 * P2)) (2 * mu)
      (by simpa only [R2, mu] using hR2) hneg
    rw [show M * L2 = R2 + -(M ^ 2 * P2) by
      rw [hfac2]
      ring]
    exact hsum
  have hL1 : (↑mu : WithTop ℚ) ≤ L1.1.orderTop :=
    orderTop_lower_of_monomial_mul_orderTop_lower mu J.hmu L1 hML1
  have hL2 : (↑mu : WithTop ℚ) ≤ L2.1.orderTop :=
    orderTop_lower_of_monomial_mul_orderTop_lower mu J.hmu L2 hML2
  have htwoL2 : (↑mu : WithTop ℚ) ≤ (2 * L2).1.orderTop := by
    simpa only [zero_add] using
      (mul_orderTop_lower (2 : GCD369CubeHahnRegular k) L2 0 mu
        (2 : GCD369CubeHahnRegular k).2 hL2)
  have hrL1 : (↑mu : WithTop ℚ) ≤ (r * L1).1.orderTop := by
    simpa only [zero_add] using
      (mul_orderTop_lower r L1 0 mu r.2 hL1)
  have hthree_rL1 : (↑mu : WithTop ℚ) ≤
      (3 * (r * L1)).1.orderTop := by
    simpa only [zero_add] using
      (mul_orderTop_lower (3 : GCD369CubeHahnRegular k) (r * L1) 0 mu
        (3 : GCD369CubeHahnRegular k).2 hrL1)
  have hnegthree : (↑mu : WithTop ℚ) ≤
      (- (3 * (r * L1))).1.orderTop := by
    change (↑mu : WithTop ℚ) ≤ (- (3 * (r * L1)).1).orderTop
    rw [HahnSeries.orderTop_neg]
    exact hthree_rL1
  have hcomb := add_orderTop_lower (2 * L2) (- (3 * (r * L1))) mu
    htwoL2 hnegthree
  have hprod : (↑mu : WithTop ℚ) ≤
      (A ^ 2 * r * J.Dn).1.orderTop := by
    rw [show A ^ 2 * r * J.Dn = 2 * L2 + -(3 * (r * L1)) by
      dsimp only [L1, L2, Qn]
      ring]
    exact hcomb
  have huAr : constantCoeff (A ^ 2 * r) ≠ 0 := by
    simp only [map_mul, map_pow]
    exact mul_ne_zero (pow_ne_zero 2 hA) hr
  have hDn : (↑mu : WithTop ℚ) ≤ J.Dn.1.orderTop := by
    exact orderTop_lower_of_unit_mul (A ^ 2 * r) J.Dn mu huAr hprod
  have hA2Dn : (↑mu : WithTop ℚ) ≤
      (A ^ 2 * J.Dn).1.orderTop := by
    simpa only [zero_add] using
      (mul_orderTop_lower (A ^ 2) J.Dn 0 mu (A ^ 2).2 hDn)
  have hnegL1 : (↑mu : WithTop ℚ) ≤ (-L1).1.orderTop := by
    change (↑mu : WithTop ℚ) ≤ (-L1.1).orderTop
    rw [HahnSeries.orderTop_neg]
    exact hL1
  have hQprod0 := add_orderTop_lower (A ^ 2 * J.Dn) (-L1) mu
    hA2Dn hnegL1
  have hQprod : (↑mu : WithTop ℚ) ≤ (2 * A * Qn).1.orderTop := by
    rw [show 2 * A * Qn = A ^ 2 * J.Dn + -L1 by
      dsimp only [L1]
      ring]
    exact hQprod0
  have hu2A : constantCoeff (2 * A) ≠ 0 := by
    simp only [map_mul, map_ofNat]
    exact mul_ne_zero (by norm_num) hA
  have hQn : (↑mu : WithTop ℚ) ≤ Qn.1.orderTop := by
    exact orderTop_lower_of_unit_mul (2 * A) Qn mu hu2A hQprod
  exact ⟨by simpa only [mu] using hDn, by simpa only [mu, Qn] using hQn⟩

/-- Once the two kernel remainders contain a second copy of the common
monomial, the coefficients of the first three rows at `2*mu` are exactly the
finite-dimensional second-correction system. -/
theorem doubleBlowup_quadratic_coefficients
    {k : Type*} [Field k] [CharZero k]
    (mu : ℚ) (hmu : 0 < mu)
    (A r d b q : GCD369CubeHahnRegular k) :
    let M := monomial mu hmu.le
    let D := M ^ 2 * d
    let B := M * b
    let C := M ^ 2 * q - M * r * b
    ((A ^ 2 * D - 2 * A * B * r - B ^ 2 - 2 * A * C).1.coeff
        (2 * mu) =
      constantCoeff A ^ 2 * constantCoeff d -
        2 * constantCoeff A * constantCoeff q - constantCoeff b ^ 2) ∧
    ((2 * A ^ 2 * r * D - 3 * A * B * r ^ 2 - 3 * A * C * r +
        3 * A * B * D - 3 * B * C).1.coeff (2 * mu) =
      2 * constantCoeff A ^ 2 * constantCoeff r * constantCoeff d -
        3 * constantCoeff A * constantCoeff r * constantCoeff q +
        3 * constantCoeff r * constantCoeff b ^ 2) ∧
    ((-2 * A ^ 2 * r ^ 2 * D + 6 * B ^ 2 * r ^ 2 +
        2 * A ^ 2 * D ^ 2 - 2 * B ^ 2 * D - 4 * A * C * D +
        3 * C ^ 2).1.coeff (2 * mu) =
      -2 * constantCoeff A ^ 2 * constantCoeff r ^ 2 * constantCoeff d +
        9 * constantCoeff r ^ 2 * constantCoeff b ^ 2) := by
  dsimp only
  let M : GCD369CubeHahnRegular k := monomial mu hmu.le
  let D : GCD369CubeHahnRegular k := M ^ 2 * d
  let B : GCD369CubeHahnRegular k := M * b
  let C : GCD369CubeHahnRegular k := M ^ 2 * q - M * r * b
  let R1 : GCD369CubeHahnRegular k :=
    A ^ 2 * D - 2 * A * B * r - B ^ 2 - 2 * A * C
  let R2 : GCD369CubeHahnRegular k :=
    2 * A ^ 2 * r * D - 3 * A * B * r ^ 2 - 3 * A * C * r +
      3 * A * B * D - 3 * B * C
  let R3 : GCD369CubeHahnRegular k :=
    -2 * A ^ 2 * r ^ 2 * D + 6 * B ^ 2 * r ^ 2 +
      2 * A ^ 2 * D ^ 2 - 2 * B ^ 2 * D - 4 * A * C * D + 3 * C ^ 2
  let K1 : GCD369CubeHahnRegular k := A ^ 2 * d - 2 * A * q - b ^ 2
  let K2 : GCD369CubeHahnRegular k :=
    2 * A ^ 2 * r * d - 3 * A * r * q + 3 * r * b ^ 2
  let E2 : GCD369CubeHahnRegular k := 3 * A * b * d - 3 * b * q
  let K3 : GCD369CubeHahnRegular k :=
    -2 * A ^ 2 * r ^ 2 * d + 9 * r ^ 2 * b ^ 2
  let E3 : GCD369CubeHahnRegular k :=
    4 * A * r * b * d - 6 * r * b * q +
      M * (2 * A ^ 2 * d ^ 2 - 2 * b ^ 2 * d - 4 * A * q * d + 3 * q ^ 2)
  have hfac1 : R1 = M ^ 2 * K1 := by
    dsimp only [R1, D, B, C, K1]
    ring
  have hfac2 : R2 = M ^ 2 * K2 + M ^ 3 * E2 := by
    dsimp only [R2, D, B, C, K2, E2]
    ring
  have hfac3 : R3 = M ^ 2 * K3 + M ^ 3 * E3 := by
    dsimp only [R3, D, B, C, K3, E3]
    ring
  have hc1 := congrArg
    (fun z : GCD369CubeHahnRegular k => z.1.coeff (2 * mu)) hfac1
  have hc2 := congrArg
    (fun z : GCD369CubeHahnRegular k => z.1.coeff (2 * mu)) hfac2
  have hc3 := congrArg
    (fun z : GCD369CubeHahnRegular k => z.1.coeff (2 * mu)) hfac3
  have hmain1 := coeff_monomial_pow_mul_at mu hmu 2 K1
  have hmain2 := coeff_monomial_pow_mul_at mu hmu 2 K2
  have hmain3 := coeff_monomial_pow_mul_at mu hmu 2 K3
  have hhigh2 := coeff_monomial_pow_mul_of_lt mu hmu 2 3 (by norm_num) E2
  have hhigh3 := coeff_monomial_pow_mul_of_lt mu hmu 2 3 (by norm_num) E3
  change (M ^ 2 * K1).1.coeff (2 * mu) = constantCoeff K1 at hmain1
  change (M ^ 2 * K2).1.coeff (2 * mu) = constantCoeff K2 at hmain2
  change (M ^ 2 * K3).1.coeff (2 * mu) = constantCoeff K3 at hmain3
  change (M ^ 3 * E2).1.coeff (2 * mu) = 0 at hhigh2
  change (M ^ 3 * E3).1.coeff (2 * mu) = 0 at hhigh3
  rw [hmain1] at hc1
  change R2.1.coeff (2 * mu) =
    (M ^ 2 * K2).1.coeff (2 * mu) + (M ^ 3 * E2).1.coeff (2 * mu) at hc2
  change R3.1.coeff (2 * mu) =
    (M ^ 2 * K3).1.coeff (2 * mu) + (M ^ 3 * E3).1.coeff (2 * mu) at hc3
  rw [hmain2, hhigh2, add_zero] at hc2
  rw [hmain3, hhigh3, add_zero] at hc3
  constructor
  · simpa only [R1, K1, D, B, C, M, map_sub, map_mul, map_pow, map_ofNat]
      using hc1
  constructor
  · simpa only [R2, K2, D, B, C, M, map_sub, map_add, map_mul, map_pow,
      map_ofNat] using hc2
  · simpa only [R3, K3, D, B, C, M, map_sub, map_add, map_mul, map_pow,
      map_ofNat, map_neg] using hc3

/-- If all three zero-load rows continue through twice the first deviation
scale, the residual leading direction is impossible.  This is the abstract
quadratic obstruction; a source wrapper supplies the row bounds and zero
coefficients below the first active load. -/
theorem doubleBlowup_quadratic_inconsistent
    {k : Type*} [Field k] [CharZero k]
    (A r D B C : GCD369CubeHahnRegular k)
    (J : TripleScale D B C)
    (hA : constantCoeff A ≠ 0) (hr : constantCoeff r ≠ 0)
    (hR1 : (↑(2 * J.mu) : WithTop ℚ) ≤
      (A ^ 2 * D - 2 * A * B * r - B ^ 2 - 2 * A * C).1.orderTop)
    (hR2 : (↑(2 * J.mu) : WithTop ℚ) ≤
      (2 * A ^ 2 * r * D - 3 * A * B * r ^ 2 - 3 * A * C * r +
        3 * A * B * D - 3 * B * C).1.orderTop)
    (hz1 : (A ^ 2 * D - 2 * A * B * r - B ^ 2 - 2 * A * C).1.coeff
      (2 * J.mu) = 0)
    (hz2 : (2 * A ^ 2 * r * D - 3 * A * B * r ^ 2 - 3 * A * C * r +
        3 * A * B * D - 3 * B * C).1.coeff (2 * J.mu) = 0)
    (hz3 : (-2 * A ^ 2 * r ^ 2 * D + 6 * B ^ 2 * r ^ 2 +
        2 * A ^ 2 * D ^ 2 - 2 * B ^ 2 * D - 4 * A * C * D +
        3 * C ^ 2).1.coeff (2 * J.mu) = 0) : False := by
  let mu : ℚ := J.mu
  let M : GCD369CubeHahnRegular k := monomial mu J.hmu.le
  let Qn : GCD369CubeHahnRegular k := J.Cn + r * J.Bn
  have hrem := doubleBlowup_kernelRemainders_order_lower
    A r D B C J hA hr hR1 hR2
  have hDn : (↑mu : WithTop ℚ) ≤ J.Dn.1.orderTop := by
    simpa only [mu] using hrem.1
  have hQn : (↑mu : WithTop ℚ) ≤ Qn.1.orderTop := by
    simpa only [mu, Qn] using hrem.2
  let d : GCD369CubeHahnRegular k := shift J.Dn mu hDn
  let q : GCD369CubeHahnRegular k := shift Qn mu hQn
  have hdfact : M * d = J.Dn := by
    simpa only [M, d] using monomial_mul_shift J.Dn mu J.hmu.le hDn
  have hqfact : M * q = Qn := by
    simpa only [M, q] using monomial_mul_shift Qn mu J.hmu.le hQn
  let Dq : GCD369CubeHahnRegular k := M ^ 2 * d
  let Bq : GCD369CubeHahnRegular k := M * J.Bn
  let Cq : GCD369CubeHahnRegular k := M ^ 2 * q - M * r * J.Bn
  have hDq : D = Dq := by
    calc
      D = M * J.Dn := by simpa only [M, mu] using J.hD
      _ = M * (M * d) := congrArg (fun z => M * z) hdfact.symm
      _ = Dq := by dsimp only [Dq]; ring
  have hBq : B = Bq := by
    simpa only [Bq, M, mu] using J.hB
  have hCn : J.Cn = M * q - r * J.Bn := by
    dsimp only [Qn] at hqfact
    linear_combination -hqfact
  have hCq : C = Cq := by
    calc
      C = M * J.Cn := by simpa only [M, mu] using J.hC
      _ = M * (M * q - r * J.Bn) := congrArg (fun z => M * z) hCn
      _ = Cq := by dsimp only [Cq]; ring
  let Row1 : GCD369CubeHahnRegular k → GCD369CubeHahnRegular k →
      GCD369CubeHahnRegular k → GCD369CubeHahnRegular k :=
    fun D' B' C' => A ^ 2 * D' - 2 * A * B' * r - B' ^ 2 - 2 * A * C'
  let Row2 : GCD369CubeHahnRegular k → GCD369CubeHahnRegular k →
      GCD369CubeHahnRegular k → GCD369CubeHahnRegular k :=
    fun D' B' C' =>
      2 * A ^ 2 * r * D' - 3 * A * B' * r ^ 2 - 3 * A * C' * r +
        3 * A * B' * D' - 3 * B' * C'
  let Row3 : GCD369CubeHahnRegular k → GCD369CubeHahnRegular k →
      GCD369CubeHahnRegular k → GCD369CubeHahnRegular k :=
    fun D' B' C' =>
      -2 * A ^ 2 * r ^ 2 * D' + 6 * B' ^ 2 * r ^ 2 +
        2 * A ^ 2 * D' ^ 2 - 2 * B' ^ 2 * D' - 4 * A * C' * D' +
        3 * C' ^ 2
  have hrow1 : Row1 D B C = Row1 Dq Bq Cq := by
    calc
      Row1 D B C = Row1 Dq B C := congrArg (fun z => Row1 z B C) hDq
      _ = Row1 Dq Bq C := congrArg (fun z => Row1 Dq z C) hBq
      _ = Row1 Dq Bq Cq := congrArg (Row1 Dq Bq) hCq
  have hrow2 : Row2 D B C = Row2 Dq Bq Cq := by
    calc
      Row2 D B C = Row2 Dq B C := congrArg (fun z => Row2 z B C) hDq
      _ = Row2 Dq Bq C := congrArg (fun z => Row2 Dq z C) hBq
      _ = Row2 Dq Bq Cq := congrArg (Row2 Dq Bq) hCq
  have hrow3 : Row3 D B C = Row3 Dq Bq Cq := by
    calc
      Row3 D B C = Row3 Dq B C := congrArg (fun z => Row3 z B C) hDq
      _ = Row3 Dq Bq C := congrArg (fun z => Row3 Dq z C) hBq
      _ = Row3 Dq Bq Cq := congrArg (Row3 Dq Bq) hCq
  have hz1q : (Row1 Dq Bq Cq).1.coeff (2 * mu) = 0 := by
    rw [← hrow1]
    simpa only [Row1, mu] using hz1
  have hz2q : (Row2 Dq Bq Cq).1.coeff (2 * mu) = 0 := by
    rw [← hrow2]
    simpa only [Row2, mu] using hz2
  have hz3q : (Row3 Dq Bq Cq).1.coeff (2 * mu) = 0 := by
    rw [← hrow3]
    simpa only [Row3, mu] using hz3
  have hc := doubleBlowup_quadratic_coefficients mu J.hmu A r d J.Bn q
  have hc' :
      (Row1 Dq Bq Cq).1.coeff (2 * mu) =
          constantCoeff A ^ 2 * constantCoeff d -
            2 * constantCoeff A * constantCoeff q -
              constantCoeff J.Bn ^ 2 ∧
      (Row2 Dq Bq Cq).1.coeff (2 * mu) =
          2 * constantCoeff A ^ 2 * constantCoeff r * constantCoeff d -
            3 * constantCoeff A * constantCoeff r * constantCoeff q +
              3 * constantCoeff r * constantCoeff J.Bn ^ 2 ∧
      (Row3 Dq Bq Cq).1.coeff (2 * mu) =
          -2 * constantCoeff A ^ 2 * constantCoeff r ^ 2 * constantCoeff d +
            9 * constantCoeff r ^ 2 * constantCoeff J.Bn ^ 2 := by
    simpa only [Row1, Row2, Row3, Dq, Bq, Cq, M] using hc
  let A0 : k := constantCoeff A
  let r0 : k := constantCoeff r
  let b0 : k := constantCoeff J.Bn
  let d0 : k := constantCoeff d
  let q0 : k := constantCoeff q
  have heq1 : A0 ^ 2 * d0 - 2 * A0 * q0 - b0 ^ 2 = 0 := by
    calc
      _ = (Row1 Dq Bq Cq).1.coeff (2 * mu) := by
        simpa only [A0, d0, q0, b0] using hc'.1.symm
      _ = 0 := hz1q
  have heq2 : 2 * A0 ^ 2 * r0 * d0 - 3 * A0 * r0 * q0 +
      3 * r0 * b0 ^ 2 = 0 := by
    calc
      _ = (Row2 Dq Bq Cq).1.coeff (2 * mu) := by
        simpa only [A0, r0, d0, q0, b0] using hc'.2.1.symm
      _ = 0 := hz2q
  have heq3 : -2 * A0 ^ 2 * r0 ^ 2 * d0 + 9 * r0 ^ 2 * b0 ^ 2 = 0 := by
    calc
      _ = (Row3 Dq Bq Cq).1.coeff (2 * mu) := by
        simpa only [A0, r0, d0, b0] using hc'.2.2.symm
      _ = 0 := hz3q
  have hr0 : r0 ≠ 0 := by simpa only [r0] using hr
  have hsecond := GCD369CubeDoubleBlowup_secondCorrection
    A0 b0 q0 r0 d0 hr0 heq1 heq2
  have hdres : constantCoeff J.Dn = 0 := by
    apply HahnSeries.coeff_eq_zero_of_lt_orderTop
    exact (WithTop.coe_lt_coe.mpr J.hmu).trans_le hDn
  have hqres : constantCoeff Qn = 0 := by
    change Qn.1.coeff 0 = 0
    apply HahnSeries.coeff_eq_zero_of_lt_orderTop
    exact (WithTop.coe_lt_coe.mpr J.hmu).trans_le hQn
  have hb0 : b0 ≠ 0 := by
    intro hb
    have hcres : constantCoeff J.Cn = 0 := by
      dsimp only [Qn] at hqres
      simp only [map_add, map_mul] at hqres
      dsimp only [b0, r0] at hb
      rw [hb, mul_zero, add_zero] at hqres
      exact hqres
    rcases J.hleading with h | h | h
    · exact h hdres
    · exact h (by simpa only [b0] using hb)
    · exact h hcres
  have hnonzero : (27 : k) * r0 ^ 2 * b0 ^ 2 ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hr0))
      (pow_ne_zero 2 hb0)
  apply hnonzero
  calc
    (27 : k) * r0 ^ 2 * b0 ^ 2 =
        -2 * A0 ^ 2 * r0 ^ 2 * d0 + 9 * r0 ^ 2 * b0 ^ 2 :=
      hsecond.1.symm
    _ = 0 := heq3

end GCD369CubeHahnRegular

namespace GCD369CubeHahnCommonValueData

/-- Below the first active load, the literal source equations make the first
three moving-root row coefficients vanish at every nonnegative residual
exponent `e < delta`.  The strict inequality removes the intrinsic cubic
term from the third Faber numerator. -/
theorem TransverseFactor.doubleRoot_rowCoeffs_zero_before_d
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (F : GCD369CubeHahnFaberPoleData k)
    (hscale : S.normal.sextic.scale = F.scale)
    (D0 C7 C5 C4 C3 C2 C1 Rho1 Rho2 Rho3 Rho4 : k)
    (hd : F.d = GCD369CubeHahnRegular.constant D0)
    (hc7 : F.c7 = GCD369CubeHahnRegular.constant C7)
    (hc5 : F.c5 = GCD369CubeHahnRegular.constant C5)
    (hc4 : F.c4 = GCD369CubeHahnRegular.constant C4)
    (hc3 : F.c3 = GCD369CubeHahnRegular.constant C3)
    (hc2 : F.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : F.c1 = GCD369CubeHahnRegular.constant C1)
    (hrho1 : F.rho1 = GCD369CubeHahnRegular.constant Rho1)
    (hrho2 : F.rho2 = GCD369CubeHahnRegular.constant Rho2)
    (hrho3 : F.rho3 = GCD369CubeHahnRegular.constant Rho3)
    (hrho4 : F.rho4 = GCD369CubeHahnRegular.constant Rho4)
    (r : GCD369CubeHahnRegular k)
    (hroot : 2 * S.cubicU * r + 3 * S.cubicV = 0)
    (e : ℚ) (he : 0 ≤ e) (heDelta : e < T.delta)
    (hearly : 2 * T.delta + e < F.scale.p) :
    let A := T.Xn
    let D := S.cubicU + 3 * r ^ 2
    let B := T.Yn - r * A
    let C := T.Zn + 2 * r ^ 2 * A
    ((A ^ 2 * D - 2 * A * B * r - B ^ 2 - 2 * A * C).1.coeff e = 0) ∧
    ((2 * A ^ 2 * r * D - 3 * A * B * r ^ 2 - 3 * A * C * r +
        3 * A * B * D - 3 * B * C).1.coeff e = 0) ∧
    ((-2 * A ^ 2 * r ^ 2 * D + 6 * B ^ 2 * r ^ 2 +
        2 * A ^ 2 * D ^ 2 - 2 * B ^ 2 * D - 4 * A * C * D +
        3 * C ^ 2).1.coeff e = 0) := by
  dsimp only
  let A : GCD369CubeHahnRegular k := T.Xn
  let D : GCD369CubeHahnRegular k := S.cubicU + 3 * r ^ 2
  let B : GCD369CubeHahnRegular k := T.Yn - r * A
  let C : GCD369CubeHahnRegular k := T.Zn + 2 * r ^ 2 * A
  let H : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
  let R1 : GCD369CubeHahnRegular k :=
    A ^ 2 * D - 2 * A * B * r - B ^ 2 - 2 * A * C
  let R2 : GCD369CubeHahnRegular k :=
    2 * A ^ 2 * r * D - 3 * A * B * r ^ 2 - 3 * A * C * r +
      3 * A * B * D - 3 * B * C
  let R3 : GCD369CubeHahnRegular k :=
    -2 * A ^ 2 * r ^ 2 * D + 6 * B ^ 2 * r ^ 2 +
      2 * A ^ 2 * D ^ 2 - 2 * B ^ 2 * D - 4 * A * C * D + 3 * C ^ 2
  let N1 : GCD369CubeHahnRegular k :=
    GCD369CubeFaberN1
      S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
      S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
      S.normal.sextic.scale.regular4
  let N2 : GCD369CubeHahnRegular k :=
    GCD369CubeFaberN2
      S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
      S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
      S.normal.sextic.scale.regular4
  let N3 : GCD369CubeHahnRegular k :=
    GCD369CubeFaberN3
      S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
      S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
      S.normal.sextic.scale.regular4
  have hz := F.zeroHighNCoeff_zero_before_d
    D0 C7 C5 C4 C3 C2 C1 Rho1 Rho2 Rho3 Rho4
    hd hc7 hc5 hc4 hc3 hc2 hc1 hrho1 hrho2 hrho3 hrho4
    (2 * T.delta + e) (by nlinarith [T.hdelta]) hearly
  rw [← hscale] at hz
  have hexp := T.doubleRoot_zeroHigh_expansions r hroot
  have hexp1 : 729 * N1 = (-32 * (729 * R1)) * H ^ 2 := by
    simpa only [N1, R1, A, D, B, C, H] using hexp.1
  have hexp2 : 2187 * N2 = (32 * (-1458 * R2)) * H ^ 2 := by
    simpa only [N2, R2, A, D, B, C, H] using hexp.2.1
  have hexp3 : N3 = (128 * R3) * H ^ 2 - (64 * A ^ 3) * H ^ 3 := by
    simpa only [N3, R3, A, D, B, C, H] using hexp.2.2.1
  have hshift1 := GCD369CubeHahnRegular.coeff_mul_monomial_pow_add
    (-32 * (729 * R1)) T.delta e T.hdelta.le 2
  have hshift2 := GCD369CubeHahnRegular.coeff_mul_monomial_pow_add
    (32 * (-1458 * R2)) T.delta e T.hdelta.le 2
  have hshift3 := GCD369CubeHahnRegular.coeff_mul_monomial_pow_add
    (128 * R3) T.delta e T.hdelta.le 2
  change ((-32 * (729 * R1)) * H ^ 2).1.coeff
      (e + (2 : ℚ) * T.delta) = (-32 * (729 * R1)).1.coeff e at hshift1
  change ((32 * (-1458 * R2)) * H ^ 2).1.coeff
      (e + (2 : ℚ) * T.delta) = (32 * (-1458 * R2)).1.coeff e at hshift2
  change ((128 * R3) * H ^ 2).1.coeff
      (e + (2 : ℚ) * T.delta) = (128 * R3).1.coeff e at hshift3
  have hc1 := congrArg
    (fun z : GCD369CubeHahnRegular k => z.1.coeff (2 * T.delta + e)) hexp1
  have hc2 := congrArg
    (fun z : GCD369CubeHahnRegular k => z.1.coeff (2 * T.delta + e)) hexp2
  have hc3 := congrArg
    (fun z : GCD369CubeHahnRegular k => z.1.coeff (2 * T.delta + e)) hexp3
  rw [show 2 * T.delta + e = e + (2 : ℚ) * T.delta by ring,
    hshift1] at hc1
  rw [show 2 * T.delta + e = e + (2 : ℚ) * T.delta by ring,
    hshift2] at hc2
  have hcubicShift := GCD369CubeHahnRegular.coeff_mul_monomial_pow_add
    (64 * A ^ 3) T.delta (e - T.delta) T.hdelta.le 3
  change ((64 * A ^ 3) * H ^ 3).1.coeff
      ((e - T.delta) + (3 : ℚ) * T.delta) =
        (64 * A ^ 3).1.coeff (e - T.delta) at hcubicShift
  have hcubicZero : (64 * A ^ 3).1.coeff (e - T.delta) = 0 := by
    exact GCD369CubeHahnRegular.coeff_eq_zero_of_neg (64 * A ^ 3)
      (sub_neg.mpr heDelta)
  change N3.1.coeff (2 * T.delta + e) =
    ((128 * R3) * H ^ 2).1.coeff (2 * T.delta + e) -
      ((64 * A ^ 3) * H ^ 3).1.coeff (2 * T.delta + e) at hc3
  rw [show 2 * T.delta + e = e + (2 : ℚ) * T.delta by ring,
    hshift3] at hc3
  rw [show e + (2 : ℚ) * T.delta =
      (e - T.delta) + (3 : ℚ) * T.delta by ring,
    hcubicShift, hcubicZero, sub_zero] at hc3
  have hz1scaled : (-32 * (729 * R1)).1.coeff e = 0 := by
    calc
      _ = (729 * N1).1.coeff (e + 2 * T.delta) := hc1.symm
      _ = (729 * N1).1.coeff (2 * T.delta + e) := by
        rw [show e + 2 * T.delta = 2 * T.delta + e by ring]
      _ = 0 := by simpa only [N1] using hz.1
  have hz2scaled : (32 * (-1458 * R2)).1.coeff e = 0 := by
    calc
      _ = (2187 * N2).1.coeff (e + 2 * T.delta) := hc2.symm
      _ = (2187 * N2).1.coeff (2 * T.delta + e) := by
        rw [show e + 2 * T.delta = 2 * T.delta + e by ring]
      _ = 0 := by simpa only [N2] using hz.2.1
  have hz3N : N3.1.coeff (2 * T.delta + e) = 0 := by
    have hnat : (243 * N3).1.coeff (2 * T.delta + e) =
        (243 : k) * N3.1.coeff (2 * T.delta + e) :=
      GCD369CubeHahnRegular.coeff_nat_mul 243 N3 (2 * T.delta + e)
    have hscaled : (243 * N3).1.coeff (2 * T.delta + e) = 0 := by
      simpa only [N3] using hz.2.2.1
    rw [hnat] at hscaled
    exact (mul_eq_zero.mp hscaled).resolve_left (by norm_num)
  have hz3scaled : (128 * R3).1.coeff e = 0 := by
    calc
      _ = N3.1.coeff (e - T.delta + 3 * T.delta) := hc3.symm
      _ = N3.1.coeff (2 * T.delta + e) := by
        rw [show e - T.delta + 3 * T.delta = 2 * T.delta + e by ring]
      _ = 0 := hz3N
  have hscalar1 : -32 * (729 * R1) = (-23328 : ℤ) * R1 := by
    ring
  have hscalar2 : 32 * (-1458 * R2) = (-46656 : ℤ) * R2 := by
    ring
  rw [hscalar1, GCD369CubeHahnRegular.coeff_int_mul] at hz1scaled
  rw [hscalar2, GCD369CubeHahnRegular.coeff_int_mul] at hz2scaled
  have hcoeff128 : (128 * R3).1.coeff e = (128 : k) * R3.1.coeff e :=
    GCD369CubeHahnRegular.coeff_nat_mul 128 R3 e
  rw [hcoeff128] at hz3scaled
  have hR1zero : R1.1.coeff e = 0 :=
    (mul_eq_zero.mp hz1scaled).resolve_left (by norm_num)
  have hR2zero : R2.1.coeff e = 0 :=
    (mul_eq_zero.mp hz2scaled).resolve_left (by norm_num)
  have hR3zero : R3.1.coeff e = 0 :=
    (mul_eq_zero.mp hz3scaled).resolve_left (by norm_num)
  exact ⟨by simpa only [R1, A, D, B, C] using hR1zero,
    by simpa only [R2, A, D, B, C] using hR2zero,
    by simpa only [R3, A, D, B, C] using hR3zero⟩

/-- In the balanced branch `p = 3*delta`, the first nonzero common moving-
root deviation cannot occur before the half scale. -/
theorem TransverseFactor.doubleRoot_firstCommonScale_not_below_half
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (F : GCD369CubeHahnFaberPoleData k)
    (hscale : S.normal.sextic.scale = F.scale)
    (D0 C7 C5 C4 C3 C2 C1 Rho1 Rho2 Rho3 Rho4 : k)
    (hd : F.d = GCD369CubeHahnRegular.constant D0)
    (hc7 : F.c7 = GCD369CubeHahnRegular.constant C7)
    (hc5 : F.c5 = GCD369CubeHahnRegular.constant C5)
    (hc4 : F.c4 = GCD369CubeHahnRegular.constant C4)
    (hc3 : F.c3 = GCD369CubeHahnRegular.constant C3)
    (hc2 : F.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : F.c1 = GCD369CubeHahnRegular.constant C1)
    (hrho1 : F.rho1 = GCD369CubeHahnRegular.constant Rho1)
    (hrho2 : F.rho2 = GCD369CubeHahnRegular.constant Rho2)
    (hrho3 : F.rho3 = GCD369CubeHahnRegular.constant Rho3)
    (hrho4 : F.rho4 = GCD369CubeHahnRegular.constant Rho4)
    (hp : F.scale.p = 3 * T.delta)
    (r : GCD369CubeHahnRegular k)
    (hA : GCD369CubeHahnRegular.constantCoeff T.Xn ≠ 0)
    (hr : GCD369CubeHahnRegular.constantCoeff r ≠ 0)
    (hroot : 2 * S.cubicU * r + 3 * S.cubicV = 0)
    (J : GCD369CubeHahnRegular.TripleScale
      (S.cubicU + 3 * r ^ 2)
      (T.Yn - r * T.Xn)
      (T.Zn + 2 * r ^ 2 * T.Xn)) :
    ¬ J.mu < T.delta / 2 := by
  intro hsmall
  let A : GCD369CubeHahnRegular k := T.Xn
  let D : GCD369CubeHahnRegular k := S.cubicU + 3 * r ^ 2
  let B : GCD369CubeHahnRegular k := T.Yn - r * A
  let C : GCD369CubeHahnRegular k := T.Zn + 2 * r ^ 2 * A
  change GCD369CubeHahnRegular.TripleScale D B C at J
  let Row1 : GCD369CubeHahnRegular k :=
    A ^ 2 * D - 2 * A * B * r - B ^ 2 - 2 * A * C
  let Row2 : GCD369CubeHahnRegular k :=
    2 * A ^ 2 * r * D - 3 * A * B * r ^ 2 - 3 * A * C * r +
      3 * A * B * D - 3 * B * C
  let Row3 : GCD369CubeHahnRegular k :=
    -2 * A ^ 2 * r ^ 2 * D + 6 * B ^ 2 * r ^ 2 +
      2 * A ^ 2 * D ^ 2 - 2 * B ^ 2 * D - 4 * A * C * D + 3 * C ^ 2
  have htwoMuDelta : 2 * J.mu < T.delta := by nlinarith
  have hR1 : (↑(2 * J.mu) : WithTop ℚ) ≤ Row1.1.orderTop := by
    rw [HahnSeries.le_orderTop_iff_forall]
    intro q hq
    have hq' : q < 2 * J.mu := WithTop.coe_lt_coe.mp hq
    by_cases hq0 : 0 ≤ q
    · have hrows := T.doubleRoot_rowCoeffs_zero_before_d F hscale
        D0 C7 C5 C4 C3 C2 C1 Rho1 Rho2 Rho3 Rho4
        hd hc7 hc5 hc4 hc3 hc2 hc1 hrho1 hrho2 hrho3 hrho4
        r hroot q hq0 (by linarith)
        (by rw [hp]; linarith)
      simpa only [Row1, A, D, B, C] using hrows.1
    · exact GCD369CubeHahnRegular.coeff_eq_zero_of_neg Row1
        (lt_of_not_ge hq0)
  have hR2 : (↑(2 * J.mu) : WithTop ℚ) ≤ Row2.1.orderTop := by
    rw [HahnSeries.le_orderTop_iff_forall]
    intro q hq
    have hq' : q < 2 * J.mu := WithTop.coe_lt_coe.mp hq
    by_cases hq0 : 0 ≤ q
    · have hrows := T.doubleRoot_rowCoeffs_zero_before_d F hscale
        D0 C7 C5 C4 C3 C2 C1 Rho1 Rho2 Rho3 Rho4
        hd hc7 hc5 hc4 hc3 hc2 hc1 hrho1 hrho2 hrho3 hrho4
        r hroot q hq0 (by linarith)
        (by rw [hp]; linarith)
      simpa only [Row2, A, D, B, C] using hrows.2.1
    · exact GCD369CubeHahnRegular.coeff_eq_zero_of_neg Row2
        (lt_of_not_ge hq0)
  have hrows2 := T.doubleRoot_rowCoeffs_zero_before_d F hscale
    D0 C7 C5 C4 C3 C2 C1 Rho1 Rho2 Rho3 Rho4
    hd hc7 hc5 hc4 hc3 hc2 hc1 hrho1 hrho2 hrho3 hrho4
    r hroot (2 * J.mu) (by linarith [J.hmu]) htwoMuDelta
    (by rw [hp]; linarith)
  have hz1 : Row1.1.coeff (2 * J.mu) = 0 := by
    simpa only [Row1, A, D, B, C] using hrows2.1
  have hz2 : Row2.1.coeff (2 * J.mu) = 0 := by
    simpa only [Row2, A, D, B, C] using hrows2.2.1
  have hz3 : Row3.1.coeff (2 * J.mu) = 0 := by
    simpa only [Row3, A, D, B, C] using hrows2.2.2
  exact GCD369CubeHahnRegular.doubleBlowup_quadratic_inconsistent
    A r D B C J (by simpa only [A] using hA) hr
    (by simpa only [Row1] using hR1) (by simpa only [Row2] using hR2)
    (by simpa only [Row1] using hz1) (by simpa only [Row2] using hz2)
    (by simpa only [Row3] using hz3)

end GCD369CubeHahnCommonValueData

#print axioms GCD369CubeHahnRegular.coeff_int_mul
#print axioms GCD369CubeHahnRegular.orderTop_lower_of_unit_mul
#print axioms GCD369CubeHahnRegular.orderTop_lower_of_monomial_mul_orderTop_lower
#print axioms GCD369CubeHahnRegular.monomial_sq_mul_orderTop_lower
#print axioms GCD369CubeHahnRegular.doubleBlowup_kernelRemainders_order_lower
#print axioms GCD369CubeHahnRegular.doubleBlowup_quadratic_coefficients
#print axioms GCD369CubeHahnRegular.doubleBlowup_quadratic_inconsistent
#print axioms GCD369CubeHahnCommonValueData.TransverseFactor.doubleRoot_rowCoeffs_zero_before_d
#print axioms GCD369CubeHahnCommonValueData.TransverseFactor.doubleRoot_firstCommonScale_not_below_half
