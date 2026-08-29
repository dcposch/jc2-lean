import LowScale68ScaleTwoSourceFace

/-! # Aligned scale-two source face for the normalized `(6,8)` leaf

The nonzero seventh-power face is closed by
`LowScale68ScaleTwoAfterRhoOneAfterP3Closure`.  The remaining chamber is
the aligned discriminator `N = 4 p₅ H - 3 q₇ = 0`.  This file extracts the
next Keller coefficient (degree `11`) and proves that, on that face, the
cleared defect

`M = 9 q₆ H² - 12 p₄ H³ - 2 p₅²`

satisfies `M = C κ * H⁵`.  Consequently `H ∣ p₅` and `H² ∣ q₇`.  No
polynomial square root of `H` is assumed, and no total-degree or
twice-prime theorem is used.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

/-! ## Literal next Keller coefficient -/

/-- The second row below the leading weighted-Wronskian row for outer
degrees `(6,8)`.  It is the source of the first aligned sextic/octic
defect after the septic discriminator. -/
theorem secondCoefficientJacobianRow_68 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 6).derivative * (q.coeff 6 * Polynomial.C (6 : K)) +
        (p.coeff 5).derivative * (q.coeff 7 * Polynomial.C (7 : K)) +
        (p.coeff 4).derivative * (q.coeff 8 * Polynomial.C (8 : K)) -
      ((p.coeff 6 * Polynomial.C (6 : K)) * (q.coeff 6).derivative +
        (p.coeff 5 * Polynomial.C (5 : K)) * (q.coeff 7).derivative +
        (p.coeff 4 * Polynomial.C (4 : K)) * (q.coeff 8).derivative) = 0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 11) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (11 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 11 :
      Finset (ℕ × ℕ)) =
      ({(0, 11), (1, 10), (2, 9), (3, 8), (4, 7), (5, 6), (6, 5),
        (7, 4), (8, 3), (9, 2), (10, 1), (11, 0)} :
        Finset (ℕ × ℕ)) := by decide
  rw [hanti] at hcoeff
  norm_num [hp, hq, Polynomial.coeff_eq_zero_of_natDegree_lt] at hcoeff ⊢
  have hC6 : Polynomial.C (6 : K) = (6 : K[X]) :=
    Polynomial.C_eq_natCast 6
  have hC7 : Polynomial.C (7 : K) = (7 : K[X]) :=
    Polynomial.C_eq_natCast 7
  have hC8 : Polynomial.C (8 : K) = (8 : K[X]) :=
    Polynomial.C_eq_natCast 8
  have hC5 : Polynomial.C (5 : K) = (5 : K[X]) :=
    Polynomial.C_eq_natCast 5
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) :=
    Polynomial.C_eq_natCast 4
  rw [hC6, hC7, hC8, hC5, hC4]
  linear_combination hcoeff

/-! ## Aligned cleared defect -/

/-- Polynomial numerator of `9 H⁵ (P - (4/3) A)` after a square-core
affine depression.  On the aligned face it is an actual polynomial first
integral, with no square root of `H` required. -/
def alignedSecondDefect68 {K : Type*} [CommRing K]
    (H a4 a5 b6 : K[X]) : K[X] :=
  (9 : K[X]) * b6 * H ^ 2 - (12 : K[X]) * a4 * H ^ 3 - (2 : K[X]) * a5 ^ 2

theorem C_ofNat_poly {K : Type*} [Semiring K] {n : ℕ} [n.AtLeastTwo] :
    Polynomial.C (OfNat.ofNat n : K) = (OfNat.ofNat n : K[X]) :=
  map_ofNat _ n

set_option maxHeartbeats 8000000 in
/-- Exact combination of the degree-11 Jacobian expression with the
weighted derivative of `M`.  The right-hand side vanishes on `N = 0`. -/
theorem alignedSecondDefect_weightedDerivative_identity {K : Type*}
    [Field K] [CharZero K] (H a4 a5 b6 b7 : K[X]) :
    (2 : K[X]) *
        (H * (alignedSecondDefect68 H a4 a5 b6).derivative -
          (5 : K[X]) * alignedSecondDefect68 H a4 a5 b6 * H.derivative) +
      (3 : K[X]) *
        ((H ^ 3).derivative * (b6 * (6 : K[X])) +
          a5.derivative * (b7 * (7 : K[X])) +
          a4.derivative * (H ^ 4 * (8 : K[X])) -
        ((H ^ 3 * (6 : K[X])) * b6.derivative +
          (a5 * (5 : K[X])) * b7.derivative +
          (a4 * (4 : K[X])) * (H ^ 4).derivative)) =
      (7 : K[X]) * a5.derivative *
          ((3 : K[X]) * b7 - (4 : K[X]) * a5 * H) -
        (5 : K[X]) * a5 *
          ((3 : K[X]) * b7.derivative -
            ((4 : K[X]) * a5.derivative * H +
              (4 : K[X]) * a5 * H.derivative)) := by
  simp only [alignedSecondDefect68, Polynomial.derivative_sub,
    Polynomial.derivative_mul, Polynomial.derivative_pow,
    Polynomial.derivative_ofNat, nsmul_eq_mul, zero_mul, zero_add]
  apply Polynomial.funext
  intro x
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_natCast,
    Polynomial.eval_ofNat]
  ring

/-- On the aligned face, the degree-`11` row is the weighted derivative
`H M' - 5 M H' = 0`. -/
theorem alignedSecondDefectRow_eq_zero_68 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]}
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (_hH : H ≠ 0)
    (hp6 : p.coeff 6 = H ^ 3) (hq8 : q.coeff 8 = H ^ 4)
    (haligned :
      (4 : K[X]) * p.coeff 5 * H - (3 : K[X]) * q.coeff 7 = 0) :
    H * (alignedSecondDefect68 H (p.coeff 4) (p.coeff 5) (q.coeff 6)).derivative -
      (5 : K[X]) *
        alignedSecondDefect68 H (p.coeff 4) (p.coeff 5) (q.coeff 6) *
          H.derivative = 0 := by
  have hrow := secondCoefficientJacobianRow_68 hp hq hjac
  rw [hp6, hq8] at hrow
  have hC6 : Polynomial.C (6 : K) = (6 : K[X]) := C_ofNat_poly
  have hC7 : Polynomial.C (7 : K) = (7 : K[X]) := C_ofNat_poly
  have hC8 : Polynomial.C (8 : K) = (8 : K[X]) := C_ofNat_poly
  have hC5 : Polynomial.C (5 : K) = (5 : K[X]) := C_ofNat_poly
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) := C_ofNat_poly
  rw [hC6, hC7, hC8, hC5, hC4] at hrow
  have hN :
      (3 : K[X]) * q.coeff 7 - (4 : K[X]) * p.coeff 5 * H = 0 := by
    linear_combination -haligned
  have hN' :
      (3 : K[X]) * (q.coeff 7).derivative -
        ((4 : K[X]) * (p.coeff 5).derivative * H +
          (4 : K[X]) * p.coeff 5 * H.derivative) = 0 := by
    have hder := congrArg derivative hN
    simpa [Polynomial.derivative_sub, Polynomial.derivative_mul,
      Polynomial.derivative_ofNat, zero_mul, zero_add] using hder
  have hid := alignedSecondDefect_weightedDerivative_identity
    H (p.coeff 4) (p.coeff 5) (q.coeff 6) (q.coeff 7)
  simp only [hrow, hN, hN', mul_zero, sub_zero, add_zero] at hid
  have h2 : (2 : K[X]) ≠ 0 := by
    rw [← C_ofNat_poly]
    exact Polynomial.C_ne_zero.mpr (by norm_num)
  exact (mul_eq_zero.mp hid).resolve_left h2

/-- Polynomial first integral of the aligned `(6,8)` second defect. -/
theorem alignedSecondDefectPowerRelation_68 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]}
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hH : H ≠ 0)
    (hp6 : p.coeff 6 = H ^ 3) (hq8 : q.coeff 8 = H ^ 4)
    (haligned :
      (4 : K[X]) * p.coeff 5 * H - (3 : K[X]) * q.coeff 7 = 0) :
    ∃ κ : K,
      alignedSecondDefect68 H (p.coeff 4) (p.coeff 5) (q.coeff 6) =
        Polynomial.C κ * H ^ 5 := by
  let M : K[X] :=
    alignedSecondDefect68 H (p.coeff 4) (p.coeff 5) (q.coeff 6)
  have hrow :
      H * M.derivative - (5 : K[X]) * M * H.derivative = 0 := by
    simpa only [M] using
      alignedSecondDefectRow_eq_zero_68 hp hq hjac hH hp6 hq8 haligned
  have hC5 : Polynomial.C (5 : K) = (5 : K[X]) := C_ofNat_poly
  have hW : Polynomial.wronskian M (H ^ 5) = 0 := by
    rw [Polynomial.wronskian, Polynomial.derivative_pow]
    calc
      M * (Polynomial.C (5 : K) * H ^ (5 - 1) * H.derivative) -
          M.derivative * H ^ 5 =
          H ^ 4 *
            (Polynomial.C (5 : K) * M * H.derivative -
              H * M.derivative) := by
                ring
      _ = 0 := by
        rw [hC5]
        have hfac :
            (5 : K[X]) * M * H.derivative - H * M.derivative = 0 := by
          linear_combination -hrow
        rw [hfac, mul_zero]
  exact eq_C_mul_of_wronskian_eq_zero (pow_ne_zero 5 hH) hW

/-- Square divisibility in `K[X]`. -/
theorem dvd_of_sq_dvd_sq_poly {K : Type*} [Field K] {d f : K[X]}
    (h : d ^ 2 ∣ f ^ 2) : d ∣ f := by
  classical
  letI := EuclideanDomain.gcdMonoid K[X]
  by_cases hf : f = 0
  · simp [hf]
  let g := gcd d f
  let d' := d / g
  let f' := f / g
  have hg : g ≠ 0 := gcd_ne_zero_of_right hf
  have hd : g * d' = d :=
    EuclideanDomain.mul_div_cancel' hg (gcd_dvd_left d f)
  have hf' : g * f' = f :=
    EuclideanDomain.mul_div_cancel' hg (gcd_dvd_right d f)
  have hcop : IsCoprime d' f' := isCoprime_div_gcd_div_gcd hf
  obtain ⟨s, hs⟩ := h
  have hred : d' ^ 2 * s * g ^ 2 = f' ^ 2 * g ^ 2 := by
    calc
      d' ^ 2 * s * g ^ 2 = (g * d') ^ 2 * s := by ring
      _ = d ^ 2 * s := by rw [hd]
      _ = f ^ 2 := hs.symm
      _ = (g * f') ^ 2 := by rw [hf']
      _ = f' ^ 2 * g ^ 2 := by ring
  have hsq : d' ^ 2 * s = f' ^ 2 :=
    mul_right_cancel₀ (pow_ne_zero 2 hg) hred
  have hd'f' : d' ∣ f' ^ 2 := ⟨d' * s, by rw [← hsq]; ring⟩
  have hd'unit : IsUnit d' :=
    isUnit_of_dvd_one
      (hcop.pow_right.dvd_of_dvd_mul_right (by simpa using hd'f'))
  obtain ⟨u, hu⟩ := isUnit_iff_exists_inv.mp hd'unit
  refine ⟨f' * u, ?_⟩
  calc
    f = g * f' := hf'.symm
    _ = g * (d' * u) * f' := by rw [hu, mul_one]
    _ = (g * d') * (f' * u) := by ring
    _ = d * (f' * u) := by rw [hd]

/-- The aligned second defect forces `H` to divide `p₅`. -/
theorem alignedSecondDefect_dvd_p5_68 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]}
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hH : H ≠ 0)
    (hp6 : p.coeff 6 = H ^ 3) (hq8 : q.coeff 8 = H ^ 4)
    (haligned :
      (4 : K[X]) * p.coeff 5 * H - (3 : K[X]) * q.coeff 7 = 0) :
    H ∣ p.coeff 5 := by
  obtain ⟨κ, hM⟩ :=
    alignedSecondDefectPowerRelation_68 hp hq hjac hH hp6 hq8 haligned
  have hsq :
      (2 : K[X]) * (p.coeff 5) ^ 2 =
        H ^ 2 *
          ((9 : K[X]) * q.coeff 6 - (12 : K[X]) * p.coeff 4 * H -
            Polynomial.C κ * H ^ 3) := by
    have hM' :
        (9 : K[X]) * q.coeff 6 * H ^ 2 -
            (12 : K[X]) * p.coeff 4 * H ^ 3 -
            (2 : K[X]) * (p.coeff 5) ^ 2 =
          Polynomial.C κ * H ^ 5 := by
      simpa [alignedSecondDefect68] using hM
    linear_combination -hM'
  have h2ne : (2 : K[X]) ≠ 0 := by
    rw [← C_ofNat_poly]
    exact Polynomial.C_ne_zero.mpr (by norm_num)
  have hcancel :
      (p.coeff 5) ^ 2 =
        H ^ 2 *
          (Polynomial.C (2⁻¹ : K) *
            ((9 : K[X]) * q.coeff 6 - (12 : K[X]) * p.coeff 4 * H -
              Polynomial.C κ * H ^ 3)) := by
    apply mul_left_cancel₀ h2ne
    have h2inv : (2 : K[X]) * Polynomial.C (2⁻¹ : K) = 1 := by
      rw [← C_ofNat_poly, ← Polynomial.C_mul]
      norm_num
    calc
      (2 : K[X]) * (p.coeff 5) ^ 2 =
          H ^ 2 *
            ((9 : K[X]) * q.coeff 6 - (12 : K[X]) * p.coeff 4 * H -
              Polynomial.C κ * H ^ 3) := hsq
      _ = H ^ 2 *
            (((2 : K[X]) * Polynomial.C (2⁻¹ : K)) *
              ((9 : K[X]) * q.coeff 6 - (12 : K[X]) * p.coeff 4 * H -
                Polynomial.C κ * H ^ 3)) := by
                  rw [h2inv, one_mul]
      _ = (2 : K[X]) *
            (H ^ 2 *
              (Polynomial.C (2⁻¹ : K) *
                ((9 : K[X]) * q.coeff 6 - (12 : K[X]) * p.coeff 4 * H -
                  Polynomial.C κ * H ^ 3))) := by
                    ring
  have hdiv : H ^ 2 ∣ (p.coeff 5) ^ 2 := ⟨_, hcancel⟩
  exact dvd_of_sq_dvd_sq_poly hdiv

/-- On the aligned face the first-face relation already gives `H ∣ q₇`;
the second defect upgrades this to `H² ∣ q₇`. -/
theorem alignedSecondDefect_pow_dvd_q7_68 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]}
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hH : H ≠ 0)
    (hp6 : p.coeff 6 = H ^ 3) (hq8 : q.coeff 8 = H ^ 4)
    (haligned :
      (4 : K[X]) * p.coeff 5 * H - (3 : K[X]) * q.coeff 7 = 0) :
    H ^ 2 ∣ q.coeff 7 := by
  obtain ⟨g, hg⟩ :=
    alignedSecondDefect_dvd_p5_68 hp hq hjac hH hp6 hq8 haligned
  have h3eq :
      (3 : K[X]) * q.coeff 7 = (4 : K[X]) * g * H ^ 2 := by
    have hN : (3 : K[X]) * q.coeff 7 = (4 : K[X]) * p.coeff 5 * H := by
      linear_combination -haligned
    calc
      (3 : K[X]) * q.coeff 7 = (4 : K[X]) * p.coeff 5 * H := hN
      _ = (4 : K[X]) * (H * g) * H := by rw [hg]
      _ = (4 : K[X]) * g * H ^ 2 := by ring
  have h3ne : (3 : K[X]) ≠ 0 := by
    rw [← C_ofNat_poly]
    exact Polynomial.C_ne_zero.mpr (by norm_num)
  have h3inv : (3 : K[X]) * Polynomial.C (3⁻¹ : K) = 1 := by
    rw [← C_ofNat_poly, ← Polynomial.C_mul]
    norm_num
  refine ⟨Polynomial.C (3⁻¹ : K) * ((4 : K[X]) * g), ?_⟩
  apply mul_left_cancel₀ h3ne
  calc
    (3 : K[X]) * q.coeff 7 = (4 : K[X]) * g * H ^ 2 := h3eq
    _ = ((3 : K[X]) * Polynomial.C (3⁻¹ : K)) * ((4 : K[X]) * g) * H ^ 2 := by
          rw [h3inv, one_mul]
    _ = (3 : K[X]) * (H ^ 2 * (Polynomial.C (3⁻¹ : K) * ((4 : K[X]) * g))) := by
          ring

/-! ## Source-facing aligned packet -/

/-- Source-facing fifth-power integral on a normalized aligned `(6,8)`
scale-two source. -/
theorem normalized68ScaleTwo_alignedFace_secondDefectPowerRelation
    {K : Type*} [Field K] [CharZero K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized68LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (4 : K[X]) * p.coeff 5 * H - (3 : K[X]) * q.coeff 7 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ κ : K,
      alignedSecondDefect68 H (p.coeff 4) (p.coeff 5) (q.coeff 6) =
        Polynomial.C κ * H ^ 5 := by
  dsimp only at haligned ⊢
  rcases hsource with
    ⟨hH, _hHdegree, hPdegree, hQdegree, hp6, hq8, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 6 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 8 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  exact alignedSecondDefectPowerRelation_68 hp hq hjac hH
    (by simpa only [p] using hp6) (by simpa only [q] using hq8) haligned

/-- Exact finite residual packet of a normalized aligned scale-two
`(6,8)` source: `p₅ = g H`, `q₇ = (4/3) g H²`, and `M = κ H⁵`. -/
theorem normalized68ScaleTwo_alignedFace_packet
    {K : Type*} [Field K] [CharZero K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized68LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (4 : K[X]) * p.coeff 5 * H - (3 : K[X]) * q.coeff 7 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (κ : K) (g : K[X]),
      p.coeff 5 = H * g ∧
        q.coeff 7 = Polynomial.C (4 / 3 : K) * g * H ^ 2 ∧
          alignedSecondDefect68 H (p.coeff 4) (p.coeff 5) (q.coeff 6) =
            Polynomial.C κ * H ^ 5 := by
  dsimp only at haligned ⊢
  rcases hsource with
    ⟨hH, _hHdegree, hPdegree, hQdegree, hp6, hq8, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 6 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 8 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hp6' : p.coeff 6 = H ^ 3 := by simpa only [p] using hp6
  have hq8' : q.coeff 8 = H ^ 4 := by simpa only [q] using hq8
  obtain ⟨κ, hM⟩ :=
    alignedSecondDefectPowerRelation_68 hp hq hjac hH hp6' hq8' haligned
  obtain ⟨g, hg⟩ :=
    alignedSecondDefect_dvd_p5_68 hp hq hjac hH hp6' hq8' haligned
  have h3eq :
      (3 : K[X]) * q.coeff 7 = (4 : K[X]) * g * H ^ 2 := by
    have hN : (3 : K[X]) * q.coeff 7 = (4 : K[X]) * p.coeff 5 * H := by
      linear_combination -haligned
    calc
      (3 : K[X]) * q.coeff 7 = (4 : K[X]) * p.coeff 5 * H := hN
      _ = (4 : K[X]) * (H * g) * H := by rw [hg]
      _ = (4 : K[X]) * g * H ^ 2 := by ring
  have h3ne : (3 : K[X]) ≠ 0 := by
    rw [← C_ofNat_poly]
    exact Polynomial.C_ne_zero.mpr (by norm_num)
  have h3scale : (3 : K[X]) * Polynomial.C (4 / 3 : K) = (4 : K[X]) := by
    rw [← C_ofNat_poly (n := 3), ← C_ofNat_poly (n := 4), ← Polynomial.C_mul]
    norm_num
  have hq7 :
      q.coeff 7 = Polynomial.C (4 / 3 : K) * g * H ^ 2 := by
    apply mul_left_cancel₀ h3ne
    calc
      (3 : K[X]) * q.coeff 7 = (4 : K[X]) * g * H ^ 2 := h3eq
      _ = ((3 : K[X]) * Polynomial.C (4 / 3 : K)) * g * H ^ 2 := by
            rw [h3scale]
      _ = (3 : K[X]) * (Polynomial.C (4 / 3 : K) * g * H ^ 2) := by
            ring
  exact ⟨κ, g, hg, hq7, hM⟩

/-- At scale two the common core has a root, and the aligned jet vanishes
there. -/
theorem normalized68ScaleTwo_alignedFace_rootJet
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized68LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (4 : K[X]) * p.coeff 5 * H - (3 : K[X]) * q.coeff 7 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ a : K, H.eval a = 0 ∧ (p.coeff 5).eval a = 0 ∧
      (q.coeff 7).eval a = 0 := by
  dsimp only at haligned ⊢
  have hH : H ≠ 0 := hsource.1
  have hHdegree : H.natDegree = 2 := hsource.2.1
  have hdeg : H.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hH, hHdegree]
    decide
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root H hdeg
  obtain ⟨_, g, hp5, hq7, _⟩ :=
    normalized68ScaleTwo_alignedFace_packet hsource haligned
  have hroot : H.eval a = 0 := ha
  refine ⟨a, hroot, ?_, ?_⟩
  · simp [hp5, hroot]
  · simp [hq7, hroot]

#print axioms secondCoefficientJacobianRow_68
#print axioms alignedSecondDefectRow_eq_zero_68
#print axioms alignedSecondDefectPowerRelation_68
#print axioms alignedSecondDefect_dvd_p5_68
#print axioms alignedSecondDefect_pow_dvd_q7_68
#print axioms normalized68ScaleTwo_alignedFace_secondDefectPowerRelation
#print axioms normalized68ScaleTwo_alignedFace_packet
#print axioms normalized68ScaleTwo_alignedFace_rootJet

end Max11DegreeRoutes
