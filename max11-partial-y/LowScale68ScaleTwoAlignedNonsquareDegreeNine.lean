import LowScale68ScaleTwoAlignedNonsquareDegreeTen

/-! # Degree-nine Keller row on the aligned nonsquare `(6,8)` face -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

section DegreeNineRow68

variable {k : Type*} [Field k] [CharZero k]

/-- The degree-nine coefficient of the literal `(6,8)` Keller bracket. -/
theorem fourthCoefficientJacobianRow_68 {p q : k[X][Y]} {j : k}
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hjac : bivariateJacobian p q = C (C j)) :
    (p.coeff 6).derivative * (q.coeff 4 * C (4 : k)) +
        (p.coeff 5).derivative * (q.coeff 5 * C (5 : k)) +
        (p.coeff 4).derivative * (q.coeff 6 * C (6 : k)) +
        (p.coeff 3).derivative * (q.coeff 7 * C (7 : k)) +
        (p.coeff 2).derivative * (q.coeff 8 * C (8 : k)) -
      ((p.coeff 6 * C (6 : k)) * (q.coeff 4).derivative +
        (p.coeff 5 * C (5 : k)) * (q.coeff 5).derivative +
        (p.coeff 4 * C (4 : k)) * (q.coeff 6).derivative +
        (p.coeff 3 * C (3 : k)) * (q.coeff 7).derivative +
        (p.coeff 2 * C (2 : k)) * (q.coeff 8).derivative) = 0 := by
  have hcoeff := congrArg (fun r : k[X][Y] => r.coeff 9) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (9 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 9 :
      Finset (ℕ × ℕ)) =
      ({(0, 9), (1, 8), (2, 7), (3, 6), (4, 5), (5, 4), (6, 3),
        (7, 2), (8, 1), (9, 0)} : Finset (ℕ × ℕ)) := by decide
  rw [hanti] at hcoeff
  norm_num [hp, hq, Polynomial.coeff_eq_zero_of_natDegree_lt] at hcoeff ⊢
  have hC4 : C (4 : k) = (4 : k[X]) := C_eq_natCast 4
  have hC5 : C (5 : k) = (5 : k[X]) := C_eq_natCast 5
  have hC6 : C (6 : k) = (6 : k[X]) := C_eq_natCast 6
  have hC7 : C (7 : k) = (7 : k[X]) := C_eq_natCast 7
  have hC8 : C (8 : k) = (8 : k[X]) := C_eq_natCast 8
  have hC3 : C (3 : k) = (3 : k[X]) := C_eq_natCast 3
  have hC2 : C (2 : k) = (2 : k[X]) := C_eq_natCast 2
  rw [hC4, hC5, hC6, hC7, hC8, hC3, hC2]
  linear_combination hcoeff

/-- At a common simple-core root where the degree-ten row has already
forced `g=q₆=0`, the degree-nine row is `4 p₄ q₆' = 0`. -/
theorem fourthCoefficientJacobianRow_eval_root_68
    {p q : k[X][Y]} {j : k} {H g : k[X]} {a : k}
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hjac : bivariateJacobian p q = C (C j))
    (hp6 : p.coeff 6 = H ^ 3) (hq8 : q.coeff 8 = H ^ 4)
    (hg : p.coeff 5 = H * g)
    (hq7 : q.coeff 7 = C (4 / 3 : k) * g * H ^ 2)
    (ha : H.eval a = 0) (hg0 : g.eval a = 0)
    (hq60 : (q.coeff 6).eval a = 0) :
    (4 : k) * (p.coeff 4).eval a * (q.coeff 6).derivative.eval a = 0 := by
  have hrow := fourthCoefficientJacobianRow_68 hp hq hjac
  have hH3 : (H ^ 3).eval a = 0 := eval_pow_of_isRoot (by decide) ha
  have hH3' : (H ^ 3).derivative.eval a = 0 :=
    eval_derivative_pow_of_isRoot (by decide) ha
  have hH4 : (H ^ 4).eval a = 0 := eval_pow_of_isRoot (by decide) ha
  have hH4' : (H ^ 4).derivative.eval a = 0 :=
    eval_derivative_pow_of_isRoot (by decide) ha
  have hp5 : (H * g).eval a = 0 := by simp [eval_mul, ha]
  have hp5' : (H * g).derivative.eval a = 0 := by
    rw [eval_derivative_mul_of_left_root ha, hg0, mul_zero]
  have hq7e : (q.coeff 7).eval a = 0 := by
    simpa [hq7] using eval_C_mul_g_H_pow_two (c := (4 / 3 : k)) (g := g) ha
  have hq7' : (q.coeff 7).derivative.eval a = 0 := by
    simpa [hq7] using
      eval_derivative_C_mul_g_H_pow_two (c := (4 / 3 : k)) (g := g) ha
  have heval := congrArg (fun f : k[X] => f.eval a) hrow
  simp only [eval_add, eval_sub, eval_mul, eval_C, hp6, hq8, hg] at heval
  simp only [hH3, hH3', hH4, hH4', hp5, hp5', hq7e, hq7', hq60,
    ha, hg0]
    at heval
  simp only [zero_mul, mul_zero, add_zero, zero_add, sub_zero, eval_zero]
    at heval
  linear_combination -heval

/-- The derivative of the second defect at a root where `g` vanishes. -/
theorem nine_q6_derivative_eq_twelve_Hderiv_p4_eval_root
    (H a4 a5 b6 g : k[X]) (kappa : k) {a : k} (hH : H ≠ 0)
    (hM : alignedSecondDefect68 H a4 a5 b6 = C kappa * H ^ 5)
    (hg : a5 = H * g) (ha : H.eval a = 0) (hg0 : g.eval a = 0) :
    (9 : k) * b6.derivative.eval a =
      (12 : k) * H.derivative.eval a * a4.eval a := by
  have hid :=
    nine_q6_sub_two_g_sq_of_secondDefect H a4 a5 b6 g kappa hH hM hg
  have hder := congrArg (fun f : k[X] => f.derivative.eval a) hid
  have hder' : (9 : k) * b6.derivative.eval a =
      (12 : k) * a4.eval a * H.derivative.eval a := by
    simpa [derivative_add, derivative_sub, derivative_mul, derivative_sq,
      derivative_pow, derivative_C, C_ofNat_poly, eval_add, eval_sub,
      eval_mul, eval_pow, eval_C, eval_ofNat, ha, hg0] using hder
  calc
    (9 : k) * b6.derivative.eval a =
        (12 : k) * a4.eval a * H.derivative.eval a := hder'
    _ = (12 : k) * H.derivative.eval a * a4.eval a := by ring

/-- The degree-nine row and the differentiated second defect force `p₄`
to vanish at every simple root of `H`. -/
theorem degreeNine_simpleRoot_p4_vanishing_68
    {p q : k[X][Y]} {j kappa : k} {H g : k[X]} {a : k}
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hjac : bivariateJacobian p q = C (C j)) (hH : H ≠ 0)
    (hp6 : p.coeff 6 = H ^ 3) (hq8 : q.coeff 8 = H ^ 4)
    (hg : p.coeff 5 = H * g)
    (hq7 : q.coeff 7 = C (4 / 3 : k) * g * H ^ 2)
    (hM : alignedSecondDefect68 H (p.coeff 4) (p.coeff 5) (q.coeff 6) =
      C kappa * H ^ 5)
    (ha : H.eval a = 0) (hH' : H.derivative.eval a ≠ 0) :
    (p.coeff 4).eval a = 0 := by
  have hten := degreeTen_simpleRoot_vanishing_68 hp hq hjac hH hp6 hq8
    hg hq7 hM ha hH'
  have hrow := fourthCoefficientJacobianRow_eval_root_68 hp hq hjac hp6
    hq8 hg hq7 ha hten.1 hten.2
  have hder := nine_q6_derivative_eq_twelve_Hderiv_p4_eval_root H
    (p.coeff 4) (p.coeff 5) (q.coeff 6) g kappa hH hM hg ha hten.1
  by_contra hp40
  have h4 : (4 : k) ≠ 0 := by norm_num
  have hq6' : (q.coeff 6).derivative.eval a = 0 := by
    have hrow' : (4 : k) *
        ((p.coeff 4).eval a * (q.coeff 6).derivative.eval a) = 0 := by
      simpa only [mul_assoc] using hrow
    have hprod : (p.coeff 4).eval a * (q.coeff 6).derivative.eval a = 0 :=
      (mul_eq_zero.mp hrow').resolve_left h4
    exact (mul_eq_zero.mp hprod).resolve_left hp40
  have h12 : (12 : k) ≠ 0 := by norm_num
  have hmid : H.derivative.eval a * (p.coeff 4).eval a = 0 := by
    have hz : (12 : k) * H.derivative.eval a * (p.coeff 4).eval a = 0 := by
      rw [← hder, hq6', mul_zero]
    have hz' : (12 : k) *
        (H.derivative.eval a * (p.coeff 4).eval a) = 0 := by
      simpa only [mul_assoc] using hz
    exact (mul_eq_zero.mp hz').resolve_left h12
  exact hp40 ((mul_eq_zero.mp hmid).resolve_left hH')

end DegreeNineRow68

section NonsquareDegreeNine68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- The new degree-nine consequence: the nonsquare quadratic core divides
the quartic sextic coefficient. -/
theorem alignedDegreeNine_dvd_p4_68
    {p q : k[X][Y]} {j : k} {H g : k[X]} (hdeg : H.natDegree = 2)
    (hnsq : ∀ h0 : k[X], H ≠ h0 ^ 2)
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hjac : bivariateJacobian p q = C (C j))
    (hp6 : p.coeff 6 = H ^ 3) (hq8 : q.coeff 8 = H ^ 4)
    (hg : p.coeff 5 = H * g)
    (hq7 : q.coeff 7 = C (4 / 3 : k) * g * H ^ 2)
    {kappa : k}
    (hM : alignedSecondDefect68 H (p.coeff 4) (p.coeff 5) (q.coeff 6) =
      C kappa * H ^ 5) :
    H ∣ p.coeff 4 := by
  have hH : H ≠ 0 := by
    rintro rfl
    simp at hdeg
  have hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero hdeg hnsq ha
  refine dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple ?_
  intro a ha
  exact degreeNine_simpleRoot_p4_vanishing_68 hp hq hjac hH hp6 hq8 hg
    hq7 hM ha (hsimple a ha)

/-- Once `H ∣ g` and the degree-nine row gives `H ∣ p₄`, the second
defect yields the next full packet: `H² ∣ q₆`, `H²` divides the source
remainder, and `H⁴` divides the even-cleared `A` numerator. -/
theorem degreeNine_higher_divisibilities_68
    (H a4 a5 b6 g : k[X]) (kappa : k) (hH : H ≠ 0)
    (hM : alignedSecondDefect68 H a4 a5 b6 = C kappa * H ^ 5)
    (hg : a5 = H * g) (hgdvd : H ∣ g) (ha4dvd : H ∣ a4) :
    H ^ 2 ∣ b6 ∧
      H ^ 2 ∣ (9 : k[X]) * b6 - (7 : k[X]) * g ^ 2 ∧
      H ^ 4 ∣ evenClearedA68 H a5 a4 := by
  obtain ⟨r, hr⟩ := hgdvd
  obtain ⟨t, ht⟩ := ha4dvd
  have h2 :=
    nine_q6_sub_two_g_sq_of_secondDefect H a4 a5 b6 g kappa hH hM hg
  have h9shape :
      (9 : k[X]) * b6 = H ^ 2 *
        ((2 : k[X]) * r ^ 2 + (12 : k[X]) * t + C kappa * H) := by
    rw [hr, ht] at h2
    linear_combination h2
  have h9dvd : H ^ 2 ∣ (9 : k[X]) * b6 := ⟨_, h9shape⟩
  have h9unit : IsUnit (9 : k[X]) := by
    rw [← C_ofNat_poly]
    exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (by norm_num))
  have hb6 : H ^ 2 ∣ b6 := (h9unit.dvd_mul_left).mp h9dvd
  have hg2 : H ^ 2 ∣ g ^ 2 := by
    refine ⟨r ^ 2, ?_⟩
    rw [hr]
    ring
  have hsrc : H ^ 2 ∣ (9 : k[X]) * b6 - (7 : k[X]) * g ^ 2 :=
    dvd_sub (dvd_mul_of_dvd_right hb6 _) (dvd_mul_of_dvd_right hg2 _)
  have hsrcOut := hsrc
  obtain ⟨s, hs⟩ := hsrc
  have hshape :=
    evenClearedA68_of_secondDefect_p5 H a4 a5 b6 g kappa hM hg
  have hA4 : H ^ 4 ∣ evenClearedA68 H a5 a4 := by
    refine ⟨C (1 / 12 : k) * (s - C kappa * H), ?_⟩
    rw [hshape, hs]
    ring
  exact ⟨hb6, hsrcOut, hA4⟩

end NonsquareDegreeNine68

section QuadraticDegreeNineSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Source-facing degree-nine divisibility packet. -/
theorem NonsquareAlignedSourceCurveData68.degreeNinePacket
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hdeg : H.natDegree = 2)
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hp6 : p.coeff 6 = H ^ 3) (hq8 : q.coeff 8 = H ^ 4)
    (haligned :
      (4 : k[X]) * p.coeff 5 * H - (3 : k[X]) * q.coeff 7 = 0)
    (hjac : bivariateJacobian p q = C (C j)) :
    ∃ (kappa : k) (g : k[X]),
      p.coeff 5 = H * g ∧
        q.coeff 7 = C (4 / 3 : k) * g * H ^ 2 ∧
        alignedSecondDefect68 H (p.coeff 4) (p.coeff 5) (q.coeff 6) =
          C kappa * H ^ 5 ∧
        H ∣ g ∧ H ∣ p.coeff 4 ∧ H ^ 2 ∣ q.coeff 6 ∧
        H ^ 2 ∣ (9 : k[X]) * q.coeff 6 - (7 : k[X]) * g ^ 2 ∧
        H ^ 4 ∣ evenClearedA68 H (p.coeff 5) (p.coeff 4) ∧
        (H ^ 5 ∣ evenClearedA68 H (p.coeff 5) (p.coeff 4) ↔
          H ^ 3 ∣ (9 : k[X]) * q.coeff 6 - (7 : k[X]) * g ^ 2) := by
  have hH : H ≠ 0 := H_ne_zero_of_nonsquare68 (H := H)
  have hnsq : ∀ h0 : k[X], H ≠ h0 ^ 2 := NonsquarePolynomial46.not_sq
  obtain ⟨kappa, g, hg, hq7, hM, hgdvd, _hq6, _hsrc, _hA3,
      _hiffp4, hiffA⟩ :=
    S.degreeTenEvenClearedDvd (H := H) hdeg hp hq hp6 hq8 haligned hjac
  have hp4 := alignedDegreeNine_dvd_p4_68 hdeg hnsq hp hq hjac hp6 hq8
    hg hq7 hM
  have hnext := degreeNine_higher_divisibilities_68 H (p.coeff 4)
    (p.coeff 5) (q.coeff 6) g kappa hH hM hg hgdvd hp4
  exact ⟨kappa, g, hg, hq7, hM, hgdvd, hp4, hnext.1, hnext.2.1,
    hnext.2.2, hiffA⟩

end QuadraticDegreeNineSource68

end Max11DegreeRoutes
