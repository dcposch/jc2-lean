import LowScale68ScaleTwoAlignedNonsquareDegreeNine

/-! # Exact residual after the nonsquare degree-nine gain -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

section DegreeEightRow68

variable {k : Type*} [Field k] [CharZero k]

/-- The next unused, degree-eight coefficient of the `(6,8)` Keller
bracket. -/
theorem fifthCoefficientJacobianRow_68 {p q : k[X][Y]} {j : k}
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hjac : bivariateJacobian p q = C (C j)) :
    (p.coeff 6).derivative * (q.coeff 3 * C (3 : k)) +
        (p.coeff 5).derivative * (q.coeff 4 * C (4 : k)) +
        (p.coeff 4).derivative * (q.coeff 5 * C (5 : k)) +
        (p.coeff 3).derivative * (q.coeff 6 * C (6 : k)) +
        (p.coeff 2).derivative * (q.coeff 7 * C (7 : k)) +
        (p.coeff 1).derivative * (q.coeff 8 * C (8 : k)) -
      ((p.coeff 6 * C (6 : k)) * (q.coeff 3).derivative +
        (p.coeff 5 * C (5 : k)) * (q.coeff 4).derivative +
        (p.coeff 4 * C (4 : k)) * (q.coeff 5).derivative +
        (p.coeff 3 * C (3 : k)) * (q.coeff 6).derivative +
        (p.coeff 2 * C (2 : k)) * (q.coeff 7).derivative +
        (p.coeff 1 * C (1 : k)) * (q.coeff 8).derivative) = 0 := by
  have hcoeff := congrArg (fun r : k[X][Y] => r.coeff 8) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (8 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 8 :
      Finset (ℕ × ℕ)) =
      ({(0, 8), (1, 7), (2, 6), (3, 5), (4, 4), (5, 3), (6, 2),
        (7, 1), (8, 0)} : Finset (ℕ × ℕ)) := by decide
  rw [hanti] at hcoeff
  norm_num [hp, hq, Polynomial.coeff_eq_zero_of_natDegree_lt] at hcoeff ⊢
  have hC3 : C (3 : k) = (3 : k[X]) := C_eq_natCast 3
  have hC4 : C (4 : k) = (4 : k[X]) := C_eq_natCast 4
  have hC5 : C (5 : k) = (5 : k[X]) := C_eq_natCast 5
  have hC6 : C (6 : k) = (6 : k[X]) := C_eq_natCast 6
  have hC7 : C (7 : k) = (7 : k[X]) := C_eq_natCast 7
  have hC8 : C (8 : k) = (8 : k[X]) := C_eq_natCast 8
  have hC2 : C (2 : k) = (2 : k[X]) := C_eq_natCast 2
  rw [hC3, hC4, hC5, hC6, hC7, hC8, hC2]
  linear_combination hcoeff

/-- Under the degree-nine packet, the raw degree-eight row has just the
`p₄' q₅` product left at a simple core root. -/
theorem fifthCoefficientJacobianRow_eval_root_68
    {p q : k[X][Y]} {j : k} {H g : k[X]} {a : k}
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hjac : bivariateJacobian p q = C (C j))
    (hp6 : p.coeff 6 = H ^ 3) (hq8 : q.coeff 8 = H ^ 4)
    (hg : p.coeff 5 = H * g)
    (hq7 : q.coeff 7 = C (4 / 3 : k) * g * H ^ 2)
    (ha : H.eval a = 0) (hg0 : g.eval a = 0)
    (hp40 : (p.coeff 4).eval a = 0)
    (hq60 : (q.coeff 6).eval a = 0)
    (hq6' : (q.coeff 6).derivative.eval a = 0) :
    (5 : k) * (p.coeff 4).derivative.eval a * (q.coeff 5).eval a = 0 := by
  have hrow := fifthCoefficientJacobianRow_68 hp hq hjac
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
  simp only [hH3, hH3', hH4, hH4', hp5, hp5', hq7e, hq7', hp40,
    hq60, hq6', ha, hg0] at heval
  simp only [zero_mul, mul_zero, add_zero, zero_add, sub_zero, eval_zero]
    at heval
  linear_combination heval

/-- The exact scalar split supplied by the degree-eight row after writing
`p₄=H t`. -/
theorem degreeEight_simpleRoot_t_q5_split_68
    {p q : k[X][Y]} {j : k} {H g t : k[X]} {a : k}
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hjac : bivariateJacobian p q = C (C j))
    (hp6 : p.coeff 6 = H ^ 3) (hq8 : q.coeff 8 = H ^ 4)
    (hg : p.coeff 5 = H * g)
    (hq7 : q.coeff 7 = C (4 / 3 : k) * g * H ^ 2)
    (hp4 : p.coeff 4 = H * t)
    (hq6sq : H ^ 2 ∣ q.coeff 6)
    (ha : H.eval a = 0) (hH' : H.derivative.eval a ≠ 0)
    (hg0 : g.eval a = 0) :
    t.eval a = 0 ∨ (q.coeff 5).eval a = 0 := by
  obtain ⟨s, hs⟩ := hq6sq
  have hp40 : (p.coeff 4).eval a = 0 := by simp [hp4, eval_mul, ha]
  have hq60 : (q.coeff 6).eval a = 0 := by
    rw [hs, eval_mul, eval_pow, ha, zero_pow (by decide), zero_mul]
  have hq6' : (q.coeff 6).derivative.eval a = 0 := by
    rw [hs, derivative_mul, eval_add, eval_mul, eval_mul, eval_pow, ha]
    have hpow' : (H ^ 2).derivative.eval a = 0 :=
      eval_derivative_pow_of_isRoot (by decide) ha
    rw [hpow', zero_mul, zero_add]
    simp
  have hrow := fifthCoefficientJacobianRow_eval_root_68 hp hq hjac hp6 hq8
    hg hq7 ha hg0 hp40 hq60 hq6'
  have hp4' : (p.coeff 4).derivative.eval a =
      H.derivative.eval a * t.eval a := by
    rw [hp4, eval_derivative_mul_of_left_root ha]
  rw [hp4'] at hrow
  have h5 : (5 : k) ≠ 0 := by norm_num
  have hprod : t.eval a * (q.coeff 5).eval a = 0 := by
    have hrow' : (5 : k) *
        (H.derivative.eval a * (t.eval a * (q.coeff 5).eval a)) = 0 := by
      simpa only [mul_assoc] using hrow
    have hmid := (mul_eq_zero.mp hrow').resolve_left h5
    exact (mul_eq_zero.mp hmid).resolve_left hH'
  exact mul_eq_zero.mp hprod

end DegreeEightRow68

section ExactAResidual68

variable {k : Type*} [Field k] [CharZero k]

/-- Exact source remainder after writing the two degree-nine quotients. -/
theorem nine_q6_sub_seven_g_sq_degreeNine_shape_68
    (H a4 a5 b6 g r t : k[X]) (kappa : k) (hH : H ≠ 0)
    (hM : alignedSecondDefect68 H a4 a5 b6 = C kappa * H ^ 5)
    (hg : a5 = H * g) (hr : g = H * r) (ht : a4 = H * t) :
    (9 : k[X]) * b6 - (7 : k[X]) * g ^ 2 =
      H ^ 2 * ((12 : k[X]) * t - (5 : k[X]) * r ^ 2 + C kappa * H) := by
  have hshape :=
    nine_q6_sub_seven_g_sq_of_secondDefect H a4 a5 b6 g kappa hH hM hg
  rw [hr] at hshape ⊢
  rw [ht] at hshape
  linear_combination hshape

/-- The even-cleared `A` numerator is `H⁴/12` times the single residual
`12t-5r²`. -/
theorem evenClearedA68_degreeNine_shape
    (H a4 a5 g r t : k[X])
    (hg : a5 = H * g) (hr : g = H * r) (ht : a4 = H * t) :
    evenClearedA68 H a5 a4 =
      H ^ 4 * (C (1 / 12 : k) *
        ((12 : k[X]) * t - (5 : k[X]) * r ^ 2)) := by
  have h12 : C (1 / 12 : k) * (12 : k[X]) = 1 := by
    rw [← C_ofNat_poly, ← C_mul]
    norm_num
  have h5 : C (1 / 12 : k) * (5 : k[X]) = C (5 / 12 : k) := by
    rw [← C_ofNat_poly, ← C_mul]
    congr 1
    norm_num
  have hinner : C (1 / 12 : k) *
      ((12 : k[X]) * t - (5 : k[X]) * r ^ 2) =
        t - C (5 / 12 : k) * r ^ 2 := by
    calc
      C (1 / 12 : k) *
          ((12 : k[X]) * t - (5 : k[X]) * r ^ 2) =
          (C (1 / 12 : k) * (12 : k[X])) * t -
            (C (1 / 12 : k) * (5 : k[X])) * r ^ 2 := by ring
      _ = t - C (5 / 12 : k) * r ^ 2 := by rw [h12, h5, one_mul]
  rw [evenClearedA68, hg, hr, ht, hinner]
  ring

/-- The requested one-more source order is exactly divisibility of the
single quotient residual `12t-5r²`. -/
theorem degreeNine_source_pow3_iff_residual_68
    (H a4 a5 b6 g r t : k[X]) (kappa : k) (hH : H ≠ 0)
    (hM : alignedSecondDefect68 H a4 a5 b6 = C kappa * H ^ 5)
    (hg : a5 = H * g) (hr : g = H * r) (ht : a4 = H * t) :
    H ^ 3 ∣ (9 : k[X]) * b6 - (7 : k[X]) * g ^ 2 ↔
      H ∣ (12 : k[X]) * t - (5 : k[X]) * r ^ 2 := by
  have hshape := nine_q6_sub_seven_g_sq_degreeNine_shape_68 H a4 a5 b6
    g r t kappa hH hM hg hr ht
  have hH2 : H ^ 2 ≠ 0 := pow_ne_zero 2 hH
  have hpow : H ^ 3 = H ^ 2 * H := by ring
  constructor
  · intro hsrc
    have hrew : H ^ 2 * H ∣ H ^ 2 *
        ((12 : k[X]) * t - (5 : k[X]) * r ^ 2 + C kappa * H) := by
      rw [← hpow, ← hshape]
      exact hsrc
    have hsum : H ∣
        (12 : k[X]) * t - (5 : k[X]) * r ^ 2 + C kappa * H :=
      (mul_dvd_mul_iff_left hH2).mp hrew
    have hk : H ∣ C kappa * H := ⟨C kappa, by ring⟩
    have hout : H ∣
        ((12 : k[X]) * t - (5 : k[X]) * r ^ 2 + C kappa * H) -
          C kappa * H := dvd_sub hsum hk
    simpa only [add_sub_cancel_right] using hout
  · intro hres
    have hsum : H ∣
        (12 : k[X]) * t - (5 : k[X]) * r ^ 2 + C kappa * H :=
      dvd_add hres ⟨C kappa, by ring⟩
    have hmul : H ^ 2 * H ∣ H ^ 2 *
        ((12 : k[X]) * t - (5 : k[X]) * r ^ 2 + C kappa * H) :=
      mul_dvd_mul_left _ hsum
    rw [← hpow, ← hshape] at hmul
    exact hmul

/-- Equivalently, the full `A` numerator divisibility is the same single
residual. -/
theorem degreeNine_evenClearedA_pow5_iff_residual_68
    (H a4 a5 g r t : k[X]) (hH : H ≠ 0)
    (hg : a5 = H * g) (hr : g = H * r) (ht : a4 = H * t) :
    H ^ 5 ∣ evenClearedA68 H a5 a4 ↔
      H ∣ (12 : k[X]) * t - (5 : k[X]) * r ^ 2 := by
  have hshape := evenClearedA68_degreeNine_shape H a4 a5 g r t hg hr ht
  have hH4 : H ^ 4 ≠ 0 := pow_ne_zero 4 hH
  have hpow : H ^ 5 = H ^ 4 * H := by ring
  have hunit : IsUnit (C (1 / 12 : k) : k[X]) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (by norm_num))
  constructor
  · intro hA
    have hrew : H ^ 4 * H ∣ H ^ 4 *
        (C (1 / 12 : k) *
          ((12 : k[X]) * t - (5 : k[X]) * r ^ 2)) := by
      rw [← hpow, ← hshape]
      exact hA
    have hmid : H ∣ C (1 / 12 : k) *
        ((12 : k[X]) * t - (5 : k[X]) * r ^ 2) :=
      (mul_dvd_mul_iff_left hH4).mp hrew
    exact (hunit.dvd_mul_left).mp hmid
  · intro hres
    have hmid : H ∣ C (1 / 12 : k) *
        ((12 : k[X]) * t - (5 : k[X]) * r ^ 2) :=
      (hunit.dvd_mul_left).mpr hres
    have hmul : H ^ 4 * H ∣ H ^ 4 *
        (C (1 / 12 : k) *
          ((12 : k[X]) * t - (5 : k[X]) * r ^ 2)) :=
      mul_dvd_mul_left _ hmid
    rw [← hpow, ← hshape] at hmul
    exact hmul

end ExactAResidual68

section QuadraticDegreeEightSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Source-facing exact residual and the finite split supplied by the next
unused Keller row. -/
theorem NonsquareAlignedSourceCurveData68.degreeEightResidualPacket
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hdeg : H.natDegree = 2)
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hp6 : p.coeff 6 = H ^ 3) (hq8 : q.coeff 8 = H ^ 4)
    (haligned :
      (4 : k[X]) * p.coeff 5 * H - (3 : k[X]) * q.coeff 7 = 0)
    (hjac : bivariateJacobian p q = C (C j)) :
    ∃ (kappa : k) (g r t : k[X]),
      p.coeff 5 = H * g ∧ g = H * r ∧ p.coeff 4 = H * t ∧
      q.coeff 7 = C (4 / 3 : k) * g * H ^ 2 ∧
      H ^ 2 ∣ q.coeff 6 ∧
      ((9 : k[X]) * q.coeff 6 - (7 : k[X]) * g ^ 2 =
        H ^ 2 * ((12 : k[X]) * t - (5 : k[X]) * r ^ 2 + C kappa * H)) ∧
      (H ^ 3 ∣ (9 : k[X]) * q.coeff 6 - (7 : k[X]) * g ^ 2 ↔
        H ∣ (12 : k[X]) * t - (5 : k[X]) * r ^ 2) ∧
      (H ^ 5 ∣ evenClearedA68 H (p.coeff 5) (p.coeff 4) ↔
        H ∣ (12 : k[X]) * t - (5 : k[X]) * r ^ 2) ∧
      ∀ a : k, H.eval a = 0 →
        t.eval a = 0 ∨ (q.coeff 5).eval a = 0 := by
  have hH : H ≠ 0 := H_ne_zero_of_nonsquare68 (H := H)
  have hnsq : ∀ h0 : k[X], H ≠ h0 ^ 2 := NonsquarePolynomial46.not_sq
  obtain ⟨kappa, g, hg, hq7, hM, hgdvd, hp4dvd, hq6sq, _hsrc2,
      _hA4, _hiffA⟩ :=
    S.degreeNinePacket (H := H) hdeg hp hq hp6 hq8 haligned hjac
  obtain ⟨r, hr⟩ := hgdvd
  obtain ⟨t, ht⟩ := hp4dvd
  have hshape := nine_q6_sub_seven_g_sq_degreeNine_shape_68 H
    (p.coeff 4) (p.coeff 5) (q.coeff 6) g r t kappa hH hM hg hr ht
  have hiffsrc := degreeNine_source_pow3_iff_residual_68 H
    (p.coeff 4) (p.coeff 5) (q.coeff 6) g r t kappa hH hM hg hr ht
  have hiffA := degreeNine_evenClearedA_pow5_iff_residual_68 H
    (p.coeff 4) (p.coeff 5) g r t hH hg hr ht
  have hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero hdeg hnsq ha
  have hroots : ∀ a : k, H.eval a = 0 →
      t.eval a = 0 ∨ (q.coeff 5).eval a = 0 := by
    intro a ha
    have hg0 : g.eval a = 0 := by simp [hr, eval_mul, ha]
    exact degreeEight_simpleRoot_t_q5_split_68 hp hq hjac hp6 hq8 hg hq7
      ht hq6sq ha (hsimple a ha) hg0
  exact ⟨kappa, g, r, t, hg, hr, ht, hq7, hq6sq, hshape, hiffsrc,
    hiffA, hroots⟩

end QuadraticDegreeEightSource68

end Max11DegreeRoutes
