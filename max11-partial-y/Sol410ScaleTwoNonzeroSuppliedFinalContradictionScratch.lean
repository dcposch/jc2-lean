import Sol410ScaleTwoNonzeroSuppliedP3FourthRootScratch

/-!
# Closure of the supplied nonzero square `(4,10)` face

The literal degree-four Keller row now has a unique term not visibly carrying
`h₀⁴`, namely `(p₄)' q₁`.  The degree-zero row makes `q₁` a unit at the
supplied root, so `(p₄)'` would carry `h₀⁴`.  This is impossible because
`p₄ = h₀⁴` and `h₀` is linear.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option linter.unusedSectionVars false

theorem linearPolynomial_fourthPower_derivative_not_four_dvd_410
    (h : k[X]) (a : k) (hdegree : h.natDegree = 1)
    (hroot : h.eval a = 0) :
    ¬ h ^ 4 ∣ (h ^ 4).derivative := by
  intro hdvd
  have hh : h ≠ 0 := by
    intro hz
    rw [hz, Polynomial.natDegree_zero] at hdegree
    exact zero_ne_one hdegree
  obtain ⟨c, hc, d, hlinear⟩ := Polynomial.natDegree_eq_one.mp hdegree
  have hprime : h.derivative.eval a = c := by
    rw [← hlinear]
    simp
  obtain ⟨w, hw⟩ := hdvd
  have hder : (h ^ 4).derivative =
      h ^ 3 * ((4 : k[X]) * h.derivative) := by
    simp only [derivative_pow]
    rw [Polynomial.C_eq_natCast]
    ring
  have heq : h ^ 3 * ((4 : k[X]) * h.derivative) =
      h ^ 3 * (h * w) := by
    calc
      h ^ 3 * ((4 : k[X]) * h.derivative) = (h ^ 4).derivative := hder.symm
      _ = h ^ 4 * w := hw
      _ = h ^ 3 * (h * w) := by ring
  have hcancel : (4 : k[X]) * h.derivative = h * w :=
    mul_left_cancel₀ (pow_ne_zero 3 hh) heq
  have heval := congrArg (fun r : k[X] => r.eval a) hcancel
  simp only [eval_mul, eval_ofNat, hroot, zero_mul, hprime] at heval
  exact (mul_ne_zero (by norm_num : (4 : k) ≠ 0) hc) heval

set_option maxHeartbeats 64000000 in
theorem nonzeroFace410_linearRoot_suppliedFinalContradiction
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hdegree : h0.natDegree = 1) (hH : H = h0 ^ 2)
    (hp4 : p.coeff 4 = H ^ 2) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 3 * H ^ 3 - (2 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0) (hlambda : lambda ≠ 0) (hj : j ≠ 0) :
    False := by
  have hp1cube := nonzeroFace410_linearRoot_suppliedP1TripleRoot p q H h0
    j lambda a hp hq hh0 hdegree hH hp4 hq10 hN hD hroot hlambda hj
  obtain ⟨p13, hp13⟩ := hp1cube
  have hp1cube' : h0 ^ 3 ∣ p.coeff 1 := ⟨p13, hp13⟩
  have hp2cube := nonzeroFace410_linearRoot_suppliedP2TripleRoot p q H h0
    j lambda a hp hq hh0 hdegree hH hp4 hq10 hN hD hroot hlambda hj
  obtain ⟨p23, hp23⟩ := hp2cube
  have hp2cube' : h0 ^ 3 ∣ p.coeff 2 := ⟨p23, hp23⟩
  have hp3four := nonzeroFace410_linearRoot_suppliedP3FourthRoot p q H h0
    j lambda a hp hq hh0 hdegree hH hp4 hq10 hN hD hroot hlambda hj
  obtain ⟨p34, hp34⟩ := hp3four
  have hp3four' : h0 ^ 4 ∣ p.coeff 3 := ⟨p34, hp34⟩
  obtain ⟨t2, a22, s22, vis, w73, q54, b44, b33, q22, hp3, hp2,
      hq8, hq7, hq6, hq5, hq4, hq3, hq2⟩ :=
    nonzeroFace410_linearRoot_suppliedGroundDoubleRoot p q H h0 j lambda a
      hp hq hh0 hdegree hH hp4 hq10 hN hD hroot hlambda
  have hp4four : h0 ^ 4 ∣ p.coeff 4 := by
    refine ⟨1, ?_⟩
    rw [hp4, hH]
    ring
  have hq5four : h0 ^ 4 ∣ q.coeff 5 := ⟨q54, hq5⟩
  have hq4four : h0 ^ 4 ∣ q.coeff 4 := ⟨b44, hq4⟩
  have hq3cube : h0 ^ 3 ∣ q.coeff 3 := ⟨b33, hq3⟩
  have hq2sq : h0 ^ 2 ∣ q.coeff 2 := ⟨q22, hq2⟩
  have h2d3 : h0 ^ 2 ∣ h0 ^ 3 := ⟨h0, by ring⟩
  have h2d4 : h0 ^ 2 ∣ h0 ^ 4 := ⟨h0 ^ 2, by ring⟩
  have hp1sq : h0 ^ 2 ∣ p.coeff 1 := h2d3.trans hp1cube'
  have hp2sq : h0 ^ 2 ∣ p.coeff 2 := h2d3.trans hp2cube'
  have hp3sq : h0 ^ 2 ∣ p.coeff 3 := h2d4.trans hp3four'
  have hq3sq : h0 ^ 2 ∣ q.coeff 3 := h2d3.trans hq3cube
  have hp3d2 : h0 ^ 2 ∣ (p.coeff 3).derivative := by
    refine ⟨h0 * ((4 : k[X]) * h0.derivative * p34 +
        h0 * p34.derivative), ?_⟩
    rw [hp34]
    simp only [derivative_mul, derivative_pow]
    rw [Polynomial.C_eq_natCast]
    ring
  have hp2d2 : h0 ^ 2 ∣ (p.coeff 2).derivative := by
    refine ⟨(3 : k[X]) * h0.derivative * p23 + h0 * p23.derivative, ?_⟩
    rw [hp23]
    simp only [derivative_mul, derivative_pow]
    rw [Polynomial.C_eq_natCast]
    ring
  have hp1d2 : h0 ^ 2 ∣ (p.coeff 1).derivative := by
    refine ⟨(3 : k[X]) * h0.derivative * p13 + h0 * p13.derivative, ?_⟩
    rw [hp13]
    simp only [derivative_mul, derivative_pow]
    rw [Polynomial.C_eq_natCast]
    ring
  have hq3d2 : h0 ^ 2 ∣ (q.coeff 3).derivative := by
    refine ⟨(3 : k[X]) * h0.derivative * b33 + h0 * b33.derivative, ?_⟩
    rw [hq3]
    simp only [derivative_mul, derivative_pow]
    rw [Polynomial.C_eq_natCast]
    ring
  have hq4d2 : h0 ^ 2 ∣ (q.coeff 4).derivative := by
    refine ⟨h0 * ((4 : k[X]) * h0.derivative * b44 +
        h0 * b44.derivative), ?_⟩
    rw [hq4]
    simp only [derivative_mul, derivative_pow]
    rw [Polynomial.C_eq_natCast]
    ring
  have hsquareMul : ∀ f g : k[X], h0 ^ 2 ∣ f → h0 ^ 2 ∣ g →
      h0 ^ 4 ∣ f * g := by
    intro f g hf hg
    obtain ⟨u, hu⟩ := hf
    obtain ⟨v, hv⟩ := hg
    refine ⟨u * v, ?_⟩
    rw [hu, hv]
    ring
  have ha1 : (p.coeff 1).eval a = 0 := by
    rw [hp13, eval_mul, eval_pow, hroot]
    norm_num
  have hkelP := iotaZeroBranch_kellerRowZero410 p q j a hp hq hD ha1
  have hq1nz := (iotaZeroBranch_kellerUnits410
    ((p.coeff 0).derivative.eval a) ((q.coeff 1).eval a) j hj hkelP).2
  have hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j) := by
    simpa [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hD
  have hrow := ninthCoefficientJacobianRow_410 hp hq hjac
  have hC2 : Polynomial.C (2 : k) = (2 : k[X]) :=
    Polynomial.C_eq_natCast 2
  have hC3 : Polynomial.C (3 : k) = (3 : k[X]) :=
    Polynomial.C_eq_natCast 3
  have hC4 : Polynomial.C (4 : k) = (4 : k[X]) :=
    Polynomial.C_eq_natCast 4
  have hC5 : Polynomial.C (5 : k) = (5 : k[X]) :=
    Polynomial.C_eq_natCast 5
  rw [hC2, hC3, hC4, hC5] at hrow
  have ht1 : h0 ^ 4 ∣
      (p.coeff 3).derivative * (q.coeff 2 * (2 : k[X])) := by
    simpa only [mul_assoc] using
      dvd_mul_of_dvd_left (hsquareMul _ _ hp3d2 hq2sq) (2 : k[X])
  have ht2 : h0 ^ 4 ∣
      (p.coeff 2).derivative * (q.coeff 3 * (3 : k[X])) := by
    simpa only [mul_assoc] using
      dvd_mul_of_dvd_left (hsquareMul _ _ hp2d2 hq3sq) (3 : k[X])
  have ht3 : h0 ^ 4 ∣
      (p.coeff 1).derivative * (q.coeff 4 * (4 : k[X])) := by
    have hq4sq : h0 ^ 2 ∣ q.coeff 4 := h2d4.trans hq4four
    simpa only [mul_assoc] using
      dvd_mul_of_dvd_left (hsquareMul _ _ hp1d2 hq4sq) (4 : k[X])
  have ht4 : h0 ^ 4 ∣
      (p.coeff 0).derivative * (q.coeff 5 * (5 : k[X])) :=
    dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hq5four _) _
  have hr1 : h0 ^ 4 ∣
      (p.coeff 4 * (4 : k[X])) * (q.coeff 1).derivative :=
    dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hp4four _) _
  have hr2 : h0 ^ 4 ∣
      (p.coeff 3 * (3 : k[X])) * (q.coeff 2).derivative :=
    dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hp3four' _) _
  have hr3 : h0 ^ 4 ∣
      (p.coeff 2 * (2 : k[X])) * (q.coeff 3).derivative :=
    hsquareMul _ _ (dvd_mul_of_dvd_left hp2sq _) hq3d2
  have hr4 : h0 ^ 4 ∣ p.coeff 1 * (q.coeff 4).derivative :=
    hsquareMul _ _ hp1sq hq4d2
  have hrest : h0 ^ 4 ∣
      ((((p.coeff 3).derivative * (q.coeff 2 * (2 : k[X])) +
        (p.coeff 2).derivative * (q.coeff 3 * (3 : k[X]))) +
        (p.coeff 1).derivative * (q.coeff 4 * (4 : k[X]))) +
        (p.coeff 0).derivative * (q.coeff 5 * (5 : k[X]))) -
      ((((p.coeff 4 * (4 : k[X])) * (q.coeff 1).derivative +
        (p.coeff 3 * (3 : k[X])) * (q.coeff 2).derivative) +
        (p.coeff 2 * (2 : k[X])) * (q.coeff 3).derivative) +
        p.coeff 1 * (q.coeff 4).derivative) :=
    (((ht1.add ht2).add ht3).add ht4).sub
      (((hr1.add hr2).add hr3).add hr4)
  obtain ⟨w, hw⟩ := hrest
  have hp4prod : h0 ^ 4 ∣ (p.coeff 4).derivative * q.coeff 1 := by
    refine ⟨-w, ?_⟩
    calc
      (p.coeff 4).derivative * q.coeff 1 =
          -(((((p.coeff 3).derivative * (q.coeff 2 * (2 : k[X])) +
            (p.coeff 2).derivative * (q.coeff 3 * (3 : k[X]))) +
            (p.coeff 1).derivative * (q.coeff 4 * (4 : k[X]))) +
            (p.coeff 0).derivative * (q.coeff 5 * (5 : k[X]))) -
          ((((p.coeff 4 * (4 : k[X])) * (q.coeff 1).derivative +
            (p.coeff 3 * (3 : k[X])) * (q.coeff 2).derivative) +
            (p.coeff 2 * (2 : k[X])) * (q.coeff 3).derivative) +
            p.coeff 1 * (q.coeff 4).derivative)) := by
              linear_combination hrow
      _ = h0 ^ 4 * (-w) := by rw [hw]; ring
  have hp4d4 : h0 ^ 4 ∣ (p.coeff 4).derivative :=
    linearPolynomial_pow_dvd_mul_cancel_right_410 h0
      (p.coeff 4).derivative (q.coeff 1) a 4 hdegree hroot hq1nz hp4prod
  have hp4eq : p.coeff 4 = h0 ^ 4 := by
    rw [hp4, hH]
    ring
  rw [hp4eq] at hp4d4
  exact linearPolynomial_fourthPower_derivative_not_four_dvd_410 h0 a
    hdegree hroot hp4d4

end Max11DegreeRoutes
