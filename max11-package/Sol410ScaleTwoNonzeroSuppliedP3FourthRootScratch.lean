import Sol410ScaleTwoNonzeroSuppliedP2TripleRootScratch

/-!
# The degree-three coefficient gains a fourth supplied factor

The literal degree-three Keller row now has a unique order-two term,
`p₃' q₁`.  All seven remaining terms carry `h₀³`, so cancellation of the
root-unit `q₁` promotes `p₃` from order three to order four.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option linter.unusedSectionVars false

theorem linearPolynomial_four_dvd_of_cube_dvd_derivative_410
    (h f : k[X]) (a : k) (hdegree : h.natDegree = 1)
    (hroot : h.eval a = 0) (hf : h ^ 3 ∣ f)
    (hfd : h ^ 3 ∣ f.derivative) :
    h ^ 4 ∣ f := by
  obtain ⟨u, hu⟩ := hf
  obtain ⟨v, hv⟩ := hfd
  have hh : h ≠ 0 := by
    intro hz
    rw [hz, Polynomial.natDegree_zero] at hdegree
    exact zero_ne_one hdegree
  obtain ⟨c, hc, d, hlinear⟩ := Polynomial.natDegree_eq_one.mp hdegree
  have hprime : h.derivative.eval a = c := by
    rw [← hlinear]
    simp
  have hder : f.derivative = h ^ 2 *
      ((3 : k[X]) * h.derivative * u + h * u.derivative) := by
    rw [hu]
    simp only [derivative_mul, derivative_pow]
    rw [Polynomial.C_eq_natCast]
    ring
  have heq : h ^ 2 *
        ((3 : k[X]) * h.derivative * u + h * u.derivative) =
      h ^ 2 * (h * v) := by
    calc
      h ^ 2 * ((3 : k[X]) * h.derivative * u + h * u.derivative) =
          f.derivative := hder.symm
      _ = h ^ 3 * v := hv
      _ = h ^ 2 * (h * v) := by ring
  have hcancel : (3 : k[X]) * h.derivative * u + h * u.derivative =
      h * v := mul_left_cancel₀ (pow_ne_zero 2 hh) heq
  have heval := congrArg (fun r : k[X] => r.eval a) hcancel
  simp only [eval_add, eval_mul, eval_ofNat, hroot, zero_mul, add_zero]
    at heval
  have hu0 : u.eval a = 0 := by
    have hcoef : (3 : k) * h.derivative.eval a ≠ 0 := by
      rw [hprime]
      exact mul_ne_zero (by norm_num) hc
    exact (mul_eq_zero.mp heval).resolve_left hcoef
  obtain ⟨w, hw⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_410 h u a hdegree hroot hu0
  refine ⟨w, ?_⟩
  rw [hu, hw]
  ring

set_option maxHeartbeats 64000000 in
theorem nonzeroFace410_linearRoot_suppliedP3FourthRoot
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
    h0 ^ 4 ∣ p.coeff 3 := by
  have hp1cube := nonzeroFace410_linearRoot_suppliedP1TripleRoot p q H h0
    j lambda a hp hq hh0 hdegree hH hp4 hq10 hN hD hroot hlambda hj
  obtain ⟨p13, hp13⟩ := hp1cube
  have hp1cube' : h0 ^ 3 ∣ p.coeff 1 := ⟨p13, hp13⟩
  have hp2cube := nonzeroFace410_linearRoot_suppliedP2TripleRoot p q H h0
    j lambda a hp hq hh0 hdegree hH hp4 hq10 hN hD hroot hlambda hj
  obtain ⟨p23, hp23⟩ := hp2cube
  have hp2cube' : h0 ^ 3 ∣ p.coeff 2 := ⟨p23, hp23⟩
  obtain ⟨t2, a22, s22, vis, w73, q54, b44, b33, q22, hp3, hp2,
      hq8, hq7, hq6, hq5, hq4, hq3, hq2⟩ :=
    nonzeroFace410_linearRoot_suppliedGroundDoubleRoot p q H h0 j lambda a
      hp hq hh0 hdegree hH hp4 hq10 hN hD hroot hlambda
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
  have hq2sq : h0 ^ 2 ∣ q.coeff 2 := ⟨q22, hq2⟩
  have hq3cube : h0 ^ 3 ∣ q.coeff 3 := ⟨b33, hq3⟩
  have hq4cube : h0 ^ 3 ∣ q.coeff 4 := by
    refine ⟨h0 * b44, ?_⟩
    rw [hq4]
    ring
  have hp4cube : h0 ^ 3 ∣ p.coeff 4 := by
    refine ⟨h0, ?_⟩
    rw [hp4, hH]
    ring
  have hp3cube : h0 ^ 3 ∣ p.coeff 3 := ⟨t2, hp3⟩
  have hsquareMul : ∀ f g : k[X], h0 ^ 2 ∣ f → h0 ^ 2 ∣ g →
      h0 ^ 3 ∣ f * g := by
    intro f g hf hg
    obtain ⟨u, hu⟩ := hf
    obtain ⟨v, hv⟩ := hg
    refine ⟨h0 * u * v, ?_⟩
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
  have hrow := tenthCoefficientJacobianRow_410 hp hq hjac
  have hC2 : Polynomial.C (2 : k) = (2 : k[X]) :=
    Polynomial.C_eq_natCast 2
  have hC3 : Polynomial.C (3 : k) = (3 : k[X]) :=
    Polynomial.C_eq_natCast 3
  have hC4 : Polynomial.C (4 : k) = (4 : k[X]) :=
    Polynomial.C_eq_natCast 4
  rw [hC2, hC3, hC4] at hrow
  have ht1 : h0 ^ 3 ∣
      (p.coeff 2).derivative * (q.coeff 2 * (2 : k[X])) :=
    by simpa only [mul_assoc] using
      dvd_mul_of_dvd_left (hsquareMul _ _ hp2d2 hq2sq) (2 : k[X])
  have ht2 : h0 ^ 3 ∣
      (p.coeff 1).derivative * (q.coeff 3 * (3 : k[X])) :=
    by
      have hq3sq : h0 ^ 2 ∣ q.coeff 3 := by
        have hpow : h0 ^ 2 ∣ h0 ^ 3 := ⟨h0, by ring⟩
        exact hpow.trans hq3cube
      simpa only [mul_assoc] using
        dvd_mul_of_dvd_left (hsquareMul _ _ hp1d2 hq3sq) (3 : k[X])
  have ht3 : h0 ^ 3 ∣
      (p.coeff 0).derivative * (q.coeff 4 * (4 : k[X])) :=
    dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hq4cube _) _
  have hr1 : h0 ^ 3 ∣
      (p.coeff 4 * (4 : k[X])) * (q.coeff 0).derivative :=
    dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hp4cube _) _
  have hr2 : h0 ^ 3 ∣
      (p.coeff 3 * (3 : k[X])) * (q.coeff 1).derivative :=
    dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hp3cube _) _
  have hr3 : h0 ^ 3 ∣
      (p.coeff 2 * (2 : k[X])) * (q.coeff 2).derivative :=
    dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hp2cube' _) _
  have hr4 : h0 ^ 3 ∣ p.coeff 1 * (q.coeff 3).derivative :=
    dvd_mul_of_dvd_left hp1cube' _
  have hrest : h0 ^ 3 ∣
      (((p.coeff 2).derivative * (q.coeff 2 * (2 : k[X])) +
        (p.coeff 1).derivative * (q.coeff 3 * (3 : k[X]))) +
        (p.coeff 0).derivative * (q.coeff 4 * (4 : k[X]))) -
      ((((p.coeff 4 * (4 : k[X])) * (q.coeff 0).derivative +
        (p.coeff 3 * (3 : k[X])) * (q.coeff 1).derivative) +
        (p.coeff 2 * (2 : k[X])) * (q.coeff 2).derivative) +
        p.coeff 1 * (q.coeff 3).derivative) :=
    ((ht1.add ht2).add ht3).sub (((hr1.add hr2).add hr3).add hr4)
  obtain ⟨w, hw⟩ := hrest
  have hp3prod : h0 ^ 3 ∣ (p.coeff 3).derivative * q.coeff 1 := by
    refine ⟨-w, ?_⟩
    calc
      (p.coeff 3).derivative * q.coeff 1 =
          -(((((p.coeff 2).derivative * (q.coeff 2 * (2 : k[X])) +
            (p.coeff 1).derivative * (q.coeff 3 * (3 : k[X]))) +
            (p.coeff 0).derivative * (q.coeff 4 * (4 : k[X]))) -
          ((((p.coeff 4 * (4 : k[X])) * (q.coeff 0).derivative +
            (p.coeff 3 * (3 : k[X])) * (q.coeff 1).derivative) +
            (p.coeff 2 * (2 : k[X])) * (q.coeff 2).derivative) +
            p.coeff 1 * (q.coeff 3).derivative))) := by
              linear_combination hrow
      _ = h0 ^ 3 * (-w) := by rw [hw]; ring
  have hp3d3 : h0 ^ 3 ∣ (p.coeff 3).derivative :=
    linearPolynomial_pow_dvd_mul_cancel_right_410 h0
      (p.coeff 3).derivative (q.coeff 1) a 3 hdegree hroot hq1nz hp3prod
  exact linearPolynomial_four_dvd_of_cube_dvd_derivative_410 h0
    (p.coeff 3) a hdegree hroot hp3cube hp3d3

end Max11DegreeRoutes
