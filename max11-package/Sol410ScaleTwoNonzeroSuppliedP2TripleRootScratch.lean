import Sol410ScaleTwoNonzeroSuppliedP1TripleRootScratch

/-!
# The degree-two coefficient gains a third supplied factor

With `p₁` already carrying `h₀³`, the literal degree-two Keller row has a
unique order-one term: `p₂' q₁`.  Every other term carries `h₀²`; the
degree-zero row keeps `q₁` invertible at the supplied root.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option linter.unusedSectionVars false

set_option maxHeartbeats 64000000 in
theorem nonzeroFace410_linearRoot_suppliedP2TripleRoot
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
    h0 ^ 3 ∣ p.coeff 2 := by
  have hp1cube := nonzeroFace410_linearRoot_suppliedP1TripleRoot p q H h0
    j lambda a hp hq hh0 hdegree hH hp4 hq10 hN hD hroot hlambda hj
  obtain ⟨p13, hp13⟩ := hp1cube
  have hp1cube' : h0 ^ 3 ∣ p.coeff 1 := ⟨p13, hp13⟩
  obtain ⟨t2, a22, s22, vis, w73, q54, b44, b33, q22, hp3, hp2,
      hq8, hq7, hq6, hq5, hq4, hq3, hq2⟩ :=
    nonzeroFace410_linearRoot_suppliedGroundDoubleRoot p q H h0 j lambda a
      hp hq hh0 hdegree hH hp4 hq10 hN hD hroot hlambda
  have hp1d2 : h0 ^ 2 ∣ (p.coeff 1).derivative := by
    refine ⟨(3 : k[X]) * h0.derivative * p13 + h0 * p13.derivative, ?_⟩
    rw [hp13]
    simp only [derivative_mul, derivative_pow]
    rw [Polynomial.C_eq_natCast]
    ring
  have hq3d2 : h0 ^ 2 ∣ q.coeff 3 := by
    refine ⟨h0 * b33, ?_⟩
    rw [hq3]
    ring
  have hp3d2 : h0 ^ 2 ∣ p.coeff 3 := by
    refine ⟨h0 * t2, ?_⟩
    rw [hp3]
    ring
  have hp2sq : h0 ^ 2 ∣ p.coeff 2 := ⟨a22, hp2⟩
  have hp1sq : h0 ^ 2 ∣ p.coeff 1 := by
    have hpow : h0 ^ 2 ∣ h0 ^ 3 := by
      refine ⟨h0, ?_⟩
      ring
    exact hpow.trans hp1cube'
  have ha1 : (p.coeff 1).eval a = 0 := by
    rw [hp13, eval_mul, eval_pow, hroot]
    norm_num
  have hkelP := iotaZeroBranch_kellerRowZero410 p q j a hp hq hD ha1
  have hq1nz := (iotaZeroBranch_kellerUnits410
    ((p.coeff 0).derivative.eval a) ((q.coeff 1).eval a) j hj hkelP).2
  have hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j) := by
    simpa [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hD
  have hrow := eleventhCoefficientJacobianRow_410 hp hq hjac
  have hC2 : Polynomial.C (2 : k) = (2 : k[X]) :=
    Polynomial.C_eq_natCast 2
  have hC3 : Polynomial.C (3 : k) = (3 : k[X]) :=
    Polynomial.C_eq_natCast 3
  rw [hC2, hC3] at hrow
  have hterm1 : h0 ^ 2 ∣
      (p.coeff 1).derivative * (q.coeff 2 * (2 : k[X])) :=
    dvd_mul_of_dvd_left hp1d2 _
  have hterm2 : h0 ^ 2 ∣
      (p.coeff 0).derivative * (q.coeff 3 * (3 : k[X])) :=
    dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hq3d2 _) _
  have hterm3 : h0 ^ 2 ∣
      (p.coeff 3 * (3 : k[X])) * (q.coeff 0).derivative :=
    dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hp3d2 _) _
  have hterm4 : h0 ^ 2 ∣
      (p.coeff 2 * (2 : k[X])) * (q.coeff 1).derivative :=
    dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hp2sq _) _
  have hterm5 : h0 ^ 2 ∣
      p.coeff 1 * (q.coeff 2).derivative :=
    dvd_mul_of_dvd_left hp1sq _
  have hrest : h0 ^ 2 ∣
      ((p.coeff 1).derivative * (q.coeff 2 * (2 : k[X])) +
        (p.coeff 0).derivative * (q.coeff 3 * (3 : k[X]))) -
      (((p.coeff 3 * (3 : k[X])) * (q.coeff 0).derivative +
        (p.coeff 2 * (2 : k[X])) * (q.coeff 1).derivative) +
        p.coeff 1 * (q.coeff 2).derivative) :=
    (hterm1.add hterm2).sub ((hterm3.add hterm4).add hterm5)
  obtain ⟨w, hw⟩ := hrest
  have hp2prod : h0 ^ 2 ∣ (p.coeff 2).derivative * q.coeff 1 := by
    refine ⟨-w, ?_⟩
    calc
      (p.coeff 2).derivative * q.coeff 1 =
          -(((p.coeff 1).derivative * (q.coeff 2 * (2 : k[X])) +
              (p.coeff 0).derivative * (q.coeff 3 * (3 : k[X]))) -
            (((p.coeff 3 * (3 : k[X])) * (q.coeff 0).derivative +
              (p.coeff 2 * (2 : k[X])) * (q.coeff 1).derivative) +
              p.coeff 1 * (q.coeff 2).derivative)) := by
            linear_combination hrow
      _ = h0 ^ 2 * (-w) := by rw [hw]; ring
  have hp2dsq : h0 ^ 2 ∣ (p.coeff 2).derivative :=
    linearPolynomial_pow_dvd_mul_cancel_right_410 h0
      (p.coeff 2).derivative (q.coeff 1) a 2 hdegree hroot hq1nz hp2prod
  exact linearPolynomial_cube_dvd_of_sq_dvd_derivative_410 h0
    (p.coeff 2) a hdegree hroot hp2sq hp2dsq

end Max11DegreeRoutes
