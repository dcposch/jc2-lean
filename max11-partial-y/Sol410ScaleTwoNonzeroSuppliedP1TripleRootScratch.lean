import Sol410ScaleTwoNonzeroSuppliedP1DoubleRootScratch

/-!
# The degree-one Keller row promotes `p₁` to a triple supplied root

After `p₁`, `p₂`, and `q₂` all acquire an `h₀²` factor, the literal
degree-one Keller row puts `h₀²` into `p₁' q₁`.  The degree-zero row and
the nonzero Jacobian make `q₁` a unit at the supplied root, so the factor
cancels and `p₁` gains one further `h₀`.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false

/-- A polynomial with a double linear factor whose derivative still has the
same double factor has a triple factor. -/
theorem linearPolynomial_cube_dvd_of_sq_dvd_derivative_410
    (h f : k[X]) (a : k) (hdegree : h.natDegree = 1)
    (hroot : h.eval a = 0) (hf : h ^ 2 ∣ f)
    (hfd : h ^ 2 ∣ f.derivative) :
    h ^ 3 ∣ f := by
  obtain ⟨u, hu⟩ := hf
  obtain ⟨v, hv⟩ := hfd
  obtain ⟨c, hc, d, hlinear⟩ := Polynomial.natDegree_eq_one.mp hdegree
  have hprime : h.derivative.eval a = c := by
    rw [← hlinear]
    simp
  have hsecond0 : f.derivative.derivative.eval a = 0 := by
    rw [hv, pow_two]
    simp [derivative_mul, hroot]
  have hsecond : f.derivative.derivative.eval a =
      (2 : k) * (h.derivative.eval a) ^ 2 * u.eval a := by
    have hformula : derivative (derivative (h ^ 2 * u)) =
        (2 : k[X]) * h.derivative ^ 2 * u +
          (2 : k[X]) * h * h.derivative.derivative * u +
          (4 : k[X]) * h * h.derivative * u.derivative +
          h ^ 2 * u.derivative.derivative := by
      simp only [pow_two, derivative_add, derivative_mul, derivative_ofNat]
      ring
    calc
      f.derivative.derivative.eval a =
          (derivative (derivative (h ^ 2 * u))).eval a := by rw [hu]
      _ = ((2 : k[X]) * h.derivative ^ 2 * u +
          (2 : k[X]) * h * h.derivative.derivative * u +
          (4 : k[X]) * h * h.derivative * u.derivative +
          h ^ 2 * u.derivative.derivative).eval a := by rw [hformula]
      _ = (2 : k) * (h.derivative.eval a) ^ 2 * u.eval a := by
        simp [hroot]
  have hu0 : u.eval a = 0 := by
    rw [hsecond] at hsecond0
    have hcoef : (2 : k) * (h.derivative.eval a) ^ 2 ≠ 0 := by
      rw [hprime]
      exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hc)
    exact (mul_eq_zero.mp hsecond0).resolve_left hcoef
  obtain ⟨w, hw⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_410 h u a hdegree hroot hu0
  refine ⟨w, ?_⟩
  rw [hu, hw]
  ring

/-- At the supplied root, a nonvanishing right factor is coprime to every
power of the exact degree-one polynomial and can be cancelled. -/
theorem linearPolynomial_pow_dvd_mul_cancel_right_410
    [IsAlgClosed k] (h f u : k[X]) (a : k) (n : ℕ)
    (hdegree : h.natDegree = 1) (hroot : h.eval a = 0)
    (hu : u.eval a ≠ 0) (hdiv : h ^ n ∣ f * u) :
    h ^ n ∣ f := by
  obtain ⟨c, hc, d, hlinear⟩ := Polynomial.natDegree_eq_one.mp hdegree
  have hca : c * a + d = 0 := by simpa [← hlinear] using hroot
  have hd : d = -(c * a) := by linear_combination hca
  have hfactor : h = C c * (X - C a) := by
    calc
      h = C c * X + C d := hlinear.symm
      _ = C c * X - C (c * a) := by rw [hd, map_neg]; ring
      _ = C c * (X - C a) := by rw [mul_sub, ← map_mul]
  have hcop : IsCoprime h u := by
    rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed (k := k) k]
    intro z
    rw [aeval_def, aeval_def]
    by_cases hz : z = a
    · right
      simpa [hz] using hu
    · left
      rw [hfactor]
      simpa [Polynomial.eval₂_mul, Polynomial.eval₂_C,
        Polynomial.eval₂_sub, Polynomial.eval₂_X] using
        mul_ne_zero hc (sub_ne_zero.mpr hz)
  exact hcop.pow_left.dvd_of_dvd_mul_right hdiv

set_option maxHeartbeats 64000000 in
theorem nonzeroFace410_linearRoot_suppliedP1TripleRoot
    [IsAlgClosed k]
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
    h0 ^ 3 ∣ p.coeff 1 := by
  have hp1sq := nonzeroFace410_linearRoot_suppliedP1DoubleRoot p q H h0
    j lambda a hp hq hh0 hdegree hH hp4 hq10 hN hD hroot hlambda hj
  obtain ⟨p12, hp12⟩ := hp1sq
  have hp1sq' : h0 ^ 2 ∣ p.coeff 1 := ⟨p12, hp12⟩
  obtain ⟨t2, a22, s22, vis, w73, q54, b44, b33, q22, hp3, hp2,
      hq8, hq7, hq6, hq5, hq4, hq3, hq2⟩ :=
    nonzeroFace410_linearRoot_suppliedGroundDoubleRoot p q H h0 j lambda a
      hp hq hh0 hdegree hH hp4 hq10 hN hD hroot hlambda
  have ha1 : (p.coeff 1).eval a = 0 := by
    rw [hp12, eval_mul, eval_pow, hroot]
    norm_num
  have hkelP := iotaZeroBranch_kellerRowZero410 p q j a hp hq hD ha1
  have hq1nz := (iotaZeroBranch_kellerUnits410
    ((p.coeff 0).derivative.eval a) ((q.coeff 1).eval a) j hj hkelP).2
  have hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j) := by
    simpa [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hD
  have hrow := twelfthCoefficientJacobianRow_410 hp hq hjac
  have hC2 : Polynomial.C (2 : k) = (2 : k[X]) :=
    Polynomial.C_eq_natCast 2
  rw [hC2] at hrow
  have hprod : h0 ^ 2 ∣ (p.coeff 1).derivative * q.coeff 1 := by
    refine ⟨(a22 * (2 : k[X])) * (q.coeff 0).derivative +
        p12 * (q.coeff 1).derivative -
        (p.coeff 0).derivative * (q22 * (2 : k[X])), ?_⟩
    rw [hp12, hp2, hq2] at hrow
    rw [hp12]
    linear_combination hrow
  have hp1dsq : h0 ^ 2 ∣ (p.coeff 1).derivative :=
    linearPolynomial_pow_dvd_mul_cancel_right_410 h0
      (p.coeff 1).derivative (q.coeff 1) a 2 hdegree hroot hq1nz hprod
  exact linearPolynomial_cube_dvd_of_sq_dvd_derivative_410 h0
    (p.coeff 1) a hdegree hroot hp1sq' hp1dsq

end Max11DegreeRoutes
