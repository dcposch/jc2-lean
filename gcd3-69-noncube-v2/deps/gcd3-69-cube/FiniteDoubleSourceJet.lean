import FiniteDoubleSource

/-! # Polynomial jets of the source values at a moving double root

The second-blowup chart is written in `K[X]` with `Q = X`.  Below the
weight-one load, the cubic and the transverse quadratic both vanish through
order one, so the sextic source value starts at order three and the nonic
source value starts at order four.  This file records those two leading
coefficients.
-/

noncomputable section
open Polynomial

/-- Coefficient 3 of the sextic Faber value on the moving double-root chart
is the displayed linear form in the first correction of the root. -/
theorem GCD369CubeFaberSixDoubleSourceJet_coeff3
    {K : Type*} [Field K] [CharZero K]
    (r A d B B2 C2 x1 x2 : K) :
    let Q : K[X] := X
    let q : ℚ →+* K[X] := C.comp (algebraMap ℚ K)
    let U : K[X] := C (-3 * r ^ 2) + Q ^ 2 * C d
    let V : K[X] :=
      C (2 * r ^ 3) - Q ^ 2 * C (algebraMap ℚ K (2 / 3) * d * r)
    let Xn : K[X] := C A
    let Yn : K[X] := C (r * A) + Q * C B + Q ^ 2 * C B2
    let Zn : K[X] :=
      C (-2 * r ^ 2 * A) - Q * C (r * B) + Q ^ 2 * C C2
    let a2 : K[X] := U ^ 2 + Q ^ 2 * Xn
    let a1 : K[X] := 2 * U * V + Q ^ 2 * Yn
    let a0 : K[X] := V ^ 2 + Q ^ 2 * Zn
    let x : K[X] := C r + Q * C x1 + Q ^ 2 * C x2
    (GCD369CubeFaberSixValueQ q a0 a1 a2 (2 * V) (2 * U) x).coeff 3 =
      3 * A * r * x1 := by
  dsimp only
  set Q : K[X] := X
  set q : ℚ →+* K[X] := C.comp (algebraMap ℚ K)
  set U : K[X] := C (-3 * r ^ 2) + Q ^ 2 * C d
  set V : K[X] :=
    C (2 * r ^ 3) - Q ^ 2 * C (algebraMap ℚ K (2 / 3) * d * r)
  set Xn : K[X] := C A
  set Yn : K[X] := C (r * A) + Q * C B + Q ^ 2 * C B2
  set Zn : K[X] :=
    C (-2 * r ^ 2 * A) - Q * C (r * B) + Q ^ 2 * C C2
  set a2 : K[X] := U ^ 2 + Q ^ 2 * Xn
  set a1 : K[X] := 2 * U * V + Q ^ 2 * Yn
  set a0 : K[X] := V ^ 2 + Q ^ 2 * Zn
  set x : K[X] := C r + Q * C x1 + Q ^ 2 * C x2
  set Kval : K[X] := x ^ 3 + U * x + V
  set Phi : K[X] := Xn * x ^ 2 + Yn * x + Zn
  have hcoeff1 (p : K[X]) : p.coeff 1 = p.derivative.eval 0 := by
    rw [← coeff_zero_eq_eval_zero, coeff_derivative]
    ring
  have hexp :
      GCD369CubeFaberSixValueQ q a0 a1 a2 (2 * V) (2 * U) x =
        Kval ^ 2 + Q ^ 2 * Phi := by
    simp only [GCD369CubeFaberSixValueQ, Kval, Phi, a0, a1, a2]
    ring
  have hx0 : x.eval 0 = r := by
    simp [x, Q, eval_add, eval_mul, eval_pow, eval_C, eval_X]
  have hx1 : x.derivative.eval 0 = x1 := by
    simp [x, Q, derivative_add, derivative_sub, derivative_mul, derivative_C,
      derivative_X, derivative_pow, eval_add, eval_mul, eval_pow, eval_C,
      eval_X]
  have hU0 : U.eval 0 = -3 * r ^ 2 := by
    simp [U, Q, eval_add, eval_mul, eval_pow, eval_C, eval_X]
  have hU1 : U.derivative.eval 0 = 0 := by
    simp [U, Q, derivative_add, derivative_mul, derivative_C, derivative_X,
      derivative_pow, eval_add, eval_mul, eval_pow, eval_C, eval_X]
  have hV1 : V.derivative.eval 0 = 0 := by
    simp [V, Q, derivative_add, derivative_sub, derivative_mul, derivative_C,
      derivative_X, derivative_pow, eval_add, eval_mul, eval_pow, eval_C,
      eval_X]
  have hXn0 : Xn.eval 0 = A := by
    simp [Xn]
  have hXn1 : Xn.derivative.eval 0 = 0 := by
    simp [Xn]
  have hYn0 : Yn.eval 0 = r * A := by
    simp [Yn, Q, eval_add, eval_mul, eval_pow, eval_C, eval_X]
  have hYn1 : Yn.derivative.eval 0 = B := by
    simp [Yn, Q, derivative_add, derivative_mul, derivative_C, derivative_X,
      derivative_pow, eval_add, eval_mul, eval_pow, eval_C, eval_X]
  have hZn1 : Zn.derivative.eval 0 = -(r * B) := by
    simp [Zn, Q, derivative_add, derivative_sub, derivative_mul, derivative_C,
      derivative_X, derivative_pow, eval_add, eval_mul, eval_pow, eval_C,
      eval_X]
  have hK0 : Kval.coeff 0 = 0 := by
    dsimp [Kval]
    rw [coeff_zero_eq_eval_zero, eval_add, eval_add, eval_pow, eval_mul]
    rw [hx0, hU0]
    simp [V, Q, eval_sub, eval_add, eval_mul, eval_pow, eval_C, eval_X]
    ring
  have hK1 : Kval.coeff 1 = 0 := by
    rw [hcoeff1]
    dsimp [Kval]
    rw [derivative_add, derivative_add, derivative_pow, derivative_mul]
    simp [eval_add, eval_mul, eval_pow, eval_C, hx0, hx1, hU0, hU1, hV1]
  have hKdiv : X ^ 2 ∣ Kval := by
    rw [X_pow_dvd_iff]
    intro n hn
    interval_cases n
    · exact hK0
    · exact hK1
  have hKsq : (Kval ^ 2).coeff 3 = 0 := by
    have hpow : X ^ 4 ∣ Kval ^ 2 := by
      have h := pow_dvd_pow_of_dvd hKdiv 2
      have hX : (X ^ 2) ^ 2 = (X : K[X]) ^ 4 := by ring
      rwa [hX] at h
    exact (X_pow_dvd_iff.mp hpow) 3 (by norm_num)
  have hPhi1 : Phi.coeff 1 = 3 * A * r * x1 := by
    rw [hcoeff1]
    dsimp [Phi]
    rw [derivative_add, derivative_add, derivative_mul, derivative_mul,
      derivative_sq]
    simp [eval_add, eval_mul, eval_pow, eval_C, hx0, hx1, hXn0, hXn1, hYn0,
      hYn1, hZn1]
    ring
  rw [hexp, coeff_add, hKsq, zero_add]
  have hQ : Q = (X : K[X]) := rfl
  rw [hQ, show (3 : ℕ) = 1 + 2 from rfl, coeff_X_pow_mul, hPhi1]

/-- With vanishing first root correction, coefficient 4 of the ninth Faber
value on the same chart is the displayed quadratic residue. -/
theorem GCD369CubeFaberNineDoubleSourceJet_coeff4
    {K : Type*} [Field K] [CharZero K]
    (r A d B B2 C2 x2 : K) :
    let Q : K[X] := X
    let q : ℚ →+* K[X] := C.comp (algebraMap ℚ K)
    let U : K[X] := C (-3 * r ^ 2) + Q ^ 2 * C d
    let V : K[X] :=
      C (2 * r ^ 3) - Q ^ 2 * C (algebraMap ℚ K (2 / 3) * d * r)
    let Xn : K[X] := C A
    let Yn : K[X] := C (r * A) + Q * C B + Q ^ 2 * C B2
    let Zn : K[X] :=
      C (-2 * r ^ 2 * A) - Q * C (r * B) + Q ^ 2 * C C2
    let a2 : K[X] := U ^ 2 + Q ^ 2 * Xn
    let a1 : K[X] := 2 * U * V + Q ^ 2 * Yn
    let a0 : K[X] := V ^ 2 + Q ^ 2 * Zn
    let x : K[X] := C r + Q * C (0 : K) + Q ^ 2 * C x2
    (GCD369CubeFaberNineValueQ q a0 a1 a2 (2 * V) (2 * U) x).coeff 4 =
      algebraMap ℚ K (9 / 8) * A ^ 2 * r := by
  dsimp only
  set Q : K[X] := X
  set q : ℚ →+* K[X] := C.comp (algebraMap ℚ K)
  set U : K[X] := C (-3 * r ^ 2) + Q ^ 2 * C d
  set V : K[X] :=
    C (2 * r ^ 3) - Q ^ 2 * C (algebraMap ℚ K (2 / 3) * d * r)
  set Xn : K[X] := C A
  set Yn : K[X] := C (r * A) + Q * C B + Q ^ 2 * C B2
  set Zn : K[X] :=
    C (-2 * r ^ 2 * A) - Q * C (r * B) + Q ^ 2 * C C2
  set a2 : K[X] := U ^ 2 + Q ^ 2 * Xn
  set a1 : K[X] := 2 * U * V + Q ^ 2 * Yn
  set a0 : K[X] := V ^ 2 + Q ^ 2 * Zn
  set x : K[X] := C r + Q * C (0 : K) + Q ^ 2 * C x2
  set Kval : K[X] := x ^ 3 + U * x + V
  set Phi : K[X] := Xn * x ^ 2 + Yn * x + Zn
  have hcoeff1 (p : K[X]) : p.coeff 1 = p.derivative.eval 0 := by
    rw [← coeff_zero_eq_eval_zero, coeff_derivative]
    ring
  have hexact :=
    GCD369CubeFaberNineCommonNormalExactQ (R := K[X]) q Xn Yn Zn U V
      (Q ^ 2) x
  dsimp only [a0, a1, a2]
  rw [hexact]
  have hx0 : x.eval 0 = r := by
    simp [x, Q, eval_add, eval_mul, eval_pow, eval_C, eval_X]
  have hx1 : x.derivative.eval 0 = (0 : K) := by
    simp [x, Q, derivative_add, derivative_mul, derivative_C, derivative_X,
      derivative_pow, eval_add, eval_mul, eval_pow, eval_C, eval_X]
  have hU0 : U.eval 0 = -3 * r ^ 2 := by
    simp [U, Q, eval_add, eval_mul, eval_pow, eval_C, eval_X]
  have hU1 : U.derivative.eval 0 = 0 := by
    simp [U, Q, derivative_add, derivative_mul, derivative_C, derivative_X,
      derivative_pow, eval_add, eval_mul, eval_pow, eval_C, eval_X]
  have hV1 : V.derivative.eval 0 = 0 := by
    simp [V, Q, derivative_add, derivative_sub, derivative_mul, derivative_C,
      derivative_X, derivative_pow, eval_add, eval_mul, eval_pow, eval_C,
      eval_X]
  have hXn0 : Xn.eval 0 = A := by
    simp [Xn]
  have hXn1 : Xn.derivative.eval 0 = 0 := by
    simp [Xn]
  have hYn0 : Yn.eval 0 = r * A := by
    simp [Yn, Q, eval_add, eval_mul, eval_pow, eval_C, eval_X]
  have hYn1 : Yn.derivative.eval 0 = B := by
    simp [Yn, Q, derivative_add, derivative_mul, derivative_C, derivative_X,
      derivative_pow, eval_add, eval_mul, eval_pow, eval_C, eval_X]
  have hZn1 : Zn.derivative.eval 0 = -(r * B) := by
    simp [Zn, Q, derivative_add, derivative_sub, derivative_mul, derivative_C,
      derivative_X, derivative_pow, eval_add, eval_mul, eval_pow, eval_C,
      eval_X]
  have hK0 : Kval.coeff 0 = 0 := by
    dsimp [Kval]
    rw [coeff_zero_eq_eval_zero, eval_add, eval_add, eval_pow, eval_mul]
    rw [hx0, hU0]
    simp [V, Q, eval_sub, eval_add, eval_mul, eval_pow, eval_C, eval_X]
    ring
  have hK1 : Kval.coeff 1 = 0 := by
    rw [hcoeff1]
    dsimp [Kval]
    rw [derivative_add, derivative_add, derivative_pow, derivative_mul]
    simp [eval_add, eval_mul, eval_pow, eval_C, hx0, hx1, hU0, hU1, hV1]
  have hPhi0 : Phi.coeff 0 = 0 := by
    dsimp [Phi]
    rw [coeff_zero_eq_eval_zero, eval_add, eval_add, eval_mul, eval_mul,
      eval_pow]
    simp [hx0, hXn0, hYn0, Zn, Q, eval_add, eval_sub, eval_mul, eval_pow,
      eval_C, eval_X]
    ring
  have hPhi1 : Phi.coeff 1 = 0 := by
    rw [hcoeff1]
    dsimp [Phi]
    rw [derivative_add, derivative_add, derivative_mul, derivative_mul,
      derivative_sq]
    simp [eval_add, eval_mul, eval_pow, eval_C, hx0, hx1, hXn0, hXn1, hYn0,
      hYn1, hZn1]
    ring
  have hKdiv : X ^ 2 ∣ Kval := by
    rw [X_pow_dvd_iff]
    intro n hn
    interval_cases n
    · exact hK0
    · exact hK1
  have hPhidiv : X ^ 2 ∣ Phi := by
    rw [X_pow_dvd_iff]
    intro n hn
    interval_cases n
    · exact hPhi0
    · exact hPhi1
  have hQ : Q = (X : K[X]) := rfl
  have hKcube : ((x ^ 3 + U * x + V) ^ 3).coeff 4 = 0 := by
    change (Kval ^ 3).coeff 4 = 0
    have hpow : X ^ 6 ∣ Kval ^ 3 := by
      have h := pow_dvd_pow_of_dvd hKdiv 3
      have hX : (X ^ 2) ^ 3 = (X : K[X]) ^ 6 := by ring
      rwa [hX] at h
    exact (X_pow_dvd_iff.mp hpow) 4 (by norm_num)
  have hmid :
      (q (3 / 2) * (x ^ 3 + U * x + V) *
        (Xn * x ^ 2 + Yn * x + Zn) * Q ^ 2).coeff 4 = 0 := by
    change (q (3 / 2) * Kval * Phi * Q ^ 2).coeff 4 = 0
    have hprod : X ^ 6 ∣ Kval * Phi * X ^ 2 := by
      have hX : X ^ 2 * X ^ 2 * X ^ 2 = (X : K[X]) ^ 6 := by ring
      have hmul :=
        mul_dvd_mul (mul_dvd_mul hKdiv hPhidiv) (dvd_refl (X ^ 2))
      rwa [hX] at hmul
    have hdiv : X ^ 6 ∣ q (3 / 2) * Kval * Phi * Q ^ 2 := by
      rw [hQ]
      convert dvd_mul_of_dvd_right hprod (q (3 / 2)) using 1
      ring
    exact (X_pow_dvd_iff.mp hdiv) 4 (by norm_num)
  have hlast :
      (q (3 / 8) * Xn * (Xn * x + 2 * Yn) * (Q ^ 2) ^ 2).coeff 4 =
        algebraMap ℚ K (9 / 8) * A ^ 2 * r := by
    have hpow : (Q ^ 2) ^ 2 = (X : K[X]) ^ 4 := by
      rw [hQ]; ring
    rw [hpow, show (4 : ℕ) = 0 + 4 from rfl, coeff_mul_X_pow]
    rw [coeff_zero_eq_eval_zero, eval_mul, eval_mul, eval_add, eval_mul]
    have hq0 : (q (3 / 8)).eval 0 = algebraMap ℚ K (3 / 8) := by
      dsimp [q]; simp [eval_C]
    have h2Yn : eval 0 ((2 : K[X]) * Yn) = 2 * (r * A) := by
      simp [eval_mul, hYn0]
    rw [hq0, hXn0, hx0, h2Yn]
    have hscalar :
        algebraMap ℚ K (3 / 8) * A * (A * r + 2 * (r * A)) =
          algebraMap ℚ K (9 / 8) * A ^ 2 * r := by
      norm_num
      ring
    exact hscalar
  rw [coeff_add, coeff_add, hKcube, hmid, hlast]
  ring

#print axioms GCD369CubeFaberSixDoubleSourceJet_coeff3
#print axioms GCD369CubeFaberNineDoubleSourceJet_coeff4
