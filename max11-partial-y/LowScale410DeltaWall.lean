import LowScale410GammaWall

/-!
# The pure delta wall for the `(4,10)`, scale-zero leaf

This module isolates the wall
`l = beta = gamma = zeta = eta = theta = 0`, `delta != 0` in the
denominator-free coordinate `U = A^2 - 4 C0`.  The two first integrals
become a sparse pair of weighted curves.  More importantly, the terminal
one-form has an exact primitive after subtracting the first integral times
`A'`. Thus every hypothetical trajectory on this wall gives a completely
explicit constant-fiber system whose shifted primitive has degree one.
-/

noncomputable section

set_option maxHeartbeats 2000000

open Polynomial

namespace Max11DegreeRoutes

section DeltaWall410

variable {k : Type*} [Field k] [CharZero k]

/-- The first denominator-free invariant on the pure `delta` wall, divided
by its common numerical factor `160`. -/
def deltaCurveTwo410 (delta : k) (A B U : k[X]) : k[X] :=
  (2 * delta : k) • A ^ 3 - (4 * delta : k) • (A * U) +
    (8 * delta : k) • B ^ 2 - (8 : k) • (A * B ^ 3) +
    (3 : k) • (B * U ^ 2)

/-- The second denominator-free invariant on the pure `delta` wall, divided
by its common numerical factor `40`. -/
def deltaCurveOne410 (delta : k) (A B U : k[X]) : k[X] :=
  -(8 * delta : k) • (A ^ 2 * B) -
    (16 * delta : k) • (B * U) +
    (24 : k) • (A * B ^ 2 * U) - (8 : k) • B ^ 4 - U ^ 3

/-- A primitive for the terminal one-form modulo the first invariant. -/
def deltaTerminalPrimitive410 (delta : k) (A B U : k[X]) : k[X] :=
  (560 * delta : k) • A ^ 4 -
    (960 * delta : k) • (A ^ 2 * U) -
    (1280 * delta : k) • (A * B ^ 2) +
    (1280 : k) • (B ^ 3 * U) + (320 * delta : k) • U ^ 2

/-- The primitive shifted by the value of the first invariant. -/
def deltaFiberPrimitive410
    (delta k2 : k) (A B U : k[X]) : k[X] :=
  deltaTerminalPrimitive410 delta A B U - k2 • A

theorem discriminantInvariantTwoNumerator410_delta
    (delta : k) (A B U : k[X]) :
    discriminantInvariantTwoNumerator410 0 0 0 delta 0 0 0 A B U =
      (160 : k) • deltaCurveTwo410 delta A B U := by
  simp only [discriminantInvariantTwoNumerator410, deltaCurveTwo410,
    zero_mul, mul_zero, zero_smul, add_zero, sub_zero]
  module

theorem discriminantInvariantOneNumerator410_delta
    (delta : k) (A B U : k[X]) :
    discriminantInvariantOneNumerator410 0 0 0 delta 0 0 0 A B U =
      (40 : k) • deltaCurveOne410 delta A B U := by
  simp only [discriminantInvariantOneNumerator410, deltaCurveOne410,
    zero_mul, mul_zero, zero_smul, add_zero, sub_zero]
  module

/-- Exactness of the terminal row on the pure `delta` wall.  This is the
sharp differential identity: no degree assumptions and no invariant-fiber
assumptions enter it. -/
theorem lWallTerminalNumerator410_delta_eq_derivative_sub
    (delta : k) (A B U : k[X]) :
    lWallTerminalNumerator410 0 0 0 delta 0 0 0 A B U =
      derivative (deltaTerminalPrimitive410 delta A B U) -
        discriminantInvariantTwoNumerator410 0 0 0 delta 0 0 0 A B U *
          derivative A := by
  simp only [lWallTerminalNumerator410, lWallTerminalACoefficient410,
    lWallTerminalBCoefficient410, lWallTerminalUCoefficient410,
    discriminantInvariantTwoNumerator410, deltaTerminalPrimitive410,
    Polynomial.derivative_add, Polynomial.derivative_sub,
    Polynomial.derivative_mul, Polynomial.derivative_pow,
    Polynomial.derivative_smul, Polynomial.derivative_C,
    Polynomial.smul_eq_C_mul, zero_mul, mul_zero, zero_smul, add_zero,
    sub_zero, neg_zero, Polynomial.C_0]
  push_cast
  simp only [Polynomial.C_ofNat, Polynomial.C_neg,
    Polynomial.derivative_ofNat, zero_mul, mul_zero, add_zero, sub_zero]
  ring_nf
  have hC (x : k) : Polynomial.C x = x • (1 : k[X]) := by
    simp [Algebra.smul_def, Polynomial.C_eq_algebraMap]
  have h2 : (2 : k[X]) = (2 : k) • (1 : k[X]) := by
    rw [← hC]
    exact (Polynomial.C_ofNat 2).symm
  have h4 : (4 : k[X]) = (4 : k) • (1 : k[X]) := by
    rw [← hC]
    exact (Polynomial.C_ofNat 4).symm
  simp only [hC, pow_two, one_mul, mul_one, smul_mul_assoc,
    mul_smul_comm, smul_smul, _root_.smul_pow, one_pow]
  rw [h2, h4]
  simp only [one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_smul]
  module

/-- On a constant first-invariant fiber, the terminal row is literally the
derivative of the shifted primitive. -/
theorem lWallTerminalNumerator410_delta_eq_fiberDerivative
    (delta k2 : k) (A B U : k[X])
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 0 delta 0 0 0 A B U = C k2) :
    lWallTerminalNumerator410 0 0 0 delta 0 0 0 A B U =
      derivative (deltaFiberPrimitive410 delta k2 A B U) := by
  rw [lWallTerminalNumerator410_delta_eq_derivative_sub, hTwo]
  simp only [deltaFiberPrimitive410, Polynomial.derivative_sub,
    Polynomial.derivative_smul, Polynomial.C_mul']

/-- A nonzero constant terminal row therefore forces the exact shifted
primitive to have degree one. -/
theorem deltaOnly410_shiftedPrimitive_degree_one
    (delta k2 terminal : k) (A B U : k[X])
    (hterminal : terminal ≠ 0)
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 0 delta 0 0 0 A B U = C k2)
    (hTerminal : lWallTerminalNumerator410
      0 0 0 delta 0 0 0 A B U = C terminal) :
    (deltaFiberPrimitive410 delta k2 A B U).natDegree = 1 := by
  apply natDegree_eq_one_of_derivative_eq_nonzero_C410
    (deltaFiberPrimitive410 delta k2 A B U) terminal hterminal
  rw [← lWallTerminalNumerator410_delta_eq_fiberDerivative
    delta k2 A B U hTwo]
  exact hTerminal

/-- Exact residual packet in discriminant coordinates.  It is the strongest
current handoff for the pure `delta` wall: the two curve values are
normalized, the terminal row is the derivative of the displayed shifted
primitive, and that primitive has degree exactly one. -/
theorem deltaOnly410_discriminant_residual_packet
    (delta k2 k1 terminal : k) (A B U : k[X])
    (hdelta : delta ≠ 0) (hterminal : terminal ≠ 0)
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 0 delta 0 0 0 A B U = C k2)
    (hOne : discriminantInvariantOneNumerator410
      0 0 0 delta 0 0 0 A B U = C k1)
    (hTerminal : lWallTerminalNumerator410
      0 0 0 delta 0 0 0 A B U = C terminal) :
    deltaCurveTwo410 delta A B U = C (k2 / 160) ∧
      deltaCurveOne410 delta A B U = C (k1 / 40) ∧
      derivative (deltaFiberPrimitive410 delta k2 A B U) = C terminal ∧
      (deltaFiberPrimitive410 delta k2 A B U).natDegree = 1 := by
  have hTwoCurve : deltaCurveTwo410 delta A B U = C (k2 / 160) := by
    rw [discriminantInvariantTwoNumerator410_delta] at hTwo
    have hs := congrArg (fun P : k[X] => (1 / 160 : k) • P) hTwo
    simp only [smul_smul, Polynomial.smul_C] at hs
    norm_num at hs
    rw [← Polynomial.C_mul] at hs
    convert hs using 1 <;> ring
  have hOneCurve : deltaCurveOne410 delta A B U = C (k1 / 40) := by
    rw [discriminantInvariantOneNumerator410_delta] at hOne
    have hs := congrArg (fun P : k[X] => (1 / 40 : k) • P) hOne
    simp only [smul_smul, Polynomial.smul_C] at hs
    norm_num at hs
    rw [← Polynomial.C_mul] at hs
    convert hs using 1 <;> ring
  have hDerivative : derivative (deltaFiberPrimitive410 delta k2 A B U) =
      C terminal := by
    rw [← lWallTerminalNumerator410_delta_eq_fiberDerivative
      delta k2 A B U hTwo]
    exact hTerminal
  exact ⟨hTwoCurve, hOneCurve, hDerivative,
    natDegree_eq_one_of_derivative_eq_nonzero_C410
      (deltaFiberPrimitive410 delta k2 A B U) terminal hterminal hDerivative⟩

/-- Original-coordinate version of the exact pure-`delta` residual. -/
theorem deltaOnly410_original_residual_packet
    (alpha delta epsilon iota k2 k1 terminal : k)
    (A B C0 : k[X]) (hdelta : delta ≠ 0) (hterminal : terminal ≠ 0)
    (hTwo : firstIntegralTwoPolynomial410
      0 0 0 delta 0 0 0 A B C0 = C k2)
    (hOne : firstIntegralOnePolynomial410
      0 0 0 delta 0 0 0 A B C0 = C k1)
    (hLower : lowerRowZeroPolynomial410
      (integratedWPolynomial410 0 alpha 0 0 delta epsilon 0 0 A B C0)
      (integratedZPolynomial410 0 alpha 0 0 delta epsilon 0 0 iota A B C0)
      B C0 = C terminal) :
    let U := A ^ 2 - (4 : k) • C0
    deltaCurveTwo410 delta A B U = C ((64 / 5 : k) * k2) ∧
      deltaCurveOne410 delta A B U = C ((256 / 5 : k) * k1) ∧
      derivative (deltaFiberPrimitive410 delta (2048 * k2) A B U) =
        C (8192 * terminal) ∧
      (deltaFiberPrimitive410 delta (2048 * k2) A B U).natDegree = 1 := by
  dsimp only
  have hTwoD :
      discriminantInvariantTwoNumerator410 0 0 0 delta 0 0 0 A B
          (A ^ 2 - (4 : k) • C0) = C (2048 * k2) := by
    rw [← firstIntegralTwoPolynomial410_discriminantNumerator, hTwo,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  have hOneD :
      discriminantInvariantOneNumerator410 0 0 0 delta 0 0 0 A B
          (A ^ 2 - (4 : k) • C0) = C (2048 * k1) := by
    rw [← firstIntegralOnePolynomial410_discriminantNumerator, hOne,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  have hTerminalD :
      lWallTerminalNumerator410 0 0 0 delta 0 0 0 A B
          (A ^ 2 - (4 : k) • C0) = C (8192 * terminal) := by
    rw [← lowerRow410_discriminantTerminalNumerator, hLower,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  have hPacket := deltaOnly410_discriminant_residual_packet
    delta (2048 * k2) (2048 * k1) (8192 * terminal) A B
      (A ^ 2 - (4 : k) • C0) hdelta (mul_ne_zero (by norm_num) hterminal)
      hTwoD hOneD hTerminalD
  rcases hPacket with ⟨hCurveTwo, hCurveOne, hDerivative, hDegree⟩
  have hTwoScale : (2048 * k2) / 160 = (64 / 5 : k) * k2 := by ring
  have hOneScale : (2048 * k1) / 40 = (256 / 5 : k) * k1 := by ring
  rw [hTwoScale] at hCurveTwo
  rw [hOneScale] at hCurveOne
  exact ⟨hCurveTwo, hCurveOne, hDerivative, hDegree⟩

end DeltaWall410

end Max11DegreeRoutes
