import LowScale410DeltaWallEliminationPart12Scratch

/-!
# Elimination of the pure delta wall

The two constant invariant curves and the degree-one terminal primitive have
only one possible nondegenerate Newton ray.  Its degree ratio is
`(deg A, deg B, deg U) = (8,7,11)` up to scale.  The two invariant faces on
that ray give incompatible leading-coefficient equations.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Polynomial

namespace Max11DegreeRoutes

section DeltaWallElimination410

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
/-- Original-coordinate closure of the pure `delta` wall. -/
theorem deltaOnly410_original_trajectory_impossible
    (alpha delta epsilon iota k2 k1 terminal : k)
    (A B C0 : k[X]) (hdelta : delta ≠ 0) (hterminal : terminal ≠ 0)
    (hTwo : firstIntegralTwoPolynomial410
      0 0 0 delta 0 0 0 A B C0 = C k2)
    (hOne : firstIntegralOnePolynomial410
      0 0 0 delta 0 0 0 A B C0 = C k1)
    (hLower : lowerRowZeroPolynomial410
      (integratedWPolynomial410 0 alpha 0 0 delta epsilon 0 0 A B C0)
      (integratedZPolynomial410 0 alpha 0 0 delta epsilon 0 0 iota A B C0)
      B C0 = C terminal) : False := by
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
  exact deltaOnly410_discriminant_trajectory_impossible delta
    (2048 * k2) (2048 * k1) (8192 * terminal) A B
      (A ^ 2 - (4 : k) • C0) hdelta
      (mul_ne_zero (by norm_num) hterminal) hTwoD hOneD hTerminalD

end DeltaWallElimination410

end Max11DegreeRoutes
