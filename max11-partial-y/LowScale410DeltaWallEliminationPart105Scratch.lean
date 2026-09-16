import LowScale410DeltaWallEliminationPart11Scratch

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

open private deltaOnly410_nonzero_polynomials_impossible from LowScale410DeltaWallEliminationPart103Scratch in
open private deltaOnly410_zeroA_impossible from LowScale410DeltaWallEliminationPart104Scratch in
open private deltaOnly410_zeroB_impossible from LowScale410DeltaWallEliminationPart104Scratch in
open private deltaOnly410_zeroU_impossible from LowScale410DeltaWallEliminationPart11Scratch in
set_option maxHeartbeats 64000000 in
/-- The exact pure-`delta` constant-fiber system is impossible.  The proof
also covers all three degenerate coordinate cases. -/
theorem deltaOnly410_discriminant_trajectory_impossible
    (delta k2 k1 terminal : k) (A B U : k[X])
    (hdelta : delta ≠ 0) (hterminal : terminal ≠ 0)
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 0 delta 0 0 0 A B U = C k2)
    (hOne : discriminantInvariantOneNumerator410
      0 0 0 delta 0 0 0 A B U = C k1)
    (hTerminal : lWallTerminalNumerator410
      0 0 0 delta 0 0 0 A B U = C terminal) : False := by
  obtain ⟨hTwoCurve, hOneCurve, hDerivative, hDegree⟩ :=
    deltaOnly410_discriminant_residual_packet delta k2 k1 terminal A B U
      hdelta hterminal hTwo hOne hTerminal
  by_cases hAzero : A = 0
  · exact deltaOnly410_zeroA_impossible delta k2 (k2 / 160) (k1 / 40)
      A B U hdelta hAzero hTwoCurve hOneCurve hDegree
  · by_cases hBzero : B = 0
    · exact deltaOnly410_zeroB_impossible delta k2 (k2 / 160) (k1 / 40)
        A B U hdelta hBzero hTwoCurve hOneCurve hDegree
    · by_cases hUzero : U = 0
      · exact deltaOnly410_zeroU_impossible delta k2 (k2 / 160) (k1 / 40)
          A B U hdelta hUzero hTwoCurve hOneCurve hDegree
      · have hscale : (160 : k) * (k2 / 160) = k2 := by ring
        have hDegree' :
            (deltaFiberPrimitive410 delta (160 * (k2 / 160)) A B U).natDegree =
              1 := by
          rw [hscale]
          exact hDegree
        exact deltaOnly410_nonzero_polynomials_impossible
          delta (k2 / 160) (k1 / 40) terminal A B U
            A.natDegree B.natDegree U.natDegree hdelta hterminal
            hAzero hBzero hUzero rfl rfl rfl hTwoCurve hOneCurve hDegree'

end DeltaWallElimination410

end Max11DegreeRoutes
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
/-- After closing `l`, `beta`, `gamma`, and `delta`, a nonzero terminal row
must carry one of the three final effective loads. -/
theorem deltaWall410_laterEffectiveLoad_residual
    (alpha delta epsilon zeta eta theta iota k2 k1 terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hTwo : firstIntegralTwoPolynomial410
      0 0 0 delta zeta eta theta A B C0 = C k2)
    (hOne : firstIntegralOnePolynomial410
      0 0 0 delta zeta eta theta A B C0 = C k1)
    (hLower : lowerRowZeroPolynomial410
      (integratedWPolynomial410 0 alpha 0 0 delta epsilon zeta theta A B C0)
      (integratedZPolynomial410 0 alpha 0 0 delta epsilon zeta eta iota A B C0)
      B C0 = C terminal) :
    zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0 := by
  by_contra hlater
  push_neg at hlater
  obtain ⟨hzeta, heta, htheta⟩ := hlater
  subst zeta
  subst eta
  subst theta
  have hwall := constantIntegral410_effectiveLoadWall
    (k := k) 0 alpha 0 0 delta epsilon 0 0 0 iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower
  rcases hwall with hl | hbeta | hgamma | hdelta | hzeta | heta | htheta
  · exact hl rfl
  · exact hbeta rfl
  · exact hgamma rfl
  · exact deltaOnly410_original_trajectory_impossible
      alpha delta epsilon iota k2 k1 terminal A B C0 hdelta hterminal
        hTwo hOne hLower
  · exact hzeta rfl
  · exact heta rfl
  · exact htheta rfl

end DeltaWallElimination410

end Max11DegreeRoutes
