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

open private deltaOnly410_nonzero_polynomials_impossible from LowScale410DeltaWallEliminationPart07Scratch in
open private deltaOnly410_zeroA_impossible from LowScale410DeltaWallEliminationPart09Scratch in
open private deltaOnly410_zeroB_impossible from LowScale410DeltaWallEliminationPart10Scratch in
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
