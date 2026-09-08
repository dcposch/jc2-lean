import LowScale410DeltaWallEliminationPart05Scratch

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

open private deltaLowerOne410 from LowScale410DeltaWallEliminationPart04Scratch in
set_option maxHeartbeats 64000000 in
private theorem deltaCurveOne410_face
    (delta : k) (A B U : k[X]) :
    deltaCurveOne410 delta A B U =
      (24 : k) • (A * B ^ 2 * U) - U ^ 3 +
        deltaLowerOne410 delta A B U := by
  simp only [deltaCurveOne410, deltaLowerOne410]
  module

end DeltaWallElimination410

end Max11DegreeRoutes
