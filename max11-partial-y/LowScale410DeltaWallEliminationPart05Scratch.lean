import LowScale410DeltaWallEliminationPart04Scratch

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

open private deltaLowerTwo410 from LowScale410DeltaWallEliminationPart03Scratch in
set_option maxHeartbeats 64000000 in
private theorem deltaCurveTwo410_face
    (delta : k) (A B U : k[X]) :
    deltaCurveTwo410 delta A B U =
      -(8 : k) • (A * B ^ 3) + (3 : k) • (B * U ^ 2) +
        deltaLowerTwo410 delta A B U := by
  simp only [deltaCurveTwo410, deltaLowerTwo410]
  module

end DeltaWallElimination410

end Max11DegreeRoutes
