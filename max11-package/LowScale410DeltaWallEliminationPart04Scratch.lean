import LowScale410DeltaWallEliminationPart03Scratch

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
private def deltaLowerOne410 (delta : k) (A B U : k[X]) : k[X] :=
  -(8 * delta : k) • (A ^ 2 * B) -
    (16 * delta : k) • (B * U) - (8 : k) • B ^ 4

end DeltaWallElimination410

end Max11DegreeRoutes
