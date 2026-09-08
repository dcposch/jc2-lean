import LowScale410DeltaWallEliminationPart02Scratch

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
private def deltaLowerTwo410 (delta : k) (A B U : k[X]) : k[X] :=
  (2 * delta : k) • A ^ 3 - (4 * delta : k) • (A * U) +
    (8 * delta : k) • B ^ 2

end DeltaWallElimination410

end Max11DegreeRoutes
