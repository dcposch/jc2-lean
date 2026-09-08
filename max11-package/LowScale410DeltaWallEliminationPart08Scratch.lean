import LowScale410DeltaWallEliminationPart07Scratch

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
private theorem deltaFiber_degree_one_impossible_of_degrees_zero
    (delta k2 : k) (A B U : k[X])
    (hA : A.natDegree = 0) (hB : B.natDegree = 0)
    (hU : U.natDegree = 0)
    (hDegree : (deltaFiberPrimitive410 delta k2 A B U).natDegree = 1) :
    False := by
  have hle : (deltaFiberPrimitive410 delta k2 A B U).natDegree ≤ 0 := by
    simp only [deltaFiberPrimitive410, deltaTerminalPrimitive410]
    compute_degree
    omega
  omega

end DeltaWallElimination410

end Max11DegreeRoutes
