import LowScale410DeltaWall

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
private def fiveDegreeTie410 (d1 d2 d3 d4 d5 m : ℕ) : Prop :=
  (d1 = m ∧ d2 = m) ∨ (d1 = m ∧ d3 = m) ∨
  (d1 = m ∧ d4 = m) ∨ (d1 = m ∧ d5 = m) ∨
  (d2 = m ∧ d3 = m) ∨ (d2 = m ∧ d4 = m) ∨
  (d2 = m ∧ d5 = m) ∨ (d3 = m ∧ d4 = m) ∨
  (d3 = m ∧ d5 = m) ∨ (d4 = m ∧ d5 = m)

end DeltaWallElimination410

end Max11DegreeRoutes
