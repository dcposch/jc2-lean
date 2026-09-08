import LowScale410DeltaWallEliminationPart13Scratch

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
