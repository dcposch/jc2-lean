import Grok610ScaleZeroCubicADominantPart153Scratch
import Grok610ScaleZeroCubicADominantPart154Scratch
import Grok610ScaleZeroCubicADominantPart156Scratch
import Grok610ScaleZeroCubicADominantPart155Scratch

/-! # Scale-zero cubic A-dominant Stage B+C, for normalized `(6,10)`, `H = 0`

Continuation of `Grok610ScaleZeroCubicConesScratch`.  That file ends at
`normalized610ScaleZero_cubicADominantResidual`: the source loads the
cubic letters `A,B,C,D,E` on the single cone `R = {A}`.

CAS jobs `scripts/derive_610_scale_zero_cubic_adominant.py` and
`scripts/derive_610_scale_zero_cubic_balanced.py` analyse the σ-grading
inside `R = {A}`.  Thirteen argmin cones are empty, `{C,D}` closes by
the σ-7 part of `N₁ = μ + (A/6) κ`, and the balanced cell dies by
`⟨G1,G2,G3,G4⟩`.  Odd loads vanish on the competing-load wall by the
pure-`A` column of `N₁`.

No total-degree or twice-prime theorem is used.  No `sorry`, no new
axioms, no finite-root shortcut.  Untracked working note.
-/
/-! ## σ-argmin cones inside `R = {A}` -/

namespace Max11DegreeRoutes

#print axioms degreeZeroN1Cubic610_eq_mu_add_A_kappa
#print axioms cubicADominant_l_eq_zero
#print axioms cubicADominant_allLettersZero_impossible
#print axioms cubicSigmaCone_B_impossible
#print axioms cubicSigmaCone_BCE_impossible
#print axioms normalized610ScaleZero_cubicADominantResidual2

end Max11DegreeRoutes
