import Grok810ScaleZeroQuarticConstantCornerScratch
import Grok810ScaleZeroQuarticFullConeD6F6Part61Scratch
import Grok810ScaleZeroQuarticAssemblyCore2Scratch

/-! # Final assembly, `(8,10)` scale zero

`normalized810ScaleZero_impossible` and
`planeKeller810ScaleZeroExclusion_closed`, the two names the tracked
route glue expects.  **This module gates only once the three external
lemmas land**; it assumes exactly

* `quarticChamberResidual{tag}810_impossible` — the aggregate kill of the
  0-constructor inductive `QuarticChamberResidual7810`
  (tower lane: the 2 open, 19 deep-rescue and 405-wall families; power
  lane: the `power_target` systems whose cofactors the taxonomy never
  recorded), with the signature of `hresid` in
  `…AssemblyCoreScratch`;
* `quarticAllConstantCorner810_impossible` — the all-constant corner with
  `l = β = δ = ζ = 0`, with the signature of `hcorner`;
* `quarticConeABCDEFG810_impossible` — the sibling cone, expected from
  `Grok810ScaleZeroQuarticFullConeFinalScratch` (whose latest is
  `quarticConeABCDEFG810_residual9`), with the signature of `habcdefg`.

Untracked working note.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

set_option maxRecDepth 1000000

variable {k : Type*} [Field k] [CharZero k]

section QuarticAssembly810

variable [IsAlgClosed k]

set_option maxHeartbeats 64000000 in
/-- The `(8,10)` scale-zero leaf: no normalised leading-core source exists. -/
theorem normalized810ScaleZero_impossible7
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    False :=
  normalized810ScaleZero_impossible_of_residual7Kills
    quarticChamberResidual7810_impossible
    quarticAllConstantCorner810_impossible
    quarticConeABCDEFG810_impossible
    hsource

set_option maxHeartbeats 64000000 in
/-- Identity glue to the tracked exclusion
(`Grok810ScaleZeroConeEliminationScratch.lean:2266`). -/
theorem planeKeller810ScaleZeroExclusion_closed7 :
    PlaneKeller810ScaleZeroExclusion (K := k) :=
  planeKeller810ScaleZeroExclusion_of_impossible
    (fun P Q H hsource => normalized810ScaleZero_impossible7 hsource)

#print axioms normalized810ScaleZero_impossible7
#print axioms planeKeller810ScaleZeroExclusion_closed7

end QuarticAssembly810

end Max11DegreeRoutes
