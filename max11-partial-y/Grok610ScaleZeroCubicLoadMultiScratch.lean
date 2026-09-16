import Grok610ScaleZeroCubicLoadMultiPart101Scratch
import Grok610ScaleZeroCubicLoadMultiPart102Scratch
import Grok610ScaleZeroCubicLoadMultiPart103Scratch
import Grok610ScaleZeroCubicLoadMultiPart22Scratch
import Grok610ScaleZeroCubicLoadMultiPart104Scratch
import Grok610ScaleZeroCubicLoadMultiPart105Scratch

/-! # Scale-zero cubic load-compete multi-monomial cones, `(6,10)`, `H = 0`

Continuation of `Grok610ScaleZeroCubicLoadConesScratch`.  That file
ends at `normalized610ScaleZero_cubicResidual7`: the leftover is the
multi-monomial cones `{B,C}`, `{B,C,E}`, `{B,C,D,E}` and `{C,D}`
(N₁ odd-column walls `7T ∈ {18a,30a,42a,54a}` and the chamber
`2c+d ≤ a`).

Plan `Grok610ScaleZeroCubicLoadCompetePlanScratch.md` File C (§2,
§3.3–3.5, §4, §5 item 1): kill those cones via the identities
`cubicSigmaInner_{BC,BCE,BCDE}` and the N₁/N₂ 2×2 on the CD/BCDE
walls, then assemble `normalized610ScaleZero_impossible`.

No `sorry`, no new axioms, no finite-root shortcut.
Untracked working note.
-/

namespace Max11DegreeRoutes

#print axioms cubicLoadSigmaCone_BC_impossible
#print axioms cubicLoadSigmaCone_BCE_impossible
#print axioms cubicLoadSigmaCone_BCDE_offWall_impossible
#print axioms normalized610ScaleZero_cubicResidual8

end Max11DegreeRoutes
