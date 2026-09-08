import Grok610AlignedSquareTowerOrders61to68Part31Scratch

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 100000000
set_option maxHeartbeats 1600000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option maxHeartbeats 800000000 in
theorem map_alignedSquareMuZeroQ8Order62610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (w1 e1n e3 a2 a1 a0 b7 b6 b5 b4 : R) :
    phi (alignedSquareMuZeroQ8Order62610 w1 e1n e3 a2 a1 a0 b7 b6 b5 b4) =
      alignedSquareMuZeroQ8Order62610 (phi w1) (phi e1n) (phi e3) (phi a2) (phi a1) (phi a0) (phi b7) (phi b6) (phi b5) (phi b4) := by
  simp only [alignedSquareMuZeroQ8Order62610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

end Max11DegreeRoutes
