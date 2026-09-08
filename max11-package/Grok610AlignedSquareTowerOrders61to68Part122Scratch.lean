import Grok610AlignedSquareTowerOrders61to68Part50Scratch

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
theorem map_alignedSquareW1ComplementOrder66610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (w1n e1b e3b a2b a1 a0 b8 b7 : R) :
    phi (alignedSquareW1ComplementOrder66610 w1n e1b e3b a2b a1 a0 b8 b7) =
      alignedSquareW1ComplementOrder66610 (phi w1n) (phi e1b) (phi e3b) (phi a2b) (phi a1) (phi a0) (phi b8) (phi b7) := by
  simp only [alignedSquareW1ComplementOrder66610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

end Max11DegreeRoutes
