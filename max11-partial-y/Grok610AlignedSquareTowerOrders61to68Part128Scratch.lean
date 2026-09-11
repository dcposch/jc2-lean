import Grok610AlignedSquareTowerOrders61to68Part212Scratch

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
theorem map_alignedSquareW1ZeroOrder67610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (e1 e3 a2 a1 a0 b6 b5 b4 : R) :
    phi (alignedSquareW1ZeroOrder67610 e1 e3 a2 a1 a0 b6 b5 b4) =
      alignedSquareW1ZeroOrder67610 (phi e1) (phi e3) (phi a2) (phi a1) (phi a0) (phi b6) (phi b5) (phi b4) := by
  simp only [alignedSquareW1ZeroOrder67610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

end Max11DegreeRoutes
