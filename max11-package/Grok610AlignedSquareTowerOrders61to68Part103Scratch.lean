import Grok610AlignedSquareTowerOrders61to68Part102Scratch

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

theorem alignedSquareW1ComplementOrder64610_eval
    {k : Type*} [CommRing k]
    (w1n a2b a1 b8 : k[X]) (a : k) :
    (alignedSquareW1ComplementOrder64610 w1n a2b a1 b8).eval a =
      alignedSquareW1ComplementOrder64610 (w1n.eval a) (a2b.eval a) (a1.eval a) (b8.eval a) :=
  map_alignedSquareW1ComplementOrder64610 (Polynomial.evalRingHom a) w1n a2b a1 b8

end Max11DegreeRoutes
