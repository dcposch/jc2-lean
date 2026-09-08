import Grok610AlignedSquareTowerOrders61to68Part150Scratch

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

theorem alignedSquareW1ComplementOrder68Plus610_eval
    {k : Type*} [CommRing k]
    (h w1n e1b e3b a2b a1 a0 b6 b5 b4 b3 b2 b1 : k[X]) (a : k) :
    (alignedSquareW1ComplementOrder68Plus610 h w1n e1b e3b a2b a1 a0 b6 b5 b4 b3 b2 b1).eval a =
      alignedSquareW1ComplementOrder68Plus610 (h.eval a) (w1n.eval a) (e1b.eval a) (e3b.eval a) (a2b.eval a) (a1.eval a) (a0.eval a) (b6.eval a) (b5.eval a) (b4.eval a) (b3.eval a) (b2.eval a) (b1.eval a) :=
  map_alignedSquareW1ComplementOrder68Plus610 (Polynomial.evalRingHom a) h w1n e1b e3b a2b a1 a0 b6 b5 b4 b3 b2 b1

end Max11DegreeRoutes
