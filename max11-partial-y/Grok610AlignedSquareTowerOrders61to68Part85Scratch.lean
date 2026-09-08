import Grok610AlignedSquareTowerOrders61to68Part84Scratch

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

theorem alignedSquareMuZeroQ8Order62610_eval
    {k : Type*} [CommRing k]
    (w1 e1n e3 a2 a1 a0 b7 b6 b5 b4 : k[X]) (a : k) :
    (alignedSquareMuZeroQ8Order62610 w1 e1n e3 a2 a1 a0 b7 b6 b5 b4).eval a =
      alignedSquareMuZeroQ8Order62610 (w1.eval a) (e1n.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b7.eval a) (b6.eval a) (b5.eval a) (b4.eval a) :=
  map_alignedSquareMuZeroQ8Order62610 (Polynomial.evalRingHom a) w1 e1n e3 a2 a1 a0 b7 b6 b5 b4

end Max11DegreeRoutes
