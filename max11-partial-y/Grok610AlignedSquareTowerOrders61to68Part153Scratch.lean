import Grok610AlignedSquareTowerOrders61to68Part152Scratch

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

theorem alignedSquareMuZeroQ8Order68Plus610_eval
    {k : Type*} [CommRing k]
    (h w1 e1n e3 a2 a1 a0 b5 b4 b3 b2 b1 : k[X]) (a : k) :
    (alignedSquareMuZeroQ8Order68Plus610 h w1 e1n e3 a2 a1 a0 b5 b4 b3 b2 b1).eval a =
      alignedSquareMuZeroQ8Order68Plus610 (h.eval a) (w1.eval a) (e1n.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b5.eval a) (b4.eval a) (b3.eval a) (b2.eval a) (b1.eval a) :=
  map_alignedSquareMuZeroQ8Order68Plus610 (Polynomial.evalRingHom a) h w1 e1n e3 a2 a1 a0 b5 b4 b3 b2 b1

end Max11DegreeRoutes
