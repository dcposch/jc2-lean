import Grok610AlignedSquareTowerOrders61to68Part146Scratch

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

theorem alignedSquareW1ZeroOrder68Plus610_eval
    {k : Type*} [CommRing k]
    (h e1 e3 a2 a1 a0 b4 b3 b2 b1 : k[X]) (a : k) :
    (alignedSquareW1ZeroOrder68Plus610 h e1 e3 a2 a1 a0 b4 b3 b2 b1).eval a =
      alignedSquareW1ZeroOrder68Plus610 (h.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b4.eval a) (b3.eval a) (b2.eval a) (b1.eval a) :=
  map_alignedSquareW1ZeroOrder68Plus610 (Polynomial.evalRingHom a) h e1 e3 a2 a1 a0 b4 b3 b2 b1

end Max11DegreeRoutes
