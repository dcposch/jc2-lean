import Grok610AlignedSquareTowerOrders61to68Part68Scratch

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

theorem alignedSquareW1ZeroOrder61610_eval
    {k : Type*} [CommRing k]
    (e1 e3 a2 b8 : k[X]) (a : k) :
    (alignedSquareW1ZeroOrder61610 e1 e3 a2 b8).eval a =
      alignedSquareW1ZeroOrder61610 (e1.eval a) (e3.eval a) (a2.eval a) (b8.eval a) :=
  map_alignedSquareW1ZeroOrder61610 (Polynomial.evalRingHom a) e1 e3 a2 b8

end Max11DegreeRoutes
