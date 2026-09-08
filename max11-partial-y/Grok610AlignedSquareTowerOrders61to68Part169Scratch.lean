import Grok610AlignedSquareTowerOrders61to68Part168Scratch

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

section AlignedSquareTowerHeads610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 1600000000 in
theorem alignedSquareJetQuotient610_muZeroQ8_factor_one
    {R : Type*} [CommRing R]
    (h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 : R) :
    alignedSquareJetQuotient610 h w1 (h * e1n) e3 a2 a1 a0 (h * b8n) b7
        b6 b5 b4 b3 b2 b1 =
      h * alignedSquareMuZeroQ8QuotOne610 h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 := by
  simp only [alignedSquareJetQuotient610,
    alignedSquareMuZeroQ8QuotOne610]
  ring

end AlignedSquareTowerHeads610

end Max11DegreeRoutes
