import Grok610AlignedSquareTowerOrders61to68Part157Scratch

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

/-- Frozen `w₁ = 0` likewise yields `h₀⁷ ∣` the MixedPair jet. -/
theorem alignedSquareJetQuotient610_w1Zero_pow_dvd
    (h0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : k[X]) :
    h0 ^ 7 ∣
      alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3
        b2 b1 :=
  ⟨_, alignedSquareJetQuotient610_w1Zero_scale h0 e1 e3 a2 a1 a0 b8 b7
      b6 b5 b4 b3 b2 b1⟩

end AlignedSquareTowerHeads610

end Max11DegreeRoutes
