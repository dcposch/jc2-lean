import Grok610AlignedSquareTowerOrders61to68Part159Scratch

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

/-- Complement peels yield `h₀¹⁰ ∣` the MixedPair jet.  Orders `61`–`63`
vanish identically in that quotient. -/
theorem alignedSquareJetQuotient610_w1Complement_pow_dvd
    (h0 w1n e1b e3b a2b a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : k[X]) :
    h0 ^ 10 ∣
      alignedSquareJetQuotient610 h0 (h0 * w1n) (h0 * e1b) (h0 * e3b)
        (h0 * a2b) a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 :=
  ⟨_, alignedSquareJetQuotient610_w1Complement_scale h0 w1n e1b e3b a2b
      a1 a0 b8 b7 b6 b5 b4 b3 b2 b1⟩

end AlignedSquareTowerHeads610

end Max11DegreeRoutes
