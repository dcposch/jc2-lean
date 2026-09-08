import Grok610AlignedSquareSourceWrapperScratch
import Grok610PoleCeilingLemmaScratch

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

section AlignedSquareTowerDvd610

variable {k : Type*} [Field k]

/-- Evaluation of a remaining numerator `c₀ + h₀ · rest` at a root of
the linear scale is the head `c₀`. -/
theorem alignedSquare_eval_head_of_linear_factor610
    (h0 c0 rest : k[X]) (a : k) (hroot : h0.eval a = 0) :
    (c0 + h0 * rest).eval a = c0.eval a := by
  simp [Polynomial.eval_add, Polynomial.eval_mul, hroot, zero_mul,
    add_zero]

end AlignedSquareTowerDvd610

end Max11DegreeRoutes
