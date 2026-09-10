import Fable810ScaleZeroFourteenthDefectPart18Scratch

/-! Part 19 of 40 of `Fable810ScaleZeroFourteenthDefectScratch`, split so that no single module elaborates them all
at once.  Statements are unchanged. -/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

set_option maxRecDepth 1000000

section Depression810FifteenthClearing

variable {F : Type*} [Field F] [CharZero F]


set_option maxHeartbeats 16000000 in
/-- Polynomial numerator of `36028797018963968 h¹⁰⁵ ο` on the
ninth-power face.  The large literal is blocked above to keep elaboration
linear. -/
def localClearedFifteenthDefect810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X])
    (lambda : F) : F[X] :=
  localClearedFifteenthDefectCore810 h a7 a6 a5 a4 a3 a2 a1 a0
    b8 b7 b6 b5 b4 b3 b2 b1 (Polynomial.C lambda)



end Depression810FifteenthClearing
end Max11DegreeRoutes
end
