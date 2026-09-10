import Grok810AlignedSquareClearedNumeratorBlocksSeg04Scratch

/-! Part 5 of 118 of `Grok810AlignedSquareClearedNumeratorBlocksScratch`, split so that no single module elaborates them all
at once.  Statements are unchanged. -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

set_option maxRecDepth 1000000
set_option maxHeartbeats 800000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section AlignedSquareClearedNumerator810

variable {R : Type*} [CommRing R]


/-- The `h^{119}`-cleared source numerator on the aligned face
`λ = 0`.  The ninth-power scalar is specialised here; `b₉` remains an
argument of the primitive, as `alignedSquareSourcePrimitive810` does. -/
def alignedSquareClearedNumerator810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) : R :=
  degreeZeroClearedSource810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4
    b3 b2 b1 0


end AlignedSquareClearedNumerator810
end Max11DegreeRoutes
end
