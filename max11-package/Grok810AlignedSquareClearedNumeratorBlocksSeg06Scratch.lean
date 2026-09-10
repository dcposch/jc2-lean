import Grok810AlignedSquareClearedNumeratorBlocksSeg05Scratch

/-! Part 6 of 118 of `Grok810AlignedSquareClearedNumeratorBlocksScratch`, split so that no single module elaborates them all
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

section AlignedSquareClearedNumeratorMap810

variable {R S : Type*} [CommRing R] [CommRing S]


set_option maxHeartbeats 800000000 in
theorem alignedSquareClearedNumerator810_map
    (f : R →+* S)
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) :
    f (alignedSquareClearedNumerator810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7
        b6 b5 b4 b3 b2 b1) =
      alignedSquareClearedNumerator810 (f h) (f a7) (f a6) (f a5) (f a4)
        (f a3) (f a2) (f a1) (f a0) (f b8) (f b7) (f b6) (f b5) (f b4)
        (f b3) (f b2) (f b1) := by
  have h0 : f 0 = 0 := map_zero f
  simpa [alignedSquareClearedNumerator810, h0] using
    degreeZeroClearedSource810_map f h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6
      b5 b4 b3 b2 b1 0


end AlignedSquareClearedNumeratorMap810
end Max11DegreeRoutes
end
