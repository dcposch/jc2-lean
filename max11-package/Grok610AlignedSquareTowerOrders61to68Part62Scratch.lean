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

set_option maxHeartbeats 1600000000 in
/-- Remaining factor after order `68` on `w₁ = 0` (frozen). -/
def alignedSquareW1ZeroOrder68Plus610 {R : Type*} [CommRing R] (h e1 e3 a2 a1 a0 b4 b3 b2 b1 : R) : R :=
    (2106428730900480 : R) * h ^ 5 * e3 * a0 ^ 2
    + (58498535041007616 : R) * h ^ 5 * a0 * b1
    - (13691786750853120 : R) * h ^ 3 * e1 ^ 2 * a1 * a0
    - (2086844497920 : R) * h ^ 3 * e3 ^ 3 * a0
    - (6687075336192 : R) * h ^ 3 * e3 ^ 2 * b1
    + (113747151468625920 : R) * h ^ 3 * a2 * a1 * a0
    + (18957858578104320 : R) * h ^ 3 * a1 ^ 3
    + (178425204572160 : R) * h ^ 2 * e1 ^ 3 * e3 * a0
    + (70214291030016 : R) * h ^ 2 * e1 ^ 3 * b1
    - (3042619277967360 : R) * h ^ 2 * e1 * e3 * a2 * a0
    - (1521309638983680 : R) * h ^ 2 * e1 * e3 * a1 ^ 2
    - (3249918613389312 : R) * h ^ 2 * e1 * a2 * b1
    - (6499837226778624 : R) * h ^ 2 * e1 * a1 * b2
    - (9749755840167936 : R) * h ^ 2 * e1 * a0 * b3
    + (29737534095360 : R) * h * e1 ^ 2 * e3 ^ 2 * a1
    + (46809527353344 : R) * h * e1 ^ 2 * e3 * b2
    + (453246976 : R) * h * e3 ^ 5
    - (169034404331520 : R) * h * e3 ^ 2 * a2 * a1
    - (722204136308736 : R) * h * e3 * a2 * b2
    - (1083306204463104 : R) * h * e3 * a1 * b3
    - (1444408272617472 : R) * h * e3 * a0 * b4
    - (111515752857600 : R) * e1 ^ 5 * a1
    - (169967616000 : R) * e1 ^ 3 * e3 ^ 3
    + (4817480523448320 : R) * e1 ^ 3 * a2 * a1
    + (2202780303360 : R) * e1 * e3 ^ 3 * a2
    + (7801587892224 : R) * e1 * e3 ^ 2 * b3
    - (41075360252559360 : R) * e1 * a2 ^ 2 * a1

end Max11DegreeRoutes
