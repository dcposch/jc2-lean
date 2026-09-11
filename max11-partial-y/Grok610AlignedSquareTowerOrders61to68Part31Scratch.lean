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
/-- Order-`62` mixed coefficient on `μ = 0` after the pole-`21` `q₈` peel: `e₁ = h e₁n`, `b₈ = h b₈n`. -/
def alignedSquareMuZeroQ8Order62610 {R : Type*} [CommRing R] (w1 e1n e3 a2 a1 a0 b7 b6 b5 b4 : R) : R :=
    (69754744080 : R) * w1 ^ 13 * e1n
    - (24284496600 : R) * w1 ^ 12 * e3
    + (2062916968320 : R) * w1 ^ 11 * a2
    + (11972302848 : R) * w1 ^ 9 * b4
    + (2918248819200 : R) * w1 ^ 8 * e1n * b5
    + (100543399317504 : R) * w1 ^ 7 * e1n ^ 2 * b6
    - (1037599580160 : R) * w1 ^ 7 * e3 * b5
    + (445110481041408 : R) * w1 ^ 6 * e1n ^ 3 * b7
    - (49389740015616 : R) * w1 ^ 6 * e1n * e3 * b6
    + (90510609530880 : R) * w1 ^ 6 * a2 * b5
    + (108612731437056 : R) * w1 ^ 6 * a1 * b6
    + (126714853343232 : R) * w1 ^ 6 * a0 * b7
    - (232231555325952 : R) * w1 ^ 5 * e1n ^ 2 * e3 * b7
    + (2823931017363456 : R) * w1 ^ 5 * e1n * a2 * b6
    + (3294586186924032 : R) * w1 ^ 5 * e1n * a1 * b7
    + (5810557648896 : R) * w1 ^ 5 * e3 ^ 2 * b6
    + (8957502848286720 : R) * w1 ^ 4 * e1n ^ 2 * a2 * b7
    + (36862151639040 : R) * w1 ^ 4 * e1n * e3 ^ 2 * b7
    - (627540226080768 : R) * w1 ^ 4 * e3 * a2 * b6
    - (732130263760896 : R) * w1 ^ 4 * e3 * a1 * b7
    - (2514386764431360 : R) * w1 ^ 3 * e1n * e3 * a2 * b7
    - (1724545105920 : R) * w1 ^ 3 * e3 ^ 3 * b7
    + (15640233326936064 : R) * w1 ^ 3 * a2 ^ 2 * b6
    + (36493877762850816 : R) * w1 ^ 3 * a2 * a1 * b7
    + (35940940220989440 : R) * w1 ^ 2 * e1n * a2 ^ 2 * b7
    + (147905103790080 : R) * w1 ^ 2 * e3 ^ 2 * a2 * b7
    - (3194750241865728 : R) * w1 * e3 * a2 ^ 2 * b7
    + (13270501004673024 : R) * a2 ^ 3 * b7

end Max11DegreeRoutes
