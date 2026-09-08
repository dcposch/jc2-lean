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
/-- Order-`66` coefficient on the `w₁ = 0` complement peel `w₁ = h w₁n`, `e₁ = h e₁b`, `e₃ = h e₃b`, `a₂ = h a₂b`. -/
def alignedSquareW1ComplementOrder66610 {R : Type*} [CommRing R] (w1n e1b e3b a2b a1 a0 b8 b7 : R) : R :=
    - (4409798215680 : R) * w1n ^ 9 * a2b * b8
    + (14007594332160 : R) * w1n ^ 8 * a1 * b8
    + (804347194540032 : R) * w1n ^ 7 * e1b * a2b * b8
    - (1778030640562176 : R) * w1n ^ 6 * e1b * a1 * b8
    - (197558960062464 : R) * w1n ^ 6 * e3b * a2b * b8
    - (7166002278629376 : R) * w1n ^ 5 * e1b ^ 2 * a2b * b8
    + (418360150720512 : R) * w1n ^ 5 * e3b * a1 * b8
    + (10237146112327680 : R) * w1n ^ 4 * e1b ^ 2 * a1 * b8
    + (2274921358295040 : R) * w1n ^ 4 * e1b * e3b * a2b * b8
    - (9883758560772096 : R) * w1n ^ 4 * a2b ^ 2 * b7
    + (8617937380835328 : R) * w1n ^ 3 * e1b ^ 3 * a2b * b8
    - (2873584873635840 : R) * w1n ^ 3 * e1b * e3b * a1 * b8
    - (159643604090880 : R) * w1n ^ 3 * e3b ^ 2 * a2b * b8
    + (36493877762850816 : R) * w1n ^ 3 * a2b * a1 * b7
    + (41707288871829504 : R) * w1n ^ 3 * a2b * a0 * b8
    - (6744472732827648 : R) * w1n ^ 2 * e1b ^ 3 * a1 * b8
    - (2248157577609216 : R) * w1n ^ 2 * e1b ^ 2 * e3b * a2b * b8
    + (35940940220989440 : R) * w1n ^ 2 * e1b * a2b ^ 2 * b7
    + (169034404331520 : R) * w1n ^ 2 * e3b ^ 2 * a1 * b8
    - (29858627260514304 : R) * w1n ^ 2 * a1 ^ 2 * b7
    - (68248290881175552 : R) * w1n ^ 2 * a1 * a0 * b8
    - (1338189034291200 : R) * w1n * e1b ^ 4 * a2b * b8
    + (1284661472919552 : R) * w1n * e1b ^ 2 * e3b * a1 * b8
    + (142740163657728 : R) * w1n * e1b * e3b ^ 2 * a2b * b8
    - (57505504353583104 : R) * w1n * e1b * a2b * a1 * b7
    - (65720576404094976 : R) * w1n * e1b * a2b * a0 * b8
    - (3194750241865728 : R) * w1n * e3b * a2b ^ 2 * b7
    + (321165368229888 : R) * e1b ^ 4 * a1 * b8
    + (142740163657728 : R) * e1b ^ 3 * e3b * a2b * b8
    - (4792125362798592 : R) * e1b ^ 2 * a2b ^ 2 * b7
    - (45075841155072 : R) * e1b * e3b ^ 2 * a1 * b8
    + (13270501004673024 : R) * e1b * a1 ^ 2 * b7
    + (30332573724966912 : R) * e1b * a1 * a0 * b8
    - (1669475598336 : R) * e3b ^ 3 * a2b * b8
    + (2949000223260672 : R) * e3b * a2b * a1 * b7
    + (3370285969440768 : R) * e3b * a2b * a0 * b8

end Max11DegreeRoutes
