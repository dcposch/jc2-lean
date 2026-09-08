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
/-- Frozen order-`62` coefficient of the MixedPair jet (`h^8` of `alignedSquareJetQuotient610`). -/
def alignedSquareMixedPairOrder62610 {R : Type*} [CommRing R] (w1 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 : R) : R :=
    - (24284496600 : R) * w1 ^ 12 * e3
    - (14193574012800 : R) * w1 ^ 11 * e1 ^ 2
    + (2062916968320 : R) * w1 ^ 11 * a2
    + (11972302848 : R) * w1 ^ 9 * b4
    - (1037599580160 : R) * w1 ^ 7 * e3 * b5
    - (185211525058560 : R) * w1 ^ 6 * e1 ^ 2 * b5
    + (90510609530880 : R) * w1 ^ 6 * a2 * b5
    + (108612731437056 : R) * w1 ^ 6 * a1 * b6
    + (126714853343232 : R) * w1 ^ 6 * a0 * b7
    + (5810557648896 : R) * w1 ^ 5 * e3 ^ 2 * b6
    + (284365169786880 : R) * w1 ^ 4 * e1 ^ 2 * e3 * b6
    - (627540226080768 : R) * w1 ^ 4 * e3 * a2 * b6
    - (732130263760896 : R) * w1 ^ 4 * e3 * a1 * b7
    - (836720301441024 : R) * w1 ^ 4 * e3 * a0 * b8
    + (538621086302208 : R) * w1 ^ 3 * e1 ^ 4 * b6
    - (9698348948520960 : R) * w1 ^ 3 * e1 ^ 2 * a2 * b6
    - (11314740439941120 : R) * w1 ^ 3 * e1 ^ 2 * a1 * b7
    - (12931131931361280 : R) * w1 ^ 3 * e1 ^ 2 * a0 * b8
    - (1724545105920 : R) * w1 ^ 3 * e3 ^ 3 * b7
    + (15640233326936064 : R) * w1 ^ 3 * a2 ^ 2 * b6
    + (36493877762850816 : R) * w1 ^ 3 * a2 * a1 * b7
    + (41707288871829504 : R) * w1 ^ 3 * a2 * a0 * b8
    + (20853644435914752 : R) * w1 ^ 3 * a1 ^ 2 * b8
    - (36428479266816 : R) * w1 ^ 2 * e1 ^ 2 * e3 ^ 2 * b7
    + (147905103790080 : R) * w1 ^ 2 * e3 ^ 2 * a2 * b7
    + (169034404331520 : R) * w1 ^ 2 * e3 ^ 2 * a1 * b8
    - (43367237222400 : R) * w1 * e1 ^ 4 * e3 * b7
    + (1124078788804608 : R) * w1 * e1 ^ 2 * e3 * a2 * b7
    + (1284661472919552 : R) * w1 * e1 ^ 2 * e3 * a1 * b8
    + (48950673408 : R) * w1 * e3 ^ 4 * b8
    - (3194750241865728 : R) * w1 * e3 * a2 ^ 2 * b7
    - (7302286267121664 : R) * w1 * e3 * a2 * a1 * b8
    - (4336723722240 : R) * e1 ^ 6 * b7
    + (281019697201152 : R) * e1 ^ 4 * a2 * b7
    + (321165368229888 : R) * e1 ^ 4 * a1 * b8
    + (293704040448 : R) * e1 ^ 2 * e3 ^ 3 * b8
    - (4792125362798592 : R) * e1 ^ 2 * a2 ^ 2 * b7
    - (10953429400682496 : R) * e1 ^ 2 * a2 * a1 * b8
    - (1669475598336 : R) * e3 ^ 3 * a2 * b8
    + (13270501004673024 : R) * a2 ^ 3 * b7
    + (45498860587450368 : R) * a2 ^ 2 * a1 * b8

end Max11DegreeRoutes
