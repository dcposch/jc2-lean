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
/-- Frozen order-`66` coefficient of the MixedPair jet (`h^12` of `alignedSquareJetQuotient610`). -/
def alignedSquareMixedPairOrder66610 {R : Type*} [CommRing R] (w1 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 : R) : R :=
    (20751991603200 : R) * w1 ^ 9 * a0
    - (258708161986560 : R) * w1 ^ 7 * e3 * a1
    + (156728328192 : R) * w1 ^ 7 * b2
    - (7713405230469120 : R) * w1 ^ 6 * e1 ^ 2 * a1
    - (1175644753920 : R) * w1 ^ 6 * e3 ^ 3
    + (14511867728117760 : R) * w1 ^ 6 * a2 * a1
    - (41560269004800 : R) * w1 ^ 5 * e1 ^ 2 * e3 ^ 2
    + (126384519905280 : R) * w1 ^ 5 * e3 ^ 2 * a2
    - (6582589784064 : R) * w1 ^ 5 * e3 * b3
    - (46787569920000 : R) * w1 ^ 4 * e1 ^ 4 * e3
    + (1645786652590080 : R) * w1 ^ 4 * e1 ^ 2 * e3 * a2
    - (470655169560576 : R) * w1 ^ 4 * e1 ^ 2 * b3
    - (3816479910297600 : R) * w1 ^ 4 * e3 * a2 ^ 2
    + (592433080565760 : R) * w1 ^ 4 * a2 * b3
    + (789910774087680 : R) * w1 ^ 4 * a1 * b4
    + (987388467609600 : R) * w1 ^ 4 * a0 * b5
    + (39122296012800 : R) * w1 ^ 3 * e1 ^ 6
    - (418184073216000 : R) * w1 ^ 3 * e1 ^ 4 * a2
    - (8430590916034560 : R) * w1 ^ 3 * e1 ^ 2 * a2 ^ 2
    + (14302911135744 : R) * w1 ^ 3 * e3 ^ 2 * b4
    + (28524555730944000 : R) * w1 ^ 3 * a2 ^ 3
    + (253551606497280 : R) * w1 ^ 2 * e1 ^ 2 * e3 * b4
    - (1263857238540288 : R) * w1 ^ 2 * e3 * a2 * b4
    - (1579821548175360 : R) * w1 ^ 2 * e3 * a1 * b5
    - (1895785857810432 : R) * w1 ^ 2 * e3 * a0 * b6
    + (160582684114944 : R) * w1 * e1 ^ 4 * b4
    - (5476714700341248 : R) * w1 * e1 ^ 2 * a2 * b4
    - (6845893375426560 : R) * w1 * e1 ^ 2 * a1 * b5
    - (8215072050511872 : R) * w1 * e1 ^ 2 * a0 * b6
    - (1043422248960 : R) * w1 * e3 ^ 3 * b5
    + (22749430293725184 : R) * w1 * a2 ^ 2 * b4
    + (56873575734312960 : R) * w1 * a2 * a1 * b5
    + (68248290881175552 : R) * w1 * a2 * a0 * b6
    + (34124145440587776 : R) * w1 * a1 ^ 2 * b6
    + (79623006028038144 : R) * w1 * a1 * a0 * b7
    + (45498860587450368 : R) * w1 * a0 ^ 2 * b8
    - (4695400120320 : R) * e1 ^ 2 * e3 ^ 2 * b5
    + (39007939461120 : R) * e3 ^ 2 * a2 * b5
    + (46809527353344 : R) * e3 ^ 2 * a1 * b6
    + (54611115245568 : R) * e3 ^ 2 * a0 * b7

end Max11DegreeRoutes
