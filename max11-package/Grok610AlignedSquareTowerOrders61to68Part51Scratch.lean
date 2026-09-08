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
/-- Order-`66` mixed coefficient on `μ = 0` after the pole-`21` `q₈` peel: `e₁ = h e₁n`, `b₈ = h b₈n`. -/
def alignedSquareMuZeroQ8Order66610 {R : Type*} [CommRing R] (w1 e1n e3 a2 a1 a0 b7 b6 b5 b4 b3 b2 : R) : R :=
    (205018291296000 : R) * w1 ^ 9 * e1n ^ 3
    + (20751991603200 : R) * w1 ^ 9 * a0
    - (118279783440000 : R) * w1 ^ 8 * e1n ^ 2 * e3
    + (1068273617748480 : R) * w1 ^ 8 * e1n * a1
    + (5177815799869440 : R) * w1 ^ 7 * e1n ^ 2 * a2
    + (21307883950080 : R) * w1 ^ 7 * e1n * e3 ^ 2
    - (258708161986560 : R) * w1 ^ 7 * e3 * a1
    + (156728328192 : R) * w1 ^ 7 * b2
    - (1714090051215360 : R) * w1 ^ 6 * e1n * e3 * a2
    + (18102121906176 : R) * w1 ^ 6 * e1n * b3
    - (1175644753920 : R) * w1 ^ 6 * e3 ^ 3
    + (14511867728117760 : R) * w1 ^ 6 * a2 * a1
    + (313770113040384 : R) * w1 ^ 5 * e1n ^ 2 * b4
    + (30711438336983040 : R) * w1 ^ 5 * e1n * a2 ^ 2
    + (126384519905280 : R) * w1 ^ 5 * e3 ^ 2 * a2
    - (6582589784064 : R) * w1 ^ 5 * e3 * b3
    + (710912924467200 : R) * w1 ^ 4 * e1n ^ 3 * b5
    - (139453383573504 : R) * w1 ^ 4 * e1n * e3 * b4
    - (3816479910297600 : R) * w1 ^ 4 * e3 * a2 ^ 2
    + (592433080565760 : R) * w1 ^ 4 * a2 * b3
    + (789910774087680 : R) * w1 ^ 4 * a1 * b4
    + (987388467609600 : R) * w1 ^ 4 * a0 * b5
    + (538621086302208 : R) * w1 ^ 3 * e1n ^ 4 * b6
    - (299331757670400 : R) * w1 ^ 3 * e1n ^ 2 * e3 * b5
    + (6951214811971584 : R) * w1 ^ 3 * e1n * a2 * b4
    + (8689018514964480 : R) * w1 ^ 3 * e1n * a1 * b5
    + (10426822217957376 : R) * w1 ^ 3 * e1n * a0 * b6
    + (14302911135744 : R) * w1 ^ 3 * e3 ^ 2 * b4
    + (28524555730944000 : R) * w1 ^ 3 * a2 ^ 3
    + (175637310750720 : R) * w1 ^ 2 * e1n ^ 5 * b7
    - (187346464800768 : R) * w1 ^ 2 * e1n ^ 3 * e3 * b6
    + (8557366719283200 : R) * w1 ^ 2 * e1n ^ 2 * a2 * b5
    + (10268840063139840 : R) * w1 ^ 2 * e1n ^ 2 * a1 * b6
    + (11980313406996480 : R) * w1 ^ 2 * e1n ^ 2 * a0 * b7
    + (35215500902400 : R) * w1 ^ 2 * e1n * e3 ^ 2 * b5
    - (1263857238540288 : R) * w1 ^ 2 * e3 * a2 * b4
    - (1579821548175360 : R) * w1 ^ 2 * e3 * a1 * b5
    - (1895785857810432 : R) * w1 ^ 2 * e3 * a0 * b6
    - (43367237222400 : R) * w1 * e1n ^ 4 * e3 * b7
    + (2890488314068992 : R) * w1 * e1n ^ 3 * a2 * b6
    + (3372236366413824 : R) * w1 * e1n ^ 3 * a1 * b7
    + (17842520457216 : R) * w1 * e1n ^ 2 * e3 ^ 2 * b6
    - (1521309638983680 : R) * w1 * e1n * e3 * a2 * b5
    - (1825571566780416 : R) * w1 * e1n * e3 * a1 * b6
    - (2129833494577152 : R) * w1 * e1n * e3 * a0 * b7
    - (1043422248960 : R) * w1 * e3 ^ 3 * b5
    + (22749430293725184 : R) * w1 * a2 ^ 2 * b4
    + (56873575734312960 : R) * w1 * a2 * a1 * b5
    + (68248290881175552 : R) * w1 * a2 * a0 * b6
    + (34124145440587776 : R) * w1 * a1 ^ 2 * b6
    + (79623006028038144 : R) * w1 * a1 * a0 * b7
    + (281019697201152 : R) * e1n ^ 4 * a2 * b7
    + (2312919318528 : R) * e1n ^ 3 * e3 ^ 2 * b7
    - (304261927796736 : R) * e1n ^ 2 * e3 * a2 * b6
    - (354972249096192 : R) * e1n ^ 2 * e3 * a1 * b7
    - (417368899584 : R) * e1n * e3 ^ 3 * b6
    + (9478929289052160 : R) * e1n * a2 ^ 2 * b5
    + (22749430293725184 : R) * e1n * a2 * a1 * b6
    + (26541002009346048 : R) * e1n * a2 * a0 * b7
    + (13270501004673024 : R) * e1n * a1 ^ 2 * b7
    + (39007939461120 : R) * e3 ^ 2 * a2 * b5
    + (46809527353344 : R) * e3 ^ 2 * a1 * b6
    + (54611115245568 : R) * e3 ^ 2 * a0 * b7

end Max11DegreeRoutes
