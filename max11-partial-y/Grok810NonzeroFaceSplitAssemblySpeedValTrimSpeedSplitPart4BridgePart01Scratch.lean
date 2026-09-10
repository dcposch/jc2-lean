import Grok810NonzeroFaceSplit4SpeedValChainScratch

/-! Bridge helper for `degreeZeroClearedSource810_eq_sum_groups`:
`h`-degree band decomposition, so that no single module runs a `ring`
over all 4497 monomials at once.  No public statement is changed. -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1600000000

section DegreeZeroSourceEqExpansion810Band

variable {R : Type*} [CommRing R]

def nfsBand810Src5b0
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (-2422444018316083200 : R) * h ^ 95 * a7 ^ 2 * a4 * a3 ^ 2 * lambda
    + (-4844888036632166400 : R) * h ^ 95 * a7 * a6 ^ 2 * a5 * a0 * lambda
    + (-4844888036632166400 : R) * h ^ 95 * a7 * a6 ^ 2 * a4 * a1 * lambda
    + (-4844888036632166400 : R) * h ^ 95 * a7 * a6 ^ 2 * a3 * a2 * lambda
    + (-4844888036632166400 : R) * h ^ 95 * a7 * a6 * a5 ^ 2 * a1 * lambda
    + (-9689776073264332800 : R) * h ^ 95 * a7 * a6 * a5 * a4 * a2 * lambda
    + (-4844888036632166400 : R) * h ^ 95 * a7 * a6 * a5 * a3 ^ 2 * lambda
    + (-4844888036632166400 : R) * h ^ 95 * a7 * a6 * a4 ^ 2 * a3 * lambda
    + (-1614962678877388800 : R) * h ^ 95 * a7 * a5 ^ 3 * a2 * lambda
    + (-4844888036632166400 : R) * h ^ 95 * a7 * a5 ^ 2 * a4 * a3 * lambda
    + (-1614962678877388800 : R) * h ^ 95 * a7 * a5 * a4 ^ 3 * lambda
    + (-403740669719347200 : R) * h ^ 95 * a6 ^ 4 * a0 * lambda
    + (-1614962678877388800 : R) * h ^ 95 * a6 ^ 3 * a5 * a1 * lambda
    + (-1614962678877388800 : R) * h ^ 95 * a6 ^ 3 * a4 * a2 * lambda
    + (-807481339438694400 : R) * h ^ 95 * a6 ^ 3 * a3 ^ 2 * lambda
    + (-2422444018316083200 : R) * h ^ 95 * a6 ^ 2 * a5 ^ 2 * a2 * lambda
    + (-4844888036632166400 : R) * h ^ 95 * a6 ^ 2 * a5 * a4 * a3 * lambda
    + (-807481339438694400 : R) * h ^ 95 * a6 ^ 2 * a4 ^ 3 * lambda
    + (-1614962678877388800 : R) * h ^ 95 * a6 * a5 ^ 3 * a3 * lambda
    + (-2422444018316083200 : R) * h ^ 95 * a6 * a5 ^ 2 * a4 ^ 2 * lambda
    + (-403740669719347200 : R) * h ^ 95 * a5 ^ 4 * a4 * lambda

def nfsBand810Src5b1
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (-229683580995895296 : R) * h ^ 94 * a7 ^ 3 * a3 * b1
    + (-459367161991790592 : R) * h ^ 94 * a7 ^ 3 * a2 * b2
    + (-689050742987685888 : R) * h ^ 94 * a7 ^ 3 * a1 * b3
    + (-918734323983581184 : R) * h ^ 94 * a7 ^ 3 * a0 * b4
    + (-689050742987685888 : R) * h ^ 94 * a7 ^ 2 * a6 * a4 * b1
    + (-1378101485975371776 : R) * h ^ 94 * a7 ^ 2 * a6 * a3 * b2
    + (-2067152228963057664 : R) * h ^ 94 * a7 ^ 2 * a6 * a2 * b3
    + (-2756202971950743552 : R) * h ^ 94 * a7 ^ 2 * a6 * a1 * b4
    + (-3445253714938429440 : R) * h ^ 94 * a7 ^ 2 * a6 * a0 * b5
    + (-344525371493842944 : R) * h ^ 94 * a7 ^ 2 * a5 ^ 2 * b1
    + (-1378101485975371776 : R) * h ^ 94 * a7 ^ 2 * a5 * a4 * b2
    + (-2067152228963057664 : R) * h ^ 94 * a7 ^ 2 * a5 * a3 * b3
    + (-2756202971950743552 : R) * h ^ 94 * a7 ^ 2 * a5 * a2 * b4
    + (-3445253714938429440 : R) * h ^ 94 * a7 ^ 2 * a5 * a1 * b5
    + (-4134304457926115328 : R) * h ^ 94 * a7 ^ 2 * a5 * a0 * b6
    + (-1033576114481528832 : R) * h ^ 94 * a7 ^ 2 * a4 ^ 2 * b3
    + (-2756202971950743552 : R) * h ^ 94 * a7 ^ 2 * a4 * a3 * b4
    + (-3445253714938429440 : R) * h ^ 94 * a7 ^ 2 * a4 * a2 * b5
    + (-4134304457926115328 : R) * h ^ 94 * a7 ^ 2 * a4 * a1 * b6

def nfsBand810Src9b1
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (832715131296153600 : R) * h ^ 87 * a7 ^ 4 * a2 ^ 2 * lambda
    + (6661721050369228800 : R) * h ^ 87 * a7 ^ 3 * a6 * a5 * a0 * lambda
    + (6661721050369228800 : R) * h ^ 87 * a7 ^ 3 * a6 * a4 * a1 * lambda
    + (6661721050369228800 : R) * h ^ 87 * a7 ^ 3 * a6 * a3 * a2 * lambda
    + (3330860525184614400 : R) * h ^ 87 * a7 ^ 3 * a5 ^ 2 * a1 * lambda
    + (6661721050369228800 : R) * h ^ 87 * a7 ^ 3 * a5 * a4 * a2 * lambda
    + (3330860525184614400 : R) * h ^ 87 * a7 ^ 3 * a5 * a3 ^ 2 * lambda
    + (3330860525184614400 : R) * h ^ 87 * a7 ^ 3 * a4 ^ 2 * a3 * lambda
    + (3330860525184614400 : R) * h ^ 87 * a7 ^ 2 * a6 ^ 3 * a0 * lambda
    + (9992581575553843200 : R) * h ^ 87 * a7 ^ 2 * a6 ^ 2 * a5 * a1 * lambda
    + (9992581575553843200 : R) * h ^ 87 * a7 ^ 2 * a6 ^ 2 * a4 * a2 * lambda
    + (4996290787776921600 : R) * h ^ 87 * a7 ^ 2 * a6 ^ 2 * a3 ^ 2 * lambda
    + (9992581575553843200 : R) * h ^ 87 * a7 ^ 2 * a6 * a5 ^ 2 * a2 * lambda
    + (19985163151107686400 : R) * h ^ 87 * a7 ^ 2 * a6 * a5 * a4 * a3 * lambda
    + (3330860525184614400 : R) * h ^ 87 * a7 ^ 2 * a6 * a4 ^ 3 * lambda
    + (3330860525184614400 : R) * h ^ 87 * a7 ^ 2 * a5 ^ 3 * a3 * lambda
    + (4996290787776921600 : R) * h ^ 87 * a7 ^ 2 * a5 ^ 2 * a4 ^ 2 * lambda
    + (1665430262592307200 : R) * h ^ 87 * a7 * a6 ^ 4 * a1 * lambda
    + (6661721050369228800 : R) * h ^ 87 * a7 * a6 ^ 3 * a5 * a2 * lambda
    + (6661721050369228800 : R) * h ^ 87 * a7 * a6 ^ 3 * a4 * a3 * lambda
    + (9992581575553843200 : R) * h ^ 87 * a7 * a6 ^ 2 * a5 ^ 2 * a3 * lambda
    + (9992581575553843200 : R) * h ^ 87 * a7 * a6 ^ 2 * a5 * a4 ^ 2 * lambda
    + (6661721050369228800 : R) * h ^ 87 * a7 * a6 * a5 ^ 3 * a4 * lambda
    + (333086052518461440 : R) * h ^ 87 * a7 * a5 ^ 5 * lambda
    + (333086052518461440 : R) * h ^ 87 * a6 ^ 5 * a2 * lambda
    + (1665430262592307200 : R) * h ^ 87 * a6 ^ 4 * a5 * a3 * lambda
    + (832715131296153600 : R) * h ^ 87 * a6 ^ 4 * a4 ^ 2 * lambda
    + (3330860525184614400 : R) * h ^ 87 * a6 ^ 3 * a5 ^ 2 * a4 * lambda
    + (832715131296153600 : R) * h ^ 87 * a6 ^ 2 * a5 ^ 4 * lambda

def nfsBand810Src9b2
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (179440297653043200 : R) * h ^ 86 * a7 ^ 4 * a4 * b1
    + (358880595306086400 : R) * h ^ 86 * a7 ^ 4 * a3 * b2
    + (538320892959129600 : R) * h ^ 86 * a7 ^ 4 * a2 * b3
    + (717761190612172800 : R) * h ^ 86 * a7 ^ 4 * a1 * b4
    + (897201488265216000 : R) * h ^ 86 * a7 ^ 4 * a0 * b5
    + (717761190612172800 : R) * h ^ 86 * a7 ^ 3 * a6 * a5 * b1
    + (1435522381224345600 : R) * h ^ 86 * a7 ^ 3 * a6 * a4 * b2
    + (2153283571836518400 : R) * h ^ 86 * a7 ^ 3 * a6 * a3 * b3
    + (2871044762448691200 : R) * h ^ 86 * a7 ^ 3 * a6 * a2 * b4
    + (3588805953060864000 : R) * h ^ 86 * a7 ^ 3 * a6 * a1 * b5
    + (4306567143673036800 : R) * h ^ 86 * a7 ^ 3 * a6 * a0 * b6

def nfsBand810Src13b2
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (59215298225504256000 : R) * h ^ 80 * a7 * a6 ^ 3 * a5 ^ 2 * a4
    + (14803824556376064000 : R) * h ^ 80 * a7 * a6 ^ 2 * a5 ^ 4
    + (1264493347523788800 : R) * h ^ 80 * a6 ^ 6 * a3
    + (7586960085142732800 : R) * h ^ 80 * a6 ^ 5 * a5 * a4
    + (6322466737618944000 : R) * h ^ 80 * a6 ^ 4 * a5 ^ 3
    + (-1707066019157114880 : R) * h ^ 79 * a7 ^ 5 * a5 * a0 * lambda
    + (-1707066019157114880 : R) * h ^ 79 * a7 ^ 5 * a4 * a1 * lambda
    + (-1707066019157114880 : R) * h ^ 79 * a7 ^ 5 * a3 * a2 * lambda
    + (-4267665047892787200 : R) * h ^ 79 * a7 ^ 4 * a6 ^ 2 * a0 * lambda
    + (-8535330095785574400 : R) * h ^ 79 * a7 ^ 4 * a6 * a5 * a1 * lambda
    + (-8535330095785574400 : R) * h ^ 79 * a7 ^ 4 * a6 * a4 * a2 * lambda
    + (-4267665047892787200 : R) * h ^ 79 * a7 ^ 4 * a6 * a3 ^ 2 * lambda
    + (-4267665047892787200 : R) * h ^ 79 * a7 ^ 4 * a5 ^ 2 * a2 * lambda
    + (-8535330095785574400 : R) * h ^ 79 * a7 ^ 4 * a5 * a4 * a3 * lambda
    + (-1422555015964262400 : R) * h ^ 79 * a7 ^ 4 * a4 ^ 3 * lambda
    + (-5690220063857049600 : R) * h ^ 79 * a7 ^ 3 * a6 ^ 3 * a1 * lambda
    + (-17070660191571148800 : R) * h ^ 79 * a7 ^ 3 * a6 ^ 2 * a5 * a2 * lambda
    + (-17070660191571148800 : R) * h ^ 79 * a7 ^ 3 * a6 ^ 2 * a4 * a3 * lambda
    + (-17070660191571148800 : R) * h ^ 79 * a7 ^ 3 * a6 * a5 ^ 2 * a3 * lambda
    + (-17070660191571148800 : R) * h ^ 79 * a7 ^ 3 * a6 * a5 * a4 ^ 2 * lambda
    + (-5690220063857049600 : R) * h ^ 79 * a7 ^ 3 * a5 ^ 3 * a4 * lambda
    + (-4267665047892787200 : R) * h ^ 79 * a7 ^ 2 * a6 ^ 4 * a2 * lambda
    + (-17070660191571148800 : R) * h ^ 79 * a7 ^ 2 * a6 ^ 3 * a5 * a3 * lambda
    + (-8535330095785574400 : R) * h ^ 79 * a7 ^ 2 * a6 ^ 3 * a4 ^ 2 * lambda
    + (-25605990287356723200 : R) * h ^ 79 * a7 ^ 2 * a6 ^ 2 * a5 ^ 2 * a4 * lambda
    + (-4267665047892787200 : R) * h ^ 79 * a7 ^ 2 * a6 * a5 ^ 4 * lambda
    + (-1707066019157114880 : R) * h ^ 79 * a7 * a6 ^ 5 * a3 * lambda
    + (-8535330095785574400 : R) * h ^ 79 * a7 * a6 ^ 4 * a5 * a4 * lambda
    + (-5690220063857049600 : R) * h ^ 79 * a7 * a6 ^ 3 * a5 ^ 3 * lambda
    + (-284511003192852480 : R) * h ^ 79 * a6 ^ 6 * a4 * lambda
    + (-853533009578557440 : R) * h ^ 79 * a6 ^ 5 * a5 ^ 2 * lambda

def nfsBand810Src13b3
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (-148038245563760640 : R) * h ^ 78 * a7 ^ 5 * a5 * b1
    + (-296076491127521280 : R) * h ^ 78 * a7 ^ 5 * a4 * b2
    + (-444114736691281920 : R) * h ^ 78 * a7 ^ 5 * a3 * b3
    + (-592152982255042560 : R) * h ^ 78 * a7 ^ 5 * a2 * b4
    + (-740191227818803200 : R) * h ^ 78 * a7 ^ 5 * a1 * b5
    + (-888229473382563840 : R) * h ^ 78 * a7 ^ 5 * a0 * b6
    + (-370095613909401600 : R) * h ^ 78 * a7 ^ 4 * a6 ^ 2 * b1
    + (-1480382455637606400 : R) * h ^ 78 * a7 ^ 4 * a6 * a5 * b2
    + (-2220573683456409600 : R) * h ^ 78 * a7 ^ 4 * a6 * a4 * b3

def nfsBand810Src17b3
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (5227889683668664320 : R) * h ^ 71 * a7 ^ 2 * a6 ^ 5 * a4 * lambda
    + (13069724209171660800 : R) * h ^ 71 * a7 ^ 2 * a6 ^ 4 * a5 ^ 2 * lambda
    + (1742629894556221440 : R) * h ^ 71 * a7 * a6 ^ 6 * a5 * lambda
    + (31118390974218240 : R) * h ^ 71 * a6 ^ 8 * lambda

def nfsBand810Src17b4
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (126449334752378880 : R) * h ^ 70 * a7 ^ 6 * a6 * b1
    + (252898669504757760 : R) * h ^ 70 * a7 ^ 6 * a5 * b2
    + (379348004257136640 : R) * h ^ 70 * a7 ^ 6 * a4 * b3
    + (505797339009515520 : R) * h ^ 70 * a7 ^ 6 * a3 * b4
    + (632246673761894400 : R) * h ^ 70 * a7 ^ 6 * a2 * b5
    + (758696008514273280 : R) * h ^ 70 * a7 ^ 6 * a1 * b6
    + (885145343266652160 : R) * h ^ 70 * a7 ^ 6 * a0 * b7
    + (758696008514273280 : R) * h ^ 70 * a7 ^ 5 * a6 ^ 2 * b2
    + (2276088025542819840 : R) * h ^ 70 * a7 ^ 5 * a6 * a5 * b3
    + (3034784034057093120 : R) * h ^ 70 * a7 ^ 5 * a6 * a4 * b4
    + (3793480042571366400 : R) * h ^ 70 * a7 ^ 5 * a6 * a3 * b5
    + (4552176051085639680 : R) * h ^ 70 * a7 ^ 5 * a6 * a2 * b6
    + (5310872059599912960 : R) * h ^ 70 * a7 ^ 5 * a6 * a1 * b7
    + (6069568068114186240 : R) * h ^ 70 * a7 ^ 5 * a6 * a0 * b8
    + (1517392017028546560 : R) * h ^ 70 * a7 ^ 5 * a5 ^ 2 * b4
    + (3793480042571366400 : R) * h ^ 70 * a7 ^ 5 * a5 * a4 * b5
    + (4552176051085639680 : R) * h ^ 70 * a7 ^ 5 * a5 * a3 * b6
    + (5310872059599912960 : R) * h ^ 70 * a7 ^ 5 * a5 * a2 * b7
    + (6069568068114186240 : R) * h ^ 70 * a7 ^ 5 * a5 * a1 * b8
    + (2276088025542819840 : R) * h ^ 70 * a7 ^ 5 * a4 ^ 2 * b6
    + (5310872059599912960 : R) * h ^ 70 * a7 ^ 5 * a4 * a3 * b7
    + (6069568068114186240 : R) * h ^ 70 * a7 ^ 5 * a4 * a2 * b8
    + (3034784034057093120 : R) * h ^ 70 * a7 ^ 5 * a3 ^ 2 * b8
    + (1896740021285683200 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 3 * b3
    + (7586960085142732800 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a5 * b4
    + (9483700106428416000 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a4 * b5
    + (11380440127714099200 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a3 * b6
    + (13277180148999782400 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a2 * b7
    + (15173920170285465600 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a1 * b8
    + (9483700106428416000 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 ^ 2 * b5
    + (22760880255428198400 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 * a4 * b6
    + (26554360297999564800 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 * a3 * b7
    + (30347840340570931200 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 * a2 * b8
    + (13277180148999782400 : R) * h ^ 70 * a7 ^ 4 * a6 * a4 ^ 2 * b7
    + (30347840340570931200 : R) * h ^ 70 * a7 ^ 4 * a6 * a4 * a3 * b8
    + (3793480042571366400 : R) * h ^ 70 * a7 ^ 4 * a5 ^ 3 * b6

def nfsBand810Src19b4
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (34852597891124428800 : R) * h ^ 64 * a7 ^ 5 * a6 * a5 ^ 2 * a4
    + (2904383157593702400 : R) * h ^ 64 * a7 ^ 5 * a5 ^ 4
    + (25413352628944896000 : R) * h ^ 64 * a7 ^ 4 * a6 ^ 4 * a3
    + (101653410515779584000 : R) * h ^ 64 * a7 ^ 4 * a6 ^ 3 * a5 * a4
    + (50826705257889792000 : R) * h ^ 64 * a7 ^ 4 * a6 ^ 2 * a5 ^ 3
    + (29043831575937024000 : R) * h ^ 64 * a7 ^ 3 * a6 ^ 5 * a4
    + (72609578939842560000 : R) * h ^ 64 * a7 ^ 3 * a6 ^ 4 * a5 ^ 2
    + (18878490524359065600 : R) * h ^ 64 * a7 ^ 2 * a6 ^ 6 * a5
    + (829823759312486400 : R) * h ^ 64 * a7 * a6 ^ 8
    + (-221718535691304960 : R) * h ^ 63 * a7 ^ 8 * a0 * lambda
    + (-1773748285530439680 : R) * h ^ 63 * a7 ^ 7 * a6 * a1 * lambda
    + (-1773748285530439680 : R) * h ^ 63 * a7 ^ 7 * a5 * a2 * lambda
    + (-1773748285530439680 : R) * h ^ 63 * a7 ^ 7 * a4 * a3 * lambda
    + (-6208118999356538880 : R) * h ^ 63 * a7 ^ 6 * a6 ^ 2 * a2 * lambda
    + (-12416237998713077760 : R) * h ^ 63 * a7 ^ 6 * a6 * a5 * a3 * lambda
    + (-6208118999356538880 : R) * h ^ 63 * a7 ^ 6 * a6 * a4 ^ 2 * lambda
    + (-6208118999356538880 : R) * h ^ 63 * a7 ^ 6 * a5 ^ 2 * a4 * lambda
    + (-12416237998713077760 : R) * h ^ 63 * a7 ^ 5 * a6 ^ 3 * a3 * lambda
    + (-37248713996139233280 : R) * h ^ 63 * a7 ^ 5 * a6 ^ 2 * a5 * a4 * lambda
    + (-12416237998713077760 : R) * h ^ 63 * a7 ^ 5 * a6 * a5 ^ 3 * lambda
    + (-15520297498391347200 : R) * h ^ 63 * a7 ^ 4 * a6 ^ 4 * a4 * lambda
    + (-31040594996782694400 : R) * h ^ 63 * a7 ^ 4 * a6 ^ 3 * a5 ^ 2 * lambda
    + (-12416237998713077760 : R) * h ^ 63 * a7 ^ 3 * a6 ^ 5 * a5 * lambda
    + (-886874142765219840 : R) * h ^ 63 * a7 ^ 2 * a6 ^ 7 * lambda

def nfsBand810Src19b5
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (-13830395988541440 : R) * h ^ 62 * a7 ^ 8 * b1
    + (-221286335816663040 : R) * h ^ 62 * a7 ^ 7 * a6 * b2
    + (-331929503724994560 : R) * h ^ 62 * a7 ^ 7 * a5 * b3
    + (-442572671633326080 : R) * h ^ 62 * a7 ^ 7 * a4 * b4
    + (-553215839541657600 : R) * h ^ 62 * a7 ^ 7 * a3 * b5
    + (-663859007449989120 : R) * h ^ 62 * a7 ^ 7 * a2 * b6
    + (-774502175358320640 : R) * h ^ 62 * a7 ^ 7 * a1 * b7
    + (-885145343266652160 : R) * h ^ 62 * a7 ^ 7 * a0 * b8
    + (-1161753263037480960 : R) * h ^ 62 * a7 ^ 6 * a6 ^ 2 * b3
    + (-3098008701433282560 : R) * h ^ 62 * a7 ^ 6 * a6 * a5 * b4
    + (-3872510876791603200 : R) * h ^ 62 * a7 ^ 6 * a6 * a4 * b5
    + (-4647013052149923840 : R) * h ^ 62 * a7 ^ 6 * a6 * a3 * b6
    + (-5421515227508244480 : R) * h ^ 62 * a7 ^ 6 * a6 * a2 * b7
    + (-6196017402866565120 : R) * h ^ 62 * a7 ^ 6 * a6 * a1 * b8
    + (-1936255438395801600 : R) * h ^ 62 * a7 ^ 6 * a5 ^ 2 * b5
    + (-4647013052149923840 : R) * h ^ 62 * a7 ^ 6 * a5 * a4 * b6

def nfsBand810Src21b5
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (-34489549996425216000 : R) * h ^ 56 * a7 ^ 5 * a6 ^ 4 * a4
    + (-68979099992850432000 : R) * h ^ 56 * a7 ^ 5 * a6 ^ 3 * a5 ^ 2
    + (-50009847494816563200 : R) * h ^ 56 * a7 ^ 4 * a6 ^ 5 * a5
    + (-6240966189829324800 : R) * h ^ 56 * a7 ^ 3 * a6 ^ 7
    + (200162566943539200 : R) * h ^ 55 * a7 ^ 9 * a1 * lambda
    + (1801463102491852800 : R) * h ^ 55 * a7 ^ 8 * a6 * a2 * lambda
    + (1801463102491852800 : R) * h ^ 55 * a7 ^ 8 * a5 * a3 * lambda
    + (900731551245926400 : R) * h ^ 55 * a7 ^ 8 * a4 ^ 2 * lambda
    + (7205852409967411200 : R) * h ^ 55 * a7 ^ 7 * a6 ^ 2 * a3 * lambda
    + (14411704819934822400 : R) * h ^ 55 * a7 ^ 7 * a6 * a5 * a4 * lambda
    + (2401950803322470400 : R) * h ^ 55 * a7 ^ 7 * a5 ^ 3 * lambda
    + (16813655623257292800 : R) * h ^ 55 * a7 ^ 6 * a6 ^ 3 * a4 * lambda
    + (25220483434885939200 : R) * h ^ 55 * a7 ^ 6 * a6 ^ 2 * a5 ^ 2 * lambda
    + (25220483434885939200 : R) * h ^ 55 * a7 ^ 5 * a6 ^ 4 * a5 * lambda
    + (4203413905814323200 : R) * h ^ 55 * a7 ^ 4 * a6 ^ 6 * lambda

def nfsBand810Src21b6
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (21898126981857280 : R) * h ^ 54 * a7 ^ 9 * b2
    + (295624714255073280 : R) * h ^ 54 * a7 ^ 8 * a6 * b3
    + (394166285673431040 : R) * h ^ 54 * a7 ^ 8 * a5 * b4
    + (492707857091788800 : R) * h ^ 54 * a7 ^ 8 * a4 * b5
    + (591249428510146560 : R) * h ^ 54 * a7 ^ 8 * a3 * b6
    + (689790999928504320 : R) * h ^ 54 * a7 ^ 8 * a2 * b7
    + (788332571346862080 : R) * h ^ 54 * a7 ^ 8 * a1 * b8
    + (1576665142693724160 : R) * h ^ 54 * a7 ^ 7 * a6 ^ 2 * b4
    + (3941662856734310400 : R) * h ^ 54 * a7 ^ 7 * a6 * a5 * b5
    + (4729995428081172480 : R) * h ^ 54 * a7 ^ 7 * a6 * a4 * b6
    + (5518327999428034560 : R) * h ^ 54 * a7 ^ 7 * a6 * a3 * b7
    + (6306660570774896640 : R) * h ^ 54 * a7 ^ 7 * a6 * a2 * b8
    + (2364997714040586240 : R) * h ^ 54 * a7 ^ 7 * a5 ^ 2 * b6
    + (5518327999428034560 : R) * h ^ 54 * a7 ^ 7 * a5 * a4 * b7
    + (6306660570774896640 : R) * h ^ 54 * a7 ^ 7 * a5 * a3 * b8
    + (3153330285387448320 : R) * h ^ 54 * a7 ^ 7 * a4 ^ 2 * b8
    + (4598606666190028800 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 3 * b5
    + (16554983998284103680 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a5 * b6
    + (19314147997998120960 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a4 * b7
    + (22073311997712138240 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a3 * b8
    + (19314147997998120960 : R) * h ^ 54 * a7 ^ 6 * a6 * a5 ^ 2 * b7
    + (44146623995424276480 : R) * h ^ 54 * a7 ^ 6 * a6 * a5 * a4 * b8
    + (7357770665904046080 : R) * h ^ 54 * a7 ^ 6 * a5 ^ 3 * b8
    + (8277491999142051840 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 4 * b6
    + (38628295995996241920 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 3 * a5 * b7

def nfsBand810Src23b6
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (-59781886660470374400 : R) * h ^ 46 * a7 ^ 6 * a6 ^ 3 * a5 * b8
    + (-17934565998141112320 : R) * h ^ 46 * a7 ^ 5 * a6 ^ 5 * b8

def nfsBand810Src23b7
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (166043947578163200 : R) * h ^ 40 * a7 ^ 11 * a2
    + (913241711679897600 : R) * h ^ 40 * a7 ^ 10 * a6 * a3
    + (913241711679897600 : R) * h ^ 40 * a7 ^ 10 * a5 * a4
    + (-13698625675198464000 : R) * h ^ 40 * a7 ^ 8 * a6 ^ 3 * a5
    + (-10958900540158771200 : R) * h ^ 40 * a7 ^ 7 * a6 ^ 5
    + (168119496922890240 : R) * h ^ 39 * a7 ^ 11 * a3 * lambda
    + (1849314466151792640 : R) * h ^ 39 * a7 ^ 10 * a6 * a4 * lambda
    + (924657233075896320 : R) * h ^ 39 * a7 ^ 10 * a5 ^ 2 * lambda
    + (9246572330758963200 : R) * h ^ 39 * a7 ^ 9 * a6 ^ 2 * a5 * lambda
    + (6934929248069222400 : R) * h ^ 39 * a7 ^ 8 * a6 ^ 4 * lambda
    + (29518924013895680 : R) * h ^ 38 * a7 ^ 11 * b4
    + (405885205191065600 : R) * h ^ 38 * a7 ^ 10 * a6 * b5
    + (487062246229278720 : R) * h ^ 38 * a7 ^ 10 * a5 * b6
    + (568239287267491840 : R) * h ^ 38 * a7 ^ 10 * a4 * b7
    + (649416328305704960 : R) * h ^ 38 * a7 ^ 10 * a3 * b8
    + (2435311231146393600 : R) * h ^ 38 * a7 ^ 9 * a6 ^ 2 * b6
    + (5682392872674918400 : R) * h ^ 38 * a7 ^ 9 * a6 * a5 * b7
    + (6494163283057049600 : R) * h ^ 38 * a7 ^ 9 * a6 * a4 * b8
    + (3247081641528524800 : R) * h ^ 38 * a7 ^ 9 * a5 ^ 2 * b8
    + (8523589309012377600 : R) * h ^ 38 * a7 ^ 8 * a6 ^ 3 * b7
    + (29223734773756723200 : R) * h ^ 38 * a7 ^ 8 * a6 ^ 2 * a5 * b8
    + (19482489849171148800 : R) * h ^ 38 * a7 ^ 7 * a6 ^ 4 * b8
    + (-147882890811801600 : R) * h ^ 32 * a7 ^ 12 * a3
    + (-933997205127168000 : R) * h ^ 32 * a7 ^ 11 * a6 * a4
    + (-466998602563584000 : R) * h ^ 32 * a7 ^ 11 * a5 ^ 2
    + (-513698462819942400 : R) * h ^ 32 * a7 ^ 10 * a6 ^ 2 * a5
    + (3424656418799616000 : R) * h ^ 32 * a7 ^ 9 * a6 ^ 4
    + (-155860783605596160 : R) * h ^ 31 * a7 ^ 12 * a4 * lambda
    + (-1870329403267153920 : R) * h ^ 31 * a7 ^ 11 * a6 * a5 * lambda
    + (-3428937239323115520 : R) * h ^ 31 * a7 ^ 10 * a6 ^ 3 * lambda
    + (-31133240170905600 : R) * h ^ 30 * a7 ^ 12 * b5
    + (-448318658461040640 : R) * h ^ 30 * a7 ^ 11 * a6 * b6
    + (-523038434871214080 : R) * h ^ 30 * a7 ^ 11 * a5 * b7
    + (-597758211281387520 : R) * h ^ 30 * a7 ^ 11 * a4 * b8
    + (-2876711391791677440 : R) * h ^ 30 * a7 ^ 10 * a6 ^ 2 * b7
    + (-6575340324095262720 : R) * h ^ 30 * a7 ^ 10 * a6 * a5 * b8
    + (-10958900540158771200 : R) * h ^ 30 * a7 ^ 9 * a6 ^ 3 * b8
    + (133214344962048000 : R) * h ^ 24 * a7 ^ 13 * a4

set_option maxHeartbeats 1600000000 in
theorem nfsBand810Src5_split (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroClearedSourceBlock5_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda =
      nfsBand810Src5b0 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      nfsBand810Src5b1 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroClearedSourceBlock5_810, nfsBand810Src5b0, nfsBand810Src5b1]
  ring

set_option maxHeartbeats 1600000000 in
theorem nfsBand810Src9_split (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroClearedSourceBlock9_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda =
      nfsBand810Src9b1 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      nfsBand810Src9b2 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroClearedSourceBlock9_810, nfsBand810Src9b1, nfsBand810Src9b2]
  ring

set_option maxHeartbeats 1600000000 in
theorem nfsBand810Src13_split (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroClearedSourceBlock13_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda =
      nfsBand810Src13b2 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      nfsBand810Src13b3 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroClearedSourceBlock13_810, nfsBand810Src13b2, nfsBand810Src13b3]
  ring

set_option maxHeartbeats 1600000000 in
theorem nfsBand810Src17_split (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroClearedSourceBlock17_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda =
      nfsBand810Src17b3 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      nfsBand810Src17b4 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroClearedSourceBlock17_810, nfsBand810Src17b3, nfsBand810Src17b4]
  ring

set_option maxHeartbeats 1600000000 in
theorem nfsBand810Src19_split (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroClearedSourceBlock19_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda =
      nfsBand810Src19b4 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      nfsBand810Src19b5 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroClearedSourceBlock19_810, nfsBand810Src19b4, nfsBand810Src19b5]
  ring

set_option maxHeartbeats 1600000000 in
theorem nfsBand810Src21_split (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroClearedSourceBlock21_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda =
      nfsBand810Src21b5 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      nfsBand810Src21b6 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroClearedSourceBlock21_810, nfsBand810Src21b5, nfsBand810Src21b6]
  ring

set_option maxHeartbeats 1600000000 in
theorem nfsBand810Src23_split (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroClearedSourceBlock23_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda =
      nfsBand810Src23b6 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      nfsBand810Src23b7 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroClearedSourceBlock23_810, nfsBand810Src23b6, nfsBand810Src23b7]
  ring

end DegreeZeroSourceEqExpansion810Band

end Max11DegreeRoutes

end
