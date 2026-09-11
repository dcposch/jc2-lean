import Grok810SpeedValLibScratch
import Grok810DegreeZeroSourceNumeratorScratch

/-! Bridge helper for `alignedSquareClearedNumerator810_eq_sum_expansions`:
`h`-degree band decomposition, so that no single module runs a `ring` over
all 5845 monomials at once.  No public statement is changed. -/

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

section AlignedSquareSourceEqExpansion810Band

variable {R : Type*} [CommRing R]

def asqBand810Src20b4
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    (-5421515227508244480 : R) * h ^ 62 * a7 ^ 6 * a5 * a3 * b7
    + (-6196017402866565120 : R) * h ^ 62 * a7 ^ 6 * a5 * a2 * b8
    + (-2710757613754122240 : R) * h ^ 62 * a7 ^ 6 * a4 ^ 2 * b7
    + (-6196017402866565120 : R) * h ^ 62 * a7 ^ 6 * a4 * a3 * b8
    + (-3098008701433282560 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 3 * b4
    + (-11617532630374809600 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a5 * b5
    + (-13941039156449771520 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a4 * b6
    + (-16264545682524733440 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a3 * b7
    + (-18588052208599695360 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a2 * b8
    + (-13941039156449771520 : R) * h ^ 62 * a7 ^ 5 * a6 * a5 ^ 2 * b6
    + (-32529091365049466880 : R) * h ^ 62 * a7 ^ 5 * a6 * a5 * a4 * b7
    + (-37176104417199390720 : R) * h ^ 62 * a7 ^ 5 * a6 * a5 * a3 * b8
    + (-18588052208599695360 : R) * h ^ 62 * a7 ^ 5 * a6 * a4 ^ 2 * b8
    + (-5421515227508244480 : R) * h ^ 62 * a7 ^ 5 * a5 ^ 3 * b7
    + (-18588052208599695360 : R) * h ^ 62 * a7 ^ 5 * a5 ^ 2 * a4 * b8
    + (-4840638595989504000 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 4 * b5
    + (-23235065260749619200 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 3 * a5 * b6
    + (-27107576137541222400 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 3 * a4 * b7
    + (-30980087014332825600 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 3 * a3 * b8
    + (-40661364206311833600 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 2 * a5 ^ 2 * b7
    + (-92940261042998476800 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 2 * a5 * a4 * b8
    + (-30980087014332825600 : R) * h ^ 62 * a7 ^ 4 * a6 * a5 ^ 3 * b8
    + (-4647013052149923840 : R) * h ^ 62 * a7 ^ 3 * a6 ^ 5 * b6
    + (-27107576137541222400 : R) * h ^ 62 * a7 ^ 3 * a6 ^ 4 * a5 * b7
    + (-30980087014332825600 : R) * h ^ 62 * a7 ^ 3 * a6 ^ 4 * a4 * b8
    + (-61960174028665651200 : R) * h ^ 62 * a7 ^ 3 * a6 ^ 3 * a5 ^ 2 * b8
    + (-2710757613754122240 : R) * h ^ 62 * a7 ^ 2 * a6 ^ 6 * b7
    + (-18588052208599695360 : R) * h ^ 62 * a7 ^ 2 * a6 ^ 5 * a5 * b8
    + (-885145343266652160 : R) * h ^ 62 * a7 * a6 ^ 7 * b8

def asqBand810Src20b5
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    (218981269818572800 : R) * h ^ 56 * a7 ^ 9 * a0
    + (862238749910630400 : R) * h ^ 56 * a7 ^ 8 * a6 * a1
    + (862238749910630400 : R) * h ^ 56 * a7 ^ 8 * a5 * a2
    + (862238749910630400 : R) * h ^ 56 * a7 ^ 8 * a4 * a3
    + (-985415714183577600 : R) * h ^ 56 * a7 ^ 7 * a6 ^ 2 * a2
    + (-1970831428367155200 : R) * h ^ 56 * a7 ^ 7 * a6 * a5 * a3
    + (-985415714183577600 : R) * h ^ 56 * a7 ^ 7 * a6 * a4 ^ 2
    + (-985415714183577600 : R) * h ^ 56 * a7 ^ 7 * a5 ^ 2 * a4
    + (-12646168332022579200 : R) * h ^ 56 * a7 ^ 6 * a6 ^ 3 * a3
    + (-37938504996067737600 : R) * h ^ 56 * a7 ^ 6 * a6 ^ 2 * a5 * a4
    + (-12646168332022579200 : R) * h ^ 56 * a7 ^ 6 * a6 * a5 ^ 3

set_option maxHeartbeats 1600000000 in
theorem asqBand810Src20_split (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) :
    degreeZeroClearedSourceBlock20_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 0 =
      asqBand810Src20b4 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      asqBand810Src20b5 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 := by
  simp only [degreeZeroClearedSourceBlock20_810, asqBand810Src20b4, asqBand810Src20b5]
  try ring

def asqBand810Src21b5
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    (-34489549996425216000 : R) * h ^ 56 * a7 ^ 5 * a6 ^ 4 * a4
    + (-68979099992850432000 : R) * h ^ 56 * a7 ^ 5 * a6 ^ 3 * a5 ^ 2
    + (-50009847494816563200 : R) * h ^ 56 * a7 ^ 4 * a6 ^ 5 * a5
    + (-6240966189829324800 : R) * h ^ 56 * a7 ^ 3 * a6 ^ 7
    + (21898126981857280 : R) * h ^ 54 * a7 ^ 9 * b2
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

set_option maxHeartbeats 1600000000 in
theorem asqBand810Src21_split (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) :
    degreeZeroClearedSourceBlock21_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 0 =
      asqBand810Src21b5 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 := by
  simp only [degreeZeroClearedSourceBlock21_810, asqBand810Src21b5]
  try ring

def asqBand810Src22b5
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    (44146623995424276480 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 3 * a4 * b8
    + (66219935993136414720 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 2 * a5 ^ 2 * b8
    + (9657073998999060480 : R) * h ^ 54 * a7 ^ 4 * a6 ^ 5 * b7
    + (55183279994280345600 : R) * h ^ 54 * a7 ^ 4 * a6 ^ 4 * a5 * b8
    + (7357770665904046080 : R) * h ^ 54 * a7 ^ 3 * a6 ^ 6 * b8

def asqBand810Src22b6
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    (-189042424335564800 : R) * h ^ 48 * a7 ^ 10 * a1
    + (-889611408637952000 : R) * h ^ 48 * a7 ^ 9 * a6 * a2
    + (-889611408637952000 : R) * h ^ 48 * a7 ^ 9 * a5 * a3
    + (-444805704318976000 : R) * h ^ 48 * a7 ^ 9 * a4 ^ 2
    + (500406417358848000 : R) * h ^ 48 * a7 ^ 8 * a6 ^ 2 * a3
    + (1000812834717696000 : R) * h ^ 48 * a7 ^ 8 * a6 * a5 * a4
    + (166802139119616000 : R) * h ^ 48 * a7 ^ 8 * a5 ^ 3
    + (13344171129569280000 : R) * h ^ 48 * a7 ^ 7 * a6 ^ 3 * a4
    + (20016256694353920000 : R) * h ^ 48 * a7 ^ 7 * a6 ^ 2 * a5 ^ 2
    + (44369369005817856000 : R) * h ^ 48 * a7 ^ 6 * a6 ^ 4 * a5
    + (13077287706977894400 : R) * h ^ 48 * a7 ^ 5 * a6 ^ 6
    + (-26688342259138560 : R) * h ^ 46 * a7 ^ 10 * b3
    + (-355844563455180800 : R) * h ^ 46 * a7 ^ 9 * a6 * b4
    + (-444805704318976000 : R) * h ^ 46 * a7 ^ 9 * a5 * b5
    + (-533766845182771200 : R) * h ^ 46 * a7 ^ 9 * a4 * b6
    + (-622727986046566400 : R) * h ^ 46 * a7 ^ 9 * a3 * b7
    + (-711689126910361600 : R) * h ^ 46 * a7 ^ 9 * a2 * b8
    + (-2001625669435392000 : R) * h ^ 46 * a7 ^ 8 * a6 ^ 2 * b5
    + (-4803901606644940800 : R) * h ^ 46 * a7 ^ 8 * a6 * a5 * b6
    + (-5604551874419097600 : R) * h ^ 46 * a7 ^ 8 * a6 * a4 * b7
    + (-6405202142193254400 : R) * h ^ 46 * a7 ^ 8 * a6 * a3 * b8
    + (-2802275937209548800 : R) * h ^ 46 * a7 ^ 8 * a5 ^ 2 * b7
    + (-6405202142193254400 : R) * h ^ 46 * a7 ^ 8 * a5 * a4 * b8
    + (-6405202142193254400 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 3 * b6
    + (-22418207497676390400 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 2 * a5 * b7
    + (-25620808568773017600 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 2 * a4 * b8
    + (-25620808568773017600 : R) * h ^ 46 * a7 ^ 7 * a6 * a5 ^ 2 * b8
    + (-13077287706977894400 : R) * h ^ 46 * a7 ^ 6 * a6 ^ 4 * b7

set_option maxHeartbeats 1600000000 in
theorem asqBand810Src22_split (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) :
    degreeZeroClearedSourceBlock22_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 0 =
      asqBand810Src22b5 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      asqBand810Src22b6 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 := by
  simp only [degreeZeroClearedSourceBlock22_810, asqBand810Src22b5, asqBand810Src22b6]
  try ring

def asqBand810Src23b6
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    (-59781886660470374400 : R) * h ^ 46 * a7 ^ 6 * a6 ^ 3 * a5 * b8
    + (-17934565998141112320 : R) * h ^ 46 * a7 ^ 5 * a6 ^ 5 * b8
    + (166043947578163200 : R) * h ^ 40 * a7 ^ 11 * a2
    + (913241711679897600 : R) * h ^ 40 * a7 ^ 10 * a6 * a3
    + (913241711679897600 : R) * h ^ 40 * a7 ^ 10 * a5 * a4
    + (-13698625675198464000 : R) * h ^ 40 * a7 ^ 8 * a6 ^ 3 * a5
    + (-10958900540158771200 : R) * h ^ 40 * a7 ^ 7 * a6 ^ 5

def asqBand810Src23b7
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    (29518924013895680 : R) * h ^ 38 * a7 ^ 11 * b4
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
    + (-31133240170905600 : R) * h ^ 30 * a7 ^ 12 * b5
    + (-448318658461040640 : R) * h ^ 30 * a7 ^ 11 * a6 * b6
    + (-523038434871214080 : R) * h ^ 30 * a7 ^ 11 * a5 * b7
    + (-597758211281387520 : R) * h ^ 30 * a7 ^ 11 * a4 * b8
    + (-2876711391791677440 : R) * h ^ 30 * a7 ^ 10 * a6 ^ 2 * b7
    + (-6575340324095262720 : R) * h ^ 30 * a7 ^ 10 * a6 * a5 * b8
    + (-10958900540158771200 : R) * h ^ 30 * a7 ^ 9 * a6 ^ 3 * b8
    + (133214344962048000 : R) * h ^ 24 * a7 ^ 13 * a4

set_option maxHeartbeats 1600000000 in
theorem asqBand810Src23_split (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) :
    degreeZeroClearedSourceBlock23_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 0 =
      asqBand810Src23b6 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      asqBand810Src23b7 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 := by
  simp only [degreeZeroClearedSourceBlock23_810, asqBand810Src23b6, asqBand810Src23b7]
  try ring

def asqBand810Src24b7
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    (952482566478643200 : R) * h ^ 24 * a7 ^ 12 * a6 * a5
    + (346357296901324800 : R) * h ^ 24 * a7 ^ 11 * a6 ^ 3
    + (31971442790891520 : R) * h ^ 22 * a7 ^ 13 * b6
    + (484900215661854720 : R) * h ^ 22 * a7 ^ 12 * a6 * b7
    + (554171675042119680 : R) * h ^ 22 * a7 ^ 12 * a5 * b8
    + (3325030050252718080 : R) * h ^ 22 * a7 ^ 11 * a6 ^ 2 * b8

def asqBand810Src24b8
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    (-121141794949862400 : R) * h ^ 16 * a7 ^ 14 * a5
    + (-484567179799449600 : R) * h ^ 16 * a7 ^ 13 * a6 ^ 2
    + (-32304478653296640 : R) * h ^ 14 * a7 ^ 14 * b7
    + (-516871658452746240 : R) * h ^ 14 * a7 ^ 13 * a6 * b8
    + (111046645370707200 : R) * h ^ 8 * a7 ^ 15 * a6
    + (32304478653296640 : R) * h ^ 6 * a7 ^ 15 * b8
    + (-8387881635621600 : R) * a7 ^ 17

set_option maxHeartbeats 1600000000 in
theorem asqBand810Src24_split (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) :
    degreeZeroClearedSourceBlock24_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 0 =
      asqBand810Src24b7 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      asqBand810Src24b8 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 := by
  simp only [degreeZeroClearedSourceBlock24_810, asqBand810Src24b7, asqBand810Src24b8]
  try ring

end AlignedSquareSourceEqExpansion810Band

end Max11DegreeRoutes

end
