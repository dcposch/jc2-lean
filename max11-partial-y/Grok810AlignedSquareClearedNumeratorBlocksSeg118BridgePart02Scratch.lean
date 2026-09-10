import Grok810AlignedSquareClearedNumeratorBlocksSeg118BridgePart01Scratch

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

def asqBand810Src5b0
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) : R :=
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

set_option maxHeartbeats 1600000000 in
theorem asqBand810Src5_split (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) :
    degreeZeroClearedSourceBlock5_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 0 =
      asqBand810Src5b0 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 := by
  simp only [degreeZeroClearedSourceBlock5_810, asqBand810Src5b0]
  try ring

def asqBand810Src6b0
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    (-4823355200913801216 : R) * h ^ 94 * a7 ^ 2 * a4 * a0 * b7
    + (-1722626857469214720 : R) * h ^ 94 * a7 ^ 2 * a3 ^ 2 * b5
    + (-4134304457926115328 : R) * h ^ 94 * a7 ^ 2 * a3 * a2 * b6
    + (-4823355200913801216 : R) * h ^ 94 * a7 ^ 2 * a3 * a1 * b7
    + (-5512405943901487104 : R) * h ^ 94 * a7 ^ 2 * a3 * a0 * b8
    + (-2411677600456900608 : R) * h ^ 94 * a7 ^ 2 * a2 ^ 2 * b7
    + (-5512405943901487104 : R) * h ^ 94 * a7 ^ 2 * a2 * a1 * b8
    + (-689050742987685888 : R) * h ^ 94 * a7 * a6 ^ 2 * a5 * b1
    + (-1378101485975371776 : R) * h ^ 94 * a7 * a6 ^ 2 * a4 * b2
    + (-2067152228963057664 : R) * h ^ 94 * a7 * a6 ^ 2 * a3 * b3
    + (-2756202971950743552 : R) * h ^ 94 * a7 * a6 ^ 2 * a2 * b4
    + (-3445253714938429440 : R) * h ^ 94 * a7 * a6 ^ 2 * a1 * b5
    + (-4134304457926115328 : R) * h ^ 94 * a7 * a6 ^ 2 * a0 * b6
    + (-1378101485975371776 : R) * h ^ 94 * a7 * a6 * a5 ^ 2 * b2
    + (-4134304457926115328 : R) * h ^ 94 * a7 * a6 * a5 * a4 * b3
    + (-5512405943901487104 : R) * h ^ 94 * a7 * a6 * a5 * a3 * b4
    + (-6890507429876858880 : R) * h ^ 94 * a7 * a6 * a5 * a2 * b5
    + (-8268608915852230656 : R) * h ^ 94 * a7 * a6 * a5 * a1 * b6
    + (-9646710401827602432 : R) * h ^ 94 * a7 * a6 * a5 * a0 * b7
    + (-2756202971950743552 : R) * h ^ 94 * a7 * a6 * a4 ^ 2 * b4
    + (-6890507429876858880 : R) * h ^ 94 * a7 * a6 * a4 * a3 * b5
    + (-8268608915852230656 : R) * h ^ 94 * a7 * a6 * a4 * a2 * b6
    + (-9646710401827602432 : R) * h ^ 94 * a7 * a6 * a4 * a1 * b7
    + (-11024811887802974208 : R) * h ^ 94 * a7 * a6 * a4 * a0 * b8
    + (-4134304457926115328 : R) * h ^ 94 * a7 * a6 * a3 ^ 2 * b6
    + (-9646710401827602432 : R) * h ^ 94 * a7 * a6 * a3 * a2 * b7
    + (-11024811887802974208 : R) * h ^ 94 * a7 * a6 * a3 * a1 * b8
    + (-5512405943901487104 : R) * h ^ 94 * a7 * a6 * a2 ^ 2 * b8
    + (-689050742987685888 : R) * h ^ 94 * a7 * a5 ^ 3 * b3
    + (-2756202971950743552 : R) * h ^ 94 * a7 * a5 ^ 2 * a4 * b4
    + (-3445253714938429440 : R) * h ^ 94 * a7 * a5 ^ 2 * a3 * b5
    + (-4134304457926115328 : R) * h ^ 94 * a7 * a5 ^ 2 * a2 * b6
    + (-4823355200913801216 : R) * h ^ 94 * a7 * a5 ^ 2 * a1 * b7
    + (-5512405943901487104 : R) * h ^ 94 * a7 * a5 ^ 2 * a0 * b8
    + (-3445253714938429440 : R) * h ^ 94 * a7 * a5 * a4 ^ 2 * b5
    + (-8268608915852230656 : R) * h ^ 94 * a7 * a5 * a4 * a3 * b6
    + (-9646710401827602432 : R) * h ^ 94 * a7 * a5 * a4 * a2 * b7
    + (-11024811887802974208 : R) * h ^ 94 * a7 * a5 * a4 * a1 * b8
    + (-4823355200913801216 : R) * h ^ 94 * a7 * a5 * a3 ^ 2 * b7
    + (-11024811887802974208 : R) * h ^ 94 * a7 * a5 * a3 * a2 * b8

set_option maxHeartbeats 1600000000 in
theorem asqBand810Src6_split (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) :
    degreeZeroClearedSourceBlock6_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 0 =
      asqBand810Src6b0 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 := by
  simp only [degreeZeroClearedSourceBlock6_810, asqBand810Src6b0]
  try ring

def asqBand810Src7b0
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    (-1378101485975371776 : R) * h ^ 94 * a7 * a4 ^ 3 * b6
    + (-4823355200913801216 : R) * h ^ 94 * a7 * a4 ^ 2 * a3 * b7
    + (-5512405943901487104 : R) * h ^ 94 * a7 * a4 ^ 2 * a2 * b8
    + (-5512405943901487104 : R) * h ^ 94 * a7 * a4 * a3 ^ 2 * b8
    + (-57420895248973824 : R) * h ^ 94 * a6 ^ 4 * b1
    + (-459367161991790592 : R) * h ^ 94 * a6 ^ 3 * a5 * b2
    + (-689050742987685888 : R) * h ^ 94 * a6 ^ 3 * a4 * b3
    + (-918734323983581184 : R) * h ^ 94 * a6 ^ 3 * a3 * b4
    + (-1148417904979476480 : R) * h ^ 94 * a6 ^ 3 * a2 * b5
    + (-1378101485975371776 : R) * h ^ 94 * a6 ^ 3 * a1 * b6
    + (-1607785066971267072 : R) * h ^ 94 * a6 ^ 3 * a0 * b7
    + (-1033576114481528832 : R) * h ^ 94 * a6 ^ 2 * a5 ^ 2 * b3
    + (-2756202971950743552 : R) * h ^ 94 * a6 ^ 2 * a5 * a4 * b4
    + (-3445253714938429440 : R) * h ^ 94 * a6 ^ 2 * a5 * a3 * b5
    + (-4134304457926115328 : R) * h ^ 94 * a6 ^ 2 * a5 * a2 * b6
    + (-4823355200913801216 : R) * h ^ 94 * a6 ^ 2 * a5 * a1 * b7
    + (-5512405943901487104 : R) * h ^ 94 * a6 ^ 2 * a5 * a0 * b8
    + (-1722626857469214720 : R) * h ^ 94 * a6 ^ 2 * a4 ^ 2 * b5
    + (-4134304457926115328 : R) * h ^ 94 * a6 ^ 2 * a4 * a3 * b6
    + (-4823355200913801216 : R) * h ^ 94 * a6 ^ 2 * a4 * a2 * b7
    + (-5512405943901487104 : R) * h ^ 94 * a6 ^ 2 * a4 * a1 * b8
    + (-2411677600456900608 : R) * h ^ 94 * a6 ^ 2 * a3 ^ 2 * b7
    + (-5512405943901487104 : R) * h ^ 94 * a6 ^ 2 * a3 * a2 * b8
    + (-918734323983581184 : R) * h ^ 94 * a6 * a5 ^ 3 * b4
    + (-3445253714938429440 : R) * h ^ 94 * a6 * a5 ^ 2 * a4 * b5
    + (-4134304457926115328 : R) * h ^ 94 * a6 * a5 ^ 2 * a3 * b6
    + (-4823355200913801216 : R) * h ^ 94 * a6 * a5 ^ 2 * a2 * b7
    + (-5512405943901487104 : R) * h ^ 94 * a6 * a5 ^ 2 * a1 * b8
    + (-4134304457926115328 : R) * h ^ 94 * a6 * a5 * a4 ^ 2 * b6
    + (-9646710401827602432 : R) * h ^ 94 * a6 * a5 * a4 * a3 * b7
    + (-11024811887802974208 : R) * h ^ 94 * a6 * a5 * a4 * a2 * b8
    + (-5512405943901487104 : R) * h ^ 94 * a6 * a5 * a3 ^ 2 * b8
    + (-1607785066971267072 : R) * h ^ 94 * a6 * a4 ^ 3 * b7
    + (-5512405943901487104 : R) * h ^ 94 * a6 * a4 ^ 2 * a3 * b8
    + (-287104476244869120 : R) * h ^ 94 * a5 ^ 4 * b5
    + (-1378101485975371776 : R) * h ^ 94 * a5 ^ 3 * a4 * b6
    + (-1607785066971267072 : R) * h ^ 94 * a5 ^ 3 * a3 * b7
    + (-1837468647967162368 : R) * h ^ 94 * a5 ^ 3 * a2 * b8
    + (-2411677600456900608 : R) * h ^ 94 * a5 ^ 2 * a4 ^ 2 * b7
    + (-5512405943901487104 : R) * h ^ 94 * a5 ^ 2 * a4 * a3 * b8

set_option maxHeartbeats 1600000000 in
theorem asqBand810Src7_split (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) :
    degreeZeroClearedSourceBlock7_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 0 =
      asqBand810Src7b0 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 := by
  simp only [degreeZeroClearedSourceBlock7_810, asqBand810Src7b0]
  try ring

def asqBand810Src8b0
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    (-1837468647967162368 : R) * h ^ 94 * a5 * a4 ^ 3 * b8

def asqBand810Src8b1
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    (672901116198912000 : R) * h ^ 88 * a7 ^ 4 * a3 * a0
    + (672901116198912000 : R) * h ^ 88 * a7 ^ 4 * a2 * a1
    + (-5383208929591296000 : R) * h ^ 88 * a7 ^ 3 * a6 * a4 * a0
    + (-5383208929591296000 : R) * h ^ 88 * a7 ^ 3 * a6 * a3 * a1
    + (-2691604464795648000 : R) * h ^ 88 * a7 ^ 3 * a6 * a2 ^ 2
    + (-2691604464795648000 : R) * h ^ 88 * a7 ^ 3 * a5 ^ 2 * a0
    + (-5383208929591296000 : R) * h ^ 88 * a7 ^ 3 * a5 * a4 * a1
    + (-5383208929591296000 : R) * h ^ 88 * a7 ^ 3 * a5 * a3 * a2
    + (-2691604464795648000 : R) * h ^ 88 * a7 ^ 3 * a4 ^ 2 * a2
    + (-2691604464795648000 : R) * h ^ 88 * a7 ^ 3 * a4 * a3 ^ 2
    + (-20187033485967360000 : R) * h ^ 88 * a7 ^ 2 * a6 ^ 2 * a5 * a0
    + (-20187033485967360000 : R) * h ^ 88 * a7 ^ 2 * a6 ^ 2 * a4 * a1
    + (-20187033485967360000 : R) * h ^ 88 * a7 ^ 2 * a6 ^ 2 * a3 * a2
    + (-20187033485967360000 : R) * h ^ 88 * a7 ^ 2 * a6 * a5 ^ 2 * a1
    + (-40374066971934720000 : R) * h ^ 88 * a7 ^ 2 * a6 * a5 * a4 * a2
    + (-20187033485967360000 : R) * h ^ 88 * a7 ^ 2 * a6 * a5 * a3 ^ 2
    + (-20187033485967360000 : R) * h ^ 88 * a7 ^ 2 * a6 * a4 ^ 2 * a3
    + (-6729011161989120000 : R) * h ^ 88 * a7 ^ 2 * a5 ^ 3 * a2
    + (-20187033485967360000 : R) * h ^ 88 * a7 ^ 2 * a5 ^ 2 * a4 * a3
    + (-6729011161989120000 : R) * h ^ 88 * a7 ^ 2 * a5 * a4 ^ 3
    + (-5383208929591296000 : R) * h ^ 88 * a7 * a6 ^ 4 * a0
    + (-21532835718365184000 : R) * h ^ 88 * a7 * a6 ^ 3 * a5 * a1
    + (-21532835718365184000 : R) * h ^ 88 * a7 * a6 ^ 3 * a4 * a2
    + (-10766417859182592000 : R) * h ^ 88 * a7 * a6 ^ 3 * a3 ^ 2
    + (-32299253577547776000 : R) * h ^ 88 * a7 * a6 ^ 2 * a5 ^ 2 * a2
    + (-64598507155095552000 : R) * h ^ 88 * a7 * a6 ^ 2 * a5 * a4 * a3
    + (-10766417859182592000 : R) * h ^ 88 * a7 * a6 ^ 2 * a4 ^ 3
    + (-21532835718365184000 : R) * h ^ 88 * a7 * a6 * a5 ^ 3 * a3
    + (-32299253577547776000 : R) * h ^ 88 * a7 * a6 * a5 ^ 2 * a4 ^ 2
    + (-5383208929591296000 : R) * h ^ 88 * a7 * a5 ^ 4 * a4
    + (-1480382455637606400 : R) * h ^ 88 * a6 ^ 5 * a1
    + (-7401912278188032000 : R) * h ^ 88 * a6 ^ 4 * a5 * a2
    + (-7401912278188032000 : R) * h ^ 88 * a6 ^ 4 * a4 * a3
    + (-14803824556376064000 : R) * h ^ 88 * a6 ^ 3 * a5 ^ 2 * a3
    + (-14803824556376064000 : R) * h ^ 88 * a6 ^ 3 * a5 * a4 ^ 2
    + (-14803824556376064000 : R) * h ^ 88 * a6 ^ 2 * a5 ^ 3 * a4
    + (-1480382455637606400 : R) * h ^ 88 * a6 * a5 ^ 5

set_option maxHeartbeats 1600000000 in
theorem asqBand810Src8_split (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) :
    degreeZeroClearedSourceBlock8_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 0 =
      asqBand810Src8b0 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      asqBand810Src8b1 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 := by
  simp only [degreeZeroClearedSourceBlock8_810, asqBand810Src8b0, asqBand810Src8b1]
  try ring

def asqBand810Src9b1
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) : R :=
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

set_option maxHeartbeats 1600000000 in
theorem asqBand810Src9_split (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) :
    degreeZeroClearedSourceBlock9_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 0 =
      asqBand810Src9b1 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 := by
  simp only [degreeZeroClearedSourceBlock9_810, asqBand810Src9b1]
  try ring

end AlignedSquareSourceEqExpansion810Band

end Max11DegreeRoutes

end
