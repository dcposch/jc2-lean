import Grok610DegreeZeroOrder71GrandchildScratch

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
set_option maxRecDepth 100000000
set_option maxHeartbeats 800000000

section DegreeZeroOrderThreeHead610

variable {R : Type*} [CommRing R]

set_option maxHeartbeats 4000000 in
theorem degreeZeroPostCollapseJetOrderOne610_q41Zero
    (w1 a42 p32 p21 p1 q53 q41 q3 u2 : R) (hq41 : q41 = 0) :
    degreeZeroPostCollapseJetOrderOne610 w1 a42 p32 p21 p1 q53 q41 q3
        u2 =
      (17062072720293888 : R) * a42 * p32 ^ 2 * q3 -
        29249267520503808 * p1 * p32 * q3 -
        14624633760251904 * p21 ^ 2 * q3 +
        28436787867156480 * p21 * p32 ^ 2 * q53 +
        34124145440587776 * p21 * p32 * q3 * w1 +
        6503598706655232 * p32 ^ 5 - 7188188044197888 * p32 ^ 4 * u2 -
        20537680126279680 * p32 ^ 3 * q53 * w1 -
        18483912113651712 * p32 ^ 2 * q3 * w1 ^ 2 := by
  simp only [degreeZeroPostCollapseJetOrderOne610, hq41]
  ring

end DegreeZeroOrderThreeHead610

end Max11DegreeRoutes
