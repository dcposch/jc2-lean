import Fable810ScaleZeroTwelfthDefectScratch

/-! Part 3 of 37 of `Fable810ScaleZeroThirteenthDefectScratch`, split so that no single module elaborates them all
at once.  Statements are unchanged. -/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

set_option maxRecDepth 1000000

section Depression810FourteenthClearing

variable {F : Type*} [Field F] [CharZero F]


set_option maxHeartbeats 16000000 in
/-- First block of the weight-`98` cleared defect.  Splitting the generated
literal keeps typeclass synthesis linear in the expression size. -/
def localClearedFourteenthDefectBlock0_810
    {R : Type*} [CommRing R]
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (31646351360 : R) * a7 ^ 14
    - (123283177472 : R) * h ^ 6 * a7 ^ 12 * b8
    - (30672617472 : R) * h ^ 7 * a7 ^ 13 * lambda
    - (308207943680 : R) * h ^ 8 * a7 ^ 12 * a6
    + (123283177472 : R) * h ^ 14 * a7 ^ 11 * b7
    + (1549845659648 : R) * h ^ 14 * a7 ^ 10 * a6 * b8
    + (416080723968 : R) * h ^ 15 * a7 ^ 11 * a6 * lambda
    + (330222796800 : R) * h ^ 16 * a7 ^ 11 * a5
    + (726490152960 : R) * h ^ 16 * a7 ^ 10 * a6 ^ 2
    - (122356236288 : R) * h ^ 22 * a7 ^ 10 * b6
    - (1427489423360 : R) * h ^ 22 * a7 ^ 9 * a6 * b7
    - (1631416483840 : R) * h ^ 22 * a7 ^ 9 * a5 * b8
    - (7341374177280 : R) * h ^ 22 * a7 ^ 8 * a6 ^ 2 * b8
    - (435894091776 : R) * h ^ 23 * a7 ^ 10 * a5 * lambda
    - (2179470458880 : R) * h ^ 23 * a7 ^ 9 * a6 ^ 2 * lambda
    - (356872355840 : R) * h ^ 24 * a7 ^ 10 * a4
    - (1274544128000 : R) * h ^ 24 * a7 ^ 9 * a6 * a5
    + (1529452953600 : R) * h ^ 24 * a7 ^ 8 * a6 ^ 3
    + (119957094400 : R) * h ^ 30 * a7 ^ 9 * b5
    + (1295536619520 : R) * h ^ 30 * a7 ^ 8 * a6 * b6
    + (1511459389440 : R) * h ^ 30 * a7 ^ 8 * a5 * b7
    + (1727382159360 : R) * h ^ 30 * a7 ^ 8 * a4 * b8
    + (6045837557760 : R) * h ^ 30 * a7 ^ 7 * a6 ^ 2 * b7
    + (13819057274880 : R) * h ^ 30 * a7 ^ 7 * a6 * a5 * b8
    + (16122233487360 : R) * h ^ 30 * a7 ^ 6 * a6 ^ 3 * b8
    + (458835886080 : R) * h ^ 31 * a7 ^ 9 * a4 * lambda
    + (4129522974720 : R) * h ^ 31 * a7 ^ 8 * a6 * a5 * lambda
    + (5506030632960 : R) * h ^ 31 * a7 ^ 7 * a6 ^ 3 * lambda
    + (389860556800 : R) * h ^ 32 * a7 ^ 9 * a3
    + (1079613849600 : R) * h ^ 32 * a7 ^ 8 * a6 * a4
    + (539806924800 : R) * h ^ 32 * a7 ^ 8 * a5 ^ 2
    - (5398069248000 : R) * h ^ 32 * a7 ^ 7 * a6 ^ 2 * a5
    - (8816846438400 : R) * h ^ 32 * a7 ^ 6 * a6 ^ 4
    - (115158810624 : R) * h ^ 38 * a7 ^ 8 * b4
    - (1151588106240 : R) * h ^ 38 * a7 ^ 7 * a6 * b5
    - (1381905727488 : R) * h ^ 38 * a7 ^ 7 * a5 * b6
    - (1612223348736 : R) * h ^ 38 * a7 ^ 7 * a4 * b7
    - (1842540969984 : R) * h ^ 38 * a7 ^ 7 * a3 * b8
    - (4836670046208 : R) * h ^ 38 * a7 ^ 6 * a6 ^ 2 * b6
    - (11285563441152 : R) * h ^ 38 * a7 ^ 6 * a6 * a5 * b7


end Depression810FourteenthClearing
end Max11DegreeRoutes
end
