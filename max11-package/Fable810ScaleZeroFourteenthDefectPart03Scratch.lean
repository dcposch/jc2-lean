import Fable810ScaleZeroTwelfthDefectScratch

/-! Part 3 of 40 of `Fable810ScaleZeroFourteenthDefectScratch`, split so that no single module elaborates them all
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

section Depression810FifteenthClearing

variable {F : Type*} [Field F] [CharZero F]


set_option maxHeartbeats 16000000 in
/-- First block of the weight-`105` cleared defect.  Splitting the generated
literal keeps typeclass synthesis linear in the expression size. -/
def localClearedFifteenthDefectBlock0_810
    {R : Type*} [CommRing R]
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (63159562772460 : R) * a7 ^ 15
    + (244982546511360 : R) * h ^ 6 * a7 ^ 13 * b8
    + (60903864102015 : R) * h ^ 7 * a7 ^ 14 * lambda
    + (689013412063200 : R) * h ^ 8 * a7 ^ 13 * a6
    - (244982546511360 : R) * h ^ 14 * a7 ^ 12 * b7
    - (3359760637870080 : R) * h ^ 14 * a7 ^ 11 * a6 * b8
    - (895717435682160 : R) * h ^ 15 * a7 ^ 12 * a6 * lambda
    - (743697016195200 : R) * h ^ 16 * a7 ^ 12 * a5
    - (2099850398668800 : R) * h ^ 16 * a7 ^ 11 * a6 ^ 2
    + (242874262978560 : R) * h ^ 22 * a7 ^ 11 * b6
    + (3116886374891520 : R) * h ^ 22 * a7 ^ 10 * a6 * b7
    + (3562155857018880 : R) * h ^ 22 * a7 ^ 10 * a5 * b8
    + (17810779285094400 : R) * h ^ 22 * a7 ^ 9 * a6 ^ 2 * b8
    + (944932679400960 : R) * h ^ 23 * a7 ^ 11 * a5 * lambda
    + (5197129736705280 : R) * h ^ 23 * a7 ^ 10 * a6 ^ 2 * lambda
    + (809580876595200 : R) * h ^ 24 * a7 ^ 11 * a4
    + (3896107968614400 : R) * h ^ 24 * a7 ^ 10 * a6 * a5
    - (1855289508864000 : R) * h ^ 24 * a7 ^ 9 * a6 ^ 3
    - (237477057134592 : R) * h ^ 30 * a7 ^ 10 * b5
    - (2849724685615104 : R) * h ^ 30 * a7 ^ 9 * a6 * b6
    - (3324678799884288 : R) * h ^ 30 * a7 ^ 9 * a5 * b7
    - (3799632914153472 : R) * h ^ 30 * a7 ^ 9 * a4 * b8
    - (14961054599479296 : R) * h ^ 30 * a7 ^ 8 * a6 ^ 2 * b7
    - (34196696227381248 : R) * h ^ 30 * a7 ^ 8 * a6 * a5 * b8
    - (45595594969841664 : R) * h ^ 30 * a7 ^ 7 * a6 ^ 3 * b8
    - (1001856334786560 : R) * h ^ 31 * a7 ^ 10 * a4 * lambda
    - (10018563347865600 : R) * h ^ 31 * a7 ^ 9 * a6 * a5 * lambda
    - (15027845021798400 : R) * h ^ 31 * a7 ^ 8 * a6 ^ 3 * lambda
    - (890538964254720 : R) * h ^ 32 * a7 ^ 10 * a3
    - (3562155857018880 : R) * h ^ 32 * a7 ^ 9 * a6 * a4
    - (1781077928509440 : R) * h ^ 32 * a7 ^ 9 * a5 ^ 2
    + (8014850678292480 : R) * h ^ 32 * a7 ^ 8 * a6 ^ 2 * a5
    + (21372935142113280 : R) * h ^ 32 * a7 ^ 7 * a6 ^ 4
    + (226843756068864 : R) * h ^ 38 * a7 ^ 9 * b4
    + (2551992255774720 : R) * h ^ 38 * a7 ^ 8 * a6 * b5
    + (3062390706929664 : R) * h ^ 38 * a7 ^ 8 * a5 * b6
    + (3572789158084608 : R) * h ^ 38 * a7 ^ 8 * a4 * b7
    + (4083187609239552 : R) * h ^ 38 * a7 ^ 8 * a3 * b8
    + (12249562827718656 : R) * h ^ 38 * a7 ^ 7 * a6 ^ 2 * b6
    + (28582313264676864 : R) * h ^ 38 * a7 ^ 7 * a6 * a5 * b7


end Depression810FifteenthClearing
end Max11DegreeRoutes
end
