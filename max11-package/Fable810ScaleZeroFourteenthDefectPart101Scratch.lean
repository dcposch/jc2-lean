import Fable810ScaleTwoFifteenthFaceScratch
import Fable810ScaleZeroTwelfthDefectScratch

/-! Part 1 of 40 of `Fable810ScaleZeroFourteenthDefectScratch`, split so that no single module elaborates them all
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


/-! ## Literal next Keller coefficient -/

/-- The fifteenth row below the leading weighted-Wronskian row for outer
degrees `(8,10)`.  Unused Jacobian coefficients of the thirteenth-defect
packet start at degree `2`. -/
theorem fableScaleZero_fifteenthCoefficientJacobianRow_raw_810 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 2).derivative * q.coeff 1 +
        (p.coeff 1).derivative * (q.coeff 2 * Polynomial.C (2 : K)) +
        (p.coeff 0).derivative * (q.coeff 3 * Polynomial.C (3 : K)) -
      ((p.coeff 3 * Polynomial.C (3 : K)) * (q.coeff 0).derivative +
        (p.coeff 2 * Polynomial.C (2 : K)) * (q.coeff 1).derivative +
        p.coeff 1 * (q.coeff 2).derivative) =
      0 := by
  exact fifteenthCoefficientJacobianRow_810 hp hq hjac


end Max11DegreeRoutes
end
/-! Part 2 of 40 of `Fable810ScaleZeroFourteenthDefectScratch`, split so that no single module elaborates them all
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
/-- First residual of the degree-`2` row.  Its exactness certificate
uses the degree-`4`, degree-`5`, and degree-`6` rows again, with the
multipliers `-(3/64) A`, `-(3/64) B`, and `(33/1024) A² - (3/64) C`. -/
def omicronResidual810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : F) : F :=
  (1 / 8 : F) * thetaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 W0 * E0
    - (3 / 64 : F) * thetaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 W0 * A * C0
    - (3 / 128 : F) * thetaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 W0 * B ^ 2
    + (11 / 1024 : F) * thetaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 W0 * A ^ 3
    + (1 / 4 : F) * etaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 V0 * F0
    - (3 / 32 : F) * etaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 V0 * A * D0
    - (3 / 32 : F) * etaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 V0 * B * C0
    + (33 / 512 : F) * etaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 V0 * A ^ 2 * B
    + (3 / 8 : F) * zetaResidual810 L A B C0 D0 E0 F0 P Q R S0 U0 * G0
    - (3 / 32 : F) * zetaResidual810 L A B C0 D0 E0 F0 P Q R S0 U0 * A * E0
    - (9 / 64 : F) * zetaResidual810 L A B C0 D0 E0 F0 P Q R S0 U0 * B * D0
    - (9 / 128 : F) * zetaResidual810 L A B C0 D0 E0 F0 P Q R S0 U0 * C0 ^ 2
    + (81 / 1024 : F) * zetaResidual810 L A B C0 D0 E0 F0 P Q R S0 U0 * A ^ 2 * C0
    + (45 / 512 : F) * zetaResidual810 L A B C0 D0 E0 F0 P Q R S0 U0 * A * B ^ 2
    - (495 / 32768 : F) * zetaResidual810 L A B C0 D0 E0 F0 P Q R S0 U0 * A ^ 4
    - (1 / 16 : F) * epsilonResidual810 L A B C0 D0 E0 P Q R T0 * A * F0
    - (1 / 8 : F) * epsilonResidual810 L A B C0 D0 E0 P Q R T0 * B * E0
    - (3 / 16 : F) * epsilonResidual810 L A B C0 D0 E0 P Q R T0 * C0 * D0
    + (21 / 256 : F) * epsilonResidual810 L A B C0 D0 E0 P Q R T0 * A ^ 2 * D0
    + (3 / 16 : F) * epsilonResidual810 L A B C0 D0 E0 P Q R T0 * A * B * C0
    + (1 / 32 : F) * epsilonResidual810 L A B C0 D0 E0 P Q R T0 * B ^ 3
    - (33 / 512 : F) * epsilonResidual810 L A B C0 D0 E0 P Q R T0 * A ^ 3 * B
    - (5 / 64 : F) * deltaResidual810 L A B C0 D0 P Q S0 * B * F0
    - (5 / 32 : F) * deltaResidual810 L A B C0 D0 P Q S0 * C0 * E0
    + (15 / 256 : F) * deltaResidual810 L A B C0 D0 P Q S0 * A ^ 2 * E0
    - (15 / 128 : F) * deltaResidual810 L A B C0 D0 P Q S0 * D0 ^ 2
    + (45 / 256 : F) * deltaResidual810 L A B C0 D0 P Q S0 * A * B * D0
    + (45 / 512 : F) * deltaResidual810 L A B C0 D0 P Q S0 * A * C0 ^ 2
    + (45 / 512 : F) * deltaResidual810 L A B C0 D0 P Q S0 * B ^ 2 * C0
    - (225 / 4096 : F) * deltaResidual810 L A B C0 D0 P Q S0 * A ^ 3 * C0
    - (45 / 512 : F) * deltaResidual810 L A B C0 D0 P Q S0 * A ^ 2 * B ^ 2
    + (1089 / 131072 : F) * deltaResidual810 L A B C0 D0 P Q S0 * A ^ 5
    - (3 / 32 : F) * gammaResidual810 L A B C0 P R * C0 * F0
    + (15 / 512 : F) * gammaResidual810 L A B C0 P R * A ^ 2 * F0
    - (3 / 16 : F) * gammaResidual810 L A B C0 P R * D0 * E0
    + (15 / 128 : F) * gammaResidual810 L A B C0 P R * A * B * E0
    + (9 / 64 : F) * gammaResidual810 L A B C0 P R * A * C0 * D0
    + (9 / 128 : F) * gammaResidual810 L A B C0 P R * B ^ 2 * D0
    - (81 / 2048 : F) * gammaResidual810 L A B C0 P R * A ^ 3 * D0
    + (9 / 128 : F) * gammaResidual810 L A B C0 P R * B * C0 ^ 2
    - (261 / 2048 : F) * gammaResidual810 L A B C0 P R * A ^ 2 * B * C0
    - (45 / 1024 : F) * gammaResidual810 L A B C0 P R * A * B ^ 3
    + (495 / 16384 : F) * gammaResidual810 L A B C0 P R * A ^ 4 * B
    - (7 / 64 : F) * betaResidual810 L A B Q * D0 * F0
    + (7 / 128 : F) * betaResidual810 L A B Q * A * B * F0
    - (7 / 128 : F) * betaResidual810 L A B Q * E0 ^ 2
    + (35 / 512 : F) * betaResidual810 L A B Q * A * C0 * E0
    + (35 / 1024 : F) * betaResidual810 L A B Q * B ^ 2 * E0
    - (147 / 8192 : F) * betaResidual810 L A B Q * A ^ 3 * E0
    + (21 / 512 : F) * betaResidual810 L A B Q * A * D0 ^ 2
    + (21 / 256 : F) * betaResidual810 L A B Q * B * C0 * D0
    - (273 / 4096 : F) * betaResidual810 L A B Q * A ^ 2 * B * D0
    + (7 / 512 : F) * betaResidual810 L A B Q * C0 ^ 3
    - (273 / 8192 : F) * betaResidual810 L A B Q * A ^ 2 * C0 ^ 2
    - (567 / 8192 : F) * betaResidual810 L A B Q * A * B ^ 2 * C0
    + (1953 / 131072 : F) * betaResidual810 L A B Q * A ^ 4 * C0
    - (189 / 32768 : F) * betaResidual810 L A B Q * B ^ 4
    + (4095 / 131072 : F) * betaResidual810 L A B Q * A ^ 3 * B ^ 2
    - (3927 / 2097152 : F) * betaResidual810 L A B Q * A ^ 6
    - (34155 / 33554432 : F) * L * A ^ 7
    + (19845 / 2097152 : F) * L * A ^ 5 * C0
    + (103005 / 4194304 : F) * L * A ^ 4 * B ^ 2
    - (3087 / 262144 : F) * L * A ^ 4 * E0
    - (3591 / 65536 : F) * L * A ^ 3 * B * D0
    - (3591 / 131072 : F) * L * A ^ 3 * C0 ^ 2
    + (99 / 8192 : F) * L * A ^ 3 * G0
    - (11151 / 131072 : F) * L * A ^ 2 * B ^ 2 * C0
    + (207 / 4096 : F) * L * A ^ 2 * B * F0
    + (477 / 8192 : F) * L * A ^ 2 * C0 * E0
    + (135 / 4096 : F) * L * A ^ 2 * D0 ^ 2
    - (945 / 65536 : F) * L * A * B ^ 4
    + (63 / 1024 : F) * L * A * B ^ 2 * E0
    + (567 / 4096 : F) * L * A * B * C0 * D0
    + (189 / 8192 : F) * L * A * C0 ^ 3
    - (27 / 512 : F) * L * A * C0 * G0
    - (9 / 128 : F) * L * A * D0 * F0
    - (9 / 256 : F) * L * A * E0 ^ 2
    + (189 / 8192 : F) * L * B ^ 3 * D0
    + (567 / 16384 : F) * L * B ^ 2 * C0 ^ 2
    - (27 / 1024 : F) * L * B ^ 2 * G0
    - (9 / 128 : F) * L * B * C0 * F0
    - (45 / 512 : F) * L * B * D0 * E0
    - (45 / 1024 : F) * L * C0 ^ 2 * E0
    - (27 / 512 : F) * L * C0 * D0 ^ 2
    + (9 / 64 : F) * L * E0 * G0
    + (9 / 128 : F) * L * F0 ^ 2
    - (12705 / 1048576 : F) * A ^ 6 * B
    + (525 / 32768 : F) * A ^ 5 * D0
    + (1365 / 16384 : F) * A ^ 4 * B * C0
    - (305 / 16384 : F) * A ^ 4 * F0
    + (3745 / 65536 : F) * A ^ 3 * B ^ 3
    - (725 / 8192 : F) * A ^ 3 * B * E0
    - (795 / 8192 : F) * A ^ 3 * C0 * D0
    - (2475 / 16384 : F) * A ^ 2 * B ^ 2 * D0
    - (2475 / 16384 : F) * A ^ 2 * B * C0 ^ 2
    + (165 / 2048 : F) * A ^ 2 * B * G0
    + (195 / 2048 : F) * A ^ 2 * C0 * F0
    + (225 / 2048 : F) * A ^ 2 * D0 * E0
    - (105 / 1024 : F) * A * B ^ 3 * C0
    + (105 / 1024 : F) * A * B ^ 2 * F0
    + (15 / 64 : F) * A * B * C0 * E0
    + (135 / 1024 : F) * A * B * D0 ^ 2
    + (135 / 1024 : F) * A * C0 ^ 2 * D0
    - (15 / 128 : F) * A * D0 * G0
    - (15 / 128 : F) * A * E0 * F0
    - (21 / 4096 : F) * B ^ 5
    + (5 / 128 : F) * B ^ 3 * E0
    + (135 / 1024 : F) * B ^ 2 * C0 * D0
    + (45 / 1024 : F) * B * C0 ^ 3
    - (15 / 128 : F) * B * C0 * G0
    - (5 / 32 : F) * B * D0 * F0
    - (5 / 64 : F) * B * E0 ^ 2
    - (5 / 64 : F) * C0 ^ 2 * F0
    - (25 / 128 : F) * C0 * D0 * E0
    - (5 / 128 : F) * D0 ^ 3
    + (5 / 16 : F) * F0 * G0


end Depression810FifteenthClearing
end Max11DegreeRoutes
end
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
/-! Part 4 of 40 of `Fable810ScaleZeroFourteenthDefectScratch`, split so that no single module elaborates them all
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


def localClearedFifteenthDefectBlock1_810
    {R : Type*} [CommRing R]
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (32665500873916416 : R) * h ^ 38 * a7 ^ 7 * a6 * a4 * b8
    + (16332750436958208 : R) * h ^ 38 * a7 ^ 7 * a5 ^ 2 * b8
    + (33346032142123008 : R) * h ^ 38 * a7 ^ 6 * a6 ^ 3 * b7
    + (114329253058707456 : R) * h ^ 38 * a7 ^ 6 * a6 ^ 2 * a5 * b8
    + (57164626529353728 : R) * h ^ 38 * a7 ^ 5 * a6 ^ 4 * b8
    + (1068646757105664 : R) * h ^ 39 * a7 ^ 9 * a3 * lambda
    + (9617820813950976 : R) * h ^ 39 * a7 ^ 8 * a6 * a4 * lambda
    + (4808910406975488 : R) * h ^ 39 * a7 ^ 8 * a5 ^ 2 * lambda
    + (38471283255803904 : R) * h ^ 39 * a7 ^ 7 * a6 ^ 2 * a5 * lambda
    + (22441581899218944 : R) * h ^ 39 * a7 ^ 6 * a6 ^ 4 * lambda
    + (992441432801280 : R) * h ^ 40 * a7 ^ 9 * a2
    + (3189990319718400 : R) * h ^ 40 * a7 ^ 8 * a6 * a3
    + (3189990319718400 : R) * h ^ 40 * a7 ^ 8 * a5 * a4
    - (10207969023098880 : R) * h ^ 40 * a7 ^ 7 * a6 ^ 2 * a4
    - (10207969023098880 : R) * h ^ 40 * a7 ^ 7 * a6 * a5 ^ 2
    - (77410431758499840 : R) * h ^ 40 * a7 ^ 6 * a6 ^ 3 * a5
    - (39300680738930688 : R) * h ^ 40 * a7 ^ 5 * a6 ^ 5
    - (207619708944384 : R) * h ^ 46 * a7 ^ 8 * b3
    - (2214610228740096 : R) * h ^ 46 * a7 ^ 7 * a6 * b4
    - (2768262785925120 : R) * h ^ 46 * a7 ^ 7 * a5 * b5
    - (3321915343110144 : R) * h ^ 46 * a7 ^ 7 * a4 * b6
    - (3875567900295168 : R) * h ^ 46 * a7 ^ 7 * a3 * b7
    - (4429220457480192 : R) * h ^ 46 * a7 ^ 7 * a2 * b8
    - (9688919750737920 : R) * h ^ 46 * a7 ^ 6 * a6 ^ 2 * b5
    - (23253407401771008 : R) * h ^ 46 * a7 ^ 6 * a6 * a5 * b6
    - (27128975302066176 : R) * h ^ 46 * a7 ^ 6 * a6 * a4 * b7
    - (31004543202361344 : R) * h ^ 46 * a7 ^ 6 * a6 * a3 * b8
    - (13564487651033088 : R) * h ^ 46 * a7 ^ 6 * a5 ^ 2 * b7
    - (31004543202361344 : R) * h ^ 46 * a7 ^ 6 * a5 * a4 * b8
    - (23253407401771008 : R) * h ^ 46 * a7 ^ 5 * a6 ^ 3 * b6
    - (81386925906198528 : R) * h ^ 46 * a7 ^ 5 * a6 ^ 2 * a5 * b7
    - (93013629607084032 : R) * h ^ 46 * a7 ^ 5 * a6 ^ 2 * a4 * b8
    - (93013629607084032 : R) * h ^ 46 * a7 ^ 5 * a6 * a5 ^ 2 * b8
    - (33911219127582720 : R) * h ^ 46 * a7 ^ 4 * a6 ^ 4 * b7
    - (155022716011806720 : R) * h ^ 46 * a7 ^ 4 * a6 ^ 3 * a5 * b8
    - (31004543202361344 : R) * h ^ 46 * a7 ^ 3 * a6 ^ 5 * b8
    - (1148396515098624 : R) * h ^ 47 * a7 ^ 8 * a2 * lambda
    - (9187172120788992 : R) * h ^ 47 * a7 ^ 7 * a6 * a3 * lambda
    - (9187172120788992 : R) * h ^ 47 * a7 ^ 7 * a5 * a4 * lambda
    - (32155102422761472 : R) * h ^ 47 * a7 ^ 6 * a6 ^ 2 * a4 * lambda


end Depression810FifteenthClearing
end Max11DegreeRoutes
end
/-! Part 5 of 40 of `Fable810ScaleZeroFourteenthDefectScratch`, split so that no single module elaborates them all
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


def localClearedFifteenthDefectBlock2_810
    {R : Type*} [CommRing R]
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (32155102422761472 : R) * h ^ 47 * a7 ^ 6 * a6 * a5 ^ 2 * lambda
    - (64310204845522944 : R) * h ^ 47 * a7 ^ 5 * a6 ^ 3 * a5 * lambda
    - (16077551211380736 : R) * h ^ 47 * a7 ^ 4 * a6 ^ 5 * lambda
    - (1124606756782080 : R) * h ^ 48 * a7 ^ 8 * a1
    - (2768262785925120 : R) * h ^ 48 * a7 ^ 7 * a6 * a2
    - (2768262785925120 : R) * h ^ 48 * a7 ^ 7 * a5 * a3
    - (1384131392962560 : R) * h ^ 48 * a7 ^ 7 * a4 ^ 2
    + (12111149688422400 : R) * h ^ 48 * a7 ^ 6 * a6 ^ 2 * a3
    + (24222299376844800 : R) * h ^ 48 * a7 ^ 6 * a6 * a5 * a4
    + (4037049896140800 : R) * h ^ 48 * a7 ^ 6 * a5 ^ 3
    + (67822438255165440 : R) * h ^ 48 * a7 ^ 5 * a6 ^ 3 * a4
    + (101733657382748160 : R) * h ^ 48 * a7 ^ 5 * a6 ^ 2 * a5 ^ 2
    + (139278221416857600 : R) * h ^ 48 * a7 ^ 4 * a6 ^ 4 * a5
    + (25837119335301120 : R) * h ^ 48 * a7 ^ 3 * a6 ^ 6
    + (173694919901184 : R) * h ^ 54 * a7 ^ 7 * b2
    + (1823796658962432 : R) * h ^ 54 * a7 ^ 6 * a6 * b3
    + (2431728878616576 : R) * h ^ 54 * a7 ^ 6 * a5 * b4
    + (3039661098270720 : R) * h ^ 54 * a7 ^ 6 * a4 * b5
    + (3647593317924864 : R) * h ^ 54 * a7 ^ 6 * a3 * b6
    + (4255525537579008 : R) * h ^ 54 * a7 ^ 6 * a2 * b7
    + (4863457757233152 : R) * h ^ 54 * a7 ^ 6 * a1 * b8
    + (7295186635849728 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 2 * b4
    + (18237966589624320 : R) * h ^ 54 * a7 ^ 5 * a6 * a5 * b5
    + (21885559907549184 : R) * h ^ 54 * a7 ^ 5 * a6 * a4 * b6
    + (25533153225474048 : R) * h ^ 54 * a7 ^ 5 * a6 * a3 * b7
    + (29180746543398912 : R) * h ^ 54 * a7 ^ 5 * a6 * a2 * b8
    + (10942779953774592 : R) * h ^ 54 * a7 ^ 5 * a5 ^ 2 * b6
    + (25533153225474048 : R) * h ^ 54 * a7 ^ 5 * a5 * a4 * b7
    + (29180746543398912 : R) * h ^ 54 * a7 ^ 5 * a5 * a3 * b8
    + (14590373271699456 : R) * h ^ 54 * a7 ^ 5 * a4 ^ 2 * b8
    + (15198305491353600 : R) * h ^ 54 * a7 ^ 4 * a6 ^ 3 * b5
    + (54713899768872960 : R) * h ^ 54 * a7 ^ 4 * a6 ^ 2 * a5 * b6
    + (63832883063685120 : R) * h ^ 54 * a7 ^ 4 * a6 ^ 2 * a4 * b7
    + (72951866358497280 : R) * h ^ 54 * a7 ^ 4 * a6 ^ 2 * a3 * b8
    + (63832883063685120 : R) * h ^ 54 * a7 ^ 4 * a6 * a5 ^ 2 * b7
    + (145903732716994560 : R) * h ^ 54 * a7 ^ 4 * a6 * a5 * a4 * b8
    + (24317288786165760 : R) * h ^ 54 * a7 ^ 4 * a5 ^ 3 * b8
    + (18237966589624320 : R) * h ^ 54 * a7 ^ 3 * a6 ^ 4 * b6
    + (85110510751580160 : R) * h ^ 54 * a7 ^ 3 * a6 ^ 3 * a5 * b7
    + (97269155144663040 : R) * h ^ 54 * a7 ^ 3 * a6 ^ 3 * a4 * b8


end Depression810FifteenthClearing
end Max11DegreeRoutes
end
/-! Part 6 of 40 of `Fable810ScaleZeroFourteenthDefectScratch`, split so that no single module elaborates them all
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


def localClearedFifteenthDefectBlock3_810
    {R : Type*} [CommRing R]
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (145903732716994560 : R) * h ^ 54 * a7 ^ 3 * a6 ^ 2 * a5 ^ 2 * b8
    + (12766576612737024 : R) * h ^ 54 * a7 ^ 2 * a6 ^ 5 * b7
    + (72951866358497280 : R) * h ^ 54 * a7 ^ 2 * a6 ^ 4 * a5 * b8
    + (4863457757233152 : R) * h ^ 54 * a7 * a6 ^ 6 * b8
    + (1245718253666304 : R) * h ^ 55 * a7 ^ 7 * a1 * lambda
    + (8720027775664128 : R) * h ^ 55 * a7 ^ 6 * a6 * a2 * lambda
    + (8720027775664128 : R) * h ^ 55 * a7 ^ 6 * a5 * a3 * lambda
    + (4360013887832064 : R) * h ^ 55 * a7 ^ 6 * a4 ^ 2 * lambda
    + (26160083326992384 : R) * h ^ 55 * a7 ^ 5 * a6 ^ 2 * a3 * lambda
    + (52320166653984768 : R) * h ^ 55 * a7 ^ 5 * a6 * a5 * a4 * lambda
    + (8720027775664128 : R) * h ^ 55 * a7 ^ 5 * a5 ^ 3 * lambda
    + (43600138878320640 : R) * h ^ 55 * a7 ^ 4 * a6 ^ 3 * a4 * lambda
    + (65400208317480960 : R) * h ^ 55 * a7 ^ 4 * a6 ^ 2 * a5 ^ 2 * lambda
    + (43600138878320640 : R) * h ^ 55 * a7 ^ 3 * a6 ^ 4 * a5 * lambda
    + (4360013887832064 : R) * h ^ 55 * a7 ^ 2 * a6 ^ 6 * lambda
    + (1302711899258880 : R) * h ^ 56 * a7 ^ 7 * a0
    + (2279745823703040 : R) * h ^ 56 * a7 ^ 6 * a6 * a1
    + (2279745823703040 : R) * h ^ 56 * a7 ^ 6 * a5 * a2
    + (2279745823703040 : R) * h ^ 56 * a7 ^ 6 * a4 * a3
    - (13678474942218240 : R) * h ^ 56 * a7 ^ 5 * a6 ^ 2 * a2
    - (27356949884436480 : R) * h ^ 56 * a7 ^ 5 * a6 * a5 * a3
    - (13678474942218240 : R) * h ^ 56 * a7 ^ 5 * a6 * a4 ^ 2
    - (13678474942218240 : R) * h ^ 56 * a7 ^ 5 * a5 ^ 2 * a4
    - (56993645592576000 : R) * h ^ 56 * a7 ^ 4 * a6 ^ 3 * a3
    - (170980936777728000 : R) * h ^ 56 * a7 ^ 4 * a6 ^ 2 * a5 * a4
    - (56993645592576000 : R) * h ^ 56 * a7 ^ 4 * a6 * a5 ^ 3
    - (91189832948121600 : R) * h ^ 56 * a7 ^ 3 * a6 ^ 4 * a4
    - (182379665896243200 : R) * h ^ 56 * a7 ^ 3 * a6 ^ 3 * a5 ^ 2
    - (75231612182200320 : R) * h ^ 56 * a7 ^ 2 * a6 ^ 5 * a5
    - (4559491647406080 : R) * h ^ 56 * a7 * a6 ^ 7
    - (113103668772864 : R) * h ^ 62 * a7 ^ 6 * b1
    - (1357244025274368 : R) * h ^ 62 * a7 ^ 5 * a6 * b2
    - (2035866037911552 : R) * h ^ 62 * a7 ^ 5 * a5 * b3
    - (2714488050548736 : R) * h ^ 62 * a7 ^ 5 * a4 * b4
    - (3393110063185920 : R) * h ^ 62 * a7 ^ 5 * a3 * b5
    - (4071732075823104 : R) * h ^ 62 * a7 ^ 5 * a2 * b6
    - (4750354088460288 : R) * h ^ 62 * a7 ^ 5 * a1 * b7
    - (5428976101097472 : R) * h ^ 62 * a7 ^ 5 * a0 * b8
    - (5089665094778880 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 2 * b3
    - (13572440252743680 : R) * h ^ 62 * a7 ^ 4 * a6 * a5 * b4


end Depression810FifteenthClearing
end Max11DegreeRoutes
end
/-! Part 7 of 40 of `Fable810ScaleZeroFourteenthDefectScratch`, split so that no single module elaborates them all
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


def localClearedFifteenthDefectBlock4_810
    {R : Type*} [CommRing R]
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (16965550315929600 : R) * h ^ 62 * a7 ^ 4 * a6 * a4 * b5
    - (20358660379115520 : R) * h ^ 62 * a7 ^ 4 * a6 * a3 * b6
    - (23751770442301440 : R) * h ^ 62 * a7 ^ 4 * a6 * a2 * b7
    - (27144880505487360 : R) * h ^ 62 * a7 ^ 4 * a6 * a1 * b8
    - (8482775157964800 : R) * h ^ 62 * a7 ^ 4 * a5 ^ 2 * b5
    - (20358660379115520 : R) * h ^ 62 * a7 ^ 4 * a5 * a4 * b6
    - (23751770442301440 : R) * h ^ 62 * a7 ^ 4 * a5 * a3 * b7
    - (27144880505487360 : R) * h ^ 62 * a7 ^ 4 * a5 * a2 * b8
    - (11875885221150720 : R) * h ^ 62 * a7 ^ 4 * a4 ^ 2 * b7
    - (27144880505487360 : R) * h ^ 62 * a7 ^ 4 * a4 * a3 * b8
    - (9048293501829120 : R) * h ^ 62 * a7 ^ 3 * a6 ^ 3 * b4
    - (33931100631859200 : R) * h ^ 62 * a7 ^ 3 * a6 ^ 2 * a5 * b5
    - (40717320758231040 : R) * h ^ 62 * a7 ^ 3 * a6 ^ 2 * a4 * b6
    - (47503540884602880 : R) * h ^ 62 * a7 ^ 3 * a6 ^ 2 * a3 * b7
    - (54289761010974720 : R) * h ^ 62 * a7 ^ 3 * a6 ^ 2 * a2 * b8
    - (40717320758231040 : R) * h ^ 62 * a7 ^ 3 * a6 * a5 ^ 2 * b6
    - (95007081769205760 : R) * h ^ 62 * a7 ^ 3 * a6 * a5 * a4 * b7
    - (108579522021949440 : R) * h ^ 62 * a7 ^ 3 * a6 * a5 * a3 * b8
    - (54289761010974720 : R) * h ^ 62 * a7 ^ 3 * a6 * a4 ^ 2 * b8
    - (15834513628200960 : R) * h ^ 62 * a7 ^ 3 * a5 ^ 3 * b7
    - (54289761010974720 : R) * h ^ 62 * a7 ^ 3 * a5 ^ 2 * a4 * b8
    - (8482775157964800 : R) * h ^ 62 * a7 ^ 2 * a6 ^ 4 * b5
    - (40717320758231040 : R) * h ^ 62 * a7 ^ 2 * a6 ^ 3 * a5 * b6
    - (47503540884602880 : R) * h ^ 62 * a7 ^ 2 * a6 ^ 3 * a4 * b7
    - (54289761010974720 : R) * h ^ 62 * a7 ^ 2 * a6 ^ 3 * a3 * b8
    - (71255311326904320 : R) * h ^ 62 * a7 ^ 2 * a6 ^ 2 * a5 ^ 2 * b7
    - (162869283032924160 : R) * h ^ 62 * a7 ^ 2 * a6 ^ 2 * a5 * a4 * b8
    - (54289761010974720 : R) * h ^ 62 * a7 ^ 2 * a6 * a5 ^ 3 * b8
    - (4071732075823104 : R) * h ^ 62 * a7 * a6 ^ 5 * b6
    - (23751770442301440 : R) * h ^ 62 * a7 * a6 ^ 4 * a5 * b7
    - (27144880505487360 : R) * h ^ 62 * a7 * a6 ^ 4 * a4 * b8
    - (54289761010974720 : R) * h ^ 62 * a7 * a6 ^ 3 * a5 ^ 2 * b8
    - (791725681410048 : R) * h ^ 62 * a6 ^ 6 * b7
    - (5428976101097472 : R) * h ^ 62 * a6 ^ 5 * a5 * b8
    - (1367847494221824 : R) * h ^ 63 * a7 ^ 6 * a0 * lambda
    - (8207084965330944 : R) * h ^ 63 * a7 ^ 5 * a6 * a1 * lambda
    - (8207084965330944 : R) * h ^ 63 * a7 ^ 5 * a5 * a2 * lambda
    - (8207084965330944 : R) * h ^ 63 * a7 ^ 5 * a4 * a3 * lambda
    - (20517712413327360 : R) * h ^ 63 * a7 ^ 4 * a6 ^ 2 * a2 * lambda
    - (41035424826654720 : R) * h ^ 63 * a7 ^ 4 * a6 * a5 * a3 * lambda


end Depression810FifteenthClearing
end Max11DegreeRoutes
end
/-! Part 8 of 40 of `Fable810ScaleZeroFourteenthDefectScratch`, split so that no single module elaborates them all
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


def localClearedFifteenthDefectBlock5_810
    {R : Type*} [CommRing R]
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (20517712413327360 : R) * h ^ 63 * a7 ^ 4 * a6 * a4 ^ 2 * lambda
    - (20517712413327360 : R) * h ^ 63 * a7 ^ 4 * a5 ^ 2 * a4 * lambda
    - (27356949884436480 : R) * h ^ 63 * a7 ^ 3 * a6 ^ 3 * a3 * lambda
    - (82070849653309440 : R) * h ^ 63 * a7 ^ 3 * a6 ^ 2 * a5 * a4 * lambda
    - (27356949884436480 : R) * h ^ 63 * a7 ^ 3 * a6 * a5 ^ 3 * lambda
    - (20517712413327360 : R) * h ^ 63 * a7 ^ 2 * a6 ^ 4 * a4 * lambda
    - (41035424826654720 : R) * h ^ 63 * a7 ^ 2 * a6 ^ 3 * a5 ^ 2 * lambda
    - (8207084965330944 : R) * h ^ 63 * a7 * a6 ^ 5 * a5 * lambda
    - (195406784888832 : R) * h ^ 63 * a6 ^ 7 * lambda
    - (1696555031592960 : R) * h ^ 64 * a7 ^ 5 * a6 * a0
    - (1696555031592960 : R) * h ^ 64 * a7 ^ 5 * a5 * a1
    - (1696555031592960 : R) * h ^ 64 * a7 ^ 5 * a4 * a2
    - (848277515796480 : R) * h ^ 64 * a7 ^ 5 * a3 ^ 2
    + (14844856526438400 : R) * h ^ 64 * a7 ^ 4 * a6 ^ 2 * a1
    + (29689713052876800 : R) * h ^ 64 * a7 ^ 4 * a6 * a5 * a2
    + (29689713052876800 : R) * h ^ 64 * a7 ^ 4 * a6 * a4 * a3
    + (14844856526438400 : R) * h ^ 64 * a7 ^ 4 * a5 ^ 2 * a3
    + (14844856526438400 : R) * h ^ 64 * a7 ^ 4 * a5 * a4 ^ 2
    + (45241467509145600 : R) * h ^ 64 * a7 ^ 3 * a6 ^ 3 * a2
    + (135724402527436800 : R) * h ^ 64 * a7 ^ 3 * a6 ^ 2 * a5 * a3
    + (67862201263718400 : R) * h ^ 64 * a7 ^ 3 * a6 ^ 2 * a4 ^ 2
    + (135724402527436800 : R) * h ^ 64 * a7 ^ 3 * a6 * a5 ^ 2 * a4
    + (11310366877286400 : R) * h ^ 64 * a7 ^ 3 * a5 ^ 4
    + (53017344737280000 : R) * h ^ 64 * a7 ^ 2 * a6 ^ 4 * a3
    + (212069378949120000 : R) * h ^ 64 * a7 ^ 2 * a6 ^ 3 * a5 * a4
    + (106034689474560000 : R) * h ^ 64 * a7 ^ 2 * a6 ^ 2 * a5 ^ 3
    + (28841435537080320 : R) * h ^ 64 * a7 * a6 ^ 5 * a4
    + (72103588842700800 : R) * h ^ 64 * a7 * a6 ^ 4 * a5 ^ 2
    + (6079322196541440 : R) * h ^ 64 * a6 ^ 6 * a5
    + (775568014442496 : R) * h ^ 70 * a7 ^ 4 * a6 * b1
    + (1551136028884992 : R) * h ^ 70 * a7 ^ 4 * a5 * b2
    + (2326704043327488 : R) * h ^ 70 * a7 ^ 4 * a4 * b3
    + (3102272057769984 : R) * h ^ 70 * a7 ^ 4 * a3 * b4
    + (3877840072212480 : R) * h ^ 70 * a7 ^ 4 * a2 * b5
    + (4653408086654976 : R) * h ^ 70 * a7 ^ 4 * a1 * b6
    + (5428976101097472 : R) * h ^ 70 * a7 ^ 4 * a0 * b7
    + (3102272057769984 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 2 * b2
    + (9306816173309952 : R) * h ^ 70 * a7 ^ 3 * a6 * a5 * b3
    + (12409088231079936 : R) * h ^ 70 * a7 ^ 3 * a6 * a4 * b4
    + (15511360288849920 : R) * h ^ 70 * a7 ^ 3 * a6 * a3 * b5


end Depression810FifteenthClearing
end Max11DegreeRoutes
end
/-! Part 9 of 40 of `Fable810ScaleZeroFourteenthDefectScratch`, split so that no single module elaborates them all
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


def localClearedFifteenthDefectBlock6_810
    {R : Type*} [CommRing R]
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (18613632346619904 : R) * h ^ 70 * a7 ^ 3 * a6 * a2 * b6
    + (21715904404389888 : R) * h ^ 70 * a7 ^ 3 * a6 * a1 * b7
    + (24818176462159872 : R) * h ^ 70 * a7 ^ 3 * a6 * a0 * b8
    + (6204544115539968 : R) * h ^ 70 * a7 ^ 3 * a5 ^ 2 * b4
    + (15511360288849920 : R) * h ^ 70 * a7 ^ 3 * a5 * a4 * b5
    + (18613632346619904 : R) * h ^ 70 * a7 ^ 3 * a5 * a3 * b6
    + (21715904404389888 : R) * h ^ 70 * a7 ^ 3 * a5 * a2 * b7
    + (24818176462159872 : R) * h ^ 70 * a7 ^ 3 * a5 * a1 * b8
    + (9306816173309952 : R) * h ^ 70 * a7 ^ 3 * a4 ^ 2 * b6
    + (21715904404389888 : R) * h ^ 70 * a7 ^ 3 * a4 * a3 * b7
    + (24818176462159872 : R) * h ^ 70 * a7 ^ 3 * a4 * a2 * b8
    + (12409088231079936 : R) * h ^ 70 * a7 ^ 3 * a3 ^ 2 * b8
    + (4653408086654976 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 3 * b3
    + (18613632346619904 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 2 * a5 * b4
    + (23267040433274880 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 2 * a4 * b5
    + (27920448519929856 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 2 * a3 * b6
    + (32573856606584832 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 2 * a2 * b7
    + (37227264693239808 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 2 * a1 * b8
    + (23267040433274880 : R) * h ^ 70 * a7 ^ 2 * a6 * a5 ^ 2 * b5
    + (55840897039859712 : R) * h ^ 70 * a7 ^ 2 * a6 * a5 * a4 * b6
    + (65147713213169664 : R) * h ^ 70 * a7 ^ 2 * a6 * a5 * a3 * b7
    + (74454529386479616 : R) * h ^ 70 * a7 ^ 2 * a6 * a5 * a2 * b8
    + (32573856606584832 : R) * h ^ 70 * a7 ^ 2 * a6 * a4 ^ 2 * b7
    + (74454529386479616 : R) * h ^ 70 * a7 ^ 2 * a6 * a4 * a3 * b8
    + (9306816173309952 : R) * h ^ 70 * a7 ^ 2 * a5 ^ 3 * b6
    + (32573856606584832 : R) * h ^ 70 * a7 ^ 2 * a5 ^ 2 * a4 * b7
    + (37227264693239808 : R) * h ^ 70 * a7 ^ 2 * a5 ^ 2 * a3 * b8
    + (37227264693239808 : R) * h ^ 70 * a7 ^ 2 * a5 * a4 ^ 2 * b8
    + (3102272057769984 : R) * h ^ 70 * a7 * a6 ^ 4 * b4
    + (15511360288849920 : R) * h ^ 70 * a7 * a6 ^ 3 * a5 * b5
    + (18613632346619904 : R) * h ^ 70 * a7 * a6 ^ 3 * a4 * b6
    + (21715904404389888 : R) * h ^ 70 * a7 * a6 ^ 3 * a3 * b7
    + (24818176462159872 : R) * h ^ 70 * a7 * a6 ^ 3 * a2 * b8
    + (27920448519929856 : R) * h ^ 70 * a7 * a6 ^ 2 * a5 ^ 2 * b6
    + (65147713213169664 : R) * h ^ 70 * a7 * a6 ^ 2 * a5 * a4 * b7
    + (74454529386479616 : R) * h ^ 70 * a7 * a6 ^ 2 * a5 * a3 * b8
    + (37227264693239808 : R) * h ^ 70 * a7 * a6 ^ 2 * a4 ^ 2 * b8
    + (21715904404389888 : R) * h ^ 70 * a7 * a6 * a5 ^ 3 * b7
    + (74454529386479616 : R) * h ^ 70 * a7 * a6 * a5 ^ 2 * a4 * b8
    + (6204544115539968 : R) * h ^ 70 * a7 * a5 ^ 4 * b8


end Depression810FifteenthClearing
end Max11DegreeRoutes
end
/-! Part 10 of 40 of `Fable810ScaleZeroFourteenthDefectScratch`, split so that no single module elaborates them all
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


def localClearedFifteenthDefectBlock7_810
    {R : Type*} [CommRing R]
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (775568014442496 : R) * h ^ 70 * a6 ^ 5 * b5
    + (4653408086654976 : R) * h ^ 70 * a6 ^ 4 * a5 * b6
    + (5428976101097472 : R) * h ^ 70 * a6 ^ 4 * a4 * b7
    + (6204544115539968 : R) * h ^ 70 * a6 ^ 4 * a3 * b8
    + (10857952202194944 : R) * h ^ 70 * a6 ^ 3 * a5 ^ 2 * b7
    + (24818176462159872 : R) * h ^ 70 * a6 ^ 3 * a5 * a4 * b8
    + (12409088231079936 : R) * h ^ 70 * a6 ^ 2 * a5 ^ 3 * b8
    + (7634497642168320 : R) * h ^ 71 * a7 ^ 4 * a6 * a0 * lambda
    + (7634497642168320 : R) * h ^ 71 * a7 ^ 4 * a5 * a1 * lambda
    + (7634497642168320 : R) * h ^ 71 * a7 ^ 4 * a4 * a2 * lambda
    + (3817248821084160 : R) * h ^ 71 * a7 ^ 4 * a3 ^ 2 * lambda
    + (15268995284336640 : R) * h ^ 71 * a7 ^ 3 * a6 ^ 2 * a1 * lambda
    + (30537990568673280 : R) * h ^ 71 * a7 ^ 3 * a6 * a5 * a2 * lambda
    + (30537990568673280 : R) * h ^ 71 * a7 ^ 3 * a6 * a4 * a3 * lambda
    + (15268995284336640 : R) * h ^ 71 * a7 ^ 3 * a5 ^ 2 * a3 * lambda
    + (15268995284336640 : R) * h ^ 71 * a7 ^ 3 * a5 * a4 ^ 2 * lambda
    + (15268995284336640 : R) * h ^ 71 * a7 ^ 2 * a6 ^ 3 * a2 * lambda
    + (45806985853009920 : R) * h ^ 71 * a7 ^ 2 * a6 ^ 2 * a5 * a3 * lambda
    + (22903492926504960 : R) * h ^ 71 * a7 ^ 2 * a6 ^ 2 * a4 ^ 2 * lambda
    + (45806985853009920 : R) * h ^ 71 * a7 ^ 2 * a6 * a5 ^ 2 * a4 * lambda
    + (3817248821084160 : R) * h ^ 71 * a7 ^ 2 * a5 ^ 4 * lambda
    + (7634497642168320 : R) * h ^ 71 * a7 * a6 ^ 4 * a3 * lambda
    + (30537990568673280 : R) * h ^ 71 * a7 * a6 ^ 3 * a5 * a4 * lambda
    + (15268995284336640 : R) * h ^ 71 * a7 * a6 ^ 2 * a5 ^ 3 * lambda
    + (1526899528433664 : R) * h ^ 71 * a6 ^ 5 * a4 * lambda
    + (3817248821084160 : R) * h ^ 71 * a6 ^ 4 * a5 ^ 2 * lambda
    + (969460018053120 : R) * h ^ 72 * a7 ^ 4 * a5 * a0
    + (969460018053120 : R) * h ^ 72 * a7 ^ 4 * a4 * a1
    + (969460018053120 : R) * h ^ 72 * a7 ^ 4 * a3 * a2
    - (15511360288849920 : R) * h ^ 72 * a7 ^ 3 * a6 ^ 2 * a0
    - (31022720577699840 : R) * h ^ 72 * a7 ^ 3 * a6 * a5 * a1
    - (31022720577699840 : R) * h ^ 72 * a7 ^ 3 * a6 * a4 * a2
    - (15511360288849920 : R) * h ^ 72 * a7 ^ 3 * a6 * a3 ^ 2
    - (15511360288849920 : R) * h ^ 72 * a7 ^ 3 * a5 ^ 2 * a2
    - (31022720577699840 : R) * h ^ 72 * a7 ^ 3 * a5 * a4 * a3
    - (5170453429616640 : R) * h ^ 72 * a7 ^ 3 * a4 ^ 3
    - (32961640613806080 : R) * h ^ 72 * a7 ^ 2 * a6 ^ 3 * a1
    - (98884921841418240 : R) * h ^ 72 * a7 ^ 2 * a6 ^ 2 * a5 * a2
    - (98884921841418240 : R) * h ^ 72 * a7 ^ 2 * a6 ^ 2 * a4 * a3
    - (98884921841418240 : R) * h ^ 72 * a7 ^ 2 * a6 * a5 ^ 2 * a3


end Depression810FifteenthClearing
end Max11DegreeRoutes
end
/-! Part 11 of 40 of `Fable810ScaleZeroFourteenthDefectScratch`, split so that no single module elaborates them all
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


def localClearedFifteenthDefectBlock8_810
    {R : Type*} [CommRing R]
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (98884921841418240 : R) * h ^ 72 * a7 ^ 2 * a6 * a5 * a4 ^ 2
    - (32961640613806080 : R) * h ^ 72 * a7 ^ 2 * a5 ^ 3 * a4
    - (25205960469381120 : R) * h ^ 72 * a7 * a6 ^ 4 * a2
    - (100823841877524480 : R) * h ^ 72 * a7 * a6 ^ 3 * a5 * a3
    - (50411920938762240 : R) * h ^ 72 * a7 * a6 ^ 3 * a4 ^ 2
    - (151235762816286720 : R) * h ^ 72 * a7 * a6 ^ 2 * a5 ^ 2 * a4
    - (25205960469381120 : R) * h ^ 72 * a7 * a6 * a5 ^ 4
    - (6786220126371840 : R) * h ^ 72 * a6 ^ 5 * a3
    - (33931100631859200 : R) * h ^ 72 * a6 ^ 4 * a5 * a4
    - (22620733754572800 : R) * h ^ 72 * a6 ^ 3 * a5 ^ 3
    - (919191720820736 : R) * h ^ 78 * a7 ^ 3 * a5 * b1
    - (1838383441641472 : R) * h ^ 78 * a7 ^ 3 * a4 * b2
    - (2757575162462208 : R) * h ^ 78 * a7 ^ 3 * a3 * b3
    - (3676766883282944 : R) * h ^ 78 * a7 ^ 3 * a2 * b4
    - (4595958604103680 : R) * h ^ 78 * a7 ^ 3 * a1 * b5
    - (5515150324924416 : R) * h ^ 78 * a7 ^ 3 * a0 * b6
    - (1378787581231104 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 2 * b1
    - (5515150324924416 : R) * h ^ 78 * a7 ^ 2 * a6 * a5 * b2
    - (8272725487386624 : R) * h ^ 78 * a7 ^ 2 * a6 * a4 * b3
    - (11030300649848832 : R) * h ^ 78 * a7 ^ 2 * a6 * a3 * b4
    - (13787875812311040 : R) * h ^ 78 * a7 ^ 2 * a6 * a2 * b5
    - (16545450974773248 : R) * h ^ 78 * a7 ^ 2 * a6 * a1 * b6
    - (19303026137235456 : R) * h ^ 78 * a7 ^ 2 * a6 * a0 * b7
    - (4136362743693312 : R) * h ^ 78 * a7 ^ 2 * a5 ^ 2 * b3
    - (11030300649848832 : R) * h ^ 78 * a7 ^ 2 * a5 * a4 * b4
    - (13787875812311040 : R) * h ^ 78 * a7 ^ 2 * a5 * a3 * b5
    - (16545450974773248 : R) * h ^ 78 * a7 ^ 2 * a5 * a2 * b6
    - (19303026137235456 : R) * h ^ 78 * a7 ^ 2 * a5 * a1 * b7
    - (22060601299697664 : R) * h ^ 78 * a7 ^ 2 * a5 * a0 * b8
    - (6893937906155520 : R) * h ^ 78 * a7 ^ 2 * a4 ^ 2 * b5
    - (16545450974773248 : R) * h ^ 78 * a7 ^ 2 * a4 * a3 * b6
    - (19303026137235456 : R) * h ^ 78 * a7 ^ 2 * a4 * a2 * b7
    - (22060601299697664 : R) * h ^ 78 * a7 ^ 2 * a4 * a1 * b8
    - (9651513068617728 : R) * h ^ 78 * a7 ^ 2 * a3 ^ 2 * b7
    - (22060601299697664 : R) * h ^ 78 * a7 ^ 2 * a3 * a2 * b8
    - (1838383441641472 : R) * h ^ 78 * a7 * a6 ^ 3 * b2
    - (8272725487386624 : R) * h ^ 78 * a7 * a6 ^ 2 * a5 * b3
    - (11030300649848832 : R) * h ^ 78 * a7 * a6 ^ 2 * a4 * b4
    - (13787875812311040 : R) * h ^ 78 * a7 * a6 ^ 2 * a3 * b5
    - (16545450974773248 : R) * h ^ 78 * a7 * a6 ^ 2 * a2 * b6


end Depression810FifteenthClearing
end Max11DegreeRoutes
end
/-! Part 12 of 40 of `Fable810ScaleZeroFourteenthDefectScratch`, split so that no single module elaborates them all
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


def localClearedFifteenthDefectBlock9_810
    {R : Type*} [CommRing R]
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (19303026137235456 : R) * h ^ 78 * a7 * a6 ^ 2 * a1 * b7
    - (22060601299697664 : R) * h ^ 78 * a7 * a6 ^ 2 * a0 * b8
    - (11030300649848832 : R) * h ^ 78 * a7 * a6 * a5 ^ 2 * b4
    - (27575751624622080 : R) * h ^ 78 * a7 * a6 * a5 * a4 * b5
    - (33090901949546496 : R) * h ^ 78 * a7 * a6 * a5 * a3 * b6
    - (38606052274470912 : R) * h ^ 78 * a7 * a6 * a5 * a2 * b7
    - (44121202599395328 : R) * h ^ 78 * a7 * a6 * a5 * a1 * b8
    - (16545450974773248 : R) * h ^ 78 * a7 * a6 * a4 ^ 2 * b6
    - (38606052274470912 : R) * h ^ 78 * a7 * a6 * a4 * a3 * b7
    - (44121202599395328 : R) * h ^ 78 * a7 * a6 * a4 * a2 * b8
    - (22060601299697664 : R) * h ^ 78 * a7 * a6 * a3 ^ 2 * b8
    - (4595958604103680 : R) * h ^ 78 * a7 * a5 ^ 3 * b5
    - (16545450974773248 : R) * h ^ 78 * a7 * a5 ^ 2 * a4 * b6
    - (19303026137235456 : R) * h ^ 78 * a7 * a5 ^ 2 * a3 * b7
    - (22060601299697664 : R) * h ^ 78 * a7 * a5 ^ 2 * a2 * b8
    - (19303026137235456 : R) * h ^ 78 * a7 * a5 * a4 ^ 2 * b7
    - (44121202599395328 : R) * h ^ 78 * a7 * a5 * a4 * a3 * b8
    - (7353533766565888 : R) * h ^ 78 * a7 * a4 ^ 3 * b8
    - (689393790615552 : R) * h ^ 78 * a6 ^ 4 * b3
    - (3676766883282944 : R) * h ^ 78 * a6 ^ 3 * a5 * b4
    - (4595958604103680 : R) * h ^ 78 * a6 ^ 3 * a4 * b5
    - (5515150324924416 : R) * h ^ 78 * a6 ^ 3 * a3 * b6
    - (6434342045745152 : R) * h ^ 78 * a6 ^ 3 * a2 * b7
    - (7353533766565888 : R) * h ^ 78 * a6 ^ 3 * a1 * b8
    - (6893937906155520 : R) * h ^ 78 * a6 ^ 2 * a5 ^ 2 * b5
    - (16545450974773248 : R) * h ^ 78 * a6 ^ 2 * a5 * a4 * b6
    - (19303026137235456 : R) * h ^ 78 * a6 ^ 2 * a5 * a3 * b7
    - (22060601299697664 : R) * h ^ 78 * a6 ^ 2 * a5 * a2 * b8
    - (9651513068617728 : R) * h ^ 78 * a6 ^ 2 * a4 ^ 2 * b7
    - (22060601299697664 : R) * h ^ 78 * a6 ^ 2 * a4 * a3 * b8
    - (5515150324924416 : R) * h ^ 78 * a6 * a5 ^ 3 * b6
    - (19303026137235456 : R) * h ^ 78 * a6 * a5 ^ 2 * a4 * b7
    - (22060601299697664 : R) * h ^ 78 * a6 * a5 ^ 2 * a3 * b8
    - (22060601299697664 : R) * h ^ 78 * a6 * a5 * a4 ^ 2 * b8
    - (1608585511436288 : R) * h ^ 78 * a5 ^ 4 * b7
    - (7353533766565888 : R) * h ^ 78 * a5 ^ 3 * a4 * b8
    - (6980112129982464 : R) * h ^ 79 * a7 ^ 3 * a5 * a0 * lambda
    - (6980112129982464 : R) * h ^ 79 * a7 ^ 3 * a4 * a1 * lambda
    - (6980112129982464 : R) * h ^ 79 * a7 ^ 3 * a3 * a2 * lambda
    - (10470168194973696 : R) * h ^ 79 * a7 ^ 2 * a6 ^ 2 * a0 * lambda


end Depression810FifteenthClearing
end Max11DegreeRoutes
end
/-! Part 13 of 40 of `Fable810ScaleZeroFourteenthDefectScratch`, split so that no single module elaborates them all
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


def localClearedFifteenthDefectBlock10_810
    {R : Type*} [CommRing R]
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (20940336389947392 : R) * h ^ 79 * a7 ^ 2 * a6 * a5 * a1 * lambda
    - (20940336389947392 : R) * h ^ 79 * a7 ^ 2 * a6 * a4 * a2 * lambda
    - (10470168194973696 : R) * h ^ 79 * a7 ^ 2 * a6 * a3 ^ 2 * lambda
    - (10470168194973696 : R) * h ^ 79 * a7 ^ 2 * a5 ^ 2 * a2 * lambda
    - (20940336389947392 : R) * h ^ 79 * a7 ^ 2 * a5 * a4 * a3 * lambda
    - (3490056064991232 : R) * h ^ 79 * a7 ^ 2 * a4 ^ 3 * lambda
    - (6980112129982464 : R) * h ^ 79 * a7 * a6 ^ 3 * a1 * lambda
    - (20940336389947392 : R) * h ^ 79 * a7 * a6 ^ 2 * a5 * a2 * lambda
    - (20940336389947392 : R) * h ^ 79 * a7 * a6 ^ 2 * a4 * a3 * lambda
    - (20940336389947392 : R) * h ^ 79 * a7 * a6 * a5 ^ 2 * a3 * lambda
    - (20940336389947392 : R) * h ^ 79 * a7 * a6 * a5 * a4 ^ 2 * lambda
    - (6980112129982464 : R) * h ^ 79 * a7 * a5 ^ 3 * a4 * lambda
    - (1745028032495616 : R) * h ^ 79 * a6 ^ 4 * a2 * lambda
    - (6980112129982464 : R) * h ^ 79 * a6 ^ 3 * a5 * a3 * lambda
    - (3490056064991232 : R) * h ^ 79 * a6 ^ 3 * a4 ^ 2 * lambda
    - (10470168194973696 : R) * h ^ 79 * a6 ^ 2 * a5 ^ 2 * a4 * lambda
    - (1745028032495616 : R) * h ^ 79 * a6 * a5 ^ 4 * lambda
    + (31022720577699840 : R) * h ^ 80 * a7 ^ 2 * a6 * a5 * a0
    + (31022720577699840 : R) * h ^ 80 * a7 ^ 2 * a6 * a4 * a1
    + (31022720577699840 : R) * h ^ 80 * a7 ^ 2 * a6 * a3 * a2
    + (15511360288849920 : R) * h ^ 80 * a7 ^ 2 * a5 ^ 2 * a1
    + (31022720577699840 : R) * h ^ 80 * a7 ^ 2 * a5 * a4 * a2
    + (15511360288849920 : R) * h ^ 80 * a7 ^ 2 * a5 * a3 ^ 2
    + (15511360288849920 : R) * h ^ 80 * a7 ^ 2 * a4 ^ 2 * a3
    + (20681813718466560 : R) * h ^ 80 * a7 * a6 ^ 3 * a0
    + (62045441155399680 : R) * h ^ 80 * a7 * a6 ^ 2 * a5 * a1
    + (62045441155399680 : R) * h ^ 80 * a7 * a6 ^ 2 * a4 * a2
    + (31022720577699840 : R) * h ^ 80 * a7 * a6 ^ 2 * a3 ^ 2
    + (62045441155399680 : R) * h ^ 80 * a7 * a6 * a5 ^ 2 * a2
    + (124090882310799360 : R) * h ^ 80 * a7 * a6 * a5 * a4 * a3
    + (20681813718466560 : R) * h ^ 80 * a7 * a6 * a4 ^ 3
    + (20681813718466560 : R) * h ^ 80 * a7 * a5 ^ 3 * a3
    + (31022720577699840 : R) * h ^ 80 * a7 * a5 ^ 2 * a4 ^ 2
    + (7755680144424960 : R) * h ^ 80 * a6 ^ 4 * a1
    + (31022720577699840 : R) * h ^ 80 * a6 ^ 3 * a5 * a2
    + (31022720577699840 : R) * h ^ 80 * a6 ^ 3 * a4 * a3
    + (46534080866549760 : R) * h ^ 80 * a6 ^ 2 * a5 ^ 2 * a3
    + (46534080866549760 : R) * h ^ 80 * a6 ^ 2 * a5 * a4 ^ 2
    + (31022720577699840 : R) * h ^ 80 * a6 * a5 ^ 3 * a4
    + (1551136028884992 : R) * h ^ 80 * a5 ^ 5


end Depression810FifteenthClearing
end Max11DegreeRoutes
end
/-! Part 14 of 40 of `Fable810ScaleZeroFourteenthDefectScratch`, split so that no single module elaborates them all
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


def localClearedFifteenthDefectBlock11_810
    {R : Type*} [CommRing R]
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (1161084278931456 : R) * h ^ 86 * a7 ^ 2 * a4 * b1
    + (2322168557862912 : R) * h ^ 86 * a7 ^ 2 * a3 * b2
    + (3483252836794368 : R) * h ^ 86 * a7 ^ 2 * a2 * b3
    + (4644337115725824 : R) * h ^ 86 * a7 ^ 2 * a1 * b4
    + (5805421394657280 : R) * h ^ 86 * a7 ^ 2 * a0 * b5
    + (2322168557862912 : R) * h ^ 86 * a7 * a6 * a5 * b1
    + (4644337115725824 : R) * h ^ 86 * a7 * a6 * a4 * b2
    + (6966505673588736 : R) * h ^ 86 * a7 * a6 * a3 * b3
    + (9288674231451648 : R) * h ^ 86 * a7 * a6 * a2 * b4
    + (11610842789314560 : R) * h ^ 86 * a7 * a6 * a1 * b5
    + (13933011347177472 : R) * h ^ 86 * a7 * a6 * a0 * b6
    + (2322168557862912 : R) * h ^ 86 * a7 * a5 ^ 2 * b2
    + (6966505673588736 : R) * h ^ 86 * a7 * a5 * a4 * b3
    + (9288674231451648 : R) * h ^ 86 * a7 * a5 * a3 * b4
    + (11610842789314560 : R) * h ^ 86 * a7 * a5 * a2 * b5
    + (13933011347177472 : R) * h ^ 86 * a7 * a5 * a1 * b6
    + (16255179905040384 : R) * h ^ 86 * a7 * a5 * a0 * b7
    + (4644337115725824 : R) * h ^ 86 * a7 * a4 ^ 2 * b4
    + (11610842789314560 : R) * h ^ 86 * a7 * a4 * a3 * b5
    + (13933011347177472 : R) * h ^ 86 * a7 * a4 * a2 * b6
    + (16255179905040384 : R) * h ^ 86 * a7 * a4 * a1 * b7
    + (18577348462903296 : R) * h ^ 86 * a7 * a4 * a0 * b8
    + (6966505673588736 : R) * h ^ 86 * a7 * a3 ^ 2 * b6
    + (16255179905040384 : R) * h ^ 86 * a7 * a3 * a2 * b7
    + (18577348462903296 : R) * h ^ 86 * a7 * a3 * a1 * b8
    + (9288674231451648 : R) * h ^ 86 * a7 * a2 ^ 2 * b8
    + (387028092977152 : R) * h ^ 86 * a6 ^ 3 * b1
    + (2322168557862912 : R) * h ^ 86 * a6 ^ 2 * a5 * b2
    + (3483252836794368 : R) * h ^ 86 * a6 ^ 2 * a4 * b3
    + (4644337115725824 : R) * h ^ 86 * a6 ^ 2 * a3 * b4
    + (5805421394657280 : R) * h ^ 86 * a6 ^ 2 * a2 * b5
    + (6966505673588736 : R) * h ^ 86 * a6 ^ 2 * a1 * b6
    + (8127589952520192 : R) * h ^ 86 * a6 ^ 2 * a0 * b7
    + (3483252836794368 : R) * h ^ 86 * a6 * a5 ^ 2 * b3
    + (9288674231451648 : R) * h ^ 86 * a6 * a5 * a4 * b4
    + (11610842789314560 : R) * h ^ 86 * a6 * a5 * a3 * b5
    + (13933011347177472 : R) * h ^ 86 * a6 * a5 * a2 * b6
    + (16255179905040384 : R) * h ^ 86 * a6 * a5 * a1 * b7
    + (18577348462903296 : R) * h ^ 86 * a6 * a5 * a0 * b8
    + (5805421394657280 : R) * h ^ 86 * a6 * a4 ^ 2 * b5


end Depression810FifteenthClearing
end Max11DegreeRoutes
end
/-! Part 15 of 40 of `Fable810ScaleZeroFourteenthDefectScratch`, split so that no single module elaborates them all
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


def localClearedFifteenthDefectBlock12_810
    {R : Type*} [CommRing R]
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (13933011347177472 : R) * h ^ 86 * a6 * a4 * a3 * b6
    + (16255179905040384 : R) * h ^ 86 * a6 * a4 * a2 * b7
    + (18577348462903296 : R) * h ^ 86 * a6 * a4 * a1 * b8
    + (8127589952520192 : R) * h ^ 86 * a6 * a3 ^ 2 * b7
    + (18577348462903296 : R) * h ^ 86 * a6 * a3 * a2 * b8
    + (1548112371908608 : R) * h ^ 86 * a5 ^ 3 * b4
    + (5805421394657280 : R) * h ^ 86 * a5 ^ 2 * a4 * b5
    + (6966505673588736 : R) * h ^ 86 * a5 ^ 2 * a3 * b6
    + (8127589952520192 : R) * h ^ 86 * a5 ^ 2 * a2 * b7
    + (9288674231451648 : R) * h ^ 86 * a5 ^ 2 * a1 * b8
    + (6966505673588736 : R) * h ^ 86 * a5 * a4 ^ 2 * b6
    + (16255179905040384 : R) * h ^ 86 * a5 * a4 * a3 * b7
    + (18577348462903296 : R) * h ^ 86 * a5 * a4 * a2 * b8
    + (9288674231451648 : R) * h ^ 86 * a5 * a3 ^ 2 * b8
    + (2709196650840064 : R) * h ^ 86 * a4 ^ 3 * b7
    + (9288674231451648 : R) * h ^ 86 * a4 ^ 2 * a3 * b8
    + (6204544115539968 : R) * h ^ 87 * a7 ^ 2 * a4 * a0 * lambda
    + (6204544115539968 : R) * h ^ 87 * a7 ^ 2 * a3 * a1 * lambda
    + (3102272057769984 : R) * h ^ 87 * a7 ^ 2 * a2 ^ 2 * lambda
    + (12409088231079936 : R) * h ^ 87 * a7 * a6 * a5 * a0 * lambda
    + (12409088231079936 : R) * h ^ 87 * a7 * a6 * a4 * a1 * lambda
    + (12409088231079936 : R) * h ^ 87 * a7 * a6 * a3 * a2 * lambda
    + (6204544115539968 : R) * h ^ 87 * a7 * a5 ^ 2 * a1 * lambda
    + (12409088231079936 : R) * h ^ 87 * a7 * a5 * a4 * a2 * lambda
    + (6204544115539968 : R) * h ^ 87 * a7 * a5 * a3 ^ 2 * lambda
    + (6204544115539968 : R) * h ^ 87 * a7 * a4 ^ 2 * a3 * lambda
    + (2068181371846656 : R) * h ^ 87 * a6 ^ 3 * a0 * lambda
    + (6204544115539968 : R) * h ^ 87 * a6 ^ 2 * a5 * a1 * lambda
    + (6204544115539968 : R) * h ^ 87 * a6 ^ 2 * a4 * a2 * lambda
    + (3102272057769984 : R) * h ^ 87 * a6 ^ 2 * a3 ^ 2 * lambda
    + (6204544115539968 : R) * h ^ 87 * a6 * a5 ^ 2 * a2 * lambda
    + (12409088231079936 : R) * h ^ 87 * a6 * a5 * a4 * a3 * lambda
    + (2068181371846656 : R) * h ^ 87 * a6 * a4 ^ 3 * lambda
    + (2068181371846656 : R) * h ^ 87 * a5 ^ 3 * a3 * lambda
    + (3102272057769984 : R) * h ^ 87 * a5 ^ 2 * a4 ^ 2 * lambda
    - (1451355348664320 : R) * h ^ 88 * a7 ^ 2 * a3 * a0
    - (1451355348664320 : R) * h ^ 88 * a7 ^ 2 * a2 * a1
    - (29027106973286400 : R) * h ^ 88 * a7 * a6 * a4 * a0
    - (29027106973286400 : R) * h ^ 88 * a7 * a6 * a3 * a1
    - (14513553486643200 : R) * h ^ 88 * a7 * a6 * a2 ^ 2


end Depression810FifteenthClearing
end Max11DegreeRoutes
end
/-! Part 16 of 40 of `Fable810ScaleZeroFourteenthDefectScratch`, split so that no single module elaborates them all
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


def localClearedFifteenthDefectBlock13_810
    {R : Type*} [CommRing R]
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (14513553486643200 : R) * h ^ 88 * a7 * a5 ^ 2 * a0
    - (29027106973286400 : R) * h ^ 88 * a7 * a5 * a4 * a1
    - (29027106973286400 : R) * h ^ 88 * a7 * a5 * a3 * a2
    - (14513553486643200 : R) * h ^ 88 * a7 * a4 ^ 2 * a2
    - (14513553486643200 : R) * h ^ 88 * a7 * a4 * a3 ^ 2
    - (27575751624622080 : R) * h ^ 88 * a6 ^ 2 * a5 * a0
    - (27575751624622080 : R) * h ^ 88 * a6 ^ 2 * a4 * a1
    - (27575751624622080 : R) * h ^ 88 * a6 ^ 2 * a3 * a2
    - (27575751624622080 : R) * h ^ 88 * a6 * a5 ^ 2 * a1
    - (55151503249244160 : R) * h ^ 88 * a6 * a5 * a4 * a2
    - (27575751624622080 : R) * h ^ 88 * a6 * a5 * a3 ^ 2
    - (27575751624622080 : R) * h ^ 88 * a6 * a4 ^ 2 * a3
    - (9191917208207360 : R) * h ^ 88 * a5 ^ 3 * a2
    - (27575751624622080 : R) * h ^ 88 * a5 ^ 2 * a4 * a3
    - (9191917208207360 : R) * h ^ 88 * a5 * a4 ^ 3
    - (1688849860263936 : R) * h ^ 94 * a7 * a3 * b1
    - (3377699720527872 : R) * h ^ 94 * a7 * a2 * b2
    - (5066549580791808 : R) * h ^ 94 * a7 * a1 * b3
    - (6755399441055744 : R) * h ^ 94 * a7 * a0 * b4
    - (1688849860263936 : R) * h ^ 94 * a6 * a4 * b1
    - (3377699720527872 : R) * h ^ 94 * a6 * a3 * b2
    - (5066549580791808 : R) * h ^ 94 * a6 * a2 * b3
    - (6755399441055744 : R) * h ^ 94 * a6 * a1 * b4
    - (8444249301319680 : R) * h ^ 94 * a6 * a0 * b5
    - (844424930131968 : R) * h ^ 94 * a5 ^ 2 * b1
    - (3377699720527872 : R) * h ^ 94 * a5 * a4 * b2
    - (5066549580791808 : R) * h ^ 94 * a5 * a3 * b3
    - (6755399441055744 : R) * h ^ 94 * a5 * a2 * b4
    - (8444249301319680 : R) * h ^ 94 * a5 * a1 * b5
    - (10133099161583616 : R) * h ^ 94 * a5 * a0 * b6
    - (2533274790395904 : R) * h ^ 94 * a4 ^ 2 * b3
    - (6755399441055744 : R) * h ^ 94 * a4 * a3 * b4
    - (8444249301319680 : R) * h ^ 94 * a4 * a2 * b5
    - (10133099161583616 : R) * h ^ 94 * a4 * a1 * b6
    - (11821949021847552 : R) * h ^ 94 * a4 * a0 * b7
    - (4222124650659840 : R) * h ^ 94 * a3 ^ 2 * b5
    - (10133099161583616 : R) * h ^ 94 * a3 * a2 * b6
    - (11821949021847552 : R) * h ^ 94 * a3 * a1 * b7
    - (13510798882111488 : R) * h ^ 94 * a3 * a0 * b8
    - (5910974510923776 : R) * h ^ 94 * a2 ^ 2 * b7


end Depression810FifteenthClearing
end Max11DegreeRoutes
end
/-! Part 17 of 40 of `Fable810ScaleZeroFourteenthDefectScratch`, split so that no single module elaborates them all
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


def localClearedFifteenthDefectBlock14_810
    {R : Type*} [CommRing R]
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (13510798882111488 : R) * h ^ 94 * a2 * a1 * b8
    - (5224879255191552 : R) * h ^ 95 * a7 * a3 * a0 * lambda
    - (5224879255191552 : R) * h ^ 95 * a7 * a2 * a1 * lambda
    - (5224879255191552 : R) * h ^ 95 * a6 * a4 * a0 * lambda
    - (5224879255191552 : R) * h ^ 95 * a6 * a3 * a1 * lambda
    - (2612439627595776 : R) * h ^ 95 * a6 * a2 ^ 2 * lambda
    - (2612439627595776 : R) * h ^ 95 * a5 ^ 2 * a0 * lambda
    - (5224879255191552 : R) * h ^ 95 * a5 * a4 * a1 * lambda
    - (5224879255191552 : R) * h ^ 95 * a5 * a3 * a2 * lambda
    - (2612439627595776 : R) * h ^ 95 * a4 ^ 2 * a2 * lambda
    - (2612439627595776 : R) * h ^ 95 * a4 * a3 ^ 2 * lambda
    + (4222124650659840 : R) * h ^ 96 * a7 * a2 * a0
    + (2111062325329920 : R) * h ^ 96 * a7 * a1 ^ 2
    + (23221685578629120 : R) * h ^ 96 * a6 * a3 * a0
    + (23221685578629120 : R) * h ^ 96 * a6 * a2 * a1
    + (23221685578629120 : R) * h ^ 96 * a5 * a4 * a0
    + (23221685578629120 : R) * h ^ 96 * a5 * a3 * a1
    + (11610842789314560 : R) * h ^ 96 * a5 * a2 ^ 2
    + (11610842789314560 : R) * h ^ 96 * a4 ^ 2 * a1
    + (23221685578629120 : R) * h ^ 96 * a4 * a3 * a2
    + (3870280929771520 : R) * h ^ 96 * a3 ^ 3
    + (4503599627370496 : R) * h ^ 102 * a2 * b1
    + (9007199254740992 : R) * h ^ 102 * a1 * b2
    + (13510798882111488 : R) * h ^ 102 * a0 * b3
    + (3799912185593856 : R) * h ^ 103 * a2 * a0 * lambda
    + (1899956092796928 : R) * h ^ 103 * a1 ^ 2 * lambda
    - (16888498602639360 : R) * h ^ 104 * a1 * a0


end Depression810FifteenthClearing
end Max11DegreeRoutes
end
