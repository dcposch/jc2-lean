import Fable810ScaleZeroTwelfthDefectScratch
import Grok810ScaleTwoFourteenthFaceScratch

/-! # Scale-zero thirteenth defect for the normalized `(8,10)`, `H = 0` leaf

The twelfth-defect packet already makes the discriminator `N` a
ground-field constant and, after a square root of the core, clears the
first twelve octic/decic defects to ground constants times `h¹⁴`, `h²¹`,
`h²⁸`, `h³⁵`, `h⁴²`, `h⁴⁹`, `h⁵⁶`, `h⁶³`, `h⁷⁰`, `h⁷⁷`, `h⁸⁴`, and
`h⁹¹`.  This file consumes the next unused Keller coefficient of the
same monic octic-decic depression: the degree-`3` Jacobian row is
`4 T G' + 3 U F' + 2 V E' + W D'
- F U' - 2 E V' - 3 D W' - 4 C X' = 0`.  Its first integral needs the
degree-`5` and degree-`6` rows a second time, with multipliers
`-(1/16) A` and `-(1/16) B`, and the corresponding fourteenth cleared
polynomial defect of weight ninety-eight is likewise a ground-field
constant.

Both constant faces of `N` are treated honestly: the vanishing face
`λ = 0` and the nonzero constant face use the same ninth-power clearing,
and neither is claimed closed.  The same zero/nonzero split is recorded
for the weight-`98` defect itself.  Root-evaluation from a scale-two
face is unavailable, because a nonzero constant has no finite root.

No total-degree or twice-prime theorem is used.  The packet does not
close the leaf: the next missing input is the degree-`2` residual of
the same monic depression.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000

/-! ## Literal next Keller coefficient -/

/-- The fourteenth row below the leading weighted-Wronskian row for outer
degrees `(8,10)`.  Unused Jacobian coefficients of the twelfth-defect
packet start at degree `3`. -/
theorem fableScaleZero_fourteenthCoefficientJacobianRow_raw_810 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 3).derivative * q.coeff 1 +
        (p.coeff 2).derivative * (q.coeff 2 * Polynomial.C (2 : K)) +
        (p.coeff 1).derivative * (q.coeff 3 * Polynomial.C (3 : K)) +
        (p.coeff 0).derivative * (q.coeff 4 * Polynomial.C (4 : K)) -
      ((p.coeff 4 * Polynomial.C (4 : K)) * (q.coeff 0).derivative +
        (p.coeff 3 * Polynomial.C (3 : K)) * (q.coeff 1).derivative +
        (p.coeff 2 * Polynomial.C (2 : K)) * (q.coeff 2).derivative +
        p.coeff 1 * (q.coeff 3).derivative) =
      0 := by
  exact fourteenthCoefficientJacobianRow_810 hp hq hjac

section Depression810FourteenthClearing

variable {F : Type*} [Field F] [CharZero F]

set_option maxHeartbeats 16000000 in
/-- First residual of the degree-`3` row.  Its exactness certificate
uses the degree-`5` and degree-`6` rows again, with the multipliers
`-(1/16) A` and `-(1/16) B`. -/
def xiResidual810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : F) : F :=
  (1 / 8 : F) * thetaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 W0 * D0
    - (1 / 16 : F) * thetaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 W0 * A * B
    + (1 / 4 : F) * etaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 V0 * E0
    - (1 / 8 : F) * etaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 V0 * A * C0
    - (1 / 16 : F) * etaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 V0 * B ^ 2
    + (1 / 32 : F) * etaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 V0 * A ^ 3
    + (3 / 8 : F) * zetaResidual810 L A B C0 D0 E0 F0 P Q R S0 U0 * F0
    - (9 / 64 : F) * zetaResidual810 L A B C0 D0 E0 F0 P Q R S0 U0 * A * D0
    - (3 / 16 : F) * zetaResidual810 L A B C0 D0 E0 F0 P Q R S0 U0 * B * C0
    + (15 / 128 : F) * zetaResidual810 L A B C0 D0 E0 F0 P Q R S0 U0 * A ^ 2 * B
    + (1 / 2 : F) * epsilonResidual810 L A B C0 D0 E0 P Q R T0 * G0
    - (1 / 8 : F) * epsilonResidual810 L A B C0 D0 E0 P Q R T0 * A * E0
    - (3 / 16 : F) * epsilonResidual810 L A B C0 D0 E0 P Q R T0 * B * D0
    - (1 / 8 : F) * epsilonResidual810 L A B C0 D0 E0 P Q R T0 * C0 ^ 2
    + (1 / 8 : F) * epsilonResidual810 L A B C0 D0 E0 P Q R T0 * A ^ 2 * C0
    + (1 / 8 : F) * epsilonResidual810 L A B C0 D0 E0 P Q R T0 * A * B ^ 2
    - (3 / 128 : F) * epsilonResidual810 L A B C0 D0 E0 P Q R T0 * A ^ 4
    - (5 / 64 : F) * deltaResidual810 L A B C0 D0 P Q S0 * A * F0
    - (5 / 32 : F) * deltaResidual810 L A B C0 D0 P Q S0 * B * E0
    - (15 / 64 : F) * deltaResidual810 L A B C0 D0 P Q S0 * C0 * D0
    + (105 / 1024 : F) * deltaResidual810 L A B C0 D0 P Q S0 * A ^ 2 * D0
    + (15 / 64 : F) * deltaResidual810 L A B C0 D0 P Q S0 * A * B * C0
    + (5 / 128 : F) * deltaResidual810 L A B C0 D0 P Q S0 * B ^ 3
    - (165 / 2048 : F) * deltaResidual810 L A B C0 D0 P Q S0 * A ^ 3 * B
    - (3 / 32 : F) * gammaResidual810 L A B C0 P R * B * F0
    - (3 / 16 : F) * gammaResidual810 L A B C0 P R * C0 * E0
    + (9 / 128 : F) * gammaResidual810 L A B C0 P R * A ^ 2 * E0
    - (3 / 32 : F) * gammaResidual810 L A B C0 P R * D0 ^ 2
    + (21 / 128 : F) * gammaResidual810 L A B C0 P R * A * B * D0
    + (3 / 32 : F) * gammaResidual810 L A B C0 P R * A * C0 ^ 2
    + (3 / 32 : F) * gammaResidual810 L A B C0 P R * B ^ 2 * C0
    - (15 / 256 : F) * gammaResidual810 L A B C0 P R * A ^ 3 * C0
    - (45 / 512 : F) * gammaResidual810 L A B C0 P R * A ^ 2 * B ^ 2
    + (9 / 1024 : F) * gammaResidual810 L A B C0 P R * A ^ 5
    - (7 / 64 : F) * betaResidual810 L A B Q * C0 * F0
    + (35 / 1024 : F) * betaResidual810 L A B Q * A ^ 2 * F0
    - (7 / 64 : F) * betaResidual810 L A B Q * D0 * E0
    + (21 / 256 : F) * betaResidual810 L A B Q * A * B * E0
    + (49 / 512 : F) * betaResidual810 L A B Q * A * C0 * D0
    + (49 / 1024 : F) * betaResidual810 L A B Q * B ^ 2 * D0
    - (231 / 8192 : F) * betaResidual810 L A B Q * A ^ 3 * D0
    + (7 / 128 : F) * betaResidual810 L A B Q * B * C0 ^ 2
    - (189 / 2048 : F) * betaResidual810 L A B Q * A ^ 2 * B * C0
    - (63 / 2048 : F) * betaResidual810 L A B Q * A * B ^ 3
    + (357 / 16384 : F) * betaResidual810 L A B Q * A ^ 4 * B
    + (7245 / 524288 : F) * L * A ^ 5 * B
    - (4725 / 262144 : F) * L * A ^ 4 * D0
    - (315 / 4096 : F) * L * A ^ 3 * B * C0
    + (189 / 8192 : F) * L * A ^ 3 * F0
    - (315 / 8192 : F) * L * A ^ 2 * B ^ 3
    + (315 / 4096 : F) * L * A ^ 2 * B * E0
    + (693 / 8192 : F) * L * A ^ 2 * C0 * D0
    + (693 / 8192 : F) * L * A * B ^ 2 * D0
    + (189 / 2048 : F) * L * A * B * C0 ^ 2
    - (9 / 128 : F) * L * A * B * G0
    - (45 / 512 : F) * L * A * C0 * F0
    - (45 / 512 : F) * L * A * D0 * E0
    + (63 / 2048 : F) * L * B ^ 3 * C0
    - (45 / 1024 : F) * L * B ^ 2 * F0
    - (27 / 256 : F) * L * B * C0 * E0
    - (27 / 512 : F) * L * B * D0 ^ 2
    - (63 / 1024 : F) * L * C0 ^ 2 * D0
    + (9 / 64 : F) * L * D0 * G0
    + (9 / 64 : F) * L * E0 * F0
    - (165 / 65536 : F) * A ^ 7
    + (385 / 16384 : F) * A ^ 5 * C0
    + (1925 / 32768 : F) * A ^ 4 * B ^ 2
    - (245 / 8192 : F) * A ^ 4 * E0
    - (525 / 4096 : F) * A ^ 3 * B * D0
    - (35 / 512 : F) * A ^ 3 * C0 ^ 2
    + (5 / 128 : F) * A ^ 3 * G0
    - (105 / 512 : F) * A ^ 2 * B ^ 2 * C0
    + (135 / 1024 : F) * A ^ 2 * B * F0
    + (75 / 512 : F) * A ^ 2 * C0 * E0
    + (75 / 1024 : F) * A ^ 2 * D0 ^ 2
    - (35 / 1024 : F) * A * B ^ 4
    + (75 / 512 : F) * A * B ^ 2 * E0
    + (165 / 512 : F) * A * B * C0 * D0
    + (15 / 256 : F) * A * C0 ^ 3
    - (5 / 32 : F) * A * C0 * G0
    - (5 / 32 : F) * A * D0 * F0
    - (5 / 64 : F) * A * E0 ^ 2
    + (55 / 1024 : F) * B ^ 3 * D0
    + (45 / 512 : F) * B ^ 2 * C0 ^ 2
    - (5 / 64 : F) * B ^ 2 * G0
    - (25 / 128 : F) * B * C0 * F0
    - (25 / 128 : F) * B * D0 * E0
    - (15 / 128 : F) * C0 ^ 2 * E0
    - (15 / 128 : F) * C0 * D0 ^ 2
    + (5 / 16 : F) * E0 * G0
    + (5 / 32 : F) * F0 ^ 2

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

def localClearedFourteenthDefectBlock1_810
    {R : Type*} [CommRing R]
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (12897786789888 : R) * h ^ 38 * a7 ^ 6 * a6 * a4 * b8
    - (6448893394944 : R) * h ^ 38 * a7 ^ 6 * a5 ^ 2 * b8
    - (11285563441152 : R) * h ^ 38 * a7 ^ 5 * a6 ^ 3 * b7
    - (38693360369664 : R) * h ^ 38 * a7 ^ 5 * a6 ^ 2 * a5 * b8
    - (16122233487360 : R) * h ^ 38 * a7 ^ 4 * a6 ^ 4 * b8
    - (485826232320 : R) * h ^ 39 * a7 ^ 8 * a3 * lambda
    - (3886609858560 : R) * h ^ 39 * a7 ^ 7 * a6 * a4 * lambda
    - (1943304929280 : R) * h ^ 39 * a7 ^ 7 * a5 ^ 2 * lambda
    - (13603134504960 : R) * h ^ 39 * a7 ^ 6 * a6 ^ 2 * a5 * lambda
    - (6801567252480 : R) * h ^ 39 * a7 ^ 5 * a6 ^ 4 * lambda
    - (431845539840 : R) * h ^ 40 * a7 ^ 8 * a2
    - (863691079680 : R) * h ^ 40 * a7 ^ 7 * a6 * a3
    - (863691079680 : R) * h ^ 40 * a7 ^ 7 * a5 * a4
    + (6045837557760 : R) * h ^ 40 * a7 ^ 6 * a6 ^ 2 * a4
    + (6045837557760 : R) * h ^ 40 * a7 ^ 6 * a6 * a5 ^ 2
    + (30229187788800 : R) * h ^ 40 * a7 ^ 5 * a6 ^ 3 * a5
    + (12091675115520 : R) * h ^ 40 * a7 ^ 4 * a6 ^ 5
    + (106300440576 : R) * h ^ 46 * a7 ^ 7 * b3
    + (992137445376 : R) * h ^ 46 * a7 ^ 6 * a6 * b4
    + (1240171806720 : R) * h ^ 46 * a7 ^ 6 * a5 * b5
    + (1488206168064 : R) * h ^ 46 * a7 ^ 6 * a4 * b6
    + (1736240529408 : R) * h ^ 46 * a7 ^ 6 * a3 * b7
    + (1984274890752 : R) * h ^ 46 * a7 ^ 6 * a2 * b8
    + (3720515420160 : R) * h ^ 46 * a7 ^ 5 * a6 ^ 2 * b5
    + (8929237008384 : R) * h ^ 46 * a7 ^ 5 * a6 * a5 * b6
    + (10417443176448 : R) * h ^ 46 * a7 ^ 5 * a6 * a4 * b7
    + (11905649344512 : R) * h ^ 46 * a7 ^ 5 * a6 * a3 * b8
    + (5208721588224 : R) * h ^ 46 * a7 ^ 5 * a5 ^ 2 * b7
    + (11905649344512 : R) * h ^ 46 * a7 ^ 5 * a5 * a4 * b8
    + (7441030840320 : R) * h ^ 46 * a7 ^ 4 * a6 ^ 3 * b6
    + (26043607941120 : R) * h ^ 46 * a7 ^ 4 * a6 ^ 2 * a5 * b7
    + (29764123361280 : R) * h ^ 46 * a7 ^ 4 * a6 ^ 2 * a4 * b8
    + (29764123361280 : R) * h ^ 46 * a7 ^ 4 * a6 * a5 ^ 2 * b8
    + (8681202647040 : R) * h ^ 46 * a7 ^ 3 * a6 ^ 4 * b7
    + (39685497815040 : R) * h ^ 46 * a7 ^ 3 * a6 ^ 3 * a5 * b8
    + (5952824672256 : R) * h ^ 46 * a7 ^ 2 * a6 ^ 5 * b8
    + (518214647808 : R) * h ^ 47 * a7 ^ 7 * a2 * lambda
    + (3627502534656 : R) * h ^ 47 * a7 ^ 6 * a6 * a3 * lambda
    + (3627502534656 : R) * h ^ 47 * a7 ^ 6 * a5 * a4 * lambda
    + (10882507603968 : R) * h ^ 47 * a7 ^ 5 * a6 ^ 2 * a4 * lambda

def localClearedFourteenthDefectBlock2_810
    {R : Type*} [CommRing R]
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (10882507603968 : R) * h ^ 47 * a7 ^ 5 * a6 * a5 ^ 2 * lambda
    + (18137512673280 : R) * h ^ 47 * a7 ^ 4 * a6 ^ 3 * a5 * lambda
    + (3627502534656 : R) * h ^ 47 * a7 ^ 3 * a6 ^ 5 * lambda
    + (487210352640 : R) * h ^ 48 * a7 ^ 7 * a1
    + (620085903360 : R) * h ^ 48 * a7 ^ 6 * a6 * a2
    + (620085903360 : R) * h ^ 48 * a7 ^ 6 * a5 * a3
    + (310042951680 : R) * h ^ 48 * a7 ^ 6 * a4 ^ 2
    - (6510901985280 : R) * h ^ 48 * a7 ^ 5 * a6 ^ 2 * a3
    - (13021803970560 : R) * h ^ 48 * a7 ^ 5 * a6 * a5 * a4
    - (2170300661760 : R) * h ^ 48 * a7 ^ 5 * a5 ^ 3
    - (24803436134400 : R) * h ^ 48 * a7 ^ 4 * a6 ^ 3 * a4
    - (37205154201600 : R) * h ^ 48 * a7 ^ 4 * a6 ^ 2 * a5 ^ 2
    - (38755368960000 : R) * h ^ 48 * a7 ^ 3 * a6 ^ 4 * a5
    - (5270730178560 : R) * h ^ 48 * a7 ^ 2 * a6 ^ 6
    - (90194313216 : R) * h ^ 54 * a7 ^ 6 * b2
    - (811748818944 : R) * h ^ 54 * a7 ^ 5 * a6 * b3
    - (1082331758592 : R) * h ^ 54 * a7 ^ 5 * a5 * b4
    - (1352914698240 : R) * h ^ 54 * a7 ^ 5 * a4 * b5
    - (1623497637888 : R) * h ^ 54 * a7 ^ 5 * a3 * b6
    - (1894080577536 : R) * h ^ 54 * a7 ^ 5 * a2 * b7
    - (2164663517184 : R) * h ^ 54 * a7 ^ 5 * a1 * b8
    - (2705829396480 : R) * h ^ 54 * a7 ^ 4 * a6 ^ 2 * b4
    - (6764573491200 : R) * h ^ 54 * a7 ^ 4 * a6 * a5 * b5
    - (8117488189440 : R) * h ^ 54 * a7 ^ 4 * a6 * a4 * b6
    - (9470402887680 : R) * h ^ 54 * a7 ^ 4 * a6 * a3 * b7
    - (10823317585920 : R) * h ^ 54 * a7 ^ 4 * a6 * a2 * b8
    - (4058744094720 : R) * h ^ 54 * a7 ^ 4 * a5 ^ 2 * b6
    - (9470402887680 : R) * h ^ 54 * a7 ^ 4 * a5 * a4 * b7
    - (10823317585920 : R) * h ^ 54 * a7 ^ 4 * a5 * a3 * b8
    - (5411658792960 : R) * h ^ 54 * a7 ^ 4 * a4 ^ 2 * b8
    - (4509715660800 : R) * h ^ 54 * a7 ^ 3 * a6 ^ 3 * b5
    - (16234976378880 : R) * h ^ 54 * a7 ^ 3 * a6 ^ 2 * a5 * b6
    - (18940805775360 : R) * h ^ 54 * a7 ^ 3 * a6 ^ 2 * a4 * b7
    - (21646635171840 : R) * h ^ 54 * a7 ^ 3 * a6 ^ 2 * a3 * b8
    - (18940805775360 : R) * h ^ 54 * a7 ^ 3 * a6 * a5 ^ 2 * b7
    - (43293270343680 : R) * h ^ 54 * a7 ^ 3 * a6 * a5 * a4 * b8
    - (7215545057280 : R) * h ^ 54 * a7 ^ 3 * a5 ^ 3 * b8
    - (4058744094720 : R) * h ^ 54 * a7 ^ 2 * a6 ^ 4 * b6
    - (18940805775360 : R) * h ^ 54 * a7 ^ 2 * a6 ^ 3 * a5 * b7
    - (21646635171840 : R) * h ^ 54 * a7 ^ 2 * a6 ^ 3 * a4 * b8

def localClearedFourteenthDefectBlock3_810
    {R : Type*} [CommRing R]
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (32469952757760 : R) * h ^ 54 * a7 ^ 2 * a6 ^ 2 * a5 ^ 2 * b8
    - (1894080577536 : R) * h ^ 54 * a7 * a6 ^ 5 * b7
    - (10823317585920 : R) * h ^ 54 * a7 * a6 ^ 4 * a5 * b8
    - (360777252864 : R) * h ^ 54 * a6 ^ 6 * b8
    - (558077313024 : R) * h ^ 55 * a7 ^ 6 * a1 * lambda
    - (3348463878144 : R) * h ^ 55 * a7 ^ 5 * a6 * a2 * lambda
    - (3348463878144 : R) * h ^ 55 * a7 ^ 5 * a5 * a3 * lambda
    - (1674231939072 : R) * h ^ 55 * a7 ^ 5 * a4 ^ 2 * lambda
    - (8371159695360 : R) * h ^ 55 * a7 ^ 4 * a6 ^ 2 * a3 * lambda
    - (16742319390720 : R) * h ^ 55 * a7 ^ 4 * a6 * a5 * a4 * lambda
    - (2790386565120 : R) * h ^ 55 * a7 ^ 4 * a5 ^ 3 * lambda
    - (11161546260480 : R) * h ^ 55 * a7 ^ 3 * a6 ^ 3 * a4 * lambda
    - (16742319390720 : R) * h ^ 55 * a7 ^ 3 * a6 ^ 2 * a5 ^ 2 * lambda
    - (8371159695360 : R) * h ^ 55 * a7 ^ 2 * a6 ^ 4 * a5 * lambda
    - (558077313024 : R) * h ^ 55 * a7 * a6 ^ 6 * lambda
    - (563714457600 : R) * h ^ 56 * a7 ^ 6 * a0
    - (338228674560 : R) * h ^ 56 * a7 ^ 5 * a6 * a1
    - (338228674560 : R) * h ^ 56 * a7 ^ 5 * a5 * a2
    - (338228674560 : R) * h ^ 56 * a7 ^ 5 * a4 * a3
    + (6764573491200 : R) * h ^ 56 * a7 ^ 4 * a6 ^ 2 * a2
    + (13529146982400 : R) * h ^ 56 * a7 ^ 4 * a6 * a5 * a3
    + (6764573491200 : R) * h ^ 56 * a7 ^ 4 * a6 * a4 ^ 2
    + (6764573491200 : R) * h ^ 56 * a7 ^ 4 * a5 ^ 2 * a4
    + (19166291558400 : R) * h ^ 56 * a7 ^ 3 * a6 ^ 3 * a3
    + (57498874675200 : R) * h ^ 56 * a7 ^ 3 * a6 ^ 2 * a5 * a4
    + (19166291558400 : R) * h ^ 56 * a7 ^ 3 * a6 * a5 ^ 3
    + (21984863846400 : R) * h ^ 56 * a7 ^ 2 * a6 ^ 4 * a4
    + (43969727692800 : R) * h ^ 56 * a7 ^ 2 * a6 ^ 3 * a5 ^ 2
    + (11838003609600 : R) * h ^ 56 * a7 * a6 ^ 5 * a5
    + (354334801920 : R) * h ^ 56 * a6 ^ 7
    + (60129542144 : R) * h ^ 62 * a7 ^ 5 * b1
    + (601295421440 : R) * h ^ 62 * a7 ^ 4 * a6 * b2
    + (901943132160 : R) * h ^ 62 * a7 ^ 4 * a5 * b3
    + (1202590842880 : R) * h ^ 62 * a7 ^ 4 * a4 * b4
    + (1503238553600 : R) * h ^ 62 * a7 ^ 4 * a3 * b5
    + (1803886264320 : R) * h ^ 62 * a7 ^ 4 * a2 * b6
    + (2104533975040 : R) * h ^ 62 * a7 ^ 4 * a1 * b7
    + (2405181685760 : R) * h ^ 62 * a7 ^ 4 * a0 * b8
    + (1803886264320 : R) * h ^ 62 * a7 ^ 3 * a6 ^ 2 * b3
    + (4810363371520 : R) * h ^ 62 * a7 ^ 3 * a6 * a5 * b4

def localClearedFourteenthDefectBlock4_810
    {R : Type*} [CommRing R]
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (6012954214400 : R) * h ^ 62 * a7 ^ 3 * a6 * a4 * b5
    + (7215545057280 : R) * h ^ 62 * a7 ^ 3 * a6 * a3 * b6
    + (8418135900160 : R) * h ^ 62 * a7 ^ 3 * a6 * a2 * b7
    + (9620726743040 : R) * h ^ 62 * a7 ^ 3 * a6 * a1 * b8
    + (3006477107200 : R) * h ^ 62 * a7 ^ 3 * a5 ^ 2 * b5
    + (7215545057280 : R) * h ^ 62 * a7 ^ 3 * a5 * a4 * b6
    + (8418135900160 : R) * h ^ 62 * a7 ^ 3 * a5 * a3 * b7
    + (9620726743040 : R) * h ^ 62 * a7 ^ 3 * a5 * a2 * b8
    + (4209067950080 : R) * h ^ 62 * a7 ^ 3 * a4 ^ 2 * b7
    + (9620726743040 : R) * h ^ 62 * a7 ^ 3 * a4 * a3 * b8
    + (2405181685760 : R) * h ^ 62 * a7 ^ 2 * a6 ^ 3 * b4
    + (9019431321600 : R) * h ^ 62 * a7 ^ 2 * a6 ^ 2 * a5 * b5
    + (10823317585920 : R) * h ^ 62 * a7 ^ 2 * a6 ^ 2 * a4 * b6
    + (12627203850240 : R) * h ^ 62 * a7 ^ 2 * a6 ^ 2 * a3 * b7
    + (14431090114560 : R) * h ^ 62 * a7 ^ 2 * a6 ^ 2 * a2 * b8
    + (10823317585920 : R) * h ^ 62 * a7 ^ 2 * a6 * a5 ^ 2 * b6
    + (25254407700480 : R) * h ^ 62 * a7 ^ 2 * a6 * a5 * a4 * b7
    + (28862180229120 : R) * h ^ 62 * a7 ^ 2 * a6 * a5 * a3 * b8
    + (14431090114560 : R) * h ^ 62 * a7 ^ 2 * a6 * a4 ^ 2 * b8
    + (4209067950080 : R) * h ^ 62 * a7 ^ 2 * a5 ^ 3 * b7
    + (14431090114560 : R) * h ^ 62 * a7 ^ 2 * a5 ^ 2 * a4 * b8
    + (1503238553600 : R) * h ^ 62 * a7 * a6 ^ 4 * b5
    + (7215545057280 : R) * h ^ 62 * a7 * a6 ^ 3 * a5 * b6
    + (8418135900160 : R) * h ^ 62 * a7 * a6 ^ 3 * a4 * b7
    + (9620726743040 : R) * h ^ 62 * a7 * a6 ^ 3 * a3 * b8
    + (12627203850240 : R) * h ^ 62 * a7 * a6 ^ 2 * a5 ^ 2 * b7
    + (28862180229120 : R) * h ^ 62 * a7 * a6 ^ 2 * a5 * a4 * b8
    + (9620726743040 : R) * h ^ 62 * a7 * a6 * a5 ^ 3 * b8
    + (360777252864 : R) * h ^ 62 * a6 ^ 5 * b6
    + (2104533975040 : R) * h ^ 62 * a6 ^ 4 * a5 * b7
    + (2405181685760 : R) * h ^ 62 * a6 ^ 4 * a4 * b8
    + (4810363371520 : R) * h ^ 62 * a6 ^ 3 * a5 ^ 2 * b8
    + (608811614208 : R) * h ^ 63 * a7 ^ 5 * a0 * lambda
    + (3044058071040 : R) * h ^ 63 * a7 ^ 4 * a6 * a1 * lambda
    + (3044058071040 : R) * h ^ 63 * a7 ^ 4 * a5 * a2 * lambda
    + (3044058071040 : R) * h ^ 63 * a7 ^ 4 * a4 * a3 * lambda
    + (6088116142080 : R) * h ^ 63 * a7 ^ 3 * a6 ^ 2 * a2 * lambda
    + (12176232284160 : R) * h ^ 63 * a7 ^ 3 * a6 * a5 * a3 * lambda
    + (6088116142080 : R) * h ^ 63 * a7 ^ 3 * a6 * a4 ^ 2 * lambda
    + (6088116142080 : R) * h ^ 63 * a7 ^ 3 * a5 ^ 2 * a4 * lambda

def localClearedFourteenthDefectBlock5_810
    {R : Type*} [CommRing R]
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (6088116142080 : R) * h ^ 63 * a7 ^ 2 * a6 ^ 3 * a3 * lambda
    + (18264348426240 : R) * h ^ 63 * a7 ^ 2 * a6 ^ 2 * a5 * a4 * lambda
    + (6088116142080 : R) * h ^ 63 * a7 ^ 2 * a6 * a5 ^ 3 * lambda
    + (3044058071040 : R) * h ^ 63 * a7 * a6 ^ 4 * a4 * lambda
    + (6088116142080 : R) * h ^ 63 * a7 * a6 ^ 3 * a5 ^ 2 * lambda
    + (608811614208 : R) * h ^ 63 * a6 ^ 5 * a5 * lambda
    - (6764573491200 : R) * h ^ 64 * a7 ^ 3 * a6 ^ 2 * a1
    - (13529146982400 : R) * h ^ 64 * a7 ^ 3 * a6 * a5 * a2
    - (13529146982400 : R) * h ^ 64 * a7 ^ 3 * a6 * a4 * a3
    - (6764573491200 : R) * h ^ 64 * a7 ^ 3 * a5 ^ 2 * a3
    - (6764573491200 : R) * h ^ 64 * a7 ^ 3 * a5 * a4 ^ 2
    - (13529146982400 : R) * h ^ 64 * a7 ^ 2 * a6 ^ 3 * a2
    - (40587440947200 : R) * h ^ 64 * a7 ^ 2 * a6 ^ 2 * a5 * a3
    - (20293720473600 : R) * h ^ 64 * a7 ^ 2 * a6 ^ 2 * a4 ^ 2
    - (40587440947200 : R) * h ^ 64 * a7 ^ 2 * a6 * a5 ^ 2 * a4
    - (3382286745600 : R) * h ^ 64 * a7 ^ 2 * a5 ^ 4
    - (10146860236800 : R) * h ^ 64 * a7 * a6 ^ 4 * a3
    - (40587440947200 : R) * h ^ 64 * a7 * a6 ^ 3 * a5 * a4
    - (20293720473600 : R) * h ^ 64 * a7 * a6 ^ 2 * a5 ^ 3
    - (2705829396480 : R) * h ^ 64 * a6 ^ 5 * a4
    - (6764573491200 : R) * h ^ 64 * a6 ^ 4 * a5 ^ 2
    - (343597383680 : R) * h ^ 70 * a7 ^ 3 * a6 * b1
    - (687194767360 : R) * h ^ 70 * a7 ^ 3 * a5 * b2
    - (1030792151040 : R) * h ^ 70 * a7 ^ 3 * a4 * b3
    - (1374389534720 : R) * h ^ 70 * a7 ^ 3 * a3 * b4
    - (1717986918400 : R) * h ^ 70 * a7 ^ 3 * a2 * b5
    - (2061584302080 : R) * h ^ 70 * a7 ^ 3 * a1 * b6
    - (2405181685760 : R) * h ^ 70 * a7 ^ 3 * a0 * b7
    - (1030792151040 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 2 * b2
    - (3092376453120 : R) * h ^ 70 * a7 ^ 2 * a6 * a5 * b3
    - (4123168604160 : R) * h ^ 70 * a7 ^ 2 * a6 * a4 * b4
    - (5153960755200 : R) * h ^ 70 * a7 ^ 2 * a6 * a3 * b5
    - (6184752906240 : R) * h ^ 70 * a7 ^ 2 * a6 * a2 * b6
    - (7215545057280 : R) * h ^ 70 * a7 ^ 2 * a6 * a1 * b7
    - (8246337208320 : R) * h ^ 70 * a7 ^ 2 * a6 * a0 * b8
    - (2061584302080 : R) * h ^ 70 * a7 ^ 2 * a5 ^ 2 * b4
    - (5153960755200 : R) * h ^ 70 * a7 ^ 2 * a5 * a4 * b5
    - (6184752906240 : R) * h ^ 70 * a7 ^ 2 * a5 * a3 * b6
    - (7215545057280 : R) * h ^ 70 * a7 ^ 2 * a5 * a2 * b7
    - (8246337208320 : R) * h ^ 70 * a7 ^ 2 * a5 * a1 * b8

def localClearedFourteenthDefectBlock6_810
    {R : Type*} [CommRing R]
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (3092376453120 : R) * h ^ 70 * a7 ^ 2 * a4 ^ 2 * b6
    - (7215545057280 : R) * h ^ 70 * a7 ^ 2 * a4 * a3 * b7
    - (8246337208320 : R) * h ^ 70 * a7 ^ 2 * a4 * a2 * b8
    - (4123168604160 : R) * h ^ 70 * a7 ^ 2 * a3 ^ 2 * b8
    - (1030792151040 : R) * h ^ 70 * a7 * a6 ^ 3 * b3
    - (4123168604160 : R) * h ^ 70 * a7 * a6 ^ 2 * a5 * b4
    - (5153960755200 : R) * h ^ 70 * a7 * a6 ^ 2 * a4 * b5
    - (6184752906240 : R) * h ^ 70 * a7 * a6 ^ 2 * a3 * b6
    - (7215545057280 : R) * h ^ 70 * a7 * a6 ^ 2 * a2 * b7
    - (8246337208320 : R) * h ^ 70 * a7 * a6 ^ 2 * a1 * b8
    - (5153960755200 : R) * h ^ 70 * a7 * a6 * a5 ^ 2 * b5
    - (12369505812480 : R) * h ^ 70 * a7 * a6 * a5 * a4 * b6
    - (14431090114560 : R) * h ^ 70 * a7 * a6 * a5 * a3 * b7
    - (16492674416640 : R) * h ^ 70 * a7 * a6 * a5 * a2 * b8
    - (7215545057280 : R) * h ^ 70 * a7 * a6 * a4 ^ 2 * b7
    - (16492674416640 : R) * h ^ 70 * a7 * a6 * a4 * a3 * b8
    - (2061584302080 : R) * h ^ 70 * a7 * a5 ^ 3 * b6
    - (7215545057280 : R) * h ^ 70 * a7 * a5 ^ 2 * a4 * b7
    - (8246337208320 : R) * h ^ 70 * a7 * a5 ^ 2 * a3 * b8
    - (8246337208320 : R) * h ^ 70 * a7 * a5 * a4 ^ 2 * b8
    - (343597383680 : R) * h ^ 70 * a6 ^ 4 * b4
    - (1717986918400 : R) * h ^ 70 * a6 ^ 3 * a5 * b5
    - (2061584302080 : R) * h ^ 70 * a6 ^ 3 * a4 * b6
    - (2405181685760 : R) * h ^ 70 * a6 ^ 3 * a3 * b7
    - (2748779069440 : R) * h ^ 70 * a6 ^ 3 * a2 * b8
    - (3092376453120 : R) * h ^ 70 * a6 ^ 2 * a5 ^ 2 * b6
    - (7215545057280 : R) * h ^ 70 * a6 ^ 2 * a5 * a4 * b7
    - (8246337208320 : R) * h ^ 70 * a6 ^ 2 * a5 * a3 * b8
    - (4123168604160 : R) * h ^ 70 * a6 ^ 2 * a4 ^ 2 * b8
    - (2405181685760 : R) * h ^ 70 * a6 * a5 ^ 3 * b7
    - (8246337208320 : R) * h ^ 70 * a6 * a5 ^ 2 * a4 * b8
    - (687194767360 : R) * h ^ 70 * a5 ^ 4 * b8
    - (2705829396480 : R) * h ^ 71 * a7 ^ 3 * a6 * a0 * lambda
    - (2705829396480 : R) * h ^ 71 * a7 ^ 3 * a5 * a1 * lambda
    - (2705829396480 : R) * h ^ 71 * a7 ^ 3 * a4 * a2 * lambda
    - (1352914698240 : R) * h ^ 71 * a7 ^ 3 * a3 ^ 2 * lambda
    - (4058744094720 : R) * h ^ 71 * a7 ^ 2 * a6 ^ 2 * a1 * lambda
    - (8117488189440 : R) * h ^ 71 * a7 ^ 2 * a6 * a5 * a2 * lambda
    - (8117488189440 : R) * h ^ 71 * a7 ^ 2 * a6 * a4 * a3 * lambda
    - (4058744094720 : R) * h ^ 71 * a7 ^ 2 * a5 ^ 2 * a3 * lambda

def localClearedFourteenthDefectBlock7_810
    {R : Type*} [CommRing R]
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (4058744094720 : R) * h ^ 71 * a7 ^ 2 * a5 * a4 ^ 2 * lambda
    - (2705829396480 : R) * h ^ 71 * a7 * a6 ^ 3 * a2 * lambda
    - (8117488189440 : R) * h ^ 71 * a7 * a6 ^ 2 * a5 * a3 * lambda
    - (4058744094720 : R) * h ^ 71 * a7 * a6 ^ 2 * a4 ^ 2 * lambda
    - (8117488189440 : R) * h ^ 71 * a7 * a6 * a5 ^ 2 * a4 * lambda
    - (676457349120 : R) * h ^ 71 * a7 * a5 ^ 4 * lambda
    - (676457349120 : R) * h ^ 71 * a6 ^ 4 * a3 * lambda
    - (2705829396480 : R) * h ^ 71 * a6 ^ 3 * a5 * a4 * lambda
    - (1352914698240 : R) * h ^ 71 * a6 ^ 2 * a5 ^ 3 * lambda
    + (429496729600 : R) * h ^ 72 * a7 ^ 3 * a5 * a0
    + (429496729600 : R) * h ^ 72 * a7 ^ 3 * a4 * a1
    + (429496729600 : R) * h ^ 72 * a7 ^ 3 * a3 * a2
    + (6442450944000 : R) * h ^ 72 * a7 ^ 2 * a6 ^ 2 * a0
    + (12884901888000 : R) * h ^ 72 * a7 ^ 2 * a6 * a5 * a1
    + (12884901888000 : R) * h ^ 72 * a7 ^ 2 * a6 * a4 * a2
    + (6442450944000 : R) * h ^ 72 * a7 ^ 2 * a6 * a3 ^ 2
    + (6442450944000 : R) * h ^ 72 * a7 ^ 2 * a5 ^ 2 * a2
    + (12884901888000 : R) * h ^ 72 * a7 ^ 2 * a5 * a4 * a3
    + (2147483648000 : R) * h ^ 72 * a7 ^ 2 * a4 ^ 3
    + (8160437862400 : R) * h ^ 72 * a7 * a6 ^ 3 * a1
    + (24481313587200 : R) * h ^ 72 * a7 * a6 ^ 2 * a5 * a2
    + (24481313587200 : R) * h ^ 72 * a7 * a6 ^ 2 * a4 * a3
    + (24481313587200 : R) * h ^ 72 * a7 * a6 * a5 ^ 2 * a3
    + (24481313587200 : R) * h ^ 72 * a7 * a6 * a5 * a4 ^ 2
    + (8160437862400 : R) * h ^ 72 * a7 * a5 ^ 3 * a4
    + (3006477107200 : R) * h ^ 72 * a6 ^ 4 * a2
    + (12025908428800 : R) * h ^ 72 * a6 ^ 3 * a5 * a3
    + (6012954214400 : R) * h ^ 72 * a6 ^ 3 * a4 ^ 2
    + (18038862643200 : R) * h ^ 72 * a6 ^ 2 * a5 ^ 2 * a4
    + (3006477107200 : R) * h ^ 72 * a6 * a5 ^ 4
    + (412316860416 : R) * h ^ 78 * a7 ^ 2 * a5 * b1
    + (824633720832 : R) * h ^ 78 * a7 ^ 2 * a4 * b2
    + (1236950581248 : R) * h ^ 78 * a7 ^ 2 * a3 * b3
    + (1649267441664 : R) * h ^ 78 * a7 ^ 2 * a2 * b4
    + (2061584302080 : R) * h ^ 78 * a7 ^ 2 * a1 * b5
    + (2473901162496 : R) * h ^ 78 * a7 ^ 2 * a0 * b6
    + (412316860416 : R) * h ^ 78 * a7 * a6 ^ 2 * b1
    + (1649267441664 : R) * h ^ 78 * a7 * a6 * a5 * b2
    + (2473901162496 : R) * h ^ 78 * a7 * a6 * a4 * b3
    + (3298534883328 : R) * h ^ 78 * a7 * a6 * a3 * b4

def localClearedFourteenthDefectBlock8_810
    {R : Type*} [CommRing R]
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (4123168604160 : R) * h ^ 78 * a7 * a6 * a2 * b5
    + (4947802324992 : R) * h ^ 78 * a7 * a6 * a1 * b6
    + (5772436045824 : R) * h ^ 78 * a7 * a6 * a0 * b7
    + (1236950581248 : R) * h ^ 78 * a7 * a5 ^ 2 * b3
    + (3298534883328 : R) * h ^ 78 * a7 * a5 * a4 * b4
    + (4123168604160 : R) * h ^ 78 * a7 * a5 * a3 * b5
    + (4947802324992 : R) * h ^ 78 * a7 * a5 * a2 * b6
    + (5772436045824 : R) * h ^ 78 * a7 * a5 * a1 * b7
    + (6597069766656 : R) * h ^ 78 * a7 * a5 * a0 * b8
    + (2061584302080 : R) * h ^ 78 * a7 * a4 ^ 2 * b5
    + (4947802324992 : R) * h ^ 78 * a7 * a4 * a3 * b6
    + (5772436045824 : R) * h ^ 78 * a7 * a4 * a2 * b7
    + (6597069766656 : R) * h ^ 78 * a7 * a4 * a1 * b8
    + (2886218022912 : R) * h ^ 78 * a7 * a3 ^ 2 * b7
    + (6597069766656 : R) * h ^ 78 * a7 * a3 * a2 * b8
    + (274877906944 : R) * h ^ 78 * a6 ^ 3 * b2
    + (1236950581248 : R) * h ^ 78 * a6 ^ 2 * a5 * b3
    + (1649267441664 : R) * h ^ 78 * a6 ^ 2 * a4 * b4
    + (2061584302080 : R) * h ^ 78 * a6 ^ 2 * a3 * b5
    + (2473901162496 : R) * h ^ 78 * a6 ^ 2 * a2 * b6
    + (2886218022912 : R) * h ^ 78 * a6 ^ 2 * a1 * b7
    + (3298534883328 : R) * h ^ 78 * a6 ^ 2 * a0 * b8
    + (1649267441664 : R) * h ^ 78 * a6 * a5 ^ 2 * b4
    + (4123168604160 : R) * h ^ 78 * a6 * a5 * a4 * b5
    + (4947802324992 : R) * h ^ 78 * a6 * a5 * a3 * b6
    + (5772436045824 : R) * h ^ 78 * a6 * a5 * a2 * b7
    + (6597069766656 : R) * h ^ 78 * a6 * a5 * a1 * b8
    + (2473901162496 : R) * h ^ 78 * a6 * a4 ^ 2 * b6
    + (5772436045824 : R) * h ^ 78 * a6 * a4 * a3 * b7
    + (6597069766656 : R) * h ^ 78 * a6 * a4 * a2 * b8
    + (3298534883328 : R) * h ^ 78 * a6 * a3 ^ 2 * b8
    + (687194767360 : R) * h ^ 78 * a5 ^ 3 * b5
    + (2473901162496 : R) * h ^ 78 * a5 ^ 2 * a4 * b6
    + (2886218022912 : R) * h ^ 78 * a5 ^ 2 * a3 * b7
    + (3298534883328 : R) * h ^ 78 * a5 ^ 2 * a2 * b8
    + (2886218022912 : R) * h ^ 78 * a5 * a4 ^ 2 * b7
    + (6597069766656 : R) * h ^ 78 * a5 * a4 * a3 * b8
    + (1099511627776 : R) * h ^ 78 * a4 ^ 3 * b8
    + (2319282339840 : R) * h ^ 79 * a7 ^ 2 * a5 * a0 * lambda
    + (2319282339840 : R) * h ^ 79 * a7 ^ 2 * a4 * a1 * lambda

def localClearedFourteenthDefectBlock9_810
    {R : Type*} [CommRing R]
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (2319282339840 : R) * h ^ 79 * a7 ^ 2 * a3 * a2 * lambda
    + (2319282339840 : R) * h ^ 79 * a7 * a6 ^ 2 * a0 * lambda
    + (4638564679680 : R) * h ^ 79 * a7 * a6 * a5 * a1 * lambda
    + (4638564679680 : R) * h ^ 79 * a7 * a6 * a4 * a2 * lambda
    + (2319282339840 : R) * h ^ 79 * a7 * a6 * a3 ^ 2 * lambda
    + (2319282339840 : R) * h ^ 79 * a7 * a5 ^ 2 * a2 * lambda
    + (4638564679680 : R) * h ^ 79 * a7 * a5 * a4 * a3 * lambda
    + (773094113280 : R) * h ^ 79 * a7 * a4 ^ 3 * lambda
    + (773094113280 : R) * h ^ 79 * a6 ^ 3 * a1 * lambda
    + (2319282339840 : R) * h ^ 79 * a6 ^ 2 * a5 * a2 * lambda
    + (2319282339840 : R) * h ^ 79 * a6 ^ 2 * a4 * a3 * lambda
    + (2319282339840 : R) * h ^ 79 * a6 * a5 ^ 2 * a3 * lambda
    + (2319282339840 : R) * h ^ 79 * a6 * a5 * a4 ^ 2 * lambda
    + (773094113280 : R) * h ^ 79 * a5 ^ 3 * a4 * lambda
    - (1030792151040 : R) * h ^ 80 * a7 ^ 2 * a4 * a0
    - (1030792151040 : R) * h ^ 80 * a7 ^ 2 * a3 * a1
    - (515396075520 : R) * h ^ 80 * a7 ^ 2 * a2 ^ 2
    - (11338713661440 : R) * h ^ 80 * a7 * a6 * a5 * a0
    - (11338713661440 : R) * h ^ 80 * a7 * a6 * a4 * a1
    - (11338713661440 : R) * h ^ 80 * a7 * a6 * a3 * a2
    - (5669356830720 : R) * h ^ 80 * a7 * a5 ^ 2 * a1
    - (11338713661440 : R) * h ^ 80 * a7 * a5 * a4 * a2
    - (5669356830720 : R) * h ^ 80 * a7 * a5 * a3 ^ 2
    - (5669356830720 : R) * h ^ 80 * a7 * a4 ^ 2 * a3
    - (3435973836800 : R) * h ^ 80 * a6 ^ 3 * a0
    - (10307921510400 : R) * h ^ 80 * a6 ^ 2 * a5 * a1
    - (10307921510400 : R) * h ^ 80 * a6 ^ 2 * a4 * a2
    - (5153960755200 : R) * h ^ 80 * a6 ^ 2 * a3 ^ 2
    - (10307921510400 : R) * h ^ 80 * a6 * a5 ^ 2 * a2
    - (20615843020800 : R) * h ^ 80 * a6 * a5 * a4 * a3
    - (3435973836800 : R) * h ^ 80 * a6 * a4 ^ 3
    - (3435973836800 : R) * h ^ 80 * a5 ^ 3 * a3
    - (5153960755200 : R) * h ^ 80 * a5 ^ 2 * a4 ^ 2
    - (549755813888 : R) * h ^ 86 * a7 * a4 * b1
    - (1099511627776 : R) * h ^ 86 * a7 * a3 * b2
    - (1649267441664 : R) * h ^ 86 * a7 * a2 * b3
    - (2199023255552 : R) * h ^ 86 * a7 * a1 * b4
    - (2748779069440 : R) * h ^ 86 * a7 * a0 * b5
    - (549755813888 : R) * h ^ 86 * a6 * a5 * b1
    - (1099511627776 : R) * h ^ 86 * a6 * a4 * b2

def localClearedFourteenthDefectBlock10_810
    {R : Type*} [CommRing R]
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (1649267441664 : R) * h ^ 86 * a6 * a3 * b3
    - (2199023255552 : R) * h ^ 86 * a6 * a2 * b4
    - (2748779069440 : R) * h ^ 86 * a6 * a1 * b5
    - (3298534883328 : R) * h ^ 86 * a6 * a0 * b6
    - (549755813888 : R) * h ^ 86 * a5 ^ 2 * b2
    - (1649267441664 : R) * h ^ 86 * a5 * a4 * b3
    - (2199023255552 : R) * h ^ 86 * a5 * a3 * b4
    - (2748779069440 : R) * h ^ 86 * a5 * a2 * b5
    - (3298534883328 : R) * h ^ 86 * a5 * a1 * b6
    - (3848290697216 : R) * h ^ 86 * a5 * a0 * b7
    - (1099511627776 : R) * h ^ 86 * a4 ^ 2 * b4
    - (2748779069440 : R) * h ^ 86 * a4 * a3 * b5
    - (3298534883328 : R) * h ^ 86 * a4 * a2 * b6
    - (3848290697216 : R) * h ^ 86 * a4 * a1 * b7
    - (4398046511104 : R) * h ^ 86 * a4 * a0 * b8
    - (1649267441664 : R) * h ^ 86 * a3 ^ 2 * b6
    - (3848290697216 : R) * h ^ 86 * a3 * a2 * b7
    - (4398046511104 : R) * h ^ 86 * a3 * a1 * b8
    - (2199023255552 : R) * h ^ 86 * a2 ^ 2 * b8
    - (1855425871872 : R) * h ^ 87 * a7 * a4 * a0 * lambda
    - (1855425871872 : R) * h ^ 87 * a7 * a3 * a1 * lambda
    - (927712935936 : R) * h ^ 87 * a7 * a2 ^ 2 * lambda
    - (1855425871872 : R) * h ^ 87 * a6 * a5 * a0 * lambda
    - (1855425871872 : R) * h ^ 87 * a6 * a4 * a1 * lambda
    - (1855425871872 : R) * h ^ 87 * a6 * a3 * a2 * lambda
    - (927712935936 : R) * h ^ 87 * a5 ^ 2 * a1 * lambda
    - (1855425871872 : R) * h ^ 87 * a5 * a4 * a2 * lambda
    - (927712935936 : R) * h ^ 87 * a5 * a3 ^ 2 * lambda
    - (927712935936 : R) * h ^ 87 * a4 ^ 2 * a3 * lambda
    + (2061584302080 : R) * h ^ 88 * a7 * a3 * a0
    + (2061584302080 : R) * h ^ 88 * a7 * a2 * a1
    + (8246337208320 : R) * h ^ 88 * a6 * a4 * a0
    + (8246337208320 : R) * h ^ 88 * a6 * a3 * a1
    + (4123168604160 : R) * h ^ 88 * a6 * a2 ^ 2
    + (4123168604160 : R) * h ^ 88 * a5 ^ 2 * a0
    + (8246337208320 : R) * h ^ 88 * a5 * a4 * a1
    + (8246337208320 : R) * h ^ 88 * a5 * a3 * a2
    + (4123168604160 : R) * h ^ 88 * a4 ^ 2 * a2
    + (4123168604160 : R) * h ^ 88 * a4 * a3 ^ 2
    + (1099511627776 : R) * h ^ 94 * a3 * b1

def localClearedFourteenthDefectBlock11_810
    {R : Type*} [CommRing R]
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (2199023255552 : R) * h ^ 94 * a2 * b2
    + (3298534883328 : R) * h ^ 94 * a1 * b3
    + (4398046511104 : R) * h ^ 94 * a0 * b4
    + (1236950581248 : R) * h ^ 95 * a3 * a0 * lambda
    + (1236950581248 : R) * h ^ 95 * a2 * a1 * lambda
    - (5497558138880 : R) * h ^ 96 * a2 * a0
    - (2748779069440 : R) * h ^ 96 * a1 ^ 2

set_option maxHeartbeats 16000000 in
def localClearedFourteenthDefectCore810
    {R : Type*} [CommRing R]
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    localClearedFourteenthDefectBlock0_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
    + localClearedFourteenthDefectBlock1_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
    + localClearedFourteenthDefectBlock2_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
    + localClearedFourteenthDefectBlock3_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
    + localClearedFourteenthDefectBlock4_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
    + localClearedFourteenthDefectBlock5_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
    + localClearedFourteenthDefectBlock6_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
    + localClearedFourteenthDefectBlock7_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
    + localClearedFourteenthDefectBlock8_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
    + localClearedFourteenthDefectBlock9_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
    + localClearedFourteenthDefectBlock10_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
    + localClearedFourteenthDefectBlock11_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda

set_option maxHeartbeats 16000000 in
/-- Polynomial numerator of `8796093022208 h⁹⁸ ξ` on the ninth-power
face.  The large literal is blocked above to keep elaboration linear. -/
def localClearedFourteenthDefect810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X])
    (lambda : F) : F[X] :=
  localClearedFourteenthDefectCore810 h a7 a6 a5 a4 a3 a2 a1 a0
    b8 b7 b6 b5 b4 b3 b2 b1 (Polynomial.C lambda)


set_option maxHeartbeats 400000000 in
/-- Clearing the first integral `ξ` of the degree-`3` row against `h⁹⁸`
on the ninth-power face. -/
theorem fourteenthDefect_eq_clearedXi810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b9 b8 b7 b6 b5 b4 b3 b2 b1 lambda : F)
    (hh : h ≠ 0)
    (hN : 5 * a7 * h ^ 2 - 4 * b9 = lambda * h ^ 9) :
    (8796093022208 : F) * h ^ 98 *
        xiResidual810
          (depressedL810 h (octicDepressionR810 h a7) b9)
          (depressedA810 h (octicDepressionR810 h a7) a7 a6)
          (depressedB810 h (octicDepressionR810 h a7) a7 a6 a5)
          (depressedC810 h (octicDepressionR810 h a7) a7 a6 a5 a4)
          (depressedD810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3)
          (depressedE810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2)
          (depressedF810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2
            a1)
          (depressedG810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2
            a1 a0)
          (depressedP810 h (octicDepressionR810 h a7) b9 b8)
          (depressedQ810 h (octicDepressionR810 h a7) b9 b8 b7)
          (depressedR810 h (octicDepressionR810 h a7) b9 b8 b7 b6)
          (depressedS810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5)
          (depressedT810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4)
          (depressedU810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4
            b3)
          (depressedV810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4
            b3 b2)
          (depressedW810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4
            b3 b2 b1) =
    localClearedFourteenthDefectCore810 h a7 a6 a5 a4 a3 a2 a1 a0
      b8 b7 b6 b5 b4 b3 b2 b1 lambda := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h32 : (32 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have h128 : (128 : F) ≠ 0 := by norm_num
  have h256 : (256 : F) ≠ 0 := by norm_num
  have h512 : (512 : F) ≠ 0 := by norm_num
  have h1024 : (1024 : F) ≠ 0 := by norm_num
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have h4096 : (4096 : F) ≠ 0 := by norm_num
  have h16384 : (16384 : F) ≠ 0 := by norm_num
  have h8192 : (8192 : F) ≠ 0 := by norm_num
  have h32768 : (32768 : F) ≠ 0 := by norm_num
  have h65536 : (65536 : F) ≠ 0 := by norm_num
  have h131072 : (131072 : F) ≠ 0 := by norm_num
  have h262144 : (262144 : F) ≠ 0 := by norm_num
  have h16777216 : (16777216 : F) ≠ 0 := by norm_num
  have h67108864 : (67108864 : F) ≠ 0 := by norm_num
  have h524288 : (524288 : F) ≠ 0 := by norm_num
  have h8796093022208 : (8796093022208 : F) ≠ 0 := by norm_num
  have hh14 : h ^ 14 ≠ 0 := pow_ne_zero 14 hh
  have hh21 : h ^ 21 ≠ 0 := pow_ne_zero 21 hh
  have hh28 : h ^ 28 ≠ 0 := pow_ne_zero 28 hh
  have hh35 : h ^ 35 ≠ 0 := pow_ne_zero 35 hh
  have hh42 : h ^ 42 ≠ 0 := pow_ne_zero 42 hh
  have hh49 : h ^ 49 ≠ 0 := pow_ne_zero 49 hh
  have hh56 : h ^ 56 ≠ 0 := pow_ne_zero 56 hh
  have hh63 : h ^ 63 ≠ 0 := pow_ne_zero 63 hh
  have hh98 : h ^ 98 ≠ 0 := pow_ne_zero 98 hh
  have hL :
      depressedL810 h (octicDepressionR810 h a7) b9 = -lambda / 4 :=
    depressedL810_eq_of_ninthPower h a7 b9 lambda hh hN
  have hA :
      depressedA810 h (octicDepressionR810 h a7) a7 a6 =
        (16 * a6 * h ^ 8 - 7 * a7 ^ 2) / (16 * h ^ 14) :=
    depressedA810_eq_cleared h a7 a6 hh
  have hB :
      depressedB810 h (octicDepressionR810 h a7) a7 a6 a5 =
        (32 * a5 * h ^ 16 - 24 * a6 * a7 * h ^ 8 + 7 * a7 ^ 3) /
          (32 * h ^ 21) :=
    depressedB810_eq_cleared h a7 a6 a5 hh
  have hC :
      depressedC810 h (octicDepressionR810 h a7) a7 a6 a5 a4 =
        (2048 * a4 * h ^ 24 - 1280 * a5 * a7 * h ^ 16 +
            480 * a6 * a7 ^ 2 * h ^ 8 - 105 * a7 ^ 4) /
          (2048 * h ^ 28) :=
    depressedC810_eq_cleared h a7 a6 a5 a4 hh
  have hD0 :
      depressedD810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 =
        (1024 * a3 * h ^ 32 - 512 * a4 * a7 * h ^ 24 +
            160 * a5 * a7 ^ 2 * h ^ 16 - 40 * a6 * a7 ^ 3 * h ^ 8 +
            7 * a7 ^ 5) /
          (1024 * h ^ 35) :=
    depressedD810_eq_cleared h a7 a6 a5 a4 a3 hh
  have hE0 :
      depressedE810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2 =
        (65536 * a2 * h ^ 40 - 24576 * a3 * a7 * h ^ 32 +
            6144 * a4 * a7 ^ 2 * h ^ 24 - 1280 * a5 * a7 ^ 3 * h ^ 16 +
            240 * a6 * a7 ^ 4 * h ^ 8 - 35 * a7 ^ 6) /
          (65536 * h ^ 42) :=
    depressedE810_eq_cleared h a7 a6 a5 a4 a3 a2 hh
  have hF0 :
      depressedF810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2 a1 =
        (131072 * a1 * h ^ 48 - 32768 * a2 * a7 * h ^ 40 +
            6144 * a3 * a7 ^ 2 * h ^ 32 - 1024 * a4 * a7 ^ 3 * h ^ 24 +
            160 * a5 * a7 ^ 4 * h ^ 16 - 24 * a6 * a7 ^ 5 * h ^ 8 +
            3 * a7 ^ 7) /
          (131072 * h ^ 49) :=
    depressedF810_eq_cleared h a7 a6 a5 a4 a3 a2 a1 hh
  have hG0 :
      depressedG810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2 a1
          a0 =
        (16777216 * a0 * h ^ 56 - 2097152 * a1 * a7 * h ^ 48 +
            262144 * a2 * a7 ^ 2 * h ^ 40 - 32768 * a3 * a7 ^ 3 * h ^ 32 +
            4096 * a4 * a7 ^ 4 * h ^ 24 - 512 * a5 * a7 ^ 5 * h ^ 16 +
            64 * a6 * a7 ^ 6 * h ^ 8 - 7 * a7 ^ 8) /
          (16777216 * h ^ 56) :=
    depressedG810_eq_cleared h a7 a6 a5 a4 a3 a2 a1 a0 hh
  have hP :
      depressedP810 h (octicDepressionR810 h a7) b9 b8 =
        (-45 * a7 ^ 2 + 18 * lambda * a7 * h ^ 7 + 64 * b8 * h ^ 6) /
          (64 * h ^ 14) :=
    depressedP810_eq_cleared_ninthPower h a7 b9 b8 lambda hh hN
  have hQ :
      depressedQ810 h (octicDepressionR810 h a7) b9 b8 b7 =
        (64 * b7 * h ^ 14 - 64 * a7 * b8 * h ^ 6 -
            9 * lambda * a7 ^ 2 * h ^ 7 + 30 * a7 ^ 3) /
          (64 * h ^ 21) :=
    depressedQ810_eq_cleared h a7 b9 b8 b7 lambda hh hN
  have hR :
      depressedR810 h (octicDepressionR810 h a7) b9 b8 b7 b6 =
        (-315 * a7 ^ 4 + 84 * lambda * a7 ^ 3 * h ^ 7 +
            896 * a7 ^ 2 * b8 * h ^ 6 - 1792 * a7 * b7 * h ^ 14 +
            2048 * b6 * h ^ 22) /
          (2048 * h ^ 28) :=
    depressedR810_eq_cleared h a7 b9 b8 b7 b6 lambda hh hN
  have hS :
      depressedS810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 =
        (252 * a7 ^ 5 - 63 * lambda * a7 ^ 4 * h ^ 7 -
            896 * a7 ^ 3 * b8 * h ^ 6 + 2688 * a7 ^ 2 * b7 * h ^ 14 -
            6144 * a7 * b6 * h ^ 22 + 8192 * b5 * h ^ 30) /
          (8192 * h ^ 35) :=
    depressedS810_eq_cleared h a7 b9 b8 b7 b6 b5 lambda hh hN
  have hT0 :
      depressedT810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4 =
        (-525 * a7 ^ 6 + 126 * lambda * a7 ^ 5 * h ^ 7 +
            2240 * a7 ^ 4 * b8 * h ^ 6 - 8960 * a7 ^ 3 * b7 * h ^ 14 +
            30720 * a7 ^ 2 * b6 * h ^ 22 - 81920 * a7 * b5 * h ^ 30 +
            131072 * b4 * h ^ 38) /
          (131072 * h ^ 42) :=
    depressedT810_eq_cleared h a7 b9 b8 b7 b6 b5 b4 lambda hh hN
  have hU0 :
      depressedU810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4 b3 =
        (90 * a7 ^ 7 - 21 * lambda * a7 ^ 6 * h ^ 7 -
            448 * a7 ^ 5 * b8 * h ^ 6 + 2240 * a7 ^ 4 * b7 * h ^ 14 -
            10240 * a7 ^ 3 * b6 * h ^ 22 + 40960 * a7 ^ 2 * b5 * h ^ 30 -
            131072 * a7 * b4 * h ^ 38 + 262144 * b3 * h ^ 46) /
          (262144 * h ^ 49) :=
    depressedU810_eq_cleared h a7 b9 b8 b7 b6 b5 b4 b3 lambda hh hN
  have hV0 :
      depressedV810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4 b3
          b2 =
        (-315 * a7 ^ 8 + 72 * lambda * a7 ^ 7 * h ^ 7 +
            1792 * a7 ^ 6 * b8 * h ^ 6 - 10752 * a7 ^ 5 * b7 * h ^ 14 +
            61440 * a7 ^ 4 * b6 * h ^ 22 - 327680 * a7 ^ 3 * b5 * h ^ 30 +
            1572864 * a7 ^ 2 * b4 * h ^ 38 -
            6291456 * a7 * b3 * h ^ 46 + 16777216 * b2 * h ^ 54) /
          (16777216 * h ^ 56) :=
    depressedV810_eq_cleared h a7 b9 b8 b7 b6 b5 b4 b3 b2 lambda hh hN
  have hW0 :
      depressedW810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4 b3
          b2 b1 =
        (40 * a7 ^ 9 - 9 * lambda * a7 ^ 8 * h ^ 7 -
            256 * a7 ^ 7 * b8 * h ^ 6 + 1792 * a7 ^ 6 * b7 * h ^ 14 -
            12288 * a7 ^ 5 * b6 * h ^ 22 + 81920 * a7 ^ 4 * b5 * h ^ 30 -
            524288 * a7 ^ 3 * b4 * h ^ 38 +
            3145728 * a7 ^ 2 * b3 * h ^ 46 -
            16777216 * a7 * b2 * h ^ 54 + 67108864 * b1 * h ^ 62) /
          (67108864 * h ^ 63) :=
    depressedW810_eq_cleared h a7 b9 b8 b7 b6 b5 b4 b3 b2 b1 lambda hh hN
  simp only [localClearedFourteenthDefectCore810,
    localClearedFourteenthDefectBlock0_810,
    localClearedFourteenthDefectBlock1_810,
    localClearedFourteenthDefectBlock2_810,
    localClearedFourteenthDefectBlock3_810,
    localClearedFourteenthDefectBlock4_810,
    localClearedFourteenthDefectBlock5_810,
    localClearedFourteenthDefectBlock6_810,
    localClearedFourteenthDefectBlock7_810,
    localClearedFourteenthDefectBlock8_810,
    localClearedFourteenthDefectBlock9_810,
    localClearedFourteenthDefectBlock10_810,
    localClearedFourteenthDefectBlock11_810,
    xiResidual810, hL, hA, hB, hC, hD0, hE0, hF0, hG0, hP, hQ,
    hR, hS, hT0, hU0, hV0, hW0, alphaResidual810, betaResidual810,
    gammaResidual810, deltaResidual810, epsilonResidual810,
    zetaResidual810, etaResidual810, thetaResidual810]
  field_simp [hh, h2, h4, h8, h16, h32, h64, h128, h256, h512, h1024, h2048,
    h4096, h8192, h16384, h32768, h65536, h131072, h262144, h524288,
    h16777216, h67108864, h8796093022208, hh14, hh21, hh28, hh35, hh42,
    hh49, hh56, hh63, hh98]
  ring

end Depression810FourteenthClearing

/-! ## Degree-`3` depressed Jacobian coefficient -/

section DepressedRow810Fourteenth

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]

/-- For a depressed monic octic and a monic decic whose `z⁹` coefficient is
already a differential constant, the degree-`3` Jacobian coefficient is
exactly `4 T G' + 3 U F' + 2 V E' + W D'
- F U' - 2 E V' - 3 D W' - 4 C X'`. -/
theorem differentialJacobian_coeff_3_monicOcticDecic
    (d : Derivation k F F) (f g : F[X])
    (hf_high : ∀ n, 8 < n → f.coeff n = 0) (hf8 : f.coeff 8 = 1)
    (hf7 : f.coeff 7 = 0)
    (hg_high : ∀ n, 10 < n → g.coeff n = 0) (hg10 : g.coeff 10 = 1)
    (hL : d (g.coeff 9) = 0) :
    (differentialJacobian d f g).coeff 3 =
      (4 : F) * g.coeff 4 * d (f.coeff 0) +
        (3 : F) * g.coeff 3 * d (f.coeff 1) +
        (2 : F) * g.coeff 2 * d (f.coeff 2) +
        g.coeff 1 * d (f.coeff 3) -
          f.coeff 1 * d (g.coeff 3) -
          (2 : F) * f.coeff 2 * d (g.coeff 2) -
          (3 : F) * f.coeff 3 * d (g.coeff 1) -
          (4 : F) * f.coeff 4 * d (g.coeff 0) := by
  have hanti : (Finset.HasAntidiagonal.antidiagonal (3 : ℕ) :
      Finset (ℕ × ℕ)) =
      ({(0, 3), (1, 2), (2, 1),
        (3, 0)} : Finset (ℕ × ℕ)) := by decide
  have hne03_12 : ((0, 3) : ℕ × ℕ) ≠ (1, 2) := by decide
  have hne03_21 : ((0, 3) : ℕ × ℕ) ≠ (2, 1) := by decide
  have hne03_30 : ((0, 3) : ℕ × ℕ) ≠ (3, 0) := by decide
  have hne12_21 : ((1, 2) : ℕ × ℕ) ≠ (2, 1) := by decide
  have hne12_30 : ((1, 2) : ℕ × ℕ) ≠ (3, 0) := by decide
  have hne21_30 : ((2, 1) : ℕ × ℕ) ≠ (3, 0) := by decide
  have hfirst :
      (coefficientDeriv d f * g.derivative).coeff 3 =
        (4 : F) * g.coeff 4 * d (f.coeff 0) +
          (3 : F) * g.coeff 3 * d (f.coeff 1) +
          (2 : F) * g.coeff 2 * d (f.coeff 2) +
          g.coeff 1 * d (f.coeff 3) := by
    rw [Polynomial.coeff_mul, hanti]
    have hpair :
        (∑ p ∈ ({(0, 3), (1, 2), (2, 1), (3, 0)} : Finset (ℕ × ℕ)),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (coefficientDeriv d f).coeff 0 * g.derivative.coeff 3 +
            (coefficientDeriv d f).coeff 1 * g.derivative.coeff 2 +
            (coefficientDeriv d f).coeff 2 * g.derivative.coeff 1 +
            (coefficientDeriv d f).coeff 3 * g.derivative.coeff 0 := by
      rw [Finset.sum_insert (by simp [hne03_12, hne03_21, hne03_30]),
        Finset.sum_insert (by simp [hne12_21, hne12_30]),
        Finset.sum_insert (by simp [hne21_30]),
        Finset.sum_singleton]
      ring
    have hder3 : g.derivative.coeff 3 = (4 : F) * g.coeff 4 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder2 : g.derivative.coeff 2 = (3 : F) * g.coeff 3 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder1 : g.derivative.coeff 1 = (2 : F) * g.coeff 2 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder0 : g.derivative.coeff 0 = g.coeff 1 := by
      rw [Polynomial.coeff_derivative]; simp
    rw [hpair, coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, coeff_coefficientDeriv,
      hder3, hder2, hder1, hder0]
    ring
  have hsecond :
      (f.derivative * coefficientDeriv d g).coeff 3 =
        f.coeff 1 * d (g.coeff 3) +
          (2 : F) * f.coeff 2 * d (g.coeff 2) +
          (3 : F) * f.coeff 3 * d (g.coeff 1) +
          (4 : F) * f.coeff 4 * d (g.coeff 0) := by
    rw [Polynomial.coeff_mul, hanti]
    have hpair :
        (∑ p ∈ ({(0, 3), (1, 2), (2, 1), (3, 0)} : Finset (ℕ × ℕ)),
            f.derivative.coeff p.1 * (coefficientDeriv d g).coeff p.2) =
          f.derivative.coeff 0 * (coefficientDeriv d g).coeff 3 +
            f.derivative.coeff 1 * (coefficientDeriv d g).coeff 2 +
            f.derivative.coeff 2 * (coefficientDeriv d g).coeff 1 +
            f.derivative.coeff 3 * (coefficientDeriv d g).coeff 0 := by
      rw [Finset.sum_insert (by simp [hne03_12, hne03_21, hne03_30]),
        Finset.sum_insert (by simp [hne12_21, hne12_30]),
        Finset.sum_insert (by simp [hne21_30]),
        Finset.sum_singleton]
      ring
    have hder0 : f.derivative.coeff 0 = f.coeff 1 := by
      rw [Polynomial.coeff_derivative]; simp
    have hder1 : f.derivative.coeff 1 = (2 : F) * f.coeff 2 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder2 : f.derivative.coeff 2 = (3 : F) * f.coeff 3 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder3 : f.derivative.coeff 3 = (4 : F) * f.coeff 4 := by
      rw [Polynomial.coeff_derivative]; ring
    rw [hpair, coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, coeff_coefficientDeriv,
      hder0, hder1, hder2, hder3]
  simp only [differentialJacobian, Polynomial.coeff_sub, hfirst, hsecond]
  ring

set_option maxHeartbeats 400000000 in
theorem xiResidual810_deriv_zero
    (d : Derivation k F F)
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 X0 : F)
    (hL : d L = 0)
    (halpha : d (alphaResidual810 A P) = 0)
    (hbeta : d (betaResidual810 L A B Q) = 0)
    (hgamma : d (gammaResidual810 L A B C0 P R) = 0)
    (hdelta : d (deltaResidual810 L A B C0 D0 P Q S0) = 0)
    (hepsilon : d (epsilonResidual810 L A B C0 D0 E0 P Q R T0) = 0)
    (hzeta : d (zetaResidual810 L A B C0 D0 E0 F0 P Q R S0 U0) = 0)
    (heta : d (etaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 V0) = 0)
    (htheta : d (thetaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 W0) = 0)
    (hiota : d (iotaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 X0) = 0)
    (hrow8 : (9 : F) * L * d G0 + (8 : F) * P * d F0 +
        (7 : F) * Q * d E0 + (6 : F) * R * d D0 +
        (5 : F) * S0 * d C0 + (4 : F) * T0 * d B +
        (3 : F) * U0 * d A -
        F0 * d P - (2 : F) * E0 * d Q -
        (3 : F) * D0 * d R - (4 : F) * C0 * d S0 -
        (5 : F) * B * d T0 - (6 : F) * A * d U0 -
        (8 : F) * d W0 = 0)
    (hrow7 : (8 : F) * P * d G0 + (7 : F) * Q * d F0 +
        (6 : F) * R * d E0 + (5 : F) * S0 * d D0 +
        (4 : F) * T0 * d C0 + (3 : F) * U0 * d B +
        (2 : F) * V0 * d A -
        F0 * d Q - (2 : F) * E0 * d R -
        (3 : F) * D0 * d S0 - (4 : F) * C0 * d T0 -
        (5 : F) * B * d U0 - (6 : F) * A * d V0 -
        (8 : F) * d X0 = 0)
    (hrow6 : (7 : F) * Q * d G0 + (6 : F) * R * d F0 +
        (5 : F) * S0 * d E0 + (4 : F) * T0 * d D0 +
        (3 : F) * U0 * d C0 + (2 : F) * V0 * d B +
        W0 * d A -
        F0 * d R - (2 : F) * E0 * d S0 -
        (3 : F) * D0 * d T0 - (4 : F) * C0 * d U0 -
        (5 : F) * B * d V0 - (6 : F) * A * d W0 = 0)
    (hrow5 : (6 : F) * R * d G0 + (5 : F) * S0 * d F0 +
        (4 : F) * T0 * d E0 + (3 : F) * U0 * d D0 +
        (2 : F) * V0 * d C0 + W0 * d B -
        F0 * d S0 - (2 : F) * E0 * d T0 -
        (3 : F) * D0 * d U0 - (4 : F) * C0 * d V0 -
        (5 : F) * B * d W0 - (6 : F) * A * d X0 = 0)
    (hrow : (4 : F) * T0 * d G0 + (3 : F) * U0 * d F0 +
        (2 : F) * V0 * d E0 + W0 * d D0 -
        F0 * d U0 - (2 : F) * E0 * d V0 -
        (3 : F) * D0 * d W0 - (4 : F) * C0 * d X0 = 0) :
    d (xiResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0) = 0 := by
  have h2 : d (2 : F) = 0 := d.map_natCast 2
  have h3 : d (3 : F) = 0 := d.map_natCast 3
  have h4 : d (4 : F) = 0 := d.map_natCast 4
  have h5 : d (5 : F) = 0 := d.map_natCast 5
  have h7 : d (7 : F) = 0 := d.map_natCast 7
  have h8 : d (8 : F) = 0 := d.map_natCast 8
  have h9 : d (9 : F) = 0 := d.map_natCast 9
  have h15 : d (15 : F) = 0 := d.map_natCast 15
  have h16 : d (16 : F) = 0 := d.map_natCast 16
  have h21 : d (21 : F) = 0 := d.map_natCast 21
  have h32 : d (32 : F) = 0 := d.map_natCast 32
  have h35 : d (35 : F) = 0 := d.map_natCast 35
  have h63 : d (63 : F) = 0 := d.map_natCast 63
  have h64 : d (64 : F) = 0 := d.map_natCast 64
  have h128 : d (128 : F) = 0 := d.map_natCast 128
  have h315 : d (315 : F) = 0 := d.map_natCast 315
  have h512 : d (512 : F) = 0 := d.map_natCast 512
  have h1024 : d (1024 : F) = 0 := d.map_natCast 1024
  have h2048 : d (2048 : F) = 0 := d.map_natCast 2048
  have h32768 : d (32768 : F) = 0 := d.map_natCast 32768
  have h77 : d (77 : F) = 0 := d.map_natCast 77
  have h105 : d (105 : F) = 0 := d.map_natCast 105
  have h8192 : d (8192 : F) = 0 := d.map_natCast 8192
  have h12 : d (1 / 2 : F) = 0 := by
    simp [Derivation.leibniz_inv, h2]
  have h14 : d (1 / 4 : F) = 0 := by
    simp [Derivation.leibniz_inv, h4]
  have h18 : d (1 / 8 : F) = 0 := by
    simp [Derivation.leibniz_inv, h8]
  have h38 : d (3 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, h8, h3]
  have h54 : d (5 / 4 : F) = 0 := by
    simp [Derivation.leibniz_div, h4, h5]
  have h98 : d (9 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, h8, h9]
  have h78 : d (7 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, h8, h7]
  have h34 : d (3 / 4 : F) = 0 := by
    simp [Derivation.leibniz_div, h4, h3]
  have h58 : d (5 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, h8, h5]
  have h516 : d (5 / 16 : F) = 0 := by
    simp [Derivation.leibniz_div, h16, h5]
  have h316 : d (3 / 16 : F) = 0 := by
    simp [Derivation.leibniz_div, h16, h3]
  have h532 : d (5 / 32 : F) = 0 := by
    simp [Derivation.leibniz_div, h32, h5]
  have h15128 : d (15 / 128 : F) = 0 := by
    simp [Derivation.leibniz_div, h128, h15]
  have h5128 : d (5 / 128 : F) = 0 := by
    simp [Derivation.leibniz_div, h128, h5]
  have h7128 : d (7 / 128 : F) = 0 := by
    simp [Derivation.leibniz_div, h128, h7]
  have h9128 : d (9 / 128 : F) = 0 := by
    simp [Derivation.leibniz_div, h128, h9]
  have h1564 : d (15 / 64 : F) = 0 := by
    simp [Derivation.leibniz_div, h64, h15]
  have h964 : d (9 / 64 : F) = 0 := by
    simp [Derivation.leibniz_div, h64, h9]
  have h764 : d (7 / 64 : F) = 0 := by
    simp [Derivation.leibniz_div, h64, h7]
  have h35512 : d (35 / 512 : F) = 0 := by
    simp [Derivation.leibniz_div, h512, h35]
  have h211024 : d (21 / 1024 : F) = 0 := by
    simp [Derivation.leibniz_div, h1024, h21]
  have h631024 : d (63 / 1024 : F) = 0 := by
    simp [Derivation.leibniz_div, h1024, h63]
  have h31532768 : d (315 / 32768 : F) = 0 := by
    simp [Derivation.leibniz_div, h32768, h315]
  have h778192 : d (77 / 8192 : F) = 0 := by
    simp [Derivation.leibniz_div, h8192, h77]
  have h3158192 : d (315 / 8192 : F) = 0 := by
    simp [Derivation.leibniz_div, h8192, h315]
  have h1051024 : d (105 / 1024 : F) = 0 := by
    simp [Derivation.leibniz_div, h1024, h105]
  have h63512 : d (63 / 512 : F) = 0 := by
    simp [Derivation.leibniz_div, h512, h63]
  have h332 : d (3 / 32 : F) = 0 := by
    simp [Derivation.leibniz_div, h32, h3]
  have h352048 : d (35 / 2048 : F) = 0 := by
    simp [Derivation.leibniz_div, h2048, h35]

  have h13 : d (13 : F) = 0 := d.map_natCast 13
  have h17 : d (17 : F) = 0 := d.map_natCast 17
  have h75 : d (75 : F) = 0 := d.map_natCast 75
  have h81 : d (81 : F) = 0 := d.map_natCast 81
  have h85 : d (85 : F) = 0 := d.map_natCast 85
  have h189 : d (189 : F) = 0 := d.map_natCast 189
  have h441 : d (441 : F) = 0 := d.map_natCast 441
  have h455 : d (455 : F) = 0 := d.map_natCast 455
  have h1071 : d (1071 : F) = 0 := d.map_natCast 1071
  have h4096 : d (4096 : F) = 0 := d.map_natCast 4096
  have h16384 : d (16384 : F) = 0 := d.map_natCast 16384
  have h65536n : d (65536 : F) = 0 := d.map_natCast 65536
  have h44132768 : d (441 / 32768 : F) = 0 := by
    simp [Derivation.leibniz_div, h32768, h441]
  have h44165536 : d (441 / 65536 : F) = 0 := by
    simp [Derivation.leibniz_div, h65536n, h441]
  have h4558192 : d (455 / 8192 : F) = 0 := by
    simp [Derivation.leibniz_div, h8192, h455]
  have h107116384 : d (1071 / 16384 : F) = 0 := by
    simp [Derivation.leibniz_div, h16384, h1071]
  have h1894096 : d (189 / 4096 : F) = 0 := by
    simp [Derivation.leibniz_div, h4096, h189]
  have h851024 : d (85 / 1024 : F) = 0 := by
    simp [Derivation.leibniz_div, h1024, h85]
  have h751024 : d (75 / 1024 : F) = 0 := by
    simp [Derivation.leibniz_div, h1024, h75]
  have h811024 : d (81 / 1024 : F) = 0 := by
    simp [Derivation.leibniz_div, h1024, h81]
  have h932 : d (9 / 32 : F) = 0 := by
    simp [Derivation.leibniz_div, h32, h9]
  have h732 : d (7 / 32 : F) = 0 := by
    simp [Derivation.leibniz_div, h32, h7]
  have h21128 : d (21 / 128 : F) = 0 := by
    simp [Derivation.leibniz_div, h128, h21]
  have h35128 : d (35 / 128 : F) = 0 := by
    simp [Derivation.leibniz_div, h128, h35]
  have h771024 : d (77 / 1024 : F) = 0 := by
    simp [Derivation.leibniz_div, h1024, h77]

  have h256 : d (256 : F) = 0 := d.map_natCast 256
  have h45 : d (45 : F) = 0 := d.map_natCast 45
  have h225 : d (225 : F) = 0 := d.map_natCast 225
  have h385 : d (385 : F) = 0 := d.map_natCast 385
  have h945 : d (945 : F) = 0 := d.map_natCast 945
  have h45256 : d (45 / 256 : F) = 0 := by
    simp [Derivation.leibniz_div, h256, h45]
  have h452048 : d (45 / 2048 : F) = 0 := by
    simp [Derivation.leibniz_div, h2048, h45]
  have h1894096' : d (189 / 4096 : F) = 0 := by
    simp [Derivation.leibniz_div, h4096, h189]
  have h94532768 : d (945 / 32768 : F) = 0 := by
    simp [Derivation.leibniz_div, h32768, h945]
  have h38565536 : d (385 / 65536 : F) = 0 := by
    simp [Derivation.leibniz_div, h65536n, h385]
  have h2251024 : d (225 / 1024 : F) = 0 := by
    simp [Derivation.leibniz_div, h1024, h225]
  have h7256 : d (7 / 256 : F) = 0 := by
    simp [Derivation.leibniz_div, h256, h7]
  have h3858192 : d (385 / 8192 : F) = 0 := by
    simp [Derivation.leibniz_div, h8192, h385]
  have h1532 : d (15 / 32 : F) = 0 := by
    simp [Derivation.leibniz_div, h32, h15]
  have h116 : d (1 / 16 : F) = 0 := by
    simp [Derivation.leibniz_inv, h16]
  have h35256 : d (35 / 256 : F) = 0 := by
    simp [Derivation.leibniz_div, h256, h35]
  have hn25 : d (25 : F) = 0 := d.map_natCast 25
  have hn27 : d (27 : F) = 0 := d.map_natCast 27
  have hn49 : d (49 : F) = 0 := d.map_natCast 49
  have hn55 : d (55 : F) = 0 := d.map_natCast 55
  have hn135 : d (135 : F) = 0 := d.map_natCast 135
  have hn147 : d (147 : F) = 0 := d.map_natCast 147
  have hn175 : d (175 : F) = 0 := d.map_natCast 175
  have hn195 : d (195 : F) = 0 := d.map_natCast 195
  have hn357 : d (357 : F) = 0 := d.map_natCast 357
  have hn665 : d (665 : F) = 0 := d.map_natCast 665
  have hn819 : d (819 : F) = 0 := d.map_natCast 819
  have hn825 : d (825 : F) = 0 := d.map_natCast 825
  have hn1575 : d (1575 : F) = 0 := d.map_natCast 1575
  have hn1925 : d (1925 : F) = 0 := d.map_natCast 1925
  have hn5985 : d (5985 : F) = 0 := d.map_natCast 5985
  have hn12075 : d (12075 : F) = 0 := d.map_natCast 12075
  have hn262144 : d (262144 : F) = 0 := d.map_natCast 262144
  have hn4194304 : d (4194304 : F) = 0 := d.map_natCast 4194304
  have hf25_128 : d (25 / 128 : F) = 0 := by
    simp [Derivation.leibniz_div, h128, hn25]
  have hf27_128 : d (27 / 128 : F) = 0 := by
    simp [Derivation.leibniz_div, h128, hn27]
  have hf27_256 : d (27 / 256 : F) = 0 := by
    simp [Derivation.leibniz_div, h256, hn27]
  have hf25_512 : d (25 / 512 : F) = 0 := by
    simp [Derivation.leibniz_div, h512, hn25]
  have hf27_512 : d (27 / 512 : F) = 0 := by
    simp [Derivation.leibniz_div, h512, hn27]
  have hf75_512 : d (75 / 512 : F) = 0 := by
    simp [Derivation.leibniz_div, h512, h75]
  have hf45_1024 : d (45 / 1024 : F) = 0 := by
    simp [Derivation.leibniz_div, h1024, h45]
  have hf49_1024 : d (49 / 1024 : F) = 0 := by
    simp [Derivation.leibniz_div, h1024, hn49]
  have hf55_1024 : d (55 / 1024 : F) = 0 := by
    simp [Derivation.leibniz_div, h1024, hn55]
  have hf135_1024 : d (135 / 1024 : F) = 0 := by
    simp [Derivation.leibniz_div, h1024, hn135]
  have hf195_1024 : d (195 / 1024 : F) = 0 := by
    simp [Derivation.leibniz_div, h1024, hn195]
  have hf63_2048 : d (63 / 2048 : F) = 0 := by
    simp [Derivation.leibniz_div, h2048, h63]
  have hf175_2048 : d (175 / 2048 : F) = 0 := by
    simp [Derivation.leibniz_div, h2048, hn175]
  have hf147_4096 : d (147 / 4096 : F) = 0 := by
    simp [Derivation.leibniz_div, h4096, hn147]
  have hf441_4096 : d (441 / 4096 : F) = 0 := by
    simp [Derivation.leibniz_div, h4096, h441]
  have hf665_4096 : d (665 / 4096 : F) = 0 := by
    simp [Derivation.leibniz_div, h4096, hn665]
  have hf819_8192 : d (819 / 8192 : F) = 0 := by
    simp [Derivation.leibniz_div, h8192, hn819]
  have hf819_16384 : d (819 / 16384 : F) = 0 := by
    simp [Derivation.leibniz_div, h16384, hn819]
  have hf945_16384 : d (945 / 16384 : F) = 0 := by
    simp [Derivation.leibniz_div, h16384, h945]
  have hf825_32768 : d (825 / 32768 : F) = 0 := by
    simp [Derivation.leibniz_div, h32768, hn825]
  have hf1575_32768 : d (1575 / 32768 : F) = 0 := by
    simp [Derivation.leibniz_div, h32768, hn1575]
  have hf357_65536 : d (357 / 65536 : F) = 0 := by
    simp [Derivation.leibniz_div, h65536n, hn357]
  have hf1925_65536 : d (1925 / 65536 : F) = 0 := by
    simp [Derivation.leibniz_div, h65536n, hn1925]
  have hf5985_262144 : d (5985 / 262144 : F) = 0 := by
    simp [Derivation.leibniz_div, hn262144, hn5985]
  have hf12075_4194304 : d (12075 / 4194304 : F) = 0 := by
    simp [Derivation.leibniz_div, hn4194304, hn12075]
  have hm165 : d (165 : F) = 0 := d.map_natCast 165
  have hm231 : d (231 : F) = 0 := d.map_natCast 231
  have hm245 : d (245 : F) = 0 := d.map_natCast 245
  have hm525 : d (525 : F) = 0 := d.map_natCast 525
  have hm693 : d (693 : F) = 0 := d.map_natCast 693
  have hm4725 : d (4725 : F) = 0 := d.map_natCast 4725
  have hm7245 : d (7245 : F) = 0 := d.map_natCast 7245
  have hm524288 : d (524288 : F) = 0 := d.map_natCast 524288
  have hg1_32 : d (1 / 32 : F) = 0 := by
    simp [Derivation.leibniz_inv, h32]
  have hg5_64 : d (5 / 64 : F) = 0 := by
    simp [Derivation.leibniz_div, h64, h5]
  have hg3_128 : d (3 / 128 : F) = 0 := by
    simp [Derivation.leibniz_div, h128, h3]
  have hg15_256 : d (15 / 256 : F) = 0 := by
    simp [Derivation.leibniz_div, h256, h15]
  have hg21_256 : d (21 / 256 : F) = 0 := by
    simp [Derivation.leibniz_div, h256, h21]
  have hg45_512 : d (45 / 512 : F) = 0 := by
    simp [Derivation.leibniz_div, h512, h45]
  have hg49_512 : d (49 / 512 : F) = 0 := by
    simp [Derivation.leibniz_div, h512, hn49]
  have hg105_512 : d (105 / 512 : F) = 0 := by
    simp [Derivation.leibniz_div, h512, h105]
  have hg165_512 : d (165 / 512 : F) = 0 := by
    simp [Derivation.leibniz_div, h512, hm165]
  have hg9_1024 : d (9 / 1024 : F) = 0 := by
    simp [Derivation.leibniz_div, h1024, h9]
  have hg35_1024 : d (35 / 1024 : F) = 0 := by
    simp [Derivation.leibniz_div, h1024, h35]
  have hg165_2048 : d (165 / 2048 : F) = 0 := by
    simp [Derivation.leibniz_div, h2048, hm165]
  have hg189_2048 : d (189 / 2048 : F) = 0 := by
    simp [Derivation.leibniz_div, h2048, h189]
  have hg315_4096 : d (315 / 4096 : F) = 0 := by
    simp [Derivation.leibniz_div, h4096, h315]
  have hg525_4096 : d (525 / 4096 : F) = 0 := by
    simp [Derivation.leibniz_div, h4096, hm525]
  have hg189_8192 : d (189 / 8192 : F) = 0 := by
    simp [Derivation.leibniz_div, h8192, h189]
  have hg231_8192 : d (231 / 8192 : F) = 0 := by
    simp [Derivation.leibniz_div, h8192, hm231]
  have hg245_8192 : d (245 / 8192 : F) = 0 := by
    simp [Derivation.leibniz_div, h8192, hm245]
  have hg693_8192 : d (693 / 8192 : F) = 0 := by
    simp [Derivation.leibniz_div, h8192, hm693]
  have hg357_16384 : d (357 / 16384 : F) = 0 := by
    simp [Derivation.leibniz_div, h16384, hn357]
  have hg385_16384 : d (385 / 16384 : F) = 0 := by
    simp [Derivation.leibniz_div, h16384, h385]
  have hg1925_32768 : d (1925 / 32768 : F) = 0 := by
    simp [Derivation.leibniz_div, h32768, hn1925]
  have hg165_65536 : d (165 / 65536 : F) = 0 := by
    simp [Derivation.leibniz_div, h65536n, hm165]
  have hg4725_262144 : d (4725 / 262144 : F) = 0 := by
    simp [Derivation.leibniz_div, hn262144, hm4725]
  have hg7245_524288 : d (7245 / 524288 : F) = 0 := by
    simp [Derivation.leibniz_div, hm524288, hm7245]
  have _hiota := hiota
  have hPderiv : d P = (5 / 4 : F) * d A := by
    have halpha' : d P - (5 / 4 : F) * d A = 0 := by
      simpa [alphaResidual810, map_sub, Derivation.leibniz, h54, zero_mul,
        add_zero] using halpha
    linear_combination halpha'
  have hQderiv : d Q = (5 / 4 : F) * d B + (9 / 8 : F) * L * d A := by
    have hbeta' :
        d Q - (5 / 4 : F) * d B - (9 / 8 : F) * L * d A = 0 := by
      simpa [betaResidual810, map_sub, Derivation.leibniz, h54, h98, hL,
        zero_mul, add_zero, mul_zero] using hbeta
    linear_combination hbeta'
  have hsq : d (A * A) = (2 : F) * A * d A := by
    simp [Derivation.leibniz]
    ring
  have hsqB : d (B * B) = (2 : F) * B * d B := by
    simp [Derivation.leibniz]
    ring
  have hsqC : d (C0 * C0) = (2 : F) * C0 * d C0 := by
    simp [Derivation.leibniz]
    ring
  have hcub : d (A ^ 3) = (3 : F) * A ^ 2 * d A := by
    have h2A : d (A ^ 2) = (2 : F) * A * d A := by
      simpa [pow_two] using hsq
    simp [pow_three, Derivation.leibniz, h2A]
    ring
  have hcubB : d (B ^ 3) = (3 : F) * B ^ 2 * d B := by
    have h2B : d (B ^ 2) = (2 : F) * B * d B := by
      simpa [pow_two] using hsqB
    simp [pow_three, Derivation.leibniz, h2B]
    ring
  have hquar : d (A ^ 4) = (4 : F) * A ^ 3 * d A := by
    have : A ^ 4 = A ^ 3 * A := by ring
    rw [this]
    simp [Derivation.leibniz, hcub]
    ring
  have hquint : d (A ^ 5) = (5 : F) * A ^ 4 * d A := by
    have : A ^ 5 = A ^ 4 * A := by ring
    rw [this]
    simp [Derivation.leibniz, hquar]
    ring
  have hsqD : d (D0 * D0) = (2 : F) * D0 * d D0 := by
    simp [Derivation.leibniz]
    ring
  have hsqE : d (E0 * E0) = (2 : F) * E0 * d E0 := by
    simp [Derivation.leibniz]
    ring
  have hcubC : d (C0 ^ 3) = (3 : F) * C0 ^ 2 * d C0 := by
    have h2C : d (C0 ^ 2) = (2 : F) * C0 * d C0 := by
      simpa [pow_two] using hsqC
    simp [pow_three, Derivation.leibniz, h2C]
    ring
  have hquarB : d (B ^ 4) = (4 : F) * B ^ 3 * d B := by
    have : B ^ 4 = B ^ 3 * B := by ring
    rw [this]
    simp [Derivation.leibniz, hcubB]
    ring
  have hsextA : d (A ^ 6) = (6 : F) * A ^ 5 * d A := by
    have : A ^ 6 = A ^ 5 * A := by ring
    rw [this]
    simp [Derivation.leibniz, hquint]
    ring
  have hseptA : d (A ^ 7) = (7 : F) * A ^ 6 * d A := by
    have : A ^ 7 = A ^ 6 * A := by ring
    rw [this]
    simp [Derivation.leibniz, hsextA]
    ring
  have hsqF : d (F0 * F0) = (2 : F) * F0 * d F0 := by
    simp [Derivation.leibniz]
    ring
  have hgamma_id :
      d (gammaResidual810 L A B C0 P R) =
        d R - ((5 / 4 : F) * d C0 + (5 / 16 : F) * A * d A +
          (9 / 8 : F) * L * d B + alphaResidual810 A P * d A) := by
    simp only [gammaResidual810, map_sub, map_add, Derivation.leibniz, h54,
      h98, h532, hL, halpha, zero_mul, add_zero, mul_zero, pow_two, hsq]
    ring
  have hRderiv' :
      d R = (5 / 4 : F) * d C0 + (5 / 16 : F) * A * d A +
        (9 / 8 : F) * L * d B + alphaResidual810 A P * d A := by
    linear_combination hgamma_id.symm + hgamma
  have hRderiv :
      d R = (5 / 4 : F) * d C0 + (5 / 16 : F) * A * d A +
        (9 / 8 : F) * L * d B + (P - (5 / 4 : F) * A) * d A := by
    rw [hRderiv']
    simp only [alphaResidual810]
  have hdelta_id :
      d (deltaResidual810 L A B C0 D0 P Q S0) =
        d S0 - ((5 / 4 : F) * d D0 + (9 / 8 : F) * L * d C0 +
          alphaResidual810 A P * d B +
          (7 / 8 : F) * betaResidual810 L A B Q * d A +
          (5 / 16 : F) * (A * d B + B * d A) +
          (9 / 64 : F) * L * A * d A) := by
    unfold deltaResidual810
    simp [map_sub, map_add, Derivation.leibniz, h54, h98, h78, h516, h964,
      h9128, hL, halpha, hbeta, zero_mul, add_zero, mul_zero, pow_two, hsq]
    ring
  have hSderiv' :
      d S0 = (5 / 4 : F) * d D0 + (9 / 8 : F) * L * d C0 +
        alphaResidual810 A P * d B +
        (7 / 8 : F) * betaResidual810 L A B Q * d A +
        (5 / 16 : F) * (A * d B + B * d A) +
        (9 / 64 : F) * L * A * d A := by
    linear_combination hdelta_id.symm + hdelta
  have hSderiv :
      d S0 = (5 / 4 : F) * d D0 + (9 / 8 : F) * L * d C0 +
        (P - (5 / 4 : F) * A) * d B +
        (7 / 8 : F) * (Q - (5 / 4 : F) * B - (9 / 8 : F) * L * A) * d A +
        (5 / 16 : F) * (A * d B + B * d A) +
        (9 / 64 : F) * L * A * d A := by
    rw [hSderiv']
    simp [alphaResidual810, betaResidual810]
  have hepsilon_id :
      d (epsilonResidual810 L A B C0 D0 E0 P Q R T0) =
        d T0 - ((5 / 4 : F) * d E0 + (5 / 16 : F) * B * d B +
          (5 / 16 : F) * (A * d C0 + C0 * d A) -
          (15 / 128 : F) * A ^ 2 * d A +
          L * ((9 / 8 : F) * d D0 + (9 / 64 : F) * (A * d B + B * d A)) +
          alphaResidual810 A P * d C0 +
          (7 / 8 : F) * betaResidual810 L A B Q * d B +
          (3 / 4 : F) * gammaResidual810 L A B C0 P R * d A) := by
    simp only [epsilonResidual810, map_sub, map_add, Derivation.leibniz, h54,
      h98, h78, h34, h532, h516, h5128, h15128, h964, hL, halpha, hbeta,
      hgamma, zero_mul, add_zero, mul_zero, pow_two, hsq, hsqB, hcub]
    ring
  have hTderiv' :
      d T0 = (5 / 4 : F) * d E0 + (5 / 16 : F) * B * d B +
        (5 / 16 : F) * (A * d C0 + C0 * d A) -
        (15 / 128 : F) * A ^ 2 * d A +
        L * ((9 / 8 : F) * d D0 + (9 / 64 : F) * (A * d B + B * d A)) +
        alphaResidual810 A P * d C0 +
        (7 / 8 : F) * betaResidual810 L A B Q * d B +
        (3 / 4 : F) * gammaResidual810 L A B C0 P R * d A := by
    linear_combination hepsilon_id.symm + hepsilon
  have hTderiv :
      d T0 = (5 / 4 : F) * d E0 + (5 / 16 : F) * B * d B +
        (5 / 16 : F) * (A * d C0 + C0 * d A) -
        (15 / 128 : F) * A ^ 2 * d A +
        L * ((9 / 8 : F) * d D0 + (9 / 64 : F) * (A * d B + B * d A)) +
        (P - (5 / 4 : F) * A) * d C0 +
        (7 / 8 : F) * (Q - (5 / 4 : F) * B - (9 / 8 : F) * L * A) * d B +
        (3 / 4 : F) * (R - ((5 / 4 : F) * C0 + (5 / 32 : F) * A ^ 2 +
          (9 / 8 : F) * L * B + (P - (5 / 4 : F) * A) * A)) * d A := by
    rw [hTderiv']
    simp [gammaResidual810, alphaResidual810, betaResidual810]
  have hzeta_id :
      d (zetaResidual810 L A B C0 D0 E0 F0 P Q R S0 U0) =
        d U0 - ((5 / 4 : F) * d F0 + (9 / 8 : F) * L * d E0 +
          alphaResidual810 A P * d D0 +
          (7 / 8 : F) * betaResidual810 L A B Q * d C0 +
          (3 / 4 : F) * gammaResidual810 L A B C0 P R * d B +
          (5 / 8 : F) * deltaResidual810 L A B C0 D0 P Q S0 * d A +
          (5 / 16 : F) * (A * d D0 + D0 * d A) +
          (5 / 16 : F) * (B * d C0 + C0 * d B) -
          (7 / 64 : F) * betaResidual810 L A B Q * A * d A -
          (15 / 128 : F) * (2 * A * B * d A + A ^ 2 * d B) -
          (63 / 1024 : F) * L * A ^ 2 * d A +
          (9 / 64 : F) * L * (A * d C0 + C0 * d A) +
          (9 / 64 : F) * L * B * d B) := by
    simp only [zetaResidual810, map_sub, map_add, Derivation.leibniz, h54,
      h98, h78, h34, h58, h516, h7128, h15128, h211024, h964, h9128, hL,
      halpha, hbeta, hgamma, hdelta, zero_mul, add_zero, mul_zero, pow_two,
      hsq, hsqB, hcub]
    ring
  have hUderiv' :
      d U0 = (5 / 4 : F) * d F0 + (9 / 8 : F) * L * d E0 +
        alphaResidual810 A P * d D0 +
        (7 / 8 : F) * betaResidual810 L A B Q * d C0 +
        (3 / 4 : F) * gammaResidual810 L A B C0 P R * d B +
        (5 / 8 : F) * deltaResidual810 L A B C0 D0 P Q S0 * d A +
        (5 / 16 : F) * (A * d D0 + D0 * d A) +
        (5 / 16 : F) * (B * d C0 + C0 * d B) -
        (7 / 64 : F) * betaResidual810 L A B Q * A * d A -
        (15 / 128 : F) * (2 * A * B * d A + A ^ 2 * d B) -
        (63 / 1024 : F) * L * A ^ 2 * d A +
        (9 / 64 : F) * L * (A * d C0 + C0 * d A) +
        (9 / 64 : F) * L * B * d B := by
    linear_combination hzeta_id.symm + hzeta
  have hUderiv :
      d U0 = (5 / 4 : F) * d F0 + (9 / 8 : F) * L * d E0 +
        (P - (5 / 4 : F) * A) * d D0 +
        (7 / 8 : F) * (Q - (5 / 4 : F) * B - (9 / 8 : F) * L * A) * d C0 +
        (3 / 4 : F) * (R - ((5 / 4 : F) * C0 + (5 / 32 : F) * A ^ 2 +
          (9 / 8 : F) * L * B + (P - (5 / 4 : F) * A) * A)) * d B +
        (5 / 8 : F) * (S0 - ((5 / 4 : F) * D0 + (9 / 8 : F) * L * C0 +
          (P - (5 / 4 : F) * A) * B +
          (7 / 8 : F) * (Q - (5 / 4 : F) * B - (9 / 8 : F) * L * A) * A +
          (5 / 16 : F) * A * B + (9 / 128 : F) * L * A ^ 2)) * d A +
        (5 / 16 : F) * (A * d D0 + D0 * d A) +
        (5 / 16 : F) * (B * d C0 + C0 * d B) -
        (7 / 64 : F) * (Q - (5 / 4 : F) * B - (9 / 8 : F) * L * A) * A *
          d A -
        (15 / 128 : F) * (2 * A * B * d A + A ^ 2 * d B) -
        (63 / 1024 : F) * L * A ^ 2 * d A +
        (9 / 64 : F) * L * (A * d C0 + C0 * d A) +
        (9 / 64 : F) * L * B * d B := by
    rw [hUderiv']
    simp [alphaResidual810, betaResidual810, gammaResidual810,
      deltaResidual810]
  have heta_id :
      d (etaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 V0) =
        d V0 - ((5 / 4 : F) * d G0 + (9 / 8 : F) * L * d F0 +
          alphaResidual810 A P * d E0 +
          (7 / 8 : F) * betaResidual810 L A B Q * d D0 +
          (3 / 4 : F) * gammaResidual810 L A B C0 P R * d C0 +
          (5 / 8 : F) * deltaResidual810 L A B C0 D0 P Q S0 * d B +
          (1 / 2 : F) * epsilonResidual810 L A B C0 D0 E0 P Q R T0 * d A +
          (5 / 16 : F) * (A * d E0 + E0 * d A) +
          (5 / 16 : F) * (B * d D0 + D0 * d B) +
          (5 / 16 : F) * C0 * d C0 -
          (15 / 128 : F) * (B ^ 2 * d A + (2 : F) * A * B * d B) -
          (15 / 128 : F) * ((2 : F) * A * C0 * d A + A ^ 2 * d C0) +
          (35 / 512 : F) * A ^ 3 * d A +
          (9 / 64 : F) * L * (B * d C0 + C0 * d B) +
          (9 / 64 : F) * L * (A * d D0 + D0 * d A) -
          (63 / 1024 : F) * L * ((2 : F) * A * B * d A + A ^ 2 * d B) -
          (7 / 64 : F) * betaResidual810 L A B Q * (A * d B + B * d A) -
          (3 / 16 : F) * gammaResidual810 L A B C0 P R * A * d A) := by
    simp only [etaResidual810, map_sub, map_add, Derivation.leibniz, h12,
      h14, h18, h54, h98, h78, h34, h58, h516, h532, h15128, h352048, h964,
      h631024, h764, h332, hL, halpha, hbeta, hgamma, hdelta, hepsilon,
      zero_mul, add_zero, mul_zero, pow_two, hsq, hsqB, hsqC, hcub, hquar]
    ring
  have hVderiv' :
      d V0 = (5 / 4 : F) * d G0 + (9 / 8 : F) * L * d F0 +
        alphaResidual810 A P * d E0 +
        (7 / 8 : F) * betaResidual810 L A B Q * d D0 +
        (3 / 4 : F) * gammaResidual810 L A B C0 P R * d C0 +
        (5 / 8 : F) * deltaResidual810 L A B C0 D0 P Q S0 * d B +
        (1 / 2 : F) * epsilonResidual810 L A B C0 D0 E0 P Q R T0 * d A +
        (5 / 16 : F) * (A * d E0 + E0 * d A) +
        (5 / 16 : F) * (B * d D0 + D0 * d B) +
        (5 / 16 : F) * C0 * d C0 -
        (15 / 128 : F) * (B ^ 2 * d A + (2 : F) * A * B * d B) -
        (15 / 128 : F) * ((2 : F) * A * C0 * d A + A ^ 2 * d C0) +
        (35 / 512 : F) * A ^ 3 * d A +
        (9 / 64 : F) * L * (B * d C0 + C0 * d B) +
        (9 / 64 : F) * L * (A * d D0 + D0 * d A) -
        (63 / 1024 : F) * L * ((2 : F) * A * B * d A + A ^ 2 * d B) -
        (7 / 64 : F) * betaResidual810 L A B Q * (A * d B + B * d A) -
        (3 / 16 : F) * gammaResidual810 L A B C0 P R * A * d A := by
    linear_combination heta_id.symm + heta
  have hVderiv :
      d V0 = (5 / 4 : F) * d G0 + (9 / 8 : F) * L * d F0 +
        (P - (5 / 4 : F) * A) * d E0 +
        (7 / 8 : F) * (Q - (5 / 4 : F) * B - (9 / 8 : F) * L * A) * d D0 +
        (3 / 4 : F) * (R - ((5 / 4 : F) * C0 + (5 / 32 : F) * A ^ 2 +
          (9 / 8 : F) * L * B + (P - (5 / 4 : F) * A) * A)) * d C0 +
        (5 / 8 : F) * (S0 - ((5 / 4 : F) * D0 + (9 / 8 : F) * L * C0 +
          (P - (5 / 4 : F) * A) * B +
          (7 / 8 : F) * (Q - (5 / 4 : F) * B - (9 / 8 : F) * L * A) * A +
          (5 / 16 : F) * A * B + (9 / 128 : F) * L * A ^ 2)) * d B +
        (1 / 2 : F) * (T0 - ((5 / 4 : F) * E0 + (5 / 32 : F) * B ^ 2 +
          (5 / 16 : F) * A * C0 - (5 / 128 : F) * A ^ 3 +
          L * ((9 / 8 : F) * D0 + (9 / 64 : F) * A * B) +
          (P - (5 / 4 : F) * A) * C0 +
          (7 / 8 : F) * (Q - (5 / 4 : F) * B - (9 / 8 : F) * L * A) * B +
          (3 / 4 : F) * (R - ((5 / 4 : F) * C0 + (5 / 32 : F) * A ^ 2 +
            (9 / 8 : F) * L * B + (P - (5 / 4 : F) * A) * A)) * A)) * d A +
        (5 / 16 : F) * (A * d E0 + E0 * d A) +
        (5 / 16 : F) * (B * d D0 + D0 * d B) +
        (5 / 16 : F) * C0 * d C0 -
        (15 / 128 : F) * (B ^ 2 * d A + (2 : F) * A * B * d B) -
        (15 / 128 : F) * ((2 : F) * A * C0 * d A + A ^ 2 * d C0) +
        (35 / 512 : F) * A ^ 3 * d A +
        (9 / 64 : F) * L * (B * d C0 + C0 * d B) +
        (9 / 64 : F) * L * (A * d D0 + D0 * d A) -
        (63 / 1024 : F) * L * ((2 : F) * A * B * d A + A ^ 2 * d B) -
        (7 / 64 : F) * (Q - (5 / 4 : F) * B - (9 / 8 : F) * L * A) *
          (A * d B + B * d A) -
        (3 / 16 : F) * (R - ((5 / 4 : F) * C0 + (5 / 32 : F) * A ^ 2 +
          (9 / 8 : F) * L * B + (P - (5 / 4 : F) * A) * A)) * A * d A := by
    rw [hVderiv']
    simp [alphaResidual810, betaResidual810, gammaResidual810,
      deltaResidual810, epsilonResidual810]
  have _htheta := htheta
  have hWderiv :
      d W0 = (9 / 8 : F) * L * d G0 + P * d F0 +
        (7 / 8 : F) * Q * d E0 + (3 / 4 : F) * R * d D0 +
        (5 / 8 : F) * S0 * d C0 + (1 / 2 : F) * T0 * d B +
        (3 / 8 : F) * U0 * d A -
        (1 / 8 : F) * F0 * d P - (1 / 4 : F) * E0 * d Q -
        (3 / 8 : F) * D0 * d R - (1 / 2 : F) * C0 * d S0 -
        (5 / 8 : F) * B * d T0 - (3 / 4 : F) * A * d U0 := by
    linear_combination (-1 / 8 : F) * hrow8
  have hXderiv :
      d X0 = P * d G0 + (7 / 8 : F) * Q * d F0 +
        (3 / 4 : F) * R * d E0 + (5 / 8 : F) * S0 * d D0 +
        (1 / 2 : F) * T0 * d C0 + (3 / 8 : F) * U0 * d B +
        (1 / 4 : F) * V0 * d A -
        (1 / 8 : F) * F0 * d Q - (1 / 4 : F) * E0 * d R -
        (3 / 8 : F) * D0 * d S0 - (1 / 2 : F) * C0 * d T0 -
        (5 / 8 : F) * B * d U0 - (3 / 4 : F) * A * d V0 := by
    linear_combination (-1 / 8 : F) * hrow7
  have hrow_red := hrow
  rw [hWderiv, hXderiv, hPderiv, hQderiv, hRderiv, hSderiv, hTderiv, hUderiv,
    hVderiv] at hrow_red
  have hrow5_red := hrow5
  rw [hWderiv, hXderiv, hPderiv, hQderiv, hRderiv, hSderiv, hTderiv, hUderiv,
    hVderiv] at hrow5_red
  have hrow6_red := hrow6
  rw [hWderiv, hPderiv, hQderiv, hRderiv, hSderiv, hTderiv, hUderiv,
    hVderiv] at hrow6_red
  simp only [xiResidual810, alphaResidual810, betaResidual810,
    gammaResidual810, deltaResidual810, epsilonResidual810,
    zetaResidual810, etaResidual810, thetaResidual810, map_sub, map_add,
    Derivation.leibniz, h12, h14, h18, h38, h54, h98, h78, h34, h58, h516,
    h316, h532, h15128, h5128, h7128, h9128, h1564, h964, h764, h35512,
    h211024, h631024, h31532768, h778192, h3158192, h1051024, h63512, h332,
    h352048, hL, h44132768, h44165536, h4558192, h107116384, h1894096,
    h851024, h751024, h811024, h932, h732, h21128, h35128, h771024, h45256,
    h452048, h1894096', h94532768, h38565536, h2251024, h7256, h3858192,
    h1532, h116, h35256, hf25_128, hf27_128, hf27_256, hf25_512, hf27_512,
    hf75_512, hf45_1024, hf49_1024, hf55_1024, hf135_1024, hf195_1024,
    hf63_2048, hf175_2048, hf147_4096, hf441_4096, hf665_4096, hf819_8192,
    hf819_16384, hf945_16384, hf825_32768, hf1575_32768, hf357_65536,
    hf1925_65536, hf5985_262144, hf12075_4194304, zero_mul, add_zero,
    mul_zero, pow_two, hsq, hsqB, hsqC, hsqD, hsqE, hcub, hcubB, hcubC,
    hquar, hquarB, hquint, hsextA,
    hg1_32, hg5_64, hg3_128, hg15_256, hg21_256, hg45_512, hg49_512,
    hg105_512, hg165_512, hg9_1024, hg35_1024, hg165_2048, hg189_2048,
    hg315_4096, hg525_4096, hg189_8192, hg231_8192, hg245_8192, hg693_8192,
    hg357_16384, hg385_16384, hg1925_32768, hg165_65536, hg4725_262144,
    hg7245_524288, hseptA, hsqF]
  rw [hWderiv, hPderiv, hQderiv, hRderiv, hSderiv, hTderiv, hUderiv,
    hVderiv]
  linear_combination (1 / 8 : F) * hrow_red -
    (1 / 16 : F) * A * hrow5_red - (1 / 16 : F) * B * hrow6_red

end DepressedRow810Fourteenth

section NonzeroFourteenthFaceClearing810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 400000000 in
/-- The thirteenth octic/decic integral on a square-core ninth-power source:
the cleared defect is a scalar times `h⁹⁸`. -/
theorem nonzeroFace810_fourteenthDefectPowerRelation
    (p q : k[X][X]) (H h0 : k[X]) (j lambda : k)
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j)) :
    ∃ eta : k,
      localClearedFourteenthDefect810 h0 (p.coeff 7) (p.coeff 6) (p.coeff 5)
          (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
          (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5) (q.coeff 4)
          (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda =
        Polynomial.C eta * h0 ^ 98 := by
  let h : RatFunc k := algebraMap k[X] (RatFunc k) h0
  let a7 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 7)
  let a6 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 6)
  let a5 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 5)
  let a4 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 4)
  let a3 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 3)
  let a2 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 2)
  let a1 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 1)
  let a0 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 0)
  let b9 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 9)
  let b8 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 8)
  let b7 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 7)
  let b6 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 6)
  let b5 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 5)
  let b4 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 4)
  let b3 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 3)
  let b2 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 2)
  let b1 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 1)
  let b0 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 0)
  have hh : h ≠ 0 := RatFunc.algebraMap_ne_zero hh0
  have hpTop : algebraMap k[X] (RatFunc k) (p.coeff 8) = h ^ 8 := by
    simp only [hp8, hH, h, map_pow]
    ring
  have hqTop : algebraMap k[X] (RatFunc k) (q.coeff 10) = h ^ 10 := by
    simp only [hq10, hH, h, map_pow]
    ring
  have hpDep := affineDepress_sourceOctic68 p h
    (octicDepressionR810 h a7) hp hh hpTop
  have hL0 : depressedL68 h (octicDepressionR810 h a7) a7 = 0 :=
    depressedL68_eq_zero_of_octicCenter h a7 hh
  have hNrat : 5 * a7 * h ^ 2 - 4 * b9 = RatFunc.C lambda * h ^ 9 := by
    have hmapped := congrArg (algebraMap k[X] (RatFunc k)) hN
    simpa only [hH, h, a7, b9, map_sub, map_mul, map_pow, map_ofNat,
      RatFunc.algebraMap_C] using hmapped
  have hLval :
      depressedL810 h (octicDepressionR810 h a7) b9 =
        RatFunc.C (-lambda / 4) := by
    have hL := depressedL810_eq_of_ninthPower h a7 b9
      (RatFunc.C lambda) hh (by simpa using hNrat)
    simpa [map_neg, map_div₀, map_ofNat] using hL
  have hbracket := differentialJacobian_affineDepress_sourceToRatFunc68
    p q j h (octicDepressionR810 h a7) hh hD
  let f : (RatFunc k)[X] :=
    affineDepress68 h (octicDepressionR810 h a7) (sourceToRatFunc68 p)
  let g : (RatFunc k)[X] :=
    affineDepress68 h (octicDepressionR810 h a7) (sourceToRatFunc68 q)
  have hf7 : f.coeff 7 = 0 := by
    dsimp only [f]
    rw [hpDep, coeff_depressedOctic68_seven, hL0]
  have hf8 : f.coeff 8 = 1 := by
    dsimp only [f]
    rw [hpDep, coeff_depressedOctic68_eight]
  have hf_high : ∀ n, 8 < n → f.coeff n = 0 := by
    intro n hn
    dsimp only [f]
    rw [hpDep, coeff_depressedOctic68_of_gt_eight _ _ _ _ _ _ _ _ hn]
  have hg_high_src : ∀ n, 10 < n → (sourceToRatFunc68 q).coeff n = 0 := by
    intro n hn
    simp [sourceToRatFunc68, sourceToRatFunc46,
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : q.natDegree < n)]
  have hgTop : (sourceToRatFunc68 q).coeff 10 = h ^ 10 := by
    simpa [sourceToRatFunc68, sourceToRatFunc46] using hqTop
  obtain ⟨hg10, hg9, hg8, hg_high⟩ :=
    affineDepress_degreeTen_highCoeffs810 (sourceToRatFunc68 q) h
      (octicDepressionR810 h a7) hh hgTop hg_high_src
  have hg7 :
      g.coeff 7 =
        depressedQ810 h (octicDepressionR810 h a7) b9 b8 b7 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff7_810 (sourceToRatFunc68 q) h
      (octicDepressionR810 h a7) hh hgTop hg_high_src]
    simp [depressedQ810, octicDepressionR810, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7]
  have hg6 :
      g.coeff 6 =
        depressedR810 h (octicDepressionR810 h a7) b9 b8 b7 b6 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff6_810 (sourceToRatFunc68 q) h
      (octicDepressionR810 h a7) hh hgTop hg_high_src]
    simp [depressedR810, octicDepressionR810, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6]
  have hg5 :
      g.coeff 5 =
        depressedS810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff5_810 (sourceToRatFunc68 q) h
      (octicDepressionR810 h a7) hh hgTop hg_high_src]
    simp [depressedS810, octicDepressionR810, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5]
  have hg4 :
      g.coeff 4 =
        depressedT810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff4_810 (sourceToRatFunc68 q) h
      (octicDepressionR810 h a7) hh hgTop hg_high_src]
    simp [depressedT810, octicDepressionR810, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4]
  have hg2 :
      g.coeff 2 =
        depressedV810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4
          b3 b2 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff2_810 (sourceToRatFunc68 q) h
      (octicDepressionR810 h a7) hh hgTop hg_high_src]
    simp [depressedV810, octicDepressionR810, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4, b3, b2]
  have hg3 :
      g.coeff 3 =
        depressedU810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4
          b3 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff3_810 (sourceToRatFunc68 q) h
      (octicDepressionR810 h a7) hh hgTop hg_high_src]
    simp [depressedU810, octicDepressionR810, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4, b3]
  have hg1 :
      g.coeff 1 =
        depressedW810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4 b3
          b2 b1 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff1_810 (sourceToRatFunc68 q) h
      (octicDepressionR810 h a7) hh hgTop hg_high_src]
    simp [depressedW810, octicDepressionR810, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4, b3, b2, b1]
  have hg8' :
      g.coeff 8 =
        depressedP810 h (octicDepressionR810 h a7) b9 b8 := by
    dsimp only [g]
    rw [hg8]
    simp [depressedP810, octicDepressionR810, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8]
  have hg9' : g.coeff 9 = RatFunc.C (-lambda / 4) := by
    dsimp only [g]
    rw [hg9]
    have : -10 * octicDepressionR810 h a7 +
        (sourceToRatFunc68 q).coeff 9 / h ^ 9 =
          depressedL810 h (octicDepressionR810 h a7) b9 := by
      simp [depressedL810, octicDepressionR810, sourceToRatFunc68,
        sourceToRatFunc46, b9]
    rw [this, hLval]
  have hLconst : ratFuncDerivation68 (g.coeff 9) = 0 := by
    rw [hg9']
    have hx := ratFuncDerivation46_polynomial (Polynomial.C (-lambda / 4) : k[X])
    simpa [ratFuncDerivation68, RatFunc.algebraMap_C] using hx
  have hrow15 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 6) -
        (8 : RatFunc k) * ratFuncDerivation68 (g.coeff 8) = 0 := by
    have hrow :=
      differentialJacobian_coeff_15_monicOcticDecic
        ratFuncDerivation68 f g hf_high hf8 hf7 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 15) hbracket
    simpa [f, g, Polynomial.coeff_C, show (15 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow14 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 5) +
          (9 : RatFunc k) * g.coeff 9 * ratFuncDerivation68 (f.coeff 6) -
        (8 : RatFunc k) * ratFuncDerivation68 (g.coeff 7) = 0 := by
    have hrow :=
      differentialJacobian_coeff_14_monicOcticDecic
        ratFuncDerivation68 f g hf_high hf8 hf7 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 14) hbracket
    simpa [f, g, Polynomial.coeff_C, show (14 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow13 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 4) +
          (9 : RatFunc k) * g.coeff 9 * ratFuncDerivation68 (f.coeff 5) +
        (8 : RatFunc k) * g.coeff 8 * ratFuncDerivation68 (f.coeff 6) -
          (6 : RatFunc k) * f.coeff 6 * ratFuncDerivation68 (g.coeff 8) -
          (8 : RatFunc k) * ratFuncDerivation68 (g.coeff 6) = 0 := by
    have hrow :=
      differentialJacobian_coeff_13_monicOcticDecic
        ratFuncDerivation68 f g hf_high hf8 hf7 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 13) hbracket
    simpa [f, g, Polynomial.coeff_C, show (13 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow12 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 3) +
          (9 : RatFunc k) * g.coeff 9 * ratFuncDerivation68 (f.coeff 4) +
        (8 : RatFunc k) * g.coeff 8 * ratFuncDerivation68 (f.coeff 5) +
        (7 : RatFunc k) * g.coeff 7 * ratFuncDerivation68 (f.coeff 6) -
          (5 : RatFunc k) * f.coeff 5 * ratFuncDerivation68 (g.coeff 8) -
          (6 : RatFunc k) * f.coeff 6 * ratFuncDerivation68 (g.coeff 7) -
          (8 : RatFunc k) * ratFuncDerivation68 (g.coeff 5) = 0 := by
    have hrow :=
      differentialJacobian_coeff_12_monicOcticDecic
        ratFuncDerivation68 f g hf_high hf8 hf7 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 12) hbracket
    simpa [f, g, Polynomial.coeff_C, show (12 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow11 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 2) +
          (9 : RatFunc k) * g.coeff 9 * ratFuncDerivation68 (f.coeff 3) +
        (8 : RatFunc k) * g.coeff 8 * ratFuncDerivation68 (f.coeff 4) +
        (7 : RatFunc k) * g.coeff 7 * ratFuncDerivation68 (f.coeff 5) +
        (6 : RatFunc k) * g.coeff 6 * ratFuncDerivation68 (f.coeff 6) -
          (4 : RatFunc k) * f.coeff 4 * ratFuncDerivation68 (g.coeff 8) -
          (5 : RatFunc k) * f.coeff 5 * ratFuncDerivation68 (g.coeff 7) -
          (6 : RatFunc k) * f.coeff 6 * ratFuncDerivation68 (g.coeff 6) -
          (8 : RatFunc k) * ratFuncDerivation68 (g.coeff 4) = 0 := by
    have hrow :=
      differentialJacobian_coeff_11_monicOcticDecic
        ratFuncDerivation68 f g hf_high hf8 hf7 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 11) hbracket
    simpa [f, g, Polynomial.coeff_C, show (11 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow9 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 0) +
          (9 : RatFunc k) * g.coeff 9 * ratFuncDerivation68 (f.coeff 1) +
        (8 : RatFunc k) * g.coeff 8 * ratFuncDerivation68 (f.coeff 2) +
        (7 : RatFunc k) * g.coeff 7 * ratFuncDerivation68 (f.coeff 3) +
        (6 : RatFunc k) * g.coeff 6 * ratFuncDerivation68 (f.coeff 4) +
        (5 : RatFunc k) * g.coeff 5 * ratFuncDerivation68 (f.coeff 5) +
        (4 : RatFunc k) * g.coeff 4 * ratFuncDerivation68 (f.coeff 6) -
          (2 : RatFunc k) * f.coeff 2 * ratFuncDerivation68 (g.coeff 8) -
          (3 : RatFunc k) * f.coeff 3 * ratFuncDerivation68 (g.coeff 7) -
          (4 : RatFunc k) * f.coeff 4 * ratFuncDerivation68 (g.coeff 6) -
          (5 : RatFunc k) * f.coeff 5 * ratFuncDerivation68 (g.coeff 5) -
          (6 : RatFunc k) * f.coeff 6 * ratFuncDerivation68 (g.coeff 4) -
          (8 : RatFunc k) * ratFuncDerivation68 (g.coeff 2) = 0 := by
    have hrow :=
      differentialJacobian_coeff_9_monicOcticDecic
        ratFuncDerivation68 f g hf_high hf8 hf7 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 9) hbracket
    simpa [f, g, Polynomial.coeff_C, show (9 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow10 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 1) +
          (9 : RatFunc k) * g.coeff 9 * ratFuncDerivation68 (f.coeff 2) +
        (8 : RatFunc k) * g.coeff 8 * ratFuncDerivation68 (f.coeff 3) +
        (7 : RatFunc k) * g.coeff 7 * ratFuncDerivation68 (f.coeff 4) +
        (6 : RatFunc k) * g.coeff 6 * ratFuncDerivation68 (f.coeff 5) +
        (5 : RatFunc k) * g.coeff 5 * ratFuncDerivation68 (f.coeff 6) -
          (3 : RatFunc k) * f.coeff 3 * ratFuncDerivation68 (g.coeff 8) -
          (4 : RatFunc k) * f.coeff 4 * ratFuncDerivation68 (g.coeff 7) -
          (5 : RatFunc k) * f.coeff 5 * ratFuncDerivation68 (g.coeff 6) -
          (6 : RatFunc k) * f.coeff 6 * ratFuncDerivation68 (g.coeff 5) -
          (8 : RatFunc k) * ratFuncDerivation68 (g.coeff 3) = 0 := by
    have hrow :=
      differentialJacobian_coeff_10_monicOcticDecic
        ratFuncDerivation68 f g hf_high hf8 hf7 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 10) hbracket
    simpa [f, g, Polynomial.coeff_C, show (10 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow8 :
      (9 : RatFunc k) * g.coeff 9 * ratFuncDerivation68 (f.coeff 0) +
        (8 : RatFunc k) * g.coeff 8 * ratFuncDerivation68 (f.coeff 1) +
        (7 : RatFunc k) * g.coeff 7 * ratFuncDerivation68 (f.coeff 2) +
        (6 : RatFunc k) * g.coeff 6 * ratFuncDerivation68 (f.coeff 3) +
        (5 : RatFunc k) * g.coeff 5 * ratFuncDerivation68 (f.coeff 4) +
        (4 : RatFunc k) * g.coeff 4 * ratFuncDerivation68 (f.coeff 5) +
        (3 : RatFunc k) * g.coeff 3 * ratFuncDerivation68 (f.coeff 6) -
          f.coeff 1 * ratFuncDerivation68 (g.coeff 8) -
          (2 : RatFunc k) * f.coeff 2 * ratFuncDerivation68 (g.coeff 7) -
          (3 : RatFunc k) * f.coeff 3 * ratFuncDerivation68 (g.coeff 6) -
          (4 : RatFunc k) * f.coeff 4 * ratFuncDerivation68 (g.coeff 5) -
          (5 : RatFunc k) * f.coeff 5 * ratFuncDerivation68 (g.coeff 4) -
          (6 : RatFunc k) * f.coeff 6 * ratFuncDerivation68 (g.coeff 3) -
          (8 : RatFunc k) * ratFuncDerivation68 (g.coeff 1) = 0 := by
    have hrow :=
      differentialJacobian_coeff_8_monicOcticDecic
        ratFuncDerivation68 f g hf_high hf8 hf7 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 8) hbracket
    simpa [f, g, Polynomial.coeff_C, show (8 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow7 :
      (8 : RatFunc k) * g.coeff 8 * ratFuncDerivation68 (f.coeff 0) +
        (7 : RatFunc k) * g.coeff 7 * ratFuncDerivation68 (f.coeff 1) +
        (6 : RatFunc k) * g.coeff 6 * ratFuncDerivation68 (f.coeff 2) +
        (5 : RatFunc k) * g.coeff 5 * ratFuncDerivation68 (f.coeff 3) +
        (4 : RatFunc k) * g.coeff 4 * ratFuncDerivation68 (f.coeff 4) +
        (3 : RatFunc k) * g.coeff 3 * ratFuncDerivation68 (f.coeff 5) +
        (2 : RatFunc k) * g.coeff 2 * ratFuncDerivation68 (f.coeff 6) -
          f.coeff 1 * ratFuncDerivation68 (g.coeff 7) -
          (2 : RatFunc k) * f.coeff 2 * ratFuncDerivation68 (g.coeff 6) -
          (3 : RatFunc k) * f.coeff 3 * ratFuncDerivation68 (g.coeff 5) -
          (4 : RatFunc k) * f.coeff 4 * ratFuncDerivation68 (g.coeff 4) -
          (5 : RatFunc k) * f.coeff 5 * ratFuncDerivation68 (g.coeff 3) -
          (6 : RatFunc k) * f.coeff 6 * ratFuncDerivation68 (g.coeff 2) -
          (8 : RatFunc k) * ratFuncDerivation68 (g.coeff 0) = 0 := by
    have hrow :=
      differentialJacobian_coeff_7_monicOcticDecic
        ratFuncDerivation68 f g hf_high hf8 hf7 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 7) hbracket
    simpa [f, g, Polynomial.coeff_C, show (7 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow6 :
      (7 : RatFunc k) * g.coeff 7 * ratFuncDerivation68 (f.coeff 0) +
        (6 : RatFunc k) * g.coeff 6 * ratFuncDerivation68 (f.coeff 1) +
        (5 : RatFunc k) * g.coeff 5 * ratFuncDerivation68 (f.coeff 2) +
        (4 : RatFunc k) * g.coeff 4 * ratFuncDerivation68 (f.coeff 3) +
        (3 : RatFunc k) * g.coeff 3 * ratFuncDerivation68 (f.coeff 4) +
        (2 : RatFunc k) * g.coeff 2 * ratFuncDerivation68 (f.coeff 5) +
        g.coeff 1 * ratFuncDerivation68 (f.coeff 6) -
          f.coeff 1 * ratFuncDerivation68 (g.coeff 6) -
          (2 : RatFunc k) * f.coeff 2 * ratFuncDerivation68 (g.coeff 5) -
          (3 : RatFunc k) * f.coeff 3 * ratFuncDerivation68 (g.coeff 4) -
          (4 : RatFunc k) * f.coeff 4 * ratFuncDerivation68 (g.coeff 3) -
          (5 : RatFunc k) * f.coeff 5 * ratFuncDerivation68 (g.coeff 2) -
          (6 : RatFunc k) * f.coeff 6 * ratFuncDerivation68 (g.coeff 1) = 0 := by
    have hrow :=
      differentialJacobian_coeff_6_monicOcticDecic
        ratFuncDerivation68 f g hf_high hf8 hf7 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 6) hbracket
    simpa [f, g, Polynomial.coeff_C, show (6 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow5 :
      (6 : RatFunc k) * g.coeff 6 * ratFuncDerivation68 (f.coeff 0) +
        (5 : RatFunc k) * g.coeff 5 * ratFuncDerivation68 (f.coeff 1) +
        (4 : RatFunc k) * g.coeff 4 * ratFuncDerivation68 (f.coeff 2) +
        (3 : RatFunc k) * g.coeff 3 * ratFuncDerivation68 (f.coeff 3) +
        (2 : RatFunc k) * g.coeff 2 * ratFuncDerivation68 (f.coeff 4) +
        g.coeff 1 * ratFuncDerivation68 (f.coeff 5) -
          f.coeff 1 * ratFuncDerivation68 (g.coeff 5) -
          (2 : RatFunc k) * f.coeff 2 * ratFuncDerivation68 (g.coeff 4) -
          (3 : RatFunc k) * f.coeff 3 * ratFuncDerivation68 (g.coeff 3) -
          (4 : RatFunc k) * f.coeff 4 * ratFuncDerivation68 (g.coeff 2) -
          (5 : RatFunc k) * f.coeff 5 * ratFuncDerivation68 (g.coeff 1) -
          (6 : RatFunc k) * f.coeff 6 * ratFuncDerivation68 (g.coeff 0) = 0 := by
    have hrow :=
      differentialJacobian_coeff_5_monicOcticDecic
        ratFuncDerivation68 f g hf_high hf8 hf7 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 5) hbracket
    simpa [f, g, Polynomial.coeff_C, show (5 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow3 :
      (4 : RatFunc k) * g.coeff 4 * ratFuncDerivation68 (f.coeff 0) +
        (3 : RatFunc k) * g.coeff 3 * ratFuncDerivation68 (f.coeff 1) +
        (2 : RatFunc k) * g.coeff 2 * ratFuncDerivation68 (f.coeff 2) +
        g.coeff 1 * ratFuncDerivation68 (f.coeff 3) -
          f.coeff 1 * ratFuncDerivation68 (g.coeff 3) -
          (2 : RatFunc k) * f.coeff 2 * ratFuncDerivation68 (g.coeff 2) -
          (3 : RatFunc k) * f.coeff 3 * ratFuncDerivation68 (g.coeff 1) -
          (4 : RatFunc k) * f.coeff 4 * ratFuncDerivation68 (g.coeff 0) = 0 := by
    have hrow :=
      differentialJacobian_coeff_3_monicOcticDecic
        ratFuncDerivation68 f g hf_high hf8 hf7 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 3) hbracket
    simpa [f, g, Polynomial.coeff_C, show (3 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr

  have hf6 : f.coeff 6 = depressedA810 h (octicDepressionR810 h a7) a7 a6 := by
    dsimp only [f, depressedA810, a7, a6]
    rw [hpDep, coeff_depressedOctic68_six]
  have hf5 : f.coeff 5 =
      depressedB810 h (octicDepressionR810 h a7) a7 a6 a5 := by
    dsimp only [f, depressedB810, a7, a6, a5]
    rw [hpDep, coeff_depressedOctic68_five]
  have hf4 : f.coeff 4 =
      depressedC810 h (octicDepressionR810 h a7) a7 a6 a5 a4 := by
    dsimp only [f, depressedC810, a7, a6, a5, a4]
    rw [hpDep, coeff_depressedOctic68_four]
  have hf3 : f.coeff 3 =
      depressedD810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 := by
    dsimp only [f, depressedD810, a7, a6, a5, a4, a3]
    rw [hpDep, coeff_depressedOctic68_three]
  have hf2 : f.coeff 2 =
      depressedE810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2 := by
    dsimp only [f, depressedE810, a7, a6, a5, a4, a3, a2]
    rw [hpDep, coeff_depressedOctic68_two]
  have hf1 : f.coeff 1 =
      depressedF810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2 a1 := by
    dsimp only [f, depressedF810, a7, a6, a5, a4, a3, a2, a1]
    rw [hpDep, coeff_depressedOctic68_one]
  have hf0 : f.coeff 0 =
      depressedG810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2 a1
        a0 := by
    dsimp only [f, depressedG810, a7, a6, a5, a4, a3, a2, a1, a0]
    rw [hpDep, coeff_depressedOctic68_zero]
  have halpha0 :
      ratFuncDerivation68 (alphaResidual810 (f.coeff 6) (g.coeff 8)) = 0 :=
    alphaResidual810_deriv_zero ratFuncDerivation68 (f.coeff 6)
      (g.coeff 8) hrow15
  have hbeta0 :
      ratFuncDerivation68
        (betaResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
          (g.coeff 7)) = 0 :=
    betaResidual810_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 6) (f.coeff 5) (g.coeff 7) hLconst (by simpa using hrow14)
  have hgamma0 :
      ratFuncDerivation68
        (gammaResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
          (f.coeff 4) (g.coeff 8) (g.coeff 6)) = 0 :=
    gammaResidual810_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 6) (f.coeff 5) (f.coeff 4) (g.coeff 8) (g.coeff 6)
      hLconst halpha0 (by simpa using hrow13)
  have hdelta0 :
      ratFuncDerivation68
        (deltaResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
          (f.coeff 4) (f.coeff 3) (g.coeff 8) (g.coeff 7)
          (g.coeff 5)) = 0 :=
    deltaResidual810_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 6) (f.coeff 5) (f.coeff 4) (f.coeff 3) (g.coeff 8)
      (g.coeff 7) (g.coeff 5) hLconst halpha0 hbeta0
      (by simpa using hrow12)
  have hepsilon0 :
      ratFuncDerivation68
        (epsilonResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
          (f.coeff 4) (f.coeff 3) (f.coeff 2) (g.coeff 8) (g.coeff 7)
          (g.coeff 6) (g.coeff 4)) = 0 :=
    epsilonResidual810_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 6) (f.coeff 5) (f.coeff 4) (f.coeff 3) (f.coeff 2)
      (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 4) hLconst halpha0
      hbeta0 hgamma0 (by simpa using hrow11)
  have hzeta0 :
      ratFuncDerivation68
        (zetaResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
          (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (g.coeff 8)
          (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 3)) = 0 :=
    zetaResidual810_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 6) (f.coeff 5) (f.coeff 4) (f.coeff 3) (f.coeff 2)
      (f.coeff 1) (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5)
      (g.coeff 3) hLconst halpha0 hbeta0 hgamma0 hdelta0
      (by simpa using hrow10)
  have heta0deriv :
      ratFuncDerivation68
        (etaResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
          (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
          (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
          (g.coeff 2)) = 0 :=
    etaResidual810_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 6) (f.coeff 5) (f.coeff 4) (f.coeff 3) (f.coeff 2)
      (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6)
      (g.coeff 5) (g.coeff 4) (g.coeff 2) hLconst halpha0 hbeta0
      hgamma0 hdelta0 hepsilon0 (by simpa using hrow9)
  have htheta0deriv :
      ratFuncDerivation68
        (thetaResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
          (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
          (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
          (g.coeff 3) (g.coeff 1)) = 0 :=
    thetaResidual810_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 6) (f.coeff 5) (f.coeff 4) (f.coeff 3) (f.coeff 2)
      (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6)
      (g.coeff 5) (g.coeff 4) (g.coeff 3) (g.coeff 1) hLconst halpha0
      hbeta0 hgamma0 hdelta0 hepsilon0 hzeta0 (by simpa using hrow8)
  have hiota0deriv :
      ratFuncDerivation68
        (iotaResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
          (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
          (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
          (g.coeff 3) (g.coeff 2) (g.coeff 0)) = 0 :=
    iotaResidual810_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 6) (f.coeff 5) (f.coeff 4) (f.coeff 3) (f.coeff 2)
      (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6)
      (g.coeff 5) (g.coeff 4) (g.coeff 3) (g.coeff 2) (g.coeff 0)
      hLconst halpha0 hbeta0 hgamma0 hdelta0 hepsilon0 hzeta0 heta0deriv
      (by simpa using hrow7)
  have hxi0deriv :
      ratFuncDerivation68
        (xiResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
          (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
          (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
          (g.coeff 3) (g.coeff 2) (g.coeff 1)) = 0 :=
    xiResidual810_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 6) (f.coeff 5) (f.coeff 4) (f.coeff 3) (f.coeff 2)
      (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6)
      (g.coeff 5) (g.coeff 4) (g.coeff 3) (g.coeff 2) (g.coeff 1)
      (g.coeff 0) hLconst halpha0 hbeta0 hgamma0 hdelta0 hepsilon0 hzeta0
      heta0deriv htheta0deriv hiota0deriv (by simpa using hrow8)
      (by simpa using hrow7) (by simpa using hrow6) (by simpa using hrow5)
      (by simpa using hrow3)
  obtain ⟨xi0, hxi0⟩ :
      ∃ a : k,
        xiResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
            (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
            (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
            (g.coeff 3) (g.coeff 2) (g.coeff 1) =
          algebraMap k (RatFunc k) a := by
    apply GCD369RatFuncConstantsOfPolynomialDerivative
      ratFuncDerivation46_polynomial
    simpa [ratFuncDerivation68, ratFuncDerivation46_apply] using
      hxi0deriv
  have hclear :
      algebraMap k[X] (RatFunc k)
          (localClearedFourteenthDefect810 h0 (p.coeff 7) (p.coeff 6)
            (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2)
            (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7) (q.coeff 6)
            (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda) =
        (8796093022208 : RatFunc k) * h ^ 98 *
          xiResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
            (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
            (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
            (g.coeff 3) (g.coeff 2) (g.coeff 1) := by
    have hF := fourteenthDefect_eq_clearedXi810 h a7 a6 a5 a4 a3 a2 a1 a0 b9
      b8 b7 b6 b5 b4 b3 b2 b1 (RatFunc.C lambda) hh (by convert hNrat)
    have hg9L : g.coeff 9 =
        depressedL810 h (octicDepressionR810 h a7) b9 := by
      dsimp only [g]
      rw [hg9]
      simp [depressedL810, octicDepressionR810, sourceToRatFunc68,
        sourceToRatFunc46, b9]
    simpa [localClearedFourteenthDefect810,
      localClearedFourteenthDefectCore810,
      localClearedFourteenthDefectBlock0_810,
      localClearedFourteenthDefectBlock1_810,
      localClearedFourteenthDefectBlock2_810,
      localClearedFourteenthDefectBlock3_810,
      localClearedFourteenthDefectBlock4_810,
      localClearedFourteenthDefectBlock5_810,
      localClearedFourteenthDefectBlock6_810,
      localClearedFourteenthDefectBlock7_810,
      localClearedFourteenthDefectBlock8_810,
      localClearedFourteenthDefectBlock9_810,
      localClearedFourteenthDefectBlock10_810,
      localClearedFourteenthDefectBlock11_810,
      map_sub, map_mul, map_pow,
      map_ofNat, map_neg, map_add, RatFunc.algebraMap_C, h, a7, a6, a5,
      a4, a3, a2, a1, a0, b8, b7, b6, b5, b4, b3, b2, b1, xiResidual810,
      alphaResidual810, betaResidual810, gammaResidual810,
      deltaResidual810, epsilonResidual810, zetaResidual810,
      etaResidual810, thetaResidual810, hf6, hf5, hf4, hf3, hf2, hf1,
      hf0, hg1, hg2, hg3, hg4, hg5, hg6, hg7, hg8', hg9L] using hF.symm
  have htarget :
      algebraMap k[X] (RatFunc k)
          (localClearedFourteenthDefect810 h0 (p.coeff 7) (p.coeff 6)
            (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2)
            (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7) (q.coeff 6)
            (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda) =
        algebraMap k[X] (RatFunc k)
          (Polynomial.C (8796093022208 * xi0) * h0 ^ 98) := by
    rw [hclear, hxi0]
    simp [h, map_mul, map_pow, RatFunc.algebraMap_C, map_ofNat]
    ring
  refine ⟨8796093022208 * xi0, ?_⟩
  exact IsFractionRing.injective k[X] (RatFunc k) htarget

end NonzeroFourteenthFaceClearing810

section ScaleZeroThirteenthDefect810

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false

/-! ## Degree-`4` source Jacobian row -/

/-- Source-facing degree-`3` Jacobian row of a normalized scale-zero
`(8,10)` pair. -/
theorem normalized810ScaleZero_fourteenthCoefficientJacobianRow
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    (p.coeff 3).derivative * q.coeff 1 +
        (p.coeff 2).derivative * (q.coeff 2 * Polynomial.C (2 : k)) +
        (p.coeff 1).derivative * (q.coeff 3 * Polynomial.C (3 : k)) +
        (p.coeff 0).derivative * (q.coeff 4 * Polynomial.C (4 : k)) -
      ((p.coeff 4 * Polynomial.C (4 : k)) * (q.coeff 0).derivative +
        (p.coeff 3 * Polynomial.C (3 : k)) * (q.coeff 1).derivative +
        (p.coeff 2 * Polynomial.C (2 : k)) * (q.coeff 2).derivative +
        p.coeff 1 * (q.coeff 3).derivative) =
      0 := by
  dsimp only
  rcases hsource with
    ⟨_hH, _hHdegree, hPdegree, hQdegree, _hp8, _hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
  have hp : p.natDegree = 8 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  simpa only [p, q] using fableScaleZero_fourteenthCoefficientJacobianRow_raw_810 hp hq hjac

/-- At scale zero the common core is constant, so the leading octic
coefficient of the degree-`3` row is a differential constant. -/
theorem scaleZero_fourteenthCoefficientJacobianRow_810
    {p q : k[X][X]} {j : k} {H : k[X]}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hHdegree : H.natDegree = 0)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5) :
    (p.coeff 3).derivative * q.coeff 1 +
        (p.coeff 2).derivative * (q.coeff 2 * Polynomial.C (2 : k)) +
        (p.coeff 1).derivative * (q.coeff 3 * Polynomial.C (3 : k)) +
        (p.coeff 0).derivative * (q.coeff 4 * Polynomial.C (4 : k)) -
      ((p.coeff 4 * Polynomial.C (4 : k)) * (q.coeff 0).derivative +
        (p.coeff 3 * Polynomial.C (3 : k)) * (q.coeff 1).derivative +
        (p.coeff 2 * Polynomial.C (2 : k)) * (q.coeff 2).derivative +
        p.coeff 1 * (q.coeff 3).derivative) =
      0 := by
  have hrow := fableScaleZero_fourteenthCoefficientJacobianRow_raw_810 hp hq hjac
  simpa using hrow

/-- Source-facing scale-zero collapse of the degree-`3` row. -/
theorem normalized810ScaleZero_fourteenthCoefficientJacobianRow_collapsed
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    (p.coeff 3).derivative * q.coeff 1 +
        (p.coeff 2).derivative * (q.coeff 2 * Polynomial.C (2 : k)) +
        (p.coeff 1).derivative * (q.coeff 3 * Polynomial.C (3 : k)) +
        (p.coeff 0).derivative * (q.coeff 4 * Polynomial.C (4 : k)) -
      ((p.coeff 4 * Polynomial.C (4 : k)) * (q.coeff 0).derivative +
        (p.coeff 3 * Polynomial.C (3 : k)) * (q.coeff 1).derivative +
        (p.coeff 2 * Polynomial.C (2 : k)) * (q.coeff 2).derivative +
        p.coeff 1 * (q.coeff 3).derivative) =
      0 := by
  dsimp only
  rcases hsource with
    ⟨_hH, hHdegree, hPdegree, hQdegree, hp8, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
  have hp : p.natDegree = 8 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  simpa only [p, q] using
    scaleZero_fourteenthCoefficientJacobianRow_810 hp hq hjac hHdegree
      (by simpa only [p] using hp8) (by simpa only [q] using hq10)


/-! ## Degree-`4` monic Jacobian row -/

/-- For a monic octic and a monic decic whose `z⁹` coefficient `L` is
already a differential constant, the degree-`3` Jacobian coefficient
is exactly
`4 T G' + 3 U F' + 2 V E' + W D'
- F U' - 2 E V' - 3 D W' - 4 C X'`.
Here `A = f.coeff 6`, `B = f.coeff 5`, `C = f.coeff 4`, `D = f.coeff 3`,
`E = f.coeff 2`, `F = f.coeff 1`, `G = f.coeff 0`, `L = g.coeff 9`,
`P = g.coeff 8`, `Q = g.coeff 7`, `R = g.coeff 6`, `S = g.coeff 5`,
`T = g.coeff 4`, `U = g.coeff 3`, `V = g.coeff 2`, `W = g.coeff 1`,
and `X = g.coeff 0`. -/
theorem scaleZero_monicOcticDecic_degree3Row_810
    {F : Type*} [Field F] [Algebra k F] [CharZero F]
    (d : Derivation k F F) (f g : F[X])
    (hf_high : ∀ n, 8 < n → f.coeff n = 0) (hf8 : f.coeff 8 = 1)
    (hf7 : f.coeff 7 = 0)
    (hg_high : ∀ n, 10 < n → g.coeff n = 0) (hg10 : g.coeff 10 = 1)
    (hL : d (g.coeff 9) = 0) :
    (differentialJacobian d f g).coeff 3 =
      (4 : F) * g.coeff 4 * d (f.coeff 0) +
        (3 : F) * g.coeff 3 * d (f.coeff 1) +
        (2 : F) * g.coeff 2 * d (f.coeff 2) +
        g.coeff 1 * d (f.coeff 3) -
          f.coeff 1 * d (g.coeff 3) -
          (2 : F) * f.coeff 2 * d (g.coeff 2) -
          (3 : F) * f.coeff 3 * d (g.coeff 1) -
          (4 : F) * f.coeff 4 * d (g.coeff 0) :=
  differentialJacobian_coeff_3_monicOcticDecic d f g hf_high hf8 hf7
    hg_high hg10 hL

/-- The same row integrates: if the degree-`8`, degree-`7`, degree-`6`,
degree-`5`, and degree-`3` Jacobian rows vanish, `L` is constant, and the
residuals `α, β, γ, δ, ε, ζ, η, θ, ι` are constant, then the next
residual `ξ` is a differential constant. -/
theorem scaleZero_xiResidual_deriv_zero_810
    {F : Type*} [Field F] [Algebra k F] [CharZero F]
    (d : Derivation k F F)
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 X0 : F)
    (hL : d L = 0)
    (halpha : d (alphaResidual810 A P) = 0)
    (hbeta : d (betaResidual810 L A B Q) = 0)
    (hgamma : d (gammaResidual810 L A B C0 P R) = 0)
    (hdelta : d (deltaResidual810 L A B C0 D0 P Q S0) = 0)
    (hepsilon : d (epsilonResidual810 L A B C0 D0 E0 P Q R T0) = 0)
    (hzeta : d (zetaResidual810 L A B C0 D0 E0 F0 P Q R S0 U0) = 0)
    (heta : d (etaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 V0) = 0)
    (htheta : d (thetaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 W0) = 0)
    (hiota : d (iotaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 X0) = 0)
    (hrow8 : (9 : F) * L * d G0 + (8 : F) * P * d F0 +
        (7 : F) * Q * d E0 + (6 : F) * R * d D0 +
        (5 : F) * S0 * d C0 + (4 : F) * T0 * d B +
        (3 : F) * U0 * d A -
        F0 * d P - (2 : F) * E0 * d Q -
        (3 : F) * D0 * d R - (4 : F) * C0 * d S0 -
        (5 : F) * B * d T0 - (6 : F) * A * d U0 -
        (8 : F) * d W0 = 0)
    (hrow7 : (8 : F) * P * d G0 + (7 : F) * Q * d F0 +
        (6 : F) * R * d E0 + (5 : F) * S0 * d D0 +
        (4 : F) * T0 * d C0 + (3 : F) * U0 * d B +
        (2 : F) * V0 * d A -
        F0 * d Q - (2 : F) * E0 * d R -
        (3 : F) * D0 * d S0 - (4 : F) * C0 * d T0 -
        (5 : F) * B * d U0 - (6 : F) * A * d V0 -
        (8 : F) * d X0 = 0)
    (hrow6 : (7 : F) * Q * d G0 + (6 : F) * R * d F0 +
        (5 : F) * S0 * d E0 + (4 : F) * T0 * d D0 +
        (3 : F) * U0 * d C0 + (2 : F) * V0 * d B +
        W0 * d A -
        F0 * d R - (2 : F) * E0 * d S0 -
        (3 : F) * D0 * d T0 - (4 : F) * C0 * d U0 -
        (5 : F) * B * d V0 - (6 : F) * A * d W0 = 0)
    (hrow5 : (6 : F) * R * d G0 + (5 : F) * S0 * d F0 +
        (4 : F) * T0 * d E0 + (3 : F) * U0 * d D0 +
        (2 : F) * V0 * d C0 + W0 * d B -
        F0 * d S0 - (2 : F) * E0 * d T0 -
        (3 : F) * D0 * d U0 - (4 : F) * C0 * d V0 -
        (5 : F) * B * d W0 - (6 : F) * A * d X0 = 0)
    (hrow : (4 : F) * T0 * d G0 + (3 : F) * U0 * d F0 +
        (2 : F) * V0 * d E0 + W0 * d D0 -
        F0 * d U0 - (2 : F) * E0 * d V0 -
        (3 : F) * D0 * d W0 - (4 : F) * C0 * d X0 = 0) :
    d (xiResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0) = 0 :=
  xiResidual810_deriv_zero d L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 X0
    hL halpha hbeta hgamma hdelta hepsilon hzeta heta htheta hiota hrow8
    hrow7 hrow6 hrow5 hrow

/-! ## Cleared weight-`98` defect on a constant square core -/

/-- On a constant square core the source discriminator is a scalar times
`h⁹`, so the existing ninth-power identities apply with a constant
square root on both the vanishing face `λ = 0` and the nonzero
constant face. -/
theorem scaleZero_thirteenthClearedDefect_exists_C_810
    {p q : k[X][X]} {j t : k} {H : k[X]}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (ht : t ≠ 0) (hH : H = (Polynomial.C t) ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5) :
    ∃ (lambda eta : k),
      (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
          Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
      localClearedFourteenthDefect810 (Polynomial.C t) (p.coeff 7) (p.coeff 6)
          (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1)
          (p.coeff 0) (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
          (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda =
        Polynomial.C eta * (Polynomial.C t) ^ 98 := by
  have hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hD
  obtain ⟨lambda, hN⟩ :=
    scaleZero_discriminator_eq_C_mul_ninthPower_810 hp hq hjac ht hH hp8 hq10
  have hh0 : (Polynomial.C t : k[X]) ≠ 0 := Polynomial.C_ne_zero.mpr ht
  obtain ⟨eta, heta⟩ :=
    nonzeroFace810_fourteenthDefectPowerRelation p q H (Polynomial.C t) j lambda
      hp hq hh0 hH hp8 hq10 hN hD
  exact ⟨lambda, eta, hN, heta⟩

/-- Aligned constant face `N = 0`: the same degree-`3` clearing applies
with `λ = 0`, and the weight-`98` defect is still a ground constant.
This does not close the face. -/
theorem scaleZero_alignedThirteenthClearedDefect_exists_C_810
    {p q : k[X][X]} {j t : k} {H : k[X]}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (ht : t ≠ 0) (hH : H = (Polynomial.C t) ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 = 0) :
    ∃ eta : k,
      localClearedFourteenthDefect810 (Polynomial.C t) (p.coeff 7) (p.coeff 6)
          (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1)
          (p.coeff 0) (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
          (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1) 0 =
        Polynomial.C eta * (Polynomial.C t) ^ 98 := by
  have hh0 : (Polynomial.C t : k[X]) ≠ 0 := Polynomial.C_ne_zero.mpr ht
  have hN0 :
      (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
        Polynomial.C (0 : k) * (Polynomial.C t) ^ 9 := by
    simpa [map_zero, zero_mul] using hN
  obtain ⟨eta, heta⟩ :=
    nonzeroFace810_fourteenthDefectPowerRelation p q H (Polynomial.C t) j 0
      hp hq hh0 hH hp8 hq10 hN0 hD
  exact ⟨eta, heta⟩

/-- Nonzero constant face: `N` is a nonzero scalar times `h⁹`, and the
weight-`98` defect is a ground constant.  This does not close the
face. -/
theorem scaleZero_nonzeroThirteenthClearedDefect_exists_C_810
    {p q : k[X][X]} {j t lambda : k} {H : k[X]}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (ht : t ≠ 0) (_hlambda : lambda ≠ 0)
    (hH : H = (Polynomial.C t) ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * (Polynomial.C t) ^ 9) :
    ∃ eta : k,
      localClearedFourteenthDefect810 (Polynomial.C t) (p.coeff 7) (p.coeff 6)
          (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1)
          (p.coeff 0) (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
          (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda =
        Polynomial.C eta * (Polynomial.C t) ^ 98 := by
  have hh0 : (Polynomial.C t : k[X]) ≠ 0 := Polynomial.C_ne_zero.mpr ht
  obtain ⟨eta, heta⟩ :=
    nonzeroFace810_fourteenthDefectPowerRelation p q H (Polynomial.C t) j lambda
      hp hq hh0 hH hp8 hq10 hN hD
  exact ⟨eta, heta⟩

variable [IsAlgClosed k]

/-- Source-facing thirteenth residual packet for a normalized scale-zero
`(8,10)` pair: after a square root of the core, the cleared weight-`98`
defect is a ground-field constant. -/
theorem normalized810ScaleZero_exists_thirteenthClearedDefect
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    ∃ (t lambda eta : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7 *
            H -
        (4 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 =
        Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
      localClearedFourteenthDefect810 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 1)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 0)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 1)
          lambda =
        Polynomial.C eta * (Polynomial.C t) ^ 98 := by
  rcases hsource with
    ⟨hH, hHdegree, hPdegree, hQdegree, hp8, hq10, hKeller⟩
  obtain ⟨t, ht, hHsq⟩ :=
    scaleZero_exists_constantSquareRoot_810 hH hHdegree
  let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
  have hp : p.natDegree = 8 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hjac
  obtain ⟨lambda, eta, hN, hX⟩ :=
    scaleZero_thirteenthClearedDefect_exists_C_810 hp hq hD ht hHsq
      (by simpa only [p] using hp8) (by simpa only [q] using hq10)
  exact ⟨t, lambda, eta, ht, hHsq, by simpa only [p, q] using hN,
    by simpa only [p, q] using hX⟩

/-- The weight-`98` defect is a literal ground-field constant. -/
theorem normalized810ScaleZero_thirteenthClearedDefect_exists_C
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    ∃ (t lambda eta : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      localClearedFourteenthDefect810 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 1)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 0)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 1)
          lambda =
        Polynomial.C eta := by
  obtain ⟨t, lambda, eta, ht, hHsq, _hN, hX⟩ :=
    normalized810ScaleZero_exists_thirteenthClearedDefect hsource
  refine ⟨t, lambda, eta * t ^ 98, ht, hHsq, ?_⟩
  have hconst :
      localClearedFourteenthDefect810 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 1)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 0)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 1)
          lambda =
        Polynomial.C (eta * t ^ 98) := by
    rw [hX, ← Polynomial.C_pow]
    exact (map_mul (Polynomial.C : k →+* k[X]) eta (t ^ 98)).symm
  exact hconst

/-- Newton degree of the thirteenth cleared octic/decic defect at scale
zero. -/
theorem normalized810ScaleZero_thirteenthClearedDefect_natDegree_le_zero
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    ∃ (t lambda : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      (localClearedFourteenthDefect810 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 1)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 0)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 1)
          lambda).natDegree ≤ 0 := by
  obtain ⟨t, lambda, eta, ht, hHsq, hX⟩ :=
    normalized810ScaleZero_thirteenthClearedDefect_exists_C hsource
  refine ⟨t, lambda, ht, hHsq, ?_⟩
  rw [hX]
  exact (natDegree_C eta).le

/-- Aligned/nonzero split of the scale-zero thirteenth defect: both constant
faces of `N` make the weight-`98` defect a ground constant, and neither
face is excluded or claimed closed. -/
theorem normalized810ScaleZero_thirteenthClearedDefectFirstFace
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    let N :=
      (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9
    ∃ t : k, t ≠ 0 ∧ H = (Polynomial.C t) ^ 2 ∧
      ((N = 0 ∧
          ∃ eta : k,
            localClearedFourteenthDefect810 (Polynomial.C t) (p.coeff 7)
                (p.coeff 6) (p.coeff 5) (p.coeff 4) (p.coeff 3)
                (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 8)
                (q.coeff 7) (q.coeff 6) (q.coeff 5) (q.coeff 4)
                (q.coeff 3) (q.coeff 2) (q.coeff 1) 0 =
              Polynomial.C eta * (Polynomial.C t) ^ 98) ∨
        ∃ lambda eta : k, lambda ≠ 0 ∧
          N = Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
          localClearedFourteenthDefect810 (Polynomial.C t) (p.coeff 7)
              (p.coeff 6) (p.coeff 5) (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 8)
              (q.coeff 7) (q.coeff 6) (q.coeff 5) (q.coeff 4)
              (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda =
            Polynomial.C eta * (Polynomial.C t) ^ 98) := by
  dsimp only
  obtain ⟨t, lambda, eta, ht, hHsq, hN, hX⟩ :=
    normalized810ScaleZero_exists_thirteenthClearedDefect hsource
  refine ⟨t, ht, hHsq, ?_⟩
  by_cases hlambda : lambda = 0
  · left
    refine ⟨?_, eta, ?_⟩
    · simpa [hlambda, map_zero, zero_mul] using hN
    · simpa [hlambda] using hX
  · exact Or.inr ⟨lambda, eta, hlambda, hN, hX⟩

/-- Explicit zero/nonzero constant branches of both the discriminator and
the weight-`98` defect.  Neither vanishing face is claimed closed. -/
theorem normalized810ScaleZero_thirteenthClearedDefectBranches
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    ∃ (t lambda eta : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      let N :=
        (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9
      let X :=
        localClearedFourteenthDefect810 (Polynomial.C t)
          (p.coeff 7) (p.coeff 6) (p.coeff 5) (p.coeff 4) (p.coeff 3)
          (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
          (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
          (q.coeff 1)
          lambda
      N = Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
      X = Polynomial.C eta ∧
      (lambda = 0 ∧ N = 0 ∨
        lambda ≠ 0 ∧ N = Polynomial.C (lambda * t ^ 9)) ∧
      (eta = 0 ∧ X = 0 ∨
        eta ≠ 0 ∧ X = Polynomial.C eta) := by
  dsimp only
  obtain ⟨t, lambda, eta0, ht, hHsq, hN, hXpow⟩ :=
    normalized810ScaleZero_exists_thirteenthClearedDefect hsource
  let eta : k := eta0 * t ^ 98
  have hX :
      localClearedFourteenthDefect810 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 1)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 0)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 1)
          lambda =
        Polynomial.C eta := by
    rw [hXpow, ← Polynomial.C_pow]
    exact (map_mul (Polynomial.C : k →+* k[X]) eta0 (t ^ 98)).symm
  refine ⟨t, lambda, eta, ht, hHsq, hN, hX, ?_, ?_⟩
  · by_cases hlambda : lambda = 0
    · left
      refine ⟨hlambda, ?_⟩
      simpa only [hlambda, Polynomial.C_0, zero_mul] using hN
    · right
      refine ⟨hlambda, ?_⟩
      have hNconst :
          (5 : k[X]) *
                ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7 *
                  H -
              (4 : k[X]) *
                ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 =
            Polynomial.C (lambda * t ^ 9) := by
        rw [hN, ← Polynomial.C_pow]
        exact (map_mul (Polynomial.C : k →+* k[X]) lambda (t ^ 9)).symm
      exact hNconst
  · by_cases heta : eta = 0
    · left
      refine ⟨heta, ?_⟩
      simpa only [heta, Polynomial.C_0] using hX
    · exact Or.inr ⟨heta, hX⟩

/-- Source-facing aligned packet: if the discriminator vanishes, the
weight-`98` defect is still a ground constant.  The face is not
closed. -/
theorem normalized810ScaleZero_aligned_exists_thirteenthClearedDefect
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0)
    (hNzero :
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7 *
            H -
        (4 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 =
        0) :
    ∃ (t eta : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      localClearedFourteenthDefect810 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 1)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 0)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 1)
          0 =
        Polynomial.C eta * (Polynomial.C t) ^ 98 := by
  rcases hsource with
    ⟨hH, hHdegree, hPdegree, hQdegree, hp8, hq10, hKeller⟩
  obtain ⟨t, ht, hHsq⟩ :=
    scaleZero_exists_constantSquareRoot_810 hH hHdegree
  let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
  have hp : p.natDegree = 8 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hjac
  obtain ⟨eta, hX⟩ :=
    scaleZero_alignedThirteenthClearedDefect_exists_C_810 hp hq hD ht hHsq
      (by simpa only [p] using hp8) (by simpa only [q] using hq10)
      (by simpa only [p, q] using hNzero)
  exact ⟨t, eta, ht, hHsq, by simpa only [p, q] using hX⟩

/-- Source-facing nonzero packet: if the discriminator is a nonzero
ground constant, the weight-`98` defect is still a ground constant.
The face is not closed. -/
theorem normalized810ScaleZero_nonzero_exists_thirteenthClearedDefect
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0)
    (hNnonzero :
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7 *
            H -
        (4 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 ≠
        0) :
    ∃ (t lambda eta : k),
      t ≠ 0 ∧
      lambda ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7 *
            H -
        (4 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 =
        Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
      localClearedFourteenthDefect810 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 1)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 0)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 1)
          lambda =
        Polynomial.C eta * (Polynomial.C t) ^ 98 := by
  obtain ⟨t, lambda, eta, ht, hHsq, hN, hX⟩ :=
    normalized810ScaleZero_exists_thirteenthClearedDefect hsource
  have hlambda : lambda ≠ 0 := by
    intro h0
    apply hNnonzero
    simpa [h0, map_zero, zero_mul] using hN
  exact ⟨t, lambda, eta, ht, hlambda, hHsq, hN, hX⟩

end ScaleZeroThirteenthDefect810


#print axioms fableScaleZero_fourteenthCoefficientJacobianRow_raw_810
#print axioms scaleZero_fourteenthCoefficientJacobianRow_810
#print axioms normalized810ScaleZero_fourteenthCoefficientJacobianRow
#print axioms normalized810ScaleZero_fourteenthCoefficientJacobianRow_collapsed
#print axioms differentialJacobian_coeff_3_monicOcticDecic
#print axioms scaleZero_monicOcticDecic_degree3Row_810
#print axioms xiResidual810_deriv_zero
#print axioms scaleZero_xiResidual_deriv_zero_810
#print axioms fourteenthDefect_eq_clearedXi810
#print axioms nonzeroFace810_fourteenthDefectPowerRelation
#print axioms scaleZero_thirteenthClearedDefect_exists_C_810
#print axioms scaleZero_alignedThirteenthClearedDefect_exists_C_810
#print axioms scaleZero_nonzeroThirteenthClearedDefect_exists_C_810
#print axioms normalized810ScaleZero_exists_thirteenthClearedDefect
#print axioms normalized810ScaleZero_thirteenthClearedDefect_exists_C
#print axioms normalized810ScaleZero_thirteenthClearedDefect_natDegree_le_zero
#print axioms normalized810ScaleZero_thirteenthClearedDefectFirstFace
#print axioms normalized810ScaleZero_thirteenthClearedDefectBranches
#print axioms normalized810ScaleZero_aligned_exists_thirteenthClearedDefect
#print axioms normalized810ScaleZero_nonzero_exists_thirteenthClearedDefect

end Max11DegreeRoutes
