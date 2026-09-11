import Fable810ScaleZeroTwelfthDefectScratch

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
