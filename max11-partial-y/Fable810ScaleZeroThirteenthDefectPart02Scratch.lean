import Fable810ScaleZeroThirteenthDefectPart01Scratch

/-! Part 2 of 37 of `Fable810ScaleZeroThirteenthDefectScratch`, split so that no single module elaborates them all
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


end Depression810FourteenthClearing
end Max11DegreeRoutes
end
