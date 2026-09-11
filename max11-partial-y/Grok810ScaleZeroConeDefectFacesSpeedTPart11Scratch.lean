import Grok810ScaleZeroConeDefectFacesSpeedTPart01Scratch

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## Algebra map of the polynomial first integrals -/

section DefectAlgebraMap810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
/-- Field-level integrated `ξ`. -/
def degreeZeroXiIntegrated810
    {F : Type*} [Field F] [CharZero F]
    (L A B C0 D0 E0 F0 G0 beta gamma delta epsilon zeta eta theta : F) : F :=
  -(165 / 65536 : F) * A ^ 7
    + (1925 / 32768 : F) * (A ^ 4 * B ^ 2)
    + (385 / 16384 : F) * (A ^ 5 * C0)
    + (7245 / 524288 : F) * L * (A ^ 5 * B)
    - (35 / 1024 : F) * (A * B ^ 4)
    - (105 / 512 : F) * (A ^ 2 * B ^ 2 * C0)
    - (315 / 8192 : F) * L * (A ^ 2 * B ^ 3)
    - (35 / 512 : F) * (A ^ 3 * C0 ^ 2)
    - (525 / 4096 : F) * (A ^ 3 * B * D0)
    - (315 / 4096 : F) * L * (A ^ 3 * B * C0)
    - (245 / 8192 : F) * (A ^ 4 * E0)
    - (4725 / 262144 : F) * L * (A ^ 4 * D0)
    + (357 / 16384 : F) * beta * (A ^ 4 * B)
    + (9 / 1024 : F) * gamma * A ^ 5
    + (45 / 512 : F) * (B ^ 2 * C0 ^ 2)
    + (55 / 1024 : F) * (B ^ 3 * D0)
    + (63 / 2048 : F) * L * (B ^ 3 * C0)
    + (15 / 256 : F) * (A * C0 ^ 3)
    + (165 / 512 : F) * (A * B * C0 * D0)
    + (189 / 2048 : F) * L * (A * B * C0 ^ 2)
    + (75 / 512 : F) * (A * B ^ 2 * E0)
    + (693 / 8192 : F) * L * (A * B ^ 2 * D0)
    - (63 / 2048 : F) * beta * (A * B ^ 3)
    + (75 / 1024 : F) * (A ^ 2 * D0 ^ 2)
    + (75 / 512 : F) * (A ^ 2 * C0 * E0)
    + (693 / 8192 : F) * L * (A ^ 2 * C0 * D0)
    + (135 / 1024 : F) * (A ^ 2 * B * F0)
    + (315 / 4096 : F) * L * (A ^ 2 * B * E0)
    - (189 / 2048 : F) * beta * (A ^ 2 * B * C0)
    - (45 / 512 : F) * gamma * (A ^ 2 * B ^ 2)
    + (5 / 128 : F) * (A ^ 3 * G0)
    + (189 / 8192 : F) * L * (A ^ 3 * F0)
    - (231 / 8192 : F) * beta * (A ^ 3 * D0)
    - (15 / 256 : F) * gamma * (A ^ 3 * C0)
    - (165 / 2048 : F) * delta * (A ^ 3 * B)
    - (3 / 128 : F) * epsilon * A ^ 4
    - (15 / 128 : F) * (C0 * D0 ^ 2)
    - (15 / 128 : F) * (C0 ^ 2 * E0)
    - (63 / 1024 : F) * L * (C0 ^ 2 * D0)
    - (25 / 128 : F) * (B * D0 * E0)
    - (27 / 512 : F) * L * (B * D0 ^ 2)
    - (25 / 128 : F) * (B * C0 * F0)
    - (27 / 256 : F) * L * (B * C0 * E0)
    + (7 / 128 : F) * beta * (B * C0 ^ 2)
    - (5 / 64 : F) * (B ^ 2 * G0)
    - (45 / 1024 : F) * L * (B ^ 2 * F0)
    + (49 / 1024 : F) * beta * (B ^ 2 * D0)
    + (3 / 32 : F) * gamma * (B ^ 2 * C0)
    + (5 / 128 : F) * delta * B ^ 3
    - (5 / 64 : F) * (A * E0 ^ 2)
    - (5 / 32 : F) * (A * D0 * F0)
    - (45 / 512 : F) * L * (A * D0 * E0)
    - (5 / 32 : F) * (A * C0 * G0)
    - (45 / 512 : F) * L * (A * C0 * F0)
    + (49 / 512 : F) * beta * (A * C0 * D0)
    + (3 / 32 : F) * gamma * (A * C0 ^ 2)
    - (9 / 128 : F) * L * (A * B * G0)
    + (21 / 256 : F) * beta * (A * B * E0)
    + (21 / 128 : F) * gamma * (A * B * D0)
    + (15 / 64 : F) * delta * (A * B * C0)
    + (1 / 8 : F) * epsilon * (A * B ^ 2)
    + (35 / 1024 : F) * beta * (A ^ 2 * F0)
    + (9 / 128 : F) * gamma * (A ^ 2 * E0)
    + (105 / 1024 : F) * delta * (A ^ 2 * D0)
    + (1 / 8 : F) * epsilon * (A ^ 2 * C0)
    + (15 / 128 : F) * zeta * (A ^ 2 * B)
    + (1 / 32 : F) * eta * A ^ 3
    + (5 / 32 : F) * F0 ^ 2
    + (5 / 16 : F) * (E0 * G0)
    + (9 / 64 : F) * L * (E0 * F0)
    + (9 / 64 : F) * L * (D0 * G0)
    - (7 / 64 : F) * beta * (D0 * E0)
    - (3 / 32 : F) * gamma * D0 ^ 2
    - (7 / 64 : F) * beta * (C0 * F0)
    - (3 / 16 : F) * gamma * (C0 * E0)
    - (15 / 64 : F) * delta * (C0 * D0)
    - (1 / 8 : F) * epsilon * C0 ^ 2
    - (3 / 32 : F) * gamma * (B * F0)
    - (5 / 32 : F) * delta * (B * E0)
    - (3 / 16 : F) * epsilon * (B * D0)
    - (3 / 16 : F) * zeta * (B * C0)
    - (1 / 16 : F) * eta * B ^ 2
    - (5 / 64 : F) * delta * (A * F0)
    - (1 / 8 : F) * epsilon * (A * E0)
    - (9 / 64 : F) * zeta * (A * D0)
    - (1 / 8 : F) * eta * (A * C0)
    - (1 / 16 : F) * theta * (A * B)
    + (1 / 2 : F) * epsilon * G0
    + (3 / 8 : F) * zeta * F0
    + (1 / 4 : F) * eta * E0
    + (1 / 8 : F) * theta * D0

set_option maxHeartbeats 64000000 in
/-- Field-level integrated `μ`. -/
def degreeZeroMuIntegrated810
    {F : Type*} [Field F] [CharZero F]
    (L A B C0 D0 E0 F0 G0 beta gamma delta epsilon zeta eta theta : F) : F :=
  (385 / 65536 : F) * A ^ 6
    - (385 / 4096 : F) * (A ^ 3 * B ^ 2)
    - (385 / 8192 : F) * (A ^ 4 * C0)
    - (7245 / 262144 : F) * L * (A ^ 4 * B)
    + (35 / 2048 : F) * B ^ 4
    + (105 / 512 : F) * (A * B ^ 2 * C0)
    + (315 / 8192 : F) * L * (A * B ^ 3)
    + (105 / 1024 : F) * (A ^ 2 * C0 ^ 2)
    + (105 / 512 : F) * (A ^ 2 * B * D0)
    + (945 / 8192 : F) * L * (A ^ 2 * B * C0)
    + (35 / 512 : F) * (A ^ 3 * E0)
    + (315 / 8192 : F) * L * (A ^ 3 * D0)
    - (357 / 8192 : F) * beta * (A ^ 3 * B)
    - (45 / 2048 : F) * gamma * A ^ 4
    - (5 / 128 : F) * C0 ^ 3
    - (15 / 64 : F) * (B * C0 * D0)
    - (63 / 1024 : F) * L * (B * C0 ^ 2)
    - (15 / 128 : F) * (B ^ 2 * E0)
    - (63 / 1024 : F) * L * (B ^ 2 * D0)
    + (21 / 1024 : F) * beta * B ^ 3
    - (15 / 128 : F) * (A * D0 ^ 2)
    - (15 / 64 : F) * (A * C0 * E0)
    - (63 / 512 : F) * L * (A * C0 * D0)
    - (15 / 64 : F) * (A * B * F0)
    - (63 / 512 : F) * L * (A * B * E0)
    + (63 / 512 : F) * beta * (A * B * C0)
    + (15 / 128 : F) * gamma * (A * B ^ 2)
    - (15 / 128 : F) * (A ^ 2 * G0)
    - (63 / 1024 : F) * L * (A ^ 2 * F0)
    + (63 / 1024 : F) * beta * (A ^ 2 * D0)
    + (15 / 128 : F) * gamma * (A ^ 2 * C0)
    + (165 / 1024 : F) * delta * (A ^ 2 * B)
    + (1 / 16 : F) * epsilon * A ^ 3
    + (5 / 32 : F) * E0 ^ 2
    + (5 / 16 : F) * (D0 * F0)
    + (9 / 64 : F) * L * (D0 * E0)
    + (5 / 16 : F) * (C0 * G0)
    + (9 / 64 : F) * L * (C0 * F0)
    - (7 / 64 : F) * beta * (C0 * D0)
    - (3 / 32 : F) * gamma * C0 ^ 2
    + (9 / 64 : F) * L * (B * G0)
    - (7 / 64 : F) * beta * (B * E0)
    - (3 / 16 : F) * gamma * (B * D0)
    - (15 / 64 : F) * delta * (B * C0)
    - (1 / 8 : F) * epsilon * B ^ 2
    - (7 / 64 : F) * beta * (A * F0)
    - (3 / 16 : F) * gamma * (A * E0)
    - (15 / 64 : F) * delta * (A * D0)
    - (1 / 4 : F) * epsilon * (A * C0)
    - (15 / 64 : F) * zeta * (A * B)
    - (3 / 32 : F) * eta * A ^ 2
    + (3 / 4 : F) * gamma * G0
    + (5 / 8 : F) * delta * F0
    + (1 / 2 : F) * epsilon * E0
    + (3 / 8 : F) * zeta * D0
    + (1 / 4 : F) * eta * C0
    + (1 / 8 : F) * theta * B

set_option maxHeartbeats 64000000 in
/-- Field-level integrated `ο`. -/
def degreeZeroOmicronIntegrated810
    {F : Type*} [Field F] [CharZero F]
    (L A B C0 D0 E0 F0 G0 beta gamma delta epsilon zeta eta theta : F) : F :=
  -(12705 / 1048576 : F) * (A ^ 6 * B)
    - (34155 / 33554432 : F) * L * A ^ 7
    + (3745 / 65536 : F) * (A ^ 3 * B ^ 3)
    + (1365 / 16384 : F) * (A ^ 4 * B * C0)
    + (103005 / 4194304 : F) * L * (A ^ 4 * B ^ 2)
    + (525 / 32768 : F) * (A ^ 5 * D0)
    + (19845 / 2097152 : F) * L * (A ^ 5 * C0)
    - (3927 / 2097152 : F) * beta * A ^ 6
    - (21 / 4096 : F) * B ^ 5
    - (105 / 1024 : F) * (A * B ^ 3 * C0)
    - (945 / 65536 : F) * L * (A * B ^ 4)
    - (2475 / 16384 : F) * (A ^ 2 * B * C0 ^ 2)
    - (2475 / 16384 : F) * (A ^ 2 * B ^ 2 * D0)
    - (11151 / 131072 : F) * L * (A ^ 2 * B ^ 2 * C0)
    - (795 / 8192 : F) * (A ^ 3 * C0 * D0)
    - (3591 / 131072 : F) * L * (A ^ 3 * C0 ^ 2)
    - (725 / 8192 : F) * (A ^ 3 * B * E0)
    - (3591 / 65536 : F) * L * (A ^ 3 * B * D0)
    + (4095 / 131072 : F) * beta * (A ^ 3 * B ^ 2)
    - (305 / 16384 : F) * (A ^ 4 * F0)
    - (3087 / 262144 : F) * L * (A ^ 4 * E0)
    + (1953 / 131072 : F) * beta * (A ^ 4 * C0)
    + (495 / 16384 : F) * gamma * (A ^ 4 * B)
    + (1089 / 131072 : F) * delta * A ^ 5
    + (45 / 1024 : F) * (B * C0 ^ 3)
    + (135 / 1024 : F) * (B ^ 2 * C0 * D0)
    + (567 / 16384 : F) * L * (B ^ 2 * C0 ^ 2)
    + (5 / 128 : F) * (B ^ 3 * E0)
    + (189 / 8192 : F) * L * (B ^ 3 * D0)
    - (189 / 32768 : F) * beta * B ^ 4
    + (135 / 1024 : F) * (A * C0 ^ 2 * D0)
    + (189 / 8192 : F) * L * (A * C0 ^ 3)
    + (135 / 1024 : F) * (A * B * D0 ^ 2)
    + (15 / 64 : F) * (A * B * C0 * E0)
    + (567 / 4096 : F) * L * (A * B * C0 * D0)
    + (105 / 1024 : F) * (A * B ^ 2 * F0)
    + (63 / 1024 : F) * L * (A * B ^ 2 * E0)
    - (567 / 8192 : F) * beta * (A * B ^ 2 * C0)
    - (45 / 1024 : F) * gamma * (A * B ^ 3)
    + (225 / 2048 : F) * (A ^ 2 * D0 * E0)
    + (135 / 4096 : F) * L * (A ^ 2 * D0 ^ 2)
    + (195 / 2048 : F) * (A ^ 2 * C0 * F0)
    + (477 / 8192 : F) * L * (A ^ 2 * C0 * E0)
    - (273 / 8192 : F) * beta * (A ^ 2 * C0 ^ 2)
    + (165 / 2048 : F) * (A ^ 2 * B * G0)
    + (207 / 4096 : F) * L * (A ^ 2 * B * F0)
    - (273 / 4096 : F) * beta * (A ^ 2 * B * D0)
    - (261 / 2048 : F) * gamma * (A ^ 2 * B * C0)
    - (45 / 512 : F) * delta * (A ^ 2 * B ^ 2)
    + (99 / 8192 : F) * L * (A ^ 3 * G0)
    - (147 / 8192 : F) * beta * (A ^ 3 * E0)
    - (81 / 2048 : F) * gamma * (A ^ 3 * D0)
    - (225 / 4096 : F) * delta * (A ^ 3 * C0)
    - (33 / 512 : F) * epsilon * (A ^ 3 * B)
    - (495 / 32768 : F) * zeta * A ^ 4
    - (5 / 128 : F) * D0 ^ 3
    - (25 / 128 : F) * (C0 * D0 * E0)
    - (27 / 512 : F) * L * (C0 * D0 ^ 2)
    - (5 / 64 : F) * (C0 ^ 2 * F0)
    - (45 / 1024 : F) * L * (C0 ^ 2 * E0)
    + (7 / 512 : F) * beta * C0 ^ 3
    - (5 / 64 : F) * (B * E0 ^ 2)
    - (5 / 32 : F) * (B * D0 * F0)
    - (45 / 512 : F) * L * (B * D0 * E0)
    - (15 / 128 : F) * (B * C0 * G0)
    - (9 / 128 : F) * L * (B * C0 * F0)
    + (21 / 256 : F) * beta * (B * C0 * D0)
    + (9 / 128 : F) * gamma * (B * C0 ^ 2)
    - (27 / 1024 : F) * L * (B ^ 2 * G0)
    + (35 / 1024 : F) * beta * (B ^ 2 * E0)
    + (9 / 128 : F) * gamma * (B ^ 2 * D0)
    + (45 / 512 : F) * delta * (B ^ 2 * C0)
    + (1 / 32 : F) * epsilon * B ^ 3
    - (15 / 128 : F) * (A * E0 * F0)
    - (9 / 256 : F) * L * (A * E0 ^ 2)
    - (15 / 128 : F) * (A * D0 * G0)
    - (9 / 128 : F) * L * (A * D0 * F0)
    + (21 / 512 : F) * beta * (A * D0 ^ 2)
    - (27 / 512 : F) * L * (A * C0 * G0)
    + (35 / 512 : F) * beta * (A * C0 * E0)
    + (9 / 64 : F) * gamma * (A * C0 * D0)
    + (45 / 512 : F) * delta * (A * C0 ^ 2)
    + (7 / 128 : F) * beta * (A * B * F0)
    + (15 / 128 : F) * gamma * (A * B * E0)
    + (45 / 256 : F) * delta * (A * B * D0)
    + (3 / 16 : F) * epsilon * (A * B * C0)
    + (45 / 512 : F) * zeta * (A * B ^ 2)
    + (15 / 512 : F) * gamma * (A ^ 2 * F0)
    + (15 / 256 : F) * delta * (A ^ 2 * E0)
    + (21 / 256 : F) * epsilon * (A ^ 2 * D0)
    + (81 / 1024 : F) * zeta * (A ^ 2 * C0)
    + (33 / 512 : F) * eta * (A ^ 2 * B)
    + (11 / 1024 : F) * theta * A ^ 3
    + (5 / 16 : F) * (F0 * G0)
    + (9 / 128 : F) * L * F0 ^ 2
    + (9 / 64 : F) * L * (E0 * G0)
    - (7 / 128 : F) * beta * E0 ^ 2
    - (7 / 64 : F) * beta * (D0 * F0)
    - (3 / 16 : F) * gamma * (D0 * E0)
    - (15 / 128 : F) * delta * D0 ^ 2
    - (3 / 32 : F) * gamma * (C0 * F0)
    - (5 / 32 : F) * delta * (C0 * E0)
    - (3 / 16 : F) * epsilon * (C0 * D0)
    - (9 / 128 : F) * zeta * C0 ^ 2
    - (5 / 64 : F) * delta * (B * F0)
    - (1 / 8 : F) * epsilon * (B * E0)
    - (9 / 64 : F) * zeta * (B * D0)
    - (3 / 32 : F) * eta * (B * C0)
    - (3 / 128 : F) * theta * B ^ 2
    - (1 / 16 : F) * epsilon * (A * F0)
    - (3 / 32 : F) * zeta * (A * E0)
    - (3 / 32 : F) * eta * (A * D0)
    - (3 / 64 : F) * theta * (A * C0)
    + (3 / 8 : F) * zeta * G0
    + (1 / 4 : F) * eta * F0
    + (1 / 8 : F) * theta * E0

set_option maxHeartbeats 64000000 in
theorem xiResidual810_eq_integrated
    {F : Type*} [Field F] [CharZero F]
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0
      beta gamma delta epsilon zeta eta theta : F)
    (hbeta : betaResidual810 L A B Q = beta)
    (hgamma : gammaResidual810 L A B C0 P R = gamma)
    (hdelta : deltaResidual810 L A B C0 D0 P Q S0 = delta)
    (hepsilon : epsilonResidual810 L A B C0 D0 E0 P Q R T0 = epsilon)
    (hzeta : zetaResidual810 L A B C0 D0 E0 F0 P Q R S0 U0 = zeta)
    (heta : etaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 V0 = eta)
    (htheta : thetaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 W0 =
      theta) :
    xiResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 =
      degreeZeroXiIntegrated810 L A B C0 D0 E0 F0 G0 beta gamma delta
        epsilon zeta eta theta := by
  simp only [xiResidual810, degreeZeroXiIntegrated810, hbeta, hgamma,
    hdelta, hepsilon, hzeta, heta, htheta]
  ring

set_option maxHeartbeats 64000000 in
theorem omicronResidual810_eq_integrated
    {F : Type*} [Field F] [CharZero F]
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0
      beta gamma delta epsilon zeta eta theta : F)
    (hbeta : betaResidual810 L A B Q = beta)
    (hgamma : gammaResidual810 L A B C0 P R = gamma)
    (hdelta : deltaResidual810 L A B C0 D0 P Q S0 = delta)
    (hepsilon : epsilonResidual810 L A B C0 D0 E0 P Q R T0 = epsilon)
    (hzeta : zetaResidual810 L A B C0 D0 E0 F0 P Q R S0 U0 = zeta)
    (heta : etaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 V0 = eta)
    (htheta : thetaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 W0 =
      theta) :
    omicronResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 =
      degreeZeroOmicronIntegrated810 L A B C0 D0 E0 F0 G0 beta gamma delta
        epsilon zeta eta theta := by
  simp only [omicronResidual810, degreeZeroOmicronIntegrated810, hbeta,
    hgamma, hdelta, hepsilon, hzeta, heta, htheta]
  ring

set_option maxHeartbeats 64000000 in
theorem muResidual810_eq_integrated
    {F : Type*} [Field F] [CharZero F]
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0
      beta gamma delta epsilon zeta eta theta : F)
    (hbeta : betaResidual810 L A B Q = beta)
    (hgamma : gammaResidual810 L A B C0 P R = gamma)
    (hdelta : deltaResidual810 L A B C0 D0 P Q S0 = delta)
    (hepsilon : epsilonResidual810 L A B C0 D0 E0 P Q R T0 = epsilon)
    (hzeta : zetaResidual810 L A B C0 D0 E0 F0 P Q R S0 U0 = zeta)
    (heta : etaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 V0 = eta)
    (htheta : thetaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 W0 =
      theta) :
    muResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 =
      degreeZeroMuIntegrated810 L A B C0 D0 E0 F0 G0 beta gamma delta
        epsilon zeta eta theta := by
  have hW :
      W0 =
        theta +
          ((9 / 8 : F) * L * G0 +
            alphaResidual810 A P * F0 +
            (7 / 8 : F) * betaResidual810 L A B Q * E0 +
            (3 / 4 : F) * gammaResidual810 L A B C0 P R * D0 +
            (5 / 8 : F) * deltaResidual810 L A B C0 D0 P Q S0 * C0 +
            (1 / 2 : F) * epsilonResidual810 L A B C0 D0 E0 P Q R T0 * B +
            (3 / 8 : F) * zetaResidual810 L A B C0 D0 E0 F0 P Q R S0 U0 *
              A +
            (5 / 16 : F) * A * F0 + (5 / 16 : F) * B * E0 +
            (5 / 16 : F) * C0 * D0 - (5 / 128 : F) * B ^ 3 -
            (15 / 64 : F) * A * B * C0 - (15 / 128 : F) * A ^ 2 * D0 +
            (35 / 512 : F) * A ^ 3 * B +
            (9 / 64 : F) * L * A * E0 + (9 / 64 : F) * L * B * D0 +
            (9 / 128 : F) * L * C0 ^ 2 - (63 / 1024 : F) * L * A ^ 2 * C0 -
            (63 / 1024 : F) * L * A * B ^ 2 +
            (315 / 32768 : F) * L * A ^ 4 -
            (7 / 128 : F) * betaResidual810 L A B Q * B ^ 2 -
            (7 / 64 : F) * betaResidual810 L A B Q * A * C0 +
            (21 / 1024 : F) * betaResidual810 L A B Q * A ^ 3 -
            (3 / 16 : F) * gammaResidual810 L A B C0 P R * A * B -
            (15 / 128 : F) * deltaResidual810 L A B C0 D0 P Q S0 *
              A ^ 2) := by
    have h := htheta
    simp only [thetaResidual810] at h
    linear_combination h
  simp only [muResidual810, degreeZeroMuIntegrated810, hW, hbeta, hgamma,
    hdelta, hepsilon, hzeta, heta, alphaResidual810]
  ring

set_option maxHeartbeats 64000000 in
theorem algebraMap_degreeZeroXiPolynomial810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    algebraMap k[X] (RatFunc k)
        (degreeZeroXiPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0) =
      degreeZeroXiIntegrated810 (RatFunc.C l)
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0)
        (algebraMap k[X] (RatFunc k) E0)
        (algebraMap k[X] (RatFunc k) F0)
        (algebraMap k[X] (RatFunc k) G0)
        (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
        (RatFunc.C epsilon) (RatFunc.C zeta) (RatFunc.C eta)
        (RatFunc.C theta) := by
  simp only [degreeZeroXiPolynomial810, degreeZeroXiIntegrated810,
    map_add, map_sub, map_neg, map_mul, map_pow, Polynomial.smul_eq_C_mul,
    RatFunc.algebraMap_C, map_div₀, map_ofNat, map_one]
  try ring

set_option maxHeartbeats 64000000 in
theorem algebraMap_degreeZeroMuPolynomial810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    algebraMap k[X] (RatFunc k)
        (degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0) =
      degreeZeroMuIntegrated810 (RatFunc.C l)
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0)
        (algebraMap k[X] (RatFunc k) E0)
        (algebraMap k[X] (RatFunc k) F0)
        (algebraMap k[X] (RatFunc k) G0)
        (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
        (RatFunc.C epsilon) (RatFunc.C zeta) (RatFunc.C eta)
        (RatFunc.C theta) := by
  simp only [degreeZeroMuPolynomial810, degreeZeroMuIntegrated810,
    map_add, map_sub, map_neg, map_mul, map_pow, Polynomial.smul_eq_C_mul,
    RatFunc.algebraMap_C, map_div₀, map_ofNat, map_one]
  try ring

set_option maxHeartbeats 64000000 in
theorem algebraMap_degreeZeroOmicronPolynomial810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    algebraMap k[X] (RatFunc k)
        (degreeZeroOmicronPolynomial810 l beta gamma delta epsilon zeta
          eta theta A B C0 D0 E0 F0 G0) =
      degreeZeroOmicronIntegrated810 (RatFunc.C l)
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0)
        (algebraMap k[X] (RatFunc k) E0)
        (algebraMap k[X] (RatFunc k) F0)
        (algebraMap k[X] (RatFunc k) G0)
        (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
        (RatFunc.C epsilon) (RatFunc.C zeta) (RatFunc.C eta)
        (RatFunc.C theta) := by
  simp only [degreeZeroOmicronPolynomial810,
    degreeZeroOmicronIntegrated810, map_add, map_sub, map_neg, map_mul,
    map_pow, Polynomial.smul_eq_C_mul, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_one]
  try ring

set_option maxHeartbeats 64000000 in
theorem degreeZeroXiPolynomial810_eq_C_of_ratFuncDeriv
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hderiv :
      ratFuncDerivation46
          (algebraMap k[X] (RatFunc k)
            (degreeZeroXiPolynomial810 l beta gamma delta epsilon zeta
              eta theta A B C0 D0 E0 F0 G0)) =
        0) :
    ∃ c : k,
      degreeZeroXiPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0 =
        Polynomial.C c := by
  let I :=
    degreeZeroXiPolynomial810 l beta gamma delta epsilon zeta eta theta
      A B C0 D0 E0 F0 G0
  have hdmap : algebraMap k[X] (RatFunc k) I.derivative = 0 := by
    rw [← ratFuncDerivation46_polynomial]
    simpa only [I] using hderiv
  have hd : I.derivative = 0 := by
    apply RatFunc.algebraMap_injective k
    simpa using hdmap
  exact ⟨I.coeff 0, Polynomial.eq_C_of_derivative_eq_zero hd⟩

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuPolynomial810_eq_C_of_ratFuncDeriv
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hderiv :
      ratFuncDerivation46
          (algebraMap k[X] (RatFunc k)
            (degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta
              eta theta A B C0 D0 E0 F0 G0)) =
        0) :
    ∃ c : k,
      degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0 =
        Polynomial.C c := by
  let I :=
    degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta theta
      A B C0 D0 E0 F0 G0
  have hdmap : algebraMap k[X] (RatFunc k) I.derivative = 0 := by
    rw [← ratFuncDerivation46_polynomial]
    simpa only [I] using hderiv
  have hd : I.derivative = 0 := by
    apply RatFunc.algebraMap_injective k
    simpa using hdmap
  exact ⟨I.coeff 0, Polynomial.eq_C_of_derivative_eq_zero hd⟩

set_option maxHeartbeats 64000000 in
theorem degreeZeroOmicronPolynomial810_eq_C_of_ratFuncDeriv
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hderiv :
      ratFuncDerivation46
          (algebraMap k[X] (RatFunc k)
            (degreeZeroOmicronPolynomial810 l beta gamma delta epsilon
              zeta eta theta A B C0 D0 E0 F0 G0)) =
        0) :
    ∃ c : k,
      degreeZeroOmicronPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0 =
        Polynomial.C c := by
  let I :=
    degreeZeroOmicronPolynomial810 l beta gamma delta epsilon zeta eta
      theta A B C0 D0 E0 F0 G0
  have hdmap : algebraMap k[X] (RatFunc k) I.derivative = 0 := by
    rw [← ratFuncDerivation46_polynomial]
    simpa only [I] using hderiv
  have hd : I.derivative = 0 := by
    apply RatFunc.algebraMap_injective k
    simpa using hdmap
  exact ⟨I.coeff 0, Polynomial.eq_C_of_derivative_eq_zero hd⟩

set_option maxHeartbeats 64000000 in
theorem degreeZeroXiPolynomial810_natDegree_eq_zero_of_eq_C
    {l beta gamma delta epsilon zeta eta theta : k}
    {A B C0 D0 E0 F0 G0 : k[X]} {c : k}
    (h :
      degreeZeroXiPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0 =
        Polynomial.C c) :
    (degreeZeroXiPolynomial810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0).natDegree =
      0 := by
  rw [h, natDegree_C]

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuPolynomial810_natDegree_eq_zero_of_eq_C
    {l beta gamma delta epsilon zeta eta theta : k}
    {A B C0 D0 E0 F0 G0 : k[X]} {c : k}
    (h :
      degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0 =
        Polynomial.C c) :
    (degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0).natDegree =
      0 := by
  rw [h, natDegree_C]

set_option maxHeartbeats 64000000 in
theorem degreeZeroOmicronPolynomial810_natDegree_eq_zero_of_eq_C
    {l beta gamma delta epsilon zeta eta theta : k}
    {A B C0 D0 E0 F0 G0 : k[X]} {c : k}
    (h :
      degreeZeroOmicronPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0 =
        Polynomial.C c) :
    (degreeZeroOmicronPolynomial810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0).natDegree =
      0 := by
  rw [h, natDegree_C]

end DefectAlgebraMap810


#print axioms degreeZeroXiIntegrated810.eq_1
#print axioms degreeZeroMuIntegrated810.eq_1
#print axioms degreeZeroOmicronIntegrated810.eq_1

end Max11DegreeRoutes
