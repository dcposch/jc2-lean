import Grok810ScaleZeroQuarticMultiKills1bSpeedReflSplitBasePart47Scratch
import Grok810ScaleZeroQuarticMultiKills1bSpeedReflSplitBasePart48Scratch
import Grok810ScaleZeroQuarticMultiKills1bSpeedReflSplitBasePart49Scratch

/-! Part 50 of 84 of `Grok810ScaleZeroQuarticMultiKills1bSpeedReflSplitBaseScratch`, split so that no single module elaborates them all
at once.  Statements are unchanged. -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section QuarticKills810

variable {k : Type*} [Field k] [CharZero k]


set_option maxHeartbeats 32000000 in
theorem quarticInner_ABDF_identity
    (a b d f : k) :
    ((43 / 1152000 : k) * a ^ 3 * b + (-1237 / 576000 : k) * a ^ 2 * d + (53 / 3600 : k) * a * f + (37 / 64000 : k) * b ^ 3) * kappaQuarticInnerABDF810 a b d f +
      ((21 / 64000 : k) * a * b ^ 2 + (-277 / 48000 : k) * b * d) * muQuarticInnerABDF810 a b d f +
      ((43 / 1152000 : k) * a ^ 2 * b + (-31 / 36000 : k) * a * d + (23 / 36000 : k) * f) * nuQuarticInnerABDF810 a b d f +
      ((23 / 24000 : k) * b ^ 2) * xiQuarticInnerABDF810 a b d f +
      ((-1 / 2560 : k) * d) * omicronQuarticInnerABDF810 a b d f =
      d ^ 4 := by
  simp only [kappaQuarticInnerABDF810, muQuarticInnerABDF810, nuQuarticInnerABDF810, xiQuarticInnerABDF810, omicronQuarticInnerABDF810, piQuarticInnerABDF810, primitiveQuarticInnerABDF810]
  ring


set_option maxHeartbeats 16000000 in
def kappaQuarticFaceABDF810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)


set_option maxHeartbeats 16000000 in
def degreeZeroKappaQuarticNoABDF810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
  + (5 / 16 : k) • (C * F)
  + (5 / 16 : k) • (D * E)
  + (63 / 262144 * l : k) • A ^ 5
  + (45 / 8192 * l : k) • (A ^ 3 * C)
  - (9 / 16384 * l : k) • (A ^ 2 * B ^ 2)
  + (27 / 1024 * l : k) • (A ^ 2 * E)
  - (9 / 512 * l : k) • (A * B * D)
  + (9 / 1024 * l : k) • (A * C ^ 2)
  - (63 / 1024 * l : k) • (B ^ 2 * C)
  + (9 / 64 * l : k) • (A * G)
  + (9 / 64 * l : k) • (B * F)
  + (9 / 64 * l : k) • (C * E)
  + (9 / 128 * l : k) • D ^ 2
  + (35 / 32768 * beta : k) • A ^ 4
  + (21 / 1024 * beta : k) • (A ^ 2 * C)
  + (7 / 1024 * beta : k) • (A * B ^ 2)
  + (7 / 64 * beta : k) • (A * E)
  - (7 / 64 * beta : k) • (B * D)
  - (7 / 128 * beta : k) • C ^ 2
  + (7 / 8 * beta : k) • G
  - (3 / 16 * gamma : k) • (B * C)
  + (3 / 4 * gamma : k) • F
  + (5 / 1024 * delta : k) • A ^ 3
  + (5 / 64 * delta : k) • (A * C)
  - (15 / 128 * delta : k) • B ^ 2
  + (5 / 8 * delta : k) • E
  + (1 / 2 * epsilon : k) • D
  + (3 / 128 * zeta : k) • A ^ 2
  + (3 / 8 * zeta : k) • C
  + (1 / 4 * eta : k) • B
  + (1 / 8 * theta : k) • A


end QuarticKills810
end Max11DegreeRoutes
end
