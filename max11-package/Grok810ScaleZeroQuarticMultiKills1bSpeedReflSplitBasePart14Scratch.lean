import Grok810ScaleZeroQuarticMultiKills1bSpeedReflSplitBasePart11Scratch
import Grok810ScaleZeroQuarticMultiKills1bSpeedReflSplitBasePart12Scratch
import Grok810ScaleZeroQuarticMultiKills1bSpeedReflSplitBasePart13Scratch

/-! Part 14 of 84 of `Grok810ScaleZeroQuarticMultiKills1bSpeedReflSplitBaseScratch`, split so that no single module elaborates them all
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
theorem quarticInner_ABCE_identity
    (a b c e : k) :
    ((-3 / 5120 : k) * a ^ 3 * b + (-37 / 1600 : k) * a * b * c + (-3 / 1600 : k) * b ^ 3 + (1 / 200 : k) * b * e) * kappaQuarticInnerABCE810 a b c e +
      ((-1 / 80 : k) * c ^ 2) * muQuarticInnerABCE810 a b c e +
      ((-1 / 2560 : k) * a ^ 2 * b + (-1 / 800 : k) * b * c) * nuQuarticInnerABCE810 a b c e +
      ((3 / 800 : k) * b ^ 2 + (-1 / 60 : k) * e) * xiQuarticInnerABCE810 a b c e +
      ((-1 / 5120 : k) * a * b) * omicronQuarticInnerABCE810 a b c e =
      c ^ 5 := by
  simp only [kappaQuarticInnerABCE810, muQuarticInnerABCE810, nuQuarticInnerABCE810, xiQuarticInnerABCE810, omicronQuarticInnerABCE810, piQuarticInnerABCE810, primitiveQuarticInnerABCE810]
  ring


set_option maxHeartbeats 16000000 in
def kappaQuarticFaceABCE810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B * C ^ 2)


set_option maxHeartbeats 16000000 in
def degreeZeroKappaQuarticNoABCE810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B ^ 2 * D)
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
