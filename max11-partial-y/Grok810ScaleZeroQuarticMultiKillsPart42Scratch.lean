import Grok810ScaleZeroQuarticMultiKillsPart41Scratch

/-! Part 42 of 47 of `Grok810ScaleZeroQuarticMultiKillsScratch`, split so that no single module elaborates them all
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


def piQuarticInnerCEG810 (c e g : k) : k :=
  15 * c ^ 4 + (-80 : k) * c ^ 2 * g + (-160 : k) * c * e ^ 2 + 320 * g ^ 2


set_option maxHeartbeats 32000000 in
theorem quarticInner_CEG_identity
    (c e g : k) :
    ((-3 / 5120 : k) * c ^ 3 * g + (63 / 56320 : k) * c ^ 2 * e ^ 2 + (1 / 128 : k) * c * g ^ 2 + (7 / 1408 : k) * e ^ 2 * g) * muQuarticInnerCEG810 c e g +
      ((9 / 14080 : k) * c * e * g + (-7 / 2816 : k) * e ^ 3) * xiQuarticInnerCEG810 c e g +
      ((-1 / 5120 : k) * c ^ 2 * g + (21 / 56320 : k) * c * e ^ 2 + (1 / 320 : k) * g ^ 2) * piQuarticInnerCEG810 c e g =
      g ^ 4 := by
  simp only [muQuarticInnerCEG810, xiQuarticInnerCEG810, piQuarticInnerCEG810]
  ring


set_option maxHeartbeats 16000000 in
def muQuarticFaceCEG810 (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 128 : k)) • C ^ 3
  + (5 / 16 : k) • (C * G)
  + (5 / 32 : k) • E ^ 2


set_option maxHeartbeats 32000000 in
def degreeZeroMuQuarticNoCEG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  + (35 / 2048 : k) • B ^ 4
  - (5 / 64 : k) • (A * B * F)
  - (5 / 128 : k) • (A * D ^ 2)
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  + (5 / 16 : k) • (D * F)
  - (45 / 262144 * l : k) • (A ^ 4 * B)
  - (9 / 8192 * l : k) • (A ^ 3 * D)
  - (9 / 8192 * l : k) • (A ^ 2 * B * C)
  + (63 / 8192 * l : k) • (A * B ^ 3)
  - (9 / 1024 * l : k) • (A ^ 2 * F)
  - (9 / 512 * l : k) • (A * B * E)
  - (9 / 512 * l : k) • (A * C * D)
  - (63 / 1024 * l : k) • (B ^ 2 * D)
  - (63 / 1024 * l : k) • (B * C ^ 2)
  + (9 / 64 * l : k) • (B * G)
  + (9 / 64 * l : k) • (C * F)
  + (9 / 64 * l : k) • (D * E)
  - (7 / 8192 * beta : k) • (A ^ 3 * B)
  - (7 / 1024 * beta : k) • (A ^ 2 * D)
  + (7 / 512 * beta : k) • (A * B * C)
  + (21 / 1024 * beta : k) • B ^ 3
  - (7 / 64 * beta : k) • (A * F)
  - (7 / 64 * beta : k) • (B * E)
  - (7 / 64 * beta : k) • (C * D)
  + (3 / 128 * gamma : k) • (A * B ^ 2)
  - (3 / 16 * gamma : k) • (B * D)
  - (3 / 32 * gamma : k) • C ^ 2
  + (3 / 4 * gamma : k) • G
  - (5 / 1024 * delta : k) • (A ^ 2 * B)
  - (5 / 64 * delta : k) • (A * D)
  - (15 / 64 * delta : k) • (B * C)
  + (5 / 8 * delta : k) • F
  - (1 / 8 * epsilon : k) • B ^ 2
  + (1 / 2 * epsilon : k) • E
  - (3 / 64 * zeta : k) • (A * B)
  + (3 / 8 * zeta : k) • D
  + (1 / 4 * eta : k) • C
  + (1 / 8 * theta : k) • B


end QuarticKills810
end Max11DegreeRoutes
end
