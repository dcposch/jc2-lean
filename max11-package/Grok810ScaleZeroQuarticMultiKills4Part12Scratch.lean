import Grok810ScaleZeroQuarticMultiKills4Part11Scratch

/-! # Part 12 of `Grok810ScaleZeroQuarticMultiKills4Scratch`.

One declaration split out of `Grok810ScaleZeroQuarticMultiKills4Scratch`; statements are byte-identical.
-/

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

def kappaQuarticInnerABDFG810 (a b d f g : k) : k :=
  5 * a * b ^ 3 + (-60 : k) * b ^ 2 * d + 160 * b * g

def muQuarticInnerABDFG810 (a b d f g : k) : k :=
  (-160 : k) * a * b * f + (-80 : k) * a * d ^ 2 + 35 * b ^ 4 + 640 * d * f

def nuQuarticInnerABDFG810 (a b d f g : k) : k :=
  (-5 : k) * a ^ 2 * b ^ 3 + 180 * a * b ^ 2 * d + (-160 : k) * a * b * g + (-480 : k) * b ^ 2 * f + (-480 : k) * b * d ^ 2 + 1280 * d * g

def xiQuarticInnerABDFG810 (a b d f g : k) : k :=
  (-15 : k) * a * b ^ 4 + (-160 : k) * a * d * f + 110 * b ^ 3 * d + (-160 : k) * b ^ 2 * g + 320 * f ^ 2

def omicronQuarticInnerABDFG810 (a b d f g : k) : k :=
  (-5 : k) * a ^ 3 * b ^ 3 + (-180 : k) * a ^ 2 * b ^ 2 * d + (-160 : k) * a ^ 2 * b * g + 1600 * a * b ^ 2 * f + 2240 * a * b * d ^ 2 + (-2560 : k) * a * d * g + (-336 : k) * b ^ 5 + (-10240 : k) * b * d * f + (-2560 : k) * d ^ 3 + 20480 * f * g

def piQuarticInnerABDFG810 (a b d f g : k) : k :=
  15 * a ^ 2 * b ^ 4 + (-480 : k) * a * b ^ 3 * d + 320 * a * b ^ 2 * g + (-1280 : k) * a * f ^ 2 + 800 * b ^ 3 * f + 1440 * b ^ 2 * d ^ 2 + (-2560 : k) * b * d * g + 5120 * g ^ 2

def primitiveQuarticInnerABDFG810 (a b d f g : k) : k :=
  (-5 : k) * a ^ 4 * b ^ 3 + (-60 : k) * a ^ 3 * b ^ 2 * d + (-160 : k) * a ^ 3 * b * g + (-160 : k) * a ^ 2 * b ^ 2 * f + (-800 : k) * a ^ 2 * b * d ^ 2 + (-1280 : k) * a ^ 2 * d * g + 520 * a * b ^ 5 + 10240 * a * b * d * f + 2560 * a * d ^ 3 + (-20480 : k) * a * f * g + (-4000 : k) * b ^ 4 * d + 3840 * b ^ 3 * g + (-20480 : k) * b * f ^ 2 + (-20480 : k) * d ^ 2 * f

set_option maxHeartbeats 32000000 in
theorem quarticInner_ABDFG_identity
    (a b d f g : k) :
    ((101871 / 16627793920 : k) * a ^ 5 * b + (-379077 / 64952320000 : k) * a ^ 4 * d + (-201940979 / 259809280000 : k) * a ^ 3 * f + (-750516991 / 4156948480000 : k) * a ^ 2 * b ^ 3 + (6062283449 / 2598092800000 : k) * a * b ^ 2 * d + (-1023578077 / 324761600000 : k) * a * b * g + (483740159 / 324761600000 : k) * b ^ 2 * f + (-1559531761 / 324761600000 : k) * b * d ^ 2 + (425448687 / 40595200000 : k) * d * g) * kappaQuarticInnerABDFG810 a b d f g +
      ((-33957 / 2078474240 : k) * a ^ 3 * b ^ 2 + (8893253 / 32476160000 : k) * a ^ 2 * b * d + (-33957 / 64952320 : k) * a ^ 2 * g + (4235941 / 16238080000 : k) * a * b * f + (-1162157 / 4059520000 : k) * a * d ^ 2 + (-98759913 / 259809280000 : k) * b ^ 4 + (9817901 / 8119040000 : k) * d * f) * muQuarticInnerABDFG810 a b d f g +
      ((33957 / 8313896960 : k) * a ^ 4 * b + (-1920311 / 129904640000 : k) * a ^ 3 * d + (-905817 / 25980928000 : k) * a ^ 2 * f + (566923791 / 2598092800000 : k) * b ^ 2 * d + (-281702797 / 324761600000 : k) * b * g) * nuQuarticInnerABDFG810 a b d f g +
      ((-16997841 / 129904640000 : k) * a ^ 2 * b ^ 2 + (44440213 / 32476160000 : k) * a * b * d + (-7687691 / 4059520000 : k) * a * g + (-9817901 / 4059520000 : k) * d ^ 2) * xiQuarticInnerABDFG810 a b d f g +
      ((33957 / 16627793920 : k) * a ^ 3 * b + (1162157 / 129904640000 : k) * a ^ 2 * d + (10859191 / 259809280000 : k) * a * f + (-32919971 / 831389696000 : k) * b ^ 3) * omicronQuarticInnerABDFG810 a b d f g +
      ((-1688589 / 129904640000 : k) * b * d + (1 / 5120 : k) * g) * piQuarticInnerABDFG810 a b d f g =
      g ^ 3 := by
  simp only [kappaQuarticInnerABDFG810, muQuarticInnerABDFG810, nuQuarticInnerABDFG810, xiQuarticInnerABDFG810, omicronQuarticInnerABDFG810, piQuarticInnerABDFG810, primitiveQuarticInnerABDFG810]
  ring

end QuarticKills810

end Max11DegreeRoutes
