import Grok810ScaleZeroQuarticMultiKills4bSpeedReflSplitBasePart11Scratch

/-! # Part 12 of `Grok810ScaleZeroQuarticMultiKills4bSpeedReflSplitBaseScratch`.

One declaration split out of `Grok810ScaleZeroQuarticMultiKills4bSpeedReflSplitBaseScratch`; statements are byte-identical.
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

def kappaQuarticInnerBCDFG810 (b c d f g : k) : k :=
  (-15 : k) * b ^ 2 * d + (-15 : k) * b * c ^ 2 + 40 * b * g + 40 * c * f

def muQuarticInnerBCDFG810 (b c d f g : k) : k :=
  35 * b ^ 4 + (-480 : k) * b * c * d + (-80 : k) * c ^ 3 + 640 * c * g + 640 * d * f

def nuQuarticInnerBCDFG810 (b c d f g : k) : k :=
  35 * b ^ 3 * c + (-60 : k) * b ^ 2 * f + (-60 : k) * b * d ^ 2 + (-60 : k) * c ^ 2 * d + 160 * d * g

def xiQuarticInnerBCDFG810 (b c d f g : k) : k :=
  55 * b ^ 3 * d + 90 * b ^ 2 * c ^ 2 + (-80 : k) * b ^ 2 * g + (-200 : k) * b * c * f + (-120 : k) * c * d ^ 2 + 160 * f ^ 2

def omicronQuarticInnerBCDFG810 (b c d f g : k) : k :=
  (-21 : k) * b ^ 5 + 540 * b ^ 2 * c * d + 180 * b * c ^ 3 + (-480 : k) * b * c * g + (-640 : k) * b * d * f + (-320 : k) * c ^ 2 * f + (-160 : k) * d ^ 3 + 1280 * f * g

def piQuarticInnerBCDFG810 (b c d f g : k) : k :=
  (-35 : k) * b ^ 4 * c + 50 * b ^ 3 * f + 90 * b ^ 2 * d ^ 2 + 180 * b * c ^ 2 * d + (-160 : k) * b * d * g + 15 * c ^ 4 + (-80 : k) * c ^ 2 * g + (-240 : k) * c * d * f + 320 * g ^ 2

def primitiveQuarticInnerBCDFG810 (b c d f g : k) : k :=
  (-125 : k) * b ^ 4 * d + (-265 : k) * b ^ 3 * c ^ 2 + 120 * b ^ 3 * g + 680 * b ^ 2 * c * f + 720 * b * c * d ^ 2 + (-640 : k) * b * f ^ 2 + 240 * c ^ 3 * d + (-640 : k) * c * d * g + (-640 : k) * d ^ 2 * f

set_option maxHeartbeats 32000000 in
theorem quarticInner_BCDFG_identity
    (b c d f g : k) :
    ((49721439699 / 92489280634880 : k) * b ^ 4 * d + (-1412223896701 / 55493568380928 : k) * b ^ 3 * c ^ 2 + (-433327923123 / 11561160079360 : k) * b ^ 3 * g + (718669049307 / 16185624111104 : k) * b ^ 2 * c * f + (338005186913 / 5780580039680 : k) * b * c * d ^ 2 + (181171989941 / 5780580039680 : k) * b * f ^ 2 + (600807275947 / 10116015069440 : k) * c ^ 3 * d + (-13099546853549 / 60696090416640 : k) * c * d * g + (-1897249609669 / 40464060277760 : k) * d ^ 2 * f) * kappaQuarticInnerBCDFG810 b c d f g +
      ((69797673027 / 129484992888832 : k) * b ^ 3 * f + (1038672910209 / 258969985777664 : k) * b * c ^ 2 * d + (765235362377 / 161856241111040 : k) * b * d * g + (191100579987 / 323712482222080 : k) * c ^ 4 + (-63700193329 / 20232030138880 : k) * c ^ 2 * g + (-128691860909 / 23122320158720 : k) * c * d * f + (63700193329 / 5058007534720 : k) * g ^ 2) * muQuarticInnerBCDFG810 b c d f g +
      ((-1213263453279 / 161856241111040 : k) * b * c ^ 3 + (1471610468093 / 60696090416640 : k) * b * c * g + (-934271627935 / 32371248222208 : k) * b * d * f + (221467542707 / 8670870059520 : k) * c ^ 2 * f + (16573813233 / 16185624111104 : k) * d ^ 3 + (-7193167623 / 2023203013888 : k) * f * g) * nuQuarticInnerBCDFG810 b c d f g +
      ((-12263569863 / 36995712253952 : k) * b ^ 2 * c ^ 2 + (-61185507293 / 4624464031744 : k) * b ^ 2 * g + (-528863701 / 23122320158720 : k) * b * c * f + (-11963841453 / 4624464031744 : k) * c * d ^ 2 + (1 / 160 : k) * f ^ 2) * xiQuarticInnerBCDFG810 b c d f g +
      ((116329455045 / 129484992888832 : k) * b ^ 2 * f + (-49721439699 / 129484992888832 : k) * b * d ^ 2 + (5303137653 / 3407499812864 : k) * c ^ 2 * d + (16573813233 / 16185624111104 : k) * d * g) * omicronQuarticInnerBCDFG810 b c d f g +
      ((133856743379 / 10116015069440 : k) * b * c * d + (63700193329 / 20232030138880 : k) * c ^ 3 + (-63700193329 / 2529003767360 : k) * c * g + (-278252387341 / 10116015069440 : k) * d * f) * piQuarticInnerBCDFG810 b c d f g =
      f ^ 4 := by
  simp only [kappaQuarticInnerBCDFG810, muQuarticInnerBCDFG810, nuQuarticInnerBCDFG810, xiQuarticInnerBCDFG810, omicronQuarticInnerBCDFG810, piQuarticInnerBCDFG810, primitiveQuarticInnerBCDFG810]
  ring

end QuarticKills810

end Max11DegreeRoutes
