import Grok810ScaleZeroQuarticDefsScratch
import Grok810ScaleZeroQuarticMultiKills7SpeedReflValDegSplitBaseScratch

/-! # SPEED: theorems of `Grok810ScaleZeroQuarticMultiKills7SpeedReflValDegScratch`, part 0 of 24, so that no single
module retains all the reflective bridge proof terms at once.
Statements unchanged. -/

noncomputable section

open scoped Polynomial.Bivariate
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
set_option maxRecDepth 8000000

section QuarticKills810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
theorem quarticInner_ABDEFG_identity
    (a b d e f g : k) :
    ((-55345 / 15096455168 : k) * a ^ 6 * d + (-15855 / 656367616 : k) * a ^ 5 * f + (20535 / 1312735232 : k) * a ^ 4 * b * e + (-101858877 / 16606100684800 : k) * a ^ 3 * b ^ 2 * d + (1363727 / 16409190400 : k) * a ^ 3 * b * g + (-11422337 / 23588211200 : k) * a ^ 3 * d * e + (366447153 / 1660610068480 : k) * a ^ 2 * b ^ 2 * f + (1781524013 / 2075762585600 : k) * a ^ 2 * b * d ^ 2 + (-42188431 / 54625331200 : k) * a ^ 2 * d * g + (-259788149 / 207576258560 : k) * a ^ 2 * e * f + (-2162529227 / 132848805478400 : k) * a * b ^ 5 + (2465020343 / 8303050342400 : k) * a * b ^ 3 * e + (-64215295 / 41515251712 : k) * a * b * d * f + (-52471307 / 37741137920 : k) * a * b * e ^ 2 + (-1537848229 / 1037881292800 : k) * a * d ^ 3 + (47831901 / 3414083200 : k) * a * f * g + (-21894297 / 874005299200 : k) * b ^ 4 * d + (-283139 / 237501440 : k) * b ^ 3 * g + (516064619 / 1037881292800 : k) * b ^ 2 * d * e + (9121641 / 1410164800 : k) * b * e * g + (2221277 / 705082400 : k) * b * f ^ 2 + (-176728241 / 129735161600 : k) * d ^ 2 * f + (-35149377 / 10378812928 : k) * d * e ^ 2) * kappaQuarticInnerABDEFG810 a b d e f g +
      ((33207 / 589705280 : k) * a ^ 2 * d * f + (303429 / 1025574400 : k) * a * b ^ 2 * g + (-315801003 / 259470323200 : k) * a * b * d * e + (3171 / 5127872 : k) * a * f ^ 2 + (1305508033 / 4151525171200 : k) * b ^ 3 * f + (2421833619 / 2075762585600 : k) * b ^ 2 * d ^ 2 + (-135106987 / 23588211200 : k) * b * d * g + (-240815051 / 518940646400 : k) * b * e * f + (663639417 / 518940646400 : k) * d ^ 2 * e + (240009 / 32049200 : k) * g ^ 2) * muQuarticInnerABDEFG810 a b d e f g +
      ((-33207 / 15096455168 : k) * a ^ 5 * d + (-9513 / 656367616 : k) * a ^ 4 * f + (12321 / 1312735232 : k) * a ^ 3 * b * e + (-19612105 / 1328488054784 : k) * a ^ 2 * b ^ 2 * d + (681041 / 16409190400 : k) * a ^ 2 * b * g + (-12052243 / 45125273600 : k) * a ^ 2 * d * e + (3332010831 / 8303050342400 : k) * a * b * d ^ 2 + (-163315307 / 518940646400 : k) * a * d * g + (-52720883 / 103788129280 : k) * a * e * f + (584068213 / 132848805478400 : k) * b ^ 5 + (901462127 / 8303050342400 : k) * b ^ 3 * e + (-15265851 / 94352844800 : k) * b * d * f + (-1440036269 / 2075762585600 : k) * b * e ^ 2 + (-63819611 / 103788129280 : k) * d ^ 3 + (75924047 / 64867580800 : k) * f * g) * nuQuarticInnerABDEFG810 a b d e f g +
      ((77483 / 1179410560 : k) * a ^ 2 * d ^ 2 + (139141 / 1187507200 : k) * a * b ^ 2 * e + (389349 / 1179410560 : k) * a * d * f + (-269054889 / 1037881292800 : k) * b ^ 3 * d + (30939 / 18554800 : k) * b ^ 2 * g + (8390597 / 25947032320 : k) * b * d * e + (-108371 / 37109600 : k) * e * g + (1 / 320 : k) * f ^ 2) * xiQuarticInnerABDEFG810 a b d e f g +
      ((-11069 / 15096455168 : k) * a ^ 4 * d + (-3171 / 656367616 : k) * a ^ 3 * f + (4107 / 1312735232 : k) * a ^ 2 * b * e + (-329 / 3281838080 : k) * a * b * g + (-585289 / 4512527360 : k) * a * d * e + (71214369 / 1660610068480 : k) * b ^ 2 * f + (191458833 / 1660610068480 : k) * b * d ^ 2 + (-63819611 / 207576258560 : k) * d * g + (-25984303 / 207576258560 : k) * e * f) * omicronQuarticInnerABDEFG810 a b d e f g +
      ((11069 / 2358821120 : k) * a ^ 2 * b * d + (197969 / 4717642240 : k) * a * d ^ 2 + (6547 / 950005760 : k) * b ^ 4 + (4519 / 282032960 : k) * b ^ 2 * e + (259 / 235882112 : k) * d * f + (-11621 / 112813184 : k) * e ^ 2) * piQuarticInnerABDEFG810 a b d e f g +
      ((-11069 / 15096455168 : k) * a ^ 3 * d + (-3171 / 656367616 : k) * a ^ 2 * f + (4107 / 1312735232 : k) * a * b * e + (-142006809 / 33212201369600 : k) * b ^ 2 * d + (684331 / 16409190400 : k) * b * g + (6642431 / 1037881292800 : k) * d * e) * primitiveQuarticInnerABDEFG810 a b d e f g =
      f ^ 4 := by
  simp only [kappaQuarticInnerABDEFG810, muQuarticInnerABDEFG810, nuQuarticInnerABDEFG810, xiQuarticInnerABDEFG810, omicronQuarticInnerABDEFG810, piQuarticInnerABDEFG810, primitiveQuarticInnerABDEFG810]
  ring


set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaQuartic810_eq_ABDEFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceABDEFG810 A B C D E F G +
        degreeZeroKappaQuarticNoABDEFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, degreeZeroKappaQuartic810, kappaQuarticFaceABDEFG810, degreeZeroKappaQuarticNoABDEFG810]
  all_goals module


set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroKappaQuarticNoABDEFG810` (31 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroKappaQuarticNoABDEFG810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    degreeZeroKappaQuarticNoABDEFG810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 128) : k), (5 / 16 : k), (63 / 262144 * l : k),
      (45 / 8192 * l : k), (-(9 / 16384 * l) : k), (27 / 1024 * l : k),
      (-(9 / 512 * l) : k), (9 / 1024 * l : k), (-(63 / 1024 * l) : k),
      (9 / 64 * l : k), (9 / 64 * l : k), (9 / 64 * l : k),
      (9 / 128 * l : k), (35 / 32768 * beta : k), (21 / 1024 * beta : k),
      (7 / 1024 * beta : k), (7 / 64 * beta : k), (-(7 / 64 * beta) : k),
      (-(7 / 128 * beta) : k), (7 / 8 * beta : k), (-(3 / 16 * gamma) : k),
      (3 / 4 * gamma : k), (5 / 1024 * delta : k), (5 / 64 * delta : k),
      (-(15 / 128 * delta) : k), (5 / 8 * delta : k), (1 / 2 * epsilon : k),
      (3 / 128 * zeta : k), (3 / 8 * zeta : k), (1 / 4 * eta : k),
      (1 / 8 * theta : k)]
      [
      [0, 1, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0], [5, 0, 0, 0, 0, 0, 0], [3, 0, 1, 0, 0, 0, 0],
      [2, 2, 0, 0, 0, 0, 0], [2, 0, 0, 0, 1, 0, 0], [1, 1, 0, 1, 0, 0, 0], [1, 0, 2, 0, 0, 0, 0],
      [0, 2, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1], [0, 1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0],
      [0, 0, 0, 2, 0, 0, 0], [4, 0, 0, 0, 0, 0, 0], [2, 0, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0],
      [1, 0, 0, 0, 1, 0, 0], [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1],
      [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0], [3, 0, 0, 0, 0, 0, 0], [1, 0, 1, 0, 0, 0, 0],
      [0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0],
      [0, 0, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0]] :=
  rfl


set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaQuarticNoABDEFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABDEFG810 A B C D E F G) :
    (degreeZeroKappaQuarticNoABDEFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hFpos, hGpos, hAB, hAD, hAE, hAF, hAG, hClt⟩
  have hC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hClt
  rw [speedRefl_degreeZeroKappaQuarticNoABDEFG810_eq_polyOf]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk (by omega) ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mdeg_cons,
    Max11ReflectDeg.mdeg_nil_left, Max11ReflectDeg.mdeg_nil_right,
    List.map_cons, List.map_nil, mul_zero, zero_mul, neg_zero,
    Nat.mul_zero, Nat.zero_mul, Nat.add_zero, Nat.zero_add,
    mul_one, one_mul, and_true, true_and, natDegree_zero]
  repeat' apply And.intro
  all_goals first
    | (right; right; omega)
    | (left; norm_num; done)
    | (right; left; simp; done)
    | trivial


end QuarticKills810

end Max11DegreeRoutes

end
