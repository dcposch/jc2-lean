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
/-! # SPEED: theorems of `Grok810ScaleZeroQuarticMultiKills7SpeedReflValDegScratch`, part 1 of 24, so that no single
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

theorem kappaQuarticFaceABDEFG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeABDEFG810 A B C D E F G)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    : (kappaQuarticFaceABDEFG810 A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) =
      (1 / 512 : k) * kappaQuarticInnerABDEFG810 A.leadingCoeff B.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hFpos, hGpos, hAB, hAD, hAE, hAF, hAG, hClt⟩
  simp only [kappaQuarticFaceABDEFG810, kappaQuarticInnerABDEFG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_AB3 : ((A * B ^ 3)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 3 hBne), natDegree_pow]
  have hcf_AB3 : ((A * B ^ 3)).coeff (A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 3 := by
    rw [← hdeg_AB3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B2D : ((B ^ 2 * D)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) hDne, natDegree_pow]
    omega
  have hcf_B2D : ((B ^ 2 * D)).coeff (A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_B2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BG : ((B * G)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne hGne]
    omega
  have hcf_BG : ((B * G)).coeff (A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_BG, coeff_natDegree, leadingCoeff_mul]
  have hdeg_DE : ((D * E)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hDne hEne]
    omega
  have hcf_DE : ((D * E)).coeff (A.natDegree + 3 * B.natDegree) =
      D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_DE, coeff_natDegree, leadingCoeff_mul]
  rw [hcf_AB3, hcf_B2D, hcf_BG, hcf_DE]
  ring


set_option maxHeartbeats 16000000 in
theorem degreeZeroMuQuartic810_eq_ABDEFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticFaceABDEFG810 A B C D E F G +
        degreeZeroMuQuarticNoABDEFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, degreeZeroMuQuartic810, muQuarticFaceABDEFG810, degreeZeroMuQuarticNoABDEFG810]
  all_goals module


set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroMuQuarticNoABDEFG810` (37 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroMuQuarticNoABDEFG810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    degreeZeroMuQuarticNoABDEFG810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 512 : k), (-(15 / 64) : k), (-(5 / 128) : k),
      (5 / 16 : k), (-(45 / 262144 * l) : k), (-(9 / 8192 * l) : k),
      (-(9 / 8192 * l) : k), (63 / 8192 * l : k), (-(9 / 1024 * l) : k),
      (-(9 / 512 * l) : k), (-(9 / 512 * l) : k), (-(63 / 1024 * l) : k),
      (-(63 / 1024 * l) : k), (9 / 64 * l : k), (9 / 64 * l : k),
      (9 / 64 * l : k), (-(7 / 8192 * beta) : k), (-(7 / 1024 * beta) : k),
      (7 / 512 * beta : k), (21 / 1024 * beta : k), (-(7 / 64 * beta) : k),
      (-(7 / 64 * beta) : k), (-(7 / 64 * beta) : k), (3 / 128 * gamma : k),
      (-(3 / 16 * gamma) : k), (-(3 / 32 * gamma) : k), (3 / 4 * gamma : k),
      (-(5 / 1024 * delta) : k), (-(5 / 64 * delta) : k), (-(15 / 64 * delta) : k),
      (5 / 8 * delta : k), (-(1 / 8 * epsilon) : k), (1 / 2 * epsilon : k),
      (-(3 / 64 * zeta) : k), (3 / 8 * zeta : k), (1 / 4 * eta : k),
      (1 / 8 * theta : k)]
      [
      [1, 2, 1, 0, 0, 0, 0], [0, 1, 1, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 1],
      [4, 1, 0, 0, 0, 0, 0], [3, 0, 0, 1, 0, 0, 0], [2, 1, 1, 0, 0, 0, 0], [1, 3, 0, 0, 0, 0, 0],
      [2, 0, 0, 0, 0, 1, 0], [1, 1, 0, 0, 1, 0, 0], [1, 0, 1, 1, 0, 0, 0], [0, 2, 0, 1, 0, 0, 0],
      [0, 1, 2, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 1], [0, 0, 1, 0, 0, 1, 0], [0, 0, 0, 1, 1, 0, 0],
      [3, 1, 0, 0, 0, 0, 0], [2, 0, 0, 1, 0, 0, 0], [1, 1, 1, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0],
      [1, 0, 0, 0, 0, 1, 0], [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0],
      [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1], [2, 1, 0, 0, 0, 0, 0],
      [1, 0, 0, 1, 0, 0, 0], [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 2, 0, 0, 0, 0, 0],
      [0, 0, 0, 0, 1, 0, 0], [1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0],
      [0, 1, 0, 0, 0, 0, 0]] :=
  rfl


set_option maxHeartbeats 16000000 in
theorem degreeZeroMuQuarticNoABDEFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABDEFG810 A B C D E F G) :
    (degreeZeroMuQuarticNoABDEFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      A.natDegree + B.natDegree + F.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hFpos, hGpos, hAB, hAD, hAE, hAF, hAG, hClt⟩
  have hC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hClt
  rw [speedRefl_degreeZeroMuQuarticNoABDEFG810_eq_polyOf]
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
/-! # SPEED: theorems of `Grok810ScaleZeroQuarticMultiKills7SpeedReflValDegScratch`, part 2 of 24, so that no single
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

theorem muQuarticFaceABDEFG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeABDEFG810 A B C D E F G)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    : (muQuarticFaceABDEFG810 A B C D E F G).coeff (A.natDegree + B.natDegree + F.natDegree) =
      (1 / 2048 : k) * muQuarticInnerABDEFG810 A.leadingCoeff B.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hFpos, hGpos, hAB, hAD, hAE, hAF, hAG, hClt⟩
  simp only [muQuarticFaceABDEFG810, muQuarticInnerABDEFG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_ABF : ((A * B * F)).natDegree = A.natDegree + B.natDegree + F.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) hFne, natDegree_mul hAne hBne]
  have hcf_ABF : ((A * B * F)).coeff (A.natDegree + B.natDegree + F.natDegree) =
      A.leadingCoeff * B.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_ABF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_AD2 : ((A * D ^ 2)).natDegree = A.natDegree + B.natDegree + F.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 2 hDne), natDegree_pow]
    omega
  have hcf_AD2 : ((A * D ^ 2)).coeff (A.natDegree + B.natDegree + F.natDegree) =
      A.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_AD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B4 : (B ^ 4).natDegree = A.natDegree + B.natDegree + F.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_B4 : (B ^ 4).coeff (A.natDegree + B.natDegree + F.natDegree) =
      B.leadingCoeff ^ 4 := by
    rw [← hdeg_B4, coeff_natDegree, leadingCoeff_pow]
  have hdeg_B2E : ((B ^ 2 * E)).natDegree = A.natDegree + B.natDegree + F.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) hEne, natDegree_pow]
    omega
  have hcf_B2E : ((B ^ 2 * E)).coeff (A.natDegree + B.natDegree + F.natDegree) =
      B.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hdeg_B2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_DF : ((D * F)).natDegree = A.natDegree + B.natDegree + F.natDegree := by
    rw [natDegree_mul hDne hFne]
    omega
  have hcf_DF : ((D * F)).coeff (A.natDegree + B.natDegree + F.natDegree) =
      D.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_DF, coeff_natDegree, leadingCoeff_mul]
  have hdeg_E2 : (E ^ 2).natDegree = A.natDegree + B.natDegree + F.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_E2 : (E ^ 2).coeff (A.natDegree + B.natDegree + F.natDegree) =
      E.leadingCoeff ^ 2 := by
    rw [← hdeg_E2, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_ABF, hcf_AD2, hcf_B4, hcf_B2E, hcf_DF, hcf_E2]
  ring


set_option maxHeartbeats 32000000 in
theorem degreeZeroNuQuartic810_eq_ABDEFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      nuQuarticFaceABDEFG810 A B C D E F G +
        degreeZeroNuQuarticNoABDEFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, degreeZeroNuQuartic810, nuQuarticFaceABDEFG810, degreeZeroNuQuarticNoABDEFG810]
  all_goals module


set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroNuQuarticNoABDEFG810` (51 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroNuQuarticNoABDEFG810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    degreeZeroNuQuarticNoABDEFG810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 1024 : k), (35 / 512 : k), (-(5 / 128) : k),
      (-(15 / 64) : k), (-(15 / 128) : k), (105 / 4194304 * l : k),
      (135 / 262144 * l : k), (9 / 4096 * l : k), (9 / 8192 * l : k),
      (9 / 16384 * l : k), (63 / 4096 * l : k), (315 / 32768 * l : k),
      (9 / 1024 * l : k), (-(9 / 256 * l) : k), (-(9 / 512 * l) : k),
      (-(63 / 1024 * l) : k), (-(63 / 512 * l) : k), (-(21 / 1024 * l) : k),
      (9 / 64 * l : k), (9 / 64 * l : k), (9 / 128 * l : k),
      (7 / 65536 * beta : k), (7 / 4096 * beta : k), (-(7 / 16384 * beta) : k),
      (7 / 1024 * beta : k), (7 / 256 * beta : k), (63 / 1024 * beta : k),
      (-(7 / 64 * beta) : k), (-(7 / 64 * beta) : k), (-(7 / 128 * beta) : k),
      (3 / 128 * gamma : k), (5 / 128 * gamma : k), (-(3 / 32 * gamma) : k),
      (-(3 / 16 * gamma) : k), (-(3 / 16 * gamma) : k), (15 / 32768 * delta : k),
      (5 / 1024 * delta : k), (15 / 512 * delta : k), (-(15 / 64 * delta) : k),
      (-(15 / 128 * delta) : k), (5 / 8 * delta : k), (-(1 / 16 * epsilon) : k),
      (-(1 / 4 * epsilon) : k), (1 / 2 * epsilon : k), (1 / 512 * zeta : k),
      (-(15 / 128 * zeta) : k), (3 / 8 * zeta : k), (-(1 / 32 * eta) : k),
      (1 / 4 * eta : k), (1 / 128 * theta : k), (1 / 8 * theta : k)]
      [
      [1, 1, 2, 0, 0, 0, 0], [0, 3, 1, 0, 0, 0, 0], [1, 0, 1, 0, 0, 1, 0], [0, 1, 1, 0, 1, 0, 0],
      [0, 0, 2, 1, 0, 0, 0], [6, 0, 0, 0, 0, 0, 0], [4, 0, 1, 0, 0, 0, 0], [3, 0, 0, 0, 1, 0, 0],
      [2, 1, 0, 1, 0, 0, 0], [2, 0, 2, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0],
      [2, 0, 0, 0, 0, 0, 1], [1, 1, 0, 0, 0, 1, 0], [1, 0, 0, 2, 0, 0, 0], [0, 2, 0, 0, 1, 0, 0],
      [0, 1, 1, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 1], [0, 0, 0, 1, 0, 1, 0],
      [0, 0, 0, 0, 2, 0, 0], [5, 0, 0, 0, 0, 0, 0], [3, 0, 1, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0],
      [2, 0, 0, 0, 1, 0, 0], [1, 1, 0, 1, 0, 0, 0], [0, 2, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 1, 0],
      [0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0], [1, 1, 1, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0],
      [1, 0, 0, 0, 0, 1, 0], [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0], [4, 0, 0, 0, 0, 0, 0],
      [2, 0, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0],
      [0, 0, 0, 0, 0, 0, 1], [1, 0, 0, 1, 0, 0, 0], [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0],
      [3, 0, 0, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [1, 1, 0, 0, 0, 0, 0],
      [0, 0, 0, 1, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0]] :=
  rfl


set_option maxHeartbeats 32000000 in
theorem degreeZeroNuQuarticNoABDEFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABDEFG810 A B C D E F G) :
    (degreeZeroNuQuarticNoABDEFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      2 * A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hFpos, hGpos, hAB, hAD, hAE, hAF, hAG, hClt⟩
  have hC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hClt
  rw [speedRefl_degreeZeroNuQuarticNoABDEFG810_eq_polyOf]
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
/-! # SPEED: theorems of `Grok810ScaleZeroQuarticMultiKills7SpeedReflValDegScratch`, part 3 of 24, so that no single
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

theorem nuQuarticFaceABDEFG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeABDEFG810 A B C D E F G)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    : (nuQuarticFaceABDEFG810 A B C D E F G).coeff (2 * A.natDegree + 3 * B.natDegree) =
      (1 / 4096 : k) * nuQuarticInnerABDEFG810 A.leadingCoeff B.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hFpos, hGpos, hAB, hAD, hAE, hAF, hAG, hClt⟩
  simp only [nuQuarticFaceABDEFG810, nuQuarticInnerABDEFG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_A2B3 : ((A ^ 2 * B ^ 3)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 3 hBne), natDegree_pow, natDegree_pow]
  have hcf_A2B3 : ((A ^ 2 * B ^ 3)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * B.leadingCoeff ^ 3 := by
    rw [← hdeg_A2B3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_AB2D : ((A * B ^ 2 * D)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hDne, natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow]
    omega
  have hcf_AB2D : ((A * B ^ 2 * D)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_AB2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_ABG : ((A * B * G)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) hGne, natDegree_mul hAne hBne]
    omega
  have hcf_ABG : ((A * B * G)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_ABG, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_ADE : ((A * D * E)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hDne) hEne, natDegree_mul hAne hDne]
    omega
  have hcf_ADE : ((A * D * E)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_ADE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_B2F : ((B ^ 2 * F)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) hFne, natDegree_pow]
    omega
  have hcf_B2F : ((B ^ 2 * F)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 2 * F.leadingCoeff := by
    rw [← hdeg_B2F, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BD2 : ((B * D ^ 2)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hDne), natDegree_pow]
    omega
  have hcf_BD2 : ((B * D ^ 2)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_BD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_DG : ((D * G)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hDne hGne]
    omega
  have hcf_DG : ((D * G)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      D.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_DG, coeff_natDegree, leadingCoeff_mul]
  have hdeg_EF : ((E * F)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hEne hFne]
    omega
  have hcf_EF : ((E * F)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      E.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_EF, coeff_natDegree, leadingCoeff_mul]
  rw [hcf_A2B3, hcf_AB2D, hcf_ABG, hcf_ADE, hcf_B2F, hcf_BD2, hcf_DG, hcf_EF]
  ring


set_option maxHeartbeats 32000000 in
theorem degreeZeroXiQuartic810_eq_ABDEFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      xiQuarticFaceABDEFG810 A B C D E F G +
        degreeZeroXiQuarticNoABDEFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, degreeZeroXiQuartic810, xiQuarticFaceABDEFG810, degreeZeroXiQuarticNoABDEFG810]
  all_goals module


set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroXiQuarticNoABDEFG810` (53 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroXiQuarticNoABDEFG810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    degreeZeroXiQuarticNoABDEFG810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 256 : k), (45 / 512 : k), (-(25 / 128) : k),
      (-(15 / 128) : k), (-(15 / 128) : k), (-(45 / 262144 * l) : k),
      (9 / 16384 * l : k), (-(9 / 16384 * l) : k), (-(9 / 8192 * l) : k),
      (9 / 4096 * l : k), (-(9 / 8192 * l) : k), (171 / 8192 * l : k),
      (9 / 1024 * l : k), (63 / 2048 * l : k), (-(9 / 512 * l) : k),
      (-(9 / 512 * l) : k), (-(45 / 1024 * l) : k), (-(27 / 256 * l) : k),
      (-(27 / 512 * l) : k), (-(63 / 1024 * l) : k), (9 / 64 * l : k),
      (9 / 64 * l : k), (-(7 / 8192 * beta) : k), (7 / 2048 * beta : k),
      (-(7 / 1024 * beta) : k), (-(7 / 1024 * beta) : k), (7 / 256 * beta : k),
      (7 / 512 * beta : k), (49 / 1024 * beta : k), (7 / 128 * beta : k),
      (-(7 / 64 * beta) : k), (-(7 / 64 * beta) : k), (3 / 64 * gamma : k),
      (3 / 32 * gamma : k), (-(3 / 32 * gamma) : k), (-(3 / 16 * gamma) : k),
      (-(3 / 32 * gamma) : k), (-(5 / 1024 * delta) : k), (5 / 128 * delta : k),
      (5 / 128 * delta : k), (-(5 / 64 * delta) : k), (-(5 / 32 * delta) : k),
      (-(15 / 64 * delta) : k), (1 / 32 * epsilon : k), (-(3 / 16 * epsilon) : k),
      (-(1 / 8 * epsilon) : k), (1 / 2 * epsilon : k), (-(3 / 64 * zeta) : k),
      (-(3 / 16 * zeta) : k), (3 / 8 * zeta : k), (-(1 / 16 * eta) : k),
      (1 / 4 * eta : k), (1 / 8 * theta : k)]
      [
      [1, 1, 1, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0], [0, 1, 1, 0, 0, 1, 0], [0, 0, 2, 0, 1, 0, 0],
      [0, 0, 1, 2, 0, 0, 0], [4, 0, 0, 1, 0, 0, 0], [3, 1, 1, 0, 0, 0, 0], [2, 3, 0, 0, 0, 0, 0],
      [3, 0, 0, 0, 0, 1, 0], [2, 1, 0, 0, 1, 0, 0], [2, 0, 1, 1, 0, 0, 0], [1, 2, 0, 1, 0, 0, 0],
      [1, 1, 2, 0, 0, 0, 0], [0, 3, 1, 0, 0, 0, 0], [1, 0, 1, 0, 0, 1, 0], [1, 0, 0, 1, 1, 0, 0],
      [0, 2, 0, 0, 0, 1, 0], [0, 1, 1, 0, 1, 0, 0], [0, 1, 0, 2, 0, 0, 0], [0, 0, 2, 1, 0, 0, 0],
      [0, 0, 0, 1, 0, 0, 1], [0, 0, 0, 0, 1, 1, 0], [3, 0, 0, 1, 0, 0, 0], [2, 1, 1, 0, 0, 0, 0],
      [1, 3, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 1, 0], [1, 1, 0, 0, 1, 0, 0], [1, 0, 1, 1, 0, 0, 0],
      [0, 2, 0, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0], [0, 0, 0, 1, 1, 0, 0],
      [1, 1, 0, 1, 0, 0, 0], [0, 2, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0],
      [0, 0, 0, 2, 0, 0, 0], [2, 0, 0, 1, 0, 0, 0], [1, 1, 1, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0],
      [1, 0, 0, 0, 0, 1, 0], [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0],
      [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1], [1, 0, 0, 1, 0, 0, 0],
      [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0],
      [0, 0, 0, 1, 0, 0, 0]] :=
  rfl


set_option maxHeartbeats 32000000 in
theorem degreeZeroXiQuarticNoABDEFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABDEFG810 A B C D E F G) :
    (degreeZeroXiQuarticNoABDEFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      A.natDegree + 4 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hFpos, hGpos, hAB, hAD, hAE, hAF, hAG, hClt⟩
  have hC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hClt
  rw [speedRefl_degreeZeroXiQuarticNoABDEFG810_eq_polyOf]
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
/-! # SPEED: theorems of `Grok810ScaleZeroQuarticMultiKills7SpeedReflValDegScratch`, part 4 of 24, so that no single
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

theorem xiQuarticFaceABDEFG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeABDEFG810 A B C D E F G)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    : (xiQuarticFaceABDEFG810 A B C D E F G).coeff (A.natDegree + 4 * B.natDegree) =
      (1 / 2048 : k) * xiQuarticInnerABDEFG810 A.leadingCoeff B.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hFpos, hGpos, hAB, hAD, hAE, hAF, hAG, hClt⟩
  simp only [xiQuarticFaceABDEFG810, xiQuarticInnerABDEFG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_AB4 : ((A * B ^ 4)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 4 hBne), natDegree_pow]
  have hcf_AB4 : ((A * B ^ 4)).coeff (A.natDegree + 4 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 4 := by
    rw [← hdeg_AB4, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_AB2E : ((A * B ^ 2 * E)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hEne, natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow]
    omega
  have hcf_AB2E : ((A * B ^ 2 * E)).coeff (A.natDegree + 4 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hdeg_AB2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_ADF : ((A * D * F)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hDne) hFne, natDegree_mul hAne hDne]
    omega
  have hcf_ADF : ((A * D * F)).coeff (A.natDegree + 4 * B.natDegree) =
      A.leadingCoeff * D.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_ADF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_B3D : ((B ^ 3 * D)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) hDne, natDegree_pow]
    omega
  have hcf_B3D : ((B ^ 3 * D)).coeff (A.natDegree + 4 * B.natDegree) =
      B.leadingCoeff ^ 3 * D.leadingCoeff := by
    rw [← hdeg_B3D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B2G : ((B ^ 2 * G)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) hGne, natDegree_pow]
    omega
  have hcf_B2G : ((B ^ 2 * G)).coeff (A.natDegree + 4 * B.natDegree) =
      B.leadingCoeff ^ 2 * G.leadingCoeff := by
    rw [← hdeg_B2G, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BDE : ((B * D * E)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hDne) hEne, natDegree_mul hBne hDne]
    omega
  have hcf_BDE : ((B * D * E)).coeff (A.natDegree + 4 * B.natDegree) =
      B.leadingCoeff * D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_BDE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_EG : ((E * G)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul hEne hGne]
    omega
  have hcf_EG : ((E * G)).coeff (A.natDegree + 4 * B.natDegree) =
      E.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_EG, coeff_natDegree, leadingCoeff_mul]
  have hdeg_F2 : (F ^ 2).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_F2 : (F ^ 2).coeff (A.natDegree + 4 * B.natDegree) =
      F.leadingCoeff ^ 2 := by
    rw [← hdeg_F2, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_AB4, hcf_AB2E, hcf_ADF, hcf_B3D, hcf_B2G, hcf_BDE, hcf_EG, hcf_F2]
  ring


set_option maxHeartbeats 32000000 in
theorem degreeZeroOmicronQuartic810_eq_ABDEFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      omicronQuarticFaceABDEFG810 A B C D E F G +
        degreeZeroOmicronQuarticNoABDEFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, degreeZeroOmicronQuartic810, omicronQuarticFaceABDEFG810, degreeZeroOmicronQuarticNoABDEFG810]
  all_goals module


set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroOmicronQuarticNoABDEFG810` (88 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroOmicronQuarticNoABDEFG810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    degreeZeroOmicronQuarticNoABDEFG810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 16384 : k), (-(35 / 2048) : k), (-(5 / 2048) : k),
      (15 / 512 : k), (15 / 1024 : k), (135 / 1024 : k),
      (45 / 1024 : k), (-(15 / 128) : k), (-(5 / 64) : k),
      (-(25 / 128) : k), (135 / 33554432 * l : k), (225 / 2097152 * l : k),
      (-(171 / 4194304 * l) : k), (81 / 262144 * l : k), (-(9 / 65536 * l) : k),
      (99 / 131072 * l : k), (-(45 / 131072 * l) : k), (-(189 / 65536 * l) : k),
      (9 / 8192 * l : k), (-(9 / 4096 * l) : k), (27 / 8192 * l : k),
      (45 / 4096 * l : k), (99 / 4096 * l : k), (9 / 8192 * l : k),
      (189 / 8192 * l : k), (567 / 16384 * l : k), (9 / 512 * l : k),
      (-(9 / 256 * l) : k), (-(27 / 1024 * l) : k), (-(9 / 128 * l) : k),
      (-(45 / 512 * l) : k), (-(45 / 1024 * l) : k), (-(27 / 512 * l) : k),
      (9 / 64 * l : k), (9 / 128 * l : k), (35 / 2097152 * beta : k),
      (49 / 131072 * beta : k), (-(35 / 131072 * beta) : k), (7 / 8192 * beta : k),
      (-(7 / 4096 * beta) : k), (21 / 8192 * beta : k), (-(91 / 8192 * beta) : k),
      (-(189 / 32768 * beta) : k), (7 / 512 * beta : k), (7 / 512 * beta : k),
      (35 / 1024 * beta : k), (21 / 256 * beta : k), (7 / 512 * beta : k),
      (-(7 / 64 * beta) : k), (-(7 / 128 * beta) : k), (3 / 2048 * gamma : k),
      (-(9 / 1024 * gamma) : k), (-(3 / 512 * gamma) : k), (3 / 128 * gamma : k),
      (3 / 128 * gamma : k), (9 / 128 * gamma : k), (9 / 128 * gamma : k),
      (-(3 / 32 * gamma) : k), (-(3 / 16 * gamma) : k), (9 / 131072 * delta : k),
      (5 / 4096 * delta : k), (-(5 / 4096 * delta) : k), (5 / 128 * delta : k),
      (5 / 512 * delta : k), (45 / 512 * delta : k), (-(5 / 64 * delta) : k),
      (-(5 / 32 * delta) : k), (-(15 / 128 * delta) : k), (-(1 / 256 * epsilon) : k),
      (1 / 32 * epsilon : k), (1 / 32 * epsilon : k), (-(1 / 16 * epsilon) : k),
      (-(1 / 8 * epsilon) : k), (-(3 / 16 * epsilon) : k), (9 / 32768 * zeta : k),
      (3 / 1024 * zeta : k), (9 / 512 * zeta : k), (-(9 / 64 * zeta) : k),
      (-(9 / 128 * zeta) : k), (3 / 8 * zeta : k), (-(1 / 512 * eta) : k),
      (-(1 / 32 * eta) : k), (-(3 / 32 * eta) : k), (1 / 4 * eta : k),
      (1 / 1024 * theta : k), (1 / 64 * theta : k), (-(3 / 128 * theta) : k),
      (1 / 8 * theta : k)]
      [
      [2, 1, 2, 0, 0, 0, 0], [1, 3, 1, 0, 0, 0, 0], [2, 0, 1, 0, 0, 1, 0], [1, 1, 1, 0, 1, 0, 0],
      [1, 0, 2, 1, 0, 0, 0], [0, 2, 1, 1, 0, 0, 0], [0, 1, 3, 0, 0, 0, 0], [0, 1, 1, 0, 0, 0, 1],
      [0, 0, 2, 0, 0, 1, 0], [0, 0, 1, 1, 1, 0, 0], [7, 0, 0, 0, 0, 0, 0], [5, 0, 1, 0, 0, 0, 0],
      [4, 2, 0, 0, 0, 0, 0], [4, 0, 0, 0, 1, 0, 0], [3, 1, 0, 1, 0, 0, 0], [3, 0, 2, 0, 0, 0, 0],
      [2, 2, 1, 0, 0, 0, 0], [1, 4, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 0, 1], [2, 1, 0, 0, 0, 1, 0],
      [2, 0, 1, 0, 1, 0, 0], [1, 2, 0, 0, 1, 0, 0], [1, 1, 1, 1, 0, 0, 0], [1, 0, 3, 0, 0, 0, 0],
      [0, 3, 0, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0], [1, 0, 1, 0, 0, 0, 1], [1, 0, 0, 1, 0, 1, 0],
      [0, 2, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 1, 0], [0, 1, 0, 1, 1, 0, 0], [0, 0, 2, 0, 1, 0, 0],
      [0, 0, 1, 2, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1], [0, 0, 0, 0, 0, 2, 0], [6, 0, 0, 0, 0, 0, 0],
      [4, 0, 1, 0, 0, 0, 0], [3, 2, 0, 0, 0, 0, 0], [3, 0, 0, 0, 1, 0, 0], [2, 1, 0, 1, 0, 0, 0],
      [2, 0, 2, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [1, 0, 1, 0, 1, 0, 0],
      [1, 0, 0, 2, 0, 0, 0], [0, 2, 0, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0],
      [0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0], [2, 1, 1, 0, 0, 0, 0], [1, 3, 0, 0, 0, 0, 0],
      [2, 0, 0, 0, 0, 1, 0], [1, 1, 0, 0, 1, 0, 0], [1, 0, 1, 1, 0, 0, 0], [0, 2, 0, 1, 0, 0, 0],
      [0, 1, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0], [0, 0, 0, 1, 1, 0, 0], [5, 0, 0, 0, 0, 0, 0],
      [3, 0, 1, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0], [1, 1, 0, 1, 0, 0, 0], [1, 0, 2, 0, 0, 0, 0],
      [0, 2, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0],
      [2, 0, 0, 1, 0, 0, 0], [1, 1, 1, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0],
      [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0], [4, 0, 0, 0, 0, 0, 0], [2, 0, 1, 0, 0, 0, 0],
      [1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1],
      [2, 1, 0, 0, 0, 0, 0], [1, 0, 0, 1, 0, 0, 0], [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0],
      [3, 0, 0, 0, 0, 0, 0], [1, 0, 1, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0]] :=
  rfl


set_option maxHeartbeats 32000000 in
theorem degreeZeroOmicronQuarticNoABDEFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABDEFG810 A B C D E F G) :
    (degreeZeroOmicronQuarticNoABDEFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      3 * A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hFpos, hGpos, hAB, hAD, hAE, hAF, hAG, hClt⟩
  have hC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hClt
  rw [speedRefl_degreeZeroOmicronQuarticNoABDEFG810_eq_polyOf]
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
/-! # SPEED: theorems of `Grok810ScaleZeroQuarticMultiKills7SpeedReflValDegScratch`, part 5 of 24, so that no single
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

theorem omicronQuarticFaceABDEFG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeABDEFG810 A B C D E F G)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    : (omicronQuarticFaceABDEFG810 A B C D E F G).coeff (3 * A.natDegree + 3 * B.natDegree) =
      (1 / 65536 : k) * omicronQuarticInnerABDEFG810 A.leadingCoeff B.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hFpos, hGpos, hAB, hAD, hAE, hAF, hAG, hClt⟩
  simp only [omicronQuarticFaceABDEFG810, omicronQuarticInnerABDEFG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_A3B3 : ((A ^ 3 * B ^ 3)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hAne) (pow_ne_zero 3 hBne), natDegree_pow, natDegree_pow]
  have hcf_A3B3 : ((A ^ 3 * B ^ 3)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 3 * B.leadingCoeff ^ 3 := by
    rw [← hdeg_A3B3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_A2B2D : ((A ^ 2 * B ^ 2 * D)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) (pow_ne_zero 2 hBne)) hDne, natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 2 hBne), natDegree_pow, natDegree_pow]
    omega
  have hcf_A2B2D : ((A ^ 2 * B ^ 2 * D)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * B.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_A2B2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_A2BG : ((A ^ 2 * B * G)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hBne) hGne, natDegree_mul (pow_ne_zero 2 hAne) hBne, natDegree_pow]
    omega
  have hcf_A2BG : ((A ^ 2 * B * G)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * B.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_A2BG, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_A2DE : ((A ^ 2 * D * E)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hDne) hEne, natDegree_mul (pow_ne_zero 2 hAne) hDne, natDegree_pow]
    omega
  have hcf_A2DE : ((A ^ 2 * D * E)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_A2DE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_AB2F : ((A * B ^ 2 * F)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hFne, natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow]
    omega
  have hcf_AB2F : ((A * B ^ 2 * F)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * F.leadingCoeff := by
    rw [← hdeg_AB2F, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_ABD2 : ((A * B * D ^ 2)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) (pow_ne_zero 2 hDne), natDegree_mul hAne hBne, natDegree_pow]
    omega
  have hcf_ABD2 : ((A * B * D ^ 2)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_ABD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_ADG : ((A * D * G)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hDne) hGne, natDegree_mul hAne hDne]
    omega
  have hcf_ADG : ((A * D * G)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * D.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_ADG, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_AEF : ((A * E * F)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hEne) hFne, natDegree_mul hAne hEne]
    omega
  have hcf_AEF : ((A * E * F)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * E.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_AEF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_B5 : (B ^ 5).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_B5 : (B ^ 5).coeff (3 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 5 := by
    rw [← hdeg_B5, coeff_natDegree, leadingCoeff_pow]
  have hdeg_B3E : ((B ^ 3 * E)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) hEne, natDegree_pow]
    omega
  have hcf_B3E : ((B ^ 3 * E)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 3 * E.leadingCoeff := by
    rw [← hdeg_B3E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BDF : ((B * D * F)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hDne) hFne, natDegree_mul hBne hDne]
    omega
  have hcf_BDF : ((B * D * F)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * D.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_BDF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_BE2 : ((B * E ^ 2)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hEne), natDegree_pow]
    omega
  have hcf_BE2 : ((B * E ^ 2)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * E.leadingCoeff ^ 2 := by
    rw [← hdeg_BE2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_D3 : (D ^ 3).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_D3 : (D ^ 3).coeff (3 * A.natDegree + 3 * B.natDegree) =
      D.leadingCoeff ^ 3 := by
    rw [← hdeg_D3, coeff_natDegree, leadingCoeff_pow]
  have hdeg_FG : ((F * G)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hFne hGne]
    omega
  have hcf_FG : ((F * G)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      F.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_FG, coeff_natDegree, leadingCoeff_mul]
  rw [hcf_A3B3, hcf_A2B2D, hcf_A2BG, hcf_A2DE, hcf_AB2F, hcf_ABD2, hcf_ADG, hcf_AEF, hcf_B5, hcf_B3E, hcf_BDF, hcf_BE2, hcf_D3, hcf_FG]
  ring


set_option maxHeartbeats 32000000 in
theorem degreeZeroPiQuartic810_eq_ABDEFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      piQuarticFaceABDEFG810 A B C D E F G +
        degreeZeroPiQuarticNoABDEFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, degreeZeroPiQuartic810, piBaseGroupQuartic810,
    piBetaGroupQuartic810, piGammaGroupQuartic810, piDeltaGroupQuartic810,
    piEpsilonGroupQuartic810, piZetaGroupQuartic810, piEtaGroupQuartic810,
    piThetaGroupQuartic810, piQuarticFaceABDEFG810, degreeZeroPiQuarticNoABDEFG810]
  all_goals module


set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroPiQuarticNoABDEFG810` (84 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroPiQuarticNoABDEFG810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    degreeZeroPiQuarticNoABDEFG810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(45 / 512) : k), (-(35 / 256) : k), (5 / 32 : k),
      (5 / 32 : k), (45 / 64 : k), (45 / 64 : k),
      (15 / 256 : k), (-(5 / 16) : k), (-(15 / 16) : k),
      (-(5 / 8) : k), (45 / 131072 * l : k), (-(3 / 32768 * l) : k),
      (-(45 / 32768 * l) : k), (9 / 4096 * l : k), (9 / 4096 * l : k),
      (-(27 / 4096 * l) : k), (9 / 4096 * l : k), (-(189 / 4096 * l) : k),
      (-(63 / 4096 * l) : k), (-(27 / 1024 * l) : k), (9 / 512 * l : k),
      (63 / 1024 * l : k), (9 / 128 * l : k), (27 / 256 * l : k),
      (9 / 256 * l : k), (63 / 512 * l : k), (189 / 512 * l : k),
      (63 / 512 * l : k), (-(9 / 64 * l) : k), (-(9 / 32 * l) : k),
      (-(27 / 64 * l) : k), (-(9 / 32 * l) : k), (-(27 / 128 * l) : k),
      (-(9 / 16 * l) : k), (-(3 / 32 * l) : k), (9 / 8 * l : k),
      (7 / 4096 * beta : k), (7 / 4096 * beta : k), (-(7 / 1024 * beta) : k),
      (7 / 512 * beta : k), (7 / 512 * beta : k), (-(21 / 256 * beta) : k),
      (-(7 / 256 * beta) : k), (-(63 / 512 * beta) : k), (-(7 / 64 * beta) : k),
      (7 / 32 * beta : k), (21 / 128 * beta : k), (7 / 16 * beta : k),
      (7 / 32 * beta : k), (7 / 32 * beta : k), (-(7 / 8 * beta) : k),
      (-(3 / 32 * gamma) : k), (-(15 / 256 * gamma) : k), (3 / 16 * gamma : k),
      (3 / 8 * gamma : k), (3 / 4 * gamma : k), (1 / 8 * gamma : k),
      (-(3 / 4 * gamma) : k), (-(3 / 4 * gamma) : k), (5 / 512 * delta : k),
      (-(15 / 256 * delta) : k), (-(5 / 128 * delta) : k), (5 / 32 * delta : k),
      (5 / 32 * delta : k), (15 / 32 * delta : k), (15 / 32 * delta : k),
      (-(5 / 8 * delta) : k), (-(5 / 4 * delta) : k), (1 / 4 * epsilon : k),
      (1 / 2 * epsilon : k), (-(1 / 2 * epsilon) : k), (-(1 * epsilon) : k),
      (-(1 / 2 * epsilon) : k), (3 / 32 * zeta : k), (5 / 32 * zeta : k),
      (-(3 / 8 * zeta) : k), (-(3 / 4 * zeta) : k), (-(3 / 4 * zeta) : k),
      (1 / 16 * eta : k), (-(1 / 2 * eta) : k), (-(1 / 4 * eta) : k),
      (2 * eta : k), (-(1 / 4 * theta) : k), (1 * theta : k)]
      [
      [1, 2, 2, 0, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0], [1, 1, 1, 0, 0, 1, 0], [1, 0, 1, 2, 0, 0, 0],
      [0, 2, 1, 0, 1, 0, 0], [0, 1, 2, 1, 0, 0, 0], [0, 0, 4, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 1],
      [0, 0, 1, 1, 0, 1, 0], [0, 0, 1, 0, 2, 0, 0], [4, 1, 1, 0, 0, 0, 0], [3, 3, 0, 0, 0, 0, 0],
      [4, 0, 0, 0, 0, 1, 0], [3, 1, 0, 0, 1, 0, 0], [3, 0, 1, 1, 0, 0, 0], [2, 2, 0, 1, 0, 0, 0],
      [2, 1, 2, 0, 0, 0, 0], [1, 3, 1, 0, 0, 0, 0], [0, 5, 0, 0, 0, 0, 0], [2, 0, 1, 0, 0, 1, 0],
      [2, 0, 0, 1, 1, 0, 0], [1, 2, 0, 0, 0, 1, 0], [1, 1, 1, 0, 1, 0, 0], [1, 1, 0, 2, 0, 0, 0],
      [1, 0, 2, 1, 0, 0, 0], [0, 3, 0, 0, 1, 0, 0], [0, 2, 1, 1, 0, 0, 0], [0, 1, 3, 0, 0, 0, 0],
      [1, 0, 0, 0, 1, 1, 0], [0, 1, 1, 0, 0, 0, 1], [0, 1, 0, 1, 0, 1, 0], [0, 1, 0, 0, 2, 0, 0],
      [0, 0, 2, 0, 0, 1, 0], [0, 0, 1, 1, 1, 0, 0], [0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1],
      [3, 1, 1, 0, 0, 0, 0], [2, 3, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 1, 0], [2, 1, 0, 0, 1, 0, 0],
      [2, 0, 1, 1, 0, 0, 0], [1, 2, 0, 1, 0, 0, 0], [1, 1, 2, 0, 0, 0, 0], [0, 3, 1, 0, 0, 0, 0],
      [1, 0, 1, 0, 0, 1, 0], [1, 0, 0, 1, 1, 0, 0], [0, 2, 0, 0, 0, 1, 0], [0, 1, 1, 0, 1, 0, 0],
      [0, 1, 0, 2, 0, 0, 0], [0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 0, 1, 1, 0], [1, 2, 1, 0, 0, 0, 0],
      [0, 4, 0, 0, 0, 0, 0], [1, 0, 0, 2, 0, 0, 0], [0, 2, 0, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0, 0],
      [0, 0, 3, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0], [2, 1, 1, 0, 0, 0, 0],
      [1, 3, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 1, 0], [1, 1, 0, 0, 1, 0, 0], [1, 0, 1, 1, 0, 0, 0],
      [0, 2, 0, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0], [0, 0, 0, 1, 1, 0, 0],
      [1, 1, 0, 1, 0, 0, 0], [0, 2, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0],
      [0, 0, 0, 2, 0, 0, 0], [1, 1, 1, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0],
      [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0],
      [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0]] :=
  rfl


end QuarticKills810

end Max11DegreeRoutes

end
/-! # SPEED: theorems of `Grok810ScaleZeroQuarticMultiKills7SpeedReflValDegScratch`, part 8 of 24, so that no single
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

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaQuartic810_eq_ACDEFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceACDEFG810 A B C D E F G +
        degreeZeroKappaQuarticNoACDEFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, degreeZeroKappaQuartic810, kappaQuarticFaceACDEFG810, degreeZeroKappaQuarticNoACDEFG810]
  all_goals module


set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroKappaQuarticNoACDEFG810` (33 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroKappaQuarticNoACDEFG810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    degreeZeroKappaQuarticNoACDEFG810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (5 / 512 : k), (-(15 / 128) : k), (-(15 / 128) : k),
      (5 / 16 : k), (63 / 262144 * l : k), (45 / 8192 * l : k),
      (-(9 / 16384 * l) : k), (27 / 1024 * l : k), (-(9 / 512 * l) : k),
      (9 / 1024 * l : k), (-(63 / 1024 * l) : k), (9 / 64 * l : k),
      (9 / 64 * l : k), (9 / 64 * l : k), (9 / 128 * l : k),
      (35 / 32768 * beta : k), (21 / 1024 * beta : k), (7 / 1024 * beta : k),
      (7 / 64 * beta : k), (-(7 / 64 * beta) : k), (-(7 / 128 * beta) : k),
      (7 / 8 * beta : k), (-(3 / 16 * gamma) : k), (3 / 4 * gamma : k),
      (5 / 1024 * delta : k), (5 / 64 * delta : k), (-(15 / 128 * delta) : k),
      (5 / 8 * delta : k), (1 / 2 * epsilon : k), (3 / 128 * zeta : k),
      (3 / 8 * zeta : k), (1 / 4 * eta : k), (1 / 8 * theta : k)]
      [
      [1, 3, 0, 0, 0, 0, 0], [0, 2, 0, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 1],
      [5, 0, 0, 0, 0, 0, 0], [3, 0, 1, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0], [2, 0, 0, 0, 1, 0, 0],
      [1, 1, 0, 1, 0, 0, 0], [1, 0, 2, 0, 0, 0, 0], [0, 2, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1],
      [0, 1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0], [4, 0, 0, 0, 0, 0, 0],
      [2, 0, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 0], [0, 1, 0, 1, 0, 0, 0],
      [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0],
      [3, 0, 0, 0, 0, 0, 0], [1, 0, 1, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0],
      [0, 0, 0, 1, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0],
      [1, 0, 0, 0, 0, 0, 0]] :=
  rfl


set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaQuarticNoACDEFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeACDEFG810 A B C D E F G) :
    (degreeZeroKappaQuarticNoACDEFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      C.natDegree + F.natDegree := by
  rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hFpos, hGpos, hAC, hAD, hAE, hAF, hAG, hBlt⟩
  have hB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hBlt
  rw [speedRefl_degreeZeroKappaQuarticNoACDEFG810_eq_polyOf]
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


theorem kappaQuarticFaceACDEFG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeACDEFG810 A B C D E F G)
    (hAne : A ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    : (kappaQuarticFaceACDEFG810 A B C D E F G).coeff (C.natDegree + F.natDegree) =
      (1 / 16 : k) * kappaQuarticInnerACDEFG810 A.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hFpos, hGpos, hAC, hAD, hAE, hAF, hAG, hBlt⟩
  simp only [kappaQuarticFaceACDEFG810, kappaQuarticInnerACDEFG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_CF : ((C * F)).natDegree = C.natDegree + F.natDegree := by
    rw [natDegree_mul hCne hFne]
  have hcf_CF : ((C * F)).coeff (C.natDegree + F.natDegree) =
      C.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_CF, coeff_natDegree, leadingCoeff_mul]
  have hdeg_DE : ((D * E)).natDegree = C.natDegree + F.natDegree := by
    rw [natDegree_mul hDne hEne]
    omega
  have hcf_DE : ((D * E)).coeff (C.natDegree + F.natDegree) =
      D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_DE, coeff_natDegree, leadingCoeff_mul]
  rw [hcf_CF, hcf_DE]
  ring


end QuarticKills810

end Max11DegreeRoutes

end
/-! # SPEED: theorems of `Grok810ScaleZeroQuarticMultiKills7SpeedReflValDegScratch`, part 9 of 24, so that no single
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

set_option maxHeartbeats 16000000 in
theorem degreeZeroMuQuartic810_eq_ACDEFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticFaceACDEFG810 A B C D E F G +
        degreeZeroMuQuarticNoACDEFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, degreeZeroMuQuartic810, muQuarticFaceACDEFG810, degreeZeroMuQuarticNoACDEFG810]
  all_goals module


set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroMuQuarticNoACDEFG810` (38 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroMuQuarticNoACDEFG810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    degreeZeroMuQuarticNoACDEFG810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 512 : k), (35 / 2048 : k), (-(5 / 64) : k),
      (-(15 / 128) : k), (-(15 / 64) : k), (-(45 / 262144 * l) : k),
      (-(9 / 8192 * l) : k), (-(9 / 8192 * l) : k), (63 / 8192 * l : k),
      (-(9 / 1024 * l) : k), (-(9 / 512 * l) : k), (-(9 / 512 * l) : k),
      (-(63 / 1024 * l) : k), (-(63 / 1024 * l) : k), (9 / 64 * l : k),
      (9 / 64 * l : k), (9 / 64 * l : k), (-(7 / 8192 * beta) : k),
      (-(7 / 1024 * beta) : k), (7 / 512 * beta : k), (21 / 1024 * beta : k),
      (-(7 / 64 * beta) : k), (-(7 / 64 * beta) : k), (-(7 / 64 * beta) : k),
      (3 / 128 * gamma : k), (-(3 / 16 * gamma) : k), (-(3 / 32 * gamma) : k),
      (3 / 4 * gamma : k), (-(5 / 1024 * delta) : k), (-(5 / 64 * delta) : k),
      (-(15 / 64 * delta) : k), (5 / 8 * delta : k), (-(1 / 8 * epsilon) : k),
      (1 / 2 * epsilon : k), (-(3 / 64 * zeta) : k), (3 / 8 * zeta : k),
      (1 / 4 * eta : k), (1 / 8 * theta : k)]
      [
      [1, 2, 1, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 1, 0], [0, 2, 0, 0, 1, 0, 0],
      [0, 1, 1, 1, 0, 0, 0], [4, 1, 0, 0, 0, 0, 0], [3, 0, 0, 1, 0, 0, 0], [2, 1, 1, 0, 0, 0, 0],
      [1, 3, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 1, 0], [1, 1, 0, 0, 1, 0, 0], [1, 0, 1, 1, 0, 0, 0],
      [0, 2, 0, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 1], [0, 0, 1, 0, 0, 1, 0],
      [0, 0, 0, 1, 1, 0, 0], [3, 1, 0, 0, 0, 0, 0], [2, 0, 0, 1, 0, 0, 0], [1, 1, 1, 0, 0, 0, 0],
      [0, 3, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0], [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0],
      [1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1],
      [2, 1, 0, 0, 0, 0, 0], [1, 0, 0, 1, 0, 0, 0], [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0],
      [0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0],
      [0, 0, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0]] :=
  rfl


set_option maxHeartbeats 16000000 in
theorem degreeZeroMuQuarticNoACDEFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeACDEFG810 A B C D E F G) :
    (degreeZeroMuQuarticNoACDEFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      A.natDegree + 2 * D.natDegree := by
  rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hFpos, hGpos, hAC, hAD, hAE, hAF, hAG, hBlt⟩
  have hB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hBlt
  rw [speedRefl_degreeZeroMuQuarticNoACDEFG810_eq_polyOf]
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


theorem muQuarticFaceACDEFG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeACDEFG810 A B C D E F G)
    (hAne : A ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    : (muQuarticFaceACDEFG810 A B C D E F G).coeff (A.natDegree + 2 * D.natDegree) =
      (1 / 128 : k) * muQuarticInnerACDEFG810 A.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hFpos, hGpos, hAC, hAD, hAE, hAF, hAG, hBlt⟩
  simp only [muQuarticFaceACDEFG810, muQuarticInnerACDEFG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_AD2 : ((A * D ^ 2)).natDegree = A.natDegree + 2 * D.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 2 hDne), natDegree_pow]
  have hcf_AD2 : ((A * D ^ 2)).coeff (A.natDegree + 2 * D.natDegree) =
      A.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_AD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_C3 : (C ^ 3).natDegree = A.natDegree + 2 * D.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_C3 : (C ^ 3).coeff (A.natDegree + 2 * D.natDegree) =
      C.leadingCoeff ^ 3 := by
    rw [← hdeg_C3, coeff_natDegree, leadingCoeff_pow]
  have hdeg_CG : ((C * G)).natDegree = A.natDegree + 2 * D.natDegree := by
    rw [natDegree_mul hCne hGne]
    omega
  have hcf_CG : ((C * G)).coeff (A.natDegree + 2 * D.natDegree) =
      C.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_CG, coeff_natDegree, leadingCoeff_mul]
  have hdeg_DF : ((D * F)).natDegree = A.natDegree + 2 * D.natDegree := by
    rw [natDegree_mul hDne hFne]
    omega
  have hcf_DF : ((D * F)).coeff (A.natDegree + 2 * D.natDegree) =
      D.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_DF, coeff_natDegree, leadingCoeff_mul]
  have hdeg_E2 : (E ^ 2).natDegree = A.natDegree + 2 * D.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_E2 : (E ^ 2).coeff (A.natDegree + 2 * D.natDegree) =
      E.leadingCoeff ^ 2 := by
    rw [← hdeg_E2, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_AD2, hcf_C3, hcf_CG, hcf_DF, hcf_E2]
  ring


end QuarticKills810

end Max11DegreeRoutes

end
/-! # SPEED: theorems of `Grok810ScaleZeroQuarticMultiKills7SpeedReflValDegScratch`, part 10 of 24, so that no single
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

set_option maxHeartbeats 32000000 in
theorem degreeZeroNuQuartic810_eq_ACDEFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      nuQuarticFaceACDEFG810 A B C D E F G +
        degreeZeroNuQuarticNoACDEFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, degreeZeroNuQuartic810, nuQuarticFaceACDEFG810, degreeZeroNuQuarticNoACDEFG810]
  all_goals module


set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroNuQuarticNoACDEFG810` (54 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroNuQuarticNoACDEFG810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    degreeZeroNuQuarticNoACDEFG810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 4096) : k), (45 / 1024 : k), (15 / 1024 : k),
      (35 / 512 : k), (-(5 / 128) : k), (-(15 / 128) : k),
      (-(15 / 64) : k), (-(15 / 128) : k), (105 / 4194304 * l : k),
      (135 / 262144 * l : k), (9 / 4096 * l : k), (9 / 8192 * l : k),
      (9 / 16384 * l : k), (63 / 4096 * l : k), (315 / 32768 * l : k),
      (9 / 1024 * l : k), (-(9 / 256 * l) : k), (-(9 / 512 * l) : k),
      (-(63 / 1024 * l) : k), (-(63 / 512 * l) : k), (-(21 / 1024 * l) : k),
      (9 / 64 * l : k), (9 / 64 * l : k), (9 / 128 * l : k),
      (7 / 65536 * beta : k), (7 / 4096 * beta : k), (-(7 / 16384 * beta) : k),
      (7 / 1024 * beta : k), (7 / 256 * beta : k), (63 / 1024 * beta : k),
      (-(7 / 64 * beta) : k), (-(7 / 64 * beta) : k), (-(7 / 128 * beta) : k),
      (3 / 128 * gamma : k), (5 / 128 * gamma : k), (-(3 / 32 * gamma) : k),
      (-(3 / 16 * gamma) : k), (-(3 / 16 * gamma) : k), (15 / 32768 * delta : k),
      (5 / 1024 * delta : k), (15 / 512 * delta : k), (-(15 / 64 * delta) : k),
      (-(15 / 128 * delta) : k), (5 / 8 * delta : k), (-(1 / 16 * epsilon) : k),
      (-(1 / 4 * epsilon) : k), (1 / 2 * epsilon : k), (1 / 512 * zeta : k),
      (-(15 / 128 * zeta) : k), (3 / 8 * zeta : k), (-(1 / 32 * eta) : k),
      (1 / 4 * eta : k), (1 / 128 * theta : k), (1 / 8 * theta : k)]
      [
      [2, 3, 0, 0, 0, 0, 0], [1, 2, 0, 1, 0, 0, 0], [1, 1, 2, 0, 0, 0, 0], [0, 3, 1, 0, 0, 0, 0],
      [1, 1, 0, 0, 0, 0, 1], [0, 2, 0, 0, 0, 1, 0], [0, 1, 1, 0, 1, 0, 0], [0, 1, 0, 2, 0, 0, 0],
      [6, 0, 0, 0, 0, 0, 0], [4, 0, 1, 0, 0, 0, 0], [3, 0, 0, 0, 1, 0, 0], [2, 1, 0, 1, 0, 0, 0],
      [2, 0, 2, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0, 1],
      [1, 1, 0, 0, 0, 1, 0], [1, 0, 0, 2, 0, 0, 0], [0, 2, 0, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0, 0],
      [0, 0, 3, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 1], [0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0],
      [5, 0, 0, 0, 0, 0, 0], [3, 0, 1, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0], [2, 0, 0, 0, 1, 0, 0],
      [1, 1, 0, 1, 0, 0, 0], [0, 2, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0],
      [0, 0, 0, 2, 0, 0, 0], [1, 1, 1, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0],
      [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0], [4, 0, 0, 0, 0, 0, 0], [2, 0, 1, 0, 0, 0, 0],
      [1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1],
      [1, 0, 0, 1, 0, 0, 0], [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0], [3, 0, 0, 0, 0, 0, 0],
      [0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0],
      [2, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0]] :=
  rfl


set_option maxHeartbeats 32000000 in
theorem degreeZeroNuQuarticNoACDEFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeACDEFG810 A B C D E F G) :
    (degreeZeroNuQuarticNoACDEFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      A.natDegree + C.natDegree + F.natDegree := by
  rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hFpos, hGpos, hAC, hAD, hAE, hAF, hAG, hBlt⟩
  have hB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hBlt
  rw [speedRefl_degreeZeroNuQuarticNoACDEFG810_eq_polyOf]
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


theorem nuQuarticFaceACDEFG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeACDEFG810 A B C D E F G)
    (hAne : A ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    : (nuQuarticFaceACDEFG810 A B C D E F G).coeff (A.natDegree + C.natDegree + F.natDegree) =
      (1 / 128 : k) * nuQuarticInnerACDEFG810 A.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hFpos, hGpos, hAC, hAD, hAE, hAF, hAG, hBlt⟩
  simp only [nuQuarticFaceACDEFG810, nuQuarticInnerACDEFG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_ACF : ((A * C * F)).natDegree = A.natDegree + C.natDegree + F.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hCne) hFne, natDegree_mul hAne hCne]
  have hcf_ACF : ((A * C * F)).coeff (A.natDegree + C.natDegree + F.natDegree) =
      A.leadingCoeff * C.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_ACF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_ADE : ((A * D * E)).natDegree = A.natDegree + C.natDegree + F.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hDne) hEne, natDegree_mul hAne hDne]
    omega
  have hcf_ADE : ((A * D * E)).coeff (A.natDegree + C.natDegree + F.natDegree) =
      A.leadingCoeff * D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_ADE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_C2D : ((C ^ 2 * D)).natDegree = A.natDegree + C.natDegree + F.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hDne, natDegree_pow]
    omega
  have hcf_C2D : ((C ^ 2 * D)).coeff (A.natDegree + C.natDegree + F.natDegree) =
      C.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_C2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_DG : ((D * G)).natDegree = A.natDegree + C.natDegree + F.natDegree := by
    rw [natDegree_mul hDne hGne]
    omega
  have hcf_DG : ((D * G)).coeff (A.natDegree + C.natDegree + F.natDegree) =
      D.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_DG, coeff_natDegree, leadingCoeff_mul]
  have hdeg_EF : ((E * F)).natDegree = A.natDegree + C.natDegree + F.natDegree := by
    rw [natDegree_mul hEne hFne]
    omega
  have hcf_EF : ((E * F)).coeff (A.natDegree + C.natDegree + F.natDegree) =
      E.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_EF, coeff_natDegree, leadingCoeff_mul]
  rw [hcf_ACF, hcf_ADE, hcf_C2D, hcf_DG, hcf_EF]
  ring


end QuarticKills810

end Max11DegreeRoutes

end
