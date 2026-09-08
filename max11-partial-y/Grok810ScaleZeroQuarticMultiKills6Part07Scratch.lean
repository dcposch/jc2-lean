import Grok810ScaleZeroQuarticMultiKills6Part06Scratch

/-! # Part 7 of `Grok810ScaleZeroQuarticMultiKills6Scratch`.

One declaration split out of `Grok810ScaleZeroQuarticMultiKills6Scratch`; statements are byte-identical.
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

def piQuarticInnerABCDFG810 (a b c d f g : k) : k :=
  15 * a ^ 2 * b ^ 4 + (-480 : k) * a * b ^ 3 * d + (-360 : k) * a * b ^ 2 * c ^ 2 + 320 * a * b ^ 2 * g + 640 * a * b * c * f + 640 * a * c * d ^ 2 + (-1280 : k) * a * f ^ 2 + (-560 : k) * b ^ 4 * c + 800 * b ^ 3 * f + 1440 * b ^ 2 * d ^ 2 + 2880 * b * c ^ 2 * d + (-2560 : k) * b * d * g + 240 * c ^ 4 + (-1280 : k) * c ^ 2 * g + (-3840 : k) * c * d * f + 5120 * g ^ 2

def primitiveQuarticInnerABCDFG810 (a b c d f g : k) : k :=
  (-5 : k) * a ^ 4 * b ^ 3 + (-60 : k) * a ^ 3 * b ^ 2 * d + 60 * a ^ 3 * b * c ^ 2 + (-160 : k) * a ^ 3 * b * g + (-160 : k) * a ^ 3 * c * f + 120 * a ^ 2 * b ^ 3 * c + (-160 : k) * a ^ 2 * b ^ 2 * f + (-800 : k) * a ^ 2 * b * d ^ 2 + 480 * a ^ 2 * c ^ 2 * d + (-1280 : k) * a ^ 2 * d * g + 520 * a * b ^ 5 + (-8640 : k) * a * b ^ 2 * c * d + (-960 : k) * a * b * c ^ 3 + 2560 * a * b * c * g + 10240 * a * b * d * f + 2560 * a * d ^ 3 + (-20480 : k) * a * f * g + (-4000 : k) * b ^ 4 * d + (-8480 : k) * b ^ 3 * c ^ 2 + 3840 * b ^ 3 * g + 21760 * b ^ 2 * c * f + 23040 * b * c * d ^ 2 + (-20480 : k) * b * f ^ 2 + 7680 * c ^ 3 * d + (-20480 : k) * c * d * g + (-20480 : k) * d ^ 2 * f

set_option maxHeartbeats 64000000 in
theorem quarticInner_ABCDFG_identity
    (a b c d f g : k) :
    ((876483770191 / 57744057588224 : k) * a ^ 4 * b * c ^ 2 + (-13111824287 / 1862711535104 : k) * a ^ 4 * b * g + (-1159758490199 / 57744057588224 : k) * a ^ 4 * c * f + (-382943254258883 / 3048886240658227200 : k) * a ^ 3 * b ^ 3 * c + (203661567940141 / 254073853388185600 : k) * a ^ 3 * b ^ 2 * f + (162964447860993 / 36296264769740800 : k) * a ^ 3 * b * d ^ 2 + (-192782468103 / 12553055997440 : k) * a ^ 3 * c ^ 2 * d + (-567322695673 / 37659167992320 : k) * a ^ 3 * d * g + (4372128747697 / 232296094526341120 : k) * a ^ 2 * b ^ 5 + (-8883471500926707 / 508147706776371200 : k) * a ^ 2 * b ^ 2 * c * d + (9294626144752917 / 63518463347046400 : k) * a ^ 2 * b * c ^ 3 + (1085413036877447 / 23819423755142400 : k) * a ^ 2 * b * c * g + (15251803434807077 / 1333887730287974400 : k) * a ^ 2 * b * d * f + (-614927651944597 / 4330804319116800 : k) * a ^ 2 * c ^ 2 * f + (-54824910649910239 / 889258486858649600 : k) * a ^ 2 * d ^ 3 + (9156344039 / 2984890194880 : k) * a ^ 2 * f * g + (563462879754007 / 127036926694092800 : k) * a * b ^ 4 * d + (-563634703262547239 / 6097772481316454400 : k) * a * b ^ 3 * c ^ 2 + (205691201384738063 / 1067110184230379520 : k) * a * b ^ 3 * g + (1258224178580510459 / 5335550921151897600 : k) * a * b ^ 2 * c * f + (-966254141234014949 / 1333887730287974400 : k) * a * b * c * d ^ 2 + (13822077444865889 / 166735966285996800 : k) * a * b * f ^ 2 + (-160257382590964217 / 889258486858649600 : k) * a * c ^ 3 * d + (-25487901599571739 / 30315630233817600 : k) * a * c * d * g + (115542502561061803 / 166735966285996800 : k) * a * d ^ 2 * f + (11517374573658787 / 762221560164556800 : k) * b ^ 5 * c + (37363319152837827 / 889258486858649600 : k) * b ^ 4 * f + (-21912017970267499 / 77326824944230400 : k) * b ^ 3 * d ^ 2 + (-4731526664929552293 / 1778516973717299200 : k) * b ^ 2 * c ^ 2 * d + (-3601798944239999 / 5014615527398400 : k) * b ^ 2 * d * g + (-2668087471364311 / 9074066192435200 : k) * b * c ^ 4 + (-369315182070389 / 1134258274054400 : k) * b * c ^ 2 * g + (478460918764723051 / 83367983142998400 : k) * b * c * d * f + (33275644234359 / 31014874681175 : k) * b * g ^ 2 + (283181612884957 / 307347403292160 : k) * c ^ 3 * f + (2724987940039361 / 3624694919260800 : k) * c * d ^ 3 + (-3037197967137901 / 850693705540800 : k) * c * f * g + (-1933647010850117 / 604115819876800 : k) * d * f ^ 2) * kappaQuarticInnerABCDFG810 a b c d f g +
      ((-106128823798379477 / 1778516973717299200 : k) * a * b ^ 2 * d ^ 2 + (5259409458983929 / 127036926694092800 : k) * a * b * c ^ 2 * d + (852652795636909 / 15879615836761600 : k) * a * b * d * g + (-521791582409 / 346464345529344 : k) * a * c * d * f + (13116386243091 / 72592529539481600 : k) * b ^ 6 + (-47650227562174561 / 381110780082278400 : k) * b ^ 3 * c * d + (4569382566378759 / 254073853388185600 : k) * b ^ 2 * c ^ 3 + (23152319960329913 / 95277695020569600 : k) * b ^ 2 * c * g + (38698926182597837 / 222314621714662400 : k) * b ^ 2 * d * f + (-6453256793899123 / 38111078008227840 : k) * b * c ^ 2 * f + (17574653345402907 / 88925848685864960 : k) * b * d ^ 3 + (-284141264836251 / 1587961583676160 : k) * b * f * g + (16816494639790619 / 444629243429324800 : k) * c ^ 2 * d ^ 2 + (9265244263065671 / 23819423755142400 : k) * c * f ^ 2 + (-769226554419927 / 1792859852537600 : k) * d ^ 2 * g) * muQuarticInnerABCDFG810 a b c d f g +
      ((2629451310573 / 288720287941120 : k) * a ^ 3 * b * c ^ 2 + (-39335472861 / 9313557675520 : k) * a ^ 3 * b * g + (-3479275470597 / 288720287941120 : k) * a ^ 3 * c * f + (1360940780584439 / 508147706776371200 : k) * a ^ 2 * b * d ^ 2 + (-25032793346557 / 3175923167352320 : k) * a ^ 2 * c ^ 2 * d + (-24010228037457 / 3175923167352320 : k) * a ^ 2 * d * g + (553904777526981 / 11046689277747200 : k) * a * b * c ^ 3 + (974539765217 / 18168896838400 : k) * a * b * c * g + (-11355632070228541 / 333471932571993600 : k) * a * b * d * f + (-10172471651039 / 303916092569600 : k) * a * c ^ 2 * f + (-11391115361805017 / 889258486858649600 : k) * a * d ^ 3 + (3709485043 / 135676827040 : k) * a * f * g + (-4443014213160829 / 508147706776371200 : k) * b ^ 4 * d + (-273480823088980919 / 6097772481316454400 : k) * b ^ 3 * c ^ 2 + (166862667776312779 / 5335550921151897600 : k) * b ^ 3 * g + (167786507052955113 / 1778516973717299200 : k) * b ^ 2 * c * f + (-14097232165527591 / 444629243429324800 : k) * b * c * d ^ 2 + (37953001842803 / 10420997892874800 : k) * b * f ^ 2 + (-85038809893104521 / 889258486858649600 : k) * c ^ 3 * d + (122966923042776971 / 333471932571993600 : k) * c * d * g + (1608046498037281 / 30315630233817600 : k) * d ^ 2 * f) * nuQuarticInnerABCDFG810 a b c d f g +
      ((7615634641849 / 156706735231200 : k) * a * b ^ 2 * g + (1396039010767 / 39176683807800 : k) * a * b * c * f + (-35384474641 / 593586118300 : k) * a * c * d ^ 2 + (2121291982 / 89037917745 : k) * a * f ^ 2 + (16703104693733 / 398889871497600 : k) * b ^ 3 * f + (-528086876564073 / 5557865542866560 : k) * b ^ 2 * d ^ 2 + (-907363129413981 / 1389466385716640 : k) * b * c ^ 2 * d + (-1929281670864703 / 5210498946437400 : k) * b * d * g + (-1862723246807 / 39176683807800 : k) * c ^ 4 + (-8342281181907 / 13058894602600 : k) * c ^ 2 * g + (9315444779119637 / 10420997892874800 : k) * c * d * f + (1428162017839 / 979417095195 : k) * g ^ 2) * xiQuarticInnerABCDFG810 a b c d f g +
      ((876483770191 / 288720287941120 : k) * a ^ 2 * b * c ^ 2 + (-13111824287 / 9313557675520 : k) * a ^ 2 * b * g + (-1159758490199 / 288720287941120 : k) * a ^ 2 * c * f + (-117097611737367 / 101629541355274240 : k) * a * b * d ^ 2 + (-258324452611 / 635184633470464 : k) * a * c ^ 2 * d + (-528726219473 / 9527769502056960 : k) * a * d * g + (4372128747697 / 232296094526341120 : k) * b ^ 5 + (-294067939355647 / 20325908271054848 : k) * b ^ 2 * c * d + (-48617654537491 / 50814770677637120 : k) * b * c ^ 3 + (105366400039 / 2849213367840 : k) * b * c * g + (219959290511867 / 12703692669409280 : k) * b * d * f + (3651121868557 / 182349655541760 : k) * c ^ 2 * f + (-1 / 2560 : k) * d ^ 3 + (-72452326907 / 2984890194880 : k) * f * g) * omicronQuarticInnerABCDFG810 a b c d f g +
      ((-1060645991 / 356151670980 : k) * a * d * f + (-97465503338573 / 23819423755142400 : k) * b ^ 3 * d + (-11553883108717 / 567129137027200 : k) * b ^ 2 * c ^ 2 + (8962114747907 / 744356992348200 : k) * b ^ 2 * g + (89312336837771 / 2977427969392800 : k) * b * c * f + (1060645991 / 178075835490 : k) * f ^ 2) * piQuarticInnerABCDFG810 a b c d f g +
      ((876483770191 / 288720287941120 : k) * a * b * c ^ 2 + (-13111824287 / 9313557675520 : k) * a * b * g + (-1159758490199 / 288720287941120 : k) * a * c * f + (-382943254258883 / 3048886240658227200 : k) * b ^ 3 * c + (203661567940141 / 254073853388185600 : k) * b ^ 2 * f + (753024774078149 / 254073853388185600 : k) * b * d ^ 2 + (-3207078402921 / 453703309621760 : k) * c ^ 2 * d + (-14194646334685 / 1905553900411392 : k) * d * g) * primitiveQuarticInnerABCDFG810 a b c d f g =
      d ^ 6 := by
  simp only [kappaQuarticInnerABCDFG810, muQuarticInnerABCDFG810, nuQuarticInnerABCDFG810, xiQuarticInnerABCDFG810, omicronQuarticInnerABCDFG810, piQuarticInnerABCDFG810, primitiveQuarticInnerABCDFG810]
  ring

set_option maxHeartbeats 16000000 in
def kappaQuarticFaceABCDFG810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
  + (5 / 16 : k) • (C * F)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaQuarticNoABCDFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (D * E)
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

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaQuartic810_eq_ABCDFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceABCDFG810 A B C D E F G +
        degreeZeroKappaQuarticNoABCDFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticFaceABCDFG810, degreeZeroKappaQuarticNoABCDFG810]
  all_goals module

set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroKappaQuarticNoABCDFG810` (30 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroKappaQuarticNoABCDFG810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    degreeZeroKappaQuarticNoABCDFG810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
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
      [0, 0, 0, 1, 1, 0, 0], [5, 0, 0, 0, 0, 0, 0], [3, 0, 1, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0],
      [2, 0, 0, 0, 1, 0, 0], [1, 1, 0, 1, 0, 0, 0], [1, 0, 2, 0, 0, 0, 0], [0, 2, 1, 0, 0, 0, 0],
      [1, 0, 0, 0, 0, 0, 1], [0, 1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0],
      [4, 0, 0, 0, 0, 0, 0], [2, 0, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 0],
      [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 0, 0],
      [0, 0, 0, 0, 0, 1, 0], [3, 0, 0, 0, 0, 0, 0], [1, 0, 1, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0],
      [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0],
      [0, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0]] := by
  simp only [degreeZeroKappaQuarticNoABCDFG810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaQuarticNoABCDFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABCDFG810 A B C D E F G) :
    (degreeZeroKappaQuarticNoABCDFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hFpos, hGpos, hAB, hAC, hAD, hAF, hAG, hElt⟩
  have hE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hElt
  rw [speedRefl_degreeZeroKappaQuarticNoABCDFG810_eq_polyOf]
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
