import Grok810PiOrder98Scratch

/-! # Order-`99` continuation of the `(8,10)` degree-one `π` tower

`Grok810PiOrder98Scratch` leaves three live chambers after the unsolved
order-`98` coefficient is extracted:

* LEFT: `o97n(a) + Order98(a) = 0` with the fifty-term frozen mixin
  and unsolved witnesses `m1, τ1, g1, k1`;
* RIGHT/`u1 = 0`: order-`97` vanished identically, the order-`96` head
  peeled twice, and order-`98` is mixed with the next coefficient;
* RIGHT complement: the seven-term `λ u1` hypersurface mixed with
  order-`98`, together with the fifteenth-face extra `2 u1² + v1³ = 0`.

This file extracts the order-`99` coefficient (`h⁰` of the order-`98`
Plus remainder, equivalently `h²` of the unsolved tail) and applies the
remaining power vanishing.  The four scalar load solves are not inserted
as polynomial identities, and the old scalar-solved jet is not imported.
Witnesses stay unsolved.

The landed fifteenth-face extras are carried from the parent: on
RIGHT/`u1 = 0` the mixed extra is `16 b62 v1 = 5 v1³`; on the complement
`5 v1² = 8 b62` it is `2 u1² + v1³ = 0`.  The frozen order-`99` mixin
vanishes at `v1 = 0` on both right packets, and the extras specialize it
to a multiple of `a3 λ v1⁵`.  Those scalar conclusions of the named
order-`96` residuals from the parent are not re-evaluated against the
source-facing residual.  Neither chamber is closed.  The next unused
compact-numerator order is `100`.

Vanishing is recorded in the `h0`-divisibility shape the ceiling lemma
consumes: `Head = h0 · o96n`, `o96n + Order97 = h0 · o97n`,
`o97n + Order98 = h0 · o98n`, and `o98n(a) + Order99(a) = 0`.  The
tower ceiling is order `112` from the weight-`112` source power
relation; orders `96` through `112` exhaust the unsolved head before
the cancel-and-expose endgame.  This file does not close any chamber.

No total-degree or twice-prime theorem is used.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option maxHeartbeats 800000000
set_option linter.unusedVariables false

section PiOrder99Frozen810

variable {R : Type*} [CommRing R]

set_option maxHeartbeats 800000000 in
/-- Frozen order-`99` mixin: the `h⁰` coefficient of the order-`98` Plus
remainder. -/
def piLeftUnsolvedOrder99810 (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (1923167600640 : R) * t0 ^ 10 * a3 * lambda
    + (18711900979200 : R) * t0 ^ 8 * v1 * a3 * lambda
    - (18144873676800 : R) * t0 ^ 7 * u1 * a3 * lambda
    - (63507057868800 : R) * t0 ^ 6 * v1 ^ 2 * a3 * lambda
    + (17519188377600 : R) * t0 ^ 6 * a4 * a3 * lambda
    + (105115130265600 : R) * t0 ^ 5 * v1 * u1 * a3 * lambda
    + (87595941888000 : R) * t0 ^ 4 * v1 ^ 3 * a3 * lambda
    - (84092104212480 : R) * t0 ^ 4 * v1 * a4 * a3 * lambda
    - (42046052106240 : R) * t0 ^ 4 * u1 ^ 2 * a3 * lambda
    - (168184208424960 : R) * t0 ^ 3 * v1 ^ 2 * u1 * a3 * lambda
    + (64070174638080 : R) * t0 ^ 3 * u1 * a4 * a3 * lambda
    - (42046052106240 : R) * t0 ^ 2 * v1 ^ 4 * a3 * lambda
    + (96105261957120 : R) * t0 ^ 2 * v1 ^ 2 * a4 * a3 * lambda
    + (96105261957120 : R) * t0 ^ 2 * v1 * u1 ^ 2 * a3 * lambda
    - (22613002813440 : R) * t0 ^ 2 * a4 ^ 2 * a3 * lambda
    + (64070174638080 : R) * t0 * v1 ^ 3 * u1 * a3 * lambda
    - (90452011253760 : R) * t0 * v1 * u1 * a4 * a3 * lambda
    - (15075335208960 : R) * t0 * u1 ^ 3 * a3 * lambda
    + (3203508731904 : R) * v1 ^ 5 * a3 * lambda
    - (15075335208960 : R) * v1 ^ 3 * a4 * a3 * lambda
    - (22613002813440 : R) * v1 ^ 2 * u1 ^ 2 * a3 * lambda
    + (13915694039040 : R) * v1 * a4 ^ 2 * a3 * lambda
    + (13915694039040 : R) * u1 ^ 2 * a4 * a3 * lambda

set_option maxHeartbeats 800000000 in
/-- Remaining factor after `h` is removed from the order-`98` Plus
remainder. -/
def piLeftUnsolvedOrder99Plus810 (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (21990232555520 : R) * h ^ 12 * a0 ^ 2
    + (9895604649984 : R) * h ^ 11 * a1 * a0 * lambda
    + (5497558138880 : R) * h ^ 10 * t0 * a1 * a0
    + (17592186044416 : R) * h ^ 10 * a1 * b1
    + (35184372088832 : R) * h ^ 10 * a0 * b2
    - (12369505812480 : R) * h ^ 9 * t0 * a2 * a0 * lambda
    - (6184752906240 : R) * h ^ 9 * t0 * a1 ^ 2 * lambda
    - (4398046511104 : R) * h ^ 8 * t0 * a2 * b1
    - (8796093022208 : R) * h ^ 8 * t0 * a1 * b2
    - (13194139533312 : R) * h ^ 8 * t0 * a0 * b3
    + (54975581388800 : R) * h ^ 8 * v1 * a2 * a0
    + (27487790694400 : R) * h ^ 8 * v1 * a1 ^ 2
    - (35184372088832 : R) * h ^ 8 * a2 * a0 * s1
    - (17592186044416 : R) * h ^ 8 * a1 ^ 2 * s1
    + (13915694039040 : R) * h ^ 7 * t0 ^ 2 * a3 * a0 * lambda
    + (13915694039040 : R) * h ^ 7 * t0 ^ 2 * a2 * a1 * lambda
    - (12369505812480 : R) * h ^ 7 * v1 * a3 * a0 * lambda
    - (12369505812480 : R) * h ^ 7 * v1 * a2 * a1 * lambda
    - (2576980377600 : R) * h ^ 6 * t0 ^ 3 * a3 * a0
    - (2576980377600 : R) * h ^ 6 * t0 ^ 3 * a2 * a1
    + (2748779069440 : R) * h ^ 6 * t0 ^ 2 * a3 * b1
    + (5497558138880 : R) * h ^ 6 * t0 ^ 2 * a2 * b2
    + (8246337208320 : R) * h ^ 6 * t0 ^ 2 * a1 * b3
    + (10995116277760 : R) * h ^ 6 * t0 ^ 2 * a0 * b4
    - (61847529062400 : R) * h ^ 6 * t0 * v1 * a3 * a0
    - (61847529062400 : R) * h ^ 6 * t0 * v1 * a2 * a1
    + (43980465111040 : R) * h ^ 6 * t0 * a3 * a0 * s1
    + (43980465111040 : R) * h ^ 6 * t0 * a2 * a1 * s1
    - (4398046511104 : R) * h ^ 6 * v1 * a3 * b1
    - (8796093022208 : R) * h ^ 6 * v1 * a2 * b2
    - (13194139533312 : R) * h ^ 6 * v1 * a1 * b3
    - (17592186044416 : R) * h ^ 6 * v1 * a0 * b4
    + (54975581388800 : R) * h ^ 6 * u1 * a3 * a0
    + (54975581388800 : R) * h ^ 6 * u1 * a2 * a1
    - (30786325577728 : R) * h ^ 6 * a3 * a0 * w1
    - (30786325577728 : R) * h ^ 6 * a2 * a1 * w1
    + (2502741196800 : R) * h ^ 5 * t0 ^ 7 * a0 * lambda
    - (16818420842496 : R) * h ^ 5 * t0 ^ 5 * v1 * a0 * lambda
    + (16017543659520 : R) * h ^ 5 * t0 ^ 4 * u1 * a0 * lambda
    + (32035087319040 : R) * h ^ 5 * t0 ^ 3 * v1 ^ 2 * a0 * lambda
    - (15075335208960 : R) * h ^ 5 * t0 ^ 3 * a4 * a0 * lambda
    - (15075335208960 : R) * h ^ 5 * t0 ^ 3 * a3 * a1 * lambda
    - (7537667604480 : R) * h ^ 5 * t0 ^ 3 * a2 ^ 2 * lambda
    - (45226005626880 : R) * h ^ 5 * t0 ^ 2 * v1 * u1 * a0 * lambda
    - (15075335208960 : R) * h ^ 5 * t0 * v1 ^ 3 * a0 * lambda
    + (27831388078080 : R) * h ^ 5 * t0 * v1 * a4 * a0 * lambda
    + (27831388078080 : R) * h ^ 5 * t0 * v1 * a3 * a1 * lambda
    + (13915694039040 : R) * h ^ 5 * t0 * v1 * a2 ^ 2 * lambda
    + (13915694039040 : R) * h ^ 5 * t0 * u1 ^ 2 * a0 * lambda
    + (13915694039040 : R) * h ^ 5 * v1 ^ 2 * u1 * a0 * lambda
    - (12369505812480 : R) * h ^ 5 * u1 * a4 * a0 * lambda
    - (12369505812480 : R) * h ^ 5 * u1 * a3 * a1 * lambda
    - (6184752906240 : R) * h ^ 5 * u1 * a2 ^ 2 * lambda
    - (2433220608000 : R) * h ^ 4 * t0 ^ 8 * a0
    + (177972707328 : R) * h ^ 4 * t0 ^ 7 * b1
    + (6229044756480 : R) * h ^ 4 * t0 ^ 6 * v1 * a0
    + (9966471610368 : R) * h ^ 4 * t0 ^ 6 * a0 * s1
    - (1423781658624 : R) * h ^ 4 * t0 ^ 5 * v1 * b1
    - (5339181219840 : R) * h ^ 4 * t0 ^ 5 * u1 * a0
    - (9966471610368 : R) * h ^ 4 * t0 ^ 5 * a0 * w1
    + (26695906099200 : R) * h ^ 4 * t0 ^ 4 * v1 ^ 2 * a0
    - (56951266344960 : R) * h ^ 4 * t0 ^ 4 * v1 * a0 * s1
    + (1675037245440 : R) * h ^ 4 * t0 ^ 4 * u1 * b1
    + (4187593113600 : R) * h ^ 4 * t0 ^ 4 * a4 * a0
    + (4187593113600 : R) * h ^ 4 * t0 ^ 4 * a3 * a1
    + (2093796556800 : R) * h ^ 4 * t0 ^ 4 * a2 ^ 2
    + (10050223472640 : R) * h ^ 4 * t0 ^ 4 * a0 * b62
    + (3350074490880 : R) * h ^ 4 * t0 ^ 3 * v1 ^ 2 * b1
    - (58626303590400 : R) * h ^ 4 * t0 ^ 3 * v1 * u1 * a0
    + (46901042872320 : R) * h ^ 4 * t0 ^ 3 * v1 * a0 * w1
    + (53601191854080 : R) * h ^ 4 * t0 ^ 3 * u1 * a0 * s1
    - (2061584302080 : R) * h ^ 4 * t0 ^ 3 * a4 * b1
    - (4123168604160 : R) * h ^ 4 * t0 ^ 3 * a3 * b2
    - (6184752906240 : R) * h ^ 4 * t0 ^ 3 * a2 * b3
    - (8246337208320 : R) * h ^ 4 * t0 ^ 3 * a1 * b4
    - (10307921510400 : R) * h ^ 4 * t0 ^ 3 * a0 * b5
    - (67001489817600 : R) * h ^ 4 * t0 ^ 2 * v1 ^ 3 * a0
    + (80401787781120 : R) * h ^ 4 * t0 ^ 2 * v1 ^ 2 * a0 * s1
    - (6184752906240 : R) * h ^ 4 * t0 ^ 2 * v1 * u1 * b1
    + (61847529062400 : R) * h ^ 4 * t0 ^ 2 * v1 * a4 * a0
    + (61847529062400 : R) * h ^ 4 * t0 ^ 2 * v1 * a3 * a1
    + (30923764531200 : R) * h ^ 4 * t0 ^ 2 * v1 * a2 ^ 2
    - (37108517437440 : R) * h ^ 4 * t0 ^ 2 * v1 * a0 * b62
    + (30923764531200 : R) * h ^ 4 * t0 ^ 2 * u1 ^ 2 * a0
    - (43293270343680 : R) * h ^ 4 * t0 ^ 2 * u1 * a0 * w1
    - (49478023249920 : R) * h ^ 4 * t0 ^ 2 * a4 * a0 * s1
    - (49478023249920 : R) * h ^ 4 * t0 ^ 2 * a3 * a1 * s1
    - (24739011624960 : R) * h ^ 4 * t0 ^ 2 * a2 ^ 2 * s1
    - (2061584302080 : R) * h ^ 4 * t0 * v1 ^ 3 * b1
    + (131425999257600 : R) * h ^ 4 * t0 * v1 ^ 2 * u1 * a0
    - (43293270343680 : R) * h ^ 4 * t0 * v1 ^ 2 * a0 * w1
    - (98956046499840 : R) * h ^ 4 * t0 * v1 * u1 * a0 * s1
    + (5497558138880 : R) * h ^ 4 * t0 * v1 * a4 * b1
    + (10995116277760 : R) * h ^ 4 * t0 * v1 * a3 * b2
    + (16492674416640 : R) * h ^ 4 * t0 * v1 * a2 * b3
    + (21990232555520 : R) * h ^ 4 * t0 * v1 * a1 * b4
    + (27487790694400 : R) * h ^ 4 * t0 * v1 * a0 * b5
    + (2748779069440 : R) * h ^ 4 * t0 * u1 ^ 2 * b1
    - (61847529062400 : R) * h ^ 4 * t0 * u1 * a4 * a0
    - (61847529062400 : R) * h ^ 4 * t0 * u1 * a3 * a1
    - (30923764531200 : R) * h ^ 4 * t0 * u1 * a2 ^ 2
    + (32985348833280 : R) * h ^ 4 * t0 * u1 * a0 * b62
    + (38482906972160 : R) * h ^ 4 * t0 * a4 * a0 * w1
    + (38482906972160 : R) * h ^ 4 * t0 * a3 * a1 * w1
    + (19241453486080 : R) * h ^ 4 * t0 * a2 ^ 2 * w1
    + (16750372454400 : R) * h ^ 4 * v1 ^ 4 * a0
    - (16492674416640 : R) * h ^ 4 * v1 ^ 3 * a0 * s1
    + (2748779069440 : R) * h ^ 4 * v1 ^ 2 * u1 * b1
    - (61847529062400 : R) * h ^ 4 * v1 ^ 2 * a4 * a0
    - (61847529062400 : R) * h ^ 4 * v1 ^ 2 * a3 * a1
    - (30923764531200 : R) * h ^ 4 * v1 ^ 2 * a2 ^ 2
    + (16492674416640 : R) * h ^ 4 * v1 ^ 2 * a0 * b62
    - (61847529062400 : R) * h ^ 4 * v1 * u1 ^ 2 * a0
    + (38482906972160 : R) * h ^ 4 * v1 * u1 * a0 * w1
    + (43980465111040 : R) * h ^ 4 * v1 * a4 * a0 * s1
    + (43980465111040 : R) * h ^ 4 * v1 * a3 * a1 * s1
    + (21990232555520 : R) * h ^ 4 * v1 * a2 ^ 2 * s1
    + (21990232555520 : R) * h ^ 4 * u1 ^ 2 * a0 * s1
    - (4398046511104 : R) * h ^ 4 * u1 * a4 * b1
    - (8796093022208 : R) * h ^ 4 * u1 * a3 * b2
    - (13194139533312 : R) * h ^ 4 * u1 * a2 * b3
    - (17592186044416 : R) * h ^ 4 * u1 * a1 * b4
    - (21990232555520 : R) * h ^ 4 * u1 * a0 * b5
    + (27487790694400 : R) * h ^ 4 * a4 ^ 2 * a0
    + (54975581388800 : R) * h ^ 4 * a4 * a3 * a1
    + (27487790694400 : R) * h ^ 4 * a4 * a2 ^ 2
    - (26388279066624 : R) * h ^ 4 * a4 * a0 * b62
    + (27487790694400 : R) * h ^ 4 * a3 ^ 2 * a2
    - (26388279066624 : R) * h ^ 4 * a3 * a1 * b62
    - (13194139533312 : R) * h ^ 4 * a2 ^ 2 * b62
    - (2268109209600 : R) * h ^ 3 * t0 ^ 8 * a1 * lambda
    + (17519188377600 : R) * h ^ 3 * t0 ^ 6 * v1 * a1 * lambda
    - (16818420842496 : R) * h ^ 3 * t0 ^ 5 * u1 * a1 * lambda
    - (42046052106240 : R) * h ^ 3 * t0 ^ 4 * v1 ^ 2 * a1 * lambda
    + (16017543659520 : R) * h ^ 3 * t0 ^ 4 * a4 * a1 * lambda
    + (16017543659520 : R) * h ^ 3 * t0 ^ 4 * a3 * a2 * lambda
    + (64070174638080 : R) * h ^ 3 * t0 ^ 3 * v1 * u1 * a1 * lambda
    + (32035087319040 : R) * h ^ 3 * t0 ^ 2 * v1 ^ 3 * a1 * lambda
    - (45226005626880 : R) * h ^ 3 * t0 ^ 2 * v1 * a4 * a1 * lambda
    - (45226005626880 : R) * h ^ 3 * t0 ^ 2 * v1 * a3 * a2 * lambda
    - (22613002813440 : R) * h ^ 3 * t0 ^ 2 * u1 ^ 2 * a1 * lambda
    - (45226005626880 : R) * h ^ 3 * t0 * v1 ^ 2 * u1 * a1 * lambda
    + (27831388078080 : R) * h ^ 3 * t0 * u1 * a4 * a1 * lambda
    + (27831388078080 : R) * h ^ 3 * t0 * u1 * a3 * a2 * lambda
    - (3768833802240 : R) * h ^ 3 * v1 ^ 4 * a1 * lambda
    + (13915694039040 : R) * h ^ 3 * v1 ^ 2 * a4 * a1 * lambda
    + (13915694039040 : R) * h ^ 3 * v1 ^ 2 * a3 * a2 * lambda
    + (13915694039040 : R) * h ^ 3 * v1 * u1 ^ 2 * a1 * lambda
    - (6184752906240 : R) * h ^ 3 * a4 ^ 2 * a1 * lambda
    - (12369505812480 : R) * h ^ 3 * a4 * a3 * a2 * lambda
    - (2061584302080 : R) * h ^ 3 * a3 ^ 3 * lambda
    + (2100101120000 : R) * h ^ 2 * t0 ^ 9 * a1
    - (278082355200 : R) * h ^ 2 * t0 ^ 8 * b2
    - (6952058880000 : R) * h ^ 2 * t0 ^ 7 * v1 * a1
    - (8898635366400 : R) * h ^ 2 * t0 ^ 7 * a1 * s1
    + (2491617902592 : R) * h ^ 2 * t0 ^ 6 * v1 * b2
    + (6229044756480 : R) * h ^ 2 * t0 ^ 6 * u1 * a1
    + (8720662659072 : R) * h ^ 2 * t0 ^ 6 * a1 * w1
    - (23358917836800 : R) * h ^ 2 * t0 ^ 5 * v1 ^ 2 * a1
    + (59798829662208 : R) * h ^ 2 * t0 ^ 5 * v1 * a1 * s1
    - (2847563317248 : R) * h ^ 2 * t0 ^ 5 * u1 * b2
    - (5339181219840 : R) * h ^ 2 * t0 ^ 5 * a4 * a1
    - (5339181219840 : R) * h ^ 2 * t0 ^ 5 * a3 * a2
    - (8542689951744 : R) * h ^ 2 * t0 ^ 5 * a1 * b62
    - (7118908293120 : R) * h ^ 2 * t0 ^ 4 * v1 ^ 2 * b2
    + (53391812198400 : R) * h ^ 2 * t0 ^ 4 * v1 * u1 * a1
    - (49832358051840 : R) * h ^ 2 * t0 ^ 4 * v1 * a1 * w1
    - (56951266344960 : R) * h ^ 2 * t0 ^ 4 * u1 * a1 * s1
    + (3350074490880 : R) * h ^ 2 * t0 ^ 4 * a4 * b2
    + (5025111736320 : R) * h ^ 2 * t0 ^ 4 * a3 * b3
    + (6700148981760 : R) * h ^ 2 * t0 ^ 4 * a2 * b4
    + (8375186227200 : R) * h ^ 2 * t0 ^ 4 * a1 * b5
    + (88986353664000 : R) * h ^ 2 * t0 ^ 3 * v1 ^ 3 * a1
    - (113902532689920 : R) * h ^ 2 * t0 ^ 3 * v1 ^ 2 * a1 * s1
    + (13400297963520 : R) * h ^ 2 * t0 ^ 3 * v1 * u1 * b2
    - (58626303590400 : R) * h ^ 2 * t0 ^ 3 * v1 * a4 * a1
    - (58626303590400 : R) * h ^ 2 * t0 ^ 3 * v1 * a3 * a2
    + (40200893890560 : R) * h ^ 2 * t0 ^ 3 * v1 * a1 * b62
    - (29313151795200 : R) * h ^ 2 * t0 ^ 3 * u1 ^ 2 * a1
    + (46901042872320 : R) * h ^ 2 * t0 ^ 3 * u1 * a1 * w1
    + (53601191854080 : R) * h ^ 2 * t0 ^ 3 * a4 * a1 * s1
    + (53601191854080 : R) * h ^ 2 * t0 ^ 3 * a3 * a2 * s1
    + (6700148981760 : R) * h ^ 2 * t0 ^ 2 * v1 ^ 3 * b2
    - (201004469452800 : R) * h ^ 2 * t0 ^ 2 * v1 ^ 2 * u1 * a1
    + (70351564308480 : R) * h ^ 2 * t0 ^ 2 * v1 ^ 2 * a1 * w1
    + (160803575562240 : R) * h ^ 2 * t0 ^ 2 * v1 * u1 * a1 * s1
    - (12369505812480 : R) * h ^ 2 * t0 ^ 2 * v1 * a4 * b2
    - (18554258718720 : R) * h ^ 2 * t0 ^ 2 * v1 * a3 * b3
    - (24739011624960 : R) * h ^ 2 * t0 ^ 2 * v1 * a2 * b4
    - (30923764531200 : R) * h ^ 2 * t0 ^ 2 * v1 * a1 * b5
    - (6184752906240 : R) * h ^ 2 * t0 ^ 2 * u1 ^ 2 * b2
    + (61847529062400 : R) * h ^ 2 * t0 ^ 2 * u1 * a4 * a1
    + (61847529062400 : R) * h ^ 2 * t0 ^ 2 * u1 * a3 * a2
    - (37108517437440 : R) * h ^ 2 * t0 ^ 2 * u1 * a1 * b62
    - (43293270343680 : R) * h ^ 2 * t0 ^ 2 * a4 * a1 * w1
    - (43293270343680 : R) * h ^ 2 * t0 ^ 2 * a3 * a2 * w1
    - (52344913920000 : R) * h ^ 2 * t0 * v1 ^ 4 * a1
    + (53601191854080 : R) * h ^ 2 * t0 * v1 ^ 3 * a1 * s1
    - (12369505812480 : R) * h ^ 2 * t0 * v1 ^ 2 * u1 * b2
    + (131425999257600 : R) * h ^ 2 * t0 * v1 ^ 2 * a4 * a1
    + (131425999257600 : R) * h ^ 2 * t0 * v1 ^ 2 * a3 * a2
    - (37108517437440 : R) * h ^ 2 * t0 * v1 ^ 2 * a1 * b62
    + (131425999257600 : R) * h ^ 2 * t0 * v1 * u1 ^ 2 * a1
    - (86586540687360 : R) * h ^ 2 * t0 * v1 * u1 * a1 * w1
    - (98956046499840 : R) * h ^ 2 * t0 * v1 * a4 * a1 * s1
    - (98956046499840 : R) * h ^ 2 * t0 * v1 * a3 * a2 * s1
    - (49478023249920 : R) * h ^ 2 * t0 * u1 ^ 2 * a1 * s1
    + (10995116277760 : R) * h ^ 2 * t0 * u1 * a4 * b2
    + (16492674416640 : R) * h ^ 2 * t0 * u1 * a3 * b3
    + (21990232555520 : R) * h ^ 2 * t0 * u1 * a2 * b4
    + (27487790694400 : R) * h ^ 2 * t0 * u1 * a1 * b5
    - (30923764531200 : R) * h ^ 2 * t0 * a4 ^ 2 * a1
    - (61847529062400 : R) * h ^ 2 * t0 * a4 * a3 * a2
    + (32985348833280 : R) * h ^ 2 * t0 * a4 * a1 * b62
    - (10307921510400 : R) * h ^ 2 * t0 * a3 ^ 3
    + (32985348833280 : R) * h ^ 2 * t0 * a3 * a2 * b62
    - (1030792151040 : R) * h ^ 2 * v1 ^ 4 * b2
    + (67001489817600 : R) * h ^ 2 * v1 ^ 3 * u1 * a1
    - (14431090114560 : R) * h ^ 2 * v1 ^ 3 * a1 * w1
    - (49478023249920 : R) * h ^ 2 * v1 ^ 2 * u1 * a1 * s1
    + (5497558138880 : R) * h ^ 2 * v1 ^ 2 * a4 * b2
    + (8246337208320 : R) * h ^ 2 * v1 ^ 2 * a3 * b3
    + (10995116277760 : R) * h ^ 2 * v1 ^ 2 * a2 * b4
    + (13743895347200 : R) * h ^ 2 * v1 ^ 2 * a1 * b5
    + (5497558138880 : R) * h ^ 2 * v1 * u1 ^ 2 * b2
    - (123695058124800 : R) * h ^ 2 * v1 * u1 * a4 * a1
    - (123695058124800 : R) * h ^ 2 * v1 * u1 * a3 * a2
    + (32985348833280 : R) * h ^ 2 * v1 * u1 * a1 * b62
    + (38482906972160 : R) * h ^ 2 * v1 * a4 * a1 * w1
    + (38482906972160 : R) * h ^ 2 * v1 * a3 * a2 * w1
    - (20615843020800 : R) * h ^ 2 * u1 ^ 3 * a1
    + (19241453486080 : R) * h ^ 2 * u1 ^ 2 * a1 * w1
    + (43980465111040 : R) * h ^ 2 * u1 * a4 * a1 * s1
    + (43980465111040 : R) * h ^ 2 * u1 * a3 * a2 * s1
    - (4398046511104 : R) * h ^ 2 * a4 ^ 2 * b2
    - (13194139533312 : R) * h ^ 2 * a4 * a3 * b3
    - (17592186044416 : R) * h ^ 2 * a4 * a2 * b4
    - (21990232555520 : R) * h ^ 2 * a4 * a1 * b5
    - (8796093022208 : R) * h ^ 2 * a3 ^ 2 * b4
    - (21990232555520 : R) * h ^ 2 * a3 * a2 * b5
    + (2079100108800 : R) * h * t0 ^ 9 * a2 * lambda
    - (18144873676800 : R) * h * t0 ^ 7 * v1 * a2 * lambda
    + (17519188377600 : R) * h * t0 ^ 6 * u1 * a2 * lambda
    + (52557565132800 : R) * h * t0 ^ 5 * v1 ^ 2 * a2 * lambda
    - (16818420842496 : R) * h * t0 ^ 5 * a4 * a2 * lambda
    - (8409210421248 : R) * h * t0 ^ 5 * a3 ^ 2 * lambda
    - (84092104212480 : R) * h * t0 ^ 4 * v1 * u1 * a2 * lambda
    - (56061402808320 : R) * h * t0 ^ 3 * v1 ^ 3 * a2 * lambda
    + (64070174638080 : R) * h * t0 ^ 3 * v1 * a4 * a2 * lambda
    + (32035087319040 : R) * h * t0 ^ 3 * v1 * a3 ^ 2 * lambda
    + (32035087319040 : R) * h * t0 ^ 3 * u1 ^ 2 * a2 * lambda
    + (96105261957120 : R) * h * t0 ^ 2 * v1 ^ 2 * u1 * a2 * lambda
    - (45226005626880 : R) * h * t0 ^ 2 * u1 * a4 * a2 * lambda
    - (22613002813440 : R) * h * t0 ^ 2 * u1 * a3 ^ 2 * lambda
    + (16017543659520 : R) * h * t0 * v1 ^ 4 * a2 * lambda
    - (45226005626880 : R) * h * t0 * v1 ^ 2 * a4 * a2 * lambda
    - (22613002813440 : R) * h * t0 * v1 ^ 2 * a3 ^ 2 * lambda
    - (45226005626880 : R) * h * t0 * v1 * u1 ^ 2 * a2 * lambda
    + (13915694039040 : R) * h * t0 * a4 ^ 2 * a2 * lambda
    + (13915694039040 : R) * h * t0 * a4 * a3 ^ 2 * lambda
    - (15075335208960 : R) * h * v1 ^ 3 * u1 * a2 * lambda
    + (27831388078080 : R) * h * v1 * u1 * a4 * a2 * lambda
    + (13915694039040 : R) * h * v1 * u1 * a3 ^ 2 * lambda
    + (4638564679680 : R) * h * u1 ^ 3 * a2 * lambda
    - (1848088985600 : R) * t0 ^ 10 * a2
    + (336016179200 : R) * t0 ^ 9 * b3
    + (7560364032000 : R) * t0 ^ 8 * v1 * a2
    + (8064388300800 : R) * t0 ^ 8 * a2 * s1
    - (3336988262400 : R) * t0 ^ 7 * v1 * b3
    - (6952058880000 : R) * t0 ^ 7 * u1 * a2
    - (7786305945600 : R) * t0 ^ 7 * a2 * w1
    + (19465764864000 : R) * t0 ^ 6 * v1 ^ 2 * a2
    - (62290447564800 : R) * t0 ^ 6 * v1 * a2 * s1
    + (3737426853888 : R) * t0 ^ 6 * u1 * b3
    + (6229044756480 : R) * t0 ^ 6 * a4 * a2
    + (3114522378240 : R) * t0 ^ 6 * a3 ^ 2
    + (7474853707776 : R) * t0 ^ 6 * a2 * b62
    + (11212280561664 : R) * t0 ^ 5 * v1 ^ 2 * b3
    - (46717835673600 : R) * t0 ^ 5 * v1 * u1 * a2
    + (52323975954432 : R) * t0 ^ 5 * v1 * a2 * w1
    + (59798829662208 : R) * t0 ^ 5 * u1 * a2 * s1
    - (4271344975872 : R) * t0 ^ 5 * a4 * b3
    - (5695126634496 : R) * t0 ^ 5 * a3 * b4
    - (7118908293120 : R) * t0 ^ 5 * a2 * b5
    - (109008283238400 : R) * t0 ^ 4 * v1 ^ 3 * a2
    + (149497074155520 : R) * t0 ^ 4 * v1 ^ 2 * a2 * s1
    - (21356724879360 : R) * t0 ^ 4 * v1 * u1 * b3
    + (53391812198400 : R) * t0 ^ 4 * v1 * a4 * a2
    + (26695906099200 : R) * t0 ^ 4 * v1 * a3 ^ 2
    - (42713449758720 : R) * t0 ^ 4 * v1 * a2 * b62
    + (26695906099200 : R) * t0 ^ 4 * u1 ^ 2 * a2
    - (49832358051840 : R) * t0 ^ 4 * u1 * a2 * w1
    - (56951266344960 : R) * t0 ^ 4 * a4 * a2 * s1
    - (28475633172480 : R) * t0 ^ 4 * a3 ^ 2 * s1
    - (14237816586240 : R) * t0 ^ 3 * v1 ^ 3 * b3
    + (266959060992000 : R) * t0 ^ 3 * v1 ^ 2 * u1 * a2
    - (99664716103680 : R) * t0 ^ 3 * v1 ^ 2 * a2 * w1
    - (227805065379840 : R) * t0 ^ 3 * v1 * u1 * a2 * s1
    + (20100446945280 : R) * t0 ^ 3 * v1 * a4 * b3
    + (26800595927040 : R) * t0 ^ 3 * v1 * a3 * b4
    + (33500744908800 : R) * t0 ^ 3 * v1 * a2 * b5
    + (10050223472640 : R) * t0 ^ 3 * u1 ^ 2 * b3
    - (58626303590400 : R) * t0 ^ 3 * u1 * a4 * a2
    - (29313151795200 : R) * t0 ^ 3 * u1 * a3 ^ 2
    + (40200893890560 : R) * t0 ^ 3 * u1 * a2 * b62
    + (46901042872320 : R) * t0 ^ 3 * a4 * a2 * w1
    + (23450521436160 : R) * t0 ^ 3 * a3 ^ 2 * w1
    + (106783624396800 : R) * t0 ^ 2 * v1 ^ 4 * a2
    - (113902532689920 : R) * t0 ^ 2 * v1 ^ 3 * a2 * s1
    + (30150670417920 : R) * t0 ^ 2 * v1 ^ 2 * u1 * b3
    - (201004469452800 : R) * t0 ^ 2 * v1 ^ 2 * a4 * a2
    - (100502234726400 : R) * t0 ^ 2 * v1 ^ 2 * a3 ^ 2
    + (60301340835840 : R) * t0 ^ 2 * v1 ^ 2 * a2 * b62
    - (201004469452800 : R) * t0 ^ 2 * v1 * u1 ^ 2 * a2
    + (140703128616960 : R) * t0 ^ 2 * v1 * u1 * a2 * w1
    + (160803575562240 : R) * t0 ^ 2 * v1 * a4 * a2 * s1
    + (80401787781120 : R) * t0 ^ 2 * v1 * a3 ^ 2 * s1
    + (80401787781120 : R) * t0 ^ 2 * u1 ^ 2 * a2 * s1
    - (18554258718720 : R) * t0 ^ 2 * u1 * a4 * b3
    - (24739011624960 : R) * t0 ^ 2 * u1 * a3 * b4
    - (30923764531200 : R) * t0 ^ 2 * u1 * a2 * b5
    + (30923764531200 : R) * t0 ^ 2 * a4 ^ 2 * a2
    + (30923764531200 : R) * t0 ^ 2 * a4 * a3 ^ 2
    - (37108517437440 : R) * t0 ^ 2 * a4 * a2 * b62
    - (18554258718720 : R) * t0 ^ 2 * a3 ^ 2 * b62
    + (5025111736320 : R) * t0 * v1 ^ 4 * b3
    - (209379655680000 : R) * t0 * v1 ^ 3 * u1 * a2
    + (46901042872320 : R) * t0 * v1 ^ 3 * a2 * w1
    + (160803575562240 : R) * t0 * v1 ^ 2 * u1 * a2 * s1
    - (18554258718720 : R) * t0 * v1 ^ 2 * a4 * b3
    - (24739011624960 : R) * t0 * v1 ^ 2 * a3 * b4
    - (30923764531200 : R) * t0 * v1 ^ 2 * a2 * b5
    - (18554258718720 : R) * t0 * v1 * u1 ^ 2 * b3
    + (262851998515200 : R) * t0 * v1 * u1 * a4 * a2
    + (131425999257600 : R) * t0 * v1 * u1 * a3 ^ 2
    - (74217034874880 : R) * t0 * v1 * u1 * a2 * b62
    - (86586540687360 : R) * t0 * v1 * a4 * a2 * w1
    - (43293270343680 : R) * t0 * v1 * a3 ^ 2 * w1
    + (43808666419200 : R) * t0 * u1 ^ 3 * a2
    - (43293270343680 : R) * t0 * u1 ^ 2 * a2 * w1
    - (98956046499840 : R) * t0 * u1 * a4 * a2 * s1
    - (49478023249920 : R) * t0 * u1 * a3 ^ 2 * s1
    + (8246337208320 : R) * t0 * a4 ^ 2 * b3
    + (21990232555520 : R) * t0 * a4 * a3 * b4
    + (27487790694400 : R) * t0 * a4 * a2 * b5
    + (13743895347200 : R) * t0 * a3 ^ 2 * b5
    - (14237816586240 : R) * v1 ^ 5 * a2
    + (13400297963520 : R) * v1 ^ 4 * a2 * s1
    - (6184752906240 : R) * v1 ^ 3 * u1 * b3
    + (67001489817600 : R) * v1 ^ 3 * a4 * a2
    + (33500744908800 : R) * v1 ^ 3 * a3 ^ 2
    - (12369505812480 : R) * v1 ^ 3 * a2 * b62
    + (100502234726400 : R) * v1 ^ 2 * u1 ^ 2 * a2
    - (43293270343680 : R) * v1 ^ 2 * u1 * a2 * w1
    - (49478023249920 : R) * v1 ^ 2 * a4 * a2 * s1
    - (24739011624960 : R) * v1 ^ 2 * a3 ^ 2 * s1
    - (49478023249920 : R) * v1 * u1 ^ 2 * a2 * s1
    + (16492674416640 : R) * v1 * u1 * a4 * b3
    + (21990232555520 : R) * v1 * u1 * a3 * b4
    + (27487790694400 : R) * v1 * u1 * a2 * b5
    - (61847529062400 : R) * v1 * a4 ^ 2 * a2
    - (61847529062400 : R) * v1 * a4 * a3 ^ 2
    + (32985348833280 : R) * v1 * a4 * a2 * b62
    + (16492674416640 : R) * v1 * a3 ^ 2 * b62
    + (2748779069440 : R) * u1 ^ 3 * b3
    - (61847529062400 : R) * u1 ^ 2 * a4 * a2
    - (30923764531200 : R) * u1 ^ 2 * a3 ^ 2
    + (16492674416640 : R) * u1 ^ 2 * a2 * b62
    + (38482906972160 : R) * u1 * a4 * a2 * w1
    + (19241453486080 : R) * u1 * a3 ^ 2 * w1
    + (21990232555520 : R) * a4 ^ 2 * a2 * s1
    + (21990232555520 : R) * a4 * a3 ^ 2 * s1

set_option maxHeartbeats 800000000 in
theorem piLeftUnsolvedOrder98Plus810_of_order99
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    piLeftUnsolvedOrder98Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda =
      piLeftUnsolvedOrder99810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
          b5 b4 b3 b2 b1 lambda +
        h * piLeftUnsolvedOrder99Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
          s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  simp only [piLeftUnsolvedOrder98Plus810, piLeftUnsolvedOrder99810,
    piLeftUnsolvedOrder99Plus810]
  ring

set_option maxHeartbeats 400000000 in
theorem piLeftUnsolvedOrder98Plus810_zero
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    piLeftUnsolvedOrder98Plus810 0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda =
      piLeftUnsolvedOrder99810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda := by
  rw [piLeftUnsolvedOrder98Plus810_of_order99]
  simp only [zero_mul, add_zero]

set_option maxHeartbeats 800000000 in
theorem piLeftUnsolvedTail810_of_order99
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    piLeftUnsolvedTail810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda =
      piLeftUnsolvedOrder97810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
          b5 b4 b3 b2 b1 lambda +
        h * piLeftUnsolvedOrder98810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
          b62 b5 b4 b3 b2 b1 lambda +
        h ^ 2 * piLeftUnsolvedOrder99810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 3 * piLeftUnsolvedOrder99Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
          s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  rw [piLeftUnsolvedTail810_of_order98,
    piLeftUnsolvedOrder98Plus810_of_order99]
  ring

/-- Order-`99` mixin on `t0 = u1 = 0`. -/
def piLeftUnsolvedOrder99810_t0u1Zero
    (v1 a4 a3 lambda : R) : R :=
    (13915694039040 : R) * a3 * a4 ^ 2 * v1 * lambda
    - (15075335208960 : R) * a3 * a4 * v1 ^ 3 * lambda
    + (3203508731904 : R) * a3 * v1 ^ 5 * lambda

set_option maxHeartbeats 400000000 in
theorem piLeftUnsolvedOrder99810_of_t0u1Zero
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) (ht0 : t0 = 0) (hu1 : u1 = 0) :
    piLeftUnsolvedOrder99810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda =
      piLeftUnsolvedOrder99810_t0u1Zero v1 a4 a3 lambda := by
  simp only [piLeftUnsolvedOrder99810,
    piLeftUnsolvedOrder99810_t0u1Zero, ht0, hu1]
  ring

set_option maxHeartbeats 400000000 in
theorem piLeftUnsolvedOrder99810_t0u1Zero_v1Zero
    (v1 a4 a3 lambda : R) (hv1 : v1 = 0) :
    piLeftUnsolvedOrder99810_t0u1Zero v1 a4 a3 lambda = 0 := by
  simp only [piLeftUnsolvedOrder99810_t0u1Zero, hv1]
  ring

/-- Integer `5`-clearing of the LEFT order-`99` mixin after
the four scalar relations.  Witnesses `m1, τ1, g1, k1` are not
inserted. -/
def piLeftUnsolvedLeftOrder99810 (t0 v1 u1 b62 a3 lambda : R) : R :=
    - (72361609003008 : R) * a3 * b62 ^ 2 * t0 ^ 2 * lambda
    + (44530220924928 : R) * a3 * b62 ^ 2 * v1 * lambda
    + (72550050693120 : R) * a3 * b62 * t0 ^ 6 * lambda
    - (354850197995520 : R) * a3 * b62 * t0 ^ 4 * v1 * lambda
    + (301506704179200 : R) * a3 * b62 * t0 ^ 3 * u1 * lambda
    + (417470821171200 : R) * a3 * b62 * t0 ^ 2 * v1 ^ 2 * lambda
    - (389639433093120 : R) * a3 * b62 * t0 * u1 * v1 * lambda
    + (55662776156160 : R) * a3 * b62 * u1 ^ 2 * lambda
    - (74217034874880 : R) * a3 * b62 * v1 ^ 3 * lambda
    - (10834572902400 : R) * a3 * t0 ^ 10 * lambda
    + (107822953267200 : R) * a3 * t0 ^ 8 * v1 * lambda
    - (117776056320000 : R) * a3 * t0 ^ 7 * u1 * lambda
    - (376031202508800 : R) * a3 * t0 ^ 6 * v1 ^ 2 * lambda
    + (672682475520000 : R) * a3 * t0 ^ 5 * u1 * v1 * lambda
    - (298335810355200 : R) * a3 * t0 ^ 4 * u1 ^ 2 * lambda
    + (540116464435200 : R) * a3 * t0 ^ 4 * v1 ^ 3 * lambda
    - (1053823913164800 : R) * a3 * t0 ^ 3 * u1 * v1 ^ 2 * lambda
    + (604462959820800 : R) * a3 * t0 ^ 2 * u1 ^ 2 * v1 * lambda
    - (280759998873600 : R) * a3 * t0 ^ 2 * v1 ^ 4 * lambda
    - (92771293593600 : R) * a3 * t0 * u1 ^ 3 * lambda
    + (400076203622400 : R) * a3 * t0 * u1 * v1 ^ 3 * lambda
    - (121762322841600 : R) * a3 * u1 ^ 2 * v1 ^ 2 * lambda
    + (26526791761920 : R) * a3 * v1 ^ 5 * lambda

/-- Integer `5`-clearing of the RIGHT/`u1 = 0` order-`99`
mixin after the four scalar relations. -/
def piLeftUnsolvedRightU1ZeroOrder99810 (v1 b62 a3 lambda : R) : R :=
    (44530220924928 : R) * a3 * b62 ^ 2 * v1 * lambda
    - (74217034874880 : R) * a3 * b62 * v1 ^ 3 * lambda
    + (26526791761920 : R) * a3 * v1 ^ 5 * lambda

set_option maxHeartbeats 400000000 in
theorem piLeftUnsolvedRightU1ZeroOrder99810_v1Zero
    (v1 b62 a3 lambda : R) (hv1 : v1 = 0) :
    piLeftUnsolvedRightU1ZeroOrder99810 v1 b62 a3 lambda = 0 := by
  simp only [piLeftUnsolvedRightU1ZeroOrder99810, hv1]
  ring

/-- Cofactor of `16 b62 - 5 v1²` in the `16²`-cleared RIGHT/`u1 = 0`
order-`99` mixin. -/
def piLeftUnsolvedRightU1ZeroOrder99B62Cofactor810
    (v1 b62 a3 lambda : R) : R :=
    (712483534798848 : R) * a3 * b62 * v1 * lambda
    - (964821453373440 : R) * a3 * v1 ^ 3 * lambda

set_option maxHeartbeats 400000000 in
/-- Fifteenth-face extra `16 b62 = 5 v1²` specializes the RIGHT/`u1 = 0`
order-`99` mixin to a multiple of `a3 λ v1⁵`. -/
theorem piLeftUnsolvedRightU1ZeroOrder99810_b62Law
    (v1 b62 a3 lambda : R) :
    (16 : R) ^ 2 * piLeftUnsolvedRightU1ZeroOrder99810 v1 b62 a3
        lambda =
      ((16 : R) * b62 - (5 : R) * v1 ^ 2) *
          piLeftUnsolvedRightU1ZeroOrder99B62Cofactor810
            v1 b62 a3 lambda +
        (1966751424184320 : R) * a3 * v1 ^ 5 * lambda := by
  simp only [piLeftUnsolvedRightU1ZeroOrder99810,
    piLeftUnsolvedRightU1ZeroOrder99B62Cofactor810]
  ring

/-- Frozen order-`99` mixin on the RIGHT complement scalar locus. -/
def piLeftUnsolvedRightComplementOrder99810
    (v1 u1 a3 lambda : R) : R :=
    - (17394617548800 : R) * a3 * u1 ^ 2 * v1 ^ 2 * lambda
    - (492847497216 : R) * a3 * v1 ^ 5 * lambda

set_option maxHeartbeats 400000000 in
theorem piLeftUnsolvedRightComplementOrder99810_v1Zero
    (v1 u1 a3 lambda : R) (hv1 : v1 = 0) :
    piLeftUnsolvedRightComplementOrder99810 v1 u1 a3 lambda = 0 := by
  simp only [piLeftUnsolvedRightComplementOrder99810, hv1]
  ring

/-- Cofactor of `2 u1² + v1³` in the `4`-cleared complement mixin. -/
def piLeftUnsolvedRightComplementOrder99U1Cofactor810
    (v1 u1 a3 lambda : R) : R :=
    - (34789235097600 : R) * a3 * v1 ^ 2 * lambda

set_option maxHeartbeats 400000000 in
/-- Fifteenth-face extra `2 u1² + v1³ = 0` specializes the complement
order-`99` mixin. -/
theorem piLeftUnsolvedRightComplementOrder99810_u1rel
    (v1 u1 a3 lambda : R) :
    (4 : R) * piLeftUnsolvedRightComplementOrder99810 v1 u1 a3
        lambda =
      ((2 : R) * u1 ^ 2 + v1 ^ 3) *
          piLeftUnsolvedRightComplementOrder99U1Cofactor810
            v1 u1 a3 lambda +
        (32817845108736 : R) * a3 * v1 ^ 5 * lambda := by
  simp only [piLeftUnsolvedRightComplementOrder99810,
    piLeftUnsolvedRightComplementOrder99U1Cofactor810]
  ring

end PiOrder99Frozen810

section PiOrder99Map810

variable {R S : Type*} [CommRing R] [CommRing S]

set_option maxHeartbeats 800000000 in
theorem map_piLeftUnsolvedOrder99810 (phi : R →+* S)
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    phi (piLeftUnsolvedOrder99810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda) =
      piLeftUnsolvedOrder99810 (phi t0) (phi v1) (phi u1) (phi a4)
        (phi a3) (phi a2) (phi a1) (phi a0) (phi s1) (phi w1)
        (phi b62) (phi b5) (phi b4) (phi b3) (phi b2) (phi b1)
        (phi lambda) := by
  simp only [piLeftUnsolvedOrder99810, map_add, map_sub, map_mul,
    map_pow, map_neg, map_ofNat, map_zero]

#print axioms map_piLeftUnsolvedOrder99810

end PiOrder99Map810

section PiOrder99Eval810

variable {k : Type*} [CommRing k]

theorem piLeftUnsolvedOrder99810_eval
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 : k[X])
    (lambda a : k) :
    (piLeftUnsolvedOrder99810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a =
      piLeftUnsolvedOrder99810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda := by
  simpa [Polynomial.eval_C] using
    map_piLeftUnsolvedOrder99810 (Polynomial.evalRingHom a) t0 v1 u1 a4
      a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)

#print axioms piLeftUnsolvedOrder99810_eval

end PiOrder99Eval810

section PiOrder99Source810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 800000000 in
/-- Remaining power vanishing after the unsolved order-`98` residual is
peeled.  Witnesses stay unsolved.  The three `h0`-divisibilities are
the shape the ceiling lemma consumes. -/
theorem piLeftUnsolvedOrder99810_zero_of_power
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 : k[X])
    (lambda eta a : k) (hh : h ≠ 0) (hdegree : h.natDegree = 1)
    (hroot : h.eval a = 0)
    (hpower :
      localClearedSixteenthDefect810
          h (h ^ 6 * t0) (h ^ 4 * v1) (h ^ 2 * u1)
          a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1)
          (h ^ 2 * b62) b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 112) :
    ∃ (o96n o97n o98n : k[X]),
      piLeftUnsolvedHead810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
          b5 b4 b3 b2 b1 (Polynomial.C lambda) = h * o96n ∧
        o96n +
            piLeftUnsolvedOrder97810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o97n ∧
        o97n +
            piLeftUnsolvedOrder98810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o98n ∧
        o98n.eval a +
            piLeftUnsolvedOrder99810 (t0.eval a) (v1.eval a)
              (u1.eval a) (a4.eval a) (a3.eval a) (a2.eval a)
              (a1.eval a) (a0.eval a) (s1.eval a) (w1.eval a)
              (b62.eval a) (b5.eval a) (b4.eval a) (b3.eval a)
              (b2.eval a) (b1.eval a) lambda = 0 := by
  obtain ⟨o96n, o97n, ho, ho97, hmix⟩ :=
    piLeftUnsolvedOrder98810_zero_of_power h t0 v1 u1 a4 a3 a2 a1 a0 s1
      w1 b62 b5 b4 b3 b2 b1 lambda eta a hh hdegree hroot hpower
  have hsum0 :
      (o97n +
          piLeftUnsolvedOrder98810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
            b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a = 0 := by
    rw [Polynomial.eval_add, piLeftUnsolvedOrder98810_eval]
    exact hmix
  obtain ⟨o98n, ho98⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h
      (o97n +
        piLeftUnsolvedOrder98810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
          b5 b4 b3 b2 b1 (Polynomial.C lambda))
      a hdegree hroot hsum0
  have h96 : h ^ 96 ≠ 0 := pow_ne_zero 96 hh
  have hquot :
      piLeftUnsolvedHead810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
          b5 b4 b3 b2 b1 (Polynomial.C lambda) +
        h * piLeftUnsolvedTail810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
          b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 16 := by
    apply mul_left_cancel₀ h96
    rw [← localClearedSixteenthDefect810_left_unsolved_factored]
    rw [hpower]
    ring
  have hcancel :
      o96n +
          piLeftUnsolvedTail810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
            b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 15 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o96n +
            piLeftUnsolvedTail810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          piLeftUnsolvedHead810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
              b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedTail810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
              w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho]
        ring
      _ = Polynomial.C eta * h ^ 16 := hquot
      _ = h * (Polynomial.C eta * h ^ 15) := by ring
  have hplus14 :
      o97n +
          piLeftUnsolvedOrder97Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 14 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o97n +
            piLeftUnsolvedOrder97Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o96n +
            piLeftUnsolvedOrder97810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder97Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho97]
        ring
      _ = o96n +
            piLeftUnsolvedTail810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedTail810_of_order97]
        ring
      _ = Polynomial.C eta * h ^ 15 := hcancel
      _ = h * (Polynomial.C eta * h ^ 14) := by ring
  have hplus13 :
      o98n +
          piLeftUnsolvedOrder98Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 13 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o98n +
            piLeftUnsolvedOrder98Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o97n +
            piLeftUnsolvedOrder98810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder98Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho98]
        ring
      _ = o97n +
            piLeftUnsolvedOrder97Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedOrder97Plus810_of_order98]
        ring
      _ = Polynomial.C eta * h ^ 14 := hplus14
      _ = h * (Polynomial.C eta * h ^ 13) := by ring
  have htail :
      (piLeftUnsolvedOrder98Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
          b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a =
        (piLeftUnsolvedOrder99810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
          b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a := by
    rw [piLeftUnsolvedOrder98Plus810_of_order99]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, hroot,
      zero_mul, add_zero]
  refine ⟨o96n, o97n, o98n, ho, ho97, ho98, ?_⟩
  have hev := congrArg (Polynomial.eval a) hplus13
  rw [← piLeftUnsolvedOrder99810_eval, ← htail]
  simpa [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, hroot] using hev

set_option maxHeartbeats 800000000 in
/-- Source-facing order-`99` peel from a literal `(8,10)` source. -/
theorem piLeftUnsolvedOrder99810_zero_of_source
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (t0 v1 u1 s1 w1 b62 : k[X])
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hdegree : h0.natDegree = 1) (hH : H = h0 ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0)
    (ht0 : p.coeff 7 = h0 ^ 6 * t0)
    (hv1 : p.coeff 6 = h0 ^ 4 * v1)
    (hu1 : p.coeff 5 = h0 ^ 2 * u1)
    (hs1 : q.coeff 8 = h0 ^ 6 * s1)
    (hw1 : q.coeff 7 = h0 ^ 4 * w1)
    (hb62 : q.coeff 6 = h0 ^ 2 * b62) :
    ∃ (o96n o97n o98n : k[X]),
      piLeftUnsolvedHead810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
          (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62 (q.coeff 5)
          (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
          (Polynomial.C lambda) = h0 * o96n ∧
        o96n +
            piLeftUnsolvedOrder97810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o97n ∧
        o97n +
            piLeftUnsolvedOrder98810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o98n ∧
        o98n.eval a +
            piLeftUnsolvedOrder99810 (t0.eval a) (v1.eval a)
              (u1.eval a) ((p.coeff 4).eval a) ((p.coeff 3).eval a)
              ((p.coeff 2).eval a) ((p.coeff 1).eval a)
              ((p.coeff 0).eval a) (s1.eval a) (w1.eval a)
              (b62.eval a) ((q.coeff 5).eval a) ((q.coeff 4).eval a)
              ((q.coeff 3).eval a) ((q.coeff 2).eval a)
              ((q.coeff 1).eval a) lambda = 0 := by
  obtain ⟨eta, heta⟩ :=
    sourcePiResidual810_eq_C_of_source p q H h0 j lambda hp hq hh0 hH
      hp8 hq10 hN hD
  have hNpeel :
      5 * (h0 ^ 6 * t0) * h0 ^ 2 - 4 * q.coeff 9 =
        Polynomial.C lambda * h0 ^ 9 := by
    simpa only [ht0, hH] using hN
  have hpi :
      sourcePiResidual810
          (algebraMap k[X] (RatFunc k) h0)
          (algebraMap k[X] (RatFunc k) (h0 ^ 6 * t0))
          (algebraMap k[X] (RatFunc k) (h0 ^ 4 * v1))
          (algebraMap k[X] (RatFunc k) (h0 ^ 2 * u1))
          (algebraMap k[X] (RatFunc k) (p.coeff 4))
          (algebraMap k[X] (RatFunc k) (p.coeff 3))
          (algebraMap k[X] (RatFunc k) (p.coeff 2))
          (algebraMap k[X] (RatFunc k) (p.coeff 1))
          (algebraMap k[X] (RatFunc k) (p.coeff 0))
          (algebraMap k[X] (RatFunc k) (q.coeff 9))
          (algebraMap k[X] (RatFunc k) (h0 ^ 6 * s1))
          (algebraMap k[X] (RatFunc k) (h0 ^ 4 * w1))
          (algebraMap k[X] (RatFunc k) (h0 ^ 2 * b62))
          (algebraMap k[X] (RatFunc k) (q.coeff 5))
          (algebraMap k[X] (RatFunc k) (q.coeff 4))
          (algebraMap k[X] (RatFunc k) (q.coeff 3))
          (algebraMap k[X] (RatFunc k) (q.coeff 2))
          (algebraMap k[X] (RatFunc k) (q.coeff 1))
          (RatFunc.C lambda) =
        algebraMap k (RatFunc k) eta := by
    simpa only [ht0, hv1, hu1, hs1, hw1, hb62] using heta
  have hpower :=
    piSourcePowerRelation810_of_residual_eq_C h0 (h0 ^ 6 * t0)
      (h0 ^ 4 * v1) (h0 ^ 2 * u1) (p.coeff 4) (p.coeff 3)
      (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 9) (h0 ^ 6 * s1)
      (h0 ^ 4 * w1) (h0 ^ 2 * b62) (q.coeff 5) (q.coeff 4)
      (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda eta hh0 hNpeel hpi
  exact piLeftUnsolvedOrder99810_zero_of_power h0 t0 v1 u1
    (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1
    b62 (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
    lambda (17592186044416 * eta) a hh0 hdegree hroot hpower

set_option maxHeartbeats 800000000 in
/-- Source-facing order-`99` chambers.  Witnesses stay unsolved.  The
fifteenth-face extras are carried from the parent.  This is not a
closure. -/
theorem piFace810_linearRoot_order99Chambers
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hh0degree : h0.natDegree = 1) (hH : H = h0 ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0) :
    ∃ (t0 v0 u0 s0 w0 v1 s1 u1 w1 b62 o96n o97n o98n : k[X]),
      p.coeff 7 = h0 ^ 6 * t0 ∧ p.coeff 6 = h0 ^ 3 * v0 ∧
        p.coeff 5 = h0 * u0 ∧ q.coeff 8 = h0 ^ 5 * s0 ∧
        q.coeff 7 = h0 ^ 3 * w0 ∧ v0 = h0 * v1 ∧ s0 = h0 * s1 ∧
        u0 = h0 * u1 ∧ w0 = h0 * w1 ∧ q.coeff 6 = h0 ^ 2 * b62 ∧
        piLeftUnsolvedHead810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
            (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
            (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
            (q.coeff 1) (Polynomial.C lambda) = h0 * o96n ∧
        o96n +
            piLeftUnsolvedOrder97810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o97n ∧
        o97n +
            piLeftUnsolvedOrder98810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o98n ∧
        o98n.eval a +
            piLeftUnsolvedOrder99810 (t0.eval a) (v1.eval a)
              (u1.eval a) ((p.coeff 4).eval a) ((p.coeff 3).eval a)
              ((p.coeff 2).eval a) ((p.coeff 1).eval a)
              ((p.coeff 0).eval a) (s1.eval a) (w1.eval a)
              (b62.eval a) ((q.coeff 5).eval a) ((q.coeff 4).eval a)
              ((q.coeff 3).eval a) ((q.coeff 2).eval a)
              ((q.coeff 1).eval a) lambda = 0 ∧
        ((v0.eval a = 0 ∧ s0.eval a = 0 ∧ (q.coeff 6).eval a = 0 ∧
            u0.eval a = 0 ∧ w0.eval a = 0 ∧
            (32 : k) * s1.eval a - (40 : k) * v1.eval a =
              (5 : k) * (t0.eval a) ^ 2 ∧
            (128 : k) * w1.eval a - (160 : k) * u1.eval a -
                (40 : k) * t0.eval a * v1.eval a +
              (5 : k) * (t0.eval a) ^ 3 = 0 ∧
            tenthFace_Gred810 (t0.eval a) (v1.eval a) (u1.eval a)
                ((p.coeff 4).eval a) (b62.eval a) ∧
            tenthFace_Vred810 (t0.eval a) (v1.eval a) (u1.eval a)
                ((p.coeff 4).eval a) (b62.eval a)
                ((q.coeff 5).eval a) ∧
            (twelfthFace_leftF1_810 (t0.eval a) (v1.eval a)
                (u1.eval a) ∨
              twelfthFace_leftF2_810 (t0.eval a) (v1.eval a)
                (u1.eval a)) ∧
            (∃ (m1 tau1 : k[X]),
              (32 : k[X]) * s1 - (40 : k[X]) * v1 -
                    (5 : k[X]) * t0 ^ 2 =
                  h0 * m1 ∧
                (128 : k[X]) * w1 - (160 : k[X]) * u1 -
                    (40 : k[X]) * t0 * v1 + (5 : k[X]) * t0 ^ 3 =
                  h0 * tau1 ∧
                m1.eval a + (9 : k) * lambda * t0.eval a = 0 ∧
                (4 : k) * tau1.eval a +
                    (9 : k) * lambda * (t0.eval a) ^ 2 +
                  (144 : k) * lambda * v1.eval a = 0) ∧
            (∃ g1 : k[X],
              (2560 : k[X]) * (p.coeff 4) - (2048 : k[X]) * b62 +
                    (35 : k[X]) * t0 ^ 4 -
                    (240 : k[X]) * t0 ^ 2 * v1 +
                    (640 : k[X]) * t0 * u1 + (320 : k[X]) * v1 ^ 2 =
                  h0 * g1 ∧
                (2 : k) * g1.eval a +
                    (3 : k) * lambda *
                      ((7 : k) * (t0.eval a) ^ 3 -
                        (48 : k) * t0.eval a * v1.eval a -
                        (384 : k) * u1.eval a) = 0) ∧
            (∃ k1 : k[X],
              (81920 : k[X]) * (p.coeff 4) * t0 +
                    (131072 : k[X]) * (q.coeff 5) -
                    (98304 : k[X]) * b62 * t0 +
                    (2912 : k[X]) * t0 ^ 5 -
                    (20480 : k[X]) * t0 ^ 3 * v1 +
                    (46080 : k[X]) * t0 ^ 2 * u1 +
                    (30720 : k[X]) * t0 * v1 ^ 2 -
                    (40960 : k[X]) * u1 * v1 =
                  h0 * k1)) ∨
          (t0.eval a = 0 ∧ u0.eval a = 0 ∧ w0.eval a = 0 ∧
            v0.eval a = 0 ∧ s0.eval a = 0 ∧
            (q.coeff 6).eval a = 0 ∧
            (4 : k) * s1.eval a = (5 : k) * v1.eval a ∧
            (4 : k) * w1.eval a = (5 : k) * u1.eval a ∧
            (40 : k) * (p.coeff 4).eval a - (32 : k) * b62.eval a +
              (5 : k) * (v1.eval a) ^ 2 = 0 ∧
            (16 : k) * (q.coeff 5).eval a =
              (5 : k) * u1.eval a * v1.eval a ∧
            ((u1.eval a = 0 ∧ o96n.eval a = 0 ∧
                (16 : k) * b62.eval a * v1.eval a =
                  (5 : k) * (v1.eval a) ^ 3) ∨
              ((5 : k) * (v1.eval a) ^ 2 - (8 : k) * b62.eval a =
                  0 ∧
                (2 : k) * (u1.eval a) ^ 2 + (v1.eval a) ^ 3 =
                  0)))) := by
  obtain ⟨t0, v0, u0, s0, w0, v1, s1, u1, w1, b62, o96n, o97n, ht0, hv0,
      hu0, hs0, hw0, hv1, hs1, hu1, hw1, hb62, ho96, ho97, hmix98,
      hsplit⟩ :=
    piFace810_linearRoot_order98Chambers p q H h0 j lambda a hp hq
      hh0 hh0degree hH hp8 hq10 hN hD hroot
  have ha6 : p.coeff 6 = h0 ^ 4 * v1 := by
    rw [hv0, hv1]
    ring
  have ha5 : p.coeff 5 = h0 ^ 2 * u1 := by
    rw [hu0, hu1]
    ring
  have hb8 : q.coeff 8 = h0 ^ 6 * s1 := by
    rw [hs0, hs1]
    ring
  have hb7 : q.coeff 7 = h0 ^ 4 * w1 := by
    rw [hw0, hw1]
    ring
  obtain ⟨o96n', o97n', o98n, ho', ho97', ho98, hmix99⟩ :=
    piLeftUnsolvedOrder99810_zero_of_source p q H h0 j lambda a t0 v1
      u1 s1 w1 b62 hp hq hh0 hh0degree hH hp8 hq10 hN hD hroot ht0 ha6
      ha5 hb8 hb7 hb62
  have ho96eq : o96n = o96n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o96n = piLeftUnsolvedHead810 t0 v1 u1 (p.coeff 4)
          (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
          (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
          (q.coeff 1) (Polynomial.C lambda) := ho96.symm
      _ = h0 * o96n' := ho'
  subst ho96eq
  have ho97eq : o97n = o97n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o97n = o96n +
          piLeftUnsolvedOrder97810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
            (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
            (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
            (q.coeff 1) (Polynomial.C lambda) := ho97.symm
      _ = h0 * o97n' := ho97'
  subst ho97eq
  refine ⟨t0, v0, u0, s0, w0, v1, s1, u1, w1, b62, o96n, o97n, o98n,
    ht0, hv0, hu0, hs0, hw0, hv1, hs1, hu1, hw1, hb62, ho96, ho97, ho98,
    hmix99, ?_⟩
  exact hsplit

#print axioms piLeftUnsolvedOrder98Plus810_of_order99
#print axioms piLeftUnsolvedOrder99810_of_t0u1Zero
#print axioms piLeftUnsolvedOrder99810_t0u1Zero_v1Zero
#print axioms piLeftUnsolvedRightU1ZeroOrder99810_v1Zero
#print axioms piLeftUnsolvedRightU1ZeroOrder99810_b62Law
#print axioms piLeftUnsolvedRightComplementOrder99810_v1Zero
#print axioms piLeftUnsolvedRightComplementOrder99810_u1rel
#print axioms piLeftUnsolvedOrder99810_zero_of_power
#print axioms piLeftUnsolvedOrder99810_zero_of_source
#print axioms piFace810_linearRoot_order99Chambers

end PiOrder99Source810

end Max11DegreeRoutes
