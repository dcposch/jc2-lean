import Grok810PiOrder99Scratch

/-! # Orders `100` through `104` of the `(8,10)` degree-one `π` tower

`Grok810PiOrder99Scratch` leaves three live chambers after the unsolved
order-`99` coefficient is extracted:

* LEFT: `o98n(a) + Order99(a) = 0` with the frozen mixin and unsolved
  witnesses `m1, τ1, g1, k1`;
* RIGHT/`u1 = 0`: the fifteenth-face extra `16 b62 v1 = 5 v1³` mixed
  with the next coefficient;
* RIGHT complement: the extra `2 u1² + v1³ = 0` on `5 v1² = 8 b62`.

This file continues the unsolved tail through orders `100`, `101`,
`102`, `103`, and `104` in one module.  Each order `k` is the `h⁰`
coefficient of the previous Plus remainder, equivalently the
`h^(k-97)` coefficient of the unsolved tail and the `h^(k-96)`
coefficient of the factored residual after the order-`96` head.  The
four scalar load solves are not inserted as polynomial identities, and
the old scalar-solved jet is not imported.  Witnesses stay unsolved.

The landed fifteenth-face extras are carried from the parent: on
RIGHT/`u1 = 0` the mixed extra is `16 b62 v1 = 5 v1³`; on the complement
`5 v1² = 8 b62` it is `2 u1² + v1³ = 0`.  Order `101` vanishes
identically at `t0 = u1 = 0`, so the RIGHT/`u1 = 0` packet has a
vanishing order-`101` coefficient.  Those scalar conclusions of the
named residuals are not re-evaluated against the source-facing
residual.  No chamber is closed.  The next unused compact-numerator
order is `105`.

Vanishing is recorded in the `h0`-divisibility shape the ceiling lemma
consumes: `Head = h0 · o96n`, then `o(n-1)n + Order n = h0 · on n` for
`n = 97, …, 103`, and `o103n(a) + Order104(a) = 0`.  Intermediate
orders record the same shape truncated at that order.  The tower
ceiling is order `112` from the weight-`112` source power relation;
orders `96` through `112` exhaust the unsolved head before the
cancel-and-expose endgame (`ρ` polynomial versus `ρ' = j/h0`).  This
file does not close any chamber.

No total-degree or twice-prime theorem is used.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option maxHeartbeats 1600000000
set_option linter.unusedVariables false

section PiOrder100Frozen810

variable {R : Type*} [CommRing R]

set_option maxHeartbeats 1600000000 in
/-- Frozen order-`100` mixin: the `h⁰` coefficient of the order-`99` Plus
remainder, equivalently the `h^3` coefficient of the unsolved tail
and the `h^4` coefficient of the factored residual after the
order-`96` head. -/
def piLeftUnsolvedOrder100810 (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
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

set_option maxHeartbeats 1600000000 in
/-- Remaining factor after `h` is removed from the order-`99` Plus
remainder. -/
def piLeftUnsolvedOrder100Plus810 (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (21990232555520 : R) * h ^ 11 * a0 ^ 2
    + (9895604649984 : R) * h ^ 10 * a1 * a0 * lambda
    + (5497558138880 : R) * h ^ 9 * t0 * a1 * a0
    + (17592186044416 : R) * h ^ 9 * a1 * b1
    + (35184372088832 : R) * h ^ 9 * a0 * b2
    - (12369505812480 : R) * h ^ 8 * t0 * a2 * a0 * lambda
    - (6184752906240 : R) * h ^ 8 * t0 * a1 ^ 2 * lambda
    - (4398046511104 : R) * h ^ 7 * t0 * a2 * b1
    - (8796093022208 : R) * h ^ 7 * t0 * a1 * b2
    - (13194139533312 : R) * h ^ 7 * t0 * a0 * b3
    + (54975581388800 : R) * h ^ 7 * v1 * a2 * a0
    + (27487790694400 : R) * h ^ 7 * v1 * a1 ^ 2
    - (35184372088832 : R) * h ^ 7 * a2 * a0 * s1
    - (17592186044416 : R) * h ^ 7 * a1 ^ 2 * s1
    + (13915694039040 : R) * h ^ 6 * t0 ^ 2 * a3 * a0 * lambda
    + (13915694039040 : R) * h ^ 6 * t0 ^ 2 * a2 * a1 * lambda
    - (12369505812480 : R) * h ^ 6 * v1 * a3 * a0 * lambda
    - (12369505812480 : R) * h ^ 6 * v1 * a2 * a1 * lambda
    - (2576980377600 : R) * h ^ 5 * t0 ^ 3 * a3 * a0
    - (2576980377600 : R) * h ^ 5 * t0 ^ 3 * a2 * a1
    + (2748779069440 : R) * h ^ 5 * t0 ^ 2 * a3 * b1
    + (5497558138880 : R) * h ^ 5 * t0 ^ 2 * a2 * b2
    + (8246337208320 : R) * h ^ 5 * t0 ^ 2 * a1 * b3
    + (10995116277760 : R) * h ^ 5 * t0 ^ 2 * a0 * b4
    - (61847529062400 : R) * h ^ 5 * t0 * v1 * a3 * a0
    - (61847529062400 : R) * h ^ 5 * t0 * v1 * a2 * a1
    + (43980465111040 : R) * h ^ 5 * t0 * a3 * a0 * s1
    + (43980465111040 : R) * h ^ 5 * t0 * a2 * a1 * s1
    - (4398046511104 : R) * h ^ 5 * v1 * a3 * b1
    - (8796093022208 : R) * h ^ 5 * v1 * a2 * b2
    - (13194139533312 : R) * h ^ 5 * v1 * a1 * b3
    - (17592186044416 : R) * h ^ 5 * v1 * a0 * b4
    + (54975581388800 : R) * h ^ 5 * u1 * a3 * a0
    + (54975581388800 : R) * h ^ 5 * u1 * a2 * a1
    - (30786325577728 : R) * h ^ 5 * a3 * a0 * w1
    - (30786325577728 : R) * h ^ 5 * a2 * a1 * w1
    + (2502741196800 : R) * h ^ 4 * t0 ^ 7 * a0 * lambda
    - (16818420842496 : R) * h ^ 4 * t0 ^ 5 * v1 * a0 * lambda
    + (16017543659520 : R) * h ^ 4 * t0 ^ 4 * u1 * a0 * lambda
    + (32035087319040 : R) * h ^ 4 * t0 ^ 3 * v1 ^ 2 * a0 * lambda
    - (15075335208960 : R) * h ^ 4 * t0 ^ 3 * a4 * a0 * lambda
    - (15075335208960 : R) * h ^ 4 * t0 ^ 3 * a3 * a1 * lambda
    - (7537667604480 : R) * h ^ 4 * t0 ^ 3 * a2 ^ 2 * lambda
    - (45226005626880 : R) * h ^ 4 * t0 ^ 2 * v1 * u1 * a0 * lambda
    - (15075335208960 : R) * h ^ 4 * t0 * v1 ^ 3 * a0 * lambda
    + (27831388078080 : R) * h ^ 4 * t0 * v1 * a4 * a0 * lambda
    + (27831388078080 : R) * h ^ 4 * t0 * v1 * a3 * a1 * lambda
    + (13915694039040 : R) * h ^ 4 * t0 * v1 * a2 ^ 2 * lambda
    + (13915694039040 : R) * h ^ 4 * t0 * u1 ^ 2 * a0 * lambda
    + (13915694039040 : R) * h ^ 4 * v1 ^ 2 * u1 * a0 * lambda
    - (12369505812480 : R) * h ^ 4 * u1 * a4 * a0 * lambda
    - (12369505812480 : R) * h ^ 4 * u1 * a3 * a1 * lambda
    - (6184752906240 : R) * h ^ 4 * u1 * a2 ^ 2 * lambda
    - (2433220608000 : R) * h ^ 3 * t0 ^ 8 * a0
    + (177972707328 : R) * h ^ 3 * t0 ^ 7 * b1
    + (6229044756480 : R) * h ^ 3 * t0 ^ 6 * v1 * a0
    + (9966471610368 : R) * h ^ 3 * t0 ^ 6 * a0 * s1
    - (1423781658624 : R) * h ^ 3 * t0 ^ 5 * v1 * b1
    - (5339181219840 : R) * h ^ 3 * t0 ^ 5 * u1 * a0
    - (9966471610368 : R) * h ^ 3 * t0 ^ 5 * a0 * w1
    + (26695906099200 : R) * h ^ 3 * t0 ^ 4 * v1 ^ 2 * a0
    - (56951266344960 : R) * h ^ 3 * t0 ^ 4 * v1 * a0 * s1
    + (1675037245440 : R) * h ^ 3 * t0 ^ 4 * u1 * b1
    + (4187593113600 : R) * h ^ 3 * t0 ^ 4 * a4 * a0
    + (4187593113600 : R) * h ^ 3 * t0 ^ 4 * a3 * a1
    + (2093796556800 : R) * h ^ 3 * t0 ^ 4 * a2 ^ 2
    + (10050223472640 : R) * h ^ 3 * t0 ^ 4 * a0 * b62
    + (3350074490880 : R) * h ^ 3 * t0 ^ 3 * v1 ^ 2 * b1
    - (58626303590400 : R) * h ^ 3 * t0 ^ 3 * v1 * u1 * a0
    + (46901042872320 : R) * h ^ 3 * t0 ^ 3 * v1 * a0 * w1
    + (53601191854080 : R) * h ^ 3 * t0 ^ 3 * u1 * a0 * s1
    - (2061584302080 : R) * h ^ 3 * t0 ^ 3 * a4 * b1
    - (4123168604160 : R) * h ^ 3 * t0 ^ 3 * a3 * b2
    - (6184752906240 : R) * h ^ 3 * t0 ^ 3 * a2 * b3
    - (8246337208320 : R) * h ^ 3 * t0 ^ 3 * a1 * b4
    - (10307921510400 : R) * h ^ 3 * t0 ^ 3 * a0 * b5
    - (67001489817600 : R) * h ^ 3 * t0 ^ 2 * v1 ^ 3 * a0
    + (80401787781120 : R) * h ^ 3 * t0 ^ 2 * v1 ^ 2 * a0 * s1
    - (6184752906240 : R) * h ^ 3 * t0 ^ 2 * v1 * u1 * b1
    + (61847529062400 : R) * h ^ 3 * t0 ^ 2 * v1 * a4 * a0
    + (61847529062400 : R) * h ^ 3 * t0 ^ 2 * v1 * a3 * a1
    + (30923764531200 : R) * h ^ 3 * t0 ^ 2 * v1 * a2 ^ 2
    - (37108517437440 : R) * h ^ 3 * t0 ^ 2 * v1 * a0 * b62
    + (30923764531200 : R) * h ^ 3 * t0 ^ 2 * u1 ^ 2 * a0
    - (43293270343680 : R) * h ^ 3 * t0 ^ 2 * u1 * a0 * w1
    - (49478023249920 : R) * h ^ 3 * t0 ^ 2 * a4 * a0 * s1
    - (49478023249920 : R) * h ^ 3 * t0 ^ 2 * a3 * a1 * s1
    - (24739011624960 : R) * h ^ 3 * t0 ^ 2 * a2 ^ 2 * s1
    - (2061584302080 : R) * h ^ 3 * t0 * v1 ^ 3 * b1
    + (131425999257600 : R) * h ^ 3 * t0 * v1 ^ 2 * u1 * a0
    - (43293270343680 : R) * h ^ 3 * t0 * v1 ^ 2 * a0 * w1
    - (98956046499840 : R) * h ^ 3 * t0 * v1 * u1 * a0 * s1
    + (5497558138880 : R) * h ^ 3 * t0 * v1 * a4 * b1
    + (10995116277760 : R) * h ^ 3 * t0 * v1 * a3 * b2
    + (16492674416640 : R) * h ^ 3 * t0 * v1 * a2 * b3
    + (21990232555520 : R) * h ^ 3 * t0 * v1 * a1 * b4
    + (27487790694400 : R) * h ^ 3 * t0 * v1 * a0 * b5
    + (2748779069440 : R) * h ^ 3 * t0 * u1 ^ 2 * b1
    - (61847529062400 : R) * h ^ 3 * t0 * u1 * a4 * a0
    - (61847529062400 : R) * h ^ 3 * t0 * u1 * a3 * a1
    - (30923764531200 : R) * h ^ 3 * t0 * u1 * a2 ^ 2
    + (32985348833280 : R) * h ^ 3 * t0 * u1 * a0 * b62
    + (38482906972160 : R) * h ^ 3 * t0 * a4 * a0 * w1
    + (38482906972160 : R) * h ^ 3 * t0 * a3 * a1 * w1
    + (19241453486080 : R) * h ^ 3 * t0 * a2 ^ 2 * w1
    + (16750372454400 : R) * h ^ 3 * v1 ^ 4 * a0
    - (16492674416640 : R) * h ^ 3 * v1 ^ 3 * a0 * s1
    + (2748779069440 : R) * h ^ 3 * v1 ^ 2 * u1 * b1
    - (61847529062400 : R) * h ^ 3 * v1 ^ 2 * a4 * a0
    - (61847529062400 : R) * h ^ 3 * v1 ^ 2 * a3 * a1
    - (30923764531200 : R) * h ^ 3 * v1 ^ 2 * a2 ^ 2
    + (16492674416640 : R) * h ^ 3 * v1 ^ 2 * a0 * b62
    - (61847529062400 : R) * h ^ 3 * v1 * u1 ^ 2 * a0
    + (38482906972160 : R) * h ^ 3 * v1 * u1 * a0 * w1
    + (43980465111040 : R) * h ^ 3 * v1 * a4 * a0 * s1
    + (43980465111040 : R) * h ^ 3 * v1 * a3 * a1 * s1
    + (21990232555520 : R) * h ^ 3 * v1 * a2 ^ 2 * s1
    + (21990232555520 : R) * h ^ 3 * u1 ^ 2 * a0 * s1
    - (4398046511104 : R) * h ^ 3 * u1 * a4 * b1
    - (8796093022208 : R) * h ^ 3 * u1 * a3 * b2
    - (13194139533312 : R) * h ^ 3 * u1 * a2 * b3
    - (17592186044416 : R) * h ^ 3 * u1 * a1 * b4
    - (21990232555520 : R) * h ^ 3 * u1 * a0 * b5
    + (27487790694400 : R) * h ^ 3 * a4 ^ 2 * a0
    + (54975581388800 : R) * h ^ 3 * a4 * a3 * a1
    + (27487790694400 : R) * h ^ 3 * a4 * a2 ^ 2
    - (26388279066624 : R) * h ^ 3 * a4 * a0 * b62
    + (27487790694400 : R) * h ^ 3 * a3 ^ 2 * a2
    - (26388279066624 : R) * h ^ 3 * a3 * a1 * b62
    - (13194139533312 : R) * h ^ 3 * a2 ^ 2 * b62
    - (2268109209600 : R) * h ^ 2 * t0 ^ 8 * a1 * lambda
    + (17519188377600 : R) * h ^ 2 * t0 ^ 6 * v1 * a1 * lambda
    - (16818420842496 : R) * h ^ 2 * t0 ^ 5 * u1 * a1 * lambda
    - (42046052106240 : R) * h ^ 2 * t0 ^ 4 * v1 ^ 2 * a1 * lambda
    + (16017543659520 : R) * h ^ 2 * t0 ^ 4 * a4 * a1 * lambda
    + (16017543659520 : R) * h ^ 2 * t0 ^ 4 * a3 * a2 * lambda
    + (64070174638080 : R) * h ^ 2 * t0 ^ 3 * v1 * u1 * a1 * lambda
    + (32035087319040 : R) * h ^ 2 * t0 ^ 2 * v1 ^ 3 * a1 * lambda
    - (45226005626880 : R) * h ^ 2 * t0 ^ 2 * v1 * a4 * a1 * lambda
    - (45226005626880 : R) * h ^ 2 * t0 ^ 2 * v1 * a3 * a2 * lambda
    - (22613002813440 : R) * h ^ 2 * t0 ^ 2 * u1 ^ 2 * a1 * lambda
    - (45226005626880 : R) * h ^ 2 * t0 * v1 ^ 2 * u1 * a1 * lambda
    + (27831388078080 : R) * h ^ 2 * t0 * u1 * a4 * a1 * lambda
    + (27831388078080 : R) * h ^ 2 * t0 * u1 * a3 * a2 * lambda
    - (3768833802240 : R) * h ^ 2 * v1 ^ 4 * a1 * lambda
    + (13915694039040 : R) * h ^ 2 * v1 ^ 2 * a4 * a1 * lambda
    + (13915694039040 : R) * h ^ 2 * v1 ^ 2 * a3 * a2 * lambda
    + (13915694039040 : R) * h ^ 2 * v1 * u1 ^ 2 * a1 * lambda
    - (6184752906240 : R) * h ^ 2 * a4 ^ 2 * a1 * lambda
    - (12369505812480 : R) * h ^ 2 * a4 * a3 * a2 * lambda
    - (2061584302080 : R) * h ^ 2 * a3 ^ 3 * lambda
    + (2100101120000 : R) * h * t0 ^ 9 * a1
    - (278082355200 : R) * h * t0 ^ 8 * b2
    - (6952058880000 : R) * h * t0 ^ 7 * v1 * a1
    - (8898635366400 : R) * h * t0 ^ 7 * a1 * s1
    + (2491617902592 : R) * h * t0 ^ 6 * v1 * b2
    + (6229044756480 : R) * h * t0 ^ 6 * u1 * a1
    + (8720662659072 : R) * h * t0 ^ 6 * a1 * w1
    - (23358917836800 : R) * h * t0 ^ 5 * v1 ^ 2 * a1
    + (59798829662208 : R) * h * t0 ^ 5 * v1 * a1 * s1
    - (2847563317248 : R) * h * t0 ^ 5 * u1 * b2
    - (5339181219840 : R) * h * t0 ^ 5 * a4 * a1
    - (5339181219840 : R) * h * t0 ^ 5 * a3 * a2
    - (8542689951744 : R) * h * t0 ^ 5 * a1 * b62
    - (7118908293120 : R) * h * t0 ^ 4 * v1 ^ 2 * b2
    + (53391812198400 : R) * h * t0 ^ 4 * v1 * u1 * a1
    - (49832358051840 : R) * h * t0 ^ 4 * v1 * a1 * w1
    - (56951266344960 : R) * h * t0 ^ 4 * u1 * a1 * s1
    + (3350074490880 : R) * h * t0 ^ 4 * a4 * b2
    + (5025111736320 : R) * h * t0 ^ 4 * a3 * b3
    + (6700148981760 : R) * h * t0 ^ 4 * a2 * b4
    + (8375186227200 : R) * h * t0 ^ 4 * a1 * b5
    + (88986353664000 : R) * h * t0 ^ 3 * v1 ^ 3 * a1
    - (113902532689920 : R) * h * t0 ^ 3 * v1 ^ 2 * a1 * s1
    + (13400297963520 : R) * h * t0 ^ 3 * v1 * u1 * b2
    - (58626303590400 : R) * h * t0 ^ 3 * v1 * a4 * a1
    - (58626303590400 : R) * h * t0 ^ 3 * v1 * a3 * a2
    + (40200893890560 : R) * h * t0 ^ 3 * v1 * a1 * b62
    - (29313151795200 : R) * h * t0 ^ 3 * u1 ^ 2 * a1
    + (46901042872320 : R) * h * t0 ^ 3 * u1 * a1 * w1
    + (53601191854080 : R) * h * t0 ^ 3 * a4 * a1 * s1
    + (53601191854080 : R) * h * t0 ^ 3 * a3 * a2 * s1
    + (6700148981760 : R) * h * t0 ^ 2 * v1 ^ 3 * b2
    - (201004469452800 : R) * h * t0 ^ 2 * v1 ^ 2 * u1 * a1
    + (70351564308480 : R) * h * t0 ^ 2 * v1 ^ 2 * a1 * w1
    + (160803575562240 : R) * h * t0 ^ 2 * v1 * u1 * a1 * s1
    - (12369505812480 : R) * h * t0 ^ 2 * v1 * a4 * b2
    - (18554258718720 : R) * h * t0 ^ 2 * v1 * a3 * b3
    - (24739011624960 : R) * h * t0 ^ 2 * v1 * a2 * b4
    - (30923764531200 : R) * h * t0 ^ 2 * v1 * a1 * b5
    - (6184752906240 : R) * h * t0 ^ 2 * u1 ^ 2 * b2
    + (61847529062400 : R) * h * t0 ^ 2 * u1 * a4 * a1
    + (61847529062400 : R) * h * t0 ^ 2 * u1 * a3 * a2
    - (37108517437440 : R) * h * t0 ^ 2 * u1 * a1 * b62
    - (43293270343680 : R) * h * t0 ^ 2 * a4 * a1 * w1
    - (43293270343680 : R) * h * t0 ^ 2 * a3 * a2 * w1
    - (52344913920000 : R) * h * t0 * v1 ^ 4 * a1
    + (53601191854080 : R) * h * t0 * v1 ^ 3 * a1 * s1
    - (12369505812480 : R) * h * t0 * v1 ^ 2 * u1 * b2
    + (131425999257600 : R) * h * t0 * v1 ^ 2 * a4 * a1
    + (131425999257600 : R) * h * t0 * v1 ^ 2 * a3 * a2
    - (37108517437440 : R) * h * t0 * v1 ^ 2 * a1 * b62
    + (131425999257600 : R) * h * t0 * v1 * u1 ^ 2 * a1
    - (86586540687360 : R) * h * t0 * v1 * u1 * a1 * w1
    - (98956046499840 : R) * h * t0 * v1 * a4 * a1 * s1
    - (98956046499840 : R) * h * t0 * v1 * a3 * a2 * s1
    - (49478023249920 : R) * h * t0 * u1 ^ 2 * a1 * s1
    + (10995116277760 : R) * h * t0 * u1 * a4 * b2
    + (16492674416640 : R) * h * t0 * u1 * a3 * b3
    + (21990232555520 : R) * h * t0 * u1 * a2 * b4
    + (27487790694400 : R) * h * t0 * u1 * a1 * b5
    - (30923764531200 : R) * h * t0 * a4 ^ 2 * a1
    - (61847529062400 : R) * h * t0 * a4 * a3 * a2
    + (32985348833280 : R) * h * t0 * a4 * a1 * b62
    - (10307921510400 : R) * h * t0 * a3 ^ 3
    + (32985348833280 : R) * h * t0 * a3 * a2 * b62
    - (1030792151040 : R) * h * v1 ^ 4 * b2
    + (67001489817600 : R) * h * v1 ^ 3 * u1 * a1
    - (14431090114560 : R) * h * v1 ^ 3 * a1 * w1
    - (49478023249920 : R) * h * v1 ^ 2 * u1 * a1 * s1
    + (5497558138880 : R) * h * v1 ^ 2 * a4 * b2
    + (8246337208320 : R) * h * v1 ^ 2 * a3 * b3
    + (10995116277760 : R) * h * v1 ^ 2 * a2 * b4
    + (13743895347200 : R) * h * v1 ^ 2 * a1 * b5
    + (5497558138880 : R) * h * v1 * u1 ^ 2 * b2
    - (123695058124800 : R) * h * v1 * u1 * a4 * a1
    - (123695058124800 : R) * h * v1 * u1 * a3 * a2
    + (32985348833280 : R) * h * v1 * u1 * a1 * b62
    + (38482906972160 : R) * h * v1 * a4 * a1 * w1
    + (38482906972160 : R) * h * v1 * a3 * a2 * w1
    - (20615843020800 : R) * h * u1 ^ 3 * a1
    + (19241453486080 : R) * h * u1 ^ 2 * a1 * w1
    + (43980465111040 : R) * h * u1 * a4 * a1 * s1
    + (43980465111040 : R) * h * u1 * a3 * a2 * s1
    - (4398046511104 : R) * h * a4 ^ 2 * b2
    - (13194139533312 : R) * h * a4 * a3 * b3
    - (17592186044416 : R) * h * a4 * a2 * b4
    - (21990232555520 : R) * h * a4 * a1 * b5
    - (8796093022208 : R) * h * a3 ^ 2 * b4
    - (21990232555520 : R) * h * a3 * a2 * b5
    + (2079100108800 : R) * t0 ^ 9 * a2 * lambda
    - (18144873676800 : R) * t0 ^ 7 * v1 * a2 * lambda
    + (17519188377600 : R) * t0 ^ 6 * u1 * a2 * lambda
    + (52557565132800 : R) * t0 ^ 5 * v1 ^ 2 * a2 * lambda
    - (16818420842496 : R) * t0 ^ 5 * a4 * a2 * lambda
    - (8409210421248 : R) * t0 ^ 5 * a3 ^ 2 * lambda
    - (84092104212480 : R) * t0 ^ 4 * v1 * u1 * a2 * lambda
    - (56061402808320 : R) * t0 ^ 3 * v1 ^ 3 * a2 * lambda
    + (64070174638080 : R) * t0 ^ 3 * v1 * a4 * a2 * lambda
    + (32035087319040 : R) * t0 ^ 3 * v1 * a3 ^ 2 * lambda
    + (32035087319040 : R) * t0 ^ 3 * u1 ^ 2 * a2 * lambda
    + (96105261957120 : R) * t0 ^ 2 * v1 ^ 2 * u1 * a2 * lambda
    - (45226005626880 : R) * t0 ^ 2 * u1 * a4 * a2 * lambda
    - (22613002813440 : R) * t0 ^ 2 * u1 * a3 ^ 2 * lambda
    + (16017543659520 : R) * t0 * v1 ^ 4 * a2 * lambda
    - (45226005626880 : R) * t0 * v1 ^ 2 * a4 * a2 * lambda
    - (22613002813440 : R) * t0 * v1 ^ 2 * a3 ^ 2 * lambda
    - (45226005626880 : R) * t0 * v1 * u1 ^ 2 * a2 * lambda
    + (13915694039040 : R) * t0 * a4 ^ 2 * a2 * lambda
    + (13915694039040 : R) * t0 * a4 * a3 ^ 2 * lambda
    - (15075335208960 : R) * v1 ^ 3 * u1 * a2 * lambda
    + (27831388078080 : R) * v1 * u1 * a4 * a2 * lambda
    + (13915694039040 : R) * v1 * u1 * a3 ^ 2 * lambda
    + (4638564679680 : R) * u1 ^ 3 * a2 * lambda

set_option maxHeartbeats 1600000000 in
theorem piLeftUnsolvedOrder99Plus810_of_order100
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    piLeftUnsolvedOrder99Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda =
      piLeftUnsolvedOrder100810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
          b5 b4 b3 b2 b1 lambda +
        h * piLeftUnsolvedOrder100Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
          s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  simp only [piLeftUnsolvedOrder99Plus810, piLeftUnsolvedOrder100810,
    piLeftUnsolvedOrder100Plus810]
  ring

set_option maxHeartbeats 400000000 in
theorem piLeftUnsolvedOrder99Plus810_zero
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    piLeftUnsolvedOrder99Plus810 0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda =
      piLeftUnsolvedOrder100810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda := by
  rw [piLeftUnsolvedOrder99Plus810_of_order100]
  simp only [zero_mul, add_zero]

set_option maxHeartbeats 800000000 in
theorem piLeftUnsolvedTail810_of_order100
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    piLeftUnsolvedTail810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda =
      piLeftUnsolvedOrder97810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
          b5 b4 b3 b2 b1 lambda +
        h * piLeftUnsolvedOrder98810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
          b62 b5 b4 b3 b2 b1 lambda +
        h ^ 2 * piLeftUnsolvedOrder99810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 3 * piLeftUnsolvedOrder100810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 4 * piLeftUnsolvedOrder100Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
          s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  rw [piLeftUnsolvedTail810_of_order99, piLeftUnsolvedOrder99Plus810_of_order100]
  ring

/-- Order-`100` mixin on `t0 = u1 = 0`. -/
def piLeftUnsolvedOrder100810_t0u1Zero
    (v1 a4 a3 a2 s1 b62 : R) : R :=
    - (14237816586240 : R) * v1 ^ 5 * a2
    + (13400297963520 : R) * v1 ^ 4 * a2 * s1
    + (67001489817600 : R) * v1 ^ 3 * a4 * a2
    + (33500744908800 : R) * v1 ^ 3 * a3 ^ 2
    - (12369505812480 : R) * v1 ^ 3 * a2 * b62
    - (49478023249920 : R) * v1 ^ 2 * a4 * a2 * s1
    - (24739011624960 : R) * v1 ^ 2 * a3 ^ 2 * s1
    - (61847529062400 : R) * v1 * a4 ^ 2 * a2
    - (61847529062400 : R) * v1 * a4 * a3 ^ 2
    + (32985348833280 : R) * v1 * a4 * a2 * b62
    + (16492674416640 : R) * v1 * a3 ^ 2 * b62
    + (21990232555520 : R) * a4 ^ 2 * a2 * s1
    + (21990232555520 : R) * a4 * a3 ^ 2 * s1

set_option maxHeartbeats 800000000 in
theorem piLeftUnsolvedOrder100810_of_t0u1Zero
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) (ht0 : t0 = 0) (hu1 : u1 = 0) :
    piLeftUnsolvedOrder100810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda =
      piLeftUnsolvedOrder100810_t0u1Zero v1 a4 a3 a2 s1 b62 := by
  simp only [piLeftUnsolvedOrder100810,
    piLeftUnsolvedOrder100810_t0u1Zero, ht0, hu1]
  ring

/-- Integer `5`-clearing of the LEFT order-`100` mixin after
the four scalar relations.  Witnesses `m1, τ1, g1, k1` are not
inserted. -/
def piLeftUnsolvedLeftOrder100810 (t0 v1 u1 a3 a2 b62 b4 b3 : R) : R :=
    - (567200972800 : R) * t0 ^ 10 * a2
    + (1979774402560 : R) * t0 ^ 9 * b3
    + (6711672832000 : R) * t0 ^ 8 * v1 * a2
    - (20166884720640 : R) * t0 ^ 7 * v1 * b3
    - (9110028288000 : R) * t0 ^ 7 * u1 * a2
    - (28529655808000 : R) * t0 ^ 6 * v1 ^ 2 * a2
    + (25576530247680 : R) * t0 ^ 6 * u1 * b3
    - (14542490828800 : R) * t0 ^ 6 * a3 ^ 2
    + (7274600857600 : R) * t0 ^ 6 * a2 * b62
    + (69924751933440 : R) * t0 ^ 5 * v1 ^ 2 * b3
    + (64760053760000 : R) * t0 ^ 5 * v1 * u1 * a2
    - (29978871726080 : R) * t0 ^ 5 * a3 * b4
    - (17987323035648 : R) * t0 ^ 5 * b62 * b3
    + (51841597440000 : R) * t0 ^ 4 * v1 ^ 3 * a2
    - (143666656051200 : R) * t0 ^ 4 * v1 * u1 * b3
    + (88583700480000 : R) * t0 ^ 4 * v1 * a3 ^ 2
    - (46385646796800 : R) * t0 ^ 4 * v1 * a2 * b62
    - (36909875200000 : R) * t0 ^ 4 * u1 ^ 2 * a2
    - (93415538688000 : R) * t0 ^ 3 * v1 ^ 3 * b3
    - (132070244352000 : R) * t0 ^ 3 * v1 ^ 2 * u1 * a2
    + (144310901145600 : R) * t0 ^ 3 * v1 * a3 * b4
    + (86586540687360 : R) * t0 ^ 3 * v1 * b62 * b3
    + (76020921139200 : R) * t0 ^ 3 * u1 ^ 2 * b3
    - (98784247808000 : R) * t0 ^ 3 * u1 * a3 ^ 2
    + (42090679500800 : R) * t0 ^ 3 * u1 * a2 * b62
    - (36507222016000 : R) * t0 ^ 2 * v1 ^ 4 * a2
    + (195850508697600 : R) * t0 ^ 2 * v1 ^ 2 * u1 * b3
    - (135291469824000 : R) * t0 ^ 2 * v1 ^ 2 * a3 ^ 2
    + (80745385164800 : R) * t0 ^ 2 * v1 ^ 2 * a2 * b62
    + (113816633344000 : R) * t0 ^ 2 * v1 * u1 ^ 2 * a2
    - (151182848819200 : R) * t0 ^ 2 * u1 * a3 * b4
    - (90709709291520 : R) * t0 ^ 2 * u1 * b62 * b3
    + (61847529062400 : R) * t0 ^ 2 * a3 ^ 2 * b62
    - (10995116277760 : R) * t0 ^ 2 * a2 * b62 ^ 2
    + (37366215475200 : R) * t0 * v1 ^ 4 * b3
    + (64424509440000 : R) * t0 * v1 ^ 3 * u1 * a2
    - (137438953472000 : R) * t0 * v1 ^ 2 * a3 * b4
    - (82463372083200 : R) * t0 * v1 ^ 2 * b62 * b3
    - (113387136614400 : R) * t0 * v1 * u1 ^ 2 * b3
    + (171798691840000 : R) * t0 * v1 * u1 * a3 ^ 2
    - (103079215104000 : R) * t0 * v1 * u1 * a2 * b62
    - (34359738368000 : R) * t0 * u1 ^ 3 * a2
    + (87960930222080 : R) * t0 * a3 * b62 * b4
    + (26388279066624 : R) * t0 * b62 ^ 2 * b3
    + (6657199308800 : R) * v1 ^ 5 * a2
    - (41231686041600 : R) * v1 ^ 3 * u1 * b3
    + (34359738368000 : R) * v1 ^ 3 * a3 ^ 2
    - (27487790694400 : R) * v1 ^ 3 * a2 * b62
    - (25769803776000 : R) * v1 ^ 2 * u1 ^ 2 * a2
    + (109951162777600 : R) * v1 * u1 * a3 * b4
    + (65970697666560 : R) * v1 * u1 * b62 * b3
    - (54975581388800 : R) * v1 * a3 ^ 2 * b62
    + (21990232555520 : R) * v1 * a2 * b62 ^ 2
    + (13743895347200 : R) * u1 ^ 3 * b3
    - (34359738368000 : R) * u1 ^ 2 * a3 ^ 2
    + (27487790694400 : R) * u1 ^ 2 * a2 * b62

/-- Integer `1`-clearing of the RIGHT/`u1 = 0` order-`100`
mixin after the four scalar relations. -/
def piLeftUnsolvedRightU1ZeroOrder100810 (v1 a3 a2 b62 : R) : R :=
    (1331439861760 : R) * v1 ^ 5 * a2
    + (6871947673600 : R) * v1 ^ 3 * a3 ^ 2
    - (5497558138880 : R) * v1 ^ 3 * a2 * b62
    - (10995116277760 : R) * v1 * a3 ^ 2 * b62
    + (4398046511104 : R) * v1 * a2 * b62 ^ 2

set_option maxHeartbeats 400000000 in
theorem piLeftUnsolvedRightU1ZeroOrder100810_v1Zero
    (v1 a3 a2 b62 : R) (hv1 : v1 = 0) :
    piLeftUnsolvedRightU1ZeroOrder100810 v1 a3 a2 b62 = 0 := by
  simp only [piLeftUnsolvedRightU1ZeroOrder100810, hv1]
  ring

/-- Cofactor of `16 b62 - 5 v1²` in the cleared RIGHT/`u1 = 0`
order-`100` mixin. -/
def piLeftUnsolvedRightU1ZeroOrder100B62Cofactor810
    (v1 a3 a2 b62 : R) : R :=
    - (65970697666560 : R) * v1 ^ 3 * a2
    - (175921860444160 : R) * v1 * a3 ^ 2
    + (70368744177664 : R) * v1 * a2 * b62

set_option maxHeartbeats 400000000 in
/-- Fifteenth-face extra `16 b62 = 5 v1²` specializes the RIGHT/`u1 = 0`
order-`100` mixin. -/
theorem piLeftUnsolvedRightU1ZeroOrder100810_b62Law
    (v1 a3 a2 b62 : R) :
    (256 : R) * piLeftUnsolvedRightU1ZeroOrder100810 v1 a3 a2 b62 =
      ((16 : R) * b62 - (5 : R) * v1 ^ 2) *
          piLeftUnsolvedRightU1ZeroOrder100B62Cofactor810
            v1 a3 a2 b62 +
        (10995116277760 : R) * v1 ^ 5 * a2
        + (879609302220800 : R) * v1 ^ 3 * a3 ^ 2 := by
  simp only [piLeftUnsolvedRightU1ZeroOrder100810,
    piLeftUnsolvedRightU1ZeroOrder100B62Cofactor810]
  ring

/-- Frozen order-`100` mixin on the RIGHT complement scalar locus. -/
def piLeftUnsolvedRightComplementOrder100810
    (v1 u1 a3 a2 b4 b3 : R) : R :=
    - (386547056640 : R) * v1 ^ 5 * a2
    - (1717986918400 : R) * v1 ^ 2 * u1 ^ 2 * a2
    + (21990232555520 : R) * v1 * u1 * a3 * b4
    + (2748779069440 : R) * u1 ^ 3 * b3
    - (6871947673600 : R) * u1 ^ 2 * a3 ^ 2

/-- Cofactor of `2 u1² + v1³` in the cleared complement mixin. -/
def piLeftUnsolvedRightComplementOrder100U1Cofactor810
    (v1 u1 a3 a2 b4 b3 : R) : R :=
    - (3435973836800 : R) * v1 ^ 2 * a2
    + (5497558138880 : R) * u1 * b3
    - (13743895347200 : R) * a3 ^ 2

set_option maxHeartbeats 400000000 in
/-- Fifteenth-face extra `2 u1² + v1³ = 0` specializes the complement
order-`100` mixin. -/
theorem piLeftUnsolvedRightComplementOrder100810_u1rel
    (v1 u1 a3 a2 b4 b3 : R) :
    (4 : R) * piLeftUnsolvedRightComplementOrder100810 v1 u1 a3 a2 b4 b3 =
      ((2 : R) * u1 ^ 2 + v1 ^ 3) *
          piLeftUnsolvedRightComplementOrder100U1Cofactor810
            v1 u1 a3 a2 b4 b3 +
        (1889785610240 : R) * v1 ^ 5 * a2
        - (5497558138880 : R) * v1 ^ 3 * u1 * b3
        + (13743895347200 : R) * v1 ^ 3 * a3 ^ 2
        + (87960930222080 : R) * v1 * u1 * a3 * b4 := by
  simp only [piLeftUnsolvedRightComplementOrder100810,
    piLeftUnsolvedRightComplementOrder100U1Cofactor810]
  ring

end PiOrder100Frozen810

section PiOrder100Map810

variable {R S : Type*} [CommRing R] [CommRing S]

set_option maxHeartbeats 800000000 in
theorem map_piLeftUnsolvedOrder100810 (phi : R →+* S)
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    phi (piLeftUnsolvedOrder100810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda) =
      piLeftUnsolvedOrder100810 (phi t0) (phi v1) (phi u1) (phi a4)
        (phi a3) (phi a2) (phi a1) (phi a0) (phi s1) (phi w1)
        (phi b62) (phi b5) (phi b4) (phi b3) (phi b2) (phi b1)
        (phi lambda) := by
  simp only [piLeftUnsolvedOrder100810, map_add, map_sub, map_mul,
    map_pow, map_neg, map_ofNat, map_zero]

#print axioms map_piLeftUnsolvedOrder100810

end PiOrder100Map810

section PiOrder100Eval810

variable {k : Type*} [CommRing k]

theorem piLeftUnsolvedOrder100810_eval
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 : k[X])
    (lambda a : k) :
    (piLeftUnsolvedOrder100810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a =
      piLeftUnsolvedOrder100810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda := by
  simpa [Polynomial.eval_C] using
    map_piLeftUnsolvedOrder100810 (Polynomial.evalRingHom a) t0 v1 u1 a4
      a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)

#print axioms piLeftUnsolvedOrder100810_eval

end PiOrder100Eval810
section PiOrder100Source810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 800000000 in
/-- Remaining power vanishing after the unsolved order-`99` residual is
peeled.  Witnesses stay unsolved.  The `h0`-divisibilities are the
shape the ceiling lemma consumes. -/
theorem piLeftUnsolvedOrder100810_zero_of_power
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 : k[X])
    (lambda eta a : k) (hh : h ≠ 0) (hdegree : h.natDegree = 1)
    (hroot : h.eval a = 0)
    (hpower :
      localClearedSixteenthDefect810
          h (h ^ 6 * t0) (h ^ 4 * v1) (h ^ 2 * u1)
          a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1)
          (h ^ 2 * b62) b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 112) :
    ∃ (o96n o97n o98n o99n : k[X]),
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
        o98n +
            piLeftUnsolvedOrder99810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o99n ∧
        o99n.eval a +
            piLeftUnsolvedOrder100810 (t0.eval a) (v1.eval a)
              (u1.eval a) (a4.eval a) (a3.eval a) (a2.eval a)
              (a1.eval a) (a0.eval a) (s1.eval a) (w1.eval a)
              (b62.eval a) (b5.eval a) (b4.eval a) (b3.eval a)
              (b2.eval a) (b1.eval a) lambda = 0 := by
  obtain ⟨o96n, o97n, o98n, ho, ho97, ho98, hmix⟩ :=
    piLeftUnsolvedOrder99810_zero_of_power h t0 v1 u1 a4 a3 a2 a1 a0 s1
      w1 b62 b5 b4 b3 b2 b1 lambda eta a hh hdegree hroot hpower
  have hsum0 :
      (o98n +
          piLeftUnsolvedOrder99810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a = 0 := by
    rw [Polynomial.eval_add, piLeftUnsolvedOrder99810_eval]
    exact hmix
  obtain ⟨o99n, ho99⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h
      (o98n +
        piLeftUnsolvedOrder99810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda))
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
  have hplus12 :
      o99n +
          piLeftUnsolvedOrder99Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 12 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o99n +
            piLeftUnsolvedOrder99Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o98n +
            piLeftUnsolvedOrder99810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder99Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho99]
        ring
      _ = o98n +
            piLeftUnsolvedOrder98Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedOrder98Plus810_of_order99]
        ring
      _ = Polynomial.C eta * h ^ 13 := hplus13
      _ = h * (Polynomial.C eta * h ^ 12) := by ring
  have htail :
      (piLeftUnsolvedOrder99Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
          b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a =
        (piLeftUnsolvedOrder100810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
          b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a := by
    rw [piLeftUnsolvedOrder99Plus810_of_order100]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, hroot,
      zero_mul, add_zero]
  refine ⟨o96n, o97n, o98n, o99n, ho, ho97, ho98, ho99, ?_⟩
  have hev := congrArg (Polynomial.eval a) hplus12
  rw [← piLeftUnsolvedOrder100810_eval, ← htail]
  simpa [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, hroot] using hev

set_option maxHeartbeats 800000000 in
/-- Source-facing order-`100` peel from a literal `(8,10)` source. -/
theorem piLeftUnsolvedOrder100810_zero_of_source
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
    ∃ (o96n o97n o98n o99n : k[X]),
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
        o98n +
            piLeftUnsolvedOrder99810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o99n ∧
        o99n.eval a +
            piLeftUnsolvedOrder100810 (t0.eval a) (v1.eval a)
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
  exact piLeftUnsolvedOrder100810_zero_of_power h0 t0 v1 u1
    (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1
    b62 (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
    lambda (17592186044416 * eta) a hh0 hdegree hroot hpower

set_option maxHeartbeats 800000000 in
/-- Source-facing order-`100` chambers.  Witnesses stay unsolved.  The
fifteenth-face extras are carried from the parent.  This is not a
closure. -/
theorem piFace810_linearRoot_order100Chambers
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
    ∃ (t0 v0 u0 s0 w0 v1 s1 u1 w1 b62 o96n o97n o98n o99n : k[X]),
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
        o98n +
            piLeftUnsolvedOrder99810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o99n ∧
        o99n.eval a +
            piLeftUnsolvedOrder100810 (t0.eval a) (v1.eval a)
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
  obtain ⟨t0, v0, u0, s0, w0, v1, s1, u1, w1, b62, o96n, o97n, o98n, ht0, hv0, hu0, hs0, hw0, hv1, hs1, hu1, hw1, hb62, ho96, ho97, ho98, hmix99, hsplit⟩ :=
    piFace810_linearRoot_order99Chambers p q H h0 j lambda a hp hq
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
  obtain ⟨o96n', o97n', o98n', o99n, ho', ho97', ho98', ho99, hmix100⟩ :=
    piLeftUnsolvedOrder100810_zero_of_source p q H h0 j lambda a t0 v1
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
  have ho98eq : o98n = o98n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o98n = o97n +
          piLeftUnsolvedOrder98810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) := ho98.symm
      _ = h0 * o98n' := ho98'
  subst ho98eq
  refine ⟨t0, v0, u0, s0, w0, v1, s1, u1, w1, b62, o96n, o97n, o98n, o99n,
    ht0, hv0, hu0, hs0, hw0, hv1, hs1, hu1, hw1, hb62, ho96, ho97, ho98, ho99, hmix100, ?_⟩
  exact hsplit

#print axioms piLeftUnsolvedOrder99Plus810_of_order100
#print axioms piLeftUnsolvedOrder100810_of_t0u1Zero
#print axioms piLeftUnsolvedOrder100810_zero_of_power
#print axioms piLeftUnsolvedOrder100810_zero_of_source
#print axioms piFace810_linearRoot_order100Chambers
#print axioms piLeftUnsolvedRightU1ZeroOrder100810_b62Law
#print axioms piLeftUnsolvedRightComplementOrder100810_u1rel

end PiOrder100Source810
section PiOrder101Frozen810

variable {R : Type*} [CommRing R]

set_option maxHeartbeats 1600000000 in
/-- Frozen order-`101` mixin: the `h⁰` coefficient of the order-`100` Plus
remainder, equivalently the `h^4` coefficient of the unsolved tail
and the `h^5` coefficient of the factored residual after the
order-`96` head. -/
def piLeftUnsolvedOrder101810 (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (2079100108800 : R) * t0 ^ 9 * a2 * lambda
    - (18144873676800 : R) * t0 ^ 7 * v1 * a2 * lambda
    + (17519188377600 : R) * t0 ^ 6 * u1 * a2 * lambda
    + (52557565132800 : R) * t0 ^ 5 * v1 ^ 2 * a2 * lambda
    - (16818420842496 : R) * t0 ^ 5 * a4 * a2 * lambda
    - (8409210421248 : R) * t0 ^ 5 * a3 ^ 2 * lambda
    - (84092104212480 : R) * t0 ^ 4 * v1 * u1 * a2 * lambda
    - (56061402808320 : R) * t0 ^ 3 * v1 ^ 3 * a2 * lambda
    + (64070174638080 : R) * t0 ^ 3 * v1 * a4 * a2 * lambda
    + (32035087319040 : R) * t0 ^ 3 * v1 * a3 ^ 2 * lambda
    + (32035087319040 : R) * t0 ^ 3 * u1 ^ 2 * a2 * lambda
    + (96105261957120 : R) * t0 ^ 2 * v1 ^ 2 * u1 * a2 * lambda
    - (45226005626880 : R) * t0 ^ 2 * u1 * a4 * a2 * lambda
    - (22613002813440 : R) * t0 ^ 2 * u1 * a3 ^ 2 * lambda
    + (16017543659520 : R) * t0 * v1 ^ 4 * a2 * lambda
    - (45226005626880 : R) * t0 * v1 ^ 2 * a4 * a2 * lambda
    - (22613002813440 : R) * t0 * v1 ^ 2 * a3 ^ 2 * lambda
    - (45226005626880 : R) * t0 * v1 * u1 ^ 2 * a2 * lambda
    + (13915694039040 : R) * t0 * a4 ^ 2 * a2 * lambda
    + (13915694039040 : R) * t0 * a4 * a3 ^ 2 * lambda
    - (15075335208960 : R) * v1 ^ 3 * u1 * a2 * lambda
    + (27831388078080 : R) * v1 * u1 * a4 * a2 * lambda
    + (13915694039040 : R) * v1 * u1 * a3 ^ 2 * lambda
    + (4638564679680 : R) * u1 ^ 3 * a2 * lambda

set_option maxHeartbeats 1600000000 in
/-- Remaining factor after `h` is removed from the order-`100` Plus
remainder. -/
def piLeftUnsolvedOrder101Plus810 (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (21990232555520 : R) * h ^ 10 * a0 ^ 2
    + (9895604649984 : R) * h ^ 9 * a1 * a0 * lambda
    + (5497558138880 : R) * h ^ 8 * t0 * a1 * a0
    + (17592186044416 : R) * h ^ 8 * a1 * b1
    + (35184372088832 : R) * h ^ 8 * a0 * b2
    - (12369505812480 : R) * h ^ 7 * t0 * a2 * a0 * lambda
    - (6184752906240 : R) * h ^ 7 * t0 * a1 ^ 2 * lambda
    - (4398046511104 : R) * h ^ 6 * t0 * a2 * b1
    - (8796093022208 : R) * h ^ 6 * t0 * a1 * b2
    - (13194139533312 : R) * h ^ 6 * t0 * a0 * b3
    + (54975581388800 : R) * h ^ 6 * v1 * a2 * a0
    + (27487790694400 : R) * h ^ 6 * v1 * a1 ^ 2
    - (35184372088832 : R) * h ^ 6 * a2 * a0 * s1
    - (17592186044416 : R) * h ^ 6 * a1 ^ 2 * s1
    + (13915694039040 : R) * h ^ 5 * t0 ^ 2 * a3 * a0 * lambda
    + (13915694039040 : R) * h ^ 5 * t0 ^ 2 * a2 * a1 * lambda
    - (12369505812480 : R) * h ^ 5 * v1 * a3 * a0 * lambda
    - (12369505812480 : R) * h ^ 5 * v1 * a2 * a1 * lambda
    - (2576980377600 : R) * h ^ 4 * t0 ^ 3 * a3 * a0
    - (2576980377600 : R) * h ^ 4 * t0 ^ 3 * a2 * a1
    + (2748779069440 : R) * h ^ 4 * t0 ^ 2 * a3 * b1
    + (5497558138880 : R) * h ^ 4 * t0 ^ 2 * a2 * b2
    + (8246337208320 : R) * h ^ 4 * t0 ^ 2 * a1 * b3
    + (10995116277760 : R) * h ^ 4 * t0 ^ 2 * a0 * b4
    - (61847529062400 : R) * h ^ 4 * t0 * v1 * a3 * a0
    - (61847529062400 : R) * h ^ 4 * t0 * v1 * a2 * a1
    + (43980465111040 : R) * h ^ 4 * t0 * a3 * a0 * s1
    + (43980465111040 : R) * h ^ 4 * t0 * a2 * a1 * s1
    - (4398046511104 : R) * h ^ 4 * v1 * a3 * b1
    - (8796093022208 : R) * h ^ 4 * v1 * a2 * b2
    - (13194139533312 : R) * h ^ 4 * v1 * a1 * b3
    - (17592186044416 : R) * h ^ 4 * v1 * a0 * b4
    + (54975581388800 : R) * h ^ 4 * u1 * a3 * a0
    + (54975581388800 : R) * h ^ 4 * u1 * a2 * a1
    - (30786325577728 : R) * h ^ 4 * a3 * a0 * w1
    - (30786325577728 : R) * h ^ 4 * a2 * a1 * w1
    + (2502741196800 : R) * h ^ 3 * t0 ^ 7 * a0 * lambda
    - (16818420842496 : R) * h ^ 3 * t0 ^ 5 * v1 * a0 * lambda
    + (16017543659520 : R) * h ^ 3 * t0 ^ 4 * u1 * a0 * lambda
    + (32035087319040 : R) * h ^ 3 * t0 ^ 3 * v1 ^ 2 * a0 * lambda
    - (15075335208960 : R) * h ^ 3 * t0 ^ 3 * a4 * a0 * lambda
    - (15075335208960 : R) * h ^ 3 * t0 ^ 3 * a3 * a1 * lambda
    - (7537667604480 : R) * h ^ 3 * t0 ^ 3 * a2 ^ 2 * lambda
    - (45226005626880 : R) * h ^ 3 * t0 ^ 2 * v1 * u1 * a0 * lambda
    - (15075335208960 : R) * h ^ 3 * t0 * v1 ^ 3 * a0 * lambda
    + (27831388078080 : R) * h ^ 3 * t0 * v1 * a4 * a0 * lambda
    + (27831388078080 : R) * h ^ 3 * t0 * v1 * a3 * a1 * lambda
    + (13915694039040 : R) * h ^ 3 * t0 * v1 * a2 ^ 2 * lambda
    + (13915694039040 : R) * h ^ 3 * t0 * u1 ^ 2 * a0 * lambda
    + (13915694039040 : R) * h ^ 3 * v1 ^ 2 * u1 * a0 * lambda
    - (12369505812480 : R) * h ^ 3 * u1 * a4 * a0 * lambda
    - (12369505812480 : R) * h ^ 3 * u1 * a3 * a1 * lambda
    - (6184752906240 : R) * h ^ 3 * u1 * a2 ^ 2 * lambda
    - (2433220608000 : R) * h ^ 2 * t0 ^ 8 * a0
    + (177972707328 : R) * h ^ 2 * t0 ^ 7 * b1
    + (6229044756480 : R) * h ^ 2 * t0 ^ 6 * v1 * a0
    + (9966471610368 : R) * h ^ 2 * t0 ^ 6 * a0 * s1
    - (1423781658624 : R) * h ^ 2 * t0 ^ 5 * v1 * b1
    - (5339181219840 : R) * h ^ 2 * t0 ^ 5 * u1 * a0
    - (9966471610368 : R) * h ^ 2 * t0 ^ 5 * a0 * w1
    + (26695906099200 : R) * h ^ 2 * t0 ^ 4 * v1 ^ 2 * a0
    - (56951266344960 : R) * h ^ 2 * t0 ^ 4 * v1 * a0 * s1
    + (1675037245440 : R) * h ^ 2 * t0 ^ 4 * u1 * b1
    + (4187593113600 : R) * h ^ 2 * t0 ^ 4 * a4 * a0
    + (4187593113600 : R) * h ^ 2 * t0 ^ 4 * a3 * a1
    + (2093796556800 : R) * h ^ 2 * t0 ^ 4 * a2 ^ 2
    + (10050223472640 : R) * h ^ 2 * t0 ^ 4 * a0 * b62
    + (3350074490880 : R) * h ^ 2 * t0 ^ 3 * v1 ^ 2 * b1
    - (58626303590400 : R) * h ^ 2 * t0 ^ 3 * v1 * u1 * a0
    + (46901042872320 : R) * h ^ 2 * t0 ^ 3 * v1 * a0 * w1
    + (53601191854080 : R) * h ^ 2 * t0 ^ 3 * u1 * a0 * s1
    - (2061584302080 : R) * h ^ 2 * t0 ^ 3 * a4 * b1
    - (4123168604160 : R) * h ^ 2 * t0 ^ 3 * a3 * b2
    - (6184752906240 : R) * h ^ 2 * t0 ^ 3 * a2 * b3
    - (8246337208320 : R) * h ^ 2 * t0 ^ 3 * a1 * b4
    - (10307921510400 : R) * h ^ 2 * t0 ^ 3 * a0 * b5
    - (67001489817600 : R) * h ^ 2 * t0 ^ 2 * v1 ^ 3 * a0
    + (80401787781120 : R) * h ^ 2 * t0 ^ 2 * v1 ^ 2 * a0 * s1
    - (6184752906240 : R) * h ^ 2 * t0 ^ 2 * v1 * u1 * b1
    + (61847529062400 : R) * h ^ 2 * t0 ^ 2 * v1 * a4 * a0
    + (61847529062400 : R) * h ^ 2 * t0 ^ 2 * v1 * a3 * a1
    + (30923764531200 : R) * h ^ 2 * t0 ^ 2 * v1 * a2 ^ 2
    - (37108517437440 : R) * h ^ 2 * t0 ^ 2 * v1 * a0 * b62
    + (30923764531200 : R) * h ^ 2 * t0 ^ 2 * u1 ^ 2 * a0
    - (43293270343680 : R) * h ^ 2 * t0 ^ 2 * u1 * a0 * w1
    - (49478023249920 : R) * h ^ 2 * t0 ^ 2 * a4 * a0 * s1
    - (49478023249920 : R) * h ^ 2 * t0 ^ 2 * a3 * a1 * s1
    - (24739011624960 : R) * h ^ 2 * t0 ^ 2 * a2 ^ 2 * s1
    - (2061584302080 : R) * h ^ 2 * t0 * v1 ^ 3 * b1
    + (131425999257600 : R) * h ^ 2 * t0 * v1 ^ 2 * u1 * a0
    - (43293270343680 : R) * h ^ 2 * t0 * v1 ^ 2 * a0 * w1
    - (98956046499840 : R) * h ^ 2 * t0 * v1 * u1 * a0 * s1
    + (5497558138880 : R) * h ^ 2 * t0 * v1 * a4 * b1
    + (10995116277760 : R) * h ^ 2 * t0 * v1 * a3 * b2
    + (16492674416640 : R) * h ^ 2 * t0 * v1 * a2 * b3
    + (21990232555520 : R) * h ^ 2 * t0 * v1 * a1 * b4
    + (27487790694400 : R) * h ^ 2 * t0 * v1 * a0 * b5
    + (2748779069440 : R) * h ^ 2 * t0 * u1 ^ 2 * b1
    - (61847529062400 : R) * h ^ 2 * t0 * u1 * a4 * a0
    - (61847529062400 : R) * h ^ 2 * t0 * u1 * a3 * a1
    - (30923764531200 : R) * h ^ 2 * t0 * u1 * a2 ^ 2
    + (32985348833280 : R) * h ^ 2 * t0 * u1 * a0 * b62
    + (38482906972160 : R) * h ^ 2 * t0 * a4 * a0 * w1
    + (38482906972160 : R) * h ^ 2 * t0 * a3 * a1 * w1
    + (19241453486080 : R) * h ^ 2 * t0 * a2 ^ 2 * w1
    + (16750372454400 : R) * h ^ 2 * v1 ^ 4 * a0
    - (16492674416640 : R) * h ^ 2 * v1 ^ 3 * a0 * s1
    + (2748779069440 : R) * h ^ 2 * v1 ^ 2 * u1 * b1
    - (61847529062400 : R) * h ^ 2 * v1 ^ 2 * a4 * a0
    - (61847529062400 : R) * h ^ 2 * v1 ^ 2 * a3 * a1
    - (30923764531200 : R) * h ^ 2 * v1 ^ 2 * a2 ^ 2
    + (16492674416640 : R) * h ^ 2 * v1 ^ 2 * a0 * b62
    - (61847529062400 : R) * h ^ 2 * v1 * u1 ^ 2 * a0
    + (38482906972160 : R) * h ^ 2 * v1 * u1 * a0 * w1
    + (43980465111040 : R) * h ^ 2 * v1 * a4 * a0 * s1
    + (43980465111040 : R) * h ^ 2 * v1 * a3 * a1 * s1
    + (21990232555520 : R) * h ^ 2 * v1 * a2 ^ 2 * s1
    + (21990232555520 : R) * h ^ 2 * u1 ^ 2 * a0 * s1
    - (4398046511104 : R) * h ^ 2 * u1 * a4 * b1
    - (8796093022208 : R) * h ^ 2 * u1 * a3 * b2
    - (13194139533312 : R) * h ^ 2 * u1 * a2 * b3
    - (17592186044416 : R) * h ^ 2 * u1 * a1 * b4
    - (21990232555520 : R) * h ^ 2 * u1 * a0 * b5
    + (27487790694400 : R) * h ^ 2 * a4 ^ 2 * a0
    + (54975581388800 : R) * h ^ 2 * a4 * a3 * a1
    + (27487790694400 : R) * h ^ 2 * a4 * a2 ^ 2
    - (26388279066624 : R) * h ^ 2 * a4 * a0 * b62
    + (27487790694400 : R) * h ^ 2 * a3 ^ 2 * a2
    - (26388279066624 : R) * h ^ 2 * a3 * a1 * b62
    - (13194139533312 : R) * h ^ 2 * a2 ^ 2 * b62
    - (2268109209600 : R) * h * t0 ^ 8 * a1 * lambda
    + (17519188377600 : R) * h * t0 ^ 6 * v1 * a1 * lambda
    - (16818420842496 : R) * h * t0 ^ 5 * u1 * a1 * lambda
    - (42046052106240 : R) * h * t0 ^ 4 * v1 ^ 2 * a1 * lambda
    + (16017543659520 : R) * h * t0 ^ 4 * a4 * a1 * lambda
    + (16017543659520 : R) * h * t0 ^ 4 * a3 * a2 * lambda
    + (64070174638080 : R) * h * t0 ^ 3 * v1 * u1 * a1 * lambda
    + (32035087319040 : R) * h * t0 ^ 2 * v1 ^ 3 * a1 * lambda
    - (45226005626880 : R) * h * t0 ^ 2 * v1 * a4 * a1 * lambda
    - (45226005626880 : R) * h * t0 ^ 2 * v1 * a3 * a2 * lambda
    - (22613002813440 : R) * h * t0 ^ 2 * u1 ^ 2 * a1 * lambda
    - (45226005626880 : R) * h * t0 * v1 ^ 2 * u1 * a1 * lambda
    + (27831388078080 : R) * h * t0 * u1 * a4 * a1 * lambda
    + (27831388078080 : R) * h * t0 * u1 * a3 * a2 * lambda
    - (3768833802240 : R) * h * v1 ^ 4 * a1 * lambda
    + (13915694039040 : R) * h * v1 ^ 2 * a4 * a1 * lambda
    + (13915694039040 : R) * h * v1 ^ 2 * a3 * a2 * lambda
    + (13915694039040 : R) * h * v1 * u1 ^ 2 * a1 * lambda
    - (6184752906240 : R) * h * a4 ^ 2 * a1 * lambda
    - (12369505812480 : R) * h * a4 * a3 * a2 * lambda
    - (2061584302080 : R) * h * a3 ^ 3 * lambda
    + (2100101120000 : R) * t0 ^ 9 * a1
    - (278082355200 : R) * t0 ^ 8 * b2
    - (6952058880000 : R) * t0 ^ 7 * v1 * a1
    - (8898635366400 : R) * t0 ^ 7 * a1 * s1
    + (2491617902592 : R) * t0 ^ 6 * v1 * b2
    + (6229044756480 : R) * t0 ^ 6 * u1 * a1
    + (8720662659072 : R) * t0 ^ 6 * a1 * w1
    - (23358917836800 : R) * t0 ^ 5 * v1 ^ 2 * a1
    + (59798829662208 : R) * t0 ^ 5 * v1 * a1 * s1
    - (2847563317248 : R) * t0 ^ 5 * u1 * b2
    - (5339181219840 : R) * t0 ^ 5 * a4 * a1
    - (5339181219840 : R) * t0 ^ 5 * a3 * a2
    - (8542689951744 : R) * t0 ^ 5 * a1 * b62
    - (7118908293120 : R) * t0 ^ 4 * v1 ^ 2 * b2
    + (53391812198400 : R) * t0 ^ 4 * v1 * u1 * a1
    - (49832358051840 : R) * t0 ^ 4 * v1 * a1 * w1
    - (56951266344960 : R) * t0 ^ 4 * u1 * a1 * s1
    + (3350074490880 : R) * t0 ^ 4 * a4 * b2
    + (5025111736320 : R) * t0 ^ 4 * a3 * b3
    + (6700148981760 : R) * t0 ^ 4 * a2 * b4
    + (8375186227200 : R) * t0 ^ 4 * a1 * b5
    + (88986353664000 : R) * t0 ^ 3 * v1 ^ 3 * a1
    - (113902532689920 : R) * t0 ^ 3 * v1 ^ 2 * a1 * s1
    + (13400297963520 : R) * t0 ^ 3 * v1 * u1 * b2
    - (58626303590400 : R) * t0 ^ 3 * v1 * a4 * a1
    - (58626303590400 : R) * t0 ^ 3 * v1 * a3 * a2
    + (40200893890560 : R) * t0 ^ 3 * v1 * a1 * b62
    - (29313151795200 : R) * t0 ^ 3 * u1 ^ 2 * a1
    + (46901042872320 : R) * t0 ^ 3 * u1 * a1 * w1
    + (53601191854080 : R) * t0 ^ 3 * a4 * a1 * s1
    + (53601191854080 : R) * t0 ^ 3 * a3 * a2 * s1
    + (6700148981760 : R) * t0 ^ 2 * v1 ^ 3 * b2
    - (201004469452800 : R) * t0 ^ 2 * v1 ^ 2 * u1 * a1
    + (70351564308480 : R) * t0 ^ 2 * v1 ^ 2 * a1 * w1
    + (160803575562240 : R) * t0 ^ 2 * v1 * u1 * a1 * s1
    - (12369505812480 : R) * t0 ^ 2 * v1 * a4 * b2
    - (18554258718720 : R) * t0 ^ 2 * v1 * a3 * b3
    - (24739011624960 : R) * t0 ^ 2 * v1 * a2 * b4
    - (30923764531200 : R) * t0 ^ 2 * v1 * a1 * b5
    - (6184752906240 : R) * t0 ^ 2 * u1 ^ 2 * b2
    + (61847529062400 : R) * t0 ^ 2 * u1 * a4 * a1
    + (61847529062400 : R) * t0 ^ 2 * u1 * a3 * a2
    - (37108517437440 : R) * t0 ^ 2 * u1 * a1 * b62
    - (43293270343680 : R) * t0 ^ 2 * a4 * a1 * w1
    - (43293270343680 : R) * t0 ^ 2 * a3 * a2 * w1
    - (52344913920000 : R) * t0 * v1 ^ 4 * a1
    + (53601191854080 : R) * t0 * v1 ^ 3 * a1 * s1
    - (12369505812480 : R) * t0 * v1 ^ 2 * u1 * b2
    + (131425999257600 : R) * t0 * v1 ^ 2 * a4 * a1
    + (131425999257600 : R) * t0 * v1 ^ 2 * a3 * a2
    - (37108517437440 : R) * t0 * v1 ^ 2 * a1 * b62
    + (131425999257600 : R) * t0 * v1 * u1 ^ 2 * a1
    - (86586540687360 : R) * t0 * v1 * u1 * a1 * w1
    - (98956046499840 : R) * t0 * v1 * a4 * a1 * s1
    - (98956046499840 : R) * t0 * v1 * a3 * a2 * s1
    - (49478023249920 : R) * t0 * u1 ^ 2 * a1 * s1
    + (10995116277760 : R) * t0 * u1 * a4 * b2
    + (16492674416640 : R) * t0 * u1 * a3 * b3
    + (21990232555520 : R) * t0 * u1 * a2 * b4
    + (27487790694400 : R) * t0 * u1 * a1 * b5
    - (30923764531200 : R) * t0 * a4 ^ 2 * a1
    - (61847529062400 : R) * t0 * a4 * a3 * a2
    + (32985348833280 : R) * t0 * a4 * a1 * b62
    - (10307921510400 : R) * t0 * a3 ^ 3
    + (32985348833280 : R) * t0 * a3 * a2 * b62
    - (1030792151040 : R) * v1 ^ 4 * b2
    + (67001489817600 : R) * v1 ^ 3 * u1 * a1
    - (14431090114560 : R) * v1 ^ 3 * a1 * w1
    - (49478023249920 : R) * v1 ^ 2 * u1 * a1 * s1
    + (5497558138880 : R) * v1 ^ 2 * a4 * b2
    + (8246337208320 : R) * v1 ^ 2 * a3 * b3
    + (10995116277760 : R) * v1 ^ 2 * a2 * b4
    + (13743895347200 : R) * v1 ^ 2 * a1 * b5
    + (5497558138880 : R) * v1 * u1 ^ 2 * b2
    - (123695058124800 : R) * v1 * u1 * a4 * a1
    - (123695058124800 : R) * v1 * u1 * a3 * a2
    + (32985348833280 : R) * v1 * u1 * a1 * b62
    + (38482906972160 : R) * v1 * a4 * a1 * w1
    + (38482906972160 : R) * v1 * a3 * a2 * w1
    - (20615843020800 : R) * u1 ^ 3 * a1
    + (19241453486080 : R) * u1 ^ 2 * a1 * w1
    + (43980465111040 : R) * u1 * a4 * a1 * s1
    + (43980465111040 : R) * u1 * a3 * a2 * s1
    - (4398046511104 : R) * a4 ^ 2 * b2
    - (13194139533312 : R) * a4 * a3 * b3
    - (17592186044416 : R) * a4 * a2 * b4
    - (21990232555520 : R) * a4 * a1 * b5
    - (8796093022208 : R) * a3 ^ 2 * b4
    - (21990232555520 : R) * a3 * a2 * b5

set_option maxHeartbeats 1600000000 in
theorem piLeftUnsolvedOrder100Plus810_of_order101
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    piLeftUnsolvedOrder100Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda =
      piLeftUnsolvedOrder101810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
          b5 b4 b3 b2 b1 lambda +
        h * piLeftUnsolvedOrder101Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
          s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  simp only [piLeftUnsolvedOrder100Plus810, piLeftUnsolvedOrder101810,
    piLeftUnsolvedOrder101Plus810]
  ring

set_option maxHeartbeats 400000000 in
theorem piLeftUnsolvedOrder100Plus810_zero
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    piLeftUnsolvedOrder100Plus810 0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda =
      piLeftUnsolvedOrder101810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda := by
  rw [piLeftUnsolvedOrder100Plus810_of_order101]
  simp only [zero_mul, add_zero]

set_option maxHeartbeats 800000000 in
theorem piLeftUnsolvedTail810_of_order101
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    piLeftUnsolvedTail810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda =
      piLeftUnsolvedOrder97810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
          b5 b4 b3 b2 b1 lambda +
        h * piLeftUnsolvedOrder98810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
          b62 b5 b4 b3 b2 b1 lambda +
        h ^ 2 * piLeftUnsolvedOrder99810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 3 * piLeftUnsolvedOrder100810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 4 * piLeftUnsolvedOrder101810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 5 * piLeftUnsolvedOrder101Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
          s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  rw [piLeftUnsolvedTail810_of_order100, piLeftUnsolvedOrder100Plus810_of_order101]
  ring

/-- Order-`101` mixin on `t0 = u1 = 0`. -/
def piLeftUnsolvedOrder101810_t0u1Zero
    (v1 : R) : R :=
    0

set_option maxHeartbeats 800000000 in
theorem piLeftUnsolvedOrder101810_of_t0u1Zero
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) (ht0 : t0 = 0) (hu1 : u1 = 0) :
    piLeftUnsolvedOrder101810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda =
      piLeftUnsolvedOrder101810_t0u1Zero v1 := by
  simp only [piLeftUnsolvedOrder101810,
    piLeftUnsolvedOrder101810_t0u1Zero, ht0, hu1]
  ring

/-- Integer `5`-clearing of the LEFT order-`101` mixin after
the four scalar relations.  Witnesses `m1, τ1, g1, k1` are not
inserted. -/
def piLeftUnsolvedLeftOrder101810 (t0 v1 u1 a3 a2 b62 lambda : R) : R :=
    (11558202900480 : R) * t0 ^ 9 * a2 * lambda
    - (103166163025920 : R) * t0 ^ 7 * v1 * a2 * lambda
    + (112186223493120 : R) * t0 ^ 6 * u1 * a2 * lambda
    + (307273201090560 : R) * t0 ^ 5 * v1 ^ 2 * a2 * lambda
    - (42997320253440 : R) * t0 ^ 5 * a3 ^ 2 * lambda
    - (68795712405504 : R) * t0 ^ 5 * a2 * b62 * lambda
    - (526911956582400 : R) * t0 ^ 4 * v1 * u1 * a2 * lambda
    - (343181308723200 : R) * t0 ^ 3 * v1 ^ 3 * a2 * lambda
    + (166698418176000 : R) * t0 ^ 3 * v1 * a3 ^ 2 * lambda
    + (266717469081600 : R) * t0 ^ 3 * v1 * a2 * b62 * lambda
    + (221056598016000 : R) * t0 ^ 3 * u1 ^ 2 * a2 * lambda
    + (582719687884800 : R) * t0 ^ 2 * v1 ^ 2 * u1 * a2 * lambda
    - (130459631616000 : R) * t0 ^ 2 * u1 * a3 ^ 2 * lambda
    - (208735410585600 : R) * t0 ^ 2 * u1 * a2 * b62 * lambda
    + (109441135411200 : R) * t0 * v1 ^ 4 * a2 * lambda
    - (121762322841600 : R) * t0 * v1 ^ 2 * a3 ^ 2 * lambda
    - (194819716546560 : R) * t0 * v1 ^ 2 * a2 * b62 * lambda
    - (260919263232000 : R) * t0 * v1 * u1 ^ 2 * a2 * lambda
    + (55662776156160 : R) * t0 * a3 ^ 2 * b62 * lambda
    + (44530220924928 : R) * t0 * a2 * b62 ^ 2 * lambda
    - (92771293593600 : R) * v1 ^ 3 * u1 * a2 * lambda
    + (69578470195200 : R) * v1 * u1 * a3 ^ 2 * lambda
    + (111325552312320 : R) * v1 * u1 * a2 * b62 * lambda
    + (23192823398400 : R) * u1 ^ 3 * a2 * lambda

/-- Integer `1`-clearing of the RIGHT/`u1 = 0` order-`101`
mixin after the four scalar relations. -/
def piLeftUnsolvedRightU1ZeroOrder101810 (v1 b62 : R) : R :=
    0

/-- Frozen order-`101` mixin on the RIGHT complement scalar locus. -/
def piLeftUnsolvedRightComplementOrder101810
    (v1 u1 a3 a2 lambda : R) : R :=
    - (4638564679680 : R) * v1 ^ 3 * u1 * a2 * lambda
    + (13915694039040 : R) * v1 * u1 * a3 ^ 2 * lambda
    + (4638564679680 : R) * u1 ^ 3 * a2 * lambda

/-- Cofactor of `2 u1² + v1³` in the cleared complement mixin. -/
def piLeftUnsolvedRightComplementOrder101U1Cofactor810
    (v1 u1 a3 a2 lambda : R) : R :=
    (9277129359360 : R) * u1 * a2 * lambda

set_option maxHeartbeats 400000000 in
/-- Fifteenth-face extra `2 u1² + v1³ = 0` specializes the complement
order-`101` mixin. -/
theorem piLeftUnsolvedRightComplementOrder101810_u1rel
    (v1 u1 a3 a2 lambda : R) :
    (4 : R) * piLeftUnsolvedRightComplementOrder101810 v1 u1 a3 a2 lambda =
      ((2 : R) * u1 ^ 2 + v1 ^ 3) *
          piLeftUnsolvedRightComplementOrder101U1Cofactor810
            v1 u1 a3 a2 lambda +
        - (27831388078080 : R) * v1 ^ 3 * u1 * a2 * lambda
        + (55662776156160 : R) * v1 * u1 * a3 ^ 2 * lambda := by
  simp only [piLeftUnsolvedRightComplementOrder101810,
    piLeftUnsolvedRightComplementOrder101U1Cofactor810]
  ring

end PiOrder101Frozen810

section PiOrder101Map810

variable {R S : Type*} [CommRing R] [CommRing S]

set_option maxHeartbeats 800000000 in
theorem map_piLeftUnsolvedOrder101810 (phi : R →+* S)
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    phi (piLeftUnsolvedOrder101810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda) =
      piLeftUnsolvedOrder101810 (phi t0) (phi v1) (phi u1) (phi a4)
        (phi a3) (phi a2) (phi a1) (phi a0) (phi s1) (phi w1)
        (phi b62) (phi b5) (phi b4) (phi b3) (phi b2) (phi b1)
        (phi lambda) := by
  simp only [piLeftUnsolvedOrder101810, map_add, map_sub, map_mul,
    map_pow, map_neg, map_ofNat, map_zero]

#print axioms map_piLeftUnsolvedOrder101810

end PiOrder101Map810

section PiOrder101Eval810

variable {k : Type*} [CommRing k]

theorem piLeftUnsolvedOrder101810_eval
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 : k[X])
    (lambda a : k) :
    (piLeftUnsolvedOrder101810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a =
      piLeftUnsolvedOrder101810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda := by
  simpa [Polynomial.eval_C] using
    map_piLeftUnsolvedOrder101810 (Polynomial.evalRingHom a) t0 v1 u1 a4
      a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)

#print axioms piLeftUnsolvedOrder101810_eval

end PiOrder101Eval810
section PiOrder101Source810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 800000000 in
/-- Remaining power vanishing after the unsolved order-`100` residual is
peeled.  Witnesses stay unsolved.  The `h0`-divisibilities are the
shape the ceiling lemma consumes. -/
theorem piLeftUnsolvedOrder101810_zero_of_power
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 : k[X])
    (lambda eta a : k) (hh : h ≠ 0) (hdegree : h.natDegree = 1)
    (hroot : h.eval a = 0)
    (hpower :
      localClearedSixteenthDefect810
          h (h ^ 6 * t0) (h ^ 4 * v1) (h ^ 2 * u1)
          a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1)
          (h ^ 2 * b62) b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 112) :
    ∃ (o96n o97n o98n o99n o100n : k[X]),
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
        o98n +
            piLeftUnsolvedOrder99810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o99n ∧
        o99n +
            piLeftUnsolvedOrder100810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o100n ∧
        o100n.eval a +
            piLeftUnsolvedOrder101810 (t0.eval a) (v1.eval a)
              (u1.eval a) (a4.eval a) (a3.eval a) (a2.eval a)
              (a1.eval a) (a0.eval a) (s1.eval a) (w1.eval a)
              (b62.eval a) (b5.eval a) (b4.eval a) (b3.eval a)
              (b2.eval a) (b1.eval a) lambda = 0 := by
  obtain ⟨o96n, o97n, o98n, o99n, ho, ho97, ho98, ho99, hmix⟩ :=
    piLeftUnsolvedOrder100810_zero_of_power h t0 v1 u1 a4 a3 a2 a1 a0 s1
      w1 b62 b5 b4 b3 b2 b1 lambda eta a hh hdegree hroot hpower
  have hsum0 :
      (o99n +
          piLeftUnsolvedOrder100810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a = 0 := by
    rw [Polynomial.eval_add, piLeftUnsolvedOrder100810_eval]
    exact hmix
  obtain ⟨o100n, ho100⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h
      (o99n +
        piLeftUnsolvedOrder100810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda))
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
  have hplus12 :
      o99n +
          piLeftUnsolvedOrder99Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 12 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o99n +
            piLeftUnsolvedOrder99Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o98n +
            piLeftUnsolvedOrder99810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder99Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho99]
        ring
      _ = o98n +
            piLeftUnsolvedOrder98Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedOrder98Plus810_of_order99]
        ring
      _ = Polynomial.C eta * h ^ 13 := hplus13
      _ = h * (Polynomial.C eta * h ^ 12) := by ring
  have hplus11 :
      o100n +
          piLeftUnsolvedOrder100Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 11 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o100n +
            piLeftUnsolvedOrder100Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o99n +
            piLeftUnsolvedOrder100810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder100Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho100]
        ring
      _ = o99n +
            piLeftUnsolvedOrder99Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedOrder99Plus810_of_order100]
        ring
      _ = Polynomial.C eta * h ^ 12 := hplus12
      _ = h * (Polynomial.C eta * h ^ 11) := by ring
  have htail :
      (piLeftUnsolvedOrder100Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
          b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a =
        (piLeftUnsolvedOrder101810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
          b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a := by
    rw [piLeftUnsolvedOrder100Plus810_of_order101]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, hroot,
      zero_mul, add_zero]
  refine ⟨o96n, o97n, o98n, o99n, o100n, ho, ho97, ho98, ho99, ho100, ?_⟩
  have hev := congrArg (Polynomial.eval a) hplus11
  rw [← piLeftUnsolvedOrder101810_eval, ← htail]
  simpa [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, hroot] using hev

set_option maxHeartbeats 800000000 in
/-- Source-facing order-`101` peel from a literal `(8,10)` source. -/
theorem piLeftUnsolvedOrder101810_zero_of_source
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
    ∃ (o96n o97n o98n o99n o100n : k[X]),
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
        o98n +
            piLeftUnsolvedOrder99810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o99n ∧
        o99n +
            piLeftUnsolvedOrder100810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o100n ∧
        o100n.eval a +
            piLeftUnsolvedOrder101810 (t0.eval a) (v1.eval a)
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
  exact piLeftUnsolvedOrder101810_zero_of_power h0 t0 v1 u1
    (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1
    b62 (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
    lambda (17592186044416 * eta) a hh0 hdegree hroot hpower

set_option maxHeartbeats 800000000 in
/-- Source-facing order-`101` chambers.  Witnesses stay unsolved.  The
fifteenth-face extras are carried from the parent.  This is not a
closure. -/
theorem piFace810_linearRoot_order101Chambers
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
    ∃ (t0 v0 u0 s0 w0 v1 s1 u1 w1 b62 o96n o97n o98n o99n o100n : k[X]),
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
        o98n +
            piLeftUnsolvedOrder99810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o99n ∧
        o99n +
            piLeftUnsolvedOrder100810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o100n ∧
        o100n.eval a +
            piLeftUnsolvedOrder101810 (t0.eval a) (v1.eval a)
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
  obtain ⟨t0, v0, u0, s0, w0, v1, s1, u1, w1, b62, o96n, o97n, o98n, o99n, ht0, hv0, hu0, hs0, hw0, hv1, hs1, hu1, hw1, hb62, ho96, ho97, ho98, ho99, hmix100, hsplit⟩ :=
    piFace810_linearRoot_order100Chambers p q H h0 j lambda a hp hq
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
  obtain ⟨o96n', o97n', o98n', o99n', o100n, ho', ho97', ho98', ho99', ho100, hmix101⟩ :=
    piLeftUnsolvedOrder101810_zero_of_source p q H h0 j lambda a t0 v1
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
  have ho98eq : o98n = o98n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o98n = o97n +
          piLeftUnsolvedOrder98810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) := ho98.symm
      _ = h0 * o98n' := ho98'
  subst ho98eq
  have ho99eq : o99n = o99n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o99n = o98n +
          piLeftUnsolvedOrder99810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) := ho99.symm
      _ = h0 * o99n' := ho99'
  subst ho99eq
  refine ⟨t0, v0, u0, s0, w0, v1, s1, u1, w1, b62, o96n, o97n, o98n, o99n, o100n,
    ht0, hv0, hu0, hs0, hw0, hv1, hs1, hu1, hw1, hb62, ho96, ho97, ho98, ho99, ho100, hmix101, ?_⟩
  exact hsplit

#print axioms piLeftUnsolvedOrder100Plus810_of_order101
#print axioms piLeftUnsolvedOrder101810_of_t0u1Zero
#print axioms piLeftUnsolvedOrder101810_zero_of_power
#print axioms piLeftUnsolvedOrder101810_zero_of_source
#print axioms piFace810_linearRoot_order101Chambers
#print axioms piLeftUnsolvedRightComplementOrder101810_u1rel

end PiOrder101Source810
section PiOrder102Frozen810

variable {R : Type*} [CommRing R]

set_option maxHeartbeats 1600000000 in
/-- Frozen order-`102` mixin: the `h⁰` coefficient of the order-`101` Plus
remainder, equivalently the `h^5` coefficient of the unsolved tail
and the `h^6` coefficient of the factored residual after the
order-`96` head. -/
def piLeftUnsolvedOrder102810 (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (2100101120000 : R) * t0 ^ 9 * a1
    - (278082355200 : R) * t0 ^ 8 * b2
    - (6952058880000 : R) * t0 ^ 7 * v1 * a1
    - (8898635366400 : R) * t0 ^ 7 * a1 * s1
    + (2491617902592 : R) * t0 ^ 6 * v1 * b2
    + (6229044756480 : R) * t0 ^ 6 * u1 * a1
    + (8720662659072 : R) * t0 ^ 6 * a1 * w1
    - (23358917836800 : R) * t0 ^ 5 * v1 ^ 2 * a1
    + (59798829662208 : R) * t0 ^ 5 * v1 * a1 * s1
    - (2847563317248 : R) * t0 ^ 5 * u1 * b2
    - (5339181219840 : R) * t0 ^ 5 * a4 * a1
    - (5339181219840 : R) * t0 ^ 5 * a3 * a2
    - (8542689951744 : R) * t0 ^ 5 * a1 * b62
    - (7118908293120 : R) * t0 ^ 4 * v1 ^ 2 * b2
    + (53391812198400 : R) * t0 ^ 4 * v1 * u1 * a1
    - (49832358051840 : R) * t0 ^ 4 * v1 * a1 * w1
    - (56951266344960 : R) * t0 ^ 4 * u1 * a1 * s1
    + (3350074490880 : R) * t0 ^ 4 * a4 * b2
    + (5025111736320 : R) * t0 ^ 4 * a3 * b3
    + (6700148981760 : R) * t0 ^ 4 * a2 * b4
    + (8375186227200 : R) * t0 ^ 4 * a1 * b5
    + (88986353664000 : R) * t0 ^ 3 * v1 ^ 3 * a1
    - (113902532689920 : R) * t0 ^ 3 * v1 ^ 2 * a1 * s1
    + (13400297963520 : R) * t0 ^ 3 * v1 * u1 * b2
    - (58626303590400 : R) * t0 ^ 3 * v1 * a4 * a1
    - (58626303590400 : R) * t0 ^ 3 * v1 * a3 * a2
    + (40200893890560 : R) * t0 ^ 3 * v1 * a1 * b62
    - (29313151795200 : R) * t0 ^ 3 * u1 ^ 2 * a1
    + (46901042872320 : R) * t0 ^ 3 * u1 * a1 * w1
    + (53601191854080 : R) * t0 ^ 3 * a4 * a1 * s1
    + (53601191854080 : R) * t0 ^ 3 * a3 * a2 * s1
    + (6700148981760 : R) * t0 ^ 2 * v1 ^ 3 * b2
    - (201004469452800 : R) * t0 ^ 2 * v1 ^ 2 * u1 * a1
    + (70351564308480 : R) * t0 ^ 2 * v1 ^ 2 * a1 * w1
    + (160803575562240 : R) * t0 ^ 2 * v1 * u1 * a1 * s1
    - (12369505812480 : R) * t0 ^ 2 * v1 * a4 * b2
    - (18554258718720 : R) * t0 ^ 2 * v1 * a3 * b3
    - (24739011624960 : R) * t0 ^ 2 * v1 * a2 * b4
    - (30923764531200 : R) * t0 ^ 2 * v1 * a1 * b5
    - (6184752906240 : R) * t0 ^ 2 * u1 ^ 2 * b2
    + (61847529062400 : R) * t0 ^ 2 * u1 * a4 * a1
    + (61847529062400 : R) * t0 ^ 2 * u1 * a3 * a2
    - (37108517437440 : R) * t0 ^ 2 * u1 * a1 * b62
    - (43293270343680 : R) * t0 ^ 2 * a4 * a1 * w1
    - (43293270343680 : R) * t0 ^ 2 * a3 * a2 * w1
    - (52344913920000 : R) * t0 * v1 ^ 4 * a1
    + (53601191854080 : R) * t0 * v1 ^ 3 * a1 * s1
    - (12369505812480 : R) * t0 * v1 ^ 2 * u1 * b2
    + (131425999257600 : R) * t0 * v1 ^ 2 * a4 * a1
    + (131425999257600 : R) * t0 * v1 ^ 2 * a3 * a2
    - (37108517437440 : R) * t0 * v1 ^ 2 * a1 * b62
    + (131425999257600 : R) * t0 * v1 * u1 ^ 2 * a1
    - (86586540687360 : R) * t0 * v1 * u1 * a1 * w1
    - (98956046499840 : R) * t0 * v1 * a4 * a1 * s1
    - (98956046499840 : R) * t0 * v1 * a3 * a2 * s1
    - (49478023249920 : R) * t0 * u1 ^ 2 * a1 * s1
    + (10995116277760 : R) * t0 * u1 * a4 * b2
    + (16492674416640 : R) * t0 * u1 * a3 * b3
    + (21990232555520 : R) * t0 * u1 * a2 * b4
    + (27487790694400 : R) * t0 * u1 * a1 * b5
    - (30923764531200 : R) * t0 * a4 ^ 2 * a1
    - (61847529062400 : R) * t0 * a4 * a3 * a2
    + (32985348833280 : R) * t0 * a4 * a1 * b62
    - (10307921510400 : R) * t0 * a3 ^ 3
    + (32985348833280 : R) * t0 * a3 * a2 * b62
    - (1030792151040 : R) * v1 ^ 4 * b2
    + (67001489817600 : R) * v1 ^ 3 * u1 * a1
    - (14431090114560 : R) * v1 ^ 3 * a1 * w1
    - (49478023249920 : R) * v1 ^ 2 * u1 * a1 * s1
    + (5497558138880 : R) * v1 ^ 2 * a4 * b2
    + (8246337208320 : R) * v1 ^ 2 * a3 * b3
    + (10995116277760 : R) * v1 ^ 2 * a2 * b4
    + (13743895347200 : R) * v1 ^ 2 * a1 * b5
    + (5497558138880 : R) * v1 * u1 ^ 2 * b2
    - (123695058124800 : R) * v1 * u1 * a4 * a1
    - (123695058124800 : R) * v1 * u1 * a3 * a2
    + (32985348833280 : R) * v1 * u1 * a1 * b62
    + (38482906972160 : R) * v1 * a4 * a1 * w1
    + (38482906972160 : R) * v1 * a3 * a2 * w1
    - (20615843020800 : R) * u1 ^ 3 * a1
    + (19241453486080 : R) * u1 ^ 2 * a1 * w1
    + (43980465111040 : R) * u1 * a4 * a1 * s1
    + (43980465111040 : R) * u1 * a3 * a2 * s1
    - (4398046511104 : R) * a4 ^ 2 * b2
    - (13194139533312 : R) * a4 * a3 * b3
    - (17592186044416 : R) * a4 * a2 * b4
    - (21990232555520 : R) * a4 * a1 * b5
    - (8796093022208 : R) * a3 ^ 2 * b4
    - (21990232555520 : R) * a3 * a2 * b5

set_option maxHeartbeats 1600000000 in
/-- Remaining factor after `h` is removed from the order-`101` Plus
remainder. -/
def piLeftUnsolvedOrder102Plus810 (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (21990232555520 : R) * h ^ 9 * a0 ^ 2
    + (9895604649984 : R) * h ^ 8 * a1 * a0 * lambda
    + (5497558138880 : R) * h ^ 7 * t0 * a1 * a0
    + (17592186044416 : R) * h ^ 7 * a1 * b1
    + (35184372088832 : R) * h ^ 7 * a0 * b2
    - (12369505812480 : R) * h ^ 6 * t0 * a2 * a0 * lambda
    - (6184752906240 : R) * h ^ 6 * t0 * a1 ^ 2 * lambda
    - (4398046511104 : R) * h ^ 5 * t0 * a2 * b1
    - (8796093022208 : R) * h ^ 5 * t0 * a1 * b2
    - (13194139533312 : R) * h ^ 5 * t0 * a0 * b3
    + (54975581388800 : R) * h ^ 5 * v1 * a2 * a0
    + (27487790694400 : R) * h ^ 5 * v1 * a1 ^ 2
    - (35184372088832 : R) * h ^ 5 * a2 * a0 * s1
    - (17592186044416 : R) * h ^ 5 * a1 ^ 2 * s1
    + (13915694039040 : R) * h ^ 4 * t0 ^ 2 * a3 * a0 * lambda
    + (13915694039040 : R) * h ^ 4 * t0 ^ 2 * a2 * a1 * lambda
    - (12369505812480 : R) * h ^ 4 * v1 * a3 * a0 * lambda
    - (12369505812480 : R) * h ^ 4 * v1 * a2 * a1 * lambda
    - (2576980377600 : R) * h ^ 3 * t0 ^ 3 * a3 * a0
    - (2576980377600 : R) * h ^ 3 * t0 ^ 3 * a2 * a1
    + (2748779069440 : R) * h ^ 3 * t0 ^ 2 * a3 * b1
    + (5497558138880 : R) * h ^ 3 * t0 ^ 2 * a2 * b2
    + (8246337208320 : R) * h ^ 3 * t0 ^ 2 * a1 * b3
    + (10995116277760 : R) * h ^ 3 * t0 ^ 2 * a0 * b4
    - (61847529062400 : R) * h ^ 3 * t0 * v1 * a3 * a0
    - (61847529062400 : R) * h ^ 3 * t0 * v1 * a2 * a1
    + (43980465111040 : R) * h ^ 3 * t0 * a3 * a0 * s1
    + (43980465111040 : R) * h ^ 3 * t0 * a2 * a1 * s1
    - (4398046511104 : R) * h ^ 3 * v1 * a3 * b1
    - (8796093022208 : R) * h ^ 3 * v1 * a2 * b2
    - (13194139533312 : R) * h ^ 3 * v1 * a1 * b3
    - (17592186044416 : R) * h ^ 3 * v1 * a0 * b4
    + (54975581388800 : R) * h ^ 3 * u1 * a3 * a0
    + (54975581388800 : R) * h ^ 3 * u1 * a2 * a1
    - (30786325577728 : R) * h ^ 3 * a3 * a0 * w1
    - (30786325577728 : R) * h ^ 3 * a2 * a1 * w1
    + (2502741196800 : R) * h ^ 2 * t0 ^ 7 * a0 * lambda
    - (16818420842496 : R) * h ^ 2 * t0 ^ 5 * v1 * a0 * lambda
    + (16017543659520 : R) * h ^ 2 * t0 ^ 4 * u1 * a0 * lambda
    + (32035087319040 : R) * h ^ 2 * t0 ^ 3 * v1 ^ 2 * a0 * lambda
    - (15075335208960 : R) * h ^ 2 * t0 ^ 3 * a4 * a0 * lambda
    - (15075335208960 : R) * h ^ 2 * t0 ^ 3 * a3 * a1 * lambda
    - (7537667604480 : R) * h ^ 2 * t0 ^ 3 * a2 ^ 2 * lambda
    - (45226005626880 : R) * h ^ 2 * t0 ^ 2 * v1 * u1 * a0 * lambda
    - (15075335208960 : R) * h ^ 2 * t0 * v1 ^ 3 * a0 * lambda
    + (27831388078080 : R) * h ^ 2 * t0 * v1 * a4 * a0 * lambda
    + (27831388078080 : R) * h ^ 2 * t0 * v1 * a3 * a1 * lambda
    + (13915694039040 : R) * h ^ 2 * t0 * v1 * a2 ^ 2 * lambda
    + (13915694039040 : R) * h ^ 2 * t0 * u1 ^ 2 * a0 * lambda
    + (13915694039040 : R) * h ^ 2 * v1 ^ 2 * u1 * a0 * lambda
    - (12369505812480 : R) * h ^ 2 * u1 * a4 * a0 * lambda
    - (12369505812480 : R) * h ^ 2 * u1 * a3 * a1 * lambda
    - (6184752906240 : R) * h ^ 2 * u1 * a2 ^ 2 * lambda
    - (2433220608000 : R) * h * t0 ^ 8 * a0
    + (177972707328 : R) * h * t0 ^ 7 * b1
    + (6229044756480 : R) * h * t0 ^ 6 * v1 * a0
    + (9966471610368 : R) * h * t0 ^ 6 * a0 * s1
    - (1423781658624 : R) * h * t0 ^ 5 * v1 * b1
    - (5339181219840 : R) * h * t0 ^ 5 * u1 * a0
    - (9966471610368 : R) * h * t0 ^ 5 * a0 * w1
    + (26695906099200 : R) * h * t0 ^ 4 * v1 ^ 2 * a0
    - (56951266344960 : R) * h * t0 ^ 4 * v1 * a0 * s1
    + (1675037245440 : R) * h * t0 ^ 4 * u1 * b1
    + (4187593113600 : R) * h * t0 ^ 4 * a4 * a0
    + (4187593113600 : R) * h * t0 ^ 4 * a3 * a1
    + (2093796556800 : R) * h * t0 ^ 4 * a2 ^ 2
    + (10050223472640 : R) * h * t0 ^ 4 * a0 * b62
    + (3350074490880 : R) * h * t0 ^ 3 * v1 ^ 2 * b1
    - (58626303590400 : R) * h * t0 ^ 3 * v1 * u1 * a0
    + (46901042872320 : R) * h * t0 ^ 3 * v1 * a0 * w1
    + (53601191854080 : R) * h * t0 ^ 3 * u1 * a0 * s1
    - (2061584302080 : R) * h * t0 ^ 3 * a4 * b1
    - (4123168604160 : R) * h * t0 ^ 3 * a3 * b2
    - (6184752906240 : R) * h * t0 ^ 3 * a2 * b3
    - (8246337208320 : R) * h * t0 ^ 3 * a1 * b4
    - (10307921510400 : R) * h * t0 ^ 3 * a0 * b5
    - (67001489817600 : R) * h * t0 ^ 2 * v1 ^ 3 * a0
    + (80401787781120 : R) * h * t0 ^ 2 * v1 ^ 2 * a0 * s1
    - (6184752906240 : R) * h * t0 ^ 2 * v1 * u1 * b1
    + (61847529062400 : R) * h * t0 ^ 2 * v1 * a4 * a0
    + (61847529062400 : R) * h * t0 ^ 2 * v1 * a3 * a1
    + (30923764531200 : R) * h * t0 ^ 2 * v1 * a2 ^ 2
    - (37108517437440 : R) * h * t0 ^ 2 * v1 * a0 * b62
    + (30923764531200 : R) * h * t0 ^ 2 * u1 ^ 2 * a0
    - (43293270343680 : R) * h * t0 ^ 2 * u1 * a0 * w1
    - (49478023249920 : R) * h * t0 ^ 2 * a4 * a0 * s1
    - (49478023249920 : R) * h * t0 ^ 2 * a3 * a1 * s1
    - (24739011624960 : R) * h * t0 ^ 2 * a2 ^ 2 * s1
    - (2061584302080 : R) * h * t0 * v1 ^ 3 * b1
    + (131425999257600 : R) * h * t0 * v1 ^ 2 * u1 * a0
    - (43293270343680 : R) * h * t0 * v1 ^ 2 * a0 * w1
    - (98956046499840 : R) * h * t0 * v1 * u1 * a0 * s1
    + (5497558138880 : R) * h * t0 * v1 * a4 * b1
    + (10995116277760 : R) * h * t0 * v1 * a3 * b2
    + (16492674416640 : R) * h * t0 * v1 * a2 * b3
    + (21990232555520 : R) * h * t0 * v1 * a1 * b4
    + (27487790694400 : R) * h * t0 * v1 * a0 * b5
    + (2748779069440 : R) * h * t0 * u1 ^ 2 * b1
    - (61847529062400 : R) * h * t0 * u1 * a4 * a0
    - (61847529062400 : R) * h * t0 * u1 * a3 * a1
    - (30923764531200 : R) * h * t0 * u1 * a2 ^ 2
    + (32985348833280 : R) * h * t0 * u1 * a0 * b62
    + (38482906972160 : R) * h * t0 * a4 * a0 * w1
    + (38482906972160 : R) * h * t0 * a3 * a1 * w1
    + (19241453486080 : R) * h * t0 * a2 ^ 2 * w1
    + (16750372454400 : R) * h * v1 ^ 4 * a0
    - (16492674416640 : R) * h * v1 ^ 3 * a0 * s1
    + (2748779069440 : R) * h * v1 ^ 2 * u1 * b1
    - (61847529062400 : R) * h * v1 ^ 2 * a4 * a0
    - (61847529062400 : R) * h * v1 ^ 2 * a3 * a1
    - (30923764531200 : R) * h * v1 ^ 2 * a2 ^ 2
    + (16492674416640 : R) * h * v1 ^ 2 * a0 * b62
    - (61847529062400 : R) * h * v1 * u1 ^ 2 * a0
    + (38482906972160 : R) * h * v1 * u1 * a0 * w1
    + (43980465111040 : R) * h * v1 * a4 * a0 * s1
    + (43980465111040 : R) * h * v1 * a3 * a1 * s1
    + (21990232555520 : R) * h * v1 * a2 ^ 2 * s1
    + (21990232555520 : R) * h * u1 ^ 2 * a0 * s1
    - (4398046511104 : R) * h * u1 * a4 * b1
    - (8796093022208 : R) * h * u1 * a3 * b2
    - (13194139533312 : R) * h * u1 * a2 * b3
    - (17592186044416 : R) * h * u1 * a1 * b4
    - (21990232555520 : R) * h * u1 * a0 * b5
    + (27487790694400 : R) * h * a4 ^ 2 * a0
    + (54975581388800 : R) * h * a4 * a3 * a1
    + (27487790694400 : R) * h * a4 * a2 ^ 2
    - (26388279066624 : R) * h * a4 * a0 * b62
    + (27487790694400 : R) * h * a3 ^ 2 * a2
    - (26388279066624 : R) * h * a3 * a1 * b62
    - (13194139533312 : R) * h * a2 ^ 2 * b62
    - (2268109209600 : R) * t0 ^ 8 * a1 * lambda
    + (17519188377600 : R) * t0 ^ 6 * v1 * a1 * lambda
    - (16818420842496 : R) * t0 ^ 5 * u1 * a1 * lambda
    - (42046052106240 : R) * t0 ^ 4 * v1 ^ 2 * a1 * lambda
    + (16017543659520 : R) * t0 ^ 4 * a4 * a1 * lambda
    + (16017543659520 : R) * t0 ^ 4 * a3 * a2 * lambda
    + (64070174638080 : R) * t0 ^ 3 * v1 * u1 * a1 * lambda
    + (32035087319040 : R) * t0 ^ 2 * v1 ^ 3 * a1 * lambda
    - (45226005626880 : R) * t0 ^ 2 * v1 * a4 * a1 * lambda
    - (45226005626880 : R) * t0 ^ 2 * v1 * a3 * a2 * lambda
    - (22613002813440 : R) * t0 ^ 2 * u1 ^ 2 * a1 * lambda
    - (45226005626880 : R) * t0 * v1 ^ 2 * u1 * a1 * lambda
    + (27831388078080 : R) * t0 * u1 * a4 * a1 * lambda
    + (27831388078080 : R) * t0 * u1 * a3 * a2 * lambda
    - (3768833802240 : R) * v1 ^ 4 * a1 * lambda
    + (13915694039040 : R) * v1 ^ 2 * a4 * a1 * lambda
    + (13915694039040 : R) * v1 ^ 2 * a3 * a2 * lambda
    + (13915694039040 : R) * v1 * u1 ^ 2 * a1 * lambda
    - (6184752906240 : R) * a4 ^ 2 * a1 * lambda
    - (12369505812480 : R) * a4 * a3 * a2 * lambda
    - (2061584302080 : R) * a3 ^ 3 * lambda

set_option maxHeartbeats 1600000000 in
theorem piLeftUnsolvedOrder101Plus810_of_order102
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    piLeftUnsolvedOrder101Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda =
      piLeftUnsolvedOrder102810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
          b5 b4 b3 b2 b1 lambda +
        h * piLeftUnsolvedOrder102Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
          s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  simp only [piLeftUnsolvedOrder101Plus810, piLeftUnsolvedOrder102810,
    piLeftUnsolvedOrder102Plus810]
  ring

set_option maxHeartbeats 400000000 in
theorem piLeftUnsolvedOrder101Plus810_zero
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    piLeftUnsolvedOrder101Plus810 0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda =
      piLeftUnsolvedOrder102810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda := by
  rw [piLeftUnsolvedOrder101Plus810_of_order102]
  simp only [zero_mul, add_zero]

set_option maxHeartbeats 800000000 in
theorem piLeftUnsolvedTail810_of_order102
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    piLeftUnsolvedTail810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda =
      piLeftUnsolvedOrder97810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
          b5 b4 b3 b2 b1 lambda +
        h * piLeftUnsolvedOrder98810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
          b62 b5 b4 b3 b2 b1 lambda +
        h ^ 2 * piLeftUnsolvedOrder99810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 3 * piLeftUnsolvedOrder100810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 4 * piLeftUnsolvedOrder101810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 5 * piLeftUnsolvedOrder102810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 6 * piLeftUnsolvedOrder102Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
          s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  rw [piLeftUnsolvedTail810_of_order101, piLeftUnsolvedOrder101Plus810_of_order102]
  ring

/-- Order-`102` mixin on `t0 = u1 = 0`. -/
def piLeftUnsolvedOrder102810_t0u1Zero
    (v1 a4 a3 a2 a1 w1 b5 b4 b3 b2 : R) : R :=
    - (1030792151040 : R) * v1 ^ 4 * b2
    - (14431090114560 : R) * v1 ^ 3 * a1 * w1
    + (5497558138880 : R) * v1 ^ 2 * a4 * b2
    + (8246337208320 : R) * v1 ^ 2 * a3 * b3
    + (10995116277760 : R) * v1 ^ 2 * a2 * b4
    + (13743895347200 : R) * v1 ^ 2 * a1 * b5
    + (38482906972160 : R) * v1 * a4 * a1 * w1
    + (38482906972160 : R) * v1 * a3 * a2 * w1
    - (4398046511104 : R) * a4 ^ 2 * b2
    - (13194139533312 : R) * a4 * a3 * b3
    - (17592186044416 : R) * a4 * a2 * b4
    - (21990232555520 : R) * a4 * a1 * b5
    - (8796093022208 : R) * a3 ^ 2 * b4
    - (21990232555520 : R) * a3 * a2 * b5

set_option maxHeartbeats 800000000 in
theorem piLeftUnsolvedOrder102810_of_t0u1Zero
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) (ht0 : t0 = 0) (hu1 : u1 = 0) :
    piLeftUnsolvedOrder102810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda =
      piLeftUnsolvedOrder102810_t0u1Zero v1 a4 a3 a2 a1 w1 b5 b4 b3 b2 := by
  simp only [piLeftUnsolvedOrder102810,
    piLeftUnsolvedOrder102810_t0u1Zero, ht0, hu1]
  ring

/-- Integer `25`-clearing of the LEFT order-`102` mixin after
the four scalar relations.  Witnesses `m1, τ1, g1, k1` are not
inserted. -/
def piLeftUnsolvedLeftOrder102810 (t0 v1 u1 a3 a2 a1 b62 b4 b3 b2 : R) : R :=
    (4500357120000 : R) * t0 ^ 9 * a1
    - (8117655961600 : R) * t0 ^ 8 * b2
    - (48423239680000 : R) * t0 ^ 7 * v1 * a1
    + (74651900313600 : R) * t0 ^ 6 * v1 * b2
    + (66521661440000 : R) * t0 ^ 6 * u1 * a1
    + (178929008640000 : R) * t0 ^ 5 * v1 ^ 2 * a1
    - (96636764160000 : R) * t0 ^ 5 * u1 * b2
    + (146834194432000 : R) * t0 ^ 5 * a3 * a2
    - (53150220288000 : R) * t0 ^ 5 * a1 * b62
    - (220653944832000 : R) * t0 ^ 4 * v1 ^ 2 * b2
    - (397955563520000 : R) * t0 ^ 4 * v1 * u1 * a1
    + (130137509068800 : R) * t0 ^ 4 * a3 * b3
    + (173516678758400 : R) * t0 ^ 4 * a2 * b4
    + (69406671503360 : R) * t0 ^ 4 * b62 * b2
    - (259040215040000 : R) * t0 ^ 3 * v1 ^ 3 * a1
    + (443240624947200 : R) * t0 ^ 3 * v1 * u1 * b2
    - (751619276800000 : R) * t0 ^ 3 * v1 * a3 * a2
    + (274877906944000 : R) * t0 ^ 3 * v1 * a1 * b62
    + (220117073920000 : R) * t0 ^ 3 * u1 ^ 2 * a1
    + (221620312473600 : R) * t0 ^ 2 * v1 ^ 3 * b2
    + (595926712320000 : R) * t0 ^ 2 * v1 ^ 2 * u1 * a1
    - (494780232499200 : R) * t0 ^ 2 * v1 * a3 * b3
    - (659706976665600 : R) * t0 ^ 2 * v1 * a2 * b4
    - (263882790666240 : R) * t0 ^ 2 * v1 * b62 * b2
    - (230210247065600 : R) * t0 ^ 2 * u1 ^ 2 * b2
    + (858993459200000 : R) * t0 ^ 2 * u1 * a3 * a2
    - (240518168576000 : R) * t0 ^ 2 * u1 * a1 * b62
    + (115427246080000 : R) * t0 * v1 ^ 4 * a1
    - (384829069721600 : R) * t0 * v1 ^ 2 * u1 * b2
    + (773094113280000 : R) * t0 * v1 ^ 2 * a3 * a2
    - (309237645312000 : R) * t0 * v1 ^ 2 * a1 * b62
    - (429496729600000 : R) * t0 * v1 * u1 ^ 2 * a1
    + (494780232499200 : R) * t0 * u1 * a3 * b3
    + (659706976665600 : R) * t0 * u1 * a2 * b4
    + (263882790666240 : R) * t0 * u1 * b62 * b2
    - (257698037760000 : R) * t0 * a3 ^ 3
    - (549755813888000 : R) * t0 * a3 * a2 * b62
    + (54975581388800 : R) * t0 * a1 * b62 ^ 2
    - (44667659878400 : R) * v1 ^ 4 * b2
    - (128849018880000 : R) * v1 ^ 3 * u1 * a1
    + (247390116249600 : R) * v1 ^ 2 * a3 * b3
    + (329853488332800 : R) * v1 ^ 2 * a2 * b4
    + (131941395333120 : R) * v1 ^ 2 * b62 * b2
    + (137438953472000 : R) * v1 * u1 ^ 2 * b2
    - (687194767360000 : R) * v1 * u1 * a3 * a2
    + (274877906944000 : R) * v1 * u1 * a1 * b62
    + (85899345920000 : R) * u1 ^ 3 * a1
    - (219902325555200 : R) * a3 ^ 2 * b4
    - (263882790666240 : R) * a3 * b62 * b3
    - (351843720888320 : R) * a2 * b62 * b4
    - (70368744177664 : R) * b62 ^ 2 * b2

/-- Integer `25`-clearing of the RIGHT/`u1 = 0` order-`102`
mixin after the four scalar relations. -/
def piLeftUnsolvedRightU1ZeroOrder102810 (v1 a3 a2 b62 b4 b3 b2 : R) : R :=
    - (44667659878400 : R) * v1 ^ 4 * b2
    + (247390116249600 : R) * v1 ^ 2 * a3 * b3
    + (329853488332800 : R) * v1 ^ 2 * a2 * b4
    + (131941395333120 : R) * v1 ^ 2 * b62 * b2
    - (219902325555200 : R) * a3 ^ 2 * b4
    - (263882790666240 : R) * a3 * b62 * b3
    - (351843720888320 : R) * a2 * b62 * b4
    - (70368744177664 : R) * b62 ^ 2 * b2

/-- Cofactor of `16 b62 - 5 v1²` in the cleared RIGHT/`u1 = 0`
order-`102` mixin. -/
def piLeftUnsolvedRightU1ZeroOrder102B62Cofactor810
    (v1 a3 a2 b62 b4 b3 b2 : R) : R :=
    (1759218604441600 : R) * v1 ^ 2 * b2
    - (4222124650659840 : R) * a3 * b3
    - (5629499534213120 : R) * a2 * b4
    - (1125899906842624 : R) * b62 * b2

set_option maxHeartbeats 400000000 in
/-- Fifteenth-face extra `16 b62 = 5 v1²` specializes the RIGHT/`u1 = 0`
order-`102` mixin. -/
theorem piLeftUnsolvedRightU1ZeroOrder102810_b62Law
    (v1 a3 a2 b62 b4 b3 b2 : R) :
    (256 : R) * piLeftUnsolvedRightU1ZeroOrder102810 v1 a3 a2 b62 b4 b3 b2 =
      ((16 : R) * b62 - (5 : R) * v1 ^ 2) *
          piLeftUnsolvedRightU1ZeroOrder102B62Cofactor810
            v1 a3 a2 b62 b4 b3 b2 +
        - (2638827906662400 : R) * v1 ^ 4 * b2
        + (42221246506598400 : R) * v1 ^ 2 * a3 * b3
        + (56294995342131200 : R) * v1 ^ 2 * a2 * b4
        - (56294995342131200 : R) * a3 ^ 2 * b4 := by
  simp only [piLeftUnsolvedRightU1ZeroOrder102810,
    piLeftUnsolvedRightU1ZeroOrder102B62Cofactor810]
  ring

/-- Frozen order-`102` mixin on the RIGHT complement scalar locus. -/
def piLeftUnsolvedRightComplementOrder102810
    (v1 u1 a3 a2 a1 b4 b3 b2 : R) : R :=
    (412316860416 : R) * v1 ^ 4 * b2
    + (1717986918400 : R) * v1 ^ 3 * u1 * a1
    + (3298534883328 : R) * v1 ^ 2 * a3 * b3
    + (4398046511104 : R) * v1 ^ 2 * a2 * b4
    + (5497558138880 : R) * v1 * u1 ^ 2 * b2
    - (27487790694400 : R) * v1 * u1 * a3 * a2
    + (3435973836800 : R) * u1 ^ 3 * a1
    - (8796093022208 : R) * a3 ^ 2 * b4

/-- Cofactor of `2 u1² + v1³` in the cleared complement mixin. -/
def piLeftUnsolvedRightComplementOrder102U1Cofactor810
    (v1 u1 a3 a2 a1 b4 b3 b2 : R) : R :=
    (10995116277760 : R) * v1 * b2
    + (6871947673600 : R) * u1 * a1

set_option maxHeartbeats 400000000 in
/-- Fifteenth-face extra `2 u1² + v1³ = 0` specializes the complement
order-`102` mixin. -/
theorem piLeftUnsolvedRightComplementOrder102810_u1rel
    (v1 u1 a3 a2 a1 b4 b3 b2 : R) :
    (4 : R) * piLeftUnsolvedRightComplementOrder102810 v1 u1 a3 a2 a1 b4 b3 b2 =
      ((2 : R) * u1 ^ 2 + v1 ^ 3) *
          piLeftUnsolvedRightComplementOrder102U1Cofactor810
            v1 u1 a3 a2 a1 b4 b3 b2 +
        - (9345848836096 : R) * v1 ^ 4 * b2
        + (13194139533312 : R) * v1 ^ 2 * a3 * b3
        + (17592186044416 : R) * v1 ^ 2 * a2 * b4
        - (109951162777600 : R) * v1 * u1 * a3 * a2
        - (35184372088832 : R) * a3 ^ 2 * b4 := by
  simp only [piLeftUnsolvedRightComplementOrder102810,
    piLeftUnsolvedRightComplementOrder102U1Cofactor810]
  ring

end PiOrder102Frozen810

section PiOrder102Map810

variable {R S : Type*} [CommRing R] [CommRing S]

set_option maxHeartbeats 800000000 in
theorem map_piLeftUnsolvedOrder102810 (phi : R →+* S)
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    phi (piLeftUnsolvedOrder102810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda) =
      piLeftUnsolvedOrder102810 (phi t0) (phi v1) (phi u1) (phi a4)
        (phi a3) (phi a2) (phi a1) (phi a0) (phi s1) (phi w1)
        (phi b62) (phi b5) (phi b4) (phi b3) (phi b2) (phi b1)
        (phi lambda) := by
  simp only [piLeftUnsolvedOrder102810, map_add, map_sub, map_mul,
    map_pow, map_neg, map_ofNat, map_zero]

#print axioms map_piLeftUnsolvedOrder102810

end PiOrder102Map810

section PiOrder102Eval810

variable {k : Type*} [CommRing k]

theorem piLeftUnsolvedOrder102810_eval
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 : k[X])
    (lambda a : k) :
    (piLeftUnsolvedOrder102810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a =
      piLeftUnsolvedOrder102810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda := by
  simpa [Polynomial.eval_C] using
    map_piLeftUnsolvedOrder102810 (Polynomial.evalRingHom a) t0 v1 u1 a4
      a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)

#print axioms piLeftUnsolvedOrder102810_eval

end PiOrder102Eval810
section PiOrder102Source810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 800000000 in
/-- Remaining power vanishing after the unsolved order-`101` residual is
peeled.  Witnesses stay unsolved.  The `h0`-divisibilities are the
shape the ceiling lemma consumes. -/
theorem piLeftUnsolvedOrder102810_zero_of_power
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 : k[X])
    (lambda eta a : k) (hh : h ≠ 0) (hdegree : h.natDegree = 1)
    (hroot : h.eval a = 0)
    (hpower :
      localClearedSixteenthDefect810
          h (h ^ 6 * t0) (h ^ 4 * v1) (h ^ 2 * u1)
          a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1)
          (h ^ 2 * b62) b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 112) :
    ∃ (o96n o97n o98n o99n o100n o101n : k[X]),
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
        o98n +
            piLeftUnsolvedOrder99810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o99n ∧
        o99n +
            piLeftUnsolvedOrder100810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o100n ∧
        o100n +
            piLeftUnsolvedOrder101810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o101n ∧
        o101n.eval a +
            piLeftUnsolvedOrder102810 (t0.eval a) (v1.eval a)
              (u1.eval a) (a4.eval a) (a3.eval a) (a2.eval a)
              (a1.eval a) (a0.eval a) (s1.eval a) (w1.eval a)
              (b62.eval a) (b5.eval a) (b4.eval a) (b3.eval a)
              (b2.eval a) (b1.eval a) lambda = 0 := by
  obtain ⟨o96n, o97n, o98n, o99n, o100n, ho, ho97, ho98, ho99, ho100, hmix⟩ :=
    piLeftUnsolvedOrder101810_zero_of_power h t0 v1 u1 a4 a3 a2 a1 a0 s1
      w1 b62 b5 b4 b3 b2 b1 lambda eta a hh hdegree hroot hpower
  have hsum0 :
      (o100n +
          piLeftUnsolvedOrder101810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a = 0 := by
    rw [Polynomial.eval_add, piLeftUnsolvedOrder101810_eval]
    exact hmix
  obtain ⟨o101n, ho101⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h
      (o100n +
        piLeftUnsolvedOrder101810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda))
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
  have hplus12 :
      o99n +
          piLeftUnsolvedOrder99Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 12 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o99n +
            piLeftUnsolvedOrder99Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o98n +
            piLeftUnsolvedOrder99810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder99Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho99]
        ring
      _ = o98n +
            piLeftUnsolvedOrder98Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedOrder98Plus810_of_order99]
        ring
      _ = Polynomial.C eta * h ^ 13 := hplus13
      _ = h * (Polynomial.C eta * h ^ 12) := by ring
  have hplus11 :
      o100n +
          piLeftUnsolvedOrder100Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 11 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o100n +
            piLeftUnsolvedOrder100Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o99n +
            piLeftUnsolvedOrder100810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder100Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho100]
        ring
      _ = o99n +
            piLeftUnsolvedOrder99Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedOrder99Plus810_of_order100]
        ring
      _ = Polynomial.C eta * h ^ 12 := hplus12
      _ = h * (Polynomial.C eta * h ^ 11) := by ring
  have hplus10 :
      o101n +
          piLeftUnsolvedOrder101Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 10 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o101n +
            piLeftUnsolvedOrder101Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o100n +
            piLeftUnsolvedOrder101810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder101Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho101]
        ring
      _ = o100n +
            piLeftUnsolvedOrder100Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedOrder100Plus810_of_order101]
        ring
      _ = Polynomial.C eta * h ^ 11 := hplus11
      _ = h * (Polynomial.C eta * h ^ 10) := by ring
  have htail :
      (piLeftUnsolvedOrder101Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
          b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a =
        (piLeftUnsolvedOrder102810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
          b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a := by
    rw [piLeftUnsolvedOrder101Plus810_of_order102]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, hroot,
      zero_mul, add_zero]
  refine ⟨o96n, o97n, o98n, o99n, o100n, o101n, ho, ho97, ho98, ho99, ho100, ho101, ?_⟩
  have hev := congrArg (Polynomial.eval a) hplus10
  rw [← piLeftUnsolvedOrder102810_eval, ← htail]
  simpa [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, hroot] using hev

set_option maxHeartbeats 800000000 in
/-- Source-facing order-`102` peel from a literal `(8,10)` source. -/
theorem piLeftUnsolvedOrder102810_zero_of_source
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
    ∃ (o96n o97n o98n o99n o100n o101n : k[X]),
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
        o98n +
            piLeftUnsolvedOrder99810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o99n ∧
        o99n +
            piLeftUnsolvedOrder100810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o100n ∧
        o100n +
            piLeftUnsolvedOrder101810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o101n ∧
        o101n.eval a +
            piLeftUnsolvedOrder102810 (t0.eval a) (v1.eval a)
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
  exact piLeftUnsolvedOrder102810_zero_of_power h0 t0 v1 u1
    (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1
    b62 (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
    lambda (17592186044416 * eta) a hh0 hdegree hroot hpower

set_option maxHeartbeats 800000000 in
/-- Source-facing order-`102` chambers.  Witnesses stay unsolved.  The
fifteenth-face extras are carried from the parent.  This is not a
closure. -/
theorem piFace810_linearRoot_order102Chambers
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
    ∃ (t0 v0 u0 s0 w0 v1 s1 u1 w1 b62 o96n o97n o98n o99n o100n o101n : k[X]),
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
        o98n +
            piLeftUnsolvedOrder99810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o99n ∧
        o99n +
            piLeftUnsolvedOrder100810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o100n ∧
        o100n +
            piLeftUnsolvedOrder101810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o101n ∧
        o101n.eval a +
            piLeftUnsolvedOrder102810 (t0.eval a) (v1.eval a)
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
  obtain ⟨t0, v0, u0, s0, w0, v1, s1, u1, w1, b62, o96n, o97n, o98n, o99n, o100n, ht0, hv0, hu0, hs0, hw0, hv1, hs1, hu1, hw1, hb62, ho96, ho97, ho98, ho99, ho100, hmix101, hsplit⟩ :=
    piFace810_linearRoot_order101Chambers p q H h0 j lambda a hp hq
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
  obtain ⟨o96n', o97n', o98n', o99n', o100n', o101n, ho', ho97', ho98', ho99', ho100', ho101, hmix102⟩ :=
    piLeftUnsolvedOrder102810_zero_of_source p q H h0 j lambda a t0 v1
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
  have ho98eq : o98n = o98n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o98n = o97n +
          piLeftUnsolvedOrder98810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) := ho98.symm
      _ = h0 * o98n' := ho98'
  subst ho98eq
  have ho99eq : o99n = o99n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o99n = o98n +
          piLeftUnsolvedOrder99810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) := ho99.symm
      _ = h0 * o99n' := ho99'
  subst ho99eq
  have ho100eq : o100n = o100n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o100n = o99n +
          piLeftUnsolvedOrder100810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) := ho100.symm
      _ = h0 * o100n' := ho100'
  subst ho100eq
  refine ⟨t0, v0, u0, s0, w0, v1, s1, u1, w1, b62, o96n, o97n, o98n, o99n, o100n, o101n,
    ht0, hv0, hu0, hs0, hw0, hv1, hs1, hu1, hw1, hb62, ho96, ho97, ho98, ho99, ho100, ho101, hmix102, ?_⟩
  exact hsplit

#print axioms piLeftUnsolvedOrder101Plus810_of_order102
#print axioms piLeftUnsolvedOrder102810_of_t0u1Zero
#print axioms piLeftUnsolvedOrder102810_zero_of_power
#print axioms piLeftUnsolvedOrder102810_zero_of_source
#print axioms piFace810_linearRoot_order102Chambers
#print axioms piLeftUnsolvedRightU1ZeroOrder102810_b62Law
#print axioms piLeftUnsolvedRightComplementOrder102810_u1rel

end PiOrder102Source810
section PiOrder103Frozen810

variable {R : Type*} [CommRing R]

set_option maxHeartbeats 800000000 in
/-- Frozen order-`103` mixin: the `h⁰` coefficient of the order-`102` Plus
remainder, equivalently the `h^6` coefficient of the unsolved tail
and the `h^7` coefficient of the factored residual after the
order-`96` head. -/
def piLeftUnsolvedOrder103810 (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (2268109209600 : R) * t0 ^ 8 * a1 * lambda
    + (17519188377600 : R) * t0 ^ 6 * v1 * a1 * lambda
    - (16818420842496 : R) * t0 ^ 5 * u1 * a1 * lambda
    - (42046052106240 : R) * t0 ^ 4 * v1 ^ 2 * a1 * lambda
    + (16017543659520 : R) * t0 ^ 4 * a4 * a1 * lambda
    + (16017543659520 : R) * t0 ^ 4 * a3 * a2 * lambda
    + (64070174638080 : R) * t0 ^ 3 * v1 * u1 * a1 * lambda
    + (32035087319040 : R) * t0 ^ 2 * v1 ^ 3 * a1 * lambda
    - (45226005626880 : R) * t0 ^ 2 * v1 * a4 * a1 * lambda
    - (45226005626880 : R) * t0 ^ 2 * v1 * a3 * a2 * lambda
    - (22613002813440 : R) * t0 ^ 2 * u1 ^ 2 * a1 * lambda
    - (45226005626880 : R) * t0 * v1 ^ 2 * u1 * a1 * lambda
    + (27831388078080 : R) * t0 * u1 * a4 * a1 * lambda
    + (27831388078080 : R) * t0 * u1 * a3 * a2 * lambda
    - (3768833802240 : R) * v1 ^ 4 * a1 * lambda
    + (13915694039040 : R) * v1 ^ 2 * a4 * a1 * lambda
    + (13915694039040 : R) * v1 ^ 2 * a3 * a2 * lambda
    + (13915694039040 : R) * v1 * u1 ^ 2 * a1 * lambda
    - (6184752906240 : R) * a4 ^ 2 * a1 * lambda
    - (12369505812480 : R) * a4 * a3 * a2 * lambda
    - (2061584302080 : R) * a3 ^ 3 * lambda

set_option maxHeartbeats 800000000 in
/-- Remaining factor after `h` is removed from the order-`102` Plus
remainder. -/
def piLeftUnsolvedOrder103Plus810 (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (21990232555520 : R) * h ^ 8 * a0 ^ 2
    + (9895604649984 : R) * h ^ 7 * a1 * a0 * lambda
    + (5497558138880 : R) * h ^ 6 * t0 * a1 * a0
    + (17592186044416 : R) * h ^ 6 * a1 * b1
    + (35184372088832 : R) * h ^ 6 * a0 * b2
    - (12369505812480 : R) * h ^ 5 * t0 * a2 * a0 * lambda
    - (6184752906240 : R) * h ^ 5 * t0 * a1 ^ 2 * lambda
    - (4398046511104 : R) * h ^ 4 * t0 * a2 * b1
    - (8796093022208 : R) * h ^ 4 * t0 * a1 * b2
    - (13194139533312 : R) * h ^ 4 * t0 * a0 * b3
    + (54975581388800 : R) * h ^ 4 * v1 * a2 * a0
    + (27487790694400 : R) * h ^ 4 * v1 * a1 ^ 2
    - (35184372088832 : R) * h ^ 4 * a2 * a0 * s1
    - (17592186044416 : R) * h ^ 4 * a1 ^ 2 * s1
    + (13915694039040 : R) * h ^ 3 * t0 ^ 2 * a3 * a0 * lambda
    + (13915694039040 : R) * h ^ 3 * t0 ^ 2 * a2 * a1 * lambda
    - (12369505812480 : R) * h ^ 3 * v1 * a3 * a0 * lambda
    - (12369505812480 : R) * h ^ 3 * v1 * a2 * a1 * lambda
    - (2576980377600 : R) * h ^ 2 * t0 ^ 3 * a3 * a0
    - (2576980377600 : R) * h ^ 2 * t0 ^ 3 * a2 * a1
    + (2748779069440 : R) * h ^ 2 * t0 ^ 2 * a3 * b1
    + (5497558138880 : R) * h ^ 2 * t0 ^ 2 * a2 * b2
    + (8246337208320 : R) * h ^ 2 * t0 ^ 2 * a1 * b3
    + (10995116277760 : R) * h ^ 2 * t0 ^ 2 * a0 * b4
    - (61847529062400 : R) * h ^ 2 * t0 * v1 * a3 * a0
    - (61847529062400 : R) * h ^ 2 * t0 * v1 * a2 * a1
    + (43980465111040 : R) * h ^ 2 * t0 * a3 * a0 * s1
    + (43980465111040 : R) * h ^ 2 * t0 * a2 * a1 * s1
    - (4398046511104 : R) * h ^ 2 * v1 * a3 * b1
    - (8796093022208 : R) * h ^ 2 * v1 * a2 * b2
    - (13194139533312 : R) * h ^ 2 * v1 * a1 * b3
    - (17592186044416 : R) * h ^ 2 * v1 * a0 * b4
    + (54975581388800 : R) * h ^ 2 * u1 * a3 * a0
    + (54975581388800 : R) * h ^ 2 * u1 * a2 * a1
    - (30786325577728 : R) * h ^ 2 * a3 * a0 * w1
    - (30786325577728 : R) * h ^ 2 * a2 * a1 * w1
    + (2502741196800 : R) * h * t0 ^ 7 * a0 * lambda
    - (16818420842496 : R) * h * t0 ^ 5 * v1 * a0 * lambda
    + (16017543659520 : R) * h * t0 ^ 4 * u1 * a0 * lambda
    + (32035087319040 : R) * h * t0 ^ 3 * v1 ^ 2 * a0 * lambda
    - (15075335208960 : R) * h * t0 ^ 3 * a4 * a0 * lambda
    - (15075335208960 : R) * h * t0 ^ 3 * a3 * a1 * lambda
    - (7537667604480 : R) * h * t0 ^ 3 * a2 ^ 2 * lambda
    - (45226005626880 : R) * h * t0 ^ 2 * v1 * u1 * a0 * lambda
    - (15075335208960 : R) * h * t0 * v1 ^ 3 * a0 * lambda
    + (27831388078080 : R) * h * t0 * v1 * a4 * a0 * lambda
    + (27831388078080 : R) * h * t0 * v1 * a3 * a1 * lambda
    + (13915694039040 : R) * h * t0 * v1 * a2 ^ 2 * lambda
    + (13915694039040 : R) * h * t0 * u1 ^ 2 * a0 * lambda
    + (13915694039040 : R) * h * v1 ^ 2 * u1 * a0 * lambda
    - (12369505812480 : R) * h * u1 * a4 * a0 * lambda
    - (12369505812480 : R) * h * u1 * a3 * a1 * lambda
    - (6184752906240 : R) * h * u1 * a2 ^ 2 * lambda
    - (2433220608000 : R) * t0 ^ 8 * a0
    + (177972707328 : R) * t0 ^ 7 * b1
    + (6229044756480 : R) * t0 ^ 6 * v1 * a0
    + (9966471610368 : R) * t0 ^ 6 * a0 * s1
    - (1423781658624 : R) * t0 ^ 5 * v1 * b1
    - (5339181219840 : R) * t0 ^ 5 * u1 * a0
    - (9966471610368 : R) * t0 ^ 5 * a0 * w1
    + (26695906099200 : R) * t0 ^ 4 * v1 ^ 2 * a0
    - (56951266344960 : R) * t0 ^ 4 * v1 * a0 * s1
    + (1675037245440 : R) * t0 ^ 4 * u1 * b1
    + (4187593113600 : R) * t0 ^ 4 * a4 * a0
    + (4187593113600 : R) * t0 ^ 4 * a3 * a1
    + (2093796556800 : R) * t0 ^ 4 * a2 ^ 2
    + (10050223472640 : R) * t0 ^ 4 * a0 * b62
    + (3350074490880 : R) * t0 ^ 3 * v1 ^ 2 * b1
    - (58626303590400 : R) * t0 ^ 3 * v1 * u1 * a0
    + (46901042872320 : R) * t0 ^ 3 * v1 * a0 * w1
    + (53601191854080 : R) * t0 ^ 3 * u1 * a0 * s1
    - (2061584302080 : R) * t0 ^ 3 * a4 * b1
    - (4123168604160 : R) * t0 ^ 3 * a3 * b2
    - (6184752906240 : R) * t0 ^ 3 * a2 * b3
    - (8246337208320 : R) * t0 ^ 3 * a1 * b4
    - (10307921510400 : R) * t0 ^ 3 * a0 * b5
    - (67001489817600 : R) * t0 ^ 2 * v1 ^ 3 * a0
    + (80401787781120 : R) * t0 ^ 2 * v1 ^ 2 * a0 * s1
    - (6184752906240 : R) * t0 ^ 2 * v1 * u1 * b1
    + (61847529062400 : R) * t0 ^ 2 * v1 * a4 * a0
    + (61847529062400 : R) * t0 ^ 2 * v1 * a3 * a1
    + (30923764531200 : R) * t0 ^ 2 * v1 * a2 ^ 2
    - (37108517437440 : R) * t0 ^ 2 * v1 * a0 * b62
    + (30923764531200 : R) * t0 ^ 2 * u1 ^ 2 * a0
    - (43293270343680 : R) * t0 ^ 2 * u1 * a0 * w1
    - (49478023249920 : R) * t0 ^ 2 * a4 * a0 * s1
    - (49478023249920 : R) * t0 ^ 2 * a3 * a1 * s1
    - (24739011624960 : R) * t0 ^ 2 * a2 ^ 2 * s1
    - (2061584302080 : R) * t0 * v1 ^ 3 * b1
    + (131425999257600 : R) * t0 * v1 ^ 2 * u1 * a0
    - (43293270343680 : R) * t0 * v1 ^ 2 * a0 * w1
    - (98956046499840 : R) * t0 * v1 * u1 * a0 * s1
    + (5497558138880 : R) * t0 * v1 * a4 * b1
    + (10995116277760 : R) * t0 * v1 * a3 * b2
    + (16492674416640 : R) * t0 * v1 * a2 * b3
    + (21990232555520 : R) * t0 * v1 * a1 * b4
    + (27487790694400 : R) * t0 * v1 * a0 * b5
    + (2748779069440 : R) * t0 * u1 ^ 2 * b1
    - (61847529062400 : R) * t0 * u1 * a4 * a0
    - (61847529062400 : R) * t0 * u1 * a3 * a1
    - (30923764531200 : R) * t0 * u1 * a2 ^ 2
    + (32985348833280 : R) * t0 * u1 * a0 * b62
    + (38482906972160 : R) * t0 * a4 * a0 * w1
    + (38482906972160 : R) * t0 * a3 * a1 * w1
    + (19241453486080 : R) * t0 * a2 ^ 2 * w1
    + (16750372454400 : R) * v1 ^ 4 * a0
    - (16492674416640 : R) * v1 ^ 3 * a0 * s1
    + (2748779069440 : R) * v1 ^ 2 * u1 * b1
    - (61847529062400 : R) * v1 ^ 2 * a4 * a0
    - (61847529062400 : R) * v1 ^ 2 * a3 * a1
    - (30923764531200 : R) * v1 ^ 2 * a2 ^ 2
    + (16492674416640 : R) * v1 ^ 2 * a0 * b62
    - (61847529062400 : R) * v1 * u1 ^ 2 * a0
    + (38482906972160 : R) * v1 * u1 * a0 * w1
    + (43980465111040 : R) * v1 * a4 * a0 * s1
    + (43980465111040 : R) * v1 * a3 * a1 * s1
    + (21990232555520 : R) * v1 * a2 ^ 2 * s1
    + (21990232555520 : R) * u1 ^ 2 * a0 * s1
    - (4398046511104 : R) * u1 * a4 * b1
    - (8796093022208 : R) * u1 * a3 * b2
    - (13194139533312 : R) * u1 * a2 * b3
    - (17592186044416 : R) * u1 * a1 * b4
    - (21990232555520 : R) * u1 * a0 * b5
    + (27487790694400 : R) * a4 ^ 2 * a0
    + (54975581388800 : R) * a4 * a3 * a1
    + (27487790694400 : R) * a4 * a2 ^ 2
    - (26388279066624 : R) * a4 * a0 * b62
    + (27487790694400 : R) * a3 ^ 2 * a2
    - (26388279066624 : R) * a3 * a1 * b62
    - (13194139533312 : R) * a2 ^ 2 * b62

set_option maxHeartbeats 800000000 in
theorem piLeftUnsolvedOrder102Plus810_of_order103
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    piLeftUnsolvedOrder102Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda =
      piLeftUnsolvedOrder103810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
          b5 b4 b3 b2 b1 lambda +
        h * piLeftUnsolvedOrder103Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
          s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  simp only [piLeftUnsolvedOrder102Plus810, piLeftUnsolvedOrder103810,
    piLeftUnsolvedOrder103Plus810]
  ring

set_option maxHeartbeats 400000000 in
theorem piLeftUnsolvedOrder102Plus810_zero
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    piLeftUnsolvedOrder102Plus810 0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda =
      piLeftUnsolvedOrder103810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda := by
  rw [piLeftUnsolvedOrder102Plus810_of_order103]
  simp only [zero_mul, add_zero]

set_option maxHeartbeats 800000000 in
theorem piLeftUnsolvedTail810_of_order103
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    piLeftUnsolvedTail810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda =
      piLeftUnsolvedOrder97810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
          b5 b4 b3 b2 b1 lambda +
        h * piLeftUnsolvedOrder98810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
          b62 b5 b4 b3 b2 b1 lambda +
        h ^ 2 * piLeftUnsolvedOrder99810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 3 * piLeftUnsolvedOrder100810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 4 * piLeftUnsolvedOrder101810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 5 * piLeftUnsolvedOrder102810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 6 * piLeftUnsolvedOrder103810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 7 * piLeftUnsolvedOrder103Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
          s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  rw [piLeftUnsolvedTail810_of_order102, piLeftUnsolvedOrder102Plus810_of_order103]
  ring

/-- Order-`103` mixin on `t0 = u1 = 0`. -/
def piLeftUnsolvedOrder103810_t0u1Zero
    (v1 a4 a3 a2 a1 lambda : R) : R :=
    - (3768833802240 : R) * v1 ^ 4 * a1 * lambda
    + (13915694039040 : R) * v1 ^ 2 * a4 * a1 * lambda
    + (13915694039040 : R) * v1 ^ 2 * a3 * a2 * lambda
    - (6184752906240 : R) * a4 ^ 2 * a1 * lambda
    - (12369505812480 : R) * a4 * a3 * a2 * lambda
    - (2061584302080 : R) * a3 ^ 3 * lambda

set_option maxHeartbeats 800000000 in
theorem piLeftUnsolvedOrder103810_of_t0u1Zero
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) (ht0 : t0 = 0) (hu1 : u1 = 0) :
    piLeftUnsolvedOrder103810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda =
      piLeftUnsolvedOrder103810_t0u1Zero v1 a4 a3 a2 a1 lambda := by
  simp only [piLeftUnsolvedOrder103810,
    piLeftUnsolvedOrder103810_t0u1Zero, ht0, hu1]
  ring

/-- Integer `5`-clearing of the LEFT order-`103` mixin after
the four scalar relations.  Witnesses `m1, τ1, g1, k1` are not
inserted. -/
def piLeftUnsolvedLeftOrder103810 (t0 v1 u1 a3 a2 a1 b62 lambda : R) : R :=
    - (12441275596800 : R) * t0 ^ 8 * a1 * lambda
    + (98275059302400 : R) * t0 ^ 6 * v1 * a1 * lambda
    - (106227963002880 : R) * t0 ^ 5 * u1 * a1 * lambda
    - (242769670963200 : R) * t0 ^ 4 * v1 ^ 2 * a1 * lambda
    + (80933289984000 : R) * t0 ^ 4 * a3 * a2 * lambda
    + (64746631987200 : R) * t0 ^ 4 * a1 * b62 * lambda
    + (391378894848000 : R) * t0 ^ 3 * v1 * u1 * a1 * lambda
    + (195689447424000 : R) * t0 ^ 2 * v1 ^ 3 * a1 * lambda
    - (231928233984000 : R) * t0 ^ 2 * v1 * a3 * a2 * lambda
    - (185542587187200 : R) * t0 ^ 2 * v1 * a1 * b62 * lambda
    - (149786984448000 : R) * t0 ^ 2 * u1 ^ 2 * a1 * lambda
    - (262851998515200 : R) * t0 * v1 ^ 2 * u1 * a1 * lambda
    + (154618822656000 : R) * t0 * u1 * a3 * a2 * lambda
    + (123695058124800 : R) * t0 * u1 * a1 * b62 * lambda
    - (28024661606400 : R) * v1 ^ 4 * a1 * lambda
    + (77309411328000 : R) * v1 ^ 2 * a3 * a2 * lambda
    + (61847529062400 : R) * v1 ^ 2 * a1 * b62 * lambda
    + (69578470195200 : R) * v1 * u1 ^ 2 * a1 * lambda
    - (10307921510400 : R) * a3 ^ 3 * lambda
    - (49478023249920 : R) * a3 * a2 * b62 * lambda
    - (19791209299968 : R) * a1 * b62 ^ 2 * lambda

/-- Integer `5`-clearing of the RIGHT/`u1 = 0` order-`103`
mixin after the four scalar relations. -/
def piLeftUnsolvedRightU1ZeroOrder103810 (v1 a3 a2 a1 b62 lambda : R) : R :=
    - (28024661606400 : R) * v1 ^ 4 * a1 * lambda
    + (77309411328000 : R) * v1 ^ 2 * a3 * a2 * lambda
    + (61847529062400 : R) * v1 ^ 2 * a1 * b62 * lambda
    - (10307921510400 : R) * a3 ^ 3 * lambda
    - (49478023249920 : R) * a3 * a2 * b62 * lambda
    - (19791209299968 : R) * a1 * b62 ^ 2 * lambda

/-- Cofactor of `16 b62 - 5 v1²` in the cleared RIGHT/`u1 = 0`
order-`103` mixin. -/
def piLeftUnsolvedRightU1ZeroOrder103B62Cofactor810
    (v1 a3 a2 a1 b62 lambda : R) : R :=
    (890604418498560 : R) * v1 ^ 2 * a1 * lambda
    - (791648371998720 : R) * a3 * a2 * lambda
    - (316659348799488 : R) * a1 * b62 * lambda

set_option maxHeartbeats 400000000 in
/-- Fifteenth-face extra `16 b62 = 5 v1²` specializes the RIGHT/`u1 = 0`
order-`103` mixin. -/
theorem piLeftUnsolvedRightU1ZeroOrder103810_b62Law
    (v1 a3 a2 a1 b62 lambda : R) :
    (256 : R) * piLeftUnsolvedRightU1ZeroOrder103810 v1 a3 a2 a1 b62 lambda =
      ((16 : R) * b62 - (5 : R) * v1 ^ 2) *
          piLeftUnsolvedRightU1ZeroOrder103B62Cofactor810
            v1 a3 a2 a1 b62 lambda +
        - (2721291278745600 : R) * v1 ^ 4 * a1 * lambda
        + (15832967439974400 : R) * v1 ^ 2 * a3 * a2 * lambda
        - (2638827906662400 : R) * a3 ^ 3 * lambda := by
  simp only [piLeftUnsolvedRightU1ZeroOrder103810,
    piLeftUnsolvedRightU1ZeroOrder103B62Cofactor810]
  ring

/-- Frozen order-`103` mixin on the RIGHT complement scalar locus. -/
def piLeftUnsolvedRightComplementOrder103810
    (v1 u1 a3 a2 a1 lambda : R) : R :=
    (579820584960 : R) * v1 ^ 4 * a1 * lambda
    + (9277129359360 : R) * v1 ^ 2 * a3 * a2 * lambda
    + (13915694039040 : R) * v1 * u1 ^ 2 * a1 * lambda
    - (2061584302080 : R) * a3 ^ 3 * lambda

/-- Cofactor of `2 u1² + v1³` in the cleared complement mixin. -/
def piLeftUnsolvedRightComplementOrder103U1Cofactor810
    (v1 u1 a3 a2 a1 lambda : R) : R :=
    (27831388078080 : R) * v1 * a1 * lambda

set_option maxHeartbeats 400000000 in
/-- Fifteenth-face extra `2 u1² + v1³ = 0` specializes the complement
order-`103` mixin. -/
theorem piLeftUnsolvedRightComplementOrder103810_u1rel
    (v1 u1 a3 a2 a1 lambda : R) :
    (4 : R) * piLeftUnsolvedRightComplementOrder103810 v1 u1 a3 a2 a1 lambda =
      ((2 : R) * u1 ^ 2 + v1 ^ 3) *
          piLeftUnsolvedRightComplementOrder103U1Cofactor810
            v1 u1 a3 a2 a1 lambda +
        - (25512105738240 : R) * v1 ^ 4 * a1 * lambda
        + (37108517437440 : R) * v1 ^ 2 * a3 * a2 * lambda
        - (8246337208320 : R) * a3 ^ 3 * lambda := by
  simp only [piLeftUnsolvedRightComplementOrder103810,
    piLeftUnsolvedRightComplementOrder103U1Cofactor810]
  ring

end PiOrder103Frozen810

section PiOrder103Map810

variable {R S : Type*} [CommRing R] [CommRing S]

set_option maxHeartbeats 800000000 in
theorem map_piLeftUnsolvedOrder103810 (phi : R →+* S)
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    phi (piLeftUnsolvedOrder103810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda) =
      piLeftUnsolvedOrder103810 (phi t0) (phi v1) (phi u1) (phi a4)
        (phi a3) (phi a2) (phi a1) (phi a0) (phi s1) (phi w1)
        (phi b62) (phi b5) (phi b4) (phi b3) (phi b2) (phi b1)
        (phi lambda) := by
  simp only [piLeftUnsolvedOrder103810, map_add, map_sub, map_mul,
    map_pow, map_neg, map_ofNat, map_zero]

#print axioms map_piLeftUnsolvedOrder103810

end PiOrder103Map810

section PiOrder103Eval810

variable {k : Type*} [CommRing k]

theorem piLeftUnsolvedOrder103810_eval
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 : k[X])
    (lambda a : k) :
    (piLeftUnsolvedOrder103810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a =
      piLeftUnsolvedOrder103810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda := by
  simpa [Polynomial.eval_C] using
    map_piLeftUnsolvedOrder103810 (Polynomial.evalRingHom a) t0 v1 u1 a4
      a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)

#print axioms piLeftUnsolvedOrder103810_eval

end PiOrder103Eval810
section PiOrder103Source810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 800000000 in
/-- Remaining power vanishing after the unsolved order-`102` residual is
peeled.  Witnesses stay unsolved.  The `h0`-divisibilities are the
shape the ceiling lemma consumes. -/
theorem piLeftUnsolvedOrder103810_zero_of_power
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 : k[X])
    (lambda eta a : k) (hh : h ≠ 0) (hdegree : h.natDegree = 1)
    (hroot : h.eval a = 0)
    (hpower :
      localClearedSixteenthDefect810
          h (h ^ 6 * t0) (h ^ 4 * v1) (h ^ 2 * u1)
          a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1)
          (h ^ 2 * b62) b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 112) :
    ∃ (o96n o97n o98n o99n o100n o101n o102n : k[X]),
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
        o98n +
            piLeftUnsolvedOrder99810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o99n ∧
        o99n +
            piLeftUnsolvedOrder100810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o100n ∧
        o100n +
            piLeftUnsolvedOrder101810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o101n ∧
        o101n +
            piLeftUnsolvedOrder102810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o102n ∧
        o102n.eval a +
            piLeftUnsolvedOrder103810 (t0.eval a) (v1.eval a)
              (u1.eval a) (a4.eval a) (a3.eval a) (a2.eval a)
              (a1.eval a) (a0.eval a) (s1.eval a) (w1.eval a)
              (b62.eval a) (b5.eval a) (b4.eval a) (b3.eval a)
              (b2.eval a) (b1.eval a) lambda = 0 := by
  obtain ⟨o96n, o97n, o98n, o99n, o100n, o101n, ho, ho97, ho98, ho99, ho100, ho101, hmix⟩ :=
    piLeftUnsolvedOrder102810_zero_of_power h t0 v1 u1 a4 a3 a2 a1 a0 s1
      w1 b62 b5 b4 b3 b2 b1 lambda eta a hh hdegree hroot hpower
  have hsum0 :
      (o101n +
          piLeftUnsolvedOrder102810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a = 0 := by
    rw [Polynomial.eval_add, piLeftUnsolvedOrder102810_eval]
    exact hmix
  obtain ⟨o102n, ho102⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h
      (o101n +
        piLeftUnsolvedOrder102810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda))
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
  have hplus12 :
      o99n +
          piLeftUnsolvedOrder99Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 12 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o99n +
            piLeftUnsolvedOrder99Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o98n +
            piLeftUnsolvedOrder99810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder99Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho99]
        ring
      _ = o98n +
            piLeftUnsolvedOrder98Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedOrder98Plus810_of_order99]
        ring
      _ = Polynomial.C eta * h ^ 13 := hplus13
      _ = h * (Polynomial.C eta * h ^ 12) := by ring
  have hplus11 :
      o100n +
          piLeftUnsolvedOrder100Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 11 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o100n +
            piLeftUnsolvedOrder100Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o99n +
            piLeftUnsolvedOrder100810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder100Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho100]
        ring
      _ = o99n +
            piLeftUnsolvedOrder99Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedOrder99Plus810_of_order100]
        ring
      _ = Polynomial.C eta * h ^ 12 := hplus12
      _ = h * (Polynomial.C eta * h ^ 11) := by ring
  have hplus10 :
      o101n +
          piLeftUnsolvedOrder101Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 10 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o101n +
            piLeftUnsolvedOrder101Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o100n +
            piLeftUnsolvedOrder101810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder101Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho101]
        ring
      _ = o100n +
            piLeftUnsolvedOrder100Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedOrder100Plus810_of_order101]
        ring
      _ = Polynomial.C eta * h ^ 11 := hplus11
      _ = h * (Polynomial.C eta * h ^ 10) := by ring
  have hplus9 :
      o102n +
          piLeftUnsolvedOrder102Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 9 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o102n +
            piLeftUnsolvedOrder102Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o101n +
            piLeftUnsolvedOrder102810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder102Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho102]
        ring
      _ = o101n +
            piLeftUnsolvedOrder101Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedOrder101Plus810_of_order102]
        ring
      _ = Polynomial.C eta * h ^ 10 := hplus10
      _ = h * (Polynomial.C eta * h ^ 9) := by ring
  have htail :
      (piLeftUnsolvedOrder102Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
          b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a =
        (piLeftUnsolvedOrder103810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
          b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a := by
    rw [piLeftUnsolvedOrder102Plus810_of_order103]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, hroot,
      zero_mul, add_zero]
  refine ⟨o96n, o97n, o98n, o99n, o100n, o101n, o102n, ho, ho97, ho98, ho99, ho100, ho101, ho102, ?_⟩
  have hev := congrArg (Polynomial.eval a) hplus9
  rw [← piLeftUnsolvedOrder103810_eval, ← htail]
  simpa [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, hroot] using hev

set_option maxHeartbeats 800000000 in
/-- Source-facing order-`103` peel from a literal `(8,10)` source. -/
theorem piLeftUnsolvedOrder103810_zero_of_source
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
    ∃ (o96n o97n o98n o99n o100n o101n o102n : k[X]),
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
        o98n +
            piLeftUnsolvedOrder99810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o99n ∧
        o99n +
            piLeftUnsolvedOrder100810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o100n ∧
        o100n +
            piLeftUnsolvedOrder101810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o101n ∧
        o101n +
            piLeftUnsolvedOrder102810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o102n ∧
        o102n.eval a +
            piLeftUnsolvedOrder103810 (t0.eval a) (v1.eval a)
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
  exact piLeftUnsolvedOrder103810_zero_of_power h0 t0 v1 u1
    (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1
    b62 (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
    lambda (17592186044416 * eta) a hh0 hdegree hroot hpower

set_option maxHeartbeats 800000000 in
/-- Source-facing order-`103` chambers.  Witnesses stay unsolved.  The
fifteenth-face extras are carried from the parent.  This is not a
closure. -/
theorem piFace810_linearRoot_order103Chambers
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
    ∃ (t0 v0 u0 s0 w0 v1 s1 u1 w1 b62 o96n o97n o98n o99n o100n o101n o102n : k[X]),
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
        o98n +
            piLeftUnsolvedOrder99810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o99n ∧
        o99n +
            piLeftUnsolvedOrder100810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o100n ∧
        o100n +
            piLeftUnsolvedOrder101810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o101n ∧
        o101n +
            piLeftUnsolvedOrder102810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o102n ∧
        o102n.eval a +
            piLeftUnsolvedOrder103810 (t0.eval a) (v1.eval a)
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
  obtain ⟨t0, v0, u0, s0, w0, v1, s1, u1, w1, b62, o96n, o97n, o98n, o99n, o100n, o101n, ht0, hv0, hu0, hs0, hw0, hv1, hs1, hu1, hw1, hb62, ho96, ho97, ho98, ho99, ho100, ho101, hmix102, hsplit⟩ :=
    piFace810_linearRoot_order102Chambers p q H h0 j lambda a hp hq
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
  obtain ⟨o96n', o97n', o98n', o99n', o100n', o101n', o102n, ho', ho97', ho98', ho99', ho100', ho101', ho102, hmix103⟩ :=
    piLeftUnsolvedOrder103810_zero_of_source p q H h0 j lambda a t0 v1
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
  have ho98eq : o98n = o98n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o98n = o97n +
          piLeftUnsolvedOrder98810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) := ho98.symm
      _ = h0 * o98n' := ho98'
  subst ho98eq
  have ho99eq : o99n = o99n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o99n = o98n +
          piLeftUnsolvedOrder99810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) := ho99.symm
      _ = h0 * o99n' := ho99'
  subst ho99eq
  have ho100eq : o100n = o100n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o100n = o99n +
          piLeftUnsolvedOrder100810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) := ho100.symm
      _ = h0 * o100n' := ho100'
  subst ho100eq
  have ho101eq : o101n = o101n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o101n = o100n +
          piLeftUnsolvedOrder101810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) := ho101.symm
      _ = h0 * o101n' := ho101'
  subst ho101eq
  refine ⟨t0, v0, u0, s0, w0, v1, s1, u1, w1, b62, o96n, o97n, o98n, o99n, o100n, o101n, o102n,
    ht0, hv0, hu0, hs0, hw0, hv1, hs1, hu1, hw1, hb62, ho96, ho97, ho98, ho99, ho100, ho101, ho102, hmix103, ?_⟩
  exact hsplit

#print axioms piLeftUnsolvedOrder102Plus810_of_order103
#print axioms piLeftUnsolvedOrder103810_of_t0u1Zero
#print axioms piLeftUnsolvedOrder103810_zero_of_power
#print axioms piLeftUnsolvedOrder103810_zero_of_source
#print axioms piFace810_linearRoot_order103Chambers
#print axioms piLeftUnsolvedRightU1ZeroOrder103810_b62Law
#print axioms piLeftUnsolvedRightComplementOrder103810_u1rel

end PiOrder103Source810
section PiOrder104Frozen810

variable {R : Type*} [CommRing R]

set_option maxHeartbeats 800000000 in
/-- Frozen order-`104` mixin: the `h⁰` coefficient of the order-`103` Plus
remainder, equivalently the `h^7` coefficient of the unsolved tail
and the `h^8` coefficient of the factored residual after the
order-`96` head. -/
def piLeftUnsolvedOrder104810 (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (2433220608000 : R) * t0 ^ 8 * a0
    + (177972707328 : R) * t0 ^ 7 * b1
    + (6229044756480 : R) * t0 ^ 6 * v1 * a0
    + (9966471610368 : R) * t0 ^ 6 * a0 * s1
    - (1423781658624 : R) * t0 ^ 5 * v1 * b1
    - (5339181219840 : R) * t0 ^ 5 * u1 * a0
    - (9966471610368 : R) * t0 ^ 5 * a0 * w1
    + (26695906099200 : R) * t0 ^ 4 * v1 ^ 2 * a0
    - (56951266344960 : R) * t0 ^ 4 * v1 * a0 * s1
    + (1675037245440 : R) * t0 ^ 4 * u1 * b1
    + (4187593113600 : R) * t0 ^ 4 * a4 * a0
    + (4187593113600 : R) * t0 ^ 4 * a3 * a1
    + (2093796556800 : R) * t0 ^ 4 * a2 ^ 2
    + (10050223472640 : R) * t0 ^ 4 * a0 * b62
    + (3350074490880 : R) * t0 ^ 3 * v1 ^ 2 * b1
    - (58626303590400 : R) * t0 ^ 3 * v1 * u1 * a0
    + (46901042872320 : R) * t0 ^ 3 * v1 * a0 * w1
    + (53601191854080 : R) * t0 ^ 3 * u1 * a0 * s1
    - (2061584302080 : R) * t0 ^ 3 * a4 * b1
    - (4123168604160 : R) * t0 ^ 3 * a3 * b2
    - (6184752906240 : R) * t0 ^ 3 * a2 * b3
    - (8246337208320 : R) * t0 ^ 3 * a1 * b4
    - (10307921510400 : R) * t0 ^ 3 * a0 * b5
    - (67001489817600 : R) * t0 ^ 2 * v1 ^ 3 * a0
    + (80401787781120 : R) * t0 ^ 2 * v1 ^ 2 * a0 * s1
    - (6184752906240 : R) * t0 ^ 2 * v1 * u1 * b1
    + (61847529062400 : R) * t0 ^ 2 * v1 * a4 * a0
    + (61847529062400 : R) * t0 ^ 2 * v1 * a3 * a1
    + (30923764531200 : R) * t0 ^ 2 * v1 * a2 ^ 2
    - (37108517437440 : R) * t0 ^ 2 * v1 * a0 * b62
    + (30923764531200 : R) * t0 ^ 2 * u1 ^ 2 * a0
    - (43293270343680 : R) * t0 ^ 2 * u1 * a0 * w1
    - (49478023249920 : R) * t0 ^ 2 * a4 * a0 * s1
    - (49478023249920 : R) * t0 ^ 2 * a3 * a1 * s1
    - (24739011624960 : R) * t0 ^ 2 * a2 ^ 2 * s1
    - (2061584302080 : R) * t0 * v1 ^ 3 * b1
    + (131425999257600 : R) * t0 * v1 ^ 2 * u1 * a0
    - (43293270343680 : R) * t0 * v1 ^ 2 * a0 * w1
    - (98956046499840 : R) * t0 * v1 * u1 * a0 * s1
    + (5497558138880 : R) * t0 * v1 * a4 * b1
    + (10995116277760 : R) * t0 * v1 * a3 * b2
    + (16492674416640 : R) * t0 * v1 * a2 * b3
    + (21990232555520 : R) * t0 * v1 * a1 * b4
    + (27487790694400 : R) * t0 * v1 * a0 * b5
    + (2748779069440 : R) * t0 * u1 ^ 2 * b1
    - (61847529062400 : R) * t0 * u1 * a4 * a0
    - (61847529062400 : R) * t0 * u1 * a3 * a1
    - (30923764531200 : R) * t0 * u1 * a2 ^ 2
    + (32985348833280 : R) * t0 * u1 * a0 * b62
    + (38482906972160 : R) * t0 * a4 * a0 * w1
    + (38482906972160 : R) * t0 * a3 * a1 * w1
    + (19241453486080 : R) * t0 * a2 ^ 2 * w1
    + (16750372454400 : R) * v1 ^ 4 * a0
    - (16492674416640 : R) * v1 ^ 3 * a0 * s1
    + (2748779069440 : R) * v1 ^ 2 * u1 * b1
    - (61847529062400 : R) * v1 ^ 2 * a4 * a0
    - (61847529062400 : R) * v1 ^ 2 * a3 * a1
    - (30923764531200 : R) * v1 ^ 2 * a2 ^ 2
    + (16492674416640 : R) * v1 ^ 2 * a0 * b62
    - (61847529062400 : R) * v1 * u1 ^ 2 * a0
    + (38482906972160 : R) * v1 * u1 * a0 * w1
    + (43980465111040 : R) * v1 * a4 * a0 * s1
    + (43980465111040 : R) * v1 * a3 * a1 * s1
    + (21990232555520 : R) * v1 * a2 ^ 2 * s1
    + (21990232555520 : R) * u1 ^ 2 * a0 * s1
    - (4398046511104 : R) * u1 * a4 * b1
    - (8796093022208 : R) * u1 * a3 * b2
    - (13194139533312 : R) * u1 * a2 * b3
    - (17592186044416 : R) * u1 * a1 * b4
    - (21990232555520 : R) * u1 * a0 * b5
    + (27487790694400 : R) * a4 ^ 2 * a0
    + (54975581388800 : R) * a4 * a3 * a1
    + (27487790694400 : R) * a4 * a2 ^ 2
    - (26388279066624 : R) * a4 * a0 * b62
    + (27487790694400 : R) * a3 ^ 2 * a2
    - (26388279066624 : R) * a3 * a1 * b62
    - (13194139533312 : R) * a2 ^ 2 * b62

set_option maxHeartbeats 800000000 in
/-- Remaining factor after `h` is removed from the order-`103` Plus
remainder. -/
def piLeftUnsolvedOrder104Plus810 (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (21990232555520 : R) * h ^ 7 * a0 ^ 2
    + (9895604649984 : R) * h ^ 6 * a1 * a0 * lambda
    + (5497558138880 : R) * h ^ 5 * t0 * a1 * a0
    + (17592186044416 : R) * h ^ 5 * a1 * b1
    + (35184372088832 : R) * h ^ 5 * a0 * b2
    - (12369505812480 : R) * h ^ 4 * t0 * a2 * a0 * lambda
    - (6184752906240 : R) * h ^ 4 * t0 * a1 ^ 2 * lambda
    - (4398046511104 : R) * h ^ 3 * t0 * a2 * b1
    - (8796093022208 : R) * h ^ 3 * t0 * a1 * b2
    - (13194139533312 : R) * h ^ 3 * t0 * a0 * b3
    + (54975581388800 : R) * h ^ 3 * v1 * a2 * a0
    + (27487790694400 : R) * h ^ 3 * v1 * a1 ^ 2
    - (35184372088832 : R) * h ^ 3 * a2 * a0 * s1
    - (17592186044416 : R) * h ^ 3 * a1 ^ 2 * s1
    + (13915694039040 : R) * h ^ 2 * t0 ^ 2 * a3 * a0 * lambda
    + (13915694039040 : R) * h ^ 2 * t0 ^ 2 * a2 * a1 * lambda
    - (12369505812480 : R) * h ^ 2 * v1 * a3 * a0 * lambda
    - (12369505812480 : R) * h ^ 2 * v1 * a2 * a1 * lambda
    - (2576980377600 : R) * h * t0 ^ 3 * a3 * a0
    - (2576980377600 : R) * h * t0 ^ 3 * a2 * a1
    + (2748779069440 : R) * h * t0 ^ 2 * a3 * b1
    + (5497558138880 : R) * h * t0 ^ 2 * a2 * b2
    + (8246337208320 : R) * h * t0 ^ 2 * a1 * b3
    + (10995116277760 : R) * h * t0 ^ 2 * a0 * b4
    - (61847529062400 : R) * h * t0 * v1 * a3 * a0
    - (61847529062400 : R) * h * t0 * v1 * a2 * a1
    + (43980465111040 : R) * h * t0 * a3 * a0 * s1
    + (43980465111040 : R) * h * t0 * a2 * a1 * s1
    - (4398046511104 : R) * h * v1 * a3 * b1
    - (8796093022208 : R) * h * v1 * a2 * b2
    - (13194139533312 : R) * h * v1 * a1 * b3
    - (17592186044416 : R) * h * v1 * a0 * b4
    + (54975581388800 : R) * h * u1 * a3 * a0
    + (54975581388800 : R) * h * u1 * a2 * a1
    - (30786325577728 : R) * h * a3 * a0 * w1
    - (30786325577728 : R) * h * a2 * a1 * w1
    + (2502741196800 : R) * t0 ^ 7 * a0 * lambda
    - (16818420842496 : R) * t0 ^ 5 * v1 * a0 * lambda
    + (16017543659520 : R) * t0 ^ 4 * u1 * a0 * lambda
    + (32035087319040 : R) * t0 ^ 3 * v1 ^ 2 * a0 * lambda
    - (15075335208960 : R) * t0 ^ 3 * a4 * a0 * lambda
    - (15075335208960 : R) * t0 ^ 3 * a3 * a1 * lambda
    - (7537667604480 : R) * t0 ^ 3 * a2 ^ 2 * lambda
    - (45226005626880 : R) * t0 ^ 2 * v1 * u1 * a0 * lambda
    - (15075335208960 : R) * t0 * v1 ^ 3 * a0 * lambda
    + (27831388078080 : R) * t0 * v1 * a4 * a0 * lambda
    + (27831388078080 : R) * t0 * v1 * a3 * a1 * lambda
    + (13915694039040 : R) * t0 * v1 * a2 ^ 2 * lambda
    + (13915694039040 : R) * t0 * u1 ^ 2 * a0 * lambda
    + (13915694039040 : R) * v1 ^ 2 * u1 * a0 * lambda
    - (12369505812480 : R) * u1 * a4 * a0 * lambda
    - (12369505812480 : R) * u1 * a3 * a1 * lambda
    - (6184752906240 : R) * u1 * a2 ^ 2 * lambda

set_option maxHeartbeats 800000000 in
theorem piLeftUnsolvedOrder103Plus810_of_order104
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    piLeftUnsolvedOrder103Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda =
      piLeftUnsolvedOrder104810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
          b5 b4 b3 b2 b1 lambda +
        h * piLeftUnsolvedOrder104Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
          s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  simp only [piLeftUnsolvedOrder103Plus810, piLeftUnsolvedOrder104810,
    piLeftUnsolvedOrder104Plus810]
  ring

set_option maxHeartbeats 400000000 in
theorem piLeftUnsolvedOrder103Plus810_zero
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    piLeftUnsolvedOrder103Plus810 0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda =
      piLeftUnsolvedOrder104810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda := by
  rw [piLeftUnsolvedOrder103Plus810_of_order104]
  simp only [zero_mul, add_zero]

set_option maxHeartbeats 800000000 in
theorem piLeftUnsolvedTail810_of_order104
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    piLeftUnsolvedTail810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda =
      piLeftUnsolvedOrder97810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
          b5 b4 b3 b2 b1 lambda +
        h * piLeftUnsolvedOrder98810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
          b62 b5 b4 b3 b2 b1 lambda +
        h ^ 2 * piLeftUnsolvedOrder99810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 3 * piLeftUnsolvedOrder100810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 4 * piLeftUnsolvedOrder101810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 5 * piLeftUnsolvedOrder102810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 6 * piLeftUnsolvedOrder103810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 7 * piLeftUnsolvedOrder104810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 8 * piLeftUnsolvedOrder104Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
          s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  rw [piLeftUnsolvedTail810_of_order103, piLeftUnsolvedOrder103Plus810_of_order104]
  ring

/-- Order-`104` mixin on `t0 = u1 = 0`. -/
def piLeftUnsolvedOrder104810_t0u1Zero
    (v1 a4 a3 a2 a1 a0 s1 b62 : R) : R :=
    (16750372454400 : R) * v1 ^ 4 * a0
    - (16492674416640 : R) * v1 ^ 3 * a0 * s1
    - (61847529062400 : R) * v1 ^ 2 * a4 * a0
    - (61847529062400 : R) * v1 ^ 2 * a3 * a1
    - (30923764531200 : R) * v1 ^ 2 * a2 ^ 2
    + (16492674416640 : R) * v1 ^ 2 * a0 * b62
    + (43980465111040 : R) * v1 * a4 * a0 * s1
    + (43980465111040 : R) * v1 * a3 * a1 * s1
    + (21990232555520 : R) * v1 * a2 ^ 2 * s1
    + (27487790694400 : R) * a4 ^ 2 * a0
    + (54975581388800 : R) * a4 * a3 * a1
    + (27487790694400 : R) * a4 * a2 ^ 2
    - (26388279066624 : R) * a4 * a0 * b62
    + (27487790694400 : R) * a3 ^ 2 * a2
    - (26388279066624 : R) * a3 * a1 * b62
    - (13194139533312 : R) * a2 ^ 2 * b62

set_option maxHeartbeats 800000000 in
theorem piLeftUnsolvedOrder104810_of_t0u1Zero
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) (ht0 : t0 = 0) (hu1 : u1 = 0) :
    piLeftUnsolvedOrder104810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda =
      piLeftUnsolvedOrder104810_t0u1Zero v1 a4 a3 a2 a1 a0 s1 b62 := by
  simp only [piLeftUnsolvedOrder104810,
    piLeftUnsolvedOrder104810_t0u1Zero, ht0, hu1]
  ring

/-- Integer `5`-clearing of the LEFT order-`104` mixin after
the four scalar relations.  Witnesses `m1, τ1, g1, k1` are not
inserted. -/
def piLeftUnsolvedLeftOrder104810 (t0 v1 u1 a3 a2 a1 a0 b62 b4 b3 b2 b1 : R) : R :=
    - (1357905920000 : R) * t0 ^ 8 * a0
    + (1030792151040 : R) * t0 ^ 7 * b1
    + (13287555072000 : R) * t0 ^ 6 * v1 * a0
    - (8461085573120 : R) * t0 ^ 5 * v1 * b1
    - (18897856102400 : R) * t0 ^ 5 * u1 * a0
    - (42278584320000 : R) * t0 ^ 4 * v1 ^ 2 * a0
    + (11252814315520 : R) * t0 ^ 4 * u1 * b1
    - (28991029248000 : R) * t0 ^ 4 * a3 * a1
    - (14495514624000 : R) * t0 ^ 4 * a2 ^ 2
    + (15977278341120 : R) * t0 ^ 4 * a0 * b62
    + (20615843020800 : R) * t0 ^ 3 * v1 ^ 2 * b1
    + (92341796864000 : R) * t0 ^ 3 * v1 * u1 * a0
    - (20615843020800 : R) * t0 ^ 3 * a3 * b2
    - (30923764531200 : R) * t0 ^ 3 * a2 * b3
    - (41231686041600 : R) * t0 ^ 3 * a1 * b4
    - (8246337208320 : R) * t0 ^ 3 * b62 * b1
    + (47244640256000 : R) * t0 ^ 2 * v1 ^ 3 * a0
    - (39857296506880 : R) * t0 ^ 2 * v1 * u1 * b1
    + (120259084288000 : R) * t0 ^ 2 * v1 * a3 * a1
    + (60129542144000 : R) * t0 ^ 2 * v1 * a2 ^ 2
    - (67345087201280 : R) * t0 ^ 2 * v1 * a0 * b62
    - (51539607552000 : R) * t0 ^ 2 * u1 ^ 2 * a0
    - (13743895347200 : R) * t0 * v1 ^ 3 * b1
    - (85899345920000 : R) * t0 * v1 ^ 2 * u1 * a0
    + (54975581388800 : R) * t0 * v1 * a3 * b2
    + (82463372083200 : R) * t0 * v1 * a2 * b3
    + (109951162777600 : R) * t0 * v1 * a1 * b4
    + (21990232555520 : R) * t0 * v1 * b62 * b1
    + (19241453486080 : R) * t0 * u1 ^ 2 * b1
    - (137438953472000 : R) * t0 * u1 * a3 * a1
    - (68719476736000 : R) * t0 * u1 * a2 ^ 2
    + (60473139527680 : R) * t0 * u1 * a0 * b62
    - (12884901888000 : R) * v1 ^ 4 * a0
    + (16492674416640 : R) * v1 ^ 2 * u1 * b1
    - (68719476736000 : R) * v1 ^ 2 * a3 * a1
    - (34359738368000 : R) * v1 ^ 2 * a2 ^ 2
    + (43980465111040 : R) * v1 ^ 2 * a0 * b62
    + (34359738368000 : R) * v1 * u1 ^ 2 * a0
    - (43980465111040 : R) * u1 * a3 * b2
    - (65970697666560 : R) * u1 * a2 * b3
    - (87960930222080 : R) * u1 * a1 * b4
    - (17592186044416 : R) * u1 * b62 * b1
    + (137438953472000 : R) * a3 ^ 2 * a2
    + (87960930222080 : R) * a3 * a1 * b62
    + (43980465111040 : R) * a2 ^ 2 * b62
    - (17592186044416 : R) * a0 * b62 ^ 2

/-- Integer `5`-clearing of the RIGHT/`u1 = 0` order-`104`
mixin after the four scalar relations. -/
def piLeftUnsolvedRightU1ZeroOrder104810 (v1 a3 a2 a1 a0 b62 : R) : R :=
    - (12884901888000 : R) * v1 ^ 4 * a0
    - (68719476736000 : R) * v1 ^ 2 * a3 * a1
    - (34359738368000 : R) * v1 ^ 2 * a2 ^ 2
    + (43980465111040 : R) * v1 ^ 2 * a0 * b62
    + (137438953472000 : R) * a3 ^ 2 * a2
    + (87960930222080 : R) * a3 * a1 * b62
    + (43980465111040 : R) * a2 ^ 2 * b62
    - (17592186044416 : R) * a0 * b62 ^ 2

/-- Cofactor of `16 b62 - 5 v1²` in the cleared RIGHT/`u1 = 0`
order-`104` mixin. -/
def piLeftUnsolvedRightU1ZeroOrder104B62Cofactor810
    (v1 a3 a2 a1 a0 b62 : R) : R :=
    (615726511554560 : R) * v1 ^ 2 * a0
    + (1407374883553280 : R) * a3 * a1
    + (703687441776640 : R) * a2 ^ 2
    - (281474976710656 : R) * a0 * b62

set_option maxHeartbeats 400000000 in
/-- Fifteenth-face extra `16 b62 = 5 v1²` specializes the RIGHT/`u1 = 0`
order-`104` mixin. -/
theorem piLeftUnsolvedRightU1ZeroOrder104810_b62Law
    (v1 a3 a2 a1 a0 b62 : R) :
    (256 : R) * piLeftUnsolvedRightU1ZeroOrder104810 v1 a3 a2 a1 a0 b62 =
      ((16 : R) * b62 - (5 : R) * v1 ^ 2) *
          piLeftUnsolvedRightU1ZeroOrder104B62Cofactor810
            v1 a3 a2 a1 a0 b62 +
        - (219902325555200 : R) * v1 ^ 4 * a0
        - (10555311626649600 : R) * v1 ^ 2 * a3 * a1
        - (5277655813324800 : R) * v1 ^ 2 * a2 ^ 2
        + (35184372088832000 : R) * a3 ^ 2 * a2 := by
  simp only [piLeftUnsolvedRightU1ZeroOrder104810,
    piLeftUnsolvedRightU1ZeroOrder104B62Cofactor810]
  ring

/-- Frozen order-`104` mixin on the RIGHT complement scalar locus. -/
def piLeftUnsolvedRightComplementOrder104810
    (v1 u1 a3 a2 a1 a0 b4 b3 b2 b1 : R) : R :=
    (1546188226560 : R) * v1 ^ 4 * a0
    + (1099511627776 : R) * v1 ^ 2 * u1 * b1
    - (2748779069440 : R) * v1 ^ 2 * a3 * a1
    - (1374389534720 : R) * v1 ^ 2 * a2 ^ 2
    + (6871947673600 : R) * v1 * u1 ^ 2 * a0
    - (8796093022208 : R) * u1 * a3 * b2
    - (13194139533312 : R) * u1 * a2 * b3
    - (17592186044416 : R) * u1 * a1 * b4
    + (27487790694400 : R) * a3 ^ 2 * a2

/-- Cofactor of `2 u1² + v1³` in the cleared complement mixin. -/
def piLeftUnsolvedRightComplementOrder104U1Cofactor810
    (v1 u1 a3 a2 a1 a0 b4 b3 b2 b1 : R) : R :=
    (13743895347200 : R) * v1 * a0

set_option maxHeartbeats 400000000 in
/-- Fifteenth-face extra `2 u1² + v1³ = 0` specializes the complement
order-`104` mixin. -/
theorem piLeftUnsolvedRightComplementOrder104810_u1rel
    (v1 u1 a3 a2 a1 a0 b4 b3 b2 b1 : R) :
    (4 : R) * piLeftUnsolvedRightComplementOrder104810 v1 u1 a3 a2 a1 a0 b4 b3 b2 b1 =
      ((2 : R) * u1 ^ 2 + v1 ^ 3) *
          piLeftUnsolvedRightComplementOrder104U1Cofactor810
            v1 u1 a3 a2 a1 a0 b4 b3 b2 b1 +
        - (7559142440960 : R) * v1 ^ 4 * a0
        + (4398046511104 : R) * v1 ^ 2 * u1 * b1
        - (10995116277760 : R) * v1 ^ 2 * a3 * a1
        - (5497558138880 : R) * v1 ^ 2 * a2 ^ 2
        - (35184372088832 : R) * u1 * a3 * b2
        - (52776558133248 : R) * u1 * a2 * b3
        - (70368744177664 : R) * u1 * a1 * b4
        + (109951162777600 : R) * a3 ^ 2 * a2 := by
  simp only [piLeftUnsolvedRightComplementOrder104810,
    piLeftUnsolvedRightComplementOrder104U1Cofactor810]
  ring

end PiOrder104Frozen810

section PiOrder104Map810

variable {R S : Type*} [CommRing R] [CommRing S]

set_option maxHeartbeats 800000000 in
theorem map_piLeftUnsolvedOrder104810 (phi : R →+* S)
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    phi (piLeftUnsolvedOrder104810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda) =
      piLeftUnsolvedOrder104810 (phi t0) (phi v1) (phi u1) (phi a4)
        (phi a3) (phi a2) (phi a1) (phi a0) (phi s1) (phi w1)
        (phi b62) (phi b5) (phi b4) (phi b3) (phi b2) (phi b1)
        (phi lambda) := by
  simp only [piLeftUnsolvedOrder104810, map_add, map_sub, map_mul,
    map_pow, map_neg, map_ofNat, map_zero]

#print axioms map_piLeftUnsolvedOrder104810

end PiOrder104Map810

section PiOrder104Eval810

variable {k : Type*} [CommRing k]

theorem piLeftUnsolvedOrder104810_eval
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 : k[X])
    (lambda a : k) :
    (piLeftUnsolvedOrder104810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a =
      piLeftUnsolvedOrder104810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda := by
  simpa [Polynomial.eval_C] using
    map_piLeftUnsolvedOrder104810 (Polynomial.evalRingHom a) t0 v1 u1 a4
      a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)

#print axioms piLeftUnsolvedOrder104810_eval

end PiOrder104Eval810
section PiOrder104Source810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 800000000 in
/-- Remaining power vanishing after the unsolved order-`103` residual is
peeled.  Witnesses stay unsolved.  The `h0`-divisibilities are the
shape the ceiling lemma consumes. -/
theorem piLeftUnsolvedOrder104810_zero_of_power
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 : k[X])
    (lambda eta a : k) (hh : h ≠ 0) (hdegree : h.natDegree = 1)
    (hroot : h.eval a = 0)
    (hpower :
      localClearedSixteenthDefect810
          h (h ^ 6 * t0) (h ^ 4 * v1) (h ^ 2 * u1)
          a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1)
          (h ^ 2 * b62) b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 112) :
    ∃ (o96n o97n o98n o99n o100n o101n o102n o103n : k[X]),
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
        o98n +
            piLeftUnsolvedOrder99810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o99n ∧
        o99n +
            piLeftUnsolvedOrder100810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o100n ∧
        o100n +
            piLeftUnsolvedOrder101810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o101n ∧
        o101n +
            piLeftUnsolvedOrder102810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o102n ∧
        o102n +
            piLeftUnsolvedOrder103810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o103n ∧
        o103n.eval a +
            piLeftUnsolvedOrder104810 (t0.eval a) (v1.eval a)
              (u1.eval a) (a4.eval a) (a3.eval a) (a2.eval a)
              (a1.eval a) (a0.eval a) (s1.eval a) (w1.eval a)
              (b62.eval a) (b5.eval a) (b4.eval a) (b3.eval a)
              (b2.eval a) (b1.eval a) lambda = 0 := by
  obtain ⟨o96n, o97n, o98n, o99n, o100n, o101n, o102n, ho, ho97, ho98, ho99, ho100, ho101, ho102, hmix⟩ :=
    piLeftUnsolvedOrder103810_zero_of_power h t0 v1 u1 a4 a3 a2 a1 a0 s1
      w1 b62 b5 b4 b3 b2 b1 lambda eta a hh hdegree hroot hpower
  have hsum0 :
      (o102n +
          piLeftUnsolvedOrder103810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a = 0 := by
    rw [Polynomial.eval_add, piLeftUnsolvedOrder103810_eval]
    exact hmix
  obtain ⟨o103n, ho103⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h
      (o102n +
        piLeftUnsolvedOrder103810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda))
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
  have hplus12 :
      o99n +
          piLeftUnsolvedOrder99Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 12 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o99n +
            piLeftUnsolvedOrder99Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o98n +
            piLeftUnsolvedOrder99810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder99Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho99]
        ring
      _ = o98n +
            piLeftUnsolvedOrder98Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedOrder98Plus810_of_order99]
        ring
      _ = Polynomial.C eta * h ^ 13 := hplus13
      _ = h * (Polynomial.C eta * h ^ 12) := by ring
  have hplus11 :
      o100n +
          piLeftUnsolvedOrder100Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 11 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o100n +
            piLeftUnsolvedOrder100Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o99n +
            piLeftUnsolvedOrder100810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder100Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho100]
        ring
      _ = o99n +
            piLeftUnsolvedOrder99Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedOrder99Plus810_of_order100]
        ring
      _ = Polynomial.C eta * h ^ 12 := hplus12
      _ = h * (Polynomial.C eta * h ^ 11) := by ring
  have hplus10 :
      o101n +
          piLeftUnsolvedOrder101Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 10 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o101n +
            piLeftUnsolvedOrder101Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o100n +
            piLeftUnsolvedOrder101810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder101Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho101]
        ring
      _ = o100n +
            piLeftUnsolvedOrder100Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedOrder100Plus810_of_order101]
        ring
      _ = Polynomial.C eta * h ^ 11 := hplus11
      _ = h * (Polynomial.C eta * h ^ 10) := by ring
  have hplus9 :
      o102n +
          piLeftUnsolvedOrder102Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 9 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o102n +
            piLeftUnsolvedOrder102Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o101n +
            piLeftUnsolvedOrder102810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder102Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho102]
        ring
      _ = o101n +
            piLeftUnsolvedOrder101Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedOrder101Plus810_of_order102]
        ring
      _ = Polynomial.C eta * h ^ 10 := hplus10
      _ = h * (Polynomial.C eta * h ^ 9) := by ring
  have hplus8 :
      o103n +
          piLeftUnsolvedOrder103Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 8 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o103n +
            piLeftUnsolvedOrder103Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o102n +
            piLeftUnsolvedOrder103810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder103Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho103]
        ring
      _ = o102n +
            piLeftUnsolvedOrder102Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedOrder102Plus810_of_order103]
        ring
      _ = Polynomial.C eta * h ^ 9 := hplus9
      _ = h * (Polynomial.C eta * h ^ 8) := by ring
  have htail :
      (piLeftUnsolvedOrder103Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
          b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a =
        (piLeftUnsolvedOrder104810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
          b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a := by
    rw [piLeftUnsolvedOrder103Plus810_of_order104]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, hroot,
      zero_mul, add_zero]
  refine ⟨o96n, o97n, o98n, o99n, o100n, o101n, o102n, o103n, ho, ho97, ho98, ho99, ho100, ho101, ho102, ho103, ?_⟩
  have hev := congrArg (Polynomial.eval a) hplus8
  rw [← piLeftUnsolvedOrder104810_eval, ← htail]
  simpa [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, hroot] using hev

set_option maxHeartbeats 800000000 in
/-- Source-facing order-`104` peel from a literal `(8,10)` source. -/
theorem piLeftUnsolvedOrder104810_zero_of_source
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
    ∃ (o96n o97n o98n o99n o100n o101n o102n o103n : k[X]),
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
        o98n +
            piLeftUnsolvedOrder99810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o99n ∧
        o99n +
            piLeftUnsolvedOrder100810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o100n ∧
        o100n +
            piLeftUnsolvedOrder101810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o101n ∧
        o101n +
            piLeftUnsolvedOrder102810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o102n ∧
        o102n +
            piLeftUnsolvedOrder103810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o103n ∧
        o103n.eval a +
            piLeftUnsolvedOrder104810 (t0.eval a) (v1.eval a)
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
  exact piLeftUnsolvedOrder104810_zero_of_power h0 t0 v1 u1
    (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1
    b62 (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
    lambda (17592186044416 * eta) a hh0 hdegree hroot hpower

set_option maxHeartbeats 800000000 in
/-- Source-facing order-`104` chambers.  Witnesses stay unsolved.  The
fifteenth-face extras are carried from the parent.  This is not a
closure. -/
theorem piFace810_linearRoot_order104Chambers
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
    ∃ (t0 v0 u0 s0 w0 v1 s1 u1 w1 b62 o96n o97n o98n o99n o100n o101n o102n o103n : k[X]),
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
        o98n +
            piLeftUnsolvedOrder99810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o99n ∧
        o99n +
            piLeftUnsolvedOrder100810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o100n ∧
        o100n +
            piLeftUnsolvedOrder101810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o101n ∧
        o101n +
            piLeftUnsolvedOrder102810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o102n ∧
        o102n +
            piLeftUnsolvedOrder103810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o103n ∧
        o103n.eval a +
            piLeftUnsolvedOrder104810 (t0.eval a) (v1.eval a)
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
  obtain ⟨t0, v0, u0, s0, w0, v1, s1, u1, w1, b62, o96n, o97n, o98n, o99n, o100n, o101n, o102n, ht0, hv0, hu0, hs0, hw0, hv1, hs1, hu1, hw1, hb62, ho96, ho97, ho98, ho99, ho100, ho101, ho102, hmix103, hsplit⟩ :=
    piFace810_linearRoot_order103Chambers p q H h0 j lambda a hp hq
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
  obtain ⟨o96n', o97n', o98n', o99n', o100n', o101n', o102n', o103n, ho', ho97', ho98', ho99', ho100', ho101', ho102', ho103, hmix104⟩ :=
    piLeftUnsolvedOrder104810_zero_of_source p q H h0 j lambda a t0 v1
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
  have ho98eq : o98n = o98n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o98n = o97n +
          piLeftUnsolvedOrder98810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) := ho98.symm
      _ = h0 * o98n' := ho98'
  subst ho98eq
  have ho99eq : o99n = o99n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o99n = o98n +
          piLeftUnsolvedOrder99810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) := ho99.symm
      _ = h0 * o99n' := ho99'
  subst ho99eq
  have ho100eq : o100n = o100n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o100n = o99n +
          piLeftUnsolvedOrder100810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) := ho100.symm
      _ = h0 * o100n' := ho100'
  subst ho100eq
  have ho101eq : o101n = o101n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o101n = o100n +
          piLeftUnsolvedOrder101810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) := ho101.symm
      _ = h0 * o101n' := ho101'
  subst ho101eq
  have ho102eq : o102n = o102n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o102n = o101n +
          piLeftUnsolvedOrder102810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) := ho102.symm
      _ = h0 * o102n' := ho102'
  subst ho102eq
  refine ⟨t0, v0, u0, s0, w0, v1, s1, u1, w1, b62, o96n, o97n, o98n, o99n, o100n, o101n, o102n, o103n,
    ht0, hv0, hu0, hs0, hw0, hv1, hs1, hu1, hw1, hb62, ho96, ho97, ho98, ho99, ho100, ho101, ho102, ho103, hmix104, ?_⟩
  exact hsplit

#print axioms piLeftUnsolvedOrder103Plus810_of_order104
#print axioms piLeftUnsolvedOrder104810_of_t0u1Zero
#print axioms piLeftUnsolvedOrder104810_zero_of_power
#print axioms piLeftUnsolvedOrder104810_zero_of_source
#print axioms piFace810_linearRoot_order104Chambers
#print axioms piLeftUnsolvedRightU1ZeroOrder104810_b62Law
#print axioms piLeftUnsolvedRightComplementOrder104810_u1rel

end PiOrder104Source810

end Max11DegreeRoutes
