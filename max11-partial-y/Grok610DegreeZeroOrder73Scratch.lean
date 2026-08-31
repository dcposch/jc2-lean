import Grok610DegreeZeroOrder72Scratch

/-! # Order-`73` continuation of the `(6,10)` degree-zero post-collapse tower

`Grok610DegreeZeroOrder72Scratch` leaves four live arms:

* `(a)` the forty-six-term order-`72` hypersurface on
  `p32(a) = p21(a) = p1(a) = 0`;
* `(b)` the mixed `o71n + OrderThree` relation on `p32(a) = p21(a) = 0`
  with the nine-term order-`71` cofactor;
* `(c)` the eight-term order-`71` residual on
  `p32(a) = q41(a) = q3(a) = 0`, already split at `p21(a) = 0` into
  `p1(a) = 0` or `q53(a) = 0`, together with the sixty-two-term
  order-`72` mixin;
* `(d)` the eight-term `q41n`-linear residual on `p32(a) ≠ 0`.

The jet quotient has `h`-degree at most `6`, so frozen heads run through
order `75`.  This file extracts the order-`73` (`h^4`) coefficient on
`(a)(b)(c)` and the mixed order-`71` (`h^2`) object on `(d)`, and applies
the simple-pole obstruction.

On `(a)` the forty-six-term hypersurface peels as `h0 · o72n`; pole-two
forces `o72n(a)` plus the frozen order-`73` mixin to vanish, so the
hypersurface condition lives on its first Taylor coefficient.  On `(b)`
the same peel is applied to `o71n + OrderThree`.  On `(c)` both
subpackets are pushed: `p21 = p1 = 0` kills the sixty-two-term mixin
identically, while `p21 = q53 = 0` splits that mixin as `p1` times a
thirteen-term cofactor.  On `(d)` the mixed order-`70` head peels and
pole-four forces the mixed order-`71` object; `q41n` is expanded as
`C(q41n(a)) + h0 · q41nn` so the second Taylor of `q41` is named
honestly.

None of these arms is False.  No total-degree or twice-prime theorem is
used, and no chamber is closed.  Cumulative vanishing toward the order-`75`
ceiling is recorded as `h0^M ∣` the jet quotient.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option maxHeartbeats 800000000

section LinearPoleTwo610

variable {k : Type*} [Field k] [CharZero k]

local instance degreeZeroOrder73HahnCharZero610 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-- A rational function cleared by exactly two powers of a linear local
parameter cannot have a nonzero exponent-`-2` head when its derivative is a
simple pole. -/
theorem localLinearPoleTwo_head_eval_zero_of_deriv_eq_simplePole610
    (a j : k) (h0 A0 : k[X]) (rho : RatFunc k)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear : algebraMap k[X] (RatFunc k) A0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 2 * rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    A0.eval a = 0 := by
  obtain ⟨c, hc, hsingle, hscaleDeriv⟩ :=
    ratFuncAtHahn68_linearRoot_single_deriv h0 a hdegree hroot
  have hrhoBoundary := localHahn_coeff_neg_of_cleared a c h0 A0 rho 2 hc
    hsingle hclear
  have hderivBoundary := localHahn_deriv_coeff_neg_succ_of_cleared
    a c h0 A0 rho 2 hc hsingle hscaleDeriv hclear
  have hmapped := congrArg (ratFuncAtHahn46 a) hderiv
  have hminusThree :
      (ratFuncAtHahn46 a (Differential.deriv rho)).coeff (-3 : ℚ) = 0 := by
    have hcoeff := congrArg
      (fun z : HahnSeries ℚ k ↦ z.coeff (-3 : ℚ)) hmapped
    simpa only [div_eq_mul_inv, map_mul, map_inv₀, ratFuncAtHahn46_C,
      hsingle,
      HahnSeries.inv_single, HahnSeries.C_mul_eq_smul,
      HahnSeries.coeff_smul, HahnSeries.coeff_single_of_ne (by norm_num :
        (-3 : ℚ) ≠ -(1 : ℚ)), smul_zero] using hcoeff
  have hrhoZero : (ratFuncAtHahn46 a rho).coeff (-2 : ℚ) = 0 := by
    norm_num at hderivBoundary
    rw [hminusThree] at hderivBoundary
    have htwo : (2 : k) ≠ 0 := by norm_num
    have hprod : (2 : k) * (ratFuncAtHahn46 a rho).coeff (-2 : ℚ) = 0 :=
      neg_eq_zero.mp hderivBoundary.symm
    exact (mul_eq_zero.mp hprod).resolve_left htwo
  norm_num at hrhoBoundary
  rw [hrhoZero] at hrhoBoundary
  have hcinv : (c ^ 2)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero 2 hc)
  exact (mul_eq_zero.mp hrhoBoundary.symm).resolve_left hcinv

end LinearPoleTwo610

section DegreeZeroOrderFourHead610

variable {R : Type*} [CommRing R]

/-- Frozen order-`73` mixin on `p32 = h · p32n`, `p21 = h · p21n`,
`p1 = h · p1n`: the `h^0` part of the order-`72` remainder. -/
def degreeZeroPostCollapseP32P21P1ZeroOrderFour610
    (w1 a42 p32n p21n p1n p0 q53 q2 : R) : R :=
  -24374389600419840*p1n^2*q53-835513869939840*q53*w1^10+666704893870080*q2*w1^7+3251799353327616*a42^5*q53-48748779200839680*p0*p21n*q53-35974284898406400*a42^2*q53*w1^6-33872909930496000*a42^4*q53*w1^2-33872909930496000*p32n^2*q53*w1^4-30806520189419520*a42^2*p32n^2*q53-30806520189419520*p21n^2*q53*w1^2-20537680126279680*a42^3*p21n*q53-20537680126279680*p32n^3*q53*w1-19499511680335872*a42*p1n*q2-19499511680335872*p0*q2*w1-19499511680335872*p21n*p32n*q2-13549163972198400*p1n*q53*w1^5-10278367113830400*p32n*q53*w1^7-8215072050511872*p21n*q2*w1^3-8215072050511872*a42^3*q2*w1-5419665588879360*a42*q2*w1^5+6503598706655232*p32n*q2*w1^4+9207703872806400*a42*q53*w1^8+11374715146862592*p1n*q2*w1^2+11374715146862592*a42^2*p32n*q2+11374715146862592*p32n^2*q2*w1+11667335642726400*p21n*q53*w1^6+13007197413310464*a42^2*q2*w1^3+16258996766638080*p0*q53*w1^4+28436787867156480*a42*p21n^2*q53+28436787867156480*a42^2*p0*q53+28436787867156480*p21n*p32n^2*q53+58336678213632000*a42^3*q53*w1^4-135491639721984000*a42^2*p32n*q53*w1^3-67745819860992000*a42*p21n*q53*w1^4-61613040378839040*a42*p0*q53*w1^2-61613040378839040*p1n*p32n*q53*w1^2-61613040378839040*a42^2*p1n*q53*w1-24645216151535616*a42*p32n*q2*w1^2+22749430293725184*a42*p21n*q2*w1+56873575734312960*a42*p1n*p32n*q53+56873575734312960*p0*p32n*q53*w1+56873575734312960*p1n*p21n*q53*w1+65035987066552320*a42*p1n*q53*w1^3+65035987066552320*p21n*p32n*q53*w1^3+65035987066552320*a42^3*p32n*q53*w1+70004013856358400*a42*p32n*q53*w1^5+97553980599828480*a42*p32n^2*q53*w1^2+97553980599828480*a42^2*p21n*q53*w1^2-123226080757678080*a42*p21n*p32n*q53*w1

/-- Frozen order-`73` mixin on `p32 = h · p32n`, `p21 = h · p21n`. -/
def degreeZeroPostCollapseP32P21ZeroOrderFour610
    (w1 a42 p32n p21n p1 p0 s2 u2 b63 q53 q2 q1 lambda : R) : R :=
  -31614715935129600*p1^2*w1^5-835513869939840*q53*w1^10+666704893870080*q2*w1^7+3251799353327616*a42^5*q53-123226080757678080*a42*p1^2*p32n-58498535041007616*b63*p0*p1-48748779200839680*p0*p21n*q53-37915717156208640*p1^2*p21n*w1-35974284898406400*a42^2*q53*w1^6-33872909930496000*a42^4*q53*w1^2-33872909930496000*p32n^2*q53*w1^4-30806520189419520*a42^2*p32n^2*q53-30806520189419520*p21n^2*q53*w1^2-24645216151535616*a42^3*b63*p1-20537680126279680*a42^3*p21n*q53-20537680126279680*p32n^3*q53*w1-19499511680335872*p0*q2*w1-19499511680335872*p21n*p32n*q2-17062072720293888*lambda*p1^2*p21n-14389713959362560*p1*u2*w1^7-10278367113830400*p32n*q53*w1^7-9749755840167936*p1*q1*w1-8215072050511872*p21n*q2*w1^3-8215072050511872*a42^3*q2*w1-5419665588879360*a42*q2*w1^5+6503598706655232*p32n*q2*w1^4+9207703872806400*a42*q53*w1^8+10268840063139840*p1^2*p32n*w1^2+11374715146862592*a42^2*p32n*q2+11374715146862592*p32n^2*q2*w1+11667335642726400*p21n*q53*w1^6+13007197413310464*a42^2*q2*w1^3+14000802771271680*b63*p1*w1^6+16258996766638080*p0*q53*w1^4+18483912113651712*a42^2*lambda*p1^2+20323745958297600*lambda*p1^2*w1^4+21678662355517440*a42*p1^2*w1^3+28436787867156480*a42*p21n^2*q53+28436787867156480*a42^2*p0*q53+28436787867156480*p21n*p32n^2*q53+34124145440587776*b63*p1*p32n^2+45498860587450368*p1^2*p32n*s2+52028789653241856*p1^2*s2*w1^3+58336678213632000*a42^3*q53*w1^4+102688400631398400*a42^2*p1^2*w1-189688295610777600*a42^2*p1*u2*w1^3-135491639721984000*a42^2*p32n*q53*w1^3-98580864606142464*a42*p1^2*s2*w1-94844147805388800*p1*p32n*u2*w1^4-86258256530374656*a42^2*p1*p32n*u2-86258256530374656*p1*p32n^2*u2*w1-81294983833190400*a42*b63*p1*w1^4-73935648454606848*b63*p1*p21n*w1^2-67745819860992000*a42*p21n*q53*w1^4-61613040378839040*a42*p0*q53*w1^2-58532388359897088*a42*lambda*p1^2*w1^2-24645216151535616*a42*p32n*q2*w1^2+22749430293725184*a42*p21n*q2*w1+36967824227303424*lambda*p1^2*p32n*w1+56873575734312960*p0*p32n*q53*w1+65035987066552320*p21n*p32n*q53*w1^3+65035987066552320*a42^3*p32n*q53*w1+68248290881175552*a42*b63*p1*p21n+70004013856358400*a42*p32n*q53*w1^5+78043184479862784*b63*p1*p32n*w1^3+79623006028038144*p0*p1*u2*w1+79623006028038144*p1*p21n*p32n*u2+91050381893173248*p1*p21n*u2*w1^3+91050381893173248*a42^3*p1*u2*w1+97553980599828480*a42*p32n^2*q53*w1^2+97553980599828480*a42^2*p21n*q53*w1^2+98005619398901760*a42*p1*u2*w1^5+117064776719794176*a42^2*b63*p1*w1^2-172516513060749312*a42*p1*p21n*u2*w1-147871296909213696*a42*b63*p1*p32n*w1-123226080757678080*a42*p21n*p32n*q53*w1+273151145679519744*a42*p1*p32n*u2*w1^2

/-- Frozen order-`73` mixin on `p32 = h · p32n`, `q41 = h · q41n`,
`q3 = h · q3n`. -/
def degreeZeroPostCollapseP32Q41Q3ZeroOrderFour610
    (w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda : R) : R :=
  -34261223712768000*p21^2*w1^7-31614715935129600*p1^2*w1^5-3080652018941952*a42^4*q3n-835513869939840*q53*w1^10-770877533537280*q3n*w1^8+666704893870080*q2*w1^7+818462566471680*q41n*w1^9+3251799353327616*a42^5*q53+7583143431241728*p32n^3*q41n-173429298844139520*a42^3*p21^2*w1-123226080757678080*a42*p1^2*p32n-123226080757678080*p1*p21*p32n^2-58498535041007616*b63*p0*p1-56454849884160000*p21^2*p32n*w1^4-38999023360671744*p0*p32n*q41n-37915717156208640*p0*p21^2*w1-36131103925862400*a42^3*q41n*w1^3-35974284898406400*a42^2*q53*w1^6-33872909930496000*a42^4*q53*w1^2-33872909930496000*p32n^2*q53*w1^4-30806520189419520*a42^2*p32n^2*q53-29249267520503808*a42*p0*q3n-24645216151535616*a42^3*b63*p1-20537680126279680*p32n^3*q53*w1-20323745958297600*a42^2*q3n*w1^4-19510796119965696*a42^3*lambda*p21^2-19499511680335872*p0*q2*w1-18483912113651712*p32n^2*q3n*w1^2-17062072720293888*lambda*p0*p21^2-16430144101023744*p0*q41n*w1^3-16430144101023744*a42^3*p32n*q41n-14389713959362560*p1*u2*w1^7-12334040536596480*b63*p21*w1^7-10278367113830400*p32n*q53*w1^7-9749755840167936*a42*p21*q1-9749755840167936*p1*q1*w1-8222693691064320*a42*q41n*w1^7-8215072050511872*a42^3*q2*w1-8129498383319040*p32n*q3n*w1^5-5419665588879360*a42*q2*w1^5+5687357573431296*p21*q1*w1^2+6503598706655232*p32n*q2*w1^4+7000401385635840*a42*q3n*w1^6+9207703872806400*a42*q53*w1^8+9333868514181120*p32n*q41n*w1^6+10268840063139840*p1^2*p32n*w1^2+11374715146862592*a42^2*p32n*q2+11374715146862592*p32n^2*q2*w1+12890785421928960*p21*u2*w1^8+13007197413310464*a42^2*q2*w1^3+13007197413310464*a42^4*q41n*w1+14000802771271680*b63*p1*w1^6+16258996766638080*p0*q53*w1^4+17062072720293888*a42*p32n^2*q3n+17062072720293888*p0*q3n*w1^2+18483912113651712*a42^2*lambda*p1^2+18483912113651712*lambda*p21^2*p32n^2+19510796119965696*a42^3*q3n*w1^2+20323745958297600*lambda*p1^2*w1^4+21584570939043840*lambda*p21^2*w1^6+21678662355517440*a42*p1^2*w1^3+22762595473293312*a42^4*p21*u2+26014394826620928*p32n^2*q41n*w1^3+28001605542543360*a42^2*q41n*w1^5+28436787867156480*a42^2*p0*q53+34124145440587776*b63*p1*p32n^2+45498860587450368*p1^2*p32n*s2+52028789653241856*p1^2*s2*w1^3+56003211085086720*p21^2*s2*w1^5+58336678213632000*a42^3*q53*w1^4+66114901975449600*p1*p21*w1^6+90327759814656000*a42^2*p21^2*w1^3+93338685141811200*a42*p21^2*w1^5+102688400631398400*a42^2*p1^2*w1+102688400631398400*p21^2*p32n^2*w1+113747151468625920*p0*p1*p21+130071974133104640*a42^3*p1*p21+195107961199656960*a42^2*p21^2*p32n-227625954732933120*a42*p21^2*p32n*w1^2-227625954732933120*a42^2*p1*p21*w1^2-216786623555174400*a42*p21^2*s2*w1^3-189688295610777600*a42^2*p1*u2*w1^3-189688295610777600*a42^3*p21*u2*w1^2-162589967666380800*a42^2*b63*p21*w1^3-135491639721984000*a42^2*p32n*q53*w1^3-112909699768320000*a42*p1*p21*w1^4-108393311777587200*p1*p21*s2*w1^4-105006020784537600*a42*lambda*p21^2*w1^4-100727997715537920*a42*p21*u2*w1^6-98580864606142464*a42*p21^2*p32n*s2-98580864606142464*a42*p1^2*s2*w1-98580864606142464*a42^2*p1*p21*s2-94844147805388800*p1*p32n*u2*w1^4-86258256530374656*a42*p21*p32n^2*u2-86258256530374656*p0*p21*u2*w1^2-86258256530374656*a42^2*p1*p32n*u2-86258256530374656*p1*p32n^2*u2*w1-81294983833190400*a42*b63*p1*w1^4-81294983833190400*b63*p21*p32n*w1^4-73935648454606848*a42^2*b63*p21*p32n-73935648454606848*b63*p21*p32n^2*w1-61613040378839040*a42*p0*q53*w1^2-58532388359897088*a42*lambda*p1^2*w1^2-54196655888793600*a42*p32n*q41n*w1^4-49290432303071232*a42*p32n^2*q41n*w1-42002408313815040*lambda*p1*p21*w1^5-36967824227303424*a42^2*p32n*q3n*w1-24645216151535616*a42*p32n*q2*w1^2+36967824227303424*lambda*p1^2*p32n*w1+39021592239931392*a42*p32n*q3n*w1^3+43357324711034880*p1*p21*p32n*w1^3+45498860587450368*a42*p0*q41n*w1+56873575734312960*p0*p32n*q53*w1+65035987066552320*a42^3*p32n*q53*w1+68248290881175552*b63*p0*p21*w1+70004013856358400*a42*p32n*q53*w1^5+78043184479862784*b63*p1*p32n*w1^3+78043184479862784*a42^3*b63*p21*w1+78043184479862784*a42^2*p32n*q41n*w1^2+79623006028038144*a42*p0*p21*u2+79623006028038144*p0*p1*u2*w1+81294983833190400*lambda*p21^2*p32n*w1^3+84004816627630080*a42*b63*p21*w1^5+91050381893173248*a42^3*p1*u2*w1+97553980599828480*a42*p32n^2*q53*w1^2+98005619398901760*a42*p1*u2*w1^5+98005619398901760*p21*p32n*u2*w1^5+117064776719794176*a42^2*b63*p1*w1^2+121942475749785600*a42^2*lambda*p21^2*w1^2+136575572839759872*p21*p32n^2*u2*w1^2+156086368959725568*p21^2*p32n*s2*w1^2+156086368959725568*a42^2*p21^2*s2*w1+245014048497254400*a42^2*p21*u2*w1^4-379376591221555200*a42*p21*p32n*u2*w1^3-197161729212284928*p1*p21*p32n*s2*w1-147871296909213696*a42*b63*p1*p32n*w1-117064776719794176*a42*lambda*p21^2*p32n*w1-117064776719794176*lambda*p1*p21*p32n*w1^2-117064776719794176*a42^2*lambda*p1*p21*w1+73935648454606848*a42*lambda*p1*p21*p32n+162589967666380800*a42*lambda*p1*p21*w1^3+234129553439588352*a42*b63*p21*p32n*w1^2+273151145679519744*a42*p1*p32n*u2*w1^2+273151145679519744*a42^2*p21*p32n*u2*w1+312172737919451136*a42*p1*p21*s2*w1^2+410753602525593600*a42*p1*p21*p32n*w1

/-- Eighteen-term cofactor of the sixty-two-term order-`72` mixin at
`p21 = 0`. -/
def degreeZeroPostCollapseP32Q41Q3P21ZeroOrderThreeHeadCofactor610
    (w1 a42 p32n p1 u2 q53 q41n q3n q2 b63 : R) : R :=
  (72576 : R) * a42 ^ 2 * q41n - 196560 * a42 ^ 2 * q53 * w1 +
    127008 * a42 * p1 * u2 + 181440 * a42 * p32n * q53 -
    62208 * a42 * q2 + 108864 * a42 * q3n * w1 -
    157248 * a42 * q41n * w1 ^ 2 + 207480 * a42 * q53 * w1 ^ 3 +
    108864 * b63 * p1 * w1 + 60480 * p1 ^ 2 -
    137592 * p1 * u2 * w1 ^ 2 - 93312 * p32n * q3n +
    145152 * p32n * q41n * w1 - 196560 * p32n * q53 * w1 ^ 2 +
    36288 * q2 * w1 ^ 2 - 39312 * q3n * w1 ^ 3 +
    41496 * q41n * w1 ^ 4 - 43225 * q53 * w1 ^ 5

/-- Thirteen-term cofactor of the sixty-two-term order-`72` mixin at
`p21 = q53 = 0`. -/
def degreeZeroPostCollapseP32Q41Q3P21Q53ZeroOrderThreeHeadCofactor610
    (w1 a42 p32n p1 u2 q41n q3n q2 b63 : R) : R :=
  (3024 : R) * a42 ^ 2 * q41n + 5292 * a42 * p1 * u2 -
    2592 * a42 * q2 + 4536 * a42 * q3n * w1 -
    6552 * a42 * q41n * w1 ^ 2 + 4536 * b63 * p1 * w1 +
    2520 * p1 ^ 2 - 5733 * p1 * u2 * w1 ^ 2 -
    3888 * p32n * q3n + 6048 * p32n * q41n * w1 +
    1512 * q2 * w1 ^ 2 - 1638 * q3n * w1 ^ 3 +
    1729 * q41n * w1 ^ 4

/-- Mixed order-`71` head on `q41 = h · q41n`: the seven-term Taylor of
`OrderOne` plus the frozen `h^2` coefficient at `q41 = 0`. -/
def degreeZeroPostCollapseQ41ZeroMixedOrderTwo610
    (w1 a42 p32 p21 p1 s2 u2 b63 q53 q41n q3 q2 lambda : R) : R :=
  -41075360252559360*p21^3*p32-24374389600419840*p1^2*q53+13270501004673024*p21^3*u2+15054626635776000*p32^4*w1^3-123226080757678080*p1*p21*p32^2-86714649422069760*a42*p32^4*w1-75875318244311040*p21*p32^3*w1^2-63229431870259200*p32^3*u2*w1^3-38999023360671744*p1*p21*q41n-33872909930496000*p32^2*q53*w1^4-32860288202047488*p21*p32^3*s2-30806520189419520*a42^2*p32^2*q53-30806520189419520*p21^2*q53*w1^2-24645216151535616*a42*b63*p32^3-19499511680335872*p21*p32*q2-12322608075767808*p1*q3*w1^3-9755398059982848*a42*lambda*p32^4-8129498383319040*p32*q3*w1^5+9755398059982848*p21*q3*w1^4+11374715146862592*p32^2*q2*w1+12322608075767808*lambda*p1*p32^3+17062072720293888*a42^2*p21*q3+18483912113651712*lambda*p21^2*p32^2+20323745958297600*lambda*p32^4*w1^2+22749430293725184*p21^2*q41n*w1+26014394826620928*p32^2*q41n*w1^3+26014394826620928*p32^4*s2*w1+28436787867156480*a42*p21^2*q53+34124145440587776*b63*p1*p32^2+34124145440587776*b63*p21^2*p32+39021592239931392*b63*p32^3*w1^2+68458933754265600*p1*p32^3*w1+102688400631398400*p21^2*p32^2*w1+130071974133104640*a42*p21*p32^3-86258256530374656*a42*p21*p32^2*u2-86258256530374656*p1*p32^2*u2*w1-86258256530374656*p21^2*p32*u2*w1-73935648454606848*b63*p21*p32^2*w1-61613040378839040*p1*p32*q53*w1^2-49290432303071232*a42*p32^2*q41n*w1-49290432303071232*p21*p32*q41n*w1^2-39021592239931392*lambda*p21*p32^3*w1-36967824227303424*a42*p21*q3*w1^2-36967824227303424*a42^2*p32*q3*w1+34124145440587776*a42*p1*q3*w1+39021592239931392*a42*p32*q3*w1^3+45498860587450368*a42*p21*p32*q41n+45498860587450368*p1*p32*q41n*w1+56873575734312960*a42*p1*p32*q53+56873575734312960*p1*p21*q53*w1+65035987066552320*p21*p32*q53*w1^3+79623006028038144*p1*p21*p32*u2+91050381893173248*a42*p32^3*u2*w1+97553980599828480*a42*p32^2*q53*w1^2+136575572839759872*p21*p32^2*u2*w1^2-123226080757678080*a42*p21*p32*q53*w1

set_option maxHeartbeats 800000000 in
theorem degreeZeroPostCollapseP32P21P1ZeroOrderThreePlus610_zero
    (w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda : R) :
    degreeZeroPostCollapseP32P21P1ZeroOrderThreePlus610 0 w1 a42 p32n
        p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda =
      degreeZeroPostCollapseP32P21P1ZeroOrderFour610 w1 a42 p32n p21n
        p1n p0 q53 q2 := by
  simp only [degreeZeroPostCollapseP32P21P1ZeroOrderThreePlus610,
    degreeZeroPostCollapseP32P21P1ZeroOrderFour610, zero_mul, mul_zero,
    zero_pow, Nat.ofNat_pos, add_zero, sub_zero]
  ring

set_option maxHeartbeats 800000000 in
theorem degreeZeroPostCollapseP32P21ZeroOrderThreePlus610_zero
    (w1 a42 p32n p21n p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda : R) :
    degreeZeroPostCollapseP32P21ZeroOrderThreePlus610 0 w1 a42 p32n p21n
        p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda =
      degreeZeroPostCollapseP32P21ZeroOrderFour610 w1 a42 p32n p21n p1
        p0 s2 u2 b63 q53 q2 q1 lambda := by
  simp only [degreeZeroPostCollapseP32P21ZeroOrderThreePlus610,
    degreeZeroPostCollapseP32P21ZeroOrderFour610, zero_mul, mul_zero,
    zero_pow, Nat.ofNat_pos, add_zero, sub_zero]
  ring

set_option maxHeartbeats 800000000 in
theorem degreeZeroPostCollapseP32Q41Q3ZeroOrderThreePlus610_zero
    (w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda : R) :
    degreeZeroPostCollapseP32Q41Q3ZeroOrderThreePlus610 0 w1 a42 p32n
        p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda =
      degreeZeroPostCollapseP32Q41Q3ZeroOrderFour610 w1 a42 p32n p21 p1
        p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda := by
  simp only [degreeZeroPostCollapseP32Q41Q3ZeroOrderThreePlus610,
    degreeZeroPostCollapseP32Q41Q3ZeroOrderFour610, zero_mul, mul_zero,
    zero_pow, Nat.ofNat_pos, add_zero, sub_zero]
  ring

set_option maxHeartbeats 4000000 in
theorem degreeZeroPostCollapseP32Q41Q3ZeroOrderThreeHead610_p21Zero
    (w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 lambda : R)
    (hp21 : p21 = 0) :
    degreeZeroPostCollapseP32Q41Q3ZeroOrderThreeHead610 w1 a42 p32n p21
        p1 p0 s2 u2 b63 q53 q41n q3n q2 lambda =
      (313456656384 : R) * p1 *
        degreeZeroPostCollapseP32Q41Q3P21ZeroOrderThreeHeadCofactor610
          w1 a42 p32n p1 u2 q53 q41n q3n q2 b63 := by
  simp only [degreeZeroPostCollapseP32Q41Q3ZeroOrderThreeHead610,
    degreeZeroPostCollapseP32Q41Q3P21ZeroOrderThreeHeadCofactor610,
    hp21]
  ring

set_option maxHeartbeats 4000000 in
theorem degreeZeroPostCollapseP32Q41Q3ZeroOrderThreeHead610_p21Q53Zero
    (w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 lambda : R)
    (hp21 : p21 = 0) (hq53 : q53 = 0) :
    degreeZeroPostCollapseP32Q41Q3ZeroOrderThreeHead610 w1 a42 p32n p21
        p1 p0 s2 u2 b63 q53 q41n q3n q2 lambda =
      (7522959753216 : R) * p1 *
        degreeZeroPostCollapseP32Q41Q3P21Q53ZeroOrderThreeHeadCofactor610
          w1 a42 p32n p1 u2 q41n q3n q2 b63 := by
  simp only [degreeZeroPostCollapseP32Q41Q3ZeroOrderThreeHead610,
    degreeZeroPostCollapseP32Q41Q3P21Q53ZeroOrderThreeHeadCofactor610,
    hp21, hq53]
  ring

set_option maxHeartbeats 4000000 in
theorem degreeZeroPostCollapseP32Q41Q3ZeroOrderThreeHead610_p21P1Zero
    (w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 lambda : R)
    (hp21 : p21 = 0) (hp1 : p1 = 0) :
    degreeZeroPostCollapseP32Q41Q3ZeroOrderThreeHead610 w1 a42 p32n p21
        p1 p0 s2 u2 b63 q53 q41n q3n q2 lambda = 0 := by
  simp only [degreeZeroPostCollapseP32Q41Q3ZeroOrderThreeHead610, hp21,
    hp1]
  ring

set_option maxHeartbeats 4000000 in
theorem degreeZeroPostCollapseQ41ZeroMixedOrderOne610_q41nLinear
    (w1 a42 p32 p21 p1 q53 q41n q3 u2 : R) :
    degreeZeroPostCollapseQ41ZeroMixedOrderOne610 w1 a42 p32 p21 p1 q53
        q41n q3 u2 =
      degreeZeroPostCollapseQ41ZeroMixedOrderOne610 w1 a42 p32 p21 p1
          q53 0 q3 u2 +
        (7583143431241728 : R) * p32 ^ 3 * q41n := by
  simp only [degreeZeroPostCollapseQ41ZeroMixedOrderOne610]
  ring

set_option maxHeartbeats 800000000 in
theorem degreeZeroPostCollapseQ41ZeroMixedOrderTwo610_of_frozen
    (w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda : R) :
    (45498860587450368 : R) * a42 * p21 * p32 * q41n -
          49290432303071232 * a42 * p32 ^ 2 * q41n * w1 -
          38999023360671744 * p1 * p21 * q41n +
          45498860587450368 * p1 * p32 * q41n * w1 +
          22749430293725184 * p21 ^ 2 * q41n * w1 -
          49290432303071232 * p21 * p32 * q41n * w1 ^ 2 +
          26014394826620928 * p32 ^ 2 * q41n * w1 ^ 3 +
        degreeZeroPostCollapseJetOrderTwoPlus610 0 w1 a42 p32 p21 p1 p0
          s2 u2 b63 q53 0 q3 q2 q1 lambda =
      degreeZeroPostCollapseQ41ZeroMixedOrderTwo610 w1 a42 p32 p21 p1
        s2 u2 b63 q53 q41n q3 q2 lambda := by
  simp only [degreeZeroPostCollapseQ41ZeroMixedOrderTwo610,
    degreeZeroPostCollapseJetOrderTwoPlus610, zero_mul, mul_zero,
    zero_pow, Nat.ofNat_pos, add_zero, sub_zero]
  ring

end DegreeZeroOrderFourHead610

section DegreeZeroOrderFourEval610

variable {k : Type*} [CommRing k]

theorem degreeZeroPostCollapseP32P21P1ZeroOrderFour610_eval
    (w1 a42 p32n p21n p1n p0 q53 q2 : k[X]) (a : k) :
    (degreeZeroPostCollapseP32P21P1ZeroOrderFour610 w1 a42 p32n p21n p1n
        p0 q53 q2).eval a =
      degreeZeroPostCollapseP32P21P1ZeroOrderFour610 (w1.eval a)
        (a42.eval a) (p32n.eval a) (p21n.eval a) (p1n.eval a)
        (p0.eval a) (q53.eval a) (q2.eval a) := by
  simp only [degreeZeroPostCollapseP32P21P1ZeroOrderFour610,
    Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_neg,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat]

theorem degreeZeroPostCollapseP32P21ZeroOrderFour610_eval
    (w1 a42 p32n p21n p1 p0 s2 u2 b63 q53 q2 q1 : k[X]) (lambda a : k) :
    (degreeZeroPostCollapseP32P21ZeroOrderFour610 w1 a42 p32n p21n p1 p0
        s2 u2 b63 q53 q2 q1 (Polynomial.C lambda)).eval a =
      degreeZeroPostCollapseP32P21ZeroOrderFour610 (w1.eval a)
        (a42.eval a) (p32n.eval a) (p21n.eval a) (p1.eval a)
        (p0.eval a) (s2.eval a) (u2.eval a) (b63.eval a) (q53.eval a)
        (q2.eval a) (q1.eval a) lambda := by
  simp only [degreeZeroPostCollapseP32P21ZeroOrderFour610,
    Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_neg,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat,
    Polynomial.eval_C]

theorem degreeZeroPostCollapseP32Q41Q3ZeroOrderFour610_eval
    (w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 : k[X])
    (lambda a : k) :
    (degreeZeroPostCollapseP32Q41Q3ZeroOrderFour610 w1 a42 p32n p21 p1
        p0 s2 u2 b63 q53 q41n q3n q2 q1 (Polynomial.C lambda)).eval a =
      degreeZeroPostCollapseP32Q41Q3ZeroOrderFour610 (w1.eval a)
        (a42.eval a) (p32n.eval a) (p21.eval a) (p1.eval a) (p0.eval a)
        (s2.eval a) (u2.eval a) (b63.eval a) (q53.eval a)
        (q41n.eval a) (q3n.eval a) (q2.eval a) (q1.eval a) lambda := by
  simp only [degreeZeroPostCollapseP32Q41Q3ZeroOrderFour610,
    Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_neg,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat,
    Polynomial.eval_C]

theorem degreeZeroPostCollapseP32Q41Q3P21ZeroOrderThreeHeadCofactor610_eval
    (w1 a42 p32n p1 u2 q53 q41n q3n q2 b63 : k[X]) (a : k) :
    (degreeZeroPostCollapseP32Q41Q3P21ZeroOrderThreeHeadCofactor610 w1
        a42 p32n p1 u2 q53 q41n q3n q2 b63).eval a =
      degreeZeroPostCollapseP32Q41Q3P21ZeroOrderThreeHeadCofactor610
        (w1.eval a) (a42.eval a) (p32n.eval a) (p1.eval a) (u2.eval a)
        (q53.eval a) (q41n.eval a) (q3n.eval a) (q2.eval a)
        (b63.eval a) := by
  simp only [
    degreeZeroPostCollapseP32Q41Q3P21ZeroOrderThreeHeadCofactor610,
    Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_ofNat]

theorem degreeZeroPostCollapseP32Q41Q3P21Q53ZeroOrderThreeHeadCofactor610_eval
    (w1 a42 p32n p1 u2 q41n q3n q2 b63 : k[X]) (a : k) :
    (degreeZeroPostCollapseP32Q41Q3P21Q53ZeroOrderThreeHeadCofactor610
        w1 a42 p32n p1 u2 q41n q3n q2 b63).eval a =
      degreeZeroPostCollapseP32Q41Q3P21Q53ZeroOrderThreeHeadCofactor610
        (w1.eval a) (a42.eval a) (p32n.eval a) (p1.eval a) (u2.eval a)
        (q41n.eval a) (q3n.eval a) (q2.eval a) (b63.eval a) := by
  simp only [
    degreeZeroPostCollapseP32Q41Q3P21Q53ZeroOrderThreeHeadCofactor610,
    Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_ofNat]

theorem degreeZeroPostCollapseQ41ZeroMixedOrderTwo610_eval
    (w1 a42 p32 p21 p1 s2 u2 b63 q53 q41n q3 q2 : k[X]) (lambda a : k) :
    (degreeZeroPostCollapseQ41ZeroMixedOrderTwo610 w1 a42 p32 p21 p1 s2
        u2 b63 q53 q41n q3 q2 (Polynomial.C lambda)).eval a =
      degreeZeroPostCollapseQ41ZeroMixedOrderTwo610 (w1.eval a)
        (a42.eval a) (p32.eval a) (p21.eval a) (p1.eval a) (s2.eval a)
        (u2.eval a) (b63.eval a) (q53.eval a) (q41n.eval a) (q3.eval a)
        (q2.eval a) lambda := by
  simp only [degreeZeroPostCollapseQ41ZeroMixedOrderTwo610,
    Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_neg,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat,
    Polynomial.eval_C]

theorem degreeZeroPostCollapseP32P21P1ZeroOrderThreePlus610_eval_root
    (h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 : k[X])
    (lambda a : k) (hroot : h.eval a = 0) :
    (degreeZeroPostCollapseP32P21P1ZeroOrderThreePlus610 h w1 a42 p32n
        p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1
        (Polynomial.C lambda)).eval a =
      degreeZeroPostCollapseP32P21P1ZeroOrderFour610 (w1.eval a)
        (a42.eval a) (p32n.eval a) (p21n.eval a) (p1n.eval a)
        (p0.eval a) (q53.eval a) (q2.eval a) := by
  rw [degreeZeroPostCollapseP32P21P1ZeroOrderThreePlus610_eval, hroot,
    degreeZeroPostCollapseP32P21P1ZeroOrderThreePlus610_zero]

theorem degreeZeroPostCollapseP32P21ZeroOrderThreePlus610_eval_root
    (h w1 a42 p32n p21n p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 : k[X])
    (lambda a : k) (hroot : h.eval a = 0) :
    (degreeZeroPostCollapseP32P21ZeroOrderThreePlus610 h w1 a42 p32n
        p21n p1 p0 s2 u2 b63 q53 q41 q3 q2 q1
        (Polynomial.C lambda)).eval a =
      degreeZeroPostCollapseP32P21ZeroOrderFour610 (w1.eval a)
        (a42.eval a) (p32n.eval a) (p21n.eval a) (p1.eval a)
        (p0.eval a) (s2.eval a) (u2.eval a) (b63.eval a) (q53.eval a)
        (q2.eval a) (q1.eval a) lambda := by
  rw [degreeZeroPostCollapseP32P21ZeroOrderThreePlus610_eval, hroot,
    degreeZeroPostCollapseP32P21ZeroOrderThreePlus610_zero]

theorem degreeZeroPostCollapseP32Q41Q3ZeroOrderThreePlus610_eval_root
    (h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 : k[X])
    (lambda a : k) (hroot : h.eval a = 0) :
    (degreeZeroPostCollapseP32Q41Q3ZeroOrderThreePlus610 h w1 a42 p32n
        p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1
        (Polynomial.C lambda)).eval a =
      degreeZeroPostCollapseP32Q41Q3ZeroOrderFour610 (w1.eval a)
        (a42.eval a) (p32n.eval a) (p21.eval a) (p1.eval a) (p0.eval a)
        (s2.eval a) (u2.eval a) (b63.eval a) (q53.eval a)
        (q41n.eval a) (q3n.eval a) (q2.eval a) (q1.eval a) lambda := by
  rw [degreeZeroPostCollapseP32Q41Q3ZeroOrderThreePlus610_eval, hroot,
    degreeZeroPostCollapseP32Q41Q3ZeroOrderThreePlus610_zero]

end DegreeZeroOrderFourEval610

section DegreeZeroOrderFourSplit610

variable {F : Type*} [Field F] [CharZero F]

/-- Honest scalar split of the sixty-two-term mixin at `p21 = 0`. -/
theorem degreeZeroPostCollapseP32Q41Q3ZeroOrderThreeHead610_p21Zero_split
    (w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 lambda : F)
    (hhead :
      degreeZeroPostCollapseP32Q41Q3ZeroOrderThreeHead610 w1 a42 p32n
        p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 lambda = 0)
    (hp21 : p21 = 0) :
    p1 = 0 ∨
      degreeZeroPostCollapseP32Q41Q3P21ZeroOrderThreeHeadCofactor610
          w1 a42 p32n p1 u2 q53 q41n q3n q2 b63 = 0 := by
  rw [degreeZeroPostCollapseP32Q41Q3ZeroOrderThreeHead610_p21Zero w1 a42
    p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 lambda hp21] at hhead
  rcases mul_eq_zero.mp hhead with hprod | hcof
  · rcases mul_eq_zero.mp hprod with hconstant | hp1
    · exact (by norm_num : (313456656384 : F) ≠ 0).elim hconstant
    · exact Or.inl hp1
  · exact Or.inr hcof

/-- Honest scalar split of the sixty-two-term mixin at `p21 = q53 = 0`. -/
theorem degreeZeroPostCollapseP32Q41Q3ZeroOrderThreeHead610_p21Q53Zero_split
    (w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 lambda : F)
    (hhead :
      degreeZeroPostCollapseP32Q41Q3ZeroOrderThreeHead610 w1 a42 p32n
        p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 lambda = 0)
    (hp21 : p21 = 0) (hq53 : q53 = 0) :
    p1 = 0 ∨
      degreeZeroPostCollapseP32Q41Q3P21Q53ZeroOrderThreeHeadCofactor610
          w1 a42 p32n p1 u2 q41n q3n q2 b63 = 0 := by
  rw [degreeZeroPostCollapseP32Q41Q3ZeroOrderThreeHead610_p21Q53Zero w1
    a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 lambda hp21 hq53]
    at hhead
  rcases mul_eq_zero.mp hhead with hprod | hcof
  · rcases mul_eq_zero.mp hprod with hconstant | hp1
    · exact (by norm_num : (7522959753216 : F) ≠ 0).elim hconstant
    · exact Or.inl hp1
  · exact Or.inr hcof

end DegreeZeroOrderFourSplit610

section DegreeZeroOrderFourSource610

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false

/-- Cancel four polynomial powers from a pole-six clearing. -/
theorem algebraMap_cancel_four_of_six_clearing610
    (h0 Q4 : k[X]) (rho : RatFunc k) (hh0 : h0 ≠ 0)
    (hquot :
      algebraMap k[X] (RatFunc k) (h0 ^ 4 * Q4) =
        (algebraMap k[X] (RatFunc k) h0) ^ 6 * rho) :
    algebraMap k[X] (RatFunc k) Q4 =
      (algebraMap k[X] (RatFunc k) h0) ^ 2 * rho := by
  let hRF : RatFunc k := algebraMap k[X] (RatFunc k) h0
  have hhRF : hRF ≠ 0 := RatFunc.algebraMap_ne_zero hh0
  apply mul_left_cancel₀ (pow_ne_zero 4 hhRF)
  have hmapPow :
      algebraMap k[X] (RatFunc k) (h0 ^ 4 * Q4) =
        hRF ^ 4 * algebraMap k[X] (RatFunc k) Q4 := by
    simp only [hRF, map_mul, map_pow]
  calc
    hRF ^ 4 * algebraMap k[X] (RatFunc k) Q4 =
        algebraMap k[X] (RatFunc k) (h0 ^ 4 * Q4) := hmapPow.symm
    _ = hRF ^ 6 * rho := hquot
    _ = hRF ^ 4 * (hRF ^ 2 * rho) := by ring

/-- Cancel two polynomial powers from a pole-six clearing. -/
theorem algebraMap_cancel_two_of_six_clearing610
    (h0 Q2 : k[X]) (rho : RatFunc k) (hh0 : h0 ≠ 0)
    (hquot :
      algebraMap k[X] (RatFunc k) (h0 ^ 2 * Q2) =
        (algebraMap k[X] (RatFunc k) h0) ^ 6 * rho) :
    algebraMap k[X] (RatFunc k) Q2 =
      (algebraMap k[X] (RatFunc k) h0) ^ 4 * rho := by
  let hRF : RatFunc k := algebraMap k[X] (RatFunc k) h0
  have hhRF : hRF ≠ 0 := RatFunc.algebraMap_ne_zero hh0
  apply mul_left_cancel₀ (pow_ne_zero 2 hhRF)
  have hmapPow :
      algebraMap k[X] (RatFunc k) (h0 ^ 2 * Q2) =
        hRF ^ 2 * algebraMap k[X] (RatFunc k) Q2 := by
    simp only [hRF, map_mul, map_pow]
  calc
    hRF ^ 2 * algebraMap k[X] (RatFunc k) Q2 =
        algebraMap k[X] (RatFunc k) (h0 ^ 2 * Q2) := hmapPow.symm
    _ = hRF ^ 6 * rho := hquot
    _ = hRF ^ 2 * (hRF ^ 4 * rho) := by ring

set_option maxHeartbeats 800000000 in
/-- On `p32(a) = p21(a) = p1(a) = 0` the forty-six-term hypersurface
peels and pole-two forces its first Taylor plus the order-`73` mixin
to vanish.  Cumulative vanishing: `h0^5` divides the jet quotient
(`M = 5`; next unused order `74`). -/
theorem degreeZeroPostCollapseP32P21P1ZeroOrderFourHead610_zero_of_primitiveDeriv
    (h0 w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 : k[X])
    (lambda j a : k) (hh0 : h0 ≠ 0) (hdegree : h0.natDegree = 1)
    (hroot : h0.eval a = 0) (hp32 : p32.eval a = 0)
    (hp21 : p21.eval a = 0) (hp1 : p1.eval a = 0)
    (hderiv :
      Differential.deriv
          ((58498535041007616 : RatFunc k) *
            degreeZeroPostCollapsePrimitive610
              (algebraMap k[X] (RatFunc k) h0)
              (algebraMap k[X] (RatFunc k) w1)
              (algebraMap k[X] (RatFunc k) a42)
              (algebraMap k[X] (RatFunc k) p32)
              (algebraMap k[X] (RatFunc k) p21)
              (algebraMap k[X] (RatFunc k) p1)
              (algebraMap k[X] (RatFunc k) p0)
              (algebraMap k[X] (RatFunc k) s2)
              (algebraMap k[X] (RatFunc k) u2)
              (algebraMap k[X] (RatFunc k) b63)
              (algebraMap k[X] (RatFunc k) q53)
              (algebraMap k[X] (RatFunc k) q41)
              (algebraMap k[X] (RatFunc k) q3)
              (algebraMap k[X] (RatFunc k) q2)
              (algebraMap k[X] (RatFunc k) q1) (RatFunc.C lambda)) =
        RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    ∃ p32n p21n p1n o72n : k[X],
      p32 = h0 * p32n ∧ p21 = h0 * p21n ∧ p1 = h0 * p1n ∧
        degreeZeroPostCollapseP32P21P1ZeroOrderThreeHead610 w1 a42 p32n
            p21n p1n p0 q41 q3 =
          h0 * o72n ∧
        o72n.eval a +
            degreeZeroPostCollapseP32P21P1ZeroOrderFour610 (w1.eval a)
              (a42.eval a) (p32n.eval a) (p21n.eval a) (p1n.eval a)
              (p0.eval a) (q53.eval a) (q2.eval a) =
          0 ∧
        h0 ^ 5 ∣
          degreeZeroPostCollapseJetQuotient610 h0 w1 a42 p32 p21 p1 p0
            s2 u2 b63 q53 q41 q3 q2 q1 (Polynomial.C lambda) := by
  obtain ⟨p32n, p21n, p1n, hp32eq, hp21eq, hp1eq, hhead⟩ :=
    degreeZeroPostCollapseP32P21P1ZeroOrderThreeHead610_zero_of_primitiveDeriv
      h0 w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda j a hh0
      hdegree hroot hp32 hp21 hp1 hderiv
  let hRF : RatFunc k := algebraMap k[X] (RatFunc k) h0
  let quotient : k[X] := degreeZeroPostCollapseJetQuotient610 h0 w1 a42
    p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 (Polynomial.C lambda)
  let rho : RatFunc k :=
    (58498535041007616 : RatFunc k) *
      degreeZeroPostCollapsePrimitive610 hRF
        (algebraMap k[X] (RatFunc k) w1)
        (algebraMap k[X] (RatFunc k) a42)
        (algebraMap k[X] (RatFunc k) p32)
        (algebraMap k[X] (RatFunc k) p21)
        (algebraMap k[X] (RatFunc k) p1)
        (algebraMap k[X] (RatFunc k) p0)
        (algebraMap k[X] (RatFunc k) s2)
        (algebraMap k[X] (RatFunc k) u2)
        (algebraMap k[X] (RatFunc k) b63)
        (algebraMap k[X] (RatFunc k) q53)
        (algebraMap k[X] (RatFunc k) q41)
        (algebraMap k[X] (RatFunc k) q3)
        (algebraMap k[X] (RatFunc k) q2)
        (algebraMap k[X] (RatFunc k) q1) (RatFunc.C lambda)
  have hhRF : hRF ≠ 0 := RatFunc.algebraMap_ne_zero hh0
  have hbridge := degreeZeroPostCollapseJetQuotient610_div_eq_clearedPrimitive
    hRF (algebraMap k[X] (RatFunc k) w1)
    (algebraMap k[X] (RatFunc k) a42)
    (algebraMap k[X] (RatFunc k) p32)
    (algebraMap k[X] (RatFunc k) p21)
    (algebraMap k[X] (RatFunc k) p1)
    (algebraMap k[X] (RatFunc k) p0)
    (algebraMap k[X] (RatFunc k) s2)
    (algebraMap k[X] (RatFunc k) u2)
    (algebraMap k[X] (RatFunc k) b63)
    (algebraMap k[X] (RatFunc k) q53)
    (algebraMap k[X] (RatFunc k) q41)
    (algebraMap k[X] (RatFunc k) q3)
    (algebraMap k[X] (RatFunc k) q2)
    (algebraMap k[X] (RatFunc k) q1) (RatFunc.C lambda) hhRF
  have hmap := degreeZeroPostCollapseJetQuotient610_map
    (algebraMap k[X] (RatFunc k)) h0 w1 a42 p32 p21 p1 p0 s2 u2 b63 q53
      q41 q3 q2 q1 (Polynomial.C lambda)
  have hclear : algebraMap k[X] (RatFunc k) quotient = hRF ^ 6 * rho := by
    dsimp only [quotient, rho]
    rw [hmap]
    simp only [RatFunc.algebraMap_C]
    rw [mul_comm (hRF ^ 6), ← div_eq_iff (pow_ne_zero 6 hhRF)]
    simpa only [hRF] using hbridge
  have hHeadEval :
      (degreeZeroPostCollapseP32P21P1ZeroOrderThreeHead610 w1 a42 p32n
          p21n p1n p0 q41 q3).eval a = 0 := by
    rw [degreeZeroPostCollapseP32P21P1ZeroOrderThreeHead610_eval]
    exact hhead
  obtain ⟨o72n, ho72⟩ := linearPolynomial_dvd_of_eval_eq_zero_610 h0
    (degreeZeroPostCollapseP32P21P1ZeroOrderThreeHead610 w1 a42 p32n
      p21n p1n p0 q41 q3) a hdegree hroot hHeadEval
  let Q4 : k[X] :=
    o72n +
      degreeZeroPostCollapseP32P21P1ZeroOrderThreePlus610 h0 w1 a42
        p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1
        (Polynomial.C lambda)
  have hquot : quotient = h0 ^ 4 * Q4 := by
    calc
      quotient =
          degreeZeroPostCollapseJetQuotient610 h0 w1 a42 (h0 * p32n)
            (h0 * p21n) (h0 * p1n) p0 s2 u2 b63 q53 q41 q3 q2 q1
            (Polynomial.C lambda) := by
        simp only [quotient, hp32eq, hp21eq, hp1eq]
      _ = h0 ^ 3 *
              degreeZeroPostCollapseP32P21P1ZeroOrderThreeHead610 w1
                a42 p32n p21n p1n p0 q41 q3 +
            h0 ^ 4 *
              degreeZeroPostCollapseP32P21P1ZeroOrderThreePlus610 h0 w1
                a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1
                (Polynomial.C lambda) :=
        degreeZeroPostCollapseJetQuotient610_p32P21P1Scale h0 w1 a42
          p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1
          (Polynomial.C lambda)
      _ = h0 ^ 4 * Q4 := by
        rw [ho72]
        simp only [Q4]
        ring
  have hclear2 : algebraMap k[X] (RatFunc k) Q4 = hRF ^ 2 * rho :=
    algebraMap_cancel_four_of_six_clearing610 h0 Q4 rho hh0 (by
      simpa [hquot] using hclear)
  have hQ4zero : Q4.eval a = 0 :=
    localLinearPoleTwo_head_eval_zero_of_deriv_eq_simplePole610 a j h0
      Q4 rho hdegree hroot hclear2 (by simpa [rho, hRF] using hderiv)
  have hQ4eval :
      Q4.eval a =
        o72n.eval a +
          degreeZeroPostCollapseP32P21P1ZeroOrderFour610 (w1.eval a)
            (a42.eval a) (p32n.eval a) (p21n.eval a) (p1n.eval a)
            (p0.eval a) (q53.eval a) (q2.eval a) := by
    simp only [Q4, Polynomial.eval_add]
    rw [degreeZeroPostCollapseP32P21P1ZeroOrderThreePlus610_eval_root h0
      w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda a
      hroot]
  obtain ⟨Q5, hQ5⟩ := linearPolynomial_dvd_of_eval_eq_zero_610 h0 Q4 a
    hdegree hroot hQ4zero
  refine ⟨p32n, p21n, p1n, o72n, hp32eq, hp21eq, hp1eq, ho72, ?_, ?_⟩
  · rw [← hQ4eval]
    exact hQ4zero
  · refine ⟨Q5, ?_⟩
    calc
      quotient = h0 ^ 4 * Q4 := hquot
      _ = h0 ^ 4 * (h0 * Q5) := by rw [hQ5]
      _ = h0 ^ 5 * Q5 := by ring


set_option maxHeartbeats 800000000 in
/-- On `p32(a) = p21(a) = 0` pole-two forces the next Taylor of
`o71n + OrderThree` plus the order-`73` mixin to vanish.
Cumulative vanishing: `h0^5` divides the jet quotient (`M = 5`; next
unused order `74`). -/
theorem degreeZeroPostCollapseP32P21ZeroOrderFourHead610_zero_of_primitiveDeriv
    (h0 w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 : k[X])
    (lambda j a : k) (hh0 : h0 ≠ 0) (hdegree : h0.natDegree = 1)
    (hroot : h0.eval a = 0) (hp32 : p32.eval a = 0)
    (hp21 : p21.eval a = 0)
    (hderiv :
      Differential.deriv
          ((58498535041007616 : RatFunc k) *
            degreeZeroPostCollapsePrimitive610
              (algebraMap k[X] (RatFunc k) h0)
              (algebraMap k[X] (RatFunc k) w1)
              (algebraMap k[X] (RatFunc k) a42)
              (algebraMap k[X] (RatFunc k) p32)
              (algebraMap k[X] (RatFunc k) p21)
              (algebraMap k[X] (RatFunc k) p1)
              (algebraMap k[X] (RatFunc k) p0)
              (algebraMap k[X] (RatFunc k) s2)
              (algebraMap k[X] (RatFunc k) u2)
              (algebraMap k[X] (RatFunc k) b63)
              (algebraMap k[X] (RatFunc k) q53)
              (algebraMap k[X] (RatFunc k) q41)
              (algebraMap k[X] (RatFunc k) q3)
              (algebraMap k[X] (RatFunc k) q2)
              (algebraMap k[X] (RatFunc k) q1) (RatFunc.C lambda)) =
        RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    ∃ p32n p21n o71n o72n : k[X],
      p32 = h0 * p32n ∧ p21 = h0 * p21n ∧
        degreeZeroPostCollapseP32P21ZeroOrderTwoHead610 w1 a42 p32n
            p21n p1 q53 q41 q3 =
          h0 * o71n ∧
        o71n +
            degreeZeroPostCollapseP32P21ZeroOrderThreeHead610 w1 a42
              p32n p21n p1 p0 u2 b63 q53 q41 q3 q2 =
          h0 * o72n ∧
        o72n.eval a +
            degreeZeroPostCollapseP32P21ZeroOrderFour610 (w1.eval a)
              (a42.eval a) (p32n.eval a) (p21n.eval a) (p1.eval a)
              (p0.eval a) (s2.eval a) (u2.eval a) (b63.eval a)
              (q53.eval a) (q2.eval a) (q1.eval a) lambda =
          0 ∧
        h0 ^ 5 ∣
          degreeZeroPostCollapseJetQuotient610 h0 w1 a42 p32 p21 p1 p0
            s2 u2 b63 q53 q41 q3 q2 q1 (Polynomial.C lambda) := by
  obtain ⟨p32n, p21n, o71n, hp32eq, hp21eq, ho71, hmix⟩ :=
    degreeZeroPostCollapseP32P21ZeroOrderThreeHead610_zero_of_primitiveDeriv
      h0 w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda j a hh0
      hdegree hroot hp32 hp21 hderiv
  let hRF : RatFunc k := algebraMap k[X] (RatFunc k) h0
  let quotient : k[X] := degreeZeroPostCollapseJetQuotient610 h0 w1 a42
    p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 (Polynomial.C lambda)
  let rho : RatFunc k :=
    (58498535041007616 : RatFunc k) *
      degreeZeroPostCollapsePrimitive610 hRF
        (algebraMap k[X] (RatFunc k) w1)
        (algebraMap k[X] (RatFunc k) a42)
        (algebraMap k[X] (RatFunc k) p32)
        (algebraMap k[X] (RatFunc k) p21)
        (algebraMap k[X] (RatFunc k) p1)
        (algebraMap k[X] (RatFunc k) p0)
        (algebraMap k[X] (RatFunc k) s2)
        (algebraMap k[X] (RatFunc k) u2)
        (algebraMap k[X] (RatFunc k) b63)
        (algebraMap k[X] (RatFunc k) q53)
        (algebraMap k[X] (RatFunc k) q41)
        (algebraMap k[X] (RatFunc k) q3)
        (algebraMap k[X] (RatFunc k) q2)
        (algebraMap k[X] (RatFunc k) q1) (RatFunc.C lambda)
  have hhRF : hRF ≠ 0 := RatFunc.algebraMap_ne_zero hh0
  have hbridge := degreeZeroPostCollapseJetQuotient610_div_eq_clearedPrimitive
    hRF (algebraMap k[X] (RatFunc k) w1)
    (algebraMap k[X] (RatFunc k) a42)
    (algebraMap k[X] (RatFunc k) p32)
    (algebraMap k[X] (RatFunc k) p21)
    (algebraMap k[X] (RatFunc k) p1)
    (algebraMap k[X] (RatFunc k) p0)
    (algebraMap k[X] (RatFunc k) s2)
    (algebraMap k[X] (RatFunc k) u2)
    (algebraMap k[X] (RatFunc k) b63)
    (algebraMap k[X] (RatFunc k) q53)
    (algebraMap k[X] (RatFunc k) q41)
    (algebraMap k[X] (RatFunc k) q3)
    (algebraMap k[X] (RatFunc k) q2)
    (algebraMap k[X] (RatFunc k) q1) (RatFunc.C lambda) hhRF
  have hmap := degreeZeroPostCollapseJetQuotient610_map
    (algebraMap k[X] (RatFunc k)) h0 w1 a42 p32 p21 p1 p0 s2 u2 b63 q53
      q41 q3 q2 q1 (Polynomial.C lambda)
  have hclear : algebraMap k[X] (RatFunc k) quotient = hRF ^ 6 * rho := by
    dsimp only [quotient, rho]
    rw [hmap]
    simp only [RatFunc.algebraMap_C]
    rw [mul_comm (hRF ^ 6), ← div_eq_iff (pow_ne_zero 6 hhRF)]
    simpa only [hRF] using hbridge
  have hSumEval :
      (o71n +
          degreeZeroPostCollapseP32P21ZeroOrderThreeHead610 w1 a42 p32n
            p21n p1 p0 u2 b63 q53 q41 q3 q2).eval a = 0 := by
    simp only [Polynomial.eval_add,
      degreeZeroPostCollapseP32P21ZeroOrderThreeHead610_eval]
    exact hmix
  obtain ⟨o72n, ho72⟩ := linearPolynomial_dvd_of_eval_eq_zero_610 h0
    (o71n +
      degreeZeroPostCollapseP32P21ZeroOrderThreeHead610 w1 a42 p32n
        p21n p1 p0 u2 b63 q53 q41 q3 q2) a hdegree hroot hSumEval
  let Q4 : k[X] :=
    o72n +
      degreeZeroPostCollapseP32P21ZeroOrderThreePlus610 h0 w1 a42 p32n
        p21n p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 (Polynomial.C lambda)
  have hquot : quotient = h0 ^ 4 * Q4 := by
    calc
      quotient =
          degreeZeroPostCollapseJetQuotient610 h0 w1 a42 (h0 * p32n)
            (h0 * p21n) p1 p0 s2 u2 b63 q53 q41 q3 q2 q1
            (Polynomial.C lambda) := by
        simp only [quotient, hp32eq, hp21eq]
      _ = h0 ^ 2 *
              degreeZeroPostCollapseP32P21ZeroOrderTwoHead610 w1 a42
                p32n p21n p1 q53 q41 q3 +
            h0 ^ 3 *
              degreeZeroPostCollapseP32P21ZeroOrderThreeHead610 w1 a42
                p32n p21n p1 p0 u2 b63 q53 q41 q3 q2 +
            h0 ^ 4 *
              degreeZeroPostCollapseP32P21ZeroOrderThreePlus610 h0 w1
                a42 p32n p21n p1 p0 s2 u2 b63 q53 q41 q3 q2 q1
                (Polynomial.C lambda) :=
        degreeZeroPostCollapseJetQuotient610_p32P21Scale h0 w1 a42 p32n
          p21n p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 (Polynomial.C lambda)
      _ = h0 ^ 4 * Q4 := by
        rw [ho71]
        calc
          h0 ^ 2 * (h0 * o71n) +
                h0 ^ 3 *
                  degreeZeroPostCollapseP32P21ZeroOrderThreeHead610 w1
                    a42 p32n p21n p1 p0 u2 b63 q53 q41 q3 q2 +
                h0 ^ 4 *
                  degreeZeroPostCollapseP32P21ZeroOrderThreePlus610 h0
                    w1 a42 p32n p21n p1 p0 s2 u2 b63 q53 q41 q3 q2 q1
                    (Polynomial.C lambda) =
              h0 ^ 3 *
                    (o71n +
                      degreeZeroPostCollapseP32P21ZeroOrderThreeHead610
                        w1 a42 p32n p21n p1 p0 u2 b63 q53 q41 q3 q2) +
                  h0 ^ 4 *
                    degreeZeroPostCollapseP32P21ZeroOrderThreePlus610
                      h0 w1 a42 p32n p21n p1 p0 s2 u2 b63 q53 q41 q3
                      q2 q1 (Polynomial.C lambda) := by
            ring
          _ = h0 ^ 3 * (h0 * o72n) +
                h0 ^ 4 *
                  degreeZeroPostCollapseP32P21ZeroOrderThreePlus610 h0
                    w1 a42 p32n p21n p1 p0 s2 u2 b63 q53 q41 q3 q2 q1
                    (Polynomial.C lambda) := by
            rw [ho72]
          _ = h0 ^ 4 * Q4 := by
            simp only [Q4]
            ring
  have hclear2 : algebraMap k[X] (RatFunc k) Q4 = hRF ^ 2 * rho :=
    algebraMap_cancel_four_of_six_clearing610 h0 Q4 rho hh0 (by
      simpa [hquot] using hclear)
  have hQ4zero : Q4.eval a = 0 :=
    localLinearPoleTwo_head_eval_zero_of_deriv_eq_simplePole610 a j h0
      Q4 rho hdegree hroot hclear2 (by simpa [rho, hRF] using hderiv)
  have hQ4eval :
      Q4.eval a =
        o72n.eval a +
          degreeZeroPostCollapseP32P21ZeroOrderFour610 (w1.eval a)
            (a42.eval a) (p32n.eval a) (p21n.eval a) (p1.eval a)
            (p0.eval a) (s2.eval a) (u2.eval a) (b63.eval a)
            (q53.eval a) (q2.eval a) (q1.eval a) lambda := by
    simp only [Q4, Polynomial.eval_add]
    rw [degreeZeroPostCollapseP32P21ZeroOrderThreePlus610_eval_root h0
      w1 a42 p32n p21n p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda a hroot]
  obtain ⟨Q5, hQ5⟩ := linearPolynomial_dvd_of_eval_eq_zero_610 h0 Q4 a
    hdegree hroot hQ4zero
  refine ⟨p32n, p21n, o71n, o72n, hp32eq, hp21eq, ho71, ho72, ?_, ?_⟩
  · rw [← hQ4eval]
    exact hQ4zero
  · refine ⟨Q5, ?_⟩
    calc
      quotient = h0 ^ 4 * Q4 := hquot
      _ = h0 ^ 4 * (h0 * Q5) := by rw [hQ5]
      _ = h0 ^ 5 * Q5 := by ring

set_option maxHeartbeats 800000000 in
/-- On `p32(a) = q41(a) = q3(a) = 0` pole-two forces the next Taylor of
the sixty-two-term mixin plus the order-`73` remainder to vanish.
Cumulative vanishing: `h0^5` divides the jet quotient (`M = 5`; next
unused order `74`). -/
theorem degreeZeroPostCollapseP32Q41Q3ZeroOrderFourHead610_zero_of_primitiveDeriv
    (h0 w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 : k[X])
    (lambda j a : k) (hh0 : h0 ≠ 0) (hdegree : h0.natDegree = 1)
    (hroot : h0.eval a = 0) (hp32 : p32.eval a = 0)
    (hq41 : q41.eval a = 0) (hq3 : q3.eval a = 0)
    (hderiv :
      Differential.deriv
          ((58498535041007616 : RatFunc k) *
            degreeZeroPostCollapsePrimitive610
              (algebraMap k[X] (RatFunc k) h0)
              (algebraMap k[X] (RatFunc k) w1)
              (algebraMap k[X] (RatFunc k) a42)
              (algebraMap k[X] (RatFunc k) p32)
              (algebraMap k[X] (RatFunc k) p21)
              (algebraMap k[X] (RatFunc k) p1)
              (algebraMap k[X] (RatFunc k) p0)
              (algebraMap k[X] (RatFunc k) s2)
              (algebraMap k[X] (RatFunc k) u2)
              (algebraMap k[X] (RatFunc k) b63)
              (algebraMap k[X] (RatFunc k) q53)
              (algebraMap k[X] (RatFunc k) q41)
              (algebraMap k[X] (RatFunc k) q3)
              (algebraMap k[X] (RatFunc k) q2)
              (algebraMap k[X] (RatFunc k) q1) (RatFunc.C lambda)) =
        RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    ∃ p32n q41n q3n o71n o72n : k[X],
      p32 = h0 * p32n ∧ q41 = h0 * q41n ∧ q3 = h0 * q3n ∧
        degreeZeroPostCollapseP32Q41Q3ZeroOrderTwoHead610 w1 a42 p21 p1
            q53 q41n q3n u2 =
          h0 * o71n ∧
        o71n +
            degreeZeroPostCollapseP32Q41Q3ZeroOrderThreeHead610 w1 a42
              p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2
              (Polynomial.C lambda) =
          h0 * o72n ∧
        o72n.eval a +
            degreeZeroPostCollapseP32Q41Q3ZeroOrderFour610 (w1.eval a)
              (a42.eval a) (p32n.eval a) (p21.eval a) (p1.eval a)
              (p0.eval a) (s2.eval a) (u2.eval a) (b63.eval a)
              (q53.eval a) (q41n.eval a) (q3n.eval a) (q2.eval a)
              (q1.eval a) lambda =
          0 ∧
        h0 ^ 5 ∣
          degreeZeroPostCollapseJetQuotient610 h0 w1 a42 p32 p21 p1 p0
            s2 u2 b63 q53 q41 q3 q2 q1 (Polynomial.C lambda) := by
  obtain ⟨p32n, q41n, q3n, o71n, hp32eq, hq41eq, hq3eq, ho71, hmix⟩ :=
    degreeZeroPostCollapseP32Q41Q3ZeroOrderThreeHead610_zero_of_primitiveDeriv
      h0 w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda j a hh0
      hdegree hroot hp32 hq41 hq3 hderiv
  let hRF : RatFunc k := algebraMap k[X] (RatFunc k) h0
  let quotient : k[X] := degreeZeroPostCollapseJetQuotient610 h0 w1 a42
    p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 (Polynomial.C lambda)
  let rho : RatFunc k :=
    (58498535041007616 : RatFunc k) *
      degreeZeroPostCollapsePrimitive610 hRF
        (algebraMap k[X] (RatFunc k) w1)
        (algebraMap k[X] (RatFunc k) a42)
        (algebraMap k[X] (RatFunc k) p32)
        (algebraMap k[X] (RatFunc k) p21)
        (algebraMap k[X] (RatFunc k) p1)
        (algebraMap k[X] (RatFunc k) p0)
        (algebraMap k[X] (RatFunc k) s2)
        (algebraMap k[X] (RatFunc k) u2)
        (algebraMap k[X] (RatFunc k) b63)
        (algebraMap k[X] (RatFunc k) q53)
        (algebraMap k[X] (RatFunc k) q41)
        (algebraMap k[X] (RatFunc k) q3)
        (algebraMap k[X] (RatFunc k) q2)
        (algebraMap k[X] (RatFunc k) q1) (RatFunc.C lambda)
  have hhRF : hRF ≠ 0 := RatFunc.algebraMap_ne_zero hh0
  have hbridge := degreeZeroPostCollapseJetQuotient610_div_eq_clearedPrimitive
    hRF (algebraMap k[X] (RatFunc k) w1)
    (algebraMap k[X] (RatFunc k) a42)
    (algebraMap k[X] (RatFunc k) p32)
    (algebraMap k[X] (RatFunc k) p21)
    (algebraMap k[X] (RatFunc k) p1)
    (algebraMap k[X] (RatFunc k) p0)
    (algebraMap k[X] (RatFunc k) s2)
    (algebraMap k[X] (RatFunc k) u2)
    (algebraMap k[X] (RatFunc k) b63)
    (algebraMap k[X] (RatFunc k) q53)
    (algebraMap k[X] (RatFunc k) q41)
    (algebraMap k[X] (RatFunc k) q3)
    (algebraMap k[X] (RatFunc k) q2)
    (algebraMap k[X] (RatFunc k) q1) (RatFunc.C lambda) hhRF
  have hmap := degreeZeroPostCollapseJetQuotient610_map
    (algebraMap k[X] (RatFunc k)) h0 w1 a42 p32 p21 p1 p0 s2 u2 b63 q53
      q41 q3 q2 q1 (Polynomial.C lambda)
  have hclear : algebraMap k[X] (RatFunc k) quotient = hRF ^ 6 * rho := by
    dsimp only [quotient, rho]
    rw [hmap]
    simp only [RatFunc.algebraMap_C]
    rw [mul_comm (hRF ^ 6), ← div_eq_iff (pow_ne_zero 6 hhRF)]
    simpa only [hRF] using hbridge
  have hSumEval :
      (o71n +
          degreeZeroPostCollapseP32Q41Q3ZeroOrderThreeHead610 w1 a42
            p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2
            (Polynomial.C lambda)).eval a = 0 := by
    simp only [Polynomial.eval_add,
      degreeZeroPostCollapseP32Q41Q3ZeroOrderThreeHead610_eval]
    exact hmix
  obtain ⟨o72n, ho72⟩ := linearPolynomial_dvd_of_eval_eq_zero_610 h0
    (o71n +
      degreeZeroPostCollapseP32Q41Q3ZeroOrderThreeHead610 w1 a42 p32n
        p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 (Polynomial.C lambda)) a
    hdegree hroot hSumEval
  let Q4 : k[X] :=
    o72n +
      degreeZeroPostCollapseP32Q41Q3ZeroOrderThreePlus610 h0 w1 a42
        p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1
        (Polynomial.C lambda)
  have hquot : quotient = h0 ^ 4 * Q4 := by
    calc
      quotient =
          degreeZeroPostCollapseJetQuotient610 h0 w1 a42 (h0 * p32n)
            p21 p1 p0 s2 u2 b63 q53 (h0 * q41n) (h0 * q3n) q2 q1
            (Polynomial.C lambda) := by
        simp only [quotient, hp32eq, hq41eq, hq3eq]
      _ = h0 ^ 2 *
              degreeZeroPostCollapseP32Q41Q3ZeroOrderTwoHead610 w1 a42
                p21 p1 q53 q41n q3n u2 +
            h0 ^ 3 *
              degreeZeroPostCollapseP32Q41Q3ZeroOrderThreeHead610 w1
                a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2
                (Polynomial.C lambda) +
            h0 ^ 4 *
              degreeZeroPostCollapseP32Q41Q3ZeroOrderThreePlus610 h0
                w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1
                (Polynomial.C lambda) :=
        degreeZeroPostCollapseJetQuotient610_p32Q41Q3Scale h0 w1 a42
          p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1
          (Polynomial.C lambda)
      _ = h0 ^ 4 * Q4 := by
        rw [ho71]
        calc
          h0 ^ 2 * (h0 * o71n) +
                h0 ^ 3 *
                  degreeZeroPostCollapseP32Q41Q3ZeroOrderThreeHead610
                    w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2
                    (Polynomial.C lambda) +
                h0 ^ 4 *
                  degreeZeroPostCollapseP32Q41Q3ZeroOrderThreePlus610
                    h0 w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2
                    q1 (Polynomial.C lambda) =
              h0 ^ 3 *
                    (o71n +
                      degreeZeroPostCollapseP32Q41Q3ZeroOrderThreeHead610
                        w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n
                        q2 (Polynomial.C lambda)) +
                  h0 ^ 4 *
                    degreeZeroPostCollapseP32Q41Q3ZeroOrderThreePlus610
                      h0 w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n
                      q2 q1 (Polynomial.C lambda) := by
            ring
          _ = h0 ^ 3 * (h0 * o72n) +
                h0 ^ 4 *
                  degreeZeroPostCollapseP32Q41Q3ZeroOrderThreePlus610
                    h0 w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2
                    q1 (Polynomial.C lambda) := by
            rw [ho72]
          _ = h0 ^ 4 * Q4 := by
            simp only [Q4]
            ring
  have hclear2 : algebraMap k[X] (RatFunc k) Q4 = hRF ^ 2 * rho :=
    algebraMap_cancel_four_of_six_clearing610 h0 Q4 rho hh0 (by
      simpa [hquot] using hclear)
  have hQ4zero : Q4.eval a = 0 :=
    localLinearPoleTwo_head_eval_zero_of_deriv_eq_simplePole610 a j h0
      Q4 rho hdegree hroot hclear2 (by simpa [rho, hRF] using hderiv)
  have hQ4eval :
      Q4.eval a =
        o72n.eval a +
          degreeZeroPostCollapseP32Q41Q3ZeroOrderFour610 (w1.eval a)
            (a42.eval a) (p32n.eval a) (p21.eval a) (p1.eval a)
            (p0.eval a) (s2.eval a) (u2.eval a) (b63.eval a)
            (q53.eval a) (q41n.eval a) (q3n.eval a) (q2.eval a)
            (q1.eval a) lambda := by
    simp only [Q4, Polynomial.eval_add]
    rw [degreeZeroPostCollapseP32Q41Q3ZeroOrderThreePlus610_eval_root h0
      w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda a
      hroot]
  obtain ⟨Q5, hQ5⟩ := linearPolynomial_dvd_of_eval_eq_zero_610 h0 Q4 a
    hdegree hroot hQ4zero
  refine ⟨p32n, q41n, q3n, o71n, o72n, hp32eq, hq41eq, hq3eq, ho71,
    ho72, ?_, ?_⟩
  · rw [← hQ4eval]
    exact hQ4zero
  · refine ⟨Q5, ?_⟩
    calc
      quotient = h0 ^ 4 * Q4 := hquot
      _ = h0 ^ 4 * (h0 * Q5) := by rw [hQ5]
      _ = h0 ^ 5 * Q5 := by ring


set_option maxHeartbeats 800000000 in
/-- On `q41(a) = 0` the mixed order-`70` head peels and pole-four forces
the mixed order-`71` object to vanish.  The next Taylor `q41nn` of
`q41n` is named honestly.  Cumulative vanishing: `h0^3` divides the
jet quotient (`M = 3`; next unused mixed order `72`). -/
theorem degreeZeroPostCollapseQ41ZeroMixedOrderTwo610_zero_of_primitiveDeriv
    (h0 w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 : k[X])
    (lambda j a : k) (hh0 : h0 ≠ 0) (hdegree : h0.natDegree = 1)
    (hroot : h0.eval a = 0) (hq41 : q41.eval a = 0)
    (hderiv :
      Differential.deriv
          ((58498535041007616 : RatFunc k) *
            degreeZeroPostCollapsePrimitive610
              (algebraMap k[X] (RatFunc k) h0)
              (algebraMap k[X] (RatFunc k) w1)
              (algebraMap k[X] (RatFunc k) a42)
              (algebraMap k[X] (RatFunc k) p32)
              (algebraMap k[X] (RatFunc k) p21)
              (algebraMap k[X] (RatFunc k) p1)
              (algebraMap k[X] (RatFunc k) p0)
              (algebraMap k[X] (RatFunc k) s2)
              (algebraMap k[X] (RatFunc k) u2)
              (algebraMap k[X] (RatFunc k) b63)
              (algebraMap k[X] (RatFunc k) q53)
              (algebraMap k[X] (RatFunc k) q41)
              (algebraMap k[X] (RatFunc k) q3)
              (algebraMap k[X] (RatFunc k) q2)
              (algebraMap k[X] (RatFunc k) q1) (RatFunc.C lambda)) =
        RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    ∃ q41n q41nn o70n : k[X],
      q41 = h0 * q41n ∧
        q41n = C (q41n.eval a) + h0 * q41nn ∧
        degreeZeroPostCollapseQ41ZeroMixedOrderOne610 w1 a42 p32 p21 p1
            q53 q41n q3 u2 =
          h0 * o70n ∧
        o70n.eval a +
            degreeZeroPostCollapseQ41ZeroMixedOrderTwo610 (w1.eval a)
              (a42.eval a) (p32.eval a) (p21.eval a) (p1.eval a)
              (s2.eval a) (u2.eval a) (b63.eval a) (q53.eval a)
              (q41n.eval a) (q3.eval a) (q2.eval a) lambda =
          0 ∧
        h0 ^ 3 ∣
          degreeZeroPostCollapseJetQuotient610 h0 w1 a42 p32 p21 p1 p0
            s2 u2 b63 q53 q41 q3 q2 q1 (Polynomial.C lambda) := by
  obtain ⟨q41n, hq41eq, hmixed⟩ :=
    degreeZeroPostCollapseQ41ZeroMixedOrderOne610_zero_of_primitiveDeriv
      h0 w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda j a hh0
      hdegree hroot hq41 hderiv
  let hRF : RatFunc k := algebraMap k[X] (RatFunc k) h0
  let quotient : k[X] := degreeZeroPostCollapseJetQuotient610 h0 w1 a42
    p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 (Polynomial.C lambda)
  let rho : RatFunc k :=
    (58498535041007616 : RatFunc k) *
      degreeZeroPostCollapsePrimitive610 hRF
        (algebraMap k[X] (RatFunc k) w1)
        (algebraMap k[X] (RatFunc k) a42)
        (algebraMap k[X] (RatFunc k) p32)
        (algebraMap k[X] (RatFunc k) p21)
        (algebraMap k[X] (RatFunc k) p1)
        (algebraMap k[X] (RatFunc k) p0)
        (algebraMap k[X] (RatFunc k) s2)
        (algebraMap k[X] (RatFunc k) u2)
        (algebraMap k[X] (RatFunc k) b63)
        (algebraMap k[X] (RatFunc k) q53)
        (algebraMap k[X] (RatFunc k) q41)
        (algebraMap k[X] (RatFunc k) q3)
        (algebraMap k[X] (RatFunc k) q2)
        (algebraMap k[X] (RatFunc k) q1) (RatFunc.C lambda)
  have hhRF : hRF ≠ 0 := RatFunc.algebraMap_ne_zero hh0
  have hbridge := degreeZeroPostCollapseJetQuotient610_div_eq_clearedPrimitive
    hRF (algebraMap k[X] (RatFunc k) w1)
    (algebraMap k[X] (RatFunc k) a42)
    (algebraMap k[X] (RatFunc k) p32)
    (algebraMap k[X] (RatFunc k) p21)
    (algebraMap k[X] (RatFunc k) p1)
    (algebraMap k[X] (RatFunc k) p0)
    (algebraMap k[X] (RatFunc k) s2)
    (algebraMap k[X] (RatFunc k) u2)
    (algebraMap k[X] (RatFunc k) b63)
    (algebraMap k[X] (RatFunc k) q53)
    (algebraMap k[X] (RatFunc k) q41)
    (algebraMap k[X] (RatFunc k) q3)
    (algebraMap k[X] (RatFunc k) q2)
    (algebraMap k[X] (RatFunc k) q1) (RatFunc.C lambda) hhRF
  have hmap := degreeZeroPostCollapseJetQuotient610_map
    (algebraMap k[X] (RatFunc k)) h0 w1 a42 p32 p21 p1 p0 s2 u2 b63 q53
      q41 q3 q2 q1 (Polynomial.C lambda)
  have hclear : algebraMap k[X] (RatFunc k) quotient = hRF ^ 6 * rho := by
    dsimp only [quotient, rho]
    rw [hmap]
    simp only [RatFunc.algebraMap_C]
    rw [mul_comm (hRF ^ 6), ← div_eq_iff (pow_ne_zero 6 hhRF)]
    simpa only [hRF] using hbridge
  have hα :
      (q41n - C (q41n.eval a)).eval a = 0 := by
    simp [Polynomial.eval_sub, Polynomial.eval_C]
  obtain ⟨q41nn, hTaylor⟩ := linearPolynomial_dvd_of_eval_eq_zero_610 h0
    (q41n - C (q41n.eval a)) a hdegree hroot hα
  have hq41nTaylor : q41n = C (q41n.eval a) + h0 * q41nn :=
    (sub_eq_iff_eq_add.mp hTaylor).trans
      (add_comm (h0 * q41nn) (C (q41n.eval a)))
  have hMixEval :
      (degreeZeroPostCollapseQ41ZeroMixedOrderOne610 w1 a42 p32 p21 p1
          q53 q41n q3 u2).eval a = 0 := by
    rw [degreeZeroPostCollapseQ41ZeroMixedOrderOne610_eval]
    exact hmixed
  obtain ⟨o70n, ho70⟩ := linearPolynomial_dvd_of_eval_eq_zero_610 h0
    (degreeZeroPostCollapseQ41ZeroMixedOrderOne610 w1 a42 p32 p21 p1
      q53 q41n q3 u2) a hdegree hroot hMixEval
  let seven : k[X] :=
    (45498860587450368 : k[X]) * a42 * p21 * p32 * q41n -
      49290432303071232 * a42 * p32 ^ 2 * q41n * w1 -
      38999023360671744 * p1 * p21 * q41n +
      45498860587450368 * p1 * p32 * q41n * w1 +
      22749430293725184 * p21 ^ 2 * q41n * w1 -
      49290432303071232 * p21 * p32 * q41n * w1 ^ 2 +
      26014394826620928 * p32 ^ 2 * q41n * w1 ^ 3
  let Q2 : k[X] :=
    o70n + seven +
      degreeZeroPostCollapseJetOrderTwoPlus610 h0 w1 a42 p32 p21 p1 p0
        s2 u2 b63 q53 q41 q3 q2 q1 (Polynomial.C lambda)
  have hquot : quotient = h0 ^ 2 * Q2 := by
    have hform := degreeZeroPostCollapseJetQuotient610_orderExpansion h0
      w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1
      (Polynomial.C lambda)
    have hheadEq :=
      degreeZeroPostCollapseQ41ZeroMixedOrderOne610_headEq h0 w1 a42
        p32 p21 p1 q53 q41n q3 u2
    calc
      quotient =
          degreeZeroPostCollapseJetHead610 p32 q41 +
            h0 *
              degreeZeroPostCollapseJetOrderOne610 w1 a42 p32 p21 p1
                q53 q41 q3 u2 +
            h0 ^ 2 *
              degreeZeroPostCollapseJetOrderTwoPlus610 h0 w1 a42 p32
                p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1
                (Polynomial.C lambda) := by
        simpa [quotient] using hform
      _ = degreeZeroPostCollapseJetHead610 p32 (h0 * q41n) +
            h0 *
              degreeZeroPostCollapseJetOrderOne610 w1 a42 p32 p21 p1
                q53 (h0 * q41n) q3 u2 +
            h0 ^ 2 *
              degreeZeroPostCollapseJetOrderTwoPlus610 h0 w1 a42 p32
                p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1
                (Polynomial.C lambda) := by
        simp only [hq41eq]
      _ = h0 *
              degreeZeroPostCollapseQ41ZeroMixedOrderOne610 w1 a42 p32
                p21 p1 q53 q41n q3 u2 +
            h0 ^ 2 * seven +
            h0 ^ 2 *
              degreeZeroPostCollapseJetOrderTwoPlus610 h0 w1 a42 p32
                p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1
                (Polynomial.C lambda) := by
        rw [hheadEq]
      _ = h0 ^ 2 * Q2 := by
        rw [ho70]
        simp only [Q2]
        ring
  have hclear4 : algebraMap k[X] (RatFunc k) Q2 = hRF ^ 4 * rho :=
    algebraMap_cancel_two_of_six_clearing610 h0 Q2 rho hh0 (by
      simpa [hquot] using hclear)
  have hQ2zero : Q2.eval a = 0 :=
    localLinearPoleFour_head_eval_zero_of_deriv_eq_simplePole610 a j h0
      Q2 rho hdegree hroot hclear4 (by simpa [rho, hRF] using hderiv)
  have hq41a : q41.eval a = 0 := by
    rw [hq41eq, Polynomial.eval_mul, hroot, zero_mul]
  have hQ2eval :
      Q2.eval a =
        o70n.eval a +
          degreeZeroPostCollapseQ41ZeroMixedOrderTwo610 (w1.eval a)
            (a42.eval a) (p32.eval a) (p21.eval a) (p1.eval a)
            (s2.eval a) (u2.eval a) (b63.eval a) (q53.eval a)
            (q41n.eval a) (q3.eval a) (q2.eval a) lambda := by
    have hfr :=
      degreeZeroPostCollapseQ41ZeroMixedOrderTwo610_of_frozen
        (w1.eval a) (a42.eval a) (p32.eval a) (p21.eval a) (p1.eval a)
        (p0.eval a) (s2.eval a) (u2.eval a) (b63.eval a) (q53.eval a)
        (q41n.eval a) (q3.eval a) (q2.eval a) (q1.eval a) lambda
    simp only [Q2, seven, Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat,
      degreeZeroPostCollapseJetOrderTwoPlus610_eval, hroot, hq41a]
    rw [add_assoc]
    exact congrArg (fun z : k ↦ o70n.eval a + z) hfr
  obtain ⟨Q3, hQ3⟩ := linearPolynomial_dvd_of_eval_eq_zero_610 h0 Q2 a
    hdegree hroot hQ2zero
  refine ⟨q41n, q41nn, o70n, hq41eq, hq41nTaylor, ho70, ?_, ?_⟩
  · rw [← hQ2eval]
    exact hQ2zero
  · refine ⟨Q3, ?_⟩
    calc
      quotient = h0 ^ 2 * Q2 := hquot
      _ = h0 ^ 2 * (h0 * Q3) := by rw [hQ3]
      _ = h0 ^ 3 * Q3 := by ring

theorem degreeZeroPostCollapseP32P21P1ZeroOrderFourHead610_zero_of_source
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (w1 a42 p32 p21 s2 u2 b63 q53 q41 : k[X])
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hh0degree : h0.natDegree = 1) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0)
    (hw : p.coeff 5 = h0 ^ 5 * w1)
    (hp4deep : p.coeff 4 = h0 ^ 4 * a42)
    (hp3deep : p.coeff 3 = h0 ^ 2 * p32)
    (hp2deep : p.coeff 2 = h0 * p21)
    (hq8deep : q.coeff 8 = h0 ^ 8 * s2)
    (hq7deep : q.coeff 7 = h0 ^ 6 * u2)
    (hq6deep : q.coeff 6 = h0 ^ 5 * b63)
    (hq5deep : q.coeff 5 = h0 ^ 3 * q53)
    (hq4deep : q.coeff 4 = h0 * q41)
    (hp32 : p32.eval a = 0) (hp21 : p21.eval a = 0)
    (hp1 : (p.coeff 1).eval a = 0) :
    ∃ p32n p21n p1n o72n : k[X],
      p32 = h0 * p32n ∧ p21 = h0 * p21n ∧ p.coeff 1 = h0 * p1n ∧
        degreeZeroPostCollapseP32P21P1ZeroOrderThreeHead610 w1 a42 p32n
            p21n p1n (p.coeff 0) q41 (q.coeff 3) =
          h0 * o72n ∧
        o72n.eval a +
            degreeZeroPostCollapseP32P21P1ZeroOrderFour610 (w1.eval a)
              (a42.eval a) (p32n.eval a) (p21n.eval a) (p1n.eval a)
              ((p.coeff 0).eval a) (q53.eval a) ((q.coeff 2).eval a) =
          0 := by
  obtain ⟨p32n, p21n, p1n, o72n, hp32eq, hp21eq, hp1eq, ho72, hmix,
      _hdvd⟩ :=
    degreeZeroPostCollapseP32P21P1ZeroOrderFourHead610_zero_of_primitiveDeriv
      h0 w1 a42 p32 p21 (p.coeff 1) (p.coeff 0) s2 u2 b63 q53 q41
      (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda
      (58498535041007616 * j) a hh0 hh0degree hroot hp32 hp21 hp1
      (degreeZeroPostCollapsePrimitive610_deriv_eq_simplePole_of_source
        p q H h0 j lambda w1 a42 p32 p21 s2 u2 b63 q53 q41 hp hq hh0
        hH hp6 hq10 hN hD hw hp4deep hp3deep hp2deep hq8deep hq7deep
        hq6deep hq5deep hq4deep)
  exact ⟨p32n, p21n, p1n, o72n, hp32eq, hp21eq, hp1eq, ho72, hmix⟩

theorem degreeZeroPostCollapseQ41ZeroMixedOrderTwo610_zero_of_source
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (w1 a42 p32 p21 s2 u2 b63 q53 q41 : k[X])
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hh0degree : h0.natDegree = 1) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0)
    (hw : p.coeff 5 = h0 ^ 5 * w1)
    (hp4deep : p.coeff 4 = h0 ^ 4 * a42)
    (hp3deep : p.coeff 3 = h0 ^ 2 * p32)
    (hp2deep : p.coeff 2 = h0 * p21)
    (hq8deep : q.coeff 8 = h0 ^ 8 * s2)
    (hq7deep : q.coeff 7 = h0 ^ 6 * u2)
    (hq6deep : q.coeff 6 = h0 ^ 5 * b63)
    (hq5deep : q.coeff 5 = h0 ^ 3 * q53)
    (hq4deep : q.coeff 4 = h0 * q41)
    (hq41 : q41.eval a = 0) :
    ∃ q41n q41nn o70n : k[X],
      q41 = h0 * q41n ∧
        q41n = C (q41n.eval a) + h0 * q41nn ∧
        degreeZeroPostCollapseQ41ZeroMixedOrderOne610 w1 a42 p32 p21
            (p.coeff 1) q53 q41n (q.coeff 3) u2 =
          h0 * o70n ∧
        o70n.eval a +
            degreeZeroPostCollapseQ41ZeroMixedOrderTwo610 (w1.eval a)
              (a42.eval a) (p32.eval a) (p21.eval a)
              ((p.coeff 1).eval a) (s2.eval a) (u2.eval a)
              (b63.eval a) (q53.eval a) (q41n.eval a)
              ((q.coeff 3).eval a) ((q.coeff 2).eval a) lambda =
          0 := by
  obtain ⟨q41n, q41nn, o70n, hq41eq, hTaylor, ho70, hmix, _hdvd⟩ :=
    degreeZeroPostCollapseQ41ZeroMixedOrderTwo610_zero_of_primitiveDeriv
      h0 w1 a42 p32 p21 (p.coeff 1) (p.coeff 0) s2 u2 b63 q53 q41
      (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda
      (58498535041007616 * j) a hh0 hh0degree hroot hq41
      (degreeZeroPostCollapsePrimitive610_deriv_eq_simplePole_of_source
        p q H h0 j lambda w1 a42 p32 p21 s2 u2 b63 q53 q41 hp hq hh0
        hH hp6 hq10 hN hD hw hp4deep hp3deep hp2deep hq8deep hq7deep
        hq6deep hq5deep hq4deep)
  exact ⟨q41n, q41nn, o70n, hq41eq, hTaylor, ho70, hmix⟩

end DegreeZeroOrderFourSource610


section DegreeZeroOrder73Grandchildren610

variable {k : Type*} [Field k] [CharZero k]

/-- Source-facing joint order-`73` packet.  This is not a closure:
each surviving arm retains a residual.  Cumulative vanishing is
`M = 5` (next unused order `74`) on `(a)(b)(c)` and `M = 3` (next
unused mixed order `72`) on `(d)`. -/
theorem degreeZeroFace610_linearRoot_order73Grandchildren
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hh0degree : h0.natDegree = 1) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0) (hlambda : lambda ≠ 0) :
    ∃ (w1 a42 p32 p21 s2 u2 b63 q53 q41 : k[X]),
      p.coeff 5 = h0 ^ 5 * w1 ∧
      p.coeff 4 = h0 ^ 4 * a42 ∧
      p.coeff 3 = h0 ^ 2 * p32 ∧
      p.coeff 2 = h0 * p21 ∧
      q.coeff 8 = h0 ^ 8 * s2 ∧
      q.coeff 7 = h0 ^ 6 * u2 ∧
      q.coeff 6 = h0 ^ 5 * b63 ∧
      q.coeff 5 = h0 ^ 3 * q53 ∧
      q.coeff 4 = h0 * q41 ∧
      ((p32.eval a = 0 ∧ p21.eval a = 0 ∧
          ∃ p32n p21n : k[X],
            p32 = h0 * p32n ∧ p21 = h0 * p21n ∧
              (((p.coeff 1).eval a = 0 ∧
                  ∃ p1n o72n : k[X],
                    p.coeff 1 = h0 * p1n ∧
                      degreeZeroPostCollapseP32P21P1ZeroOrderThreeHead610
                            w1 a42 p32n p21n p1n (p.coeff 0) q41
                            (q.coeff 3) =
                          h0 * o72n ∧
                        o72n.eval a +
                            degreeZeroPostCollapseP32P21P1ZeroOrderFour610
                              (w1.eval a) (a42.eval a) (p32n.eval a)
                              (p21n.eval a) (p1n.eval a)
                              ((p.coeff 0).eval a) (q53.eval a)
                              ((q.coeff 2).eval a) =
                          0) ∨
                (degreeZeroPostCollapseP32P21ZeroOrderTwoHeadCofactor610
                      (w1.eval a) (a42.eval a) (p32n.eval a)
                      (p21n.eval a) ((p.coeff 1).eval a) (q53.eval a)
                      (q41.eval a) ((q.coeff 3).eval a) = 0 ∧
                    ∃ o71n o72n : k[X],
                      degreeZeroPostCollapseP32P21ZeroOrderTwoHead610
                            w1 a42 p32n p21n (p.coeff 1) q53 q41
                            (q.coeff 3) =
                          h0 * o71n ∧
                        o71n +
                            degreeZeroPostCollapseP32P21ZeroOrderThreeHead610
                              w1 a42 p32n p21n (p.coeff 1) (p.coeff 0)
                              u2 b63 q53 q41 (q.coeff 3) (q.coeff 2) =
                          h0 * o72n ∧
                        o72n.eval a +
                            degreeZeroPostCollapseP32P21ZeroOrderFour610
                              (w1.eval a) (a42.eval a) (p32n.eval a)
                              (p21n.eval a) ((p.coeff 1).eval a)
                              ((p.coeff 0).eval a) (s2.eval a)
                              (u2.eval a) (b63.eval a) (q53.eval a)
                              ((q.coeff 2).eval a) ((q.coeff 1).eval a)
                              lambda =
                          0))) ∨
        (p32.eval a = 0 ∧ q41.eval a = 0 ∧ (q.coeff 3).eval a = 0 ∧
          ∃ p32n q41n q3n o71n o72n : k[X],
            p32 = h0 * p32n ∧ q41 = h0 * q41n ∧
              q.coeff 3 = h0 * q3n ∧
              degreeZeroPostCollapseP32Q41Q3ZeroOrderTwoHead610 w1 a42
                  p21 (p.coeff 1) q53 q41n q3n u2 =
                h0 * o71n ∧
              o71n +
                  degreeZeroPostCollapseP32Q41Q3ZeroOrderThreeHead610
                    w1 a42 p32n p21 (p.coeff 1) (p.coeff 0) s2 u2 b63
                    q53 q41n q3n (q.coeff 2) (Polynomial.C lambda) =
                h0 * o72n ∧
              o72n.eval a +
                  degreeZeroPostCollapseP32Q41Q3ZeroOrderFour610
                    (w1.eval a) (a42.eval a) (p32n.eval a)
                    (p21.eval a) ((p.coeff 1).eval a)
                    ((p.coeff 0).eval a) (s2.eval a) (u2.eval a)
                    (b63.eval a) (q53.eval a) (q41n.eval a)
                    (q3n.eval a) ((q.coeff 2).eval a)
                    ((q.coeff 1).eval a) lambda =
                0 ∧
              (p21.eval a = 0 →
                (p.coeff 1).eval a = 0 ∨ q53.eval a = 0)) ∨
        (q41.eval a = 0 ∧
          10 * (p32.eval a) ^ 2 * (q53.eval a) +
              (18 * (p32.eval a) * (w1.eval a) -
                27 * (p21.eval a)) * (q.coeff 3).eval a = 0 ∧
          ∃ q41n q41nn o70n : k[X],
            q41 = h0 * q41n ∧
              q41n = C (q41n.eval a) + h0 * q41nn ∧
              degreeZeroPostCollapseQ41ZeroMixedOrderOne610 w1 a42 p32
                  p21 (p.coeff 1) q53 q41n (q.coeff 3) u2 =
                h0 * o70n ∧
              o70n.eval a +
                  degreeZeroPostCollapseQ41ZeroMixedOrderTwo610
                    (w1.eval a) (a42.eval a) (p32.eval a)
                    (p21.eval a) ((p.coeff 1).eval a) (s2.eval a)
                    (u2.eval a) (b63.eval a) (q53.eval a)
                    (q41n.eval a) ((q.coeff 3).eval a)
                    ((q.coeff 2).eval a) lambda =
                0 ∧
              (p32.eval a = 0 ∨
                degreeZeroPostCollapseQ41ZeroMixedFiveReduced610
                    (w1.eval a) (a42.eval a) (p32.eval a)
                    (p21.eval a) ((p.coeff 1).eval a) (q41n.eval a)
                    ((q.coeff 3).eval a) (u2.eval a) = 0))) := by
  obtain ⟨w1, a42, p32, p21, s2, u2, b63, q53, q41, hw, hp4deep,
      hp3deep, hp2deep, hq8deep, hq7deep, hq6deep, hq5deep, hq4deep,
      hpacket⟩ :=
    degreeZeroFace610_linearRoot_order72Grandchildren p q H h0 j lambda
      a hp hq hh0 hh0degree hH hp6 hq10 hN hD hroot hlambda
  refine ⟨w1, a42, p32, p21, s2, u2, b63, q53, q41, hw, hp4deep,
    hp3deep, hp2deep, hq8deep, hq7deep, hq6deep, hq5deep, hq4deep, ?_⟩
  rcases hpacket with hAB | hC | hD
  · obtain ⟨hp32, hp21, p32n, p21n, hp32eq, hp21eq, hsplit⟩ := hAB
    refine Or.inl ⟨hp32, hp21, p32n, p21n, hp32eq, hp21eq, ?_⟩
    rcases hsplit with hp1pack | hcof
    · obtain ⟨hp1, p1n, hp1eq, _hhead72⟩ := hp1pack
      obtain ⟨p32n', p21n', p1n', o72n, hp32eq', hp21eq', hp1eq', ho72,
          hmix⟩ :=
        degreeZeroPostCollapseP32P21P1ZeroOrderFourHead610_zero_of_source
          p q H h0 j lambda a w1 a42 p32 p21 s2 u2 b63 q53 q41 hp hq
          hh0 hh0degree hH hp6 hq10 hN hD hroot hw hp4deep hp3deep
          hp2deep hq8deep hq7deep hq6deep hq5deep hq4deep hp32 hp21 hp1
      have hp32n : p32n' = p32n := by
        apply mul_left_cancel₀ hh0
        rw [← hp32eq', ← hp32eq]
      have hp21n : p21n' = p21n := by
        apply mul_left_cancel₀ hh0
        rw [← hp21eq', ← hp21eq]
      have hp1n : p1n' = p1n := by
        apply mul_left_cancel₀ hh0
        rw [← hp1eq', ← hp1eq]
      refine Or.inl ⟨hp1, p1n, o72n, hp1eq, ?_, ?_⟩
      · simpa [hp32n, hp21n, hp1n] using ho72
      · simpa [hp32n, hp21n, hp1n] using hmix
    · obtain ⟨hcof0, o71n, ho71, _hmix72⟩ := hcof
      obtain ⟨p32n', p21n', o71n', o72n, hp32eq', hp21eq', ho71', ho72,
          hmix, _hdvd⟩ :=
        degreeZeroPostCollapseP32P21ZeroOrderFourHead610_zero_of_primitiveDeriv
          h0 w1 a42 p32 p21 (p.coeff 1) (p.coeff 0) s2 u2 b63 q53 q41
          (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda
          (58498535041007616 * j) a hh0 hh0degree hroot hp32 hp21
          (degreeZeroPostCollapsePrimitive610_deriv_eq_simplePole_of_source
            p q H h0 j lambda w1 a42 p32 p21 s2 u2 b63 q53 q41 hp hq
            hh0 hH hp6 hq10 hN hD hw hp4deep hp3deep hp2deep hq8deep
            hq7deep hq6deep hq5deep hq4deep)
      have hp32n : p32n' = p32n := by
        apply mul_left_cancel₀ hh0
        rw [← hp32eq', ← hp32eq]
      have hp21n : p21n' = p21n := by
        apply mul_left_cancel₀ hh0
        rw [← hp21eq', ← hp21eq]
      refine Or.inr ⟨hcof0, o71n', o72n, ?_, ?_, ?_⟩
      · simpa [hp32n, hp21n] using ho71'
      · simpa [hp32n, hp21n] using ho72
      · simpa [hp32n, hp21n] using hmix
  · obtain ⟨hp32, hq41, hq3, p32n, q41n, q3n, o71n, hp32eq, hq41eq,
        hq3eq, ho71, _hmix72, hp21split⟩ := hC
    obtain ⟨p32n', q41n', q3n', o71n', o72n, hp32eq', hq41eq', hq3eq',
        ho71', ho72, hmix, _hdvd⟩ :=
      degreeZeroPostCollapseP32Q41Q3ZeroOrderFourHead610_zero_of_primitiveDeriv
        h0 w1 a42 p32 p21 (p.coeff 1) (p.coeff 0) s2 u2 b63 q53 q41
        (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda
        (58498535041007616 * j) a hh0 hh0degree hroot hp32 hq41 hq3
        (degreeZeroPostCollapsePrimitive610_deriv_eq_simplePole_of_source
          p q H h0 j lambda w1 a42 p32 p21 s2 u2 b63 q53 q41 hp hq hh0
          hH hp6 hq10 hN hD hw hp4deep hp3deep hp2deep hq8deep hq7deep
          hq6deep hq5deep hq4deep)
    have hp32n : p32n' = p32n := by
      apply mul_left_cancel₀ hh0
      rw [← hp32eq', ← hp32eq]
    have hq41n : q41n' = q41n := by
      apply mul_left_cancel₀ hh0
      rw [← hq41eq', ← hq41eq]
    have hq3n : q3n' = q3n := by
      apply mul_left_cancel₀ hh0
      rw [← hq3eq', ← hq3eq]
    refine Or.inr (Or.inl ⟨hp32, hq41, hq3, p32n, q41n, q3n, o71n',
      o72n, hp32eq, hq41eq, hq3eq, ?_, ?_, ?_, hp21split⟩)
    · simpa [hp32n, hq41n, hq3n] using ho71'
    · simpa [hp32n, hq41n, hq3n] using ho72
    · simpa [hp32n, hq41n, hq3n] using hmix
  · obtain ⟨hq41, hfive, q41n, hq41eq, hmixed, hred⟩ := hD
    obtain ⟨q41n', q41nn, o70n, hq41eq', hTaylor, ho70, hmix⟩ :=
      degreeZeroPostCollapseQ41ZeroMixedOrderTwo610_zero_of_source p q
        H h0 j lambda a w1 a42 p32 p21 s2 u2 b63 q53 q41 hp hq hh0
        hh0degree hH hp6 hq10 hN hD hroot hw hp4deep hp3deep hp2deep
        hq8deep hq7deep hq6deep hq5deep hq4deep hq41
    have hq41n : q41n' = q41n := by
      apply mul_left_cancel₀ hh0
      rw [← hq41eq', ← hq41eq]
    refine Or.inr (Or.inr ⟨hq41, hfive, q41n, q41nn, o70n, hq41eq,
      ?_, ?_, ?_, hred⟩)
    · simpa [hq41n] using hTaylor
    · simpa [hq41n] using ho70
    · simpa [hq41n] using hmix

#print axioms localLinearPoleTwo_head_eval_zero_of_deriv_eq_simplePole610
#print axioms algebraMap_cancel_four_of_six_clearing610
#print axioms degreeZeroPostCollapseP32P21P1ZeroOrderThreePlus610_zero
#print axioms degreeZeroPostCollapseP32Q41Q3ZeroOrderThreeHead610_p21P1Zero
#print axioms degreeZeroPostCollapseP32Q41Q3ZeroOrderThreeHead610_p21Q53Zero_split
#print axioms degreeZeroPostCollapseQ41ZeroMixedOrderOne610_q41nLinear
#print axioms degreeZeroPostCollapseP32P21P1ZeroOrderFourHead610_zero_of_source
#print axioms degreeZeroPostCollapseQ41ZeroMixedOrderTwo610_zero_of_source
#print axioms degreeZeroFace610_linearRoot_order73Grandchildren

end DegreeZeroOrder73Grandchildren610

end Max11DegreeRoutes
