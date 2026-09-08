import Grok610DegreeZeroOrder74Scratch
import Grok610PoleCeilingLemmaScratch

/-! # Order-`75` frozen-head ceiling of the `(6,10)` degree-zero tower

`Grok610DegreeZeroOrder74Scratch` leaves four live arms, all with a
simple-pole derivative.  The jet quotient has `h`-degree at most `6`, so
the coefficient of `h^6` is the last frozen head (order `75`).

This file extracts that head on `(a)(b)(c)` and applies the pole
obstruction.

On each of those arms the order-`74` remainder peels as
`OrderFourPlus = OrderFive + h · OrderSix` with `OrderSix` independent
of `h`.  Combined with the landed residual
`o73n(a) + OrderFive(a) = 0` this identifies the remaining factor after
`h0^6` as `o74n + OrderSix`.  Cancelling all six clearing powers shows
that this remaining factor *is* `rho`.  A polynomial cannot have
derivative `C j / h0` with `j ≠ 0`, so each of `(a)(b)(c)` is False.

This is the holomorphic case of the order-`75` ceiling: after the last
frozen head there is no remaining pole, so the ceiling lemmas' `A0 = 0`
path is replaced by the equivalent statement that the remaining
numerator *is* `rho`.  Taylor mixins of the compact coordinates are not
required on these arms.

**CLOSED:** arm `(a)` (46-term hypersurface / `p32 = p21 = p1 = 0`).
**CLOSED:** arm `(b)` (9-term cofactor / `p32 = p21 = 0`).
**CLOSED:** arm `(c)` (`p32 = q41 = q3 = 0`, both subpackets).

Arm `(d)` (mixed tower at order `72`, `M = 4`) is copied unchanged from
order `74` and is not advanced.  Cumulative vanishing on the surviving
arm remains `h0^4 ∣` the jet quotient; next unused mixed order `73`.

No total-degree or twice-prime theorem is used.  No `sorry`, no new
axioms, no finite-root shortcut.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option maxHeartbeats 800000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section LinearPoleZero610

variable {k : Type*} [Field k] [CharZero k]

/-- Cancel all six polynomial powers from a pole-six clearing. -/
theorem algebraMap_cancel_six_of_six_clearing610
    (h0 Q6 : k[X]) (rho : RatFunc k) (hh0 : h0 ≠ 0)
    (hquot :
      algebraMap k[X] (RatFunc k) (h0 ^ 6 * Q6) =
        (algebraMap k[X] (RatFunc k) h0) ^ 6 * rho) :
    algebraMap k[X] (RatFunc k) Q6 = rho := by
  let hRF : RatFunc k := algebraMap k[X] (RatFunc k) h0
  have hhRF : hRF ≠ 0 := RatFunc.algebraMap_ne_zero hh0
  apply mul_left_cancel₀ (pow_ne_zero 6 hhRF)
  have hmapPow :
      algebraMap k[X] (RatFunc k) (h0 ^ 6 * Q6) =
        hRF ^ 6 * algebraMap k[X] (RatFunc k) Q6 := by
    simp only [hRF, map_mul, map_pow]
  calc
    hRF ^ 6 * algebraMap k[X] (RatFunc k) Q6 =
        algebraMap k[X] (RatFunc k) (h0 ^ 6 * Q6) := hmapPow.symm
    _ = hRF ^ 6 * rho := hquot

/-- A rational function that is the image of a polynomial cannot have
derivative `C j / h0` with `j ≠ 0`: evaluating `h0 * (remaining)' = C j`
at the simple root forces `j = 0`. -/
theorem localLinearPoleZero_C_eq_zero_of_deriv_eq_simplePole610
    (a j : k) (h0 A0 : k[X]) (rho : RatFunc k) (hh0 : h0 ≠ 0)
    (hroot : h0.eval a = 0)
    (hclear : algebraMap k[X] (RatFunc k) A0 = rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    j = 0 := by
  have hhRF : algebraMap k[X] (RatFunc k) h0 ≠ 0 :=
    RatFunc.algebraMap_ne_zero hh0
  have hderivA :
      algebraMap k[X] (RatFunc k) (derivative A0) =
        RatFunc.C j / algebraMap k[X] (RatFunc k) h0 := by
    rw [← hderiv, ← hclear, GCD369RatFuncDerivative]
  have hpoly : h0 * derivative A0 = Polynomial.C j := by
    apply FaithfulSMul.algebraMap_injective k[X] (RatFunc k)
    rw [map_mul, hderivA, mul_div_cancel₀ _ hhRF]
    simp only [RatFunc.algebraMap_C]
  have heval := congrArg (fun p : k[X] ↦ p.eval a) hpoly
  have heval' : (0 : k) = j := by
    simpa [hroot, Polynomial.eval_mul, Polynomial.eval_C] using heval
  exact heval'.symm

/-- Ceiling of a pole-six clearing whose numerator is already divisible
by `h0^6`: the remaining factor is `rho` itself, so the simple-pole
equation forces `j = 0`. -/
theorem localLinearPoleSix_of_pow_six_dvd_simplePole_eval610
    (a j : k) (h0 A0 Q6 : k[X]) (rho : RatFunc k) (hh0 : h0 ≠ 0)
    (hroot : h0.eval a = 0) (hA : A0 = h0 ^ 6 * Q6)
    (hclear : algebraMap k[X] (RatFunc k) A0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 6 * rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    j = 0 :=
  localLinearPoleZero_C_eq_zero_of_deriv_eq_simplePole610 a j h0 Q6 rho
    hh0 hroot
    (algebraMap_cancel_six_of_six_clearing610 h0 Q6 rho hh0
      (by simpa [hA] using hclear))
    hderiv

/-- Same holomorphic remainder, with `j ≠ 0`, is False.  This is the
companion of `localLinearPoleSix_simplePole_contradicts_eq_zero610` for
the case where the remaining numerator *is* `rho` rather than the zero
polynomial. -/
theorem localLinearPoleSix_of_pow_six_dvd_simplePole_ne_zero610
    (a j : k) (h0 A0 Q6 : k[X]) (rho : RatFunc k) (hh0 : h0 ≠ 0)
    (hroot : h0.eval a = 0) (hA : A0 = h0 ^ 6 * Q6)
    (hclear : algebraMap k[X] (RatFunc k) A0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 6 * rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
    (hj : j ≠ 0) : False :=
  hj (localLinearPoleSix_of_pow_six_dvd_simplePole_eval610 a j h0 A0 Q6
    rho hh0 hroot hA hclear hderiv)

/-- Source-facing form: `h0^6` divides the jet quotient of the compact
primitive, so a simple pole with `j ≠ 0` is impossible. -/
theorem degreeZeroPostCollapseJetQuotient610_pow_six_dvd_contradicts_simplePole
    (h0 w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 : k[X])
    (lambda j a : k) (hh0 : h0 ≠ 0) (hroot : h0.eval a = 0)
    (hdvd :
      h0 ^ 6 ∣
        degreeZeroPostCollapseJetQuotient610 h0 w1 a42 p32 p21 p1 p0 s2
          u2 b63 q53 q41 q3 q2 q1 (Polynomial.C lambda))
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
        RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
    (hj : j ≠ 0) : False := by
  obtain ⟨Q6, hQ6⟩ := hdvd
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
  exact localLinearPoleSix_of_pow_six_dvd_simplePole_ne_zero610 a j h0
    quotient Q6 rho hh0 hroot hQ6 hclear (by simpa [rho, hRF] using hderiv)
    hj

end LinearPoleZero610

section DegreeZeroOrderSixHead610

variable {R : Type*} [CommRing R]

/-- Frozen order-`75` mixin on `p32 = h · p32n`, `p21 = h · p21n`,
`p1 = h · p1n`: the `h^1` part of the order-`74` remainder.  Independent
of `h` (last frozen head). -/
def degreeZeroPostCollapseP32P21P1ZeroOrderSix610
    (w1 a42 p32n p21n p1n p0 s2 lambda : R) : R :=
  -547985470548040*w1^15+6503598706655232*p32n^5+18957858578104320*p1n^3-90327759814656000*a42^3*p32n^3-66841109595187200*a42^4*w1^7-43968570431385600*p32n^3*w1^6-41075360252559360*p0*p32n^3-41075360252559360*p21n^3*p32n-37752848938022400*a42^2*w1^11-36205601030726400*p32n^2*w1^9-34375427791810560*a42^5*w1^5-34261223712768000*p21n^2*w1^7-31614715935129600*p1n^2*w1^5-27383573501706240*p0^2*w1^3-27098327944396800*a42^5*p1n-15556447523635200*a42^7*w1-9747661815964800*p1n*w1^10-8061806283640200*p32n*w1^12-1000057340805120*a42^7*lambda+264207280442805*lambda*w1^14+810718230399840*s2*w1^13+7226220785172480*p21n^3*w1^3+7431583778665200*a42*w1^13+8819313071587200*p21n*w1^11+10912834219622400*p0*w1^9+15054626635776000*p32n^4*w1^3+23334671285452800*a42^6*p32n+56873575734312960*p0^2*p32n+63954284263833600*a42^6*w1^3+85098634901280000*a42^3*w1^9-388911188090880000*a42^3*p32n^2*w1^3-221679377211801600*a42^5*p32n*w1^2-213056036834659200*a42^2*p32n*w1^8-194455594045440000*a42^4*p21n*w1^3-173429298844139520*a42^3*p21n^2*w1-160418663028449280*a42^3*s2*w1^7-135491639721984000*a42^4*p21n*p32n-131905711294156800*a42^2*p1n*w1^6-123226080757678080*a42*p1n*p21n^2-123226080757678080*a42*p1n^2*p32n-123226080757678080*a42^2*p0*p1n-123226080757678080*p1n*p21n*p32n^2-115117711674900480*a42^5*s2*w1^3-86714649422069760*a42*p32n^4*w1-86714649422069760*a42^4*p0*w1-77344712531573760*a42^5*lambda*w1^4-75875318244311040*p21n*p32n^3*w1^2-72411202061452800*a42*p21n*w1^9-71948569796812800*a42^2*p32n^2*w1^5-68929894270036800*a42^3*lambda*w1^8-68522447425536000*a42*p0*w1^7-68522447425536000*p1n*p32n*w1^7-63229431870259200*p0*p21n*w1^5-56454849884160000*p1n*p32n^2*w1^4-56454849884160000*p21n^2*p32n*w1^4-47965713197875200*a42^3*p21n*w1^5-37915717156208640*a42*p0^2*w1-37915717156208640*p0*p21n^2*w1-37915717156208640*p1n^2*p21n*w1-32860288202047488*p21n*p32n^3*s2-32860288202047488*p21n^3*s2*w1-21678662355517440*a42^5*p32n*s2-19510796119965696*a42^3*lambda*p21n^2-19510796119965696*lambda*p21n^3*w1^2-19445559404544000*a42*p32n^3*w1^4-19445559404544000*a42^3*p1n*w1^4-17062072720293888*a42*lambda*p0^2-17062072720293888*lambda*p0*p21n^2-17062072720293888*lambda*p1n^2*p21n-16445387382128640*p0*s2*w1^7-13368221919037440*p21n*s2*w1^9-11325854681406720*a42*s2*w1^11-9755398059982848*a42*lambda*p32n^4-9755398059982848*a42^4*lambda*p0-5524622323683840*lambda*p0*w1^8-4595326284669120*lambda*p21n*w1^10-3952251373199220*a42*lambda*w1^12+4247195505527520*lambda*p32n*w1^11+5013083219639040*lambda*p1n*w1^9+8129498383319040*a42^5*lambda*p21n+10268840063139840*p1n*p21n^2*w1^2+10268840063139840*p1n^2*p32n*w1^2+12254203425784320*p32n*s2*w1^10+12322608075767808*a42*lambda*p21n^3+12322608075767808*lambda*p1n*p32n^3+14732326196490240*p1n*s2*w1^8+18483912113651712*a42^2*lambda*p1n^2+18483912113651712*lambda*p0^2*w1^2+18483912113651712*lambda*p21n^2*p32n^2+18667737028362240*a42^6*s2*w1+20323745958297600*a42^4*lambda*p32n^2+20323745958297600*lambda*p1n^2*w1^4+20323745958297600*lambda*p32n^4*w1^2+21584570939043840*a42^6*lambda*w1^2+21584570939043840*lambda*p21n^2*w1^6+21678662355517440*a42*p1n^2*w1^3+21678662355517440*p0*p32n^2*w1^3+22558874488375680*lambda*p32n^2*w1^8+23359575280401360*a42^2*lambda*w1^10+26014394826620928*a42^4*p1n*s2+26014394826620928*p32n^4*s2*w1+43169141878087680*lambda*p32n^3*w1^5+45498860587450368*p1n*p21n^2*s2+45498860587450368*p1n^2*p32n*s2+45498860587450368*p0^2*s2*w1+52028789653241856*a42^2*p32n^3*s2+52028789653241856*p1n^2*s2*w1^3+56003211085086720*p21n^2*s2*w1^5+58929304785960960*p32n^2*s2*w1^7+59616321477672960*p0*p1n*w1^4+60218506543104000*a42^3*p0*w1^3+61271017128921600*a42^2*s2*w1^9+66114901975449600*p0*p32n*w1^6+66114901975449600*p1n*p21n*w1^6+68458933754265600*a42*p21n^3*w1+68458933754265600*p1n*p32n^3*w1+70592396358182400*a42*p1n*w1^8+70592396358182400*p21n*p32n*w1^8+74035812364113600*a42*p32n*w1^10+90327759814656000*a42^2*p21n^2*w1^3+93338685141811200*a42*p21n^2*w1^5+93338685141811200*a42^2*p0*w1^5+93338685141811200*p21n*p32n^2*w1^5+93338685141811200*p32n^3*s2*w1^4+99360535796121600*a42^5*p21n*w1+102688400631398400*a42^2*p1n^2*w1+102688400631398400*p21n^2*p32n^2*w1+105274747612419840*a42^4*lambda*w1^6+113747151468625920*p0*p1n*p21n+130071974133104640*a42*p21n*p32n^3+130071974133104640*a42^3*p0*p32n+130071974133104640*a42^3*p1n*p21n+143230949132544000*a42^3*p32n*w1^6+146782609698816000*a42^4*p1n*w1^2+171877138959052800*a42*p32n^2*w1^7+171877138959052800*a42^2*p21n*w1^7+195107961199656960*a42^2*p1n*p32n^2+195107961199656960*a42^2*p21n^2*p32n+206252566750863360*a42^4*s2*w1^5+209849995240704000*a42^4*p32n*w1^4+248401339490304000*a42^4*p32n^2*w1+293565219397632000*a42^2*p32n^3*w1^2-575588558374502400*a42^3*p32n*s2*w1^4-520287896532418560*a42^2*p21n*p32n^2*w1-346858597688279040*a42^3*p1n*p32n*w1-345353135024701440*a42*p32n^2*s2*w1^5-345353135024701440*a42^2*p21n*s2*w1^5-309378850126295040*a42^3*lambda*p32n*w1^5-263811422588313600*a42*p21n*p32n*w1^6-246452161515356160*a42*p0*p21n*p32n-227625954732933120*a42*p1n*p32n^2*w1^2-227625954732933120*a42*p21n^2*p32n*w1^2-227625954732933120*a42^2*p0*p32n*w1^2-227625954732933120*a42^2*p1n*p21n*w1^2-216786623555174400*a42*p21n^2*s2*w1^3-216786623555174400*a42*p32n^3*s2*w1^2-216786623555174400*a42^2*p0*s2*w1^3-216786623555174400*a42^3*p1n*s2*w1^2-216786623555174400*p21n*p32n^2*s2*w1^3-216786623555174400*a42^3*p32n^2*s2*w1-210012041569075200*a42^3*lambda*p32n^2*w1^2-154689425063147520*a42*lambda*p32n^2*w1^6-154689425063147520*a42^2*lambda*p21n*w1^6-140008027712716800*a42*lambda*p32n^3*w1^3-140008027712716800*a42^3*lambda*p1n*w1^3-120313997271336960*a42*p32n*s2*w1^8-115117711674900480*a42*p1n*s2*w1^6-115117711674900480*p21n*p32n*s2*w1^6-112909699768320000*a42*p0*p32n*w1^4-112909699768320000*a42*p1n*p21n*w1^4-108393311777587200*p0*p32n*s2*w1^4-108393311777587200*p1n*p21n*s2*w1^4-108393311777587200*a42^4*p21n*s2*w1-105006020784537600*a42*lambda*p21n^2*w1^4-105006020784537600*a42^2*lambda*p0*w1^4-105006020784537600*a42^4*lambda*p21n*w1^2-105006020784537600*lambda*p21n*p32n^2*w1^4-98580864606142464*a42*p1n*p32n^2*s2-98580864606142464*a42*p21n^2*p32n*s2-98580864606142464*a42*p1n^2*s2*w1-98580864606142464*p0*p1n*s2*w1^2-98580864606142464*a42^2*p0*p32n*s2-98580864606142464*p0*p32n^2*s2*w1-98580864606142464*a42^2*p1n*p21n*s2-75831434312417280*p0*p1n*p32n*w1-58532388359897088*a42*lambda*p1n^2*w1^2-58532388359897088*lambda*p0*p32n^2*w1^2-58532388359897088*a42^2*lambda*p21n*p32n^2-58336678213632000*a42^2*p21n*p32n*w1^4-45953262846691200*a42*lambda*p32n*w1^9-44196978589470720*a42*lambda*p1n*w1^7-44196978589470720*lambda*p21n*p32n*w1^7-42002408313815040*lambda*p0*p32n*w1^5-42002408313815040*lambda*p1n*p21n*w1^5-42002408313815040*a42^5*lambda*p32n*w1-39021592239931392*lambda*p0*p1n*w1^3-39021592239931392*a42^3*lambda*p1n*p32n-39021592239931392*lambda*p21n*p32n^3*w1-34124145440587776*lambda*p0*p1n*p32n+20537680126279680*a42*p0*p1n*w1^2+20537680126279680*p0*p21n*p32n*w1^2+36967824227303424*a42*lambda*p0*p32n^2+36967824227303424*a42^2*lambda*p0*p21n+36967824227303424*lambda*p1n*p21n^2*w1+36967824227303424*lambda*p1n^2*p32n*w1+40647491916595200*lambda*p0*p21n*w1^4+40647491916595200*a42^4*lambda*p1n*w1+43169141878087680*a42*lambda*p0*w1^6+43169141878087680*lambda*p1n*p32n*w1^6+43357324711034880*a42*p0*p21n*w1^3+43357324711034880*p1n*p21n*p32n*w1^3+45117748976751360*a42*lambda*p21n*w1^8+81294983833190400*a42^3*lambda*p0*w1^2+81294983833190400*lambda*p1n*p32n^2*w1^3+81294983833190400*lambda*p21n^2*p32n*w1^3+81294983833190400*a42^2*lambda*p32n^3*w1+90997721174900736*a42*p0*p1n*s2+90997721174900736*p0*p21n*p32n*s2+104057579306483712*p0*p21n*s2*w1^3+104057579306483712*a42^3*p0*s2*w1+104057579306483712*a42^3*p21n*p32n*s2+112006422170173440*a42*p0*s2*w1^5+112006422170173440*p1n*p32n*s2*w1^5+117858609571921920*a42*p21n*s2*w1^7+121942475749785600*a42^2*lambda*p21n^2*w1^2+129507425634263040*a42^2*lambda*p1n*w1^5+156086368959725568*p1n*p32n^2*s2*w1^2+156086368959725568*p21n^2*p32n*s2*w1^2+156086368959725568*a42^2*p21n^2*s2*w1+180470995907005440*a42^2*lambda*p32n*w1^7+180655519629312000*a42*p21n*p32n^2*w1^3+180655519629312000*a42^2*p1n*p32n*w1^3+186677370283622400*a42*p1n*p32n*w1^5+205376801262796800*a42*p0*p32n^2*w1+205376801262796800*a42^2*p0*p21n*w1+215845709390438400*a42^3*lambda*p21n*w1^4+215845709390438400*a42^4*lambda*p32n*w1^3+280016055425433600*a42^2*p1n*s2*w1^4+280016055425433600*a42^4*p32n*s2*w1^2+323768564085657600*a42^2*lambda*p32n^2*w1^4+373354740567244800*a42^3*p21n*s2*w1^3+412505133501726720*a42^2*p32n*s2*w1^6+560032110850867200*a42^2*p32n^2*s2*w1^3+587130438795264000*a42^3*p21n*p32n*w1^2-650359870665523200*a42^2*p21n*p32n*s2*w1^2-433573247110348800*a42*p1n*p32n*s2*w1^3-420024083138150400*a42^2*lambda*p21n*p32n*w1^3-210012041569075200*a42*lambda*p1n*p32n*w1^4-197161729212284928*a42*p0*p21n*s2*w1-197161729212284928*p1n*p21n*p32n*s2*w1-117064776719794176*a42*lambda*p0*p21n*w1^2-117064776719794176*a42*lambda*p1n*p32n^2*w1-117064776719794176*a42*lambda*p21n^2*p32n*w1-117064776719794176*a42^2*lambda*p0*p32n*w1-117064776719794176*lambda*p1n*p21n*p32n*w1^2-117064776719794176*a42^2*lambda*p1n*p21n*w1+73935648454606848*a42*lambda*p0*p1n*w1+73935648454606848*a42*lambda*p1n*p21n*p32n+73935648454606848*lambda*p0*p21n*p32n*w1+162589967666380800*a42*lambda*p0*p32n*w1^3+162589967666380800*a42*lambda*p1n*p21n*w1^3+162589967666380800*a42^3*lambda*p21n*p32n*w1+243884951499571200*a42*lambda*p21n*p32n^2*w1^2+243884951499571200*a42^2*lambda*p1n*p32n*w1^2+259014851268526080*a42*lambda*p21n*p32n*w1^5+312172737919451136*a42*p0*p32n*s2*w1^2+312172737919451136*a42*p1n*p21n*s2*w1^2+312172737919451136*a42*p21n*p32n^2*s2*w1+312172737919451136*a42^2*p1n*p32n*s2*w1+410753602525593600*a42*p1n*p21n*p32n*w1+560032110850867200*a42*p21n*p32n*s2*w1^4

/-- Frozen order-`75` mixin on `p32 = h · p32n`, `p21 = h · p21n`.
Independent of `h` (last frozen head). -/
def degreeZeroPostCollapseP32P21ZeroOrderSix610
    (w1 a42 p32n p21n p0 s2 lambda : R) : R :=
  -547985470548040*w1^15+6503598706655232*p32n^5-90327759814656000*a42^3*p32n^3-66841109595187200*a42^4*w1^7-43968570431385600*p32n^3*w1^6-41075360252559360*p0*p32n^3-41075360252559360*p21n^3*p32n-37752848938022400*a42^2*w1^11-36205601030726400*p32n^2*w1^9-34375427791810560*a42^5*w1^5-34261223712768000*p21n^2*w1^7-27383573501706240*p0^2*w1^3-15556447523635200*a42^7*w1-8061806283640200*p32n*w1^12-1000057340805120*a42^7*lambda+264207280442805*lambda*w1^14+810718230399840*s2*w1^13+7226220785172480*p21n^3*w1^3+7431583778665200*a42*w1^13+8819313071587200*p21n*w1^11+10912834219622400*p0*w1^9+15054626635776000*p32n^4*w1^3+23334671285452800*a42^6*p32n+56873575734312960*p0^2*p32n+63954284263833600*a42^6*w1^3+85098634901280000*a42^3*w1^9-388911188090880000*a42^3*p32n^2*w1^3-221679377211801600*a42^5*p32n*w1^2-213056036834659200*a42^2*p32n*w1^8-194455594045440000*a42^4*p21n*w1^3-173429298844139520*a42^3*p21n^2*w1-160418663028449280*a42^3*s2*w1^7-135491639721984000*a42^4*p21n*p32n-115117711674900480*a42^5*s2*w1^3-86714649422069760*a42*p32n^4*w1-86714649422069760*a42^4*p0*w1-77344712531573760*a42^5*lambda*w1^4-75875318244311040*p21n*p32n^3*w1^2-72411202061452800*a42*p21n*w1^9-71948569796812800*a42^2*p32n^2*w1^5-68929894270036800*a42^3*lambda*w1^8-68522447425536000*a42*p0*w1^7-63229431870259200*p0*p21n*w1^5-56454849884160000*p21n^2*p32n*w1^4-47965713197875200*a42^3*p21n*w1^5-37915717156208640*a42*p0^2*w1-37915717156208640*p0*p21n^2*w1-32860288202047488*p21n*p32n^3*s2-32860288202047488*p21n^3*s2*w1-21678662355517440*a42^5*p32n*s2-19510796119965696*a42^3*lambda*p21n^2-19510796119965696*lambda*p21n^3*w1^2-19445559404544000*a42*p32n^3*w1^4-17062072720293888*a42*lambda*p0^2-17062072720293888*lambda*p0*p21n^2-16445387382128640*p0*s2*w1^7-13368221919037440*p21n*s2*w1^9-11325854681406720*a42*s2*w1^11-9755398059982848*a42*lambda*p32n^4-9755398059982848*a42^4*lambda*p0-5524622323683840*lambda*p0*w1^8-4595326284669120*lambda*p21n*w1^10-3952251373199220*a42*lambda*w1^12+4247195505527520*lambda*p32n*w1^11+8129498383319040*a42^5*lambda*p21n+12254203425784320*p32n*s2*w1^10+12322608075767808*a42*lambda*p21n^3+18483912113651712*lambda*p0^2*w1^2+18483912113651712*lambda*p21n^2*p32n^2+18667737028362240*a42^6*s2*w1+20323745958297600*a42^4*lambda*p32n^2+20323745958297600*lambda*p32n^4*w1^2+21584570939043840*a42^6*lambda*w1^2+21584570939043840*lambda*p21n^2*w1^6+21678662355517440*p0*p32n^2*w1^3+22558874488375680*lambda*p32n^2*w1^8+23359575280401360*a42^2*lambda*w1^10+26014394826620928*p32n^4*s2*w1+43169141878087680*lambda*p32n^3*w1^5+45498860587450368*p0^2*s2*w1+52028789653241856*a42^2*p32n^3*s2+56003211085086720*p21n^2*s2*w1^5+58929304785960960*p32n^2*s2*w1^7+60218506543104000*a42^3*p0*w1^3+61271017128921600*a42^2*s2*w1^9+66114901975449600*p0*p32n*w1^6+68458933754265600*a42*p21n^3*w1+70592396358182400*p21n*p32n*w1^8+74035812364113600*a42*p32n*w1^10+90327759814656000*a42^2*p21n^2*w1^3+93338685141811200*a42*p21n^2*w1^5+93338685141811200*a42^2*p0*w1^5+93338685141811200*p21n*p32n^2*w1^5+93338685141811200*p32n^3*s2*w1^4+99360535796121600*a42^5*p21n*w1+102688400631398400*p21n^2*p32n^2*w1+105274747612419840*a42^4*lambda*w1^6+130071974133104640*a42*p21n*p32n^3+130071974133104640*a42^3*p0*p32n+143230949132544000*a42^3*p32n*w1^6+171877138959052800*a42*p32n^2*w1^7+171877138959052800*a42^2*p21n*w1^7+195107961199656960*a42^2*p21n^2*p32n+206252566750863360*a42^4*s2*w1^5+209849995240704000*a42^4*p32n*w1^4+248401339490304000*a42^4*p32n^2*w1+293565219397632000*a42^2*p32n^3*w1^2-575588558374502400*a42^3*p32n*s2*w1^4-520287896532418560*a42^2*p21n*p32n^2*w1-345353135024701440*a42*p32n^2*s2*w1^5-345353135024701440*a42^2*p21n*s2*w1^5-309378850126295040*a42^3*lambda*p32n*w1^5-263811422588313600*a42*p21n*p32n*w1^6-246452161515356160*a42*p0*p21n*p32n-227625954732933120*a42*p21n^2*p32n*w1^2-227625954732933120*a42^2*p0*p32n*w1^2-216786623555174400*a42*p21n^2*s2*w1^3-216786623555174400*a42*p32n^3*s2*w1^2-216786623555174400*a42^2*p0*s2*w1^3-216786623555174400*p21n*p32n^2*s2*w1^3-216786623555174400*a42^3*p32n^2*s2*w1-210012041569075200*a42^3*lambda*p32n^2*w1^2-154689425063147520*a42*lambda*p32n^2*w1^6-154689425063147520*a42^2*lambda*p21n*w1^6-140008027712716800*a42*lambda*p32n^3*w1^3-120313997271336960*a42*p32n*s2*w1^8-115117711674900480*p21n*p32n*s2*w1^6-112909699768320000*a42*p0*p32n*w1^4-108393311777587200*p0*p32n*s2*w1^4-108393311777587200*a42^4*p21n*s2*w1-105006020784537600*a42*lambda*p21n^2*w1^4-105006020784537600*a42^2*lambda*p0*w1^4-105006020784537600*a42^4*lambda*p21n*w1^2-105006020784537600*lambda*p21n*p32n^2*w1^4-98580864606142464*a42*p21n^2*p32n*s2-98580864606142464*a42^2*p0*p32n*s2-98580864606142464*p0*p32n^2*s2*w1-58532388359897088*lambda*p0*p32n^2*w1^2-58532388359897088*a42^2*lambda*p21n*p32n^2-58336678213632000*a42^2*p21n*p32n*w1^4-45953262846691200*a42*lambda*p32n*w1^9-44196978589470720*lambda*p21n*p32n*w1^7-42002408313815040*lambda*p0*p32n*w1^5-42002408313815040*a42^5*lambda*p32n*w1-39021592239931392*lambda*p21n*p32n^3*w1+20537680126279680*p0*p21n*p32n*w1^2+36967824227303424*a42*lambda*p0*p32n^2+36967824227303424*a42^2*lambda*p0*p21n+40647491916595200*lambda*p0*p21n*w1^4+43169141878087680*a42*lambda*p0*w1^6+43357324711034880*a42*p0*p21n*w1^3+45117748976751360*a42*lambda*p21n*w1^8+81294983833190400*a42^3*lambda*p0*w1^2+81294983833190400*lambda*p21n^2*p32n*w1^3+81294983833190400*a42^2*lambda*p32n^3*w1+90997721174900736*p0*p21n*p32n*s2+104057579306483712*p0*p21n*s2*w1^3+104057579306483712*a42^3*p0*s2*w1+104057579306483712*a42^3*p21n*p32n*s2+112006422170173440*a42*p0*s2*w1^5+117858609571921920*a42*p21n*s2*w1^7+121942475749785600*a42^2*lambda*p21n^2*w1^2+156086368959725568*p21n^2*p32n*s2*w1^2+156086368959725568*a42^2*p21n^2*s2*w1+180470995907005440*a42^2*lambda*p32n*w1^7+180655519629312000*a42*p21n*p32n^2*w1^3+205376801262796800*a42*p0*p32n^2*w1+205376801262796800*a42^2*p0*p21n*w1+215845709390438400*a42^3*lambda*p21n*w1^4+215845709390438400*a42^4*lambda*p32n*w1^3+280016055425433600*a42^4*p32n*s2*w1^2+323768564085657600*a42^2*lambda*p32n^2*w1^4+373354740567244800*a42^3*p21n*s2*w1^3+412505133501726720*a42^2*p32n*s2*w1^6+560032110850867200*a42^2*p32n^2*s2*w1^3+587130438795264000*a42^3*p21n*p32n*w1^2-650359870665523200*a42^2*p21n*p32n*s2*w1^2-420024083138150400*a42^2*lambda*p21n*p32n*w1^3-197161729212284928*a42*p0*p21n*s2*w1-117064776719794176*a42*lambda*p0*p21n*w1^2-117064776719794176*a42*lambda*p21n^2*p32n*w1-117064776719794176*a42^2*lambda*p0*p32n*w1+73935648454606848*lambda*p0*p21n*p32n*w1+162589967666380800*a42*lambda*p0*p32n*w1^3+162589967666380800*a42^3*lambda*p21n*p32n*w1+243884951499571200*a42*lambda*p21n*p32n^2*w1^2+259014851268526080*a42*lambda*p21n*p32n*w1^5+312172737919451136*a42*p0*p32n*s2*w1^2+312172737919451136*a42*p21n*p32n^2*s2*w1+560032110850867200*a42*p21n*p32n*s2*w1^4

/-- Frozen order-`75` mixin on `p32 = h · p32n`, `q41 = h · q41n`,
`q3 = h · q3n`.  Independent of `h` (last frozen head).  Does not vanish
at `p21 = p1 = 0`. -/
def degreeZeroPostCollapseP32Q41Q3ZeroOrderSix610
    (w1 a42 p32n p0 s2 lambda : R) : R :=
  -547985470548040*w1^15+6503598706655232*p32n^5-90327759814656000*a42^3*p32n^3-66841109595187200*a42^4*w1^7-43968570431385600*p32n^3*w1^6-41075360252559360*p0*p32n^3-37752848938022400*a42^2*w1^11-36205601030726400*p32n^2*w1^9-34375427791810560*a42^5*w1^5-27383573501706240*p0^2*w1^3-15556447523635200*a42^7*w1-8061806283640200*p32n*w1^12-1000057340805120*a42^7*lambda+264207280442805*lambda*w1^14+810718230399840*s2*w1^13+7431583778665200*a42*w1^13+10912834219622400*p0*w1^9+15054626635776000*p32n^4*w1^3+23334671285452800*a42^6*p32n+56873575734312960*p0^2*p32n+63954284263833600*a42^6*w1^3+85098634901280000*a42^3*w1^9-388911188090880000*a42^3*p32n^2*w1^3-221679377211801600*a42^5*p32n*w1^2-213056036834659200*a42^2*p32n*w1^8-160418663028449280*a42^3*s2*w1^7-115117711674900480*a42^5*s2*w1^3-86714649422069760*a42*p32n^4*w1-86714649422069760*a42^4*p0*w1-77344712531573760*a42^5*lambda*w1^4-71948569796812800*a42^2*p32n^2*w1^5-68929894270036800*a42^3*lambda*w1^8-68522447425536000*a42*p0*w1^7-37915717156208640*a42*p0^2*w1-21678662355517440*a42^5*p32n*s2-19445559404544000*a42*p32n^3*w1^4-17062072720293888*a42*lambda*p0^2-16445387382128640*p0*s2*w1^7-11325854681406720*a42*s2*w1^11-9755398059982848*a42*lambda*p32n^4-9755398059982848*a42^4*lambda*p0-5524622323683840*lambda*p0*w1^8-3952251373199220*a42*lambda*w1^12+4247195505527520*lambda*p32n*w1^11+12254203425784320*p32n*s2*w1^10+18483912113651712*lambda*p0^2*w1^2+18667737028362240*a42^6*s2*w1+20323745958297600*a42^4*lambda*p32n^2+20323745958297600*lambda*p32n^4*w1^2+21584570939043840*a42^6*lambda*w1^2+21678662355517440*p0*p32n^2*w1^3+22558874488375680*lambda*p32n^2*w1^8+23359575280401360*a42^2*lambda*w1^10+26014394826620928*p32n^4*s2*w1+43169141878087680*lambda*p32n^3*w1^5+45498860587450368*p0^2*s2*w1+52028789653241856*a42^2*p32n^3*s2+58929304785960960*p32n^2*s2*w1^7+60218506543104000*a42^3*p0*w1^3+61271017128921600*a42^2*s2*w1^9+66114901975449600*p0*p32n*w1^6+74035812364113600*a42*p32n*w1^10+93338685141811200*a42^2*p0*w1^5+93338685141811200*p32n^3*s2*w1^4+105274747612419840*a42^4*lambda*w1^6+130071974133104640*a42^3*p0*p32n+143230949132544000*a42^3*p32n*w1^6+171877138959052800*a42*p32n^2*w1^7+206252566750863360*a42^4*s2*w1^5+209849995240704000*a42^4*p32n*w1^4+248401339490304000*a42^4*p32n^2*w1+293565219397632000*a42^2*p32n^3*w1^2-575588558374502400*a42^3*p32n*s2*w1^4-345353135024701440*a42*p32n^2*s2*w1^5-309378850126295040*a42^3*lambda*p32n*w1^5-227625954732933120*a42^2*p0*p32n*w1^2-216786623555174400*a42*p32n^3*s2*w1^2-216786623555174400*a42^2*p0*s2*w1^3-216786623555174400*a42^3*p32n^2*s2*w1-210012041569075200*a42^3*lambda*p32n^2*w1^2-154689425063147520*a42*lambda*p32n^2*w1^6-140008027712716800*a42*lambda*p32n^3*w1^3-120313997271336960*a42*p32n*s2*w1^8-112909699768320000*a42*p0*p32n*w1^4-108393311777587200*p0*p32n*s2*w1^4-105006020784537600*a42^2*lambda*p0*w1^4-98580864606142464*a42^2*p0*p32n*s2-98580864606142464*p0*p32n^2*s2*w1-58532388359897088*lambda*p0*p32n^2*w1^2-45953262846691200*a42*lambda*p32n*w1^9-42002408313815040*lambda*p0*p32n*w1^5-42002408313815040*a42^5*lambda*p32n*w1+36967824227303424*a42*lambda*p0*p32n^2+43169141878087680*a42*lambda*p0*w1^6+81294983833190400*a42^3*lambda*p0*w1^2+81294983833190400*a42^2*lambda*p32n^3*w1+104057579306483712*a42^3*p0*s2*w1+112006422170173440*a42*p0*s2*w1^5+180470995907005440*a42^2*lambda*p32n*w1^7+205376801262796800*a42*p0*p32n^2*w1+215845709390438400*a42^4*lambda*p32n*w1^3+280016055425433600*a42^4*p32n*s2*w1^2+323768564085657600*a42^2*lambda*p32n^2*w1^4+412505133501726720*a42^2*p32n*s2*w1^6+560032110850867200*a42^2*p32n^2*s2*w1^3-117064776719794176*a42^2*lambda*p0*p32n*w1+162589967666380800*a42*lambda*p0*p32n*w1^3+312172737919451136*a42*p0*p32n*s2*w1^2

set_option maxHeartbeats 800000000 in
theorem degreeZeroPostCollapseP32P21P1ZeroOrderFourPlus610_of_fivePlus
    (h w1 a42 p32n p21n p1n p0 s2 u2 b63 q1 lambda : R) :
    degreeZeroPostCollapseP32P21P1ZeroOrderFourPlus610 h w1 a42 p32n
        p21n p1n p0 s2 u2 b63 q1 lambda =
      degreeZeroPostCollapseP32P21P1ZeroOrderFive610 w1 a42 p32n p21n
        p1n p0 u2 b63 q1 +
        h *
          degreeZeroPostCollapseP32P21P1ZeroOrderSix610 w1 a42 p32n
            p21n p1n p0 s2 lambda := by
  simp only [degreeZeroPostCollapseP32P21P1ZeroOrderFourPlus610,
    degreeZeroPostCollapseP32P21P1ZeroOrderFive610,
    degreeZeroPostCollapseP32P21P1ZeroOrderSix610]
  ring

set_option maxHeartbeats 800000000 in
theorem degreeZeroPostCollapseP32P21ZeroOrderFourPlus610_of_fivePlus
    (h w1 a42 p32n p21n p1 p0 s2 u2 b63 q1 lambda : R) :
    degreeZeroPostCollapseP32P21ZeroOrderFourPlus610 h w1 a42 p32n p21n
        p1 p0 s2 u2 b63 q1 lambda =
      degreeZeroPostCollapseP32P21ZeroOrderFive610 w1 a42 p32n p21n p1
        p0 s2 u2 b63 q1 lambda +
        h *
          degreeZeroPostCollapseP32P21ZeroOrderSix610 w1 a42 p32n p21n
            p0 s2 lambda := by
  simp only [degreeZeroPostCollapseP32P21ZeroOrderFourPlus610,
    degreeZeroPostCollapseP32P21ZeroOrderFive610,
    degreeZeroPostCollapseP32P21ZeroOrderSix610]
  ring

set_option maxHeartbeats 800000000 in
theorem degreeZeroPostCollapseP32Q41Q3ZeroOrderFourPlus610_of_fivePlus
    (h w1 a42 p32n p21 p1 p0 s2 u2 b63 q1 lambda : R) :
    degreeZeroPostCollapseP32Q41Q3ZeroOrderFourPlus610 h w1 a42 p32n
        p21 p1 p0 s2 u2 b63 q1 lambda =
      degreeZeroPostCollapseP32Q41Q3ZeroOrderFive610 w1 a42 p32n p21 p1
        p0 s2 u2 b63 q1 lambda +
        h *
          degreeZeroPostCollapseP32Q41Q3ZeroOrderSix610 w1 a42 p32n p0
            s2 lambda := by
  simp only [degreeZeroPostCollapseP32Q41Q3ZeroOrderFourPlus610,
    degreeZeroPostCollapseP32Q41Q3ZeroOrderFive610,
    degreeZeroPostCollapseP32Q41Q3ZeroOrderSix610]
  ring

end DegreeZeroOrderSixHead610

section DegreeZeroOrderSixEval610

variable {k : Type*} [CommRing k]

theorem degreeZeroPostCollapseP32P21P1ZeroOrderSix610_eval
    (w1 a42 p32n p21n p1n p0 s2 : k[X]) (lambda a : k) :
    (degreeZeroPostCollapseP32P21P1ZeroOrderSix610 w1 a42 p32n p21n p1n
        p0 s2 (Polynomial.C lambda)).eval a =
      degreeZeroPostCollapseP32P21P1ZeroOrderSix610 (w1.eval a)
        (a42.eval a) (p32n.eval a) (p21n.eval a) (p1n.eval a)
        (p0.eval a) (s2.eval a) lambda := by
  simp only [degreeZeroPostCollapseP32P21P1ZeroOrderSix610,
    Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_neg,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat,
    Polynomial.eval_C]

theorem degreeZeroPostCollapseP32P21ZeroOrderSix610_eval
    (w1 a42 p32n p21n p0 s2 : k[X]) (lambda a : k) :
    (degreeZeroPostCollapseP32P21ZeroOrderSix610 w1 a42 p32n p21n p0 s2
        (Polynomial.C lambda)).eval a =
      degreeZeroPostCollapseP32P21ZeroOrderSix610 (w1.eval a)
        (a42.eval a) (p32n.eval a) (p21n.eval a) (p0.eval a)
        (s2.eval a) lambda := by
  simp only [degreeZeroPostCollapseP32P21ZeroOrderSix610,
    Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_neg,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat,
    Polynomial.eval_C]

theorem degreeZeroPostCollapseP32Q41Q3ZeroOrderSix610_eval
    (w1 a42 p32n p0 s2 : k[X]) (lambda a : k) :
    (degreeZeroPostCollapseP32Q41Q3ZeroOrderSix610 w1 a42 p32n p0 s2
        (Polynomial.C lambda)).eval a =
      degreeZeroPostCollapseP32Q41Q3ZeroOrderSix610 (w1.eval a)
        (a42.eval a) (p32n.eval a) (p0.eval a) (s2.eval a) lambda := by
  simp only [degreeZeroPostCollapseP32Q41Q3ZeroOrderSix610,
    Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_neg,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat,
    Polynomial.eval_C]

end DegreeZeroOrderSixEval610

section DegreeZeroOrderSixSource610

variable {k : Type*} [Field k] [CharZero k]

/-- **CLOSED.** Arm `(a)`: `p32(a) = p21(a) = p1(a) = 0`.  The last
frozen head is extracted; `h0^6` already divides the jet quotient, so
the remaining factor is `rho` and `j ≠ 0` is impossible. -/
theorem degreeZeroPostCollapseP32P21P1ZeroOrderSixHead610_false_of_primitiveDeriv
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
        RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
    (hj : j ≠ 0) : False := by
  obtain ⟨_p32n, _p21n, _p1n, _o72n, _o73n, _hp32eq, _hp21eq, _hp1eq,
      _ho72, _ho73, _hmix, hdvd⟩ :=
    degreeZeroPostCollapseP32P21P1ZeroOrderFiveHead610_zero_of_primitiveDeriv
      h0 w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda j a hh0
      hdegree hroot hp32 hp21 hp1 hderiv
  exact degreeZeroPostCollapseJetQuotient610_pow_six_dvd_contradicts_simplePole
    h0 w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda j a hh0
    hroot hdvd hderiv hj

/-- **CLOSED.** Arm `(b)`: `p32(a) = p21(a) = 0` with the nine-term
cofactor. -/
theorem degreeZeroPostCollapseP32P21ZeroOrderSixHead610_false_of_primitiveDeriv
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
        RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
    (hj : j ≠ 0) : False := by
  obtain ⟨_p32n, _p21n, _o71n, _o72n, _o73n, _hp32eq, _hp21eq, _ho71,
      _ho72, _ho73, _hmix, hdvd⟩ :=
    degreeZeroPostCollapseP32P21ZeroOrderFiveHead610_zero_of_primitiveDeriv
      h0 w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda j a hh0
      hdegree hroot hp32 hp21 hderiv
  exact degreeZeroPostCollapseJetQuotient610_pow_six_dvd_contradicts_simplePole
    h0 w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda j a hh0
    hroot hdvd hderiv hj

/-- **CLOSED.** Arm `(c)`: `p32(a) = q41(a) = q3(a) = 0`, both
subpackets. -/
theorem degreeZeroPostCollapseP32Q41Q3ZeroOrderSixHead610_false_of_primitiveDeriv
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
        RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
    (hj : j ≠ 0) : False := by
  obtain ⟨_p32n, _q41n, _q3n, _o71n, _o72n, _o73n, _hp32eq, _hq41eq,
      _hq3eq, _ho71, _ho72, _ho73, _hmix, hdvd⟩ :=
    degreeZeroPostCollapseP32Q41Q3ZeroOrderFiveHead610_zero_of_primitiveDeriv
      h0 w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda j a hh0
      hdegree hroot hp32 hq41 hq3 hderiv
  exact degreeZeroPostCollapseJetQuotient610_pow_six_dvd_contradicts_simplePole
    h0 w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda j a hh0
    hroot hdvd hderiv hj

theorem degreeZeroPostCollapseP32P21P1ZeroOrderSixHead610_false_of_source
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
    (hroot : h0.eval a = 0) (hj : j ≠ 0)
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
    (hp1 : (p.coeff 1).eval a = 0) : False := by
  have hjscaled : (58498535041007616 : k) * j ≠ 0 :=
    mul_ne_zero (by norm_num) hj
  exact degreeZeroPostCollapseP32P21P1ZeroOrderSixHead610_false_of_primitiveDeriv
    h0 w1 a42 p32 p21 (p.coeff 1) (p.coeff 0) s2 u2 b63 q53 q41
    (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda
    (58498535041007616 * j) a hh0 hh0degree hroot hp32 hp21 hp1
    (degreeZeroPostCollapsePrimitive610_deriv_eq_simplePole_of_source
      p q H h0 j lambda w1 a42 p32 p21 s2 u2 b63 q53 q41 hp hq hh0 hH
      hp6 hq10 hN hD hw hp4deep hp3deep hp2deep hq8deep hq7deep hq6deep
      hq5deep hq4deep)
    hjscaled

theorem degreeZeroPostCollapseP32P21ZeroOrderSixHead610_false_of_source
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
    (hroot : h0.eval a = 0) (hj : j ≠ 0)
    (hw : p.coeff 5 = h0 ^ 5 * w1)
    (hp4deep : p.coeff 4 = h0 ^ 4 * a42)
    (hp3deep : p.coeff 3 = h0 ^ 2 * p32)
    (hp2deep : p.coeff 2 = h0 * p21)
    (hq8deep : q.coeff 8 = h0 ^ 8 * s2)
    (hq7deep : q.coeff 7 = h0 ^ 6 * u2)
    (hq6deep : q.coeff 6 = h0 ^ 5 * b63)
    (hq5deep : q.coeff 5 = h0 ^ 3 * q53)
    (hq4deep : q.coeff 4 = h0 * q41)
    (hp32 : p32.eval a = 0) (hp21 : p21.eval a = 0) : False := by
  have hjscaled : (58498535041007616 : k) * j ≠ 0 :=
    mul_ne_zero (by norm_num) hj
  exact degreeZeroPostCollapseP32P21ZeroOrderSixHead610_false_of_primitiveDeriv
    h0 w1 a42 p32 p21 (p.coeff 1) (p.coeff 0) s2 u2 b63 q53 q41
    (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda
    (58498535041007616 * j) a hh0 hh0degree hroot hp32 hp21
    (degreeZeroPostCollapsePrimitive610_deriv_eq_simplePole_of_source
      p q H h0 j lambda w1 a42 p32 p21 s2 u2 b63 q53 q41 hp hq hh0 hH
      hp6 hq10 hN hD hw hp4deep hp3deep hp2deep hq8deep hq7deep hq6deep
      hq5deep hq4deep)
    hjscaled

theorem degreeZeroPostCollapseP32Q41Q3ZeroOrderSixHead610_false_of_source
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
    (hroot : h0.eval a = 0) (hj : j ≠ 0)
    (hw : p.coeff 5 = h0 ^ 5 * w1)
    (hp4deep : p.coeff 4 = h0 ^ 4 * a42)
    (hp3deep : p.coeff 3 = h0 ^ 2 * p32)
    (hp2deep : p.coeff 2 = h0 * p21)
    (hq8deep : q.coeff 8 = h0 ^ 8 * s2)
    (hq7deep : q.coeff 7 = h0 ^ 6 * u2)
    (hq6deep : q.coeff 6 = h0 ^ 5 * b63)
    (hq5deep : q.coeff 5 = h0 ^ 3 * q53)
    (hq4deep : q.coeff 4 = h0 * q41)
    (hp32 : p32.eval a = 0) (hq41 : q41.eval a = 0)
    (hq3 : (q.coeff 3).eval a = 0) : False := by
  have hjscaled : (58498535041007616 : k) * j ≠ 0 :=
    mul_ne_zero (by norm_num) hj
  exact degreeZeroPostCollapseP32Q41Q3ZeroOrderSixHead610_false_of_primitiveDeriv
    h0 w1 a42 p32 p21 (p.coeff 1) (p.coeff 0) s2 u2 b63 q53 q41
    (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda
    (58498535041007616 * j) a hh0 hh0degree hroot hp32 hq41 hq3
    (degreeZeroPostCollapsePrimitive610_deriv_eq_simplePole_of_source
      p q H h0 j lambda w1 a42 p32 p21 s2 u2 b63 q53 q41 hp hq hh0 hH
      hp6 hq10 hN hD hw hp4deep hp3deep hp2deep hq8deep hq7deep hq6deep
      hq5deep hq4deep)
    hjscaled

end DegreeZeroOrderSixSource610

section DegreeZeroOrder75Grandchildren610

variable {k : Type*} [Field k] [CharZero k]

/-- Source-facing joint order-`75` packet.  Arms `(a)(b)(c)` are
**CLOSED** (`j ≠ 0` makes the holomorphic remainder after `h0^6`
impossible).  The only surviving arm is `(d)`, copied from order `74`:
`M = 4` (next unused mixed order `73`). -/
theorem degreeZeroFace610_linearRoot_order75Grandchildren
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hh0degree : h0.natDegree = 1) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0) (hlambda : lambda ≠ 0) (hj : j ≠ 0) :
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
      (q41.eval a = 0 ∧
        10 * (p32.eval a) ^ 2 * (q53.eval a) +
            (18 * (p32.eval a) * (w1.eval a) -
              27 * (p21.eval a)) * (q.coeff 3).eval a = 0 ∧
        ∃ q41n q41nn o70n o71n : k[X],
          q41 = h0 * q41n ∧
            q41n = C (q41n.eval a) + h0 * q41nn ∧
            degreeZeroPostCollapseQ41ZeroMixedOrderOne610 w1 a42 p32
                p21 (p.coeff 1) q53 q41n (q.coeff 3) u2 =
              h0 * o70n ∧
            o70n +
                degreeZeroPostCollapseQ41ZeroMixedOrderTwo610 w1 a42
                  p32 p21 (p.coeff 1) s2 u2 b63 q53 q41n (q.coeff 3)
                  (q.coeff 2) (Polynomial.C lambda) =
              h0 * o71n ∧
            o71n.eval a +
                degreeZeroPostCollapseQ41ZeroMixedOrderThree610
                  (w1.eval a) (a42.eval a) (p32.eval a)
                  (p21.eval a) ((p.coeff 1).eval a)
                  ((p.coeff 0).eval a) (s2.eval a) (u2.eval a)
                  (b63.eval a) (q53.eval a) (q41n.eval a)
                  ((q.coeff 3).eval a) ((q.coeff 2).eval a)
                  ((q.coeff 1).eval a) lambda =
              0 ∧
            (p32.eval a = 0 ∨
              degreeZeroPostCollapseQ41ZeroMixedFiveReduced610
                  (w1.eval a) (a42.eval a) (p32.eval a)
                  (p21.eval a) ((p.coeff 1).eval a) (q41n.eval a)
                  ((q.coeff 3).eval a) (u2.eval a) = 0)) := by
  obtain ⟨w1, a42, p32, p21, s2, u2, b63, q53, q41, hw, hp4deep,
      hp3deep, hp2deep, hq8deep, hq7deep, hq6deep, hq5deep, hq4deep,
      hpacket⟩ :=
    degreeZeroFace610_linearRoot_order74Grandchildren p q H h0 j lambda
      a hp hq hh0 hh0degree hH hp6 hq10 hN hD hroot hlambda
  refine ⟨w1, a42, p32, p21, s2, u2, b63, q53, q41, hw, hp4deep,
    hp3deep, hp2deep, hq8deep, hq7deep, hq6deep, hq5deep, hq4deep, ?_⟩
  rcases hpacket with hAB | hC | hD
  · obtain ⟨hp32, hp21, _p32n, _p21n, _hp32eq, _hp21eq, hsplit⟩ := hAB
    rcases hsplit with hp1pack | hcof
    · obtain ⟨hp1, _p1n, _o72n, _o73n, _hp1eq, _ho72, _ho73, _hmix⟩ :=
        hp1pack
      exact (degreeZeroPostCollapseP32P21P1ZeroOrderSixHead610_false_of_source
        p q H h0 j lambda a w1 a42 p32 p21 s2 u2 b63 q53 q41 hp hq hh0
        hh0degree hH hp6 hq10 hN hD hroot hj hw hp4deep hp3deep hp2deep
        hq8deep hq7deep hq6deep hq5deep hq4deep hp32 hp21 hp1).elim
    · exact (degreeZeroPostCollapseP32P21ZeroOrderSixHead610_false_of_source
        p q H h0 j lambda a w1 a42 p32 p21 s2 u2 b63 q53 q41 hp hq hh0
        hh0degree hH hp6 hq10 hN hD hroot hj hw hp4deep hp3deep hp2deep
        hq8deep hq7deep hq6deep hq5deep hq4deep hp32 hp21).elim
  · obtain ⟨hp32, hq41, hq3, _p32n, _q41n, _q3n, _o71n, _o72n, _o73n,
        _hp32eq, _hq41eq, _hq3eq, _ho71, _ho72, _ho73, _hmix,
        _hp21split⟩ := hC
    exact (degreeZeroPostCollapseP32Q41Q3ZeroOrderSixHead610_false_of_source
      p q H h0 j lambda a w1 a42 p32 p21 s2 u2 b63 q53 q41 hp hq hh0
      hh0degree hH hp6 hq10 hN hD hroot hj hw hp4deep hp3deep hp2deep
      hq8deep hq7deep hq6deep hq5deep hq4deep hp32 hq41 hq3).elim
  · exact hD

#print axioms algebraMap_cancel_six_of_six_clearing610
#print axioms localLinearPoleZero_C_eq_zero_of_deriv_eq_simplePole610
#print axioms localLinearPoleSix_of_pow_six_dvd_simplePole_ne_zero610
#print axioms degreeZeroPostCollapseJetQuotient610_pow_six_dvd_contradicts_simplePole
#print axioms degreeZeroPostCollapseP32P21P1ZeroOrderFourPlus610_of_fivePlus
#print axioms degreeZeroPostCollapseP32P21ZeroOrderFourPlus610_of_fivePlus
#print axioms degreeZeroPostCollapseP32Q41Q3ZeroOrderFourPlus610_of_fivePlus
#print axioms degreeZeroPostCollapseP32P21P1ZeroOrderSixHead610_false_of_source
#print axioms degreeZeroPostCollapseP32P21ZeroOrderSixHead610_false_of_source
#print axioms degreeZeroPostCollapseP32Q41Q3ZeroOrderSixHead610_false_of_source
#print axioms degreeZeroFace610_linearRoot_order75Grandchildren

end DegreeZeroOrder75Grandchildren610

end Max11DegreeRoutes
