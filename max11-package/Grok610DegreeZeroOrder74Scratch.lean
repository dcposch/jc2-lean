import Grok610DegreeZeroOrder74Part01Scratch
import Grok610DegreeZeroOrder74Part02Scratch
import Grok610DegreeZeroOrder74Part03Scratch
import Grok610DegreeZeroOrder74Part04Scratch
import Grok610DegreeZeroOrder74Part05Scratch
import Grok610DegreeZeroOrder74Part06Scratch
import Grok610DegreeZeroOrder74Part07Scratch
import Grok610DegreeZeroOrder74Part08Scratch
import Grok610DegreeZeroOrder74Part09Scratch
import Grok610DegreeZeroOrder74Part10Scratch
import Grok610DegreeZeroOrder74Part11Scratch
import Grok610DegreeZeroOrder74Part12Scratch
import Grok610DegreeZeroOrder74Part13Scratch
import Grok610DegreeZeroOrder74Part14Scratch
import Grok610DegreeZeroOrder74Part15Scratch
import Grok610DegreeZeroOrder74Part16Scratch
import Grok610DegreeZeroOrder74Part17Scratch
import Grok610DegreeZeroOrder74Part18Scratch
import Grok610DegreeZeroOrder74Part19Scratch
import Grok610DegreeZeroOrder74Part20Scratch
import Grok610DegreeZeroOrder74Part21Scratch
import Grok610DegreeZeroOrder74Part22Scratch
import Grok610DegreeZeroOrder74Part23Scratch
import Grok610DegreeZeroOrder74Part24Scratch
import Grok610DegreeZeroOrder74Part25Scratch
import Grok610DegreeZeroOrder74Part26Scratch
import Grok610DegreeZeroOrder74Part27Scratch
import Grok610DegreeZeroOrder74Part28Scratch
import Grok610DegreeZeroOrder74Part29Scratch
import Grok610DegreeZeroOrder74Part30Scratch
import Grok610DegreeZeroOrder74Part31Scratch
import Grok610DegreeZeroOrder74Part32Scratch
import Grok610DegreeZeroOrder74Part33Scratch
import Grok610DegreeZeroOrder74Part34Scratch
import Grok610DegreeZeroOrder74Part35Scratch
import Grok610DegreeZeroOrder74Part36Scratch
import Grok610DegreeZeroOrder74Part37Scratch
import Grok610DegreeZeroOrder74Part38Scratch
import Grok610DegreeZeroOrder74Part39Scratch
import Grok610DegreeZeroOrder74Part40Scratch
import Grok610DegreeZeroOrder74Part41Scratch
import Grok610DegreeZeroOrder74Part42Scratch
import Grok610DegreeZeroOrder74Part43Scratch
import Grok610DegreeZeroOrder74Part44Scratch
import Grok610DegreeZeroOrder74Part45Scratch

/-! # Order-`74` continuation of the `(6,10)` degree-zero post-collapse tower

`Grok610DegreeZeroOrder73Scratch` leaves four live arms:

* `(a)` `h0^5 ∣ Q` with residual `o72n(a) + OrderFour(a) = 0` on
  `p32(a) = p21(a) = p1(a) = 0`;
* `(b)` the same `M = 5` vanishing on `p32(a) = p21(a) = 0` with the
  nine-term order-`71` cofactor and `o71n + OrderThree` already peeled;
* `(c)` `M = 5` on `p32(a) = q41(a) = q3(a) = 0`, split at `p21(a) = 0`
  into `p1(a) = 0` or `q53(a) = 0`;
* `(d)` `h0^3 ∣ Q` with mixed order-`71` residual
  `o70n(a) + MixedOrderTwo(a) = 0` and `q41n = C(q41n(a)) + h0 · q41nn`.

The jet quotient has `h`-degree at most `6`, so frozen heads run through
order `75`.  This file extracts the order-`74` (`h^5`) coefficient on
`(a)(b)(c)` and the mixed order-`72` (`h^3`) object on `(d)`, and applies
the simple-pole obstruction.

On `(a)(b)(c)` the previous residual peels as `h0 · o73n`; pole-one forces
`o73n(a)` plus the frozen order-`74` mixin to vanish, and divisibility
advances to `h0^6`.  On `(c)` the `p21 = p1 = 0` subpacket still kills
the sixty-two-term order-`72` mixin identically, but neither the
order-`73` mixin nor the order-`74` mixin vanishes there; the
`p21 = q53 = 0` subpacket still splits that mixin as `p1` times the
thirteen-term cofactor, and `p1` is **not** forced (the cofactor is a
live thirteen-term condition, and both later mixins survive at `p1 = 0`).
On `(d)` the mixed order-`71` object peels and pole-three forces the
mixed order-`72` head; `q41n` already names the first two Taylors of
`q41`, and the new residual uses `q41n(a)` rather than a third Taylor, so
`q41'''` is not introduced.

None of these arms is False.  No arm exhausts its remaining heads, so the
order-`75` ceiling lemma is not applied.  No total-degree or twice-prime
theorem is used, and no chamber is closed.  Cumulative vanishing toward
the order-`75` ceiling is recorded as `h0^M ∣` the jet quotient.
-/

namespace Max11DegreeRoutes

#print axioms localLinearPoleOne_head_eval_zero_of_deriv_eq_simplePole610
#print axioms algebraMap_cancel_five_of_six_clearing610
#print axioms degreeZeroPostCollapseP32P21P1ZeroOrderThreePlus610_of_fourPlus
#print axioms degreeZeroPostCollapseP32Q41Q3ZeroOrderFour610_p21P1Zero
#print axioms degreeZeroPostCollapseP32Q41Q3ZeroOrderFive610_p21P1Zero
#print axioms degreeZeroPostCollapseJetOrderTwoPlus610_q41Scale
#print axioms degreeZeroPostCollapseP32P21P1ZeroOrderFiveHead610_zero_of_source
#print axioms degreeZeroPostCollapseQ41ZeroMixedOrderThree610_zero_of_source
#print axioms degreeZeroFace610_linearRoot_order74Grandchildren

end Max11DegreeRoutes
