import Grok610DegreeZeroOrder72Part01Scratch
import Grok610DegreeZeroOrder72Part02Scratch
import Grok610DegreeZeroOrder72Part03Scratch
import Grok610DegreeZeroOrder72Part04Scratch
import Grok610DegreeZeroOrder72Part05Scratch
import Grok610DegreeZeroOrder72Part06Scratch
import Grok610DegreeZeroOrder72Part07Scratch
import Grok610DegreeZeroOrder72Part08Scratch
import Grok610DegreeZeroOrder72Part09Scratch
import Grok610DegreeZeroOrder72Part10Scratch
import Grok610DegreeZeroOrder72Part11Scratch
import Grok610DegreeZeroOrder72Part12Scratch
import Grok610DegreeZeroOrder72Part13Scratch
import Grok610DegreeZeroOrder72Part14Scratch
import Grok610DegreeZeroOrder72Part15Scratch
import Grok610DegreeZeroOrder72Part16Scratch
import Grok610DegreeZeroOrder72Part17Scratch
import Grok610DegreeZeroOrder72Part18Scratch
import Grok610DegreeZeroOrder72Part19Scratch
import Grok610DegreeZeroOrder72Part20Scratch
import Grok610DegreeZeroOrder72Part21Scratch
import Grok610DegreeZeroOrder72Part22Scratch
import Grok610DegreeZeroOrder72Part23Scratch
import Grok610DegreeZeroOrder72Part24Scratch
import Grok610DegreeZeroOrder72Part25Scratch
import Grok610DegreeZeroOrder72Part26Scratch
import Grok610DegreeZeroOrder72Part27Scratch
import Grok610DegreeZeroOrder72Part28Scratch
import Grok610DegreeZeroOrder72Part29Scratch
import Grok610DegreeZeroOrder72Part30Scratch
import Grok610DegreeZeroOrder72Part31Scratch
import Grok610DegreeZeroOrder72Part32Scratch
import Grok610DegreeZeroOrder72Part33Scratch
import Grok610DegreeZeroOrder72Part34Scratch
import Grok610DegreeZeroOrder72Part35Scratch
import Grok610DegreeZeroOrder72Part36Scratch
import Grok610DegreeZeroOrder72Part37Scratch
import Grok610DegreeZeroOrder72Part38Scratch
import Grok610DegreeZeroOrder72Part39Scratch
import Grok610DegreeZeroOrder72Part40Scratch
import Grok610DegreeZeroOrder72Part41Scratch
import Grok610DegreeZeroOrder72Part42Scratch
import Grok610DegreeZeroOrder72Part43Scratch

/-! # Order-`72` continuation of the `(6,10)` degree-zero post-collapse tower

`Grok610DegreeZeroOrder71GrandchildScratch` leaves four live arms:

* `(a)` `p32(a) = p21(a) = p1(a) = 0`, where the order-`71` head vanishes
  identically through the `p1` factor;
* `(b)` `p32(a) = p21(a) = 0` with the nine-term order-`71` cofactor;
* `(c)` `p32(a) = q41(a) = q3(a) = 0` with the eight-term order-`71`
  residual;
* `(d)` `q41(a) = 0` with the landed five-term cofactor.

The jet quotient has `h`-degree at most `6`, so the frozen heads are the
coefficients of `h^0` through `h^6` (orders `69` through `75`).  This
file extracts the order-`72` (`h^3`) coefficient and applies the
simple-pole obstruction on each arm that the existing jet coordinates
unlock.

On `(a)` the source jet peels `p1 = h0 · p1n` and one more clearing of
the compact numerator; pole-three forces the combined forty-six-term
head to vanish.  On `(b)` and `(c)` the order-`71` hypersurface is a
polynomial in `k[X]`, so it peels, and pole-three forces the sum of that
next coefficient with the order-`72` mixin to vanish.  On `(c)` the
eight-term residual additionally splits at `p21 = 0` into `p1 = 0` or
`q53 = 0`.  On `(d)` the differentiated order-`69` identity is the mixed
order-`70` head linear in `q41n`; together with the five-term cofactor
it forces `p32(a) = 0` or an eight-term residual linear in `q41n`.

None of these arms is False.  No total-degree or twice-prime theorem is
used, and no chamber is closed.
-/

namespace Max11DegreeRoutes

#print axioms localLinearPoleThree_head_eval_zero_of_deriv_eq_simplePole610
#print axioms degreeZeroPostCollapseJetQuotient610_p32P21P1Scale
#print axioms degreeZeroPostCollapseJetQuotient610_p32P21Scale
#print axioms degreeZeroPostCollapseJetQuotient610_p32Q41Q3Scale
#print axioms degreeZeroPostCollapseQ41ZeroMixedOrderOne610_factor
#print axioms degreeZeroPostCollapseQ41ZeroMixedFiveReduced610_identity
#print axioms degreeZeroPostCollapseQ41ZeroMixedOrderOne610_split
#print axioms degreeZeroPostCollapseQ41ZeroMixedFiveReduced610_of_five
#print axioms degreeZeroPostCollapseP32Q41Q3ZeroOrderTwoHead610_p21Zero_split
#print axioms degreeZeroPostCollapseP32P21P1ZeroOrderThreeHead610_zero_of_source
#print axioms degreeZeroPostCollapseQ41ZeroMixedOrderOne610_zero_of_source
#print axioms degreeZeroFace610_linearRoot_p32P21P1ZeroOrder72
#print axioms degreeZeroFace610_linearRoot_q41ZeroMixedOrder70
#print axioms degreeZeroFace610_linearRoot_order72Grandchildren

end Max11DegreeRoutes
