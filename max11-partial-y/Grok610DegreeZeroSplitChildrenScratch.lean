import Grok610DegreeZeroSplitChildrenPart101Scratch
import Grok610DegreeZeroSplitChildrenPart17Scratch
import Grok610DegreeZeroSplitChildrenPart18Scratch
import Grok610DegreeZeroSplitChildrenPart19Scratch

/-! # Child analysis of the `(6,10)` degree-zero post-collapse split

The source wrapper supplies the order-`69` head
`7583143431241728 p32^3 q41` and the split `p32(a) = 0 ∨ q41(a) = 0`.
This file instantiates that split and consumes two already landed heads
rather than re-deriving them:

* the fourth-tail post-collapse head, specialized on each child as in
  `Sol610ScaleTwoDegreeZeroPostCollapseHeadSplitScratch`;
* the next coefficient of the *same* degree-zero compact numerator,
  which is the explicit order-`70` polynomial recorded below.

On `p32(a) = 0` the order-`69` monomial is divisible by `h0^3`, so the
simple-pole obstruction peels one more power of the linear scale and
forces the order-`70` head to vanish.  Combined with the fourth-tail
child `q41(a) = 0 ∨ p21(a) = 0` this is `p21(a) = 0 ∨ (q41(a) = 0 ∧
q3(a) = 0)`.  On `q41(a) = 0` the order-`70` head mixes `q41'(a)` and
is not used; the honest leftover is the landed five-term cofactor, or
the same `p32(a) = 0` grandchild already analysed.

Neither child is False.  The Jacobian coefficient tower is already
exhausted at the inhomogeneous degree-`0` row.  The next unused
compact-numerator order on the live `p32 = p21 = 0` grandchild is the
order-`71` coefficient of the same quotient.

No total-degree or twice-prime theorem is used, and no chamber is
closed.
-/

namespace Max11DegreeRoutes

#print axioms linearPolynomial_dvd_of_eval_eq_zero_610
#print axioms localLinearPoleFive_head_eval_zero_of_deriv_eq_simplePole610
#print axioms degreeZeroPostCollapseJetQuotient610_orderExpansion
#print axioms degreeZeroPostCollapseP32ZeroOrderOne610_split
#print axioms degreeZeroPostCollapseP32Zero_grandchildren610
#print axioms degreeZeroPostCollapseQ41Zero_grandchildren610
#print axioms degreeZeroPostCollapseP32ZeroOrderOne610_zero_of_source
#print axioms degreeZeroFace610_linearRoot_p32ZeroChild
#print axioms degreeZeroFace610_linearRoot_q41ZeroChild
#print axioms degreeZeroFace610_linearRoot_splitChildren

end Max11DegreeRoutes
