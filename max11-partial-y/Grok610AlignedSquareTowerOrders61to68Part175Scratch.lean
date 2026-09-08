import Grok610AlignedSquareTowerOrders61to68Part18Scratch

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 100000000
set_option maxHeartbeats 1600000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

section AlignedSquareTowerHeads610

variable {k : Type*} [Field k] [CharZero k]

/-- Cancel `m` polynomial powers from a pole-`(m+n)` clearing and apply
the remaining pole-`n` obstruction.  The remaining numerator evaluates
to a recorded head, so that head vanishes.  Instantiating `m = 0` and
`n = 21` is `alignedSquare_poleTwentyOne_head_eval_zero610`. -/
theorem alignedSquare_remainingHead_eval_zero610
    (h0 A0 Q : k[X]) (rho : RatFunc k) (j a head : k) (m n : ℕ)
    (hn : n ≠ 0) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hfact : A0 = h0 ^ m * Q) (hhead : Q.eval a = head)
    (hclear : algebraMap k[X] (RatFunc k) A0 =
      (algebraMap k[X] (RatFunc k) h0) ^ (m + n) * rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    head = 0 := by
  have hclearQ :
      algebraMap k[X] (RatFunc k) Q =
        (algebraMap k[X] (RatFunc k) h0) ^ n * rho :=
    alignedSquare_algebraMap_cancel_pow610 h0 Q rho m n hh0
      (by simpa [hfact] using hclear)
  have hQ0 : Q.eval a = 0 :=
    alignedSquare_localLinearPole_head_eval_zero610 n hn a j h0 Q rho
      hdegree hroot hclearQ hderiv
  exact hhead.symm.trans hQ0

end AlignedSquareTowerHeads610

end Max11DegreeRoutes
