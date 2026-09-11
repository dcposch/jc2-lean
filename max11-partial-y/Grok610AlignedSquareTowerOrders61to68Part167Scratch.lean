import Grok610AlignedSquareTowerOrders61to68Part18Scratch
import Grok610AlignedSquareTowerOrders61to68Part20Scratch
import Grok610AlignedSquareTowerOrders61to68Part103Scratch
import Grok610AlignedSquareTowerOrders61to68Part159Scratch

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

set_option maxHeartbeats 1600000000 in
/-- On the `w₁ = 0` complement, cancel the polynomial `h₀¹⁰` from the
pole-`21` clearing.  The remaining pole-`11` obstruction forces the
first surviving coefficient, order `64`, to vanish at `a`.  Orders
`61`–`63` are identically zero. -/
theorem alignedSquareW1ComplementOrder64610_zero_of_pole
    (h0 w1n e1b e3b a2b a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 (h0 * w1n) (h0 * e1b)
            (h0 * e3b) (h0 * a2b) a1 a0 b8 b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    alignedSquareW1ComplementOrder64610 (w1n.eval a) (a2b.eval a) (a1.eval a) (b8.eval a) = 0 := by
  let Q64 : k[X] :=
    alignedSquareW1ComplementOrder64610 w1n a2b a1 b8
      + h0 * alignedSquareW1ComplementOrder65610 w1n e1b e3b a2b a1 b8 b7
      + h0 ^ 2 * alignedSquareW1ComplementOrder66610 w1n e1b e3b a2b a1 a0 b8 b7
      + h0 ^ 3 * alignedSquareW1ComplementOrder67610 w1n e1b e3b a2b a1 a0 b8 b7 b6
      + h0 ^ 4 * alignedSquareW1ComplementOrder68610 w1n e1b e3b a2b a1 a0 b7 b6 b5
      + h0 ^ 5 * alignedSquareW1ComplementOrder68Plus610 h0 w1n e1b e3b a2b a1 a0 b6 b5 b4 b3 b2 b1
  have hscale := alignedSquareJetQuotient610_w1Complement_scale h0 w1n
    e1b e3b a2b a1 a0 b8 b7 b6 b5 b4 b3 b2 b1
  have hjet : alignedSquareJetQuotient610 h0 (h0 * w1n) (h0 * e1b)
      (h0 * e3b) (h0 * a2b) a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 =
      h0 ^ 10 * Q64 := by
    simpa [Q64] using hscale
  have hclear11 :
      algebraMap k[X] (RatFunc k) Q64 =
        (algebraMap k[X] (RatFunc k) h0) ^ 11 * rho :=
    alignedSquare_algebraMap_cancel_pow610 h0 Q64 rho 10 11 hh0
      (by
        have hpow : alignedSquareRemainingPole610 = 10 + 11 := rfl
        rw [hpow] at hclear
        simpa [hjet] using hclear)
  have hQ0 : Q64.eval a = 0 :=
    alignedSquare_localLinearPole_head_eval_zero610 11 (by decide) a j
      h0 Q64 rho hdegree hroot hclear11 hderiv
  let Head : k[X] := alignedSquareW1ComplementOrder64610 w1n a2b a1 b8
  let Rest : k[X] :=
    alignedSquareW1ComplementOrder65610 w1n e1b e3b a2b a1 b8 b7
      + h0 * alignedSquareW1ComplementOrder66610 w1n e1b e3b a2b a1 a0 b8 b7
      + h0 ^ 2 * alignedSquareW1ComplementOrder67610 w1n e1b e3b a2b a1 a0 b8 b7 b6
      + h0 ^ 3 * alignedSquareW1ComplementOrder68610 w1n e1b e3b a2b a1 a0 b7 b6 b5
      + h0 ^ 4 * alignedSquareW1ComplementOrder68Plus610 h0 w1n e1b e3b a2b a1 a0 b6 b5 b4 b3 b2 b1
  have hshape : Q64 = Head + h0 * Rest := by
    simp only [Q64, Head, Rest]
    ring
  have hO : Q64.eval a =
      alignedSquareW1ComplementOrder64610 (w1n.eval a) (a2b.eval a)
        (a1.eval a) (b8.eval a) := by
    rw [hshape,
      alignedSquare_eval_head_of_linear_factor610 h0 Head Rest a hroot]
    simp only [Head, alignedSquareW1ComplementOrder64610_eval]
  exact hO.symm.trans hQ0

end AlignedSquareTowerHeads610

end Max11DegreeRoutes
