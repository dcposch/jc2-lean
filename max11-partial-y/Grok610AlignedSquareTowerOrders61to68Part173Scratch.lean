import Grok610AlignedSquareSourceWrapperPart06Scratch
import Grok610AlignedSquareTowerOrders61to68Part18Scratch
import Grok610AlignedSquareTowerOrders61to68Part17Scratch
import Grok610AlignedSquareTowerOrders61to68Part157Scratch
import Grok610AlignedSquareTowerOrders61to68Part21Scratch

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

/-- Same `h₀`-divisibility step on the frozen `w₁ = 0` limb. -/
theorem alignedSquareW1Zero_order61_remaining_dvd
    (h0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5
            b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    ∃ Q61 : k[X],
      alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3
          b2 b1 =
        h0 ^ 7 * Q61 ∧ Q61.eval a = 0 ∧ h0 ∣ Q61 := by
  let Q61 : k[X] :=
    alignedSquareW1ZeroOrder61610 e1 e3 a2 b8
      + h0 * alignedSquareW1ZeroOrder62610 e1 e3 a2 a1 b8 b7
      + h0 ^ 2 * alignedSquareW1ZeroOrder63610 e1 e3 a2 a1 b8 b7
      + h0 ^ 3 * alignedSquareW1ZeroOrder64610 e1 e3 a2 a1 a0 b8 b7 b6
      + h0 ^ 4 * alignedSquareW1ZeroOrder65610 e1 e3 a2 a1 a0 b8 b7 b6 b5
      + h0 ^ 5 * alignedSquareW1ZeroOrder66610 e1 e3 a2 a1 a0 b7 b6 b5
      + h0 ^ 6 * alignedSquareW1ZeroOrder67610 e1 e3 a2 a1 a0 b6 b5 b4
      + h0 ^ 7 * alignedSquareW1ZeroOrder68610 e1 e3 a2 a1 a0 b7 b6 b5 b4 b3
      + h0 ^ 8 * alignedSquareW1ZeroOrder68Plus610 h0 e1 e3 a2 a1 a0 b4 b3 b2 b1
  have hjet :
      alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3
          b2 b1 =
        h0 ^ 7 * Q61 := by
    simpa [Q61] using alignedSquareJetQuotient610_w1Zero_scale h0 e1 e3
      a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1
  have hclear14 :
      algebraMap k[X] (RatFunc k) Q61 =
        (algebraMap k[X] (RatFunc k) h0) ^
            alignedSquareW1ZeroRemainingPole610 * rho :=
    alignedSquare_algebraMap_cancel_pow610 h0 Q61 rho 7 14 hh0
      (by
        have hpow : alignedSquareRemainingPole610 = 7 + 14 := rfl
        rw [hpow] at hclear
        simpa [hjet] using hclear)
  have hQ0 : Q61.eval a = 0 :=
    alignedSquare_poleFourteen_head_eval_zero610 a j h0 Q61 rho hdegree
      hroot hclear14 hderiv
  exact ⟨Q61, hjet, hQ0,
    alignedSquare_linearPolynomial_dvd_of_eval_eq_zero610 h0 Q61 a
      hdegree hroot hQ0⟩

end AlignedSquareTowerHeads610

end Max11DegreeRoutes
