import Grok610AlignedSquareTowerOrders61to68Part19Scratch
import Grok610AlignedSquareTowerOrders61to68Part17Scratch

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

/-- If a remaining pole-`(r+1)` numerator vanishes at the linear root,
one more linear factor cancels and the pole-`r` obstruction forces the
new remaining numerator to vanish.  This is one step of the `h₀^M`
divisibility the ceiling lemma consumes. -/
theorem alignedSquare_remainingNumerator_succ_dvd610
    (h0 Qold : k[X]) (rho : RatFunc k) (j a : k) (r : ℕ)
    (hr : r ≠ 0) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hQold : Qold.eval a = 0)
    (hclear : algebraMap k[X] (RatFunc k) Qold =
      (algebraMap k[X] (RatFunc k) h0) ^ (r + 1) * rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    ∃ Qnew : k[X],
      Qold = h0 * Qnew ∧
        algebraMap k[X] (RatFunc k) Qnew =
          (algebraMap k[X] (RatFunc k) h0) ^ r * rho ∧
        Qnew.eval a = 0 ∧ h0 ∣ Qnew := by
  obtain ⟨Qnew, hfact⟩ :=
    alignedSquare_linearPolynomial_dvd_of_eval_eq_zero610 h0 Qold a
      hdegree hroot hQold
  have hclear' :
      algebraMap k[X] (RatFunc k) Qnew =
        (algebraMap k[X] (RatFunc k) h0) ^ r * rho :=
    alignedSquare_algebraMap_cancel_one_clearing610 h0 Qold Qnew rho r
      hh0 hfact hclear
  have hzero : Qnew.eval a = 0 :=
    alignedSquare_localLinearPole_head_eval_zero610 r hr a j h0 Qnew rho
      hdegree hroot hclear' hderiv
  exact ⟨Qnew, hfact, hclear', hzero,
    alignedSquare_linearPolynomial_dvd_of_eval_eq_zero610 h0 Qnew a
      hdegree hroot hzero⟩

end AlignedSquareTowerHeads610

end Max11DegreeRoutes
