import Sol610ScaleTwoDegreeZeroPostCollapseSourceBridgeScratch
import Grok610DegreeZeroSplitChildrenPart10Scratch
import Grok610DegreeZeroSplitChildrenPart08Scratch
import Grok610DegreeZeroSplitChildrenPart07Scratch
import Grok610DegreeZeroSplitChildrenPart03Scratch
import Grok610DegreeZeroSplitChildrenPart02Scratch
import Grok610DegreeZeroSplitChildrenPart01Scratch

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option maxHeartbeats 800000000

section DegreeZeroOrderOneSource610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 800000000 in
/-- On `p32(a) = 0` the simple-pole obstruction peels one more power of
`h0` and forces the order-`70` head to vanish. -/
theorem degreeZeroPostCollapseP32ZeroOrderOne610_zero_of_primitiveDeriv
    (h0 w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 : k[X])
    (lambda j a : k) (hh0 : h0 ≠ 0) (hdegree : h0.natDegree = 1)
    (hroot : h0.eval a = 0) (hp32 : p32.eval a = 0)
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
    degreeZeroPostCollapseP32ZeroOrderOne610 (w1.eval a) (p21.eval a)
      (p1.eval a) (q41.eval a) (q3.eval a) = 0 := by
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
  have hquotientZero : quotient.eval a = 0 :=
    localLinearPoleSix_head_eval_zero_of_deriv_eq_simplePole610 a j h0
      quotient rho hdegree hroot hclear (by simpa [rho, hRF] using hderiv)
  obtain ⟨Q1, hQeq⟩ := linearPolynomial_dvd_of_eval_eq_zero_610 h0
    quotient a hdegree hroot hquotientZero
  have hclear5 : algebraMap k[X] (RatFunc k) Q1 = hRF ^ 5 * rho :=
    algebraMap_cancel_one_clearing_610 h0 quotient Q1 rho 5 hh0 hQeq
      (by simpa [hRF] using hclear)
  have hQ1zero : Q1.eval a = 0 :=
    localLinearPoleFive_head_eval_zero_of_deriv_eq_simplePole610 a j h0
      Q1 rho hdegree hroot hclear5 (by simpa [rho, hRF] using hderiv)
  obtain ⟨p32', hp32eq⟩ := linearPolynomial_dvd_of_eval_eq_zero_610 h0
    p32 a hdegree hroot hp32
  have hform := degreeZeroPostCollapseJetQuotient610_orderExpansion h0
    w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1
    (Polynomial.C lambda)
  have hident :
      Q1 =
        (7583143431241728 : k[X]) * h0 ^ 2 * p32' ^ 3 * q41 +
          degreeZeroPostCollapseJetOrderOne610 w1 a42 p32 p21 p1 q53
            q41 q3 u2 +
          h0 * degreeZeroPostCollapseJetOrderTwoPlus610 h0 w1 a42 p32
            p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1
            (Polynomial.C lambda) := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * Q1 = quotient := hQeq.symm
      _ = degreeZeroPostCollapseJetHead610 p32 q41 +
            h0 * degreeZeroPostCollapseJetOrderOne610 w1 a42 p32 p21 p1
              q53 q41 q3 u2 +
            h0 ^ 2 * degreeZeroPostCollapseJetOrderTwoPlus610 h0 w1 a42
              p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1
              (Polynomial.C lambda) := hform
      _ = h0 *
            ((7583143431241728 : k[X]) * h0 ^ 2 * p32' ^ 3 * q41 +
              degreeZeroPostCollapseJetOrderOne610 w1 a42 p32 p21 p1
                q53 q41 q3 u2 +
              h0 * degreeZeroPostCollapseJetOrderTwoPlus610 h0 w1 a42
                p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1
                (Polynomial.C lambda)) := by
        simp only [degreeZeroPostCollapseJetHead610, hp32eq]
        ring
  have hQ1eval :
      Q1.eval a =
        (degreeZeroPostCollapseJetOrderOne610 w1 a42 p32 p21 p1 q53 q41
          q3 u2).eval a := by
    rw [hident]
    simp only [Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_ofNat, hroot]
    ring
  have horderEval :
      (degreeZeroPostCollapseJetOrderOne610 w1 a42 p32 p21 p1 q53 q41 q3
          u2).eval a =
        degreeZeroPostCollapseP32ZeroOrderOne610 (w1.eval a)
          (p21.eval a) (p1.eval a) (q41.eval a) (q3.eval a) := by
    rw [degreeZeroPostCollapseJetOrderOne610_eval]
    exact degreeZeroPostCollapseJetOrderOne610_p32Zero (w1.eval a)
      (a42.eval a) (p32.eval a) (p21.eval a) (p1.eval a) (q53.eval a)
      (q41.eval a) (q3.eval a) (u2.eval a) hp32
  rw [← horderEval, ← hQ1eval]
  exact hQ1zero

end DegreeZeroOrderOneSource610

end Max11DegreeRoutes
