import Grok610DegreeZeroOrder72Part19Scratch
import Grok610DegreeZeroOrder72Part28Scratch

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 100000000
set_option maxHeartbeats 800000000

section DegreeZeroOrderThreeSource610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 800000000 in
/-- On `q41(a) = 0` the differentiated order-`69` identity plus the
frozen order-`70` coefficient is the mixed head linear in `q41n`. -/
theorem degreeZeroPostCollapseQ41ZeroMixedOrderOne610_zero_of_primitiveDeriv
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
    ∃ q41n : k[X],
      q41 = h0 * q41n ∧
        degreeZeroPostCollapseQ41ZeroMixedOrderOne610 (w1.eval a)
            (a42.eval a) (p32.eval a) (p21.eval a) (p1.eval a)
            (q53.eval a) (q41n.eval a) (q3.eval a) (u2.eval a) =
          0 := by
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
  obtain ⟨q41n, hq41eq⟩ := linearPolynomial_dvd_of_eval_eq_zero_610 h0
    q41 a hdegree hroot hq41
  have hform := degreeZeroPostCollapseJetQuotient610_orderExpansion h0
    w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1
    (Polynomial.C lambda)
  have hident :
      Q1 =
        degreeZeroPostCollapseQ41ZeroMixedOrderOne610 w1 a42 p32 p21 p1
            q53 q41n q3 u2 +
          h0 *
            (45498860587450368 * a42 * p21 * p32 * q41n -
              49290432303071232 * a42 * p32 ^ 2 * q41n * w1 -
              38999023360671744 * p1 * p21 * q41n +
              45498860587450368 * p1 * p32 * q41n * w1 +
              22749430293725184 * p21 ^ 2 * q41n * w1 -
              49290432303071232 * p21 * p32 * q41n * w1 ^ 2 +
              26014394826620928 * p32 ^ 2 * q41n * w1 ^ 3 +
              degreeZeroPostCollapseJetOrderTwoPlus610 h0 w1 a42 p32
                p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1
                (Polynomial.C lambda)) := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * Q1 = quotient := hQeq.symm
      _ = degreeZeroPostCollapseJetHead610 p32 q41 +
            h0 *
              degreeZeroPostCollapseJetOrderOne610 w1 a42 p32 p21 p1
                q53 q41 q3 u2 +
            h0 ^ 2 *
              degreeZeroPostCollapseJetOrderTwoPlus610 h0 w1 a42 p32
                p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1
                (Polynomial.C lambda) := hform
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
            (degreeZeroPostCollapseQ41ZeroMixedOrderOne610 w1 a42 p32
                p21 p1 q53 q41n q3 u2 +
              h0 *
                (45498860587450368 * a42 * p21 * p32 * q41n -
                  49290432303071232 * a42 * p32 ^ 2 * q41n * w1 -
                  38999023360671744 * p1 * p21 * q41n +
                  45498860587450368 * p1 * p32 * q41n * w1 +
                  22749430293725184 * p21 ^ 2 * q41n * w1 -
                  49290432303071232 * p21 * p32 * q41n * w1 ^ 2 +
                  26014394826620928 * p32 ^ 2 * q41n * w1 ^ 3 +
                  degreeZeroPostCollapseJetOrderTwoPlus610 h0 w1 a42
                    p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1
                    (Polynomial.C lambda))) := by
        rw [degreeZeroPostCollapseQ41ZeroMixedOrderOne610_headEq]
        ring
  have hQ1eval :
      Q1.eval a =
        degreeZeroPostCollapseQ41ZeroMixedOrderOne610 (w1.eval a)
          (a42.eval a) (p32.eval a) (p21.eval a) (p1.eval a)
          (q53.eval a) (q41n.eval a) (q3.eval a) (u2.eval a) := by
    rw [hident]
    simp only [Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_ofNat, hroot,
      degreeZeroPostCollapseQ41ZeroMixedOrderOne610_eval]
    ring
  refine ⟨q41n, hq41eq, ?_⟩
  rw [← hQ1eval]
  exact hQ1zero

end DegreeZeroOrderThreeSource610

end Max11DegreeRoutes
