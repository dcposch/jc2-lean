import Grok610DegreeZeroOrder72Part01Scratch
import Grok610DegreeZeroOrder72Part16Scratch
import Grok610DegreeZeroOrder72Part26Scratch

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
/-- On `p32(a) = q41(a) = q3(a) = 0` pole-three forces the next Taylor
of the eight-term residual plus the order-`72` mixin to vanish. -/
theorem degreeZeroPostCollapseP32Q41Q3ZeroOrderThreeHead610_zero_of_primitiveDeriv
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
        RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    ∃ p32n q41n q3n o71n : k[X],
      p32 = h0 * p32n ∧ q41 = h0 * q41n ∧ q3 = h0 * q3n ∧
        degreeZeroPostCollapseP32Q41Q3ZeroOrderTwoHead610 w1 a42 p21 p1
            q53 q41n q3n u2 =
          h0 * o71n ∧
        o71n.eval a +
            degreeZeroPostCollapseP32Q41Q3ZeroOrderThreeHead610
              (w1.eval a) (a42.eval a) (p32n.eval a) (p21.eval a)
              (p1.eval a) (p0.eval a) (s2.eval a) (u2.eval a)
              (b63.eval a) (q53.eval a) (q41n.eval a) (q3n.eval a)
              (q2.eval a) lambda =
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
  obtain ⟨Q2, hQ1eq⟩ := linearPolynomial_dvd_of_eval_eq_zero_610 h0 Q1 a
    hdegree hroot hQ1zero
  have hclear4 : algebraMap k[X] (RatFunc k) Q2 = hRF ^ 4 * rho :=
    algebraMap_cancel_one_clearing_610 h0 Q1 Q2 rho 4 hh0 hQ1eq hclear5
  have hQ2zero : Q2.eval a = 0 :=
    localLinearPoleFour_head_eval_zero_of_deriv_eq_simplePole610 a j h0
      Q2 rho hdegree hroot hclear4 (by simpa [rho, hRF] using hderiv)
  obtain ⟨Q3, hQ2eq⟩ := linearPolynomial_dvd_of_eval_eq_zero_610 h0 Q2 a
    hdegree hroot hQ2zero
  have hclear3 : algebraMap k[X] (RatFunc k) Q3 = hRF ^ 3 * rho :=
    algebraMap_cancel_one_clearing_610 h0 Q2 Q3 rho 3 hh0 hQ2eq hclear4
  have hQ3zero : Q3.eval a = 0 :=
    localLinearPoleThree_head_eval_zero_of_deriv_eq_simplePole610 a j h0
      Q3 rho hdegree hroot hclear3 (by simpa [rho, hRF] using hderiv)
  obtain ⟨p32n, hp32eq⟩ := linearPolynomial_dvd_of_eval_eq_zero_610 h0
    p32 a hdegree hroot hp32
  obtain ⟨q41n, hq41eq⟩ := linearPolynomial_dvd_of_eval_eq_zero_610 h0
    q41 a hdegree hroot hq41
  obtain ⟨q3n, hq3eq⟩ := linearPolynomial_dvd_of_eval_eq_zero_610 h0 q3
    a hdegree hroot hq3
  have hident :
      Q2 =
        degreeZeroPostCollapseP32Q41Q3ZeroOrderTwoHead610 w1 a42 p21 p1
            q53 q41n q3n u2 +
          h0 *
            degreeZeroPostCollapseP32Q41Q3ZeroOrderThreeHead610 w1 a42
              p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2
              (Polynomial.C lambda) +
          h0 ^ 2 *
            degreeZeroPostCollapseP32Q41Q3ZeroOrderThreePlus610 h0 w1
              a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1
              (Polynomial.C lambda) := by
    apply mul_left_cancel₀ hh0
    apply mul_left_cancel₀ hh0
    calc
      h0 * (h0 * Q2) = h0 * Q1 := by
        rw [hQ1eq]
      _ = quotient := hQeq.symm
      _ = degreeZeroPostCollapseJetQuotient610 h0 w1 a42 (h0 * p32n)
            p21 p1 p0 s2 u2 b63 q53 (h0 * q41n) (h0 * q3n) q2 q1
            (Polynomial.C lambda) := by
        simp only [quotient, hp32eq, hq41eq, hq3eq]
      _ = h0 ^ 2 *
              degreeZeroPostCollapseP32Q41Q3ZeroOrderTwoHead610 w1 a42
                p21 p1 q53 q41n q3n u2 +
            h0 ^ 3 *
              degreeZeroPostCollapseP32Q41Q3ZeroOrderThreeHead610 w1
                a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2
                (Polynomial.C lambda) +
            h0 ^ 4 *
              degreeZeroPostCollapseP32Q41Q3ZeroOrderThreePlus610 h0
                w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1
                (Polynomial.C lambda) :=
        degreeZeroPostCollapseJetQuotient610_p32Q41Q3Scale h0 w1 a42
          p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1
          (Polynomial.C lambda)
      _ = h0 * (h0 *
            (degreeZeroPostCollapseP32Q41Q3ZeroOrderTwoHead610 w1 a42
                p21 p1 q53 q41n q3n u2 +
              h0 *
                degreeZeroPostCollapseP32Q41Q3ZeroOrderThreeHead610 w1
                  a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2
                  (Polynomial.C lambda) +
              h0 ^ 2 *
                degreeZeroPostCollapseP32Q41Q3ZeroOrderThreePlus610 h0
                  w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1
                  (Polynomial.C lambda))) := by
        ring
  have hQ2eval :
      Q2.eval a =
        (degreeZeroPostCollapseP32Q41Q3ZeroOrderTwoHead610 w1 a42 p21
          p1 q53 q41n q3n u2).eval a := by
    rw [hident]
    simp only [Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, hroot]
    ring
  have ho71zero :
      (degreeZeroPostCollapseP32Q41Q3ZeroOrderTwoHead610 w1 a42 p21 p1
          q53 q41n q3n u2).eval a = 0 := by
    rw [← hQ2eval]
    exact hQ2zero
  obtain ⟨o71n, ho71eq⟩ := linearPolynomial_dvd_of_eval_eq_zero_610 h0
    (degreeZeroPostCollapseP32Q41Q3ZeroOrderTwoHead610 w1 a42 p21 p1
      q53 q41n q3n u2) a hdegree hroot ho71zero
  have hQ3ident :
      Q3 =
        o71n +
          degreeZeroPostCollapseP32Q41Q3ZeroOrderThreeHead610 w1 a42
            p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2
            (Polynomial.C lambda) +
          h0 *
            degreeZeroPostCollapseP32Q41Q3ZeroOrderThreePlus610 h0 w1
              a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1
              (Polynomial.C lambda) := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * Q3 = Q2 := hQ2eq.symm
      _ = degreeZeroPostCollapseP32Q41Q3ZeroOrderTwoHead610 w1 a42 p21
            p1 q53 q41n q3n u2 +
          h0 *
            degreeZeroPostCollapseP32Q41Q3ZeroOrderThreeHead610 w1 a42
              p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2
              (Polynomial.C lambda) +
          h0 ^ 2 *
            degreeZeroPostCollapseP32Q41Q3ZeroOrderThreePlus610 h0 w1
              a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1
              (Polynomial.C lambda) := hident
      _ = h0 * o71n +
          h0 *
            degreeZeroPostCollapseP32Q41Q3ZeroOrderThreeHead610 w1 a42
              p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2
              (Polynomial.C lambda) +
          h0 ^ 2 *
            degreeZeroPostCollapseP32Q41Q3ZeroOrderThreePlus610 h0 w1
              a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1
              (Polynomial.C lambda) := by
        rw [ho71eq]
      _ = h0 *
            (o71n +
              degreeZeroPostCollapseP32Q41Q3ZeroOrderThreeHead610 w1
                a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2
                (Polynomial.C lambda) +
              h0 *
                degreeZeroPostCollapseP32Q41Q3ZeroOrderThreePlus610 h0
                  w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1
                  (Polynomial.C lambda)) := by
        ring
  have hQ3eval :
      Q3.eval a =
        o71n.eval a +
          degreeZeroPostCollapseP32Q41Q3ZeroOrderThreeHead610
            (w1.eval a) (a42.eval a) (p32n.eval a) (p21.eval a)
            (p1.eval a) (p0.eval a) (s2.eval a) (u2.eval a)
            (b63.eval a) (q53.eval a) (q41n.eval a) (q3n.eval a)
            (q2.eval a) lambda := by
    rw [hQ3ident]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, hroot,
      degreeZeroPostCollapseP32Q41Q3ZeroOrderThreeHead610_eval]
    ring
  refine ⟨p32n, q41n, q3n, o71n, hp32eq, hq41eq, hq3eq, ho71eq, ?_⟩
  rw [← hQ3eval]
  exact hQ3zero

end DegreeZeroOrderThreeSource610

end Max11DegreeRoutes
