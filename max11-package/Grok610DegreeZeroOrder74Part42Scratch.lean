import Grok610DegreeZeroOrder74Part38Scratch
import Grok610DegreeZeroOrder74Part35Scratch
import Grok610DegreeZeroOrder74Part18Scratch

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option maxHeartbeats 800000000

section DegreeZeroOrderFiveSource610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 800000000 in
/-- On `q41(a) = 0` the mixed order-`71` object peels and pole-three
forces the mixed order-`72` head.  The second Taylor `q41nn` is already
named; a third Taylor is not required.  Cumulative vanishing: `h0^4`
divides the jet quotient (`M = 4`; next unused mixed order `73`). -/
theorem degreeZeroPostCollapseQ41ZeroMixedOrderThree610_zero_of_primitiveDeriv
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
    ∃ q41n q41nn o70n o71n : k[X],
      q41 = h0 * q41n ∧
        q41n = C (q41n.eval a) + h0 * q41nn ∧
        degreeZeroPostCollapseQ41ZeroMixedOrderOne610 w1 a42 p32 p21 p1
            q53 q41n q3 u2 =
          h0 * o70n ∧
        o70n +
            degreeZeroPostCollapseQ41ZeroMixedOrderTwo610 w1 a42 p32
              p21 p1 s2 u2 b63 q53 q41n q3 q2 (Polynomial.C lambda) =
          h0 * o71n ∧
        o71n.eval a +
            degreeZeroPostCollapseQ41ZeroMixedOrderThree610 (w1.eval a)
              (a42.eval a) (p32.eval a) (p21.eval a) (p1.eval a)
              (p0.eval a) (s2.eval a) (u2.eval a) (b63.eval a)
              (q53.eval a) (q41n.eval a) (q3.eval a) (q2.eval a)
              (q1.eval a) lambda =
          0 ∧
        h0 ^ 4 ∣
          degreeZeroPostCollapseJetQuotient610 h0 w1 a42 p32 p21 p1 p0
            s2 u2 b63 q53 q41 q3 q2 q1 (Polynomial.C lambda) := by
  obtain ⟨q41n, q41nn, o70n, hq41eq, hTaylor, ho70, hmix, _hdvd⟩ :=
    degreeZeroPostCollapseQ41ZeroMixedOrderTwo610_zero_of_primitiveDeriv
      h0 w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda j a hh0
      hdegree hroot hq41 hderiv
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
  have hSumEval :
      (o70n +
          degreeZeroPostCollapseQ41ZeroMixedOrderTwo610 w1 a42 p32 p21
            p1 s2 u2 b63 q53 q41n q3 q2 (Polynomial.C lambda)).eval a =
        0 := by
    simp only [Polynomial.eval_add,
      degreeZeroPostCollapseQ41ZeroMixedOrderTwo610_eval]
    exact hmix
  obtain ⟨o71n, ho71⟩ := linearPolynomial_dvd_of_eval_eq_zero_610 h0
    (o70n +
      degreeZeroPostCollapseQ41ZeroMixedOrderTwo610 w1 a42 p32 p21 p1
        s2 u2 b63 q53 q41n q3 q2 (Polynomial.C lambda)) a hdegree hroot
    hSumEval
  let seven : k[X] :=
    (45498860587450368 : k[X]) * a42 * p21 * p32 * q41n -
      49290432303071232 * a42 * p32 ^ 2 * q41n * w1 -
      38999023360671744 * p1 * p21 * q41n +
      45498860587450368 * p1 * p32 * q41n * w1 +
      22749430293725184 * p21 ^ 2 * q41n * w1 -
      49290432303071232 * p21 * p32 * q41n * w1 ^ 2 +
      26014394826620928 * p32 ^ 2 * q41n * w1 ^ 3
  let Q3 : k[X] :=
    o71n +
      degreeZeroPostCollapseQ41ZeroMixedOrderTwoPlus610 h0 w1 a42 p32
        p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 (Polynomial.C lambda)
  have hquot : quotient = h0 ^ 3 * Q3 := by
    have hform := degreeZeroPostCollapseJetQuotient610_orderExpansion h0
      w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1
      (Polynomial.C lambda)
    have hheadEq :=
      degreeZeroPostCollapseQ41ZeroMixedOrderOne610_headEq h0 w1 a42
        p32 p21 p1 q53 q41n q3 u2
    have hscale :=
      degreeZeroPostCollapseJetOrderTwoPlus610_q41Scale h0 w1 a42 p32
        p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 (Polynomial.C lambda)
    have hfrozen :=
      degreeZeroPostCollapseQ41ZeroMixedOrderTwo610_of_frozen w1 a42
        p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1
        (Polynomial.C lambda)
    calc
      quotient =
          degreeZeroPostCollapseJetHead610 p32 q41 +
            h0 *
              degreeZeroPostCollapseJetOrderOne610 w1 a42 p32 p21 p1
                q53 q41 q3 u2 +
            h0 ^ 2 *
              degreeZeroPostCollapseJetOrderTwoPlus610 h0 w1 a42 p32
                p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1
                (Polynomial.C lambda) := by
        simpa [quotient] using hform
      _ = degreeZeroPostCollapseJetHead610 p32 (h0 * q41n) +
            h0 *
              degreeZeroPostCollapseJetOrderOne610 w1 a42 p32 p21 p1
                q53 (h0 * q41n) q3 u2 +
            h0 ^ 2 *
              degreeZeroPostCollapseJetOrderTwoPlus610 h0 w1 a42 p32
                p21 p1 p0 s2 u2 b63 q53 (h0 * q41n) q3 q2 q1
                (Polynomial.C lambda) := by
        simp only [hq41eq]
      _ = h0 *
              degreeZeroPostCollapseQ41ZeroMixedOrderOne610 w1 a42 p32
                p21 p1 q53 q41n q3 u2 +
            h0 ^ 2 * seven +
            h0 ^ 2 *
              degreeZeroPostCollapseJetOrderTwoPlus610 h0 w1 a42 p32
                p21 p1 p0 s2 u2 b63 q53 (h0 * q41n) q3 q2 q1
                (Polynomial.C lambda) := by
        rw [hheadEq]
      _ = h0 *
              degreeZeroPostCollapseQ41ZeroMixedOrderOne610 w1 a42 p32
                p21 p1 q53 q41n q3 u2 +
            h0 ^ 2 * seven +
            h0 ^ 2 *
              (degreeZeroPostCollapseJetOrderTwoPlus610 0 w1 a42 p32
                  p21 p1 p0 s2 u2 b63 q53 0 q3 q2 q1
                  (Polynomial.C lambda) +
                h0 *
                  degreeZeroPostCollapseQ41ZeroMixedOrderTwoPlus610
                    h0 w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2
                    q1 (Polynomial.C lambda)) := by
        rw [hscale]
      _ = h0 ^ 2 *
              (o70n +
                (seven +
                  degreeZeroPostCollapseJetOrderTwoPlus610 0 w1 a42
                    p32 p21 p1 p0 s2 u2 b63 q53 0 q3 q2 q1
                    (Polynomial.C lambda))) +
            h0 ^ 3 *
              degreeZeroPostCollapseQ41ZeroMixedOrderTwoPlus610 h0 w1
                a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1
                (Polynomial.C lambda) := by
        rw [ho70]
        ring
      _ = h0 ^ 2 *
              (o70n +
                degreeZeroPostCollapseQ41ZeroMixedOrderTwo610 w1 a42
                  p32 p21 p1 s2 u2 b63 q53 q41n q3 q2
                  (Polynomial.C lambda)) +
            h0 ^ 3 *
              degreeZeroPostCollapseQ41ZeroMixedOrderTwoPlus610 h0 w1
                a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1
                (Polynomial.C lambda) := by
        simp only [seven]
        rw [hfrozen]
      _ = h0 ^ 3 * Q3 := by
        rw [ho71]
        simp only [Q3]
        ring
  have hclear3 : algebraMap k[X] (RatFunc k) Q3 = hRF ^ 3 * rho :=
    algebraMap_cancel_three_of_six_clearing610 h0 Q3 rho hh0 (by
      simpa [hquot] using hclear)
  have hQ3zero : Q3.eval a = 0 :=
    localLinearPoleThree_head_eval_zero_of_deriv_eq_simplePole610 a j
      h0 Q3 rho hdegree hroot hclear3 (by simpa [rho, hRF] using hderiv)
  have hQ3eval :
      Q3.eval a =
        o71n.eval a +
          degreeZeroPostCollapseQ41ZeroMixedOrderThree610 (w1.eval a)
            (a42.eval a) (p32.eval a) (p21.eval a) (p1.eval a)
            (p0.eval a) (s2.eval a) (u2.eval a) (b63.eval a)
            (q53.eval a) (q41n.eval a) (q3.eval a) (q2.eval a)
            (q1.eval a) lambda := by
    simp only [Q3, Polynomial.eval_add]
    rw [degreeZeroPostCollapseQ41ZeroMixedOrderTwoPlus610_eval_root h0
      w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda a hroot]
  obtain ⟨Q4, hQ4⟩ := linearPolynomial_dvd_of_eval_eq_zero_610 h0 Q3 a
    hdegree hroot hQ3zero
  refine ⟨q41n, q41nn, o70n, o71n, hq41eq, hTaylor, ho70, ho71, ?_,
    ?_⟩
  · rw [← hQ3eval]
    exact hQ3zero
  · refine ⟨Q4, ?_⟩
    calc
      quotient = h0 ^ 3 * Q3 := hquot
      _ = h0 ^ 3 * (h0 * Q4) := by rw [hQ4]
      _ = h0 ^ 4 * Q4 := by ring

end DegreeZeroOrderFiveSource610

end Max11DegreeRoutes
