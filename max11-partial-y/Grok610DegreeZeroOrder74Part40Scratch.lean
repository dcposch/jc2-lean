import Grok610DegreeZeroOrder74Part37Scratch
import Grok610DegreeZeroOrder74Part01Scratch
import Grok610DegreeZeroOrder74Part33Scratch
import Grok610DegreeZeroOrder74Part13Scratch

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option maxHeartbeats 800000000

section DegreeZeroOrderFiveSource610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 800000000 in
/-- On `p32(a) = p21(a) = 0` pole-one forces the next Taylor of
`o72n + OrderFour` plus the order-`74` mixin to vanish.
Cumulative vanishing: `h0^6` divides the jet quotient (`M = 6`; next
unused order `75`). -/
theorem degreeZeroPostCollapseP32P21ZeroOrderFiveHead610_zero_of_primitiveDeriv
    (h0 w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 : k[X])
    (lambda j a : k) (hh0 : h0 ≠ 0) (hdegree : h0.natDegree = 1)
    (hroot : h0.eval a = 0) (hp32 : p32.eval a = 0)
    (hp21 : p21.eval a = 0)
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
    ∃ p32n p21n o71n o72n o73n : k[X],
      p32 = h0 * p32n ∧ p21 = h0 * p21n ∧
        degreeZeroPostCollapseP32P21ZeroOrderTwoHead610 w1 a42 p32n
            p21n p1 q53 q41 q3 =
          h0 * o71n ∧
        o71n +
            degreeZeroPostCollapseP32P21ZeroOrderThreeHead610 w1 a42
              p32n p21n p1 p0 u2 b63 q53 q41 q3 q2 =
          h0 * o72n ∧
        o72n +
            degreeZeroPostCollapseP32P21ZeroOrderFour610 w1 a42 p32n
              p21n p1 p0 s2 u2 b63 q53 q2 q1 (Polynomial.C lambda) =
          h0 * o73n ∧
        o73n.eval a +
            degreeZeroPostCollapseP32P21ZeroOrderFive610 (w1.eval a)
              (a42.eval a) (p32n.eval a) (p21n.eval a) (p1.eval a)
              (p0.eval a) (s2.eval a) (u2.eval a) (b63.eval a)
              (q1.eval a) lambda =
          0 ∧
        h0 ^ 6 ∣
          degreeZeroPostCollapseJetQuotient610 h0 w1 a42 p32 p21 p1 p0
            s2 u2 b63 q53 q41 q3 q2 q1 (Polynomial.C lambda) := by
  obtain ⟨p32n, p21n, o71n, o72n, hp32eq, hp21eq, ho71, ho72, hmix,
      _hdvd⟩ :=
    degreeZeroPostCollapseP32P21ZeroOrderFourHead610_zero_of_primitiveDeriv
      h0 w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda j a hh0
      hdegree hroot hp32 hp21 hderiv
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
      (o72n +
          degreeZeroPostCollapseP32P21ZeroOrderFour610 w1 a42 p32n
            p21n p1 p0 s2 u2 b63 q53 q2 q1 (Polynomial.C lambda)).eval
        a = 0 := by
    simp only [Polynomial.eval_add,
      degreeZeroPostCollapseP32P21ZeroOrderFour610_eval]
    exact hmix
  obtain ⟨o73n, ho73⟩ := linearPolynomial_dvd_of_eval_eq_zero_610 h0
    (o72n +
      degreeZeroPostCollapseP32P21ZeroOrderFour610 w1 a42 p32n p21n p1
        p0 s2 u2 b63 q53 q2 q1 (Polynomial.C lambda)) a hdegree hroot
    hSumEval
  let Q5 : k[X] :=
    o73n +
      degreeZeroPostCollapseP32P21ZeroOrderFourPlus610 h0 w1 a42 p32n
        p21n p1 p0 s2 u2 b63 q1 (Polynomial.C lambda)
  have hquot : quotient = h0 ^ 5 * Q5 := by
    have hplus :=
      degreeZeroPostCollapseP32P21ZeroOrderThreePlus610_of_fourPlus h0
        w1 a42 p32n p21n p1 p0 s2 u2 b63 q53 q41 q3 q2 q1
        (Polynomial.C lambda)
    calc
      quotient =
          degreeZeroPostCollapseJetQuotient610 h0 w1 a42 (h0 * p32n)
            (h0 * p21n) p1 p0 s2 u2 b63 q53 q41 q3 q2 q1
            (Polynomial.C lambda) := by
        simp only [quotient, hp32eq, hp21eq]
      _ = h0 ^ 2 *
              degreeZeroPostCollapseP32P21ZeroOrderTwoHead610 w1 a42
                p32n p21n p1 q53 q41 q3 +
            h0 ^ 3 *
              degreeZeroPostCollapseP32P21ZeroOrderThreeHead610 w1 a42
                p32n p21n p1 p0 u2 b63 q53 q41 q3 q2 +
            h0 ^ 4 *
              degreeZeroPostCollapseP32P21ZeroOrderThreePlus610 h0 w1
                a42 p32n p21n p1 p0 s2 u2 b63 q53 q41 q3 q2 q1
                (Polynomial.C lambda) :=
        degreeZeroPostCollapseJetQuotient610_p32P21Scale h0 w1 a42 p32n
          p21n p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 (Polynomial.C lambda)
      _ = h0 ^ 3 *
              (o71n +
                degreeZeroPostCollapseP32P21ZeroOrderThreeHead610 w1
                  a42 p32n p21n p1 p0 u2 b63 q53 q41 q3 q2) +
            h0 ^ 4 *
              degreeZeroPostCollapseP32P21ZeroOrderThreePlus610 h0 w1
                a42 p32n p21n p1 p0 s2 u2 b63 q53 q41 q3 q2 q1
                (Polynomial.C lambda) := by
        rw [ho71]
        ring
      _ = h0 ^ 4 *
            (o72n +
              degreeZeroPostCollapseP32P21ZeroOrderThreePlus610 h0 w1
                a42 p32n p21n p1 p0 s2 u2 b63 q53 q41 q3 q2 q1
                (Polynomial.C lambda)) := by
        rw [ho72]
        ring
      _ = h0 ^ 5 * Q5 := by
        rw [hplus, ← add_assoc, ho73]
        simp only [Q5]
        ring
  have hclear5 : algebraMap k[X] (RatFunc k) Q5 = hRF ^ 1 * rho :=
    algebraMap_cancel_five_of_six_clearing610 h0 Q5 rho hh0 (by
      simpa [hquot] using hclear)
  have hQ5zero : Q5.eval a = 0 :=
    localLinearPoleOne_head_eval_zero_of_deriv_eq_simplePole610 a j h0
      Q5 rho hdegree hroot hclear5 (by simpa [rho, hRF] using hderiv)
  have hQ5eval :
      Q5.eval a =
        o73n.eval a +
          degreeZeroPostCollapseP32P21ZeroOrderFive610 (w1.eval a)
            (a42.eval a) (p32n.eval a) (p21n.eval a) (p1.eval a)
            (p0.eval a) (s2.eval a) (u2.eval a) (b63.eval a)
            (q1.eval a) lambda := by
    simp only [Q5, Polynomial.eval_add]
    rw [degreeZeroPostCollapseP32P21ZeroOrderFourPlus610_eval_root h0
      w1 a42 p32n p21n p1 p0 s2 u2 b63 q1 lambda a hroot]
  obtain ⟨Q6, hQ6⟩ := linearPolynomial_dvd_of_eval_eq_zero_610 h0 Q5 a
    hdegree hroot hQ5zero
  refine ⟨p32n, p21n, o71n, o72n, o73n, hp32eq, hp21eq, ho71, ho72,
    ho73, ?_, ?_⟩
  · rw [← hQ5eval]
    exact hQ5zero
  · refine ⟨Q6, ?_⟩
    calc
      quotient = h0 ^ 5 * Q5 := hquot
      _ = h0 ^ 5 * (h0 * Q6) := by rw [hQ6]
      _ = h0 ^ 6 * Q6 := by ring

end DegreeZeroOrderFiveSource610

end Max11DegreeRoutes
