import Grok610DegreeZeroOrder74Part102Scratch
import Grok610DegreeZeroOrder74Part101Scratch
import Grok610DegreeZeroOrder74Part05Scratch

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option maxHeartbeats 800000000

section DegreeZeroOrderFiveHead610

variable {R : Type*} [CommRing R]

set_option maxHeartbeats 800000000 in
theorem degreeZeroPostCollapseP32Q41Q3ZeroOrderThreePlus610_of_fourPlus
    (h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda : R) :
    degreeZeroPostCollapseP32Q41Q3ZeroOrderThreePlus610 h w1 a42 p32n
        p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda =
      degreeZeroPostCollapseP32Q41Q3ZeroOrderFour610 w1 a42 p32n p21 p1
        p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda +
        h *
          degreeZeroPostCollapseP32Q41Q3ZeroOrderFourPlus610 h w1 a42
            p32n p21 p1 p0 s2 u2 b63 q1 lambda := by
  simp only [degreeZeroPostCollapseP32Q41Q3ZeroOrderThreePlus610,
    degreeZeroPostCollapseP32Q41Q3ZeroOrderFour610,
    degreeZeroPostCollapseP32Q41Q3ZeroOrderFourPlus610]
  ring

end DegreeZeroOrderFiveHead610

end Max11DegreeRoutes
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option maxHeartbeats 800000000

section DegreeZeroOrderFiveHead610

variable {R : Type*} [CommRing R]

set_option maxHeartbeats 800000000 in
theorem degreeZeroPostCollapseP32P21P1ZeroOrderFourPlus610_zero
    (w1 a42 p32n p21n p1n p0 s2 u2 b63 q1 lambda : R) :
    degreeZeroPostCollapseP32P21P1ZeroOrderFourPlus610 0 w1 a42 p32n
        p21n p1n p0 s2 u2 b63 q1 lambda =
      degreeZeroPostCollapseP32P21P1ZeroOrderFive610 w1 a42 p32n p21n
        p1n p0 u2 b63 q1 := by
  simp only [degreeZeroPostCollapseP32P21P1ZeroOrderFourPlus610,
    degreeZeroPostCollapseP32P21P1ZeroOrderFive610, zero_mul, mul_zero,
    add_zero, sub_zero]

end DegreeZeroOrderFiveHead610

end Max11DegreeRoutes
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option maxHeartbeats 800000000

section DegreeZeroOrderFiveHead610

variable {R : Type*} [CommRing R]

set_option maxHeartbeats 800000000 in
theorem degreeZeroPostCollapseP32P21ZeroOrderFourPlus610_zero
    (w1 a42 p32n p21n p1 p0 s2 u2 b63 q1 lambda : R) :
    degreeZeroPostCollapseP32P21ZeroOrderFourPlus610 0 w1 a42 p32n p21n
        p1 p0 s2 u2 b63 q1 lambda =
      degreeZeroPostCollapseP32P21ZeroOrderFive610 w1 a42 p32n p21n p1
        p0 s2 u2 b63 q1 lambda := by
  simp only [degreeZeroPostCollapseP32P21ZeroOrderFourPlus610,
    degreeZeroPostCollapseP32P21ZeroOrderFive610, zero_mul, mul_zero,
    add_zero, sub_zero]

end DegreeZeroOrderFiveHead610

end Max11DegreeRoutes
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option maxHeartbeats 800000000

section DegreeZeroOrderFiveHead610

variable {R : Type*} [CommRing R]

set_option maxHeartbeats 800000000 in
theorem degreeZeroPostCollapseP32Q41Q3ZeroOrderFourPlus610_zero
    (w1 a42 p32n p21 p1 p0 s2 u2 b63 q1 lambda : R) :
    degreeZeroPostCollapseP32Q41Q3ZeroOrderFourPlus610 0 w1 a42 p32n
        p21 p1 p0 s2 u2 b63 q1 lambda =
      degreeZeroPostCollapseP32Q41Q3ZeroOrderFive610 w1 a42 p32n p21 p1
        p0 s2 u2 b63 q1 lambda := by
  simp only [degreeZeroPostCollapseP32Q41Q3ZeroOrderFourPlus610,
    degreeZeroPostCollapseP32Q41Q3ZeroOrderFive610, zero_mul, mul_zero,
    add_zero, sub_zero]

end DegreeZeroOrderFiveHead610

end Max11DegreeRoutes
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option maxHeartbeats 800000000

section DegreeZeroOrderFiveHead610

variable {R : Type*} [CommRing R]

set_option maxHeartbeats 800000000 in
theorem degreeZeroPostCollapseJetOrderTwoPlus610_q41Scale
    (h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda : R) :
    degreeZeroPostCollapseJetOrderTwoPlus610 h w1 a42 p32 p21 p1 p0 s2
        u2 b63 q53 (h * q41n) q3 q2 q1 lambda =
      degreeZeroPostCollapseJetOrderTwoPlus610 0 w1 a42 p32 p21 p1 p0
          s2 u2 b63 q53 0 q3 q2 q1 lambda +
        h *
          degreeZeroPostCollapseQ41ZeroMixedOrderTwoPlus610 h w1 a42
            p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda := by
  simp only [degreeZeroPostCollapseJetOrderTwoPlus610,
    degreeZeroPostCollapseQ41ZeroMixedOrderTwoPlus610, zero_mul,
    mul_zero, zero_pow, Nat.ofNat_pos, add_zero, sub_zero]
  ring

end DegreeZeroOrderFiveHead610

end Max11DegreeRoutes
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option maxHeartbeats 800000000

section DegreeZeroOrderFiveHead610

variable {R : Type*} [CommRing R]

set_option maxHeartbeats 800000000 in
theorem degreeZeroPostCollapseQ41ZeroMixedOrderTwoPlus610_zero
    (w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda : R) :
    degreeZeroPostCollapseQ41ZeroMixedOrderTwoPlus610 0 w1 a42 p32 p21
        p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda =
      degreeZeroPostCollapseQ41ZeroMixedOrderThree610 w1 a42 p32 p21 p1
        p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda := by
  simp only [degreeZeroPostCollapseQ41ZeroMixedOrderTwoPlus610,
    degreeZeroPostCollapseQ41ZeroMixedOrderThree610, zero_mul, mul_zero,
    zero_pow, Nat.ofNat_pos, add_zero, sub_zero]
  ring

end DegreeZeroOrderFiveHead610

end Max11DegreeRoutes
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option maxHeartbeats 800000000

section DegreeZeroOrderFiveEval610

variable {k : Type*} [CommRing k]

theorem degreeZeroPostCollapseP32P21P1ZeroOrderFourPlus610_eval
    (h w1 a42 p32n p21n p1n p0 s2 u2 b63 q1 : k[X]) (lambda a : k) :
    (degreeZeroPostCollapseP32P21P1ZeroOrderFourPlus610 h w1 a42 p32n
        p21n p1n p0 s2 u2 b63 q1 (Polynomial.C lambda)).eval a =
      degreeZeroPostCollapseP32P21P1ZeroOrderFourPlus610 (h.eval a)
        (w1.eval a) (a42.eval a) (p32n.eval a) (p21n.eval a)
        (p1n.eval a) (p0.eval a) (s2.eval a) (u2.eval a) (b63.eval a)
        (q1.eval a) lambda := by
  simp only [degreeZeroPostCollapseP32P21P1ZeroOrderFourPlus610,
    Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_neg,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat,
    Polynomial.eval_C]

end DegreeZeroOrderFiveEval610

end Max11DegreeRoutes
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option maxHeartbeats 800000000

section DegreeZeroOrderFiveEval610

variable {k : Type*} [CommRing k]

theorem degreeZeroPostCollapseP32P21ZeroOrderFourPlus610_eval
    (h w1 a42 p32n p21n p1 p0 s2 u2 b63 q1 : k[X]) (lambda a : k) :
    (degreeZeroPostCollapseP32P21ZeroOrderFourPlus610 h w1 a42 p32n
        p21n p1 p0 s2 u2 b63 q1 (Polynomial.C lambda)).eval a =
      degreeZeroPostCollapseP32P21ZeroOrderFourPlus610 (h.eval a)
        (w1.eval a) (a42.eval a) (p32n.eval a) (p21n.eval a)
        (p1.eval a) (p0.eval a) (s2.eval a) (u2.eval a) (b63.eval a)
        (q1.eval a) lambda := by
  simp only [degreeZeroPostCollapseP32P21ZeroOrderFourPlus610,
    Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_neg,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat,
    Polynomial.eval_C]

end DegreeZeroOrderFiveEval610

end Max11DegreeRoutes
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option maxHeartbeats 800000000

section DegreeZeroOrderFiveEval610

variable {k : Type*} [CommRing k]

theorem degreeZeroPostCollapseP32Q41Q3ZeroOrderFourPlus610_eval
    (h w1 a42 p32n p21 p1 p0 s2 u2 b63 q1 : k[X]) (lambda a : k) :
    (degreeZeroPostCollapseP32Q41Q3ZeroOrderFourPlus610 h w1 a42 p32n
        p21 p1 p0 s2 u2 b63 q1 (Polynomial.C lambda)).eval a =
      degreeZeroPostCollapseP32Q41Q3ZeroOrderFourPlus610 (h.eval a)
        (w1.eval a) (a42.eval a) (p32n.eval a) (p21.eval a)
        (p1.eval a) (p0.eval a) (s2.eval a) (u2.eval a) (b63.eval a)
        (q1.eval a) lambda := by
  simp only [degreeZeroPostCollapseP32Q41Q3ZeroOrderFourPlus610,
    Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_neg,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat,
    Polynomial.eval_C]

end DegreeZeroOrderFiveEval610

end Max11DegreeRoutes
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option maxHeartbeats 800000000

section DegreeZeroOrderFiveEval610

variable {k : Type*} [CommRing k]

theorem degreeZeroPostCollapseQ41ZeroMixedOrderTwoPlus610_eval
    (h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 : k[X])
    (lambda a : k) :
    (degreeZeroPostCollapseQ41ZeroMixedOrderTwoPlus610 h w1 a42 p32 p21
        p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 (Polynomial.C lambda)).eval
      a =
      degreeZeroPostCollapseQ41ZeroMixedOrderTwoPlus610 (h.eval a)
        (w1.eval a) (a42.eval a) (p32.eval a) (p21.eval a) (p1.eval a)
        (p0.eval a) (s2.eval a) (u2.eval a) (b63.eval a) (q53.eval a)
        (q41n.eval a) (q3.eval a) (q2.eval a) (q1.eval a) lambda := by
  simp only [degreeZeroPostCollapseQ41ZeroMixedOrderTwoPlus610,
    Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_neg,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat,
    Polynomial.eval_C]

end DegreeZeroOrderFiveEval610

end Max11DegreeRoutes
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option maxHeartbeats 800000000

section DegreeZeroOrderFiveEval610

variable {k : Type*} [CommRing k]

theorem degreeZeroPostCollapseP32P21P1ZeroOrderFourPlus610_eval_root
    (h w1 a42 p32n p21n p1n p0 s2 u2 b63 q1 : k[X]) (lambda a : k)
    (hroot : h.eval a = 0) :
    (degreeZeroPostCollapseP32P21P1ZeroOrderFourPlus610 h w1 a42 p32n
        p21n p1n p0 s2 u2 b63 q1 (Polynomial.C lambda)).eval a =
      degreeZeroPostCollapseP32P21P1ZeroOrderFive610 (w1.eval a)
        (a42.eval a) (p32n.eval a) (p21n.eval a) (p1n.eval a)
        (p0.eval a) (u2.eval a) (b63.eval a) (q1.eval a) := by
  rw [degreeZeroPostCollapseP32P21P1ZeroOrderFourPlus610_eval, hroot,
    degreeZeroPostCollapseP32P21P1ZeroOrderFourPlus610_zero]

end DegreeZeroOrderFiveEval610

end Max11DegreeRoutes
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option maxHeartbeats 800000000

section DegreeZeroOrderFiveEval610

variable {k : Type*} [CommRing k]

theorem degreeZeroPostCollapseP32P21ZeroOrderFourPlus610_eval_root
    (h w1 a42 p32n p21n p1 p0 s2 u2 b63 q1 : k[X]) (lambda a : k)
    (hroot : h.eval a = 0) :
    (degreeZeroPostCollapseP32P21ZeroOrderFourPlus610 h w1 a42 p32n
        p21n p1 p0 s2 u2 b63 q1 (Polynomial.C lambda)).eval a =
      degreeZeroPostCollapseP32P21ZeroOrderFive610 (w1.eval a)
        (a42.eval a) (p32n.eval a) (p21n.eval a) (p1.eval a)
        (p0.eval a) (s2.eval a) (u2.eval a) (b63.eval a) (q1.eval a)
        lambda := by
  rw [degreeZeroPostCollapseP32P21ZeroOrderFourPlus610_eval, hroot,
    degreeZeroPostCollapseP32P21ZeroOrderFourPlus610_zero]

end DegreeZeroOrderFiveEval610

end Max11DegreeRoutes
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option maxHeartbeats 800000000

section DegreeZeroOrderFiveEval610

variable {k : Type*} [CommRing k]

theorem degreeZeroPostCollapseP32Q41Q3ZeroOrderFourPlus610_eval_root
    (h w1 a42 p32n p21 p1 p0 s2 u2 b63 q1 : k[X]) (lambda a : k)
    (hroot : h.eval a = 0) :
    (degreeZeroPostCollapseP32Q41Q3ZeroOrderFourPlus610 h w1 a42 p32n
        p21 p1 p0 s2 u2 b63 q1 (Polynomial.C lambda)).eval a =
      degreeZeroPostCollapseP32Q41Q3ZeroOrderFive610 (w1.eval a)
        (a42.eval a) (p32n.eval a) (p21.eval a) (p1.eval a)
        (p0.eval a) (s2.eval a) (u2.eval a) (b63.eval a) (q1.eval a)
        lambda := by
  rw [degreeZeroPostCollapseP32Q41Q3ZeroOrderFourPlus610_eval, hroot,
    degreeZeroPostCollapseP32Q41Q3ZeroOrderFourPlus610_zero]

end DegreeZeroOrderFiveEval610

end Max11DegreeRoutes
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option maxHeartbeats 800000000

section DegreeZeroOrderFiveEval610

variable {k : Type*} [CommRing k]

theorem degreeZeroPostCollapseQ41ZeroMixedOrderTwoPlus610_eval_root
    (h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 : k[X])
    (lambda a : k) (hroot : h.eval a = 0) :
    (degreeZeroPostCollapseQ41ZeroMixedOrderTwoPlus610 h w1 a42 p32 p21
        p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 (Polynomial.C lambda)).eval
      a =
      degreeZeroPostCollapseQ41ZeroMixedOrderThree610 (w1.eval a)
        (a42.eval a) (p32.eval a) (p21.eval a) (p1.eval a) (p0.eval a)
        (s2.eval a) (u2.eval a) (b63.eval a) (q53.eval a)
        (q41n.eval a) (q3.eval a) (q2.eval a) (q1.eval a) lambda := by
  rw [degreeZeroPostCollapseQ41ZeroMixedOrderTwoPlus610_eval, hroot,
    degreeZeroPostCollapseQ41ZeroMixedOrderTwoPlus610_zero]

end DegreeZeroOrderFiveEval610

end Max11DegreeRoutes
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option maxHeartbeats 800000000

section DegreeZeroOrderFiveSource610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 800000000 in
/-- On `p32(a) = p21(a) = p1(a) = 0` pole-one forces the next Taylor of
`o72n + OrderFour` plus the order-`74` mixin to vanish.
Cumulative vanishing: `h0^6` divides the jet quotient (`M = 6`; next
unused order `75`). -/
theorem degreeZeroPostCollapseP32P21P1ZeroOrderFiveHead610_zero_of_primitiveDeriv
    (h0 w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 : k[X])
    (lambda j a : k) (hh0 : h0 ≠ 0) (hdegree : h0.natDegree = 1)
    (hroot : h0.eval a = 0) (hp32 : p32.eval a = 0)
    (hp21 : p21.eval a = 0) (hp1 : p1.eval a = 0)
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
    ∃ p32n p21n p1n o72n o73n : k[X],
      p32 = h0 * p32n ∧ p21 = h0 * p21n ∧ p1 = h0 * p1n ∧
        degreeZeroPostCollapseP32P21P1ZeroOrderThreeHead610 w1 a42 p32n
            p21n p1n p0 q41 q3 =
          h0 * o72n ∧
        o72n +
            degreeZeroPostCollapseP32P21P1ZeroOrderFour610 w1 a42 p32n
              p21n p1n p0 q53 q2 =
          h0 * o73n ∧
        o73n.eval a +
            degreeZeroPostCollapseP32P21P1ZeroOrderFive610 (w1.eval a)
              (a42.eval a) (p32n.eval a) (p21n.eval a) (p1n.eval a)
              (p0.eval a) (u2.eval a) (b63.eval a) (q1.eval a) =
          0 ∧
        h0 ^ 6 ∣
          degreeZeroPostCollapseJetQuotient610 h0 w1 a42 p32 p21 p1 p0
            s2 u2 b63 q53 q41 q3 q2 q1 (Polynomial.C lambda) := by
  obtain ⟨p32n, p21n, p1n, o72n, hp32eq, hp21eq, hp1eq, ho72, hmix,
      _hdvd⟩ :=
    degreeZeroPostCollapseP32P21P1ZeroOrderFourHead610_zero_of_primitiveDeriv
      h0 w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda j a hh0
      hdegree hroot hp32 hp21 hp1 hderiv
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
          degreeZeroPostCollapseP32P21P1ZeroOrderFour610 w1 a42 p32n
            p21n p1n p0 q53 q2).eval a = 0 := by
    simp only [Polynomial.eval_add,
      degreeZeroPostCollapseP32P21P1ZeroOrderFour610_eval]
    exact hmix
  obtain ⟨o73n, ho73⟩ := linearPolynomial_dvd_of_eval_eq_zero_610 h0
    (o72n +
      degreeZeroPostCollapseP32P21P1ZeroOrderFour610 w1 a42 p32n p21n
        p1n p0 q53 q2) a hdegree hroot hSumEval
  let Q5 : k[X] :=
    o73n +
      degreeZeroPostCollapseP32P21P1ZeroOrderFourPlus610 h0 w1 a42 p32n
        p21n p1n p0 s2 u2 b63 q1 (Polynomial.C lambda)
  have hquot : quotient = h0 ^ 5 * Q5 := by
    have hplus :=
      degreeZeroPostCollapseP32P21P1ZeroOrderThreePlus610_of_fourPlus
        h0 w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1
        (Polynomial.C lambda)
    calc
      quotient =
          degreeZeroPostCollapseJetQuotient610 h0 w1 a42 (h0 * p32n)
            (h0 * p21n) (h0 * p1n) p0 s2 u2 b63 q53 q41 q3 q2 q1
            (Polynomial.C lambda) := by
        simp only [quotient, hp32eq, hp21eq, hp1eq]
      _ = h0 ^ 3 *
              degreeZeroPostCollapseP32P21P1ZeroOrderThreeHead610 w1
                a42 p32n p21n p1n p0 q41 q3 +
            h0 ^ 4 *
              degreeZeroPostCollapseP32P21P1ZeroOrderThreePlus610 h0 w1
                a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1
                (Polynomial.C lambda) :=
        degreeZeroPostCollapseJetQuotient610_p32P21P1Scale h0 w1 a42
          p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1
          (Polynomial.C lambda)
      _ = h0 ^ 4 *
            (o72n +
              degreeZeroPostCollapseP32P21P1ZeroOrderThreePlus610 h0
                w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1
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
          degreeZeroPostCollapseP32P21P1ZeroOrderFive610 (w1.eval a)
            (a42.eval a) (p32n.eval a) (p21n.eval a) (p1n.eval a)
            (p0.eval a) (u2.eval a) (b63.eval a) (q1.eval a) := by
    simp only [Q5, Polynomial.eval_add]
    rw [degreeZeroPostCollapseP32P21P1ZeroOrderFourPlus610_eval_root h0
      w1 a42 p32n p21n p1n p0 s2 u2 b63 q1 lambda a hroot]
  obtain ⟨Q6, hQ6⟩ := linearPolynomial_dvd_of_eval_eq_zero_610 h0 Q5 a
    hdegree hroot hQ5zero
  refine ⟨p32n, p21n, p1n, o72n, o73n, hp32eq, hp21eq, hp1eq, ho72,
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
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option maxHeartbeats 800000000

section DegreeZeroOrderFiveSource610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 800000000 in
/-- On `p32(a) = q41(a) = q3(a) = 0` pole-one forces the next Taylor of
`o72n + OrderFour` plus the order-`74` mixin to vanish.
Cumulative vanishing: `h0^6` divides the jet quotient (`M = 6`; next
unused order `75`). -/
theorem degreeZeroPostCollapseP32Q41Q3ZeroOrderFiveHead610_zero_of_primitiveDeriv
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
    ∃ p32n q41n q3n o71n o72n o73n : k[X],
      p32 = h0 * p32n ∧ q41 = h0 * q41n ∧ q3 = h0 * q3n ∧
        degreeZeroPostCollapseP32Q41Q3ZeroOrderTwoHead610 w1 a42 p21 p1
            q53 q41n q3n u2 =
          h0 * o71n ∧
        o71n +
            degreeZeroPostCollapseP32Q41Q3ZeroOrderThreeHead610 w1 a42
              p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2
              (Polynomial.C lambda) =
          h0 * o72n ∧
        o72n +
            degreeZeroPostCollapseP32Q41Q3ZeroOrderFour610 w1 a42 p32n
              p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1
              (Polynomial.C lambda) =
          h0 * o73n ∧
        o73n.eval a +
            degreeZeroPostCollapseP32Q41Q3ZeroOrderFive610 (w1.eval a)
              (a42.eval a) (p32n.eval a) (p21.eval a) (p1.eval a)
              (p0.eval a) (s2.eval a) (u2.eval a) (b63.eval a)
              (q1.eval a) lambda =
          0 ∧
        h0 ^ 6 ∣
          degreeZeroPostCollapseJetQuotient610 h0 w1 a42 p32 p21 p1 p0
            s2 u2 b63 q53 q41 q3 q2 q1 (Polynomial.C lambda) := by
  obtain ⟨p32n, q41n, q3n, o71n, o72n, hp32eq, hq41eq, hq3eq, ho71,
      ho72, hmix, _hdvd⟩ :=
    degreeZeroPostCollapseP32Q41Q3ZeroOrderFourHead610_zero_of_primitiveDeriv
      h0 w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda j a hh0
      hdegree hroot hp32 hq41 hq3 hderiv
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
          degreeZeroPostCollapseP32Q41Q3ZeroOrderFour610 w1 a42 p32n
            p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1
            (Polynomial.C lambda)).eval a = 0 := by
    simp only [Polynomial.eval_add,
      degreeZeroPostCollapseP32Q41Q3ZeroOrderFour610_eval]
    exact hmix
  obtain ⟨o73n, ho73⟩ := linearPolynomial_dvd_of_eval_eq_zero_610 h0
    (o72n +
      degreeZeroPostCollapseP32Q41Q3ZeroOrderFour610 w1 a42 p32n p21 p1
        p0 s2 u2 b63 q53 q41n q3n q2 q1 (Polynomial.C lambda)) a
    hdegree hroot hSumEval
  let Q5 : k[X] :=
    o73n +
      degreeZeroPostCollapseP32Q41Q3ZeroOrderFourPlus610 h0 w1 a42 p32n
        p21 p1 p0 s2 u2 b63 q1 (Polynomial.C lambda)
  have hquot : quotient = h0 ^ 5 * Q5 := by
    have hplus :=
      degreeZeroPostCollapseP32Q41Q3ZeroOrderThreePlus610_of_fourPlus
        h0 w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1
        (Polynomial.C lambda)
    calc
      quotient =
          degreeZeroPostCollapseJetQuotient610 h0 w1 a42 (h0 * p32n)
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
      _ = h0 ^ 3 *
              (o71n +
                degreeZeroPostCollapseP32Q41Q3ZeroOrderThreeHead610 w1
                  a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2
                  (Polynomial.C lambda)) +
            h0 ^ 4 *
              degreeZeroPostCollapseP32Q41Q3ZeroOrderThreePlus610 h0
                w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1
                (Polynomial.C lambda) := by
        rw [ho71]
        ring
      _ = h0 ^ 4 *
            (o72n +
              degreeZeroPostCollapseP32Q41Q3ZeroOrderThreePlus610 h0
                w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1
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
          degreeZeroPostCollapseP32Q41Q3ZeroOrderFive610 (w1.eval a)
            (a42.eval a) (p32n.eval a) (p21.eval a) (p1.eval a)
            (p0.eval a) (s2.eval a) (u2.eval a) (b63.eval a)
            (q1.eval a) lambda := by
    simp only [Q5, Polynomial.eval_add]
    rw [degreeZeroPostCollapseP32Q41Q3ZeroOrderFourPlus610_eval_root h0
      w1 a42 p32n p21 p1 p0 s2 u2 b63 q1 lambda a hroot]
  obtain ⟨Q6, hQ6⟩ := linearPolynomial_dvd_of_eval_eq_zero_610 h0 Q5 a
    hdegree hroot hQ5zero
  refine ⟨p32n, q41n, q3n, o71n, o72n, o73n, hp32eq, hq41eq, hq3eq,
    ho71, ho72, ho73, ?_, ?_⟩
  · rw [← hQ5eval]
    exact hQ5zero
  · refine ⟨Q6, ?_⟩
    calc
      quotient = h0 ^ 5 * Q5 := hquot
      _ = h0 ^ 5 * (h0 * Q6) := by rw [hQ6]
      _ = h0 ^ 6 * Q6 := by ring

end DegreeZeroOrderFiveSource610

end Max11DegreeRoutes
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
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option maxHeartbeats 800000000

section DegreeZeroOrderFiveSource610

variable {k : Type*} [Field k] [CharZero k]

theorem degreeZeroPostCollapseP32P21P1ZeroOrderFiveHead610_zero_of_source
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (w1 a42 p32 p21 s2 u2 b63 q53 q41 : k[X])
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hh0degree : h0.natDegree = 1) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0)
    (hw : p.coeff 5 = h0 ^ 5 * w1)
    (hp4deep : p.coeff 4 = h0 ^ 4 * a42)
    (hp3deep : p.coeff 3 = h0 ^ 2 * p32)
    (hp2deep : p.coeff 2 = h0 * p21)
    (hq8deep : q.coeff 8 = h0 ^ 8 * s2)
    (hq7deep : q.coeff 7 = h0 ^ 6 * u2)
    (hq6deep : q.coeff 6 = h0 ^ 5 * b63)
    (hq5deep : q.coeff 5 = h0 ^ 3 * q53)
    (hq4deep : q.coeff 4 = h0 * q41)
    (hp32 : p32.eval a = 0) (hp21 : p21.eval a = 0)
    (hp1 : (p.coeff 1).eval a = 0) :
    ∃ p32n p21n p1n o72n o73n : k[X],
      p32 = h0 * p32n ∧ p21 = h0 * p21n ∧ p.coeff 1 = h0 * p1n ∧
        degreeZeroPostCollapseP32P21P1ZeroOrderThreeHead610 w1 a42 p32n
            p21n p1n (p.coeff 0) q41 (q.coeff 3) =
          h0 * o72n ∧
        o72n +
            degreeZeroPostCollapseP32P21P1ZeroOrderFour610 w1 a42 p32n
              p21n p1n (p.coeff 0) q53 (q.coeff 2) =
          h0 * o73n ∧
        o73n.eval a +
            degreeZeroPostCollapseP32P21P1ZeroOrderFive610 (w1.eval a)
              (a42.eval a) (p32n.eval a) (p21n.eval a) (p1n.eval a)
              ((p.coeff 0).eval a) (u2.eval a) (b63.eval a)
              ((q.coeff 1).eval a) =
          0 := by
  obtain ⟨p32n, p21n, p1n, o72n, o73n, hp32eq, hp21eq, hp1eq, ho72,
      ho73, hmix, _hdvd⟩ :=
    degreeZeroPostCollapseP32P21P1ZeroOrderFiveHead610_zero_of_primitiveDeriv
      h0 w1 a42 p32 p21 (p.coeff 1) (p.coeff 0) s2 u2 b63 q53 q41
      (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda
      (58498535041007616 * j) a hh0 hh0degree hroot hp32 hp21 hp1
      (degreeZeroPostCollapsePrimitive610_deriv_eq_simplePole_of_source
        p q H h0 j lambda w1 a42 p32 p21 s2 u2 b63 q53 q41 hp hq hh0
        hH hp6 hq10 hN hD hw hp4deep hp3deep hp2deep hq8deep hq7deep
        hq6deep hq5deep hq4deep)
  exact ⟨p32n, p21n, p1n, o72n, o73n, hp32eq, hp21eq, hp1eq, ho72,
    ho73, hmix⟩

end DegreeZeroOrderFiveSource610

end Max11DegreeRoutes
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option maxHeartbeats 800000000

section DegreeZeroOrderFiveSource610

variable {k : Type*} [Field k] [CharZero k]

theorem degreeZeroPostCollapseQ41ZeroMixedOrderThree610_zero_of_source
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (w1 a42 p32 p21 s2 u2 b63 q53 q41 : k[X])
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hh0degree : h0.natDegree = 1) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0)
    (hw : p.coeff 5 = h0 ^ 5 * w1)
    (hp4deep : p.coeff 4 = h0 ^ 4 * a42)
    (hp3deep : p.coeff 3 = h0 ^ 2 * p32)
    (hp2deep : p.coeff 2 = h0 * p21)
    (hq8deep : q.coeff 8 = h0 ^ 8 * s2)
    (hq7deep : q.coeff 7 = h0 ^ 6 * u2)
    (hq6deep : q.coeff 6 = h0 ^ 5 * b63)
    (hq5deep : q.coeff 5 = h0 ^ 3 * q53)
    (hq4deep : q.coeff 4 = h0 * q41)
    (hq41 : q41.eval a = 0) :
    ∃ q41n q41nn o70n o71n : k[X],
      q41 = h0 * q41n ∧
        q41n = C (q41n.eval a) + h0 * q41nn ∧
        degreeZeroPostCollapseQ41ZeroMixedOrderOne610 w1 a42 p32 p21
            (p.coeff 1) q53 q41n (q.coeff 3) u2 =
          h0 * o70n ∧
        o70n +
            degreeZeroPostCollapseQ41ZeroMixedOrderTwo610 w1 a42 p32
              p21 (p.coeff 1) s2 u2 b63 q53 q41n (q.coeff 3)
              (q.coeff 2) (Polynomial.C lambda) =
          h0 * o71n ∧
        o71n.eval a +
            degreeZeroPostCollapseQ41ZeroMixedOrderThree610
              (w1.eval a) (a42.eval a) (p32.eval a) (p21.eval a)
              ((p.coeff 1).eval a) ((p.coeff 0).eval a) (s2.eval a)
              (u2.eval a) (b63.eval a) (q53.eval a) (q41n.eval a)
              ((q.coeff 3).eval a) ((q.coeff 2).eval a)
              ((q.coeff 1).eval a) lambda =
          0 := by
  obtain ⟨q41n, q41nn, o70n, o71n, hq41eq, hTaylor, ho70, ho71, hmix,
      _hdvd⟩ :=
    degreeZeroPostCollapseQ41ZeroMixedOrderThree610_zero_of_primitiveDeriv
      h0 w1 a42 p32 p21 (p.coeff 1) (p.coeff 0) s2 u2 b63 q53 q41
      (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda
      (58498535041007616 * j) a hh0 hh0degree hroot hq41
      (degreeZeroPostCollapsePrimitive610_deriv_eq_simplePole_of_source
        p q H h0 j lambda w1 a42 p32 p21 s2 u2 b63 q53 q41 hp hq hh0
        hH hp6 hq10 hN hD hw hp4deep hp3deep hp2deep hq8deep hq7deep
        hq6deep hq5deep hq4deep)
  exact ⟨q41n, q41nn, o70n, o71n, hq41eq, hTaylor, ho70, ho71, hmix⟩

end DegreeZeroOrderFiveSource610

end Max11DegreeRoutes
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option maxHeartbeats 800000000

section DegreeZeroOrder74Grandchildren610

variable {k : Type*} [Field k] [CharZero k]

/-- Source-facing joint order-`74` packet.  This is not a closure:
each surviving arm retains a residual.  Cumulative vanishing is
`M = 6` (next unused order `75`) on `(a)(b)(c)` and `M = 4` (next
unused mixed order `73`) on `(d)`.  On arm `(c)`, `p1` is not forced
by the `p21 = q53 = 0` thirteen-term cofactor. -/
theorem degreeZeroFace610_linearRoot_order74Grandchildren
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hh0degree : h0.natDegree = 1) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0) (hlambda : lambda ≠ 0) :
    ∃ (w1 a42 p32 p21 s2 u2 b63 q53 q41 : k[X]),
      p.coeff 5 = h0 ^ 5 * w1 ∧
      p.coeff 4 = h0 ^ 4 * a42 ∧
      p.coeff 3 = h0 ^ 2 * p32 ∧
      p.coeff 2 = h0 * p21 ∧
      q.coeff 8 = h0 ^ 8 * s2 ∧
      q.coeff 7 = h0 ^ 6 * u2 ∧
      q.coeff 6 = h0 ^ 5 * b63 ∧
      q.coeff 5 = h0 ^ 3 * q53 ∧
      q.coeff 4 = h0 * q41 ∧
      ((p32.eval a = 0 ∧ p21.eval a = 0 ∧
          ∃ p32n p21n : k[X],
            p32 = h0 * p32n ∧ p21 = h0 * p21n ∧
              (((p.coeff 1).eval a = 0 ∧
                  ∃ p1n o72n o73n : k[X],
                    p.coeff 1 = h0 * p1n ∧
                      degreeZeroPostCollapseP32P21P1ZeroOrderThreeHead610
                            w1 a42 p32n p21n p1n (p.coeff 0) q41
                            (q.coeff 3) =
                          h0 * o72n ∧
                        o72n +
                            degreeZeroPostCollapseP32P21P1ZeroOrderFour610
                              w1 a42 p32n p21n p1n (p.coeff 0) q53
                              (q.coeff 2) =
                          h0 * o73n ∧
                        o73n.eval a +
                            degreeZeroPostCollapseP32P21P1ZeroOrderFive610
                              (w1.eval a) (a42.eval a) (p32n.eval a)
                              (p21n.eval a) (p1n.eval a)
                              ((p.coeff 0).eval a) (u2.eval a)
                              (b63.eval a) ((q.coeff 1).eval a) =
                          0) ∨
                (degreeZeroPostCollapseP32P21ZeroOrderTwoHeadCofactor610
                      (w1.eval a) (a42.eval a) (p32n.eval a)
                      (p21n.eval a) ((p.coeff 1).eval a) (q53.eval a)
                      (q41.eval a) ((q.coeff 3).eval a) = 0 ∧
                    ∃ o71n o72n o73n : k[X],
                      degreeZeroPostCollapseP32P21ZeroOrderTwoHead610
                            w1 a42 p32n p21n (p.coeff 1) q53 q41
                            (q.coeff 3) =
                          h0 * o71n ∧
                        o71n +
                            degreeZeroPostCollapseP32P21ZeroOrderThreeHead610
                              w1 a42 p32n p21n (p.coeff 1) (p.coeff 0)
                              u2 b63 q53 q41 (q.coeff 3) (q.coeff 2) =
                          h0 * o72n ∧
                        o72n +
                            degreeZeroPostCollapseP32P21ZeroOrderFour610
                              w1 a42 p32n p21n (p.coeff 1) (p.coeff 0)
                              s2 u2 b63 q53 (q.coeff 2) (q.coeff 1)
                              (Polynomial.C lambda) =
                          h0 * o73n ∧
                        o73n.eval a +
                            degreeZeroPostCollapseP32P21ZeroOrderFive610
                              (w1.eval a) (a42.eval a) (p32n.eval a)
                              (p21n.eval a) ((p.coeff 1).eval a)
                              ((p.coeff 0).eval a) (s2.eval a)
                              (u2.eval a) (b63.eval a)
                              ((q.coeff 1).eval a) lambda =
                          0))) ∨
        (p32.eval a = 0 ∧ q41.eval a = 0 ∧ (q.coeff 3).eval a = 0 ∧
          ∃ p32n q41n q3n o71n o72n o73n : k[X],
            p32 = h0 * p32n ∧ q41 = h0 * q41n ∧
              q.coeff 3 = h0 * q3n ∧
              degreeZeroPostCollapseP32Q41Q3ZeroOrderTwoHead610 w1 a42
                  p21 (p.coeff 1) q53 q41n q3n u2 =
                h0 * o71n ∧
              o71n +
                  degreeZeroPostCollapseP32Q41Q3ZeroOrderThreeHead610
                    w1 a42 p32n p21 (p.coeff 1) (p.coeff 0) s2 u2 b63
                    q53 q41n q3n (q.coeff 2) (Polynomial.C lambda) =
                h0 * o72n ∧
              o72n +
                  degreeZeroPostCollapseP32Q41Q3ZeroOrderFour610 w1
                    a42 p32n p21 (p.coeff 1) (p.coeff 0) s2 u2 b63
                    q53 q41n q3n (q.coeff 2) (q.coeff 1)
                    (Polynomial.C lambda) =
                h0 * o73n ∧
              o73n.eval a +
                  degreeZeroPostCollapseP32Q41Q3ZeroOrderFive610
                    (w1.eval a) (a42.eval a) (p32n.eval a)
                    (p21.eval a) ((p.coeff 1).eval a)
                    ((p.coeff 0).eval a) (s2.eval a) (u2.eval a)
                    (b63.eval a) ((q.coeff 1).eval a) lambda =
                0 ∧
              (p21.eval a = 0 →
                (p.coeff 1).eval a = 0 ∨ q53.eval a = 0)) ∨
        (q41.eval a = 0 ∧
          10 * (p32.eval a) ^ 2 * (q53.eval a) +
              (18 * (p32.eval a) * (w1.eval a) -
                27 * (p21.eval a)) * (q.coeff 3).eval a = 0 ∧
          ∃ q41n q41nn o70n o71n : k[X],
            q41 = h0 * q41n ∧
              q41n = C (q41n.eval a) + h0 * q41nn ∧
              degreeZeroPostCollapseQ41ZeroMixedOrderOne610 w1 a42 p32
                  p21 (p.coeff 1) q53 q41n (q.coeff 3) u2 =
                h0 * o70n ∧
              o70n +
                  degreeZeroPostCollapseQ41ZeroMixedOrderTwo610 w1
                    a42 p32 p21 (p.coeff 1) s2 u2 b63 q53 q41n
                    (q.coeff 3) (q.coeff 2) (Polynomial.C lambda) =
                h0 * o71n ∧
              o71n.eval a +
                  degreeZeroPostCollapseQ41ZeroMixedOrderThree610
                    (w1.eval a) (a42.eval a) (p32.eval a)
                    (p21.eval a) ((p.coeff 1).eval a)
                    ((p.coeff 0).eval a) (s2.eval a) (u2.eval a)
                    (b63.eval a) (q53.eval a) (q41n.eval a)
                    ((q.coeff 3).eval a) ((q.coeff 2).eval a)
                    ((q.coeff 1).eval a) lambda =
                0 ∧
              (p32.eval a = 0 ∨
                degreeZeroPostCollapseQ41ZeroMixedFiveReduced610
                    (w1.eval a) (a42.eval a) (p32.eval a)
                    (p21.eval a) ((p.coeff 1).eval a) (q41n.eval a)
                    ((q.coeff 3).eval a) (u2.eval a) = 0))) := by
  obtain ⟨w1, a42, p32, p21, s2, u2, b63, q53, q41, hw, hp4deep,
      hp3deep, hp2deep, hq8deep, hq7deep, hq6deep, hq5deep, hq4deep,
      hpacket⟩ :=
    degreeZeroFace610_linearRoot_order73Grandchildren p q H h0 j lambda
      a hp hq hh0 hh0degree hH hp6 hq10 hN hD hroot hlambda
  refine ⟨w1, a42, p32, p21, s2, u2, b63, q53, q41, hw, hp4deep,
    hp3deep, hp2deep, hq8deep, hq7deep, hq6deep, hq5deep, hq4deep, ?_⟩
  rcases hpacket with hAB | hC | hD
  · obtain ⟨hp32, hp21, p32n, p21n, hp32eq, hp21eq, hsplit⟩ := hAB
    refine Or.inl ⟨hp32, hp21, p32n, p21n, hp32eq, hp21eq, ?_⟩
    rcases hsplit with hp1pack | hcof
    · obtain ⟨hp1, p1n, o72n, hp1eq, _ho72, _hmix73⟩ := hp1pack
      obtain ⟨p32n', p21n', p1n', o72n', o73n, hp32eq', hp21eq',
          hp1eq', ho72, ho73, hmix⟩ :=
        degreeZeroPostCollapseP32P21P1ZeroOrderFiveHead610_zero_of_source
          p q H h0 j lambda a w1 a42 p32 p21 s2 u2 b63 q53 q41 hp hq
          hh0 hh0degree hH hp6 hq10 hN hD hroot hw hp4deep hp3deep
          hp2deep hq8deep hq7deep hq6deep hq5deep hq4deep hp32 hp21 hp1
      have hp32n : p32n' = p32n := by
        apply mul_left_cancel₀ hh0
        rw [← hp32eq', ← hp32eq]
      have hp21n : p21n' = p21n := by
        apply mul_left_cancel₀ hh0
        rw [← hp21eq', ← hp21eq]
      have hp1n : p1n' = p1n := by
        apply mul_left_cancel₀ hh0
        rw [← hp1eq', ← hp1eq]
      refine Or.inl ⟨hp1, p1n, o72n', o73n, hp1eq, ?_, ?_, ?_⟩
      · simpa [hp32n, hp21n, hp1n] using ho72
      · simpa [hp32n, hp21n, hp1n] using ho73
      · simpa [hp32n, hp21n, hp1n] using hmix
    · obtain ⟨hcof0, o71n, o72n, _ho71, _ho72, _hmix73⟩ := hcof
      obtain ⟨p32n', p21n', o71n', o72n', o73n, hp32eq', hp21eq',
          ho71', ho72, ho73, hmix, _hdvd⟩ :=
        degreeZeroPostCollapseP32P21ZeroOrderFiveHead610_zero_of_primitiveDeriv
          h0 w1 a42 p32 p21 (p.coeff 1) (p.coeff 0) s2 u2 b63 q53 q41
          (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda
          (58498535041007616 * j) a hh0 hh0degree hroot hp32 hp21
          (degreeZeroPostCollapsePrimitive610_deriv_eq_simplePole_of_source
            p q H h0 j lambda w1 a42 p32 p21 s2 u2 b63 q53 q41 hp hq
            hh0 hH hp6 hq10 hN hD hw hp4deep hp3deep hp2deep hq8deep
            hq7deep hq6deep hq5deep hq4deep)
      have hp32n : p32n' = p32n := by
        apply mul_left_cancel₀ hh0
        rw [← hp32eq', ← hp32eq]
      have hp21n : p21n' = p21n := by
        apply mul_left_cancel₀ hh0
        rw [← hp21eq', ← hp21eq]
      refine Or.inr ⟨hcof0, o71n', o72n', o73n, ?_, ?_, ?_, ?_⟩
      · simpa [hp32n, hp21n] using ho71'
      · simpa [hp32n, hp21n] using ho72
      · simpa [hp32n, hp21n] using ho73
      · simpa [hp32n, hp21n] using hmix
  · obtain ⟨hp32, hq41, hq3, p32n, q41n, q3n, o71n, o72n, hp32eq,
        hq41eq, hq3eq, _ho71, _ho72, _hmix73, hp21split⟩ := hC
    obtain ⟨p32n', q41n', q3n', o71n', o72n', o73n, hp32eq', hq41eq',
        hq3eq', ho71', ho72, ho73, hmix, _hdvd⟩ :=
      degreeZeroPostCollapseP32Q41Q3ZeroOrderFiveHead610_zero_of_primitiveDeriv
        h0 w1 a42 p32 p21 (p.coeff 1) (p.coeff 0) s2 u2 b63 q53 q41
        (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda
        (58498535041007616 * j) a hh0 hh0degree hroot hp32 hq41 hq3
        (degreeZeroPostCollapsePrimitive610_deriv_eq_simplePole_of_source
          p q H h0 j lambda w1 a42 p32 p21 s2 u2 b63 q53 q41 hp hq hh0
          hH hp6 hq10 hN hD hw hp4deep hp3deep hp2deep hq8deep hq7deep
          hq6deep hq5deep hq4deep)
    have hp32n : p32n' = p32n := by
      apply mul_left_cancel₀ hh0
      rw [← hp32eq', ← hp32eq]
    have hq41n : q41n' = q41n := by
      apply mul_left_cancel₀ hh0
      rw [← hq41eq', ← hq41eq]
    have hq3n : q3n' = q3n := by
      apply mul_left_cancel₀ hh0
      rw [← hq3eq', ← hq3eq]
    refine Or.inr (Or.inl ⟨hp32, hq41, hq3, p32n, q41n, q3n, o71n',
      o72n', o73n, hp32eq, hq41eq, hq3eq, ?_, ?_, ?_, ?_,
      hp21split⟩)
    · simpa [hp32n, hq41n, hq3n] using ho71'
    · simpa [hp32n, hq41n, hq3n] using ho72
    · simpa [hp32n, hq41n, hq3n] using ho73
    · simpa [hp32n, hq41n, hq3n] using hmix
  · obtain ⟨hq41, hfive, q41n, q41nn, o70n, hq41eq, hTaylor, ho70,
        _hmix73, hred⟩ := hD
    obtain ⟨q41n', q41nn', o70n', o71n, hq41eq', hTaylor', ho70',
        ho71, hmix⟩ :=
      degreeZeroPostCollapseQ41ZeroMixedOrderThree610_zero_of_source p
        q H h0 j lambda a w1 a42 p32 p21 s2 u2 b63 q53 q41 hp hq hh0
        hh0degree hH hp6 hq10 hN hD hroot hw hp4deep hp3deep hp2deep
        hq8deep hq7deep hq6deep hq5deep hq4deep hq41
    have hq41n : q41n' = q41n := by
      apply mul_left_cancel₀ hh0
      rw [← hq41eq', ← hq41eq]
    refine Or.inr (Or.inr ⟨hq41, hfive, q41n, q41nn', o70n', o71n,
      hq41eq, ?_, ?_, ?_, ?_, hred⟩)
    · simpa [hq41n] using hTaylor'
    · simpa [hq41n] using ho70'
    · simpa [hq41n] using ho71
    · simpa [hq41n] using hmix

end DegreeZeroOrder74Grandchildren610

end Max11DegreeRoutes
