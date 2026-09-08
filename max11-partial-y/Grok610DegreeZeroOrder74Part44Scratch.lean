import Grok610DegreeZeroOrder74Part42Scratch

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
