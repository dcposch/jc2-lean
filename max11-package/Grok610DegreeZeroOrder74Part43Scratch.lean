import Grok610DegreeZeroOrder74Part39Scratch

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
