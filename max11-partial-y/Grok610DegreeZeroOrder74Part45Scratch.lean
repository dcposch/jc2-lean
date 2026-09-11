import Grok610DegreeZeroOrder74Part44Scratch
import Grok610DegreeZeroOrder74Part43Scratch
import Grok610DegreeZeroOrder74Part41Scratch
import Grok610DegreeZeroOrder74Part40Scratch

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
