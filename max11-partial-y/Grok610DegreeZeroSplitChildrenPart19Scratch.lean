import Grok610DegreeZeroSplitChildrenPart14Scratch
import Grok610DegreeZeroSplitChildrenPart16Scratch

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option maxHeartbeats 800000000

section DegreeZeroSplitChildren610

variable {k : Type*} [Field k] [CharZero k]

/-- Source-facing joint grandchild packet.  This is not a closure:
each surviving arm retains a residual. -/
theorem degreeZeroFace610_linearRoot_splitChildren
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
      ((p32.eval a = 0 ∧
          (p21.eval a = 0 ∨
            (q41.eval a = 0 ∧ (q.coeff 3).eval a = 0))) ∨
        (q41.eval a = 0 ∧
          10 * (p32.eval a) ^ 2 * (q53.eval a) +
              (18 * (p32.eval a) * (w1.eval a) -
                27 * (p21.eval a)) * (q.coeff 3).eval a = 0)) := by
  obtain ⟨w1, a42, p32, p21, s2, u2, b63, q53, q41, _nu, hw, hp4deep,
      hp3deep, hp2deep, hq8deep, hq7deep, hq6deep, hq5deep, hq4deep,
      _hpost, hfourteenth⟩ :=
    nonzeroFace610_linearRoot_postCollapseResidual p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp6 hq10 hN hD hroot hlambda
  have hdegree := degreeZeroPostCollapseJetHead610_zero_of_source p q H
    h0 j lambda a w1 a42 p32 p21 s2 u2 b63 q53 q41 hp hq hh0 hh0degree
    hH hp6 hq10 hN hD hroot hw hp4deep hp3deep hp2deep hq8deep hq7deep
    hq6deep hq5deep hq4deep
  refine ⟨w1, a42, p32, p21, s2, u2, b63, q53, q41, hw, hp4deep,
    hp3deep, hp2deep, hq8deep, hq7deep, hq6deep, hq5deep, hq4deep, ?_⟩
  have horder_of_p32 (hp32 : p32.eval a = 0) :
      degreeZeroPostCollapseP32ZeroOrderOne610 (w1.eval a) (p21.eval a)
        ((p.coeff 1).eval a) (q41.eval a) ((q.coeff 3).eval a) = 0 :=
    degreeZeroPostCollapseP32ZeroOrderOne610_zero_of_source p q H h0 j
      lambda a w1 a42 p32 p21 s2 u2 b63 q53 q41 hp hq hh0 hh0degree hH
      hp6 hq10 hN hD hroot hw hp4deep hp3deep hp2deep hq8deep hq7deep
      hq6deep hq5deep hq4deep hp32
  rcases degreeZeroPostCollapseJetHead610_split (p32.eval a)
      (q41.eval a) hdegree with hp32 | hq41
  · exact Or.inl ⟨hp32,
      degreeZeroPostCollapseP32Zero_grandchildren610 (w1.eval a)
        (a42.eval a) (p32.eval a) (q53.eval a) (p21.eval a)
        ((p.coeff 1).eval a) (q41.eval a) ((q.coeff 3).eval a) hp32
        hfourteenth (horder_of_p32 hp32)⟩
  · have hchild :=
      degreeZeroPostCollapseQ41Zero_grandchildren610 (w1.eval a)
        (a42.eval a) (p32.eval a) (q53.eval a) (p21.eval a)
        ((p.coeff 1).eval a) (q41.eval a) ((q.coeff 3).eval a) hq41
        hfourteenth horder_of_p32
    rcases hchild with ⟨hp32, hrest⟩ | hcof
    · refine Or.inl ⟨hp32, ?_⟩
      rcases hrest with hp21 | hq3
      · exact Or.inl hp21
      · exact Or.inr ⟨hq41, hq3⟩
    · exact Or.inr ⟨hq41, hcof⟩

end DegreeZeroSplitChildren610

end Max11DegreeRoutes
