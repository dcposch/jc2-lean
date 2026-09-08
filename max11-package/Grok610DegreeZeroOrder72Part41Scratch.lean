import Grok610DegreeZeroOrder72Part36Scratch

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

section DegreeZeroOrder72Grandchildren610

variable {k : Type*} [Field k] [CharZero k]

/-- Source-facing `p32(a) = p21(a) = p1(a) = 0` arm: the combined
order-`72` head vanishes on the next peels. -/
theorem degreeZeroFace610_linearRoot_p32P21P1ZeroOrder72
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
      (p32.eval a = 0 ∧ p21.eval a = 0 ∧ (p.coeff 1).eval a = 0 →
        ∃ p32n p21n p1n : k[X],
          p32 = h0 * p32n ∧ p21 = h0 * p21n ∧ p.coeff 1 = h0 * p1n ∧
            degreeZeroPostCollapseP32P21P1ZeroOrderThreeHead610
                (w1.eval a) (a42.eval a) (p32n.eval a) (p21n.eval a)
                (p1n.eval a) ((p.coeff 0).eval a) (q41.eval a)
                ((q.coeff 3).eval a) = 0) := by
  obtain ⟨w1, a42, p32, p21, s2, u2, b63, q53, q41, _nu, hw, hp4deep,
      hp3deep, hp2deep, hq8deep, hq7deep, hq6deep, hq5deep, hq4deep,
      _hpost, _hfourteenth⟩ :=
    nonzeroFace610_linearRoot_postCollapseResidual p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp6 hq10 hN hD hroot hlambda
  refine ⟨w1, a42, p32, p21, s2, u2, b63, q53, q41, hw, hp4deep,
    hp3deep, hp2deep, hq8deep, hq7deep, hq6deep, hq5deep, hq4deep, ?_⟩
  intro ⟨hp32, hp21, hp1⟩
  exact degreeZeroPostCollapseP32P21P1ZeroOrderThreeHead610_zero_of_source
    p q H h0 j lambda a w1 a42 p32 p21 s2 u2 b63 q53 q41 hp hq hh0
    hh0degree hH hp6 hq10 hN hD hroot hw hp4deep hp3deep hp2deep
    hq8deep hq7deep hq6deep hq5deep hq4deep hp32 hp21 hp1

end DegreeZeroOrder72Grandchildren610

end Max11DegreeRoutes
