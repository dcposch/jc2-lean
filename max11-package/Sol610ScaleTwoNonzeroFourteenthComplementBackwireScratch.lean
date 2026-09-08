import Fable610ScaleTwoKappaIntegralBridgeCompatFollowingScratch
import Sol610ScaleTwoNonzeroFourteenthComplementCollapseScratch

/-! # Backwire of the `(6,10)` fourth-tail complement collapse

The degree-two `mu` packet previously retained a pinned `q41` child with a
new `q3` tie.  The merged fourteenth-jet head closes that child instead.
Consequently every surviving branch has four additional root vanishings,
which are lifted here to uniform one-step source divisibilities.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section NonzeroFourteenthComplementBackwire610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 800000000 in
/-- On the nonzero square-core `(6,10)` face, the merged fourth-tail
certificate removes the pinned `q41`/`q3`-tie child from the degree-two
integral packet.  All remaining children therefore deepen `p4`, `p2`,
`q8`, and `q6` by one power of the supplied linear factor. -/
theorem nonzeroFace610_linearRoot_fourteenthComplementBackwire
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
      q.coeff 4 = h0 * q41 := by
  obtain ⟨w1, a41, s1, u1, p31, b62, q52, p32, u2, q53, q41,
      iotaK, kappaMu, lambdaNu, muXi, hw, ha4s, hp3, hs, hu, hb6s,
      hq5, hMs, hUload, hrow, hroweval, hipow, hipeel, hiheadeval,
      hkpow, hkpeel, hkheadeval, hlpow, hlpeel, hlheadeval, hp31z,
      hu1z, hq52z, hq4z, hp3deep, hq7deep, hq5deep, hq4deep,
      hldeepPeel, hldeepHeadEval, hG, hmupow, hmupeel, hmuheadeval,
      hmuR22, halt⟩ :=
    nonzeroFace610_linearRoot_muIntegralBridge p q H h0 j lambda a hp hq
      hh0 hh0degree hH hp6 hq10 hN hD hroot hlambda
  have hs1zero_of_a41zero : a41.eval a = 0 → s1.eval a = 0 := by
    intro ha41z
    have hthree : (3 : k) * s1.eval a = 0 := by
      simpa only [ha41z, mul_zero] using hMs
    exact (mul_eq_zero.mp hthree).resolve_left (by norm_num)
  have hzeros :
      a41.eval a = 0 ∧ (p.coeff 2).eval a = 0 ∧
        s1.eval a = 0 ∧ b62.eval a = 0 := by
    rcases halt with hleft | hcomplement
    · rcases hleft with
        ⟨a42, p21, s2, b63, q54, q42, q31, hileft, ha41z, hp2z,
          hs1z, hb62z, hq41z, hq53z, hq3z, hu2tie, hp4deep,
          hp2deep, hq8deep, hq6deep, hq5deep2, hq4deep2, hq3deep,
          hmuDeepPeel, hmuDeepHeadEval, hsplit⟩
      exact ⟨ha41z, hp2z, hs1z, hb62z⟩
    · rcases hcomplement with ⟨hp2pin, hb62pin, hcases⟩
      rcases hcases with hzero | hcases
      · rcases hzero with ⟨ha41z, hp2z, hb62z⟩
        exact ⟨ha41z, hp2z, hs1zero_of_a41zero ha41z, hb62z⟩
      · rcases hcases with hzero | hpinned
        · rcases hzero with ⟨ha41z, hp2z, hb62z, hq41z⟩
          exact ⟨ha41z, hp2z, hs1zero_of_a41zero ha41z, hb62z⟩
        · rcases hpinned with ⟨hq41pin, hq3tie⟩
          have hp2eq :
              (6 : k) * (p.coeff 2).eval a = (a41.eval a) ^ 2 := by
            linear_combination hp2pin
          have hb62eq :
              (6 : k) * b62.eval a = (5 : k) * (a41.eval a) ^ 2 := by
            linear_combination hb62pin
          obtain ⟨ha41z, hs1z, hp2z, hb62z, hq41z⟩ :=
            nonzeroFace610_fourteenthComplementCollapse p q H h0 j lambda a
              hp hq hh0 hH hp6 hq10 hN hD hroot w1 a41 p32 s1 u2 b62
              q53 q41 hw ha4s hp3deep hs hq7deep hb6s hq5deep hq4deep
              hMs hp2eq hb62eq hq41pin
          exact ⟨ha41z, hp2z, hs1z, hb62z⟩
  obtain ⟨ha41z, hp2z, hs1z, hb62z⟩ := hzeros
  obtain ⟨a42, ha42⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 a41 a hh0degree hroot
      ha41z
  obtain ⟨p21, hp21⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 (p.coeff 2) a hh0degree
      hroot hp2z
  obtain ⟨s2, hs2⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 s1 a hh0degree hroot hs1z
  obtain ⟨b63, hb63⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 b62 a hh0degree hroot
      hb62z
  have hp4deep : p.coeff 4 = h0 ^ 4 * a42 := by
    rw [ha4s, ha42]
    ring
  have hq8deep : q.coeff 8 = h0 ^ 8 * s2 := by
    rw [hs, hs2]
    ring
  have hq6deep : q.coeff 6 = h0 ^ 5 * b63 := by
    rw [hb6s, hb63]
    ring
  exact ⟨w1, a42, p32, p21, s2, u2, b63, q53, q41, hw, hp4deep,
    hp3deep, hp21, hq8deep, hq7deep, hq6deep, hq5deep, hq4deep⟩

#print axioms nonzeroFace610_linearRoot_fourteenthComplementBackwire

end NonzeroFourteenthComplementBackwire610

end Max11DegreeRoutes
