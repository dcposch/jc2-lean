import Fable610ScaleTwoKappaIntegralBridgeCompatPart18Scratch
import Fable610ScaleTwoKappaIntegralBridgeCompatPart17Scratch
import Fable610ScaleTwoKappaIntegralBridgeCompatPart16Scratch
import Fable610ScaleTwoKappaIntegralBridgeCompatPart15Scratch
import Fable610ScaleTwoKappaIntegralBridgeCompatPart12Scratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section NonzeroKappaIntegralBridge610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 40000000 in
/-- Finite local `κ` integral bridge: the terminal integral closure
packet (the `ι` packet reused opaquely) together with the imported
weight-`55` clearing of the degree-`4` first integral `κ`, its
`h₀⁴⁸`-peeled factored head, the chamber-free root split
`a₄₁(a) p₃₁(a)³ = 0`, and the four-children combination — the three
`p₃₁(a) = 0` children are retained unchanged (the head carries an
overall `p₃₁` factor there), while the `p₃₁(a) ≠ 0` child is refined
to `a₄₁(a) = 0`, `w₁(a) = 0` and the pins `80 p₂(a) = 9 λ p₃₁(a)`,
`16 b₆₂(a) = -5 λ p₃₁(a)`, with `ψ₂(a) = -209952 λ p₁(a)` collapsing
the retained boundary elimination into the Keller row.  No child is
closed. -/
theorem nonzeroFace610_linearRoot_kappaIntegralBridge
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
    ∃ (w1 a41 s1 u1 p31 b62 q52 : k[X]) (iotaK kappaMu : k),
      p.coeff 5 = h0 ^ 5 * w1 ∧ p.coeff 4 = h0 ^ 3 * a41 ∧
        p.coeff 3 = h0 * p31 ∧ q.coeff 8 = h0 ^ 7 * s1 ∧
        q.coeff 7 = h0 ^ 5 * u1 ∧ q.coeff 6 = h0 ^ 4 * b62 ∧
        q.coeff 5 = h0 ^ 2 * q52 ∧
        (3 : k) * s1.eval a = (5 : k) * a41.eval a ∧
        (3 : k) * u1.eval a = (5 : k) * p31.eval a ∧
        (9 : k) * q52.eval a =
          (10 : k) * a41.eval a * p31.eval a ∧
        (9 : k) * (q.coeff 4).eval a = (5 : k) * (p31.eval a) ^ 2 ∧
        (10 : k) * (a41.eval a) ^ 2 - (18 : k) * b62.eval a -
            (9 : k) * lambda * p31.eval a +
          (30 : k) * (p.coeff 2).eval a +
            (20 : k) * p31.eval a * w1.eval a = 0 ∧
        (p.coeff 0).derivative * q.coeff 1 -
          p.coeff 1 * (q.coeff 0).derivative = Polynomial.C j ∧
        ((p.coeff 0).derivative).eval a * (q.coeff 1).eval a -
          (p.coeff 1).eval a * ((q.coeff 0).derivative).eval a = j ∧
        terminalClearedIotaDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
            (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
            (q.coeff 0) lambda =
          Polynomial.C iotaK * h0 ^ 50 ∧
        bridgeIotaJetHead610 w1 a41 p31 s1 u1 b62 q52 (p.coeff 2)
              (q.coeff 4) (Polynomial.C lambda) +
            h0 * bridgeIotaJetTail610 h0 w1 a41 p31 s1 u1 b62 q52
              (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 4)
              (q.coeff 3) (q.coeff 2) (q.coeff 1) (q.coeff 0)
              (Polynomial.C lambda) =
          Polynomial.C iotaK * h0 ^ 6 ∧
        bridgeIotaJetHead610 (w1.eval a) (a41.eval a) (p31.eval a)
            (s1.eval a) (u1.eval a) (b62.eval a) (q52.eval a)
            ((p.coeff 2).eval a) ((q.coeff 4).eval a) lambda = 0 ∧
        (p31.eval a) ^ 2 * ((27 : k) * b62.eval a -
            (30 : k) * (a41.eval a) ^ 2 - (5 : k) * (p.coeff 2).eval a +
            (9 : k) * lambda * p31.eval a -
            (40 : k) * p31.eval a * w1.eval a) = 0 ∧
        (p31.eval a) ^ 2 * ((144 : k) * b62.eval a -
            (170 : k) * (a41.eval a) ^ 2 +
            (45 : k) * lambda * p31.eval a -
            (220 : k) * p31.eval a * w1.eval a) = 0 ∧
        bridgeClearedKappaDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
            (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda =
          Polynomial.C kappaMu * h0 ^ 55 ∧
        bridgeKappaJetHead610 a41 p31 s1 u1 q52 (q.coeff 4) +
            h0 * bridgeKappaJetTail610 h0 w1 a41 p31 s1 u1 b62 q52
              (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 4)
              (q.coeff 3) (q.coeff 2) (q.coeff 1)
              (Polynomial.C lambda) =
          Polynomial.C kappaMu * h0 ^ 7 ∧
        bridgeKappaJetHead610 (a41.eval a) (p31.eval a) (s1.eval a)
            (u1.eval a) (q52.eval a) ((q.coeff 4).eval a) = 0 ∧
        a41.eval a * (p31.eval a) ^ 3 = 0 ∧
        (a41.eval a = 0 ∨ p31.eval a = 0) ∧
        ((p31.eval a = 0 ∧
            ∃ (p32 u2 q53 q41 : k[X]),
              p.coeff 3 = h0 ^ 2 * p32 ∧
                q.coeff 7 = h0 ^ 6 * u2 ∧
                q.coeff 5 = h0 ^ 3 * q53 ∧
                q.coeff 4 = h0 * q41 ∧
                (18 : k) * u2.eval a - (30 : k) * p32.eval a -
                    (20 : k) * a41.eval a * w1.eval a +
                  (9 : k) * lambda * a41.eval a = 0 ∧
                (81 : k) * q41.eval a -
                    (90 : k) * a41.eval a * (p.coeff 2).eval a +
                  (5 : k) * (a41.eval a) ^ 3 = 0 ∧
                (216 : k) * q53.eval a +
                    (27 : k) * lambda * (a41.eval a) ^ 2 +
                  (40 : k) * (a41.eval a) ^ 2 * w1.eval a -
                    (240 : k) * a41.eval a * p32.eval a +
                  (108 : k) * lambda * (p.coeff 2).eval a -
                    (240 : k) * (p.coeff 2).eval a * w1.eval a = 0 ∧
                (3888 : k) * (q.coeff 3).eval a -
                    (81 : k) * lambda * (a41.eval a) ^ 3 -
                  (320 : k) * (a41.eval a) ^ 3 * w1.eval a +
                    (720 : k) * (a41.eval a) ^ 2 * p32.eval a +
                  (972 : k) * lambda * a41.eval a *
                      (p.coeff 2).eval a +
                    (1440 : k) * a41.eval a * (p.coeff 2).eval a *
                      w1.eval a -
                  (4320 : k) * (p.coeff 2).eval a * p32.eval a =
                    0 ∧
                bridgeIotaLeftHead610 a41 s1 b62 (p.coeff 2) q41 +
                    h0 * bridgeIotaLeftTail610 h0 w1 a41 p32 s1 u2 b62
                      q53 (p.coeff 2) (p.coeff 1) (p.coeff 0) q41
                      (q.coeff 3) (q.coeff 2) (q.coeff 1) (q.coeff 0)
                      (Polynomial.C lambda) =
                  Polynomial.C iotaK * h0 ^ 5 ∧
                bridgeIotaLeftHead610 (a41.eval a) (s1.eval a)
                    (b62.eval a) ((p.coeff 2).eval a)
                    (q41.eval a) = 0 ∧
                (a41.eval a = 0 ∨
                  (4 : k) * (a41.eval a) ^ 4 -
                      (35 : k) * (p.coeff 2).eval a *
                        (a41.eval a) ^ 2 +
                    (90 : k) * ((p.coeff 2).eval a) ^ 2 = 0)) ∨
          ((240 : k) * (p.coeff 2).eval a -
                (40 : k) * (a41.eval a) ^ 2 -
              (27 : k) * lambda * p31.eval a -
                (40 : k) * p31.eval a * w1.eval a = 0 ∧
            (144 : k) * b62.eval a - (120 : k) * (a41.eval a) ^ 2 +
                (45 : k) * lambda * p31.eval a -
              (200 : k) * p31.eval a * w1.eval a = 0 ∧
            ((p31.eval a = 0 ∧
                (6 : k) * (p.coeff 2).eval a -
                  (a41.eval a) ^ 2 = 0 ∧
                (6 : k) * b62.eval a -
                  (5 : k) * (a41.eval a) ^ 2 = 0) ∨
              (p31.eval a ≠ 0 ∧ a41.eval a = 0 ∧ w1.eval a = 0 ∧
                (80 : k) * (p.coeff 2).eval a =
                  (9 : k) * lambda * p31.eval a ∧
                (16 : k) * b62.eval a =
                  -(5 : k) * lambda * p31.eval a ∧
                ∃ (omega psi psi2 : k[X]),
                  (583200 : k[X]) * p31 ^ 2 -
                      (489888 : k[X]) * p31 * u1 +
                    (419904 : k[X]) * q.coeff 4 = h0 * omega ∧
                  omega.eval a =
                    (648 : k) * a41.eval a *
                      ((80 : k) * (a41.eval a) ^ 2 +
                          (297 : k) * lambda * p31.eval a -
                        (960 : k) * p31.eval a * w1.eval a) ∧
                  omega + (-(518400 : k[X]) * a41 ^ 3 +
                      (466560 : k[X]) * a41 ^ 2 * s1 -
                      (419904 : k[X]) * a41 * b62 -
                      (349920 : k[X]) * a41 * Polynomial.C lambda *
                        p31 +
                      (1166400 : k[X]) * a41 * p.coeff 2 -
                      (1360800 : k[X]) * a41 * p31 * w1 +
                      (816480 : k[X]) * a41 * u1 * w1 -
                      (559872 : k[X]) * p.coeff 2 * s1 +
                      (933120 : k[X]) * p31 * s1 * w1 -
                      (349920 : k[X]) * q52 * w1) = h0 * psi ∧
                  psi.eval a =
                    (162 : k) * w1.eval a *
                      ((7600 : k) * (a41.eval a) ^ 2 * w1.eval a -
                          (2520 : k) * lambda * (a41.eval a) ^ 2 +
                          (243 : k) * lambda ^ 2 * p31.eval a -
                          (1980 : k) * lambda * p31.eval a *
                            w1.eval a +
                        (3200 : k) * p31.eval a *
                          (w1.eval a) ^ 2) ∧
                  psi + ((466560 : k[X]) * a41 ^ 2 *
                      Polynomial.C lambda * w1 +
                    (518400 : k[X]) * a41 ^ 2 * w1 ^ 2 -
                    (1244160 : k[X]) * a41 * s1 * w1 ^ 2 +
                    (349920 : k[X]) * b62 * w1 ^ 2 -
                    (349920 : k[X]) * Polynomial.C lambda *
                      p.coeff 2 * w1 +
                    (466560 : k[X]) * Polynomial.C lambda * p31 *
                      w1 ^ 2 +
                    (194400 : k[X]) * p.coeff 2 * w1 ^ 2 -
                    (432000 : k[X]) * p31 * w1 ^ 3 -
                    (362880 : k[X]) * u1 * w1 ^ 3) = h0 * psi2 ∧
                  psi2.eval a =
                    (288 : k) * ((1980 : k) * lambda * a41.eval a *
                        (w1.eval a) ^ 3 -
                      (4400 : k) * a41.eval a * (w1.eval a) ^ 4 -
                      (729 : k) * lambda * (p.coeff 1).eval a -
                      (405 : k) * (p.coeff 1).eval a *
                        w1.eval a) ∧
                  psi2.eval a =
                    -(209952 : k) * lambda * (p.coeff 1).eval a ∧
                  (288 : k) * ((729 : k) * lambda +
                        (405 : k) * w1.eval a) *
                      (((p.coeff 0).derivative).eval a *
                          (q.coeff 1).eval a - j) =
                    ((q.coeff 0).derivative).eval a *
                      ((288 : k) * ((1980 : k) * lambda *
                            a41.eval a * (w1.eval a) ^ 3 -
                          (4400 : k) * a41.eval a *
                            (w1.eval a) ^ 4) -
                        psi2.eval a))))) := by
  obtain ⟨w1, a41, s1, u1, p31, b62, q52, iotaK, hw, ha4s, hp3, hs, hu,
    hb6s, hq5, hMs, hTu, hVq, hWq, hUload, hrow, hroweval, hipow,
    hipeel, hiheadeval, hires1, hires2, halt⟩ :=
    nonzeroFace610_linearRoot_terminalIntegralClosure p q H h0 j lambda
      a hp hq hh0 hh0degree hH hp6 hq10 hN hD hroot hlambda
  obtain ⟨kappaMu, hkpow⟩ :=
    nonzeroFace610_bridgeKappaPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp6 hq10 hN hD
  have hkpowJet :
      bridgeClearedKappaDefect610 h0 (h0 ^ 5 * w1) (h0 ^ 3 * a41)
          (h0 * p31) (p.coeff 2) (p.coeff 1) (p.coeff 0)
          (h0 ^ 7 * s1) (h0 ^ 5 * u1) (h0 ^ 4 * b62) (h0 ^ 2 * q52)
          (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda =
        Polynomial.C kappaMu * h0 ^ 55 := by
    rw [← hw, ← ha4s, ← hp3, ← hs, ← hu, ← hb6s, ← hq5]
    exact hkpow
  have hkpeel :
      bridgeKappaJetHead610 a41 p31 s1 u1 q52 (q.coeff 4) +
          h0 * bridgeKappaJetTail610 h0 w1 a41 p31 s1 u1 b62 q52
            (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 4)
            (q.coeff 3) (q.coeff 2) (q.coeff 1)
            (Polynomial.C lambda) =
        Polynomial.C kappaMu * h0 ^ 7 := by
    have h48 : (h0 : k[X]) ^ 48 ≠ 0 := pow_ne_zero 48 hh0
    apply mul_left_cancel₀ h48
    rw [← bridgeClearedKappaDefect610_jet_factored h0 w1 a41 p31 s1
      u1 b62 q52 (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 4)
      (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda]
    rw [hkpowJet]
    ring
  have hkheadeval :
      bridgeKappaJetHead610 (a41.eval a) (p31.eval a) (s1.eval a)
        (u1.eval a) (q52.eval a) ((q.coeff 4).eval a) = 0 := by
    have hev := congrArg (Polynomial.eval a) hkpeel
    have h7z : (0 : k) ^ 7 = 0 := by norm_num
    simp only [Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, hroot,
      bridgeKappaJetHead610_eval, h7z, mul_zero, zero_mul,
      add_zero] at hev
    exact hev
  have hksplit0 : a41.eval a * (p31.eval a) ^ 3 = 0 :=
    bridgeKappa_chamberFree_split610 (a41.eval a) (p31.eval a)
      (s1.eval a) (u1.eval a) (q52.eval a) ((q.coeff 4).eval a)
      hkheadeval hMs hTu hVq hWq
  have hksplit : a41.eval a = 0 ∨ p31.eval a = 0 := by
    rcases mul_eq_zero.mp hksplit0 with h | h
    · exact Or.inl h
    · right
      by_contra hne
      exact pow_ne_zero 3 hne h
  refine ⟨w1, a41, s1, u1, p31, b62, q52, iotaK, kappaMu, hw, ha4s,
    hp3, hs, hu, hb6s, hq5, hMs, hTu, hVq, hWq, hUload, hrow,
    hroweval, hipow, hipeel, hiheadeval, hires1, hires2, hkpow,
    hkpeel, hkheadeval, hksplit0, hksplit, ?_⟩
  rcases halt with hleft | ⟨hload1, hload2, hcd⟩
  · exact Or.inl hleft
  · rcases hcd with ⟨hz, hp2pin, hb62pin⟩ | ⟨hnz, hcore, hp2n, hb62n,
      omega, psi, psi2, homega, homegaval, hpsieq, hpsival, hpsi2eq,
      hpsi2val, heli2⟩
    · exact Or.inr ⟨hload1, hload2, Or.inl ⟨hz, hp2pin, hb62pin⟩⟩
    · obtain ⟨ha41z, hw1z, hp2k, hb62k⟩ :=
        bridgeKappa_complement_pins610 (w1.eval a) (a41.eval a)
          (p31.eval a) ((p.coeff 2).eval a) (b62.eval a) lambda hnz
          hksplit0 hcore hp2n hb62n
      have hpsi2k : psi2.eval a =
          -(209952 : k) * lambda * (p.coeff 1).eval a := by
        rw [hpsi2val, ha41z, hw1z]
        ring
      exact Or.inr ⟨hload1, hload2, Or.inr ⟨hnz, ha41z, hw1z, hp2k,
        hb62k, omega, psi, psi2, homega, homegaval, hpsieq, hpsival,
        hpsi2eq, hpsi2val, hpsi2k, heli2⟩⟩

end NonzeroKappaIntegralBridge610

end Max11DegreeRoutes
