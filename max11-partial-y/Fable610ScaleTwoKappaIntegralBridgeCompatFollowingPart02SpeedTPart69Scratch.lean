import Fable610ScaleTwoKappaIntegralBridgeCompatFollowingPart02SpeedTPart60Scratch
import Fable610ScaleTwoKappaIntegralBridgeCompatFollowingPart02SpeedTPart63Scratch
import Fable610ScaleTwoKappaIntegralBridgeCompatFollowingPart02SpeedTPart64Scratch
import Fable610ScaleTwoKappaIntegralBridgeCompatFollowingPart02SpeedTPart65Scratch
import Fable610ScaleTwoKappaIntegralBridgeCompatFollowingPart02SpeedTPart66Scratch
import Fable610ScaleTwoKappaIntegralBridgeCompatFollowingPart02SpeedTPart67Scratch
import Fable610ScaleTwoKappaIntegralBridgeCompatFollowingPart16Scratch
import Fable610ScaleTwoKappaIntegralBridgeCompatFollowingPart02SpeedTPart68Scratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section NonzeroMuIntegralBridge610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 40000000 in
/-- Finite local `μ` integral bridge: the `λ` bridge packet (the `ι`,
`κ` and `λ` packets reused opaquely) together with the weight-`65`
clearing of the degree-`2` first integral, its `h₀⁵⁹`-peeled factored
head, the chamber-free twenty-three-term reduction of the vanishing
head, the seven sibling-child descents with the `h₀⁶¹`-peeled deep
head and its honest split `p₃₂(a) = 0 ∨` first `λ`-loaded quotient
tie, and on the pinned complement child the honest split
`a₄₁(a) = 0` (collapsing that child) `∨` the first `q₃`-tie.  Every
child is preserved; none is closed. -/
theorem nonzeroFace610_linearRoot_muIntegralBridge
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
    ∃ (w1 a41 s1 u1 p31 b62 q52 p32 u2 q53 q41 : k[X])
      (iotaK kappaMu lambdaNu muXi : k),
      p.coeff 5 = h0 ^ 5 * w1 ∧ p.coeff 4 = h0 ^ 3 * a41 ∧
        p.coeff 3 = h0 * p31 ∧ q.coeff 8 = h0 ^ 7 * s1 ∧
        q.coeff 7 = h0 ^ 5 * u1 ∧ q.coeff 6 = h0 ^ 4 * b62 ∧
        q.coeff 5 = h0 ^ 2 * q52 ∧
        (3 : k) * s1.eval a = (5 : k) * a41.eval a ∧
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
        bridgeClearedLambdaDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
            (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda =
          Polynomial.C lambdaNu * h0 ^ 60 ∧
        bridgeLambdaJetHead610 p31 u1 (q.coeff 4) +
            h0 * bridgeLambdaJetTail610 h0 w1 a41 p31 s1 u1 b62 q52
              (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 4)
              (q.coeff 3) (q.coeff 2) (q.coeff 1)
              (Polynomial.C lambda) =
          Polynomial.C lambdaNu * h0 ^ 8 ∧
        bridgeLambdaJetHead610 (p31.eval a) (u1.eval a)
          ((q.coeff 4).eval a) = 0 ∧
        p31.eval a = 0 ∧ u1.eval a = 0 ∧ q52.eval a = 0 ∧
        (q.coeff 4).eval a = 0 ∧
        p.coeff 3 = h0 ^ 2 * p32 ∧ q.coeff 7 = h0 ^ 6 * u2 ∧
        q.coeff 5 = h0 ^ 3 * q53 ∧ q.coeff 4 = h0 * q41 ∧
        bridgeLambdaDeepHead610 a41 s1 b62 (p.coeff 2) q41 +
            h0 * bridgeLambdaDeepTail610 h0 w1 a41 p32 s1 u2 b62 q53
              (p.coeff 2) (p.coeff 1) (p.coeff 0) q41
              (q.coeff 3) (q.coeff 2) (q.coeff 1)
              (Polynomial.C lambda) =
          Polynomial.C lambdaNu * h0 ^ 6 ∧
        bridgeLambdaDeepHead610 (a41.eval a) (s1.eval a) (b62.eval a)
          ((p.coeff 2).eval a) (q41.eval a) = 0 ∧
        (100 : k) * (a41.eval a) ^ 6 -
            (1575 : k) * (a41.eval a) ^ 4 * (p.coeff 2).eval a +
          (810 : k) * (a41.eval a) ^ 3 * q41.eval a +
            (4860 : k) * (a41.eval a) ^ 2 * ((p.coeff 2).eval a) ^ 2 -
          (2916 : k) * a41.eval a * (p.coeff 2).eval a * q41.eval a -
            (1620 : k) * ((p.coeff 2).eval a) ^ 3 = 0 ∧
        bridgeClearedMuDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
            (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda =
          Polynomial.C muXi * h0 ^ 65 ∧
        bridgeMuJetHead610 w1 a41 p32 s1 u2 b62 q53 (p.coeff 2) q41
              (q.coeff 3) (Polynomial.C lambda) +
            h0 * bridgeMuJetTail610 h0 w1 a41 p32 s1 u2 b62 q53
              (p.coeff 2) (p.coeff 1) (p.coeff 0) q41 (q.coeff 3)
              (q.coeff 2) (q.coeff 1) (Polynomial.C lambda) =
          Polynomial.C muXi * h0 ^ 6 ∧
        bridgeMuJetHead610 (w1.eval a) (a41.eval a) (p32.eval a)
          (s1.eval a) (u2.eval a) (b62.eval a) (q53.eval a)
          ((p.coeff 2).eval a) (q41.eval a) ((q.coeff 3).eval a)
          lambda = 0 ∧
        -(1120 : k) * (a41.eval a) ^ 6 * (w1.eval a)
        + (189 : k) * (a41.eval a) ^ 6 * lambda
        + (220 : k) * (a41.eval a) ^ 5 * (p32.eval a)
        + (588 : k) * (a41.eval a) ^ 5 * (u2.eval a)
        + (9200 : k) * (a41.eval a) ^ 4 * ((p.coeff 2).eval a) * (w1.eval a)
        - (1260 : k) * (a41.eval a) ^ 4 * ((p.coeff 2).eval a) * lambda
        - (600 : k) * (a41.eval a) ^ 4 * (q53.eval a)
        - (3360 : k) * (a41.eval a) ^ 3 * ((p.coeff 2).eval a) * (p32.eval a)
        - (3360 : k) * (a41.eval a) ^ 3 * ((p.coeff 2).eval a) * (u2.eval a)
        - (1920 : k) * (a41.eval a) ^ 3 * (q41.eval a) * (w1.eval a)
        + (576 : k) * (a41.eval a) ^ 3 * ((q.coeff 3).eval a)
        - (17280 : k) * (a41.eval a) ^ 2 * ((p.coeff 2).eval a) ^ 2 * (w1.eval a)
        + (2160 : k) * (a41.eval a) ^ 2 * ((p.coeff 2).eval a) ^ 2 * lambda
        + (2880 : k) * (a41.eval a) ^ 2 * ((p.coeff 2).eval a) * (q53.eval a)
        + (2304 : k) * (a41.eval a) ^ 2 * (p32.eval a) * (q41.eval a)
        + (4800 : k) * (a41.eval a) * ((p.coeff 2).eval a) ^ 2 * (p32.eval a)
        + (4032 : k) * (a41.eval a) * ((p.coeff 2).eval a) ^ 2 * (u2.eval a)
        + (4608 : k) * (a41.eval a) * ((p.coeff 2).eval a) * (q41.eval a) * (w1.eval a)
        - (2304 : k) * (a41.eval a) * ((p.coeff 2).eval a) * ((q.coeff 3).eval a)
        + (3840 : k) * ((p.coeff 2).eval a) ^ 3 * (w1.eval a)
        - (576 : k) * ((p.coeff 2).eval a) ^ 3 * lambda
        - (1920 : k) * ((p.coeff 2).eval a) ^ 2 * (q53.eval a)
        - (3072 : k) * ((p.coeff 2).eval a) * (p32.eval a) * (q41.eval a) = 0 ∧
        ((∃ a42 p21 s2 b63 q54 q42 q31 : k[X],
            (bridgeIotaLeftHead610 a41 s1 b62 (p.coeff 2) q41 +
                h0 * bridgeIotaLeftTail610 h0 w1 a41 p32 s1 u2 b62
                  q53 (p.coeff 2) (p.coeff 1) (p.coeff 0) q41
                  (q.coeff 3) (q.coeff 2) (q.coeff 1) (q.coeff 0)
                  (Polynomial.C lambda) =
              Polynomial.C iotaK * h0 ^ 5) ∧
            a41.eval a = 0 ∧ (p.coeff 2).eval a = 0 ∧
            s1.eval a = 0 ∧ b62.eval a = 0 ∧ q41.eval a = 0 ∧
            q53.eval a = 0 ∧ (q.coeff 3).eval a = 0 ∧
            (3 : k) * u2.eval a = (5 : k) * p32.eval a ∧
            p.coeff 4 = h0 ^ 4 * a42 ∧ p.coeff 2 = h0 * p21 ∧
            q.coeff 8 = h0 ^ 8 * s2 ∧ q.coeff 6 = h0 ^ 5 * b63 ∧
            q.coeff 5 = h0 ^ 4 * q54 ∧ q.coeff 4 = h0 ^ 2 * q42 ∧
            q.coeff 3 = h0 * q31 ∧
            (bridgeMuDeepHead610 w1 p32 u2 b63 p21 q42 q31
                  (Polynomial.C lambda) +
                h0 * bridgeMuDeepTail610 h0 w1 a42 p32 s2 u2 b63 q54
                  p21 (p.coeff 1) (p.coeff 0) q42 q31 (q.coeff 2)
                  (q.coeff 1) (Polynomial.C lambda) =
              Polynomial.C muXi * h0 ^ 4) ∧
            bridgeMuDeepHead610 (w1.eval a) (p32.eval a) (u2.eval a)
              (b63.eval a) (p21.eval a) (q42.eval a) (q31.eval a)
              lambda = 0 ∧
            ((p32.eval a = 0 ∧ u2.eval a = 0) ∨
              (45 : k) * lambda * (p32.eval a) ^ 3 +
                  (144 : k) * b63.eval a * (p32.eval a) ^ 2 +
                  (240 : k) * p21.eval a * (p32.eval a) ^ 2 +
                  (288 : k) * p32.eval a * q42.eval a * w1.eval a -
                (400 : k) * (p32.eval a) ^ 3 * w1.eval a -
                  (144 : k) * p32.eval a * q31.eval a -
                  (384 : k) * p21.eval a * q42.eval a = 0)) ∨
          ((6 : k) * (p.coeff 2).eval a - (a41.eval a) ^ 2 = 0 ∧
            (6 : k) * b62.eval a - (5 : k) * (a41.eval a) ^ 2 = 0 ∧
            ((a41.eval a = 0 ∧ (p.coeff 2).eval a = 0 ∧
                b62.eval a = 0) ∨
              (a41.eval a = 0 ∧ (p.coeff 2).eval a = 0 ∧
                b62.eval a = 0 ∧ q41.eval a = 0) ∨
              ((324 : k) * q41.eval a = (35 : k) * (a41.eval a) ^ 3 ∧
                (15552 : k) * (q.coeff 3).eval a =
                  -(2943 : k) * lambda * (a41.eval a) ^ 3 +
                    (14040 : k) * (a41.eval a) ^ 3 * w1.eval a +
                    (1060 : k) * (a41.eval a) ^ 2 * p32.eval a -
                    (11340 : k) * (a41.eval a) ^ 2 * u2.eval a +
                    (14040 : k) * a41.eval a * q53.eval a)))) := by
  obtain ⟨w1, a41, s1, u1, p31, b62, q52, p32, u2, q53, q41, iotaK,
    kappaMu, lambdaNu, hw, ha4s, hp3, hs, hu, hb6s, hq5, hMs, hUload,
    hrow, hroweval, hipow, hipeel, hiheadeval, hkpow, hkpeel,
    hkheadeval, hlpow, hlpeel, hlheadeval, hp31z, hu1z, hq52z, hq4z,
    hp3', hq7', hq5', hq4', hldeepPeel, hldeepHeadEval, hG, halt⟩ :=
    nonzeroFace610_linearRoot_lambdaIntegralBridge p q H h0 j lambda
      a hp hq hh0 hh0degree hH hp6 hq10 hN hD hroot hlambda
  obtain ⟨muXi, hmupow⟩ :=
    nonzeroFace610_bridgeMuPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp6 hq10 hN hD
  have hmupowJet :
      bridgeClearedMuDefect610 h0 (h0 ^ 5 * w1) (h0 ^ 3 * a41)
          (h0 ^ 2 * p32) (p.coeff 2) (p.coeff 1) (p.coeff 0)
          (h0 ^ 7 * s1) (h0 ^ 6 * u2) (h0 ^ 4 * b62) (h0 ^ 3 * q53)
          (h0 * q41) (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda =
        Polynomial.C muXi * h0 ^ 65 := by
    rw [← hw, ← ha4s, ← hp3', ← hs, ← hq7', ← hb6s, ← hq5', ← hq4']
    exact hmupow
  have hmupeel :
      bridgeMuJetHead610 w1 a41 p32 s1 u2 b62 q53 (p.coeff 2) q41
            (q.coeff 3) (Polynomial.C lambda) +
          h0 * bridgeMuJetTail610 h0 w1 a41 p32 s1 u2 b62 q53
            (p.coeff 2) (p.coeff 1) (p.coeff 0) q41 (q.coeff 3)
            (q.coeff 2) (q.coeff 1) (Polynomial.C lambda) =
        Polynomial.C muXi * h0 ^ 6 := by
    have h59 : (h0 : k[X]) ^ 59 ≠ 0 := pow_ne_zero 59 hh0
    apply mul_left_cancel₀ h59
    rw [← bridgeClearedMuDefect610_jet_factored h0 w1 a41 p32 s1 u2
      b62 q53 (p.coeff 2) (p.coeff 1) (p.coeff 0) q41 (q.coeff 3)
      (q.coeff 2) (q.coeff 1) lambda]
    rw [hmupowJet]
    ring
  have hmuheadeval :
      bridgeMuJetHead610 (w1.eval a) (a41.eval a) (p32.eval a)
        (s1.eval a) (u2.eval a) (b62.eval a) (q53.eval a)
        ((p.coeff 2).eval a) (q41.eval a) ((q.coeff 3).eval a)
        lambda = 0 := by
    have hev := congrArg (Polynomial.eval a) hmupeel
    have h6z : (0 : k) ^ 6 = 0 := by norm_num
    simp only [Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, hroot,
      bridgeMuJetHead610_eval, h6z, mul_zero, zero_mul,
      add_zero] at hev
    exact hev
  have hUz : (10 : k) * (a41.eval a) ^ 2 - (18 : k) * b62.eval a +
      (30 : k) * (p.coeff 2).eval a = 0 := by
    linear_combination hUload +
      ((9 : k) * lambda - (20 : k) * w1.eval a) * hp31z
  have hmuR22 :=
    bridgeMu_chamberFreeReduction610 (w1.eval a) (a41.eval a)
      (p32.eval a) (s1.eval a) (u2.eval a) (b62.eval a) (q53.eval a)
      ((p.coeff 2).eval a) (q41.eval a) ((q.coeff 3).eval a) lambda
      hmuheadeval hMs hUz
  have h3ne : (3 : k) ≠ 0 := by norm_num
  refine ⟨w1, a41, s1, u1, p31, b62, q52, p32, u2, q53, q41, iotaK,
    kappaMu, lambdaNu, muXi, hw, ha4s, hp3, hs, hu, hb6s, hq5, hMs,
    hUload, hrow, hroweval, hipow, hipeel, hiheadeval, hkpow, hkpeel,
    hkheadeval, hlpow, hlpeel, hlheadeval, hp31z, hu1z, hq52z, hq4z,
    hp3', hq7', hq5', hq4', hldeepPeel, hldeepHeadEval, hG,
    hmupow, hmupeel, hmuheadeval, hmuR22, ?_⟩
  rcases halt with ⟨hileft, ha41z, hp2z, hs1z, hb62z, hq41z, hq53z,
      hq3z, hu2tie⟩ | ⟨hp2pin, hb62pin, hcd⟩
  · obtain ⟨a42, ha42⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0 a41 a hh0degree
        hroot ha41z
    obtain ⟨p21, hp21⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0 (p.coeff 2) a
        hh0degree hroot hp2z
    obtain ⟨s2, hs2⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0 s1 a hh0degree
        hroot hs1z
    obtain ⟨b63, hb63⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0 b62 a hh0degree
        hroot hb62z
    obtain ⟨q42, hq42⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0 q41 a hh0degree
        hroot hq41z
    obtain ⟨q54, hq54⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0 q53 a hh0degree
        hroot hq53z
    obtain ⟨q31, hq31⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0 (q.coeff 3) a
        hh0degree hroot hq3z
    have hp4deep : p.coeff 4 = h0 ^ 4 * a42 := by
      rw [ha4s, ha42]
      ring
    have hq8deep : q.coeff 8 = h0 ^ 8 * s2 := by
      rw [hs, hs2]
      ring
    have hq6deep : q.coeff 6 = h0 ^ 5 * b63 := by
      rw [hb6s, hb63]
      ring
    have hq5deep2 : q.coeff 5 = h0 ^ 4 * q54 := by
      rw [hq5', hq54]
      ring
    have hq4deep2 : q.coeff 4 = h0 ^ 2 * q42 := by
      rw [hq4', hq42]
      ring
    have hmupowDeep :
        bridgeClearedMuDefect610 h0 (h0 ^ 5 * w1) (h0 ^ 4 * a42)
            (h0 ^ 2 * p32) (h0 * p21) (p.coeff 1) (p.coeff 0)
            (h0 ^ 8 * s2) (h0 ^ 6 * u2) (h0 ^ 5 * b63) (h0 ^ 4 * q54)
            (h0 ^ 2 * q42) (h0 * q31) (q.coeff 2) (q.coeff 1)
            lambda =
          Polynomial.C muXi * h0 ^ 65 := by
      rw [← hw, ← hp4deep, ← hp3', ← hp21, ← hq8deep, ← hq7',
        ← hq6deep, ← hq5deep2, ← hq4deep2, ← hq31]
      exact hmupow
    have hmuDeepPeel :
        bridgeMuDeepHead610 w1 p32 u2 b63 p21 q42 q31
              (Polynomial.C lambda) +
            h0 * bridgeMuDeepTail610 h0 w1 a42 p32 s2 u2 b63 q54
              p21 (p.coeff 1) (p.coeff 0) q42 q31 (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          Polynomial.C muXi * h0 ^ 4 := by
      have h61 : (h0 : k[X]) ^ 61 ≠ 0 := pow_ne_zero 61 hh0
      apply mul_left_cancel₀ h61
      rw [← bridgeClearedMuDefect610_deepJet_factored h0 w1 a42 p32
        s2 u2 b63 q54 p21 (p.coeff 1) (p.coeff 0) q42 q31
        (q.coeff 2) (q.coeff 1) lambda]
      rw [hmupowDeep]
      ring
    have hmuDeepHeadEval :
        bridgeMuDeepHead610 (w1.eval a) (p32.eval a) (u2.eval a)
          (b63.eval a) (p21.eval a) (q42.eval a) (q31.eval a)
          lambda = 0 := by
      have hev := congrArg (Polynomial.eval a) hmuDeepPeel
      have h4z : (0 : k) ^ 4 = 0 := by norm_num
      simp only [Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_C, hroot,
        bridgeMuDeepHead610_eval, h4z, mul_zero, zero_mul,
        add_zero] at hev
      exact hev
    have hsplit :=
      bridgeMu_siblingDeepSplit610 (w1.eval a) (p32.eval a)
        (u2.eval a) (b63.eval a) (p21.eval a) (q42.eval a)
        (q31.eval a) lambda hmuDeepHeadEval hu2tie
    exact Or.inl ⟨a42, p21, s2, b63, q54, q42, q31, hileft, ha41z,
      hp2z, hs1z, hb62z, hq41z, hq53z, hq3z, hu2tie, hp4deep, hp21,
      hq8deep, hq6deep, hq5deep2, hq4deep2, hq31, hmuDeepPeel,
      hmuDeepHeadEval, hsplit⟩
  · rcases hcd with ⟨ha41z, hp2z, hb62z⟩ | hq41pin
    · exact Or.inr ⟨hp2pin, hb62pin, Or.inl ⟨ha41z, hp2z, hb62z⟩⟩
    · rcases bridgeMu_complementSplit610 (w1.eval a) (a41.eval a)
          (p32.eval a) (u2.eval a) (q53.eval a) (q41.eval a)
          ((q.coeff 3).eval a) ((p.coeff 2).eval a) lambda hmuR22
          hp2pin hq41pin with ha41z | htie
      · have hp2z : (p.coeff 2).eval a = 0 := by
          linear_combination (1 / 6 : k) * hp2pin +
            ((1 / 6 : k) * a41.eval a) * ha41z
        have hb62z : b62.eval a = 0 := by
          linear_combination (1 / 6 : k) * hb62pin +
            ((5 / 6 : k) * a41.eval a) * ha41z
        have hq41z : q41.eval a = 0 := by
          linear_combination (1 / 324 : k) * hq41pin +
            ((35 / 324 : k) * (a41.eval a) ^ 2) * ha41z
        exact Or.inr ⟨hp2pin, hb62pin,
          Or.inr (Or.inl ⟨ha41z, hp2z, hb62z, hq41z⟩)⟩
      · exact Or.inr ⟨hp2pin, hb62pin, Or.inr (Or.inr ⟨hq41pin, htie⟩)⟩

end NonzeroMuIntegralBridge610

end Max11DegreeRoutes
