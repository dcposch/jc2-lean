import Fable610ScaleTwoKappaIntegralBridgeCompatPart19Scratch
import Fable610ScaleTwoKappaIntegralBridgeCompatNextPart18Scratch
import Fable610ScaleTwoKappaIntegralBridgeCompatNextPart17Scratch
import Fable610ScaleTwoKappaIntegralBridgeCompatNextPart16Scratch
import Fable610ScaleTwoKappaIntegralBridgeCompatNextPart15Scratch
import Fable610ScaleTwoKappaIntegralBridgeCompatNextPart14Scratch
import Fable610ScaleTwoKappaIntegralBridgeCompatNextPart13Scratch
import Fable610ScaleTwoKappaIntegralBridgeCompatNextPart12Scratch
import Fable610ScaleTwoKappaIntegralBridgeCompatNextPart11Scratch
import Fable610ScaleTwoKappaIntegralBridgeCompatNextPart06Scratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section NonzeroLambdaIntegralBridge610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 40000000 in
/-- Finite local `λ` integral bridge: the `κ` bridge packet (the `ι`
and `κ` packets reused opaquely) together with the weight-`60`
clearing of the degree-`3` first integral, its `h₀⁵²`-peeled factored
head, the chamber-free kill `p₃₁(a) = 0` (eliminating the
`p₃₁(a) ≠ 0` complement child by honest contradiction), the globally
merged deeper jet `p₃ = h₀² p₃₂`, `q₇ = h₀⁶ u₂`, `q₅ = h₀³ q₅₃`,
`q₄ = h₀ q₄₁`, the `h₀⁵⁴`-peeled deep head with its chamber-free
sextic relation, the collapsed sibling child
`a₄₁(a) = p₂(a) = 0` with its cascade, and the pinned complement
child with the honest split `a₄₁(a) = 0 ∨ 324 q₄₁(a) = 35 a₄₁(a)³`.
Neither surviving child is closed. -/
theorem nonzeroFace610_linearRoot_lambdaIntegralBridge
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
      (iotaK kappaMu lambdaNu : k),
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
        ((bridgeIotaLeftHead610 a41 s1 b62 (p.coeff 2) q41 +
              h0 * bridgeIotaLeftTail610 h0 w1 a41 p32 s1 u2 b62
                q53 (p.coeff 2) (p.coeff 1) (p.coeff 0) q41
                (q.coeff 3) (q.coeff 2) (q.coeff 1) (q.coeff 0)
                (Polynomial.C lambda) =
            Polynomial.C iotaK * h0 ^ 5 ∧
          a41.eval a = 0 ∧ (p.coeff 2).eval a = 0 ∧
          s1.eval a = 0 ∧ b62.eval a = 0 ∧ q41.eval a = 0 ∧
          q53.eval a = 0 ∧ (q.coeff 3).eval a = 0 ∧
          (3 : k) * u2.eval a = (5 : k) * p32.eval a) ∨
        ((6 : k) * (p.coeff 2).eval a - (a41.eval a) ^ 2 = 0 ∧
          (6 : k) * b62.eval a - (5 : k) * (a41.eval a) ^ 2 = 0 ∧
          ((a41.eval a = 0 ∧ (p.coeff 2).eval a = 0 ∧
              b62.eval a = 0) ∨
            (324 : k) * q41.eval a = (35 : k) * (a41.eval a) ^ 3))) := by
  obtain ⟨w1, a41, s1, u1, p31, b62, q52, iotaK, kappaMu, hw, ha4s,
    hp3, hs, hu, hb6s, hq5, hMs, hTu, hVq, hWq, hUload, hrow,
    hroweval, hipow, hipeel, hiheadeval, _hires1, _hires2, hkpow,
    hkpeel, hkheadeval, _hksplit0, _hksplit, halt⟩ :=
    nonzeroFace610_linearRoot_kappaIntegralBridge p q H h0 j lambda
      a hp hq hh0 hh0degree hH hp6 hq10 hN hD hroot hlambda
  obtain ⟨lambdaNu, hlpow⟩ :=
    nonzeroFace610_bridgeLambdaPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp6 hq10 hN hD
  have hlpowJet :
      bridgeClearedLambdaDefect610 h0 (h0 ^ 5 * w1) (h0 ^ 3 * a41)
          (h0 * p31) (p.coeff 2) (p.coeff 1) (p.coeff 0)
          (h0 ^ 7 * s1) (h0 ^ 5 * u1) (h0 ^ 4 * b62) (h0 ^ 2 * q52)
          (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda =
        Polynomial.C lambdaNu * h0 ^ 60 := by
    rw [← hw, ← ha4s, ← hp3, ← hs, ← hu, ← hb6s, ← hq5]
    exact hlpow
  have hlpeel :
      bridgeLambdaJetHead610 p31 u1 (q.coeff 4) +
          h0 * bridgeLambdaJetTail610 h0 w1 a41 p31 s1 u1 b62 q52
            (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 4)
            (q.coeff 3) (q.coeff 2) (q.coeff 1)
            (Polynomial.C lambda) =
        Polynomial.C lambdaNu * h0 ^ 8 := by
    have h52 : (h0 : k[X]) ^ 52 ≠ 0 := pow_ne_zero 52 hh0
    apply mul_left_cancel₀ h52
    rw [← bridgeClearedLambdaDefect610_jet_factored h0 w1 a41 p31 s1
      u1 b62 q52 (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 4)
      (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda]
    rw [hlpowJet]
    ring
  have hlheadeval :
      bridgeLambdaJetHead610 (p31.eval a) (u1.eval a)
        ((q.coeff 4).eval a) = 0 := by
    have hev := congrArg (Polynomial.eval a) hlpeel
    have h8z : (0 : k) ^ 8 = 0 := by norm_num
    simp only [Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, hroot,
      bridgeLambdaJetHead610_eval, h8z, mul_zero, zero_mul,
      add_zero] at hev
    exact hev
  have hp31z : p31.eval a = 0 :=
    bridgeLambda_chamberFree_kill610 (p31.eval a) (u1.eval a)
      ((q.coeff 4).eval a) hlheadeval hTu hWq
  have h3ne : (3 : k) ≠ 0 := by norm_num
  have h9ne : (9 : k) ≠ 0 := by norm_num
  have hu1z : u1.eval a = 0 := by
    have h30 : (3 : k) * u1.eval a = 0 := by
      rw [hTu, hp31z]
      ring
    exact (mul_eq_zero.mp h30).resolve_left h3ne
  have hq52z : q52.eval a = 0 := by
    have h90 : (9 : k) * q52.eval a = 0 := by
      rw [hVq, hp31z]
      ring
    exact (mul_eq_zero.mp h90).resolve_left h9ne
  have hq4z : (q.coeff 4).eval a = 0 := by
    have h90 : (9 : k) * (q.coeff 4).eval a = 0 := by
      rw [hWq, hp31z]
      ring
    exact (mul_eq_zero.mp h90).resolve_left h9ne
  obtain ⟨p32, hp32⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 p31 a hh0degree hroot
      hp31z
  obtain ⟨u2, hu2⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 u1 a hh0degree hroot
      hu1z
  obtain ⟨q53, hq53⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 q52 a hh0degree hroot
      hq52z
  obtain ⟨q41, hq41⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 (q.coeff 4) a
      hh0degree hroot hq4z
  have hp3' : p.coeff 3 = h0 ^ 2 * p32 := by
    rw [hp3, hp32]
    ring
  have hq7' : q.coeff 7 = h0 ^ 6 * u2 := by
    rw [hu, hu2]
    ring
  have hq5' : q.coeff 5 = h0 ^ 3 * q53 := by
    rw [hq5, hq53]
    ring
  have hq4' : q.coeff 4 = h0 * q41 := hq41
  have hlpowDeep :
      bridgeClearedLambdaDefect610 h0 (h0 ^ 5 * w1) (h0 ^ 3 * a41)
          (h0 ^ 2 * p32) (p.coeff 2) (p.coeff 1) (p.coeff 0)
          (h0 ^ 7 * s1) (h0 ^ 6 * u2) (h0 ^ 4 * b62) (h0 ^ 3 * q53)
          (h0 * q41) (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda =
        Polynomial.C lambdaNu * h0 ^ 60 := by
    rw [← hw, ← ha4s, ← hp3', ← hs, ← hq7', ← hb6s, ← hq5', ← hq4']
    exact hlpow
  have hldeepPeel :
      bridgeLambdaDeepHead610 a41 s1 b62 (p.coeff 2) q41 +
          h0 * bridgeLambdaDeepTail610 h0 w1 a41 p32 s1 u2 b62 q53
            (p.coeff 2) (p.coeff 1) (p.coeff 0) q41
            (q.coeff 3) (q.coeff 2) (q.coeff 1)
            (Polynomial.C lambda) =
        Polynomial.C lambdaNu * h0 ^ 6 := by
    have h54 : (h0 : k[X]) ^ 54 ≠ 0 := pow_ne_zero 54 hh0
    apply mul_left_cancel₀ h54
    rw [← bridgeClearedLambdaDefect610_deepJet_factored h0 w1 a41 p32
      s1 u2 b62 q53 (p.coeff 2) (p.coeff 1) (p.coeff 0) q41
      (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda]
    rw [hlpowDeep]
    ring
  have hldeepHeadEval :
      bridgeLambdaDeepHead610 (a41.eval a) (s1.eval a) (b62.eval a)
        ((p.coeff 2).eval a) (q41.eval a) = 0 := by
    have hev := congrArg (Polynomial.eval a) hldeepPeel
    have h6z : (0 : k) ^ 6 = 0 := by norm_num
    simp only [Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, hroot,
      bridgeLambdaDeepHead610_eval, h6z, mul_zero, zero_mul,
      add_zero] at hev
    exact hev
  have hUz : (10 : k) * (a41.eval a) ^ 2 - (18 : k) * b62.eval a +
      (30 : k) * (p.coeff 2).eval a = 0 := by
    linear_combination hUload +
      ((9 : k) * lambda - (20 : k) * w1.eval a) * hp31z
  have hG :
      (100 : k) * (a41.eval a) ^ 6 -
          (1575 : k) * (a41.eval a) ^ 4 * (p.coeff 2).eval a +
        (810 : k) * (a41.eval a) ^ 3 * q41.eval a +
          (4860 : k) * (a41.eval a) ^ 2 * ((p.coeff 2).eval a) ^ 2 -
        (2916 : k) * a41.eval a * (p.coeff 2).eval a * q41.eval a -
          (1620 : k) * ((p.coeff 2).eval a) ^ 3 = 0 :=
    bridgeLambda_deepReduction610 (a41.eval a) (s1.eval a)
      (b62.eval a) ((p.coeff 2).eval a) (q41.eval a) hldeepHeadEval
      hMs hUz
  refine ⟨w1, a41, s1, u1, p31, b62, q52, p32, u2, q53, q41, iotaK,
    kappaMu, lambdaNu, hw, ha4s, hp3, hs, hu, hb6s, hq5, hMs, hUload,
    hrow, hroweval, hipow, hipeel, hiheadeval, hkpow, hkpeel,
    hkheadeval, hlpow, hlpeel, hlheadeval, hp31z, hu1z, hq52z, hq4z,
    hp3', hq7', hq5', hq4', hldeepPeel, hldeepHeadEval, hG, ?_⟩
  rcases halt with ⟨-, p32', u2', q53', q41', hp3s, hq7s, hq5s, hq4s,
      hrel1, hrel2, hrel3, hrel4, hileft, -, hsplit⟩ |
    ⟨-, -, hcd⟩
  · have hp32e : p32' = p32 :=
      mul_left_cancel₀ (pow_ne_zero 2 hh0) (hp3s.symm.trans hp3')
    have hu2e : u2' = u2 :=
      mul_left_cancel₀ (pow_ne_zero 6 hh0) (hq7s.symm.trans hq7')
    have hq53e : q53' = q53 :=
      mul_left_cancel₀ (pow_ne_zero 3 hh0) (hq5s.symm.trans hq5')
    have hq41e : q41' = q41 :=
      mul_left_cancel₀ hh0 (hq4s.symm.trans hq4')
    simp only [hp32e, hu2e, hq53e, hq41e] at hrel1 hrel2 hrel3 hrel4 hileft
    obtain ⟨ha41z, hp2z⟩ :=
      bridgeLambda_siblingCollapse610 (a41.eval a)
        ((p.coeff 2).eval a) (q41.eval a) hG hrel2 hsplit
    have hs1z : s1.eval a = 0 := by
      have h30 : (3 : k) * s1.eval a = 0 := by
        rw [hMs, ha41z]
        ring
      exact (mul_eq_zero.mp h30).resolve_left h3ne
    have hb62z : b62.eval a = 0 := by
      linear_combination (-(1 : k) / 18) * hUz +
        ((5 : k) / 9) * a41.eval a * ha41z + ((5 : k) / 3) * hp2z
    have hq41z : q41.eval a = 0 := by
      linear_combination ((1 : k) / 81) * hrel2 +
        (((10 : k) / 9) * (p.coeff 2).eval a -
          ((5 : k) / 81) * (a41.eval a) ^ 2) * ha41z
    have hq53z : q53.eval a = 0 := by
      linear_combination ((1 : k) / 216) * hrel3 +
        (-(lambda * a41.eval a) / 8 -
          ((5 : k) / 27) * a41.eval a * w1.eval a +
          ((10 : k) / 9) * p32.eval a) * ha41z +
        (-lambda / 2 + ((10 : k) / 9) * w1.eval a) * hp2z
    have hq3z : (q.coeff 3).eval a = 0 := by
      linear_combination ((1 : k) / 3888) * hrel4 +
        (lambda * (a41.eval a) ^ 2 / 48 +
          ((20 : k) / 243) * (a41.eval a) ^ 2 * w1.eval a -
          ((5 : k) / 27) * a41.eval a * p32.eval a -
          lambda * (p.coeff 2).eval a / 4 -
          ((10 : k) / 27) * (p.coeff 2).eval a * w1.eval a) * ha41z +
        ((10 : k) / 9) * p32.eval a * hp2z
    have hu2tie : (3 : k) * u2.eval a = (5 : k) * p32.eval a := by
      linear_combination ((1 : k) / 6) * hrel1 +
        (((10 : k) / 3) * w1.eval a - ((3 : k) / 2) * lambda) * ha41z
    exact Or.inl ⟨hileft, ha41z, hp2z, hs1z, hb62z, hq41z, hq53z,
      hq3z, hu2tie⟩
  · rcases hcd with ⟨-, hp2pin, hb62pin⟩ | ⟨hnz, -⟩
    · refine Or.inr ⟨hp2pin, hb62pin, ?_⟩
      rcases bridgeLambda_complementSplit610 (a41.eval a)
          ((p.coeff 2).eval a) (q41.eval a) hG hp2pin with
        ha41z | hq41pin
      · left
        have hp2z : (p.coeff 2).eval a = 0 := by
          linear_combination ((1 : k) / 6) * hp2pin +
            ((1 : k) / 6) * a41.eval a * ha41z
        have hb62z : b62.eval a = 0 := by
          linear_combination ((1 : k) / 6) * hb62pin +
            ((5 : k) / 6) * a41.eval a * ha41z
        exact ⟨ha41z, hp2z, hb62z⟩
      · exact Or.inr hq41pin
    · exact absurd hp31z hnz

end NonzeroLambdaIntegralBridge610

end Max11DegreeRoutes
