import Sol810ScaleTwoOmicronDepthPacketScratch

/-! # Source bridge carrying the `(8,10)` omicron depth packet

This is the literal omicron integral bridge with its left packet unchanged and
its exact right witnesses upgraded by the verified nu/omicron depth ladder.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section OmicronDepthBridge810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 100000000 in
/-- The source-exact omicron bridge with the stronger right depth packet. -/
theorem nonzeroFace810_linearRoot_omicronDepthBridge
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hh0degree : h0.natDegree = 1) (hH : H = h0 ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0) :
    ∃ t0 v0 u0 s0 w0 v1 s1 u1 w1 b62 : k[X],
      ∃ eta nuGround xiGround omicronGround : k,
        p.coeff 7 = h0 ^ 6 * t0 ∧ p.coeff 6 = h0 ^ 3 * v0 ∧
        p.coeff 5 = h0 * u0 ∧ q.coeff 8 = h0 ^ 5 * s0 ∧
        q.coeff 7 = h0 ^ 3 * w0 ∧ v0 = h0 * v1 ∧ s0 = h0 * s1 ∧
        u0 = h0 * u1 ∧ w0 = h0 * w1 ∧ q.coeff 6 = h0 ^ 2 * b62 ∧
        h0 ^ 8 ∣ q.coeff 9 ∧ h0 ^ 2 ∣ q.coeff 6 ∧
        terminalClearedMuDefect810 h0 (p.coeff 7) (p.coeff 6)
            (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1)
            (p.coeff 0) (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda =
          Polynomial.C eta * h0 ^ 84 ∧
        bridgeMuJetHead810 t0 v1 u1 s1 w1 b62 (p.coeff 4) (q.coeff 5) +
            h0 * bridgeMuJetTail810 h0 t0 v1 u1 s1 w1 b62 (p.coeff 4)
              (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          Polynomial.C eta * h0 ^ 12 ∧
        bridgeMuJetHead810 (t0.eval a) (v1.eval a) (u1.eval a)
            (s1.eval a) (w1.eval a) (b62.eval a) ((p.coeff 4).eval a)
            ((q.coeff 5).eval a) = 0 ∧
        (p.coeff 0).derivative * q.coeff 1 -
          p.coeff 1 * (q.coeff 0).derivative = Polynomial.C j ∧
        ((p.coeff 0).derivative).eval a * (q.coeff 1).eval a -
          (p.coeff 1).eval a * ((q.coeff 0).derivative).eval a = j ∧
        localClearedThirteenthDefect810 h0 (p.coeff 7) (p.coeff 6)
            (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1)
            (p.coeff 0) (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda =
          Polynomial.C nuGround * h0 ^ 91 ∧
        bridgeNuJetHead810 t0 v1 u1 s1 w1 b62 (p.coeff 4) (q.coeff 5) +
            h0 * bridgeNuJetTail810 h0 t0 v1 u1 s1 w1 b62 (p.coeff 4)
              (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          Polynomial.C nuGround * h0 ^ 13 ∧
        bridgeNuJetHead810 (t0.eval a) (v1.eval a) (u1.eval a)
            (s1.eval a) (w1.eval a) (b62.eval a) ((p.coeff 4).eval a)
            ((q.coeff 5).eval a) = 0 ∧
        localClearedFourteenthDefect810 h0 (p.coeff 7) (p.coeff 6)
            (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1)
            (p.coeff 0) (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda =
          Polynomial.C xiGround * h0 ^ 98 ∧
        bridgeXiJetHead810 t0 v1 u1 s1 w1 b62 (p.coeff 4) (q.coeff 5) +
            h0 * bridgeXiJetTail810 h0 t0 v1 u1 s1 w1 b62 (p.coeff 4)
              (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          Polynomial.C xiGround * h0 ^ 14 ∧
        bridgeXiJetHead810 (t0.eval a) (v1.eval a) (u1.eval a)
            (s1.eval a) (w1.eval a) (b62.eval a) ((p.coeff 4).eval a)
            ((q.coeff 5).eval a) = 0 ∧
        localClearedFifteenthDefect810 h0 (p.coeff 7) (p.coeff 6)
            (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1)
            (p.coeff 0) (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda =
          Polynomial.C omicronGround * h0 ^ 105 ∧
        (bridgeXiLeftPacket810 p q h0 lambda a t0 v0 u0 s0 w0 v1 s1
            u1 w1 b62 ∨
          bridgeOmicronDepthRightPacket810 p q h0 lambda a t0 v0 u0 s0 w0
            v1 s1 u1 w1 b62) := by
  obtain ⟨t0, v0, u0, s0, w0, v1, s1, u1, w1, b62, eta, nuGround,
    xiGround, omicronGround, ht0, hv0, hu0, hs0, hw0, hv1, hs1, hu1,
    hw1, hb62, hq9d, hq6d, hmupow, hmupeel, hmuhead, hrow, hroweval,
    hnupow, hnupeel, hnuhead, hxipow, hxipeel, hxihead, homicronpow,
    hsplit⟩ :=
    nonzeroFace810_linearRoot_omicronIntegralBridge p q H h0 j lambda a hp hq
      hh0 hh0degree hH hp8 hq10 hN hD hroot
  refine ⟨t0, v0, u0, s0, w0, v1, s1, u1, w1, b62, eta, nuGround,
    xiGround, omicronGround, ht0, hv0, hu0, hs0, hw0, hv1, hs1, hu1,
    hw1, hb62, hq9d, hq6d, hmupow, hmupeel, hmuhead, hrow, hroweval,
    hnupow, hnupeel, hnuhead, hxipow, hxipeel, hxihead, homicronpow, ?_⟩
  rcases hsplit with hleft | hright
  · exact Or.inl hleft
  · exact Or.inr
      (bridgeOmicronRightPacket_depth810 p q h0 lambda a t0 v0 u0 s0 w0
        v1 s1 u1 w1 b62 hh0 hh0degree hroot hu0 hu1 hw0 hw1 hb62 hright)

end OmicronDepthBridge810

#print axioms nonzeroFace810_linearRoot_omicronDepthBridge

end Max11DegreeRoutes
