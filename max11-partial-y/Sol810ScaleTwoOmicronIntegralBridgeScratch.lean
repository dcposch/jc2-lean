import Sol810ScaleTwoOmicronCollapsedHeadScratch

/-! # Source-exact omicron upgrade of the `(8,10)` xi bridge

The degree-two first-integral power relation is attached to the exact
right-branch witnesses selected by the xi bridge.  The left packet is passed
through literally; the right packet gains the five-term collapsed omicron
head on those same witnesses.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000

section OmicronPackets810

variable {R : Type*} [CommRing R]

/-- Five-term root head of the collapsed weight-105 omicron quotient. -/
def bridgeOmicronCollapsedHead810
    (a41 u2 w2 b63 b51 v2 : R) : R :=
  a41 *
    (-(95 : R) * a41 ^ 2 * u2 + (28 : R) * a41 ^ 2 * w2 +
      (60 : R) * a41 * b51 * v2 + (72 : R) * a41 * b63 * u2 +
      (60 : R) * b51 * u2 ^ 2)

variable {k : Type*} [Field k] [CharZero k]

/-- Exact right packet: the imported nu packet, the same depth-two xi
witnesses and residual, the same divisibility alternative, and the new
omicron head on those witnesses. -/
def bridgeOmicronRightPacket810
    (p q : k[X][X]) (h0 : k[X]) (lambda a : k)
    (t0 v0 u0 s0 w0 v1 s1 u1 w1 b62 : k[X]) : Prop :=
  bridgeNuRightPacket810 p q h0 lambda a t0 v0 u0 s0 w0 v1 s1 u1 w1
      b62 ∧
    ∃ t1 v2 u2 s2 w2 b63 a41 b51 : k[X],
      t0 = h0 * t1 ∧ v1 = h0 * v2 ∧ u1 = h0 * u2 ∧ s1 = h0 * s2 ∧
        w1 = h0 * w2 ∧ b62 = h0 * b63 ∧ p.coeff 4 = h0 * a41 ∧
        q.coeff 5 = h0 * b51 ∧
        bridgeXiRightResidual810 (t1.eval a) (v2.eval a) (u2.eval a)
            (s2.eval a) (w2.eval a) (b63.eval a) (a41.eval a)
            (b51.eval a) ((p.coeff 3).eval a) ((q.coeff 4).eval a) =
          0 ∧
        (h0 ^ 2 ∣ q.coeff 5 ∨
          (h0 ^ 2 ∣ p.coeff 4 ∧ h0 ^ 4 ∣ p.coeff 5)) ∧
        bridgeOmicronCollapsedHead810 (a41.eval a) (u2.eval a)
            (w2.eval a) (b63.eval a) (b51.eval a) (v2.eval a) = 0

end OmicronPackets810

/-! ## Low-level source bridge -/

section OmicronSourceBridge810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 1000000000 in
/-- The xi bridge upgraded by the degree-two first integral.  Every right
witness is the one returned by xi; no existential is reselected. -/
theorem nonzeroFace810_linearRoot_omicronIntegralBridge
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
          bridgeOmicronRightPacket810 p q h0 lambda a t0 v0 u0 s0 w0
            v1 s1 u1 w1 b62) := by
  obtain ⟨t0, v0, u0, s0, w0, v1, s1, u1, w1, b62, eta, nuGround,
    xiGround, ht0, hv0, hu0, hs0, hw0, hv1, hs1, hu1, hw1, hb62, hq9d,
    hq6d, hmupow, hmupeel, hmuhead, hrow, hroweval, hnupow, hnupeel,
    hnuhead, hxipow, hxipeel, hxihead, hsplit⟩ :=
    nonzeroFace810_linearRoot_xiIntegralBridge p q H h0 j lambda a hp hq
      hh0 hh0degree hH hp8 hq10 hN hD hroot
  obtain ⟨omicronGround, homicronpow⟩ :=
    nonzeroFace810_fifteenthDefectPowerRelation p q H h0 j lambda hp hq
      hh0 hH hp8 hq10 hN hD
  refine ⟨t0, v0, u0, s0, w0, v1, s1, u1, w1, b62, eta, nuGround,
    xiGround, omicronGround, ht0, hv0, hu0, hs0, hw0, hv1, hs1, hu1,
    hw1, hb62, hq9d, hq6d, hmupow, hmupeel, hmuhead, hrow, hroweval,
    hnupow, hnupeel, hnuhead, hxipow, hxipeel, hxihead, homicronpow, ?_⟩
  rcases hsplit with hleft | hright
  · exact Or.inl hleft
  · unfold bridgeXiRightPacket810 at hright
    obtain ⟨hnuRight, t1, v2, u2, s2, w2, b63, a41, b51, ht1q, hv2q,
      hu2q, hs2q, hw2q, hb63q, ha41q, hb51q, hxires, halt⟩ := hright
    have hp7c : p.coeff 7 = h0 ^ 7 * t1 := by rw [ht0, ht1q]; ring
    have hp6c : p.coeff 6 = h0 ^ 5 * v2 := by rw [hv0, hv1, hv2q]; ring
    have hp5c : p.coeff 5 = h0 ^ 3 * u2 := by rw [hu0, hu1, hu2q]; ring
    have hq8c : q.coeff 8 = h0 ^ 7 * s2 := by rw [hs0, hs1, hs2q]; ring
    have hq7c : q.coeff 7 = h0 ^ 5 * w2 := by rw [hw0, hw1, hw2q]; ring
    have hq6c : q.coeff 6 = h0 ^ 3 * b63 := by rw [hb62, hb63q]; ring
    have homicronCollapsed := homicronpow
    rw [hp7c, hp6c, hp5c, ha41q, hq8c, hq7c, hq6c, hb51q]
      at homicronCollapsed
    have homicronHeadRaw :=
      bridgeOmicronCollapsed_head_of_power810 h0 t1 v2 u2 a41
        (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0) s2 w2 b63 b51
        (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda
        omicronGround a hh0 hroot homicronCollapsed
    have homicronHead :
        bridgeOmicronCollapsedHead810 (a41.eval a) (u2.eval a)
          (w2.eval a) (b63.eval a) (b51.eval a) (v2.eval a) = 0 := by
      simpa only [bridgeOmicronCollapsedHead810] using homicronHeadRaw
    refine Or.inr ?_
    unfold bridgeOmicronRightPacket810
    exact ⟨hnuRight, t1, v2, u2, s2, w2, b63, a41, b51, ht1q, hv2q,
      hu2q, hs2q, hw2q, hb63q, ha41q, hb51q, hxires, halt,
      homicronHead⟩

end OmicronSourceBridge810

#print axioms bridgeOmicronCollapsedHead810
#print axioms nonzeroFace810_linearRoot_omicronIntegralBridge

end Max11DegreeRoutes
