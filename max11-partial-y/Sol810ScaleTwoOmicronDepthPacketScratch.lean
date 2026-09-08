import Sol810ScaleTwoOmicronNuProductSplitScratch

/-! # Exact depth packet for the `(8,10)` omicron right branch

This packet keeps every nu and omicron witness literally and replaces the
weaker retained divisibility alternative by the common-row depth ladder.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section OmicronDepthPacket810

variable {k : Type*} [Field k] [CharZero k]

/-- Exact right packet with the omicron/nu depth ladder on the same witnesses. -/
def bridgeOmicronDepthRightPacket810
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
        bridgeOmicronCollapsedHead810 (a41.eval a) (u2.eval a)
            (w2.eval a) (b63.eval a) (b51.eval a) (v2.eval a) = 0 ∧
        h0 ^ 2 ∣ q.coeff 5 ∧
        ((h0 ^ 2 ∣ p.coeff 4 ∧ h0 ^ 4 ∣ q.coeff 6) ∨
          (h0 ^ 4 ∣ p.coeff 5 ∧ h0 ^ 6 ∣ q.coeff 7))

/-- Upgrade an omicron right packet to the exact depth packet.  The caller
supplies the outer source equations selected by the same integral bridge. -/
theorem bridgeOmicronRightPacket_depth810
    (p q : k[X][X]) (h0 : k[X]) (lambda a : k)
    (t0 v0 u0 s0 w0 v1 s1 u1 w1 b62 : k[X])
    (hh0 : h0 ≠ 0) (hh0degree : h0.natDegree = 1)
    (hroot : h0.eval a = 0)
    (hu0 : p.coeff 5 = h0 * u0) (hu1 : u0 = h0 * u1)
    (hw0 : q.coeff 7 = h0 ^ 3 * w0) (hw1 : w0 = h0 * w1)
    (hq6 : q.coeff 6 = h0 ^ 2 * b62)
    (hright :
      bridgeOmicronRightPacket810 p q h0 lambda a t0 v0 u0 s0 w0 v1 s1
        u1 w1 b62) :
    bridgeOmicronDepthRightPacket810 p q h0 lambda a t0 v0 u0 s0 w0 v1
      s1 u1 w1 b62 := by
  unfold bridgeOmicronRightPacket810 at hright
  obtain ⟨hnuRight, t1, v2, u2, s2, w2, b63, a41, b51, ht1, hv2, hu2,
    hs2, hw2, hb63, ha41, hb51, hxires, _halt, homicron⟩ := hright
  have hdepth :=
    bridgeOmicron_nuRight_depthFourSplit810 p q h0 lambda a t0 v0 u0 s0 w0
      v1 s1 u1 w1 b62 t1 v2 u2 s2 w2 b63 a41 b51 hh0 hh0degree hroot
      ht1 hv2 hu0 hu1 hu2 hs2 hw0 hw1 hw2 hq6 hb63 ha41 hb51 hnuRight
      homicron
  unfold bridgeOmicronDepthRightPacket810
  exact ⟨hnuRight, t1, v2, u2, s2, w2, b63, a41, b51, ht1, hv2, hu2,
    hs2, hw2, hb63, ha41, hb51, hxires, homicron, hdepth⟩

end OmicronDepthPacket810

#print axioms bridgeOmicronDepthRightPacket810
#print axioms bridgeOmicronRightPacket_depth810

end Max11DegreeRoutes
