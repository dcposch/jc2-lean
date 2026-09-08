import Sol810ScaleTwoOmicronRightReductionScratch

/-! # Source-exact refined right packet after the `(8,10)` omicron bridge

The omicron packet's retained divisibility alternative is refined in place.
On `h₀² ∣ q₅`, the exact omicron witnesses give either `h₀² ∣ p₄` or
the finite three-term root wall.  The complementary
`h₀² ∣ p₄ ∧ h₀⁴ ∣ p₅` cell passes through literally.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section OmicronRightPacketRefinement810

variable {k : Type*} [Field k] [CharZero k]

/-- The same witnesses as `bridgeOmicronRightPacket810`, with its final
divisibility alternative refined by the omicron head. -/
def bridgeOmicronRightRefinedPacket810
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
        ((h0 ^ 2 ∣ q.coeff 5 ∧
            (h0 ^ 2 ∣ p.coeff 4 ∨
              (95 : k) * a41.eval a * u2.eval a -
                    (28 : k) * a41.eval a * w2.eval a -
                    (72 : k) * b63.eval a * u2.eval a = 0)) ∨
          (h0 ^ 2 ∣ p.coeff 4 ∧ h0 ^ 4 ∣ p.coeff 5))

/-- Refine the imported omicron right packet without changing any source or
witness. -/
theorem bridgeOmicronRightPacket_refined810
    (p q : k[X][X]) (h0 : k[X]) (lambda a : k)
    (t0 v0 u0 s0 w0 v1 s1 u1 w1 b62 : k[X])
    (hh0 : h0 ≠ 0) (hh0degree : h0.natDegree = 1)
    (hroot : h0.eval a = 0)
    (hright :
      bridgeOmicronRightPacket810 p q h0 lambda a t0 v0 u0 s0 w0 v1 s1
        u1 w1 b62) :
    bridgeOmicronRightRefinedPacket810 p q h0 lambda a t0 v0 u0 s0 w0 v1
      s1 u1 w1 b62 := by
  unfold bridgeOmicronRightPacket810 at hright
  obtain ⟨hnuRight, t1, v2, u2, s2, w2, b63, a41, b51, ht1, hv2, hu2,
    hs2, hw2, hb63, ha41, hb51, hxires, halt, homicron⟩ := hright
  unfold bridgeOmicronRightRefinedPacket810
  refine ⟨hnuRight, t1, v2, u2, s2, w2, b63, a41, b51, ht1, hv2, hu2,
    hs2, hw2, hb63, ha41, hb51, hxires, homicron, ?_⟩
  rcases halt with hq5deep | hp4p5deep
  · exact Or.inl ⟨hq5deep,
      bridgeOmicron_q5Deep_nextSplit810 h0 (p.coeff 4) (q.coeff 5) a41
        b51 u2 w2 b63 v2 a hh0 hh0degree hroot ha41 hb51 hq5deep
        homicron⟩
  · exact Or.inr hp4p5deep

end OmicronRightPacketRefinement810

#print axioms bridgeOmicronRightRefinedPacket810
#print axioms bridgeOmicronRightPacket_refined810

end Max11DegreeRoutes
