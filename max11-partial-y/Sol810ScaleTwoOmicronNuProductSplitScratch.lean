import Sol810ScaleTwoOmicronNuCommonRowsScratch

/-! # Product and divisibility split from the `(8,10)` omicron/nu rows

The common nu rows first force `h₀² ∣ q₅`.  Together with the omicron
head they force `b₆₃(a) * u₂(a) = 0`.  In the first cell the common
affine row also forces `a₄₁(a)=0`.  Factoring the selected linear polynomial
at that same root upgrades the exact source equations to
`(h₀² ∣ p₄ ∧ h₀⁴ ∣ q₆) ∨
 (h₀⁴ ∣ p₅ ∧ h₀⁶ ∣ q₇)`.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section OmicronNuProductSplit810

variable {k : Type*} [Field k] [CharZero k]

/-- Source-exact deeper-`q₅` fact and depth-four split on the omicron right
branch. -/
theorem bridgeOmicron_nuRight_depthFourSplit810
    (p q : k[X][X]) (h0 : k[X]) (lambda a : k)
    (t0 v0 u0 s0 w0 v1 s1 u1 w1 b62 : k[X])
    (t1 v2 u2 s2 w2 b63 a41 b51 : k[X])
    (hh0 : h0 ≠ 0) (hh0degree : h0.natDegree = 1)
    (hroot : h0.eval a = 0)
    (ht1 : t0 = h0 * t1) (hv2 : v1 = h0 * v2)
    (hu0 : p.coeff 5 = h0 * u0) (hu1 : u0 = h0 * u1)
    (hu2 : u1 = h0 * u2) (hs2 : s1 = h0 * s2)
    (hw0 : q.coeff 7 = h0 ^ 3 * w0) (hw1 : w0 = h0 * w1)
    (hw2 : w1 = h0 * w2)
    (hq6 : q.coeff 6 = h0 ^ 2 * b62) (hb63 : b62 = h0 * b63)
    (ha41 : p.coeff 4 = h0 * a41) (hb51 : q.coeff 5 = h0 * b51)
    (hnu :
      bridgeNuRightPacket810 p q h0 lambda a t0 v0 u0 s0 w0 v1 s1 u1 w1
        b62)
    (hhead :
      bridgeOmicronCollapsedHead810 (a41.eval a) (u2.eval a)
          (w2.eval a) (b63.eval a) (b51.eval a) (v2.eval a) = 0) :
    h0 ^ 2 ∣ q.coeff 5 ∧
      ((h0 ^ 2 ∣ p.coeff 4 ∧ h0 ^ 4 ∣ q.coeff 6) ∨
        (h0 ^ 4 ∣ p.coeff 5 ∧ h0 ^ 6 ∣ q.coeff 7)) := by
  obtain ⟨hb51root, hwroot, habroot⟩ :=
    bridgeOmicron_nuRight_commonRows810 p q h0 lambda a t0 v0 u0 s0 w0
      v1 s1 u1 w1 b62 t1 v2 u2 s2 w2 b63 a41 b51 hh0 hroot ht1 hv2
      hu2 hs2 hw2 hb63 ha41 hb51 hnu
  have hq5deep : h0 ^ 2 ∣ q.coeff 5 := by
    obtain ⟨b52, hb52⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0 b51 a hh0degree hroot
        hb51root
    refine ⟨b52, ?_⟩
    rw [hb51, hb52]
    ring
  refine ⟨hq5deep, ?_⟩
  have hproduct : b63.eval a * u2.eval a = 0 :=
    bridgeOmicronCollapsedHead_commonRows810 (a41.eval a) (u2.eval a)
      (w2.eval a) (b63.eval a) (b51.eval a) (v2.eval a) hb51root
      hwroot habroot hhead
  rcases mul_eq_zero.mp hproduct with hb63root | hu2root
  · left
    have ha41root : a41.eval a = 0 := by
      linear_combination (1 / 40 : k) * habroot +
        (4 / 5 : k) * hb63root
    obtain ⟨a42, ha42⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0 a41 a hh0degree hroot
        ha41root
    obtain ⟨b64, hb64⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0 b63 a hh0degree hroot
        hb63root
    constructor
    · refine ⟨a42, ?_⟩
      rw [ha41, ha42]
      ring
    · refine ⟨b64, ?_⟩
      rw [hq6, hb63, hb64]
      ring
  · right
    have hw2root : w2.eval a = 0 := by
      linear_combination (1 / 32 : k) * hwroot +
        (5 / 4 : k) * hu2root
    obtain ⟨u3, hu3⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0 u2 a hh0degree hroot
        hu2root
    obtain ⟨w3, hw3⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0 w2 a hh0degree hroot
        hw2root
    constructor
    · refine ⟨u3, ?_⟩
      rw [hu0, hu1, hu2, hu3]
      ring
    · refine ⟨w3, ?_⟩
      rw [hw0, hw1, hw2, hw3]
      ring

end OmicronNuProductSplit810

#print axioms bridgeOmicron_nuRight_depthFourSplit810

end Max11DegreeRoutes
