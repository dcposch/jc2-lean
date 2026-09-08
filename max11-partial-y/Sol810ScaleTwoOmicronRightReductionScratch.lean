import Sol810ScaleTwoOmicronIntegralBridgeScratch

/-! # First exact right-branch reduction after the `(8,10)` omicron bridge

On the `h₀² ∣ q₅` alternative, the exact witness equation
`q₅ = h₀ b₅₁` forces `b₅₁` to vanish at the selected root.  The omicron head
then says either `a₄₁` vanishes there as well (and hence `h₀² ∣ p₄`), or the
remaining three-term scalar wall is zero.  All witnesses are supplied by the
caller; none is reselected.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section OmicronRightReduction810

variable {k : Type*} [Field k] [CharZero k]

/-- With the `b₅₁` root value zero, the five-term omicron head is exactly a
square factor times its three-term successor wall. -/
theorem bridgeOmicronCollapsedHead_q5Deep810
    (a41 u2 w2 b63 b51 v2 : k)
    (hb51 : b51 = 0)
    (hhead :
      bridgeOmicronCollapsedHead810 a41 u2 w2 b63 b51 v2 = 0) :
    a41 ^ 2 *
        ((95 : k) * a41 * u2 - (28 : k) * a41 * w2 -
          (72 : k) * b63 * u2) = 0 := by
  simp only [bridgeOmicronCollapsedHead810, hb51, mul_zero, zero_mul,
    add_zero] at hhead
  linear_combination -hhead

/-- Scalar split of the reduced omicron head. -/
theorem bridgeOmicronCollapsedHead_q5Deep_split810
    (a41 u2 w2 b63 b51 v2 : k)
    (hb51 : b51 = 0)
    (hhead :
      bridgeOmicronCollapsedHead810 a41 u2 w2 b63 b51 v2 = 0) :
    a41 = 0 ∨
      (95 : k) * a41 * u2 - (28 : k) * a41 * w2 -
          (72 : k) * b63 * u2 = 0 := by
  have hred :=
    bridgeOmicronCollapsedHead_q5Deep810 a41 u2 w2 b63 b51 v2
      hb51 hhead
  rcases mul_eq_zero.mp hred with ha41sq | hwall
  · exact Or.inl (eq_zero_of_pow_eq_zero ha41sq)
  · exact Or.inr hwall

/-- The three common right-packet rows turn the reduced omicron wall into the
next product split.  This is a scalar certificate only; the source transport
of the three rows is kept separate. -/
theorem bridgeOmicronCollapsedHead_commonRows810
    (a41 u2 w2 b63 b51 v2 : k)
    (hb51 : b51 = 0)
    (hw : (32 : k) * w2 - (40 : k) * u2 = 0)
    (hab : (40 : k) * a41 - (32 : k) * b63 = 0)
    (hhead :
      bridgeOmicronCollapsedHead810 a41 u2 w2 b63 b51 v2 = 0) :
    b63 * u2 = 0 := by
  rcases bridgeOmicronCollapsedHead_q5Deep_split810
      a41 u2 w2 b63 b51 v2 hb51 hhead with ha41 | hwall
  · have hb63 : b63 = 0 := by
      linear_combination (-1 / 32 : k) * hab + (5 / 4 : k) * ha41
    rw [hb63, zero_mul]
  · linear_combination
      (1 / 16 : k) * u2 * hab -
      (7 / 192 : k) * a41 * hw -
      (1 / 24 : k) * hwall

/-- Exact cancellation of one nonzero `h₀` factor: deeper divisibility of
`q₅ = h₀ b₅₁` makes the supplied `b₅₁` witness vanish at the selected root. -/
theorem bridgeOmicron_b51_root_of_q5Deep810
    (h0 q5 b51 : k[X]) (a : k)
    (hh0 : h0 ≠ 0) (hroot : h0.eval a = 0)
    (hq5 : q5 = h0 * b51) (hq5deep : h0 ^ 2 ∣ q5) :
    b51.eval a = 0 := by
  obtain ⟨b52, hb52⟩ := hq5deep
  have hcancel : h0 * b51 = h0 * (h0 * b52) := by
    rw [← hq5, hb52]
    ring
  have hb51 : b51 = h0 * b52 := mul_left_cancel₀ hh0 hcancel
  rw [hb51, Polynomial.eval_mul, hroot, zero_mul]

/-- Source-exact next split on the deep-`q₅` omicron branch.  The first
cell upgrades the caller's exact `p₄ = h₀ a₄₁` equation to
`h₀² ∣ p₄`; the other cell is the finite three-term scalar wall. -/
theorem bridgeOmicron_q5Deep_nextSplit810
    (h0 p4 q5 a41 b51 u2 w2 b63 v2 : k[X]) (a : k)
    (hh0 : h0 ≠ 0) (hh0degree : h0.natDegree = 1)
    (hroot : h0.eval a = 0)
    (hp4 : p4 = h0 * a41) (hq5 : q5 = h0 * b51)
    (hq5deep : h0 ^ 2 ∣ q5)
    (hhead :
      bridgeOmicronCollapsedHead810 (a41.eval a) (u2.eval a)
          (w2.eval a) (b63.eval a) (b51.eval a) (v2.eval a) = 0) :
    h0 ^ 2 ∣ p4 ∨
      (95 : k) * a41.eval a * u2.eval a -
          (28 : k) * a41.eval a * w2.eval a -
          (72 : k) * b63.eval a * u2.eval a = 0 := by
  have hb51root : b51.eval a = 0 :=
    bridgeOmicron_b51_root_of_q5Deep810 h0 q5 b51 a hh0 hroot hq5 hq5deep
  rcases bridgeOmicronCollapsedHead_q5Deep_split810
      (a41.eval a) (u2.eval a) (w2.eval a) (b63.eval a)
      (b51.eval a) (v2.eval a) hb51root hhead with ha41root | hwall
  · left
    obtain ⟨a42, ha42⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0 a41 a hh0degree hroot
        ha41root
    refine ⟨a42, ?_⟩
    rw [hp4, ha42]
    ring
  · exact Or.inr hwall

end OmicronRightReduction810

#print axioms bridgeOmicronCollapsedHead_q5Deep810
#print axioms bridgeOmicronCollapsedHead_q5Deep_split810
#print axioms bridgeOmicronCollapsedHead_commonRows810
#print axioms bridgeOmicron_b51_root_of_q5Deep810
#print axioms bridgeOmicron_q5Deep_nextSplit810

end Max11DegreeRoutes
