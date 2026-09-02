import Sol68ScaleTwoAlignedSquareTerminalGBoundaryCapI4SixteenBackwireScratch

/-! # Exact epsilon split after the restored I₃[12]/I₄[16] cross -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareTerminalGBoundaryCapI4SixteenClassification68

variable {k : Type*} [Field k] [CharZero k]

/-- The two restored rows have a sharp scalar normal form.  At epsilon zero,
the reduced I₃ core is the nonzero prescribed `ABF/3` scalar and the I₄
core vanishes.  At epsilon nonzero, the earlier honest split says that either
the reduced I₃ core or `C[12]` is nonzero. -/
theorem rhoOneI3I4_cap_sixteen_epsilon_classification68
    (a b f x y epsilon c12 b16 : k)
    (h3 : -(4 / 3 : k) * a * b * f + 4 * x + 3 * epsilon * c12 = 0)
    (hsplit : x ≠ 0 ∨ (epsilon ≠ 0 ∧ c12 ≠ 0))
    (h4 : 4 * y + 3 * epsilon * b16 = 0) :
    (epsilon = 0 ∧ x = (1 / 3 : k) * a * b * f ∧ y = 0 ∧ x ≠ 0) ∨
      (epsilon ≠ 0 ∧ (x ≠ 0 ∨ c12 ≠ 0)) := by
  by_cases he : epsilon = 0
  · left
    have hx : x = (1 / 3 : k) * a * b * f := by
      rw [he] at h3
      linear_combination (1 / 4 : k) * h3
    have hy : y = 0 := by
      rw [he] at h4
      linear_combination (1 / 4 : k) * h4
    have hxne : x ≠ 0 := by
      rcases hsplit with hxne | hload
      · exact hxne
      · exact (hload.1 he).elim
    exact ⟨he, hx, hy, hxne⟩
  · right
    refine ⟨he, ?_⟩
    rcases hsplit with hxne | hload
    · exact Or.inl hxne
    · exact Or.inr hload.2

/-- Packet-level form, directly reusable by every source-facing successor. -/
theorem RhoOneDoubleZeroTerminalGBoundaryCapI4SixteenPacket68.epsilon_classification
    {gamma epsilon i3 sold cs source0 source1 source2 : k}
    {A B C F G dA : HahnSeries ℚ k}
    (P : RhoOneDoubleZeroTerminalGBoundaryCapI4SixteenPacket68
      gamma epsilon i3 sold cs source0 source1 source2 A B C F G dA) :
    (epsilon = 0 ∧
        rhoOneI3CapTwelveReducedCore68 C F G =
          (1 / 3 : k) * A.coeff (-2 : ℚ) * B.coeff 11 * F.coeff 3 ∧
        rhoOneI4CapSixteenCore68 B C F G = 0 ∧
        rhoOneI3CapTwelveReducedCore68 C F G ≠ 0) ∨
      (epsilon ≠ 0 ∧
        (rhoOneI3CapTwelveReducedCore68 C F G ≠ 0 ∨ C.coeff 12 ≠ 0)) := by
  have h3 := P.1.2.1
  have hsplit := P.1.2.2
  have h4 := P.2.1
  apply rhoOneI3I4_cap_sixteen_epsilon_classification68
    (A.coeff (-2 : ℚ)) (B.coeff 11) (F.coeff 3)
    (rhoOneI3CapTwelveReducedCore68 C F G)
    (rhoOneI4CapSixteenCore68 B C F G) epsilon
    (C.coeff 12) (B.coeff 16)
  · dsimp only [RhoOneDoubleZeroTerminalGBoundaryCapI3TwelveRestoredTarget68,
      rhoOneI3CapTwelveRestoredCore68,
      rhoOneI3CapTwelveReducedCore68] at h3 ⊢
    exact h3
  · exact hsplit
  · exact h4

end AlignedSquareTerminalGBoundaryCapI4SixteenClassification68

end Max11DegreeRoutes
