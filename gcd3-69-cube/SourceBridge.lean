import ArbitraryLoads

noncomputable section

universe u

/-! # First source-to-trajectory bridge

This module begins the non-circular producer required before the finite
landing theorem can be applied to a cube-core source.  Its input is the actual
leading Faber point and the four vanishing invariant equations, not a choice
of landing constructor.  The output is the exhaustive common-cubic versus
Davenport--Stothers component split, with projective nonvanishing derived
internally.
-/

/-- A nonzero leading coefficient point satisfying the four exact zero-high
Faber equations. -/
structure GCD369CubeLeadingFaberSource (K : Type u) [Field K] where
  a0 : K
  a1 : K
  a2 : K
  a3 : K
  a4 : K
  hnonzero : a0 ≠ 0 ∨ a1 ≠ 0 ∨ a2 ≠ 0 ∨ a3 ≠ 0 ∨ a4 ≠ 0
  hr1 : GCD369CubeFaberR1 a0 a1 a2 a3 a4 0 0 0 0 0 0 0 = 0
  hr2 : GCD369CubeFaberR2 a0 a1 a2 a3 a4 0 0 0 0 0 0 0 = 0
  hr3 : GCD369CubeFaberR3 a0 a1 a2 a3 a4 0 0 0 0 0 0 0 = 0
  hr4 : GCD369CubeFaberR4 a0 a1 a2 a3 a4 0 0 0 0 0 0 0 = 0

/-- The two reduced projective components of the leading Faber source. -/
inductive GCD369CubeLeadingComponent {K : Type u} [Field K]
    (a0 a1 a2 a3 a4 : K) : Prop where
  | common (u v : K) (hprojective : u ≠ 0 ∨ v ≠ 0)
      (ha4 : a4 = 2 * u) (ha3 : a3 = 2 * v) (ha2 : a2 = u ^ 2)
      (ha1 : a1 = 2 * u * v) (ha0 : a0 = v ^ 2)
  | davenportStothers (lambda : K) (hlambda : lambda ≠ 0)
      (ha4 : a4 = 4 * lambda) (ha3 : a3 = 0)
      (ha2 : a2 = 10 * lambda ^ 2) (ha1 : a1 = 0)
      (ha0 : a0 = 6 * lambda ^ 3)

/-- Exact source equations produce one of the two projective leading
components.  Neither component is selected or assumed by the caller. -/
theorem GCD369CubeLeadingFaberSource.toComponent
    {K : Type u} [Field K] [CharZero K]
    (S : GCD369CubeLeadingFaberSource K) :
    GCD369CubeLeadingComponent S.a0 S.a1 S.a2 S.a3 S.a4 := by
  rcases GCD369CubeFaberLeadingComponentClassification
      S.a0 S.a1 S.a2 S.a3 S.a4 S.hr1 S.hr2 S.hr3 S.hr4 with
    hcommon | hds
  · rcases hcommon with ⟨u, v, ha4, ha3, ha2, ha1, ha0⟩
    have hprojective : u ≠ 0 ∨ v ≠ 0 := by
      by_contra huv
      push Not at huv
      rcases huv with ⟨hu, hv⟩
      have hnonzero := S.hnonzero
      rw [ha0, ha1, ha2, ha3, ha4] at hnonzero
      simp [hu, hv] at hnonzero
    exact .common u v hprojective ha4 ha3 ha2 ha1 ha0
  · rcases hds with ⟨lambda, ha4, ha3, ha2, ha1, ha0⟩
    have hlambda : lambda ≠ 0 := by
      intro hlambda
      have hnonzero := S.hnonzero
      rw [ha0, ha1, ha2, ha3, ha4] at hnonzero
      simp [hlambda] at hnonzero
    exact .davenportStothers lambda hlambda ha4 ha3 ha2 ha1 ha0

#print axioms GCD369CubeLeadingFaberSource.toComponent
