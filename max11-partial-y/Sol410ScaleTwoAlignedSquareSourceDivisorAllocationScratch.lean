import Sol410ScaleTwoAlignedSquareSourceAllocationScratch

/-! # Global source divisors after the aligned-square root allocation -/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false

/-- Upgrade the exact tenth/eleventh root split to global divisors of the
same supplied linear `h0`.  Thus every surviving aligned-square source has
either `h0 ∣ p1`, or simultaneous deeper factors in both `u/h0` and
`p2/H`. -/
theorem normalized410ScaleTwo_alignedSquare_sourceDivisorAllocation
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H h0 : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    ∃ (x : K) (u v g r r1 : K[X]),
      h0.eval x = 0 ∧
      p.coeff 3 = h0 ^ 2 * u ∧
      u ^ 2 - (4 : K[X]) * p.coeff 2 = h0 * v ∧
      u = h0 * g ∧ p.coeff 2 = h0 * r ∧ r = h0 * r1 ∧
      ((∃ s : K[X], p.coeff 1 = h0 * s) ∨
        (∃ g1 r2 : K[X], g = h0 * g1 ∧ r1 = h0 * r2)) := by
  dsimp only at haligned ⊢
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  obtain ⟨x, u, v, g, r, r1, hx, hp3, hv, hu, hp2, hr, hdeep⟩ :=
    normalized410ScaleTwo_alignedSquare_sourceAllocation
      hsource hh0 hHsq haligned
  have hdeg : h0.natDegree = 1 := by
    have hdegree := congrArg Polynomial.natDegree hHsq
    rw [hsource.2.1, Polynomial.natDegree_pow] at hdegree
    omega
  have hrootUnique : ∀ y : K, h0.eval y = 0 → y = x := by
    obtain ⟨c, hc, d, hlinear⟩ := Polynomial.natDegree_eq_one.mp hdeg
    intro y hy
    rw [← hlinear] at hx hy
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X] at hx hy
    have hcy : c * (y - x) = 0 := by linear_combination hy - hx
    exact sub_eq_zero.mp ((mul_eq_zero.mp hcy).resolve_left hc)
  refine ⟨x, u, v, g, r, r1, hx, hp3, hv, hu, hp2, hr, ?_⟩
  rcases hdeep with hp1x | ⟨hgx, hr1x⟩
  · left
    obtain ⟨s, hs⟩ := natDegree_one_dvd_of_root_kill_410 hdeg (fun y hy => by
      rw [hrootUnique y hy]
      exact hp1x)
    exact ⟨s, hs⟩
  · right
    obtain ⟨g1, hg⟩ := natDegree_one_dvd_of_root_kill_410 hdeg (fun y hy => by
      rw [hrootUnique y hy]
      exact hgx)
    obtain ⟨r2, hr1⟩ := natDegree_one_dvd_of_root_kill_410 hdeg (fun y hy => by
      rw [hrootUnique y hy]
      exact hr1x)
    exact ⟨g1, r2, hg, hr1⟩

#print axioms normalized410ScaleTwo_alignedSquare_sourceDivisorAllocation

end Max11DegreeRoutes
