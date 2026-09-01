import Sol410ScaleTwoAlignedFinalRootSplitScratch

/-! # Two-root allocation of the aligned `(4,10)` nonsquare terminal product

The terminal perfect cube now holds at every root of the simple quadratic
core.  Its two factors therefore allocate across the two actual roots: one
factor carries the whole core, or the factors occur in one of the two exact
transverse orientations.  No X-degree bound is used.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false

section RootAllocationAlgebra410

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- A simple degree-two polynomial has two distinct roots. -/
theorem alignedFinal_rootPair_exists410
    (H : K[X]) (hdeg : H.natDegree = 2)
    (hsimple : ∀ x : K, H.eval x = 0 → H.derivative.eval x ≠ 0) :
    ∃ x y : K, x ≠ y ∧ H.eval x = 0 ∧ H.eval y = 0 := by
  have hH : H ≠ 0 := by
    rintro rfl
    simp at hdeg
  have hdegne : H.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hH, hdeg]
    decide
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root H hdegne
  have hx' : H.eval x = 0 := hx
  have hlin : Polynomial.X - Polynomial.C x ∣ H := by
    rw [Polynomial.dvd_iff_isRoot]
    exact hx'
  obtain ⟨H1, hH1⟩ := hlin
  have hH1ne : H1 ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hH1
    exact hH hH1
  have hH1deg : H1.natDegree = 1 := by
    have hmul : H.natDegree =
        (Polynomial.X - Polynomial.C x : K[X]).natDegree + H1.natDegree := by
      rw [hH1]
      exact Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero x) hH1ne
    simp only [Polynomial.natDegree_X_sub_C] at hmul
    rw [hdeg] at hmul
    omega
  have hH1degne : H1.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hH1ne, hH1deg]
    decide
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root H1 hH1degne
  have hy1 : H1.eval y = 0 := hy
  have hyH : H.eval y = 0 := by
    rw [hH1, Polynomial.eval_mul, hy1, mul_zero]
  refine ⟨x, y, ?_, hx', hyH⟩
  intro hxy
  rw [← hxy] at hy1
  apply hsimple x hx'
  have hd1 : H.derivative = H1 +
      (Polynomial.X - Polynomial.C x) * H1.derivative := by
    rw [hH1, Polynomial.derivative_mul, Polynomial.derivative_sub,
      Polynomial.derivative_X, Polynomial.derivative_C]
    ring
  have hev := congrArg (fun P : K[X] => P.eval x) hd1
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, sub_self,
    zero_mul, add_zero] at hev
  rw [hev]
  exact hy1

/-- The two supplied distinct roots exhaust a degree-two polynomial. -/
theorem alignedFinal_natDegreeTwo_rootsExhaust410
    (H : K[X]) (hdeg : H.natDegree = 2) (x y z : K) (hxy : x ≠ y)
    (hx : H.eval x = 0) (hy : H.eval y = 0) (hz : H.eval z = 0) :
    z = x ∨ z = y := by
  have hH : H ≠ 0 := by
    rintro rfl
    simp at hdeg
  have hlinX : Polynomial.X - Polynomial.C x ∣ H := by
    rw [Polynomial.dvd_iff_isRoot]
    exact hx
  obtain ⟨H1, hH1⟩ := hlinX
  have hH1y : H1.eval y = 0 := by
    have hev := congrArg (fun P : K[X] => P.eval y) hH1
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C] at hev
    rw [hy] at hev
    exact (mul_eq_zero.mp hev.symm).resolve_left
      (sub_ne_zero.mpr (Ne.symm hxy))
  have hlinY : Polynomial.X - Polynomial.C y ∣ H1 := by
    rw [Polynomial.dvd_iff_isRoot]
    exact hH1y
  obtain ⟨H2, hH2⟩ := hlinY
  have hfull : H = (Polynomial.X - Polynomial.C x) *
      ((Polynomial.X - Polynomial.C y) * H2) := by
    rw [hH1, hH2]
  have hH2ne : H2 ≠ 0 := by
    rintro rfl
    rw [mul_zero, mul_zero] at hfull
    exact hH hfull
  have hH2deg : H2.natDegree = 0 := by
    have hX : (Polynomial.X - Polynomial.C x : K[X]) ≠ 0 :=
      Polynomial.X_sub_C_ne_zero x
    have hY : (Polynomial.X - Polynomial.C y : K[X]) ≠ 0 :=
      Polynomial.X_sub_C_ne_zero y
    have hmul : H.natDegree =
        (Polynomial.X - Polynomial.C x : K[X]).natDegree +
          ((Polynomial.X - Polynomial.C y) * H2).natDegree := by
      rw [hfull]
      exact Polynomial.natDegree_mul hX (mul_ne_zero hY hH2ne)
    rw [Polynomial.natDegree_mul hY hH2ne] at hmul
    simp only [Polynomial.natDegree_X_sub_C] at hmul
    rw [hdeg] at hmul
    omega
  have hH2z : H2.eval z ≠ 0 := by
    intro hzero
    apply hH2ne
    have hconst := Polynomial.eq_C_of_natDegree_eq_zero hH2deg
    rw [hconst] at hzero
    rw [Polynomial.eval_C] at hzero
    rw [hconst, hzero, Polynomial.C_0]
  have hev := congrArg (fun P : K[X] => P.eval z) hfull
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C] at hev
  rw [hz] at hev
  rcases mul_eq_zero.mp hev.symm with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · rcases mul_eq_zero.mp h with h' | h'
    · exact Or.inr (sub_eq_zero.mp h')
    · exact absurd h' hH2z

/-- Two zero evaluations, one at each simple quadratic root, globalize to
divisibility by the quadratic core. -/
theorem alignedFinal_dvd_of_twoRootEvals410
    (H R : K[X]) (hdeg : H.natDegree = 2)
    (hsimple : ∀ z : K, H.eval z = 0 → H.derivative.eval z ≠ 0)
    (x y : K) (hxy : x ≠ y) (hx : H.eval x = 0) (hy : H.eval y = 0)
    (hRx : R.eval x = 0) (hRy : R.eval y = 0) : H ∣ R := by
  apply dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple
  intro z hz
  rcases alignedFinal_natDegreeTwo_rootsExhaust410
      H hdeg x y z hxy hx hy hz with rfl | rfl
  · exact hRx
  · exact hRy

/-- Remove the harmless cubes from the terminal product. -/
theorem alignedFinal_cubeProduct_base410 (a b : K)
    (h : a ^ 3 * b ^ 3 = 0) : a * b = 0 := by
  rcases mul_eq_zero.mp h with ha | hb
  · rw [(pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp ha, zero_mul]
  · rw [(pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp hb, mul_zero]

/-- Allocate a two-factor product across the two simple roots. -/
theorem alignedFinal_twoRootProduct_allocation410
    (H R S : K[X]) (hdeg : H.natDegree = 2)
    (hsimple : ∀ z : K, H.eval z = 0 → H.derivative.eval z ≠ 0)
    (x y : K) (hxy : x ≠ y) (hx : H.eval x = 0) (hy : H.eval y = 0)
    (hpx : R.eval x * S.eval x = 0)
    (hpy : R.eval y * S.eval y = 0) :
    H ∣ R ∨ H ∣ S ∨
      ((R.eval x = 0 ∧ S.eval x ≠ 0 ∧
          R.eval y ≠ 0 ∧ S.eval y = 0) ∨
        (R.eval x ≠ 0 ∧ S.eval x = 0 ∧
          R.eval y = 0 ∧ S.eval y ≠ 0)) := by
  by_cases hRx : R.eval x = 0
  · by_cases hRy : R.eval y = 0
    · exact Or.inl (alignedFinal_dvd_of_twoRootEvals410
        H R hdeg hsimple x y hxy hx hy hRx hRy)
    · have hSy : S.eval y = 0 := (mul_eq_zero.mp hpy).resolve_left hRy
      by_cases hSx : S.eval x = 0
      · exact Or.inr (Or.inl (alignedFinal_dvd_of_twoRootEvals410
          H S hdeg hsimple x y hxy hx hy hSx hSy))
      · exact Or.inr (Or.inr (Or.inl ⟨hRx, hSx, hRy, hSy⟩))
  · have hSx : S.eval x = 0 := (mul_eq_zero.mp hpx).resolve_left hRx
    by_cases hRy : R.eval y = 0
    · by_cases hSy : S.eval y = 0
      · exact Or.inr (Or.inl (alignedFinal_dvd_of_twoRootEvals410
          H S hdeg hsimple x y hxy hx hy hSx hSy))
      · exact Or.inr (Or.inr (Or.inr ⟨hRx, hSx, hRy, hSy⟩))
    · have hSy : S.eval y = 0 := (mul_eq_zero.mp hpy).resolve_left hRy
      exact Or.inr (Or.inl (alignedFinal_dvd_of_twoRootEvals410
        H S hdeg hsimple x y hxy hx hy hSx hSy))

end RootAllocationAlgebra410

set_option maxHeartbeats 3000000 in
/-- Source-facing allocation of the terminal nonsquare product, retaining the
same quotient witnesses from the aligned tower. -/
theorem normalized410ScaleTwo_alignedNonsquare_rootAllocation
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (g f : K[X]) (x y : K), x ≠ y ∧ H.eval x = 0 ∧ H.eval y = 0 ∧
      p.coeff 3 = H * g ∧
      g ^ 2 - (4 : K[X]) * p.coeff 2 = H * f ∧
      let L := g * f + (8 : K[X]) * p.coeff 1
      H ∣ g ∨ H ∣ L ∨
        ((g.eval x = 0 ∧ L.eval x ≠ 0 ∧
            g.eval y ≠ 0 ∧ L.eval y = 0) ∨
          (g.eval x ≠ 0 ∧ L.eval x = 0 ∧
            g.eval y = 0 ∧ L.eval y ≠ 0)) := by
  dsimp only at haligned ⊢
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  obtain ⟨g, f, hp3, hgf, hall⟩ :=
    normalized410ScaleTwo_alignedNonsquare_allRootProduct
      hsource hnsq haligned
  have hdeg : H.natDegree = 2 := hsource.2.1
  have hsimple : ∀ z : K, H.eval z = 0 → H.derivative.eval z ≠ 0 :=
    fun z hz => nonsquare_natDegree_two_derivative_ne_zero hdeg hnsq hz
  obtain ⟨x, y, hxy, hx, hy⟩ :=
    alignedFinal_rootPair_exists410 H hdeg hsimple
  let L : K[X] := g * f + (8 : K[X]) * p.coeff 1
  have hpx : g.eval x * L.eval x = 0 := by
    apply alignedFinal_cubeProduct_base410
    simpa only [L, p, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_ofNat] using hall x hx
  have hpy : g.eval y * L.eval y = 0 := by
    apply alignedFinal_cubeProduct_base410
    simpa only [L, p, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_ofNat] using hall y hy
  exact ⟨g, f, x, y, hxy, hx, hy, hp3, hgf,
    alignedFinal_twoRootProduct_allocation410
      H g L hdeg hsimple x y hxy hx hy hpx hpy⟩

#print axioms alignedFinal_rootPair_exists410
#print axioms alignedFinal_twoRootProduct_allocation410
#print axioms normalized410ScaleTwo_alignedNonsquare_rootAllocation

end Max11DegreeRoutes
