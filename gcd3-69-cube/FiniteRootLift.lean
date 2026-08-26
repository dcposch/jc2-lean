import FiniteActiveSource

/-! # Singular common-root lifting identities

The first zero-load transverse jet can survive only over a double-root
common cubic.  This file records the exact Taylor identities and the two
possible residue roots used by the next Hahn-order lifting step.  No root is
constructed: the recovered source coordinate already supplies it.
-/

noncomputable section

/-- Taylor expansion of a depressed cubic at its double root. -/
theorem GCD369CubeSingularCubic_taylor_double
    {R : Type*} [CommRing R] (x U V r : R) :
    x ^ 3 + U * x + V =
      3 * r * (x - r) ^ 2 + (x - r) ^ 3 +
        (U + 3 * r ^ 2) * x + (V - 2 * r ^ 3) := by
  ring

/-- Taylor expansion of a depressed cubic at its other, simple root. -/
theorem GCD369CubeSingularCubic_taylor_simple
    {R : Type*} [CommRing R] (x U V r : R) :
    x ^ 3 + U * x + V =
      9 * r ^ 2 * (x + 2 * r) - 6 * r * (x + 2 * r) ^ 2 +
        (x + 2 * r) ^ 3 + (U + 3 * r ^ 2) * x +
          (V - 2 * r ^ 3) := by
  ring

/-- Exact expansion of a transverse quadratic around the singular tangent
normal. -/
theorem GCD369CubeSingularNormal_factor
    {R : Type*} [CommRing R] (x Xn Yn Zn r : R) :
    Xn * x ^ 2 + Yn * x + Zn =
      Xn * (x - r) * (x + 2 * r) +
        (Yn - r * Xn) * x + (Zn + 2 * r ^ 2 * Xn) := by
  ring

/-- A projective singular cubic has a nonzero double-root parameter. -/
theorem GCD369CubeSingularParameter_ne_zero
    {K : Type*} [Field K] [CharZero K]
    (u v r : K) (hprojective : u ≠ 0 ∨ v ≠ 0)
    (hu : u = -3 * r ^ 2) (hv : v = 2 * r ^ 3) : r ≠ 0 := by
  intro hr
  rcases hprojective with hu0 | hv0
  · apply hu0
    rw [hu, hr]
    norm_num
  · apply hv0
    rw [hv, hr]
    norm_num

/-- The only roots of the singular depressed cubic are its double root and
the remaining simple root. -/
theorem GCD369CubeSingularCubic_root_cases
    {K : Type*} [Field K] [CharZero K]
    (x u v r : K) (hu : u = -3 * r ^ 2) (hv : v = 2 * r ^ 3)
    (hx : x ^ 3 + u * x + v = 0) : x = r ∨ x = -2 * r := by
  have hfactor : (x - r) ^ 2 * (x + 2 * r) = 0 := by
    calc
      (x - r) ^ 2 * (x + 2 * r) = x ^ 3 + u * x + v := by
        rw [hu, hv]
        ring
      _ = 0 := hx
  rcases mul_eq_zero.mp hfactor with hdouble | hsimple
  · left
    exact sub_eq_zero.mp ((sq_eq_zero_iff).mp hdouble)
  · right
    linear_combination hsimple

/-- Both residue roots of the singular cubic annihilate its distinguished
zero-load transverse normal. -/
theorem GCD369CubeSingularNormal_root_zero
    {K : Type*} [Field K] [CharZero K]
    (x Xn Yn Zn r : K) (hY : Yn = r * Xn)
    (hZ : Zn = -2 * r ^ 2 * Xn) (hx : x = r ∨ x = -2 * r) :
    Xn * x ^ 2 + Yn * x + Zn = 0 := by
  rcases hx with hx | hx
  · rw [hx, hY, hZ]
    ring
  · rw [hx, hY, hZ]
    ring

/-- The classified nonzero zero-load jet determines a nonzero singular
parameter, and every recovered cubic residue root is one of its two roots
and annihilates the transverse normal. -/
theorem GCD369CubeZeroLoadNormal_root_data
    {K : Type*} [Field K] [CharZero K]
    (Xn Yn Zn u v x : K)
    (hprojective : u ≠ 0 ∨ v ≠ 0)
    (hnonzero : Xn ≠ 0 ∨ Yn ≠ 0 ∨ Zn ≠ 0)
    (h1 : GCD369CubeNormalRow1 Xn Yn Zn u = 0)
    (h2 : GCD369CubeNormalRow2 Xn Yn Zn u v = 0)
    (h3 : GCD369CubeNormalRow3 Xn Yn Zn u v = 0)
    (h4 : GCD369CubeNormalRow4 Xn Yn Zn u v = 0)
    (hx : x ^ 3 + u * x + v = 0) :
    ∃ r : K, r ≠ 0 ∧ Xn ≠ 0 ∧
      u = -3 * r ^ 2 ∧ v = 2 * r ^ 3 ∧
      Yn = r * Xn ∧ Zn = -2 * r ^ 2 * Xn ∧
      (x = r ∨ x = -2 * r) ∧
      Xn * x ^ 2 + Yn * x + Zn = 0 := by
  obtain ⟨r, hX, hu, hv, hY, hZ⟩ :=
    GCD369CubeZeroLoadNormal_parametrization
      Xn Yn Zn u v hnonzero h1 h2 h3 h4
  have hr := GCD369CubeSingularParameter_ne_zero
    u v r hprojective hu hv
  have hroot := GCD369CubeSingularCubic_root_cases x u v r hu hv hx
  exact ⟨r, hr, hX, hu, hv, hY, hZ, hroot,
    GCD369CubeSingularNormal_root_zero x Xn Yn Zn r hY hZ hroot⟩

namespace GCD369CubeHahnCommonValueData

/-- Once the three normal coordinates reach half the weight-one pole scale,
the four literal scaled Faber equations produce the exact arbitrary-`d`
Kuranishi packet on their residues. -/
theorem dLeadingFaberRowsAt_of_bounds
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubeHahnCommonValueData k)
    (F : GCD369CubeHahnFaberPoleData k)
    (hscale : S.normal.sextic.scale = F.scale)
    (D C7 C5 C4 C3 C2 C1 R1 R2 R3 R4 : k)
    (hd : F.d = GCD369CubeHahnRegular.constant D)
    (hc7 : F.c7 = GCD369CubeHahnRegular.constant C7)
    (hc5 : F.c5 = GCD369CubeHahnRegular.constant C5)
    (hc4 : F.c4 = GCD369CubeHahnRegular.constant C4)
    (hc3 : F.c3 = GCD369CubeHahnRegular.constant C3)
    (hc2 : F.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : F.c1 = GCD369CubeHahnRegular.constant C1)
    (hr1 : F.rho1 = GCD369CubeHahnRegular.constant R1)
    (hr2 : F.rho2 = GCD369CubeHahnRegular.constant R2)
    (hr3 : F.rho3 = GCD369CubeHahnRegular.constant R3)
    (hr4 : F.rho4 = GCD369CubeHahnRegular.constant R4)
    (hnormal2 : (↑(F.scale.p / 2) : WithTop ℚ) ≤
      S.normal2.1.orderTop)
    (hnormal1 : (↑(F.scale.p / 2) : WithTop ℚ) ≤
      S.normal1.1.orderTop)
    (hnormal0 : (↑(F.scale.p / 2) : WithTop ℚ) ≤
      S.normal0.1.orderTop) :
    let T := S.transverseFactorOfBounds (F.scale.p / 2)
      (div_pos F.scale.hp (by norm_num))
      hnormal2 hnormal1 hnormal0
    GCD369CubeDLeadingFaberRowsAt
      (GCD369CubeHahnRegular.constantCoeff T.Xn)
      (GCD369CubeHahnRegular.constantCoeff T.Yn)
      (GCD369CubeHahnRegular.constantCoeff T.Zn) S.u S.v D := by
  dsimp only
  let T := S.transverseFactorOfBounds (F.scale.p / 2)
    (div_pos F.scale.hp (by norm_num))
    hnormal2 hnormal1 hnormal0
  apply T.dLeadingFaberRowsAt D
  · have hz := F.dN1Coeff_zero C7 C5 C4 C3 C2 C1 R1
      hc7 hc5 hc4 hc3 hc2 hc1 hr1
    rw [hd,
      F.scale.weightedRegular_constant_eq_monomial_sq 1 (by norm_num) D] at hz
    have hTdelta : T.delta = F.scale.p / 2 := rfl
    simp only [hTdelta]
    rw [hscale]
    convert hz using 1 <;> norm_num <;> ring_nf
  · have hz := F.dN2Coeff_zero C7 C5 C4 C3 C2 C1 R2
      hc7 hc5 hc4 hc3 hc2 hc1 hr2
    rw [hd,
      F.scale.weightedRegular_constant_eq_monomial_sq 1 (by norm_num) D] at hz
    have hTdelta : T.delta = F.scale.p / 2 := rfl
    simp only [hTdelta]
    rw [hscale]
    convert hz using 1 <;> norm_num <;> ring_nf
  · have hz := F.dN3Coeff_zero C7 C5 C4 C3 C2 C1 R3
      hc7 hc5 hc4 hc3 hc2 hc1 hr3
    rw [hd,
      F.scale.weightedRegular_constant_eq_monomial_sq 1 (by norm_num) D] at hz
    have hTdelta : T.delta = F.scale.p / 2 := rfl
    simp only [hTdelta]
    rw [hscale]
    convert hz using 1 <;> norm_num <;> ring_nf
  · have hz := F.dN4Coeff_zero C7 C5 C4 C3 C2 C1 R4
      hc7 hc5 hc4 hc3 hc2 hc1 hr4
    rw [hd,
      F.scale.weightedRegular_constant_eq_monomial_sq 1 (by norm_num) D] at hz
    have hTdelta : T.delta = F.scale.p / 2 := rfl
    simp only [hTdelta]
    rw [hscale]
    convert hz using 1 <;> norm_num <;> ring_nf

end GCD369CubeHahnCommonValueData

#print axioms GCD369CubeSingularCubic_taylor_double
#print axioms GCD369CubeSingularCubic_taylor_simple
#print axioms GCD369CubeSingularNormal_factor
#print axioms GCD369CubeSingularParameter_ne_zero
#print axioms GCD369CubeSingularCubic_root_cases
#print axioms GCD369CubeSingularNormal_root_zero
#print axioms GCD369CubeZeroLoadNormal_root_data
#print axioms GCD369CubeHahnCommonValueData.dLeadingFaberRowsAt_of_bounds
