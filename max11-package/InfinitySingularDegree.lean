import InfinityDBalanced

noncomputable section

/-! # Integral pole scale on the singular infinity component

On a singular projective common cubic both coordinates are nonzero.  The
fourth and third normalized sextic coefficients therefore have degrees
`2 p` and `3 p`; subtracting those two natural degrees shows that `p` itself
is a positive natural number.  This elementary lattice fact uniformly
excludes every timing branch in which the intrinsic cubic term at `3 delta`
survives strictly before a load of weight at most thirteen.
-/

namespace GCD369CubePolynomialSource

/-- A singular projective common-cubic infinity packet has positive integral
pole scale. -/
theorem infinity_scale_eq_pos_nat_of_discriminant_zero
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (hdisc :
      4 * (S.infinityCommonCoefficientData hsdegree).u ^ 3 +
        27 * (S.infinityCommonCoefficientData hsdegree).v ^ 2 = 0) :
    ∃ m : ℕ, 0 < m ∧
      (S.infinityCommonCoefficientData hsdegree).faber.scale.p = m := by
  let hpole := S.infinityNormalizedCoeffPole_of_constantCore hsdegree
  let D := S.infinityCommonCoefficientData hsdegree
  have hu : D.u ≠ 0 := by
    intro hu0
    have hv2 : D.v ^ 2 = 0 := by
      rw [hu0] at hdisc
      norm_num at hdisc ⊢
      exact hdisc
    have hv : D.v = 0 := (sq_eq_zero_iff).mp hv2
    exact D.hprojective.elim (fun h => h hu0) (fun h => h hv)
  have hv : D.v ≠ 0 := by
    intro hv0
    have hu3 : D.u ^ 3 = 0 := by
      rw [hv0] at hdisc
      norm_num at hdisc ⊢
      exact hdisc
    have hu0 : D.u = 0 := by
      by_contra h
      exact (pow_ne_zero 3 h) hu3
    exact hu hu0
  have h4D : D.faber.scale.leading4 ≠ 0 := by
    rw [D.ha4]
    exact mul_ne_zero (by norm_num) hu
  have h3D : D.faber.scale.leading3 ≠ 0 := by
    rw [D.ha3]
    exact mul_ne_zero (by norm_num) hv
  have h4 : (S.infinityFaberPoleData hpole).scale.leading4 ≠ 0 := by
    simpa only [D, S.infinityCommonCoefficientData_faber hsdegree] using h4D
  have h3 : (S.infinityFaberPoleData hpole).scale.leading3 ≠ 0 := by
    simpa only [D, S.infinityCommonCoefficientData_faber hsdegree] using h3D
  let n4 := (S.constantCoreNormalizedPPolynomial.coeff 4).natDegree
  let n3 := (S.constantCoreNormalizedPPolynomial.coeff 3).natDegree
  have hn4 : (n4 : ℚ) = 2 * D.faber.scale.p := by
    simpa only [n4, D, S.infinityCommonCoefficientData_faber hsdegree] using
      S.infinityLeading4_natDegree hsdegree hpole h4
  have hn3 : (n3 : ℚ) = 3 * D.faber.scale.p := by
    simpa only [n3, D, S.infinityCommonCoefficientData_faber hsdegree] using
      S.infinityLeading3_natDegree hsdegree hpole h3
  have hn43 : n4 < n3 := by
    exact_mod_cast (show (n4 : ℚ) < n3 by
      rw [hn4, hn3]
      linarith [D.faber.scale.hp])
  let m := n3 - n4
  have hm : 0 < m := Nat.sub_pos_iff_lt.mpr hn43
  have hmp : (m : ℚ) = D.faber.scale.p := by
    dsimp only [m]
    rw [Nat.cast_sub (Nat.le_of_lt hn43), hn3, hn4]
    ring
  exact ⟨m, hm, hmp.symm⟩

/-- On the singular component, the global terminal order cannot be the
intrinsic cubic order `3 delta` while that order is strictly earlier than a
load of weight at most thirteen. -/
theorem infinity_terminal_three_delta_not_before_load_of_singular
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (T : (S.infinityCommonCoefficientData hsdegree).TransverseScale)
    (w : ℕ) (hw : w ≤ 13)
    (hdisc :
      4 * (S.infinityCommonCoefficientData hsdegree).u ^ 3 +
        27 * (S.infinityCommonCoefficientData hsdegree).v ^ 2 = 0)
    (hbefore : 3 * T.delta <
      w * (S.infinityCommonCoefficientData hsdegree).faber.scale.p)
    (horder :
      let hpole := S.infinityNormalizedCoeffPole_of_constantCore hsdegree
      let F := S.infinityFaberPoleData hpole
      (F.scale.t ^ 14 *
        GCD369CubeRatFuncHahnAtInfinity S.terminalFaberInvariant).order =
          3 * T.delta) :
    False := by
  let hpole := S.infinityNormalizedCoeffPole_of_constantCore hsdegree
  let D := S.infinityCommonCoefficientData hsdegree
  obtain ⟨m, hm, hp⟩ :=
    S.infinity_scale_eq_pos_nat_of_discriminant_zero hsdegree hdisc
  have hpone : (1 : ℚ) ≤ D.faber.scale.p := by
    rw [hp]
    exact_mod_cast hm
  have hglobal := S.infinityFaberPoleData_scaled_terminal_order hsdegree hpole
  have hglobalD :
      (D.faber.scale.t ^ 14 *
        GCD369CubeRatFuncHahnAtInfinity S.terminalFaberInvariant).order =
          14 * D.faber.scale.p - 1 := by
    simpa only [D, S.infinityCommonCoefficientData_faber hsdegree] using hglobal
  have horderD :
      (D.faber.scale.t ^ 14 *
        GCD369CubeRatFuncHahnAtInfinity S.terminalFaberInvariant).order =
          3 * T.delta := by
    simpa only [hpole, D, S.infinityCommonCoefficientData_faber hsdegree]
      using horder
  have heq : 14 * D.faber.scale.p - 1 = 3 * T.delta := by
    rw [← horderD]
    exact hglobalD.symm
  have hwq : (w : ℚ) ≤ 13 := by exact_mod_cast hw
  have hfactor : (1 : ℚ) ≤ 14 - w := by linarith
  have hlower : (1 : ℚ) ≤ (14 - w) * D.faber.scale.p := by
    nlinarith
  have hbeforeD : 3 * T.delta < w * D.faber.scale.p := by
    simpa only [D, S.infinityCommonCoefficientData_faber hsdegree] using hbefore
  have hupper : (14 - w) * D.faber.scale.p < 1 := by
    linarith
  linarith

/-- A surviving terminal term of any early-load weight at most twelve is
also impossible on the singular component.  Its scale equation would say
`(14-w) p = 1`, whereas `p` is a positive integer and `14-w ≥ 2`. -/
theorem infinity_terminal_weight_order_inconsistent_of_singular
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (w : ℕ) (hw : w ≤ 12)
    (hdisc :
      4 * (S.infinityCommonCoefficientData hsdegree).u ^ 3 +
        27 * (S.infinityCommonCoefficientData hsdegree).v ^ 2 = 0)
    (horder :
      let hpole := S.infinityNormalizedCoeffPole_of_constantCore hsdegree
      let F := S.infinityFaberPoleData hpole
      (F.scale.t ^ 14 *
        GCD369CubeRatFuncHahnAtInfinity S.terminalFaberInvariant).order =
          w * F.scale.p) :
    False := by
  let hpole := S.infinityNormalizedCoeffPole_of_constantCore hsdegree
  let D := S.infinityCommonCoefficientData hsdegree
  obtain ⟨m, hm, hp⟩ :=
    S.infinity_scale_eq_pos_nat_of_discriminant_zero hsdegree hdisc
  have hpone : (1 : ℚ) ≤ D.faber.scale.p := by
    rw [hp]
    exact_mod_cast hm
  have hscaleF :=
    S.infinity_terminal_scale_eq_of_order_eq_weight hsdegree hpole w horder
  have hscale : (14 - (w : ℚ)) * D.faber.scale.p = 1 := by
    simpa only [D, S.infinityCommonCoefficientData_faber hsdegree] using hscaleF
  have hwq : (w : ℚ) ≤ 12 := by exact_mod_cast hw
  have hfactor : (2 : ℚ) ≤ 14 - w := by linarith
  nlinarith

end GCD369CubePolynomialSource

#print axioms
  GCD369CubePolynomialSource.infinity_scale_eq_pos_nat_of_discriminant_zero
#print axioms
  GCD369CubePolynomialSource.infinity_terminal_three_delta_not_before_load_of_singular
#print axioms
  GCD369CubePolynomialSource.infinity_terminal_weight_order_inconsistent_of_singular
