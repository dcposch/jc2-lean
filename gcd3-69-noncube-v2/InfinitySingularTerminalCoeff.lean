import InfinitySingularDegree

/-! # Early terminal coefficients on the singular infinity component

The global terminal invariant starts at order `14 p - 1`.  On the singular
common-cubic component the pole scale `p` is a positive integer, so every
coefficient through weight two is strictly earlier and must vanish.
-/

noncomputable section

namespace GCD369CubePolynomialSource

set_option maxRecDepth 10000 in
/-- The complete fifth Faber numerator has zero coefficient at every load
exponent `w p` with `w ≤ 12` on the singular constant-core infinity
component. -/
theorem infinity_fullN5Coeff_weight_p_eq_zero_of_singular
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (w : ℕ) (hw : w ≤ 12)
    (hdisc :
      4 * (S.infinityCommonCoefficientData hsdegree).u ^ 3 +
        27 * (S.infinityCommonCoefficientData hsdegree).v ^ 2 = 0) :
    let D := S.infinityCommonCoefficientData hsdegree
    (GCD369CubeFaberFullN5
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4
      (D.faber.scale.weightedRegular 1 D.faber.d)
      (D.faber.scale.weightedRegular 2 D.faber.c7)
      (D.faber.scale.weightedRegular 4 D.faber.c5)
      (D.faber.scale.weightedRegular 5 D.faber.c4)
      (D.faber.scale.weightedRegular 6 D.faber.c3)
      (D.faber.scale.weightedRegular 7 D.faber.c2)
      (D.faber.scale.weightedRegular 8 D.faber.c1)).1.coeff
        ((w : ℚ) * D.faber.scale.p) = 0 := by
  dsimp only
  let hpole := S.infinityNormalizedCoeffPole_of_constantCore hsdegree
  let D := S.infinityCommonCoefficientData hsdegree
  let N : GCD369CubeHahnRegular k := GCD369CubeFaberFullN5
    D.faber.scale.regular0 D.faber.scale.regular1
    D.faber.scale.regular2 D.faber.scale.regular3
    D.faber.scale.regular4
    (D.faber.scale.weightedRegular 1 D.faber.d)
    (D.faber.scale.weightedRegular 2 D.faber.c7)
    (D.faber.scale.weightedRegular 4 D.faber.c5)
    (D.faber.scale.weightedRegular 5 D.faber.c4)
    (D.faber.scale.weightedRegular 6 D.faber.c3)
    (D.faber.scale.weightedRegular 7 D.faber.c2)
    (D.faber.scale.weightedRegular 8 D.faber.c1)
  let terminal : HahnSeries ℚ k := GCD369CubeFaberR5
    (D.faber.scale.regular0 : HahnSeries ℚ k)
    D.faber.scale.regular1 D.faber.scale.regular2
    D.faber.scale.regular3 D.faber.scale.regular4
    (D.faber.scale.weightedRegular 1 D.faber.d)
    (D.faber.scale.weightedRegular 2 D.faber.c7)
    (D.faber.scale.weightedRegular 4 D.faber.c5)
    (D.faber.scale.weightedRegular 5 D.faber.c4)
    (D.faber.scale.weightedRegular 6 D.faber.c3)
    (D.faber.scale.weightedRegular 7 D.faber.c2)
    (D.faber.scale.weightedRegular 8 D.faber.c1)
  obtain ⟨m, hm, hp⟩ :=
    S.infinity_scale_eq_pos_nat_of_discriminant_zero hsdegree hdisc
  have hpone : (1 : ℚ) ≤ D.faber.scale.p := by
    rw [hp]
    exact_mod_cast hm
  have hwq : (w : ℚ) ≤ 12 := by exact_mod_cast hw
  have hfactor : (2 : ℚ) ≤ 14 - w := by linarith
  have hlt : (w : ℚ) * D.faber.scale.p <
      14 * D.faber.scale.p - 1 := by
    nlinarith
  have hscaled : terminal = D.faber.scale.t ^ 14 *
      GCD369CubeRatFuncHahnAtInfinity S.terminalFaberInvariant := by
    have hs := S.infinityFaberPoleData_scaled_terminal hpole
    change terminal = D.faber.scale.t ^ 14 *
      GCD369CubeRatFuncHahnAtInfinity S.terminalFaberInvariant at hs
    exact hs
  have hglobal :=
    S.infinityFaberPoleData_scaled_terminal_order hsdegree hpole
  have hterminalOrder : terminal.order =
      14 * D.faber.scale.p - 1 := by
    rw [hscaled]
    simpa only [D, S.infinityCommonCoefficientData_faber hsdegree]
      using hglobal
  have hterminalCoeff : terminal.coeff
      ((w : ℚ) * D.faber.scale.p) = 0 := by
    apply HahnSeries.coeff_eq_zero_of_lt_order
    rw [hterminalOrder]
    exact hlt
  have hquot :=
    GCD369CubeHahnFaberPoleData.faberR5_coeff_eq_fullN5_coeff_div
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4
      (D.faber.scale.weightedRegular 1 D.faber.d)
      (D.faber.scale.weightedRegular 2 D.faber.c7)
      (D.faber.scale.weightedRegular 4 D.faber.c5)
      (D.faber.scale.weightedRegular 5 D.faber.c4)
      (D.faber.scale.weightedRegular 6 D.faber.c3)
      (D.faber.scale.weightedRegular 7 D.faber.c2)
      (D.faber.scale.weightedRegular 8 D.faber.c1)
      ((w : ℚ) * D.faber.scale.p)
  change terminal.coeff ((w : ℚ) * D.faber.scale.p) =
      N.1.coeff ((w : ℚ) * D.faber.scale.p) / (13436928 : k) at hquot
  rw [hterminalCoeff] at hquot
  have hzero : N.1.coeff ((w : ℚ) * D.faber.scale.p) = 0 := by
    field_simp at hquot
    simpa using hquot.symm
  simpa only [N, D] using hzero

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- Weight-two spelling used by the balanced `c7` resonance. -/
theorem infinity_fullN5Coeff_two_p_eq_zero_of_singular
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (hdisc :
      4 * (S.infinityCommonCoefficientData hsdegree).u ^ 3 +
        27 * (S.infinityCommonCoefficientData hsdegree).v ^ 2 = 0) :
    let D := S.infinityCommonCoefficientData hsdegree
    (GCD369CubeFaberFullN5
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4
      (D.faber.scale.weightedRegular 1 D.faber.d)
      (D.faber.scale.weightedRegular 2 D.faber.c7)
      (D.faber.scale.weightedRegular 4 D.faber.c5)
      (D.faber.scale.weightedRegular 5 D.faber.c4)
      (D.faber.scale.weightedRegular 6 D.faber.c3)
      (D.faber.scale.weightedRegular 7 D.faber.c2)
      (D.faber.scale.weightedRegular 8 D.faber.c1)).1.coeff
        (2 * D.faber.scale.p) = 0 := by
  simpa using S.infinity_fullN5Coeff_weight_p_eq_zero_of_singular
    hsdegree 2 (by norm_num) hdisc

end GCD369CubePolynomialSource

#print axioms
  GCD369CubePolynomialSource.infinity_fullN5Coeff_weight_p_eq_zero_of_singular
#print axioms
  GCD369CubePolynomialSource.infinity_fullN5Coeff_two_p_eq_zero_of_singular
