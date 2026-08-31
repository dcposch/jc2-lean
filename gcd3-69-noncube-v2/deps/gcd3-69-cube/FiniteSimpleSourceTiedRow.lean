import FiniteSimpleSourceLoadCoeff

/-! # The exact tied nonic row at the source simple root

This file specializes the weight-one coefficient equation to the singular
common cubic and its remaining simple root.  The `d` term contributes the
explicit nonzero scalar `(130 / 9) * r^8`.
-/

noncomputable section

namespace GCD369CubeHahnPoleScale

/-- At exponent `p`, a weight-one ground-field constant times a regular
factor contributes the constant times the factor's residue. -/
theorem weightedRegular_one_constant_mul_coeff
    {k : Type*} [Field k]
    (S : GCD369CubeHahnPoleScale k) (D : k)
    (P : GCD369CubeHahnRegular k) :
    (S.weightedRegular 1 (GCD369CubeHahnRegular.constant D) * P).1.coeff
        S.p = D * GCD369CubeHahnRegular.constantCoeff P := by
  change ((S.t ^ 1 * (GCD369CubeHahnRegular.constant D).1) * P.1).coeff
    S.p = _
  simp only [pow_one, GCD369CubeHahnPoleScale.t]
  rw [mul_assoc]
  change (GCD369CubeHahnRegular.monomial S.p S.hp.le *
    (GCD369CubeHahnRegular.constant D * P)).1.coeff S.p = _
  have h := GCD369CubeHahnRegular.coeff_monomial_pow_mul_at
    S.p S.hp 1 (GCD369CubeHahnRegular.constant D * P)
  simpa only [GCD369CubeHahnRegular.monomial, pow_one, Nat.cast_one,
    one_mul, map_mul,
    GCD369CubeHahnRegular.constantCoeff_constant] using h

end GCD369CubeHahnPoleScale

namespace GCD369CubeHahnCommonValueData

/-- The residue of the eighth Faber value at the remaining simple root is
the universal monomial `(130 / 9) * r^8`. -/
theorem TransverseFactor.faberEight_constantCoeff_simpleRoot
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (_T : S.TransverseFactor)
    (r : k)
    (hu : S.u = -3 * r ^ 2) (hv : S.v = 2 * r ^ 3)
    (hx : GCD369CubeHahnRegular.constantCoeff
      S.normal.sextic.regularX = -2 * r) :
    GCD369CubeHahnRegular.constantCoeff
      (GCD369CubeFaberEightValueQ GCD369CubeHahnRegular.ratCast
        S.normal.sextic.scale.regular0
        S.normal.sextic.scale.regular1
        S.normal.sextic.scale.regular2
        S.normal.sextic.scale.regular3
        S.normal.sextic.scale.regular4
        S.normal.sextic.regularX) = (130 / 9) * r ^ 8 := by
  simp only [GCD369CubeFaberEightValueQ, map_add, map_sub, map_mul,
    map_pow, GCD369CubeHahnRegular.constantCoeff_ratCast]
  change GCD369CubeFaberEightValueQ (algebraMap ℚ k)
    S.normal.sextic.scale.leading0 S.normal.sextic.scale.leading1
    S.normal.sextic.scale.leading2 S.normal.sextic.scale.leading3
    S.normal.sextic.scale.leading4
    (GCD369CubeHahnRegular.constantCoeff S.normal.sextic.regularX) = _
  rw [S.ha0, S.ha1, S.ha2, S.ha3, S.ha4, hu, hv, hx]
  convert GCD369CubeFaberEightValueQ_simpleRoot r using 1
  all_goals ring

/-- If the weight-one parameter is the ground-field constant `D`, the
literal nonic source row at exponent `p` has the exact displayed load term.
-/
theorem TransverseFactor.faberNineCoeff_at_d_simpleRoot
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (r D : k)
    (hd : S.normal.d = GCD369CubeHahnRegular.constant D)
    (hu : S.u = -3 * r ^ 2) (hv : S.v = 2 * r ^ 3)
    (hx : GCD369CubeHahnRegular.constantCoeff
      S.normal.sextic.regularX = -2 * r) :
    (GCD369CubeFaberNineValueQ GCD369CubeHahnRegular.ratCast
      S.normal.sextic.scale.regular0
      S.normal.sextic.scale.regular1
      S.normal.sextic.scale.regular2
      S.normal.sextic.scale.regular3
      S.normal.sextic.scale.regular4
      S.normal.sextic.regularX).1.coeff S.normal.sextic.scale.p =
        -(D * ((130 / 9) * r ^ 8)) := by
  let F8 : GCD369CubeHahnRegular k :=
    GCD369CubeFaberEightValueQ GCD369CubeHahnRegular.ratCast
      S.normal.sextic.scale.regular0
      S.normal.sextic.scale.regular1
      S.normal.sextic.scale.regular2
      S.normal.sextic.scale.regular3
      S.normal.sextic.scale.regular4
      S.normal.sextic.regularX
  have hF8 : GCD369CubeHahnRegular.constantCoeff F8 =
      (130 / 9) * r ^ 8 := by
    exact T.faberEight_constantCoeff_simpleRoot r hu hv hx
  have hz := S.normal.faberNine_add_dFaberEightCoeff_zero_at_d
  change (_ + S.normal.sextic.scale.weightedRegular 1 S.normal.d * F8).1.coeff
    S.normal.sextic.scale.p = 0 at hz
  change (_ +
    (S.normal.sextic.scale.weightedRegular 1 S.normal.d * F8).1).coeff
      S.normal.sextic.scale.p = 0 at hz
  rw [HahnSeries.coeff_add, hd,
    S.normal.sextic.scale.weightedRegular_one_constant_mul_coeff D F8,
    hF8] at hz
  exact eq_neg_of_add_eq_zero_left hz

end GCD369CubeHahnCommonValueData

#print axioms
  GCD369CubeHahnPoleScale.weightedRegular_one_constant_mul_coeff
#print axioms
  GCD369CubeHahnCommonValueData.TransverseFactor.faberEight_constantCoeff_simpleRoot
#print axioms
  GCD369CubeHahnCommonValueData.TransverseFactor.faberNineCoeff_at_d_simpleRoot
