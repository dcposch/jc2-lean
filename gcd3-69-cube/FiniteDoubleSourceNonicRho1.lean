import FiniteDoubleSource
import FiniteLaterSourceElimination

/-! # Source-value boundary at the moving double root before `rho1`

Once the weight-one, weight-two, weight-four, weight-five, weight-six,
weight-seven, and weight-eight loads have vanished, the literal nonic
source value still excludes the late double-root branch below the
weight-ten `rho1` load.  The argument is the same second-order residue
as in the weight-one case, now evaluated at `2 * delta` under the weaker
cutoff `3 * delta ≤ 10 * p`.  Ninth-Faber vanishing is supplied by the
later weight-nine quotient, which is available once `c1` has also
vanished.
-/

noncomputable section

namespace GCD369CubeHahnCommonValueData

/-- The literal nonic source value excludes the late double-root branch as
soon as the sextic analysis supplies the two displayed order bounds, after
the weight-one, weight-two, weight-four, weight-five, weight-six,
weight-seven, and weight-eight loads have vanished and `3 * delta ≤ 10 * p`. -/
theorem TransverseFactor.doubleRoot_sourceNonic_inconsistent_of_orderBounds_before_rho1
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (r A : k) (hr : r ≠ 0) (hA : A ≠ 0)
    (hx : GCD369CubeHahnRegular.constantCoeff
      S.normal.sextic.regularX = r)
    (hX : GCD369CubeHahnRegular.constantCoeff T.Xn = A)
    (hY : GCD369CubeHahnRegular.constantCoeff T.Yn = r * A)
    (hd : S.normal.d = 0)
    (hc7 : S.normal.c7 = 0)
    (hc5 : S.normal.c5 = 0)
    (hc4 : S.normal.c4 = 0)
    (hc3 : S.normal.c3 = 0)
    (hc2 : S.normal.c2 = 0)
    (hc1 : S.normal.c1 = 0)
    (hp : 3 * T.delta ≤ 10 * S.normal.sextic.scale.p)
    (hK : (↑T.delta : WithTop ℚ) ≤ S.cubicValue.1.orderTop)
    (hphi : (↑(2 * T.delta) : WithTop ℚ) ≤
      S.transverseValue.1.orderTop) : False := by
  have hearly : 2 * T.delta < 9 * S.normal.sextic.scale.p := by
    have hp_pos : 0 < S.normal.sextic.scale.p := S.normal.sextic.scale.hp
    nlinarith [hp, hp_pos]
  have hz := S.normal.faberNineCoeff_zero_before_later
    hd hc7 hc5 hc4 hc3 hc2 hc1 (2 * T.delta) (by nlinarith [T.hdelta]) hearly
  have hc := T.faberNineCoeff_at_twoDelta_of_orderBounds hK hphi
  rw [hc] at hz
  simp only [map_mul, map_add, map_ofNat,
    GCD369CubeHahnRegular.constantCoeff_ratCast] at hz
  rw [hx, hX, hY] at hz
  have hscalar : algebraMap ℚ k (3 / 8) * A * (A * r + 2 * (r * A)) =
      algebraMap ℚ k (9 / 8) * r * A ^ 2 := by
    norm_num
    ring
  rw [hscalar] at hz
  have hn : algebraMap ℚ k (9 / 8) ≠ 0 := by norm_num
  exact (mul_ne_zero (mul_ne_zero hn hr) (pow_ne_zero 2 hA)) hz

end GCD369CubeHahnCommonValueData

#print axioms GCD369CubeHahnCommonValueData.TransverseFactor.doubleRoot_sourceNonic_inconsistent_of_orderBounds_before_rho1
