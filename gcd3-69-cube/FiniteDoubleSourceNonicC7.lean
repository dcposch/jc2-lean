import FiniteDoubleSource
import FiniteC7SourceElimination

/-! # Source-value boundary at the moving double root before `c7`

Once the weight-one load has vanished, the literal nonic source value still
excludes the late double-root branch below the weight-two scale.  The
argument is the same second-order residue as in the weight-one case, now
evaluated at `2 * delta` under the weaker cutoff `3 * delta < 2 * p`.
-/

noncomputable section

namespace GCD369CubeHahnCommonValueData

/-- The literal nonic source value excludes the late double-root branch as
soon as the sextic analysis supplies the two displayed order bounds, after
the weight-one load has vanished and `3 * delta < 2 * p`. -/
theorem TransverseFactor.doubleRoot_sourceNonic_inconsistent_of_orderBounds_before_c7
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (r A : k) (hr : r ≠ 0) (hA : A ≠ 0)
    (hx : GCD369CubeHahnRegular.constantCoeff
      S.normal.sextic.regularX = r)
    (hX : GCD369CubeHahnRegular.constantCoeff T.Xn = A)
    (hY : GCD369CubeHahnRegular.constantCoeff T.Yn = r * A)
    (hd : S.normal.d = 0)
    (hp : 3 * T.delta < 2 * S.normal.sextic.scale.p)
    (hK : (↑T.delta : WithTop ℚ) ≤ S.cubicValue.1.orderTop)
    (hphi : (↑(2 * T.delta) : WithTop ℚ) ≤
      S.transverseValue.1.orderTop) : False := by
  have hz := S.normal.faberNineCoeff_zero_before_c7
    hd (2 * T.delta) (by nlinarith [T.hdelta])
    (by nlinarith [T.hdelta, hp])
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

#print axioms GCD369CubeHahnCommonValueData.TransverseFactor.doubleRoot_sourceNonic_inconsistent_of_orderBounds_before_c7
