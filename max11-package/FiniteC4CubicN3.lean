import FiniteC4EarlyNormal

/-! # The primitive third row at the cubic scale before `c4`

With the weight-one, weight-two, and weight-four loads killed, the primitive
third normal coefficient at `3 * delta` vanishes as soon as that exponent
lies below the weight-five cutoff `5 * p`.
-/

noncomputable section

namespace GCD369CubeHahnCommonValueData

/-- After `d = c7 = c5 = 0`, the primitive zero-high third row vanishes at
the cubic transverse exponent whenever `3 * delta < 5 * p`. -/
theorem TransverseFactor.zeroHighN3Coeff_zero_at_cubic_before_c4
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (F : GCD369CubeHahnFaberPoleData k)
    (hscale : S.normal.sextic.scale = F.scale)
    (hd : F.d = 0)
    (hc7 : F.c7 = 0)
    (hc5 : F.c5 = 0)
    (hearly : 3 * T.delta < 5 * F.scale.p) :
    (GCD369CubeFaberN3
      S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
      S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
      S.normal.sextic.scale.regular4).1.coeff (3 * T.delta) = 0 := by
  have hz := F.zeroHighNCoeff_zero_before_c4 hd hc7 hc5
    (3 * T.delta) (by nlinarith [T.hdelta]) hearly
  rw [← hscale] at hz
  have hcoeff :
      (243 * GCD369CubeFaberN3
        S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
        S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
        S.normal.sextic.scale.regular4).1.coeff (3 * T.delta) =
      (243 : k) *
        (GCD369CubeFaberN3
          S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
          S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
          S.normal.sextic.scale.regular4).1.coeff (3 * T.delta) := by
    exact GCD369CubeHahnRegular.coeff_nat_mul 243 _ _
  rw [hcoeff] at hz
  exact (mul_eq_zero.mp hz.2.2.1).resolve_left (by norm_num)

end GCD369CubeHahnCommonValueData

#print axioms
  GCD369CubeHahnCommonValueData.TransverseFactor.zeroHighN3Coeff_zero_at_cubic_before_c4
