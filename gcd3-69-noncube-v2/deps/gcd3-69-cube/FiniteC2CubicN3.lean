import FiniteC2EarlyNormal

/-! # The primitive third row at the cubic scale before `c2`

With the weight-one, weight-two, weight-four, weight-five, and weight-six
loads killed, the primitive third normal coefficient at `3 * delta`
vanishes as soon as that exponent lies below the weight-seven cutoff
`7 * p`.
-/

noncomputable section

namespace GCD369CubeHahnCommonValueData

/-- After `d = c7 = c5 = c4 = c3 = 0`, the primitive zero-high third row
vanishes at the cubic transverse exponent whenever `3 * delta < 7 * p`. -/
theorem TransverseFactor.zeroHighN3Coeff_zero_at_cubic_before_c2
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (F : GCD369CubeHahnFaberPoleData k)
    (hscale : S.normal.sextic.scale = F.scale)
    (hd : F.d = 0)
    (hc7 : F.c7 = 0)
    (hc5 : F.c5 = 0)
    (hc4 : F.c4 = 0)
    (hc3 : F.c3 = 0)
    (hearly : 3 * T.delta < 7 * F.scale.p) :
    (GCD369CubeFaberN3
      S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
      S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
      S.normal.sextic.scale.regular4).1.coeff (3 * T.delta) = 0 := by
  have hz := F.zeroHighNCoeff_zero_before_c2 hd hc7 hc5 hc4 hc3
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
  GCD369CubeHahnCommonValueData.TransverseFactor.zeroHighN3Coeff_zero_at_cubic_before_c2
