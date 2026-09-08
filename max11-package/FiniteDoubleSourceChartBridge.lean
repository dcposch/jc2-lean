import FiniteDoubleSourceChartOrders

/-! # Realization of the moving double-root source chart

The valuation arguments consume two compact chart expressions.  This file
derives those expressions from the actual moving cubic coefficients, source
coordinate, and normalized transverse coordinates.
-/

noncomputable section

namespace GCD369CubeHahnCommonValueData

/-- The displayed double-root coordinate expansions imply the exact cubic
and transverse chart equations used by the source order split. -/
theorem TransverseFactor.doubleRoot_chart_equations
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (r w d e B B2 C2 : GCD369CubeHahnRegular k)
    (hx : S.normal.sextic.regularX = r + w)
    (hU : S.cubicU = -3 * r ^ 2 +
      GCD369CubeHahnRegular.monomial T.delta T.hdelta.le * d)
    (hV : S.cubicV = 2 * r ^ 3 +
      GCD369CubeHahnRegular.monomial T.delta T.hdelta.le * e)
    (hre : 3 * e + 2 * d * r = 0)
    (hY : T.Yn = r * T.Xn +
      GCD369CubeHahnRegular.monomial (T.delta / 2)
        (div_nonneg T.hdelta.le (by norm_num)) * B +
      GCD369CubeHahnRegular.monomial T.delta T.hdelta.le * B2)
    (hZ : T.Zn = -2 * r ^ 2 * T.Xn -
      GCD369CubeHahnRegular.monomial (T.delta / 2)
        (div_nonneg T.hdelta.le (by norm_num)) * r * B +
      GCD369CubeHahnRegular.monomial T.delta T.hdelta.le * C2) :
    S.cubicValue = GCD369CubeDoubleSourceCubicChart
        T.delta T.hdelta.le r w d ∧
      S.transverseValue = GCD369CubeDoubleSourceTransverseChart
        T.delta T.hdelta.le T.Xn r w B B2 C2 := by
  let H : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
  let M : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial (T.delta / 2)
      (div_nonneg T.hdelta.le (by norm_num))
  have hthird : (3 : GCD369CubeHahnRegular k) *
      GCD369CubeHahnRegular.ratCast (1 / 3) = 1 := by
    calc
      _ = GCD369CubeHahnRegular.ratCast 3 *
          GCD369CubeHahnRegular.ratCast (1 / 3) := by rw [map_ofNat]
      _ = GCD369CubeHahnRegular.ratCast (3 * (1 / 3)) :=
        (map_mul _ _ _).symm
      _ = 1 := by norm_num
  constructor
  · dsimp only [cubicValue]
    rw [hx, hU, hV]
    dsimp only [GCD369CubeDoubleSourceCubicChart, H]
    linear_combination
      GCD369CubeHahnRegular.ratCast (1 / 3) * H * hre +
        -(r * H * d + H * e) * hthird
  · rw [T.transverseValue_eq, hx, hY, hZ]
    dsimp only [GCD369CubeDoubleSourceTransverseChart, H, M]
    ring

end GCD369CubeHahnCommonValueData

#print axioms GCD369CubeHahnCommonValueData.TransverseFactor.doubleRoot_chart_equations
