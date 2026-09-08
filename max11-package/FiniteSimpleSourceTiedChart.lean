import FiniteSimpleSourceTiedRow

/-! # Full-scale ring rewrites of the simple-root source chart

Once the late simple-root displacement and the half-scale normal correction
both factor through the intrinsic `delta` monomial, the cubic chart, the
transverse chart, and the explicit second-order ninth-Faber term become
literal multiples of that monomial.  The identities are ring rewrites of
the chart definitions; they do not use valuation theory.
-/

noncomputable section

namespace GCD369CubeHahnCommonValueData

/-- Full-scale factorizations of `w` and `M * B` convert the simple-root
cubic and transverse charts into literal `H` and `H ^ 2` multiples. -/
theorem TransverseFactor.simpleRoot_tied_chart_equations
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (r w d B B2 C2 s b : GCD369CubeHahnRegular k)
    (hw : w = GCD369CubeHahnRegular.monomial T.delta T.hdelta.le * s)
    (hB : GCD369CubeHahnRegular.monomial (T.delta / 2)
        (div_nonneg T.hdelta.le (by norm_num)) * B =
      GCD369CubeHahnRegular.monomial T.delta T.hdelta.le * b)
    (hKchart : S.cubicValue = GCD369CubeSimpleSourceCubicChart
      T.delta T.hdelta.le r w d)
    (hphichart : S.transverseValue =
      GCD369CubeSimpleSourceTransverseChart
        T.delta T.hdelta.le T.Xn r w B B2 C2) :
    let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
    let K1 := s * (9 * r ^ 2 - 6 * r * H * s + (H * s) ^ 2) +
      d * H * s + GCD369CubeHahnRegular.ratCast (-8 / 3) * d * r
    let L1 := (T.Xn * s + b) * (H * s - 3 * r) +
      B2 * (-2 * r + H * s) + C2
    S.cubicValue = H * K1 ∧ S.transverseValue = H ^ 2 * L1 := by
  dsimp only
  constructor
  · rw [hKchart]
    dsimp only [GCD369CubeSimpleSourceCubicChart]
    rw [hw]
    ring
  · rw [hphichart]
    dsimp only [GCD369CubeSimpleSourceTransverseChart]
    rw [hw, hB]
    ring

/-- The explicit second-order ninth-Faber term likewise factors through the
full `delta` monomial, once the source coordinate and first normal
coordinate are the simple-root chart expansions. -/
theorem TransverseFactor.simpleRoot_tied_explicit_equation
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (r w B B2 s b : GCD369CubeHahnRegular k)
    (hw : w = GCD369CubeHahnRegular.monomial T.delta T.hdelta.le * s)
    (hB : GCD369CubeHahnRegular.monomial (T.delta / 2)
        (div_nonneg T.hdelta.le (by norm_num)) * B =
      GCD369CubeHahnRegular.monomial T.delta T.hdelta.le * b)
    (hx : S.normal.sextic.regularX = -2 * r + w)
    (hY : T.Yn = r * T.Xn +
      GCD369CubeHahnRegular.monomial (T.delta / 2)
        (div_nonneg T.hdelta.le (by norm_num)) * B +
      GCD369CubeHahnRegular.monomial T.delta T.hdelta.le * B2) :
    let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
    let E := GCD369CubeHahnRegular.ratCast (3 / 8) * T.Xn *
      (T.Xn * S.normal.sextic.regularX + 2 * T.Yn)
    let E1 := GCD369CubeHahnRegular.ratCast (3 / 8) * T.Xn *
      (T.Xn * s + 2 * (b + B2))
    E = H * E1 := by
  dsimp only
  rw [hx, hY, hw, hB]
  ring

end GCD369CubeHahnCommonValueData

#print axioms
  GCD369CubeHahnCommonValueData.TransverseFactor.simpleRoot_tied_chart_equations
#print axioms
  GCD369CubeHahnCommonValueData.TransverseFactor.simpleRoot_tied_explicit_equation
