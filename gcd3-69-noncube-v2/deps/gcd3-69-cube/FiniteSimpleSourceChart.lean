import FiniteValueOrders

/-! # Moving-root chart identities at the source simple root

Two commutative-ring identities for the cubic value and the transverse
quadratic after translating the remaining simple root by `w`.  The first
identity uses the residual double-root relation `3 * e + 2 * d * r = 0`
and clears the denominator `3`.  Neither proof uses valuation theory.
-/

noncomputable section

/-- Three times the cubic value at `-2 * r + w`, after the residual relation
`3 * e + 2 * d * r = 0`, equals the displayed linear remainder plus the
linear `H`-correction. -/
theorem GCD369CubeSimpleSourceChart_cubic
    {R : Type*} [CommRing R] (r w H d e : R)
    (hre : 3 * e + 2 * d * r = 0) :
    3 * ((-2 * r + w) ^ 3 + (-3 * r ^ 2 + H * d) * (-2 * r + w) +
        (2 * r ^ 3 + H * e)) =
      3 * w * (9 * r ^ 2 - 6 * r * w + w ^ 2) +
        H * (3 * d * w - 8 * r * d) := by
  linear_combination H * hre

/-- The transverse quadratic at `-2 * r + w` with first-order deviation
`(M * B, -M * r * B)` and second-order correction `(H * B2, H * C2)`
equals the displayed chart form. -/
theorem GCD369CubeSimpleSourceChart_transverse
    {R : Type*} [CommRing R] (r w H M A B B2 C2 : R) :
    A * (-2 * r + w) ^ 2 +
        (r * A + M * B + H * B2) * (-2 * r + w) +
        (-2 * r ^ 2 * A - M * r * B + H * C2) =
      (A * w + M * B) * (w - 3 * r) +
        H * (B2 * (-2 * r + w) + C2) := by
  ring

/-- The moving cubic after translation to its remaining simple root. -/
def GCD369CubeSimpleSourceCubicChart
    {k : Type*} [Field k] [CharZero k]
    (delta : ℚ) (hdelta : 0 ≤ delta)
    (r w d : GCD369CubeHahnRegular k) : GCD369CubeHahnRegular k :=
  w * (9 * r ^ 2 - 6 * r * w + w ^ 2) +
    GCD369CubeHahnRegular.monomial delta hdelta *
      (d * w + GCD369CubeHahnRegular.ratCast (-8 / 3) * d * r)

/-- The transverse value after the balanced half-scale correction, evaluated
at the remaining simple root. -/
def GCD369CubeSimpleSourceTransverseChart
    {k : Type*} [Field k] [CharZero k]
    (delta : ℚ) (hdelta : 0 ≤ delta)
    (A r w B B2 C2 : GCD369CubeHahnRegular k) :
    GCD369CubeHahnRegular k :=
  GCD369CubeHahnRegular.monomial delta hdelta *
    ((A * w +
        (GCD369CubeHahnRegular.monomial (delta / 2)
          (div_nonneg hdelta (by norm_num))) * B) * (w - 3 * r) +
      GCD369CubeHahnRegular.monomial delta hdelta *
        (B2 * (-2 * r + w) + C2))

namespace GCD369CubeHahnCommonValueData

/-- The displayed simple-root coordinate expansions imply the exact cubic
and transverse chart equations used by the source order split. -/
theorem TransverseFactor.simpleRoot_chart_equations
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (r w d e B B2 C2 : GCD369CubeHahnRegular k)
    (hx : S.normal.sextic.regularX = -2 * r + w)
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
    S.cubicValue = GCD369CubeSimpleSourceCubicChart
        T.delta T.hdelta.le r w d ∧
      S.transverseValue = GCD369CubeSimpleSourceTransverseChart
        T.delta T.hdelta.le T.Xn r w B B2 C2 := by
  let H : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
  let M : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial (T.delta / 2)
      (div_nonneg T.hdelta.le (by norm_num))
  have hthree : (3 : GCD369CubeHahnRegular k) ≠ 0 := by
    intro hz
    have hc := congrArg
      (fun z : GCD369CubeHahnRegular k =>
        GCD369CubeHahnRegular.constantCoeff z) hz
    simp only [map_ofNat, map_zero] at hc
    exact (by norm_num : (3 : k) ≠ 0) hc
  have hscalar : (3 : GCD369CubeHahnRegular k) *
      GCD369CubeHahnRegular.ratCast (-8 / 3) = -8 := by
    calc
      _ = GCD369CubeHahnRegular.ratCast 3 *
          GCD369CubeHahnRegular.ratCast (-8 / 3) := by rw [map_ofNat]
      _ = GCD369CubeHahnRegular.ratCast (3 * (-8 / 3)) :=
        (map_mul _ _ _).symm
      _ = GCD369CubeHahnRegular.ratCast (-8) := by norm_num
      _ = -8 := by rw [map_neg, map_ofNat]
  constructor
  · dsimp only [cubicValue]
    rw [hx, hU, hV]
    dsimp only [GCD369CubeSimpleSourceCubicChart, H]
    apply mul_left_cancel₀ hthree
    have h3 := GCD369CubeSimpleSourceChart_cubic r w H d e hre
    calc
      3 * ((-2 * r + w) ^ 3 +
            (-3 * r ^ 2 + H * d) * (-2 * r + w) +
            (2 * r ^ 3 + H * e)) =
          3 * w * (9 * r ^ 2 - 6 * r * w + w ^ 2) +
            H * (3 * d * w - 8 * r * d) := h3
      _ = 3 * (w * (9 * r ^ 2 - 6 * r * w + w ^ 2) +
            H * (d * w +
              GCD369CubeHahnRegular.ratCast (-8 / 3) * d * r)) := by
        have hH :
            H * (3 * d * w - 8 * r * d) =
              3 * (H * (d * w +
                GCD369CubeHahnRegular.ratCast (-8 / 3) * d * r)) := by
          calc
            H * (3 * d * w - 8 * r * d) =
                3 * H * d * w + (-8) * H * d * r := by ring
            _ = 3 * H * d * w +
                  (3 * GCD369CubeHahnRegular.ratCast (-8 / 3)) *
                    H * d * r := by rw [hscalar]
            _ = 3 * (H * (d * w +
                  GCD369CubeHahnRegular.ratCast (-8 / 3) * d * r)) := by
              ring
        linear_combination hH
  · rw [T.transverseValue_eq, hx, hY, hZ]
    dsimp only [GCD369CubeSimpleSourceTransverseChart, H, M]
    linear_combination
      H * GCD369CubeSimpleSourceChart_transverse
        r w H M T.Xn B B2 C2

end GCD369CubeHahnCommonValueData

#print axioms GCD369CubeSimpleSourceChart_cubic
#print axioms GCD369CubeSimpleSourceChart_transverse
#print axioms GCD369CubeSimpleSourceCubicChart
#print axioms GCD369CubeSimpleSourceTransverseChart
#print axioms
  GCD369CubeHahnCommonValueData.TransverseFactor.simpleRoot_chart_equations
