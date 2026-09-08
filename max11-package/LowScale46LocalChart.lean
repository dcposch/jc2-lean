import LowScale46Curve

/-! # Exact local chart at the `(4,6)` weighted infinity point

The weighted-leading system has the unique infinity point `[1:0:0:0]`.
This module introduces its standard chart
`r=s⁻¹, q=Q*s⁻², B=Y*s⁻³, U=Z*s⁻⁴` and verifies that clearing weights
`4,6,7,8` in the two boundary equations and two coefficient-curve equations
gives the four full reviewed local equations.  No terms are truncated.
-/

noncomputable section

namespace Max11DegreeRoutes

section LocalChart

variable {F : Type*} [Field F] [CharZero F]

/-- The local chart's original translation parameter. -/
def localChartR46 (s : F) : F := s⁻¹

/-- The local chart's weight-two coordinate. -/
def localChartQ46 (s Q : F) : F := Q * (s⁻¹) ^ 2

/-- The local chart's weight-three coordinate. -/
def localChartB46 (s Y : F) : F := Y * (s⁻¹) ^ 3

/-- The local chart's weight-four coordinate. -/
def localChartU46 (s Z : F) : F := Z * (s⁻¹) ^ 4

/-- Since `A=2q-2r²`, this is the coefficient `A` in the local chart. -/
def localChartA46 (s Q : F) : F :=
  2 * localChartQ46 s Q - 2 * (localChartR46 s) ^ 2

/-- Weight-four clearing of the first boundary equation. -/
def localChartF46 (s Q Y Z d0 : F) : F :=
  Y + Q ^ 2 - (1 / 4 : F) * Z - d0 * s ^ 4

/-- Weight-six clearing of the second boundary equation. -/
def localChartG46
    (L s Q Y Z beta gamma delta e0 : F) : F :=
  (3 / 8 : F) * L * s - (5 / 4 : F) * L * Q * s -
    (1 / 2 : F) * beta * s ^ 3 + (5 / 8 : F) * L * Y * s +
    (15 / 8 : F) * L * Q ^ 2 * s + (3 / 2 : F) * Q * Y +
    (3 / 2 : F) * beta * Q * s ^ 3 - (5 / 16 : F) * L * Z * s +
    delta * s ^ 5 + Q ^ 3 + (5 / 8 : F) * L * Q * Y * s -
    (3 / 8 : F) * Q * Z + gamma * Q * s ^ 4 +
    (3 / 8 : F) * Y ^ 2 + (3 / 4 : F) * beta * Y * s ^ 3 -
    e0 * s ^ 6

/-- Weight-seven clearing of the first coefficient-curve equation. -/
def localChartJTwo46
    (L s Q Y Z beta gamma delta k2 : F) : F :=
  (-5 / 4 : F) * L * s + (15 / 4 : F) * L * Q * s +
    (3 / 2 : F) * beta * s ^ 3 - (15 / 4 : F) * L * Q ^ 2 * s -
    3 * beta * Q * s ^ 3 + (5 / 8 : F) * L * Z * s -
    2 * delta * s ^ 5 + (5 / 4 : F) * L * Q ^ 3 * s +
    (3 / 2 : F) * beta * Q ^ 2 * s ^ 3 -
    (5 / 8 : F) * L * Q * Z * s + 2 * delta * Q * s ^ 5 +
    (5 / 8 : F) * L * Y ^ 2 * s - (3 / 4 : F) * Y * Z +
    2 * gamma * Y * s ^ 4 - (3 / 4 : F) * beta * Z * s ^ 3 -
    k2 * s ^ 7

/-- Weight-eight clearing of the second coefficient-curve equation. -/
def localChartJOne46
    (L s Q Y Z beta gamma delta k1 : F) : F :=
  (-5 / 8 : F) * L * Y * s + (5 / 4 : F) * L * Q * Y * s +
    (3 / 2 : F) * Y ^ 2 + (3 / 2 : F) * beta * Y * s ^ 3 -
    (5 / 8 : F) * L * Q ^ 2 * Y * s - (3 / 2 : F) * Q * Y ^ 2 -
    (3 / 2 : F) * beta * Q * Y * s ^ 3 -
    (5 / 16 : F) * L * Y * Z * s + delta * Y * s ^ 5 +
    (3 / 32 : F) * Z ^ 2 - (1 / 2 : F) * gamma * Z * s ^ 4 -
    k1 * s ^ 8

/-- The first full boundary equation in the local chart. -/
theorem clear_boundaryD46_localChart
    (s Q Y Z d0 : F) (hs : s ≠ 0) :
    s ^ 4 *
        (boundaryD46 (localChartR46 s) (localChartQ46 s Q)
          (localChartB46 s Y) (localChartU46 s Z) - d0) =
      localChartF46 s Q Y Z d0 := by
  simp only [boundaryD46, localChartR46, localChartQ46, localChartB46,
    localChartU46, localChartF46]
  field_simp [hs]

/-- The second full boundary equation in the local chart. -/
theorem clear_boundaryE46_localChart
    (L s Q Y Z beta gamma delta e0 : F) (hs : s ≠ 0) :
    s ^ 6 *
        (boundaryE46 L (localChartR46 s) (localChartQ46 s Q)
          (localChartB46 s Y) (localChartU46 s Z) beta gamma delta - e0) =
      localChartG46 L s Q Y Z beta gamma delta e0 := by
  simp only [boundaryE46, localChartR46, localChartQ46, localChartB46,
    localChartU46, localChartG46]
  field_simp [hs]

/-- The first full coefficient-curve equation in the local chart. -/
theorem clear_coefficientCurveTwo46_localChart
    (L s Q Y Z beta gamma delta k2 : F) (hs : s ≠ 0) :
    s ^ 7 *
        (coefficientCurveTwo46 L (localChartA46 s Q) (localChartB46 s Y)
          (localChartU46 s Z) beta gamma delta - k2) =
      localChartJTwo46 L s Q Y Z beta gamma delta k2 := by
  simp only [coefficientCurveTwo46, localChartA46, localChartR46,
    localChartQ46, localChartB46, localChartU46, localChartJTwo46]
  field_simp [hs]
  ring

/-- The second full coefficient-curve equation in the local chart. -/
theorem clear_coefficientCurveOne46_localChart
    (L s Q Y Z beta gamma delta k1 : F) (hs : s ≠ 0) :
    s ^ 8 *
        (coefficientCurveOne46 L (localChartA46 s Q) (localChartB46 s Y)
          (localChartU46 s Z) beta gamma delta - k1) =
      localChartJOne46 L s Q Y Z beta gamma delta k1 := by
  simp only [coefficientCurveOne46, localChartA46, localChartR46,
    localChartQ46, localChartB46, localChartU46, localChartJOne46]
  field_simp [hs]
  ring

/-- Terminal contradiction in the mismatch Newton calculation.  Once the
valuation comparison has produced the two displayed initial equations and
`q₀ ≠ 0`, there is no possible leading-coefficient triple. -/
theorem mismatchLeadingSystem46_inconsistent
    (q0 y0 z0 : F) (hq0 : q0 ≠ 0)
    (hF0 : y0 + q0 ^ 2 - (1 / 4 : F) * z0 = 0)
    (hG0 : q0 *
      (q0 ^ 2 + (3 / 2 : F) * y0 - (3 / 8 : F) * z0) = 0) :
    False := by
  have hG0' : q0 ^ 2 + (3 / 2 : F) * y0 - (3 / 8 : F) * z0 = 0 :=
    (mul_eq_zero.mp hG0).resolve_left hq0
  have hz : z0 = 4 * y0 := by
    have hc : (1 / 8 : F) ≠ 0 := by norm_num
    apply mul_left_cancel₀ hc
    linear_combination hF0 - hG0'
  rw [hz] at hF0
  have hq2 : q0 ^ 2 = 0 := by
    linear_combination hF0
  exact pow_ne_zero 2 hq0 hq2

end LocalChart

end Max11DegreeRoutes
