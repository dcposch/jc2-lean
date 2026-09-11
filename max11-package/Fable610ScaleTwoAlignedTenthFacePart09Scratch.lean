import LowScale68ScaleTwoAlignedNonsquareDivisibility
import Grok810SpeedValLibScratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

/-- Solved block of the nonsquare tenth row after the carried
`u`- and `t₃`-substitutions and the NEW `v`-substitution peel the last
three powers of `H`: `9795520512 q₀` equals this block minus `κ₉` —
the constant enters at level ZERO. -/
def alignedTenthNonsquareSolved610 {K : Type*} [CommRing K]
    (H g1 t1 u t3 v a0 : K[X]) (κ κ₃ κ₅ κ₇ : K) : K[X] :=
  (-((387072 : K[X]) * t1 ^ 5) + (368640 : K[X]) * t1 ^ 3 * u -
    (201553920 : K[X]) * t1 ^ 2 * a0 - (92160 : K[X]) * t1 * u ^ 2 +
    (134369280 : K[X]) * u * a0 - Polynomial.C κ₇ * ((72 : K[X]) * t1) +
    Polynomial.C κ₅ * ((1152 : K[X]) * t1 ^ 2) - Polynomial.C κ₅ * ((768 :
    K[X]) * u) - Polynomial.C κ₃ * ((20155392 : K[X]) * a0) + Polynomial.C
    κ * ((276480 : K[X]) * t1 ^ 4) - Polynomial.C κ * ((221184 : K[X]) *
    t1 ^ 2 * u) + Polynomial.C κ * ((161243136 : K[X]) * t1 * a0) +
    Polynomial.C κ * ((36864 : K[X]) * u ^ 2)) + H * ((184320 : K[X]) * t1
    ^ 2 * t3 ^ 2 - (184320 : K[X]) * t1 * t3 * v - (30720 : K[X]) * u * t3
    ^ 2 + (10240 : K[X]) * t3 ^ 3 * g1 + (92160 : K[X]) * v ^ 2 -
    Polynomial.C κ * ((73728 : K[X]) * t1 * t3 ^ 2) + Polynomial.C κ *
    ((73728 : K[X]) * t3 * v))

end Max11DegreeRoutes
