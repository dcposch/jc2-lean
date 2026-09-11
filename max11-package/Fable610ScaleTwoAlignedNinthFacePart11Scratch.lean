import LowScale68ScaleTwoAlignedNonsquareDivisibility

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

/-- Solved block of the nonsquare ninth row after the carried
eighth-face `u`-substitution and the new `t₃`-substitution peel the
last two powers of `H`: `1632586752 q₁` equals this block outright. -/
def alignedNinthNonsquareSolved610 {K : Type*} [CommRing K]
    (H g1 t1 t2 u t3 a0 a1 : K[X]) (κ κ₃ κ₅ κ₇ : K) : K[X] :=
  (-((967680 : K[X]) * t1 ^ 4 * g1) + (184320 : K[X]) * t1 ^ 3 * t2 +
    (552960 : K[X]) * t1 ^ 2 * u * g1 - (33592320 : K[X]) * t1 ^ 2 * a1 -
    (92160 : K[X]) * t1 * t2 * u - (201553920 : K[X]) * t1 * g1 * a0 +
    (67184640 : K[X]) * t2 * a0 - (46080 : K[X]) * u ^ 2 * g1 + (22394880 :
    K[X]) * u * a1 - Polynomial.C κ₇ * ((36 : K[X]) * g1) + Polynomial.C κ₅
    * ((1152 : K[X]) * t1 * g1) - Polynomial.C κ₅ * ((384 : K[X]) * t2) -
    Polynomial.C κ₃ * ((3359232 : K[X]) * a1) + Polynomial.C κ * ((552960 :
    K[X]) * t1 ^ 3 * g1) - Polynomial.C κ * ((110592 : K[X]) * t1 ^ 2 * t2)
    - Polynomial.C κ * ((221184 : K[X]) * t1 * u * g1) + Polynomial.C κ *
    ((26873856 : K[X]) * t1 * a1) + Polynomial.C κ * ((36864 : K[X]) * t2 *
    u) + Polynomial.C κ * ((80621568 : K[X]) * g1 * a0)) + H ^ 2 * (-((5120
    : K[X]) * t3 ^ 3))

end Max11DegreeRoutes
