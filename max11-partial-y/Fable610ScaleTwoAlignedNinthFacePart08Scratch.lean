import LowScale68ScaleTwoAlignedNonsquareDivisibility

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

/-- Thrice-peeled square-chamber form of the consumed degree-`6` row
(`h₀³⁶ · h₀³` cancelled along the seventh-face divisibilities and the
eighth-face product divisor `u₂`): head
`27 w₁³ (10240 e₁³ - 7 μ w₁³) - 5120 e₂³`, `q₁` tied at `h₀⁵`.  On the
face it equals `μ₃ h₀⁶`. -/
def alignedNinthSquarePeeledRow610 {K : Type*} [CommRing K]
    (h0 w1 e1 e2 u2 a0 a1 a2 b1 : K[X]) (κ μ κ₃ ν κ₅ ν₂ κ₇ : K) :
    K[X] :=
  ((276480 : K[X]) * e1 ^ 3 * w1 ^ 3 - (5120 : K[X]) * e2 ^ 3 - Polynomial.C
    μ * ((189 : K[X]) * w1 ^ 6)) + h0 * (-((967680 : K[X]) * e1 ^ 4 * w1) +
    (184320 : K[X]) * e1 ^ 3 * e2 - (829440 : K[X]) * e1 ^ 2 * u2 * w1 +
    (44789760 : K[X]) * e1 ^ 2 * w1 * a2 + (184320 : K[X]) * e1 * e2 * u2 -
    (7464960 : K[X]) * e1 * e2 * a2 - (46080 : K[X]) * u2 ^ 2 * w1 +
    (7464960 : K[X]) * u2 * w1 * a2 - (302330880 : K[X]) * w1 * a2 ^ 2 -
    Polynomial.C μ * ((2268 : K[X]) * e1 * w1 ^ 4)) + h0 ^ 2 * (Polynomial.C
    ν * ((135 : K[X]) * w1 ^ 4) + Polynomial.C μ * ((15120 : K[X]) * e1 ^ 2
    * w1 ^ 2) - Polynomial.C μ * ((2688 : K[X]) * e2 ^ 2) - Polynomial.C μ *
    ((2016 : K[X]) * u2 * w1 ^ 2) + Polynomial.C μ * ((326592 : K[X]) * w1 ^
    2 * a2) + Polynomial.C κ * ((552960 : K[X]) * e1 ^ 3 * w1) -
    Polynomial.C κ * ((110592 : K[X]) * e1 ^ 2 * e2) + Polynomial.C κ *
    ((221184 : K[X]) * e1 * u2 * w1) - Polynomial.C κ * ((17915904 : K[X]) *
    e1 * w1 * a2) - Polynomial.C κ * ((36864 : K[X]) * e2 * u2) +
    Polynomial.C κ * ((2985984 : K[X]) * e2 * a2)) + h0 ^ 3 * (-((33592320 :
    K[X]) * e1 ^ 2 * a1) - (22394880 : K[X]) * u2 * a1 + (1813985280 : K[X])
    * a1 * a2 + Polynomial.C ν * ((1080 : K[X]) * e1 * w1 ^ 2) +
    Polynomial.C μ * ((20160 : K[X]) * e1 ^ 3) + Polynomial.C μ * ((40320 :
    K[X]) * e1 * u2) - Polynomial.C μ * ((1306368 : K[X]) * e1 * a2)) + h0 ^
    4 * (-((201553920 : K[X]) * e1 * w1 * a0) + (67184640 : K[X]) * e2 * a0
    - Polynomial.C ν₂ * ((27 : K[X]) * w1 ^ 2) + Polynomial.C κ₅ * ((1152 :
    K[X]) * e1 * w1) - Polynomial.C κ₅ * ((384 : K[X]) * e2) + Polynomial.C
    ν * ((2160 : K[X]) * e1 ^ 2) + Polynomial.C ν * ((1440 : K[X]) * u2) -
    Polynomial.C ν * ((233280 : K[X]) * a2) - Polynomial.C μ * ((3919104 :
    K[X]) * w1 * a1) + Polynomial.C κ * ((26873856 : K[X]) * e1 * a1)) + h0
    ^ 5 * (-((1632586752 : K[X]) * b1) - Polynomial.C κ₇ * ((36 : K[X]) *
    w1) - Polynomial.C ν₂ * ((108 : K[X]) * e1) - Polynomial.C κ₃ *
    ((3359232 : K[X]) * a1) + Polynomial.C κ * ((80621568 : K[X]) * w1 *
    a0)) + h0 ^ 6 * (-(Polynomial.C μ * ((23514624 : K[X]) * a0)))

end Max11DegreeRoutes
