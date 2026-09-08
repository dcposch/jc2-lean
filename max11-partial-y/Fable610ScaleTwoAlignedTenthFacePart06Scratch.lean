import Fable610ScaleTwoAlignedNinthFaceScratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

/-- Peeled square-chamber form of the consumed degree-`5` row
(`h₀⁴⁰ · h₀² · h₀ · h₀` cancelled along the seventh-face
divisibilities, the eighth-face product divisor `u₂`, and the NEW
μ-loaded divisor `s₂`): head seeing `p₂`, `q₀` tied at `h₀⁶`.  On the
face it equals `κ₉ h₀⁶`. -/
def alignedTenthSquarePeeledRow610 {K : Type*} [CommRing K]
    (h0 w1 e1 e2 u2 s2 a0 a1 a2 b0 : K[X])
    (κ μ κ₃ ν κ₅ ν₂ κ₇ μ₃ : K) : K[X] :=
  ((184320 : K[X]) * e1 ^ 2 * e2 ^ 2 + (737280 : K[X]) * e1 ^ 2 * u2 *
    w1 ^ 2 - (44789760 : K[X]) * e1 ^ 2 * w1 ^ 2 * a2 + (40960 : K[X]) *
    e2 ^ 2 * u2 - (2488320 : K[X]) * e2 ^ 2 * a2 + (92160 : K[X]) * u2 ^ 2
    * w1 ^ 2 - (14929920 : K[X]) * u2 * w1 ^ 2 * a2 - (135 : K[X]) * s2 +
    (604661760 : K[X]) * w1 ^ 2 * a2 ^ 2 + Polynomial.C μ * ((2268 : K[X])
    * e1 * w1 ^ 5)) + h0 * (-((387072 : K[X]) * e1 ^ 5) - (2580480 : K[X])
    * e1 ^ 3 * u2 + (29859840 : K[X]) * e1 ^ 3 * a2 - (798720 : K[X]) * e1
    * u2 ^ 2 + (59719680 : K[X]) * e1 * u2 * a2 - (604661760 : K[X]) * e1
    * a2 ^ 2 - Polynomial.C ν * ((81 : K[X]) * w1 ^ 5) + Polynomial.C μ *
    ((15120 : K[X]) * e1 ^ 2 * w1 ^ 3) + Polynomial.C μ * ((2520 : K[X]) *
    u2 * w1 ^ 3) - Polynomial.C μ * ((326592 : K[X]) * w1 ^ 3 * a2) -
    Polynomial.C κ * ((73728 : K[X]) * e1 * e2 ^ 2) - Polynomial.C κ *
    ((221184 : K[X]) * e1 * u2 * w1 ^ 2) + Polynomial.C κ * ((17915904 :
    K[X]) * e1 * w1 ^ 2 * a2)) + h0 ^ 2 * ((268738560 : K[X]) * e1 ^ 2 *
    w1 * a1 - (44789760 : K[X]) * e1 * e2 * a1 + (44789760 : K[X]) * u2 *
    w1 * a1 - (3627970560 : K[X]) * w1 * a1 * a2 - Polynomial.C ν * ((1080
    : K[X]) * e1 * w1 ^ 3) - Polynomial.C μ * ((221760 : K[X]) * e1 ^ 3 *
    w1) + Polynomial.C μ * ((40320 : K[X]) * e1 ^ 2 * e2) - Polynomial.C μ
    * ((100800 : K[X]) * e1 * u2 * w1) + Polynomial.C μ * ((6531840 :
    K[X]) * e1 * w1 * a2) + Polynomial.C μ * ((13440 : K[X]) * e2 * u2) -
    Polynomial.C μ * ((870912 : K[X]) * e2 * a2) + Polynomial.C κ *
    ((276480 : K[X]) * e1 ^ 4) + Polynomial.C κ * ((1105920 : K[X]) * e1 ^
    2 * u2) - Polynomial.C κ * ((17915904 : K[X]) * e1 ^ 2 * a2) +
    Polynomial.C κ * ((110592 : K[X]) * u2 ^ 2) - Polynomial.C κ *
    ((11943936 : K[X]) * u2 * a2) + Polynomial.C κ * ((241864704 : K[X]) *
    a2 ^ 2)) + h0 ^ 3 * (Polynomial.C ν₂ * ((9 : K[X]) * w1 ^ 3) -
    Polynomial.C ν * ((15120 : K[X]) * e1 ^ 2 * w1) + Polynomial.C ν *
    ((2880 : K[X]) * e1 * e2) - Polynomial.C ν * ((2160 : K[X]) * u2 * w1)
    + Polynomial.C ν * ((233280 : K[X]) * w1 * a2) + Polynomial.C μ *
    ((1959552 : K[X]) * w1 ^ 2 * a1) - Polynomial.C κ * ((107495424 :
    K[X]) * e1 * w1 * a1) + Polynomial.C κ * ((17915904 : K[X]) * e2 *
    a1)) + h0 ^ 4 * (-((201553920 : K[X]) * e1 ^ 2 * a0) - (134369280 :
    K[X]) * u2 * a0 + (10883911680 : K[X]) * a0 * a2 + (5441955840 : K[X])
    * a1 ^ 2 + Polynomial.C ν₂ * ((324 : K[X]) * e1 * w1) - Polynomial.C
    ν₂ * ((72 : K[X]) * e2) + Polynomial.C κ₅ * ((1152 : K[X]) * e1 ^ 2) +
    Polynomial.C κ₅ * ((768 : K[X]) * u2) - Polynomial.C κ₅ * ((62208 :
    K[X]) * a2) - Polynomial.C μ * ((7838208 : K[X]) * e1 * a1)) + h0 ^ 5
    * (-(Polynomial.C μ₃ * (w1)) - Polynomial.C κ₇ * ((72 : K[X]) * e1) -
    Polynomial.C ν * ((1399680 : K[X]) * a1) - Polynomial.C μ * ((23514624
    : K[X]) * w1 * a0) + Polynomial.C κ * ((161243136 : K[X]) * e1 * a0))
    + h0 ^ 6 * (-((9795520512 : K[X]) * b0) - Polynomial.C κ₃ * ((20155392
    : K[X]) * a0))

end Max11DegreeRoutes
