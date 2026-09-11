import LowScale68ScaleTwoAlignedNonsquareDivisibility
import Grok810SpeedValLibScratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

set_option maxHeartbeats 1600000000 in
/-- Peeled square-chamber form of the consumed degree-`4` row
(`h₀⁴⁴ · h₀² · h₀ · h₀` cancelled along the seventh-face
divisibilities, the eighth-face product divisor `u₂`, the tenth-face
μ-loaded divisor `s₂`, and the NEW divisor `s₄`): the FIRST aligned
square-chamber row with no `q`-coefficient at all.  On the face it
equals `μ₄ h₀⁷`. -/
def alignedEleventhSquarePeeledRow610 {K : Type*} [CommRing K]
    (h0 w1 e1 e2 u2 s2 s4 a0 a1 a2 : K[X])
    (κ μ ν κ₅ ν₂ κ₇ μ₃ : K) : K[X] :=
  (-((61931520 : K[X]) * e1 ^ 4 * w1 ^ 3) - (22118400 : K[X]) * e1 ^ 2 *
    u2 * w1 ^ 3 + (1433272320 : K[X]) * e1 ^ 2 * w1 ^ 3 * a2 + (655360 :
    K[X]) * e1 * e2 ^ 3 - (1474560 : K[X]) * u2 ^ 2 * w1 ^ 3 + (238878720
    : K[X]) * u2 * w1 ^ 3 * a2 + (2160 : K[X]) * s2 * w1 + (1215 : K[X]) *
    s4 - (9674588160 : K[X]) * w1 ^ 3 * a2 ^ 2 - Polynomial.C μ * ((21168
    : K[X]) * e1 * w1 ^ 6)) + h0 * ((61931520 : K[X]) * e1 ^ 5 * w1 -
    (10321920 : K[X]) * e1 ^ 4 * e2 + (103219200 : K[X]) * e1 ^ 3 * u2 *
    w1 - (3344302080 : K[X]) * e1 ^ 3 * w1 * a2 - (20643840 : K[X]) * e1 ^
    2 * e2 * u2 + (477757440 : K[X]) * e1 ^ 2 * e2 * a2 + (19660800 :
    K[X]) * e1 * u2 ^ 2 * w1 - (1911029760 : K[X]) * e1 * u2 * w1 * a2 +
    (38698352640 : K[X]) * e1 * w1 * a2 ^ 2 - (1638400 : K[X]) * e2 * u2 ^
    2 + (159252480 : K[X]) * e2 * u2 * a2 - (3224862720 : K[X]) * e2 * a2
    ^ 2 + Polynomial.C ν * ((540 : K[X]) * w1 ^ 6) - Polynomial.C μ *
    ((211680 : K[X]) * e1 ^ 2 * w1 ^ 4) - Polynomial.C μ * ((28224 : K[X])
    * u2 * w1 ^ 4) + Polynomial.C μ * ((3265920 : K[X]) * w1 ^ 4 * a2) +
    Polynomial.C κ * ((17694720 : K[X]) * e1 ^ 3 * w1 ^ 3) + Polynomial.C
    κ * ((3538944 : K[X]) * e1 * u2 * w1 ^ 3) - Polynomial.C κ *
    ((286654464 : K[X]) * e1 * w1 ^ 3 * a2) - Polynomial.C κ * ((131072 :
    K[X]) * e2 ^ 3)) + h0 ^ 2 * (-((2149908480 : K[X]) * e1 ^ 2 * w1 ^ 2 *
    a1) - (119439360 : K[X]) * e2 ^ 2 * a1 - (716636160 : K[X]) * u2 * w1
    ^ 2 * a1 + (58047528960 : K[X]) * w1 ^ 2 * a1 * a2 + Polynomial.C ν *
    ((10800 : K[X]) * e1 * w1 ^ 4) + Polynomial.C μ * ((887040 : K[X]) *
    e1 ^ 3 * w1 ^ 2) + Polynomial.C μ * ((215040 : K[X]) * e1 * e2 ^ 2) +
    Polynomial.C μ * ((1128960 : K[X]) * e1 * u2 * w1 ^ 2) - Polynomial.C
    μ * ((78382080 : K[X]) * e1 * w1 ^ 2 * a2) - Polynomial.C κ *
    ((35389440 : K[X]) * e1 ^ 4 * w1) + Polynomial.C κ * ((5898240 : K[X])
    * e1 ^ 3 * e2) - Polynomial.C κ * ((35389440 : K[X]) * e1 ^ 2 * u2 *
    w1) + Polynomial.C κ * ((1433272320 : K[X]) * e1 ^ 2 * w1 * a2) +
    Polynomial.C κ * ((5898240 : K[X]) * e1 * e2 * u2) - Polynomial.C κ *
    ((191102976 : K[X]) * e1 * e2 * a2) - Polynomial.C κ * ((2359296 :
    K[X]) * u2 ^ 2 * w1) + Polynomial.C κ * ((286654464 : K[X]) * u2 * w1
    * a2) - Polynomial.C κ * ((7739670528 : K[X]) * w1 * a2 ^ 2)) + h0 ^ 3
    * ((1433272320 : K[X]) * e1 ^ 3 * a1 + (2866544640 : K[X]) * e1 * u2 *
    a1 - (58047528960 : K[X]) * e1 * a1 * a2 - Polynomial.C ν₂ * ((54 :
    K[X]) * w1 ^ 4) + Polynomial.C ν * ((60480 : K[X]) * e1 ^ 2 * w1 ^ 2)
    + Polynomial.C ν * ((7680 : K[X]) * e2 ^ 2) + Polynomial.C ν * ((28800
    : K[X]) * u2 * w1 ^ 2) - Polynomial.C ν * ((2799360 : K[X]) * w1 ^ 2 *
    a2) - Polynomial.C μ * ((887040 : K[X]) * e1 ^ 4) - Polynomial.C μ *
    ((3548160 : K[X]) * e1 ^ 2 * u2) + Polynomial.C μ * ((52254720 : K[X])
    * e1 ^ 2 * a2) - Polynomial.C μ * ((376320 : K[X]) * u2 ^ 2) +
    Polynomial.C μ * ((34836480 : K[X]) * u2 * a2) - Polynomial.C μ *
    ((15676416 : K[X]) * w1 ^ 3 * a1) - Polynomial.C μ * ((564350976 :
    K[X]) * a2 ^ 2) + Polynomial.C κ * ((859963392 : K[X]) * e1 * w1 ^ 2 *
    a1)) + h0 ^ 4 * ((12899450880 : K[X]) * e1 ^ 2 * w1 * a0 - (2149908480
    : K[X]) * e1 * e2 * a0 + (2149908480 : K[X]) * u2 * w1 * a0 -
    (174142586880 : K[X]) * w1 * a0 * a2 - (87071293440 : K[X]) * w1 * a1
    ^ 2 - Polynomial.C ν₂ * ((1296 : K[X]) * e1 * w1 ^ 2) - Polynomial.C
    κ₅ * ((73728 : K[X]) * e1 ^ 2 * w1) + Polynomial.C κ₅ * ((12288 :
    K[X]) * e1 * e2) - Polynomial.C κ₅ * ((12288 : K[X]) * u2 * w1) +
    Polynomial.C κ₅ * ((995328 : K[X]) * w1 * a2) - Polynomial.C ν *
    ((80640 : K[X]) * e1 ^ 3) - Polynomial.C ν * ((161280 : K[X]) * e1 *
    u2) + Polynomial.C ν * ((3732480 : K[X]) * e1 * a2) + Polynomial.C μ *
    ((313528320 : K[X]) * e1 * w1 * a1) - Polynomial.C μ * ((41803776 :
    K[X]) * e2 * a1) - Polynomial.C κ * ((859963392 : K[X]) * e1 ^ 2 * a1)
    - Polynomial.C κ * ((573308928 : K[X]) * u2 * a1) + Polynomial.C κ *
    ((23219011584 : K[X]) * a1 * a2)) + h0 ^ 5 * (Polynomial.C μ₃ * ((4 :
    K[X]) * w1 ^ 2) + Polynomial.C κ₇ * ((2304 : K[X]) * e1 * w1) -
    Polynomial.C κ₇ * ((384 : K[X]) * e2) + Polynomial.C ν₂ * ((2592 :
    K[X]) * e1 ^ 2) + Polynomial.C ν₂ * ((1728 : K[X]) * u2) -
    Polynomial.C ν₂ * ((93312 : K[X]) * a2) + Polynomial.C ν * ((11197440
    : K[X]) * w1 * a1) + Polynomial.C μ * ((94058496 : K[X]) * w1 ^ 2 *
    a0) - Polynomial.C κ * ((5159780352 : K[X]) * e1 * w1 * a0) +
    Polynomial.C κ * ((859963392 : K[X]) * e2 * a0)) + h0 ^ 6 *
    ((522427760640 : K[X]) * a0 * a1 - Polynomial.C μ₃ * ((16 : K[X]) *
    e1) - Polynomial.C κ₅ * ((2985984 : K[X]) * a1) - Polynomial.C μ *
    ((376233984 : K[X]) * e1 * a0)) + h0 ^ 7 * (-(Polynomial.C ν *
    ((67184640 : K[X]) * a0)))

end Max11DegreeRoutes
