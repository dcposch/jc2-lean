import LowScale68ScaleTwoAlignedNonsquareDivisibility
import Grok810SpeedValLibScratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

/-- Residue of the vanished nonsquare eleventh defect after the
carried divisor cascade (`t₁, t₂`, then the `p₂` divisor `u` squared,
then the `t₃` divisor cubed, then the `v` divisor squared) peels
`H²⁸`: an inhomogeneous relation on the carried witnesses only — no
new witness and no `q`-coefficient.  On the face it vanishes, and its
root evaluation is the first `p₀`-loaded root relation of the aligned
nonsquare tower. -/
def alignedEleventhNonsquareResidue610 {K : Type*} [CommRing K]
    (H g1 t1 u t3 v a0 : K[X]) (κ κ₅ κ₇ : K) : K[X] :=
  ((80640 : K[X]) * t1 ^ 4 * t3 - (46080 : K[X]) * t1 ^ 3 * v - (46080 :
    K[X]) * t1 ^ 2 * u * t3 + (23040 : K[X]) * t1 ^ 2 * t3 ^ 2 * g1 +
    (23040 : K[X]) * t1 * u * v - (23040 : K[X]) * t1 * t3 * v * g1 +
    (16796160 : K[X]) * t1 * t3 * a0 + (3840 : K[X]) * u ^ 2 * t3 - (3840
    : K[X]) * u * t3 ^ 2 * g1 + (1280 : K[X]) * t3 ^ 3 * g1 ^ 2 + (11520 :
    K[X]) * v ^ 2 * g1 - (16796160 : K[X]) * v * a0 + Polynomial.C κ₇ *
    ((3 : K[X]) * t3) - Polynomial.C κ₅ * ((96 : K[X]) * t1 * t3) +
    Polynomial.C κ₅ * ((96 : K[X]) * v) - Polynomial.C κ * ((46080 : K[X])
    * t1 ^ 3 * t3) + Polynomial.C κ * ((27648 : K[X]) * t1 ^ 2 * v) +
    Polynomial.C κ * ((18432 : K[X]) * t1 * u * t3) - Polynomial.C κ *
    ((9216 : K[X]) * t1 * t3 ^ 2 * g1) - Polynomial.C κ * ((9216 : K[X]) *
    u * v) + Polynomial.C κ * ((9216 : K[X]) * t3 * v * g1) - Polynomial.C
    κ * ((6718464 : K[X]) * t3 * a0)) + H * (-((5120 : K[X]) * t1 * t3 ^
    3) + (3840 : K[X]) * t3 ^ 2 * v + Polynomial.C κ * ((1024 : K[X]) * t3
    ^ 3))

end Max11DegreeRoutes
