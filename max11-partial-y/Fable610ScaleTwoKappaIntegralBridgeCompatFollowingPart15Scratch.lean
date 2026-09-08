import Fable610ScaleTwoKappaIntegralBridgeCompatFollowingPart07Scratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeMuScalars610

variable {F : Type*} [Field F] [CharZero F]

set_option maxHeartbeats 4000000 in
/-- Chamber-free reduction of the vanishing order-`59` head modulo
`3 s₁ = 5 a₄₁` and the `p₃₁`-killed `U`-load alone. -/
theorem bridgeMu_chamberFreeReduction610
    (w1 a41 p32 s1 u2 b62 q53 p2 q41 q3 lam : F)
    (hhead : bridgeMuJetHead610 w1 a41 p32 s1 u2 b62 q53 p2 q41 q3
      lam = 0)
    (hs : (3 : F) * s1 = (5 : F) * a41)
    (hU : (10 : F) * a41 ^ 2 - (18 : F) * b62 + (30 : F) * p2 = 0) :
    - (1120 : F) * a41 ^ 6 * w1
    + (189 : F) * a41 ^ 6 * lam
    + (220 : F) * a41 ^ 5 * p32
    + (588 : F) * a41 ^ 5 * u2
    + (9200 : F) * a41 ^ 4 * p2 * w1
    - (1260 : F) * a41 ^ 4 * p2 * lam
    - (600 : F) * a41 ^ 4 * q53
    - (3360 : F) * a41 ^ 3 * p2 * p32
    - (3360 : F) * a41 ^ 3 * p2 * u2
    - (1920 : F) * a41 ^ 3 * q41 * w1
    + (576 : F) * a41 ^ 3 * q3
    - (17280 : F) * a41 ^ 2 * p2 ^ 2 * w1
    + (2160 : F) * a41 ^ 2 * p2 ^ 2 * lam
    + (2880 : F) * a41 ^ 2 * p2 * q53
    + (2304 : F) * a41 ^ 2 * p32 * q41
    + (4800 : F) * a41 * p2 ^ 2 * p32
    + (4032 : F) * a41 * p2 ^ 2 * u2
    + (4608 : F) * a41 * p2 * q41 * w1
    - (2304 : F) * a41 * p2 * q3
    + (3840 : F) * p2 ^ 3 * w1
    - (576 : F) * p2 ^ 3 * lam
    - (1920 : F) * p2 ^ 2 * q53
    - (3072 : F) * p2 * p32 * q41 = 0 := by
  simp only [bridgeMuJetHead610] at hhead
  linear_combination (3 / 4096 : F) * hhead +
    ((1008 : F) * a41 ^ 5 * w1 - (1120 : F) * a41 ^ 4 * p32 -
      (4480 : F) * a41 ^ 3 * p2 * w1 + (3840 : F) * a41 ^ 2 * p2 * p32 +
      (3840 : F) * a41 * p2 ^ 2 * w1 - (1536 : F) * p2 ^ 2 * p32) * hs +
    ((140 : F) * a41 ^ 4 * w1 - (160 : F) * a41 ^ 3 * p32 -
      (480 : F) * a41 ^ 2 * p2 * w1 + (384 : F) * a41 * p2 * p32 +
      (192 : F) * p2 ^ 2 * w1) * hU

end BridgeMuScalars610

end Max11DegreeRoutes
