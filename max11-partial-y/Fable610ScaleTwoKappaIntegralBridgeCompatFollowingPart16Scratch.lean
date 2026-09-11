import LowScale46SourceBridge

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeMuScalars610

variable {F : Type*} [Field F] [CharZero F]

set_option maxHeartbeats 4000000 in
/-- On the pinned complement child with the `q`-jet pin the
chamber-free relation factors as `a₄₁³ · G = 0` — the honest split
`a₄₁ = 0 ∨ 15552 q₃ = -2943 λ a₄₁³ + 14040 a₄₁³ w₁ + 1060 a₄₁² p₃₂
- 11340 a₄₁² u₂ + 14040 a₄₁ q₅₃`. -/
theorem bridgeMu_complementSplit610
    (w1 a41 p32 u2 q53 q41 q3 p2 lam : F)
    (hR : - (1120 : F) * a41 ^ 6 * w1
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
    - (3072 : F) * p2 * p32 * q41 = 0)
    (hpin : (6 : F) * p2 - a41 ^ 2 = 0)
    (hq41 : (324 : F) * q41 = (35 : F) * a41 ^ 3) :
    a41 = 0 ∨
      (15552 : F) * q3 =
        -(2943 : F) * lam * a41 ^ 3 + (14040 : F) * a41 ^ 3 * w1 +
          (1060 : F) * a41 ^ 2 * p32 - (11340 : F) * a41 ^ 2 * u2 +
          (14040 : F) * a41 * q53 := by
  have hprod : a41 ^ 3 *
      ((14040 : F) * a41 ^ 3 * w1 - (2943 : F) * a41 ^ 3 * lam +
        (1060 : F) * a41 ^ 2 * p32 - (11340 : F) * a41 ^ 2 * u2 +
        (14040 : F) * a41 * q53 - (15552 : F) * q3) = 0 := by
    linear_combination (-81 : F) * hR +
      ((86760 : F) * a41 ^ 4 * w1 - (12366 : F) * a41 ^ 4 * lam -
        (34560 : F) * a41 ^ 3 * p32 - (36288 : F) * a41 ^ 3 * u2 -
        (224640 : F) * a41 ^ 2 * p2 * w1 +
        (27864 : F) * a41 ^ 2 * p2 * lam + (34560 : F) * a41 ^ 2 * q53 +
        (64800 : F) * a41 * p2 * p32 + (54432 : F) * a41 * p2 * u2 +
        (62208 : F) * a41 * q41 * w1 - (31104 : F) * a41 * q3 +
        (51840 : F) * p2 ^ 2 * w1 - (7776 : F) * p2 ^ 2 * lam -
        (25920 : F) * p2 * q53 - (41472 : F) * p32 * q41) * hpin +
      (-(288 : F) * a41 ^ 3 * w1 + (448 : F) * a41 ^ 2 * p32) * hq41
  rcases mul_eq_zero.mp hprod with h3 | hlin
  · left
    by_contra hne
    exact pow_ne_zero 3 hne h3
  · right
    linear_combination -hlin

end BridgeMuScalars610

end Max11DegreeRoutes
