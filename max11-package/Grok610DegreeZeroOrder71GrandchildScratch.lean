import Grok610DegreeZeroSplitChildrenScratch

/-! # Order-`71` grandchild of the `(6,10)` degree-zero post-collapse split

`Grok610DegreeZeroSplitChildrenScratch` leaves three live grandchildren:

* `p32(a) = p21(a) = 0`;
* `p32(a) = q41(a) = q3(a) = 0`;
* `q41(a) = 0` with the landed five-term cofactor.

On `p32 = p21 = 0` the ring expansion
`Q = Head0 + h · OrderOne + h^2 · OrderTwoPlus` collapses to
`Q = h^2 · OrderTwoPlus`, so the next unused compact-numerator order is
the order-`71` (`h^2`) coefficient.  The source jet is not the ring
specialization alone: `p32` and `p21` vanish at the linear root rather
than identically, and the degree-one part of `OrderOne` contributes one
more linear form in the next peels `p32 = h0 · p32n`, `p21 = h0 · p21n`.
The pole-four obstruction therefore kills the combined head
`Linear(p32n, p21n) + OrderTwo|_{p32=p21=0}`, which factors as
`p1` times a nine-term cofactor.

The same order-`71` coefficient is attempted on `p32 = q41 = q3 = 0`.
`OrderOne` vanishes identically there as well, so pole-four applies; the
combined head is an eight-term residual rather than a scalar split.

Neither grandchild is False.  The `q41 = 0` five-term arm is not used:
`OrderOne` need not vanish there, so the `h^2` coefficient is mixed with
`q41'`.  No total-degree or twice-prime theorem is used, and no chamber
is closed.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option maxHeartbeats 800000000

section LinearPoleFour610

variable {k : Type*} [Field k] [CharZero k]

local instance degreeZeroOrder71HahnCharZero610 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-- A rational function cleared by exactly four powers of a linear local
parameter cannot have a nonzero exponent-`-4` head when its derivative is a
simple pole. -/
theorem localLinearPoleFour_head_eval_zero_of_deriv_eq_simplePole610
    (a j : k) (h0 A0 : k[X]) (rho : RatFunc k)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear : algebraMap k[X] (RatFunc k) A0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 4 * rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    A0.eval a = 0 := by
  obtain ⟨c, hc, hsingle, hscaleDeriv⟩ :=
    ratFuncAtHahn68_linearRoot_single_deriv h0 a hdegree hroot
  have hrhoBoundary := localHahn_coeff_neg_of_cleared a c h0 A0 rho 4 hc
    hsingle hclear
  have hderivBoundary := localHahn_deriv_coeff_neg_succ_of_cleared
    a c h0 A0 rho 4 hc hsingle hscaleDeriv hclear
  have hmapped := congrArg (ratFuncAtHahn46 a) hderiv
  have hminusFive :
      (ratFuncAtHahn46 a (Differential.deriv rho)).coeff (-5 : ℚ) = 0 := by
    have hcoeff := congrArg
      (fun z : HahnSeries ℚ k ↦ z.coeff (-5 : ℚ)) hmapped
    simpa only [div_eq_mul_inv, map_mul, map_inv₀, ratFuncAtHahn46_C,
      hsingle,
      HahnSeries.inv_single, HahnSeries.C_mul_eq_smul,
      HahnSeries.coeff_smul, HahnSeries.coeff_single_of_ne (by norm_num :
        (-5 : ℚ) ≠ -(1 : ℚ)), smul_zero] using hcoeff
  have hrhoZero : (ratFuncAtHahn46 a rho).coeff (-4 : ℚ) = 0 := by
    norm_num at hderivBoundary
    rw [hminusFive] at hderivBoundary
    have hfour : (4 : k) ≠ 0 := by norm_num
    have hprod : (4 : k) * (ratFuncAtHahn46 a rho).coeff (-4 : ℚ) = 0 :=
      neg_eq_zero.mp hderivBoundary.symm
    exact (mul_eq_zero.mp hprod).resolve_left hfour
  norm_num at hrhoBoundary
  rw [hrhoZero] at hrhoBoundary
  have hcinv : (c ^ 4)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero 4 hc)
  exact (mul_eq_zero.mp hrhoBoundary.symm).resolve_left hcinv

end LinearPoleFour610

section DegreeZeroOrderTwoHead610

variable {R : Type*} [CommRing R]

/-- Degree-one part of the order-`70` coefficient in `(p32, p21)`. -/
def degreeZeroPostCollapseJetOrderOneLinear610
    (w1 p32 p21 p1 q41 q3 : R) : R :=
  -(38999023360671744 : R) * p1 * p21 * q41 -
    29249267520503808 * p1 * p32 * q3 +
    45498860587450368 * p1 * p32 * q41 * w1

/-- Remaining factor after the linear part is scaled out of `OrderOne`. -/
def degreeZeroPostCollapseJetOrderOneHigher610
    (h w1 a42 p32 p21 q53 q41 q3 u2 : R) : R :=
  45498860587450368*a42*p21*p32*q41 + 17062072720293888*a42*p32^2*q3 - 49290432303071232*a42*p32^2*q41*w1 + 6503598706655232*h^3*p32^5 - 7188188044197888*h^2*p32^4*u2 + 28436787867156480*h*p21*p32^2*q53 - 20537680126279680*h*p32^3*q53*w1 - 14624633760251904*p21^2*q3 + 22749430293725184*p21^2*q41*w1 + 34124145440587776*p21*p32*q3*w1 - 49290432303071232*p21*p32*q41*w1^2 - 18483912113651712*p32^2*q3*w1^2 + 26014394826620928*p32^2*q41*w1^3

set_option maxHeartbeats 4000000 in
theorem degreeZeroPostCollapseJetOrderOne610_of_linearScale
    (h w1 a42 p32 p21 p1 q53 q41 q3 u2 : R) :
    degreeZeroPostCollapseJetOrderOne610 w1 a42 (h * p32) (h * p21) p1
        q53 q41 q3 u2 =
      h * degreeZeroPostCollapseJetOrderOneLinear610 w1 p32 p21 p1 q41
          q3 +
        h ^ 2 * degreeZeroPostCollapseJetOrderOneHigher610 h w1 a42 p32
          p21 q53 q41 q3 u2 := by
  simp only [degreeZeroPostCollapseJetOrderOne610,
    degreeZeroPostCollapseJetOrderOneLinear610,
    degreeZeroPostCollapseJetOrderOneHigher610]
  ring

/-- The ring `h^2` coefficient of `Q` on `p32 = p21 = 0`. -/
def degreeZeroPostCollapseP32P21ZeroOrderTwo610
    (w1 a42 p1 q53 q41 q3 : R) : R :=
  (22749430293725184 : R) * a42 ^ 2 * p1 * q41 +
    34124145440587776 * a42 * p1 * q3 * w1 -
    49290432303071232 * a42 * p1 * q41 * w1 ^ 2 -
    24374389600419840 * p1 ^ 2 * q53 -
    12322608075767808 * p1 * q3 * w1 ^ 3 +
    13007197413310464 * p1 * q41 * w1 ^ 4

/-- Combined order-`71` source head on `p32(a) = p21(a) = 0`. -/
def degreeZeroPostCollapseP32P21ZeroOrderTwoHead610
    (w1 a42 p32n p21n p1 q53 q41 q3 : R) : R :=
  degreeZeroPostCollapseJetOrderOneLinear610 w1 p32n p21n p1 q41 q3 +
    degreeZeroPostCollapseP32P21ZeroOrderTwo610 w1 a42 p1 q53 q41 q3

/-- Nine-term cofactor of the combined order-`71` head. -/
def degreeZeroPostCollapseP32P21ZeroOrderTwoHeadCofactor610
    (w1 a42 p32n p21n p1 q53 q41 q3 : R) : R :=
  -(3024 : R) * a42 ^ 2 * q41 - 4536 * a42 * q3 * w1 +
    6552 * a42 * q41 * w1 ^ 2 + 3240 * p1 * q53 +
    5184 * p21n * q41 + 3888 * p32n * q3 -
    6048 * p32n * q41 * w1 + 1638 * q3 * w1 ^ 3 -
    1729 * q41 * w1 ^ 4

/-- The ring `h^2` coefficient of `Q` on `p32 = q41 = q3 = 0`. -/
def degreeZeroPostCollapseP32Q41Q3ZeroOrderTwo610
    (w1 a42 p21 p1 q53 u2 : R) : R :=
  (28436787867156480 : R) * a42 * p21 ^ 2 * q53 -
    24374389600419840 * p1 ^ 2 * q53 +
    56873575734312960 * p1 * p21 * q53 * w1 +
    13270501004673024 * p21 ^ 3 * u2 -
    30806520189419520 * p21 ^ 2 * q53 * w1 ^ 2

/-- Combined order-`71` source head on `p32(a) = q41(a) = q3(a) = 0`. -/
def degreeZeroPostCollapseP32Q41Q3ZeroOrderTwoHead610
    (w1 a42 p21 p1 q53 q41n q3n u2 : R) : R :=
  degreeZeroPostCollapseP32ZeroOrderOne610 w1 p21 p1 q41n q3n +
    degreeZeroPostCollapseP32Q41Q3ZeroOrderTwo610 w1 a42 p21 p1 q53 u2

/-- Remaining factor after the linear `q41, q3` peel of `OrderOne`. -/
def degreeZeroPostCollapseJetOrderOneHigherQ610
    (h w1 a42 p32n p21 p1 q53 q41n q3n u2 : R) : R :=
  17062072720293888*a42*h*p32n^2*q3n - 49290432303071232*a42*h*p32n^2*q41n*w1 + 45498860587450368*a42*p21*p32n*q41n + 6503598706655232*h^3*p32n^5 - 7188188044197888*h^2*p32n^4*u2 - 20537680126279680*h*p32n^3*q53*w1 - 18483912113651712*h*p32n^2*q3n*w1^2 + 26014394826620928*h*p32n^2*q41n*w1^3 - 29249267520503808*p1*p32n*q3n + 45498860587450368*p1*p32n*q41n*w1 + 28436787867156480*p21*p32n^2*q53 + 34124145440587776*p21*p32n*q3n*w1 - 49290432303071232*p21*p32n*q41n*w1^2

set_option maxHeartbeats 4000000 in
theorem degreeZeroPostCollapseJetOrderOne610_of_qLinearScale
    (h w1 a42 p32n p21 p1 q53 q41n q3n u2 : R) :
    degreeZeroPostCollapseJetOrderOne610 w1 a42 (h * p32n) p21 p1 q53
        (h * q41n) (h * q3n) u2 =
      h * degreeZeroPostCollapseP32ZeroOrderOne610 w1 p21 p1 q41n q3n +
        h ^ 2 * degreeZeroPostCollapseJetOrderOneHigherQ610 h w1 a42
          p32n p21 p1 q53 q41n q3n u2 := by
  simp only [degreeZeroPostCollapseJetOrderOne610,
    degreeZeroPostCollapseP32ZeroOrderOne610,
    degreeZeroPostCollapseJetOrderOneHigherQ610]
  ring

set_option maxHeartbeats 800000000 in
theorem degreeZeroPostCollapseJetOrderOne610_p32P21Zero
    (w1 a42 p32 p21 p1 q53 q41 q3 u2 : R) (hp32 : p32 = 0)
    (hp21 : p21 = 0) :
    degreeZeroPostCollapseJetOrderOne610 w1 a42 p32 p21 p1 q53 q41 q3
        u2 = 0 := by
  simp only [degreeZeroPostCollapseJetOrderOne610, hp32, hp21]
  ring

set_option maxHeartbeats 800000000 in
theorem degreeZeroPostCollapseJetHead610_p32Zero
    (p32 q41 : R) (hp32 : p32 = 0) :
    degreeZeroPostCollapseJetHead610 p32 q41 = 0 := by
  simp only [degreeZeroPostCollapseJetHead610, hp32]
  ring

set_option maxHeartbeats 800000000 in
theorem degreeZeroPostCollapseJetQuotient610_p32P21Zero
    (h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda : R)
    (hp32 : p32 = 0) (hp21 : p21 = 0) :
    degreeZeroPostCollapseJetQuotient610 h w1 a42 p32 p21 p1 p0 s2 u2
        b63 q53 q41 q3 q2 q1 lambda =
      h ^ 2 * degreeZeroPostCollapseJetOrderTwoPlus610 h w1 a42 p32 p21
        p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda := by
  rw [degreeZeroPostCollapseJetQuotient610_orderExpansion]
  simp only [degreeZeroPostCollapseJetHead610_p32Zero p32 q41 hp32,
    degreeZeroPostCollapseJetOrderOne610_p32P21Zero w1 a42 p32 p21 p1
      q53 q41 q3 u2 hp32 hp21, zero_add, mul_zero, add_zero]

set_option maxHeartbeats 800000000 in
theorem degreeZeroPostCollapseJetOrderTwoPlus610_p32P21Zero
    (h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda : R)
    (hh : h = 0) (hp32 : p32 = 0) (hp21 : p21 = 0) :
    degreeZeroPostCollapseJetOrderTwoPlus610 h w1 a42 p32 p21 p1 p0 s2
        u2 b63 q53 q41 q3 q2 q1 lambda =
      degreeZeroPostCollapseP32P21ZeroOrderTwo610 w1 a42 p1 q53 q41
        q3 := by
  simp only [degreeZeroPostCollapseJetOrderTwoPlus610,
    degreeZeroPostCollapseP32P21ZeroOrderTwo610, hh, hp32, hp21,
    mul_zero, zero_mul, zero_pow, Nat.ofNat_pos, add_zero, sub_zero]
  ring

set_option maxHeartbeats 800000000 in
theorem degreeZeroPostCollapseJetOrderTwoPlus610_p32Q41Q3Zero
    (h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda : R)
    (hh : h = 0) (hp32 : p32 = 0) (hq41 : q41 = 0) (hq3 : q3 = 0) :
    degreeZeroPostCollapseJetOrderTwoPlus610 h w1 a42 p32 p21 p1 p0 s2
        u2 b63 q53 q41 q3 q2 q1 lambda =
      degreeZeroPostCollapseP32Q41Q3ZeroOrderTwo610 w1 a42 p21 p1 q53
        u2 := by
  simp only [degreeZeroPostCollapseJetOrderTwoPlus610,
    degreeZeroPostCollapseP32Q41Q3ZeroOrderTwo610, hh, hp32, hq41, hq3,
    mul_zero, zero_mul, zero_pow, Nat.ofNat_pos, add_zero, sub_zero]
  ring

set_option maxHeartbeats 4000000 in
theorem degreeZeroPostCollapseP32P21ZeroOrderTwo610_factor
    (w1 a42 p1 q53 q41 q3 : R) :
    degreeZeroPostCollapseP32P21ZeroOrderTwo610 w1 a42 p1 q53 q41 q3 =
      -(7522959753216 : R) * p1 *
        (-(3024 : R) * a42 ^ 2 * q41 - 4536 * a42 * q3 * w1 +
          6552 * a42 * q41 * w1 ^ 2 + 3240 * p1 * q53 +
          1638 * q3 * w1 ^ 3 - 1729 * q41 * w1 ^ 4) := by
  simp only [degreeZeroPostCollapseP32P21ZeroOrderTwo610]
  ring

set_option maxHeartbeats 4000000 in
theorem degreeZeroPostCollapseP32P21ZeroOrderTwoHead610_factor
    (w1 a42 p32n p21n p1 q53 q41 q3 : R) :
    degreeZeroPostCollapseP32P21ZeroOrderTwoHead610 w1 a42 p32n p21n p1
        q53 q41 q3 =
      -(7522959753216 : R) * p1 *
        degreeZeroPostCollapseP32P21ZeroOrderTwoHeadCofactor610 w1 a42
          p32n p21n p1 q53 q41 q3 := by
  simp only [degreeZeroPostCollapseP32P21ZeroOrderTwoHead610,
    degreeZeroPostCollapseJetOrderOneLinear610,
    degreeZeroPostCollapseP32P21ZeroOrderTwo610,
    degreeZeroPostCollapseP32P21ZeroOrderTwoHeadCofactor610]
  ring

set_option maxHeartbeats 4000000 in
theorem degreeZeroPostCollapseP32Q41Q3ZeroOrderTwo610_factor
    (w1 a42 p21 p1 q53 u2 : R) :
    degreeZeroPostCollapseP32Q41Q3ZeroOrderTwo610 w1 a42 p21 p1 q53
        u2 =
      -(67706637778944 : R) *
        (-(420 : R) * a42 * p21 ^ 2 * q53 + 360 * p1 ^ 2 * q53 -
          840 * p1 * p21 * q53 * w1 - 196 * p21 ^ 3 * u2 +
          455 * p21 ^ 2 * q53 * w1 ^ 2) := by
  simp only [degreeZeroPostCollapseP32Q41Q3ZeroOrderTwo610]
  ring

end DegreeZeroOrderTwoHead610

section DegreeZeroOrderTwoEval610

variable {k : Type*} [CommRing k]

theorem degreeZeroPostCollapseJetOrderOneLinear610_eval
    (w1 p32 p21 p1 q41 q3 : k[X]) (a : k) :
    (degreeZeroPostCollapseJetOrderOneLinear610 w1 p32 p21 p1 q41
        q3).eval a =
      degreeZeroPostCollapseJetOrderOneLinear610 (w1.eval a)
        (p32.eval a) (p21.eval a) (p1.eval a) (q41.eval a)
        (q3.eval a) := by
  simp only [degreeZeroPostCollapseJetOrderOneLinear610,
    Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_neg,
    Polynomial.eval_mul, Polynomial.eval_ofNat]

theorem degreeZeroPostCollapseP32P21ZeroOrderTwo610_eval
    (w1 a42 p1 q53 q41 q3 : k[X]) (a : k) :
    (degreeZeroPostCollapseP32P21ZeroOrderTwo610 w1 a42 p1 q53 q41
        q3).eval a =
      degreeZeroPostCollapseP32P21ZeroOrderTwo610 (w1.eval a)
        (a42.eval a) (p1.eval a) (q53.eval a) (q41.eval a)
        (q3.eval a) := by
  simp only [degreeZeroPostCollapseP32P21ZeroOrderTwo610,
    Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_ofNat]

theorem degreeZeroPostCollapseP32P21ZeroOrderTwoHead610_eval
    (w1 a42 p32n p21n p1 q53 q41 q3 : k[X]) (a : k) :
    (degreeZeroPostCollapseP32P21ZeroOrderTwoHead610 w1 a42 p32n p21n
        p1 q53 q41 q3).eval a =
      degreeZeroPostCollapseP32P21ZeroOrderTwoHead610 (w1.eval a)
        (a42.eval a) (p32n.eval a) (p21n.eval a) (p1.eval a)
        (q53.eval a) (q41.eval a) (q3.eval a) := by
  simp only [degreeZeroPostCollapseP32P21ZeroOrderTwoHead610]
  rw [Polynomial.eval_add, degreeZeroPostCollapseJetOrderOneLinear610_eval,
    degreeZeroPostCollapseP32P21ZeroOrderTwo610_eval]

theorem degreeZeroPostCollapseJetOrderTwoPlus610_eval
    (h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 : k[X])
    (lambda a : k) :
    (degreeZeroPostCollapseJetOrderTwoPlus610 h w1 a42 p32 p21 p1 p0 s2
        u2 b63 q53 q41 q3 q2 q1 (Polynomial.C lambda)).eval a =
      degreeZeroPostCollapseJetOrderTwoPlus610 (h.eval a) (w1.eval a)
        (a42.eval a) (p32.eval a) (p21.eval a) (p1.eval a) (p0.eval a)
        (s2.eval a) (u2.eval a) (b63.eval a) (q53.eval a) (q41.eval a)
        (q3.eval a) (q2.eval a) (q1.eval a) lambda := by
  simp only [degreeZeroPostCollapseJetOrderTwoPlus610,
    Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_neg,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat,
    Polynomial.eval_C]

theorem degreeZeroPostCollapseP32Q41Q3ZeroOrderTwo610_eval
    (w1 a42 p21 p1 q53 u2 : k[X]) (a : k) :
    (degreeZeroPostCollapseP32Q41Q3ZeroOrderTwo610 w1 a42 p21 p1 q53
        u2).eval a =
      degreeZeroPostCollapseP32Q41Q3ZeroOrderTwo610 (w1.eval a)
        (a42.eval a) (p21.eval a) (p1.eval a) (q53.eval a)
        (u2.eval a) := by
  simp only [degreeZeroPostCollapseP32Q41Q3ZeroOrderTwo610,
    Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_ofNat]

theorem degreeZeroPostCollapseP32Q41Q3ZeroOrderTwoHead610_eval
    (w1 a42 p21 p1 q53 q41n q3n u2 : k[X]) (a : k) :
    (degreeZeroPostCollapseP32Q41Q3ZeroOrderTwoHead610 w1 a42 p21 p1
        q53 q41n q3n u2).eval a =
      degreeZeroPostCollapseP32Q41Q3ZeroOrderTwoHead610 (w1.eval a)
        (a42.eval a) (p21.eval a) (p1.eval a) (q53.eval a)
        (q41n.eval a) (q3n.eval a) (u2.eval a) := by
  simp only [degreeZeroPostCollapseP32Q41Q3ZeroOrderTwoHead610]
  rw [Polynomial.eval_add, degreeZeroPostCollapseP32ZeroOrderOne610_eval,
    degreeZeroPostCollapseP32Q41Q3ZeroOrderTwo610_eval]

end DegreeZeroOrderTwoEval610

section DegreeZeroOrderTwoSplit610

variable {F : Type*} [Field F] [CharZero F]

/-- Honest scalar split of the combined `p32 = p21 = 0` order-`71`
head. -/
theorem degreeZeroPostCollapseP32P21ZeroOrderTwoHead610_split
    (w1 a42 p32n p21n p1 q53 q41 q3 : F)
    (hhead :
      degreeZeroPostCollapseP32P21ZeroOrderTwoHead610 w1 a42 p32n p21n
        p1 q53 q41 q3 = 0) :
    p1 = 0 ∨
      degreeZeroPostCollapseP32P21ZeroOrderTwoHeadCofactor610 w1 a42
          p32n p21n p1 q53 q41 q3 = 0 := by
  rw [degreeZeroPostCollapseP32P21ZeroOrderTwoHead610_factor] at hhead
  rcases mul_eq_zero.mp hhead with hconstant | hcofactor
  · have hp1 : p1 = 0 :=
      (mul_eq_zero.mp hconstant).resolve_left (by norm_num)
    exact Or.inl hp1
  · exact Or.inr hcofactor

end DegreeZeroOrderTwoSplit610

section DegreeZeroOrderTwoSource610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 800000000 in
/-- On `p32(a) = p21(a) = 0` the simple-pole obstruction peels two more
powers of `h0` and forces the combined order-`71` head to vanish. -/
theorem degreeZeroPostCollapseP32P21ZeroOrderTwoHead610_zero_of_primitiveDeriv
    (h0 w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 : k[X])
    (lambda j a : k) (hh0 : h0 ≠ 0) (hdegree : h0.natDegree = 1)
    (hroot : h0.eval a = 0) (hp32 : p32.eval a = 0)
    (hp21 : p21.eval a = 0)
    (hderiv :
      Differential.deriv
          ((58498535041007616 : RatFunc k) *
            degreeZeroPostCollapsePrimitive610
              (algebraMap k[X] (RatFunc k) h0)
              (algebraMap k[X] (RatFunc k) w1)
              (algebraMap k[X] (RatFunc k) a42)
              (algebraMap k[X] (RatFunc k) p32)
              (algebraMap k[X] (RatFunc k) p21)
              (algebraMap k[X] (RatFunc k) p1)
              (algebraMap k[X] (RatFunc k) p0)
              (algebraMap k[X] (RatFunc k) s2)
              (algebraMap k[X] (RatFunc k) u2)
              (algebraMap k[X] (RatFunc k) b63)
              (algebraMap k[X] (RatFunc k) q53)
              (algebraMap k[X] (RatFunc k) q41)
              (algebraMap k[X] (RatFunc k) q3)
              (algebraMap k[X] (RatFunc k) q2)
              (algebraMap k[X] (RatFunc k) q1) (RatFunc.C lambda)) =
        RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    ∃ p32n p21n : k[X],
      p32 = h0 * p32n ∧ p21 = h0 * p21n ∧
        degreeZeroPostCollapseP32P21ZeroOrderTwoHead610 (w1.eval a)
            (a42.eval a) (p32n.eval a) (p21n.eval a) (p1.eval a)
            (q53.eval a) (q41.eval a) (q3.eval a) = 0 := by
  let hRF : RatFunc k := algebraMap k[X] (RatFunc k) h0
  let quotient : k[X] := degreeZeroPostCollapseJetQuotient610 h0 w1 a42
    p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 (Polynomial.C lambda)
  let rho : RatFunc k :=
    (58498535041007616 : RatFunc k) *
      degreeZeroPostCollapsePrimitive610 hRF
        (algebraMap k[X] (RatFunc k) w1)
        (algebraMap k[X] (RatFunc k) a42)
        (algebraMap k[X] (RatFunc k) p32)
        (algebraMap k[X] (RatFunc k) p21)
        (algebraMap k[X] (RatFunc k) p1)
        (algebraMap k[X] (RatFunc k) p0)
        (algebraMap k[X] (RatFunc k) s2)
        (algebraMap k[X] (RatFunc k) u2)
        (algebraMap k[X] (RatFunc k) b63)
        (algebraMap k[X] (RatFunc k) q53)
        (algebraMap k[X] (RatFunc k) q41)
        (algebraMap k[X] (RatFunc k) q3)
        (algebraMap k[X] (RatFunc k) q2)
        (algebraMap k[X] (RatFunc k) q1) (RatFunc.C lambda)
  have hhRF : hRF ≠ 0 := RatFunc.algebraMap_ne_zero hh0
  have hbridge := degreeZeroPostCollapseJetQuotient610_div_eq_clearedPrimitive
    hRF (algebraMap k[X] (RatFunc k) w1)
    (algebraMap k[X] (RatFunc k) a42)
    (algebraMap k[X] (RatFunc k) p32)
    (algebraMap k[X] (RatFunc k) p21)
    (algebraMap k[X] (RatFunc k) p1)
    (algebraMap k[X] (RatFunc k) p0)
    (algebraMap k[X] (RatFunc k) s2)
    (algebraMap k[X] (RatFunc k) u2)
    (algebraMap k[X] (RatFunc k) b63)
    (algebraMap k[X] (RatFunc k) q53)
    (algebraMap k[X] (RatFunc k) q41)
    (algebraMap k[X] (RatFunc k) q3)
    (algebraMap k[X] (RatFunc k) q2)
    (algebraMap k[X] (RatFunc k) q1) (RatFunc.C lambda) hhRF
  have hmap := degreeZeroPostCollapseJetQuotient610_map
    (algebraMap k[X] (RatFunc k)) h0 w1 a42 p32 p21 p1 p0 s2 u2 b63 q53
      q41 q3 q2 q1 (Polynomial.C lambda)
  have hclear : algebraMap k[X] (RatFunc k) quotient = hRF ^ 6 * rho := by
    dsimp only [quotient, rho]
    rw [hmap]
    simp only [RatFunc.algebraMap_C]
    rw [mul_comm (hRF ^ 6), ← div_eq_iff (pow_ne_zero 6 hhRF)]
    simpa only [hRF] using hbridge
  have hquotientZero : quotient.eval a = 0 :=
    localLinearPoleSix_head_eval_zero_of_deriv_eq_simplePole610 a j h0
      quotient rho hdegree hroot hclear (by simpa [rho, hRF] using hderiv)
  obtain ⟨Q1, hQeq⟩ := linearPolynomial_dvd_of_eval_eq_zero_610 h0
    quotient a hdegree hroot hquotientZero
  have hclear5 : algebraMap k[X] (RatFunc k) Q1 = hRF ^ 5 * rho :=
    algebraMap_cancel_one_clearing_610 h0 quotient Q1 rho 5 hh0 hQeq
      (by simpa [hRF] using hclear)
  have hQ1zero : Q1.eval a = 0 :=
    localLinearPoleFive_head_eval_zero_of_deriv_eq_simplePole610 a j h0
      Q1 rho hdegree hroot hclear5 (by simpa [rho, hRF] using hderiv)
  obtain ⟨Q2, hQ1eq⟩ := linearPolynomial_dvd_of_eval_eq_zero_610 h0 Q1 a
    hdegree hroot hQ1zero
  have hclear4 : algebraMap k[X] (RatFunc k) Q2 = hRF ^ 4 * rho :=
    algebraMap_cancel_one_clearing_610 h0 Q1 Q2 rho 4 hh0 hQ1eq hclear5
  have hQ2zero : Q2.eval a = 0 :=
    localLinearPoleFour_head_eval_zero_of_deriv_eq_simplePole610 a j h0
      Q2 rho hdegree hroot hclear4 (by simpa [rho, hRF] using hderiv)
  obtain ⟨p32n, hp32eq⟩ := linearPolynomial_dvd_of_eval_eq_zero_610 h0
    p32 a hdegree hroot hp32
  obtain ⟨p21n, hp21eq⟩ := linearPolynomial_dvd_of_eval_eq_zero_610 h0
    p21 a hdegree hroot hp21
  have hform := degreeZeroPostCollapseJetQuotient610_orderExpansion h0
    w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1
    (Polynomial.C lambda)
  have hOrder := degreeZeroPostCollapseJetOrderOne610_of_linearScale h0
    w1 a42 p32n p21n p1 q53 q41 q3 u2
  have hident :
      Q2 =
        (7583143431241728 : k[X]) * h0 * p32n ^ 3 * q41 +
          degreeZeroPostCollapseJetOrderOneLinear610 w1 p32n p21n p1
            q41 q3 +
          h0 * degreeZeroPostCollapseJetOrderOneHigher610 h0 w1 a42
            p32n p21n q53 q41 q3 u2 +
          degreeZeroPostCollapseJetOrderTwoPlus610 h0 w1 a42 p32 p21 p1
            p0 s2 u2 b63 q53 q41 q3 q2 q1 (Polynomial.C lambda) := by
    apply mul_left_cancel₀ hh0
    apply mul_left_cancel₀ hh0
    calc
      h0 * (h0 * Q2) = h0 * Q1 := by
        rw [hQ1eq]
      _ = quotient := hQeq.symm
      _ = degreeZeroPostCollapseJetHead610 p32 q41 +
            h0 * degreeZeroPostCollapseJetOrderOne610 w1 a42 p32 p21 p1
              q53 q41 q3 u2 +
            h0 ^ 2 * degreeZeroPostCollapseJetOrderTwoPlus610 h0 w1 a42
              p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1
              (Polynomial.C lambda) := hform
      _ = h0 *
            (h0 *
              ((7583143431241728 : k[X]) * h0 * p32n ^ 3 * q41 +
                degreeZeroPostCollapseJetOrderOneLinear610 w1 p32n p21n
                  p1 q41 q3 +
                h0 * degreeZeroPostCollapseJetOrderOneHigher610 h0 w1
                  a42 p32n p21n q53 q41 q3 u2 +
                degreeZeroPostCollapseJetOrderTwoPlus610 h0 w1 a42 p32
                  p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1
                  (Polynomial.C lambda))) := by
        simp only [degreeZeroPostCollapseJetHead610, hp32eq, hp21eq,
          hOrder]
        ring
  have hQ2eval :
      Q2.eval a =
        degreeZeroPostCollapseP32P21ZeroOrderTwoHead610 (w1.eval a)
          (a42.eval a) (p32n.eval a) (p21n.eval a) (p1.eval a)
          (q53.eval a) (q41.eval a) (q3.eval a) := by
    rw [hident, degreeZeroPostCollapseP32P21ZeroOrderTwoHead610]
    simp only [Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_ofNat, hroot,
      degreeZeroPostCollapseJetOrderOneLinear610_eval]
    have hrest :
        (degreeZeroPostCollapseJetOrderTwoPlus610 h0 w1 a42 p32 p21 p1
            p0 s2 u2 b63 q53 q41 q3 q2 q1 (Polynomial.C lambda)).eval
          a =
          degreeZeroPostCollapseP32P21ZeroOrderTwo610 (w1.eval a)
            (a42.eval a) (p1.eval a) (q53.eval a) (q41.eval a)
            (q3.eval a) := by
      rw [degreeZeroPostCollapseJetOrderTwoPlus610_eval, hroot, hp32,
        hp21]
      exact degreeZeroPostCollapseJetOrderTwoPlus610_p32P21Zero 0
        (w1.eval a) (a42.eval a) 0 0 (p1.eval a) (p0.eval a)
        (s2.eval a) (u2.eval a) (b63.eval a) (q53.eval a) (q41.eval a)
        (q3.eval a) (q2.eval a) (q1.eval a) lambda rfl rfl rfl
    rw [hrest]
    ring
  refine ⟨p32n, p21n, hp32eq, hp21eq, ?_⟩
  rw [← hQ2eval]
  exact hQ2zero

theorem degreeZeroPostCollapseP32P21ZeroOrderTwoHead610_zero_of_source
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (w1 a42 p32 p21 s2 u2 b63 q53 q41 : k[X])
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hh0degree : h0.natDegree = 1) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0)
    (hw : p.coeff 5 = h0 ^ 5 * w1)
    (hp4deep : p.coeff 4 = h0 ^ 4 * a42)
    (hp3deep : p.coeff 3 = h0 ^ 2 * p32)
    (hp2deep : p.coeff 2 = h0 * p21)
    (hq8deep : q.coeff 8 = h0 ^ 8 * s2)
    (hq7deep : q.coeff 7 = h0 ^ 6 * u2)
    (hq6deep : q.coeff 6 = h0 ^ 5 * b63)
    (hq5deep : q.coeff 5 = h0 ^ 3 * q53)
    (hq4deep : q.coeff 4 = h0 * q41)
    (hp32 : p32.eval a = 0) (hp21 : p21.eval a = 0) :
    ∃ p32n p21n : k[X],
      p32 = h0 * p32n ∧ p21 = h0 * p21n ∧
        degreeZeroPostCollapseP32P21ZeroOrderTwoHead610 (w1.eval a)
            (a42.eval a) (p32n.eval a) (p21n.eval a)
            ((p.coeff 1).eval a) (q53.eval a) (q41.eval a)
            ((q.coeff 3).eval a) = 0 :=
  degreeZeroPostCollapseP32P21ZeroOrderTwoHead610_zero_of_primitiveDeriv
    h0 w1 a42 p32 p21 (p.coeff 1) (p.coeff 0) s2 u2 b63 q53 q41
    (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda
    (58498535041007616 * j) a hh0 hh0degree hroot hp32 hp21
    (degreeZeroPostCollapsePrimitive610_deriv_eq_simplePole_of_source
      p q H h0 j lambda w1 a42 p32 p21 s2 u2 b63 q53 q41 hp hq hh0 hH
      hp6 hq10 hN hD hw hp4deep hp3deep hp2deep hq8deep hq7deep hq6deep
      hq5deep hq4deep)

set_option maxHeartbeats 800000000 in
/-- On `p32(a) = q41(a) = q3(a) = 0` the same pole-four obstruction
forces the combined order-`71` residual to vanish. -/
theorem degreeZeroPostCollapseP32Q41Q3ZeroOrderTwoHead610_zero_of_primitiveDeriv
    (h0 w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 : k[X])
    (lambda j a : k) (hh0 : h0 ≠ 0) (hdegree : h0.natDegree = 1)
    (hroot : h0.eval a = 0) (hp32 : p32.eval a = 0)
    (hq41 : q41.eval a = 0) (hq3 : q3.eval a = 0)
    (hderiv :
      Differential.deriv
          ((58498535041007616 : RatFunc k) *
            degreeZeroPostCollapsePrimitive610
              (algebraMap k[X] (RatFunc k) h0)
              (algebraMap k[X] (RatFunc k) w1)
              (algebraMap k[X] (RatFunc k) a42)
              (algebraMap k[X] (RatFunc k) p32)
              (algebraMap k[X] (RatFunc k) p21)
              (algebraMap k[X] (RatFunc k) p1)
              (algebraMap k[X] (RatFunc k) p0)
              (algebraMap k[X] (RatFunc k) s2)
              (algebraMap k[X] (RatFunc k) u2)
              (algebraMap k[X] (RatFunc k) b63)
              (algebraMap k[X] (RatFunc k) q53)
              (algebraMap k[X] (RatFunc k) q41)
              (algebraMap k[X] (RatFunc k) q3)
              (algebraMap k[X] (RatFunc k) q2)
              (algebraMap k[X] (RatFunc k) q1) (RatFunc.C lambda)) =
        RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    ∃ p32n q41n q3n : k[X],
      p32 = h0 * p32n ∧ q41 = h0 * q41n ∧ q3 = h0 * q3n ∧
        degreeZeroPostCollapseP32Q41Q3ZeroOrderTwoHead610 (w1.eval a)
            (a42.eval a) (p21.eval a) (p1.eval a) (q53.eval a)
            (q41n.eval a) (q3n.eval a) (u2.eval a) = 0 := by
  let hRF : RatFunc k := algebraMap k[X] (RatFunc k) h0
  let quotient : k[X] := degreeZeroPostCollapseJetQuotient610 h0 w1 a42
    p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 (Polynomial.C lambda)
  let rho : RatFunc k :=
    (58498535041007616 : RatFunc k) *
      degreeZeroPostCollapsePrimitive610 hRF
        (algebraMap k[X] (RatFunc k) w1)
        (algebraMap k[X] (RatFunc k) a42)
        (algebraMap k[X] (RatFunc k) p32)
        (algebraMap k[X] (RatFunc k) p21)
        (algebraMap k[X] (RatFunc k) p1)
        (algebraMap k[X] (RatFunc k) p0)
        (algebraMap k[X] (RatFunc k) s2)
        (algebraMap k[X] (RatFunc k) u2)
        (algebraMap k[X] (RatFunc k) b63)
        (algebraMap k[X] (RatFunc k) q53)
        (algebraMap k[X] (RatFunc k) q41)
        (algebraMap k[X] (RatFunc k) q3)
        (algebraMap k[X] (RatFunc k) q2)
        (algebraMap k[X] (RatFunc k) q1) (RatFunc.C lambda)
  have hhRF : hRF ≠ 0 := RatFunc.algebraMap_ne_zero hh0
  have hbridge := degreeZeroPostCollapseJetQuotient610_div_eq_clearedPrimitive
    hRF (algebraMap k[X] (RatFunc k) w1)
    (algebraMap k[X] (RatFunc k) a42)
    (algebraMap k[X] (RatFunc k) p32)
    (algebraMap k[X] (RatFunc k) p21)
    (algebraMap k[X] (RatFunc k) p1)
    (algebraMap k[X] (RatFunc k) p0)
    (algebraMap k[X] (RatFunc k) s2)
    (algebraMap k[X] (RatFunc k) u2)
    (algebraMap k[X] (RatFunc k) b63)
    (algebraMap k[X] (RatFunc k) q53)
    (algebraMap k[X] (RatFunc k) q41)
    (algebraMap k[X] (RatFunc k) q3)
    (algebraMap k[X] (RatFunc k) q2)
    (algebraMap k[X] (RatFunc k) q1) (RatFunc.C lambda) hhRF
  have hmap := degreeZeroPostCollapseJetQuotient610_map
    (algebraMap k[X] (RatFunc k)) h0 w1 a42 p32 p21 p1 p0 s2 u2 b63 q53
      q41 q3 q2 q1 (Polynomial.C lambda)
  have hclear : algebraMap k[X] (RatFunc k) quotient = hRF ^ 6 * rho := by
    dsimp only [quotient, rho]
    rw [hmap]
    simp only [RatFunc.algebraMap_C]
    rw [mul_comm (hRF ^ 6), ← div_eq_iff (pow_ne_zero 6 hhRF)]
    simpa only [hRF] using hbridge
  have hquotientZero : quotient.eval a = 0 :=
    localLinearPoleSix_head_eval_zero_of_deriv_eq_simplePole610 a j h0
      quotient rho hdegree hroot hclear (by simpa [rho, hRF] using hderiv)
  obtain ⟨Q1, hQeq⟩ := linearPolynomial_dvd_of_eval_eq_zero_610 h0
    quotient a hdegree hroot hquotientZero
  have hclear5 : algebraMap k[X] (RatFunc k) Q1 = hRF ^ 5 * rho :=
    algebraMap_cancel_one_clearing_610 h0 quotient Q1 rho 5 hh0 hQeq
      (by simpa [hRF] using hclear)
  have hQ1zero : Q1.eval a = 0 :=
    localLinearPoleFive_head_eval_zero_of_deriv_eq_simplePole610 a j h0
      Q1 rho hdegree hroot hclear5 (by simpa [rho, hRF] using hderiv)
  obtain ⟨Q2, hQ1eq⟩ := linearPolynomial_dvd_of_eval_eq_zero_610 h0 Q1 a
    hdegree hroot hQ1zero
  have hclear4 : algebraMap k[X] (RatFunc k) Q2 = hRF ^ 4 * rho :=
    algebraMap_cancel_one_clearing_610 h0 Q1 Q2 rho 4 hh0 hQ1eq hclear5
  have hQ2zero : Q2.eval a = 0 :=
    localLinearPoleFour_head_eval_zero_of_deriv_eq_simplePole610 a j h0
      Q2 rho hdegree hroot hclear4 (by simpa [rho, hRF] using hderiv)
  obtain ⟨p32n, hp32eq⟩ := linearPolynomial_dvd_of_eval_eq_zero_610 h0
    p32 a hdegree hroot hp32
  obtain ⟨q41n, hq41eq⟩ := linearPolynomial_dvd_of_eval_eq_zero_610 h0
    q41 a hdegree hroot hq41
  obtain ⟨q3n, hq3eq⟩ := linearPolynomial_dvd_of_eval_eq_zero_610 h0 q3
    a hdegree hroot hq3
  have hform := degreeZeroPostCollapseJetQuotient610_orderExpansion h0
    w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1
    (Polynomial.C lambda)
  have hOrder := degreeZeroPostCollapseJetOrderOne610_of_qLinearScale
    h0 w1 a42 p32n p21 p1 q53 q41n q3n u2
  have hident :
      Q2 =
        (7583143431241728 : k[X]) * h0 * p32n ^ 3 * q41 +
          degreeZeroPostCollapseP32ZeroOrderOne610 w1 p21 p1 q41n q3n +
          h0 * degreeZeroPostCollapseJetOrderOneHigherQ610 h0 w1 a42
            p32n p21 p1 q53 q41n q3n u2 +
          degreeZeroPostCollapseJetOrderTwoPlus610 h0 w1 a42 p32 p21 p1
            p0 s2 u2 b63 q53 q41 q3 q2 q1 (Polynomial.C lambda) := by
    apply mul_left_cancel₀ hh0
    apply mul_left_cancel₀ hh0
    calc
      h0 * (h0 * Q2) = h0 * Q1 := by
        rw [hQ1eq]
      _ = quotient := hQeq.symm
      _ = degreeZeroPostCollapseJetHead610 p32 q41 +
            h0 * degreeZeroPostCollapseJetOrderOne610 w1 a42 p32 p21 p1
              q53 q41 q3 u2 +
            h0 ^ 2 * degreeZeroPostCollapseJetOrderTwoPlus610 h0 w1 a42
              p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1
              (Polynomial.C lambda) := hform
      _ = h0 *
            (h0 *
              ((7583143431241728 : k[X]) * h0 * p32n ^ 3 * q41 +
                degreeZeroPostCollapseP32ZeroOrderOne610 w1 p21 p1 q41n
                  q3n +
                h0 * degreeZeroPostCollapseJetOrderOneHigherQ610 h0 w1
                  a42 p32n p21 p1 q53 q41n q3n u2 +
                degreeZeroPostCollapseJetOrderTwoPlus610 h0 w1 a42 p32
                  p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1
                  (Polynomial.C lambda))) := by
        simp only [degreeZeroPostCollapseJetHead610, hp32eq, hq41eq,
          hq3eq, hOrder]
        ring
  have hQ2eval :
      Q2.eval a =
        degreeZeroPostCollapseP32Q41Q3ZeroOrderTwoHead610 (w1.eval a)
          (a42.eval a) (p21.eval a) (p1.eval a) (q53.eval a)
          (q41n.eval a) (q3n.eval a) (u2.eval a) := by
    rw [hident, degreeZeroPostCollapseP32Q41Q3ZeroOrderTwoHead610]
    simp only [Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_ofNat, hroot,
      degreeZeroPostCollapseP32ZeroOrderOne610_eval]
    have hrest :
        (degreeZeroPostCollapseJetOrderTwoPlus610 h0 w1 a42 p32 p21 p1
            p0 s2 u2 b63 q53 q41 q3 q2 q1 (Polynomial.C lambda)).eval
          a =
          degreeZeroPostCollapseP32Q41Q3ZeroOrderTwo610 (w1.eval a)
            (a42.eval a) (p21.eval a) (p1.eval a) (q53.eval a)
            (u2.eval a) := by
      rw [degreeZeroPostCollapseJetOrderTwoPlus610_eval, hroot, hp32,
        hq41, hq3]
      exact degreeZeroPostCollapseJetOrderTwoPlus610_p32Q41Q3Zero 0
        (w1.eval a) (a42.eval a) 0 (p21.eval a) (p1.eval a) (p0.eval a)
        (s2.eval a) (u2.eval a) (b63.eval a) (q53.eval a) 0 0
        (q2.eval a) (q1.eval a) lambda rfl rfl rfl rfl
    rw [hrest]
    ring
  refine ⟨p32n, q41n, q3n, hp32eq, hq41eq, hq3eq, ?_⟩
  rw [← hQ2eval]
  exact hQ2zero

theorem degreeZeroPostCollapseP32Q41Q3ZeroOrderTwoHead610_zero_of_source
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (w1 a42 p32 p21 s2 u2 b63 q53 q41 : k[X])
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hh0degree : h0.natDegree = 1) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0)
    (hw : p.coeff 5 = h0 ^ 5 * w1)
    (hp4deep : p.coeff 4 = h0 ^ 4 * a42)
    (hp3deep : p.coeff 3 = h0 ^ 2 * p32)
    (hp2deep : p.coeff 2 = h0 * p21)
    (hq8deep : q.coeff 8 = h0 ^ 8 * s2)
    (hq7deep : q.coeff 7 = h0 ^ 6 * u2)
    (hq6deep : q.coeff 6 = h0 ^ 5 * b63)
    (hq5deep : q.coeff 5 = h0 ^ 3 * q53)
    (hq4deep : q.coeff 4 = h0 * q41)
    (hp32 : p32.eval a = 0) (hq41 : q41.eval a = 0)
    (hq3 : (q.coeff 3).eval a = 0) :
    ∃ p32n q41n q3n : k[X],
      p32 = h0 * p32n ∧ q41 = h0 * q41n ∧ q.coeff 3 = h0 * q3n ∧
        degreeZeroPostCollapseP32Q41Q3ZeroOrderTwoHead610 (w1.eval a)
            (a42.eval a) (p21.eval a) ((p.coeff 1).eval a)
            (q53.eval a) (q41n.eval a) (q3n.eval a) (u2.eval a) =
          0 := by
  obtain ⟨p32n, q41n, q3n, hp32eq, hq41eq, hq3eq, hhead⟩ :=
    degreeZeroPostCollapseP32Q41Q3ZeroOrderTwoHead610_zero_of_primitiveDeriv
      h0 w1 a42 p32 p21 (p.coeff 1) (p.coeff 0) s2 u2 b63 q53 q41
      (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda
      (58498535041007616 * j) a hh0 hh0degree hroot hp32 hq41 hq3
      (degreeZeroPostCollapsePrimitive610_deriv_eq_simplePole_of_source
        p q H h0 j lambda w1 a42 p32 p21 s2 u2 b63 q53 q41 hp hq hh0
        hH hp6 hq10 hN hD hw hp4deep hp3deep hp2deep hq8deep hq7deep
        hq6deep hq5deep hq4deep)
  exact ⟨p32n, q41n, q3n, hp32eq, hq41eq, hq3eq, hhead⟩

end DegreeZeroOrderTwoSource610

section DegreeZeroOrder71Grandchildren610

variable {k : Type*} [Field k] [CharZero k]

/-- Source-facing `p32(a) = p21(a) = 0` grandchild: `p1(a) = 0` or the
nine-term order-`71` cofactor vanishes on the next peels. -/
theorem degreeZeroFace610_linearRoot_p32P21ZeroGrandchild
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hh0degree : h0.natDegree = 1) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0) (hlambda : lambda ≠ 0) :
    ∃ (w1 a42 p32 p21 s2 u2 b63 q53 q41 : k[X]),
      p.coeff 5 = h0 ^ 5 * w1 ∧
      p.coeff 4 = h0 ^ 4 * a42 ∧
      p.coeff 3 = h0 ^ 2 * p32 ∧
      p.coeff 2 = h0 * p21 ∧
      q.coeff 8 = h0 ^ 8 * s2 ∧
      q.coeff 7 = h0 ^ 6 * u2 ∧
      q.coeff 6 = h0 ^ 5 * b63 ∧
      q.coeff 5 = h0 ^ 3 * q53 ∧
      q.coeff 4 = h0 * q41 ∧
      (p32.eval a = 0 ∧ p21.eval a = 0 →
        ∃ p32n p21n : k[X],
          p32 = h0 * p32n ∧ p21 = h0 * p21n ∧
            ((p.coeff 1).eval a = 0 ∨
              degreeZeroPostCollapseP32P21ZeroOrderTwoHeadCofactor610
                  (w1.eval a) (a42.eval a) (p32n.eval a)
                  (p21n.eval a) ((p.coeff 1).eval a) (q53.eval a)
                  (q41.eval a) ((q.coeff 3).eval a) = 0)) := by
  obtain ⟨w1, a42, p32, p21, s2, u2, b63, q53, q41, _nu, hw, hp4deep,
      hp3deep, hp2deep, hq8deep, hq7deep, hq6deep, hq5deep, hq4deep,
      _hpost, _hfourteenth⟩ :=
    nonzeroFace610_linearRoot_postCollapseResidual p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp6 hq10 hN hD hroot hlambda
  refine ⟨w1, a42, p32, p21, s2, u2, b63, q53, q41, hw, hp4deep,
    hp3deep, hp2deep, hq8deep, hq7deep, hq6deep, hq5deep, hq4deep, ?_⟩
  intro ⟨hp32, hp21⟩
  obtain ⟨p32n, p21n, hp32eq, hp21eq, hhead⟩ :=
    degreeZeroPostCollapseP32P21ZeroOrderTwoHead610_zero_of_source p q
      H h0 j lambda a w1 a42 p32 p21 s2 u2 b63 q53 q41 hp hq hh0
      hh0degree hH hp6 hq10 hN hD hroot hw hp4deep hp3deep hp2deep
      hq8deep hq7deep hq6deep hq5deep hq4deep hp32 hp21
  exact ⟨p32n, p21n, hp32eq, hp21eq,
    degreeZeroPostCollapseP32P21ZeroOrderTwoHead610_split (w1.eval a)
      (a42.eval a) (p32n.eval a) (p21n.eval a) ((p.coeff 1).eval a)
      (q53.eval a) (q41.eval a) ((q.coeff 3).eval a) hhead⟩

/-- Source-facing `p32(a) = q41(a) = q3(a) = 0` grandchild: the combined
eight-term order-`71` residual vanishes. -/
theorem degreeZeroFace610_linearRoot_p32Q41Q3ZeroGrandchild
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hh0degree : h0.natDegree = 1) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0) (hlambda : lambda ≠ 0) :
    ∃ (w1 a42 p32 p21 s2 u2 b63 q53 q41 : k[X]),
      p.coeff 5 = h0 ^ 5 * w1 ∧
      p.coeff 4 = h0 ^ 4 * a42 ∧
      p.coeff 3 = h0 ^ 2 * p32 ∧
      p.coeff 2 = h0 * p21 ∧
      q.coeff 8 = h0 ^ 8 * s2 ∧
      q.coeff 7 = h0 ^ 6 * u2 ∧
      q.coeff 6 = h0 ^ 5 * b63 ∧
      q.coeff 5 = h0 ^ 3 * q53 ∧
      q.coeff 4 = h0 * q41 ∧
      (p32.eval a = 0 ∧ q41.eval a = 0 ∧ (q.coeff 3).eval a = 0 →
        ∃ p32n q41n q3n : k[X],
          p32 = h0 * p32n ∧ q41 = h0 * q41n ∧
            q.coeff 3 = h0 * q3n ∧
            degreeZeroPostCollapseP32Q41Q3ZeroOrderTwoHead610
                (w1.eval a) (a42.eval a) (p21.eval a)
                ((p.coeff 1).eval a) (q53.eval a) (q41n.eval a)
                (q3n.eval a) (u2.eval a) = 0) := by
  obtain ⟨w1, a42, p32, p21, s2, u2, b63, q53, q41, _nu, hw, hp4deep,
      hp3deep, hp2deep, hq8deep, hq7deep, hq6deep, hq5deep, hq4deep,
      _hpost, _hfourteenth⟩ :=
    nonzeroFace610_linearRoot_postCollapseResidual p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp6 hq10 hN hD hroot hlambda
  refine ⟨w1, a42, p32, p21, s2, u2, b63, q53, q41, hw, hp4deep,
    hp3deep, hp2deep, hq8deep, hq7deep, hq6deep, hq5deep, hq4deep, ?_⟩
  intro ⟨hp32, hq41, hq3⟩
  exact degreeZeroPostCollapseP32Q41Q3ZeroOrderTwoHead610_zero_of_source
    p q H h0 j lambda a w1 a42 p32 p21 s2 u2 b63 q53 q41 hp hq hh0
    hh0degree hH hp6 hq10 hN hD hroot hw hp4deep hp3deep hp2deep
    hq8deep hq7deep hq6deep hq5deep hq4deep hp32 hq41 hq3

/-- Source-facing joint order-`71` grandchild packet.  This is not a
closure: each surviving arm retains a residual. -/
theorem degreeZeroFace610_linearRoot_order71Grandchildren
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hh0degree : h0.natDegree = 1) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0) (hlambda : lambda ≠ 0) :
    ∃ (w1 a42 p32 p21 s2 u2 b63 q53 q41 : k[X]),
      p.coeff 5 = h0 ^ 5 * w1 ∧
      p.coeff 4 = h0 ^ 4 * a42 ∧
      p.coeff 3 = h0 ^ 2 * p32 ∧
      p.coeff 2 = h0 * p21 ∧
      q.coeff 8 = h0 ^ 8 * s2 ∧
      q.coeff 7 = h0 ^ 6 * u2 ∧
      q.coeff 6 = h0 ^ 5 * b63 ∧
      q.coeff 5 = h0 ^ 3 * q53 ∧
      q.coeff 4 = h0 * q41 ∧
      ((p32.eval a = 0 ∧ p21.eval a = 0 ∧
          ∃ p32n p21n : k[X],
            p32 = h0 * p32n ∧ p21 = h0 * p21n ∧
              ((p.coeff 1).eval a = 0 ∨
                degreeZeroPostCollapseP32P21ZeroOrderTwoHeadCofactor610
                    (w1.eval a) (a42.eval a) (p32n.eval a)
                    (p21n.eval a) ((p.coeff 1).eval a) (q53.eval a)
                    (q41.eval a) ((q.coeff 3).eval a) = 0)) ∨
        (p32.eval a = 0 ∧ q41.eval a = 0 ∧ (q.coeff 3).eval a = 0 ∧
          ∃ p32n q41n q3n : k[X],
            p32 = h0 * p32n ∧ q41 = h0 * q41n ∧
              q.coeff 3 = h0 * q3n ∧
              degreeZeroPostCollapseP32Q41Q3ZeroOrderTwoHead610
                  (w1.eval a) (a42.eval a) (p21.eval a)
                  ((p.coeff 1).eval a) (q53.eval a) (q41n.eval a)
                  (q3n.eval a) (u2.eval a) = 0) ∨
        (q41.eval a = 0 ∧
          10 * (p32.eval a) ^ 2 * (q53.eval a) +
              (18 * (p32.eval a) * (w1.eval a) -
                27 * (p21.eval a)) * (q.coeff 3).eval a = 0)) := by
  obtain ⟨w1, a42, p32, p21, s2, u2, b63, q53, q41, _nu, hw, hp4deep,
      hp3deep, hp2deep, hq8deep, hq7deep, hq6deep, hq5deep, hq4deep,
      _hpost, hfourteenth⟩ :=
    nonzeroFace610_linearRoot_postCollapseResidual p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp6 hq10 hN hD hroot hlambda
  have hdegree := degreeZeroPostCollapseJetHead610_zero_of_source p q H
    h0 j lambda a w1 a42 p32 p21 s2 u2 b63 q53 q41 hp hq hh0 hh0degree
    hH hp6 hq10 hN hD hroot hw hp4deep hp3deep hp2deep hq8deep hq7deep
    hq6deep hq5deep hq4deep
  refine ⟨w1, a42, p32, p21, s2, u2, b63, q53, q41, hw, hp4deep,
    hp3deep, hp2deep, hq8deep, hq7deep, hq6deep, hq5deep, hq4deep, ?_⟩
  have horder_of_p32 (hp32 : p32.eval a = 0) :
      degreeZeroPostCollapseP32ZeroOrderOne610 (w1.eval a) (p21.eval a)
        ((p.coeff 1).eval a) (q41.eval a) ((q.coeff 3).eval a) = 0 :=
    degreeZeroPostCollapseP32ZeroOrderOne610_zero_of_source p q H h0 j
      lambda a w1 a42 p32 p21 s2 u2 b63 q53 q41 hp hq hh0 hh0degree hH
      hp6 hq10 hN hD hroot hw hp4deep hp3deep hp2deep hq8deep hq7deep
      hq6deep hq5deep hq4deep hp32
  rcases degreeZeroPostCollapseJetHead610_split (p32.eval a)
      (q41.eval a) hdegree with hp32 | hq41
  · have hgrand :=
      degreeZeroPostCollapseP32Zero_grandchildren610 (w1.eval a)
        (a42.eval a) (p32.eval a) (q53.eval a) (p21.eval a)
        ((p.coeff 1).eval a) (q41.eval a) ((q.coeff 3).eval a) hp32
        hfourteenth (horder_of_p32 hp32)
    rcases hgrand with hp21 | ⟨hq41', hq3⟩
    · obtain ⟨p32n, p21n, hp32eq, hp21eq, hhead⟩ :=
        degreeZeroPostCollapseP32P21ZeroOrderTwoHead610_zero_of_source
          p q H h0 j lambda a w1 a42 p32 p21 s2 u2 b63 q53 q41 hp hq
          hh0 hh0degree hH hp6 hq10 hN hD hroot hw hp4deep hp3deep
          hp2deep hq8deep hq7deep hq6deep hq5deep hq4deep hp32 hp21
      refine Or.inl ⟨hp32, hp21, p32n, p21n, hp32eq, hp21eq,
        degreeZeroPostCollapseP32P21ZeroOrderTwoHead610_split
          (w1.eval a) (a42.eval a) (p32n.eval a) (p21n.eval a)
          ((p.coeff 1).eval a) (q53.eval a) (q41.eval a)
          ((q.coeff 3).eval a) hhead⟩
    · obtain ⟨p32n, q41n, q3n, hp32eq, hq41eq, hq3eq, hhead⟩ :=
        degreeZeroPostCollapseP32Q41Q3ZeroOrderTwoHead610_zero_of_source
          p q H h0 j lambda a w1 a42 p32 p21 s2 u2 b63 q53 q41 hp hq
          hh0 hh0degree hH hp6 hq10 hN hD hroot hw hp4deep hp3deep
          hp2deep hq8deep hq7deep hq6deep hq5deep hq4deep hp32 hq41'
          hq3
      exact Or.inr (Or.inl ⟨hp32, hq41', hq3, p32n, q41n, q3n, hp32eq,
        hq41eq, hq3eq, hhead⟩)
  · have hchild :=
      degreeZeroPostCollapseQ41Zero_grandchildren610 (w1.eval a)
        (a42.eval a) (p32.eval a) (q53.eval a) (p21.eval a)
        ((p.coeff 1).eval a) (q41.eval a) ((q.coeff 3).eval a) hq41
        hfourteenth horder_of_p32
    rcases hchild with ⟨hp32, hrest⟩ | hcof
    · rcases hrest with hp21 | hq3
      · obtain ⟨p32n, p21n, hp32eq, hp21eq, hhead⟩ :=
          degreeZeroPostCollapseP32P21ZeroOrderTwoHead610_zero_of_source
            p q H h0 j lambda a w1 a42 p32 p21 s2 u2 b63 q53 q41 hp hq
            hh0 hh0degree hH hp6 hq10 hN hD hroot hw hp4deep hp3deep
            hp2deep hq8deep hq7deep hq6deep hq5deep hq4deep hp32 hp21
        refine Or.inl ⟨hp32, hp21, p32n, p21n, hp32eq, hp21eq,
          degreeZeroPostCollapseP32P21ZeroOrderTwoHead610_split
            (w1.eval a) (a42.eval a) (p32n.eval a) (p21n.eval a)
            ((p.coeff 1).eval a) (q53.eval a) (q41.eval a)
            ((q.coeff 3).eval a) hhead⟩
      · obtain ⟨p32n, q41n, q3n, hp32eq, hq41eq, hq3eq, hhead⟩ :=
          degreeZeroPostCollapseP32Q41Q3ZeroOrderTwoHead610_zero_of_source
            p q H h0 j lambda a w1 a42 p32 p21 s2 u2 b63 q53 q41 hp hq
            hh0 hh0degree hH hp6 hq10 hN hD hroot hw hp4deep hp3deep
            hp2deep hq8deep hq7deep hq6deep hq5deep hq4deep hp32 hq41
            hq3
        exact Or.inr (Or.inl ⟨hp32, hq41, hq3, p32n, q41n, q3n, hp32eq,
          hq41eq, hq3eq, hhead⟩)
    · exact Or.inr (Or.inr ⟨hq41, hcof⟩)

#print axioms localLinearPoleFour_head_eval_zero_of_deriv_eq_simplePole610
#print axioms degreeZeroPostCollapseJetOrderOne610_of_linearScale
#print axioms degreeZeroPostCollapseJetQuotient610_p32P21Zero
#print axioms degreeZeroPostCollapseJetOrderTwoPlus610_p32P21Zero
#print axioms degreeZeroPostCollapseP32P21ZeroOrderTwoHead610_factor
#print axioms degreeZeroPostCollapseP32P21ZeroOrderTwoHead610_split
#print axioms degreeZeroPostCollapseP32P21ZeroOrderTwoHead610_zero_of_source
#print axioms degreeZeroPostCollapseP32Q41Q3ZeroOrderTwoHead610_zero_of_source
#print axioms degreeZeroFace610_linearRoot_p32P21ZeroGrandchild
#print axioms degreeZeroFace610_linearRoot_p32Q41Q3ZeroGrandchild
#print axioms degreeZeroFace610_linearRoot_order71Grandchildren

end DegreeZeroOrder71Grandchildren610

end Max11DegreeRoutes
