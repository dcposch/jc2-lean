import PolynomialSource

noncomputable section
open Polynomial

/-! # Literal Faber normal form

This module peels the monic Faber basis from a normalized nonic over `k(x)`.
The high-row Jacobian equations force every free Faber coefficient to lie in
the constant field. -/

theorem GCD369CubeDepressedCoefficientDerivative_natDegree
    {k : Type*} [Field k]
    (a0 a1 a2 a3 a4 : RatFunc k) :
    (GCD369CubeRatFuncCoefficientDerivative
      (GCD369CubeDepressedSextic a0 a1 a2 a3 a4)).natDegree ≤ 4 := by
  have hD1 : GCD369CubeRatFuncDerivative (1 : RatFunc k) = 0 := by
    simpa using GCD369CubeRatFuncDerivative_C (1 : k)
  unfold GCD369CubeDepressedSextic
  simp only [GCD369CubeRatFuncCoefficientDerivative_add,
    GCD369CubeRatFuncCoefficientDerivative_monomial, hD1]
  simp
  compute_degree

theorem GCD369CubeDepressedDerivative_coeff_five
    {k : Type*} [Field k]
    (a0 a1 a2 a3 a4 : RatFunc k) :
    (derivative
      (GCD369CubeDepressedSextic a0 a1 a2 a3 a4)).coeff 5 = 6 := by
  norm_num [GCD369CubeDepressedSextic, derivative_monomial, coeff_monomial]

theorem GCD369CubeRatFuncJacobian_topRow
    {k : Type*} [Field k]
    (a0 a1 a2 a3 a4 : RatFunc k)
    (r : (RatFunc k)[X]) (m : ℕ) (hr : r.natDegree ≤ m) :
    (GCD369CubeRatFuncJacobian
      (GCD369CubeDepressedSextic a0 a1 a2 a3 a4) r).coeff (m + 5) =
      -6 * GCD369CubeRatFuncDerivative (r.coeff m) := by
  let f := GCD369CubeDepressedSextic a0 a1 a2 a3 a4
  have hDf : (GCD369CubeRatFuncCoefficientDerivative f).natDegree ≤ 4 :=
    GCD369CubeDepressedCoefficientDerivative_natDegree a0 a1 a2 a3 a4
  have hdr : (derivative r).natDegree ≤ m - 1 :=
    (natDegree_derivative_le r).trans (Nat.sub_le_sub_right hr 1)
  have hfirstDegree :
      (GCD369CubeRatFuncCoefficientDerivative f * derivative r).natDegree <
        m + 5 := by
    apply lt_of_le_of_lt natDegree_mul_le
    omega
  have hfirst :
      (GCD369CubeRatFuncCoefficientDerivative f * derivative r).coeff
        (m + 5) = 0 :=
    coeff_eq_zero_of_natDegree_lt hfirstDegree
  have hdf : (derivative f).natDegree ≤ 5 := by
    have hfdeg : f.natDegree = 6 := by
      dsimp [f, GCD369CubeDepressedSextic]
      compute_degree <;> norm_num
    apply le_trans (natDegree_derivative_le f)
    omega
  have hDr : (GCD369CubeRatFuncCoefficientDerivative r).natDegree ≤ m :=
    (GCD369CubeRatFuncCoefficientDerivative_natDegree_le r).trans hr
  unfold GCD369CubeRatFuncJacobian
  rw [coeff_sub, hfirst]
  rw [show m + 5 = 5 + m by omega,
    coeff_mul_add_eq_of_natDegree_le hdf hDr]
  rw [show (derivative f).coeff 5 = 6 by
    exact GCD369CubeDepressedDerivative_coeff_five a0 a1 a2 a3 a4]
  rw [GCD369CubeRatFuncCoefficientDerivative_coeff]
  ring

theorem GCD369CubeRatFuncJacobian_topRow_zero
    {k : Type*} [Field k] [CharZero k]
    (a0 a1 a2 a3 a4 : RatFunc k)
    (r : (RatFunc k)[X]) (m : ℕ) (hr : r.natDegree ≤ m)
    (hJ : (GCD369CubeRatFuncJacobian
      (GCD369CubeDepressedSextic a0 a1 a2 a3 a4) r).natDegree ≤ 4) :
    GCD369CubeRatFuncDerivative (r.coeff m) = 0 := by
  have hcoeff := natDegree_le_iff_coeff_eq_zero.mp hJ (m + 5) (by omega)
  rw [GCD369CubeRatFuncJacobian_topRow a0 a1 a2 a3 a4 r m hr] at hcoeff
  have h6 : (6 : RatFunc k) ≠ 0 := by norm_num
  exact (mul_eq_zero.mp hcoeff).resolve_left (neg_ne_zero.mpr h6)

theorem GCD369CubeFaberDegreeDrop
    {R : Type*} [Ring R] (r p : R[X]) (n : ℕ) (hn : 0 < n)
    (hr : r.natDegree ≤ n) (hp : p.natDegree ≤ n)
    (hpn : p.coeff n = 1) :
    (r - C (r.coeff n) * p).natDegree ≤ n - 1 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro m hm
  rw [coeff_sub, coeff_C_mul]
  by_cases hmn : m = n
  · subst m
    rw [hpn]
    simp
  · have hnm : n < m := by omega
    have hr0 := natDegree_le_iff_coeff_eq_zero.mp hr m hnm
    have hp0 := natDegree_le_iff_coeff_eq_zero.mp hp m hnm
    rw [hr0, hp0]
    simp

theorem GCD369CubeRatFuncJacobian_sub
    {k : Type*} [Field k] (p q r : (RatFunc k)[X]) :
    GCD369CubeRatFuncJacobian p (q - r) =
      GCD369CubeRatFuncJacobian p q -
        GCD369CubeRatFuncJacobian p r := by
  simp only [GCD369CubeRatFuncJacobian,
    GCD369CubeRatFuncCoefficientDerivative_sub, derivative_sub]
  ring

theorem GCD369CubeRatFuncJacobian_C_mul_of_derivative_zero
    {k : Type*} [Field k] (p q : (RatFunc k)[X]) (c : RatFunc k)
    (hc : GCD369CubeRatFuncDerivative c = 0) :
    GCD369CubeRatFuncJacobian p (C c * q) =
      C c * GCD369CubeRatFuncJacobian p q := by
  simp only [GCD369CubeRatFuncJacobian,
    GCD369CubeRatFuncCoefficientDerivative_mul,
    GCD369CubeRatFuncCoefficientDerivative_C, hc, map_zero,
    derivative_mul, derivative_C, zero_mul, zero_add]
  ring

theorem GCD369CubeRatFuncJacobian_sub_C_mul_highRows
    {k : Type*} [Field k] (p q r : (RatFunc k)[X]) (c : RatFunc k)
    (hc : GCD369CubeRatFuncDerivative c = 0)
    (hq : (GCD369CubeRatFuncJacobian p q).natDegree ≤ 4)
    (hr : (GCD369CubeRatFuncJacobian p r).natDegree ≤ 4) :
    (GCD369CubeRatFuncJacobian p (q - C c * r)).natDegree ≤ 4 := by
  rw [GCD369CubeRatFuncJacobian_sub,
    GCD369CubeRatFuncJacobian_C_mul_of_derivative_zero p r c hc]
  apply le_trans (natDegree_sub_le _ _)
  exact max_le hq ((natDegree_C_mul_le c _).trans hr)

structure GCD369CubeFaberPeel
    {k : Type*} [Field k]
    (a0 a1 a2 a3 a4 : RatFunc k)
    (q F : (RatFunc k)[X]) (n : ℕ) where
  coefficient : RatFunc k
  residual : (RatFunc k)[X]
  hcoefficient : coefficient = q.coeff n
  hresidual : residual = q - C coefficient * F
  hcoefficient_derivative :
    GCD369CubeRatFuncDerivative coefficient = 0
  hresidual_degree : residual.natDegree ≤ n - 1
  hresidual_highRows :
    (GCD369CubeRatFuncJacobian
      (GCD369CubeDepressedSextic a0 a1 a2 a3 a4) residual).natDegree ≤ 4

noncomputable def GCD369CubeFaberPeel.ofData
    {k : Type*} [Field k] [CharZero k]
    (a0 a1 a2 a3 a4 : RatFunc k)
    (q F : (RatFunc k)[X]) (n : ℕ) (hn : 0 < n)
    (hqDegree : q.natDegree ≤ n)
    (hqHigh : (GCD369CubeRatFuncJacobian
      (GCD369CubeDepressedSextic a0 a1 a2 a3 a4) q).natDegree ≤ 4)
    (hFDegree : F.natDegree ≤ n) (hFcoeff : F.coeff n = 1)
    (hFHigh : (GCD369CubeRatFuncJacobian
      (GCD369CubeDepressedSextic a0 a1 a2 a3 a4) F).natDegree ≤ 4) :
    GCD369CubeFaberPeel a0 a1 a2 a3 a4 q F n := by
  let c := q.coeff n
  let residual := q - C c * F
  have hc : GCD369CubeRatFuncDerivative c = 0 :=
    GCD369CubeRatFuncJacobian_topRow_zero
      a0 a1 a2 a3 a4 q n hqDegree hqHigh
  have hresidualDegree : residual.natDegree ≤ n - 1 := by
    exact GCD369CubeFaberDegreeDrop q F n hn hqDegree hFDegree hFcoeff
  have hresidualHigh :
      (GCD369CubeRatFuncJacobian
        (GCD369CubeDepressedSextic a0 a1 a2 a3 a4) residual).natDegree ≤ 4 :=
    GCD369CubeRatFuncJacobian_sub_C_mul_highRows _ q F c hc hqHigh hFHigh
  exact
    { coefficient := c
      residual := residual
      hcoefficient := rfl
      hresidual := rfl
      hcoefficient_derivative := hc
      hresidual_degree := hresidualDegree
      hresidual_highRows := hresidualHigh }

structure GCD369CubeFaberNormalForm
    {k : Type*} [Field k]
    (a0 a1 a2 a3 a4 : RatFunc k) (q : (RatFunc k)[X]) where
  d : RatFunc k
  c7 : RatFunc k
  c6 : RatFunc k
  c5 : RatFunc k
  c4 : RatFunc k
  c3 : RatFunc k
  c2 : RatFunc k
  c1 : RatFunc k
  c0 : RatFunc k
  hd : GCD369CubeRatFuncDerivative d = 0
  hc7 : GCD369CubeRatFuncDerivative c7 = 0
  hc6 : GCD369CubeRatFuncDerivative c6 = 0
  hc5 : GCD369CubeRatFuncDerivative c5 = 0
  hc4 : GCD369CubeRatFuncDerivative c4 = 0
  hc3 : GCD369CubeRatFuncDerivative c3 = 0
  hc2 : GCD369CubeRatFuncDerivative c2 = 0
  hc1 : GCD369CubeRatFuncDerivative c1 = 0
  hc0 : GCD369CubeRatFuncDerivative c0 = 0
  hq : q =
    GCD369CubeFaberNine a0 a1 a2 a3 a4 +
      C d * GCD369CubeFaberEight a0 a1 a2 a3 a4 +
      C c7 * GCD369CubeFaberSeven a0 a1 a2 a3 a4 +
      C c6 * GCD369CubeFaberSix a0 a1 a2 a3 a4 +
      C c5 * GCD369CubeFaberFive a0 a1 a2 a3 a4 +
      C c4 * GCD369CubeFaberFour a0 a1 a2 a3 a4 +
      C c3 * GCD369CubeFaberThree a0 a1 a2 a3 a4 +
      C c2 * GCD369CubeFaberTwo a0 a1 a2 a3 a4 +
      C c1 * GCD369CubeFaberOne a0 a1 a2 a3 a4 + C c0

set_option maxHeartbeats 4000000 in
noncomputable def GCD369CubeFaberNormalForm.ofMonic
    {k : Type*} [Field k] [CharZero k]
    (a0 a1 a2 a3 a4 : RatFunc k) (q : (RatFunc k)[X])
    (hqDegree : q.natDegree ≤ 9) (hq9 : q.coeff 9 = 1)
    (hqHigh : (GCD369CubeRatFuncJacobian
      (GCD369CubeDepressedSextic a0 a1 a2 a3 a4) q).natDegree ≤ 4) :
    GCD369CubeFaberNormalForm a0 a1 a2 a3 a4 q := by
  let F9 := GCD369CubeFaberNine a0 a1 a2 a3 a4
  let F8 := GCD369CubeFaberEight a0 a1 a2 a3 a4
  let F7 := GCD369CubeFaberSeven a0 a1 a2 a3 a4
  let F6 := GCD369CubeFaberSix a0 a1 a2 a3 a4
  let F5 := GCD369CubeFaberFive a0 a1 a2 a3 a4
  let F4 := GCD369CubeFaberFour a0 a1 a2 a3 a4
  let F3 := GCD369CubeFaberThree a0 a1 a2 a3 a4
  let F2 := GCD369CubeFaberTwo a0 a1 a2 a3 a4
  let F1 := GCD369CubeFaberOne a0 a1 a2 a3 a4
  have hF9Degree : F9.natDegree ≤ 9 := by
    dsimp [F9, GCD369CubeFaberNine]
    compute_degree
  have hF9coeff : F9.coeff 9 = 1 := by
    norm_num [F9, GCD369CubeFaberNine, coeff_add, coeff_monomial]
  have hF8Degree : F8.natDegree ≤ 8 := by
    dsimp [F8, GCD369CubeFaberEight]
    compute_degree
  have hF8coeff : F8.coeff 8 = 1 := by
    norm_num [F8, GCD369CubeFaberEight, coeff_add, coeff_monomial]
  have hF7Degree : F7.natDegree ≤ 7 := by
    dsimp [F7, GCD369CubeFaberSeven]
    compute_degree
  have hF7coeff : F7.coeff 7 = 1 := by
    norm_num [F7, GCD369CubeFaberSeven, coeff_add, coeff_monomial]
  have hF6Degree : F6.natDegree ≤ 6 := by
    dsimp [F6, GCD369CubeFaberSix, GCD369CubeDepressedSextic]
    compute_degree
  have hF6coeff : F6.coeff 6 = 1 := by
    norm_num [F6, GCD369CubeFaberSix, GCD369CubeDepressedSextic,
      coeff_add, coeff_monomial]
  have hF5Degree : F5.natDegree ≤ 5 := by
    dsimp [F5, GCD369CubeFaberFive]
    compute_degree
  have hF5coeff : F5.coeff 5 = 1 := by
    norm_num [F5, GCD369CubeFaberFive, coeff_add, coeff_monomial]
  have hF4Degree : F4.natDegree ≤ 4 := by
    dsimp [F4, GCD369CubeFaberFour]
    compute_degree
  have hF4coeff : F4.coeff 4 = 1 := by
    norm_num [F4, GCD369CubeFaberFour, coeff_add, coeff_monomial]
  have hF3Degree : F3.natDegree ≤ 3 := by
    dsimp [F3, GCD369CubeFaberThree]
    compute_degree
  have hF3coeff : F3.coeff 3 = 1 := by
    norm_num [F3, GCD369CubeFaberThree, coeff_add, coeff_monomial]
  have hF2Degree : F2.natDegree ≤ 2 := by
    dsimp [F2, GCD369CubeFaberTwo]
    compute_degree
  have hF2coeff : F2.coeff 2 = 1 := by
    norm_num [F2, GCD369CubeFaberTwo, coeff_add, coeff_monomial]
  have hF1Degree : F1.natDegree ≤ 1 := by
    dsimp [F1, GCD369CubeFaberOne]
    compute_degree
  have hF1coeff : F1.coeff 1 = 1 := by
    norm_num [F1, GCD369CubeFaberOne, coeff_monomial]
  let p9 := GCD369CubeFaberPeel.ofData a0 a1 a2 a3 a4 q F9 9 (by norm_num)
    hqDegree hqHigh hF9Degree hF9coeff
    (by simpa only [F9] using
      GCD369CubeFaberNine_highRows a0 a1 a2 a3 a4)
  let p8 := GCD369CubeFaberPeel.ofData a0 a1 a2 a3 a4 p9.residual F8 8 (by norm_num)
    p9.hresidual_degree p9.hresidual_highRows hF8Degree hF8coeff
    (by simpa only [F8] using
      GCD369CubeFaberEight_highRows a0 a1 a2 a3 a4)
  let p7 := GCD369CubeFaberPeel.ofData a0 a1 a2 a3 a4 p8.residual F7 7 (by norm_num)
    p8.hresidual_degree p8.hresidual_highRows hF7Degree hF7coeff
    (by simpa only [F7] using
      GCD369CubeFaberSeven_highRows a0 a1 a2 a3 a4)
  let p6 := GCD369CubeFaberPeel.ofData a0 a1 a2 a3 a4 p7.residual F6 6 (by norm_num)
    p7.hresidual_degree p7.hresidual_highRows hF6Degree hF6coeff
    (by simpa only [F6] using
      GCD369CubeFaberSix_highRows a0 a1 a2 a3 a4)
  let p5 := GCD369CubeFaberPeel.ofData a0 a1 a2 a3 a4 p6.residual F5 5 (by norm_num)
    p6.hresidual_degree p6.hresidual_highRows hF5Degree hF5coeff
    (by simpa only [F5] using
      GCD369CubeFaberFive_highRows a0 a1 a2 a3 a4)
  let p4 := GCD369CubeFaberPeel.ofData a0 a1 a2 a3 a4 p5.residual F4 4 (by norm_num)
    p5.hresidual_degree p5.hresidual_highRows hF4Degree hF4coeff
    (by simpa only [F4] using
      GCD369CubeFaberFour_highRows a0 a1 a2 a3 a4)
  let p3 := GCD369CubeFaberPeel.ofData a0 a1 a2 a3 a4 p4.residual F3 3 (by norm_num)
    p4.hresidual_degree p4.hresidual_highRows hF3Degree hF3coeff
    (by simpa only [F3] using
      GCD369CubeFaberThree_highRows a0 a1 a2 a3 a4)
  let p2 := GCD369CubeFaberPeel.ofData a0 a1 a2 a3 a4 p3.residual F2 2 (by norm_num)
    p3.hresidual_degree p3.hresidual_highRows hF2Degree hF2coeff
    (by simpa only [F2] using
      GCD369CubeFaberTwo_highRows a0 a1 a2 a3 a4)
  let p1 := GCD369CubeFaberPeel.ofData a0 a1 a2 a3 a4 p2.residual F1 1 (by norm_num)
    p2.hresidual_degree p2.hresidual_highRows hF1Degree hF1coeff
    (by simpa only [F1] using
      GCD369CubeFaberOne_highRows a0 a1 a2 a3 a4)
  let c0 := p1.residual.coeff 0
  have hc0 : GCD369CubeRatFuncDerivative c0 = 0 :=
    GCD369CubeRatFuncJacobian_topRow_zero a0 a1 a2 a3 a4 p1.residual 0
      p1.hresidual_degree p1.hresidual_highRows
  have hp1C : p1.residual = C c0 :=
    eq_C_of_natDegree_le_zero p1.hresidual_degree
  have hp9coefficient : p9.coefficient = 1 := by
    rw [p9.hcoefficient, hq9]
  have hp9residual := p9.hresidual
  rw [hp9coefficient, C_1, one_mul] at hp9residual
  have hqDecomposition : q =
      F9 + C p8.coefficient * F8 + C p7.coefficient * F7 +
      C p6.coefficient * F6 + C p5.coefficient * F5 +
      C p4.coefficient * F4 + C p3.coefficient * F3 +
      C p2.coefficient * F2 + C p1.coefficient * F1 + C c0 := by
    linear_combination -hp9residual - p8.hresidual - p7.hresidual -
      p6.hresidual - p5.hresidual - p4.hresidual - p3.hresidual -
      p2.hresidual - p1.hresidual + hp1C
  exact
    { d := p8.coefficient
      c7 := p7.coefficient
      c6 := p6.coefficient
      c5 := p5.coefficient
      c4 := p4.coefficient
      c3 := p3.coefficient
      c2 := p2.coefficient
      c1 := p1.coefficient
      c0 := c0
      hd := p8.hcoefficient_derivative
      hc7 := p7.hcoefficient_derivative
      hc6 := p6.hcoefficient_derivative
      hc5 := p5.hcoefficient_derivative
      hc4 := p4.hcoefficient_derivative
      hc3 := p3.hcoefficient_derivative
      hc2 := p2.hcoefficient_derivative
      hc1 := p1.hcoefficient_derivative
      hc0 := hc0
      hq := by simpa only [F9, F8, F7, F6, F5, F4, F3, F2, F1] using
        hqDecomposition }

namespace GCD369CubeFaberNormalForm

/-- The first free Faber coefficient is literally the eighth nonic
coefficient. -/
theorem d_eq_coeff_eight
    {k : Type*} [Field k]
    {a0 a1 a2 a3 a4 : RatFunc k} {q : (RatFunc k)[X]}
    (N : GCD369CubeFaberNormalForm a0 a1 a2 a3 a4 q) :
    N.d = q.coeff 8 := by
  have h := congrArg (fun p : (RatFunc k)[X] => p.coeff 8) N.hq
  norm_num [GCD369CubeFaberNine, GCD369CubeFaberEight,
    GCD369CubeFaberSeven, GCD369CubeFaberSix, GCD369CubeFaberFive,
    GCD369CubeFaberFour, GCD369CubeFaberThree, GCD369CubeFaberTwo,
    GCD369CubeFaberOne, GCD369CubeDepressedSextic,
    coeff_add, coeff_C_mul, coeff_monomial] at h
  exact h.symm

end GCD369CubeFaberNormalForm

/-- Base-field representatives of all free Faber coefficients. -/
structure GCD369CubeFaberConstantParameters
    {k : Type*} [Field k]
    {a0 a1 a2 a3 a4 : RatFunc k} {q : (RatFunc k)[X]}
    (N : GCD369CubeFaberNormalForm a0 a1 a2 a3 a4 q) where
  d : k
  c7 : k
  c6 : k
  c5 : k
  c4 : k
  c3 : k
  c2 : k
  c1 : k
  c0 : k
  hd : N.d = algebraMap k (RatFunc k) d
  hc7 : N.c7 = algebraMap k (RatFunc k) c7
  hc6 : N.c6 = algebraMap k (RatFunc k) c6
  hc5 : N.c5 = algebraMap k (RatFunc k) c5
  hc4 : N.c4 = algebraMap k (RatFunc k) c4
  hc3 : N.c3 = algebraMap k (RatFunc k) c3
  hc2 : N.c2 = algebraMap k (RatFunc k) c2
  hc1 : N.c1 = algebraMap k (RatFunc k) c1
  hc0 : N.c0 = algebraMap k (RatFunc k) c0

namespace GCD369CubeFaberNormalForm

/-- Zero derivative descends every Faber coefficient to the base field. -/
noncomputable def constantParameters
    {k : Type*} [Field k] [CharZero k]
    {a0 a1 a2 a3 a4 : RatFunc k} {q : (RatFunc k)[X]}
    (N : GCD369CubeFaberNormalForm a0 a1 a2 a3 a4 q) :
    GCD369CubeFaberConstantParameters N := by
  choose d hd using GCD369CubeRatFuncConstants N.d N.hd
  choose c7 hc7 using GCD369CubeRatFuncConstants N.c7 N.hc7
  choose c6 hc6 using GCD369CubeRatFuncConstants N.c6 N.hc6
  choose c5 hc5 using GCD369CubeRatFuncConstants N.c5 N.hc5
  choose c4 hc4 using GCD369CubeRatFuncConstants N.c4 N.hc4
  choose c3 hc3 using GCD369CubeRatFuncConstants N.c3 N.hc3
  choose c2 hc2 using GCD369CubeRatFuncConstants N.c2 N.hc2
  choose c1 hc1 using GCD369CubeRatFuncConstants N.c1 N.hc1
  choose c0 hc0 using GCD369CubeRatFuncConstants N.c0 N.hc0
  exact ⟨d, c7, c6, c5, c4, c3, c2, c1, c0,
    hd, hc7, hc6, hc5, hc4, hc3, hc2, hc1, hc0⟩

end GCD369CubeFaberNormalForm

namespace GCD369CubePolynomialSource

/-- The literal normalized nonic of a polynomial cube source admits the
constant-coefficient Faber normal form. -/
noncomputable def faberNormalForm
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k) :
    GCD369CubeFaberNormalForm
      (S.normalizedP.coeff 0) (S.normalizedP.coeff 1)
      (S.normalizedP.coeff 2) (S.normalizedP.coeff 3)
      (S.normalizedP.coeff 4) S.normalizedQ := by
  apply GCD369CubeFaberNormalForm.ofMonic
  · exact S.normalizedQ_natDegree.le
  · exact S.normalizedQ_coeff_nine
  · have hJ := S.normalized_jacobian
    rw [S.normalizedP_eq_depressed] at hJ
    rw [hJ, natDegree_C]
    norm_num

/-- The mismatch coefficient in the Faber form is the affine-alignment
constant already extracted from the literal source. -/
theorem faberNormalForm_d
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k) (delta : k)
    (hdelta : 3 * S.A - 2 * S.B = algebraMap k (RatFunc k) delta) :
    S.faberNormalForm.d = algebraMap k (RatFunc k) (-delta / 2) := by
  rw [GCD369CubeFaberNormalForm.d_eq_coeff_eight,
    S.normalizedQ_coeff_eight delta hdelta]

/-- All free coefficients of the literal source normal form, represented in
the base field. -/
noncomputable def faberConstantParameters
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k) :
    GCD369CubeFaberConstantParameters S.faberNormalForm :=
  S.faberNormalForm.constantParameters

end GCD369CubePolynomialSource

#print axioms GCD369CubeRatFuncJacobian_topRow
#print axioms GCD369CubeRatFuncJacobian_topRow_zero
#print axioms GCD369CubeFaberPeel.ofData
#print axioms GCD369CubeFaberNormalForm.ofMonic
#print axioms GCD369CubePolynomialSource.faberNormalForm
#print axioms GCD369CubePolynomialSource.faberNormalForm_d
