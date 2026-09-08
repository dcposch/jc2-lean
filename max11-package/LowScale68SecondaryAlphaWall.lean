import LowScale68SecondaryRelaxedFirstFace

/-! # Mixed first-secondary row one on the `(6,8)` wall `g = n`

After `l = 0`, the relaxed package extracts `F₄,F₃,F₂,F₀` throughout
`2g < 3n` and extracts ordinary `F₁` for `g < n`.  On the remaining wall
`g = n` the naive bound on the `alpha A^2` piece of `T` meets the row-one
face `12n-2g-1 = 10n-1`.  The colliding cores cancel as a Jacobian
identity, so the mixed leading scalar is the ordinary `(-8/81) F₁` and
`alpha` is unconstrained.  Combined with the four extracted equations this
forces the ordinary family `e = 0`, `a*b = 3*d`.  The two exceptional
four-equation families are killed by `F₁` and are written explicitly.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlphaWallFace68

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## Exact mixed row-one scalar, including `alpha`

The unique old-weight `alpha` combination at index `10n-1` is
`(4/27) n alpha a^5` from `2 T_core E_core'` minus the same quantity from
`2 C0_core V_core'`.  The difference is the zero polynomial, so the mixed
scalar does not depend on `alpha`. -/

/-- Cleared `A^5` load numerator at index `10n-1`.  Both colliding cores
contribute `(4/27) N alpha a^5`; their difference is identically zero. -/
def alphaWallOneLoadNumerator68 (N a alpha : k) : k :=
  (4 / 27 : k) * N * alpha * a ^ 5 -
    (4 / 27 : k) * N * alpha * a ^ 5

/-- Mixed row-one scalar at index `10n-1` on `g = n`, including `alpha`. -/
def alphaWallOneScalar68 (N a b c d e alpha : k) : k :=
  (-8 / 81 : k) * firstSecondaryOne68 N N a b c d e +
    alphaWallOneLoadNumerator68 N a alpha

theorem alphaWallOneLoadNumerator68_eq_zero (N a alpha : k) :
    alphaWallOneLoadNumerator68 N a alpha = 0 := by
  simp only [alphaWallOneLoadNumerator68]
  ring

theorem alphaWallOneScalar68_eq_ordinary
    (N a b c d e alpha : k) :
    alphaWallOneScalar68 N a b c d e alpha =
      (-8 / 81 : k) * firstSecondaryOne68 N N a b c d e := by
  simp only [alphaWallOneScalar68, alphaWallOneLoadNumerator68_eq_zero,
    add_zero]

theorem alphaWallOneScalar68_eq_zero_iff
    (N a b c d e alpha : k) :
    alphaWallOneScalar68 N a b c d e alpha = 0 ↔
      firstSecondaryOne68 N N a b c d e = 0 := by
  rw [alphaWallOneScalar68_eq_ordinary]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left (by norm_num)
  · intro h
    simp [h]

/-! ## Abstract face: `F₄,F₃,F₂,F₀` plus mixed `F₁` -/

/-- The five leading equations on the wall `g = n` after `l = 0`.  Mixed
`F₁` includes `alpha`, which has already cancelled. -/
structure AlphaWallFace68 (N a b c d e alpha : k) : Prop where
  four : firstSecondaryFour68 a b c d e = 0
  three : firstSecondaryThree68 a b c d e = 0
  two : firstSecondaryTwo68 N N a b c d e = 0
  one : alphaWallOneScalar68 N a b c d e alpha = 0
  zero : firstSecondaryZero68 a b c d e = 0

theorem AlphaWallFace68.toFirstSecondaryFace68
    (N a b c d e alpha : k) (hface : AlphaWallFace68 N a b c d e alpha) :
    FirstSecondaryFace68 N N a b c d e where
  four := hface.four
  three := hface.three
  two := hface.two
  one := (alphaWallOneScalar68_eq_zero_iff N a b c d e alpha).mp hface.one
  zero := hface.zero

theorem firstSecondaryOne68_of_bcd_zero_alphaWall (N a e : k) :
    firstSecondaryOne68 N N a 0 0 0 e =
      -(135 : k) * N * e ^ 2 := by
  simp only [firstSecondaryOne68]
  ring

theorem firstSecondaryOne68_of_middle_family_alphaWall (N a b : k) :
    firstSecondaryOne68 N N a b 0 (a * b) 0 =
      (20 : k) * N * a ^ 3 * b ^ 2 := by
  simp only [firstSecondaryOne68]
  ring

/-- On the four-equation middle family, mixed `F₁` at `G = N` is
`20 N a³ b²`. -/
theorem alphaWallOneScalar68_of_middle_family
    (N a b alpha : k) :
    alphaWallOneScalar68 N a b 0 (a * b) 0 alpha =
      (-160 / 81 : k) * N * a ^ 3 * b ^ 2 := by
  rw [alphaWallOneScalar68_eq_ordinary,
    firstSecondaryOne68_of_middle_family_alphaWall]
  ring

/-- On the four-equation vanishing family, mixed `F₁` at `G = N` is
`-135 N e²`. -/
theorem alphaWallOneScalar68_of_vanishing_family
    (N a e alpha : k) :
    alphaWallOneScalar68 N a 0 0 0 e alpha =
      (120 / 9 : k) * N * e ^ 2 := by
  rw [alphaWallOneScalar68_eq_ordinary,
    firstSecondaryOne68_of_bcd_zero_alphaWall]
  ring

theorem alphaWall_gap_ne_six (N : k) (hN : N ≠ 0) :
    (N : k) - 6 * N ≠ 0 := by
  intro hzero
  have h5 : (-5 : k) * N = N - 6 * N := by ring
  have : (-5 : k) * N = 0 := by rw [h5]; exact hzero
  exact hN ((mul_eq_zero.mp this).resolve_left (by norm_num))

/-- Mixed `F₁` kills both exceptional four-equation families.  The
surviving locus is the ordinary first face; `alpha` is free. -/
theorem alphaWallFace68_classify
    (N a b c d e alpha : k) (ha : a ≠ 0) (hN : N ≠ 0)
    (hface : AlphaWallFace68 N a b c d e alpha) :
    e = 0 ∧ a * b = 3 * d := by
  exact firstSecondaryFace68_classify N N a b c d e ha
    (alphaWall_gap_ne_six N hN)
    (AlphaWallFace68.toFirstSecondaryFace68 N a b c d e alpha hface)

/-- The same classification from `F₄,F₃,F₀` plus mixed `F₁`, without
`F₂`.  Exceptional families are named and killed explicitly. -/
theorem alphaWallFourThreeZeroOne68_classify
    (N a b c d e alpha : k) (ha : a ≠ 0) (hN : N ≠ 0)
    (hfour : firstSecondaryFour68 a b c d e = 0)
    (hthree : firstSecondaryThree68 a b c d e = 0)
    (hzero : firstSecondaryZero68 a b c d e = 0)
    (hone : alphaWallOneScalar68 N a b c d e alpha = 0) :
    e = 0 ∧ a * b = 3 * d := by
  rcases firstSecondaryFourThreeZero68_classify a b c d e ha
      hfour hthree hzero with hord | hmid | hvan
  · exact hord
  · obtain ⟨he0, hc0, habd⟩ := hmid
    have hscalar : alphaWallOneScalar68 N a b c d e alpha =
        (-160 / 81 : k) * N * a ^ 3 * b ^ 2 := by
      simpa [he0, hc0, habd] using
        alphaWallOneScalar68_of_middle_family N a b alpha
    have habSq : (-160 / 81 : k) * N * a ^ 3 * b ^ 2 = 0 := by
      rw [← hscalar]
      exact hone
    have hN81 : (-160 / 81 : k) * N ≠ 0 :=
      mul_ne_zero (by norm_num) hN
    have ha3b2 : a ^ 3 * b ^ 2 = 0 := by
      have : ((-160 / 81 : k) * N) * (a ^ 3 * b ^ 2) = 0 := by
        convert habSq using 1
        ring
      exact (mul_eq_zero.mp this).resolve_left hN81
    have hbSq : b ^ 2 = 0 :=
      (mul_eq_zero.mp ha3b2).resolve_left (pow_ne_zero 3 ha)
    have hb0 : b = 0 := sq_eq_zero_iff.mp hbSq
    have hd0 : d = 0 := by simpa [hb0] using habd.symm
    exact ⟨he0, by simp [hb0, hd0]⟩
  · obtain ⟨hb0, hc0, hd0⟩ := hvan
    have hscalar : alphaWallOneScalar68 N a b c d e alpha =
        (120 / 9 : k) * N * e ^ 2 := by
      simpa [hb0, hc0, hd0] using
        alphaWallOneScalar68_of_vanishing_family N a e alpha
    have heFace : (120 / 9 : k) * N * e ^ 2 = 0 := by
      rw [← hscalar]
      exact hone
    have hN120 : (120 / 9 : k) * N ≠ 0 :=
      mul_ne_zero (by norm_num) hN
    have heSq : e ^ 2 = 0 := by
      have hassoc : ((120 / 9 : k) * N) * e ^ 2 =
          (120 / 9 : k) * N * e ^ 2 := by ring
      have : ((120 / 9 : k) * N) * e ^ 2 = 0 := by
        rw [hassoc]
        exact heFace
      exact (mul_eq_zero.mp this).resolve_left hN120
    have he0 : e = 0 := sq_eq_zero_iff.mp heSq
    exact ⟨he0, by simp [hb0, hd0]⟩

/-- Integer-radius form of the five-equation classifier. -/
theorem alphaWallFace68_classify_of_gap_eq_radius
    (n : ℕ) (a b c d e alpha : k) (ha : a ≠ 0) (hn : 0 < n)
    (hface : AlphaWallFace68 (n : k) a b c d e alpha) :
    e = 0 ∧ a * b = 3 * d :=
  alphaWallFace68_classify (n : k) a b c d e alpha ha
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)) hface

/-- Integer-radius form without `F₂`. -/
theorem alphaWallFourThreeZeroOne68_classify_of_gap_eq_radius
    (n : ℕ) (a b c d e alpha : k) (ha : a ≠ 0) (hn : 0 < n)
    (hfour : firstSecondaryFour68 a b c d e = 0)
    (hthree : firstSecondaryThree68 a b c d e = 0)
    (hzero : firstSecondaryZero68 a b c d e = 0)
    (hone : alphaWallOneScalar68 (n : k) a b c d e alpha = 0) :
    e = 0 ∧ a * b = 3 * d :=
  alphaWallFourThreeZeroOne68_classify (n : k) a b c d e alpha ha
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)) hfour hthree hzero hone

end AlphaWallFace68

/-! ## Core-plus-remainder split of the row-one `alpha` load -/

section AlphaWallExtraction68

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Pure `alpha A^2` summand of `cubicLoadTPolynomial68` after `l = 0`. -/
def cubicLoadTAlphaCorePolynomial68 (alpha : k) (A : k[X]) : k[X] :=
  (1 / 3 * alpha : k) • A ^ 2

/-- Complementary part of `T` after `l = 0`. -/
def cubicLoadTAlphaRestPolynomial68
    (alpha beta gamma epsilon : k) (A B c : k[X]) : k[X] :=
  alpha • c + (5 / 6 * beta : k) • B + (2 / 3 * gamma : k) • A + C epsilon

/-- Pure `alpha D` summand of `cubicLoadUPolynomial68` after `l = 0`. -/
def cubicLoadUAlphaCorePolynomial68 (alpha : k) (D : k[X]) : k[X] :=
  alpha • D

/-- Complementary part of `U` after `l = 0`. -/
def cubicLoadUAlphaRestPolynomial68
    (beta gamma delta zeta : k) (A B c : k[X]) : k[X] :=
  (5 / 24 * beta : k) • A ^ 2 + (5 / 6 * beta : k) • c +
    (2 / 3 * gamma : k) • B + (1 / 2 * delta : k) • A + C zeta

/-- Pure `alpha A^3` summand of `cubicLoadVPolynomial68` after `l = 0`. -/
def cubicLoadVAlphaCorePolynomial68 (alpha : k) (A : k[X]) : k[X] :=
  (1 / 27 * alpha : k) • A ^ 3

/-- Complementary part of `V` after `l = 0`. -/
def cubicLoadVAlphaRestPolynomial68
    (alpha beta gamma delta epsilon eta : k)
    (A B c D e : k[X]) : k[X] :=
  (1 / 3 * alpha : k) • (A * c) + alpha • e -
    (5 / 36 * beta : k) • (A * B) + (5 / 6 * beta : k) • D +
    (1 / 9 * gamma : k) • A ^ 2 + (2 / 3 * gamma : k) • c +
    (1 / 2 * delta : k) • B + (1 / 3 * epsilon : k) • A + C eta

theorem cubicLoadTPolynomial68_eq_alphaCore_add_rest
    (l alpha beta gamma epsilon : k) (A B c D : k[X]) (hl : l = 0) :
    cubicLoadTPolynomial68 l alpha beta gamma epsilon A B c D =
      cubicLoadTAlphaCorePolynomial68 alpha A +
        cubicLoadTAlphaRestPolynomial68 alpha beta gamma epsilon A B c := by
  simp [cubicLoadTPolynomial68, cubicLoadTAlphaCorePolynomial68,
    cubicLoadTAlphaRestPolynomial68, hl, mul_zero, zero_smul, add_zero]
  abel

theorem cubicLoadUPolynomial68_eq_alphaCore_add_rest
    (l alpha beta gamma delta zeta : k) (A B c D e : k[X])
    (hl : l = 0) :
    cubicLoadUPolynomial68 l alpha beta gamma delta zeta A B c D e =
      cubicLoadUAlphaCorePolynomial68 alpha D +
        cubicLoadUAlphaRestPolynomial68 beta gamma delta zeta A B c := by
  simp [cubicLoadUPolynomial68, cubicLoadUAlphaCorePolynomial68,
    cubicLoadUAlphaRestPolynomial68, hl, mul_zero, zero_smul, add_zero]
  abel

theorem cubicLoadVPolynomial68_eq_alphaCore_add_rest
    (l alpha beta gamma delta epsilon eta : k) (A B c D e : k[X])
    (hl : l = 0) :
    cubicLoadVPolynomial68 l alpha beta gamma delta epsilon eta
        A B c D e =
      cubicLoadVAlphaCorePolynomial68 alpha A +
        cubicLoadVAlphaRestPolynomial68 alpha beta gamma delta epsilon
          eta A B c D e := by
  simp [cubicLoadVPolynomial68, cubicLoadVAlphaCorePolynomial68,
    cubicLoadVAlphaRestPolynomial68, hl, mul_zero, zero_smul, add_zero]
  abel

/-! ### Ring identities: the two `10n-1` cores vanish identically -/

set_option maxHeartbeats 4000000 in
/-- `2 T_core E_core'` and `2 C0_core V_core'` cancel. -/
theorem cubicLoadRowOneAlphaACore_eq_zero (alpha : k) (A : k[X]) :
    (2 : k) • (cubicLoadTAlphaCorePolynomial68 alpha A *
        derivative ((1 / 27 : k) • A ^ 3)) -
      (2 : k) • (((1 / 3 : k) • A ^ 2) *
        derivative (cubicLoadVAlphaCorePolynomial68 alpha A)) = 0 := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [cubicLoadTAlphaCorePolynomial68,
    cubicLoadVAlphaCorePolynomial68, derivative_add, derivative_sub,
    derivative_smul, derivative_mul, derivative_pow, derivative_C,
    Polynomial.C_eq_natCast, Polynomial.smul_eq_C_mul, map_add, map_sub,
    map_mul, map_pow, map_zero, RatFunc.algebraMap_C]
  simp only [map_neg, map_div₀, map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 1000000 in
/-- `U_core D'` and `D U_core'` cancel. -/
theorem cubicLoadRowOneAlphaDCore_eq_zero (alpha : k) (D : k[X]) :
    cubicLoadUAlphaCorePolynomial68 alpha D * derivative D -
      D * derivative (cubicLoadUAlphaCorePolynomial68 alpha D) = 0 := by
  simp only [cubicLoadUAlphaCorePolynomial68, Polynomial.smul_eq_C_mul,
    derivative_mul, derivative_C, mul_zero, add_zero]
  ring

set_option maxHeartbeats 2000000 in
theorem jacobianRowOne_eq_alphaCore_add_rest
    (Uc Ur Tc Tr C0c c Vc Vr Ec Er D : k[X]) :
    (Uc + Ur) * derivative D +
      (2 : k) • ((Tc + Tr) * derivative (Ec + Er)) -
      (2 : k) • ((C0c + c) * derivative (Vc + Vr)) -
      D * derivative (Uc + Ur) =
    (Uc * derivative D - D * derivative Uc) +
      ((2 : k) • (Tc * derivative Ec) -
        (2 : k) • (C0c * derivative Vc)) +
      (Ur * derivative D +
        (2 : k) • (Tc * derivative Er) +
        (2 : k) • (Tr * derivative (Ec + Er)) -
        (2 : k) • (C0c * derivative Vr) -
        (2 : k) • (c * derivative (Vc + Vr)) -
        D * derivative Ur) := by
  simp only [derivative_add, mul_add, add_mul, Polynomial.smul_eq_C_mul]
  ring

/-- Explicit leftover of the second one-form load after removing the two
vanishing `alpha` cores. -/
def cubicLoadRowOneAlphaRestPolynomial68
    (alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) : k[X] :=
  let Tc := cubicLoadTAlphaCorePolynomial68 alpha A
  let Tr := cubicLoadTAlphaRestPolynomial68 alpha beta gamma epsilon A B c
  let Ur := cubicLoadUAlphaRestPolynomial68 beta gamma delta zeta A B c
  let Vc := cubicLoadVAlphaCorePolynomial68 alpha A
  let Vr := cubicLoadVAlphaRestPolynomial68 alpha beta gamma delta epsilon
    eta A B c D e
  let V := Vc + Vr
  let C0c := (1 / 3 : k) • A ^ 2
  let Ec := (1 / 27 : k) • A ^ 3
  let Er := (1 / 3 : k) • (A * c) + e
  let E := Ec + Er
  Ur * derivative D +
    (2 : k) • (Tc * derivative Er) +
    (2 : k) • (Tr * derivative E) -
    (2 : k) • (C0c * derivative Vr) -
    (2 : k) • (c * derivative V) -
    D * derivative Ur

set_option maxHeartbeats 8000000 in
theorem cubicLoadRowOnePolynomial68_eq_alphaCore_add_rest
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (hl : l = 0) :
    cubicLoadRowOnePolynomial68 l alpha beta gamma delta epsilon zeta eta
      A B c D e =
      (cubicLoadUAlphaCorePolynomial68 alpha D * derivative D -
          D * derivative (cubicLoadUAlphaCorePolynomial68 alpha D)) +
        ((2 : k) • (cubicLoadTAlphaCorePolynomial68 alpha A *
            derivative ((1 / 27 : k) • A ^ 3)) -
          (2 : k) • (((1 / 3 : k) • A ^ 2) *
            derivative (cubicLoadVAlphaCorePolynomial68 alpha A))) +
        cubicLoadRowOneAlphaRestPolynomial68 alpha beta gamma delta
          epsilon zeta eta A B c D e := by
  unfold cubicLoadRowOnePolynomial68 cubicLoadRowOneAlphaRestPolynomial68
  rw [cubicLoadTPolynomial68_eq_alphaCore_add_rest l alpha beta gamma
        epsilon A B c D hl,
      cubicLoadUPolynomial68_eq_alphaCore_add_rest l alpha beta gamma delta
        zeta A B c D e hl,
      cubicLoadVPolynomial68_eq_alphaCore_add_rest l alpha beta gamma delta
        epsilon eta A B c D e hl]
  have hE : (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e =
      (1 / 27 : k) • A ^ 3 + ((1 / 3 : k) • (A * c) + e) :=
    add_assoc _ _ _
  rw [hE]
  exact jacobianRowOne_eq_alphaCore_add_rest
    (cubicLoadUAlphaCorePolynomial68 alpha D)
    (cubicLoadUAlphaRestPolynomial68 beta gamma delta zeta A B c)
    (cubicLoadTAlphaCorePolynomial68 alpha A)
    (cubicLoadTAlphaRestPolynomial68 alpha beta gamma epsilon A B c)
    ((1 / 3 : k) • A ^ 2) c
    (cubicLoadVAlphaCorePolynomial68 alpha A)
    (cubicLoadVAlphaRestPolynomial68 alpha beta gamma delta epsilon eta
      A B c D e)
    ((1 / 27 : k) • A ^ 3) ((1 / 3 : k) • (A * c) + e) D

set_option maxHeartbeats 2000000 in
theorem cubicLoadRowOnePolynomial68_eq_alphaRest
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (hl : l = 0) :
    cubicLoadRowOnePolynomial68 l alpha beta gamma delta epsilon zeta eta
      A B c D e =
      cubicLoadRowOneAlphaRestPolynomial68 alpha beta gamma delta
        epsilon zeta eta A B c D e := by
  rw [cubicLoadRowOnePolynomial68_eq_alphaCore_add_rest l alpha beta
    gamma delta epsilon zeta eta A B c D e hl,
    cubicLoadRowOneAlphaDCore_eq_zero, cubicLoadRowOneAlphaACore_eq_zero,
    zero_add, zero_add]

/-! ## Term-by-term degree bounds on the wall `g = n` -/

private theorem natDegree_mul_derivative_le_add_sub68
    (p q : k[X]) (u v : ℕ) (hv : 0 < v)
    (hp : p.natDegree ≤ u) (hq : q.natDegree ≤ v) :
    (p * derivative q).natDegree ≤ u + v - 1 := by
  have hd : (derivative q).natDegree ≤ v - 1 :=
    (natDegree_derivative_le q).trans (Nat.sub_le_sub_right hq 1)
  have hsum : p.natDegree + (derivative q).natDegree ≤ u + (v - 1) :=
    Nat.add_le_add hp hd
  have hidx : u + (v - 1) = u + v - 1 := by omega
  exact natDegree_mul_le.trans (hidx ▸ hsum)

private theorem natDegree_mul_derivative_lt_of_add_sub68
    (p q : k[X]) (u v bound : ℕ) (hv : 0 < v)
    (hp : p.natDegree ≤ u) (hq : q.natDegree ≤ v)
    (huv : u + v - 1 < bound) :
    (p * derivative q).natDegree < bound :=
  (natDegree_mul_derivative_le_add_sub68 p q u v hv hp hq).trans_lt huv

private theorem natDegree_smul_lt68 (r : k) {p : k[X]} {n : ℕ}
    (hp : p.natDegree < n) : (r • p).natDegree < n :=
  (natDegree_smul_le r p).trans_lt hp

private theorem natDegree_add_lt68 {p q : k[X]} {n : ℕ}
    (hp : p.natDegree < n) (hq : q.natDegree < n) :
    (p + q).natDegree < n :=
  (natDegree_add_le p q).trans_lt (max_lt hp hq)

private theorem natDegree_sub_lt68 {p q : k[X]} {n : ℕ}
    (hp : p.natDegree < n) (hq : q.natDegree < n) :
    (p - q).natDegree < n :=
  (natDegree_sub_le p q).trans_lt (max_lt hp hq)

set_option maxHeartbeats 2000000 in
theorem cubicLoadTAlphaCorePolynomial68_degree_le
    (alpha : k) (A : k[X]) (n : ℕ) (hA : A.natDegree ≤ 2 * n) :
    (cubicLoadTAlphaCorePolynomial68 alpha A).natDegree ≤ 4 * n := by
  simp only [cubicLoadTAlphaCorePolynomial68]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
theorem cubicLoadTAlphaRestPolynomial68_degree_le
    (alpha beta gamma epsilon : k) (A B c : k[X]) (n g : ℕ)
    (hn : 0 < n) (hwall : g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g) :
    (cubicLoadTAlphaRestPolynomial68 alpha beta gamma epsilon A B c).natDegree ≤
      4 * n - g := by
  have hAc : (alpha • c).natDegree ≤ 4 * n - g :=
    (natDegree_smul_le alpha c).trans hc
  have hB' : ((5 / 6 * beta : k) • B).natDegree ≤ 4 * n - g :=
    (natDegree_smul_le _ B).trans (hB.trans (by omega))
  have hA' : ((2 / 3 * gamma : k) • A).natDegree ≤ 4 * n - g :=
    (natDegree_smul_le _ A).trans (hA.trans (by omega))
  have hC : (C epsilon).natDegree ≤ 4 * n - g := by
    rw [natDegree_C]
    omega
  simp only [cubicLoadTAlphaRestPolynomial68]
  refine (natDegree_add_le _ _).trans ?_
  refine max_le ((natDegree_add_le _ _).trans (max_le
      ((natDegree_add_le _ _).trans (max_le hAc hB')) hA')) hC

set_option maxHeartbeats 2000000 in
theorem cubicLoadUAlphaRestPolynomial68_degree_le
    (beta gamma delta zeta : k) (A B c : k[X]) (n g : ℕ)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g) :
    (cubicLoadUAlphaRestPolynomial68 beta gamma delta zeta A B c).natDegree ≤
      4 * n := by
  simp only [cubicLoadUAlphaRestPolynomial68]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
theorem cubicLoadVAlphaCorePolynomial68_degree_le
    (alpha : k) (A : k[X]) (n : ℕ) (hA : A.natDegree ≤ 2 * n) :
    (cubicLoadVAlphaCorePolynomial68 alpha A).natDegree ≤ 6 * n := by
  simp only [cubicLoadVAlphaCorePolynomial68]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
theorem cubicLoadVAlphaRestPolynomial68_degree_le
    (alpha beta gamma delta epsilon eta : k) (A B c D e : k[X])
    (n g : ℕ)
    (hn : 0 < n) (hwall : g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadVAlphaRestPolynomial68 alpha beta gamma delta epsilon eta
      A B c D e).natDegree ≤ 6 * n - g := by
  have hAc : ((1 / 3 * alpha : k) • (A * c)).natDegree ≤ 6 * n - g :=
    (natDegree_smul_le _ _).trans <|
      natDegree_mul_le.trans (by
        have := Nat.add_le_add hA hc
        omega)
  have he' : (alpha • e).natDegree ≤ 6 * n - g :=
    (natDegree_smul_le _ _).trans he
  have hAB : ((5 / 36 * beta : k) • (A * B)).natDegree ≤ 6 * n - g :=
    (natDegree_smul_le _ _).trans <|
      natDegree_mul_le.trans (by
        have := Nat.add_le_add hA hB
        omega)
  have hD' : ((5 / 6 * beta : k) • D).natDegree ≤ 6 * n - g :=
    (natDegree_smul_le _ _).trans (hD.trans (by omega))
  have hA2 : ((1 / 9 * gamma : k) • A ^ 2).natDegree ≤ 6 * n - g :=
    (natDegree_smul_le _ _).trans <|
      (natDegree_pow_le (p := A) (n := 2)).trans (by
        have : A.natDegree * 2 ≤ (2 * n) * 2 := Nat.mul_le_mul_right 2 hA
        omega)
  have hc' : ((2 / 3 * gamma : k) • c).natDegree ≤ 6 * n - g :=
    (natDegree_smul_le _ _).trans (hc.trans (by omega))
  have hB' : ((1 / 2 * delta : k) • B).natDegree ≤ 6 * n - g :=
    (natDegree_smul_le _ _).trans (hB.trans (by omega))
  have hA' : ((1 / 3 * epsilon : k) • A).natDegree ≤ 6 * n - g :=
    (natDegree_smul_le _ _).trans (hA.trans (by omega))
  have hC : (C eta).natDegree ≤ 6 * n - g := by
    rw [natDegree_C]
    omega
  simp only [cubicLoadVAlphaRestPolynomial68]
  -- Expression is `((((p + q - r + s) + t) + u) + v) + w + C`.
  refine (natDegree_add_le _ _).trans (max_le ?_ hC)
  refine (natDegree_add_le _ _).trans (max_le ?_ hA')
  refine (natDegree_add_le _ _).trans (max_le ?_ hB')
  refine (natDegree_add_le _ _).trans (max_le ?_ hc')
  refine (natDegree_add_le _ _).trans (max_le ?_ hA2)
  refine (natDegree_add_le _ _).trans (max_le ?_ hD')
  refine (natDegree_sub_le _ _).trans (max_le ?_ hAB)
  exact (natDegree_add_le _ _).trans (max_le hAc he')

set_option maxHeartbeats 4000000 in
theorem cubicLoadRowOneAlphaRestPolynomial68_degree_lt_alphaWall
    (alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hwall : g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadRowOneAlphaRestPolynomial68 alpha beta gamma delta epsilon
      zeta eta A B c D e).natDegree < 12 * n - 2 * g - 1 := by
  let Tc := cubicLoadTAlphaCorePolynomial68 alpha A
  let Tr := cubicLoadTAlphaRestPolynomial68 alpha beta gamma epsilon A B c
  let Ur := cubicLoadUAlphaRestPolynomial68 beta gamma delta zeta A B c
  let Vc := cubicLoadVAlphaCorePolynomial68 alpha A
  let Vr := cubicLoadVAlphaRestPolynomial68 alpha beta gamma delta epsilon
    eta A B c D e
  let V := Vc + Vr
  let C0c := (1 / 3 : k) • A ^ 2
  let Ec := (1 / 27 : k) • A ^ 3
  let Er := (1 / 3 : k) • (A * c) + e
  let E := Ec + Er
  have hTc : Tc.natDegree ≤ 4 * n :=
    cubicLoadTAlphaCorePolynomial68_degree_le alpha A n hA
  have hTr : Tr.natDegree ≤ 4 * n - g :=
    cubicLoadTAlphaRestPolynomial68_degree_le alpha beta gamma epsilon
      A B c n g hn hwall hA hB hc
  have hUr : Ur.natDegree ≤ 4 * n :=
    cubicLoadUAlphaRestPolynomial68_degree_le beta gamma delta zeta
      A B c n g hA hB hc
  have hVc : Vc.natDegree ≤ 6 * n :=
    cubicLoadVAlphaCorePolynomial68_degree_le alpha A n hA
  have hVr : Vr.natDegree ≤ 6 * n - g :=
    cubicLoadVAlphaRestPolynomial68_degree_le alpha beta gamma delta
      epsilon eta A B c D e n g hn hwall hA hB hc hD he
  have hV : V.natDegree ≤ 6 * n :=
    (natDegree_add_le Vc Vr).trans (max_le hVc (hVr.trans (by omega)))
  have hC0c : C0c.natDegree ≤ 4 * n := by
    simp only [C0c]
    compute_degree
    omega
  have hEc : Ec.natDegree ≤ 6 * n := by
    simp only [Ec]
    compute_degree
    omega
  have hEr : Er.natDegree ≤ 6 * n - g := by
    simp only [Er]
    compute_degree
    omega
  have hE : E.natDegree ≤ 6 * n :=
    (natDegree_add_le Ec Er).trans (max_le hEc (hEr.trans (by omega)))
  have hbound (u v : ℕ) (hv : 0 < v)
      (hu : u + v - 1 < 12 * n - 2 * g - 1) :
      ∀ p q : k[X], p.natDegree ≤ u → q.natDegree ≤ v →
        (p * derivative q).natDegree < 12 * n - 2 * g - 1 :=
    fun p q hp hq =>
      natDegree_mul_derivative_lt_of_add_sub68 p q u v
        (12 * n - 2 * g - 1) hv hp hq hu
  have h1 : (Ur * derivative D).natDegree < 12 * n - 2 * g - 1 :=
    hbound (4 * n) (5 * n - g) (by omega) (by omega) Ur D hUr hD
  have h2 : (Tc * derivative Er).natDegree < 12 * n - 2 * g - 1 :=
    hbound (4 * n) (6 * n - g) (by omega) (by omega) Tc Er hTc hEr
  have h3 : (Tr * derivative E).natDegree < 12 * n - 2 * g - 1 :=
    hbound (4 * n - g) (6 * n) (by omega) (by omega) Tr E hTr hE
  have h4 : (C0c * derivative Vr).natDegree < 12 * n - 2 * g - 1 :=
    hbound (4 * n) (6 * n - g) (by omega) (by omega) C0c Vr hC0c hVr
  have h5 : (c * derivative V).natDegree < 12 * n - 2 * g - 1 :=
    hbound (4 * n - g) (6 * n) (by omega) (by omega) c V hc hV
  have h6 : (D * derivative Ur).natDegree < 12 * n - 2 * g - 1 :=
    hbound (5 * n - g) (4 * n) (by omega) (by omega) D Ur hD hUr
  have h2s := natDegree_smul_lt68 (2 : k) h2
  have h3s := natDegree_smul_lt68 (2 : k) h3
  have h4s := natDegree_smul_lt68 (2 : k) h4
  have h5s := natDegree_smul_lt68 (2 : k) h5
  change (Ur * derivative D +
      (2 : k) • (Tc * derivative Er) +
      (2 : k) • (Tr * derivative E) -
      (2 : k) • (C0c * derivative Vr) -
      (2 : k) • (c * derivative V) -
      D * derivative Ur).natDegree < _
  refine natDegree_sub_lt68
    (natDegree_sub_lt68
      (natDegree_sub_lt68
        (natDegree_add_lt68
          (natDegree_add_lt68 h1 h2s) h3s) h4s) h5s) h6

set_option maxHeartbeats 2000000 in
theorem cubicLoadRowOnePolynomial68_degree_lt_alphaWall
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hl : l = 0) (hwall : g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadRowOnePolynomial68 l alpha beta gamma delta epsilon zeta eta
      A B c D e).natDegree < 12 * n - 2 * g - 1 := by
  rw [cubicLoadRowOnePolynomial68_eq_alphaRest l alpha beta gamma delta
    epsilon zeta eta A B c D e hl]
  exact cubicLoadRowOneAlphaRestPolynomial68_degree_lt_alphaWall
    alpha beta gamma delta epsilon zeta eta A B c D e n g
    hn hg hwall hA hB hc hD he

/-! ## Literal coefficient at index `10n-1` -/

set_option maxHeartbeats 3000000 in
theorem cubicLoadRowOnePolynomial68_coeff_alphaWall
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hl : l = 0) (hwall : g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadRowOnePolynomial68 l alpha beta gamma delta epsilon zeta eta
      A B c D e).coeff (12 * n - 2 * g - 1) = 0 :=
  coeff_eq_zero_of_natDegree_lt
    (cubicLoadRowOnePolynomial68_degree_lt_alphaWall
      l alpha beta gamma delta epsilon zeta eta A B c D e n g
      hn hg hl hwall hA hB hc hD he)

set_option maxHeartbeats 3000000 in
theorem cubicHomogeneousRowOnePolynomial68_secondaryCoeff_alphaWall
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hwall : g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicHomogeneousRowOnePolynomial68 A B c D e).coeff
        (12 * n - 2 * g - 1) =
      (-8 / 81 : k) * firstSecondaryOne68 (n : k) (g : k)
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
        (e.coeff (6 * n - g)) := by
  have hrel : 2 * g < 3 * n := by omega
  exact cubicHomogeneousRowOnePolynomial68_secondaryCoeff_of_two_mul_gap_lt_three
    A B c D e n g hn hg hrel hA hB hc hD he

set_option maxHeartbeats 3000000 in
/-- Mixed row-one coefficient on `g = n`: ordinary `(-8/81) F₁`, with
vanishing `alpha` load. -/
theorem integratedLowerRowOnePolynomial68_secondaryCoeff_alphaWall
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hl : l = 0) (hwall : g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (lowerRowOnePolynomial68
      (integratedTPolynomial68 l alpha beta gamma epsilon A B
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      (integratedUPolynomial68 l alpha beta gamma delta zeta A B
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta A B
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)).coeff
          (12 * n - 2 * g - 1) =
      alphaWallOneScalar68 (n : k)
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
        (e.coeff (6 * n - g)) alpha := by
  have hcoords := integratedPolynomial68_cubicCoordinates
    l alpha beta gamma delta epsilon zeta eta A B c D e
  rw [hcoords.t_eq, hcoords.u_eq, hcoords.v_eq,
    cubicRowOnePolynomial68_split, coeff_add,
    cubicLoadRowOnePolynomial68_coeff_alphaWall
      l alpha beta gamma delta epsilon zeta eta A B c D e n g
      hn hg hl hwall hA hB hc hD he, add_zero,
    cubicHomogeneousRowOnePolynomial68_secondaryCoeff_alphaWall
      A B c D e n g hn hg hwall hA hB hc hD he,
    alphaWallOneScalar68_eq_ordinary]
  simp [hwall]

set_option maxHeartbeats 3000000 in
theorem integratedLowerRowOnePolynomial68_secondaryCoeff_alphaWall_index
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n : ℕ)
    (hn : 0 < n) (hl : l = 0)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 2 * n)
    (hc : c.natDegree ≤ 3 * n)
    (hD : D.natDegree ≤ 4 * n)
    (he : e.natDegree ≤ 5 * n) :
    (lowerRowOnePolynomial68
      (integratedTPolynomial68 l alpha beta gamma epsilon A B
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      (integratedUPolynomial68 l alpha beta gamma delta zeta A B
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta A B
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)).coeff
          (10 * n - 1) =
      alphaWallOneScalar68 (n : k)
        (A.coeff (2 * n)) (B.coeff (2 * n))
        (c.coeff (3 * n)) (D.coeff (4 * n))
        (e.coeff (5 * n)) alpha := by
  have h := integratedLowerRowOnePolynomial68_secondaryCoeff_alphaWall
    l alpha beta gamma delta epsilon zeta eta A B c D e n n
    hn hn hl rfl hA (by omega) (by omega) (by omega) (by omega)
  have hidx : 12 * n - 2 * n - 1 = 10 * n - 1 := by omega
  have hBidx : 3 * n - n = 2 * n := by omega
  have hcidx : 4 * n - n = 3 * n := by omega
  have hDidx : 5 * n - n = 4 * n := by omega
  have heidx : 6 * n - n = 5 * n := by omega
  simpa [hidx, hBidx, hcidx, hDidx, heidx] using h

/-! ## Packaged face on the wall `g = n` -/

set_option maxHeartbeats 3000000 in
theorem integratedPolynomialLowerSystem_alphaWallFace68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 c D E e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hl : l = 0) (hwall : g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (ha : A.coeff (2 * n) ≠ 0)
    (hC0 : C0 = (1 / 3 : k) • A ^ 2 + c)
    (hE0 : E = (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E) :
    AlphaWallFace68 (n : k)
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
      (e.coeff (6 * n - g)) alpha := by
  have hrel : 2 * g < 3 * n := by omega
  obtain ⟨i4, hI4⟩ := hsys.firstFour
  obtain ⟨i3, hI3⟩ := hsys.firstThree
  have hinv := polynomialSecondaryInvariantEquations68_of_loadL
    l beta gamma delta epsilon zeta i4 i3 A B C0 c D E e n g
    hn hg hl hrel hA hB hc hD he hC0 hE0 hI4 hI3
  have hrowTwo := hsys.rowTwo
  rw [hC0, hE0] at hrowTwo
  have htwo := congrArg
    (fun p : k[X] => p.coeff (11 * n - 2 * g - 1)) hrowTwo
  rw [integratedLowerRowTwoPolynomial68_secondaryCoeff_of_loadL
    l alpha beta gamma delta epsilon zeta eta A B c D e n g
    hn hg hl hrel hA hB hc hD he] at htwo
  simp only [coeff_zero] at htwo
  have htwo0 : firstSecondaryTwo68 (n : k) (g : k)
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
      (e.coeff (6 * n - g)) = 0 :=
    (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  have hrowOne := hsys.rowOne
  rw [hC0, hE0] at hrowOne
  have hone := congrArg
    (fun p : k[X] => p.coeff (12 * n - 2 * g - 1)) hrowOne
  rw [integratedLowerRowOnePolynomial68_secondaryCoeff_alphaWall
    l alpha beta gamma delta epsilon zeta eta A B c D e n g
    hn hg hl hwall hA hB hc hD he] at hone
  simp only [coeff_zero] at hone
  have hrowZero := hsys.rowZero
  rw [hC0, hE0] at hrowZero
  have hzero := congrArg
    (fun p : k[X] => p.coeff (13 * n - 2 * g - 1)) hrowZero
  rw [integratedLowerRowZeroPolynomial68_secondaryCoeff_of_loadL
    l alpha beta gamma delta epsilon zeta eta A B c D e n g
    hn hg hl hrel hA hB hc hD he] at hzero
  have hindex : 13 * n - 2 * g - 1 ≠ 0 := by omega
  simp only [coeff_C, ite_eq_right hindex] at hzero
  have hncast : (n : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hfactor : (8 / 81 : k) * (n : k) * A.coeff (2 * n) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hncast) ha
  have hzero0 : firstSecondaryZero68
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
      (e.coeff (6 * n - g)) = 0 :=
    (mul_eq_zero.mp hzero).resolve_left hfactor
  have htwo0' : firstSecondaryTwo68 (n : k) (n : k)
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
      (e.coeff (6 * n - g)) = 0 := by
    simpa [hwall] using htwo0
  exact ⟨hinv.1, hinv.2, htwo0', hone, hzero0⟩

theorem integratedPolynomialLowerSystem_alphaWallClassified68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 c D E e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hl : l = 0) (hwall : g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (ha : A.coeff (2 * n) ≠ 0)
    (hC0 : C0 = (1 / 3 : k) • A ^ 2 + c)
    (hE0 : E = (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E) :
    e.coeff (6 * n - g) = 0 ∧
      A.coeff (2 * n) * B.coeff (3 * n - g) =
        3 * D.coeff (5 * n - g) :=
  alphaWallFace68_classify_of_gap_eq_radius n
    (A.coeff (2 * n)) (B.coeff (3 * n - g))
    (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
    (e.coeff (6 * n - g)) alpha ha hn
    (integratedPolynomialLowerSystem_alphaWallFace68
      l alpha beta gamma delta epsilon zeta eta terminal
      A B C0 c D E e n g hn hg hl hwall hA hB hc hD he ha hC0 hE0 hsys)

/-- Without row one, the wall still supplies only the three four-equation
families.  Mixed `F₁` is what kills the two exceptional ones. -/
theorem polynomialSecondaryFourThreeZeroEquations68_of_alphaWall
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 c D E e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hl : l = 0) (hwall : g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (ha : A.coeff (2 * n) ≠ 0)
    (hC0 : C0 = (1 / 3 : k) • A ^ 2 + c)
    (hE0 : E = (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E) :
    (e.coeff (6 * n - g) = 0 ∧
        A.coeff (2 * n) * B.coeff (3 * n - g) =
          3 * D.coeff (5 * n - g)) ∨
      (e.coeff (6 * n - g) = 0 ∧
        c.coeff (4 * n - g) = 0 ∧
        A.coeff (2 * n) * B.coeff (3 * n - g) =
          D.coeff (5 * n - g)) ∨
      (B.coeff (3 * n - g) = 0 ∧
        c.coeff (4 * n - g) = 0 ∧
        D.coeff (5 * n - g) = 0) := by
  have hrel : 2 * g < 3 * n := by omega
  exact polynomialSecondaryFourThreeZeroEquations68_of_loadL
    l alpha beta gamma delta epsilon zeta eta terminal
    A B C0 c D E e n g hn hg hl hrel hA hB hc hD he ha hC0 hE0 hsys

end AlphaWallExtraction68

#print axioms alphaWallOneLoadNumerator68_eq_zero
#print axioms alphaWallOneScalar68_eq_ordinary
#print axioms alphaWallFace68_classify
#print axioms alphaWallFourThreeZeroOne68_classify
#print axioms alphaWallFace68_classify_of_gap_eq_radius
#print axioms cubicLoadRowOneAlphaACore_eq_zero
#print axioms cubicLoadRowOneAlphaDCore_eq_zero
#print axioms cubicLoadRowOnePolynomial68_eq_alphaRest
#print axioms cubicLoadRowOneAlphaRestPolynomial68_degree_lt_alphaWall
#print axioms cubicLoadRowOnePolynomial68_coeff_alphaWall
#print axioms integratedLowerRowOnePolynomial68_secondaryCoeff_alphaWall
#print axioms integratedLowerRowOnePolynomial68_secondaryCoeff_alphaWall_index
#print axioms integratedPolynomialLowerSystem_alphaWallFace68
#print axioms integratedPolynomialLowerSystem_alphaWallClassified68
#print axioms polynomialSecondaryFourThreeZeroEquations68_of_alphaWall

end Max11DegreeRoutes
