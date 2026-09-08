import LowScale68SecondaryFirstLoadWallRemainder
import LowScale68SecondaryResidualRowTwoFaces
import LowScale68SecondaryLargeGapResidual
import LowScale68SecondaryRelaxedCanonical
import LowScale68SecondaryResidualLoadZeroEndgame

/-! # Mixed residual middle face on the `(6,8)` wall `h = n-g`

In the strip `2g < n < 3g` the residual gap `h = n-g` collides with the
Jacobian load `l A^4` at degree `8n`.  The incidence polynomial
`Q = B e + c d - B^3/9` attains the same index, so row two and row zero
meet both the cores `l A^5`, `l A^6` and the `Q`-feed `A Q'`, `A A' Q`.
I3 remains load-free.  The four leading scalars force `l = 0` and the
ordinary residual middle face.  The canonical expanded wrapper below
derives that vanishing and closes the branch by the residual load-zero
endgame on `2g < n`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Wall index arithmetic -/

theorem residualSumLoadWall_gap_lt_radius
    (n g h : ℕ) (hsmall : 2 * g < n) (hwall : h = n - g) : g < n := by
  omega

theorem residualSumLoadWall_betweenGaps
    (n g h : ℕ) (hsmall : 2 * g < n) (hstrict : n < 3 * g)
    (hwall : h = n - g) : g < h ∧ h < 2 * g := by
  omega

theorem residualSumLoadWall_fourIndex
    (n g h : ℕ) (hsmall : 2 * g < n) (hwall : h = n - g) :
    9 * n - g - h = 8 * n := by
  omega

theorem residualSumLoadWall_threeIndex
    (n g h : ℕ) (hsmall : 2 * g < n) (hwall : h = n - g) :
    10 * n - g - h = 9 * n := by
  omega

theorem residualSumLoadWall_twoHomIndex
    (n g h : ℕ) (hsmall : 2 * g < n) (hwall : h = n - g) :
    11 * n - g - h - 1 = 10 * n - 1 := by
  omega

theorem residualSumLoadWall_zeroHomIndex
    (n g h : ℕ) (hsmall : 2 * g < n) (hwall : h = n - g) :
    13 * n - g - h - 1 = 12 * n - 1 := by
  omega

theorem residualSumLoadWall_eBound
    (n g h : ℕ) (hsmall : 2 * g < n) (hwall : h = n - g)
    {e : k[X]} (he : e.natDegree ≤ 6 * n - h) :
    e.natDegree ≤ 6 * n - g :=
  he.trans (by omega)

/-! ## Abstract mixed numerators -/

/-- Homogeneous residual-middle I4 numerator `b e + c d`. -/
def residualSumFourHom68 (b c d e : k) : k :=
  b * e + c * d

/-- Homogeneous residual-middle I3 numerator. -/
def residualSumThreeHom68 (a b c d e : k) : k :=
  -a * b * d + 3 * c * e

/-- Mixed I4 numerator at index `8n`: `35 l a^4 + 4608 (b e + c d)`. -/
def residualSumLoadWallFourNumerator68 (a b c d e l : k) : k :=
  (35 : k) * l * a ^ 4 + (4608 : k) * residualSumFourHom68 b c d e

/-- Mixed row-two numerator after dropping the nonzero factor `N/324`. -/
def residualSumLoadWallTwoNumerator68 (a b c d e l : k) : k :=
  (2016 : k) * a * residualSumFourHom68 b c d e + (35 : k) * l * a ^ 5

/-- Mixed row-zero numerator after dropping the nonzero factor `N/1944`. -/
def residualSumLoadWallZeroNumerator68 (a b c d e l : k) : k :=
  -(576 : k) * a ^ 2 * residualSumFourHom68 b c d e +
    (35 : k) * l * a ^ 6

/-- Plan §3.5.D mixed I4 scalar. -/
def residualSumLoadWallFourScalar68 (a b c d e l : k) : k :=
  (35 / 1728 : k) * l * a ^ 4 +
    (8 / 3 : k) * residualSumFourHom68 b c d e

/-- Mixed row-two scalar at index `10n-1`. -/
def residualSumLoadWallTwoScalar68 (N a b c d e l : k) : k :=
  (56 / 9 : k) * N * a * residualSumFourHom68 b c d e +
    (35 / 324 : k) * N * l * a ^ 5

/-- Mixed row-zero scalar at index `12n-1`. -/
def residualSumLoadWallZeroScalar68 (N a b c d e l : k) : k :=
  -(8 / 27 : k) * N * a ^ 2 * residualSumFourHom68 b c d e +
    (35 / 1944 : k) * N * l * a ^ 6

/-- All four mixed leading equations on `h = n-g` in `2G < N < 3G`. -/
structure ResidualSumLoadWallFace68 (N a b c d e l : k) : Prop where
  four : residualSumLoadWallFourNumerator68 a b c d e l = 0
  three : residualSumThreeHom68 a b c d e = 0
  two : residualSumLoadWallTwoNumerator68 a b c d e l = 0
  zero : residualSumLoadWallZeroNumerator68 a b c d e l = 0

/-! ## Scalar identities -/

theorem residualSumLoadWallFourScalar68_eq_numerator
    (a b c d e l : k) :
    residualSumLoadWallFourScalar68 a b c d e l =
      residualSumLoadWallFourNumerator68 a b c d e l / (1728 : k) := by
  simp only [residualSumLoadWallFourScalar68,
    residualSumLoadWallFourNumerator68, residualSumFourHom68]
  ring

theorem residualSumLoadWallTwoScalar68_eq_numerator
    (N a b c d e l : k) :
    residualSumLoadWallTwoScalar68 N a b c d e l =
      N * residualSumLoadWallTwoNumerator68 a b c d e l / (324 : k) := by
  simp only [residualSumLoadWallTwoScalar68,
    residualSumLoadWallTwoNumerator68, residualSumFourHom68]
  ring

theorem residualSumLoadWallZeroScalar68_eq_numerator
    (N a b c d e l : k) :
    residualSumLoadWallZeroScalar68 N a b c d e l =
      N * residualSumLoadWallZeroNumerator68 a b c d e l / (1944 : k) := by
  simp only [residualSumLoadWallZeroScalar68,
    residualSumLoadWallZeroNumerator68, residualSumFourHom68]
  ring

theorem residualSumLoadWall_four_two_combination (a b c d e l : k) :
    (16 : k) * residualSumLoadWallTwoNumerator68 a b c d e l -
        (7 : k) * a * residualSumLoadWallFourNumerator68 a b c d e l =
      (315 : k) * l * a ^ 5 := by
  simp only [residualSumLoadWallTwoNumerator68,
    residualSumLoadWallFourNumerator68, residualSumFourHom68]
  ring

theorem residualSumLoadWall_four_zero_combination (a b c d e l : k) :
    a ^ 2 * residualSumLoadWallFourNumerator68 a b c d e l +
        (8 : k) * residualSumLoadWallZeroNumerator68 a b c d e l =
      (315 : k) * l * a ^ 6 := by
  simp only [residualSumLoadWallFourNumerator68,
    residualSumLoadWallZeroNumerator68, residualSumFourHom68]
  ring

theorem residualSumLoadWallFourNumerator68_of_l_eq_zero
    (a b c d e : k) :
    residualSumLoadWallFourNumerator68 a b c d e 0 =
      (4608 : k) * residualSumFourHom68 b c d e := by
  simp only [residualSumLoadWallFourNumerator68]
  ring

theorem ResidualSumLoadWallFace68.toBetween_of_l_eq_zero
    (N a b c d e l : k) (hl : l = 0)
    (hface : ResidualSumLoadWallFace68 N a b c d e l) :
    SecondaryResidualBetweenFace68 a b c d e where
  four := by
    have h := hface.four
    rw [hl, residualSumLoadWallFourNumerator68_of_l_eq_zero] at h
    exact (mul_eq_zero.mp h).resolve_left (by norm_num)
  three := hface.three

set_option maxHeartbeats 2000000 in
/-- Exact algebraic classification: the mixed residual sum-load wall
forces `l = 0` and the ordinary residual middle face. -/
theorem residualSumLoadWallFace68_classify
    (N a b c d e l : k) (ha : a ≠ 0)
    (hface : ResidualSumLoadWallFace68 N a b c d e l) :
    l = 0 ∧ SecondaryResidualBetweenFace68 a b c d e := by
  have hcomb := residualSumLoadWall_four_two_combination a b c d e l
  have h315 : (315 : k) * l * a ^ 5 = 0 := by
    rw [← hcomb, hface.two, hface.four]
    ring
  have h35a : (315 : k) * a ^ 5 ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 5 ha)
  have hl0 : l = 0 := by
    have : ((315 : k) * a ^ 5) * l = 0 := by
      convert h315 using 1
      ring
    exact (mul_eq_zero.mp this).resolve_left h35a
  exact ⟨hl0,
    ResidualSumLoadWallFace68.toBetween_of_l_eq_zero
      N a b c d e l hl0 hface⟩

/-- Residual first-face support upgrades the wall to the discriminant
middle face with vanishing load. -/
theorem residualSumLoadWallFace68_classify_of_support
    (N a b c d e l : k) (ha : a ≠ 0)
    (hsupport : b ≠ 0 ∨ c ≠ 0) (hattained : d ≠ 0 ∨ e ≠ 0)
    (hface : ResidualSumLoadWallFace68 N a b c d e l) :
    l = 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ d ≠ 0 ∧ e ≠ 0 ∧
      a * b ^ 2 + 3 * c ^ 2 = 0 := by
  obtain ⟨hl, hmid⟩ :=
    residualSumLoadWallFace68_classify N a b c d e l ha hface
  obtain ⟨hb, hc, hd, he, hdisc⟩ :=
    secondaryResidualBetweenFace68_classify_of_support
      a b c d e ha hsupport hattained hmid
  exact ⟨hl, hb, hc, hd, he, hdisc⟩

theorem residualSumLoadWallFace68_classify_of_sum_gap_eq_radius
    (n g h : ℕ) (a b c d e l : k) (ha : a ≠ 0)
    (hface : ResidualSumLoadWallFace68 (n : k) a b c d e l) :
    l = 0 ∧ SecondaryResidualBetweenFace68 a b c d e :=
  residualSumLoadWallFace68_classify (n : k) a b c d e l ha hface

/-! ## Shared derivative degree helpers -/

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

private theorem natDegree_add_lt_of_both68 {p q : k[X]} {n : ℕ}
    (hp : p.natDegree < n) (hq : q.natDegree < n) :
    (p + q).natDegree < n :=
  (natDegree_add_le p q).trans_lt (max_lt hp hq)

private theorem natDegree_sub_lt_of_both68 {p q : k[X]} {n : ℕ}
    (hp : p.natDegree < n) (hq : q.natDegree < n) :
    (p - q).natDegree < n :=
  (natDegree_sub_le p q).trans_lt (max_lt hp hq)

/-! ## I4 / I3 coefficients -/

set_option maxHeartbeats 2000000 in
theorem residualIncidenceQ68_degree_le_sumWall
    (B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hsmall : 2 * g < n) (hstrict : n < 3 * g)
    (hwall : h = n - g)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (residualIncidenceQ68 B c d e).natDegree ≤ 8 * n := by
  simp only [residualIncidenceQ68]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
theorem residualIncidenceQ68_coeff_sumWall
    (B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hsmall : 2 * g < n) (hstrict : n < 3 * g)
    (hwall : h = n - g)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (residualIncidenceQ68 B c d e).coeff (8 * n) =
      residualSumFourHom68 (B.coeff (3 * n - g)) (c.coeff (4 * n - g))
        (d.coeff (5 * n - h)) (e.coeff (6 * n - h)) := by
  have hB3 : (B ^ 3).natDegree < 8 * n := by
    compute_degree
    omega
  have hBe := coeff_mul_at_bounds68 B e (3 * n - g) (6 * n - h) hB he
  have hBei : (3 * n - g) + (6 * n - h) = 8 * n := by omega
  rw [hBei] at hBe
  have hcd := coeff_mul_at_bounds68 c d (4 * n - g) (5 * n - h) hc hd
  have hcdi : (4 * n - g) + (5 * n - h) = 8 * n := by omega
  rw [hcdi] at hcd
  simp only [residualIncidenceQ68, residualSumFourHom68, coeff_add,
    coeff_sub, coeff_smul, smul_eq_mul, hBe, hcd,
    coeff_eq_zero_of_natDegree_lt hB3]
  ring

set_option maxHeartbeats 2000000 in
theorem secondaryResidualInvariantFourPolynomial68_coeff_sumWall
    (B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hsmall : 2 * g < n) (hstrict : n < 3 * g)
    (hwall : h = n - g)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (secondaryResidualInvariantFourPolynomial68 B c d e).coeff (8 * n) =
      (8 / 3 : k) * residualSumFourHom68
        (B.coeff (3 * n - g)) (c.coeff (4 * n - g))
        (d.coeff (5 * n - h)) (e.coeff (6 * n - h)) := by
  have hB3 : (B ^ 3).natDegree < 8 * n := by
    compute_degree
    omega
  have hBe := coeff_mul_at_bounds68 B e (3 * n - g) (6 * n - h) hB he
  have hBei : (3 * n - g) + (6 * n - h) = 8 * n := by omega
  rw [hBei] at hBe
  have hcd := coeff_mul_at_bounds68 c d (4 * n - g) (5 * n - h) hc hd
  have hcdi : (4 * n - g) + (5 * n - h) = 8 * n := by omega
  rw [hcdi] at hcd
  simp only [secondaryResidualInvariantFourPolynomial68,
    residualSumFourHom68, coeff_add, coeff_smul, smul_eq_mul,
    coeff_eq_zero_of_natDegree_lt hB3, hBe, hcd]
  ring

set_option maxHeartbeats 2000000 in
theorem secondaryResidualInvariantThreePolynomial68_coeff_sumWall
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hsmall : 2 * g < n) (hstrict : n < 3 * g)
    (hwall : h = n - g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (secondaryResidualInvariantThreePolynomial68 A B c d e).coeff (9 * n) =
      (8 / 9 : k) * residualSumThreeHom68
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (d.coeff (5 * n - h))
        (e.coeff (6 * n - h)) := by
  have hABd := coeff_mul_mul_at_bounds68 A B d (2 * n)
    (3 * n - g) (5 * n - h) hA hB hd
  have hABdi : 2 * n + (3 * n - g) + (5 * n - h) = 9 * n := by omega
  rw [hABdi] at hABd
  have hB2c : (B ^ 2 * c).natDegree < 9 * n := by
    compute_degree
    omega
  have hce := coeff_mul_at_bounds68 c e (4 * n - g) (6 * n - h) hc he
  have hcei : (4 * n - g) + (6 * n - h) = 9 * n := by omega
  rw [hcei] at hce
  have hd2 : (d ^ 2).natDegree < 9 * n := by
    compute_degree
    omega
  simp only [secondaryResidualInvariantThreePolynomial68,
    residualSumThreeHom68, coeff_add, coeff_sub, coeff_smul, smul_eq_mul,
    hABd, coeff_eq_zero_of_natDegree_lt hB2c, hce,
    coeff_eq_zero_of_natDegree_lt hd2]
  ring

set_option maxHeartbeats 2000000 in
theorem secondaryLoadInvariantThreePolynomial68_degree_lt_sumWall
    (l beta gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g h : ℕ) (hg : 0 < g) (hsmall : 2 * g < n) (hwall : h = n - g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - h) :
    (secondaryLoadInvariantThreePolynomial68
      l beta gamma delta epsilon zeta A B c D e).natDegree < 9 * n := by
  simp only [secondaryLoadInvariantThreePolynomial68]
  compute_degree
  omega

set_option maxHeartbeats 4000000 in
/-- Mixed I4 coefficient at the collided index `8n = 9n-g-h`. -/
theorem cubicFirstIntegralFourPolynomial68_coeff_residualSumLoadWall
    (l beta gamma delta epsilon zeta : k) (A B c d e : k[X])
    (n g h : ℕ) (hn : 0 < n) (hg : 0 < g)
    (hsmall : 2 * g < n) (hstrict : n < 3 * g) (hwall : h = n - g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (cubicFirstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff (8 * n) =
      residualSumLoadWallFourScalar68
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (d.coeff (5 * n - h))
        (e.coeff (6 * n - h)) l := by
  let D := (1 / 3 : k) • (A * B) + d
  have hD : D.natDegree ≤ 5 * n - g := by
    simp only [D]
    compute_degree
    omega
  have he' : e.natDegree ≤ 6 * n - g :=
    residualSumLoadWall_eBound n g h hsmall hwall he
  have hhom := secondaryResidualInvariantFourPolynomial68_coeff_sumWall
    B c d e n g h hg hsmall hstrict hwall hB hc hd he
  have hload := secondaryLoadInvariantFourPolynomial68_coeff_eightRadius
    l beta gamma delta epsilon zeta A B c D e n g hn hg hA hB hc hD he'
  rw [cubicFirstIntegralFourPolynomial68_secondaryLoadSplit,
    show cubicFirstIntegralFourPolynomial68 0 0 0 0 0 0 A B c D e =
        secondaryResidualInvariantFourPolynomial68 B c d e by
      simpa only [D] using
        cubicFirstIntegralFourPolynomial68_residualCoordinates A B c d e,
    coeff_add, hhom, hload]
  simp only [residualSumLoadWallFourScalar68]
  ring

set_option maxHeartbeats 2000000 in
theorem cubicFirstIntegralThreePolynomial68_coeff_residualSumLoadWall
    (l beta gamma delta epsilon zeta : k) (A B c d e : k[X])
    (n g h : ℕ) (hg : 0 < g)
    (hsmall : 2 * g < n) (hstrict : n < 3 * g) (hwall : h = n - g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (cubicFirstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff (9 * n) =
      (8 / 9 : k) * residualSumThreeHom68
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (d.coeff (5 * n - h))
        (e.coeff (6 * n - h)) := by
  let D := (1 / 3 : k) • (A * B) + d
  have hD : D.natDegree ≤ 5 * n - g := by
    simp only [D]
    compute_degree
    omega
  have hload := secondaryLoadInvariantThreePolynomial68_degree_lt_sumWall
    l beta gamma delta epsilon zeta A B c D e n g h hg hsmall hwall
    hA hB hc hD he
  rw [cubicFirstIntegralThreePolynomial68_secondaryLoadSplit,
    show cubicFirstIntegralThreePolynomial68 0 0 0 0 0 0 A B c D e =
        secondaryResidualInvariantThreePolynomial68 A B c d e by
      simpa only [D] using
        cubicFirstIntegralThreePolynomial68_residualCoordinates A B c d e,
    coeff_add,
    secondaryResidualInvariantThreePolynomial68_coeff_sumWall
      A B c d e n g h hg hsmall hstrict hwall hA hB hc hd he,
    coeff_eq_zero_of_natDegree_lt hload, add_zero]

/-! ## Term-by-term remainder degree bounds on `h = n-g`

Cores, rest polynomials, Jacobian splits, and
`cubicLoadRowTwo/ZeroPolynomial68_eq_lCore_add_rest` are the tracked
definitions in `LowScale68SecondaryFirstLoadWallRemainder`.  Only the
wall-specific degree comparisons `2g < n < 3g`, `h = n-g` are restated
here. -/

set_option maxHeartbeats 2000000 in
theorem cubicLoadSRestPolynomial68_degree_le_sumWall
    (l alpha beta delta : k) (A B c : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hsmall : 2 * g < n) (hwall : h = n - g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g) :
    (cubicLoadSRestPolynomial68 l alpha beta delta A B c).natDegree ≤
      4 * n - g := by
  simp only [cubicLoadSRestPolynomial68]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
theorem cubicLoadURestPolynomial68_degree_le_sumWall
    (l alpha beta gamma delta zeta : k) (A B c D e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hsmall : 2 * g < n) (hwall : h = n - g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - h) :
    (cubicLoadURestPolynomial68 l alpha beta gamma delta zeta
      A B c D e).natDegree ≤ 6 * n - g := by
  simp only [cubicLoadURestPolynomial68]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
theorem cubicERestPolynomial68_degree_le_sumWall
    (A c e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hsmall : 2 * g < n) (hwall : h = n - g)
    (hA : A.natDegree ≤ 2 * n)
    (hc : c.natDegree ≤ 4 * n - g)
    (he : e.natDegree ≤ 6 * n - h) :
    (cubicERestPolynomial68 A c e).natDegree ≤ 6 * n - g := by
  simp only [cubicERestPolynomial68]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem cubicLoadRowTwoRestPolynomial68_degree_lt_sumWall
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g)
    (hsmall : 2 * g < n) (hwall : h = n - g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - h) :
    (cubicLoadRowTwoRestPolynomial68 l alpha beta gamma delta epsilon
      zeta eta A B c D e).natDegree < 10 * n - 1 := by
  let Ulc := cubicLoadUCorePolynomial68 l A
  let Ulr := cubicLoadURestPolynomial68 l alpha beta gamma delta zeta
    A B c D e
  let Ul := Ulc + Ulr
  let C0c := (1 / 3 : k) • A ^ 2
  let C0 := C0c + c
  let Slc := cubicLoadSCorePolynomial68 l A
  let Slr := cubicLoadSRestPolynomial68 l alpha beta delta A B c
  let Ec := (1 / 27 : k) • A ^ 3
  let Er := cubicERestPolynomial68 A c e
  let E := Ec + Er
  let Tl := cubicLoadTPolynomial68 l alpha beta gamma epsilon A B c D
  let Vl := cubicLoadVPolynomial68 l alpha beta gamma delta epsilon eta
    A B c D e
  have he' : e.natDegree ≤ 6 * n - g :=
    residualSumLoadWall_eBound n g h hsmall hwall he
  have hloads := cubicLoadPolynomials68_degreeBounds
    l alpha beta gamma delta epsilon zeta eta A B c D e n g
    hn hg hsmall hA hB hc hD he'
  have hUlc : Ulc.natDegree ≤ 6 * n :=
    cubicLoadUCorePolynomial68_degree_le l A n hA
  have hUlr : Ulr.natDegree ≤ 6 * n - g :=
    cubicLoadURestPolynomial68_degree_le_sumWall
      l alpha beta gamma delta zeta A B c D e n g h
      hg hsmall hwall hA hB hc hD he
  have hUl : Ul.natDegree ≤ 6 * n :=
    (natDegree_add_le Ulc Ulr).trans (max_le hUlc (hUlr.trans (by omega)))
  have hC0c : C0c.natDegree ≤ 4 * n := by
    simp only [C0c]
    compute_degree
    omega
  have hC0 : C0.natDegree ≤ 4 * n := by
    simp only [C0, C0c]
    compute_degree
    omega
  have hSlc : Slc.natDegree ≤ 4 * n :=
    cubicLoadSCorePolynomial68_degree_le l A n hA
  have hSlr : Slr.natDegree ≤ 4 * n - g :=
    cubicLoadSRestPolynomial68_degree_le_sumWall
      l alpha beta delta A B c n g h hg hsmall hwall hA hB hc
  have hEc : Ec.natDegree ≤ 6 * n := by
    simp only [Ec]
    compute_degree
    omega
  have hEr : Er.natDegree ≤ 6 * n - g :=
    cubicERestPolynomial68_degree_le_sumWall A c e n g h
      hg hsmall hwall hA hc he
  have hE : E.natDegree ≤ 6 * n :=
    (natDegree_add_le Ec Er).trans (max_le hEc (hEr.trans (by omega)))
  have hTl : Tl.natDegree ≤ 5 * n - g := by
    simpa only [Tl] using hloads.2.1
  have hVl : Vl.natDegree ≤ 7 * n - g := by
    simpa only [Vl] using hloads.2.2.2
  have h1 : (Ulc * derivative c).natDegree < 10 * n - 1 :=
    natDegree_mul_derivative_lt_of_add_sub68 Ulc c (6 * n) (4 * n - g)
      (10 * n - 1) (by omega) hUlc hc (by omega)
  have h2 : (Ulr * derivative C0).natDegree < 10 * n - 1 :=
    natDegree_mul_derivative_lt_of_add_sub68 Ulr C0 (6 * n - g) (4 * n)
      (10 * n - 1) (by omega) hUlr hC0 (by omega)
  have h3 : (Tl * derivative D).natDegree < 10 * n - 1 :=
    natDegree_mul_derivative_lt_of_add_sub68 Tl D (5 * n - g) (5 * n - g)
      (10 * n - 1) (by omega) hTl hD (by omega)
  have h4 : (Slc * derivative Er).natDegree < 10 * n - 1 :=
    natDegree_mul_derivative_lt_of_add_sub68 Slc Er (4 * n) (6 * n - g)
      (10 * n - 1) (by omega) hSlc hEr (by omega)
  have h5 : (Slr * derivative E).natDegree < 10 * n - 1 :=
    natDegree_mul_derivative_lt_of_add_sub68 Slr E (4 * n - g) (6 * n)
      (10 * n - 1) (by omega) hSlr hE (by omega)
  have h6 : (B * derivative Vl).natDegree < 10 * n - 1 :=
    natDegree_mul_derivative_lt_of_add_sub68 B Vl (3 * n - g) (7 * n - g)
      (10 * n - 1) (by omega) hB hVl (by omega)
  have h7 : (C0c * derivative Ulr).natDegree < 10 * n - 1 :=
    natDegree_mul_derivative_lt_of_add_sub68 C0c Ulr (4 * n) (6 * n - g)
      (10 * n - 1) (by omega) hC0c hUlr (by omega)
  have h8 : (c * derivative Ul).natDegree < 10 * n - 1 :=
    natDegree_mul_derivative_lt_of_add_sub68 c Ul (4 * n - g) (6 * n)
      (10 * n - 1) (by omega) hc hUl (by omega)
  have h9 : (D * derivative Tl).natDegree < 10 * n - 1 :=
    natDegree_mul_derivative_lt_of_add_sub68 D Tl (5 * n - g) (5 * n - g)
      (10 * n - 1) (by omega) hD hTl (by omega)
  have h3s := natDegree_smul_lt68 (2 : k) h3
  have h4s := natDegree_smul_lt68 (3 : k) h4
  have h5s := natDegree_smul_lt68 (3 : k) h5
  have h6s := natDegree_smul_lt68 (3 : k) h6
  have h7s := natDegree_smul_lt68 (2 : k) h7
  have h8s := natDegree_smul_lt68 (2 : k) h8
  have s1 := natDegree_add_lt_of_both68 h1 h2
  have s2 := natDegree_add_lt_of_both68 s1 h3s
  have s3 := natDegree_add_lt_of_both68 s2 h4s
  have s4 := natDegree_add_lt_of_both68 s3 h5s
  have s5 := natDegree_sub_lt_of_both68 s4 h6s
  have s6 := natDegree_sub_lt_of_both68 s5 h7s
  have s7 := natDegree_sub_lt_of_both68 s6 h8s
  have s8 := natDegree_sub_lt_of_both68 s7 h9
  rw [cubicLoadRowTwoRestPolynomial68_eq_splitPieces]
  exact s8

set_option maxHeartbeats 3000000 in
theorem cubicLoadRowZeroRestPolynomial68_degree_lt_sumWall
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g)
    (hsmall : 2 * g < n) (hwall : h = n - g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - h) :
    (cubicLoadRowZeroRestPolynomial68 l alpha beta gamma delta epsilon
      zeta eta A B c D e).natDegree < 12 * n - 1 := by
  let Ulc := cubicLoadUCorePolynomial68 l A
  let Ulr := cubicLoadURestPolynomial68 l alpha beta gamma delta zeta
    A B c D e
  let Ec := (1 / 27 : k) • A ^ 3
  let Er := cubicERestPolynomial68 A c e
  let E := Ec + Er
  let Vl := cubicLoadVPolynomial68 l alpha beta gamma delta epsilon eta
    A B c D e
  have he' : e.natDegree ≤ 6 * n - g :=
    residualSumLoadWall_eBound n g h hsmall hwall he
  have hloads := cubicLoadPolynomials68_degreeBounds
    l alpha beta gamma delta epsilon zeta eta A B c D e n g
    hn hg hsmall hA hB hc hD he'
  have hUlc : Ulc.natDegree ≤ 6 * n :=
    cubicLoadUCorePolynomial68_degree_le l A n hA
  have hUlr : Ulr.natDegree ≤ 6 * n - g :=
    cubicLoadURestPolynomial68_degree_le_sumWall
      l alpha beta gamma delta zeta A B c D e n g h
      hg hsmall hwall hA hB hc hD he
  have hEr : Er.natDegree ≤ 6 * n - g :=
    cubicERestPolynomial68_degree_le_sumWall A c e n g h
      hg hsmall hwall hA hc he
  have hEc : Ec.natDegree ≤ 6 * n := by
    simp only [Ec]
    compute_degree
    omega
  have hE : E.natDegree ≤ 6 * n :=
    (natDegree_add_le Ec Er).trans (max_le hEc (hEr.trans (by omega)))
  have hVl : Vl.natDegree ≤ 7 * n - g := by
    simpa only [Vl] using hloads.2.2.2
  have h1 : (Ulc * derivative Er).natDegree < 12 * n - 1 :=
    natDegree_mul_derivative_lt_of_add_sub68 Ulc Er (6 * n) (6 * n - g)
      (12 * n - 1) (by omega) hUlc hEr (by omega)
  have h2 : (Ulr * derivative E).natDegree < 12 * n - 1 :=
    natDegree_mul_derivative_lt_of_add_sub68 Ulr E (6 * n - g) (6 * n)
      (12 * n - 1) (by omega) hUlr hE (by omega)
  have h3 : (D * derivative Vl).natDegree < 12 * n - 1 :=
    natDegree_mul_derivative_lt_of_add_sub68 D Vl (5 * n - g) (7 * n - g)
      (12 * n - 1) (by omega) hD hVl (by omega)
  change (Ulc * derivative Er + Ulr * derivative E -
      D * derivative Vl).natDegree < _
  exact natDegree_sub_lt_of_both68 (natDegree_add_lt_of_both68 h1 h2) h3

set_option maxHeartbeats 2000000 in
theorem cubicLoadRowTwoPolynomial68_coeff_residualSumLoadWall
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g)
    (hsmall : 2 * g < n) (hwall : h = n - g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - h) :
    (cubicLoadRowTwoPolynomial68 l alpha beta gamma delta epsilon zeta eta
      A B c D e).coeff (10 * n - 1) =
      (35 / 324 : k) * (n : k) * l * A.coeff (2 * n) ^ 5 := by
  rw [cubicLoadRowTwoPolynomial68_eq_lCore_add_rest, coeff_add,
    coeff_eq_zero_of_natDegree_lt
      (cubicLoadRowTwoRestPolynomial68_degree_lt_sumWall
        l alpha beta gamma delta epsilon zeta eta A B c D e n g h
        hn hg hsmall hwall hA hB hc hD he), add_zero]
  exact cubicLoadRowTwoLCorePolynomial68_coeff_loadWall l A n hn hA

set_option maxHeartbeats 2000000 in
theorem cubicLoadRowZeroPolynomial68_coeff_residualSumLoadWall
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g)
    (hsmall : 2 * g < n) (hwall : h = n - g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - h) :
    (cubicLoadRowZeroPolynomial68 l alpha beta gamma delta epsilon zeta eta
      A B c D e).coeff (12 * n - 1) =
      (35 / 1944 : k) * (n : k) * l * A.coeff (2 * n) ^ 6 := by
  rw [cubicLoadRowZeroPolynomial68_eq_lCore_add_rest, coeff_add,
    coeff_eq_zero_of_natDegree_lt
      (cubicLoadRowZeroRestPolynomial68_degree_lt_sumWall
        l alpha beta gamma delta epsilon zeta eta A B c D e n g h
        hn hg hsmall hwall hA hB hc hD he), add_zero]
  exact cubicLoadRowZeroLCorePolynomial68_coeff_loadWall l A n hn hA

/-! ## Homogeneous residual one-forms at the wall indices -/

set_option maxHeartbeats 4000000 in
/-- Residual row-two coefficient at the collided index `10n-1`. -/
theorem secondaryResidualRowTwoPolynomial68_coeff_residualSumLoadWall
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g)
    (hsmall : 2 * g < n) (hstrict : n < 3 * g) (hwall : h = n - g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (secondaryResidualRowTwoPolynomial68 A B c d e).coeff (10 * n - 1) =
      (56 / 9 : k) * (n : k) * A.coeff (2 * n) *
        residualSumFourHom68 (B.coeff (3 * n - g)) (c.coeff (4 * n - g))
          (d.coeff (5 * n - h)) (e.coeff (6 * n - h)) := by
  let Q := residualIncidenceQ68 B c d e
  have hQdeg : Q.natDegree ≤ 8 * n :=
    residualIncidenceQ68_degree_le_sumWall B c d e n g h
      hg hsmall hstrict hwall hB hc hd he
  have hQcoeff : Q.coeff (8 * n) =
      residualSumFourHom68 (B.coeff (3 * n - g)) (c.coeff (4 * n - g))
        (d.coeff (5 * n - h)) (e.coeff (6 * n - h)) :=
    residualIncidenceQ68_coeff_sumWall B c d e n g h
      hg hsmall hstrict hwall hB hc hd he
  have hAQ := coeff_mul_derivative_at_bounds68 A Q (2 * n) (8 * n)
    (by omega) hA hQdeg
  have hiAQ : 2 * n + 8 * n - 1 = 10 * n - 1 := by omega
  rw [hiAQ, hQcoeff] at hAQ
  have hQA := coeff_mul_derivative_at_bounds68 Q A (8 * n) (2 * n)
    (by omega) hQdeg hA
  have hiQA : 8 * n + 2 * n - 1 = 10 * n - 1 := by omega
  rw [hiQA, hQcoeff] at hQA
  have hQA' : (derivative A * Q).coeff (10 * n - 1) =
      A.coeff (2 * n) *
        residualSumFourHom68 (B.coeff (3 * n - g)) (c.coeff (4 * n - g))
          (d.coeff (5 * n - h)) (e.coeff (6 * n - h)) *
        ((2 * n : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hQA
  have hlow1 : (A * B ^ 2 * derivative B).natDegree < 10 * n - 1 := by
    compute_degree
    omega
  have hlow2 : (derivative A * B ^ 3).natDegree < 10 * n - 1 := by
    compute_degree
    omega
  have hlow3 : (derivative (B ^ 2 * d)).natDegree < 10 * n - 1 := by
    have hB2 : (B ^ 2).natDegree ≤ 6 * n - 2 * g := by
      compute_degree
      omega
    have hprod := natDegree_mul_le_of_le hB2 hd
    have hsum : 6 * n - 2 * g + (5 * n - h) = 11 * n - 2 * g - h := by
      omega
    rw [hsum] at hprod
    have hder : (derivative (B ^ 2 * d)).natDegree ≤
        11 * n - 2 * g - h - 1 :=
      (natDegree_derivative_le (B ^ 2 * d)).trans
        (Nat.sub_le_sub_right hprod 1)
    exact hder.trans_lt (by omega)
  have hlow4 : (derivative (B * c ^ 2)).natDegree < 10 * n - 1 := by
    have hc2 : (c ^ 2).natDegree ≤ 8 * n - 2 * g := by
      compute_degree
      omega
    have hprod := natDegree_mul_le_of_le hB hc2
    have hsum : (3 * n - g) + (8 * n - 2 * g) = 11 * n - 3 * g := by
      omega
    rw [hsum] at hprod
    have hder : (derivative (B * c ^ 2)).natDegree ≤
        11 * n - 3 * g - 1 :=
      (natDegree_derivative_le (B * c ^ 2)).trans
        (Nat.sub_le_sub_right hprod 1)
    exact hder.trans_lt (by omega)
  have hlow5 : (derivative (d * e)).natDegree < 10 * n - 1 := by
    have hprod := natDegree_mul_le_of_le hd he
    have hsum : (5 * n - h) + (6 * n - h) = 11 * n - 2 * h := by omega
    rw [hsum] at hprod
    have hder : (derivative (d * e)).natDegree ≤ 11 * n - 2 * h - 1 :=
      (natDegree_derivative_le (d * e)).trans
        (Nat.sub_le_sub_right hprod 1)
    exact hder.trans_lt (by omega)
  have hcast8 : (((8 * n : ℕ) : k)) = (8 : k) * (n : k) := by
    push_cast
    rfl
  have hcast2 : (((2 * n : ℕ) : k)) = (2 : k) * (n : k) := by
    push_cast
    rfl
  simp only [Q] at hAQ hQA'
  rw [residualRowTwo_eq_inner68, coeff_smul]
  simp only [residualRowTwoInner68, coeff_add, coeff_smul, smul_eq_mul,
    hAQ, hQA',
    coeff_eq_zero_of_natDegree_lt hlow1,
    coeff_eq_zero_of_natDegree_lt hlow2,
    coeff_eq_zero_of_natDegree_lt hlow3,
    coeff_eq_zero_of_natDegree_lt hlow4,
    coeff_eq_zero_of_natDegree_lt hlow5]
  rw [hcast8, hcast2]
  ring

set_option maxHeartbeats 4000000 in
theorem secondaryResidualRowZeroPolynomial68_coeff_residualSumLoadWall
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g)
    (hsmall : 2 * g < n) (hstrict : n < 3 * g) (hwall : h = n - g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (secondaryResidualRowZeroPolynomial68 A B c d e).coeff (12 * n - 1) =
      -(8 / 27 : k) * (n : k) * A.coeff (2 * n) ^ 2 *
        residualSumFourHom68 (B.coeff (3 * n - g)) (c.coeff (4 * n - g))
          (d.coeff (5 * n - h)) (e.coeff (6 * n - h)) := by
  have h1 := coeff_mul_mul_mul_derivative_at_bounds68 A B e A
    (2 * n) (3 * n - g) (6 * n - h) (2 * n) (by omega) hA hB he hA
  have hi1 : 2 * n + (3 * n - g) + (6 * n - h) + 2 * n - 1 =
      12 * n - 1 := by omega
  rw [hi1] at h1
  have h1' : (A * derivative A * B * e).coeff (12 * n - 1) =
      A.coeff (2 * n) * B.coeff (3 * n - g) *
        e.coeff (6 * n - h) * A.coeff (2 * n) * ((2 * n : ℕ) : k) := by
    have hcomm : A * derivative A * B * e =
        A * B * e * derivative A := by
      simp only [mul_assoc, mul_comm, mul_left_comm]
    rw [hcomm]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h1
  have h2 := coeff_mul_mul_mul_derivative_at_bounds68 A c d A
    (2 * n) (4 * n - g) (5 * n - h) (2 * n) (by omega) hA hc hd hA
  have hi2 : 2 * n + (4 * n - g) + (5 * n - h) + 2 * n - 1 =
      12 * n - 1 := by omega
  rw [hi2] at h2
  have h2' : (A * derivative A * c * d).coeff (12 * n - 1) =
      A.coeff (2 * n) * c.coeff (4 * n - g) *
        d.coeff (5 * n - h) * A.coeff (2 * n) * ((2 * n : ℕ) : k) := by
    have hcomm : A * derivative A * c * d =
        A * c * d * derivative A := by
      simp only [mul_assoc, mul_comm, mul_left_comm]
    rw [hcomm]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h2
  have hlow1 : (A * B ^ 2 * derivative d).natDegree < 12 * n - 1 := by
    compute_degree
    omega
  have hlow2 : (A * B * derivative B * d).natDegree < 12 * n - 1 := by
    compute_degree
    omega
  have hlow3 : (derivative A * B * c ^ 2).natDegree < 12 * n - 1 := by
    compute_degree
    omega
  have hlow4 : (derivative A * d * e).natDegree < 12 * n - 1 := by
    compute_degree
    omega
  have hlow5 : (B * c * derivative e).natDegree < 12 * n - 1 := by
    compute_degree
    omega
  have hlow6 : (B * d * derivative d).natDegree < 12 * n - 1 := by
    compute_degree
    omega
  have hlow7 : (derivative B * d ^ 2).natDegree < 12 * n - 1 := by
    compute_degree
    omega
  have hlow8 : (c * derivative c * d).natDegree < 12 * n - 1 := by
    compute_degree
    omega
  have hcast2 : (((2 * n : ℕ) : k)) = (2 : k) * (n : k) := by
    push_cast
    rfl
  simp only [secondaryResidualRowZeroPolynomial68, coeff_smul, coeff_add,
    coeff_sub, h1', h2',
    coeff_eq_zero_of_natDegree_lt hlow1,
    coeff_eq_zero_of_natDegree_lt hlow2,
    coeff_eq_zero_of_natDegree_lt hlow3,
    coeff_eq_zero_of_natDegree_lt hlow4,
    coeff_eq_zero_of_natDegree_lt hlow5,
    coeff_eq_zero_of_natDegree_lt hlow6,
    coeff_eq_zero_of_natDegree_lt hlow7,
    coeff_eq_zero_of_natDegree_lt hlow8, smul_eq_mul]
  rw [hcast2]
  simp only [residualSumFourHom68]
  ring

/-! ## Combined one-form coefficients -/

set_option maxHeartbeats 4000000 in
theorem cubicRowTwoPolynomial68_coeff_residualSumLoadWall
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g)
    (hsmall : 2 * g < n) (hstrict : n < 3 * g) (hwall : h = n - g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (cubicHomogeneousRowTwoPolynomial68 A B c
          ((1 / 3 : k) • (A * B) + d) e +
        cubicLoadRowTwoPolynomial68 l alpha beta gamma delta epsilon zeta eta
          A B c ((1 / 3 : k) • (A * B) + d) e).coeff (10 * n - 1) =
      residualSumLoadWallTwoScalar68 (n : k)
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (d.coeff (5 * n - h))
        (e.coeff (6 * n - h)) l := by
  let D := (1 / 3 : k) • (A * B) + d
  have hD : D.natDegree ≤ 5 * n - g := by
    simp only [D]
    compute_degree
    omega
  have hident :
      cubicHomogeneousRowTwoPolynomial68 A B c D e =
        secondaryResidualRowTwoPolynomial68 A B c d e := by
    simpa only [D] using
      cubicHomogeneousRowTwoPolynomial68_residualCoordinates A B c d e
  rw [coeff_add, hident,
    secondaryResidualRowTwoPolynomial68_coeff_residualSumLoadWall
      A B c d e n g h hn hg hsmall hstrict hwall hA hB hc hd he,
    cubicLoadRowTwoPolynomial68_coeff_residualSumLoadWall
      l alpha beta gamma delta epsilon zeta eta A B c D e n g h
      hn hg hsmall hwall hA hB hc hD he]
  simp [residualSumLoadWallTwoScalar68]

set_option maxHeartbeats 4000000 in
theorem cubicRowZeroPolynomial68_coeff_residualSumLoadWall
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g)
    (hsmall : 2 * g < n) (hstrict : n < 3 * g) (hwall : h = n - g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (cubicHomogeneousRowZeroPolynomial68 A B c
          ((1 / 3 : k) • (A * B) + d) e +
        cubicLoadRowZeroPolynomial68 l alpha beta gamma delta epsilon zeta eta
          A B c ((1 / 3 : k) • (A * B) + d) e).coeff (12 * n - 1) =
      residualSumLoadWallZeroScalar68 (n : k)
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (d.coeff (5 * n - h))
        (e.coeff (6 * n - h)) l := by
  let D := (1 / 3 : k) • (A * B) + d
  have hD : D.natDegree ≤ 5 * n - g := by
    simp only [D]
    compute_degree
    omega
  have hident :
      cubicHomogeneousRowZeroPolynomial68 A B c D e =
        secondaryResidualRowZeroPolynomial68 A B c d e := by
    simpa only [D] using
      cubicHomogeneousRowZeroPolynomial68_residualCoordinates A B c d e
  rw [coeff_add, hident,
    secondaryResidualRowZeroPolynomial68_coeff_residualSumLoadWall
      A B c d e n g h hn hg hsmall hstrict hwall hA hB hc hd he,
    cubicLoadRowZeroPolynomial68_coeff_residualSumLoadWall
      l alpha beta gamma delta epsilon zeta eta A B c D e n g h
      hn hg hsmall hwall hA hB hc hD he]
  simp [residualSumLoadWallZeroScalar68]

/-! ## Polynomial face from the literal invariants and one-forms -/

set_option maxHeartbeats 4000000 in
theorem polynomialResidualSumLoadWallFace68
    (l alpha beta gamma delta epsilon zeta eta i4 i3 : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g)
    (hsmall : 2 * g < n) (hstrict : n < 3 * g) (hwall : h = n - g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (ha : A.coeff (2 * n) ≠ 0)
    (hi4 : cubicFirstIntegralFourPolynomial68
      l beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hi3 : cubicFirstIntegralThreePolynomial68
      l beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i3)
    (hrowTwo :
      (cubicHomogeneousRowTwoPolynomial68 A B c
            ((1 / 3 : k) • (A * B) + d) e +
          cubicLoadRowTwoPolynomial68 l alpha beta gamma delta epsilon
            zeta eta A B c ((1 / 3 : k) • (A * B) + d) e).coeff
          (10 * n - 1) = 0)
    (hrowZero :
      (cubicHomogeneousRowZeroPolynomial68 A B c
            ((1 / 3 : k) • (A * B) + d) e +
          cubicLoadRowZeroPolynomial68 l alpha beta gamma delta epsilon
            zeta eta A B c ((1 / 3 : k) • (A * B) + d) e).coeff
          (12 * n - 1) = 0) :
    ResidualSumLoadWallFace68 (n : k)
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (d.coeff (5 * n - h))
      (e.coeff (6 * n - h)) l := by
  have hncast : (n : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hfour := congrArg (fun p : k[X] => p.coeff (8 * n)) hi4
  rw [cubicFirstIntegralFourPolynomial68_coeff_residualSumLoadWall
    l beta gamma delta epsilon zeta A B c d e n g h hn hg
    hsmall hstrict hwall hA hB hc hd he] at hfour
  have ht4 : 8 * n ≠ 0 := by omega
  simp only [coeff_C, ite_eq_right ht4] at hfour
  have hfourNum : residualSumLoadWallFourNumerator68
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (d.coeff (5 * n - h))
      (e.coeff (6 * n - h)) l = 0 := by
    have hsc := residualSumLoadWallFourScalar68_eq_numerator
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (d.coeff (5 * n - h))
      (e.coeff (6 * n - h)) l
    rw [hsc] at hfour
    exact (div_eq_zero_iff.mp hfour).resolve_right (by norm_num)
  have hthree := congrArg (fun p : k[X] => p.coeff (9 * n)) hi3
  rw [cubicFirstIntegralThreePolynomial68_coeff_residualSumLoadWall
    l beta gamma delta epsilon zeta A B c d e n g h hg
    hsmall hstrict hwall hA hB hc hd he] at hthree
  have ht3 : 9 * n ≠ 0 := by omega
  simp only [coeff_C, ite_eq_right ht3] at hthree
  have hthreeNum : residualSumThreeHom68
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (d.coeff (5 * n - h))
      (e.coeff (6 * n - h)) = 0 :=
    (mul_eq_zero.mp hthree).resolve_left (by norm_num)
  have htwo := hrowTwo
  rw [cubicRowTwoPolynomial68_coeff_residualSumLoadWall
    l alpha beta gamma delta epsilon zeta eta A B c d e n g h
    hn hg hsmall hstrict hwall hA hB hc hd he] at htwo
  have htwoNum : residualSumLoadWallTwoNumerator68
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (d.coeff (5 * n - h))
      (e.coeff (6 * n - h)) l = 0 := by
    have hsc := residualSumLoadWallTwoScalar68_eq_numerator (n : k)
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (d.coeff (5 * n - h))
      (e.coeff (6 * n - h)) l
    rw [hsc] at htwo
    have hdiv := div_eq_zero_iff.mp htwo
    have hprod : (n : k) *
        residualSumLoadWallTwoNumerator68
          (A.coeff (2 * n)) (B.coeff (3 * n - g))
          (c.coeff (4 * n - g)) (d.coeff (5 * n - h))
          (e.coeff (6 * n - h)) l = 0 :=
      hdiv.resolve_right (by norm_num)
    exact (mul_eq_zero.mp hprod).resolve_left hncast
  have hzero := hrowZero
  rw [cubicRowZeroPolynomial68_coeff_residualSumLoadWall
    l alpha beta gamma delta epsilon zeta eta A B c d e n g h
    hn hg hsmall hstrict hwall hA hB hc hd he] at hzero
  have hzeroNum : residualSumLoadWallZeroNumerator68
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (d.coeff (5 * n - h))
      (e.coeff (6 * n - h)) l = 0 := by
    have hsc := residualSumLoadWallZeroScalar68_eq_numerator (n : k)
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (d.coeff (5 * n - h))
      (e.coeff (6 * n - h)) l
    rw [hsc] at hzero
    have hdiv := div_eq_zero_iff.mp hzero
    have hprod : (n : k) *
        residualSumLoadWallZeroNumerator68
          (A.coeff (2 * n)) (B.coeff (3 * n - g))
          (c.coeff (4 * n - g)) (d.coeff (5 * n - h))
          (e.coeff (6 * n - h)) l = 0 :=
      hdiv.resolve_right (by norm_num)
    exact (mul_eq_zero.mp hprod).resolve_left hncast
  exact ⟨hfourNum, hthreeNum, htwoNum, hzeroNum⟩

theorem polynomialResidualSumLoadWallClassified68
    (l alpha beta gamma delta epsilon zeta eta i4 i3 : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g)
    (hsmall : 2 * g < n) (hstrict : n < 3 * g) (hwall : h = n - g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (ha : A.coeff (2 * n) ≠ 0)
    (hi4 : cubicFirstIntegralFourPolynomial68
      l beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hi3 : cubicFirstIntegralThreePolynomial68
      l beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i3)
    (hrowTwo :
      (cubicHomogeneousRowTwoPolynomial68 A B c
            ((1 / 3 : k) • (A * B) + d) e +
          cubicLoadRowTwoPolynomial68 l alpha beta gamma delta epsilon
            zeta eta A B c ((1 / 3 : k) • (A * B) + d) e).coeff
          (10 * n - 1) = 0)
    (hrowZero :
      (cubicHomogeneousRowZeroPolynomial68 A B c
            ((1 / 3 : k) • (A * B) + d) e +
          cubicLoadRowZeroPolynomial68 l alpha beta gamma delta epsilon
            zeta eta A B c ((1 / 3 : k) • (A * B) + d) e).coeff
          (12 * n - 1) = 0) :
    l = 0 ∧
      SecondaryResidualBetweenFace68
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (d.coeff (5 * n - h))
        (e.coeff (6 * n - h)) :=
  residualSumLoadWallFace68_classify (n : k)
    (A.coeff (2 * n)) (B.coeff (3 * n - g))
    (c.coeff (4 * n - g)) (d.coeff (5 * n - h))
    (e.coeff (6 * n - h)) l ha
    (polynomialResidualSumLoadWallFace68
      l alpha beta gamma delta epsilon zeta eta i4 i3
      A B c d e n g h hn hg hsmall hstrict hwall hA hB hc hd he ha
      hi4 hi3 hrowTwo hrowZero)

/-! ## Expanded I4/I3 and lower-row identities -/

theorem residualSumLoadWallRowZeroIndex68_gt_fiftyNine
    (n : ℕ) (hn : 10 ≤ n) : 59 < 12 * n - 1 := by
  omega

set_option maxHeartbeats 4000000 in
theorem polynomialResidualSumLoadWallInvariants68
    (l beta gamma delta epsilon zeta i4 i3 : k)
    (A B C0 c D E d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g)
    (hsmall : 2 * g < n) (hstrict : n < 3 * g) (hwall : h = n - g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hC0 : C0 = (1 / 3 : k) • A ^ 2 + c)
    (hD0 : D = (1 / 3 : k) • (A * B) + d)
    (hE0 : E = (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)
    (hI4 : firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
      A B C0 D E = C i4)
    (hI3 : firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
      A B C0 D E = C i3) :
    residualSumLoadWallFourNumerator68
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (d.coeff (5 * n - h))
        (e.coeff (6 * n - h)) l = 0 ∧
      residualSumThreeHom68
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (d.coeff (5 * n - h))
        (e.coeff (6 * n - h)) = 0 := by
  have ht4 : 8 * n ≠ 0 := by omega
  have ht3 : 9 * n ≠ 0 := by omega
  have hfour := congrArg (fun p : k[X] => p.coeff (8 * n)) hI4
  rw [hC0, hE0, firstIntegralFourPolynomial68_cubicCoordinates, hD0,
    cubicFirstIntegralFourPolynomial68_coeff_residualSumLoadWall
      l beta gamma delta epsilon zeta A B c d e n g h hn hg
      hsmall hstrict hwall hA hB hc hd he] at hfour
  simp only [coeff_C, ite_eq_right ht4] at hfour
  have hthree := congrArg (fun p : k[X] => p.coeff (9 * n)) hI3
  rw [hC0, hE0, firstIntegralThreePolynomial68_cubicCoordinates, hD0,
    cubicFirstIntegralThreePolynomial68_coeff_residualSumLoadWall
      l beta gamma delta epsilon zeta A B c d e n g h hg
      hsmall hstrict hwall hA hB hc hd he] at hthree
  simp only [coeff_C, ite_eq_right ht3] at hthree
  constructor
  · have hsc := residualSumLoadWallFourScalar68_eq_numerator
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (d.coeff (5 * n - h))
      (e.coeff (6 * n - h)) l
    rw [hsc] at hfour
    exact (div_eq_zero_iff.mp hfour).resolve_right (by norm_num)
  · exact (mul_eq_zero.mp hthree).resolve_left (by norm_num)

set_option maxHeartbeats 4000000 in
theorem integratedLowerRowTwoPolynomial68_coeff_residualSumLoadWall
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g)
    (hsmall : 2 * g < n) (hstrict : n < 3 * g) (hwall : h = n - g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (lowerRowTwoPolynomial68
      (integratedSPolynomial68 l alpha beta delta A B
        ((1 / 3 : k) • A ^ 2 + c) ((1 / 3 : k) • (A * B) + d))
      (integratedTPolynomial68 l alpha beta gamma epsilon A B
        ((1 / 3 : k) • A ^ 2 + c) ((1 / 3 : k) • (A * B) + d)
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      (integratedUPolynomial68 l alpha beta gamma delta zeta A B
        ((1 / 3 : k) • A ^ 2 + c) ((1 / 3 : k) • (A * B) + d)
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta A B
        ((1 / 3 : k) • A ^ 2 + c) ((1 / 3 : k) • (A * B) + d)
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      B ((1 / 3 : k) • A ^ 2 + c) ((1 / 3 : k) • (A * B) + d)
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)).coeff
          (10 * n - 1) =
      residualSumLoadWallTwoScalar68 (n : k)
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (d.coeff (5 * n - h))
        (e.coeff (6 * n - h)) l := by
  let D0 := (1 / 3 : k) • (A * B) + d
  have hcoords := integratedPolynomial68_cubicCoordinates
    l alpha beta gamma delta epsilon zeta eta A B c D0 e
  rw [hcoords.s_eq, hcoords.t_eq, hcoords.u_eq, hcoords.v_eq,
    cubicRowTwoPolynomial68_split,
    cubicRowTwoPolynomial68_coeff_residualSumLoadWall
      l alpha beta gamma delta epsilon zeta eta A B c d e n g h
      hn hg hsmall hstrict hwall hA hB hc hd he]

set_option maxHeartbeats 4000000 in
theorem integratedLowerRowZeroPolynomial68_coeff_residualSumLoadWall
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g)
    (hsmall : 2 * g < n) (hstrict : n < 3 * g) (hwall : h = n - g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (lowerRowZeroPolynomial68
      (integratedUPolynomial68 l alpha beta gamma delta zeta A B
        ((1 / 3 : k) • A ^ 2 + c) ((1 / 3 : k) • (A * B) + d)
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta A B
        ((1 / 3 : k) • A ^ 2 + c) ((1 / 3 : k) • (A * B) + d)
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      ((1 / 3 : k) • (A * B) + d)
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)).coeff
          (12 * n - 1) =
      residualSumLoadWallZeroScalar68 (n : k)
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (d.coeff (5 * n - h))
        (e.coeff (6 * n - h)) l := by
  let D0 := (1 / 3 : k) • (A * B) + d
  have hcoords := integratedPolynomial68_cubicCoordinates
    l alpha beta gamma delta epsilon zeta eta A B c D0 e
  rw [hcoords.u_eq, hcoords.v_eq, cubicRowZeroPolynomial68_split,
    cubicRowZeroPolynomial68_coeff_residualSumLoadWall
      l alpha beta gamma delta epsilon zeta eta A B c d e n g h
      hn hg hsmall hstrict hwall hA hB hc hd he]

set_option maxHeartbeats 4000000 in
/-- Integrated I4/I3 and lower rows, rewritten to the cubic residual
coordinates, classify as `l = 0` and the ordinary residual middle face. -/
theorem polynomialResidualSumLoadWallClassified68_of_integratedRows
    (l alpha beta gamma delta epsilon zeta eta i4 i3 : k)
    (A B C0 c D E d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g)
    (hsmall : 2 * g < n) (hstrict : n < 3 * g) (hwall : h = n - g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (ha : A.coeff (2 * n) ≠ 0)
    (hC0 : C0 = (1 / 3 : k) • A ^ 2 + c)
    (hD0 : D = (1 / 3 : k) • (A * B) + d)
    (hE0 : E = (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)
    (hI4 : firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
      A B C0 D E = C i4)
    (hI3 : firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
      A B C0 D E = C i3)
    (hrowTwo : lowerRowTwoPolynomial68
      (integratedSPolynomial68 l alpha beta delta A B C0 D)
      (integratedTPolynomial68 l alpha beta gamma epsilon A B C0 D E)
      (integratedUPolynomial68 l alpha beta gamma delta zeta A B C0 D E)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        A B C0 D E) B C0 D E = 0)
    (hrowZero : (lowerRowZeroPolynomial68
      (integratedUPolynomial68 l alpha beta gamma delta zeta A B C0 D E)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        A B C0 D E) D E).coeff (12 * n - 1) = 0) :
    l = 0 ∧
      SecondaryResidualBetweenFace68
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (d.coeff (5 * n - h))
        (e.coeff (6 * n - h)) := by
  have hi4c : cubicFirstIntegralFourPolynomial68
      l beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4 := by
    have h := hI4
    rw [hC0, hE0, firstIntegralFourPolynomial68_cubicCoordinates, hD0] at h
    exact h
  have hi3c : cubicFirstIntegralThreePolynomial68
      l beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i3 := by
    have h := hI3
    rw [hC0, hE0, firstIntegralThreePolynomial68_cubicCoordinates, hD0] at h
    exact h
  have h2c :
      (cubicHomogeneousRowTwoPolynomial68 A B c
            ((1 / 3 : k) • (A * B) + d) e +
          cubicLoadRowTwoPolynomial68 l alpha beta gamma delta epsilon
            zeta eta A B c ((1 / 3 : k) • (A * B) + d) e).coeff
          (10 * n - 1) = 0 := by
    have h2 := hrowTwo
    rw [hC0, hD0, hE0] at h2
    have hcoeff := congrArg (fun p : k[X] => p.coeff (10 * n - 1)) h2
    rw [integratedLowerRowTwoPolynomial68_coeff_residualSumLoadWall
      l alpha beta gamma delta epsilon zeta eta A B c d e n g h
      hn hg hsmall hstrict hwall hA hB hc hd he] at hcoeff
    simp only [coeff_zero] at hcoeff
    have hsc := cubicRowTwoPolynomial68_coeff_residualSumLoadWall
      l alpha beta gamma delta epsilon zeta eta A B c d e n g h
      hn hg hsmall hstrict hwall hA hB hc hd he
    rw [hsc]
    exact hcoeff
  have h0c :
      (cubicHomogeneousRowZeroPolynomial68 A B c
            ((1 / 3 : k) • (A * B) + d) e +
          cubicLoadRowZeroPolynomial68 l alpha beta gamma delta epsilon
            zeta eta A B c ((1 / 3 : k) • (A * B) + d) e).coeff
          (12 * n - 1) = 0 := by
    have h0 := hrowZero
    rw [hC0, hD0, hE0] at h0
    rw [integratedLowerRowZeroPolynomial68_coeff_residualSumLoadWall
      l alpha beta gamma delta epsilon zeta eta A B c d e n g h
      hn hg hsmall hstrict hwall hA hB hc hd he] at h0
    have hsc := cubicRowZeroPolynomial68_coeff_residualSumLoadWall
      l alpha beta gamma delta epsilon zeta eta A B c d e n g h
      hn hg hsmall hstrict hwall hA hB hc hd he
    rw [hsc]
    exact h0
  exact polynomialResidualSumLoadWallClassified68
    l alpha beta gamma delta epsilon zeta eta i4 i3
    A B c d e n g h hn hg hsmall hstrict hwall hA hB hc hd he ha
    hi4c hi3c h2c h0c

/-! ## Canonical maximal-expanded wrapper -/

set_option maxHeartbeats 4000000 in
/-- On the canonical expanded system, the mixed residual sum-load wall
`h = n-g` inside `2g < n < 3g` forces `l = 0` and is therefore empty:
the residual load-zero endgame applies throughout `2g < n`.  No residual
support premise is required. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_residualSumLoadWall_impossible68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hchamber :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      2 * g < n ∧ n < 3 * g)
    (hwall :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      let d := secondaryDDefectPolynomial68 Ae Be De
      let h := secondaryResidualGap68 n d ee
      h = n - g) :
    False := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  let d := secondaryDDefectPolynomial68 Ae Be De
  let h := secondaryResidualGap68 n d ee
  change 2 * g < n ∧ n < 3 * g at hchamber
  change h = n - g at hwall
  have hcore := maximalExpandedIntegratedPolynomialLowerSystem_cubicCore68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have hdrop := maximalExpandedIntegratedPolynomialLowerSystem_degreeDrop68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have hsecondary :=
    maximalExpandedIntegratedPolynomialLowerSystem_secondaryRadius68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  have hn : 0 < n := by simpa only [n] using hcore.1
  have hg : 0 < g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.1
  have hA : Ae.natDegree ≤ 2 * n := by
    have hAe : Ae.natDegree = 2 * n := by
      simpa only [n, Ae, Be, Ce, De, Ee] using hdrop.1
    omega
  have hB : Be.natDegree ≤ 3 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.2.1
  have hc : ce.natDegree ≤ 4 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
      hsecondary.2.2.1
  have ha : Ae.coeff (2 * n) ≠ 0 := by
    simpa only [n, Ae] using hcore.2.2.2.2.2
  have hdrops :=
    maximalExpandedIntegratedPolynomialLowerSystem_secondaryResidualDegreeDrops68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hchamber.1)
  change d.natDegree < 5 * n - g ∧ ee.natDegree < 6 * n - g at hdrops
  have hdbase : d.natDegree < 5 * n := by omega
  have hebase : ee.natDegree < 6 * n := by omega
  have hbounds : d.natDegree ≤ 5 * n - h ∧
      ee.natDegree ≤ 6 * n - h := by
    simpa only [h] using secondaryResidualGap68_degreeBounds n d ee
      hdbase hebase
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec :
      Ee = (1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using
      cubicEDefectPolynomial68_eq_cubicCoordinates Ae Ce Ee
  have hDrec : De = (1 / 3 : k) • (Ae * Be) + d := by
    simpa only [d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
  obtain ⟨i4, hi4⟩ := hsys.firstFour
  obtain ⟨i3, hi3⟩ := hsys.firstThree
  have hi4e : firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i4 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_firstIntegralFourPolynomial68_of_eq
        l beta gamma delta epsilon zeta i4 A B C0 D E hi4
  have hi3e : firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i3 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_firstIntegralThreePolynomial68_of_eq
        l beta gamma delta epsilon zeta i3 A B C0 D E hi3
  have h2e : lowerRowTwoPolynomial68
      (integratedSPolynomial68 l alpha beta delta Ae Be Ce De)
      (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) Be Ce De Ee = 0 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_lowerRowTwoPolynomial68_of_system
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
  have h0e : lowerRowZeroPolynomial68
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) De Ee = C terminal * (60 * (X ^ 59 : k[X])) := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_lowerRowZeroPolynomial68_of_system
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
  have hnlarge : 10 ≤ n := by
    simpa only [n] using weightedRadius68_ge_ten A B C0 D E hn
  have h0target : (lowerRowZeroPolynomial68
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) De Ee).coeff (12 * n - 1) = 0 :=
    expand_lowerRowZeroPolynomial68_coeff_eq_zero_of_index_gt
      terminal _ _ _ _ _ h0e
      (residualSumLoadWallRowZeroIndex68_gt_fiftyNine n hnlarge)
  have hclass :=
    polynomialResidualSumLoadWallClassified68_of_integratedRows
      l alpha beta gamma delta epsilon zeta eta i4 i3
      Ae Be Ce ce De Ee d ee n g h hn hg hchamber.1 hchamber.2 hwall
      hA hB hc hbounds.1 hbounds.2 ha hCrec hDrec hErec hi4e hi3e
      h2e h0target
  have hl0 : l = 0 := hclass.1
  exact
    maximalExpandedIntegratedPolynomialLowerSystem_secondaryResidualLoadZero_impossible68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys hl0 (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hchamber.1)

#print axioms residualSumLoadWallFace68_classify
#print axioms residualSumLoadWallFace68_classify_of_support
#print axioms residualSumLoadWallFourScalar68_eq_numerator
#print axioms residualSumLoadWallTwoScalar68_eq_numerator
#print axioms residualSumLoadWallZeroScalar68_eq_numerator
#print axioms cubicLoadRowTwoPolynomial68_eq_lCore_add_rest
#print axioms cubicLoadRowZeroPolynomial68_eq_lCore_add_rest
#print axioms cubicLoadRowTwoLCorePolynomial68_coeff_loadWall
#print axioms cubicLoadRowZeroLCorePolynomial68_coeff_loadWall
#print axioms secondaryLoadInvariantFourPolynomial68_coeff_eightRadius
#print axioms cubicFirstIntegralFourPolynomial68_coeff_residualSumLoadWall
#print axioms cubicFirstIntegralThreePolynomial68_coeff_residualSumLoadWall
#print axioms cubicLoadRowTwoPolynomial68_coeff_residualSumLoadWall
#print axioms cubicLoadRowZeroPolynomial68_coeff_residualSumLoadWall
#print axioms secondaryResidualRowTwoPolynomial68_coeff_residualSumLoadWall
#print axioms secondaryResidualRowZeroPolynomial68_coeff_residualSumLoadWall
#print axioms polynomialResidualSumLoadWallFace68
#print axioms polynomialResidualSumLoadWallClassified68
#print axioms polynomialResidualSumLoadWallInvariants68
#print axioms integratedLowerRowTwoPolynomial68_coeff_residualSumLoadWall
#print axioms integratedLowerRowZeroPolynomial68_coeff_residualSumLoadWall
#print axioms polynomialResidualSumLoadWallClassified68_of_integratedRows
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_residualSumLoadWall_impossible68

end Max11DegreeRoutes
