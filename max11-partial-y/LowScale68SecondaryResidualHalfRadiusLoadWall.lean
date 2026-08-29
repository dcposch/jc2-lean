import LowScale68SecondaryResidualLoadZeroEndgame
import LowScale68SecondaryFirstLoadWallRemainder
import LowScale68SecondaryRelaxedCanonical

/-! # Mixed residual left face on the `(6,8)` wall `2h = n`

On `2g < n < 3g` with residual gap `2h = n`, I4/I3 remain the ordinary
middle face.  Row two at `10n-1` is the left `d e` face plus the Jacobian
core `l A^5`.  Row zero at `12n-1` is `-3 (A' d e)` plus the Jacobian
core `l A^6`.  The two scalars force `l = 0`; the tracked load-zero
endgame then closes the canonical branch.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## Mixed numerators

The displayed row-two / row-zero scalars are the literal leading
coefficients of homogeneous `d e` plus the Jacobian cores.  After I4 is
constant, `Q` may still meet degree `8n` and feed `A Q'` / `A A' Q`;
those contributions are proportional to `l a^4` and are absorbed into
the same `l`-elimination (they do not reopen the fibre). -/

/-- Homogeneous left-chamber row-two contribution after dropping `N`. -/
def residualHalfRadiusTwoHom68 (d e : k) : k :=
  (80 / 3 : k) * d * e

/-- Jacobian row-two core after dropping `N`. -/
def residualHalfRadiusTwoLoad68 (a l : k) : k :=
  (35 / 324 : k) * l * a ^ 5

/-- Mixed row-two scalar at index `10n-1`. -/
def residualHalfRadiusTwoScalar68 (N a d e l : k) : k :=
  N * (residualHalfRadiusTwoHom68 d e + residualHalfRadiusTwoLoad68 a l)

/-- Homogeneous row-zero contribution from `-3 (A' d e)` after dropping
`N a`. -/
def residualHalfRadiusZeroHom68 (d e : k) : k :=
  (-8 / 9 : k) * d * e

/-- Jacobian row-zero core after dropping `N a`. -/
def residualHalfRadiusZeroLoad68 (a l : k) : k :=
  (35 / 1944 : k) * l * a ^ 5

/-- Mixed row-zero scalar at index `12n-1`. -/
def residualHalfRadiusZeroScalar68 (N a d e l : k) : k :=
  N * a * (residualHalfRadiusZeroHom68 d e + residualHalfRadiusZeroLoad68 a l)

theorem residualHalfRadiusTwoScalar68_eq
    (N a d e l : k) :
    residualHalfRadiusTwoScalar68 N a d e l =
      N * ((80 / 3 : k) * d * e + (35 / 324 : k) * l * a ^ 5) := by
  simp only [residualHalfRadiusTwoScalar68, residualHalfRadiusTwoHom68,
    residualHalfRadiusTwoLoad68]

theorem residualHalfRadiusZeroScalar68_eq
    (N a d e l : k) :
    residualHalfRadiusZeroScalar68 N a d e l =
      N * a * ((-8 / 9 : k) * d * e + (35 / 1944 : k) * l * a ^ 5) := by
  simp only [residualHalfRadiusZeroScalar68, residualHalfRadiusZeroHom68,
    residualHalfRadiusZeroLoad68]

/-- `a • row-two - 6 • row-zero` kills the load and leaves `de`. -/
theorem residualHalfRadius_two_zero_kill_load
    (N a d e l : k) :
    a * residualHalfRadiusTwoScalar68 N a d e l -
        (6 : k) * residualHalfRadiusZeroScalar68 N a d e l =
      (32 : k) * N * a * d * e := by
  simp only [residualHalfRadiusTwoScalar68, residualHalfRadiusTwoHom68,
    residualHalfRadiusTwoLoad68, residualHalfRadiusZeroScalar68,
    residualHalfRadiusZeroHom68, residualHalfRadiusZeroLoad68]
  ring

/-- `30 • row-zero + a • row-two` kills `de` and leaves the load. -/
theorem residualHalfRadius_two_zero_kill_de
    (N a d e l : k) :
    (30 : k) * residualHalfRadiusZeroScalar68 N a d e l +
        a * residualHalfRadiusTwoScalar68 N a d e l =
      (35 / 54 : k) * N * l * a ^ 6 := by
  simp only [residualHalfRadiusTwoScalar68, residualHalfRadiusTwoHom68,
    residualHalfRadiusTwoLoad68, residualHalfRadiusZeroScalar68,
    residualHalfRadiusZeroHom68, residualHalfRadiusZeroLoad68]
  ring

theorem residualHalfRadius_two_zero_force_l
    (N a d e l : k) (hN : N ≠ 0) (ha : a ≠ 0)
    (htwo : residualHalfRadiusTwoScalar68 N a d e l = 0)
    (hzero : residualHalfRadiusZeroScalar68 N a d e l = 0) :
    l = 0 := by
  have hcomb := residualHalfRadius_two_zero_kill_de N a d e l
  rw [htwo, hzero, mul_zero, mul_zero, add_zero] at hcomb
  have h35 : (35 / 54 : k) ≠ 0 := by norm_num
  have hpre : (35 / 54 : k) * N * a ^ 6 ≠ 0 :=
    mul_ne_zero (mul_ne_zero h35 hN) (pow_ne_zero 6 ha)
  have : (35 / 54 : k) * N * a ^ 6 * l = 0 := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hcomb.symm
  exact (mul_eq_zero.mp this).resolve_left hpre

/-! ## Wall index arithmetic -/

theorem residualHalfRadiusLoadWall_gap_lt
    (n g h : ℕ) (hsmall : 2 * g < n) (hwall : 2 * h = n) : g < h := by
  omega

theorem residualHalfRadiusLoadWall_lt_double
    (n g h : ℕ) (hg : 0 < g) (hlarge : n ≤ 3 * g) (hwall : 2 * h = n) :
    h < 2 * g := by
  omega

theorem residualHalfRadiusLoadWall_win
    (n g h : ℕ) (hsmall : 2 * g < n) (hwall : 2 * h = n) : g + h < n := by
  omega

theorem residualHalfRadiusLoadWall_twoIndex
    (n h : ℕ) (hwall : 2 * h = n) : 11 * n - 2 * h - 1 = 10 * n - 1 := by
  omega

theorem residualHalfRadiusLoadWall_zeroIndex
    (n h : ℕ) (hwall : 2 * h = n) : 13 * n - 2 * h - 1 = 12 * n - 1 := by
  omega

theorem residualHalfRadiusLoadWall_deIndex
    (n h : ℕ) (hwall : 2 * h = n) : 11 * n - 2 * h = 10 * n := by
  omega

theorem residualHalfRadiusLoadWall_gap_cast
    (n h : ℕ) (hwall : 2 * h = n) :
    (h : k) = (n : k) / 2 := by
  apply eq_div_of_mul_eq (by norm_num : (2 : k) ≠ 0)
  have h2 : (2 : k) * (h : k) = (n : k) := by exact_mod_cast hwall
  rw [mul_comm]
  exact h2

/-! ## I4 / I3 on the load-free middle face -/

set_option maxHeartbeats 2000000 in
theorem cubicFirstIntegralFourPolynomial68_coeff_residualHalfRadius
    (l beta gamma delta epsilon zeta : k) (A B c d e : k[X])
    (n g h : ℕ) (hg : 0 < g) (hsmall : 2 * g < n) (hlarge : n ≤ 3 * g)
    (hwall : 2 * h = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (cubicFirstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff (9 * n - g - h) =
      (8 / 3 : k) *
        (B.coeff (3 * n - g) * e.coeff (6 * n - h) +
          c.coeff (4 * n - g) * d.coeff (5 * n - h)) := by
  have hgh : g < h := residualHalfRadiusLoadWall_gap_lt n g h hsmall hwall
  have hwin : g + h < n := residualHalfRadiusLoadWall_win n g h hsmall hwall
  exact cubicFirstIntegralFourPolynomial68_coeff_residualMiddle_of_loadWindow
    l beta gamma delta epsilon zeta A B c d e n g h hg hgh hlarge hwin
    hA hB hc hd he

set_option maxHeartbeats 2000000 in
theorem cubicFirstIntegralThreePolynomial68_coeff_residualHalfRadius
    (l beta gamma delta epsilon zeta : k) (A B c d e : k[X])
    (n g h : ℕ) (hg : 0 < g) (hsmall : 2 * g < n) (hlarge : n ≤ 3 * g)
    (hwall : 2 * h = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (cubicFirstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff (10 * n - g - h) =
      (8 / 9 : k) *
        (-(A.coeff (2 * n) * B.coeff (3 * n - g) *
            d.coeff (5 * n - h)) +
          3 * c.coeff (4 * n - g) * e.coeff (6 * n - h)) := by
  have hgh : g < h := residualHalfRadiusLoadWall_gap_lt n g h hsmall hwall
  have hwin : g + h < n := residualHalfRadiusLoadWall_win n g h hsmall hwall
  exact cubicFirstIntegralThreePolynomial68_coeff_residualMiddle_of_loadWindow
    l beta gamma delta epsilon zeta A B c d e n g h hg hgh hlarge hwin
    hA hB hc hd he

/-! ## Row-two / row-zero Jacobian cores on the wall -/

private theorem residualHalfRadius_natDegree_smul_lt68
    (r : k) {p : k[X]} {m : ℕ} (hp : p.natDegree < m) :
    (r • p).natDegree < m :=
  (natDegree_smul_le r p).trans_lt hp

private theorem residualHalfRadius_natDegree_add_lt68
    {p q : k[X]} {m : ℕ}
    (hp : p.natDegree < m) (hq : q.natDegree < m) :
    (p + q).natDegree < m :=
  (natDegree_add_le p q).trans_lt (max_lt hp hq)

private theorem residualHalfRadius_natDegree_sub_lt68
    {p q : k[X]} {m : ℕ}
    (hp : p.natDegree < m) (hq : q.natDegree < m) :
    (p - q).natDegree < m :=
  (natDegree_sub_le p q).trans_lt (max_lt hp hq)

private theorem residualHalfRadius_mul_derivative_lt
    (p q : k[X]) (u v bound : ℕ) (hv : 0 < v)
    (hp : p.natDegree ≤ u) (hq : q.natDegree ≤ v)
    (huv : u + v - 1 < bound) :
    (p * derivative q).natDegree < bound := by
  have hd : (derivative q).natDegree ≤ v - 1 :=
    (natDegree_derivative_le q).trans (Nat.sub_le_sub_right hq 1)
  have hsum : p.natDegree + (derivative q).natDegree ≤ u + (v - 1) :=
    Nat.add_le_add hp hd
  have hidx : u + (v - 1) = u + v - 1 := by omega
  exact (natDegree_mul_le.trans (hidx ▸ hsum)).trans_lt huv

set_option maxHeartbeats 2000000 in
theorem cubicLoadSRestPolynomial68_degree_le_halfRadius
    (l alpha beta delta : k) (A B c : k[X]) (n g : ℕ)
    (hg : 0 < g) (hsmall : 2 * g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g) :
    (cubicLoadSRestPolynomial68 l alpha beta delta A B c).natDegree ≤
      4 * n - g := by
  simp only [cubicLoadSRestPolynomial68]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
theorem cubicLoadURestPolynomial68_degree_le_halfRadius
    (l alpha beta gamma delta zeta : k) (A B c D e : k[X])
    (n g h : ℕ) (hg : 0 < g) (hsmall : 2 * g < n) (hwall : 2 * h = n)
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
theorem cubicERestPolynomial68_degree_le_halfRadius
    (A c e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hsmall : 2 * g < n) (hwall : 2 * h = n)
    (hA : A.natDegree ≤ 2 * n)
    (hc : c.natDegree ≤ 4 * n - g)
    (he : e.natDegree ≤ 6 * n - h) :
    (cubicERestPolynomial68 A c e).natDegree ≤ 6 * n - g := by
  simp only [cubicERestPolynomial68]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem cubicLoadRowTwoRestPolynomial68_degree_lt_halfRadius
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hsmall : 2 * g < n) (hwall : 2 * h = n)
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
  have he' : e.natDegree ≤ 6 * n - g := by omega
  have hloads := cubicLoadPolynomials68_degreeBounds
    l alpha beta gamma delta epsilon zeta eta A B c D e n g
    hn hg hsmall hA hB hc hD he'
  have hUlc : Ulc.natDegree ≤ 6 * n :=
    cubicLoadUCorePolynomial68_degree_le l A n hA
  have hUlr : Ulr.natDegree ≤ 6 * n - g :=
    cubicLoadURestPolynomial68_degree_le_halfRadius
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
    cubicLoadSRestPolynomial68_degree_le_halfRadius
      l alpha beta delta A B c n g hg hsmall hA hB hc
  have hEc : Ec.natDegree ≤ 6 * n := by
    simp only [Ec]
    compute_degree
    omega
  have hEr : Er.natDegree ≤ 6 * n - g :=
    cubicERestPolynomial68_degree_le_halfRadius A c e n g h
      hg hsmall hwall hA hc he
  have hE : E.natDegree ≤ 6 * n :=
    (natDegree_add_le Ec Er).trans (max_le hEc (hEr.trans (by omega)))
  have hTl : Tl.natDegree ≤ 5 * n - g := by
    simpa only [Tl] using hloads.2.1
  have hVl : Vl.natDegree ≤ 7 * n - g := by
    simpa only [Vl] using hloads.2.2.2
  have h1 : (Ulc * derivative c).natDegree < 10 * n - 1 :=
    residualHalfRadius_mul_derivative_lt Ulc c (6 * n) (4 * n - g)
      (10 * n - 1) (by omega) hUlc hc (by omega)
  have h2 : (Ulr * derivative C0).natDegree < 10 * n - 1 :=
    residualHalfRadius_mul_derivative_lt Ulr C0 (6 * n - g) (4 * n)
      (10 * n - 1) (by omega) hUlr hC0 (by omega)
  have h3 : (Tl * derivative D).natDegree < 10 * n - 1 :=
    residualHalfRadius_mul_derivative_lt Tl D (5 * n - g) (5 * n - g)
      (10 * n - 1) (by omega) hTl hD (by omega)
  have h4 : (Slc * derivative Er).natDegree < 10 * n - 1 :=
    residualHalfRadius_mul_derivative_lt Slc Er (4 * n) (6 * n - g)
      (10 * n - 1) (by omega) hSlc hEr (by omega)
  have h5 : (Slr * derivative E).natDegree < 10 * n - 1 :=
    residualHalfRadius_mul_derivative_lt Slr E (4 * n - g) (6 * n)
      (10 * n - 1) (by omega) hSlr hE (by omega)
  have h6 : (B * derivative Vl).natDegree < 10 * n - 1 :=
    residualHalfRadius_mul_derivative_lt B Vl (3 * n - g) (7 * n - g)
      (10 * n - 1) (by omega) hB hVl (by omega)
  have h7 : (C0c * derivative Ulr).natDegree < 10 * n - 1 :=
    residualHalfRadius_mul_derivative_lt C0c Ulr (4 * n) (6 * n - g)
      (10 * n - 1) (by omega) hC0c hUlr (by omega)
  have h8 : (c * derivative Ul).natDegree < 10 * n - 1 :=
    residualHalfRadius_mul_derivative_lt c Ul (4 * n - g) (6 * n)
      (10 * n - 1) (by omega) hc hUl (by omega)
  have h9 : (D * derivative Tl).natDegree < 10 * n - 1 :=
    residualHalfRadius_mul_derivative_lt D Tl (5 * n - g) (5 * n - g)
      (10 * n - 1) (by omega) hD hTl (by omega)
  have h3s := residualHalfRadius_natDegree_smul_lt68 (2 : k) h3
  have h4s := residualHalfRadius_natDegree_smul_lt68 (3 : k) h4
  have h5s := residualHalfRadius_natDegree_smul_lt68 (3 : k) h5
  have h6s := residualHalfRadius_natDegree_smul_lt68 (3 : k) h6
  have h7s := residualHalfRadius_natDegree_smul_lt68 (2 : k) h7
  have h8s := residualHalfRadius_natDegree_smul_lt68 (2 : k) h8
  have s1 := residualHalfRadius_natDegree_add_lt68 h1 h2
  have s2 := residualHalfRadius_natDegree_add_lt68 s1 h3s
  have s3 := residualHalfRadius_natDegree_add_lt68 s2 h4s
  have s4 := residualHalfRadius_natDegree_add_lt68 s3 h5s
  have s5 := residualHalfRadius_natDegree_sub_lt68 s4 h6s
  have s6 := residualHalfRadius_natDegree_sub_lt68 s5 h7s
  have s7 := residualHalfRadius_natDegree_sub_lt68 s6 h8s
  have s8 := residualHalfRadius_natDegree_sub_lt68 s7 h9
  rw [cubicLoadRowTwoRestPolynomial68_eq_splitPieces]
  exact s8

set_option maxHeartbeats 2000000 in
theorem cubicLoadRowTwoPolynomial68_coeff_halfRadius
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hsmall : 2 * g < n) (hwall : 2 * h = n)
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
      (cubicLoadRowTwoRestPolynomial68_degree_lt_halfRadius
        l alpha beta gamma delta epsilon zeta eta A B c D e n g h
        hn hg hsmall hwall hA hB hc hD he), add_zero]
  exact cubicLoadRowTwoLCorePolynomial68_coeff_loadWall l A n hn hA

set_option maxHeartbeats 4000000 in
theorem cubicLoadRowZeroRestPolynomial68_degree_lt_halfRadius
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hsmall : 2 * g < n) (hwall : 2 * h = n)
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
  have he' : e.natDegree ≤ 6 * n - g := by omega
  have hloads := cubicLoadPolynomials68_degreeBounds
    l alpha beta gamma delta epsilon zeta eta A B c D e n g
    hn hg hsmall hA hB hc hD he'
  have hUlc : Ulc.natDegree ≤ 6 * n :=
    cubicLoadUCorePolynomial68_degree_le l A n hA
  have hUlr : Ulr.natDegree ≤ 6 * n - g :=
    cubicLoadURestPolynomial68_degree_le_halfRadius
      l alpha beta gamma delta zeta A B c D e n g h
      hg hsmall hwall hA hB hc hD he
  have hEr : Er.natDegree ≤ 6 * n - g :=
    cubicERestPolynomial68_degree_le_halfRadius A c e n g h
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
    residualHalfRadius_mul_derivative_lt Ulc Er (6 * n) (6 * n - g)
      (12 * n - 1) (by omega) hUlc hEr (by omega)
  have h2 : (Ulr * derivative E).natDegree < 12 * n - 1 :=
    residualHalfRadius_mul_derivative_lt Ulr E (6 * n - g) (6 * n)
      (12 * n - 1) (by omega) hUlr hE (by omega)
  have h3 : (D * derivative Vl).natDegree < 12 * n - 1 :=
    residualHalfRadius_mul_derivative_lt D Vl (5 * n - g) (7 * n - g)
      (12 * n - 1) (by omega) hD hVl (by omega)
  change (Ulc * derivative Er + Ulr * derivative E -
      D * derivative Vl).natDegree < _
  exact residualHalfRadius_natDegree_sub_lt68
    (residualHalfRadius_natDegree_add_lt68 h1 h2) h3

set_option maxHeartbeats 2000000 in
theorem cubicLoadRowZeroPolynomial68_coeff_halfRadius
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hsmall : 2 * g < n) (hwall : 2 * h = n)
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
      (cubicLoadRowZeroRestPolynomial68_degree_lt_halfRadius
        l alpha beta gamma delta epsilon zeta eta A B c D e n g h
        hn hg hsmall hwall hA hB hc hD he), add_zero]
  exact cubicLoadRowZeroLCorePolynomial68_coeff_loadWall l A n hn hA

/-! ## Homogeneous left `d e` faces, after `Q.natDegree < 9n-3g`

The next `Q` face after the I4 middle cancellation is `B^3` at `9n-3g`.
On `n < 3g` this puts `A Q'` strictly below `10n-1` and `A A' Q` strictly
below `12n-1`, so the displayed coefficients are exactly the user's
row-two / row-zero pair. -/

set_option maxHeartbeats 2000000 in
theorem residualIncidenceQ68_eq_defect (B c d e : k[X]) :
    residualIncidenceQ68 B c d e =
      secondaryResidualIncidenceDefectPolynomial68 B c d e := rfl

set_option maxHeartbeats 6000000 in
theorem secondaryResidualRowTwoPolynomial68_coeff_halfRadiusHom
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g)
    (hsmall : 2 * g < n) (hstrict : n < 3 * g) (hwall : 2 * h = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualIncidenceQ68 B c d e).natDegree < 9 * n - 3 * g) :
    (secondaryResidualRowTwoPolynomial68 A B c d e).coeff (10 * n - 1) =
      (80 / 3 : k) * (n : k) *
        d.coeff (5 * n - h) * e.coeff (6 * n - h) := by
  have hgh : g < h := residualHalfRadiusLoadWall_gap_lt n g h hsmall hwall
  have hlarge : n ≤ 3 * g := Nat.le_of_lt hstrict
  have hh : h < 2 * g :=
    residualHalfRadiusLoadWall_lt_double n g h hg hlarge hwall
  have hidx : 11 * n - 2 * h - 1 = 10 * n - 1 :=
    residualHalfRadiusLoadWall_twoIndex n h hwall
  have hleft : 2 * h < 3 * g := by omega
  have hcoeff := residualRowTwo_coeff_leftChamber68_of_twoGap
    A B c d e n g h hg hgh hh hsmall hleft hA hB hc hd he hQ
  rw [hidx] at hcoeff
  have hcast : (((11 * n - 2 * h : ℕ) : k)) = (10 : k) * (n : k) := by
    have hi : 11 * n - 2 * h = 10 * n :=
      residualHalfRadiusLoadWall_deIndex n h hwall
    rw [hi]
    push_cast
    rfl
  rw [hcoeff, hcast]
  ring

theorem residualRowZero_Ae_split68 (A B c d e : k[X]) :
    A * derivative A * B * e + A * derivative A * c * d =
      A * derivative A * residualIncidenceQ68 B c d e +
        (1 / 9 : k) • (A * derivative A * B ^ 3) := by
  simp only [residualIncidenceQ68, Polynomial.smul_eq_C_mul]
  ring

set_option maxHeartbeats 8000000 in
theorem secondaryResidualRowZeroPolynomial68_coeff_halfRadiusHom
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g)
    (hsmall : 2 * g < n) (hstrict : n < 3 * g) (hwall : 2 * h = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualIncidenceQ68 B c d e).natDegree < 9 * n - 3 * g) :
    (secondaryResidualRowZeroPolynomial68 A B c d e).coeff (12 * n - 1) =
      (-8 / 9 : k) * (n : k) * A.coeff (2 * n) *
        d.coeff (5 * n - h) * e.coeff (6 * n - h) := by
  let Q := residualIncidenceQ68 B c d e
  have hdA : (derivative A).natDegree ≤ 2 * n - 1 :=
    (natDegree_derivative_le A).trans (by omega)
  have hAAd : (A * derivative A).natDegree ≤ 4 * n - 1 :=
    natDegree_mul_le.trans (by omega)
  have hQ' : Q.natDegree ≤ 9 * n - 3 * g - 1 :=
    Nat.le_sub_one_of_lt hQ
  have hAAQ : (A * derivative A * Q).natDegree < 12 * n - 1 := by
    have hmul := natDegree_mul_le_of_le hAAd hQ'
    have : 4 * n - 1 + (9 * n - 3 * g - 1) < 12 * n - 1 := by omega
    exact hmul.trans_lt this
  have hAAB3 : (A * derivative A * B ^ 3).natDegree < 12 * n - 1 := by
    have hB3 : (B ^ 3).natDegree ≤ 9 * n - 3 * g := by
      compute_degree
      omega
    have hmul := natDegree_mul_le_of_le hAAd hB3
    have : 4 * n - 1 + (9 * n - 3 * g) < 12 * n - 1 := by omega
    exact hmul.trans_lt this
  have hsplit := residualRowZero_Ae_split68 A B c d e
  have hAe : (A * derivative A * B * e +
      A * derivative A * c * d).natDegree < 12 * n - 1 := by
    have hsum := hsplit
    rw [hsum]
    exact residualHalfRadius_natDegree_add_lt68 hAAQ
      (residualHalfRadius_natDegree_smul_lt68 (1 / 9 : k) hAAB3)
  have hlow1 : (A * B ^ 2 * derivative d).natDegree < 12 * n - 1 := by
    compute_degree
    omega
  have hlow2 : (A * B * derivative B * d).natDegree < 12 * n - 1 := by
    compute_degree
    omega
  have hlow3 : (derivative A * B * c ^ 2).natDegree < 12 * n - 1 := by
    compute_degree
    omega
  have hlow4 : (B * c * derivative e).natDegree < 12 * n - 1 := by
    compute_degree
    omega
  have hlow5 : (B * d * derivative d).natDegree < 12 * n - 1 := by
    compute_degree
    omega
  have hlow6 : (derivative B * d ^ 2).natDegree < 12 * n - 1 := by
    compute_degree
    omega
  have hlow7 : (c * derivative c * d).natDegree < 12 * n - 1 := by
    compute_degree
    omega
  have hA' : (derivative A).coeff (2 * n - 1) =
      A.coeff (2 * n) * ((2 * n : ℕ) : k) :=
    coeff_derivative_at_bound68 A (2 * n) (by omega)
  have hprod : (derivative A * d * e).coeff (12 * n - 1) =
      A.coeff (2 * n) * ((2 * n : ℕ) : k) *
        d.coeff (5 * n - h) * e.coeff (6 * n - h) := by
    have hAd := coeff_mul_at_bounds68 (derivative A) d (2 * n - 1) (5 * n - h)
      hdA hd
    have hmul2 := coeff_mul_at_bounds68 (derivative A * d) e
      ((2 * n - 1) + (5 * n - h)) (6 * n - h)
      (natDegree_mul_le.trans (Nat.add_le_add hdA hd)) he
    have hi : (2 * n - 1) + (5 * n - h) + (6 * n - h) = 12 * n - 1 := by
      omega
    rw [hi, hAd, hA'] at hmul2
    simpa [mul_assoc] using hmul2
  have h0Ae : (A * derivative A * B * e).coeff (12 * n - 1) +
      (A * derivative A * c * d).coeff (12 * n - 1) = 0 := by
    have hsum := coeff_add (A * derivative A * B * e)
      (A * derivative A * c * d) (12 * n - 1)
    rw [← hsum, coeff_eq_zero_of_natDegree_lt hAe]
  have hcast2 : (((2 * n : ℕ) : k)) = (2 : k) * (n : k) := by
    push_cast
    rfl
  simp only [secondaryResidualRowZeroPolynomial68, coeff_smul, coeff_add,
    coeff_sub, smul_eq_mul,
    coeff_eq_zero_of_natDegree_lt hlow1,
    coeff_eq_zero_of_natDegree_lt hlow2,
    coeff_eq_zero_of_natDegree_lt hlow3,
    coeff_eq_zero_of_natDegree_lt hlow4,
    coeff_eq_zero_of_natDegree_lt hlow5,
    coeff_eq_zero_of_natDegree_lt hlow6,
    coeff_eq_zero_of_natDegree_lt hlow7]
  trans (4 / 27 : k) * ((-3 : k) * (derivative A * d * e).coeff (12 * n - 1))
  · congr 1
    linear_combination -h0Ae
  · rw [hprod, hcast2]
    ring

/-! ## Mixed row-two / row-zero coefficients and `l = 0` -/

set_option maxHeartbeats 2000000 in
theorem integratedLowerRowTwoPolynomial68_coeff_halfRadius
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g)
    (hsmall : 2 * g < n) (hstrict : n < 3 * g) (hwall : 2 * h = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualIncidenceQ68 B c d e).natDegree < 9 * n - 3 * g)
    (hD : ((1 / 3 : k) • (A * B) + d).natDegree ≤ 5 * n - g) :
    (secondaryResidualRowTwoPolynomial68 A B c d e +
      cubicLoadRowTwoPolynomial68 l alpha beta gamma delta epsilon zeta eta
        A B c ((1 / 3 : k) • (A * B) + d) e).coeff (10 * n - 1) =
      residualHalfRadiusTwoScalar68 (n : k) (A.coeff (2 * n))
        (d.coeff (5 * n - h)) (e.coeff (6 * n - h)) l := by
  rw [coeff_add,
    secondaryResidualRowTwoPolynomial68_coeff_halfRadiusHom
      A B c d e n g h hn hg hsmall hstrict hwall hA hB hc hd he hQ,
    cubicLoadRowTwoPolynomial68_coeff_halfRadius
      l alpha beta gamma delta epsilon zeta eta A B c
      ((1 / 3 : k) • (A * B) + d) e n g h
      hn hg hsmall hwall hA hB hc hD he]
  simp only [residualHalfRadiusTwoScalar68, residualHalfRadiusTwoHom68,
    residualHalfRadiusTwoLoad68]
  ring

set_option maxHeartbeats 2000000 in
theorem integratedLowerRowZeroPolynomial68_coeff_halfRadius
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g)
    (hsmall : 2 * g < n) (hstrict : n < 3 * g) (hwall : 2 * h = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualIncidenceQ68 B c d e).natDegree < 9 * n - 3 * g)
    (hD : ((1 / 3 : k) • (A * B) + d).natDegree ≤ 5 * n - g) :
    (secondaryResidualRowZeroPolynomial68 A B c d e +
      cubicLoadRowZeroPolynomial68 l alpha beta gamma delta epsilon zeta eta
        A B c ((1 / 3 : k) • (A * B) + d) e).coeff (12 * n - 1) =
      residualHalfRadiusZeroScalar68 (n : k) (A.coeff (2 * n))
        (d.coeff (5 * n - h)) (e.coeff (6 * n - h)) l := by
  rw [coeff_add,
    secondaryResidualRowZeroPolynomial68_coeff_halfRadiusHom
      A B c d e n g h hn hg hsmall hstrict hwall hA hB hc hd he hQ,
    cubicLoadRowZeroPolynomial68_coeff_halfRadius
      l alpha beta gamma delta epsilon zeta eta A B c
      ((1 / 3 : k) • (A * B) + d) e n g h
      hn hg hsmall hwall hA hB hc hD he]
  simp only [residualHalfRadiusZeroScalar68, residualHalfRadiusZeroHom68,
    residualHalfRadiusZeroLoad68]
  ring

set_option maxHeartbeats 2000000 in
theorem polynomialSecondaryResidualHalfRadius_force_l
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g)
    (hsmall : 2 * g < n) (hstrict : n < 3 * g) (hwall : 2 * h = n)
    (hA : A.natDegree ≤ 2 * n) (ha : A.coeff (2 * n) ≠ 0)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualIncidenceQ68 B c d e).natDegree < 9 * n - 3 * g)
    (hrowTwo : secondaryResidualRowTwoPolynomial68 A B c d e +
      cubicLoadRowTwoPolynomial68 l alpha beta gamma delta epsilon zeta eta
        A B c ((1 / 3 : k) • (A * B) + d) e = 0)
    (hrowZero : secondaryResidualRowZeroPolynomial68 A B c d e +
      cubicLoadRowZeroPolynomial68 l alpha beta gamma delta epsilon zeta eta
        A B c ((1 / 3 : k) • (A * B) + d) e = 0) :
    l = 0 := by
  have hD : ((1 / 3 : k) • (A * B) + d).natDegree ≤ 5 * n - g := by
    compute_degree
    omega
  have htwo := congrArg (fun p : k[X] => p.coeff (10 * n - 1)) hrowTwo
  have hzero := congrArg (fun p : k[X] => p.coeff (12 * n - 1)) hrowZero
  rw [coeff_zero,
    integratedLowerRowTwoPolynomial68_coeff_halfRadius
      l alpha beta gamma delta epsilon zeta eta A B c d e n g h
      hn hg hsmall hstrict hwall hA hB hc hd he hQ hD] at htwo
  rw [coeff_zero,
    integratedLowerRowZeroPolynomial68_coeff_halfRadius
      l alpha beta gamma delta epsilon zeta eta A B c d e n g h
      hn hg hsmall hstrict hwall hA hB hc hd he hQ hD] at hzero
  exact residualHalfRadius_two_zero_force_l (n : k) (A.coeff (2 * n))
    (d.coeff (5 * n - h)) (e.coeff (6 * n - h)) l
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)) ha htwo hzero

/-! ## Canonical expanded wrapper -/

theorem residualHalfRadiusLoadWallRowZeroIndex68_gt_fiftyNine
    (n h : ℕ) (hn : 10 ≤ n) (hwall : 2 * h = n) :
    59 < 12 * n - 1 := by
  omega

set_option maxHeartbeats 8000000 in
/-- On the canonical expanded system, the mixed residual half-radius wall
`2h = n` inside `2g < n < 3g` forces `l = 0`.  The tracked load-zero
endgame then closes the branch.  No residual-support premise is required. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_residualHalfRadiusLoadWall_impossible68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hsmall :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      2 * g < n)
    (hstrict :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      n < 3 * g)
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
      2 * h = n)
    (hmiddle :
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
      d.natDegree ≤ 5 * n - h ∧ ee.natDegree ≤ 6 * n - h)
    (hQ :
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
      (residualIncidenceQ68 Be ce d ee).natDegree < 9 * n - 3 * g) :
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
  change 2 * g < n at hsmall
  change n < 3 * g at hstrict
  change 2 * h = n at hwall
  change d.natDegree ≤ 5 * n - h ∧
    ee.natDegree ≤ 6 * n - h at hmiddle
  change (residualIncidenceQ68 Be ce d ee).natDegree < 9 * n - 3 * g at hQ
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
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec :
      Ee = (1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using
      cubicEDefectPolynomial68_eq_cubicCoordinates Ae Ce Ee
  have hDrec : De = (1 / 3 : k) • (Ae * Be) + d := by
    simpa only [d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
  have hDbound : ((1 / 3 : k) • (Ae * Be) + d).natDegree ≤ 5 * n - g := by
    compute_degree
    omega
  have h2e : lowerRowTwoPolynomial68
      (integratedSPolynomial68 l alpha beta delta Ae Be Ce De)
      (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) Be Ce De Ee = 0 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_lowerRowTwoPolynomial68_of_system
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
  have hrowTwo := polynomialSecondaryResidualRowTwo68
    l alpha beta gamma delta epsilon zeta eta Ae Be ce d ee (by
      rw [hCrec, hDrec, hErec] at h2e
      exact h2e)
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
      (residualHalfRadiusLoadWallRowZeroIndex68_gt_fiftyNine n h hnlarge hwall)
  have hcoords := integratedPolynomial68_cubicCoordinates
    l alpha beta gamma delta epsilon zeta eta Ae Be ce De ee
  have hsum :
      lowerRowZeroPolynomial68
        (integratedUPolynomial68 l alpha beta gamma delta zeta
          Ae Be Ce De Ee)
        (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
          Ae Be Ce De Ee) De Ee =
        secondaryResidualRowZeroPolynomial68 Ae Be ce d ee +
          cubicLoadRowZeroPolynomial68 l alpha beta gamma delta epsilon
            zeta eta Ae Be ce De ee := by
    rw [hCrec, hErec, hcoords.u_eq, hcoords.v_eq,
      cubicRowZeroPolynomial68_split,
      show cubicHomogeneousRowZeroPolynomial68 Ae Be ce De ee =
          secondaryResidualRowZeroPolynomial68 Ae Be ce d ee by
        simpa [hDrec] using
          cubicHomogeneousRowZeroPolynomial68_residualCoordinates
            Ae Be ce d ee]
  have hzeroCoeff : (secondaryResidualRowZeroPolynomial68 Ae Be ce d ee +
      cubicLoadRowZeroPolynomial68 l alpha beta gamma delta epsilon zeta eta
        Ae Be ce ((1 / 3 : k) • (Ae * Be) + d) ee).coeff (12 * n - 1) = 0 := by
    have hzEq := congrArg (fun p : k[X] => p.coeff (12 * n - 1)) hsum
    simpa [hDrec] using hzEq.symm.trans h0target
  have htwoCoeff := congrArg (fun p : k[X] => p.coeff (10 * n - 1)) hrowTwo
  have hl0 := residualHalfRadius_two_zero_force_l (n : k)
    (Ae.coeff (2 * n)) (d.coeff (5 * n - h)) (ee.coeff (6 * n - h)) l
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)) ha
    (by
      rw [← integratedLowerRowTwoPolynomial68_coeff_halfRadius
        l alpha beta gamma delta epsilon zeta eta Ae Be ce d ee n g h
        hn hg hsmall hstrict hwall hA hB hc hmiddle.1 hmiddle.2 hQ hDbound]
      simpa using htwoCoeff)
    (by
      rw [← integratedLowerRowZeroPolynomial68_coeff_halfRadius
        l alpha beta gamma delta epsilon zeta eta Ae Be ce d ee n g h
        hn hg hsmall hstrict hwall hA hB hc hmiddle.1 hmiddle.2 hQ hDbound]
      exact hzeroCoeff)
  exact
    maximalExpandedIntegratedPolynomialLowerSystem_secondaryResidualLoadZero_impossible68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys hl0 (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsmall)

#print axioms residualHalfRadius_two_zero_force_l
#print axioms cubicFirstIntegralFourPolynomial68_coeff_residualHalfRadius
#print axioms cubicLoadRowTwoPolynomial68_coeff_halfRadius
#print axioms cubicLoadRowZeroPolynomial68_coeff_halfRadius
#print axioms secondaryResidualRowTwoPolynomial68_coeff_halfRadiusHom
#print axioms secondaryResidualRowZeroPolynomial68_coeff_halfRadiusHom
#print axioms integratedLowerRowTwoPolynomial68_coeff_halfRadius
#print axioms integratedLowerRowZeroPolynomial68_coeff_halfRadius
#print axioms polynomialSecondaryResidualHalfRadius_force_l
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_residualHalfRadiusLoadWall_impossible68

end Max11DegreeRoutes
