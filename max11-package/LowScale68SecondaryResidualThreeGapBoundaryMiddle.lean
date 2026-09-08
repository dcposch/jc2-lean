import LowScale68SecondaryResidualRowTwoLoadDominance

/-! # Mixed residual cubic load chamber `n = 3g`, `n < 2h`, `h < 2g`

On the remaining open residual interval of the wall `n = 3g` after the
tracked double-load face `h = 2g`, I4/I3 remain the ordinary middle
face, while the cubic `B,c` core collides with the Jacobian index
`10n-1`.  After I4 is constant, `Q.natDegree ≤ 8n` with
`Q.coeff(8n) = -35/4608 l a^4`, so row two and row zero meet both the
cubic cores and the `Q`-feeds.  The two mixed scalars force `l = 0`;
the tracked load-zero endgame then closes the canonical `2g < n`
branch.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Chamber arithmetic -/

theorem residualThreeGapBoundaryMiddle_twoGap
    (n g : ℕ) (hg : 0 < g) (hwall : 3 * g = n) : 2 * g < n := by
  omega

theorem residualThreeGapBoundaryMiddle_gap_lt
    (n g h : ℕ) (hg : 0 < g) (hwall : 3 * g = n) (hleft : n < 2 * h) :
    g < h := by
  omega

theorem residualThreeGapBoundaryMiddle_win
    (n g h : ℕ) (hwall : 3 * g = n) (hh : h < 2 * g) : g + h < n := by
  omega

theorem residualThreeGapBoundaryMiddle_large
    (n g : ℕ) (hwall : 3 * g = n) : n ≤ 3 * g := by
  omega

theorem residualThreeGapBoundaryMiddle_right
    (n g h : ℕ) (hwall : 3 * g = n) (hleft : n < 2 * h) :
    3 * g < 2 * h := by
  omega

theorem residualThreeGapBoundaryMiddle_twoIndex
    (n g : ℕ) (hwall : 3 * g = n) :
    11 * n - 3 * g - 1 = 10 * n - 1 := by
  omega

theorem residualThreeGapBoundaryMiddle_zeroIndex
    (n g : ℕ) (hwall : 3 * g = n) :
    13 * n - 3 * g - 1 = 12 * n - 1 := by
  omega

theorem residualThreeGapBoundaryMiddle_cubicIndex
    (n g : ℕ) (hwall : 3 * g = n) : 11 * n - 3 * g = 10 * n := by
  omega

theorem residualThreeGapBoundaryMiddle_B3Index
    (n g : ℕ) (hwall : 3 * g = n) : 9 * n - 3 * g = 8 * n := by
  omega

theorem residualThreeGapBoundaryMiddle_eBound
    (n g h : ℕ) {e : k[X]} (hgh : g < h)
    (he : e.natDegree ≤ 6 * n - h) :
    e.natDegree ≤ 6 * n - g :=
  he.trans (by omega)

theorem residualThreeGapBoundaryMiddle_dBound
    (n g h : ℕ) {d : k[X]} (hgh : g < h)
    (hd : d.natDegree ≤ 5 * n - h) :
    d.natDegree ≤ 5 * n - g :=
  hd.trans (by omega)

theorem residualThreeGapBoundaryMiddle_gap_cast
    (n g : ℕ) (hwall : 3 * g = n) :
    (g : k) = (n : k) / 3 := by
  apply eq_div_of_mul_eq (by norm_num : (3 : k) ≠ 0)
  have h3 : (3 : k) * (g : k) = (n : k) := by
    exact_mod_cast hwall
  rw [mul_comm]
  exact h3

theorem residualThreeGapBoundaryMiddle_cast3
    (n g : ℕ) (hwall : 3 * g = n) :
    ((3 * n - g : ℕ) : k) = (8 / 3 : k) * (n : k) := by
  rw [Nat.cast_sub (by omega : g ≤ 3 * n)]
  push_cast
  rw [residualThreeGapBoundaryMiddle_gap_cast n g hwall]
  ring

theorem residualThreeGapBoundaryMiddle_cast11
    (n g : ℕ) (hwall : 3 * g = n) :
    ((11 * n - 3 * g : ℕ) : k) = (10 : k) * (n : k) := by
  have heq : 11 * n - 3 * g = 10 * n :=
    residualThreeGapBoundaryMiddle_cubicIndex n g hwall
  rw [heq]
  push_cast
  rfl

theorem residualThreeGapBoundaryMiddle_cast2 (n : ℕ) :
    ((2 * n : ℕ) : k) = (2 : k) * (n : k) := by
  push_cast
  rfl

theorem residualThreeGapBoundaryMiddle_cast8 (n : ℕ) :
    ((8 * n : ℕ) : k) = (8 : k) * (n : k) := by
  push_cast
  rfl

/-! ## Mixed numerators

The displayed row-two / row-zero scalars are the cubic `B,c` cores
evaluated at `11n-3g = 10n` together with the I4-forced `Q`-feed and
the Jacobian cores.  Residual `d e` and `B^2 d` lie strictly below
both load indices. -/

/-- Mixed row-two scalar at index `10n-1`. -/
def residualThreeGapBoundaryTwoScalar68 (N a b c l : k) : k :=
  N * ((80 / 81 : k) * b * (a * b ^ 2 - (9 : k) * c ^ 2) +
    (35 / 576 : k) * l * a ^ 5)

/-- Mixed row-zero scalar at index `12n-1`. -/
def residualThreeGapBoundaryZeroScalar68 (N a b c l : k) : k :=
  N * (-(8 / 243 : k) * a * b * (a * b ^ 2 - (9 : k) * c ^ 2) +
    (35 / 1728 : k) * l * a ^ 6)

theorem residualThreeGapBoundary_two_zero_kill_load
    (N a b c l : k) :
    a * residualThreeGapBoundaryTwoScalar68 N a b c l -
        (3 : k) * residualThreeGapBoundaryZeroScalar68 N a b c l =
      (88 / 81 : k) * N * a * b * (a * b ^ 2 - (9 : k) * c ^ 2) := by
  simp only [residualThreeGapBoundaryTwoScalar68,
    residualThreeGapBoundaryZeroScalar68]
  ring

theorem residualThreeGapBoundary_two_zero_force_l
    (N a b c l : k) (hN : N ≠ 0) (ha : a ≠ 0)
    (htwo : residualThreeGapBoundaryTwoScalar68 N a b c l = 0)
    (hzero : residualThreeGapBoundaryZeroScalar68 N a b c l = 0) :
    l = 0 := by
  have hcomb := residualThreeGapBoundary_two_zero_kill_load N a b c l
  rw [htwo, hzero, mul_zero, mul_zero, sub_zero] at hcomb
  have hΔ : b * (a * b ^ 2 - (9 : k) * c ^ 2) = 0 := by
    have hpre : (88 / 81 : k) * N * a ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num : (88 / 81 : k) ≠ 0) hN) ha
    have hprod : (88 / 81 : k) * N * a *
        (b * (a * b ^ 2 - (9 : k) * c ^ 2)) = 0 := by
      simpa [mul_assoc] using hcomb.symm
    exact (mul_eq_zero.mp hprod).resolve_left hpre
  have hsum :
      (80 / 81 : k) * b * (a * b ^ 2 - (9 : k) * c ^ 2) +
        (35 / 576 : k) * l * a ^ 5 = 0 := by
    have htwo' : (N : k) *
        ((80 / 81 : k) * b * (a * b ^ 2 - (9 : k) * c ^ 2) +
          (35 / 576 : k) * l * a ^ 5) = 0 := by
      simpa only [residualThreeGapBoundaryTwoScalar68] using htwo
    exact (mul_eq_zero.mp htwo').resolve_left hN
  have hcub :
      (80 / 81 : k) * b * (a * b ^ 2 - (9 : k) * c ^ 2) = 0 := by
    calc
      (80 / 81 : k) * b * (a * b ^ 2 - (9 : k) * c ^ 2)
          = (80 / 81 : k) * (b * (a * b ^ 2 - (9 : k) * c ^ 2)) := by
        ring
      _ = (80 / 81 : k) * 0 := by rw [hΔ]
      _ = 0 := by ring
  have hload : (35 / 576 : k) * l * a ^ 5 = 0 := by
    linear_combination hsum - hcub
  have h35 : (35 / 576 : k) ≠ 0 := by norm_num
  have hrearr : (35 / 576 : k) * a ^ 5 * l =
      (35 / 576 : k) * l * a ^ 5 := by ring
  have hprod : (35 / 576 : k) * a ^ 5 * l = 0 := by
    rw [hrearr, hload]
  exact (mul_eq_zero.mp hprod).resolve_left
    (mul_ne_zero h35 (pow_ne_zero 5 ha))

/-! ## I4 / I3 on the load-free middle face -/

set_option maxHeartbeats 2000000 in
theorem cubicFirstIntegralFourPolynomial68_coeff_residualThreeGapBoundary
    (l beta gamma delta epsilon zeta : k) (A B c d e : k[X])
    (n g h : ℕ) (hg : 0 < g) (hwall : 3 * g = n)
    (hleft : n < 2 * h) (hh : h < 2 * g)
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
  have hgh : g < h := residualThreeGapBoundaryMiddle_gap_lt n g h hg hwall hleft
  have hwin : g + h < n := residualThreeGapBoundaryMiddle_win n g h hwall hh
  have hlarge : n ≤ 3 * g := residualThreeGapBoundaryMiddle_large n g hwall
  exact cubicFirstIntegralFourPolynomial68_coeff_residualMiddle_of_loadWindow
    l beta gamma delta epsilon zeta A B c d e n g h hg hgh hlarge hwin
    hA hB hc hd he

set_option maxHeartbeats 2000000 in
theorem cubicFirstIntegralThreePolynomial68_coeff_residualThreeGapBoundary
    (l beta gamma delta epsilon zeta : k) (A B c d e : k[X])
    (n g h : ℕ) (hg : 0 < g) (hwall : 3 * g = n)
    (hleft : n < 2 * h) (hh : h < 2 * g)
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
  have hgh : g < h := residualThreeGapBoundaryMiddle_gap_lt n g h hg hwall hleft
  have hwin : g + h < n := residualThreeGapBoundaryMiddle_win n g h hwall hh
  have hlarge : n ≤ 3 * g := residualThreeGapBoundaryMiddle_large n g hwall
  exact cubicFirstIntegralThreePolynomial68_coeff_residualMiddle_of_loadWindow
    l beta gamma delta epsilon zeta A B c d e n g h hg hgh hlarge hwin
    hA hB hc hd he

theorem polynomialSecondaryResidualBetweenFace68_of_threeGapBoundary
    (l beta gamma delta epsilon zeta i4 i3 : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hwall : 3 * g = n)
    (hleft : n < 2 * h) (hh : h < 2 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hi4 : cubicFirstIntegralFourPolynomial68
      l beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hi3 : cubicFirstIntegralThreePolynomial68
      l beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i3) :
    SecondaryResidualBetweenFace68
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (d.coeff (5 * n - h))
      (e.coeff (6 * n - h)) := by
  have hgh : g < h := residualThreeGapBoundaryMiddle_gap_lt n g h hg hwall hleft
  have hwin : g + h < n := residualThreeGapBoundaryMiddle_win n g h hwall hh
  have hlarge : n ≤ 3 * g := residualThreeGapBoundaryMiddle_large n g hwall
  exact polynomialSecondaryResidualBetweenFace68_of_loadWindow
    l beta gamma delta epsilon zeta i4 i3 A B c d e n g h
    hg hgh hlarge hwin hA hB hc hd he hi4 hi3

/-! ## Shared degree helpers -/

private theorem residualThreeGap_natDegree_smul_lt68
    (r : k) {p : k[X]} {m : ℕ} (hp : p.natDegree < m) :
    (r • p).natDegree < m :=
  (natDegree_smul_le r p).trans_lt hp

private theorem residualThreeGap_natDegree_add_lt68
    {p q : k[X]} {m : ℕ}
    (hp : p.natDegree < m) (hq : q.natDegree < m) :
    (p + q).natDegree < m :=
  (natDegree_add_le p q).trans_lt (max_lt hp hq)

private theorem residualThreeGap_natDegree_sub_lt68
    {p q : k[X]} {m : ℕ}
    (hp : p.natDegree < m) (hq : q.natDegree < m) :
    (p - q).natDegree < m :=
  (natDegree_sub_le p q).trans_lt (max_lt hp hq)

private theorem residualThreeGap_mul_derivative_lt
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

/-! ## Jacobian row-zero core at `12n-1` under `2g < n` -/

set_option maxHeartbeats 4000000 in
theorem cubicLoadRowZeroRestPolynomial68_degree_lt_twelveRadius_of_twoGap
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hsmall : 2 * g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
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
  have hloads := cubicLoadPolynomials68_degreeBounds
    l alpha beta gamma delta epsilon zeta eta A B c D e n g
    hn hg hsmall hA hB hc hD he
  have hUlc : Ulc.natDegree ≤ 6 * n :=
    cubicLoadUCorePolynomial68_degree_le l A n hA
  have hUlr : Ulr.natDegree ≤ 6 * n - g :=
    cubicLoadURestPolynomial68_degree_le_twoGap
      l alpha beta gamma delta zeta A B c D e n g
      hg hsmall hA hB hc hD he
  have hEr : Er.natDegree ≤ 6 * n - g :=
    cubicERestPolynomial68_degree_le_twoGap A c e n g
      hg hsmall hA hc he
  have hEc : Ec.natDegree ≤ 6 * n := by
    simp only [Ec]
    compute_degree
    omega
  have hE : E.natDegree ≤ 6 * n :=
    (natDegree_add_le Ec Er).trans (max_le hEc (hEr.trans (by omega)))
  have hVl : Vl.natDegree ≤ 7 * n - g := by
    simpa only [Vl] using hloads.2.2.2
  have h1 : (Ulc * derivative Er).natDegree < 12 * n - 1 :=
    residualThreeGap_mul_derivative_lt Ulc Er (6 * n) (6 * n - g)
      (12 * n - 1) (by omega) hUlc hEr (by omega)
  have h2 : (Ulr * derivative E).natDegree < 12 * n - 1 :=
    residualThreeGap_mul_derivative_lt Ulr E (6 * n - g) (6 * n)
      (12 * n - 1) (by omega) hUlr hE (by omega)
  have h3 : (D * derivative Vl).natDegree < 12 * n - 1 :=
    residualThreeGap_mul_derivative_lt D Vl (5 * n - g) (7 * n - g)
      (12 * n - 1) (by omega) hD hVl (by omega)
  change (Ulc * derivative Er + Ulr * derivative E -
      D * derivative Vl).natDegree < _
  exact residualThreeGap_natDegree_sub_lt68
    (residualThreeGap_natDegree_add_lt68 h1 h2) h3

set_option maxHeartbeats 2000000 in
theorem cubicLoadRowZeroPolynomial68_coeff_twelveRadius_of_twoGap
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hsmall : 2 * g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadRowZeroPolynomial68 l alpha beta gamma delta epsilon zeta eta
      A B c D e).coeff (12 * n - 1) =
      (35 / 1944 : k) * (n : k) * l * A.coeff (2 * n) ^ 6 := by
  rw [cubicLoadRowZeroPolynomial68_eq_lCore_add_rest, coeff_add,
    coeff_eq_zero_of_natDegree_lt
      (cubicLoadRowZeroRestPolynomial68_degree_lt_twelveRadius_of_twoGap
        l alpha beta gamma delta epsilon zeta eta A B c D e n g
        hn hg hsmall hA hB hc hD he), add_zero]
  exact cubicLoadRowZeroLCorePolynomial68_coeff_loadWall l A n hn hA

/-! ## Row-zero incidence rewrite -/

/-- Inner expression of residual row zero after the `Q` rewrite, before
`4/27`. -/
def residualRowZeroInner68 (A B c d e : k[X]) : k[X] :=
  -(A * derivative A * residualIncidenceQ68 B c d e) -
    (1 / 9 : k) • (A * derivative A * B ^ 3) +
    derivative A * B * c ^ 2 -
    (3 : k) • (derivative A * d * e) -
    A * B ^ 2 * derivative d -
    A * B * derivative B * d +
    (3 : k) • (B * c * derivative e) -
    (3 : k) • (B * d * derivative d) -
    (3 : k) • (derivative B * d ^ 2) -
    (3 : k) • (c * derivative c * d)

set_option maxHeartbeats 8000000 in
theorem residualRowZero_eq_inner68 (A B c d e : k[X]) :
    secondaryResidualRowZeroPolynomial68 A B c d e =
      (4 / 27 : k) • residualRowZeroInner68 A B c d e := by
  simp only [secondaryResidualRowZeroPolynomial68, residualRowZeroInner68,
    residualIncidenceQ68, derivative_add, derivative_sub, derivative_mul,
    derivative_pow, derivative_smul, derivative_C, zero_mul, zero_add,
    smul_add, smul_sub, Polynomial.smul_eq_C_mul]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_zero,
    RatFunc.algebraMap_C, map_div₀, map_ofNat, map_natCast, map_one]
  ring

/-! ## Homogeneous residual row two at `10n-1` -/

set_option maxHeartbeats 8000000 in
theorem secondaryResidualRowTwoPolynomial68_coeff_threeGapBoundary
    (l beta gamma delta epsilon zeta i4 : k) (A B c d e : k[X])
    (n g h : ℕ) (hn : 0 < n) (hg : 0 < g) (hwall : 3 * g = n)
    (hleft : n < 2 * h) (hh : h < 2 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hi4 : cubicFirstIntegralFourPolynomial68
      l beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4) :
    (secondaryResidualRowTwoPolynomial68 A B c d e).coeff (10 * n - 1) =
      (80 / 81 : k) * (n : k) * B.coeff (3 * n - g) *
          (A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 -
            (9 : k) * c.coeff (4 * n - g) ^ 2) +
        (-245 / 5184 : k) * (n : k) * l * A.coeff (2 * n) ^ 5 := by
  let Q := residualIncidenceQ68 B c d e
  let inner := residualRowTwoInner68 A B c d e
  set idx := 10 * n - 1
  have hsmall : 2 * g < n := residualThreeGapBoundaryMiddle_twoGap n g hg hwall
  have hgh : g < h := residualThreeGapBoundaryMiddle_gap_lt n g h hg hwall hleft
  have he' : e.natDegree ≤ 6 * n - g :=
    residualThreeGapBoundaryMiddle_eBound n g h hgh he
  have hd' : d.natDegree ≤ 5 * n - g :=
    residualThreeGapBoundaryMiddle_dBound n g h hgh hd
  have hQdeg := residualIncidenceQ68_degree_le_eightRadius_of_I4
    l beta gamma delta epsilon zeta i4 A B c d e n g
    hg hsmall hA hB hc hd' he' hi4
  have hQ8 := residualIncidenceQ68_coeff_eightRadius_of_I4
    l beta gamma delta epsilon zeta i4 A B c d e n g
    hn hg hsmall hA hB hc hd' he' hi4
  have hAQ : (A * derivative Q).coeff idx =
      A.coeff (2 * n) * Q.coeff (8 * n) * ((8 * n : ℕ) : k) := by
    have h := coeff_mul_derivative_at_bounds68 A Q (2 * n) (8 * n)
      (by omega) hA hQdeg
    have hi : 2 * n + 8 * n - 1 = idx := by
      dsimp [idx]
      omega
    simpa only [hi] using h
  have hQA : (derivative A * Q).coeff idx =
      A.coeff (2 * n) * Q.coeff (8 * n) * ((2 * n : ℕ) : k) := by
    have hdA : (derivative A).natDegree ≤ 2 * n - 1 :=
      (natDegree_derivative_le A).trans (by omega)
    have h := coeff_mul_at_bounds68 (derivative A) Q (2 * n - 1) (8 * n)
      hdA hQdeg
    have hi : (2 * n - 1) + 8 * n = idx := by
      dsimp [idx]
      omega
    have hA' := coeff_derivative_at_bound68 A (2 * n) (by omega)
    rw [hi, hA'] at h
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  have hBd := residualRowTwoInner_Bd_degree_le68_of_twoGap
    B d n g h hg hgh hh hsmall hB hd
  have hBd' : (derivative (B ^ 2 * d)).natDegree < idx := by
    dsimp [idx]
    omega
  have hde := residualRowTwoInner_de_degree_le68_of_twoGap
    d e n g h hg hgh hh hsmall hd he
  have hde' : (derivative (d * e)).natDegree < idx := by
    dsimp [idx]
    omega
  have hB2deg : (B ^ 2).natDegree ≤ 6 * n - 2 * g := by
    compute_degree
    omega
  have hB2 : (B ^ 2).coeff (6 * n - 2 * g) =
      B.coeff (3 * n - g) ^ 2 := by
    have h := coeff_pow_at_bound68 B (3 * n - g) 2 hB
    have hi : 2 * (3 * n - g) = 6 * n - 2 * g := by omega
    simpa only [hi] using h
  have hAB := coeff_mul_mul_derivative_at_bounds68 A (B ^ 2) B
    (2 * n) (6 * n - 2 * g) (3 * n - g) (by omega) hA hB2deg hB
  have hiAB : 2 * n + (6 * n - 2 * g) + (3 * n - g) - 1 = idx := by
    dsimp [idx]
    omega
  rw [hiAB, hB2] at hAB
  have hABpow : (A * B ^ 2 * derivative B).coeff idx =
      A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 *
        ((3 * n - g : ℕ) : k) := by
    rw [hAB]
    ring
  have hB3deg : (B ^ 3).natDegree ≤ 9 * n - 3 * g := by
    compute_degree
    omega
  have hB3 : (B ^ 3).coeff (9 * n - 3 * g) =
      B.coeff (3 * n - g) ^ 3 := by
    have h := coeff_pow_at_bound68 B (3 * n - g) 3 hB
    have hi : 3 * (3 * n - g) = 9 * n - 3 * g := by omega
    simpa only [hi] using h
  have hA3 := coeff_mul_derivative_at_bounds68 (B ^ 3) A
    (9 * n - 3 * g) (2 * n) (by omega) hB3deg hA
  have hiA3 : (9 * n - 3 * g) + 2 * n - 1 = idx := by
    dsimp [idx]
    omega
  rw [hiA3, hB3] at hA3
  have hA3' : (derivative A * B ^ 3).coeff idx =
      A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 *
        ((2 * n : ℕ) : k) := by
    rw [show (derivative A * B ^ 3).coeff idx =
        (B ^ 3 * derivative A).coeff idx by
      congr 1
      ring]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hA3
  have hc2deg : (c ^ 2).natDegree ≤ 8 * n - 2 * g := by
    compute_degree
    omega
  have hc2 : (c ^ 2).coeff (8 * n - 2 * g) =
      c.coeff (4 * n - g) ^ 2 := by
    have h := coeff_pow_at_bound68 c (4 * n - g) 2 hc
    have hi : 2 * (4 * n - g) = 8 * n - 2 * g := by omega
    simpa only [hi] using h
  have hBcdeg : (B * c ^ 2).natDegree ≤ 11 * n - 3 * g := by
    have h := natDegree_mul_le_of_le hB hc2deg
    have hi : (3 * n - g) + (8 * n - 2 * g) = 11 * n - 3 * g := by omega
    rwa [hi] at h
  have hBccoeff := coeff_mul_at_bounds68 B (c ^ 2)
    (3 * n - g) (8 * n - 2 * g) hB hc2deg
  have hiBc : (3 * n - g) + (8 * n - 2 * g) = 11 * n - 3 * g := by omega
  rw [hiBc, hc2] at hBccoeff
  have hBc := coeff_derivative_at_bound68 (B * c ^ 2)
    (11 * n - 3 * g) (by omega)
  rw [hBccoeff] at hBc
  have hBc' : (derivative (B * c ^ 2)).coeff idx =
      B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 *
        ((11 * n - 3 * g : ℕ) : k) := by
    have hi : 11 * n - 3 * g - 1 = idx := by
      dsimp [idx]
      omega
    rwa [← hi]
  have hcast3 : ((3 * n - g : ℕ) : k) = (8 / 3 : k) * (n : k) :=
    residualThreeGapBoundaryMiddle_cast3 n g hwall
  have hcast2 : ((2 * n : ℕ) : k) = (2 : k) * (n : k) :=
    residualThreeGapBoundaryMiddle_cast2 n
  have hcast11 : ((11 * n - 3 * g : ℕ) : k) = (10 : k) * (n : k) :=
    residualThreeGapBoundaryMiddle_cast11 n g hwall
  have hcast8 : ((8 * n : ℕ) : k) = (8 : k) * (n : k) :=
    residualThreeGapBoundaryMiddle_cast8 n
  have h0Bd : ((6 : k) • derivative (B ^ 2 * d)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hBd', mul_zero]
  have h0de : ((-18 : k) • derivative (d * e)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hde', mul_zero]
  have hQpart : ((-6 : k) • (A * derivative Q)).coeff idx +
      ((3 : k) • (derivative A * Q)).coeff idx =
      (-42 : k) * (n : k) * A.coeff (2 * n) * Q.coeff (8 * n) := by
    rw [coeff_smul, coeff_smul, smul_eq_mul, smul_eq_mul, hAQ, hQA, hcast8,
      hcast2]
    ring
  have hcub : ((-2 : k) • (A * B ^ 2 * derivative B)).coeff idx +
      ((-2 / 3 : k) • (derivative A * B ^ 3)).coeff idx +
      ((6 : k) • derivative (B * c ^ 2)).coeff idx =
      (-20 / 3 : k) * (n : k) * B.coeff (3 * n - g) *
        (A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 -
          (9 : k) * c.coeff (4 * n - g) ^ 2) := by
    rw [coeff_smul, coeff_smul, coeff_smul, smul_eq_mul, smul_eq_mul,
      smul_eq_mul, hABpow, hA3', hBc', hcast3, hcast2, hcast11]
    ring
  have hinner : inner.coeff idx =
      (-42 : k) * (n : k) * A.coeff (2 * n) * Q.coeff (8 * n) +
        (-20 / 3 : k) * (n : k) * B.coeff (3 * n - g) *
          (A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 -
            (9 : k) * c.coeff (4 * n - g) ^ 2) := by
    dsimp [inner, residualRowTwoInner68]
    simp only [coeff_add]
    rw [h0Bd, h0de]
    linear_combination hQpart + hcub
  rw [residualRowTwo_eq_inner68, coeff_smul, smul_eq_mul]
  change ((-4 / 27 : k) * inner.coeff idx) = _
  rw [hinner]
  simp only [Q, hQ8]
  ring

/-! ## Homogeneous residual row zero at `12n-1` -/

set_option maxHeartbeats 8000000 in
theorem secondaryResidualRowZeroPolynomial68_coeff_threeGapBoundary
    (l beta gamma delta epsilon zeta i4 : k) (A B c d e : k[X])
    (n g h : ℕ) (hn : 0 < n) (hg : 0 < g) (hwall : 3 * g = n)
    (hleft : n < 2 * h) (hh : h < 2 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hi4 : cubicFirstIntegralFourPolynomial68
      l beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4) :
    (secondaryResidualRowZeroPolynomial68 A B c d e).coeff (12 * n - 1) =
      -(8 / 243 : k) * (n : k) * A.coeff (2 * n) * B.coeff (3 * n - g) *
          (A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 -
            (9 : k) * c.coeff (4 * n - g) ^ 2) +
        (35 / 15552 : k) * (n : k) * l * A.coeff (2 * n) ^ 6 := by
  let Q := residualIncidenceQ68 B c d e
  let inner := residualRowZeroInner68 A B c d e
  set idx := 12 * n - 1
  have hsmall : 2 * g < n := residualThreeGapBoundaryMiddle_twoGap n g hg hwall
  have hgh : g < h := residualThreeGapBoundaryMiddle_gap_lt n g h hg hwall hleft
  have he' : e.natDegree ≤ 6 * n - g :=
    residualThreeGapBoundaryMiddle_eBound n g h hgh he
  have hd' : d.natDegree ≤ 5 * n - g :=
    residualThreeGapBoundaryMiddle_dBound n g h hgh hd
  have hQdeg := residualIncidenceQ68_degree_le_eightRadius_of_I4
    l beta gamma delta epsilon zeta i4 A B c d e n g
    hg hsmall hA hB hc hd' he' hi4
  have hQ8 := residualIncidenceQ68_coeff_eightRadius_of_I4
    l beta gamma delta epsilon zeta i4 A B c d e n g
    hn hg hsmall hA hB hc hd' he' hi4
  have hAAQ := coeff_mul_mul_derivative_at_bounds68 A Q A
    (2 * n) (8 * n) (2 * n) (by omega) hA hQdeg hA
  have hiAAQ : 2 * n + 8 * n + 2 * n - 1 = idx := by
    dsimp [idx]
    omega
  rw [hiAAQ] at hAAQ
  have hAAQ' : (A * derivative A * Q).coeff idx =
      A.coeff (2 * n) ^ 2 * Q.coeff (8 * n) * ((2 * n : ℕ) : k) := by
    have hcomm : A * derivative A * Q = A * Q * derivative A := by
      simp only [mul_assoc, mul_comm, mul_left_comm]
    rw [hcomm]
    simpa only [mul_assoc, mul_comm, mul_left_comm, pow_two] using hAAQ
  have hB3deg : (B ^ 3).natDegree ≤ 9 * n - 3 * g := by
    compute_degree
    omega
  have hB3 : (B ^ 3).coeff (9 * n - 3 * g) =
      B.coeff (3 * n - g) ^ 3 := by
    have h := coeff_pow_at_bound68 B (3 * n - g) 3 hB
    have hi : 3 * (3 * n - g) = 9 * n - 3 * g := by omega
    simpa only [hi] using h
  have hAAB := coeff_mul_mul_derivative_at_bounds68 A (B ^ 3) A
    (2 * n) (9 * n - 3 * g) (2 * n) (by omega) hA hB3deg hA
  have hiAAB : 2 * n + (9 * n - 3 * g) + 2 * n - 1 = idx := by
    dsimp [idx]
    omega
  rw [hiAAB, hB3] at hAAB
  have hAAB' : (A * derivative A * B ^ 3).coeff idx =
      A.coeff (2 * n) ^ 2 * B.coeff (3 * n - g) ^ 3 *
        ((2 * n : ℕ) : k) := by
    have hcomm : A * derivative A * B ^ 3 =
        A * B ^ 3 * derivative A := by
      simp only [mul_assoc, mul_comm, mul_left_comm]
    rw [hcomm]
    simpa only [mul_assoc, mul_comm, mul_left_comm, pow_two] using hAAB
  have hBc2 := coeff_mul_mul_mul_derivative_at_bounds68 B c c A
    (3 * n - g) (4 * n - g) (4 * n - g) (2 * n) (by omega) hB hc hc hA
  have hiBc2 : (3 * n - g) + (4 * n - g) + (4 * n - g) + 2 * n - 1 =
      idx := by
    dsimp [idx]
    omega
  rw [hiBc2] at hBc2
  have hABc' : (derivative A * B * c ^ 2).coeff idx =
      A.coeff (2 * n) * B.coeff (3 * n - g) *
        c.coeff (4 * n - g) ^ 2 * ((2 * n : ℕ) : k) := by
    simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using hBc2
  have hlow1 : (derivative A * d * e).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  have hlow2 : (A * B ^ 2 * derivative d).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  have hlow3 : (A * B * derivative B * d).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  have hlow4 : (B * c * derivative e).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  have hlow5 : (B * d * derivative d).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  have hlow6 : (derivative B * d ^ 2).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  have hlow7 : (c * derivative c * d).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  have hcast2 : ((2 * n : ℕ) : k) = (2 : k) * (n : k) :=
    residualThreeGapBoundaryMiddle_cast2 n
  have hinner : inner.coeff idx =
      -(2 : k) * (n : k) * A.coeff (2 * n) ^ 2 * Q.coeff (8 * n) -
        (2 / 9 : k) * (n : k) * A.coeff (2 * n) ^ 2 *
          B.coeff (3 * n - g) ^ 3 +
        (2 : k) * (n : k) * A.coeff (2 * n) * B.coeff (3 * n - g) *
          c.coeff (4 * n - g) ^ 2 := by
    dsimp [inner, residualRowZeroInner68]
    simp only [Q, coeff_add, coeff_sub, coeff_neg, coeff_smul, smul_eq_mul]
    rw [hAAQ', hAAB', hABc',
      coeff_eq_zero_of_natDegree_lt hlow1,
      coeff_eq_zero_of_natDegree_lt hlow2,
      coeff_eq_zero_of_natDegree_lt hlow3,
      coeff_eq_zero_of_natDegree_lt hlow4,
      coeff_eq_zero_of_natDegree_lt hlow5,
      coeff_eq_zero_of_natDegree_lt hlow6,
      coeff_eq_zero_of_natDegree_lt hlow7, hcast2]
    ring
  rw [residualRowZero_eq_inner68, coeff_smul, smul_eq_mul]
  change ((4 / 27 : k) * inner.coeff idx) = _
  rw [hinner]
  simp only [Q, hQ8]
  ring

/-! ## Combined coefficients and `l = 0` -/

set_option maxHeartbeats 4000000 in
theorem cubicRowTwoPolynomial68_coeff_residualThreeGapBoundary
    (l alpha beta gamma delta epsilon zeta eta i4 : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hwall : 3 * g = n)
    (hleft : n < 2 * h) (hh : h < 2 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hi4 : cubicFirstIntegralFourPolynomial68
      l beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4) :
    (secondaryResidualRowTwoPolynomial68 A B c d e +
      cubicLoadRowTwoPolynomial68 l alpha beta gamma delta epsilon zeta eta
        A B c ((1 / 3 : k) • (A * B) + d) e).coeff (10 * n - 1) =
      residualThreeGapBoundaryTwoScalar68 (n : k)
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) l := by
  let D := (1 / 3 : k) • (A * B) + d
  have hD : D.natDegree ≤ 5 * n - g := by
    simp only [D]
    compute_degree
    omega
  have hsmall : 2 * g < n := residualThreeGapBoundaryMiddle_twoGap n g hg hwall
  have hgh : g < h := residualThreeGapBoundaryMiddle_gap_lt n g h hg hwall hleft
  have he' : e.natDegree ≤ 6 * n - g :=
    residualThreeGapBoundaryMiddle_eBound n g h hgh he
  have hhom := secondaryResidualRowTwoPolynomial68_coeff_threeGapBoundary
    l beta gamma delta epsilon zeta i4 A B c d e n g h
    hn hg hwall hleft hh hA hB hc hd he hi4
  have hload := cubicLoadRowTwoPolynomial68_coeff_tenRadius_of_twoGap
    l alpha beta gamma delta epsilon zeta eta A B c D e n g
    hn hg hsmall hA hB hc hD he'
  rw [coeff_add, hhom]
  change _ +
      (cubicLoadRowTwoPolynomial68 l alpha beta gamma delta epsilon zeta eta
        A B c D e).coeff (10 * n - 1) = _
  rw [hload]
  simp only [residualThreeGapBoundaryTwoScalar68]
  ring

set_option maxHeartbeats 4000000 in
theorem cubicRowZeroPolynomial68_coeff_residualThreeGapBoundary
    (l alpha beta gamma delta epsilon zeta eta i4 : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hwall : 3 * g = n)
    (hleft : n < 2 * h) (hh : h < 2 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hi4 : cubicFirstIntegralFourPolynomial68
      l beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4) :
    (secondaryResidualRowZeroPolynomial68 A B c d e +
      cubicLoadRowZeroPolynomial68 l alpha beta gamma delta epsilon zeta eta
        A B c ((1 / 3 : k) • (A * B) + d) e).coeff (12 * n - 1) =
      residualThreeGapBoundaryZeroScalar68 (n : k)
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) l := by
  let D := (1 / 3 : k) • (A * B) + d
  have hD : D.natDegree ≤ 5 * n - g := by
    simp only [D]
    compute_degree
    omega
  have hsmall : 2 * g < n := residualThreeGapBoundaryMiddle_twoGap n g hg hwall
  have hgh : g < h := residualThreeGapBoundaryMiddle_gap_lt n g h hg hwall hleft
  have he' : e.natDegree ≤ 6 * n - g :=
    residualThreeGapBoundaryMiddle_eBound n g h hgh he
  have hhom := secondaryResidualRowZeroPolynomial68_coeff_threeGapBoundary
    l beta gamma delta epsilon zeta i4 A B c d e n g h
    hn hg hwall hleft hh hA hB hc hd he hi4
  have hload := cubicLoadRowZeroPolynomial68_coeff_twelveRadius_of_twoGap
    l alpha beta gamma delta epsilon zeta eta A B c D e n g
    hn hg hsmall hA hB hc hD he'
  rw [coeff_add, hhom]
  change _ +
      (cubicLoadRowZeroPolynomial68 l alpha beta gamma delta epsilon zeta eta
        A B c D e).coeff (12 * n - 1) = _
  rw [hload]
  simp only [residualThreeGapBoundaryZeroScalar68]
  ring

set_option maxHeartbeats 2000000 in
theorem cubicRowTwoZeroPolynomial68_imp_loadL_eq_zero_of_threeGapBoundary
    (l alpha beta gamma delta epsilon zeta eta i4 : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hwall : 3 * g = n)
    (hleft : n < 2 * h) (hh : h < 2 * g)
    (hA : A.natDegree ≤ 2 * n)
    (ha : A.coeff (2 * n) ≠ 0)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hi4 : cubicFirstIntegralFourPolynomial68
      l beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hsumTwo : secondaryResidualRowTwoPolynomial68 A B c d e +
      cubicLoadRowTwoPolynomial68 l alpha beta gamma delta epsilon zeta eta
        A B c ((1 / 3 : k) • (A * B) + d) e = 0)
    (hsumZero : (secondaryResidualRowZeroPolynomial68 A B c d e +
      cubicLoadRowZeroPolynomial68 l alpha beta gamma delta epsilon zeta eta
        A B c ((1 / 3 : k) • (A * B) + d) e).coeff (12 * n - 1) = 0) :
    l = 0 := by
  have htwo := congrArg (fun p : k[X] => p.coeff (10 * n - 1)) hsumTwo
  rw [cubicRowTwoPolynomial68_coeff_residualThreeGapBoundary
    l alpha beta gamma delta epsilon zeta eta i4 A B c d e n g h
    hn hg hwall hleft hh hA hB hc hd he hi4, coeff_zero] at htwo
  have hzero := hsumZero
  rw [cubicRowZeroPolynomial68_coeff_residualThreeGapBoundary
    l alpha beta gamma delta epsilon zeta eta i4 A B c d e n g h
    hn hg hwall hleft hh hA hB hc hd he hi4] at hzero
  exact residualThreeGapBoundary_two_zero_force_l (n : k)
    (A.coeff (2 * n)) (B.coeff (3 * n - g)) (c.coeff (4 * n - g)) l
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)) ha htwo hzero

set_option maxHeartbeats 4000000 in
theorem polynomialSecondaryResidualThreeGapBoundary_loadL_eq_zero68
    (l alpha beta gamma delta epsilon zeta eta i4 : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hwall : 3 * g = n)
    (hleft : n < 2 * h) (hh : h < 2 * g)
    (hA : A.natDegree ≤ 2 * n)
    (ha : A.coeff (2 * n) ≠ 0)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hi4 : cubicFirstIntegralFourPolynomial68
      l beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hrowTwo :
      let C0 := (1 / 3 : k) • A ^ 2 + c
      let D0 := (1 / 3 : k) • (A * B) + d
      let E0 := (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
      lowerRowTwoPolynomial68
        (integratedSPolynomial68 l alpha beta delta A B C0 D0)
        (integratedTPolynomial68 l alpha beta gamma epsilon A B C0 D0 E0)
        (integratedUPolynomial68 l alpha beta gamma delta zeta A B C0 D0 E0)
        (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
          A B C0 D0 E0) B C0 D0 E0 = 0)
    (hrowZero : (lowerRowZeroPolynomial68
      (integratedUPolynomial68 l alpha beta gamma delta zeta A B
        ((1 / 3 : k) • A ^ 2 + c) ((1 / 3 : k) • (A * B) + d)
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta A B
        ((1 / 3 : k) • A ^ 2 + c) ((1 / 3 : k) • (A * B) + d)
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      ((1 / 3 : k) • (A * B) + d)
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)).coeff
          (12 * n - 1) = 0) :
    l = 0 := by
  have hsumTwo := polynomialSecondaryResidualRowTwo68
    l alpha beta gamma delta epsilon zeta eta A B c d e hrowTwo
  let D0 := (1 / 3 : k) • (A * B) + d
  have hcoords := integratedPolynomial68_cubicCoordinates
    l alpha beta gamma delta epsilon zeta eta A B c D0 e
  have hsumZero :
      (secondaryResidualRowZeroPolynomial68 A B c d e +
        cubicLoadRowZeroPolynomial68 l alpha beta gamma delta epsilon zeta eta
          A B c D0 e).coeff (12 * n - 1) = 0 := by
    have hz := hrowZero
    rw [hcoords.u_eq, hcoords.v_eq, cubicRowZeroPolynomial68_split,
      show cubicHomogeneousRowZeroPolynomial68 A B c D0 e =
          secondaryResidualRowZeroPolynomial68 A B c d e by
        simpa only [D0] using
          cubicHomogeneousRowZeroPolynomial68_residualCoordinates A B c d e]
      at hz
    simpa only [D0] using hz
  exact cubicRowTwoZeroPolynomial68_imp_loadL_eq_zero_of_threeGapBoundary
    l alpha beta gamma delta epsilon zeta eta i4 A B c d e n g h
    hn hg hwall hleft hh hA ha hB hc hd he hi4 hsumTwo (by
      simpa only [D0] using hsumZero)

/-! ## Canonical expanded wrapper -/

theorem residualThreeGapBoundaryMiddleRowZeroIndex68_gt_fiftyNine
    (n : ℕ) (hn : 10 ≤ n) : 59 < 12 * n - 1 := by
  omega

set_option maxHeartbeats 8000000 in
/-- On the canonical expanded system, the mixed residual cubic-load
chamber `n = 3g` with `n < 2h` and `h < 2g` forces `l = 0`.  The tracked
load-zero endgame then closes the branch.  No residual-support premise
is required. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_residualThreeGapBoundaryMiddle_impossible68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
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
      3 * g = n)
    (hdom :
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
      n < 2 * h ∧ h < 2 * g) :
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
  change 3 * g = n at hwall
  change n < 2 * h ∧ h < 2 * g at hdom
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
  have hsmall : 2 * g < n := residualThreeGapBoundaryMiddle_twoGap n g hg hwall
  have hdrops :=
    maximalExpandedIntegratedPolynomialLowerSystem_secondaryResidualDegreeDrops68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsmall)
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
  have hi4e : firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i4 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_firstIntegralFourPolynomial68_of_eq
        l beta gamma delta epsilon zeta i4 A B C0 D E hi4
  have hi4c := hi4e
  rw [hCrec, hErec, firstIntegralFourPolynomial68_cubicCoordinates,
    hDrec] at hi4c
  have h2e : lowerRowTwoPolynomial68
      (integratedSPolynomial68 l alpha beta delta Ae Be Ce De)
      (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) Be Ce De Ee = 0 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_lowerRowTwoPolynomial68_of_system
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
  have h2c :
      let Crec := (1 / 3 : k) • Ae ^ 2 + ce
      let Drec := (1 / 3 : k) • (Ae * Be) + d
      let Erec := (1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee
      lowerRowTwoPolynomial68
        (integratedSPolynomial68 l alpha beta delta Ae Be Crec Drec)
        (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Crec
          Drec Erec)
        (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Crec
          Drec Erec)
        (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
          Ae Be Crec Drec Erec) Be Crec Drec Erec = 0 := by
    simp only
    rw [← hCrec, ← hDrec, ← hErec]
    exact h2e
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
      (residualThreeGapBoundaryMiddleRowZeroIndex68_gt_fiftyNine n hnlarge)
  have h0c : (lowerRowZeroPolynomial68
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be
        ((1 / 3 : k) • Ae ^ 2 + ce) ((1 / 3 : k) • (Ae * Be) + d)
        ((1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee))
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta Ae Be
        ((1 / 3 : k) • Ae ^ 2 + ce) ((1 / 3 : k) • (Ae * Be) + d)
        ((1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee))
      ((1 / 3 : k) • (Ae * Be) + d)
        ((1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee)).coeff
          (12 * n - 1) = 0 := by
    simpa only [← hCrec, ← hDrec, ← hErec] using h0target
  have hl0 := polynomialSecondaryResidualThreeGapBoundary_loadL_eq_zero68
    l alpha beta gamma delta epsilon zeta eta i4 Ae Be ce d ee n g h
    hn hg hwall hdom.1 hdom.2 hA ha hB hc hbounds.1 hbounds.2 hi4c h2c h0c
  exact maximalExpandedIntegratedPolynomialLowerSystem_secondaryResidualLoadZero_impossible68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys hl0 (by
      simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsmall)

#print axioms residualThreeGapBoundary_two_zero_force_l
#print axioms polynomialSecondaryResidualBetweenFace68_of_threeGapBoundary
#print axioms secondaryResidualRowTwoPolynomial68_coeff_threeGapBoundary
#print axioms secondaryResidualRowZeroPolynomial68_coeff_threeGapBoundary
#print axioms polynomialSecondaryResidualThreeGapBoundary_loadL_eq_zero68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_residualThreeGapBoundaryMiddle_impossible68

end Max11DegreeRoutes
