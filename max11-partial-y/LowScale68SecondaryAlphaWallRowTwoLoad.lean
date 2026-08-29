import LowScale68SecondaryAlphaWallRowOneLoad
import LowScale68SecondaryResidualRowTwoSystem
import LowScale68SecondaryResidualRowTwoFaces
import LowScale68SecondaryResidualSelector

/-! # Mixed cubic residual row-two load on the alpha wall `g = n`

After `l = 0` every row-two load product meets `11n-3g-1 = 8n-1`.
The six `alpha` cores cancel.  The unique survivor is the `beta A^2`
piece of `Ul` against `C0'`, with net scalar `(5 n / 18) beta a^4`.

Row one is already load-free at `9n-1`.  The left residual chamber
`2h < 3g` remains strictly above the load, so it is still the ordinary
`d e` face.  Right and balanced share the cubic index with the load.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlphaWallRowTwoLoad68

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Mixed cubic residual row-two load scalar on `g = n`. -/
def alphaWallRowTwoLoadScalar68 (N a beta : k) : k :=
  (5 / 18 : k) * N * beta * a ^ 4

private theorem residual_natDegree_mul_derivative_lt68
    (p q : k[X]) (u v : ℕ)
    (hu : p.natDegree ≤ u) (hv : 1 < v) (hq : q.natDegree < v) :
    (p * derivative q).natDegree < u + v - 1 := by
  have hq' : q.natDegree ≤ v - 1 := Nat.le_sub_one_of_lt hq
  have hd : (derivative q).natDegree ≤ v - 2 := by
    have h := natDegree_derivative_le q
    omega
  have hmul := natDegree_mul_le_of_le hu hd
  omega

private theorem residual_natDegree_derivative_mul_lt68
    (p q : k[X]) (u v : ℕ)
    (hu0 : 0 < u) (hu : p.natDegree ≤ u) (hq : q.natDegree < v) :
    (derivative p * q).natDegree < u + v - 1 := by
  have hd : (derivative p).natDegree ≤ u - 1 :=
    (natDegree_derivative_le p).trans (by omega)
  have hq' : q.natDegree ≤ v - 1 := Nat.le_sub_one_of_lt hq
  have hmul := natDegree_mul_le_of_le hd hq'
  omega

theorem residualRowTwo_coeff_eq_zero_of_loadCutoff68_of_alphaWall
    (A B c d e load : k[X]) (idx : ℕ)
    (hload : load.natDegree < idx)
    (hsum : secondaryResidualRowTwoPolynomial68 A B c d e + load = 0) :
    (secondaryResidualRowTwoPolynomial68 A B c d e).coeff idx = 0 := by
  have h := congrArg (fun p : k[X] => p.coeff idx) hsum
  rw [coeff_add, coeff_zero, coeff_eq_zero_of_natDegree_lt hload,
    add_zero] at h
  exact h

/-! ## Leading coefficients after `l = 0` on the wall -/

set_option maxHeartbeats 2000000 in
theorem cubicLoadSPolynomial68_coeff_twoRadius_of_alphaWall
    (l alpha beta delta : k) (A B c : k[X]) (n g : ℕ)
    (hn : 0 < n) (hl : l = 0) (hwall : g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g) :
    (cubicLoadSPolynomial68 l alpha beta delta A B c).coeff (2 * n) =
      alpha * B.coeff (3 * n - g) +
        (5 / 6 * beta : k) * A.coeff (2 * n) := by
  have heq : cubicLoadSPolynomial68 l alpha beta delta A B c =
      alpha • B + (5 / 6 * beta : k) • A + C delta := by
    simp [cubicLoadSPolynomial68, hl, mul_zero, zero_smul, add_zero]
  have hBidx : 3 * n - g = 2 * n := by omega
  have hC : (C delta).coeff (2 * n) = 0 := by
    have hnz : 2 * n ≠ 0 := by omega
    simp [coeff_C, hnz]
  rw [heq, coeff_add, coeff_add, coeff_smul, coeff_smul, smul_eq_mul,
    smul_eq_mul, hC, add_zero, hBidx]

set_option maxHeartbeats 2000000 in
theorem cubicLoadTPolynomial68_coeff_fourRadius_of_alphaWall
    (l alpha beta gamma epsilon : k) (A B c D : k[X]) (n g : ℕ)
    (hn : 0 < n) (hl : l = 0) (hwall : g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g) :
    (cubicLoadTPolynomial68 l alpha beta gamma epsilon A B c D).coeff
        (4 * n) =
      (1 / 3 * alpha : k) * A.coeff (2 * n) ^ 2 := by
  have heq : cubicLoadTPolynomial68 l alpha beta gamma epsilon A B c D =
      (1 / 3 * alpha : k) • A ^ 2 + alpha • c +
        (5 / 6 * beta : k) • B + (2 / 3 * gamma : k) • A + C epsilon := by
    simp [cubicLoadTPolynomial68, hl, mul_zero, zero_smul, add_zero]
  have hA2 := coeff_pow_at_bound68 A (2 * n) 2 hA
  have hi : 2 * (2 * n) = 4 * n := by omega
  rw [hi] at hA2
  have hclt : c.natDegree < 4 * n := by omega
  have hBlt : B.natDegree < 4 * n := by omega
  have hAlt : A.natDegree < 4 * n := by omega
  have hC : (C epsilon).coeff (4 * n) = 0 := by
    have hnz : 4 * n ≠ 0 := by omega
    simp [coeff_C, hnz]
  rw [heq]
  simp only [coeff_add, coeff_smul, smul_eq_mul, hA2,
    coeff_eq_zero_of_natDegree_lt hclt, coeff_eq_zero_of_natDegree_lt hBlt,
    coeff_eq_zero_of_natDegree_lt hAlt, hC, mul_zero, add_zero]

set_option maxHeartbeats 2000000 in
theorem cubicLoadUPolynomial68_coeff_fourRadius_of_alphaWall
    (l alpha beta gamma delta zeta : k) (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hl : l = 0) (hwall : g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g) :
    (cubicLoadUPolynomial68 l alpha beta gamma delta zeta A B c D e).coeff
        (4 * n) =
      alpha * D.coeff (5 * n - g) +
        (5 / 24 * beta : k) * A.coeff (2 * n) ^ 2 := by
  have heq : cubicLoadUPolynomial68 l alpha beta gamma delta zeta
        A B c D e =
      alpha • D + (5 / 24 * beta : k) • A ^ 2 +
        (5 / 6 * beta : k) • c + (2 / 3 * gamma : k) • B +
        (1 / 2 * delta : k) • A + C zeta := by
    simp [cubicLoadUPolynomial68, hl, mul_zero, zero_smul, add_zero]
  have hA2 := coeff_pow_at_bound68 A (2 * n) 2 hA
  have hi : 2 * (2 * n) = 4 * n := by omega
  rw [hi] at hA2
  have hDidx : 5 * n - g = 4 * n := by omega
  have hclt : c.natDegree < 4 * n := by omega
  have hBlt : B.natDegree < 4 * n := by omega
  have hAlt : A.natDegree < 4 * n := by omega
  have hC : (C zeta).coeff (4 * n) = 0 := by
    have hnz : 4 * n ≠ 0 := by omega
    simp [coeff_C, hnz]
  rw [heq]
  simp only [coeff_add, coeff_smul, smul_eq_mul, hA2, hDidx,
    coeff_eq_zero_of_natDegree_lt hclt, coeff_eq_zero_of_natDegree_lt hBlt,
    coeff_eq_zero_of_natDegree_lt hAlt, hC, mul_zero, add_zero]

set_option maxHeartbeats 2000000 in
theorem cubicLoadVPolynomial68_coeff_sixRadius_of_alphaWall
    (l alpha beta gamma delta epsilon eta : k) (A B c D e : k[X])
    (n g : ℕ) (hn : 0 < n) (hl : l = 0) (hwall : g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadVPolynomial68 l alpha beta gamma delta epsilon eta
      A B c D e).coeff (6 * n) =
      (1 / 27 * alpha : k) * A.coeff (2 * n) ^ 3 := by
  have heq : cubicLoadVPolynomial68 l alpha beta gamma delta epsilon eta
        A B c D e =
      (1 / 27 * alpha : k) • A ^ 3 + (1 / 3 * alpha : k) • (A * c) +
        alpha • e - (5 / 36 * beta : k) • (A * B) +
        (5 / 6 * beta : k) • D + (1 / 9 * gamma : k) • A ^ 2 +
        (2 / 3 * gamma : k) • c + (1 / 2 * delta : k) • B +
        (1 / 3 * epsilon : k) • A + C eta := by
    simp [cubicLoadVPolynomial68, hl, mul_zero, zero_smul, add_zero, sub_zero]
  have hA3 := coeff_pow_at_bound68 A (2 * n) 3 hA
  have hi : 3 * (2 * n) = 6 * n := by omega
  rw [hi] at hA3
  have hAclt : (A * c).natDegree < 6 * n := by compute_degree; omega
  have helt : e.natDegree < 6 * n := by omega
  have hABlt : (A * B).natDegree < 6 * n := by compute_degree; omega
  have hDlt : D.natDegree < 6 * n := by omega
  have hA2lt : (A ^ 2).natDegree < 6 * n := by compute_degree; omega
  have hclt : c.natDegree < 6 * n := by omega
  have hBlt : B.natDegree < 6 * n := by omega
  have hAlt : A.natDegree < 6 * n := by omega
  have hC : (C eta).coeff (6 * n) = 0 := by
    have hnz : 6 * n ≠ 0 := by omega
    simp [coeff_C, hnz]
  rw [heq]
  simp only [coeff_add, coeff_sub, coeff_smul, smul_eq_mul, hA3,
    coeff_eq_zero_of_natDegree_lt hAclt, coeff_eq_zero_of_natDegree_lt helt,
    coeff_eq_zero_of_natDegree_lt hABlt, coeff_eq_zero_of_natDegree_lt hDlt,
    coeff_eq_zero_of_natDegree_lt hA2lt, coeff_eq_zero_of_natDegree_lt hclt,
    coeff_eq_zero_of_natDegree_lt hBlt, coeff_eq_zero_of_natDegree_lt hAlt,
    hC, mul_zero, add_zero, sub_zero]

/-! ## Exact cubic load coefficient at `8n-1` -/

set_option maxHeartbeats 8000000 in
/-- After `l = 0` on `g = n`, the cubic residual row-two load is
`(5 n / 18) beta a^4`.  The six `alpha` products cancel; the `Ul C0'`
survivor is the `beta A^2` summand. -/
theorem cubicLoadRowTwoPolynomial68_coeff_cubicFace_of_alphaWall
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hl : l = 0) (hwall : g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadRowTwoPolynomial68 l alpha beta gamma delta epsilon zeta eta
      A B c D e).coeff (11 * n - 3 * g - 1) =
      alphaWallRowTwoLoadScalar68 (n : k) (A.coeff (2 * n)) beta := by
  let C0 := (1 / 3 : k) • A ^ 2 + c
  let E := (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
  let Sl := cubicLoadSPolynomial68 l alpha beta delta A B c
  let Tl := cubicLoadTPolynomial68 l alpha beta gamma epsilon A B c D
  let Ul := cubicLoadUPolynomial68 l alpha beta gamma delta zeta A B c D e
  let Vl := cubicLoadVPolynomial68 l alpha beta gamma delta epsilon eta
    A B c D e
  have hSldeg : Sl.natDegree ≤ 2 * n := by
    have h := cubicLoadSPolynomial68_degreeBound_of_loadL l alpha beta delta
      A B c n g hl hA hB hc
    have hmax : max (2 * n) (3 * n - g) = 2 * n := by omega
    rwa [hmax] at h
  have hTldeg : Tl.natDegree ≤ 4 * n :=
    cubicLoadTPolynomial68_degreeBound_of_loadL l alpha beta gamma epsilon
      A B c D n g hl hA hB hc hD
  have hUldeg : Ul.natDegree ≤ 4 * n := by
    have h := cubicLoadUPolynomial68_degreeBound_of_loadL l alpha beta gamma
      delta zeta A B c D e n g hl hA hB hc hD he
    have hmax : max (4 * n) (5 * n - g) = 4 * n := by omega
    rwa [hmax] at h
  have hVldeg : Vl.natDegree ≤ 6 * n :=
    cubicLoadVPolynomial68_degreeBound_of_loadL l alpha beta gamma delta
      epsilon eta A B c D e n g hl hA hB hc hD he
  have hC0deg : C0.natDegree ≤ 4 * n := by
    simp only [C0]; compute_degree; omega
  have hEdeg : E.natDegree ≤ 6 * n := by
    simp only [E]; compute_degree; omega
  have hBdeg : B.natDegree ≤ 2 * n := by omega
  have hDdeg : D.natDegree ≤ 4 * n := by omega
  have hA2 := coeff_pow_at_bound68 A (2 * n) 2 hA
  have hA2i : 2 * (2 * n) = 4 * n := by omega
  rw [hA2i] at hA2
  have hA3 := coeff_pow_at_bound68 A (2 * n) 3 hA
  have hA3i : 3 * (2 * n) = 6 * n := by omega
  rw [hA3i] at hA3
  have hclt : c.natDegree < 4 * n := by omega
  have hC0 : C0.coeff (4 * n) = (1 / 3 : k) * A.coeff (2 * n) ^ 2 := by
    simp only [C0, coeff_add, coeff_smul, smul_eq_mul, hA2,
      coeff_eq_zero_of_natDegree_lt hclt, add_zero]
  have hAclt : (A * c).natDegree < 6 * n := by compute_degree; omega
  have helt : e.natDegree < 6 * n := by omega
  have hE : E.coeff (6 * n) = (1 / 27 : k) * A.coeff (2 * n) ^ 3 := by
    simp only [E, coeff_add, coeff_smul, smul_eq_mul, hA3,
      coeff_eq_zero_of_natDegree_lt hAclt, coeff_eq_zero_of_natDegree_lt helt,
      mul_zero, add_zero]
  have hSl : Sl.coeff (2 * n) =
      alpha * B.coeff (3 * n - g) +
        (5 / 6 * beta : k) * A.coeff (2 * n) := by
    simpa only [Sl] using
      cubicLoadSPolynomial68_coeff_twoRadius_of_alphaWall l alpha beta delta
        A B c n g hn hl hwall hA hB
  have hTl : Tl.coeff (4 * n) =
      (1 / 3 * alpha : k) * A.coeff (2 * n) ^ 2 := by
    simpa only [Tl] using
      cubicLoadTPolynomial68_coeff_fourRadius_of_alphaWall l alpha beta gamma
        epsilon A B c D n g hn hl hwall hA hB hc
  have hUl : Ul.coeff (4 * n) =
      alpha * D.coeff (5 * n - g) +
        (5 / 24 * beta : k) * A.coeff (2 * n) ^ 2 := by
    simpa only [Ul] using
      cubicLoadUPolynomial68_coeff_fourRadius_of_alphaWall l alpha beta gamma
        delta zeta A B c D e n g hn hl hwall hA hB hc hD
  have hVl : Vl.coeff (6 * n) =
      (1 / 27 * alpha : k) * A.coeff (2 * n) ^ 3 := by
    simpa only [Vl] using
      cubicLoadVPolynomial68_coeff_sixRadius_of_alphaWall l alpha beta gamma
        delta epsilon eta A B c D e n g hn hl hwall hA hB hc hD he
  have hBtop : B.coeff (2 * n) = B.coeff (3 * n - g) := by
    congr 1
    omega
  have hDtop : D.coeff (4 * n) = D.coeff (5 * n - g) := by
    congr 1
    omega
  have h1 : (Ul * derivative C0).coeff (11 * n - 3 * g - 1) =
      Ul.coeff (4 * n) * C0.coeff (4 * n) * ((4 * n : ℕ) : k) := by
    have h := coeff_mul_derivative_at_bounds68 Ul C0 (4 * n) (4 * n)
      (by omega) hUldeg hC0deg
    have hi : 4 * n + 4 * n - 1 = 11 * n - 3 * g - 1 := by omega
    rwa [hi] at h
  have h2 : ((2 : k) • (Tl * derivative D)).coeff (11 * n - 3 * g - 1) =
      (2 : k) * Tl.coeff (4 * n) * D.coeff (4 * n) *
        ((4 * n : ℕ) : k) := by
    have h := coeff_mul_derivative_at_bounds68 Tl D (4 * n) (4 * n)
      (by omega) hTldeg hDdeg
    have hi : 4 * n + 4 * n - 1 = 11 * n - 3 * g - 1 := by omega
    rw [hi] at h
    rw [coeff_smul, smul_eq_mul, h]
    ring
  have h3 : ((3 : k) • (Sl * derivative E)).coeff (11 * n - 3 * g - 1) =
      (3 : k) * Sl.coeff (2 * n) * E.coeff (6 * n) *
        ((6 * n : ℕ) : k) := by
    have h := coeff_mul_derivative_at_bounds68 Sl E (2 * n) (6 * n)
      (by omega) hSldeg hEdeg
    have hi : 2 * n + 6 * n - 1 = 11 * n - 3 * g - 1 := by omega
    rw [hi] at h
    rw [coeff_smul, smul_eq_mul, h]
    ring
  have h4 : ((3 : k) • (B * derivative Vl)).coeff (11 * n - 3 * g - 1) =
      (3 : k) * B.coeff (2 * n) * Vl.coeff (6 * n) *
        ((6 * n : ℕ) : k) := by
    have h := coeff_mul_derivative_at_bounds68 B Vl (2 * n) (6 * n)
      (by omega) hBdeg hVldeg
    have hi : 2 * n + 6 * n - 1 = 11 * n - 3 * g - 1 := by omega
    rw [hi] at h
    rw [coeff_smul, smul_eq_mul, h]
    ring
  have h5 : ((2 : k) • (C0 * derivative Ul)).coeff (11 * n - 3 * g - 1) =
      (2 : k) * C0.coeff (4 * n) * Ul.coeff (4 * n) *
        ((4 * n : ℕ) : k) := by
    have h := coeff_mul_derivative_at_bounds68 C0 Ul (4 * n) (4 * n)
      (by omega) hC0deg hUldeg
    have hi : 4 * n + 4 * n - 1 = 11 * n - 3 * g - 1 := by omega
    rw [hi] at h
    rw [coeff_smul, smul_eq_mul, h]
    ring
  have h6 : (D * derivative Tl).coeff (11 * n - 3 * g - 1) =
      D.coeff (4 * n) * Tl.coeff (4 * n) * ((4 * n : ℕ) : k) := by
    have h := coeff_mul_derivative_at_bounds68 D Tl (4 * n) (4 * n)
      (by omega) hDdeg hTldeg
    have hi : 4 * n + 4 * n - 1 = 11 * n - 3 * g - 1 := by omega
    rwa [hi] at h
  have hcast4 : ((4 * n : ℕ) : k) = 4 * (n : k) := by push_cast; rfl
  have hcast6 : ((6 * n : ℕ) : k) = 6 * (n : k) := by push_cast; rfl
  change (Ul * derivative C0 + (2 : k) • (Tl * derivative D) +
      (3 : k) • (Sl * derivative E) - (3 : k) • (B * derivative Vl) -
      (2 : k) • (C0 * derivative Ul) - D * derivative Tl).coeff
        (11 * n - 3 * g - 1) = _
  simp only [coeff_add, coeff_sub, h1, h2, h3, h4, h5, h6]
  rw [hUl, hC0, hTl, hSl, hE, hVl, hBtop, hDtop, hcast4, hcast6]
  simp only [alphaWallRowTwoLoadScalar68, hwall]
  ring

set_option maxHeartbeats 2000000 in
theorem cubicLoadRowTwoPolynomial68_degree_le_cubicFace_of_alphaWall
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hl : l = 0) (hwall : g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadRowTwoPolynomial68 l alpha beta gamma delta epsilon zeta eta
      A B c D e).natDegree ≤ 11 * n - 3 * g - 1 := by
  let C0 := (1 / 3 : k) • A ^ 2 + c
  let E := (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
  let Sl := cubicLoadSPolynomial68 l alpha beta delta A B c
  let Tl := cubicLoadTPolynomial68 l alpha beta gamma epsilon A B c D
  let Ul := cubicLoadUPolynomial68 l alpha beta gamma delta zeta A B c D e
  let Vl := cubicLoadVPolynomial68 l alpha beta gamma delta epsilon eta
    A B c D e
  have hSl : Sl.natDegree ≤ 2 * n := by
    have h := cubicLoadSPolynomial68_degreeBound_of_loadL l alpha beta delta
      A B c n g hl hA hB hc
    have hmax : max (2 * n) (3 * n - g) = 2 * n := by omega
    rwa [hmax] at h
  have hTl : Tl.natDegree ≤ 4 * n :=
    cubicLoadTPolynomial68_degreeBound_of_loadL l alpha beta gamma epsilon
      A B c D n g hl hA hB hc hD
  have hUl : Ul.natDegree ≤ 4 * n := by
    have h := cubicLoadUPolynomial68_degreeBound_of_loadL l alpha beta gamma
      delta zeta A B c D e n g hl hA hB hc hD he
    have hmax : max (4 * n) (5 * n - g) = 4 * n := by omega
    rwa [hmax] at h
  have hVl : Vl.natDegree ≤ 6 * n :=
    cubicLoadVPolynomial68_degreeBound_of_loadL l alpha beta gamma delta
      epsilon eta A B c D e n g hl hA hB hc hD he
  have hC0 : C0.natDegree ≤ 4 * n := by
    simp only [C0]; compute_degree; omega
  have hE : E.natDegree ≤ 6 * n := by
    simp only [E]; compute_degree; omega
  change (Ul * derivative C0 + (2 : k) • (Tl * derivative D) +
      (3 : k) • (Sl * derivative E) - (3 : k) • (B * derivative Vl) -
      (2 : k) • (C0 * derivative Ul) - D * derivative Tl).natDegree ≤ _
  compute_degree
  omega

/-! ## Mixed residual row-two face -/

set_option maxHeartbeats 2000000 in
theorem polynomialSecondaryResidualRowTwo_coeff_cubicFace_of_alphaWall
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c d e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hl : l = 0) (hwall : g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : ((1 / 3 : k) • (A * B) + d).natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (hsum : secondaryResidualRowTwoPolynomial68 A B c d e +
        cubicLoadRowTwoPolynomial68 l alpha beta gamma delta epsilon zeta eta
          A B c ((1 / 3 : k) • (A * B) + d) e = 0) :
    (secondaryResidualRowTwoPolynomial68 A B c d e).coeff
        (11 * n - 3 * g - 1) =
      -alphaWallRowTwoLoadScalar68 (n : k) (A.coeff (2 * n)) beta := by
  have hload := cubicLoadRowTwoPolynomial68_coeff_cubicFace_of_alphaWall
    l alpha beta gamma delta epsilon zeta eta A B c
    ((1 / 3 : k) • (A * B) + d) e n g
    hn hg hl hwall hA hB hc hD he
  have hcoeff := congrArg
    (fun p : k[X] => p.coeff (11 * n - 3 * g - 1)) hsum
  rw [coeff_add, coeff_zero, hload] at hcoeff
  linear_combination hcoeff

/-! ## Left chamber remains ordinary -/

set_option maxHeartbeats 2000000 in
theorem residualRowTwoInner_Q_degree_lt68_of_alphaWall
    (A B c d e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hwall : g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hQ : (residualIncidenceQ68 B c d e).natDegree < 9 * n - 3 * g) :
    (A * derivative (residualIncidenceQ68 B c d e)).natDegree <
        11 * n - 3 * g - 1 ∧
      (derivative A * residualIncidenceQ68 B c d e).natDegree <
        11 * n - 3 * g - 1 := by
  have hv : 1 < 9 * n - 3 * g := by omega
  have h1 := residual_natDegree_mul_derivative_lt68 A
    (residualIncidenceQ68 B c d e) (2 * n) (9 * n - 3 * g) hA hv hQ
  have h2 := residual_natDegree_derivative_mul_lt68 A
    (residualIncidenceQ68 B c d e) (2 * n) (9 * n - 3 * g)
    (by omega) hA hQ
  have hi : 2 * n + (9 * n - 3 * g) - 1 = 11 * n - 3 * g - 1 := by omega
  exact ⟨by simpa only [hi] using h1, by simpa only [hi] using h2⟩

set_option maxHeartbeats 2000000 in
theorem residualRowTwoInner_BcCore_degree_le68_of_alphaWall
    (A B c : k[X]) (n g : ℕ)
    (hg : 0 < g) (hwall : g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g) :
    (A * B ^ 2 * derivative B).natDegree ≤ 11 * n - 3 * g - 1 ∧
      (derivative A * B ^ 3).natDegree ≤ 11 * n - 3 * g - 1 ∧
      (derivative (B * c ^ 2)).natDegree ≤ 11 * n - 3 * g - 1 := by
  have hB2 : (B ^ 2).natDegree ≤ 6 * n - 2 * g := by
    compute_degree
    omega
  have hB3 : (B ^ 3).natDegree ≤ 9 * n - 3 * g := by
    compute_degree
    omega
  have hc2 : (c ^ 2).natDegree ≤ 8 * n - 2 * g := by
    compute_degree
    omega
  have hdB : (derivative B).natDegree ≤ 3 * n - g - 1 :=
    (natDegree_derivative_le B).trans (by omega)
  have hdA : (derivative A).natDegree ≤ 2 * n - 1 :=
    (natDegree_derivative_le A).trans (by omega)
  have hAB2 := natDegree_mul_le_of_le hA hB2
  have hAB2d := natDegree_mul_le_of_le hAB2 hdB
  have hA3 := natDegree_mul_le_of_le hdA hB3
  have hBc2 := natDegree_mul_le_of_le hB hc2
  have hdBc2 := natDegree_derivative_le (B * c ^ 2)
  refine ⟨by omega, by omega, by omega⟩

set_option maxHeartbeats 2000000 in
theorem residualRowTwoInner_Bd_degree_le68_of_alphaWall
    (B d : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g) (hwall : g = n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hd : d.natDegree ≤ 5 * n - h) :
    (derivative (B ^ 2 * d)).natDegree ≤ 11 * n - 2 * g - h - 1 := by
  have hB2 : (B ^ 2).natDegree ≤ 6 * n - 2 * g := by
    compute_degree
    omega
  have hprod := natDegree_mul_le_of_le hB2 hd
  have hsum : 6 * n - 2 * g + (5 * n - h) = 11 * n - 2 * g - h := by omega
  rw [hsum] at hprod
  have hder := natDegree_derivative_le (B ^ 2 * d)
  omega

set_option maxHeartbeats 4000000 in
/-- On `g = n` the left residual index still sits strictly above the cubic
load.  The ordinary `d e` coefficient survives. -/
theorem residualRowTwo_coeff_leftChamber68_of_alphaWall
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hwall : g = n) (hleft : 2 * h < 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualIncidenceQ68 B c d e).natDegree < 9 * n - 3 * g) :
    (secondaryResidualRowTwoPolynomial68 A B c d e).coeff
        (11 * n - 2 * h - 1) =
      (8 / 3 : k) * ((11 * n - 2 * h : ℕ) : k) *
        d.coeff (5 * n - h) * e.coeff (6 * n - h) := by
  let Q := residualIncidenceQ68 B c d e
  let inner := residualRowTwoInner68 A B c d e
  set idx := 11 * n - 2 * h - 1
  have hidx : 11 * n - 3 * g - 1 < idx := by
    dsimp [idx]
    omega
  have hQdeg := residualRowTwoInner_Q_degree_lt68_of_alphaWall A B c d e n g
    hn hwall hA hQ
  have hAQ : (A * derivative Q).natDegree < idx := hQdeg.1.trans hidx
  have hAQ' : (derivative A * Q).natDegree < idx := hQdeg.2.trans hidx
  have hcore := residualRowTwoInner_BcCore_degree_le68_of_alphaWall A B c n g
    hg hwall hA hB hc
  have hAB : (A * B ^ 2 * derivative B).natDegree < idx :=
    hcore.1.trans_lt hidx
  have hA3 : (derivative A * B ^ 3).natDegree < idx :=
    hcore.2.1.trans_lt hidx
  have hBc : (derivative (B * c ^ 2)).natDegree < idx :=
    hcore.2.2.trans_lt hidx
  have hBd := residualRowTwoInner_Bd_degree_le68_of_alphaWall B d n g h
    hg hgh hh hwall hB hd
  have hBd' : (derivative (B ^ 2 * d)).natDegree < idx := by
    dsimp [idx]
    omega
  have hide : (5 * n - h) + (6 * n - h) = 11 * n - 2 * h := by omega
  have hdecoeff := coeff_mul_at_bounds68 d e (5 * n - h) (6 * n - h) hd he
  rw [hide] at hdecoeff
  have hder0 : 0 < 11 * n - 2 * h := by omega
  have hde := coeff_derivative_at_bound68 (d * e) (11 * n - 2 * h) hder0
  rw [hdecoeff] at hde
  have h0Q : ((-6 : k) • (A * derivative Q)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hAQ, mul_zero]
  have h0Q' : ((3 : k) • (derivative A * Q)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hAQ', mul_zero]
  have h0AB : ((-2 : k) • (A * B ^ 2 * derivative B)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hAB, mul_zero]
  have h0A3 : ((-2 / 3 : k) • (derivative A * B ^ 3)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hA3, mul_zero]
  have h0Bd : ((6 : k) • derivative (B ^ 2 * d)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hBd', mul_zero]
  have h0Bc : ((6 : k) • derivative (B * c ^ 2)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hBc, mul_zero]
  have hde' : ((-18 : k) • derivative (d * e)).coeff idx =
      (-18 : k) * (d.coeff (5 * n - h) * e.coeff (6 * n - h) *
        ((11 * n - 2 * h : ℕ) : k)) := by
    rw [coeff_smul, smul_eq_mul]
    dsimp [idx]
    rw [hde]
  have hinner : inner.coeff idx =
      (-18 : k) * (d.coeff (5 * n - h) * e.coeff (6 * n - h) *
        ((11 * n - 2 * h : ℕ) : k)) := by
    dsimp [inner, residualRowTwoInner68]
    simp only [coeff_add]
    rw [h0Q, h0Q', h0AB, h0A3, h0Bd, h0Bc, hde']
    ring
  rw [residualRowTwo_eq_inner68, coeff_smul, smul_eq_mul]
  change ((-4 / 27 : k) * inner.coeff idx) = _
  rw [hinner]
  ring

theorem residualRowTwo_leftChamber_ne_zero68_of_alphaWall
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hwall : g = n) (hleft : 2 * h < 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualIncidenceQ68 B c d e).natDegree < 9 * n - 3 * g)
    (hd0 : d.coeff (5 * n - h) ≠ 0)
    (he0 : e.coeff (6 * n - h) ≠ 0) :
    (secondaryResidualRowTwoPolynomial68 A B c d e).coeff
        (11 * n - 2 * h - 1) ≠ 0 := by
  rw [residualRowTwo_coeff_leftChamber68_of_alphaWall A B c d e n g h
    hn hg hgh hh hwall hleft hA hB hc hd he hQ]
  have hscalar : (8 / 3 : k) ≠ 0 := by norm_num
  have hN : ((11 * n - 2 * h : ℕ) : k) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by omega)
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hscalar hN) hd0) he0

set_option maxHeartbeats 2000000 in
theorem residualRowTwo_not_leftChamber68_of_alphaWall
    (A B c d e load : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hwall : g = n) (hleft : 2 * h < 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualIncidenceQ68 B c d e).natDegree < 9 * n - 3 * g)
    (hload : load.natDegree ≤ 11 * n - 3 * g - 1)
    (hsum : secondaryResidualRowTwoPolynomial68 A B c d e + load = 0)
    (hd0 : d.coeff (5 * n - h) ≠ 0)
    (he0 : e.coeff (6 * n - h) ≠ 0) :
    False := by
  have hidx : 11 * n - 3 * g - 1 < 11 * n - 2 * h - 1 := by omega
  have hload' : load.natDegree < 11 * n - 2 * h - 1 :=
    hload.trans_lt hidx
  have hcoeff0 := residualRowTwo_coeff_eq_zero_of_loadCutoff68_of_alphaWall
    A B c d e load (11 * n - 2 * h - 1) hload' hsum
  exact residualRowTwo_leftChamber_ne_zero68_of_alphaWall A B c d e n g h
    hn hg hgh hh hwall hleft hA hB hc hd he hQ hd0 he0 hcoeff0

/-! ## Canonical expanded transport -/

set_option maxHeartbeats 4000000 in
/-- On the canonical expanded system, after `l = 0` on `g = n`, the cubic
residual row-two load is `(5 n / 18) beta a^4`. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_alphaWallRowTwoCubicLoad68
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
      g = n) :
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
    l = 0 ∧
      (cubicLoadRowTwoPolynomial68 l alpha beta gamma delta epsilon zeta eta
        Ae Be ce De ee).coeff (11 * n - 3 * g - 1) =
        alphaWallRowTwoLoadScalar68 (n : k) (Ae.coeff (2 * n)) beta ∧
      (secondaryResidualRowTwoPolynomial68 Ae Be ce d ee).coeff
          (11 * n - 3 * g - 1) =
        -alphaWallRowTwoLoadScalar68 (n : k) (Ae.coeff (2 * n)) beta := by
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
  change g = n at hwall
  change l = 0 ∧
    (cubicLoadRowTwoPolynomial68 l alpha beta gamma delta epsilon zeta eta
      Ae Be ce De ee).coeff (11 * n - 3 * g - 1) =
      alphaWallRowTwoLoadScalar68 (n : k) (Ae.coeff (2 * n)) beta ∧
    (secondaryResidualRowTwoPolynomial68 Ae Be ce d ee).coeff
        (11 * n - 3 * g - 1) =
      -alphaWallRowTwoLoadScalar68 (n : k) (Ae.coeff (2 * n)) beta
  have hclass :=
    maximalExpandedIntegratedPolynomialLowerSystem_alphaWallClassified68_of_wall
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
  change l = 0 ∧ ee.coeff (6 * n - g) = 0 ∧
    Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
      3 * De.coeff (5 * n - g) at hclass
  have hl : l = 0 := hclass.1
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
  have hD : De.natDegree ≤ 5 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
      hsecondary.2.2.2.1
  have he : ee.natDegree ≤ 6 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
      hsecondary.2.2.2.2.1
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec :
      Ee = (1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using
      cubicEDefectPolynomial68_eq_cubicCoordinates Ae Ce Ee
  have hDrec : De = (1 / 3 : k) • (Ae * Be) + d := by
    simpa only [d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
  have hload := cubicLoadRowTwoPolynomial68_coeff_cubicFace_of_alphaWall
    l alpha beta gamma delta epsilon zeta eta Ae Be ce De ee n g
    hn hg hl hwall hA hB hc hD he
  have h2e : lowerRowTwoPolynomial68
      (integratedSPolynomial68 l alpha beta delta Ae Be Ce De)
      (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) Be Ce De Ee = 0 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_lowerRowTwoPolynomial68_of_system
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
  rw [hCrec, hDrec, hErec] at h2e
  have hres := cubicRowTwoPolynomial68_residualSplit
    l alpha beta gamma delta epsilon zeta eta Ae Be ce d ee
  have hsum :
      secondaryResidualRowTwoPolynomial68 Ae Be ce d ee +
        cubicLoadRowTwoPolynomial68 l alpha beta gamma delta epsilon zeta eta
          Ae Be ce ((1 / 3 : k) • (Ae * Be) + d) ee = 0 := by
    simpa using hres.symm.trans h2e
  have hmix := polynomialSecondaryResidualRowTwo_coeff_cubicFace_of_alphaWall
    l alpha beta gamma delta epsilon zeta eta Ae Be ce d ee n g
    hn hg hl hwall hA hB hc (by simpa only [hDrec] using hD) he hsum
  exact ⟨hl, hload, hmix⟩

#print axioms cubicLoadRowTwoPolynomial68_coeff_cubicFace_of_alphaWall
#print axioms polynomialSecondaryResidualRowTwo_coeff_cubicFace_of_alphaWall
#print axioms residualRowTwo_coeff_leftChamber68_of_alphaWall
#print axioms residualRowTwo_not_leftChamber68_of_alphaWall
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_alphaWallRowTwoCubicLoad68

end AlphaWallRowTwoLoad68

end Max11DegreeRoutes
