import LowScale68SecondaryAlphaWallEndgame
import LowScale68SecondaryResidualRowOneSystem

/-! # Cubic residual row-one load on the alpha wall `g = n`

The leftover after the two vanishing `alpha` cores meets the cubic
residual index `12n-3g-1 = 9n-1`.  The four products that attain that
index cancel, so the leftover coefficient is zero and the load sits
strictly below the cubic residual face.  After `l = 0` the canonical
second one-form at this index is the ordinary residual row-one
polynomial.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlphaWallRowOneLoad68

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Local degree helpers -/

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

private theorem natDegree_smul_le_of_le68 (r : k) {p : k[X]} {n : ℕ}
    (hp : p.natDegree ≤ n) : (r • p).natDegree ≤ n :=
  (natDegree_smul_le r p).trans hp

private theorem natDegree_add_le_of_le68 {p q : k[X]} {n : ℕ}
    (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n) :
    (p + q).natDegree ≤ n :=
  (natDegree_add_le p q).trans (max_le hp hq)

private theorem natDegree_sub_le_of_le68 {p q : k[X]} {n : ℕ}
    (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n) :
    (p - q).natDegree ≤ n :=
  (natDegree_sub_le p q).trans (max_le hp hq)

private theorem natDegree_lt_of_le_of_coeff_eq_zero
    (p : k[X]) (m : ℕ) (hm : 0 < m)
    (hdeg : p.natDegree ≤ m) (hcoeff : p.coeff m = 0) :
    p.natDegree < m := by
  by_cases hp : p = 0
  · simpa [hp, natDegree_zero] using hm
  · have hne : p.natDegree ≠ m := by
      intro h
      have hlead : p.coeff p.natDegree ≠ 0 :=
        leadingCoeff_ne_zero.mpr hp
      rw [h] at hlead
      exact hlead hcoeff
    omega

/-! ## Termwise leftover bound `≤ 9n-1` on the wall -/

set_option maxHeartbeats 4000000 in
theorem cubicLoadRowOneAlphaRestPolynomial68_degree_le_cubicFace_of_alphaWall
    (alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hwall : g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadRowOneAlphaRestPolynomial68 alpha beta gamma delta epsilon
      zeta eta A B c D e).natDegree ≤ 12 * n - 3 * g - 1 := by
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
  have h1 : (Ur * derivative D).natDegree ≤ 12 * n - 3 * g - 1 := by
    have h := natDegree_mul_derivative_le_add_sub68 Ur D (4 * n) (5 * n - g)
      (by omega) hUr hD
    have hi : 4 * n + (5 * n - g) - 1 ≤ 12 * n - 3 * g - 1 := by omega
    exact h.trans hi
  have h2 : (Tc * derivative Er).natDegree ≤ 12 * n - 3 * g - 1 := by
    have h := natDegree_mul_derivative_le_add_sub68 Tc Er (4 * n) (6 * n - g)
      (by omega) hTc hEr
    have hi : 4 * n + (6 * n - g) - 1 ≤ 12 * n - 3 * g - 1 := by omega
    exact h.trans hi
  have h3 : (Tr * derivative E).natDegree ≤ 12 * n - 3 * g - 1 := by
    have h := natDegree_mul_derivative_le_add_sub68 Tr E (4 * n - g) (6 * n)
      (by omega) hTr hE
    have hi : (4 * n - g) + 6 * n - 1 ≤ 12 * n - 3 * g - 1 := by omega
    exact h.trans hi
  have h4 : (C0c * derivative Vr).natDegree ≤ 12 * n - 3 * g - 1 := by
    have h := natDegree_mul_derivative_le_add_sub68 C0c Vr (4 * n) (6 * n - g)
      (by omega) hC0c hVr
    have hi : 4 * n + (6 * n - g) - 1 ≤ 12 * n - 3 * g - 1 := by omega
    exact h.trans hi
  have h5 : (c * derivative V).natDegree ≤ 12 * n - 3 * g - 1 := by
    have h := natDegree_mul_derivative_le_add_sub68 c V (4 * n - g) (6 * n)
      (by omega) hc hV
    have hi : (4 * n - g) + 6 * n - 1 ≤ 12 * n - 3 * g - 1 := by omega
    exact h.trans hi
  have h6 : (D * derivative Ur).natDegree ≤ 12 * n - 3 * g - 1 := by
    have h := natDegree_mul_derivative_le_add_sub68 D Ur (5 * n - g) (4 * n)
      (by omega) hD hUr
    have hi : (5 * n - g) + 4 * n - 1 ≤ 12 * n - 3 * g - 1 := by omega
    exact h.trans hi
  change (Ur * derivative D +
      (2 : k) • (Tc * derivative Er) +
      (2 : k) • (Tr * derivative E) -
      (2 : k) • (C0c * derivative Vr) -
      (2 : k) • (c * derivative V) -
      D * derivative Ur).natDegree ≤ _
  refine natDegree_sub_le_of_le68
    (natDegree_sub_le_of_le68
      (natDegree_sub_le_of_le68
        (natDegree_add_le_of_le68
          (natDegree_add_le_of_le68 h1
            (natDegree_smul_le_of_le68 (2 : k) h2))
          (natDegree_smul_le_of_le68 (2 : k) h3))
        (natDegree_smul_le_of_le68 (2 : k) h4))
      (natDegree_smul_le_of_le68 (2 : k) h5)) h6

/-! ## Leading coefficients of the four attaining products -/

set_option maxHeartbeats 2000000 in
theorem cubicLoadTAlphaCorePolynomial68_coeff_fourRadius
    (alpha : k) (A : k[X]) (n : ℕ) (hA : A.natDegree ≤ 2 * n) :
    (cubicLoadTAlphaCorePolynomial68 alpha A).coeff (4 * n) =
      (1 / 3 * alpha : k) * A.coeff (2 * n) ^ 2 := by
  have hA2 := coeff_pow_at_bound68 A (2 * n) 2 hA
  have hi : 2 * (2 * n) = 4 * n := by omega
  rw [hi] at hA2
  simp only [cubicLoadTAlphaCorePolynomial68, coeff_smul, smul_eq_mul, hA2]

set_option maxHeartbeats 2000000 in
theorem cubicLoadTAlphaRestPolynomial68_coeff_cubicFace_of_alphaWall
    (alpha beta gamma epsilon : k) (A B c : k[X]) (n g : ℕ)
    (hn : 0 < n) (hwall : g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g) :
    (cubicLoadTAlphaRestPolynomial68 alpha beta gamma epsilon A B c).coeff
        (4 * n - g) =
      alpha * c.coeff (4 * n - g) := by
  have hBlt : B.natDegree < 4 * n - g := by omega
  have hAlt : A.natDegree < 4 * n - g := by omega
  have hC : (C epsilon).coeff (4 * n - g) = 0 := by
    have hnz : 4 * n - g ≠ 0 := by omega
    simp [coeff_C, hnz]
  simp only [cubicLoadTAlphaRestPolynomial68, coeff_add, coeff_smul,
    smul_eq_mul, coeff_eq_zero_of_natDegree_lt hBlt,
    coeff_eq_zero_of_natDegree_lt hAlt, hC, mul_zero, add_zero]

set_option maxHeartbeats 2000000 in
theorem cubicLoadVAlphaCorePolynomial68_coeff_sixRadius
    (alpha : k) (A : k[X]) (n : ℕ) (hA : A.natDegree ≤ 2 * n) :
    (cubicLoadVAlphaCorePolynomial68 alpha A).coeff (6 * n) =
      (1 / 27 * alpha : k) * A.coeff (2 * n) ^ 3 := by
  have hA3 := coeff_pow_at_bound68 A (2 * n) 3 hA
  have hi : 3 * (2 * n) = 6 * n := by omega
  rw [hi] at hA3
  simp only [cubicLoadVAlphaCorePolynomial68, coeff_smul, smul_eq_mul, hA3]

set_option maxHeartbeats 2000000 in
theorem cubicLoadVAlphaRestPolynomial68_coeff_fiveRadius_of_alphaWall
    (alpha beta gamma delta epsilon eta : k) (A B c D e : k[X])
    (n g : ℕ) (hn : 0 < n) (hwall : g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadVAlphaRestPolynomial68 alpha beta gamma delta epsilon eta
      A B c D e).coeff (6 * n - g) =
      (1 / 3 * alpha : k) * A.coeff (2 * n) * c.coeff (4 * n - g) +
        alpha * e.coeff (6 * n - g) := by
  have hAc := coeff_mul_at_bounds68 A c (2 * n) (4 * n - g) hA hc
  have hAci : 2 * n + (4 * n - g) = 6 * n - g := by omega
  rw [hAci] at hAc
  have hABlt : (A * B).natDegree < 6 * n - g := by compute_degree; omega
  have hDlt : D.natDegree < 6 * n - g := by omega
  have hA2lt : (A ^ 2).natDegree < 6 * n - g := by compute_degree; omega
  have hclt : c.natDegree < 6 * n - g := by omega
  have hBlt : B.natDegree < 6 * n - g := by omega
  have hAlt : A.natDegree < 6 * n - g := by omega
  have hC : (C eta).coeff (6 * n - g) = 0 := by
    have hnz : 6 * n - g ≠ 0 := by omega
    simp [coeff_C, hnz]
  simp only [cubicLoadVAlphaRestPolynomial68, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul, hAc,
    coeff_eq_zero_of_natDegree_lt hABlt, coeff_eq_zero_of_natDegree_lt hDlt,
    coeff_eq_zero_of_natDegree_lt hA2lt, coeff_eq_zero_of_natDegree_lt hclt,
    coeff_eq_zero_of_natDegree_lt hBlt, coeff_eq_zero_of_natDegree_lt hAlt,
    hC, mul_zero, add_zero, sub_zero]
  ring

/-! ## Vanishing leftover coefficient at `12n-3g-1` -/

set_option maxHeartbeats 4000000 in
/-- The four attaining leftover products cancel at the cubic residual
index on `g = n`. -/
theorem cubicLoadRowOneAlphaRestPolynomial68_coeff_cubicFace_of_alphaWall
    (alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hwall : g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadRowOneAlphaRestPolynomial68 alpha beta gamma delta epsilon
      zeta eta A B c D e).coeff (12 * n - 3 * g - 1) = 0 := by
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
  have hTcdeg : Tc.natDegree ≤ 4 * n :=
    cubicLoadTAlphaCorePolynomial68_degree_le alpha A n hA
  have hTrdeg : Tr.natDegree ≤ 4 * n - g :=
    cubicLoadTAlphaRestPolynomial68_degree_le alpha beta gamma epsilon
      A B c n g hn hwall hA hB hc
  have hUrdeg : Ur.natDegree ≤ 4 * n :=
    cubicLoadUAlphaRestPolynomial68_degree_le beta gamma delta zeta
      A B c n g hA hB hc
  have hVcdeg : Vc.natDegree ≤ 6 * n :=
    cubicLoadVAlphaCorePolynomial68_degree_le alpha A n hA
  have hVrdeg : Vr.natDegree ≤ 6 * n - g :=
    cubicLoadVAlphaRestPolynomial68_degree_le alpha beta gamma delta
      epsilon eta A B c D e n g hn hwall hA hB hc hD he
  have hVdeg : V.natDegree ≤ 6 * n :=
    (natDegree_add_le Vc Vr).trans (max_le hVcdeg (hVrdeg.trans (by omega)))
  have hC0cdeg : C0c.natDegree ≤ 4 * n := by
    simp only [C0c]; compute_degree; omega
  have hEcdeg : Ec.natDegree ≤ 6 * n := by
    simp only [Ec]; compute_degree; omega
  have hErdeg : Er.natDegree ≤ 6 * n - g := by
    simp only [Er]; compute_degree; omega
  have hEdeg : E.natDegree ≤ 6 * n :=
    (natDegree_add_le Ec Er).trans (max_le hEcdeg (hErdeg.trans (by omega)))
  have h1lt : (Ur * derivative D).natDegree < 12 * n - 3 * g - 1 := by
    have h := natDegree_mul_derivative_le_add_sub68 Ur D (4 * n) (5 * n - g)
      (by omega) hUrdeg hD
    have hi : 4 * n + (5 * n - g) - 1 < 12 * n - 3 * g - 1 := by omega
    exact h.trans_lt hi
  have h6lt : (D * derivative Ur).natDegree < 12 * n - 3 * g - 1 := by
    have h := natDegree_mul_derivative_le_add_sub68 D Ur (5 * n - g) (4 * n)
      (by omega) hD hUrdeg
    have hi : (5 * n - g) + 4 * n - 1 < 12 * n - 3 * g - 1 := by omega
    exact h.trans_lt hi
  have hTc := cubicLoadTAlphaCorePolynomial68_coeff_fourRadius alpha A n hA
  have hTr := cubicLoadTAlphaRestPolynomial68_coeff_cubicFace_of_alphaWall
    alpha beta gamma epsilon A B c n g hn hwall hA hB hc
  have hVc := cubicLoadVAlphaCorePolynomial68_coeff_sixRadius alpha A n hA
  have hVr := cubicLoadVAlphaRestPolynomial68_coeff_fiveRadius_of_alphaWall
    alpha beta gamma delta epsilon eta A B c D e n g hn hwall hA hB hc hD he
  have hAc := coeff_mul_at_bounds68 A c (2 * n) (4 * n - g) hA hc
  have hAci : 2 * n + (4 * n - g) = 6 * n - g := by omega
  rw [hAci] at hAc
  have hEr : Er.coeff (6 * n - g) =
      (1 / 3 : k) * A.coeff (2 * n) * c.coeff (4 * n - g) +
        e.coeff (6 * n - g) := by
    simp only [Er, coeff_add, coeff_smul, smul_eq_mul, hAc]
    ring
  have hA3 := coeff_pow_at_bound68 A (2 * n) 3 hA
  have hA3i : 3 * (2 * n) = 6 * n := by omega
  rw [hA3i] at hA3
  have hEc : Ec.coeff (6 * n) = (1 / 27 : k) * A.coeff (2 * n) ^ 3 := by
    simp only [Ec, coeff_smul, smul_eq_mul, hA3]
  have hErlt : Er.natDegree < 6 * n := by omega
  have hE : E.coeff (6 * n) = (1 / 27 : k) * A.coeff (2 * n) ^ 3 := by
    simp only [E, coeff_add, hEc, coeff_eq_zero_of_natDegree_lt hErlt, add_zero]
  have hVrlt : Vr.natDegree < 6 * n := by omega
  have hV : V.coeff (6 * n) = (1 / 27 * alpha : k) * A.coeff (2 * n) ^ 3 := by
    simp only [V, coeff_add, coeff_eq_zero_of_natDegree_lt hVrlt, add_zero]
    simpa only [Vc] using hVc
  have hA2 := coeff_pow_at_bound68 A (2 * n) 2 hA
  have hA2i : 2 * (2 * n) = 4 * n := by omega
  rw [hA2i] at hA2
  have hC0c : C0c.coeff (4 * n) = (1 / 3 : k) * A.coeff (2 * n) ^ 2 := by
    simp only [C0c, coeff_smul, smul_eq_mul, hA2]
  have hTc' : Tc.coeff (4 * n) =
      (1 / 3 * alpha : k) * A.coeff (2 * n) ^ 2 := by
    simpa only [Tc] using hTc
  have hTr' : Tr.coeff (4 * n - g) = alpha * c.coeff (4 * n - g) := by
    simpa only [Tr] using hTr
  have hVr' : Vr.coeff (6 * n - g) =
      (1 / 3 * alpha : k) * A.coeff (2 * n) * c.coeff (4 * n - g) +
        alpha * e.coeff (6 * n - g) := by
    simpa only [Vr] using hVr
  have h2 : ((2 : k) • (Tc * derivative Er)).coeff (12 * n - 3 * g - 1) =
      (2 : k) * Tc.coeff (4 * n) * Er.coeff (6 * n - g) *
        ((6 * n - g : ℕ) : k) := by
    have h := coeff_mul_derivative_at_bounds68 Tc Er (4 * n) (6 * n - g)
      (by omega) hTcdeg hErdeg
    have hi : 4 * n + (6 * n - g) - 1 = 12 * n - 3 * g - 1 := by omega
    rw [hi] at h
    rw [coeff_smul, smul_eq_mul, h]
    ring
  have h3 : ((2 : k) • (Tr * derivative E)).coeff (12 * n - 3 * g - 1) =
      (2 : k) * Tr.coeff (4 * n - g) * E.coeff (6 * n) *
        ((6 * n : ℕ) : k) := by
    have h := coeff_mul_derivative_at_bounds68 Tr E (4 * n - g) (6 * n)
      (by omega) hTrdeg hEdeg
    have hi : (4 * n - g) + 6 * n - 1 = 12 * n - 3 * g - 1 := by omega
    rw [hi] at h
    rw [coeff_smul, smul_eq_mul, h]
    ring
  have h4 : ((2 : k) • (C0c * derivative Vr)).coeff (12 * n - 3 * g - 1) =
      (2 : k) * C0c.coeff (4 * n) * Vr.coeff (6 * n - g) *
        ((6 * n - g : ℕ) : k) := by
    have h := coeff_mul_derivative_at_bounds68 C0c Vr (4 * n) (6 * n - g)
      (by omega) hC0cdeg hVrdeg
    have hi : 4 * n + (6 * n - g) - 1 = 12 * n - 3 * g - 1 := by omega
    rw [hi] at h
    rw [coeff_smul, smul_eq_mul, h]
    ring
  have h5 : ((2 : k) • (c * derivative V)).coeff (12 * n - 3 * g - 1) =
      (2 : k) * c.coeff (4 * n - g) * V.coeff (6 * n) *
        ((6 * n : ℕ) : k) := by
    have h := coeff_mul_derivative_at_bounds68 c V (4 * n - g) (6 * n)
      (by omega) hc hVdeg
    have hi : (4 * n - g) + 6 * n - 1 = 12 * n - 3 * g - 1 := by omega
    rw [hi] at h
    rw [coeff_smul, smul_eq_mul, h]
    ring
  have hcast5 : ((6 * n - g : ℕ) : k) = 6 * (n : k) - (g : k) := by
    rw [Nat.cast_sub (by omega : g ≤ 6 * n)]
    push_cast
    rfl
  have hcast6 : ((6 * n : ℕ) : k) = 6 * (n : k) := by
    push_cast
    rfl
  change (Ur * derivative D +
      (2 : k) • (Tc * derivative Er) +
      (2 : k) • (Tr * derivative E) -
      (2 : k) • (C0c * derivative Vr) -
      (2 : k) • (c * derivative V) -
      D * derivative Ur).coeff (12 * n - 3 * g - 1) = 0
  simp only [coeff_add, coeff_sub,
    coeff_eq_zero_of_natDegree_lt h1lt,
    coeff_eq_zero_of_natDegree_lt h6lt, h2, h3, h4, h5, add_zero, sub_zero]
  rw [hTc', hTr', hVr', hEr, hE, hV, hC0c, hcast5, hcast6, hwall]
  ring

set_option maxHeartbeats 2000000 in
theorem cubicLoadRowOneAlphaRestPolynomial68_degree_lt_cubicFace_of_alphaWall
    (alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hwall : g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadRowOneAlphaRestPolynomial68 alpha beta gamma delta epsilon
      zeta eta A B c D e).natDegree < 12 * n - 3 * g - 1 :=
  natDegree_lt_of_le_of_coeff_eq_zero _
    (12 * n - 3 * g - 1) (by omega)
    (cubicLoadRowOneAlphaRestPolynomial68_degree_le_cubicFace_of_alphaWall
      alpha beta gamma delta epsilon zeta eta A B c D e n g
      hn hg hwall hA hB hc hD he)
    (cubicLoadRowOneAlphaRestPolynomial68_coeff_cubicFace_of_alphaWall
      alpha beta gamma delta epsilon zeta eta A B c D e n g
      hn hg hwall hA hB hc hD he)

set_option maxHeartbeats 2000000 in
theorem cubicLoadRowOnePolynomial68_coeff_cubicFace_of_alphaWall
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hl : l = 0) (hwall : g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadRowOnePolynomial68 l alpha beta gamma delta epsilon zeta eta
      A B c D e).coeff (12 * n - 3 * g - 1) = 0 := by
  rw [cubicLoadRowOnePolynomial68_eq_alphaRest l alpha beta gamma delta
    epsilon zeta eta A B c D e hl]
  exact cubicLoadRowOneAlphaRestPolynomial68_coeff_cubicFace_of_alphaWall
    alpha beta gamma delta epsilon zeta eta A B c D e n g
    hn hg hwall hA hB hc hD he

set_option maxHeartbeats 2000000 in
theorem cubicLoadRowOnePolynomial68_degree_lt_cubicFace_of_alphaWall
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hl : l = 0) (hwall : g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadRowOnePolynomial68 l alpha beta gamma delta epsilon zeta eta
      A B c D e).natDegree < 12 * n - 3 * g - 1 := by
  rw [cubicLoadRowOnePolynomial68_eq_alphaRest l alpha beta gamma delta
    epsilon zeta eta A B c D e hl]
  exact cubicLoadRowOneAlphaRestPolynomial68_degree_lt_cubicFace_of_alphaWall
    alpha beta gamma delta epsilon zeta eta A B c D e n g
    hn hg hwall hA hB hc hD he

/-! ## Mixed canonical row-one face: load vanishes, residual remains -/

set_option maxHeartbeats 2000000 in
theorem cubicRowOnePolynomial68_coeff_cubicFace_of_alphaWall
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hl : l = 0) (hwall : g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicHomogeneousRowOnePolynomial68 A B c D e +
        cubicLoadRowOnePolynomial68 l alpha beta gamma delta epsilon zeta eta
          A B c D e).coeff (12 * n - 3 * g - 1) =
      (cubicHomogeneousRowOnePolynomial68 A B c D e).coeff
        (12 * n - 3 * g - 1) := by
  rw [coeff_add,
    cubicLoadRowOnePolynomial68_coeff_cubicFace_of_alphaWall
      l alpha beta gamma delta epsilon zeta eta A B c D e n g
      hn hg hl hwall hA hB hc hD he, add_zero]

set_option maxHeartbeats 2000000 in
/-- After `D = AB/3 + d`, the cubic residual index on `g = n` reads only
the residual second one-form. -/
theorem polynomialSecondaryResidualRowOne_coeff_cubicFace_of_alphaWall
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c d e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hl : l = 0) (hwall : g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (hD : ((1 / 3 : k) • (A * B) + d).natDegree ≤ 5 * n - g) :
    (secondaryResidualRowOnePolynomial68 A B c d e +
        cubicLoadRowOnePolynomial68 l alpha beta gamma delta epsilon zeta eta
          A B c ((1 / 3 : k) • (A * B) + d) e).coeff
            (12 * n - 3 * g - 1) =
      (secondaryResidualRowOnePolynomial68 A B c d e).coeff
        (12 * n - 3 * g - 1) := by
  rw [coeff_add,
    cubicLoadRowOnePolynomial68_coeff_cubicFace_of_alphaWall
      l alpha beta gamma delta epsilon zeta eta A B c
      ((1 / 3 : k) • (A * B) + d) e n g
      hn hg hl hwall hA hB hc hD he, add_zero]

set_option maxHeartbeats 4000000 in
/-- On the canonical expanded system, after `l = 0` on `g = n`, the cubic
residual index of row one is the residual second one-form. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_alphaWallRowOneCubicFace68
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
      (secondaryResidualRowOnePolynomial68 Ae Be ce d ee).coeff
          (12 * n - 3 * g - 1) = 0 := by
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
    (secondaryResidualRowOnePolynomial68 Ae Be ce d ee).coeff
        (12 * n - 3 * g - 1) = 0
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
  have h1e : lowerRowOnePolynomial68
      (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) Ce De Ee = 0 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_lowerRowOnePolynomial68_of_system
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
  rw [hCrec, hDrec, hErec] at h1e
  have hres := cubicRowOnePolynomial68_residualSplit
    l alpha beta gamma delta epsilon zeta eta Ae Be ce d ee
  have hsum :
      secondaryResidualRowOnePolynomial68 Ae Be ce d ee +
        cubicLoadRowOnePolynomial68 l alpha beta gamma delta epsilon zeta eta
          Ae Be ce ((1 / 3 : k) • (Ae * Be) + d) ee = 0 := by
    simpa using hres.symm.trans h1e
  have hload0 := cubicLoadRowOnePolynomial68_coeff_cubicFace_of_alphaWall
    l alpha beta gamma delta epsilon zeta eta Ae Be ce De ee n g
    hn hg hl hwall hA hB hc hD he
  have hload0' :
      (cubicLoadRowOnePolynomial68 l alpha beta gamma delta epsilon zeta eta
        Ae Be ce ((1 / 3 : k) • (Ae * Be) + d) ee).coeff
          (12 * n - 3 * g - 1) = 0 := by
    simpa only [hDrec] using hload0
  have hcoeff := congrArg
    (fun p : k[X] => p.coeff (12 * n - 3 * g - 1)) hsum
  simp only [coeff_add, hload0', add_zero] at hcoeff
  exact ⟨hl, hcoeff⟩

#print axioms cubicLoadRowOneAlphaRestPolynomial68_coeff_cubicFace_of_alphaWall
#print axioms cubicLoadRowOneAlphaRestPolynomial68_degree_lt_cubicFace_of_alphaWall
#print axioms cubicLoadRowOnePolynomial68_coeff_cubicFace_of_alphaWall
#print axioms cubicLoadRowOnePolynomial68_degree_lt_cubicFace_of_alphaWall
#print axioms cubicRowOnePolynomial68_coeff_cubicFace_of_alphaWall
#print axioms polynomialSecondaryResidualRowOne_coeff_cubicFace_of_alphaWall
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_alphaWallRowOneCubicFace68

end AlphaWallRowOneLoad68

end Max11DegreeRoutes
