import LowScale68SecondaryAlphaWall
import LowScale68SecondaryLargeGapLoadZeroFace

/-! # First secondary face after `l = 0` throughout `2g < 3n`

In the remaining H=0 deep region `g > n`, the hypothesis `n < 2g` is free,
so `l = 0`.  The naive row-one load bound uses the cancelled `alpha`
cores at `10n-1` and therefore stops at `g < n`.  After those cores are
removed, the surviving rest has degree at most `10n-g-1`, which lies
strictly below the first-face index `12n-2g-1` throughout `g < 2n`.  The
invariant window `2g < 3n` is contained in `g < 2n`, so the ordinary
five-face `e = 0`, `a*b = 3 D_top` is available on the whole open
interval `n/2 < g < 3n/2`, with no extra vanishing of `alpha`.

Feasible numerical split of `g > n` after `l = 0`:

* `n < g < 3n/2`: this module (first face load-free after alpha-core
  cancellation).
* `g = 3n/2`: mixed I4, `beta A^3` meets `9n-2g = 6n`.
* `3n/2 < g < 5n/2`: tracked `beta = 0`, then `delta A^2` at `4n` is
  still below `9n-2g`.
* `g = 5n/2`: mixed I4 with `delta A^2`.
* `g > 5n/2`: next pure I4 load is exposed.

Alpha cores `T_core E_core'` and `C0_core V_core'` (and `U_core D'`)
vanish identically.  They do **not** survive as a leading form on
`g > n`.  The rest is off the first face precisely when `g < 2n`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section DeepGapCascade68

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Chamber arithmetic -/

theorem deepGap_gap_lt_two_radius
    (n g : ℕ) (hn : 0 < n) (hrel : 2 * g < 3 * n) :
    g < 2 * n := by
  omega

theorem deepGap_index_pos (n g : ℕ) (hn : 0 < n)
    (hrel : 2 * g < 3 * n) {w : ℕ} (hw : 1 < w) :
    0 < w * n - g := by
  have hg_lt : g < 2 * n := deepGap_gap_lt_two_radius n g hn hrel
  have h2 : 2 * n ≤ w * n := by
    have : 2 ≤ w := Nat.succ_le_of_lt hw
    simpa [Nat.mul_comm n] using Nat.mul_le_mul_left n this
  exact Nat.sub_pos_of_lt (lt_of_lt_of_le hg_lt h2)

/-! ## Local derivative-degree helpers (AlphaWall copies are file-private) -/

theorem deepGap_natDegree_mul_derivative_le_add_sub68
    (p q : k[X]) (u v : ℕ) (hv : 0 < v)
    (hp : p.natDegree ≤ u) (hq : q.natDegree ≤ v) :
    (p * derivative q).natDegree ≤ u + v - 1 := by
  have hd : (derivative q).natDegree ≤ v - 1 :=
    (natDegree_derivative_le q).trans (Nat.sub_le_sub_right hq 1)
  have hsum : p.natDegree + (derivative q).natDegree ≤ u + (v - 1) :=
    Nat.add_le_add hp hd
  have hidx : u + (v - 1) = u + v - 1 := by omega
  exact natDegree_mul_le.trans (hidx ▸ hsum)

theorem deepGap_natDegree_mul_derivative_lt68
    (p q : k[X]) (u v bound : ℕ) (hv : 0 < v)
    (hp : p.natDegree ≤ u) (hq : q.natDegree ≤ v)
    (huv : u + v - 1 < bound) :
    (p * derivative q).natDegree < bound :=
  (deepGap_natDegree_mul_derivative_le_add_sub68
    p q u v hv hp hq).trans_lt huv

theorem deepGap_natDegree_smul_lt68
    (r : k) {p : k[X]} {n : ℕ} (hp : p.natDegree < n) :
    (r • p).natDegree < n :=
  (natDegree_smul_le r p).trans_lt hp

theorem deepGap_natDegree_add_lt
    {p q : k[X]} {n : ℕ}
    (hp : p.natDegree < n) (hq : q.natDegree < n) :
    (p + q).natDegree < n :=
  (natDegree_add_le p q).trans_lt (max_lt hp hq)

theorem deepGap_natDegree_sub_lt
    {p q : k[X]} {n : ℕ}
    (hp : p.natDegree < n) (hq : q.natDegree < n) :
    (p - q).natDegree < n :=
  (natDegree_sub_le p q).trans_lt (max_lt hp hq)

/-! ## Alpha-rest degree bounds on `2g < 3n` -/

set_option maxHeartbeats 2000000 in
theorem cubicLoadTAlphaRestPolynomial68_degree_le_of_two_mul_gap_lt_three
    (alpha beta gamma epsilon : k) (A B c : k[X]) (n g : ℕ)
    (hn : 0 < n) (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g) :
    (cubicLoadTAlphaRestPolynomial68 alpha beta gamma epsilon A B c).natDegree ≤
      4 * n - g := by
  have hg2 : g < 2 * n := deepGap_gap_lt_two_radius n g hn hrel
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
  exact max_le
    ((natDegree_add_le _ _).trans (max_le
      ((natDegree_add_le _ _).trans (max_le hAc hB')) hA')) hC

set_option maxHeartbeats 2000000 in
theorem cubicLoadVAlphaRestPolynomial68_degree_le_of_two_mul_gap_lt_three
    (alpha beta gamma delta epsilon eta : k) (A B c D e : k[X])
    (n g : ℕ) (hn : 0 < n) (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadVAlphaRestPolynomial68 alpha beta gamma delta epsilon eta
      A B c D e).natDegree ≤ 6 * n - g := by
  have hg2 : g < 2 * n := deepGap_gap_lt_two_radius n g hn hrel
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
  refine (natDegree_add_le _ _).trans (max_le ?_ hC)
  refine (natDegree_add_le _ _).trans (max_le ?_ hA')
  refine (natDegree_add_le _ _).trans (max_le ?_ hB')
  refine (natDegree_add_le _ _).trans (max_le ?_ hc')
  refine (natDegree_add_le _ _).trans (max_le ?_ hA2)
  refine (natDegree_add_le _ _).trans (max_le ?_ hD')
  refine (natDegree_sub_le _ _).trans (max_le ?_ hAB)
  exact (natDegree_add_le _ _).trans (max_le hAc he')

set_option maxHeartbeats 4000000 in
/-- After the identical vanishing of the two `10n-1` alpha cores, the
surviving row-one rest sits at `10n-g-1`, strictly below the first-face
index `12n-2g-1` once `g < 2n`.  The invariant window `2g < 3n` is
contained in that comparison. -/
theorem cubicLoadRowOneAlphaRestPolynomial68_degree_lt_firstFace_of_two_mul_gap_lt_three
    (alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hrel : 2 * g < 3 * n)
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
  have hg2 : g < 2 * n := deepGap_gap_lt_two_radius n g hn hrel
  have hTc : Tc.natDegree ≤ 4 * n :=
    cubicLoadTAlphaCorePolynomial68_degree_le alpha A n hA
  have hTr : Tr.natDegree ≤ 4 * n - g :=
    cubicLoadTAlphaRestPolynomial68_degree_le_of_two_mul_gap_lt_three
      alpha beta gamma epsilon A B c n g hn hrel hA hB hc
  have hUr : Ur.natDegree ≤ 4 * n :=
    cubicLoadUAlphaRestPolynomial68_degree_le beta gamma delta zeta
      A B c n g hA hB hc
  have hVc : Vc.natDegree ≤ 6 * n :=
    cubicLoadVAlphaCorePolynomial68_degree_le alpha A n hA
  have hVr : Vr.natDegree ≤ 6 * n - g :=
    cubicLoadVAlphaRestPolynomial68_degree_le_of_two_mul_gap_lt_three
      alpha beta gamma delta epsilon eta A B c D e n g
      hn hrel hA hB hc hD he
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
      deepGap_natDegree_mul_derivative_lt68 p q u v
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
  have h2s := deepGap_natDegree_smul_lt68 (2 : k) h2
  have h3s := deepGap_natDegree_smul_lt68 (2 : k) h3
  have h4s := deepGap_natDegree_smul_lt68 (2 : k) h4
  have h5s := deepGap_natDegree_smul_lt68 (2 : k) h5
  change (Ur * derivative D +
      (2 : k) • (Tc * derivative Er) +
      (2 : k) • (Tr * derivative E) -
      (2 : k) • (C0c * derivative Vr) -
      (2 : k) • (c * derivative V) -
      D * derivative Ur).natDegree < _
  exact deepGap_natDegree_sub_lt
    (deepGap_natDegree_sub_lt
      (deepGap_natDegree_sub_lt
        (deepGap_natDegree_add_lt
          (deepGap_natDegree_add_lt h1 h2s) h3s) h4s) h5s) h6

set_option maxHeartbeats 2000000 in
theorem cubicLoadRowOnePolynomial68_degree_lt_firstFace_of_deepGap
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hl : l = 0) (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadRowOnePolynomial68 l alpha beta gamma delta epsilon zeta eta
      A B c D e).natDegree < 12 * n - 2 * g - 1 := by
  rw [cubicLoadRowOnePolynomial68_eq_alphaRest l alpha beta gamma delta
    epsilon zeta eta A B c D e hl]
  exact cubicLoadRowOneAlphaRestPolynomial68_degree_lt_firstFace_of_two_mul_gap_lt_three
    alpha beta gamma delta epsilon zeta eta A B c D e n g
    hn hg hrel hA hB hc hD he

set_option maxHeartbeats 3000000 in
theorem integratedLowerRowOnePolynomial68_secondaryCoeff_of_deepGap
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hl : l = 0) (hrel : 2 * g < 3 * n)
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
      (-8 / 81 : k) * firstSecondaryOne68 (n : k) (g : k)
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
        (e.coeff (6 * n - g)) := by
  have hcoords := integratedPolynomial68_cubicCoordinates
    l alpha beta gamma delta epsilon zeta eta A B c D e
  rw [hcoords.t_eq, hcoords.u_eq, hcoords.v_eq,
    cubicRowOnePolynomial68_split, coeff_add,
    coeff_eq_zero_of_natDegree_lt
      (cubicLoadRowOnePolynomial68_degree_lt_firstFace_of_deepGap
        l alpha beta gamma delta epsilon zeta eta A B c D e n g
        hn hg hl hrel hA hB hc hD he), add_zero]
  exact cubicHomogeneousRowOnePolynomial68_secondaryCoeff_of_two_mul_gap_lt_three
    A B c D e n g hn hg hrel hA hB hc hD he

set_option maxHeartbeats 3000000 in
theorem polynomialSecondaryFace68_of_deepGap
    (l alpha beta gamma delta epsilon zeta eta i4 i3 : k)
    (A B C0 c D E e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hl : l = 0) (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (ha : A.coeff (2 * n) ≠ 0)
    (hC0 : C0 = (1 / 3 : k) • A ^ 2 + c)
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
    (hrowOne : lowerRowOnePolynomial68
      (integratedTPolynomial68 l alpha beta gamma epsilon A B C0 D E)
      (integratedUPolynomial68 l alpha beta gamma delta zeta A B C0 D E)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        A B C0 D E) C0 D E = 0)
    (hrowZero : (lowerRowZeroPolynomial68
      (integratedUPolynomial68 l alpha beta gamma delta zeta A B C0 D E)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        A B C0 D E) D E).coeff (13 * n - 2 * g - 1) = 0) :
    FirstSecondaryFace68 (n : k) (g : k)
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
      (e.coeff (6 * n - g)) := by
  have hinv := polynomialSecondaryInvariantEquations68_of_loadL
    l beta gamma delta epsilon zeta i4 i3 A B C0 c D E e n g
    hn hg hl hrel hA hB hc hD he hC0 hE0 hI4 hI3
  have h2 := hrowTwo
  rw [hC0, hE0] at h2
  have htwo := congrArg
    (fun p : k[X] => p.coeff (11 * n - 2 * g - 1)) h2
  rw [integratedLowerRowTwoPolynomial68_secondaryCoeff_of_loadL
    l alpha beta gamma delta epsilon zeta eta A B c D e n g
    hn hg hl hrel hA hB hc hD he] at htwo
  simp only [coeff_zero] at htwo
  have htwo0 : firstSecondaryTwo68 (n : k) (g : k)
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
      (e.coeff (6 * n - g)) = 0 :=
    (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  have h1 := hrowOne
  rw [hC0, hE0] at h1
  have hone := congrArg
    (fun p : k[X] => p.coeff (12 * n - 2 * g - 1)) h1
  rw [integratedLowerRowOnePolynomial68_secondaryCoeff_of_deepGap
    l alpha beta gamma delta epsilon zeta eta A B c D e n g
    hn hg hl hrel hA hB hc hD he] at hone
  simp only [coeff_zero] at hone
  have hone0 : firstSecondaryOne68 (n : k) (g : k)
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
      (e.coeff (6 * n - g)) = 0 :=
    (mul_eq_zero.mp hone).resolve_left (by norm_num)
  have h0 := hrowZero
  rw [hC0, hE0] at h0
  rw [integratedLowerRowZeroPolynomial68_secondaryCoeff_of_loadL
    l alpha beta gamma delta epsilon zeta eta A B c D e n g
    hn hg hl hrel hA hB hc hD he] at h0
  have hncast : (n : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hfactor : (8 / 81 : k) * (n : k) * A.coeff (2 * n) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hncast) ha
  have hzero0 : firstSecondaryZero68
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
      (e.coeff (6 * n - g)) = 0 :=
    (mul_eq_zero.mp h0).resolve_left hfactor
  exact ⟨hinv.1, hinv.2, htwo0, hone0, hzero0⟩

theorem polynomialSecondaryClassified68_of_deepGap
    (l alpha beta gamma delta epsilon zeta eta i4 i3 : k)
    (A B C0 c D E e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hl : l = 0) (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (ha : A.coeff (2 * n) ≠ 0)
    (hC0 : C0 = (1 / 3 : k) • A ^ 2 + c)
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
    (hrowOne : lowerRowOnePolynomial68
      (integratedTPolynomial68 l alpha beta gamma epsilon A B C0 D E)
      (integratedUPolynomial68 l alpha beta gamma delta zeta A B C0 D E)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        A B C0 D E) C0 D E = 0)
    (hrowZero : (lowerRowZeroPolynomial68
      (integratedUPolynomial68 l alpha beta gamma delta zeta A B C0 D E)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        A B C0 D E) D E).coeff (13 * n - 2 * g - 1) = 0) :
    e.coeff (6 * n - g) = 0 ∧
      A.coeff (2 * n) * B.coeff (3 * n - g) =
        3 * D.coeff (5 * n - g) := by
  exact firstSecondaryFace68_classify_of_two_mul_gap_lt_three_mul_radius n g
    (A.coeff (2 * n)) (B.coeff (3 * n - g))
    (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
    (e.coeff (6 * n - g)) ha hn hrel
    (polynomialSecondaryFace68_of_deepGap
      l alpha beta gamma delta epsilon zeta eta i4 i3
      A B C0 c D E e n g hn hg hl hrel hA hB hc hD he ha hC0 hE0
      hI4 hI3 hrowTwo hrowOne hrowZero)

set_option maxHeartbeats 4000000 in
/-- After `l = 0`, the ordinary first secondary face is available
throughout the invariant window `2g < 3n`, with no extra vanishing of
`alpha` and no restriction `g < n`. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_firstSecondaryClassified68_of_deepGap
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hl : l = 0)
    (hrel :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      2 * g < 3 * n) :
    let n := weightedRadius68 A B C0 D E
    let Ae := expand k 60 A
    let Be := expand k 60 B
    let Ce := expand k 60 C0
    let ce := cubicCDefectPolynomial68 Ae Ce
    let De := expand k 60 D
    let Ee := expand k 60 E
    let ee := cubicEDefectPolynomial68 Ae Ce Ee
    let g := cubicDefectGap68 n Be ce De ee
    ee.coeff (6 * n - g) = 0 ∧
      Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
        3 * De.coeff (5 * n - g) := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  change 2 * g < 3 * n at hrel
  change ee.coeff (6 * n - g) = 0 ∧
    Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
      3 * De.coeff (5 * n - g)
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
  have ha : Ae.coeff (2 * n) ≠ 0 := by
    simpa only [n, Ae] using hcore.2.2.2.2.2
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec :
      Ee = (1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using
      cubicEDefectPolynomial68_eq_cubicCoordinates Ae Ce Ee
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
  have h1e : lowerRowOnePolynomial68
      (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) Ce De Ee = 0 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_lowerRowOnePolynomial68_of_system
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
        Ae Be Ce De Ee) De Ee).coeff (13 * n - 2 * g - 1) = 0 :=
    expand_lowerRowZeroPolynomial68_coeff_eq_zero_of_index_gt
      terminal _ _ _ _ _ h0e
      (firstSecondaryRowZeroIndex68_gt_fiftyNine n g hnlarge hrel)
  exact polynomialSecondaryClassified68_of_deepGap
    l alpha beta gamma delta epsilon zeta eta i4 i3
    Ae Be Ce ce De Ee ee n g hn hg hl hrel hA hB hc hD he ha
    hCrec hErec hi4e hi3e h2e h1e h0target

/-- On the canonical expanded system, `n < 2g` forces `l = 0` and
`2g < 3n` extracts the ordinary first face.  This is the open deep-gap
window `n/2 < g < 3n/2`. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_deepGapClassified68
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
      n < 2 * g ∧ 2 * g < 3 * n) :
    let n := weightedRadius68 A B C0 D E
    let Ae := expand k 60 A
    let Be := expand k 60 B
    let Ce := expand k 60 C0
    let ce := cubicCDefectPolynomial68 Ae Ce
    let De := expand k 60 D
    let Ee := expand k 60 E
    let ee := cubicEDefectPolynomial68 Ae Ce Ee
    let g := cubicDefectGap68 n Be ce De ee
    l = 0 ∧ ee.coeff (6 * n - g) = 0 ∧
      Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
        3 * De.coeff (5 * n - g) := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  change n < 2 * g ∧ 2 * g < 3 * n at hchamber
  change l = 0 ∧ ee.coeff (6 * n - g) = 0 ∧
    Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
      3 * De.coeff (5 * n - g)
  have hl :=
    maximalExpandedIntegratedPolynomialLowerSystem_l_eq_zero_of_radius_lt_twoGap68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hchamber.1)
  have hclass :=
    maximalExpandedIntegratedPolynomialLowerSystem_firstSecondaryClassified68_of_deepGap
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys hl (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hchamber.2)
  exact ⟨hl, hclass.1, hclass.2⟩

/-! ## Residual degree drop after the classified deep-gap face -/

theorem secondaryDDefectPolynomial68_degree_lt_of_deepGap
    (A B D : k[X]) (n g : ℕ) (hn : 0 < n) (hg : 0 < g)
    (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (hface : A.coeff (2 * n) * B.coeff (3 * n - g) =
      3 * D.coeff (5 * n - g)) :
    (secondaryDDefectPolynomial68 A B D).natDegree < 5 * n - g := by
  have hg3 : g ≤ 3 * n := by omega
  have hindex : 2 * n + (3 * n - g) = 5 * n - g := by
    rw [← Nat.add_sub_assoc hg3]
    omega
  have hdegree : (secondaryDDefectPolynomial68 A B D).natDegree ≤
      5 * n - g := by
    simp only [secondaryDDefectPolynomial68]
    refine (natDegree_sub_le _ _).trans ?_
    rw [sup_le_iff]
    constructor
    · exact hD
    · have hmul := (natDegree_mul_le (p := A) (q := B)).trans
        (Nat.add_le_add hA hB)
      have hsmul := (natDegree_smul_le (1 / 3 : k) (A * B)).trans hmul
      rwa [hindex] at hsmul
  have hAB := coeff_mul_at_bounds68 A B (2 * n) (3 * n - g) hA hB
  rw [hindex] at hAB
  have hcoeff : (secondaryDDefectPolynomial68 A B D).coeff
      (5 * n - g) = 0 := by
    simp only [secondaryDDefectPolynomial68, coeff_sub, coeff_smul,
      smul_eq_mul]
    rw [hAB]
    linear_combination (-1 / 3 : k) * hface
  exact natDegree_lt_of_le_of_coeff_eq_zero68 _
    (5 * n - g) (deepGap_index_pos n g hn hrel (by decide))
    hdegree hcoeff

theorem firstSecondaryResidualDegreeDrops68_of_deepGap
    (A B D e : k[X]) (n g : ℕ) (hn : 0 < n) (hg : 0 < g)
    (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (hface : A.coeff (2 * n) * B.coeff (3 * n - g) =
      3 * D.coeff (5 * n - g))
    (hetop : e.coeff (6 * n - g) = 0) :
    (secondaryDDefectPolynomial68 A B D).natDegree < 5 * n - g ∧
      e.natDegree < 6 * n - g := by
  refine ⟨secondaryDDefectPolynomial68_degree_lt_of_deepGap A B D n g
    hn hg hrel hA hB hD hface, ?_⟩
  exact natDegree_lt_of_le_of_coeff_eq_zero68 e (6 * n - g)
    (deepGap_index_pos n g hn hrel (by decide)) he hetop

theorem maximalExpandedIntegratedPolynomialLowerSystem_deepGapResidualDrops68
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
      n < 2 * g ∧ 2 * g < 3 * n) :
    let n := weightedRadius68 A B C0 D E
    let Ae := expand k 60 A
    let Be := expand k 60 B
    let Ce := expand k 60 C0
    let ce := cubicCDefectPolynomial68 Ae Ce
    let De := expand k 60 D
    let Ee := expand k 60 E
    let ee := cubicEDefectPolynomial68 Ae Ce Ee
    let g := cubicDefectGap68 n Be ce De ee
    l = 0 ∧
      (secondaryDDefectPolynomial68 Ae Be De).natDegree < 5 * n - g ∧
      ee.natDegree < 6 * n - g := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  change n < 2 * g ∧ 2 * g < 3 * n at hchamber
  change l = 0 ∧
    (secondaryDDefectPolynomial68 Ae Be De).natDegree < 5 * n - g ∧
    ee.natDegree < 6 * n - g
  have hclass :=
    maximalExpandedIntegratedPolynomialLowerSystem_deepGapClassified68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hchamber)
  change l = 0 ∧ ee.coeff (6 * n - g) = 0 ∧
    Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
      3 * De.coeff (5 * n - g) at hclass
  have hcore := maximalExpandedIntegratedPolynomialLowerSystem_cubicCore68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have hdrop :=
    maximalExpandedIntegratedPolynomialLowerSystem_degreeDrop68
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
  have hD : De.natDegree ≤ 5 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
      hsecondary.2.2.2.1
  have he : ee.natDegree ≤ 6 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
      hsecondary.2.2.2.2.1
  exact ⟨hclass.1,
    firstSecondaryResidualDegreeDrops68_of_deepGap Ae Be De ee n g
      hn hg hchamber.2 hA hB hD he hclass.2.2 hclass.2.1⟩

end DeepGapCascade68

#print axioms cubicLoadRowOnePolynomial68_degree_lt_firstFace_of_deepGap
#print axioms polynomialSecondaryClassified68_of_deepGap
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_firstSecondaryClassified68_of_deepGap
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_deepGapClassified68
#print axioms firstSecondaryResidualDegreeDrops68_of_deepGap
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_deepGapResidualDrops68

end Max11DegreeRoutes
