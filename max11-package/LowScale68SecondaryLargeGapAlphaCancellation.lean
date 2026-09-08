import LowScale68SecondaryAlphaWall

/-! # Exact row-one load cancellation below the alpha wall

After `l = 0`, the two pure `alpha` cores in the cubic row-one load cancel
identically.  The surviving alpha-rest terms have degree at most `10n-g-1`.
Consequently, throughout `g < n` they lie strictly below the residual cubic
face `12n-3g-1`.  This removes the artificial restriction `3g < 2n` from
the large-gap row-one load cutoff.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LargeGapAlphaCancellation68

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

private theorem largeGapAlpha_natDegree_mul_derivative_le_add_sub68
    (p q : k[X]) (u v : ℕ) (hv : 0 < v)
    (hp : p.natDegree ≤ u) (hq : q.natDegree ≤ v) :
    (p * derivative q).natDegree ≤ u + v - 1 := by
  have hd : (derivative q).natDegree ≤ v - 1 :=
    (natDegree_derivative_le q).trans (Nat.sub_le_sub_right hq 1)
  have hsum : p.natDegree + (derivative q).natDegree ≤ u + (v - 1) :=
    Nat.add_le_add hp hd
  have hidx : u + (v - 1) = u + v - 1 := by omega
  exact natDegree_mul_le.trans (hidx ▸ hsum)

private theorem largeGapAlpha_natDegree_mul_derivative_lt68
    (p q : k[X]) (u v bound : ℕ) (hv : 0 < v)
    (hp : p.natDegree ≤ u) (hq : q.natDegree ≤ v)
    (huv : u + v - 1 < bound) :
    (p * derivative q).natDegree < bound :=
  (largeGapAlpha_natDegree_mul_derivative_le_add_sub68
    p q u v hv hp hq).trans_lt huv

private theorem largeGapAlpha_natDegree_smul_lt68
    (r : k) {p : k[X]} {n : ℕ} (hp : p.natDegree < n) :
    (r • p).natDegree < n :=
  (natDegree_smul_le r p).trans_lt hp

private theorem largeGapAlpha_natDegree_add_lt68
    {p q : k[X]} {n : ℕ}
    (hp : p.natDegree < n) (hq : q.natDegree < n) :
    (p + q).natDegree < n :=
  (natDegree_add_le p q).trans_lt (max_lt hp hq)

private theorem largeGapAlpha_natDegree_sub_lt68
    {p q : k[X]} {n : ℕ}
    (hp : p.natDegree < n) (hq : q.natDegree < n) :
    (p - q).natDegree < n :=
  (natDegree_sub_le p q).trans_lt (max_lt hp hq)

set_option maxHeartbeats 2000000 in
theorem cubicLoadTAlphaRestPolynomial68_degree_le_of_gap_lt_radius
    (alpha beta gamma epsilon : k) (A B c : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgap : g < n)
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
  exact max_le
    ((natDegree_add_le _ _).trans (max_le
      ((natDegree_add_le _ _).trans (max_le hAc hB')) hA')) hC

set_option maxHeartbeats 2000000 in
theorem cubicLoadVAlphaRestPolynomial68_degree_le_of_gap_lt_radius
    (alpha beta gamma delta epsilon eta : k) (A B c D e : k[X])
    (n g : ℕ) (hn : 0 < n) (hg : 0 < g) (hgap : g < n)
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
  refine (natDegree_add_le _ _).trans (max_le ?_ hC)
  refine (natDegree_add_le _ _).trans (max_le ?_ hA')
  refine (natDegree_add_le _ _).trans (max_le ?_ hB')
  refine (natDegree_add_le _ _).trans (max_le ?_ hc')
  refine (natDegree_add_le _ _).trans (max_le ?_ hA2)
  refine (natDegree_add_le _ _).trans (max_le ?_ hD')
  refine (natDegree_sub_le _ _).trans (max_le ?_ hAB)
  exact (natDegree_add_le _ _).trans (max_le hAc he')

set_option maxHeartbeats 4000000 in
theorem cubicLoadRowOneAlphaRestPolynomial68_degree_lt_largeGap
    (alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgap : g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadRowOneAlphaRestPolynomial68 alpha beta gamma delta epsilon
      zeta eta A B c D e).natDegree < 12 * n - 3 * g - 1 := by
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
    cubicLoadTAlphaRestPolynomial68_degree_le_of_gap_lt_radius
      alpha beta gamma epsilon A B c n g hn hg hgap hA hB hc
  have hUr : Ur.natDegree ≤ 4 * n :=
    cubicLoadUAlphaRestPolynomial68_degree_le beta gamma delta zeta
      A B c n g hA hB hc
  have hVc : Vc.natDegree ≤ 6 * n :=
    cubicLoadVAlphaCorePolynomial68_degree_le alpha A n hA
  have hVr : Vr.natDegree ≤ 6 * n - g :=
    cubicLoadVAlphaRestPolynomial68_degree_le_of_gap_lt_radius
      alpha beta gamma delta epsilon eta A B c D e n g
      hn hg hgap hA hB hc hD he
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
      (hu : u + v - 1 < 12 * n - 3 * g - 1) :
      ∀ p q : k[X], p.natDegree ≤ u → q.natDegree ≤ v →
        (p * derivative q).natDegree < 12 * n - 3 * g - 1 :=
    fun p q hp hq =>
      largeGapAlpha_natDegree_mul_derivative_lt68 p q u v
        (12 * n - 3 * g - 1) hv hp hq hu
  have h1 : (Ur * derivative D).natDegree < 12 * n - 3 * g - 1 :=
    hbound (4 * n) (5 * n - g) (by omega) (by omega) Ur D hUr hD
  have h2 : (Tc * derivative Er).natDegree < 12 * n - 3 * g - 1 :=
    hbound (4 * n) (6 * n - g) (by omega) (by omega) Tc Er hTc hEr
  have h3 : (Tr * derivative E).natDegree < 12 * n - 3 * g - 1 :=
    hbound (4 * n - g) (6 * n) (by omega) (by omega) Tr E hTr hE
  have h4 : (C0c * derivative Vr).natDegree < 12 * n - 3 * g - 1 :=
    hbound (4 * n) (6 * n - g) (by omega) (by omega) C0c Vr hC0c hVr
  have h5 : (c * derivative V).natDegree < 12 * n - 3 * g - 1 :=
    hbound (4 * n - g) (6 * n) (by omega) (by omega) c V hc hV
  have h6 : (D * derivative Ur).natDegree < 12 * n - 3 * g - 1 :=
    hbound (5 * n - g) (4 * n) (by omega) (by omega) D Ur hD hUr
  have h2s := largeGapAlpha_natDegree_smul_lt68 (2 : k) h2
  have h3s := largeGapAlpha_natDegree_smul_lt68 (2 : k) h3
  have h4s := largeGapAlpha_natDegree_smul_lt68 (2 : k) h4
  have h5s := largeGapAlpha_natDegree_smul_lt68 (2 : k) h5
  change (Ur * derivative D +
      (2 : k) • (Tc * derivative Er) +
      (2 : k) • (Tr * derivative E) -
      (2 : k) • (C0c * derivative Vr) -
      (2 : k) • (c * derivative V) -
      D * derivative Ur).natDegree < _
  exact largeGapAlpha_natDegree_sub_lt68
    (largeGapAlpha_natDegree_sub_lt68
      (largeGapAlpha_natDegree_sub_lt68
        (largeGapAlpha_natDegree_add_lt68
          (largeGapAlpha_natDegree_add_lt68 h1 h2s) h3s) h4s) h5s) h6

set_option maxHeartbeats 2000000 in
theorem cubicLoadRowOnePolynomial68_degree_lt_largeGap_of_gap_lt_radius
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hl : l = 0) (hgap : g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadRowOnePolynomial68 l alpha beta gamma delta epsilon zeta eta
      A B c D e).natDegree < 12 * n - 3 * g - 1 := by
  rw [cubicLoadRowOnePolynomial68_eq_alphaRest l alpha beta gamma delta
    epsilon zeta eta A B c D e hl]
  exact cubicLoadRowOneAlphaRestPolynomial68_degree_lt_largeGap
    alpha beta gamma delta epsilon zeta eta A B c D e n g
    hn hg hgap hA hB hc hD he

end LargeGapAlphaCancellation68

#print axioms cubicLoadTAlphaRestPolynomial68_degree_le_of_gap_lt_radius
#print axioms cubicLoadVAlphaRestPolynomial68_degree_le_of_gap_lt_radius
#print axioms cubicLoadRowOneAlphaRestPolynomial68_degree_lt_largeGap
#print axioms cubicLoadRowOnePolynomial68_degree_lt_largeGap_of_gap_lt_radius

end Max11DegreeRoutes
