import LowScale68SecondaryResidualLoadZeroEndgame
import LowScale68SecondaryFirstLoadWallRemainder
import LowScale68SecondaryRelaxedCanonical

/-! # Residual row-two load dominance in the open chamber
`2g < n < 3g` and `n/2 < h < n-g`

Plan §3.5.C of `Grok68LargeGapPlanScratch.md`: on the open residual
window `2g < n < 3g` with `n < 2h` and `g+h < n`, the residual I4/I3
middle face remains load-free, while every *named* homogeneous row-two
face (`derivative(d e)`, the `B,c` cubic core, and `B^2 d`) lies
strictly below the Jacobian index `10n-1`.  The unique load monomial
that meets that index is the already-checked core
`(35/324) n l a^5`.

I4 being constant forces the incidence polynomial
`Q = B e + c d - B^3/9` to satisfy `Q = (3/8)(C i4 - I4_load)`, so
`Q.natDegree ≤ 8n` and `Q.coeff(8n) = -(35/4608) l a^4`.  The inner
`A Q'` / `A' Q` feed therefore meets `10n-1` as well.  The exact
leading scalar of residual row two plus load is
`(35/576) n l a^5`, which still forces `l = 0` once `a ≠ 0` and
`n ≠ 0`.

The strongest reusable polynomial lemma below drops every wall
hypothesis (`2g = n`, `3g = n`, `h = n-g`, `2h = n`) and uses only
`2g < n` together with the first-face degree bounds.  After `l = 0`,
the tracked endgame
`maximalExpandedIntegratedPolynomialLowerSystem_secondaryResidualLoadZero_impossible68`
closes the whole strip `2g < n`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Chamber arithmetic -/

theorem residualLoadDominance_betweenGaps
    (n g h : ℕ) (hsmall : 2 * g < n) (hstrict : n < 3 * g)
    (hleft : n < 2 * h) (hwin : g + h < n) :
    g < h ∧ h < 2 * g := by
  omega

theorem residualLoadDominance_eBound
    (n g h : ℕ) {e : k[X]} (hgh : g < h)
    (he : e.natDegree ≤ 6 * n - h) :
    e.natDegree ≤ 6 * n - g :=
  he.trans (by omega)

/-! ## Shared derivative degree helpers -/

private theorem residualLoadDominance_mul_derivative_le
    (p q : k[X]) (u v : ℕ) (hv : 0 < v)
    (hp : p.natDegree ≤ u) (hq : q.natDegree ≤ v) :
    (p * derivative q).natDegree ≤ u + v - 1 := by
  have hd : (derivative q).natDegree ≤ v - 1 :=
    (natDegree_derivative_le q).trans (Nat.sub_le_sub_right hq 1)
  have hsum : p.natDegree + (derivative q).natDegree ≤ u + (v - 1) :=
    Nat.add_le_add hp hd
  have hidx : u + (v - 1) = u + v - 1 := by omega
  exact natDegree_mul_le.trans (hidx ▸ hsum)

private theorem residualLoadDominance_mul_derivative_lt
    (p q : k[X]) (u v bound : ℕ) (hv : 0 < v)
    (hp : p.natDegree ≤ u) (hq : q.natDegree ≤ v)
    (huv : u + v - 1 < bound) :
    (p * derivative q).natDegree < bound :=
  (residualLoadDominance_mul_derivative_le p q u v hv hp hq).trans_lt huv

private theorem residualLoadDominance_smul_lt
    (r : k) {p : k[X]} {m : ℕ} (hp : p.natDegree < m) :
    (r • p).natDegree < m :=
  (natDegree_smul_le r p).trans_lt hp

private theorem residualLoadDominance_add_lt
    {p q : k[X]} {m : ℕ}
    (hp : p.natDegree < m) (hq : q.natDegree < m) :
    (p + q).natDegree < m :=
  (natDegree_add_le p q).trans_lt (max_lt hp hq)

private theorem residualLoadDominance_sub_lt
    {p q : k[X]} {m : ℕ}
    (hp : p.natDegree < m) (hq : q.natDegree < m) :
    (p - q).natDegree < m :=
  (natDegree_sub_le p q).trans_lt (max_lt hp hq)

/-! ## Strongest reusable load coefficient at `10n-1`

Every leftover summand of `cubicLoadRowTwoRestPolynomial68` is estimated
from the first-face bounds `≤ 4n-g` / `≤ 6n-g`.  No equality wall is
used. -/

set_option maxHeartbeats 2000000 in
theorem cubicLoadSRestPolynomial68_degree_le_twoGap
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
theorem cubicLoadURestPolynomial68_degree_le_twoGap
    (l alpha beta gamma delta zeta : k) (A B c D e : k[X]) (n g : ℕ)
    (hg : 0 < g) (hsmall : 2 * g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadURestPolynomial68 l alpha beta gamma delta zeta
      A B c D e).natDegree ≤ 6 * n - g := by
  simp only [cubicLoadURestPolynomial68]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
theorem cubicERestPolynomial68_degree_le_twoGap
    (A c e : k[X]) (n g : ℕ)
    (hg : 0 < g) (hsmall : 2 * g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hc : c.natDegree ≤ 4 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicERestPolynomial68 A c e).natDegree ≤ 6 * n - g := by
  simp only [cubicERestPolynomial68]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem cubicLoadRowTwoRestPolynomial68_degree_lt_tenRadius_of_twoGap
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hsmall : 2 * g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
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
  have hloads := cubicLoadPolynomials68_degreeBounds
    l alpha beta gamma delta epsilon zeta eta A B c D e n g
    hn hg hsmall hA hB hc hD he
  have hUlc : Ulc.natDegree ≤ 6 * n :=
    cubicLoadUCorePolynomial68_degree_le l A n hA
  have hUlr : Ulr.natDegree ≤ 6 * n - g :=
    cubicLoadURestPolynomial68_degree_le_twoGap
      l alpha beta gamma delta zeta A B c D e n g
      hg hsmall hA hB hc hD he
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
    cubicLoadSRestPolynomial68_degree_le_twoGap
      l alpha beta delta A B c n g hg hsmall hA hB hc
  have hEc : Ec.natDegree ≤ 6 * n := by
    simp only [Ec]
    compute_degree
    omega
  have hEr : Er.natDegree ≤ 6 * n - g :=
    cubicERestPolynomial68_degree_le_twoGap A c e n g
      hg hsmall hA hc he
  have hE : E.natDegree ≤ 6 * n :=
    (natDegree_add_le Ec Er).trans (max_le hEc (hEr.trans (by omega)))
  have hTl : Tl.natDegree ≤ 5 * n - g := by
    simpa only [Tl] using hloads.2.1
  have hVl : Vl.natDegree ≤ 7 * n - g := by
    simpa only [Vl] using hloads.2.2.2
  have h1 : (Ulc * derivative c).natDegree < 10 * n - 1 :=
    residualLoadDominance_mul_derivative_lt Ulc c (6 * n) (4 * n - g)
      (10 * n - 1) (by omega) hUlc hc (by omega)
  have h2 : (Ulr * derivative C0).natDegree < 10 * n - 1 :=
    residualLoadDominance_mul_derivative_lt Ulr C0 (6 * n - g) (4 * n)
      (10 * n - 1) (by omega) hUlr hC0 (by omega)
  have h3 : (Tl * derivative D).natDegree < 10 * n - 1 :=
    residualLoadDominance_mul_derivative_lt Tl D (5 * n - g) (5 * n - g)
      (10 * n - 1) (by omega) hTl hD (by omega)
  have h4 : (Slc * derivative Er).natDegree < 10 * n - 1 :=
    residualLoadDominance_mul_derivative_lt Slc Er (4 * n) (6 * n - g)
      (10 * n - 1) (by omega) hSlc hEr (by omega)
  have h5 : (Slr * derivative E).natDegree < 10 * n - 1 :=
    residualLoadDominance_mul_derivative_lt Slr E (4 * n - g) (6 * n)
      (10 * n - 1) (by omega) hSlr hE (by omega)
  have h6 : (B * derivative Vl).natDegree < 10 * n - 1 :=
    residualLoadDominance_mul_derivative_lt B Vl (3 * n - g) (7 * n - g)
      (10 * n - 1) (by omega) hB hVl (by omega)
  have h7 : (C0c * derivative Ulr).natDegree < 10 * n - 1 :=
    residualLoadDominance_mul_derivative_lt C0c Ulr (4 * n) (6 * n - g)
      (10 * n - 1) (by omega) hC0c hUlr (by omega)
  have h8 : (c * derivative Ul).natDegree < 10 * n - 1 :=
    residualLoadDominance_mul_derivative_lt c Ul (4 * n - g) (6 * n)
      (10 * n - 1) (by omega) hc hUl (by omega)
  have h9 : (D * derivative Tl).natDegree < 10 * n - 1 :=
    residualLoadDominance_mul_derivative_lt D Tl (5 * n - g) (5 * n - g)
      (10 * n - 1) (by omega) hD hTl (by omega)
  have h3s := residualLoadDominance_smul_lt (2 : k) h3
  have h4s := residualLoadDominance_smul_lt (3 : k) h4
  have h5s := residualLoadDominance_smul_lt (3 : k) h5
  have h6s := residualLoadDominance_smul_lt (3 : k) h6
  have h7s := residualLoadDominance_smul_lt (2 : k) h7
  have h8s := residualLoadDominance_smul_lt (2 : k) h8
  have s1 := residualLoadDominance_add_lt h1 h2
  have s2 := residualLoadDominance_add_lt s1 h3s
  have s3 := residualLoadDominance_add_lt s2 h4s
  have s4 := residualLoadDominance_add_lt s3 h5s
  have s5 := residualLoadDominance_sub_lt s4 h6s
  have s6 := residualLoadDominance_sub_lt s5 h7s
  have s7 := residualLoadDominance_sub_lt s6 h8s
  have s8 := residualLoadDominance_sub_lt s7 h9
  rw [cubicLoadRowTwoRestPolynomial68_eq_splitPieces]
  exact s8

set_option maxHeartbeats 2000000 in
/-- The unique `l A^5` coefficient of the first one-form load at
`10n-1`, under only `2g < n` and the first-face degree bounds. -/
theorem cubicLoadRowTwoPolynomial68_coeff_tenRadius_of_twoGap
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hsmall : 2 * g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadRowTwoPolynomial68 l alpha beta gamma delta epsilon zeta eta
      A B c D e).coeff (10 * n - 1) =
      (35 / 324 : k) * (n : k) * l * A.coeff (2 * n) ^ 5 := by
  rw [cubicLoadRowTwoPolynomial68_eq_lCore_add_rest, coeff_add,
    coeff_eq_zero_of_natDegree_lt
      (cubicLoadRowTwoRestPolynomial68_degree_lt_tenRadius_of_twoGap
        l alpha beta gamma delta epsilon zeta eta A B c D e n g
        hn hg hsmall hA hB hc hD he), add_zero]
  exact cubicLoadRowTwoLCorePolynomial68_coeff_loadWall l A n hn hA

/-! ## I4 core versus remainder at `8n`, and `Q` degree -/

theorem residualLoadDominance_I4_eq_Q (B c d e : k[X]) :
    secondaryResidualInvariantFourPolynomial68 B c d e =
      (8 / 3 : k) • residualIncidenceQ68 B c d e := by
  unfold residualIncidenceQ68
  exact secondaryResidualInvariantFourPolynomial68_eq_incidenceDefect B c d e

set_option maxHeartbeats 8000000 in
theorem secondaryLoadInvariantFourPolynomial68_degree_le_eightRadius
    (l beta gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g : ℕ) (hg : 0 < g) (hsmall : 2 * g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (secondaryLoadInvariantFourPolynomial68
      l beta gamma delta epsilon zeta A B c D e).natDegree ≤ 8 * n := by
  simp only [secondaryLoadInvariantFourPolynomial68]
  compute_degree
  omega

set_option maxHeartbeats 4000000 in
theorem residualIncidenceQ68_degree_le_eightRadius_of_I4
    (l beta gamma delta epsilon zeta i4 : k) (A B c d e : k[X])
    (n g : ℕ) (hg : 0 < g) (hsmall : 2 * g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (hi4 : cubicFirstIntegralFourPolynomial68
      l beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4) :
    (residualIncidenceQ68 B c d e).natDegree ≤ 8 * n := by
  let D := (1 / 3 : k) • (A * B) + d
  let Q := residualIncidenceQ68 B c d e
  let load := secondaryLoadInvariantFourPolynomial68
    l beta gamma delta epsilon zeta A B c D e
  have hD : D.natDegree ≤ 5 * n - g := by
    simp only [D]
    compute_degree
    omega
  have hsplit := hi4
  rw [cubicFirstIntegralFourPolynomial68_secondaryLoadSplit,
    cubicFirstIntegralFourPolynomial68_residualCoordinates,
    residualLoadDominance_I4_eq_Q] at hsplit
  change (8 / 3 : k) • Q + load = C i4 at hsplit
  have hcore : (8 / 3 : k) • Q = C i4 - load :=
    eq_sub_of_add_eq hsplit
  have hQ : Q = (3 / 8 : k) • (C i4 - load) := by
    calc
      Q = (3 / 8 : k) • ((8 / 3 : k) • Q) := by
        rw [smul_smul]
        norm_num
      _ = (3 / 8 : k) • (C i4 - load) := by rw [hcore]
  have hI4load : load.natDegree ≤ 8 * n :=
    secondaryLoadInvariantFourPolynomial68_degree_le_eightRadius
      l beta gamma delta epsilon zeta A B c D e n g
      hg hsmall hA hB hc hD he
  have hC : (C i4).natDegree ≤ 8 * n :=
    (natDegree_C i4).le.trans (by omega)
  have hsub : (C i4 - load).natDegree ≤ 8 * n :=
    (natDegree_sub_le _ _).trans (max_le hC hI4load)
  change Q.natDegree ≤ 8 * n
  rw [hQ]
  exact (natDegree_smul_le (3 / 8 : k) _).trans hsub

set_option maxHeartbeats 2000000 in
theorem residualIncidenceQ68_coeff_eightRadius_of_I4
    (l beta gamma delta epsilon zeta i4 : k) (A B c d e : k[X])
    (n g : ℕ) (hn : 0 < n) (hg : 0 < g) (hsmall : 2 * g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (hi4 : cubicFirstIntegralFourPolynomial68
      l beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4) :
    (residualIncidenceQ68 B c d e).coeff (8 * n) =
      (-35 / 4608 : k) * l * A.coeff (2 * n) ^ 4 := by
  let D := (1 / 3 : k) • (A * B) + d
  let Q := residualIncidenceQ68 B c d e
  let load := secondaryLoadInvariantFourPolynomial68
    l beta gamma delta epsilon zeta A B c D e
  have hD : D.natDegree ≤ 5 * n - g := by
    simp only [D]
    compute_degree
    omega
  have hsplit := hi4
  rw [cubicFirstIntegralFourPolynomial68_secondaryLoadSplit,
    cubicFirstIntegralFourPolynomial68_residualCoordinates,
    residualLoadDominance_I4_eq_Q] at hsplit
  change (8 / 3 : k) • Q + load = C i4 at hsplit
  have hz := congrArg (fun p : k[X] => p.coeff (8 * n)) hsplit
  have hC0 : (C i4).coeff (8 * n) = 0 := by
    rw [coeff_C]
    split_ifs with h0
    · exact absurd h0 (by omega)
    · rfl
  have hsum : ((8 / 3 : k) • Q).coeff (8 * n) + load.coeff (8 * n) = 0 := by
    simpa [coeff_add, hC0] using hz
  have hload := secondaryLoadInvariantFourPolynomial68_coeff_eightRadius
    l beta gamma delta epsilon zeta A B c D e n g hn hg
    hA hB hc hD he
  have hQ8 : (8 / 3 : k) * Q.coeff (8 * n) +
      (35 / 1728 : k) * l * A.coeff (2 * n) ^ 4 = 0 := by
    rw [coeff_smul, smul_eq_mul] at hsum
    convert hsum using 2
    simpa only [load] using hload.symm
  have hsolve : Q.coeff (8 * n) =
      (-35 / 4608 : k) * l * A.coeff (2 * n) ^ 4 := by
    linear_combination (3 / 8 : k) * hQ8
  simpa only [Q] using hsolve

/-! ## Named homogeneous faces strictly below `10n-1` -/

set_option maxHeartbeats 2000000 in
theorem residualRowTwoInner_namedFaces_degree_lt_tenRadius
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hsmall : 2 * g < n)
    (hstrict : n < 3 * g) (hleft : n < 2 * h) (hwin : g + h < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (A * B ^ 2 * derivative B).natDegree < 10 * n - 1 ∧
      (derivative A * B ^ 3).natDegree < 10 * n - 1 ∧
      (derivative (B * c ^ 2)).natDegree < 10 * n - 1 ∧
      (derivative (B ^ 2 * d)).natDegree < 10 * n - 1 ∧
      (derivative (d * e)).natDegree < 10 * n - 1 := by
  have hcore := residualRowTwoInner_BcCore_degree_le68_of_twoGap
    A B c n g hg hsmall hA hB hc
  have hh : h < 2 * g := by omega
  have hBd := residualRowTwoInner_Bd_degree_le68_of_twoGap
    B d n g h hg hgh hh hsmall hB hd
  have hde := residualRowTwoInner_de_degree_le68_of_twoGap
    d e n g h hg hgh hh hsmall hd he
  have h3le : 3 * g ≤ 11 * n := by omega
  have hcorelt : 11 * n - 3 * g - 1 < 10 * n - 1 := by omega
  have hBdlt : 11 * n - 2 * g - h - 1 < 10 * n - 1 := by omega
  have hdelt : 11 * n - 2 * h - 1 < 10 * n - 1 := by omega
  exact ⟨hcore.1.trans_lt hcorelt, hcore.2.1.trans_lt hcorelt,
    hcore.2.2.trans_lt hcorelt, hBd.trans_lt hBdlt, hde.trans_lt hdelt⟩

/-! ## Homogeneous residual row two at `10n-1` -/

set_option maxHeartbeats 6000000 in
/-- Residual row two at `10n-1` is the I4-forced `A Q'` feed.  Named
homogeneous faces lie strictly below this index. -/
theorem secondaryResidualRowTwoPolynomial68_coeff_loadDominance
    (l beta gamma delta epsilon zeta i4 : k) (A B c d e : k[X])
    (n g h : ℕ) (hn : 0 < n) (hg : 0 < g)
    (hsmall : 2 * g < n) (hstrict : n < 3 * g)
    (hleft : n < 2 * h) (hwin : g + h < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hi4 : cubicFirstIntegralFourPolynomial68
      l beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4) :
    (secondaryResidualRowTwoPolynomial68 A B c d e).coeff (10 * n - 1) =
      (-245 / 5184 : k) * (n : k) * l * A.coeff (2 * n) ^ 5 := by
  let Q := residualIncidenceQ68 B c d e
  let inner := residualRowTwoInner68 A B c d e
  set idx := 10 * n - 1
  have hgaps := residualLoadDominance_betweenGaps n g h
    hsmall hstrict hleft hwin
  have hgh := hgaps.1
  have he' : e.natDegree ≤ 6 * n - g :=
    residualLoadDominance_eBound n g h hgh he
  have hd' : d.natDegree ≤ 5 * n - g := hd.trans (by omega)
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
  have hnamed := residualRowTwoInner_namedFaces_degree_lt_tenRadius
    A B c d e n g h hg hgh hsmall hstrict hleft hwin hA hB hc hd he
  have h0AB : ((-2 : k) • (A * B ^ 2 * derivative B)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul,
      coeff_eq_zero_of_natDegree_lt hnamed.1, mul_zero]
  have h0A3 : ((-2 / 3 : k) • (derivative A * B ^ 3)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul,
      coeff_eq_zero_of_natDegree_lt hnamed.2.1, mul_zero]
  have h0Bc : ((6 : k) • derivative (B * c ^ 2)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul,
      coeff_eq_zero_of_natDegree_lt hnamed.2.2.1, mul_zero]
  have h0Bd : ((6 : k) • derivative (B ^ 2 * d)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul,
      coeff_eq_zero_of_natDegree_lt hnamed.2.2.2.1, mul_zero]
  have h0de : ((-18 : k) • derivative (d * e)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul,
      coeff_eq_zero_of_natDegree_lt hnamed.2.2.2.2, mul_zero]
  have hQpart : ((-6 : k) • (A * derivative Q)).coeff idx +
      ((3 : k) • (derivative A * Q)).coeff idx =
      (-42 : k) * (n : k) * A.coeff (2 * n) * Q.coeff (8 * n) := by
    rw [coeff_smul, coeff_smul, smul_eq_mul, smul_eq_mul, hAQ, hQA]
    push_cast
    ring
  have hinner : inner.coeff idx =
      (-42 : k) * (n : k) * A.coeff (2 * n) * Q.coeff (8 * n) := by
    dsimp [inner, residualRowTwoInner68]
    simp only [coeff_add]
    rw [h0AB, h0A3, h0Bd, h0Bc, h0de]
    linear_combination hQpart
  rw [residualRowTwo_eq_inner68, coeff_smul, smul_eq_mul]
  change ((-4 / 27 : k) * inner.coeff idx) = _
  rw [hinner]
  simp only [Q, hQ8]
  ring

/-! ## Combined row-two coefficient and `l = 0` -/

set_option maxHeartbeats 4000000 in
theorem cubicRowTwoPolynomial68_coeff_residualLoadDominance
    (l alpha beta gamma delta epsilon zeta eta i4 : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g)
    (hsmall : 2 * g < n) (hstrict : n < 3 * g)
    (hleft : n < 2 * h) (hwin : g + h < n)
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
      (35 / 576 : k) * (n : k) * l * A.coeff (2 * n) ^ 5 := by
  let D := (1 / 3 : k) • (A * B) + d
  have hD : D.natDegree ≤ 5 * n - g := by
    simp only [D]
    compute_degree
    omega
  have hgaps := residualLoadDominance_betweenGaps n g h
    hsmall hstrict hleft hwin
  have he' : e.natDegree ≤ 6 * n - g :=
    residualLoadDominance_eBound n g h hgaps.1 he
  have hhom := secondaryResidualRowTwoPolynomial68_coeff_loadDominance
    l beta gamma delta epsilon zeta i4 A B c d e n g h
    hn hg hsmall hstrict hleft hwin hA hB hc hd he hi4
  have hload := cubicLoadRowTwoPolynomial68_coeff_tenRadius_of_twoGap
    l alpha beta gamma delta epsilon zeta eta A B c D e n g
    hn hg hsmall hA hB hc hD he'
  rw [coeff_add, hhom]
  change _ +
      (cubicLoadRowTwoPolynomial68 l alpha beta gamma delta epsilon zeta eta
        A B c D e).coeff (10 * n - 1) = _
  rw [hload]
  ring

set_option maxHeartbeats 2000000 in
theorem cubicRowTwoPolynomial68_imp_loadL_eq_zero_of_residualLoadDominance
    (l alpha beta gamma delta epsilon zeta eta i4 : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g)
    (hsmall : 2 * g < n) (hstrict : n < 3 * g)
    (hleft : n < 2 * h) (hwin : g + h < n)
    (hA : A.natDegree ≤ 2 * n)
    (ha : A.coeff (2 * n) ≠ 0)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hi4 : cubicFirstIntegralFourPolynomial68
      l beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hsum : secondaryResidualRowTwoPolynomial68 A B c d e +
      cubicLoadRowTwoPolynomial68 l alpha beta gamma delta epsilon zeta eta
        A B c ((1 / 3 : k) • (A * B) + d) e = 0) :
    l = 0 := by
  have hz := congrArg (fun p : k[X] => p.coeff (10 * n - 1)) hsum
  rw [cubicRowTwoPolynomial68_coeff_residualLoadDominance
    l alpha beta gamma delta epsilon zeta eta i4 A B c d e n g h
    hn hg hsmall hstrict hleft hwin hA hB hc hd he hi4,
    coeff_zero] at hz
  have hn0 : (n : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hsc : (35 / 576 : k) ≠ 0 := by norm_num
  have hprod : l * A.coeff (2 * n) ^ 5 = 0 := by
    have : ((35 / 576 : k) * (n : k)) * (l * A.coeff (2 * n) ^ 5) = 0 := by
      convert hz using 1
      ring
    exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero hsc hn0)
  exact (mul_eq_zero.mp hprod).resolve_right (pow_ne_zero 5 ha)

set_option maxHeartbeats 4000000 in
theorem polynomialSecondaryResidualLoadDominance_loadL_eq_zero68
    (l alpha beta gamma delta epsilon zeta eta i4 : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g)
    (hsmall : 2 * g < n) (hstrict : n < 3 * g)
    (hleft : n < 2 * h) (hwin : g + h < n)
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
          A B C0 D0 E0) B C0 D0 E0 = 0) :
    l = 0 := by
  have hsum := polynomialSecondaryResidualRowTwo68
    l alpha beta gamma delta epsilon zeta eta A B c d e hrowTwo
  exact cubicRowTwoPolynomial68_imp_loadL_eq_zero_of_residualLoadDominance
    l alpha beta gamma delta epsilon zeta eta i4 A B c d e n g h
    hn hg hsmall hstrict hleft hwin hA ha hB hc hd he hi4 hsum

/-! ## Canonical maximal-expanded wrapper -/

set_option maxHeartbeats 4000000 in
/-- On a maximal expanded system in `2g < n < 3g`, a residual gap in the
open load-dominance window `n < 2h` and `g+h < n` forces `l = 0`. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_residualRowTwoLoadDominance_loadL_eq_zero68
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
      n < 2 * h ∧ g + h < n) :
    l = 0 := by
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
  change n < 2 * h ∧ g + h < n at hdom
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
  have hgh : g < h := by
    simpa only [h] using secondaryResidualGap68_gt_of_strictDrops n g d ee
      hdrops.1 hdrops.2
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
  exact polynomialSecondaryResidualLoadDominance_loadL_eq_zero68
    l alpha beta gamma delta epsilon zeta eta i4 Ae Be ce d ee n g h
    hn hg hchamber.1 hchamber.2 hdom.1 hdom.2 hA ha hB hc
    hbounds.1 hbounds.2 hi4c h2c

set_option maxHeartbeats 4000000 in
/-- The open residual load-dominance chamber is empty: row two forces
`l = 0`, and the tracked `l = 0` endgame then excludes `2g < n`. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_residualRowTwoLoadDominance_impossible68
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
      n < 2 * h ∧ g + h < n) :
    False := by
  have hl0 :=
    maximalExpandedIntegratedPolynomialLowerSystem_residualRowTwoLoadDominance_loadL_eq_zero68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys hchamber hdom
  exact maximalExpandedIntegratedPolynomialLowerSystem_secondaryResidualLoadZero_impossible68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys hl0 (by
      simpa using hchamber.1)

#print axioms cubicLoadRowTwoPolynomial68_coeff_tenRadius_of_twoGap
#print axioms residualIncidenceQ68_coeff_eightRadius_of_I4
#print axioms secondaryResidualRowTwoPolynomial68_coeff_loadDominance
#print axioms cubicRowTwoPolynomial68_imp_loadL_eq_zero_of_residualLoadDominance
#print axioms polynomialSecondaryResidualLoadDominance_loadL_eq_zero68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_residualRowTwoLoadDominance_loadL_eq_zero68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_residualRowTwoLoadDominance_impossible68

end Max11DegreeRoutes
