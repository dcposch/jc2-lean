import LowScale68SecondaryResidualLoadZeroEndgame
import LowScale68SecondaryFirstLoadWallRemainder
import LowScale68SecondaryResidualRowTwoSystem

/-! # Left residual load window on the `(6,8)` chamber `g < h < n/2`

In the strip `2g < n < 3g` with residual gap `g < h` and `2h < n`, the
quartic invariant is still the ordinary middle face, while I4 constancy
forces the incidence defect `Q` into the load window `deg Q ≤ 8n`.  The
Jacobian `l A^5` load then sits at `10n-1`, strictly below the left
row-two face `11n-2h-1`.  The surviving left scalar forces a vanishing
`d_top e_top`, which the middle-face support classification excludes.
The chamber is empty, so `l = 0`; the tracked residual load-zero
endgame then closes the canonical branch.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## Chamber arithmetic -/

theorem residualLeftLoadWindow_win
    (n g h : ℕ) (hsmall : 2 * g < n) (hleft : 2 * h < n) :
    g + h < n := by
  omega

theorem residualLeftLoadWindow_lt_double
    (n g h : ℕ) (hstrict : n < 3 * g) (hleft : 2 * h < n) :
    h < 2 * g := by
  omega

theorem residualLeftLoadWindow_leftOfCubic
    (n g h : ℕ) (hstrict : n < 3 * g) (hleft : 2 * h < n) :
    2 * h < 3 * g := by
  omega

theorem residualLeftLoadWindow_load_lt_leftIndex
    (n h : ℕ) (hleft : 2 * h < n) :
    10 * n - 1 < 11 * n - 2 * h - 1 := by
  omega

theorem residualLeftLoadWindow_cubic_lt_leftIndex
    (n g h : ℕ) (hstrict : n < 3 * g) (hleft : 2 * h < n) :
    11 * n - 3 * g - 1 < 11 * n - 2 * h - 1 := by
  omega

theorem residualLeftLoadWindow_eBound
    (n g h : ℕ) (hgh : g < h)
    {e : k[X]} (he : e.natDegree ≤ 6 * n - h) :
    e.natDegree ≤ 6 * n - g :=
  he.trans (by omega)

theorem residualLeftLoadWindow_dBound
    (n g h : ℕ) (hgh : g < h)
    {d : k[X]} (hd : d.natDegree ≤ 5 * n - h) :
    d.natDegree ≤ 5 * n - g :=
  hd.trans (by omega)

theorem residualLeftLoadWindow_not_both_zero
    (n h : ℕ) (d e : k[X]) (hn : 0 < n) (hleft : 2 * h < n)
    (hh : h = secondaryResidualGap68 n d e) : ¬(d = 0 ∧ e = 0) := by
  intro hde
  have hsent : secondaryResidualGap68 n d e = 6 * n + 1 := by
    simp [secondaryResidualGap68, polynomialGap68, hde.1, hde.2]
  have : 2 * (6 * n + 1) < n := by
    simpa [hh, hsent] using hleft
  omega

/-! ## Shared degree helpers -/

private theorem residualLeft_natDegree_smul_lt68
    (r : k) {p : k[X]} {m : ℕ} (hp : p.natDegree < m) :
    (r • p).natDegree < m :=
  (natDegree_smul_le r p).trans_lt hp

private theorem residualLeft_natDegree_add_lt68
    {p q : k[X]} {m : ℕ}
    (hp : p.natDegree < m) (hq : q.natDegree < m) :
    (p + q).natDegree < m :=
  (natDegree_add_le p q).trans_lt (max_lt hp hq)

private theorem residualLeft_natDegree_sub_lt68
    {p q : k[X]} {m : ℕ}
    (hp : p.natDegree < m) (hq : q.natDegree < m) :
    (p - q).natDegree < m :=
  (natDegree_sub_le p q).trans_lt (max_lt hp hq)

private theorem residualLeft_mul_derivative_lt
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

/-! ## I4 core versus remainder at `8n`, and `Q` degree -/

theorem residualLeft_I4_eq_Q (B c d e : k[X]) :
    secondaryResidualInvariantFourPolynomial68 B c d e =
      (8 / 3 : k) • residualIncidenceQ68 B c d e :=
  secondaryResidualInvariantFourPolynomial68_eq_incidenceDefect B c d e

set_option maxHeartbeats 2000000 in
theorem secondaryLoadInvariantFourPolynomial68_degree_le_eightRadius_of_leftLoadWindow
    (l beta gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g h : ℕ) (hg : 0 < g) (hsmall : 2 * g < n) (hgh : g < h)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - h) :
    (secondaryLoadInvariantFourPolynomial68
      l beta gamma delta epsilon zeta A B c D e).natDegree ≤ 8 * n := by
  simp only [secondaryLoadInvariantFourPolynomial68]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
/-- I4 constancy forces the incidence defect into the load window `8n`. -/
theorem residualIncidenceQ68_degree_le_eightRadius_of_leftLoadWindow
    (l beta gamma delta epsilon zeta i4 : k) (A B c d e : k[X])
    (n g h : ℕ) (hg : 0 < g) (hsmall : 2 * g < n) (hgh : g < h)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hi4 : cubicFirstIntegralFourPolynomial68
      l beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4) :
    (residualIncidenceQ68 B c d e).natDegree ≤ 8 * n := by
  let D := (1 / 3 : k) • (A * B) + d
  let Q := residualIncidenceQ68 B c d e
  have hD : D.natDegree ≤ 5 * n - g := by
    simp only [D]
    compute_degree
    omega
  have hsplit := cubicFirstIntegralFourPolynomial68_secondaryLoadSplit
    l beta gamma delta epsilon zeta A B c D e
  have hhom :
      cubicFirstIntegralFourPolynomial68 0 0 0 0 0 0 A B c D e =
        (8 / 3 : k) • Q := by
    have hres := cubicFirstIntegralFourPolynomial68_residualCoordinates
      A B c d e
    simpa only [D, Q] using
      hres.trans (residualLeft_I4_eq_Q B c d e)
  have hI4load :=
    secondaryLoadInvariantFourPolynomial68_degree_le_eightRadius_of_leftLoadWindow
      l beta gamma delta epsilon zeta A B c D e n g h
      hg hsmall hgh hA hB hc hD he
  have hsum : (8 / 3 : k) • Q +
      secondaryLoadInvariantFourPolynomial68
        l beta gamma delta epsilon zeta A B c D e = C i4 := by
    simpa [hhom] using hsplit.symm.trans hi4
  have hQ : (8 / 3 : k) • Q =
      C i4 -
        secondaryLoadInvariantFourPolynomial68
          l beta gamma delta epsilon zeta A B c D e :=
    eq_sub_of_add_eq hsum
  have hQeq : Q = (3 / 8 : k) •
      (C i4 -
        secondaryLoadInvariantFourPolynomial68
          l beta gamma delta epsilon zeta A B c D e) := by
    have htmp : Q = (3 / 8 : k) • ((8 / 3 : k) • Q) := by
      rw [smul_smul]
      norm_num
    rw [htmp, hQ]
  have hC : (C i4).natDegree ≤ 8 * n :=
    (natDegree_C i4).trans_le (by omega)
  change Q.natDegree ≤ 8 * n
  rw [hQeq]
  exact (natDegree_smul_le (3 / 8 : k) _).trans
    ((natDegree_sub_le _ _).trans (max_le hC hI4load))

set_option maxHeartbeats 2000000 in
/-- Mixed I4 coefficient at the load index `8n`. Homogeneous residual
terms above `8n` have already been killed by I4 constancy; the `B^3`
summand is strictly lower because `n < 3g`. -/
theorem cubicFirstIntegralFourPolynomial68_coeff_eightRadius_of_leftLoadWindow
    (l beta gamma delta epsilon zeta i4 : k) (A B c d e : k[X])
    (n g h : ℕ) (hn : 0 < n) (hg : 0 < g)
    (hsmall : 2 * g < n) (hstrict : n < 3 * g) (hgh : g < h)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hi4 : cubicFirstIntegralFourPolynomial68
      l beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4) :
    (cubicFirstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff (8 * n) =
      (8 / 3 : k) * (residualIncidenceQ68 B c d e).coeff (8 * n) +
        (35 / 1728 : k) * l * A.coeff (2 * n) ^ 4 := by
  let D := (1 / 3 : k) • (A * B) + d
  let Q := residualIncidenceQ68 B c d e
  have hD : D.natDegree ≤ 5 * n - g := by
    simp only [D]
    compute_degree
    omega
  have he' : e.natDegree ≤ 6 * n - g :=
    residualLeftLoadWindow_eBound n g h hgh he
  have hsplit := cubicFirstIntegralFourPolynomial68_secondaryLoadSplit
    l beta gamma delta epsilon zeta A B c D e
  have hhom :
      cubicFirstIntegralFourPolynomial68 0 0 0 0 0 0 A B c D e =
        (8 / 3 : k) • Q := by
    have hres := cubicFirstIntegralFourPolynomial68_residualCoordinates
      A B c d e
    simpa only [D, Q] using
      hres.trans (residualLeft_I4_eq_Q B c d e)
  have hload := secondaryLoadInvariantFourPolynomial68_coeff_eightRadius
    l beta gamma delta epsilon zeta A B c D e n g hn hg
    hA hB hc hD he'
  rw [hsplit, coeff_add, hhom, coeff_smul, smul_eq_mul, hload]

set_option maxHeartbeats 2000000 in
theorem residualIncidenceQ68_coeff_eightRadius_of_leftLoadWindow
    (l beta gamma delta epsilon zeta i4 : k) (A B c d e : k[X])
    (n g h : ℕ) (hn : 0 < n) (hg : 0 < g)
    (hsmall : 2 * g < n) (hstrict : n < 3 * g) (hgh : g < h)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hi4 : cubicFirstIntegralFourPolynomial68
      l beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4) :
    (residualIncidenceQ68 B c d e).coeff (8 * n) =
      (-35 / 4608 : k) * l * A.coeff (2 * n) ^ 4 := by
  have hmix :=
    cubicFirstIntegralFourPolynomial68_coeff_eightRadius_of_leftLoadWindow
      l beta gamma delta epsilon zeta i4 A B c d e n g h hn hg
      hsmall hstrict hgh hA hB hc hd he hi4
  have hz := congrArg (fun p : k[X] => p.coeff (8 * n)) hi4
  have hindex : 8 * n ≠ 0 := by omega
  simp only [coeff_C, ite_eq_right hindex] at hz
  have hQ8 : (8 / 3 : k) * (residualIncidenceQ68 B c d e).coeff (8 * n) +
      (35 / 1728 : k) * l * A.coeff (2 * n) ^ 4 = 0 := by
    rw [← hmix, hz]
  have h83 : (8 / 3 : k) ≠ 0 := by norm_num
  apply mul_left_cancel₀ h83
  linear_combination hQ8

/-- If the incidence defect drops strictly below the load window, the
surviving `A^4` coefficient forces `l = 0`. -/
theorem cubicFirstIntegralFourPolynomial68_imp_loadL_eq_zero_of_leftLoadWindow
    (l beta gamma delta epsilon zeta i4 : k) (A B c d e : k[X])
    (n g h : ℕ) (hn : 0 < n) (hg : 0 < g)
    (hsmall : 2 * g < n) (hstrict : n < 3 * g) (hgh : g < h)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (ha : A.coeff (2 * n) ≠ 0)
    (hQ : (residualIncidenceQ68 B c d e).natDegree < 8 * n)
    (hi4 : cubicFirstIntegralFourPolynomial68
      l beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4) :
    l = 0 := by
  have hmix :=
    cubicFirstIntegralFourPolynomial68_coeff_eightRadius_of_leftLoadWindow
      l beta gamma delta epsilon zeta i4 A B c d e n g h hn hg
      hsmall hstrict hgh hA hB hc hd he hi4
  have hz := congrArg (fun p : k[X] => p.coeff (8 * n)) hi4
  have hindex : 8 * n ≠ 0 := by omega
  simp only [coeff_C, ite_eq_right hindex] at hz
  have hQ8 : (residualIncidenceQ68 B c d e).coeff (8 * n) = 0 :=
    coeff_eq_zero_of_natDegree_lt hQ
  have hload : (35 / 1728 : k) * l * A.coeff (2 * n) ^ 4 = 0 := by
    rw [hmix, hQ8] at hz
    simpa using hz
  have hprod : (35 / 1728 : k) * (l * A.coeff (2 * n) ^ 4) = 0 := by
    linear_combination hload
  have hla : l * A.coeff (2 * n) ^ 4 = 0 :=
    (mul_eq_zero.mp hprod).resolve_left (by norm_num)
  exact (mul_eq_zero.mp hla).resolve_right (pow_ne_zero 4 ha)

/-! ## Jacobian load below the left index -/

set_option maxHeartbeats 2000000 in
theorem cubicLoadSRestPolynomial68_degree_le_leftLoadWindow
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
theorem cubicLoadURestPolynomial68_degree_le_leftLoadWindow
    (l alpha beta gamma delta zeta : k) (A B c D e : k[X])
    (n g h : ℕ) (hg : 0 < g) (hsmall : 2 * g < n) (hgh : g < h)
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
theorem cubicERestPolynomial68_degree_le_leftLoadWindow
    (A c e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hsmall : 2 * g < n) (hgh : g < h)
    (hA : A.natDegree ≤ 2 * n)
    (hc : c.natDegree ≤ 4 * n - g)
    (he : e.natDegree ≤ 6 * n - h) :
    (cubicERestPolynomial68 A c e).natDegree ≤ 6 * n - g := by
  simp only [cubicERestPolynomial68]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem cubicLoadRowTwoRestPolynomial68_degree_lt_leftLoadWindow
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g)
    (hsmall : 2 * g < n) (hgh : g < h)
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
    residualLeftLoadWindow_eBound n g h hgh he
  have hloads := cubicLoadPolynomials68_degreeBounds
    l alpha beta gamma delta epsilon zeta eta A B c D e n g
    hn hg hsmall hA hB hc hD he'
  have hUlc : Ulc.natDegree ≤ 6 * n :=
    cubicLoadUCorePolynomial68_degree_le l A n hA
  have hUlr : Ulr.natDegree ≤ 6 * n - g :=
    cubicLoadURestPolynomial68_degree_le_leftLoadWindow
      l alpha beta gamma delta zeta A B c D e n g h
      hg hsmall hgh hA hB hc hD he
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
    cubicLoadSRestPolynomial68_degree_le_leftLoadWindow
      l alpha beta delta A B c n g hg hsmall hA hB hc
  have hEc : Ec.natDegree ≤ 6 * n := by
    simp only [Ec]
    compute_degree
    omega
  have hEr : Er.natDegree ≤ 6 * n - g :=
    cubicERestPolynomial68_degree_le_leftLoadWindow A c e n g h
      hg hsmall hgh hA hc he
  have hE : E.natDegree ≤ 6 * n :=
    (natDegree_add_le Ec Er).trans (max_le hEc (hEr.trans (by omega)))
  have hTl : Tl.natDegree ≤ 5 * n - g := by
    simpa only [Tl] using hloads.2.1
  have hVl : Vl.natDegree ≤ 7 * n - g := by
    simpa only [Vl] using hloads.2.2.2
  have h1 : (Ulc * derivative c).natDegree < 10 * n - 1 :=
    residualLeft_mul_derivative_lt Ulc c (6 * n) (4 * n - g)
      (10 * n - 1) (by omega) hUlc hc (by omega)
  have h2 : (Ulr * derivative C0).natDegree < 10 * n - 1 :=
    residualLeft_mul_derivative_lt Ulr C0 (6 * n - g) (4 * n)
      (10 * n - 1) (by omega) hUlr hC0 (by omega)
  have h3 : (Tl * derivative D).natDegree < 10 * n - 1 :=
    residualLeft_mul_derivative_lt Tl D (5 * n - g) (5 * n - g)
      (10 * n - 1) (by omega) hTl hD (by omega)
  have h4 : (Slc * derivative Er).natDegree < 10 * n - 1 :=
    residualLeft_mul_derivative_lt Slc Er (4 * n) (6 * n - g)
      (10 * n - 1) (by omega) hSlc hEr (by omega)
  have h5 : (Slr * derivative E).natDegree < 10 * n - 1 :=
    residualLeft_mul_derivative_lt Slr E (4 * n - g) (6 * n)
      (10 * n - 1) (by omega) hSlr hE (by omega)
  have h6 : (B * derivative Vl).natDegree < 10 * n - 1 :=
    residualLeft_mul_derivative_lt B Vl (3 * n - g) (7 * n - g)
      (10 * n - 1) (by omega) hB hVl (by omega)
  have h7 : (C0c * derivative Ulr).natDegree < 10 * n - 1 :=
    residualLeft_mul_derivative_lt C0c Ulr (4 * n) (6 * n - g)
      (10 * n - 1) (by omega) hC0c hUlr (by omega)
  have h8 : (c * derivative Ul).natDegree < 10 * n - 1 :=
    residualLeft_mul_derivative_lt c Ul (4 * n - g) (6 * n)
      (10 * n - 1) (by omega) hc hUl (by omega)
  have h9 : (D * derivative Tl).natDegree < 10 * n - 1 :=
    residualLeft_mul_derivative_lt D Tl (5 * n - g) (5 * n - g)
      (10 * n - 1) (by omega) hD hTl (by omega)
  have h3s := residualLeft_natDegree_smul_lt68 (2 : k) h3
  have h4s := residualLeft_natDegree_smul_lt68 (3 : k) h4
  have h5s := residualLeft_natDegree_smul_lt68 (3 : k) h5
  have h6s := residualLeft_natDegree_smul_lt68 (3 : k) h6
  have h7s := residualLeft_natDegree_smul_lt68 (2 : k) h7
  have h8s := residualLeft_natDegree_smul_lt68 (2 : k) h8
  have s1 := residualLeft_natDegree_add_lt68 h1 h2
  have s2 := residualLeft_natDegree_add_lt68 s1 h3s
  have s3 := residualLeft_natDegree_add_lt68 s2 h4s
  have s4 := residualLeft_natDegree_add_lt68 s3 h5s
  have s5 := residualLeft_natDegree_sub_lt68 s4 h6s
  have s6 := residualLeft_natDegree_sub_lt68 s5 h7s
  have s7 := residualLeft_natDegree_sub_lt68 s6 h8s
  have s8 := residualLeft_natDegree_sub_lt68 s7 h9
  rw [cubicLoadRowTwoRestPolynomial68_eq_splitPieces]
  exact s8

set_option maxHeartbeats 2000000 in
theorem cubicLoadRowTwoPolynomial68_degree_le_loadIndex_of_leftLoadWindow
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g)
    (hsmall : 2 * g < n) (hgh : g < h)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - h) :
    (cubicLoadRowTwoPolynomial68 l alpha beta gamma delta epsilon zeta eta
      A B c D e).natDegree ≤ 10 * n - 1 := by
  have hrest := cubicLoadRowTwoRestPolynomial68_degree_lt_leftLoadWindow
    l alpha beta gamma delta epsilon zeta eta A B c D e n g h
    hn hg hsmall hgh hA hB hc hD he
  have hcore : (cubicLoadRowTwoLCorePolynomial68 l A).natDegree ≤
      10 * n - 1 := by
    have hA4 : (A ^ 4).natDegree ≤ 8 * n := by
      compute_degree
      omega
    have hdA : (derivative A).natDegree ≤ 2 * n - 1 :=
      (natDegree_derivative_le A).trans (by omega)
    have hprod := natDegree_mul_le_of_le hA4 hdA
    have hi : 8 * n + (2 * n - 1) = 10 * n - 1 := by omega
    rw [cubicLoadRowTwoLCorePolynomial68_eq]
    exact (natDegree_smul_le (35 / 648 * l : k) _).trans (by
      simpa only [hi] using hprod)
  rw [cubicLoadRowTwoPolynomial68_eq_lCore_add_rest]
  exact (natDegree_add_le _ _).trans (max_le hcore (Nat.le_of_lt hrest))

set_option maxHeartbeats 2000000 in
theorem cubicLoadRowTwoPolynomial68_degree_lt_leftIndex_of_leftLoadWindow
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g)
    (hsmall : 2 * g < n) (hstrict : n < 3 * g)
    (hgh : g < h) (hleft : 2 * h < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (cubicLoadRowTwoPolynomial68 l alpha beta gamma delta epsilon zeta eta
      A B c ((1 / 3 : k) • (A * B) + d) e).natDegree <
        11 * n - 2 * h - 1 := by
  let D := (1 / 3 : k) • (A * B) + d
  have hD : D.natDegree ≤ 5 * n - g := by
    simp only [D]
    compute_degree
    omega
  have hle := cubicLoadRowTwoPolynomial68_degree_le_loadIndex_of_leftLoadWindow
    l alpha beta gamma delta epsilon zeta eta A B c D e n g h
    hn hg hsmall hgh hA hB hc hD he
  exact hle.trans_lt (residualLeftLoadWindow_load_lt_leftIndex n h hleft)

/-! ## Left row-two coefficient after the I4-forced `Q` bound -/

set_option maxHeartbeats 2000000 in
theorem residualRowTwoInner_Q_degree_le_loadIndex_of_leftLoadWindow
    (A B c d e : k[X]) (n : ℕ)
    (hn : 0 < n) (hA : A.natDegree ≤ 2 * n)
    (hQ : (residualIncidenceQ68 B c d e).natDegree ≤ 8 * n) :
    (A * derivative (residualIncidenceQ68 B c d e)).natDegree ≤
        10 * n - 1 ∧
      (derivative A * residualIncidenceQ68 B c d e).natDegree ≤
        10 * n - 1 := by
  have hQ' : (derivative (residualIncidenceQ68 B c d e)).natDegree ≤
      8 * n - 1 :=
    (natDegree_derivative_le _).trans (Nat.sub_le_sub_right hQ 1)
  have hAQ := natDegree_mul_le_of_le hA hQ'
  have hiAQ : 2 * n + (8 * n - 1) = 10 * n - 1 := by omega
  have hdA : (derivative A).natDegree ≤ 2 * n - 1 :=
    (natDegree_derivative_le A).trans (by omega)
  have hQA := natDegree_mul_le_of_le hdA hQ
  have hiQA : (2 * n - 1) + 8 * n = 10 * n - 1 := by omega
  exact ⟨by simpa only [hiAQ] using hAQ, by simpa only [hiQA] using hQA⟩

set_option maxHeartbeats 4000000 in
/-- On `2h < n < 3g`, residual row two is dominated by `derivative(d*e)`
once I4 has forced `Q` into the load window. -/
theorem residualRowTwo_coeff_leftChamber68_of_leftLoadWindow
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h)
    (hsmall : 2 * g < n) (hstrict : n < 3 * g) (hleft : 2 * h < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualIncidenceQ68 B c d e).natDegree ≤ 8 * n) :
    (secondaryResidualRowTwoPolynomial68 A B c d e).coeff
        (11 * n - 2 * h - 1) =
      (8 / 3 : k) * ((11 * n - 2 * h : ℕ) : k) *
        d.coeff (5 * n - h) * e.coeff (6 * n - h) := by
  let Q := residualIncidenceQ68 B c d e
  let inner := residualRowTwoInner68 A B c d e
  set idx := 11 * n - 2 * h - 1
  have hh : h < 2 * g :=
    residualLeftLoadWindow_lt_double n g h hstrict hleft
  have hidxLoad : 10 * n - 1 < idx := by
    dsimp [idx]
    exact residualLeftLoadWindow_load_lt_leftIndex n h hleft
  have hidxCubic : 11 * n - 3 * g - 1 < idx := by
    dsimp [idx]
    exact residualLeftLoadWindow_cubic_lt_leftIndex n g h hstrict hleft
  have hQdeg :=
    residualRowTwoInner_Q_degree_le_loadIndex_of_leftLoadWindow
      A B c d e n hn hA hQ
  have hAQ : (A * derivative Q).natDegree < idx :=
    hQdeg.1.trans_lt hidxLoad
  have hAQ' : (derivative A * Q).natDegree < idx :=
    hQdeg.2.trans_lt hidxLoad
  have hcore := residualRowTwoInner_BcCore_degree_le68_of_twoGap
    A B c n g hg hsmall hA hB hc
  have hAB : (A * B ^ 2 * derivative B).natDegree < idx :=
    hcore.1.trans_lt hidxCubic
  have hA3 : (derivative A * B ^ 3).natDegree < idx :=
    hcore.2.1.trans_lt hidxCubic
  have hBc : (derivative (B * c ^ 2)).natDegree < idx :=
    hcore.2.2.trans_lt hidxCubic
  have hBd := residualRowTwoInner_Bd_degree_le68_of_twoGap
    B d n g h hg hgh hh hsmall hB hd
  have hBd' : (derivative (B ^ 2 * d)).natDegree < idx := by
    dsimp [idx]
    omega
  have hdebound := natDegree_mul_le_of_le hd he
  have hide : (5 * n - h) + (6 * n - h) = 11 * n - 2 * h := by omega
  rw [hide] at hdebound
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

set_option maxHeartbeats 2000000 in
theorem residualRowTwo_leftChamber_ne_zero68_of_leftLoadWindow
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h)
    (hsmall : 2 * g < n) (hstrict : n < 3 * g) (hleft : 2 * h < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualIncidenceQ68 B c d e).natDegree ≤ 8 * n)
    (hd0 : d.coeff (5 * n - h) ≠ 0)
    (he0 : e.coeff (6 * n - h) ≠ 0) :
    (secondaryResidualRowTwoPolynomial68 A B c d e).coeff
        (11 * n - 2 * h - 1) ≠ 0 := by
  rw [residualRowTwo_coeff_leftChamber68_of_leftLoadWindow A B c d e n g h
    hn hg hgh hsmall hstrict hleft hA hB hc hd he hQ]
  have hscalar : (8 / 3 : k) ≠ 0 := by norm_num
  have hN : ((11 * n - 2 * h : ℕ) : k) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by omega)
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hscalar hN) hd0) he0

/-! ## Polynomial face: middle I4/I3 plus left row two -/

theorem polynomialSecondaryResidualBetweenFace68_of_leftLoadWindow
    (l beta gamma delta epsilon zeta i4 i3 : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h)
    (hsmall : 2 * g < n) (hlarge : n ≤ 3 * g) (hleft : 2 * h < n)
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
  have hwin : g + h < n := residualLeftLoadWindow_win n g h hsmall hleft
  exact polynomialSecondaryResidualBetweenFace68_of_loadWindow
    l beta gamma delta epsilon zeta i4 i3 A B c d e n g h
    hg hgh hlarge hwin hA hB hc hd he hi4 hi3

set_option maxHeartbeats 4000000 in
theorem polynomialSecondaryResidualLeftLoadWindow68_impossible
    (l alpha beta gamma delta epsilon zeta eta i4 i3 : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g)
    (hsmall : 2 * g < n) (hstrict : n < 3 * g)
    (hgh : g < h) (hleft : 2 * h < n)
    (hA : A.natDegree ≤ 2 * n)
    (ha : A.coeff (2 * n) ≠ 0)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hsupport : B.coeff (3 * n - g) ≠ 0 ∨ c.coeff (4 * n - g) ≠ 0)
    (hattained : d.coeff (5 * n - h) ≠ 0 ∨ e.coeff (6 * n - h) ≠ 0)
    (hi4 : cubicFirstIntegralFourPolynomial68
      l beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hi3 : cubicFirstIntegralThreePolynomial68
      l beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i3)
    (hrowTwo :
      secondaryResidualRowTwoPolynomial68 A B c d e +
        cubicLoadRowTwoPolynomial68 l alpha beta gamma delta epsilon
          zeta eta A B c ((1 / 3 : k) • (A * B) + d) e = 0) :
    False := by
  have hlarge : n ≤ 3 * g := Nat.le_of_lt hstrict
  have hmid := polynomialSecondaryResidualBetweenFace68_of_leftLoadWindow
    l beta gamma delta epsilon zeta i4 i3 A B c d e n g h
    hg hgh hsmall hlarge hleft hA hB hc hd he hi4 hi3
  have hclass := secondaryResidualBetweenFace68_classify_of_support
    (A.coeff (2 * n)) (B.coeff (3 * n - g))
    (c.coeff (4 * n - g)) (d.coeff (5 * n - h))
    (e.coeff (6 * n - h)) ha hsupport hattained hmid
  have hQ := residualIncidenceQ68_degree_le_eightRadius_of_leftLoadWindow
    l beta gamma delta epsilon zeta i4 A B c d e n g h
    hg hsmall hgh hA hB hc hd he hi4
  have hload :=
    cubicLoadRowTwoPolynomial68_degree_lt_leftIndex_of_leftLoadWindow
      l alpha beta gamma delta epsilon zeta eta A B c d e n g h
      hn hg hsmall hstrict hgh hleft hA hB hc hd he
  have hcoeff0 := residualRowTwo_coeff_eq_zero_of_loadCutoff68
    A B c d e
    (cubicLoadRowTwoPolynomial68 l alpha beta gamma delta epsilon
      zeta eta A B c ((1 / 3 : k) • (A * B) + d) e)
    (11 * n - 2 * h - 1) hload hrowTwo
  exact residualRowTwo_leftChamber_ne_zero68_of_leftLoadWindow
    A B c d e n g h hn hg hgh hsmall hstrict hleft hA hB hc hd he hQ
    hclass.2.2.1 hclass.2.2.2.1 hcoeff0

/-- The empty chamber yields `l = 0` for composition with the tracked
residual load-zero endgame. -/
theorem polynomialSecondaryResidualLeftLoadWindow68_loadL_eq_zero
    (l alpha beta gamma delta epsilon zeta eta i4 i3 : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g)
    (hsmall : 2 * g < n) (hstrict : n < 3 * g)
    (hgh : g < h) (hleft : 2 * h < n)
    (hA : A.natDegree ≤ 2 * n)
    (ha : A.coeff (2 * n) ≠ 0)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hsupport : B.coeff (3 * n - g) ≠ 0 ∨ c.coeff (4 * n - g) ≠ 0)
    (hattained : d.coeff (5 * n - h) ≠ 0 ∨ e.coeff (6 * n - h) ≠ 0)
    (hi4 : cubicFirstIntegralFourPolynomial68
      l beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hi3 : cubicFirstIntegralThreePolynomial68
      l beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i3)
    (hrowTwo :
      secondaryResidualRowTwoPolynomial68 A B c d e +
        cubicLoadRowTwoPolynomial68 l alpha beta gamma delta epsilon
          zeta eta A B c ((1 / 3 : k) • (A * B) + d) e = 0) :
    l = 0 :=
  (polynomialSecondaryResidualLeftLoadWindow68_impossible
    l alpha beta gamma delta epsilon zeta eta i4 i3 A B c d e n g h
    hn hg hsmall hstrict hgh hleft hA ha hB hc hd he hsupport hattained
    hi4 hi3 hrowTwo).elim

theorem integratedPolynomialLowerSystem68_residualLeftLoadWindow_loadL_eq_zero
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g)
    (hsmall : 2 * g < n) (hstrict : n < 3 * g)
    (hgh : g < h) (hleft : 2 * h < n)
    (hC0 : C0 = (1 / 3 : k) • A ^ 2 + c)
    (hD : D = (1 / 3 : k) • (A * B) + d)
    (hE : E = (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)
    (hA : A.natDegree ≤ 2 * n)
    (ha : A.coeff (2 * n) ≠ 0)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hsupport : B.coeff (3 * n - g) ≠ 0 ∨ c.coeff (4 * n - g) ≠ 0)
    (hattained : d.coeff (5 * n - h) ≠ 0 ∨ e.coeff (6 * n - h) ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E) :
    l = 0 := by
  obtain ⟨i4, hi4⟩ := hsys.firstFour
  obtain ⟨i3, hi3⟩ := hsys.firstThree
  have hi4c : cubicFirstIntegralFourPolynomial68
      l beta gamma delta epsilon zeta A B c D e = C i4 := by
    have h := hi4
    rw [hC0, hE, firstIntegralFourPolynomial68_cubicCoordinates] at h
    exact h
  have hi3c : cubicFirstIntegralThreePolynomial68
      l beta gamma delta epsilon zeta A B c D e = C i3 := by
    have h := hi3
    rw [hC0, hE, firstIntegralThreePolynomial68_cubicCoordinates] at h
    exact h
  have hi4d : cubicFirstIntegralFourPolynomial68
      l beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4 := by
    simpa [hD] using hi4c
  have hi3d : cubicFirstIntegralThreePolynomial68
      l beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i3 := by
    simpa [hD] using hi3c
  have hrowTwo := integratedPolynomialLowerSystem68_residualRowTwo
    l alpha beta gamma delta epsilon zeta eta terminal
    A B C0 D E c d e hC0 hD hE hsys
  exact polynomialSecondaryResidualLeftLoadWindow68_loadL_eq_zero
    l alpha beta gamma delta epsilon zeta eta i4 i3 A B c d e n g h
    hn hg hsmall hstrict hgh hleft hA ha hB hc hd he hsupport hattained
    hi4d hi3d hrowTwo

/-! ## Canonical expanded system -/

set_option maxHeartbeats 4000000 in
/-- On a maximal expanded system in `2g < n < 3g`, a residual gap with
`g < h` and `2h < n` forces `l = 0`. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_residualLeftLoadWindow_loadL_eq_zero68
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
    (hleft :
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
      g < h ∧ 2 * h < n) :
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
  change g < h ∧ 2 * h < n at hleft
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
  have hnotboth : ¬(d = 0 ∧ ee = 0) :=
    residualLeftLoadWindow_not_both_zero n h d ee hn hleft.2 rfl
  have hattained :
      d.coeff (5 * n - h) ≠ 0 ∨ ee.coeff (6 * n - h) ≠ 0 := by
    simpa only [h] using
      secondaryResidualGap68_boundary_attained n d ee hdbase hebase hnotboth
  have hboundary :=
    maximalExpandedIntegratedPolynomialLowerSystem_secondarySmallGapBoundary68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hchamber.1)
  have hsupport :
      Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0 := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hboundary.2.2
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hDrec : De = (1 / 3 : k) • (Ae * Be) + d := by
    simpa only [d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
  have hErec :
      Ee = (1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee := by
    calc
      Ee = (1 / 3 : k) • (Ae * Ce) - (2 / 27 : k) • Ae ^ 3 + ee := by
        simpa only [ee] using cubicEDefectPolynomial68_reconstruct Ae Ce Ee
      _ = (1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee := by
        rw [hCrec]
        apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
        simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
          map_pow, RatFunc.algebraMap_C]
        simp only [map_div₀, map_ofNat, map_one]
        ring
  obtain ⟨i4, hi4⟩ := hsys.firstFour
  obtain ⟨i3, hi3⟩ := hsys.firstThree
  have hi4e : firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i4 := by
    have hx := congrArg (expand k 60) hi4
    simpa [Ae, Be, Ce, De, Ee, expand_firstIntegralFourPolynomial68] using hx
  have hi3e : firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i3 := by
    have hx := congrArg (expand k 60) hi3
    simpa [Ae, Be, Ce, De, Ee, expand_firstIntegralThreePolynomial68] using hx
  have hi4c := hi4e
  rw [hCrec, hErec, firstIntegralFourPolynomial68_cubicCoordinates,
    hDrec] at hi4c
  have hi3c := hi3e
  rw [hCrec, hErec, firstIntegralThreePolynomial68_cubicCoordinates,
    hDrec] at hi3c
  have h2e : lowerRowTwoPolynomial68
      (integratedSPolynomial68 l alpha beta delta Ae Be Ce De)
      (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) Be Ce De Ee = 0 := by
    dsimp only [Ae, Be, Ce, De, Ee]
    rw [← expand_integratedSPolynomial68, ← expand_integratedTPolynomial68,
      ← expand_integratedUPolynomial68, ← expand_integratedVPolynomial68,
      lowerRowTwoPolynomial68_expand, hsys.rowTwo, map_zero, zero_mul]
  have hrowTwo :
      let Crec := (1 / 3 : k) • Ae ^ 2 + ce
      let Drec := (1 / 3 : k) • (Ae * Be) + d
      let Erec := (1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee
      lowerRowTwoPolynomial68
        (integratedSPolynomial68 l alpha beta delta Ae Be Crec Drec)
        (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Crec Drec
          Erec)
        (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Crec
          Drec Erec)
        (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
          Ae Be Crec Drec Erec) Be Crec Drec Erec = 0 := by
    simp only
    rw [← hCrec, ← hDrec, ← hErec]
    exact h2e
  have hsum := polynomialSecondaryResidualRowTwo68
    l alpha beta gamma delta epsilon zeta eta Ae Be ce d ee hrowTwo
  exact polynomialSecondaryResidualLeftLoadWindow68_loadL_eq_zero
    l alpha beta gamma delta epsilon zeta eta i4 i3 Ae Be ce d ee n g h
    hn hg hchamber.1 hchamber.2 hleft.1 hleft.2 hA ha hB hc
    hbounds.1 hbounds.2 hsupport hattained hi4c hi3c hsum

set_option maxHeartbeats 2000000 in
/-- After the left load window forces `l = 0`, the tracked residual
load-zero endgame closes the canonical `2g < n` branch. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_residualLeftLoadWindow_impossible68
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
    (hleft :
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
      g < h ∧ 2 * h < n) :
    False := by
  have hl :=
    maximalExpandedIntegratedPolynomialLowerSystem_residualLeftLoadWindow_loadL_eq_zero68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys hchamber hleft
  exact maximalExpandedIntegratedPolynomialLowerSystem_secondaryResidualLoadZero_impossible68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys hl (by
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      exact hchamber.1)

#print axioms cubicFirstIntegralFourPolynomial68_coeff_eightRadius_of_leftLoadWindow
#print axioms cubicFirstIntegralFourPolynomial68_imp_loadL_eq_zero_of_leftLoadWindow
#print axioms residualIncidenceQ68_degree_le_eightRadius_of_leftLoadWindow
#print axioms residualRowTwo_coeff_leftChamber68_of_leftLoadWindow
#print axioms polynomialSecondaryResidualLeftLoadWindow68_impossible
#print axioms polynomialSecondaryResidualLeftLoadWindow68_loadL_eq_zero
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_residualLeftLoadWindow_loadL_eq_zero68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_residualLeftLoadWindow_impossible68

end Max11DegreeRoutes
