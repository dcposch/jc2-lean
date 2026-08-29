import LowScale68SecondaryRelaxedFirstFace

/-! # Canonical expanded wrappers for the relaxed `l = 0` first secondary face

The checked extraction in `LowScale68SecondaryRelaxedFirstFace` packages the
five-face as `IntegratedPolynomialLowerSystem68`, whose terminal row is the
constant `C terminal`.  Source input is that system on `A,B,C0,D,E`.  After
the canonical expansion `Ae := expand k 60 A` (and likewise `Be,Ce,De,Ee`),
rows two and one remain zero, but row zero becomes
`C terminal * (60 * X^59)`.  Expanded coordinates therefore must **not** be
repackaged as `IntegratedPolynomialLowerSystem68`.

This file generalizes the face extraction to exact `I4`/`I3`, vanishing
row-two and row-one polynomials, and a single vanishing target coefficient
of row zero.  The canonical wrappers build `hi4e, hi3e, h2e, h1e, h0e` as in
`LowScale68SecondarySmallGap` / `LowScale68SecondaryResidualDouble` and
show the first-secondary index exceeds 59 from weighted-radius positivity.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section RelaxedCanonicalFace68

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Radius, reconstruction, and expanded rows -/

theorem weightedRadius68_ge_ten (A B C0 D E : k[X])
    (hn : 0 < weightedRadius68 A B C0 D E) :
    10 ≤ weightedRadius68 A B C0 D E := by
  dsimp only [weightedRadius68] at hn ⊢
  omega

theorem firstSecondaryRowZeroIndex68_gt_fiftyNine
    (n g : ℕ) (hn : 10 ≤ n) (hrel : 2 * g < 3 * n) :
    59 < 13 * n - 2 * g - 1 := by
  omega

theorem cubicEDefectPolynomial68_eq_cubicCoordinates
    (A C0 E : k[X]) :
    E = (1 / 27 : k) • A ^ 3 +
      (1 / 3 : k) • (A * cubicCDefectPolynomial68 A C0) +
      cubicEDefectPolynomial68 A C0 E := by
  let c := cubicCDefectPolynomial68 A C0
  let e := cubicEDefectPolynomial68 A C0 E
  have hC : C0 = (1 / 3 : k) • A ^ 2 + c :=
    cubicCDefectPolynomial68_reconstruct A C0
  change E = (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
  calc
    E = (1 / 3 : k) • (A * C0) - (2 / 27 : k) • A ^ 3 + e := by
      simpa only [e] using cubicEDefectPolynomial68_reconstruct A C0 E
    _ = (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e := by
      rw [hC]
      apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
      simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
        map_pow, RatFunc.algebraMap_C]
      simp only [map_div₀, map_ofNat, map_one]
      ring

theorem expand_firstIntegralFourPolynomial68_of_eq
    (l beta gamma delta epsilon zeta i4 : k) (A B C0 D E : k[X])
    (hI4 : firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
      A B C0 D E = C i4) :
    firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
      (expand k 60 A) (expand k 60 B) (expand k 60 C0) (expand k 60 D)
      (expand k 60 E) = C i4 := by
  have h := congrArg (expand k 60) hI4
  simpa [expand_firstIntegralFourPolynomial68] using h

theorem expand_firstIntegralThreePolynomial68_of_eq
    (l beta gamma delta epsilon zeta i3 : k) (A B C0 D E : k[X])
    (hI3 : firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
      A B C0 D E = C i3) :
    firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
      (expand k 60 A) (expand k 60 B) (expand k 60 C0) (expand k 60 D)
      (expand k 60 E) = C i3 := by
  have h := congrArg (expand k 60) hI3
  simpa [expand_firstIntegralThreePolynomial68] using h

theorem expand_lowerRowTwoPolynomial68_of_system
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X])
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E) :
    lowerRowTwoPolynomial68
      (integratedSPolynomial68 l alpha beta delta
        (expand k 60 A) (expand k 60 B) (expand k 60 C0) (expand k 60 D))
      (integratedTPolynomial68 l alpha beta gamma epsilon
        (expand k 60 A) (expand k 60 B) (expand k 60 C0) (expand k 60 D)
        (expand k 60 E))
      (integratedUPolynomial68 l alpha beta gamma delta zeta
        (expand k 60 A) (expand k 60 B) (expand k 60 C0) (expand k 60 D)
        (expand k 60 E))
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        (expand k 60 A) (expand k 60 B) (expand k 60 C0) (expand k 60 D)
        (expand k 60 E))
      (expand k 60 B) (expand k 60 C0) (expand k 60 D) (expand k 60 E) =
        0 := by
  rw [← expand_integratedSPolynomial68, ← expand_integratedTPolynomial68,
    ← expand_integratedUPolynomial68, ← expand_integratedVPolynomial68,
    lowerRowTwoPolynomial68_expand, hsys.rowTwo, map_zero, zero_mul]

theorem expand_lowerRowOnePolynomial68_of_system
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X])
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E) :
    lowerRowOnePolynomial68
      (integratedTPolynomial68 l alpha beta gamma epsilon
        (expand k 60 A) (expand k 60 B) (expand k 60 C0) (expand k 60 D)
        (expand k 60 E))
      (integratedUPolynomial68 l alpha beta gamma delta zeta
        (expand k 60 A) (expand k 60 B) (expand k 60 C0) (expand k 60 D)
        (expand k 60 E))
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        (expand k 60 A) (expand k 60 B) (expand k 60 C0) (expand k 60 D)
        (expand k 60 E))
      (expand k 60 C0) (expand k 60 D) (expand k 60 E) = 0 := by
  rw [← expand_integratedTPolynomial68, ← expand_integratedUPolynomial68,
    ← expand_integratedVPolynomial68, lowerRowOnePolynomial68_expand,
    hsys.rowOne, map_zero, zero_mul]

theorem expand_lowerRowZeroPolynomial68_of_system
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X])
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E) :
    lowerRowZeroPolynomial68
      (integratedUPolynomial68 l alpha beta gamma delta zeta
        (expand k 60 A) (expand k 60 B) (expand k 60 C0) (expand k 60 D)
        (expand k 60 E))
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        (expand k 60 A) (expand k 60 B) (expand k 60 C0) (expand k 60 D)
        (expand k 60 E))
      (expand k 60 D) (expand k 60 E) =
        C terminal * (60 * (X ^ 59 : k[X])) := by
  rw [← expand_integratedUPolynomial68, ← expand_integratedVPolynomial68,
    lowerRowZeroPolynomial68_expand, hsys.rowZero, expand_C]
  norm_num

theorem expand_lowerRowZeroPolynomial68_coeff_eq_zero_of_index_gt
    (terminal : k) (U V D E : k[X]) (idx : ℕ)
    (h0e : lowerRowZeroPolynomial68 U V D E =
      C terminal * (60 * (X ^ 59 : k[X])))
    (hidx : 59 < idx) :
    (lowerRowZeroPolynomial68 U V D E).coeff idx = 0 := by
  rw [h0e]
  apply coeff_eq_zero_of_natDegree_lt
  have hdegree :
      (C terminal * (60 * (X ^ 59 : k[X]))).natDegree ≤ 59 := by
    compute_degree
  exact hdegree.trans_lt hidx

/-! ## Generalized face extraction: exact I4/I3, rows, target coefficient -/

set_option maxHeartbeats 3000000 in
theorem polynomialSecondaryFace68_of_loadL
    (l alpha beta gamma delta epsilon zeta eta i4 i3 : k)
    (A B C0 c D E e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hl : l = 0) (hg_lt : g < n)
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
  have hrel : 2 * g < 3 * n := by omega
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
  rw [integratedLowerRowOnePolynomial68_secondaryCoeff_of_loadL
    l alpha beta gamma delta epsilon zeta eta A B c D e n g
    hn hg hl hg_lt hA hB hc hD he] at hone
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

theorem polynomialSecondaryClassified68_of_loadL
    (l alpha beta gamma delta epsilon zeta eta i4 i3 : k)
    (A B C0 c D E e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hl : l = 0) (hg_lt : g < n)
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
  have hrel : 2 * g < 3 * n := by omega
  exact firstSecondaryFace68_classify_of_two_mul_gap_lt_three_mul_radius n g
    (A.coeff (2 * n)) (B.coeff (3 * n - g))
    (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
    (e.coeff (6 * n - g)) ha hn hrel
    (polynomialSecondaryFace68_of_loadL
      l alpha beta gamma delta epsilon zeta eta i4 i3
      A B C0 c D E e n g hn hg hl hg_lt hA hB hc hD he ha hC0 hE0
      hI4 hI3 hrowTwo hrowOne hrowZero)

set_option maxHeartbeats 3000000 in
theorem polynomialSecondaryFace68_of_loadL_alpha
    (l alpha beta gamma delta epsilon zeta eta i4 i3 : k)
    (A B C0 c D E e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hl : l = 0) (halpha : alpha = 0)
    (hrel : 2 * g < 3 * n)
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
  rw [integratedLowerRowOnePolynomial68_secondaryCoeff_of_loadL_alpha
    l alpha beta gamma delta epsilon zeta eta A B c D e n g
    hn hg hl halpha hrel hA hB hc hD he] at hone
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

theorem polynomialSecondaryClassified68_of_loadL_alpha
    (l alpha beta gamma delta epsilon zeta eta i4 i3 : k)
    (A B C0 c D E e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hl : l = 0) (halpha : alpha = 0)
    (hrel : 2 * g < 3 * n)
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
    (polynomialSecondaryFace68_of_loadL_alpha
      l alpha beta gamma delta epsilon zeta eta i4 i3
      A B C0 c D E e n g hn hg hl halpha hrel hA hB hc hD he ha hC0 hE0
      hI4 hI3 hrowTwo hrowOne hrowZero)

set_option maxHeartbeats 3000000 in
/-- Without `F₁`, the relaxed chamber `2g < 3n` after `l = 0` still
supplies `F₄`, `F₃`, and `F₀`, leaving three algebraic families. -/
theorem polynomialSecondaryFourThreeZeroEquations68_of_equations
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
    (hrowZero : (lowerRowZeroPolynomial68
      (integratedUPolynomial68 l alpha beta gamma delta zeta A B C0 D E)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        A B C0 D E) D E).coeff (13 * n - 2 * g - 1) = 0) :
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
  have hinv := polynomialSecondaryInvariantEquations68_of_loadL
    l beta gamma delta epsilon zeta i4 i3 A B C0 c D E e n g
    hn hg hl hrel hA hB hc hD he hC0 hE0 hI4 hI3
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
  exact firstSecondaryFourThreeZero68_classify
    (A.coeff (2 * n)) (B.coeff (3 * n - g))
    (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
    (e.coeff (6 * n - g)) ha hinv.1 hinv.2 hzero0

/-! ## Canonical maximal-expanded wrappers -/

set_option maxHeartbeats 4000000 in
/-- On the canonical expanded system, after `l = 0` in the chamber `g < n`
needed by the second one-form, the first secondary face classifies as
`e = 0` and `a*b = 3*d`. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_firstSecondaryClassified68_of_loadL
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hl : l = 0)
    (hgap :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      g < n) :
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
  change g < n at hgap
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
  have hrel : 2 * g < 3 * n := by omega
  have h0target : (lowerRowZeroPolynomial68
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) De Ee).coeff (13 * n - 2 * g - 1) = 0 :=
    expand_lowerRowZeroPolynomial68_coeff_eq_zero_of_index_gt
      terminal _ _ _ _ _ h0e
      (firstSecondaryRowZeroIndex68_gt_fiftyNine n g hnlarge hrel)
  exact polynomialSecondaryClassified68_of_loadL
    l alpha beta gamma delta epsilon zeta eta i4 i3
    Ae Be Ce ce De Ee ee n g hn hg hl hgap hA hB hc hD he ha
    hCrec hErec hi4e hi3e h2e h1e h0target

set_option maxHeartbeats 4000000 in
/-- After the extra vanishing `alpha = 0`, the same classification is
available throughout the relaxed chamber `2g < 3n`. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_firstSecondaryClassified68_of_loadL_alpha
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hl : l = 0) (halpha : alpha = 0)
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
  exact polynomialSecondaryClassified68_of_loadL_alpha
    l alpha beta gamma delta epsilon zeta eta i4 i3
    Ae Be Ce ce De Ee ee n g hn hg hl halpha hrel hA hB hc hD he ha
    hCrec hErec hi4e hi3e h2e h1e h0target

set_option maxHeartbeats 4000000 in
/-- Four-equation family on the canonical expanded system after `l = 0`
throughout `2g < 3n`, without the second one-form. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_firstSecondaryFourThreeZero68_of_loadL
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
    (ee.coeff (6 * n - g) = 0 ∧
        Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
          3 * De.coeff (5 * n - g)) ∨
      (ee.coeff (6 * n - g) = 0 ∧
        ce.coeff (4 * n - g) = 0 ∧
        Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
          De.coeff (5 * n - g)) ∨
      (Be.coeff (3 * n - g) = 0 ∧
        ce.coeff (4 * n - g) = 0 ∧
        De.coeff (5 * n - g) = 0) := by
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
  change (ee.coeff (6 * n - g) = 0 ∧
      Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
        3 * De.coeff (5 * n - g)) ∨
    (ee.coeff (6 * n - g) = 0 ∧
      ce.coeff (4 * n - g) = 0 ∧
      Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
        De.coeff (5 * n - g)) ∨
    (Be.coeff (3 * n - g) = 0 ∧
      ce.coeff (4 * n - g) = 0 ∧
      De.coeff (5 * n - g) = 0)
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
  exact polynomialSecondaryFourThreeZeroEquations68_of_equations
    l alpha beta gamma delta epsilon zeta eta i4 i3
    Ae Be Ce ce De Ee ee n g hn hg hl hrel hA hB hc hD he ha
    hCrec hErec hi4e hi3e h0target

end RelaxedCanonicalFace68

#print axioms weightedRadius68_ge_ten
#print axioms firstSecondaryRowZeroIndex68_gt_fiftyNine
#print axioms cubicEDefectPolynomial68_eq_cubicCoordinates
#print axioms expand_firstIntegralFourPolynomial68_of_eq
#print axioms expand_firstIntegralThreePolynomial68_of_eq
#print axioms expand_lowerRowTwoPolynomial68_of_system
#print axioms expand_lowerRowOnePolynomial68_of_system
#print axioms expand_lowerRowZeroPolynomial68_of_system
#print axioms expand_lowerRowZeroPolynomial68_coeff_eq_zero_of_index_gt
#print axioms polynomialSecondaryFace68_of_loadL
#print axioms polynomialSecondaryClassified68_of_loadL
#print axioms polynomialSecondaryFace68_of_loadL_alpha
#print axioms polynomialSecondaryClassified68_of_loadL_alpha
#print axioms polynomialSecondaryFourThreeZeroEquations68_of_equations
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_firstSecondaryClassified68_of_loadL
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_firstSecondaryClassified68_of_loadL_alpha
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_firstSecondaryFourThreeZero68_of_loadL

end Max11DegreeRoutes
