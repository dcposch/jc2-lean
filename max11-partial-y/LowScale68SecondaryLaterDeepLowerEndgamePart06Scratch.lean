import LowScale68SecondaryLaterDeepLowerEndgamePart05Scratch

/-! # Later-deep lower `(6,8)` window `3n ≤ 2g ≤ 5n`

Tracked I4 already records the mixed walls `2g = 3n` and `2g = 5n` and
the ordinary `F₄` face between them.  This module extracts the matching
I3 face, proves that row-one is load-free after the extra `alpha`/`c`/`gamma`
cancellations, and closes the open interval `3n < 2g < 5n` to the ordinary
five-face `e = 0`, `a*b = 3d`.  The two walls keep mixed I4 together with
mixed `F₂`/`F₀`; they are not empty.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerEndgame68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Chamber arithmetic -/

/-! ## I3 at `10n-2g` -/

/-! ## Degree bounds for the extra-cancelled one-forms -/

/-! ## Row-one load below `12n-2g-1` -/

set_option maxHeartbeats 6000000 in
theorem cubicLoadRowOneDeepGapRestPolynomial68_degree_lt_firstFace_of_laterDeepLower
    (alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g)
    (hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadRowOneDeepGapRestPolynomial68 alpha beta gamma delta
      epsilon zeta eta A B c D e).natDegree < 12 * n - 2 * g - 1 := by
  let Ur := cubicLoadUAlphaRestPolynomial68 beta gamma delta zeta A B c
  let Vr := cubicLoadVAlphaRestPolynomial68 alpha beta gamma delta epsilon
    eta A B c D e
  let Vlow := cubicLoadVAlphaLowPolynomial68 beta gamma delta epsilon eta
    A B c D
  let C0c := (1 / 3 : k) • A ^ 2
  let Ec := (1 / 27 : k) • A ^ 3
  let Er := (1 / 3 : k) • (A * c) + e
  let E := Ec + Er
  have hUr : Ur.natDegree ≤ 4 * n :=
    cubicLoadUAlphaRestPolynomial68_degree_le beta gamma delta zeta
      A B c n g hA hB hc
  have hVlow : Vlow.natDegree ≤ 5 * n - g :=
    cubicLoadVAlphaLowPolynomial68_degree_le_of_laterDeepLower
      beta gamma delta epsilon eta A B c D n g hn hwindow hA hB hc hD
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
  have hTrβ : (((5 / 6 * beta : k) • B + C epsilon)).natDegree ≤
      3 * n - g := by
    compute_degree
    omega
  have hbound (u v : ℕ) (hv : 0 < v)
      (hu : u + v - 1 < 12 * n - 2 * g - 1) :
      ∀ p q : k[X], p.natDegree ≤ u → q.natDegree ≤ v →
        (p * derivative q).natDegree < 12 * n - 2 * g - 1 :=
    fun p q hp hq =>
      deepGap_natDegree_mul_derivative_lt68 p q u v
        (12 * n - 2 * g - 1) hv hp hq hu
  have h1 : (Ur * derivative D).natDegree < 12 * n - 2 * g - 1 :=
    hbound (4 * n) (5 * n - g) (by omega) (by omega) Ur D hUr hD
  have h2 : ((alpha • c) * derivative Er).natDegree <
      12 * n - 2 * g - 1 :=
    hbound (4 * n - g) (6 * n - g) (by omega) (by omega)
      (alpha • c) Er ((natDegree_smul_le alpha c).trans hc) hEr
  have h3 : (((2 / 3 * gamma : k) • A) * derivative Er).natDegree <
      12 * n - 2 * g - 1 :=
    hbound (2 * n) (6 * n - g) (by omega) (by omega)
      ((2 / 3 * gamma : k) • A) Er
      ((natDegree_smul_le _ A).trans hA) hEr
  have h4 : (((5 / 6 * beta : k) • B + C epsilon) * derivative E).natDegree <
      12 * n - 2 * g - 1 :=
    hbound (3 * n - g) (6 * n) (by omega) (by omega)
      ((5 / 6 * beta : k) • B + C epsilon) E hTrβ hE
  have h5 : (C0c * derivative Vlow).natDegree < 12 * n - 2 * g - 1 :=
    hbound (4 * n) (5 * n - g) (by omega) (by omega) C0c Vlow hC0c hVlow
  have h6 : (c * derivative Vr).natDegree < 12 * n - 2 * g - 1 := by
    rcases le_total g (2 * n) with hgle | hnge
    · have hVr : Vr.natDegree ≤ 6 * n - g :=
        cubicLoadVAlphaRestPolynomial68_degree_le_of_laterDeepLower_le_two
          alpha beta gamma delta epsilon eta A B c D e n g hn hwindow
          hgle hA hB hc hD he
      exact hbound (4 * n - g) (6 * n - g) (by omega) (by omega) c Vr hc hVr
    · have hVr : Vr.natDegree ≤ 4 * n :=
        cubicLoadVAlphaRestPolynomial68_degree_le_of_laterDeepLower_ge_two
          alpha beta gamma delta epsilon eta A B c D e n g hn hwindow
          hnge hA hB hc hD he
      exact hbound (4 * n - g) (4 * n) (by omega) (by omega) c Vr hc hVr
  have h7 : (D * derivative Ur).natDegree < 12 * n - 2 * g - 1 :=
    hbound (5 * n - g) (4 * n) (by omega) (by omega) D Ur hD hUr
  have h2s := deepGap_natDegree_smul_lt68 (2 : k) h2
  have h3s := deepGap_natDegree_smul_lt68 (2 : k) h3
  have h4s := deepGap_natDegree_smul_lt68 (2 : k) h4
  have h5s := deepGap_natDegree_smul_lt68 (2 : k) h5
  have h6s := deepGap_natDegree_smul_lt68 (2 : k) h6
  change (Ur * derivative D +
      (2 : k) • ((alpha • c) * derivative Er) +
      (2 : k) • (((2 / 3 * gamma : k) • A) * derivative Er) +
      (2 : k) • (((5 / 6 * beta : k) • B + C epsilon) * derivative E) -
      (2 : k) • (C0c * derivative Vlow) -
      (2 : k) • (c * derivative Vr) -
      D * derivative Ur).natDegree < _
  exact deepGap_natDegree_sub_lt
    (deepGap_natDegree_sub_lt
      (deepGap_natDegree_sub_lt
        (deepGap_natDegree_add_lt
          (deepGap_natDegree_add_lt
            (deepGap_natDegree_add_lt h1 h2s) h3s) h4s) h5s) h6s) h7

end LaterDeepLowerEndgame68
end Max11DegreeRoutes
