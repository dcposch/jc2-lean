import LowScale68SecondaryLaterDeepLowerEndgamePart06Scratch

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

set_option maxHeartbeats 2000000 in
theorem cubicLoadRowOnePolynomial68_degree_lt_firstFace_of_laterDeepLower
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hl : l = 0)
    (hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadRowOnePolynomial68 l alpha beta gamma delta epsilon zeta eta
      A B c D e).natDegree < 12 * n - 2 * g - 1 := by
  rw [cubicLoadRowOnePolynomial68_eq_alphaRest l alpha beta gamma delta
    epsilon zeta eta A B c D e hl,
    cubicLoadRowOneAlphaRestPolynomial68_eq_deepGapRest']
  exact cubicLoadRowOneDeepGapRestPolynomial68_degree_lt_firstFace_of_laterDeepLower
    alpha beta gamma delta epsilon zeta eta A B c D e n g
    hn hg hwindow hA hB hc hD he

set_option maxHeartbeats 2000000 in
theorem cubicLoadTAlphaRestPolynomial68_degree_le_of_laterDeepLower
    (alpha beta gamma epsilon : k) (A B c : k[X]) (n g : ℕ)
    (hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g) :
    (cubicLoadTAlphaRestPolynomial68 alpha beta gamma epsilon A B c).natDegree ≤
      max (4 * n - g) (2 * n) := by
  have hAc : (alpha • c).natDegree ≤ 4 * n - g :=
    (natDegree_smul_le alpha c).trans hc
  have hB' : ((5 / 6 * beta : k) • B).natDegree ≤ 4 * n - g :=
    (natDegree_smul_le _ B).trans (hB.trans (by omega))
  have hA' : ((2 / 3 * gamma : k) • A).natDegree ≤ 2 * n :=
    (natDegree_smul_le _ A).trans hA
  have hC : (C epsilon).natDegree ≤ 2 * n := by
    rw [natDegree_C]
    exact Nat.zero_le _
  have hleft : (alpha • c + (5 / 6 * beta : k) • B).natDegree ≤
      max (4 * n - g) (2 * n) :=
    ((natDegree_add_le _ _).trans (max_le hAc hB')).trans (le_max_left _ _)
  have hmid : ((2 / 3 * gamma : k) • A).natDegree ≤
      max (4 * n - g) (2 * n) :=
    hA'.trans (le_max_right _ _)
  have hC' : (C epsilon).natDegree ≤ max (4 * n - g) (2 * n) :=
    hC.trans (le_max_right _ _)
  simp only [cubicLoadTAlphaRestPolynomial68]
  refine (natDegree_add_le _ _).trans (max_le ?_ hC')
  exact (natDegree_add_le _ _).trans (max_le hleft hmid)

end LaterDeepLowerEndgame68
end Max11DegreeRoutes
