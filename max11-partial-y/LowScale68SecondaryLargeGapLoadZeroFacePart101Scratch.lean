import LowScale68SecondaryRelaxedCanonical
import LowScale68SecondaryLargeGapResidual

/-! # Residual faces in the large-gap load-zero chamber

The tracked theorems
`maximalExpandedIntegratedPolynomialLowerSystem_l_eq_zero_of_radius_lt_twoGap68`
and
`maximalExpandedIntegratedPolynomialLowerSystem_firstSecondaryClassified68_of_loadL`
already give `l = 0`, `ee.coeff(6n-g) = 0` and `a*b = 3*D_top` on
`n < 2g` and `g < n`.  Every first-face bound `2g < 3n` is free from
`g < n`.  This module turns those two coefficient cancellations into
strict residual degree drops, selects the residual gap `h > g`, and
extracts the ordinary residual middle and double I4/I3 faces.

After `l = 0` the heaviest quartic load is `beta A^3` at `6n`, the
heaviest cubic load is `beta A^2 B` at `7n-g`, and the heaviest row-two
product is `Ul C0'` at `9n-g-1`.  All three sit strictly below every
displayed residual index throughout `g < n`.  Row one at `12n-3g-1`
  remains load-free only on the extra window `3g < 2n`.  Closing the
chamber still needs residual one-forms and their row-one load split; this
module supplies their canonical classification and invariant-face inputs.

The existing `of_twoGap` / first-load-wall lemmas cannot be cited: their
`2g < n` or `2g = n` hypotheses are false even though the arithmetic
with `l = 0` and `g < n` remains strict.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LargeGapLoadZeroEndgame68

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Chamber arithmetic -/

theorem largeGapLoadZero_two_mul_gap_lt_three_radius
    (n g : ℕ) (hg_lt : g < n) :
    2 * g < 3 * n := by
  omega

theorem largeGapLoadZero_index_pos (n g : ℕ) (hn : 0 < n)
    (hg_lt : g < n) {w : ℕ} (hw : 1 < w) :
    0 < w * n - g := by
  have hg_le : g ≤ n := Nat.le_of_lt hg_lt
  have hn_lt : n < w * n :=
    calc
      n = n * 1 := (Nat.mul_one n).symm
      _ < n * w := Nat.mul_lt_mul_of_pos_left hw hn
      _ = w * n := Nat.mul_comm n w
  exact Nat.sub_pos_of_lt (lt_of_le_of_lt hg_le hn_lt)

theorem natDegree_lt_of_le_of_coeff_eq_zero68
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

theorem secondaryDDefectPolynomial68_degree_lt_of_largeGapLoadZero
    (A B D : k[X]) (n g : ℕ) (hn : 0 < n) (hg : 0 < g)
    (hlarge : n < 2 * g) (hg_lt : g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (hrel : A.coeff (2 * n) * B.coeff (3 * n - g) =
      3 * D.coeff (5 * n - g)) :
    (secondaryDDefectPolynomial68 A B D).natDegree < 5 * n - g := by
  have hg3 : g ≤ 3 * n := Nat.le_of_lt (hg_lt.trans (by omega))
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
    linear_combination (-1 / 3 : k) * hrel
  exact natDegree_lt_of_le_of_coeff_eq_zero68 _
    (5 * n - g) (largeGapLoadZero_index_pos n g hn hg_lt (by decide))
    hdegree hcoeff

theorem firstSecondaryResidualDegreeDrops68_of_largeGapLoadZero
    (A B D e : k[X]) (n g : ℕ) (hn : 0 < n) (hg : 0 < g)
    (hlarge : n < 2 * g) (hg_lt : g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (hrel : A.coeff (2 * n) * B.coeff (3 * n - g) =
      3 * D.coeff (5 * n - g))
    (hetop : e.coeff (6 * n - g) = 0) :
    (secondaryDDefectPolynomial68 A B D).natDegree < 5 * n - g ∧
      e.natDegree < 6 * n - g := by
  refine ⟨secondaryDDefectPolynomial68_degree_lt_of_largeGapLoadZero A B D n g
    hn hg hlarge hg_lt hA hB hD hrel, ?_⟩
  exact natDegree_lt_of_le_of_coeff_eq_zero68 e (6 * n - g)
    (largeGapLoadZero_index_pos n g hn hg_lt (by decide)) he hetop

end LargeGapLoadZeroEndgame68
end Max11DegreeRoutes
/-! # Residual faces in the large-gap load-zero chamber

The tracked theorems
`maximalExpandedIntegratedPolynomialLowerSystem_l_eq_zero_of_radius_lt_twoGap68`
and
`maximalExpandedIntegratedPolynomialLowerSystem_firstSecondaryClassified68_of_loadL`
already give `l = 0`, `ee.coeff(6n-g) = 0` and `a*b = 3*D_top` on
`n < 2g` and `g < n`.  Every first-face bound `2g < 3n` is free from
`g < n`.  This module turns those two coefficient cancellations into
strict residual degree drops, selects the residual gap `h > g`, and
extracts the ordinary residual middle and double I4/I3 faces.

After `l = 0` the heaviest quartic load is `beta A^3` at `6n`, the
heaviest cubic load is `beta A^2 B` at `7n-g`, and the heaviest row-two
product is `Ul C0'` at `9n-g-1`.  All three sit strictly below every
displayed residual index throughout `g < n`.  Row one at `12n-3g-1`
  remains load-free only on the extra window `3g < 2n`.  Closing the
chamber still needs residual one-forms and their row-one load split; this
module supplies their canonical classification and invariant-face inputs.

The existing `of_twoGap` / first-load-wall lemmas cannot be cited: their
`2g < n` or `2g = n` hypotheses are false even though the arithmetic
with `l = 0` and `g < n` remains strict.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LargeGapLoadZeroEndgame68

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Chamber arithmetic -/

/-! ## Residual degree drops after the classified face -/

/-! ## Canonical support, drops, and residual gap -/

/-- After `l = 0` on `n < 2g` with `g < n`, the first secondary face is
the ordinary pair `e = 0`, `a*b = 3 D_top`. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_largeGapLoadZeroClassified68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hlarge :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      n < 2 * g)
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
  change n < 2 * g at hlarge
  change g < n at hgap
  change l = 0 ∧ ee.coeff (6 * n - g) = 0 ∧
    Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
      3 * De.coeff (5 * n - g)
  have hl :=
    maximalExpandedIntegratedPolynomialLowerSystem_l_eq_zero_of_radius_lt_twoGap68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hlarge)
  have hclass :=
    maximalExpandedIntegratedPolynomialLowerSystem_firstSecondaryClassified68_of_loadL
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys hl (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hgap)
  change ee.coeff (6 * n - g) = 0 ∧
    Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
      3 * De.coeff (5 * n - g) at hclass
  exact ⟨hl, hclass.1, hclass.2⟩

end LargeGapLoadZeroEndgame68
end Max11DegreeRoutes
/-! # Residual faces in the large-gap load-zero chamber

The tracked theorems
`maximalExpandedIntegratedPolynomialLowerSystem_l_eq_zero_of_radius_lt_twoGap68`
and
`maximalExpandedIntegratedPolynomialLowerSystem_firstSecondaryClassified68_of_loadL`
already give `l = 0`, `ee.coeff(6n-g) = 0` and `a*b = 3*D_top` on
`n < 2g` and `g < n`.  Every first-face bound `2g < 3n` is free from
`g < n`.  This module turns those two coefficient cancellations into
strict residual degree drops, selects the residual gap `h > g`, and
extracts the ordinary residual middle and double I4/I3 faces.

After `l = 0` the heaviest quartic load is `beta A^3` at `6n`, the
heaviest cubic load is `beta A^2 B` at `7n-g`, and the heaviest row-two
product is `Ul C0'` at `9n-g-1`.  All three sit strictly below every
displayed residual index throughout `g < n`.  Row one at `12n-3g-1`
  remains load-free only on the extra window `3g < 2n`.  Closing the
chamber still needs residual one-forms and their row-one load split; this
module supplies their canonical classification and invariant-face inputs.

The existing `of_twoGap` / first-load-wall lemmas cannot be cited: their
`2g < n` or `2g = n` hypotheses are false even though the arithmetic
with `l = 0` and `g < n` remains strict.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LargeGapLoadZeroEndgame68

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Chamber arithmetic -/

/-! ## Residual degree drops after the classified face -/

/-! ## Canonical support, drops, and residual gap -/

/-- The classified large-gap load-zero chamber is genuinely supported by
`B` or the translated even coefficient `c`. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_largeGapLoadZeroBoundary68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hlarge :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      n < 2 * g)
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
    l = 0 ∧ ee.coeff (6 * n - g) = 0 ∧
      Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
        3 * De.coeff (5 * n - g) ∧
      (Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0) := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  change n < 2 * g at hlarge
  change g < n at hgap
  change l = 0 ∧ ee.coeff (6 * n - g) = 0 ∧
    Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
      3 * De.coeff (5 * n - g) ∧
    (Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0)
  have hclass :=
    maximalExpandedIntegratedPolynomialLowerSystem_largeGapLoadZeroClassified68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hlarge)
      (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hgap)
  change l = 0 ∧ ee.coeff (6 * n - g) = 0 ∧
    Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
      3 * De.coeff (5 * n - g) at hclass
  have hsecondary :=
    maximalExpandedIntegratedPolynomialLowerSystem_secondaryRadius68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  have hattained :
      Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0 ∨
        De.coeff (5 * n - g) ≠ 0 ∨ ee.coeff (6 * n - g) ≠ 0 := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
      hsecondary.2.2.2.2.2
  refine ⟨hclass.1, hclass.2.1, hclass.2.2, ?_⟩
  rcases hattained with hb | hc | hd | he
  · exact Or.inl hb
  · exact Or.inr hc
  · left
    intro hb0
    have hrel := hclass.2.2
    rw [hb0, mul_zero] at hrel
    have hd0 : De.coeff (5 * n - g) = 0 :=
      (mul_eq_zero.mp hrel.symm).resolve_left (by norm_num)
    exact hd hd0
  · exact (he hclass.2.1).elim

end LargeGapLoadZeroEndgame68
end Max11DegreeRoutes
/-! # Residual faces in the large-gap load-zero chamber

The tracked theorems
`maximalExpandedIntegratedPolynomialLowerSystem_l_eq_zero_of_radius_lt_twoGap68`
and
`maximalExpandedIntegratedPolynomialLowerSystem_firstSecondaryClassified68_of_loadL`
already give `l = 0`, `ee.coeff(6n-g) = 0` and `a*b = 3*D_top` on
`n < 2g` and `g < n`.  Every first-face bound `2g < 3n` is free from
`g < n`.  This module turns those two coefficient cancellations into
strict residual degree drops, selects the residual gap `h > g`, and
extracts the ordinary residual middle and double I4/I3 faces.

After `l = 0` the heaviest quartic load is `beta A^3` at `6n`, the
heaviest cubic load is `beta A^2 B` at `7n-g`, and the heaviest row-two
product is `Ul C0'` at `9n-g-1`.  All three sit strictly below every
displayed residual index throughout `g < n`.  Row one at `12n-3g-1`
  remains load-free only on the extra window `3g < 2n`.  Closing the
chamber still needs residual one-forms and their row-one load split; this
module supplies their canonical classification and invariant-face inputs.

The existing `of_twoGap` / first-load-wall lemmas cannot be cited: their
`2g < n` or `2g = n` hypotheses are false even though the arithmetic
with `l = 0` and `g < n` remains strict.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LargeGapLoadZeroEndgame68

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Chamber arithmetic -/

/-! ## Residual degree drops after the classified face -/

/-! ## Canonical support, drops, and residual gap -/

/-- The canonical expanded system on `n < 2g` and `g < n` has genuine
strict degree drop in both residual coordinates. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_largeGapLoadZeroResidualDrops68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hlarge :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      n < 2 * g)
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
  change n < 2 * g at hlarge
  change g < n at hgap
  change l = 0 ∧
    (secondaryDDefectPolynomial68 Ae Be De).natDegree < 5 * n - g ∧
    ee.natDegree < 6 * n - g
  have hclass :=
    maximalExpandedIntegratedPolynomialLowerSystem_largeGapLoadZeroClassified68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hlarge)
      (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hgap)
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
    firstSecondaryResidualDegreeDrops68_of_largeGapLoadZero Ae Be De ee n g
      hn hg hlarge hgap hA hB hD he hclass.2.2 hclass.2.1⟩

end LargeGapLoadZeroEndgame68
end Max11DegreeRoutes
/-! # Residual faces in the large-gap load-zero chamber

The tracked theorems
`maximalExpandedIntegratedPolynomialLowerSystem_l_eq_zero_of_radius_lt_twoGap68`
and
`maximalExpandedIntegratedPolynomialLowerSystem_firstSecondaryClassified68_of_loadL`
already give `l = 0`, `ee.coeff(6n-g) = 0` and `a*b = 3*D_top` on
`n < 2g` and `g < n`.  Every first-face bound `2g < 3n` is free from
`g < n`.  This module turns those two coefficient cancellations into
strict residual degree drops, selects the residual gap `h > g`, and
extracts the ordinary residual middle and double I4/I3 faces.

After `l = 0` the heaviest quartic load is `beta A^3` at `6n`, the
heaviest cubic load is `beta A^2 B` at `7n-g`, and the heaviest row-two
product is `Ul C0'` at `9n-g-1`.  All three sit strictly below every
displayed residual index throughout `g < n`.  Row one at `12n-3g-1`
  remains load-free only on the extra window `3g < 2n`.  Closing the
chamber still needs residual one-forms and their row-one load split; this
module supplies their canonical classification and invariant-face inputs.

The existing `of_twoGap` / first-load-wall lemmas cannot be cited: their
`2g < n` or `2g = n` hypotheses are false even though the arithmetic
with `l = 0` and `g < n` remains strict.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LargeGapLoadZeroEndgame68

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Chamber arithmetic -/

/-! ## Residual degree drops after the classified face -/

/-! ## Canonical support, drops, and residual gap -/

/-- After the classified chamber, the selected residual gap lies strictly
above `g`, and both residual polynomials obey the selected bounds. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_largeGapLoadZeroResidualGap68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hlarge :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      n < 2 * g)
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
    let d := secondaryDDefectPolynomial68 Ae Be De
    let h := secondaryResidualGap68 n d ee
    l = 0 ∧
      (Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0) ∧
      d.natDegree < 5 * n - g ∧ ee.natDegree < 6 * n - g ∧
      g < h ∧
      d.natDegree ≤ 5 * n - h ∧ ee.natDegree ≤ 6 * n - h := by
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
  change n < 2 * g at hlarge
  change g < n at hgap
  change l = 0 ∧
    (Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0) ∧
    d.natDegree < 5 * n - g ∧ ee.natDegree < 6 * n - g ∧
    g < h ∧
    d.natDegree ≤ 5 * n - h ∧ ee.natDegree ≤ 6 * n - h
  have hboundary :=
    maximalExpandedIntegratedPolynomialLowerSystem_largeGapLoadZeroBoundary68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hlarge)
      (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hgap)
  change l = 0 ∧ ee.coeff (6 * n - g) = 0 ∧
    Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
      3 * De.coeff (5 * n - g) ∧
    (Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0) at hboundary
  have hdrops :=
    maximalExpandedIntegratedPolynomialLowerSystem_largeGapLoadZeroResidualDrops68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hlarge)
      (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hgap)
  change l = 0 ∧ d.natDegree < 5 * n - g ∧
    ee.natDegree < 6 * n - g at hdrops
  have hgh : g < h := by
    simpa only [h] using secondaryResidualGap68_gt_of_strictDrops n g d ee
      hdrops.2.1 hdrops.2.2
  have hdbase : d.natDegree < 5 * n := by omega
  have hebase : ee.natDegree < 6 * n := by omega
  have hbounds : d.natDegree ≤ 5 * n - h ∧
      ee.natDegree ≤ 6 * n - h := by
    simpa only [h] using secondaryResidualGap68_degreeBounds n d ee
      hdbase hebase
  exact ⟨hboundary.1, hboundary.2.2.2, hdrops.2.1, hdrops.2.2, hgh,
    hbounds⟩

end LargeGapLoadZeroEndgame68
end Max11DegreeRoutes
/-! # Residual faces in the large-gap load-zero chamber

The tracked theorems
`maximalExpandedIntegratedPolynomialLowerSystem_l_eq_zero_of_radius_lt_twoGap68`
and
`maximalExpandedIntegratedPolynomialLowerSystem_firstSecondaryClassified68_of_loadL`
already give `l = 0`, `ee.coeff(6n-g) = 0` and `a*b = 3*D_top` on
`n < 2g` and `g < n`.  Every first-face bound `2g < 3n` is free from
`g < n`.  This module turns those two coefficient cancellations into
strict residual degree drops, selects the residual gap `h > g`, and
extracts the ordinary residual middle and double I4/I3 faces.

After `l = 0` the heaviest quartic load is `beta A^3` at `6n`, the
heaviest cubic load is `beta A^2 B` at `7n-g`, and the heaviest row-two
product is `Ul C0'` at `9n-g-1`.  All three sit strictly below every
displayed residual index throughout `g < n`.  Row one at `12n-3g-1`
  remains load-free only on the extra window `3g < 2n`.  Closing the
chamber still needs residual one-forms and their row-one load split; this
module supplies their canonical classification and invariant-face inputs.

The existing `of_twoGap` / first-load-wall lemmas cannot be cited: their
`2g < n` or `2g = n` hypotheses are false even though the arithmetic
with `l = 0` and `g < n` remains strict.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LargeGapLoadZeroEndgame68

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Chamber arithmetic -/

/-! ## Residual degree drops after the classified face -/

/-! ## Canonical support, drops, and residual gap -/

/-! ## Load cutoffs after `l = 0` on `g < n` -/

set_option maxHeartbeats 2000000 in
theorem cubicLoadPolynomials68_degreeBounds_of_l_eq_zero_largeGap
    (alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hlarge : n < 2 * g) (hg_lt : g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadSPolynomial68 0 alpha beta delta A B c).natDegree ≤ 3 * n - g ∧
    (cubicLoadTPolynomial68 0 alpha beta gamma epsilon A B c D).natDegree ≤
      4 * n ∧
    (cubicLoadUPolynomial68 0 alpha beta gamma delta zeta
      A B c D e).natDegree ≤ 5 * n - g ∧
    (cubicLoadVPolynomial68 0 alpha beta gamma delta epsilon eta
      A B c D e).natDegree ≤ 6 * n := by
  simp only [cubicLoadSPolynomial68, cubicLoadTPolynomial68,
    cubicLoadUPolynomial68, cubicLoadVPolynomial68, zero_mul, mul_zero,
    zero_smul, smul_zero, add_zero, sub_zero]
  constructor
  · compute_degree
    omega
  constructor
  · compute_degree
    omega
  constructor <;> compute_degree <;> omega

set_option maxHeartbeats 2000000 in
/-- After `l=0` the heaviest quartic-invariant load is `beta A^3` at `6n`,
strictly below the residual middle index `9n-g-h` on `h < 2g` and `g < n`. -/
theorem secondaryLoadInvariantFourPolynomial68_degree_lt_middle_of_largeGapLoadZero
    (beta gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g h : ℕ) (hg : 0 < g) (hlarge : n < 2 * g) (hg_lt : g < n)
    (hh : h < 2 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - h) :
    (secondaryLoadInvariantFourPolynomial68
      0 beta gamma delta epsilon zeta A B c D e).natDegree <
        9 * n - g - h := by
  simp only [secondaryLoadInvariantFourPolynomial68, zero_mul, mul_zero,
    zero_smul, smul_zero, add_zero, sub_zero]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
theorem secondaryLoadInvariantFourPolynomial68_degree_lt_double_of_largeGapLoadZero
    (beta gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g : ℕ) (hg : 0 < g) (hlarge : n < 2 * g) (hg_lt : g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (secondaryLoadInvariantFourPolynomial68
      0 beta gamma delta epsilon zeta A B c D e).natDegree <
        9 * n - 3 * g := by
  simp only [secondaryLoadInvariantFourPolynomial68, zero_mul, mul_zero,
    zero_smul, smul_zero, add_zero, sub_zero]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
/-- After `l=0` the heaviest cubic-invariant load is `beta A^2 B` at
`7n-g`, strictly below the residual middle index `10n-g-h`. -/
theorem secondaryLoadInvariantThreePolynomial68_degree_lt_middle_of_largeGapLoadZero
    (beta gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g h : ℕ) (hg : 0 < g) (hlarge : n < 2 * g) (hg_lt : g < n)
    (hh : h < 2 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - h) :
    (secondaryLoadInvariantThreePolynomial68
      0 beta gamma delta epsilon zeta A B c D e).natDegree <
        10 * n - g - h := by
  simp only [secondaryLoadInvariantThreePolynomial68, zero_mul, mul_zero,
    zero_smul, smul_zero, add_zero, sub_zero]
  compute_degree
  omega

end LargeGapLoadZeroEndgame68
end Max11DegreeRoutes
/-! # Residual faces in the large-gap load-zero chamber

The tracked theorems
`maximalExpandedIntegratedPolynomialLowerSystem_l_eq_zero_of_radius_lt_twoGap68`
and
`maximalExpandedIntegratedPolynomialLowerSystem_firstSecondaryClassified68_of_loadL`
already give `l = 0`, `ee.coeff(6n-g) = 0` and `a*b = 3*D_top` on
`n < 2g` and `g < n`.  Every first-face bound `2g < 3n` is free from
`g < n`.  This module turns those two coefficient cancellations into
strict residual degree drops, selects the residual gap `h > g`, and
extracts the ordinary residual middle and double I4/I3 faces.

After `l = 0` the heaviest quartic load is `beta A^3` at `6n`, the
heaviest cubic load is `beta A^2 B` at `7n-g`, and the heaviest row-two
product is `Ul C0'` at `9n-g-1`.  All three sit strictly below every
displayed residual index throughout `g < n`.  Row one at `12n-3g-1`
  remains load-free only on the extra window `3g < 2n`.  Closing the
chamber still needs residual one-forms and their row-one load split; this
module supplies their canonical classification and invariant-face inputs.

The existing `of_twoGap` / first-load-wall lemmas cannot be cited: their
`2g < n` or `2g = n` hypotheses are false even though the arithmetic
with `l = 0` and `g < n` remains strict.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LargeGapLoadZeroEndgame68

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Chamber arithmetic -/

/-! ## Residual degree drops after the classified face -/

/-! ## Canonical support, drops, and residual gap -/

/-! ## Load cutoffs after `l = 0` on `g < n` -/

set_option maxHeartbeats 2000000 in
theorem secondaryLoadInvariantThreePolynomial68_degree_lt_double_of_largeGapLoadZero
    (beta gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g : ℕ) (hg : 0 < g) (hlarge : n < 2 * g) (hg_lt : g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (secondaryLoadInvariantThreePolynomial68
      0 beta gamma delta epsilon zeta A B c D e).natDegree <
        10 * n - 3 * g := by
  simp only [secondaryLoadInvariantThreePolynomial68, zero_mul, mul_zero,
    zero_smul, smul_zero, add_zero, sub_zero]
  compute_degree
  omega

end LargeGapLoadZeroEndgame68
end Max11DegreeRoutes
/-! # Residual faces in the large-gap load-zero chamber

The tracked theorems
`maximalExpandedIntegratedPolynomialLowerSystem_l_eq_zero_of_radius_lt_twoGap68`
and
`maximalExpandedIntegratedPolynomialLowerSystem_firstSecondaryClassified68_of_loadL`
already give `l = 0`, `ee.coeff(6n-g) = 0` and `a*b = 3*D_top` on
`n < 2g` and `g < n`.  Every first-face bound `2g < 3n` is free from
`g < n`.  This module turns those two coefficient cancellations into
strict residual degree drops, selects the residual gap `h > g`, and
extracts the ordinary residual middle and double I4/I3 faces.

After `l = 0` the heaviest quartic load is `beta A^3` at `6n`, the
heaviest cubic load is `beta A^2 B` at `7n-g`, and the heaviest row-two
product is `Ul C0'` at `9n-g-1`.  All three sit strictly below every
displayed residual index throughout `g < n`.  Row one at `12n-3g-1`
  remains load-free only on the extra window `3g < 2n`.  Closing the
chamber still needs residual one-forms and their row-one load split; this
module supplies their canonical classification and invariant-face inputs.

The existing `of_twoGap` / first-load-wall lemmas cannot be cited: their
`2g < n` or `2g = n` hypotheses are false even though the arithmetic
with `l = 0` and `g < n` remains strict.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LargeGapLoadZeroEndgame68

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

private theorem leaf68_natDegree_mulDeriv_lt {p q : k[X]} {u v bound : ℕ}
    (hp : p.natDegree ≤ u) (hq : q.natDegree ≤ v) (h : u + (v - 1) < bound) :
    (p * derivative q).natDegree < bound :=
  natDegree_mul_le.trans_lt
    (lt_of_le_of_lt
      (Nat.add_le_add hp ((natDegree_derivative_le q).trans (Nat.sub_le_sub_right hq 1))) h)

private theorem leaf68_natDegree_smul_lt (r : k) {p : k[X]} {bound : ℕ}
    (h : p.natDegree < bound) : (r • p).natDegree < bound :=
  (natDegree_smul_le r p).trans_lt h

private theorem leaf68_natDegree_add_lt {p q : k[X]} {bound : ℕ}
    (hp : p.natDegree < bound) (hq : q.natDegree < bound) :
    (p + q).natDegree < bound :=
  (natDegree_add_le p q).trans_lt (max_lt hp hq)

private theorem leaf68_natDegree_sub_lt {p q : k[X]} {bound : ℕ}
    (hp : p.natDegree < bound) (hq : q.natDegree < bound) :
    (p - q).natDegree < bound :=
  (natDegree_sub_le p q).trans_lt (max_lt hp hq)


/-! ## Chamber arithmetic -/

/-! ## Residual degree drops after the classified face -/

/-! ## Canonical support, drops, and residual gap -/

/-! ## Load cutoffs after `l = 0` on `g < n` -/

set_option maxHeartbeats 6000000 in
theorem cubicLoadRowTwoPolynomial68_degree_lt_cubicFace_of_largeGapLoadZero
    (alpha beta gamma delta epsilon zeta eta : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hlarge : n < 2 * g) (hg_lt : g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (cubicLoadRowTwoPolynomial68 0 alpha beta gamma delta epsilon zeta eta
      A B c ((1 / 3 : k) • (A * B) + d) e).natDegree <
        11 * n - 3 * g - 1 := by
  let D := (1 / 3 : k) • (A * B) + d
  let C0 := (1 / 3 : k) • A ^ 2 + c
  let E := (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
  let Sl := cubicLoadSPolynomial68 0 alpha beta delta A B c
  let Tl := cubicLoadTPolynomial68 0 alpha beta gamma epsilon A B c D
  let Ul := cubicLoadUPolynomial68 0 alpha beta gamma delta zeta A B c D e
  let Vl := cubicLoadVPolynomial68 0 alpha beta gamma delta epsilon eta
    A B c D e
  have hn : 0 < n := by omega
  have he' : e.natDegree ≤ 6 * n - g := by omega
  have hD : D.natDegree ≤ 5 * n - g := by
    simp only [D]
    compute_degree
    omega
  have hloads := cubicLoadPolynomials68_degreeBounds_of_l_eq_zero_largeGap
    alpha beta gamma delta epsilon zeta eta A B c D e n g
    hn hg hlarge hg_lt hA hB hc hD he'
  have hSl : Sl.natDegree ≤ 3 * n - g := by simpa only [Sl] using hloads.1
  have hTl : Tl.natDegree ≤ 4 * n := by simpa only [Tl] using hloads.2.1
  have hUl : Ul.natDegree ≤ 5 * n - g := by
    simpa only [Ul] using hloads.2.2.1
  have hVl : Vl.natDegree ≤ 6 * n := by
    simpa only [Vl] using hloads.2.2.2
  have hC0 : C0.natDegree ≤ 4 * n := by
    simp only [C0]
    compute_degree
    omega
  have hE : E.natDegree ≤ 6 * n := by
    simp only [E]
    compute_degree
    omega
  have hUlC : (Ul * derivative C0).natDegree < 11 * n - 3 * g - 1 :=
    leaf68_natDegree_mulDeriv_lt hUl hC0 (by omega)
  have hTlD : (Tl * derivative D).natDegree < 11 * n - 3 * g - 1 :=
    leaf68_natDegree_mulDeriv_lt hTl hD (by omega)
  have hSlE : (Sl * derivative E).natDegree < 11 * n - 3 * g - 1 :=
    leaf68_natDegree_mulDeriv_lt hSl hE (by omega)
  have hBVl : (B * derivative Vl).natDegree < 11 * n - 3 * g - 1 :=
    leaf68_natDegree_mulDeriv_lt hB hVl (by omega)
  have hC0Ul : (C0 * derivative Ul).natDegree < 11 * n - 3 * g - 1 :=
    leaf68_natDegree_mulDeriv_lt hC0 hUl (by omega)
  have hDTl : (D * derivative Tl).natDegree < 11 * n - 3 * g - 1 :=
    leaf68_natDegree_mulDeriv_lt hD hTl (by omega)
  change (Ul * derivative C0 + (2 : k) • (Tl * derivative D) +
    (3 : k) • (Sl * derivative E) - (3 : k) • (B * derivative Vl) -
    (2 : k) • (C0 * derivative Ul) - D * derivative Tl).natDegree < _
  exact leaf68_natDegree_sub_lt
        (leaf68_natDegree_sub_lt
          (leaf68_natDegree_sub_lt
            (leaf68_natDegree_add_lt
              (leaf68_natDegree_add_lt
                hUlC
                (leaf68_natDegree_smul_lt (2 : k)
                  hTlD))
              (leaf68_natDegree_smul_lt (3 : k)
                hSlE))
            (leaf68_natDegree_smul_lt (3 : k)
              hBVl))
          (leaf68_natDegree_smul_lt (2 : k)
            hC0Ul))
        hDTl

end LargeGapLoadZeroEndgame68
end Max11DegreeRoutes
