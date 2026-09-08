import LowScale68SecondaryFirstLoadWallCanonical
import LowScale68SecondaryResidualLoadZeroEndgame

/-! # Residual faces on the first-gap boundary `2g = n`

The tracked classifier
`maximalExpandedIntegratedPolynomialLowerSystem_firstLoadWallClassified68`
already gives `l = 0`, `ee.coeff(6n-g) = 0` and `a*b = 3*D_top` on
`2g = n`.  This module turns those two coefficient cancellations into
strict residual degree drops, selects the residual gap `h > g`, and
extracts the ordinary residual middle invariants throughout `g < h < 2g`.

After `l = 0` the heaviest quartic load is `beta A^3` at `6n`, while the
heaviest residual row-one load is `alpha A^3` against `C0'` at `10n-1`.
Both sit strictly below every displayed residual index on this wall, so
the next exact face is the ordinary middle pair rather than a new mixed
scalar system.  Closing the wall still needs the residual double / row-two
selector and the balanced row-one cubic scalar, supplied by
`LowScale68SecondaryFirstGapBoundary`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FirstGapBoundaryEndgame68

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Residual degree drops after the classified wall -/

theorem firstLoadWall_gap_le_radius (n g : ℕ) (hwall : 2 * g = n) :
    g ≤ n := by
  have : g ≤ 2 * g := Nat.le_mul_of_pos_left g (by omega)
  exact this.trans_eq hwall

theorem firstLoadWall_index_pos (n g : ℕ) (hn : 0 < n)
    (hwall : 2 * g = n) {w : ℕ} (hw : 1 < w) :
    0 < w * n - g := by
  have hg_le : g ≤ n := firstLoadWall_gap_le_radius n g hwall
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

theorem secondaryDDefectPolynomial68_degree_lt_of_firstLoadWall
    (A B D : k[X]) (n g : ℕ) (hn : 0 < n) (hg : 0 < g)
    (hwall : 2 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (hrel : A.coeff (2 * n) * B.coeff (3 * n - g) =
      3 * D.coeff (5 * n - g)) :
    (secondaryDDefectPolynomial68 A B D).natDegree < 5 * n - g := by
  have hg3 : g ≤ 3 * n :=
    (firstLoadWall_gap_le_radius n g hwall).trans (by omega)
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
    (5 * n - g) (firstLoadWall_index_pos n g hn hwall (by decide))
    hdegree hcoeff

theorem firstSecondaryResidualDegreeDrops68_of_firstLoadWall
    (A B D e : k[X]) (n g : ℕ) (hn : 0 < n) (hg : 0 < g)
    (hwall : 2 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (hrel : A.coeff (2 * n) * B.coeff (3 * n - g) =
      3 * D.coeff (5 * n - g))
    (hetop : e.coeff (6 * n - g) = 0) :
    (secondaryDDefectPolynomial68 A B D).natDegree < 5 * n - g ∧
      e.natDegree < 6 * n - g := by
  refine ⟨secondaryDDefectPolynomial68_degree_lt_of_firstLoadWall A B D n g
    hn hg hwall hA hB hD hrel, ?_⟩
  exact natDegree_lt_of_le_of_coeff_eq_zero68 e (6 * n - g)
    (firstLoadWall_index_pos n g hn hwall (by decide)) he hetop

end FirstGapBoundaryEndgame68
end Max11DegreeRoutes
