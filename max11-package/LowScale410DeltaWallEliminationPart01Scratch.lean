import LowScale410DeltaWallEliminationPart00Scratch

/-!
# Elimination of the pure delta wall

The two constant invariant curves and the degree-one terminal primitive have
only one possible nondegenerate Newton ray.  Its degree ratio is
`(deg A, deg B, deg U) = (8,7,11)` up to scale.  The two invariant faces on
that ray give incompatible leading-coefficient equations.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Polynomial

namespace Max11DegreeRoutes

section DeltaWallElimination410

variable {k : Type*} [Field k] [CharZero k]

open private fiveDegreeTie410 from LowScale410DeltaWallEliminationPart00Scratch in
set_option maxHeartbeats 64000000 in
/-- If five nonzero summands add to a polynomial of degree below the largest
summand degree, at least two summands lie on the largest face. -/
private theorem fiveTerm_degree_tie410
    (P1 P2 P3 P4 P5 : k[X])
    (hP1 : P1 ≠ 0) (hP2 : P2 ≠ 0) (hP3 : P3 ≠ 0)
    (hP4 : P4 ≠ 0) (hP5 : P5 ≠ 0)
    (hbelow : (P1 + P2 + P3 + P4 + P5).natDegree <
      max P1.natDegree (max P2.natDegree
        (max P3.natDegree (max P4.natDegree P5.natDegree)))) :
    fiveDegreeTie410 P1.natDegree P2.natDegree P3.natDegree
      P4.natDegree P5.natDegree
      (max P1.natDegree (max P2.natDegree
        (max P3.natDegree (max P4.natDegree P5.natDegree)))) := by
  let m := max P1.natDegree (max P2.natDegree
    (max P3.natDegree (max P4.natDegree P5.natDegree)))
  have h1le : P1.natDegree ≤ m := by dsimp [m]; omega
  have h2le : P2.natDegree ≤ m := by dsimp [m]; omega
  have h3le : P3.natDegree ≤ m := by dsimp [m]; omega
  have h4le : P4.natDegree ≤ m := by dsimp [m]; omega
  have h5le : P5.natDegree ≤ m := by dsimp [m]; omega
  have hcases : P1.natDegree = m ∨ P2.natDegree = m ∨
      P3.natDegree = m ∨ P4.natDegree = m ∨ P5.natDegree = m := by
    dsimp [m]
    omega
  have hsumcoeff :
      (P1 + P2 + P3 + P4 + P5).coeff m = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    simpa only [m] using hbelow
  by_contra hnot
  change ¬ fiveDegreeTie410 P1.natDegree P2.natDegree P3.natDegree
    P4.natDegree P5.natDegree m at hnot
  rcases hcases with h1 | h2 | h3 | h4 | h5
  · have h2ne : P2.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fiveDegreeTie410, h1, heq])
    have h3ne : P3.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fiveDegreeTie410, h1, heq])
    have h4ne : P4.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fiveDegreeTie410, h1, heq])
    have h5ne : P5.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fiveDegreeTie410, h1, heq])
    have h2lt : P2.natDegree < m := by omega
    have h3lt : P3.natDegree < m := by omega
    have h4lt : P4.natDegree < m := by omega
    have h5lt : P5.natDegree < m := by omega
    rw [coeff_add, coeff_add, coeff_add, coeff_add,
      show P1.coeff m = P1.leadingCoeff by rw [← h1, coeff_natDegree],
      coeff_eq_zero_of_natDegree_lt h2lt,
      coeff_eq_zero_of_natDegree_lt h3lt,
      coeff_eq_zero_of_natDegree_lt h4lt,
      coeff_eq_zero_of_natDegree_lt h5lt] at hsumcoeff
    exact (leadingCoeff_ne_zero.mpr hP1) (by simpa using hsumcoeff)
  · have h1ne : P1.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fiveDegreeTie410, h2, heq])
    have h3ne : P3.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fiveDegreeTie410, h2, heq])
    have h4ne : P4.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fiveDegreeTie410, h2, heq])
    have h5ne : P5.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fiveDegreeTie410, h2, heq])
    have h1lt : P1.natDegree < m := by omega
    have h3lt : P3.natDegree < m := by omega
    have h4lt : P4.natDegree < m := by omega
    have h5lt : P5.natDegree < m := by omega
    rw [coeff_add, coeff_add, coeff_add, coeff_add,
      coeff_eq_zero_of_natDegree_lt h1lt,
      show P2.coeff m = P2.leadingCoeff by rw [← h2, coeff_natDegree],
      coeff_eq_zero_of_natDegree_lt h3lt,
      coeff_eq_zero_of_natDegree_lt h4lt,
      coeff_eq_zero_of_natDegree_lt h5lt] at hsumcoeff
    exact (leadingCoeff_ne_zero.mpr hP2) (by simpa using hsumcoeff)
  · have h1ne : P1.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fiveDegreeTie410, h3, heq])
    have h2ne : P2.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fiveDegreeTie410, h3, heq])
    have h4ne : P4.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fiveDegreeTie410, h3, heq])
    have h5ne : P5.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fiveDegreeTie410, h3, heq])
    have h1lt : P1.natDegree < m := by omega
    have h2lt : P2.natDegree < m := by omega
    have h4lt : P4.natDegree < m := by omega
    have h5lt : P5.natDegree < m := by omega
    rw [coeff_add, coeff_add, coeff_add, coeff_add,
      coeff_eq_zero_of_natDegree_lt h1lt,
      coeff_eq_zero_of_natDegree_lt h2lt,
      show P3.coeff m = P3.leadingCoeff by rw [← h3, coeff_natDegree],
      coeff_eq_zero_of_natDegree_lt h4lt,
      coeff_eq_zero_of_natDegree_lt h5lt] at hsumcoeff
    exact (leadingCoeff_ne_zero.mpr hP3) (by simpa using hsumcoeff)
  · have h1ne : P1.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fiveDegreeTie410, h4, heq])
    have h2ne : P2.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fiveDegreeTie410, h4, heq])
    have h3ne : P3.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fiveDegreeTie410, h4, heq])
    have h5ne : P5.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fiveDegreeTie410, h4, heq])
    have h1lt : P1.natDegree < m := by omega
    have h2lt : P2.natDegree < m := by omega
    have h3lt : P3.natDegree < m := by omega
    have h5lt : P5.natDegree < m := by omega
    rw [coeff_add, coeff_add, coeff_add, coeff_add,
      coeff_eq_zero_of_natDegree_lt h1lt,
      coeff_eq_zero_of_natDegree_lt h2lt,
      coeff_eq_zero_of_natDegree_lt h3lt,
      show P4.coeff m = P4.leadingCoeff by rw [← h4, coeff_natDegree],
      coeff_eq_zero_of_natDegree_lt h5lt] at hsumcoeff
    exact (leadingCoeff_ne_zero.mpr hP4) (by simpa using hsumcoeff)
  · have h1ne : P1.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fiveDegreeTie410, h5, heq])
    have h2ne : P2.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fiveDegreeTie410, h5, heq])
    have h3ne : P3.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fiveDegreeTie410, h5, heq])
    have h4ne : P4.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fiveDegreeTie410, h5, heq])
    have h1lt : P1.natDegree < m := by omega
    have h2lt : P2.natDegree < m := by omega
    have h3lt : P3.natDegree < m := by omega
    have h4lt : P4.natDegree < m := by omega
    rw [coeff_add, coeff_add, coeff_add, coeff_add,
      coeff_eq_zero_of_natDegree_lt h1lt,
      coeff_eq_zero_of_natDegree_lt h2lt,
      coeff_eq_zero_of_natDegree_lt h3lt,
      coeff_eq_zero_of_natDegree_lt h4lt,
      show P5.coeff m = P5.leadingCoeff by rw [← h5, coeff_natDegree]]
      at hsumcoeff
    exact (leadingCoeff_ne_zero.mpr hP5) (by simpa using hsumcoeff)

end DeltaWallElimination410

end Max11DegreeRoutes
