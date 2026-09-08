import Sol68LaterDeepLowerOpenDoubleFiveWallAlignedStrideInductionSourcePart04Scratch

/-! # Uniform aligned-stride induction on the degenerate double-five wall -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerOpenDoubleFiveWallAlignedStrideInductionSource68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 30000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option maxHeartbeats 30000000 in
theorem laterDeepLowerOpenDoubleFiveWall_aligned_offset_source_step68
    (alpha gamma delta epsilon zeta eta : k)
    (A B c d e : k[X]) (qc qd : k[X]) (i3 : k) (n g s : ℕ)
    (hn : 0 < n) (ha : A.coeff (2 * n) ≠ 0)
    (hb : B.coeff (3 * n - g) ≠ 0)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hwall : 3 * g = 5 * n) (hspos : 0 < s)
    (hs : s < 5 * n - 2 * g)
    (hsAlign : 60 ∣ s) (hcAlign : 60 ∣ 4 * n - g)
    (hdAlign : 60 ∣ 5 * n - 2 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g - s)
    (hd : d.natDegree ≤ 5 * n - 2 * g - s)
    (hD : ((1 / 3 : k) • (A * B) + d).natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - 2 * g)
    (hcexpand : c = expand k 60 qc) (hdexpand : d = expand k 60 qd)
    (hi3c : cubicFirstIntegralThreePolynomial68
      0 0 gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i3)
    (hrowPoly : secondaryResidualRowOnePolynomial68 A B c d e +
      cubicLoadRowOnePolynomial68 0 alpha 0 gamma delta epsilon zeta eta
        A B c ((1 / 3 : k) • (A * B) + d) e = 0) :
    c.natDegree ≤ 4 * n - g - (s + 60) ∧
      d.natDegree ≤ 5 * n - 2 * g - (s + 60) := by
  have hcoeff3 := congrArg
    (fun p : k[X] => p.coeff (10 * n - 3 * g - s)) hi3c
  rw [cubicFirstIntegralThreePolynomial68_secondaryLoadSplit, coeff_add,
    cubicFirstIntegralThreePolynomial68_residualCoordinates,
    secondaryResidualInvariantThreePolynomial68_coeff_aligned_offset_of_fiveWall
      A B c d e n g s hn hopen hwall (by omega) hA hB hc hd he,
    coeff_eq_zero_of_natDegree_lt
      (secondaryLoadInvariantThreePolynomial68_degree_lt_aligned_offset_of_doubleFiveWall
        gamma delta epsilon zeta A B c ((1 / 3 : k) • (A * B) + d) e
        n g s hn hopen hwall hs hA hB hc hD he), add_zero] at hcoeff3
  have hidx3 : 10 * n - 3 * g - s ≠ 0 := by omega
  simp only [coeff_C, if_neg hidx3] at hcoeff3
  have hi3scalar :
      -A.coeff (2 * n) * B.coeff (3 * n - g) *
          d.coeff (5 * n - 2 * g - s) -
        B.coeff (3 * n - g) ^ 2 * c.coeff (4 * n - g - s) +
        3 * c.coeff (4 * n - g - s) * e.coeff (6 * n - 2 * g) = 0 := by
    have ht := (mul_eq_zero.mp hcoeff3).resolve_left (by norm_num)
    linear_combination ht
  have hloadOne :=
    cubicLoadRowOnePolynomial68_degree_lt_aligned_offset_of_doubleFiveWall
      alpha gamma delta epsilon zeta eta A B c
      ((1 / 3 : k) • (A * B) + d) e n g s hn hopen hwall hs
      hA hB hc hD he
  have hcoeffOne := congrArg
    (fun p : k[X] => p.coeff (12 * n - 3 * g - s - 1)) hrowPoly
  rw [coeff_add, coeff_zero,
    coeff_eq_zero_of_natDegree_lt hloadOne, add_zero,
    secondaryResidualRowOnePolynomial68_coeff_aligned_offset_of_fiveWall
      A B c d e n g s hn hopen hwall hspos hs hA hB hc hd he]
    at hcoeffOne
  have hrowScalar :
      2 * A.coeff (2 * n) ^ 2 * B.coeff (3 * n - g) *
          d.coeff (5 * n - 2 * g - s) * (5 * (n : k) - (s : k)) -
        6 * A.coeff (2 * n) * c.coeff (4 * n - g - s) *
          e.coeff (6 * n - 2 * g) * (5 * (n : k) - (s : k)) -
        4 * (n : k) * A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 *
          c.coeff (4 * n - g - s) = 0 := by
    have ht := (mul_eq_zero.mp hcoeffOne).resolve_left (by norm_num)
    have hcastM : (((5 * n - s : ℕ) : k)) = 5 * (n : k) - (s : k) := by
      rw [Nat.cast_sub (by omega : s ≤ 5 * n)]
      push_cast
      rfl
    rw [hcastM] at ht
    exact ht
  have edges := laterDeepLowerOpenDoubleFiveWall_degenerate_aligned_offset_edges_zero68
    n s (A.coeff (2 * n)) (B.coeff (3 * n - g))
    (c.coeff (4 * n - g - s)) (d.coeff (5 * n - 2 * g - s))
    (e.coeff (6 * n - 2 * g)) hn (by omega) ha hb hi3scalar hrowScalar
  have hcAlignS : 60 ∣ 4 * n - g - s := by
    obtain ⟨u, hu⟩ := hcAlign
    obtain ⟨v, hv⟩ := hsAlign
    refine ⟨u - v, ?_⟩
    omega
  have hdAlignS : 60 ∣ 5 * n - 2 * g - s := by
    obtain ⟨u, hu⟩ := hdAlign
    obtain ⟨v, hv⟩ := hsAlign
    refine ⟨u - v, ?_⟩
    omega
  constructor
  · have ht : c.natDegree ≤ (4 * n - g - s) - 60 := by
      rw [hcexpand]
      apply natDegree_expand_le_sub_sixty_of_aligned_boundary_zero68
        qc (4 * n - g - s) hcAlignS (by omega)
      · simpa only [← hcexpand] using hc
      · rw [← hcexpand]
        exact edges.1
    omega
  · have ht : d.natDegree ≤ (5 * n - 2 * g - s) - 60 := by
      rw [hdexpand]
      apply natDegree_expand_le_sub_sixty_of_aligned_boundary_zero68
        qd (5 * n - 2 * g - s) hdAlignS (by omega)
      · simpa only [← hdexpand] using hd
      · rw [← hdexpand]
        exact edges.2
    omega

end LaterDeepLowerOpenDoubleFiveWallAlignedStrideInductionSource68
end Max11DegreeRoutes
