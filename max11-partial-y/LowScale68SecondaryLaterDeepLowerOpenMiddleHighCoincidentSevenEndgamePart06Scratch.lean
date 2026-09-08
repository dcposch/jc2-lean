import LowScale68SecondaryLaterDeepLowerOpenMiddleHighCoincidentSevenEndgamePart05Scratch

/-! # Closure for the coincident seven wall `2h=3g=7n` -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerOpenMiddleHighCoincidentSevenEndgame68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 24000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## The quartic incidence defect on the coincident wall -/

/-! ## Row zero at `6n-1` -/

/-! ## Row one after the row-zero/row-two cancellation -/

set_option maxHeartbeats 7000000 in
theorem fiveRadiusCoincidentSevenRowOneTail68_degree_lt
    (gamma epsilon zeta : k) (A B c d e : k[X])
    (n g h : ℕ) (hn : 0 < n) (hg : 0 < g) (hgh : g < h)
    (hh : h < 2 * g)
    (hwallH : 2 * h = 7 * n) (hwallG : 3 * g = 7 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (fiveRadiusCoincidentSevenRowOneTail68
      gamma epsilon zeta A B c d e).natDegree < 5 * n - 1 := by
  let idx := 5 * n - 1
  have hBcd : (derivative (B * c * d)).natDegree < idx := by
    have hp : (B * c * d).natDegree ≤ 12 * n - 2 * g - h := by
      compute_degree
      omega
    have hder := natDegree_derivative_le (B * c * d)
    dsimp [idx]
    omega
  have hBp : (derivative B * c * d).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  have hBe : (B ^ 2 * derivative e).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  have hBd : (B * derivative d).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  have hdB : (d * derivative B).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  have hcc : (c * derivative c).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  have hApB2 : (derivative A * B ^ 2).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  have hABBp : (A * B * derivative B).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  have hep : (derivative e).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  have hApB : (derivative A * B).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  have hdp : (derivative d).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  simp only [fiveRadiusCoincidentSevenRowOneTail68,
    fiveRadiusBalancedRowOneTail68]
  exact deepGap_natDegree_add_lt
    (deepGap_natDegree_add_lt
      (deepGap_natDegree_add_lt
        (deepGap_natDegree_smul_lt68 (-4 / 27 : k)
          (deepGap_natDegree_add_lt
            (deepGap_natDegree_add_lt
              (deepGap_natDegree_smul_lt68 (3 : k) hBcd)
              (deepGap_natDegree_smul_lt68 (6 : k) hBp))
            (deepGap_natDegree_smul_lt68 (-3 : k) hBe)))
        (deepGap_natDegree_smul_lt68 gamma
          (deepGap_natDegree_add_lt
            (deepGap_natDegree_add_lt
              (deepGap_natDegree_smul_lt68 (2 / 3 : k)
                (deepGap_natDegree_sub_lt
                  (deepGap_natDegree_sub_lt hBd hdB)
                  (deepGap_natDegree_smul_lt68 (2 : k) hcc)))
              (deepGap_natDegree_smul_lt68 (2 / 9 : k) hApB2))
            (deepGap_natDegree_smul_lt68 (4 / 9 : k) hABBp))))
      (deepGap_natDegree_smul_lt68 (2 * epsilon : k) hep))
    (deepGap_natDegree_smul_lt68 zeta
      (deepGap_natDegree_add_lt
        (deepGap_natDegree_smul_lt68 (1 / 3 : k) hApB) hdp))

end LaterDeepLowerOpenMiddleHighCoincidentSevenEndgame68
end Max11DegreeRoutes
