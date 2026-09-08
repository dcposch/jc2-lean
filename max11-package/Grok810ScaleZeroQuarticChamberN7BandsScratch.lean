import Grok810ScaleZeroQuarticChamberN7LadderScratch

/-! # The `n7-cost` band source, `(8,10)` scale zero

`…ChamberN7LadderScratch` already carries the cost-form `N₇` predicates,
the pure-`A` split, the rest bounds and the five kills (which go through
the tower lane's `quarticSigma_<load>_eq_zero_of_N7_column`).  This adds
only what the `n7-cost` band source of `UNOWNED_CHAMBERS.md` needs: the
five band disjunctions and the cascade (the monotonicity chain is
already in `…ChamberN7LadderScratch`).  103 single-chamber columns use
it.
Untracked working note.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

set_option maxRecDepth 1000000

variable {k : Type*} [Field k] [CharZero k]

section QuarticN7Bands810

/-! ## The five `N₇` band disjunctions -/

set_option maxHeartbeats 64000000 in
theorem quarticSigmaN7Cost_l_band
    {l : k} (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hkill : QuarticN7CostTopL810 A B C D E F G → l = 0) :
    l = 0 ∨
      7 * A.natDegree ≤ B.natDegree + C.natDegree + G.natDegree ∨
      8 * A.natDegree ≤ B.natDegree + E.natDegree + G.natDegree ∨
      8 * A.natDegree ≤ B.natDegree + 2 * F.natDegree ∨
      7 * A.natDegree ≤ 2 * C.natDegree + F.natDegree ∨
      7 * A.natDegree ≤ C.natDegree + D.natDegree + E.natDegree ∨
      8 * A.natDegree ≤ C.natDegree + D.natDegree + G.natDegree ∨
      8 * A.natDegree ≤ C.natDegree + E.natDegree + F.natDegree ∨
      8 * A.natDegree ≤ 2 * D.natDegree + F.natDegree ∨
      8 * A.natDegree ≤ D.natDegree + 2 * E.natDegree ∨
      6 * A.natDegree ≤ 3 * B.natDegree + C.natDegree ∨
      7 * A.natDegree ≤ 3 * B.natDegree + E.natDegree ∨
      8 * A.natDegree ≤ 3 * B.natDegree + G.natDegree ∨
      8 * A.natDegree ≤ 2 * B.natDegree + C.natDegree + F.natDegree ∨
      8 * A.natDegree ≤ 2 * B.natDegree + D.natDegree + E.natDegree ∨
      7 * A.natDegree ≤ B.natDegree + 3 * C.natDegree ∨
      8 * A.natDegree ≤ B.natDegree + 2 * C.natDegree + E.natDegree ∨
      8 * A.natDegree ≤ B.natDegree + C.natDegree + 2 * D.natDegree ∨
      8 * A.natDegree ≤ 3 * C.natDegree + D.natDegree ∨
      7 * A.natDegree ≤ 5 * B.natDegree ∨
      8 * A.natDegree ≤ 4 * B.natDegree + D.natDegree := by
  by_cases hb0 : B.natDegree + C.natDegree + G.natDegree < 7 * A.natDegree
  · by_cases hb1 : B.natDegree + E.natDegree + G.natDegree < 8 * A.natDegree
    · by_cases hb2 : B.natDegree + 2 * F.natDegree < 8 * A.natDegree
      · by_cases hb3 : 2 * C.natDegree + F.natDegree < 7 * A.natDegree
        · by_cases hb4 : C.natDegree + D.natDegree + E.natDegree < 7 * A.natDegree
          · by_cases hb5 : C.natDegree + D.natDegree + G.natDegree < 8 * A.natDegree
            · by_cases hb6 : C.natDegree + E.natDegree + F.natDegree < 8 * A.natDegree
              · by_cases hb7 : 2 * D.natDegree + F.natDegree < 8 * A.natDegree
                · by_cases hb8 : D.natDegree + 2 * E.natDegree < 8 * A.natDegree
                  · by_cases hb9 : 3 * B.natDegree + C.natDegree < 6 * A.natDegree
                    · by_cases hb10 : 3 * B.natDegree + E.natDegree < 7 * A.natDegree
                      · by_cases hb11 : 3 * B.natDegree + G.natDegree < 8 * A.natDegree
                        · by_cases hb12 : 2 * B.natDegree + C.natDegree + F.natDegree < 8 * A.natDegree
                          · by_cases hb13 : 2 * B.natDegree + D.natDegree + E.natDegree < 8 * A.natDegree
                            · by_cases hb14 : B.natDegree + 3 * C.natDegree < 7 * A.natDegree
                              · by_cases hb15 : B.natDegree + 2 * C.natDegree + E.natDegree < 8 * A.natDegree
                                · by_cases hb16 : B.natDegree + C.natDegree + 2 * D.natDegree < 8 * A.natDegree
                                  · by_cases hb17 : 3 * C.natDegree + D.natDegree < 8 * A.natDegree
                                    · by_cases hb18 : 5 * B.natDegree < 7 * A.natDegree
                                      · by_cases hb19 : 4 * B.natDegree + D.natDegree < 8 * A.natDegree
                                        · exact Or.inl (hkill ⟨hA, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩)
                                        · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (?_))))))))))))))))))))
                                          omega
                                      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))))))))))))
                                        omega
                                    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))))))))))
                                      omega
                                  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))))))))))
                                    omega
                                · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))))))))
                                  omega
                              · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))))))))
                                omega
                            · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))))))
                              omega
                          · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))))))
                            omega
                        · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))))
                          omega
                      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))))
                        omega
                    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))
                      omega
                  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))
                    omega
                · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))
                  omega
              · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))
                omega
            · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))
              omega
          · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))
            omega
        · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
          omega
      · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
        omega
    · refine Or.inr (Or.inr (Or.inl ?_))
      omega
  · refine Or.inr (Or.inl ?_)
    omega

set_option maxHeartbeats 64000000 in
theorem quarticSigmaN7Cost_beta_band
    {beta : k} (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hkill : QuarticN7CostTopBeta810 A B C D E F G → beta = 0) :
    beta = 0 ∨
      6 * A.natDegree ≤ B.natDegree + C.natDegree + G.natDegree ∨
      7 * A.natDegree ≤ B.natDegree + E.natDegree + G.natDegree ∨
      7 * A.natDegree ≤ B.natDegree + 2 * F.natDegree ∨
      6 * A.natDegree ≤ 2 * C.natDegree + F.natDegree ∨
      6 * A.natDegree ≤ C.natDegree + D.natDegree + E.natDegree ∨
      7 * A.natDegree ≤ C.natDegree + D.natDegree + G.natDegree ∨
      7 * A.natDegree ≤ C.natDegree + E.natDegree + F.natDegree ∨
      7 * A.natDegree ≤ 2 * D.natDegree + F.natDegree ∨
      7 * A.natDegree ≤ D.natDegree + 2 * E.natDegree ∨
      5 * A.natDegree ≤ 3 * B.natDegree + C.natDegree ∨
      6 * A.natDegree ≤ 3 * B.natDegree + E.natDegree ∨
      7 * A.natDegree ≤ 3 * B.natDegree + G.natDegree ∨
      7 * A.natDegree ≤ 2 * B.natDegree + C.natDegree + F.natDegree ∨
      7 * A.natDegree ≤ 2 * B.natDegree + D.natDegree + E.natDegree ∨
      6 * A.natDegree ≤ B.natDegree + 3 * C.natDegree ∨
      7 * A.natDegree ≤ B.natDegree + 2 * C.natDegree + E.natDegree ∨
      7 * A.natDegree ≤ B.natDegree + C.natDegree + 2 * D.natDegree ∨
      7 * A.natDegree ≤ 3 * C.natDegree + D.natDegree ∨
      6 * A.natDegree ≤ 5 * B.natDegree ∨
      7 * A.natDegree ≤ 4 * B.natDegree + D.natDegree := by
  by_cases hb0 : B.natDegree + C.natDegree + G.natDegree < 6 * A.natDegree
  · by_cases hb1 : B.natDegree + E.natDegree + G.natDegree < 7 * A.natDegree
    · by_cases hb2 : B.natDegree + 2 * F.natDegree < 7 * A.natDegree
      · by_cases hb3 : 2 * C.natDegree + F.natDegree < 6 * A.natDegree
        · by_cases hb4 : C.natDegree + D.natDegree + E.natDegree < 6 * A.natDegree
          · by_cases hb5 : C.natDegree + D.natDegree + G.natDegree < 7 * A.natDegree
            · by_cases hb6 : C.natDegree + E.natDegree + F.natDegree < 7 * A.natDegree
              · by_cases hb7 : 2 * D.natDegree + F.natDegree < 7 * A.natDegree
                · by_cases hb8 : D.natDegree + 2 * E.natDegree < 7 * A.natDegree
                  · by_cases hb9 : 3 * B.natDegree + C.natDegree < 5 * A.natDegree
                    · by_cases hb10 : 3 * B.natDegree + E.natDegree < 6 * A.natDegree
                      · by_cases hb11 : 3 * B.natDegree + G.natDegree < 7 * A.natDegree
                        · by_cases hb12 : 2 * B.natDegree + C.natDegree + F.natDegree < 7 * A.natDegree
                          · by_cases hb13 : 2 * B.natDegree + D.natDegree + E.natDegree < 7 * A.natDegree
                            · by_cases hb14 : B.natDegree + 3 * C.natDegree < 6 * A.natDegree
                              · by_cases hb15 : B.natDegree + 2 * C.natDegree + E.natDegree < 7 * A.natDegree
                                · by_cases hb16 : B.natDegree + C.natDegree + 2 * D.natDegree < 7 * A.natDegree
                                  · by_cases hb17 : 3 * C.natDegree + D.natDegree < 7 * A.natDegree
                                    · by_cases hb18 : 5 * B.natDegree < 6 * A.natDegree
                                      · by_cases hb19 : 4 * B.natDegree + D.natDegree < 7 * A.natDegree
                                        · exact Or.inl (hkill ⟨hA, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩)
                                        · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (?_))))))))))))))))))))
                                          omega
                                      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))))))))))))
                                        omega
                                    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))))))))))
                                      omega
                                  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))))))))))
                                    omega
                                · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))))))))
                                  omega
                              · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))))))))
                                omega
                            · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))))))
                              omega
                          · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))))))
                            omega
                        · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))))
                          omega
                      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))))
                        omega
                    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))
                      omega
                  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))
                    omega
                · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))
                  omega
              · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))
                omega
            · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))
              omega
          · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))
            omega
        · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
          omega
      · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
        omega
    · refine Or.inr (Or.inr (Or.inl ?_))
      omega
  · refine Or.inr (Or.inl ?_)
    omega

set_option maxHeartbeats 64000000 in
theorem quarticSigmaN7Cost_delta_band
    {delta : k} (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hkill : QuarticN7CostTopDelta810 A B C D E F G → delta = 0) :
    delta = 0 ∨
      5 * A.natDegree ≤ B.natDegree + C.natDegree + G.natDegree ∨
      6 * A.natDegree ≤ B.natDegree + E.natDegree + G.natDegree ∨
      6 * A.natDegree ≤ B.natDegree + 2 * F.natDegree ∨
      5 * A.natDegree ≤ 2 * C.natDegree + F.natDegree ∨
      5 * A.natDegree ≤ C.natDegree + D.natDegree + E.natDegree ∨
      6 * A.natDegree ≤ C.natDegree + D.natDegree + G.natDegree ∨
      6 * A.natDegree ≤ C.natDegree + E.natDegree + F.natDegree ∨
      6 * A.natDegree ≤ 2 * D.natDegree + F.natDegree ∨
      6 * A.natDegree ≤ D.natDegree + 2 * E.natDegree ∨
      4 * A.natDegree ≤ 3 * B.natDegree + C.natDegree ∨
      5 * A.natDegree ≤ 3 * B.natDegree + E.natDegree ∨
      6 * A.natDegree ≤ 3 * B.natDegree + G.natDegree ∨
      6 * A.natDegree ≤ 2 * B.natDegree + C.natDegree + F.natDegree ∨
      6 * A.natDegree ≤ 2 * B.natDegree + D.natDegree + E.natDegree ∨
      5 * A.natDegree ≤ B.natDegree + 3 * C.natDegree ∨
      6 * A.natDegree ≤ B.natDegree + 2 * C.natDegree + E.natDegree ∨
      6 * A.natDegree ≤ B.natDegree + C.natDegree + 2 * D.natDegree ∨
      6 * A.natDegree ≤ 3 * C.natDegree + D.natDegree ∨
      A.natDegree ≤ B.natDegree ∨
      6 * A.natDegree ≤ 4 * B.natDegree + D.natDegree ∨
      5 * A.natDegree ≤ C.natDegree + F.natDegree ∨
      6 * A.natDegree ≤ E.natDegree + F.natDegree ∨
      6 * A.natDegree ≤ 2 * B.natDegree + F.natDegree ∨
      5 * A.natDegree ≤ B.natDegree + 2 * C.natDegree ∨
      6 * A.natDegree ≤ B.natDegree + C.natDegree + E.natDegree ∨
      6 * A.natDegree ≤ B.natDegree + 2 * D.natDegree ∨
      6 * A.natDegree ≤ 2 * C.natDegree + D.natDegree ∨
      6 * A.natDegree ≤ 3 * B.natDegree + C.natDegree := by
  by_cases hb0 : B.natDegree + C.natDegree + G.natDegree < 5 * A.natDegree
  · by_cases hb1 : B.natDegree + E.natDegree + G.natDegree < 6 * A.natDegree
    · by_cases hb2 : B.natDegree + 2 * F.natDegree < 6 * A.natDegree
      · by_cases hb3 : 2 * C.natDegree + F.natDegree < 5 * A.natDegree
        · by_cases hb4 : C.natDegree + D.natDegree + E.natDegree < 5 * A.natDegree
          · by_cases hb5 : C.natDegree + D.natDegree + G.natDegree < 6 * A.natDegree
            · by_cases hb6 : C.natDegree + E.natDegree + F.natDegree < 6 * A.natDegree
              · by_cases hb7 : 2 * D.natDegree + F.natDegree < 6 * A.natDegree
                · by_cases hb8 : D.natDegree + 2 * E.natDegree < 6 * A.natDegree
                  · by_cases hb9 : 3 * B.natDegree + C.natDegree < 4 * A.natDegree
                    · by_cases hb10 : 3 * B.natDegree + E.natDegree < 5 * A.natDegree
                      · by_cases hb11 : 3 * B.natDegree + G.natDegree < 6 * A.natDegree
                        · by_cases hb12 : 2 * B.natDegree + C.natDegree + F.natDegree < 6 * A.natDegree
                          · by_cases hb13 : 2 * B.natDegree + D.natDegree + E.natDegree < 6 * A.natDegree
                            · by_cases hb14 : B.natDegree + 3 * C.natDegree < 5 * A.natDegree
                              · by_cases hb15 : B.natDegree + 2 * C.natDegree + E.natDegree < 6 * A.natDegree
                                · by_cases hb16 : B.natDegree + C.natDegree + 2 * D.natDegree < 6 * A.natDegree
                                  · by_cases hb17 : 3 * C.natDegree + D.natDegree < 6 * A.natDegree
                                    · by_cases hb18 : B.natDegree < A.natDegree
                                      · by_cases hb19 : 4 * B.natDegree + D.natDegree < 6 * A.natDegree
                                        · by_cases hb20 : C.natDegree + F.natDegree < 5 * A.natDegree
                                          · by_cases hb21 : E.natDegree + F.natDegree < 6 * A.natDegree
                                            · by_cases hb22 : 2 * B.natDegree + F.natDegree < 6 * A.natDegree
                                              · by_cases hb23 : B.natDegree + 2 * C.natDegree < 5 * A.natDegree
                                                · by_cases hb24 : B.natDegree + C.natDegree + E.natDegree < 6 * A.natDegree
                                                  · by_cases hb25 : B.natDegree + 2 * D.natDegree < 6 * A.natDegree
                                                    · by_cases hb26 : 2 * C.natDegree + D.natDegree < 6 * A.natDegree
                                                      · by_cases hb27 : 3 * B.natDegree + C.natDegree < 6 * A.natDegree
                                                        · exact Or.inl (hkill ⟨hA, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19, hb20, hb21, hb22, hb23, hb24, hb25, hb26, hb27⟩)
                                                        · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (?_))))))))))))))))))))))))))))
                                                          omega
                                                      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))))))))))))))))))))
                                                        omega
                                                    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))))))))))))))))))
                                                      omega
                                                  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))))))))))))))))))
                                                    omega
                                                · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))))))))))))))))
                                                  omega
                                              · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))))))))))))))))
                                                omega
                                            · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))))))))))))))
                                              omega
                                          · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))))))))))))))
                                            omega
                                        · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))))))))))))
                                          omega
                                      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))))))))))))
                                        omega
                                    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))))))))))
                                      omega
                                  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))))))))))
                                    omega
                                · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))))))))
                                  omega
                              · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))))))))
                                omega
                            · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))))))
                              omega
                          · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))))))
                            omega
                        · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))))
                          omega
                      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))))
                        omega
                    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))
                      omega
                  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))
                    omega
                · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))
                  omega
              · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))
                omega
            · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))
              omega
          · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))
            omega
        · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
          omega
      · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
        omega
    · refine Or.inr (Or.inr (Or.inl ?_))
      omega
  · refine Or.inr (Or.inl ?_)
    omega

set_option maxHeartbeats 64000000 in
theorem quarticSigmaN7Cost_zeta_band
    {zeta : k} (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hkill : QuarticN7CostTopZeta810 A B C D E F G → zeta = 0) :
    zeta = 0 ∨
      4 * A.natDegree ≤ B.natDegree + C.natDegree + G.natDegree ∨
      5 * A.natDegree ≤ B.natDegree + E.natDegree + G.natDegree ∨
      5 * A.natDegree ≤ B.natDegree + 2 * F.natDegree ∨
      4 * A.natDegree ≤ 2 * C.natDegree + F.natDegree ∨
      4 * A.natDegree ≤ C.natDegree + D.natDegree + E.natDegree ∨
      5 * A.natDegree ≤ C.natDegree + D.natDegree + G.natDegree ∨
      5 * A.natDegree ≤ C.natDegree + E.natDegree + F.natDegree ∨
      5 * A.natDegree ≤ 2 * D.natDegree + F.natDegree ∨
      5 * A.natDegree ≤ D.natDegree + 2 * E.natDegree ∨
      3 * A.natDegree ≤ 3 * B.natDegree + C.natDegree ∨
      4 * A.natDegree ≤ 3 * B.natDegree + E.natDegree ∨
      5 * A.natDegree ≤ 3 * B.natDegree + G.natDegree ∨
      5 * A.natDegree ≤ 2 * B.natDegree + C.natDegree + F.natDegree ∨
      5 * A.natDegree ≤ 2 * B.natDegree + D.natDegree + E.natDegree ∨
      4 * A.natDegree ≤ B.natDegree + 3 * C.natDegree ∨
      5 * A.natDegree ≤ B.natDegree + 2 * C.natDegree + E.natDegree ∨
      5 * A.natDegree ≤ B.natDegree + C.natDegree + 2 * D.natDegree ∨
      5 * A.natDegree ≤ 3 * C.natDegree + D.natDegree ∨
      4 * A.natDegree ≤ 5 * B.natDegree ∨
      5 * A.natDegree ≤ 4 * B.natDegree + D.natDegree ∨
      4 * A.natDegree ≤ C.natDegree + F.natDegree ∨
      5 * A.natDegree ≤ E.natDegree + F.natDegree ∨
      5 * A.natDegree ≤ 2 * B.natDegree + F.natDegree ∨
      4 * A.natDegree ≤ B.natDegree + 2 * C.natDegree ∨
      5 * A.natDegree ≤ B.natDegree + C.natDegree + E.natDegree ∨
      5 * A.natDegree ≤ B.natDegree + 2 * D.natDegree ∨
      5 * A.natDegree ≤ 2 * C.natDegree + D.natDegree ∨
      5 * A.natDegree ≤ 3 * B.natDegree + C.natDegree ∨
      4 * A.natDegree ≤ C.natDegree + D.natDegree ∨
      5 * A.natDegree ≤ C.natDegree + F.natDegree ∨
      5 * A.natDegree ≤ D.natDegree + E.natDegree ∨
      5 * A.natDegree ≤ 2 * B.natDegree + D.natDegree ∨
      5 * A.natDegree ≤ B.natDegree + 2 * C.natDegree := by
  by_cases hb0 : B.natDegree + C.natDegree + G.natDegree < 4 * A.natDegree
  · by_cases hb1 : B.natDegree + E.natDegree + G.natDegree < 5 * A.natDegree
    · by_cases hb2 : B.natDegree + 2 * F.natDegree < 5 * A.natDegree
      · by_cases hb3 : 2 * C.natDegree + F.natDegree < 4 * A.natDegree
        · by_cases hb4 : C.natDegree + D.natDegree + E.natDegree < 4 * A.natDegree
          · by_cases hb5 : C.natDegree + D.natDegree + G.natDegree < 5 * A.natDegree
            · by_cases hb6 : C.natDegree + E.natDegree + F.natDegree < 5 * A.natDegree
              · by_cases hb7 : 2 * D.natDegree + F.natDegree < 5 * A.natDegree
                · by_cases hb8 : D.natDegree + 2 * E.natDegree < 5 * A.natDegree
                  · by_cases hb9 : 3 * B.natDegree + C.natDegree < 3 * A.natDegree
                    · by_cases hb10 : 3 * B.natDegree + E.natDegree < 4 * A.natDegree
                      · by_cases hb11 : 3 * B.natDegree + G.natDegree < 5 * A.natDegree
                        · by_cases hb12 : 2 * B.natDegree + C.natDegree + F.natDegree < 5 * A.natDegree
                          · by_cases hb13 : 2 * B.natDegree + D.natDegree + E.natDegree < 5 * A.natDegree
                            · by_cases hb14 : B.natDegree + 3 * C.natDegree < 4 * A.natDegree
                              · by_cases hb15 : B.natDegree + 2 * C.natDegree + E.natDegree < 5 * A.natDegree
                                · by_cases hb16 : B.natDegree + C.natDegree + 2 * D.natDegree < 5 * A.natDegree
                                  · by_cases hb17 : 3 * C.natDegree + D.natDegree < 5 * A.natDegree
                                    · by_cases hb18 : 5 * B.natDegree < 4 * A.natDegree
                                      · by_cases hb19 : 4 * B.natDegree + D.natDegree < 5 * A.natDegree
                                        · by_cases hb20 : C.natDegree + F.natDegree < 4 * A.natDegree
                                          · by_cases hb21 : E.natDegree + F.natDegree < 5 * A.natDegree
                                            · by_cases hb22 : 2 * B.natDegree + F.natDegree < 5 * A.natDegree
                                              · by_cases hb23 : B.natDegree + 2 * C.natDegree < 4 * A.natDegree
                                                · by_cases hb24 : B.natDegree + C.natDegree + E.natDegree < 5 * A.natDegree
                                                  · by_cases hb25 : B.natDegree + 2 * D.natDegree < 5 * A.natDegree
                                                    · by_cases hb26 : 2 * C.natDegree + D.natDegree < 5 * A.natDegree
                                                      · by_cases hb27 : 3 * B.natDegree + C.natDegree < 5 * A.natDegree
                                                        · by_cases hb28 : C.natDegree + D.natDegree < 4 * A.natDegree
                                                          · by_cases hb29 : C.natDegree + F.natDegree < 5 * A.natDegree
                                                            · by_cases hb30 : D.natDegree + E.natDegree < 5 * A.natDegree
                                                              · by_cases hb31 : 2 * B.natDegree + D.natDegree < 5 * A.natDegree
                                                                · by_cases hb32 : B.natDegree + 2 * C.natDegree < 5 * A.natDegree
                                                                  · exact Or.inl (hkill ⟨hA, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19, hb20, hb21, hb22, hb23, hb24, hb25, hb26, hb27, hb28, hb29, hb30, hb31, hb32⟩)
                                                                  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (?_)))))))))))))))))))))))))))))))))
                                                                    omega
                                                                · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))))))))))))))))))))))))
                                                                  omega
                                                              · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))))))))))))))))))))))))
                                                                omega
                                                            · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))))))))))))))))))))))
                                                              omega
                                                          · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))))))))))))))))))))))
                                                            omega
                                                        · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))))))))))))))))))))
                                                          omega
                                                      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))))))))))))))))))))
                                                        omega
                                                    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))))))))))))))))))
                                                      omega
                                                  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))))))))))))))))))
                                                    omega
                                                · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))))))))))))))))
                                                  omega
                                              · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))))))))))))))))
                                                omega
                                            · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))))))))))))))
                                              omega
                                          · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))))))))))))))
                                            omega
                                        · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))))))))))))
                                          omega
                                      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))))))))))))
                                        omega
                                    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))))))))))
                                      omega
                                  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))))))))))
                                    omega
                                · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))))))))
                                  omega
                              · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))))))))
                                omega
                            · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))))))
                              omega
                          · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))))))
                            omega
                        · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))))
                          omega
                      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))))
                        omega
                    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))
                      omega
                  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))
                    omega
                · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))
                  omega
              · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))
                omega
            · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))
              omega
          · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))
            omega
        · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
          omega
      · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
        omega
    · refine Or.inr (Or.inr (Or.inl ?_))
      omega
  · refine Or.inr (Or.inl ?_)
    omega

set_option maxHeartbeats 64000000 in
theorem quarticSigmaN7Cost_theta_band
    {theta : k} (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hkill : QuarticN7CostTopTheta810 A B C D E F G → theta = 0) :
    theta = 0 ∨
      3 * A.natDegree ≤ B.natDegree + C.natDegree + G.natDegree ∨
      4 * A.natDegree ≤ B.natDegree + E.natDegree + G.natDegree ∨
      4 * A.natDegree ≤ B.natDegree + 2 * F.natDegree ∨
      3 * A.natDegree ≤ 2 * C.natDegree + F.natDegree ∨
      3 * A.natDegree ≤ C.natDegree + D.natDegree + E.natDegree ∨
      4 * A.natDegree ≤ C.natDegree + D.natDegree + G.natDegree ∨
      4 * A.natDegree ≤ C.natDegree + E.natDegree + F.natDegree ∨
      4 * A.natDegree ≤ 2 * D.natDegree + F.natDegree ∨
      4 * A.natDegree ≤ D.natDegree + 2 * E.natDegree ∨
      2 * A.natDegree ≤ 3 * B.natDegree + C.natDegree ∨
      3 * A.natDegree ≤ 3 * B.natDegree + E.natDegree ∨
      4 * A.natDegree ≤ 3 * B.natDegree + G.natDegree ∨
      4 * A.natDegree ≤ 2 * B.natDegree + C.natDegree + F.natDegree ∨
      4 * A.natDegree ≤ 2 * B.natDegree + D.natDegree + E.natDegree ∨
      3 * A.natDegree ≤ B.natDegree + 3 * C.natDegree ∨
      4 * A.natDegree ≤ B.natDegree + 2 * C.natDegree + E.natDegree ∨
      4 * A.natDegree ≤ B.natDegree + C.natDegree + 2 * D.natDegree ∨
      4 * A.natDegree ≤ 3 * C.natDegree + D.natDegree ∨
      3 * A.natDegree ≤ 5 * B.natDegree ∨
      4 * A.natDegree ≤ 4 * B.natDegree + D.natDegree ∨
      3 * A.natDegree ≤ C.natDegree + F.natDegree ∨
      4 * A.natDegree ≤ E.natDegree + F.natDegree ∨
      4 * A.natDegree ≤ 2 * B.natDegree + F.natDegree ∨
      3 * A.natDegree ≤ B.natDegree + 2 * C.natDegree ∨
      4 * A.natDegree ≤ B.natDegree + C.natDegree + E.natDegree ∨
      4 * A.natDegree ≤ B.natDegree + 2 * D.natDegree ∨
      4 * A.natDegree ≤ 2 * C.natDegree + D.natDegree ∨
      4 * A.natDegree ≤ 3 * B.natDegree + C.natDegree ∨
      3 * A.natDegree ≤ C.natDegree + D.natDegree ∨
      4 * A.natDegree ≤ C.natDegree + F.natDegree ∨
      4 * A.natDegree ≤ D.natDegree + E.natDegree ∨
      4 * A.natDegree ≤ 2 * B.natDegree + D.natDegree ∨
      4 * A.natDegree ≤ B.natDegree + 2 * C.natDegree ∨
      3 * A.natDegree ≤ B.natDegree + C.natDegree ∨
      4 * A.natDegree ≤ B.natDegree + E.natDegree ∨
      4 * A.natDegree ≤ C.natDegree + D.natDegree ∨
      4 * A.natDegree ≤ 3 * B.natDegree := by
  by_cases hb0 : B.natDegree + C.natDegree + G.natDegree < 3 * A.natDegree
  · by_cases hb1 : B.natDegree + E.natDegree + G.natDegree < 4 * A.natDegree
    · by_cases hb2 : B.natDegree + 2 * F.natDegree < 4 * A.natDegree
      · by_cases hb3 : 2 * C.natDegree + F.natDegree < 3 * A.natDegree
        · by_cases hb4 : C.natDegree + D.natDegree + E.natDegree < 3 * A.natDegree
          · by_cases hb5 : C.natDegree + D.natDegree + G.natDegree < 4 * A.natDegree
            · by_cases hb6 : C.natDegree + E.natDegree + F.natDegree < 4 * A.natDegree
              · by_cases hb7 : 2 * D.natDegree + F.natDegree < 4 * A.natDegree
                · by_cases hb8 : D.natDegree + 2 * E.natDegree < 4 * A.natDegree
                  · by_cases hb9 : 3 * B.natDegree + C.natDegree < 2 * A.natDegree
                    · by_cases hb10 : 3 * B.natDegree + E.natDegree < 3 * A.natDegree
                      · by_cases hb11 : 3 * B.natDegree + G.natDegree < 4 * A.natDegree
                        · by_cases hb12 : 2 * B.natDegree + C.natDegree + F.natDegree < 4 * A.natDegree
                          · by_cases hb13 : 2 * B.natDegree + D.natDegree + E.natDegree < 4 * A.natDegree
                            · by_cases hb14 : B.natDegree + 3 * C.natDegree < 3 * A.natDegree
                              · by_cases hb15 : B.natDegree + 2 * C.natDegree + E.natDegree < 4 * A.natDegree
                                · by_cases hb16 : B.natDegree + C.natDegree + 2 * D.natDegree < 4 * A.natDegree
                                  · by_cases hb17 : 3 * C.natDegree + D.natDegree < 4 * A.natDegree
                                    · by_cases hb18 : 5 * B.natDegree < 3 * A.natDegree
                                      · by_cases hb19 : 4 * B.natDegree + D.natDegree < 4 * A.natDegree
                                        · by_cases hb20 : C.natDegree + F.natDegree < 3 * A.natDegree
                                          · by_cases hb21 : E.natDegree + F.natDegree < 4 * A.natDegree
                                            · by_cases hb22 : 2 * B.natDegree + F.natDegree < 4 * A.natDegree
                                              · by_cases hb23 : B.natDegree + 2 * C.natDegree < 3 * A.natDegree
                                                · by_cases hb24 : B.natDegree + C.natDegree + E.natDegree < 4 * A.natDegree
                                                  · by_cases hb25 : B.natDegree + 2 * D.natDegree < 4 * A.natDegree
                                                    · by_cases hb26 : 2 * C.natDegree + D.natDegree < 4 * A.natDegree
                                                      · by_cases hb27 : 3 * B.natDegree + C.natDegree < 4 * A.natDegree
                                                        · by_cases hb28 : C.natDegree + D.natDegree < 3 * A.natDegree
                                                          · by_cases hb29 : C.natDegree + F.natDegree < 4 * A.natDegree
                                                            · by_cases hb30 : D.natDegree + E.natDegree < 4 * A.natDegree
                                                              · by_cases hb31 : 2 * B.natDegree + D.natDegree < 4 * A.natDegree
                                                                · by_cases hb32 : B.natDegree + 2 * C.natDegree < 4 * A.natDegree
                                                                  · by_cases hb33 : B.natDegree + C.natDegree < 3 * A.natDegree
                                                                    · by_cases hb34 : B.natDegree + E.natDegree < 4 * A.natDegree
                                                                      · by_cases hb35 : C.natDegree + D.natDegree < 4 * A.natDegree
                                                                        · by_cases hb36 : 3 * B.natDegree < 4 * A.natDegree
                                                                          · exact Or.inl (hkill ⟨hA, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19, hb20, hb21, hb22, hb23, hb24, hb25, hb26, hb27, hb28, hb29, hb30, hb31, hb32, hb33, hb34, hb35, hb36⟩)
                                                                          · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (?_)))))))))))))))))))))))))))))))))))))
                                                                            omega
                                                                        · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))))))))))))))))))))))))))))
                                                                          omega
                                                                      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))))))))))))))))))))))))))))
                                                                        omega
                                                                    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))))))))))))))))))))))))))
                                                                      omega
                                                                  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))))))))))))))))))))))))))
                                                                    omega
                                                                · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))))))))))))))))))))))))
                                                                  omega
                                                              · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))))))))))))))))))))))))
                                                                omega
                                                            · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))))))))))))))))))))))
                                                              omega
                                                          · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))))))))))))))))))))))
                                                            omega
                                                        · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))))))))))))))))))))
                                                          omega
                                                      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))))))))))))))))))))
                                                        omega
                                                    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))))))))))))))))))
                                                      omega
                                                  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))))))))))))))))))
                                                    omega
                                                · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))))))))))))))))
                                                  omega
                                              · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))))))))))))))))
                                                omega
                                            · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))))))))))))))
                                              omega
                                          · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))))))))))))))
                                            omega
                                        · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))))))))))))
                                          omega
                                      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))))))))))))
                                        omega
                                    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))))))))))
                                      omega
                                  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))))))))))
                                    omega
                                · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))))))))
                                  omega
                              · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))))))))
                                omega
                            · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))))))
                              omega
                          · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))))))
                            omega
                        · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))))
                          omega
                      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))))
                        omega
                    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))
                      omega
                  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))
                    omega
                · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))
                  omega
              · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))
                omega
            · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))
              omega
          · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))
            omega
        · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
          omega
      · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
        omega
    · refine Or.inr (Or.inr (Or.inl ?_))
      omega
  · refine Or.inr (Or.inl ?_)
    omega

set_option maxHeartbeats 64000000 in
/-- The cost-form `N₇` ladder as five band disjunctions, the
`n7-cost` band source of `UNOWNED_CHAMBERS.md`. -/
theorem quarticSigmaN7CostBands810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hprim : (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 1)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    (l = 0 ∨
      7 * A.natDegree ≤ B.natDegree + C.natDegree + G.natDegree ∨
      8 * A.natDegree ≤ B.natDegree + E.natDegree + G.natDegree ∨
      8 * A.natDegree ≤ B.natDegree + 2 * F.natDegree ∨
      7 * A.natDegree ≤ 2 * C.natDegree + F.natDegree ∨
      7 * A.natDegree ≤ C.natDegree + D.natDegree + E.natDegree ∨
      8 * A.natDegree ≤ C.natDegree + D.natDegree + G.natDegree ∨
      8 * A.natDegree ≤ C.natDegree + E.natDegree + F.natDegree ∨
      8 * A.natDegree ≤ 2 * D.natDegree + F.natDegree ∨
      8 * A.natDegree ≤ D.natDegree + 2 * E.natDegree ∨
      6 * A.natDegree ≤ 3 * B.natDegree + C.natDegree ∨
      7 * A.natDegree ≤ 3 * B.natDegree + E.natDegree ∨
      8 * A.natDegree ≤ 3 * B.natDegree + G.natDegree ∨
      8 * A.natDegree ≤ 2 * B.natDegree + C.natDegree + F.natDegree ∨
      8 * A.natDegree ≤ 2 * B.natDegree + D.natDegree + E.natDegree ∨
      7 * A.natDegree ≤ B.natDegree + 3 * C.natDegree ∨
      8 * A.natDegree ≤ B.natDegree + 2 * C.natDegree + E.natDegree ∨
      8 * A.natDegree ≤ B.natDegree + C.natDegree + 2 * D.natDegree ∨
      8 * A.natDegree ≤ 3 * C.natDegree + D.natDegree ∨
      7 * A.natDegree ≤ 5 * B.natDegree ∨
      8 * A.natDegree ≤ 4 * B.natDegree + D.natDegree) ∧
    (beta = 0 ∨
      6 * A.natDegree ≤ B.natDegree + C.natDegree + G.natDegree ∨
      7 * A.natDegree ≤ B.natDegree + E.natDegree + G.natDegree ∨
      7 * A.natDegree ≤ B.natDegree + 2 * F.natDegree ∨
      6 * A.natDegree ≤ 2 * C.natDegree + F.natDegree ∨
      6 * A.natDegree ≤ C.natDegree + D.natDegree + E.natDegree ∨
      7 * A.natDegree ≤ C.natDegree + D.natDegree + G.natDegree ∨
      7 * A.natDegree ≤ C.natDegree + E.natDegree + F.natDegree ∨
      7 * A.natDegree ≤ 2 * D.natDegree + F.natDegree ∨
      7 * A.natDegree ≤ D.natDegree + 2 * E.natDegree ∨
      5 * A.natDegree ≤ 3 * B.natDegree + C.natDegree ∨
      6 * A.natDegree ≤ 3 * B.natDegree + E.natDegree ∨
      7 * A.natDegree ≤ 3 * B.natDegree + G.natDegree ∨
      7 * A.natDegree ≤ 2 * B.natDegree + C.natDegree + F.natDegree ∨
      7 * A.natDegree ≤ 2 * B.natDegree + D.natDegree + E.natDegree ∨
      6 * A.natDegree ≤ B.natDegree + 3 * C.natDegree ∨
      7 * A.natDegree ≤ B.natDegree + 2 * C.natDegree + E.natDegree ∨
      7 * A.natDegree ≤ B.natDegree + C.natDegree + 2 * D.natDegree ∨
      7 * A.natDegree ≤ 3 * C.natDegree + D.natDegree ∨
      6 * A.natDegree ≤ 5 * B.natDegree ∨
      7 * A.natDegree ≤ 4 * B.natDegree + D.natDegree) ∧
    (delta = 0 ∨
      5 * A.natDegree ≤ B.natDegree + C.natDegree + G.natDegree ∨
      6 * A.natDegree ≤ B.natDegree + E.natDegree + G.natDegree ∨
      6 * A.natDegree ≤ B.natDegree + 2 * F.natDegree ∨
      5 * A.natDegree ≤ 2 * C.natDegree + F.natDegree ∨
      5 * A.natDegree ≤ C.natDegree + D.natDegree + E.natDegree ∨
      6 * A.natDegree ≤ C.natDegree + D.natDegree + G.natDegree ∨
      6 * A.natDegree ≤ C.natDegree + E.natDegree + F.natDegree ∨
      6 * A.natDegree ≤ 2 * D.natDegree + F.natDegree ∨
      6 * A.natDegree ≤ D.natDegree + 2 * E.natDegree ∨
      4 * A.natDegree ≤ 3 * B.natDegree + C.natDegree ∨
      5 * A.natDegree ≤ 3 * B.natDegree + E.natDegree ∨
      6 * A.natDegree ≤ 3 * B.natDegree + G.natDegree ∨
      6 * A.natDegree ≤ 2 * B.natDegree + C.natDegree + F.natDegree ∨
      6 * A.natDegree ≤ 2 * B.natDegree + D.natDegree + E.natDegree ∨
      5 * A.natDegree ≤ B.natDegree + 3 * C.natDegree ∨
      6 * A.natDegree ≤ B.natDegree + 2 * C.natDegree + E.natDegree ∨
      6 * A.natDegree ≤ B.natDegree + C.natDegree + 2 * D.natDegree ∨
      6 * A.natDegree ≤ 3 * C.natDegree + D.natDegree ∨
      A.natDegree ≤ B.natDegree ∨
      6 * A.natDegree ≤ 4 * B.natDegree + D.natDegree ∨
      5 * A.natDegree ≤ C.natDegree + F.natDegree ∨
      6 * A.natDegree ≤ E.natDegree + F.natDegree ∨
      6 * A.natDegree ≤ 2 * B.natDegree + F.natDegree ∨
      5 * A.natDegree ≤ B.natDegree + 2 * C.natDegree ∨
      6 * A.natDegree ≤ B.natDegree + C.natDegree + E.natDegree ∨
      6 * A.natDegree ≤ B.natDegree + 2 * D.natDegree ∨
      6 * A.natDegree ≤ 2 * C.natDegree + D.natDegree ∨
      6 * A.natDegree ≤ 3 * B.natDegree + C.natDegree) ∧
    (zeta = 0 ∨
      4 * A.natDegree ≤ B.natDegree + C.natDegree + G.natDegree ∨
      5 * A.natDegree ≤ B.natDegree + E.natDegree + G.natDegree ∨
      5 * A.natDegree ≤ B.natDegree + 2 * F.natDegree ∨
      4 * A.natDegree ≤ 2 * C.natDegree + F.natDegree ∨
      4 * A.natDegree ≤ C.natDegree + D.natDegree + E.natDegree ∨
      5 * A.natDegree ≤ C.natDegree + D.natDegree + G.natDegree ∨
      5 * A.natDegree ≤ C.natDegree + E.natDegree + F.natDegree ∨
      5 * A.natDegree ≤ 2 * D.natDegree + F.natDegree ∨
      5 * A.natDegree ≤ D.natDegree + 2 * E.natDegree ∨
      3 * A.natDegree ≤ 3 * B.natDegree + C.natDegree ∨
      4 * A.natDegree ≤ 3 * B.natDegree + E.natDegree ∨
      5 * A.natDegree ≤ 3 * B.natDegree + G.natDegree ∨
      5 * A.natDegree ≤ 2 * B.natDegree + C.natDegree + F.natDegree ∨
      5 * A.natDegree ≤ 2 * B.natDegree + D.natDegree + E.natDegree ∨
      4 * A.natDegree ≤ B.natDegree + 3 * C.natDegree ∨
      5 * A.natDegree ≤ B.natDegree + 2 * C.natDegree + E.natDegree ∨
      5 * A.natDegree ≤ B.natDegree + C.natDegree + 2 * D.natDegree ∨
      5 * A.natDegree ≤ 3 * C.natDegree + D.natDegree ∨
      4 * A.natDegree ≤ 5 * B.natDegree ∨
      5 * A.natDegree ≤ 4 * B.natDegree + D.natDegree ∨
      4 * A.natDegree ≤ C.natDegree + F.natDegree ∨
      5 * A.natDegree ≤ E.natDegree + F.natDegree ∨
      5 * A.natDegree ≤ 2 * B.natDegree + F.natDegree ∨
      4 * A.natDegree ≤ B.natDegree + 2 * C.natDegree ∨
      5 * A.natDegree ≤ B.natDegree + C.natDegree + E.natDegree ∨
      5 * A.natDegree ≤ B.natDegree + 2 * D.natDegree ∨
      5 * A.natDegree ≤ 2 * C.natDegree + D.natDegree ∨
      5 * A.natDegree ≤ 3 * B.natDegree + C.natDegree ∨
      4 * A.natDegree ≤ C.natDegree + D.natDegree ∨
      5 * A.natDegree ≤ C.natDegree + F.natDegree ∨
      5 * A.natDegree ≤ D.natDegree + E.natDegree ∨
      5 * A.natDegree ≤ 2 * B.natDegree + D.natDegree ∨
      5 * A.natDegree ≤ B.natDegree + 2 * C.natDegree) ∧
    (theta = 0 ∨
      3 * A.natDegree ≤ B.natDegree + C.natDegree + G.natDegree ∨
      4 * A.natDegree ≤ B.natDegree + E.natDegree + G.natDegree ∨
      4 * A.natDegree ≤ B.natDegree + 2 * F.natDegree ∨
      3 * A.natDegree ≤ 2 * C.natDegree + F.natDegree ∨
      3 * A.natDegree ≤ C.natDegree + D.natDegree + E.natDegree ∨
      4 * A.natDegree ≤ C.natDegree + D.natDegree + G.natDegree ∨
      4 * A.natDegree ≤ C.natDegree + E.natDegree + F.natDegree ∨
      4 * A.natDegree ≤ 2 * D.natDegree + F.natDegree ∨
      4 * A.natDegree ≤ D.natDegree + 2 * E.natDegree ∨
      2 * A.natDegree ≤ 3 * B.natDegree + C.natDegree ∨
      3 * A.natDegree ≤ 3 * B.natDegree + E.natDegree ∨
      4 * A.natDegree ≤ 3 * B.natDegree + G.natDegree ∨
      4 * A.natDegree ≤ 2 * B.natDegree + C.natDegree + F.natDegree ∨
      4 * A.natDegree ≤ 2 * B.natDegree + D.natDegree + E.natDegree ∨
      3 * A.natDegree ≤ B.natDegree + 3 * C.natDegree ∨
      4 * A.natDegree ≤ B.natDegree + 2 * C.natDegree + E.natDegree ∨
      4 * A.natDegree ≤ B.natDegree + C.natDegree + 2 * D.natDegree ∨
      4 * A.natDegree ≤ 3 * C.natDegree + D.natDegree ∨
      3 * A.natDegree ≤ 5 * B.natDegree ∨
      4 * A.natDegree ≤ 4 * B.natDegree + D.natDegree ∨
      3 * A.natDegree ≤ C.natDegree + F.natDegree ∨
      4 * A.natDegree ≤ E.natDegree + F.natDegree ∨
      4 * A.natDegree ≤ 2 * B.natDegree + F.natDegree ∨
      3 * A.natDegree ≤ B.natDegree + 2 * C.natDegree ∨
      4 * A.natDegree ≤ B.natDegree + C.natDegree + E.natDegree ∨
      4 * A.natDegree ≤ B.natDegree + 2 * D.natDegree ∨
      4 * A.natDegree ≤ 2 * C.natDegree + D.natDegree ∨
      4 * A.natDegree ≤ 3 * B.natDegree + C.natDegree ∨
      3 * A.natDegree ≤ C.natDegree + D.natDegree ∨
      4 * A.natDegree ≤ C.natDegree + F.natDegree ∨
      4 * A.natDegree ≤ D.natDegree + E.natDegree ∨
      4 * A.natDegree ≤ 2 * B.natDegree + D.natDegree ∨
      4 * A.natDegree ≤ B.natDegree + 2 * C.natDegree ∨
      3 * A.natDegree ≤ B.natDegree + C.natDegree ∨
      4 * A.natDegree ≤ B.natDegree + E.natDegree ∨
      4 * A.natDegree ≤ C.natDegree + D.natDegree ∨
      4 * A.natDegree ≤ 3 * B.natDegree) := by
  by_cases hTl : QuarticN7CostTopL810 A B C D E F G
  · have hl0 : l = 0 :=
      quarticSigmaN7Cost_l_eq_zero l beta gamma delta epsilon zeta eta theta
        A B C D E F G hTl hprim homi hnu hkap
    by_cases hTbeta : QuarticN7CostTopBeta810 A B C D E F G
    · have hbeta0 : beta = 0 :=
        quarticSigmaN7Cost_beta_eq_zero l beta gamma delta epsilon zeta eta theta
          A B C D E F G hTbeta hl0 hprim homi hnu hkap
      by_cases hTdelta : QuarticN7CostTopDelta810 A B C D E F G
      · have hdelta0 : delta = 0 :=
          quarticSigmaN7Cost_delta_eq_zero l beta gamma delta epsilon zeta eta theta
            A B C D E F G hTdelta hl0 hbeta0 hprim homi hnu hkap
        by_cases hTzeta : QuarticN7CostTopZeta810 A B C D E F G
        · have hzeta0 : zeta = 0 :=
            quarticSigmaN7Cost_zeta_eq_zero l beta gamma delta epsilon zeta eta theta
              A B C D E F G hTzeta hl0 hbeta0 hdelta0 hprim homi hnu hkap
          by_cases hTtheta : QuarticN7CostTopTheta810 A B C D E F G
          · have htheta0 : theta = 0 :=
              quarticSigmaN7Cost_theta_eq_zero l beta gamma delta epsilon zeta eta theta
                A B C D E F G hTtheta hl0 hbeta0 hdelta0 hzeta0 hprim homi hnu hkap
            exact ⟨Or.inl hl0, Or.inl hbeta0, Or.inl hdelta0, Or.inl hzeta0, Or.inl htheta0⟩
          · exact ⟨Or.inl hl0,
              Or.inl hbeta0,
              Or.inl hdelta0,
              Or.inl hzeta0,
              quarticSigmaN7Cost_theta_band (theta := theta) A B C D E F G hA
                (fun htop => absurd (htop) hTtheta)⟩
        · exact ⟨Or.inl hl0,
            Or.inl hbeta0,
            Or.inl hdelta0,
            quarticSigmaN7Cost_zeta_band (zeta := zeta) A B C D E F G hA
              (fun htop => absurd (htop) hTzeta),
            quarticSigmaN7Cost_theta_band (theta := theta) A B C D E F G hA
              (fun htop => absurd (quarticN7CostTopTheta810_imp_Zeta810 (htop)) hTzeta)⟩
      · exact ⟨Or.inl hl0,
          Or.inl hbeta0,
          quarticSigmaN7Cost_delta_band (delta := delta) A B C D E F G hA
            (fun htop => absurd (htop) hTdelta),
          quarticSigmaN7Cost_zeta_band (zeta := zeta) A B C D E F G hA
            (fun htop => absurd (quarticN7CostTopZeta810_imp_Delta810 (htop)) hTdelta),
          quarticSigmaN7Cost_theta_band (theta := theta) A B C D E F G hA
            (fun htop => absurd (quarticN7CostTopZeta810_imp_Delta810 (quarticN7CostTopTheta810_imp_Zeta810 (htop))) hTdelta)⟩
    · exact ⟨Or.inl hl0,
        quarticSigmaN7Cost_beta_band (beta := beta) A B C D E F G hA
          (fun htop => absurd (htop) hTbeta),
        quarticSigmaN7Cost_delta_band (delta := delta) A B C D E F G hA
          (fun htop => absurd (quarticN7CostTopDelta810_imp_Beta810 (htop)) hTbeta),
        quarticSigmaN7Cost_zeta_band (zeta := zeta) A B C D E F G hA
          (fun htop => absurd (quarticN7CostTopDelta810_imp_Beta810 (quarticN7CostTopZeta810_imp_Delta810 (htop))) hTbeta),
        quarticSigmaN7Cost_theta_band (theta := theta) A B C D E F G hA
          (fun htop => absurd (quarticN7CostTopDelta810_imp_Beta810 (quarticN7CostTopZeta810_imp_Delta810 (quarticN7CostTopTheta810_imp_Zeta810 (htop)))) hTbeta)⟩
  · exact ⟨quarticSigmaN7Cost_l_band (l := l) A B C D E F G hA
        (fun htop => absurd (htop) hTl),
      quarticSigmaN7Cost_beta_band (beta := beta) A B C D E F G hA
        (fun htop => absurd (quarticN7CostTopBeta810_imp_L810 (htop)) hTl),
      quarticSigmaN7Cost_delta_band (delta := delta) A B C D E F G hA
        (fun htop => absurd (quarticN7CostTopBeta810_imp_L810 (quarticN7CostTopDelta810_imp_Beta810 (htop))) hTl),
      quarticSigmaN7Cost_zeta_band (zeta := zeta) A B C D E F G hA
        (fun htop => absurd (quarticN7CostTopBeta810_imp_L810 (quarticN7CostTopDelta810_imp_Beta810 (quarticN7CostTopZeta810_imp_Delta810 (htop)))) hTl),
      quarticSigmaN7Cost_theta_band (theta := theta) A B C D E F G hA
        (fun htop => absurd (quarticN7CostTopBeta810_imp_L810 (quarticN7CostTopDelta810_imp_Beta810 (quarticN7CostTopZeta810_imp_Delta810 (quarticN7CostTopTheta810_imp_Zeta810 (htop))))) hTl)⟩


end QuarticN7Bands810

end Max11DegreeRoutes
