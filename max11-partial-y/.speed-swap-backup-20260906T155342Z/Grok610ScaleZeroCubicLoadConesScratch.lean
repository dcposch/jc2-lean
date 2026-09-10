import Grok610ScaleZeroCubicLoadLadderScratch

/-! # Scale-zero cubic load-compete single-monomial cones, `(6,10)`, `H = 0`

Continuation of `Grok610ScaleZeroCubicLoadLadderScratch`.  That file
ends at `normalized610ScaleZero_cubicResidual6`: load-compete, `l = 0`,
the four N₁ band disjunctions, and `CubicLoadSigmaSupportCone610`.

Plan `Grok610ScaleZeroCubicLoadCompetePlanScratch.md` File B (§3.3–3.6,
§5): kill the 12 single-monomial σ-argmin cones on the load-compete
side.  Reuses the cone-free `_eq_face_add_rest` module identities and
face/rest splits from `Grok610ScaleZeroCubicADominantScratch`.  `{C,D}`
uses `N₁` (and the N₁/N₂ 2×2 on the odd-column walls).  Face-degree 0
corners `{C}`, `{E}`, `{C,E}` reduce to `B = D = 0` and
`cubicLoadCompete_BD_zero_impossible`.

Does not close the multi-monomial cones `{B,C}`, `{B,C,E}`, `{B,C,D,E}`
(File C).  No `sorry`, no new axioms, no finite-root shortcut.
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

/-! ## Band specialisation: residual-6 four-way OR to the cone's `T_S` -/

section CubicLoadConeBandSpecialize610

variable {k : Type*} [Field k] [CharZero k]


/-- Specialise residual-6 four-way bands onto cone `B`. -/

theorem cubicLoadSigmaConeB610_specialize_beta
    {beta : k} {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeB610 A B C D E)
    (hband : (beta = 0 ∨
      7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 18 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 28 * E.natDegree)) :
    (beta = 0 ∨ 7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree) := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hCcmp, hDcmp, hEcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsC : 2 * C.natDegree + 1 ≤ A.natDegree + 2 * B.natDegree ∨ C.natDegree = 0 := by
    rcases hCcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  have hsD : 4 * D.natDegree + 1 ≤ A.natDegree + 6 * B.natDegree ∨ D.natDegree = 0 := by
    rcases hDcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  have hsE : 4 * E.natDegree + 1 ≤ 3 * A.natDegree + 6 * B.natDegree ∨ E.natDegree = 0 := by
    rcases hEcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  rcases hband with h | h | h | h | h
  · exact Or.inl h
  · -- B-summand of the four-way OR
    exact Or.inr h
  · -- C-summand of the four-way OR
    rcases hsC with hsC | hC0
    · omega
    · omega
  · -- D-summand of the four-way OR
    rcases hsD with hsD | hD0
    · omega
    · omega
  · -- E-summand of the four-way OR
    rcases hsE with hsE | hE0
    · omega
    · omega


theorem cubicLoadSigmaConeB610_specialize_delta
    {delta : k} {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeB610 A B C D E)
    (hband : (delta = 0 ∨
      7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 30 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 28 * E.natDegree)) :
    (delta = 0 ∨ 7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree) := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hCcmp, hDcmp, hEcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsC : 2 * C.natDegree + 1 ≤ A.natDegree + 2 * B.natDegree ∨ C.natDegree = 0 := by
    rcases hCcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  have hsD : 4 * D.natDegree + 1 ≤ A.natDegree + 6 * B.natDegree ∨ D.natDegree = 0 := by
    rcases hDcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  have hsE : 4 * E.natDegree + 1 ≤ 3 * A.natDegree + 6 * B.natDegree ∨ E.natDegree = 0 := by
    rcases hEcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  rcases hband with h | h | h | h | h
  · exact Or.inl h
  · -- B-summand of the four-way OR
    exact Or.inr h
  · -- C-summand of the four-way OR
    rcases hsC with hsC | hC0
    · omega
    · omega
  · -- D-summand of the four-way OR
    rcases hsD with hsD | hD0
    · omega
    · omega
  · -- E-summand of the four-way OR
    rcases hsE with hsE | hE0
    · omega
    · omega


theorem cubicLoadSigmaConeB610_specialize_zeta
    {zeta : k} {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeB610 A B C D E)
    (hband : (zeta = 0 ∨
      9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree ∨
      12 * A.natDegree ≤ 6 * A.natDegree + 6 * C.natDegree ∨
      10 * A.natDegree ≤ 6 * A.natDegree + 4 * D.natDegree ∨
      12 * A.natDegree ≤ 6 * A.natDegree + 4 * E.natDegree)) :
    (zeta = 0 ∨ 9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree) := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hCcmp, hDcmp, hEcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsC : 2 * C.natDegree + 1 ≤ A.natDegree + 2 * B.natDegree ∨ C.natDegree = 0 := by
    rcases hCcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  have hsD : 4 * D.natDegree + 1 ≤ A.natDegree + 6 * B.natDegree ∨ D.natDegree = 0 := by
    rcases hDcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  have hsE : 4 * E.natDegree + 1 ≤ 3 * A.natDegree + 6 * B.natDegree ∨ E.natDegree = 0 := by
    rcases hEcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  rcases hband with h | h | h | h | h
  · exact Or.inl h
  · -- B-summand of the four-way OR
    exact Or.inr h
  · -- C-summand of the four-way OR
    rcases hsC with hsC | hC0
    · omega
    · omega
  · -- D-summand of the four-way OR
    rcases hsD with hsD | hD0
    · omega
    · omega
  · -- E-summand of the four-way OR
    rcases hsE with hsE | hE0
    · omega
    · omega


theorem cubicLoadSigmaConeB610_specialize_theta
    {theta : k} {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeB610 A B C D E)
    (hband : (theta = 0 ∨
      7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 54 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 28 * E.natDegree)) :
    (theta = 0 ∨ 7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree) := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hCcmp, hDcmp, hEcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsC : 2 * C.natDegree + 1 ≤ A.natDegree + 2 * B.natDegree ∨ C.natDegree = 0 := by
    rcases hCcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  have hsD : 4 * D.natDegree + 1 ≤ A.natDegree + 6 * B.natDegree ∨ D.natDegree = 0 := by
    rcases hDcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  have hsE : 4 * E.natDegree + 1 ≤ 3 * A.natDegree + 6 * B.natDegree ∨ E.natDegree = 0 := by
    rcases hEcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  rcases hband with h | h | h | h | h
  · exact Or.inl h
  · -- B-summand of the four-way OR
    exact Or.inr h
  · -- C-summand of the four-way OR
    rcases hsC with hsC | hC0
    · omega
    · omega
  · -- D-summand of the four-way OR
    rcases hsD with hsD | hD0
    · omega
    · omega
  · -- E-summand of the four-way OR
    rcases hsE with hsE | hE0
    · omega
    · omega


/-- Specialise residual-6 four-way bands onto cone `C`. -/

theorem cubicLoadSigmaConeC610_specialize_beta
    {beta : k} {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeC610 A B C D E)
    (hband : (beta = 0 ∨
      7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 18 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 28 * E.natDegree)) :
    (beta = 0 ∨ 7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 42 * C.natDegree) := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hCne, hBcmp, hDcmp, hEcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsB : A.natDegree + 2 * B.natDegree + 1 ≤ 2 * C.natDegree ∨ B.natDegree = 0 := by
    rcases hBcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  have hsD : A.natDegree + 2 * D.natDegree + 1 ≤ 3 * C.natDegree ∨ D.natDegree = 0 := by
    rcases hDcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  have hsE : 2 * E.natDegree + 1 ≤ 3 * C.natDegree ∨ E.natDegree = 0 := by
    rcases hEcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  rcases hband with h | h | h | h | h
  · exact Or.inl h
  · -- B-summand of the four-way OR
    rcases hsB with hsB | hB0
    · omega
    · omega
  · -- C-summand of the four-way OR
    exact Or.inr h
  · -- D-summand of the four-way OR
    rcases hsD with hsD | hD0
    · omega
    · omega
  · -- E-summand of the four-way OR
    rcases hsE with hsE | hE0
    · omega
    · omega


theorem cubicLoadSigmaConeC610_specialize_delta
    {delta : k} {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeC610 A B C D E)
    (hband : (delta = 0 ∨
      7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 30 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 28 * E.natDegree)) :
    (delta = 0 ∨ 7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 42 * C.natDegree) := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hCne, hBcmp, hDcmp, hEcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsB : A.natDegree + 2 * B.natDegree + 1 ≤ 2 * C.natDegree ∨ B.natDegree = 0 := by
    rcases hBcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  have hsD : A.natDegree + 2 * D.natDegree + 1 ≤ 3 * C.natDegree ∨ D.natDegree = 0 := by
    rcases hDcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  have hsE : 2 * E.natDegree + 1 ≤ 3 * C.natDegree ∨ E.natDegree = 0 := by
    rcases hEcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  rcases hband with h | h | h | h | h
  · exact Or.inl h
  · -- B-summand of the four-way OR
    rcases hsB with hsB | hB0
    · omega
    · omega
  · -- C-summand of the four-way OR
    exact Or.inr h
  · -- D-summand of the four-way OR
    rcases hsD with hsD | hD0
    · omega
    · omega
  · -- E-summand of the four-way OR
    rcases hsE with hsE | hE0
    · omega
    · omega


theorem cubicLoadSigmaConeC610_specialize_zeta
    {zeta : k} {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeC610 A B C D E)
    (hband : (zeta = 0 ∨
      9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree ∨
      12 * A.natDegree ≤ 6 * A.natDegree + 6 * C.natDegree ∨
      10 * A.natDegree ≤ 6 * A.natDegree + 4 * D.natDegree ∨
      12 * A.natDegree ≤ 6 * A.natDegree + 4 * E.natDegree)) :
    (zeta = 0 ∨ 12 * A.natDegree ≤ 6 * A.natDegree + 6 * C.natDegree) := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hCne, hBcmp, hDcmp, hEcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsB : A.natDegree + 2 * B.natDegree + 1 ≤ 2 * C.natDegree ∨ B.natDegree = 0 := by
    rcases hBcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  have hsD : A.natDegree + 2 * D.natDegree + 1 ≤ 3 * C.natDegree ∨ D.natDegree = 0 := by
    rcases hDcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  have hsE : 2 * E.natDegree + 1 ≤ 3 * C.natDegree ∨ E.natDegree = 0 := by
    rcases hEcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  rcases hband with h | h | h | h | h
  · exact Or.inl h
  · -- B-summand of the four-way OR
    rcases hsB with hsB | hB0
    · omega
    · omega
  · -- C-summand of the four-way OR
    exact Or.inr h
  · -- D-summand of the four-way OR
    rcases hsD with hsD | hD0
    · omega
    · omega
  · -- E-summand of the four-way OR
    rcases hsE with hsE | hE0
    · omega
    · omega


theorem cubicLoadSigmaConeC610_specialize_theta
    {theta : k} {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeC610 A B C D E)
    (hband : (theta = 0 ∨
      7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 54 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 28 * E.natDegree)) :
    (theta = 0 ∨ 7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 42 * C.natDegree) := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hCne, hBcmp, hDcmp, hEcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsB : A.natDegree + 2 * B.natDegree + 1 ≤ 2 * C.natDegree ∨ B.natDegree = 0 := by
    rcases hBcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  have hsD : A.natDegree + 2 * D.natDegree + 1 ≤ 3 * C.natDegree ∨ D.natDegree = 0 := by
    rcases hDcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  have hsE : 2 * E.natDegree + 1 ≤ 3 * C.natDegree ∨ E.natDegree = 0 := by
    rcases hEcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  rcases hband with h | h | h | h | h
  · exact Or.inl h
  · -- B-summand of the four-way OR
    rcases hsB with hsB | hB0
    · omega
    · omega
  · -- C-summand of the four-way OR
    exact Or.inr h
  · -- D-summand of the four-way OR
    rcases hsD with hsD | hD0
    · omega
    · omega
  · -- E-summand of the four-way OR
    rcases hsE with hsE | hE0
    · omega
    · omega


/-- Specialise residual-6 four-way bands onto cone `D`. -/

theorem cubicLoadSigmaConeD610_specialize_beta
    {beta : k} {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeD610 A B C D E)
    (hband : (beta = 0 ∨
      7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 18 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 28 * E.natDegree)) :
    (beta = 0 ∨ 7 * (10 * A.natDegree) ≤ 18 * A.natDegree + 28 * D.natDegree) := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hDne, hBcmp, hCcmp, hEcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsB : A.natDegree + 6 * B.natDegree + 1 ≤ 4 * D.natDegree ∨ B.natDegree = 0 := by
    rcases hBcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  have hsC : 3 * C.natDegree + 1 ≤ A.natDegree + 2 * D.natDegree ∨ C.natDegree = 0 := by
    rcases hCcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  have hsE : 2 * E.natDegree + 1 ≤ A.natDegree + 2 * D.natDegree ∨ E.natDegree = 0 := by
    rcases hEcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  rcases hband with h | h | h | h | h
  · exact Or.inl h
  · -- B-summand of the four-way OR
    rcases hsB with hsB | hB0
    · omega
    · omega
  · -- C-summand of the four-way OR
    rcases hsC with hsC | hC0
    · omega
    · omega
  · -- D-summand of the four-way OR
    exact Or.inr h
  · -- E-summand of the four-way OR
    rcases hsE with hsE | hE0
    · omega
    · omega


theorem cubicLoadSigmaConeD610_specialize_delta
    {delta : k} {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeD610 A B C D E)
    (hband : (delta = 0 ∨
      7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 30 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 28 * E.natDegree)) :
    (delta = 0 ∨ 7 * (10 * A.natDegree) ≤ 30 * A.natDegree + 28 * D.natDegree) := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hDne, hBcmp, hCcmp, hEcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsB : A.natDegree + 6 * B.natDegree + 1 ≤ 4 * D.natDegree ∨ B.natDegree = 0 := by
    rcases hBcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  have hsC : 3 * C.natDegree + 1 ≤ A.natDegree + 2 * D.natDegree ∨ C.natDegree = 0 := by
    rcases hCcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  have hsE : 2 * E.natDegree + 1 ≤ A.natDegree + 2 * D.natDegree ∨ E.natDegree = 0 := by
    rcases hEcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  rcases hband with h | h | h | h | h
  · exact Or.inl h
  · -- B-summand of the four-way OR
    rcases hsB with hsB | hB0
    · omega
    · omega
  · -- C-summand of the four-way OR
    rcases hsC with hsC | hC0
    · omega
    · omega
  · -- D-summand of the four-way OR
    exact Or.inr h
  · -- E-summand of the four-way OR
    rcases hsE with hsE | hE0
    · omega
    · omega


theorem cubicLoadSigmaConeD610_specialize_zeta
    {zeta : k} {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeD610 A B C D E)
    (hband : (zeta = 0 ∨
      9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree ∨
      12 * A.natDegree ≤ 6 * A.natDegree + 6 * C.natDegree ∨
      10 * A.natDegree ≤ 6 * A.natDegree + 4 * D.natDegree ∨
      12 * A.natDegree ≤ 6 * A.natDegree + 4 * E.natDegree)) :
    (zeta = 0 ∨ 10 * A.natDegree ≤ 6 * A.natDegree + 4 * D.natDegree) := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hDne, hBcmp, hCcmp, hEcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsB : A.natDegree + 6 * B.natDegree + 1 ≤ 4 * D.natDegree ∨ B.natDegree = 0 := by
    rcases hBcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  have hsC : 3 * C.natDegree + 1 ≤ A.natDegree + 2 * D.natDegree ∨ C.natDegree = 0 := by
    rcases hCcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  have hsE : 2 * E.natDegree + 1 ≤ A.natDegree + 2 * D.natDegree ∨ E.natDegree = 0 := by
    rcases hEcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  rcases hband with h | h | h | h | h
  · exact Or.inl h
  · -- B-summand of the four-way OR
    rcases hsB with hsB | hB0
    · omega
    · omega
  · -- C-summand of the four-way OR
    rcases hsC with hsC | hC0
    · omega
    · omega
  · -- D-summand of the four-way OR
    exact Or.inr h
  · -- E-summand of the four-way OR
    rcases hsE with hsE | hE0
    · omega
    · omega


theorem cubicLoadSigmaConeD610_specialize_theta
    {theta : k} {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeD610 A B C D E)
    (hband : (theta = 0 ∨
      7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 54 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 28 * E.natDegree)) :
    (theta = 0 ∨ 7 * (10 * A.natDegree) ≤ 54 * A.natDegree + 28 * D.natDegree) := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hDne, hBcmp, hCcmp, hEcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsB : A.natDegree + 6 * B.natDegree + 1 ≤ 4 * D.natDegree ∨ B.natDegree = 0 := by
    rcases hBcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  have hsC : 3 * C.natDegree + 1 ≤ A.natDegree + 2 * D.natDegree ∨ C.natDegree = 0 := by
    rcases hCcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  have hsE : 2 * E.natDegree + 1 ≤ A.natDegree + 2 * D.natDegree ∨ E.natDegree = 0 := by
    rcases hEcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  rcases hband with h | h | h | h | h
  · exact Or.inl h
  · -- B-summand of the four-way OR
    rcases hsB with hsB | hB0
    · omega
    · omega
  · -- C-summand of the four-way OR
    rcases hsC with hsC | hC0
    · omega
    · omega
  · -- D-summand of the four-way OR
    exact Or.inr h
  · -- E-summand of the four-way OR
    rcases hsE with hsE | hE0
    · omega
    · omega


/-- Specialise residual-6 four-way bands onto cone `E`. -/

theorem cubicLoadSigmaConeE610_specialize_beta
    {beta : k} {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeE610 A B C D E)
    (hband : (beta = 0 ∨
      7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 18 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 28 * E.natDegree)) :
    (beta = 0 ∨ 7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 28 * E.natDegree) := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hEne, hBcmp, hCcmp, hDcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsB : 3 * A.natDegree + 6 * B.natDegree + 1 ≤ 4 * E.natDegree ∨ B.natDegree = 0 := by
    rcases hBcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  have hsC : 3 * C.natDegree + 1 ≤ 2 * E.natDegree ∨ C.natDegree = 0 := by
    rcases hCcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  have hsD : A.natDegree + 2 * D.natDegree + 1 ≤ 2 * E.natDegree ∨ D.natDegree = 0 := by
    rcases hDcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  rcases hband with h | h | h | h | h
  · exact Or.inl h
  · -- B-summand of the four-way OR
    rcases hsB with hsB | hB0
    · omega
    · omega
  · -- C-summand of the four-way OR
    rcases hsC with hsC | hC0
    · omega
    · omega
  · -- D-summand of the four-way OR
    rcases hsD with hsD | hD0
    · omega
    · omega
  · -- E-summand of the four-way OR
    exact Or.inr h


theorem cubicLoadSigmaConeE610_specialize_delta
    {delta : k} {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeE610 A B C D E)
    (hband : (delta = 0 ∨
      7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 30 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 28 * E.natDegree)) :
    (delta = 0 ∨ 7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 28 * E.natDegree) := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hEne, hBcmp, hCcmp, hDcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsB : 3 * A.natDegree + 6 * B.natDegree + 1 ≤ 4 * E.natDegree ∨ B.natDegree = 0 := by
    rcases hBcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  have hsC : 3 * C.natDegree + 1 ≤ 2 * E.natDegree ∨ C.natDegree = 0 := by
    rcases hCcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  have hsD : A.natDegree + 2 * D.natDegree + 1 ≤ 2 * E.natDegree ∨ D.natDegree = 0 := by
    rcases hDcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  rcases hband with h | h | h | h | h
  · exact Or.inl h
  · -- B-summand of the four-way OR
    rcases hsB with hsB | hB0
    · omega
    · omega
  · -- C-summand of the four-way OR
    rcases hsC with hsC | hC0
    · omega
    · omega
  · -- D-summand of the four-way OR
    rcases hsD with hsD | hD0
    · omega
    · omega
  · -- E-summand of the four-way OR
    exact Or.inr h


theorem cubicLoadSigmaConeE610_specialize_zeta
    {zeta : k} {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeE610 A B C D E)
    (hband : (zeta = 0 ∨
      9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree ∨
      12 * A.natDegree ≤ 6 * A.natDegree + 6 * C.natDegree ∨
      10 * A.natDegree ≤ 6 * A.natDegree + 4 * D.natDegree ∨
      12 * A.natDegree ≤ 6 * A.natDegree + 4 * E.natDegree)) :
    (zeta = 0 ∨ 12 * A.natDegree ≤ 6 * A.natDegree + 4 * E.natDegree) := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hEne, hBcmp, hCcmp, hDcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsB : 3 * A.natDegree + 6 * B.natDegree + 1 ≤ 4 * E.natDegree ∨ B.natDegree = 0 := by
    rcases hBcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  have hsC : 3 * C.natDegree + 1 ≤ 2 * E.natDegree ∨ C.natDegree = 0 := by
    rcases hCcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  have hsD : A.natDegree + 2 * D.natDegree + 1 ≤ 2 * E.natDegree ∨ D.natDegree = 0 := by
    rcases hDcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  rcases hband with h | h | h | h | h
  · exact Or.inl h
  · -- B-summand of the four-way OR
    rcases hsB with hsB | hB0
    · omega
    · omega
  · -- C-summand of the four-way OR
    rcases hsC with hsC | hC0
    · omega
    · omega
  · -- D-summand of the four-way OR
    rcases hsD with hsD | hD0
    · omega
    · omega
  · -- E-summand of the four-way OR
    exact Or.inr h


theorem cubicLoadSigmaConeE610_specialize_theta
    {theta : k} {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeE610 A B C D E)
    (hband : (theta = 0 ∨
      7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 54 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 28 * E.natDegree)) :
    (theta = 0 ∨ 7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 28 * E.natDegree) := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hEne, hBcmp, hCcmp, hDcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsB : 3 * A.natDegree + 6 * B.natDegree + 1 ≤ 4 * E.natDegree ∨ B.natDegree = 0 := by
    rcases hBcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  have hsC : 3 * C.natDegree + 1 ≤ 2 * E.natDegree ∨ C.natDegree = 0 := by
    rcases hCcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  have hsD : A.natDegree + 2 * D.natDegree + 1 ≤ 2 * E.natDegree ∨ D.natDegree = 0 := by
    rcases hDcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  rcases hband with h | h | h | h | h
  · exact Or.inl h
  · -- B-summand of the four-way OR
    rcases hsB with hsB | hB0
    · omega
    · omega
  · -- C-summand of the four-way OR
    rcases hsC with hsC | hC0
    · omega
    · omega
  · -- D-summand of the four-way OR
    rcases hsD with hsD | hD0
    · omega
    · omega
  · -- E-summand of the four-way OR
    exact Or.inr h


/-- Specialise residual-6 four-way bands onto cone `BD`. -/

theorem cubicLoadSigmaConeBD610_specialize_beta
    {beta : k} {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeBD610 A B C D E)
    (hband : (beta = 0 ∨
      7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 18 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 28 * E.natDegree)) :
    (beta = 0 ∨ 7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree) := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hDne, heq, hCcmp, hEcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsC : 2 * C.natDegree + 1 ≤ A.natDegree + 2 * B.natDegree ∨ C.natDegree = 0 := by
    rcases hCcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  have hsE : 4 * E.natDegree + 1 ≤ 3 * A.natDegree + 6 * B.natDegree ∨ E.natDegree = 0 := by
    rcases hEcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  rcases hband with h | h | h | h | h
  · exact Or.inl h
  · -- B-summand of the four-way OR
    exact Or.inr h
  · -- C-summand of the four-way OR
    rcases hsC with hsC | hC0
    · omega
    · omega
  · -- D-summand of the four-way OR
    omega
  · -- E-summand of the four-way OR
    rcases hsE with hsE | hE0
    · omega
    · omega


theorem cubicLoadSigmaConeBD610_specialize_delta
    {delta : k} {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeBD610 A B C D E)
    (hband : (delta = 0 ∨
      7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 30 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 28 * E.natDegree)) :
    (delta = 0 ∨ 7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree) := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hDne, heq, hCcmp, hEcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsC : 2 * C.natDegree + 1 ≤ A.natDegree + 2 * B.natDegree ∨ C.natDegree = 0 := by
    rcases hCcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  have hsE : 4 * E.natDegree + 1 ≤ 3 * A.natDegree + 6 * B.natDegree ∨ E.natDegree = 0 := by
    rcases hEcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  rcases hband with h | h | h | h | h
  · exact Or.inl h
  · -- B-summand of the four-way OR
    exact Or.inr h
  · -- C-summand of the four-way OR
    rcases hsC with hsC | hC0
    · omega
    · omega
  · -- D-summand of the four-way OR
    omega
  · -- E-summand of the four-way OR
    rcases hsE with hsE | hE0
    · omega
    · omega


theorem cubicLoadSigmaConeBD610_specialize_zeta
    {zeta : k} {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeBD610 A B C D E)
    (hband : (zeta = 0 ∨
      9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree ∨
      12 * A.natDegree ≤ 6 * A.natDegree + 6 * C.natDegree ∨
      10 * A.natDegree ≤ 6 * A.natDegree + 4 * D.natDegree ∨
      12 * A.natDegree ≤ 6 * A.natDegree + 4 * E.natDegree)) :
    (zeta = 0 ∨ 9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree) := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hDne, heq, hCcmp, hEcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsC : 2 * C.natDegree + 1 ≤ A.natDegree + 2 * B.natDegree ∨ C.natDegree = 0 := by
    rcases hCcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  have hsE : 4 * E.natDegree + 1 ≤ 3 * A.natDegree + 6 * B.natDegree ∨ E.natDegree = 0 := by
    rcases hEcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  rcases hband with h | h | h | h | h
  · exact Or.inl h
  · -- B-summand of the four-way OR
    exact Or.inr h
  · -- C-summand of the four-way OR
    rcases hsC with hsC | hC0
    · omega
    · omega
  · -- D-summand of the four-way OR
    omega
  · -- E-summand of the four-way OR
    rcases hsE with hsE | hE0
    · omega
    · omega


theorem cubicLoadSigmaConeBD610_specialize_theta
    {theta : k} {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeBD610 A B C D E)
    (hband : (theta = 0 ∨
      7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 54 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 28 * E.natDegree)) :
    (theta = 0 ∨ 7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree) := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hDne, heq, hCcmp, hEcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsC : 2 * C.natDegree + 1 ≤ A.natDegree + 2 * B.natDegree ∨ C.natDegree = 0 := by
    rcases hCcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  have hsE : 4 * E.natDegree + 1 ≤ 3 * A.natDegree + 6 * B.natDegree ∨ E.natDegree = 0 := by
    rcases hEcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  rcases hband with h | h | h | h | h
  · exact Or.inl h
  · -- B-summand of the four-way OR
    exact Or.inr h
  · -- C-summand of the four-way OR
    rcases hsC with hsC | hC0
    · omega
    · omega
  · -- D-summand of the four-way OR
    omega
  · -- E-summand of the four-way OR
    rcases hsE with hsE | hE0
    · omega
    · omega


/-- Specialise residual-6 four-way bands onto cone `BE`. -/

theorem cubicLoadSigmaConeBE610_specialize_beta
    {beta : k} {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeBE610 A B C D E)
    (hband : (beta = 0 ∨
      7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 18 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 28 * E.natDegree)) :
    (beta = 0 ∨ 7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree) := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hEne, heq, hCcmp, hDcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsC : 2 * C.natDegree + 1 ≤ A.natDegree + 2 * B.natDegree ∨ C.natDegree = 0 := by
    rcases hCcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  have hsD : 4 * D.natDegree + 1 ≤ A.natDegree + 6 * B.natDegree ∨ D.natDegree = 0 := by
    rcases hDcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  rcases hband with h | h | h | h | h
  · exact Or.inl h
  · -- B-summand of the four-way OR
    exact Or.inr h
  · -- C-summand of the four-way OR
    rcases hsC with hsC | hC0
    · omega
    · omega
  · -- D-summand of the four-way OR
    rcases hsD with hsD | hD0
    · omega
    · omega
  · -- E-summand of the four-way OR
    omega


theorem cubicLoadSigmaConeBE610_specialize_delta
    {delta : k} {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeBE610 A B C D E)
    (hband : (delta = 0 ∨
      7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 30 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 28 * E.natDegree)) :
    (delta = 0 ∨ 7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree) := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hEne, heq, hCcmp, hDcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsC : 2 * C.natDegree + 1 ≤ A.natDegree + 2 * B.natDegree ∨ C.natDegree = 0 := by
    rcases hCcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  have hsD : 4 * D.natDegree + 1 ≤ A.natDegree + 6 * B.natDegree ∨ D.natDegree = 0 := by
    rcases hDcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  rcases hband with h | h | h | h | h
  · exact Or.inl h
  · -- B-summand of the four-way OR
    exact Or.inr h
  · -- C-summand of the four-way OR
    rcases hsC with hsC | hC0
    · omega
    · omega
  · -- D-summand of the four-way OR
    rcases hsD with hsD | hD0
    · omega
    · omega
  · -- E-summand of the four-way OR
    omega


theorem cubicLoadSigmaConeBE610_specialize_zeta
    {zeta : k} {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeBE610 A B C D E)
    (hband : (zeta = 0 ∨
      9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree ∨
      12 * A.natDegree ≤ 6 * A.natDegree + 6 * C.natDegree ∨
      10 * A.natDegree ≤ 6 * A.natDegree + 4 * D.natDegree ∨
      12 * A.natDegree ≤ 6 * A.natDegree + 4 * E.natDegree)) :
    (zeta = 0 ∨ 9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree) := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hEne, heq, hCcmp, hDcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsC : 2 * C.natDegree + 1 ≤ A.natDegree + 2 * B.natDegree ∨ C.natDegree = 0 := by
    rcases hCcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  have hsD : 4 * D.natDegree + 1 ≤ A.natDegree + 6 * B.natDegree ∨ D.natDegree = 0 := by
    rcases hDcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  rcases hband with h | h | h | h | h
  · exact Or.inl h
  · -- B-summand of the four-way OR
    exact Or.inr h
  · -- C-summand of the four-way OR
    rcases hsC with hsC | hC0
    · omega
    · omega
  · -- D-summand of the four-way OR
    rcases hsD with hsD | hD0
    · omega
    · omega
  · -- E-summand of the four-way OR
    omega


theorem cubicLoadSigmaConeBE610_specialize_theta
    {theta : k} {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeBE610 A B C D E)
    (hband : (theta = 0 ∨
      7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 54 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 28 * E.natDegree)) :
    (theta = 0 ∨ 7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree) := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hEne, heq, hCcmp, hDcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsC : 2 * C.natDegree + 1 ≤ A.natDegree + 2 * B.natDegree ∨ C.natDegree = 0 := by
    rcases hCcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  have hsD : 4 * D.natDegree + 1 ≤ A.natDegree + 6 * B.natDegree ∨ D.natDegree = 0 := by
    rcases hDcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  rcases hband with h | h | h | h | h
  · exact Or.inl h
  · -- B-summand of the four-way OR
    exact Or.inr h
  · -- C-summand of the four-way OR
    rcases hsC with hsC | hC0
    · omega
    · omega
  · -- D-summand of the four-way OR
    rcases hsD with hsD | hD0
    · omega
    · omega
  · -- E-summand of the four-way OR
    omega


/-- Specialise residual-6 four-way bands onto cone `CD`. -/

theorem cubicLoadSigmaConeCD610_specialize_beta
    {beta : k} {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hband : (beta = 0 ∨
      7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 18 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 28 * E.natDegree)) :
    (beta = 0 ∨ 7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 42 * C.natDegree) := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hCne, hDne, heq, hBcmp, hEcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsB : A.natDegree + 2 * B.natDegree + 1 ≤ 2 * C.natDegree ∨ B.natDegree = 0 := by
    rcases hBcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  have hsE : 2 * E.natDegree + 1 ≤ 3 * C.natDegree ∨ E.natDegree = 0 := by
    rcases hEcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  rcases hband with h | h | h | h | h
  · exact Or.inl h
  · -- B-summand of the four-way OR
    rcases hsB with hsB | hB0
    · omega
    · omega
  · -- C-summand of the four-way OR
    exact Or.inr h
  · -- D-summand of the four-way OR
    omega
  · -- E-summand of the four-way OR
    rcases hsE with hsE | hE0
    · omega
    · omega


theorem cubicLoadSigmaConeCD610_specialize_delta
    {delta : k} {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hband : (delta = 0 ∨
      7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 30 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 28 * E.natDegree)) :
    (delta = 0 ∨ 7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 42 * C.natDegree) := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hCne, hDne, heq, hBcmp, hEcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsB : A.natDegree + 2 * B.natDegree + 1 ≤ 2 * C.natDegree ∨ B.natDegree = 0 := by
    rcases hBcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  have hsE : 2 * E.natDegree + 1 ≤ 3 * C.natDegree ∨ E.natDegree = 0 := by
    rcases hEcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  rcases hband with h | h | h | h | h
  · exact Or.inl h
  · -- B-summand of the four-way OR
    rcases hsB with hsB | hB0
    · omega
    · omega
  · -- C-summand of the four-way OR
    exact Or.inr h
  · -- D-summand of the four-way OR
    omega
  · -- E-summand of the four-way OR
    rcases hsE with hsE | hE0
    · omega
    · omega


theorem cubicLoadSigmaConeCD610_specialize_zeta
    {zeta : k} {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hband : (zeta = 0 ∨
      9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree ∨
      12 * A.natDegree ≤ 6 * A.natDegree + 6 * C.natDegree ∨
      10 * A.natDegree ≤ 6 * A.natDegree + 4 * D.natDegree ∨
      12 * A.natDegree ≤ 6 * A.natDegree + 4 * E.natDegree)) :
    (zeta = 0 ∨ 12 * A.natDegree ≤ 6 * A.natDegree + 6 * C.natDegree) := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hCne, hDne, heq, hBcmp, hEcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsB : A.natDegree + 2 * B.natDegree + 1 ≤ 2 * C.natDegree ∨ B.natDegree = 0 := by
    rcases hBcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  have hsE : 2 * E.natDegree + 1 ≤ 3 * C.natDegree ∨ E.natDegree = 0 := by
    rcases hEcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  rcases hband with h | h | h | h | h
  · exact Or.inl h
  · -- B-summand of the four-way OR
    rcases hsB with hsB | hB0
    · omega
    · omega
  · -- C-summand of the four-way OR
    exact Or.inr h
  · -- D-summand of the four-way OR
    omega
  · -- E-summand of the four-way OR
    rcases hsE with hsE | hE0
    · omega
    · omega


theorem cubicLoadSigmaConeCD610_specialize_theta
    {theta : k} {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hband : (theta = 0 ∨
      7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 54 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 28 * E.natDegree)) :
    (theta = 0 ∨ 7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 42 * C.natDegree) := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hCne, hDne, heq, hBcmp, hEcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsB : A.natDegree + 2 * B.natDegree + 1 ≤ 2 * C.natDegree ∨ B.natDegree = 0 := by
    rcases hBcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  have hsE : 2 * E.natDegree + 1 ≤ 3 * C.natDegree ∨ E.natDegree = 0 := by
    rcases hEcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  rcases hband with h | h | h | h | h
  · exact Or.inl h
  · -- B-summand of the four-way OR
    rcases hsB with hsB | hB0
    · omega
    · omega
  · -- C-summand of the four-way OR
    exact Or.inr h
  · -- D-summand of the four-way OR
    omega
  · -- E-summand of the four-way OR
    rcases hsE with hsE | hE0
    · omega
    · omega


/-- Specialise residual-6 four-way bands onto cone `CE`. -/

theorem cubicLoadSigmaConeCE610_specialize_beta
    {beta : k} {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeCE610 A B C D E)
    (hband : (beta = 0 ∨
      7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 18 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 28 * E.natDegree)) :
    (beta = 0 ∨ 7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 42 * C.natDegree) := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hCne, hEne, heq, hBcmp, hDcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsB : A.natDegree + 2 * B.natDegree + 1 ≤ 2 * C.natDegree ∨ B.natDegree = 0 := by
    rcases hBcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  have hsD : A.natDegree + 2 * D.natDegree + 1 ≤ 3 * C.natDegree ∨ D.natDegree = 0 := by
    rcases hDcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  rcases hband with h | h | h | h | h
  · exact Or.inl h
  · -- B-summand of the four-way OR
    rcases hsB with hsB | hB0
    · omega
    · omega
  · -- C-summand of the four-way OR
    exact Or.inr h
  · -- D-summand of the four-way OR
    rcases hsD with hsD | hD0
    · omega
    · omega
  · -- E-summand of the four-way OR
    omega


theorem cubicLoadSigmaConeCE610_specialize_delta
    {delta : k} {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeCE610 A B C D E)
    (hband : (delta = 0 ∨
      7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 30 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 28 * E.natDegree)) :
    (delta = 0 ∨ 7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 42 * C.natDegree) := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hCne, hEne, heq, hBcmp, hDcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsB : A.natDegree + 2 * B.natDegree + 1 ≤ 2 * C.natDegree ∨ B.natDegree = 0 := by
    rcases hBcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  have hsD : A.natDegree + 2 * D.natDegree + 1 ≤ 3 * C.natDegree ∨ D.natDegree = 0 := by
    rcases hDcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  rcases hband with h | h | h | h | h
  · exact Or.inl h
  · -- B-summand of the four-way OR
    rcases hsB with hsB | hB0
    · omega
    · omega
  · -- C-summand of the four-way OR
    exact Or.inr h
  · -- D-summand of the four-way OR
    rcases hsD with hsD | hD0
    · omega
    · omega
  · -- E-summand of the four-way OR
    omega


theorem cubicLoadSigmaConeCE610_specialize_zeta
    {zeta : k} {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeCE610 A B C D E)
    (hband : (zeta = 0 ∨
      9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree ∨
      12 * A.natDegree ≤ 6 * A.natDegree + 6 * C.natDegree ∨
      10 * A.natDegree ≤ 6 * A.natDegree + 4 * D.natDegree ∨
      12 * A.natDegree ≤ 6 * A.natDegree + 4 * E.natDegree)) :
    (zeta = 0 ∨ 12 * A.natDegree ≤ 6 * A.natDegree + 6 * C.natDegree) := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hCne, hEne, heq, hBcmp, hDcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsB : A.natDegree + 2 * B.natDegree + 1 ≤ 2 * C.natDegree ∨ B.natDegree = 0 := by
    rcases hBcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  have hsD : A.natDegree + 2 * D.natDegree + 1 ≤ 3 * C.natDegree ∨ D.natDegree = 0 := by
    rcases hDcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  rcases hband with h | h | h | h | h
  · exact Or.inl h
  · -- B-summand of the four-way OR
    rcases hsB with hsB | hB0
    · omega
    · omega
  · -- C-summand of the four-way OR
    exact Or.inr h
  · -- D-summand of the four-way OR
    rcases hsD with hsD | hD0
    · omega
    · omega
  · -- E-summand of the four-way OR
    omega


theorem cubicLoadSigmaConeCE610_specialize_theta
    {theta : k} {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeCE610 A B C D E)
    (hband : (theta = 0 ∨
      7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 54 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 28 * E.natDegree)) :
    (theta = 0 ∨ 7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 42 * C.natDegree) := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hCne, hEne, heq, hBcmp, hDcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsB : A.natDegree + 2 * B.natDegree + 1 ≤ 2 * C.natDegree ∨ B.natDegree = 0 := by
    rcases hBcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  have hsD : A.natDegree + 2 * D.natDegree + 1 ≤ 3 * C.natDegree ∨ D.natDegree = 0 := by
    rcases hDcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  rcases hband with h | h | h | h | h
  · exact Or.inl h
  · -- B-summand of the four-way OR
    rcases hsB with hsB | hB0
    · omega
    · omega
  · -- C-summand of the four-way OR
    exact Or.inr h
  · -- D-summand of the four-way OR
    rcases hsD with hsD | hD0
    · omega
    · omega
  · -- E-summand of the four-way OR
    omega


/-- Specialise residual-6 four-way bands onto cone `DE`. -/

theorem cubicLoadSigmaConeDE610_specialize_beta
    {beta : k} {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeDE610 A B C D E)
    (hband : (beta = 0 ∨
      7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 18 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 28 * E.natDegree)) :
    (beta = 0 ∨ 7 * (10 * A.natDegree) ≤ 18 * A.natDegree + 28 * D.natDegree) := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hDne, hEne, heq, hBcmp, hCcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsB : A.natDegree + 6 * B.natDegree + 1 ≤ 4 * D.natDegree ∨ B.natDegree = 0 := by
    rcases hBcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  have hsC : 3 * C.natDegree + 1 ≤ A.natDegree + 2 * D.natDegree ∨ C.natDegree = 0 := by
    rcases hCcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  rcases hband with h | h | h | h | h
  · exact Or.inl h
  · -- B-summand of the four-way OR
    rcases hsB with hsB | hB0
    · omega
    · omega
  · -- C-summand of the four-way OR
    rcases hsC with hsC | hC0
    · omega
    · omega
  · -- D-summand of the four-way OR
    exact Or.inr h
  · -- E-summand of the four-way OR
    omega


theorem cubicLoadSigmaConeDE610_specialize_delta
    {delta : k} {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeDE610 A B C D E)
    (hband : (delta = 0 ∨
      7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 30 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 28 * E.natDegree)) :
    (delta = 0 ∨ 7 * (10 * A.natDegree) ≤ 30 * A.natDegree + 28 * D.natDegree) := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hDne, hEne, heq, hBcmp, hCcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsB : A.natDegree + 6 * B.natDegree + 1 ≤ 4 * D.natDegree ∨ B.natDegree = 0 := by
    rcases hBcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  have hsC : 3 * C.natDegree + 1 ≤ A.natDegree + 2 * D.natDegree ∨ C.natDegree = 0 := by
    rcases hCcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  rcases hband with h | h | h | h | h
  · exact Or.inl h
  · -- B-summand of the four-way OR
    rcases hsB with hsB | hB0
    · omega
    · omega
  · -- C-summand of the four-way OR
    rcases hsC with hsC | hC0
    · omega
    · omega
  · -- D-summand of the four-way OR
    exact Or.inr h
  · -- E-summand of the four-way OR
    omega


theorem cubicLoadSigmaConeDE610_specialize_zeta
    {zeta : k} {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeDE610 A B C D E)
    (hband : (zeta = 0 ∨
      9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree ∨
      12 * A.natDegree ≤ 6 * A.natDegree + 6 * C.natDegree ∨
      10 * A.natDegree ≤ 6 * A.natDegree + 4 * D.natDegree ∨
      12 * A.natDegree ≤ 6 * A.natDegree + 4 * E.natDegree)) :
    (zeta = 0 ∨ 10 * A.natDegree ≤ 6 * A.natDegree + 4 * D.natDegree) := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hDne, hEne, heq, hBcmp, hCcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsB : A.natDegree + 6 * B.natDegree + 1 ≤ 4 * D.natDegree ∨ B.natDegree = 0 := by
    rcases hBcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  have hsC : 3 * C.natDegree + 1 ≤ A.natDegree + 2 * D.natDegree ∨ C.natDegree = 0 := by
    rcases hCcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  rcases hband with h | h | h | h | h
  · exact Or.inl h
  · -- B-summand of the four-way OR
    rcases hsB with hsB | hB0
    · omega
    · omega
  · -- C-summand of the four-way OR
    rcases hsC with hsC | hC0
    · omega
    · omega
  · -- D-summand of the four-way OR
    exact Or.inr h
  · -- E-summand of the four-way OR
    omega


theorem cubicLoadSigmaConeDE610_specialize_theta
    {theta : k} {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeDE610 A B C D E)
    (hband : (theta = 0 ∨
      7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 54 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 28 * E.natDegree)) :
    (theta = 0 ∨ 7 * (10 * A.natDegree) ≤ 54 * A.natDegree + 28 * D.natDegree) := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hDne, hEne, heq, hBcmp, hCcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsB : A.natDegree + 6 * B.natDegree + 1 ≤ 4 * D.natDegree ∨ B.natDegree = 0 := by
    rcases hBcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  have hsC : 3 * C.natDegree + 1 ≤ A.natDegree + 2 * D.natDegree ∨ C.natDegree = 0 := by
    rcases hCcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  rcases hband with h | h | h | h | h
  · exact Or.inl h
  · -- B-summand of the four-way OR
    rcases hsB with hsB | hB0
    · omega
    · omega
  · -- C-summand of the four-way OR
    rcases hsC with hsC | hC0
    · omega
    · omega
  · -- D-summand of the four-way OR
    exact Or.inr h
  · -- E-summand of the four-way OR
    omega


/-- Specialise residual-6 four-way bands onto cone `BCD`. -/

theorem cubicLoadSigmaConeBCD610_specialize_beta
    {beta : k} {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeBCD610 A B C D E)
    (hband : (beta = 0 ∨
      7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 18 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 28 * E.natDegree)) :
    (beta = 0 ∨ 7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree) := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hCne, hDne, heq1, heq2, hEcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsE : 4 * E.natDegree + 1 ≤ 3 * A.natDegree + 6 * B.natDegree ∨ E.natDegree = 0 := by
    rcases hEcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  rcases hband with h | h | h | h | h
  · exact Or.inl h
  · -- B-summand of the four-way OR
    exact Or.inr h
  · -- C-summand of the four-way OR
    omega
  · -- D-summand of the four-way OR
    omega
  · -- E-summand of the four-way OR
    rcases hsE with hsE | hE0
    · omega
    · omega


theorem cubicLoadSigmaConeBCD610_specialize_delta
    {delta : k} {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeBCD610 A B C D E)
    (hband : (delta = 0 ∨
      7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 30 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 28 * E.natDegree)) :
    (delta = 0 ∨ 7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree) := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hCne, hDne, heq1, heq2, hEcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsE : 4 * E.natDegree + 1 ≤ 3 * A.natDegree + 6 * B.natDegree ∨ E.natDegree = 0 := by
    rcases hEcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  rcases hband with h | h | h | h | h
  · exact Or.inl h
  · -- B-summand of the four-way OR
    exact Or.inr h
  · -- C-summand of the four-way OR
    omega
  · -- D-summand of the four-way OR
    omega
  · -- E-summand of the four-way OR
    rcases hsE with hsE | hE0
    · omega
    · omega


theorem cubicLoadSigmaConeBCD610_specialize_zeta
    {zeta : k} {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeBCD610 A B C D E)
    (hband : (zeta = 0 ∨
      9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree ∨
      12 * A.natDegree ≤ 6 * A.natDegree + 6 * C.natDegree ∨
      10 * A.natDegree ≤ 6 * A.natDegree + 4 * D.natDegree ∨
      12 * A.natDegree ≤ 6 * A.natDegree + 4 * E.natDegree)) :
    (zeta = 0 ∨ 9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree) := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hCne, hDne, heq1, heq2, hEcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsE : 4 * E.natDegree + 1 ≤ 3 * A.natDegree + 6 * B.natDegree ∨ E.natDegree = 0 := by
    rcases hEcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  rcases hband with h | h | h | h | h
  · exact Or.inl h
  · -- B-summand of the four-way OR
    exact Or.inr h
  · -- C-summand of the four-way OR
    omega
  · -- D-summand of the four-way OR
    omega
  · -- E-summand of the four-way OR
    rcases hsE with hsE | hE0
    · omega
    · omega


theorem cubicLoadSigmaConeBCD610_specialize_theta
    {theta : k} {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeBCD610 A B C D E)
    (hband : (theta = 0 ∨
      7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 54 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 28 * E.natDegree)) :
    (theta = 0 ∨ 7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree) := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hCne, hDne, heq1, heq2, hEcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsE : 4 * E.natDegree + 1 ≤ 3 * A.natDegree + 6 * B.natDegree ∨ E.natDegree = 0 := by
    rcases hEcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  rcases hband with h | h | h | h | h
  · exact Or.inl h
  · -- B-summand of the four-way OR
    exact Or.inr h
  · -- C-summand of the four-way OR
    omega
  · -- D-summand of the four-way OR
    omega
  · -- E-summand of the four-way OR
    rcases hsE with hsE | hE0
    · omega
    · omega


/-- Specialise residual-6 four-way bands onto cone `BDE`. -/

theorem cubicLoadSigmaConeBDE610_specialize_beta
    {beta : k} {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeBDE610 A B C D E)
    (hband : (beta = 0 ∨
      7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 18 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 28 * E.natDegree)) :
    (beta = 0 ∨ 7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree) := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hDne, hEne, heq1, heq2, hCcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsC : 2 * C.natDegree + 1 ≤ A.natDegree + 2 * B.natDegree ∨ C.natDegree = 0 := by
    rcases hCcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  rcases hband with h | h | h | h | h
  · exact Or.inl h
  · -- B-summand of the four-way OR
    exact Or.inr h
  · -- C-summand of the four-way OR
    rcases hsC with hsC | hC0
    · omega
    · omega
  · -- D-summand of the four-way OR
    omega
  · -- E-summand of the four-way OR
    omega


theorem cubicLoadSigmaConeBDE610_specialize_delta
    {delta : k} {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeBDE610 A B C D E)
    (hband : (delta = 0 ∨
      7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 30 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 28 * E.natDegree)) :
    (delta = 0 ∨ 7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree) := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hDne, hEne, heq1, heq2, hCcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsC : 2 * C.natDegree + 1 ≤ A.natDegree + 2 * B.natDegree ∨ C.natDegree = 0 := by
    rcases hCcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  rcases hband with h | h | h | h | h
  · exact Or.inl h
  · -- B-summand of the four-way OR
    exact Or.inr h
  · -- C-summand of the four-way OR
    rcases hsC with hsC | hC0
    · omega
    · omega
  · -- D-summand of the four-way OR
    omega
  · -- E-summand of the four-way OR
    omega


theorem cubicLoadSigmaConeBDE610_specialize_zeta
    {zeta : k} {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeBDE610 A B C D E)
    (hband : (zeta = 0 ∨
      9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree ∨
      12 * A.natDegree ≤ 6 * A.natDegree + 6 * C.natDegree ∨
      10 * A.natDegree ≤ 6 * A.natDegree + 4 * D.natDegree ∨
      12 * A.natDegree ≤ 6 * A.natDegree + 4 * E.natDegree)) :
    (zeta = 0 ∨ 9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree) := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hDne, hEne, heq1, heq2, hCcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsC : 2 * C.natDegree + 1 ≤ A.natDegree + 2 * B.natDegree ∨ C.natDegree = 0 := by
    rcases hCcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  rcases hband with h | h | h | h | h
  · exact Or.inl h
  · -- B-summand of the four-way OR
    exact Or.inr h
  · -- C-summand of the four-way OR
    rcases hsC with hsC | hC0
    · omega
    · omega
  · -- D-summand of the four-way OR
    omega
  · -- E-summand of the four-way OR
    omega


theorem cubicLoadSigmaConeBDE610_specialize_theta
    {theta : k} {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeBDE610 A B C D E)
    (hband : (theta = 0 ∨
      7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 54 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 28 * E.natDegree)) :
    (theta = 0 ∨ 7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree) := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hDne, hEne, heq1, heq2, hCcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsC : 2 * C.natDegree + 1 ≤ A.natDegree + 2 * B.natDegree ∨ C.natDegree = 0 := by
    rcases hCcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  rcases hband with h | h | h | h | h
  · exact Or.inl h
  · -- B-summand of the four-way OR
    exact Or.inr h
  · -- C-summand of the four-way OR
    rcases hsC with hsC | hC0
    · omega
    · omega
  · -- D-summand of the four-way OR
    omega
  · -- E-summand of the four-way OR
    omega


/-- Specialise residual-6 four-way bands onto cone `CDE`. -/

theorem cubicLoadSigmaConeCDE610_specialize_beta
    {beta : k} {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeCDE610 A B C D E)
    (hband : (beta = 0 ∨
      7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 18 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 28 * E.natDegree)) :
    (beta = 0 ∨ 7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 42 * C.natDegree) := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hCne, hDne, hEne, heq1, heq2, hBcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsB : A.natDegree + 2 * B.natDegree + 1 ≤ 2 * C.natDegree ∨ B.natDegree = 0 := by
    rcases hBcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  rcases hband with h | h | h | h | h
  · exact Or.inl h
  · -- B-summand of the four-way OR
    rcases hsB with hsB | hB0
    · omega
    · omega
  · -- C-summand of the four-way OR
    exact Or.inr h
  · -- D-summand of the four-way OR
    omega
  · -- E-summand of the four-way OR
    omega


theorem cubicLoadSigmaConeCDE610_specialize_delta
    {delta : k} {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeCDE610 A B C D E)
    (hband : (delta = 0 ∨
      7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 30 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 28 * E.natDegree)) :
    (delta = 0 ∨ 7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 42 * C.natDegree) := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hCne, hDne, hEne, heq1, heq2, hBcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsB : A.natDegree + 2 * B.natDegree + 1 ≤ 2 * C.natDegree ∨ B.natDegree = 0 := by
    rcases hBcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  rcases hband with h | h | h | h | h
  · exact Or.inl h
  · -- B-summand of the four-way OR
    rcases hsB with hsB | hB0
    · omega
    · omega
  · -- C-summand of the four-way OR
    exact Or.inr h
  · -- D-summand of the four-way OR
    omega
  · -- E-summand of the four-way OR
    omega


theorem cubicLoadSigmaConeCDE610_specialize_zeta
    {zeta : k} {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeCDE610 A B C D E)
    (hband : (zeta = 0 ∨
      9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree ∨
      12 * A.natDegree ≤ 6 * A.natDegree + 6 * C.natDegree ∨
      10 * A.natDegree ≤ 6 * A.natDegree + 4 * D.natDegree ∨
      12 * A.natDegree ≤ 6 * A.natDegree + 4 * E.natDegree)) :
    (zeta = 0 ∨ 12 * A.natDegree ≤ 6 * A.natDegree + 6 * C.natDegree) := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hCne, hDne, hEne, heq1, heq2, hBcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsB : A.natDegree + 2 * B.natDegree + 1 ≤ 2 * C.natDegree ∨ B.natDegree = 0 := by
    rcases hBcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  rcases hband with h | h | h | h | h
  · exact Or.inl h
  · -- B-summand of the four-way OR
    rcases hsB with hsB | hB0
    · omega
    · omega
  · -- C-summand of the four-way OR
    exact Or.inr h
  · -- D-summand of the four-way OR
    omega
  · -- E-summand of the four-way OR
    omega


theorem cubicLoadSigmaConeCDE610_specialize_theta
    {theta : k} {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeCDE610 A B C D E)
    (hband : (theta = 0 ∨
      7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 54 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 28 * E.natDegree)) :
    (theta = 0 ∨ 7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 42 * C.natDegree) := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hCne, hDne, hEne, heq1, heq2, hBcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsB : A.natDegree + 2 * B.natDegree + 1 ≤ 2 * C.natDegree ∨ B.natDegree = 0 := by
    rcases hBcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  rcases hband with h | h | h | h | h
  · exact Or.inl h
  · -- B-summand of the four-way OR
    rcases hsB with hsB | hB0
    · omega
    · omega
  · -- C-summand of the four-way OR
    exact Or.inr h
  · -- D-summand of the four-way OR
    omega
  · -- E-summand of the four-way OR
    omega


end CubicLoadConeBandSpecialize610


/-! ## Single-monomial rest bounds and kills -/


section CubicLoadSigmaSingleMonomial610


variable {k : Type*} [Field k] [CharZero k]


/- σ-cone B -/


set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaCubicNoSigmaB610_natDegree_lt_of_loadCone
    (alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeB610 A B C D E)
    (hb : beta  = 0 ∨ 7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree)
    (hd : delta = 0 ∨ 7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree)
    (hz : zeta  = 0 ∨ 9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree)
    (ht : theta = 0 ∨ 7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree) :
    (degreeZeroKappaCubicNoSigmaB610 0 alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hCcmp, hDcmp, hEcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsAB : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAB
  have hsAC : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hAC
  have hsAD : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hAD
  have hsAE : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAE
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hsC : 2 * C.natDegree + 1 ≤ A.natDegree + 2 * B.natDegree := by
    rcases hCcmp with h0 | hlt
    · have : C.natDegree = 0 := by simp [h0]
      omega
    · exact Nat.succ_le_of_lt hlt
  have hsD : 4 * D.natDegree + 1 ≤ A.natDegree + 6 * B.natDegree := by
    rcases hDcmp with h0 | hlt
    · have : D.natDegree = 0 := by simp [h0]
      omega
    · exact Nat.succ_le_of_lt hlt
  have hsE : 4 * E.natDegree + 1 ≤ 3 * A.natDegree + 6 * B.natDegree := by
    rcases hEcmp with h0 | hlt
    · have : E.natDegree = 0 := by simp [h0]
      omega
    · exact Nat.succ_le_of_lt hlt
  rcases hb with rfl | hb <;> rcases hd with rfl | hd <;>
    rcases hz with rfl | hz <;> rcases ht with rfl | ht <;>
      (simp only [degreeZeroKappaCubicNoSigmaB610, hpow2, hpow3, hpow4, hpow5,
                  zero_mul, mul_zero, zero_smul, smul_zero,
                  add_zero, zero_add, zero_pow, Nat.succ_ne_zero,
                  sub_zero, neg_zero, natDegree_zero];
       compute_degree; omega)


set_option maxHeartbeats 64000000 in
theorem cubicLoadSigmaCone_B_impossible {j t : k}
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeB610 A B C D E)
    (hl : l = 0)
    (hb4 : (beta = 0 ∨
      7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 18 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 28 * E.natDegree))
    (hd4 : (delta = 0 ∨
      7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 30 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 28 * E.natDegree))
    (hz4 : (zeta = 0 ∨
      9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree ∨
      12 * A.natDegree ≤ 6 * A.natDegree + 6 * C.natDegree ∨
      10 * A.natDegree ≤ 6 * A.natDegree + 4 * D.natDegree ∨
      12 * A.natDegree ≤ 6 * A.natDegree + 4 * E.natDegree))
    (ht4 : (theta = 0 ∨
      7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 54 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 28 * E.natDegree))
    (hdeg : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree = 0) :
    False := by
  subst hl
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, _⟩
    omega
  have hBne : B ≠ 0 := by
    rcases hcone with ⟨_, hBne, hCcmp, hDcmp, hEcmp⟩
    exact hBne
  have hb : beta = 0 ∨ 7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree :=
    cubicLoadSigmaConeB610_specialize_beta hcone hb4
  have hd : delta = 0 ∨ 7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree :=
    cubicLoadSigmaConeB610_specialize_delta hcone hd4
  have hz : zeta = 0 ∨ 9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree :=
    cubicLoadSigmaConeB610_specialize_zeta hcone hz4
  have ht : theta = 0 ∨ 7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree :=
    cubicLoadSigmaConeB610_specialize_theta hcone ht4
  have hc : (5 / 243 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (kappaCubicSigmaFaceB610 A B C D E).natDegree = A.natDegree + 3 * B.natDegree := by
    simp only [kappaCubicSigmaFaceB610]
    rw [natDegree_smul _ hc, natDegree_mul hAne (pow_ne_zero 3 hBne), natDegree_pow]
  have hrest := degreeZeroKappaCubicNoSigmaB610_natDegree_lt_of_loadCone alpha beta delta epsilon zeta eta theta
      A B C D E hcone hb hd hz ht
  rw [degreeZeroKappaCubic610_eq_sigmaB_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  omega



/- σ-cone C -/


set_option maxHeartbeats 64000000 in
theorem degreeZeroLambdaCubicNoSigmaC610_natDegree_lt_of_loadCone
    (alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeC610 A B C D E)
    (hb : beta  = 0 ∨ 7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 42 * C.natDegree)
    (hd : delta = 0 ∨ 7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 42 * C.natDegree)
    (hz : zeta  = 0 ∨ 12 * A.natDegree ≤ 6 * A.natDegree + 6 * C.natDegree)
    (ht : theta = 0 ∨ 7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 42 * C.natDegree)
    (hpos : 0 < 3 * C.natDegree) :
    (degreeZeroLambdaCubicNoSigmaC610 0 alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      3 * C.natDegree := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hCne, hBcmp, hDcmp, hEcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsAB : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAB
  have hsAC : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hAC
  have hsAD : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hAD
  have hsAE : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAE
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hsFace : 0 + 1 ≤ 3 * C.natDegree := Nat.succ_le_of_lt hpos

  rcases hb with rfl | hb <;> rcases hd with rfl | hd <;>
    rcases hz with rfl | hz <;> rcases ht with rfl | ht <;>
    rcases hBcmp with rfl | hBcmp <;> rcases hDcmp with rfl | hDcmp <;> rcases hEcmp with rfl | hEcmp <;>
      (simp only [degreeZeroLambdaCubicNoSigmaC610, hpow2, hpow3, hpow4, hpow5,
                  zero_mul, mul_zero, zero_smul, smul_zero,
                  add_zero, zero_add, zero_pow, Nat.succ_ne_zero,
                  sub_zero, neg_zero, natDegree_zero];
       compute_degree; omega)


set_option maxHeartbeats 64000000 in
theorem cubicLoadSigmaCone_C_impossible {j t : k}
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeC610 A B C D E)
    (hl : l = 0)
    (hb4 : (beta = 0 ∨
      7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 18 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 28 * E.natDegree))
    (hd4 : (delta = 0 ∨
      7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 30 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 28 * E.natDegree))
    (hz4 : (zeta = 0 ∨
      9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree ∨
      12 * A.natDegree ≤ 6 * A.natDegree + 6 * C.natDegree ∨
      10 * A.natDegree ≤ 6 * A.natDegree + 4 * D.natDegree ∨
      12 * A.natDegree ≤ 6 * A.natDegree + 4 * E.natDegree))
    (ht4 : (theta = 0 ∨
      7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 54 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 28 * E.natDegree))
    (hdeg : (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree = 0)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta eta
          theta A B C D E) =
        Polynomial.C (j / t)) :
    False := by
  subst hl
  have hCne : C ≠ 0 := by
    rcases hcone with ⟨_, hCne, hBcmp, hDcmp, hEcmp⟩
    exact hCne
  have hb : beta = 0 ∨ 7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 42 * C.natDegree :=
    cubicLoadSigmaConeC610_specialize_beta hcone hb4
  have hd : delta = 0 ∨ 7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 42 * C.natDegree :=
    cubicLoadSigmaConeC610_specialize_delta hcone hd4
  have hz : zeta = 0 ∨ 12 * A.natDegree ≤ 6 * A.natDegree + 6 * C.natDegree :=
    cubicLoadSigmaConeC610_specialize_zeta hcone hz4
  have ht : theta = 0 ∨ 7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 42 * C.natDegree :=
    cubicLoadSigmaConeC610_specialize_theta hcone ht4
  by_cases hpos : 0 < 3 * C.natDegree
  ·
      have hc : (-(5 / 81 : k)) ≠ 0 := neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
      have hlead : (lambdaCubicSigmaFaceC610 A B C D E).natDegree = 3 * C.natDegree := by
        simp only [lambdaCubicSigmaFaceC610]
        rw [natDegree_smul _ hc, natDegree_pow]
      have hrest := degreeZeroLambdaCubicNoSigmaC610_natDegree_lt_of_loadCone alpha beta delta epsilon zeta eta theta
          A B C D E hcone hb hd hz ht hpos
      rw [degreeZeroLambdaCubic610_eq_sigmaC_add_rest,
        natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
      omega
  ·
    have hface0 : 3 * C.natDegree = 0 := by omega
    rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
      hCne, hBcmp, hDcmp, hEcmp⟩
    have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
    have hCdeg0 : C.natDegree = 0 := by omega
    have hB0 : B = 0 := by
      rcases hBcmp with hB0 | hBlt
      · exact hB0
      · omega
    have hD0 : D = 0 := by
      rcases hDcmp with hD0 | hDlt
      · exact hD0
      · omega
    rw [hCdeg0] at hb hd hz ht
    have hbeta0 : beta = 0 := by
      rcases hb with h | h
      · exact h
      · omega
    have hdelta0 : delta = 0 := by
      rcases hd with h | h
      · exact h
      · omega
    have hzeta0 : zeta = 0 := by
      rcases hz with h | h
      · exact h
      · omega
    have htheta0 : theta = 0 := by
      rcases ht with h | h
      · exact h
      · omega
    exact cubicLoadCompete_BD_zero_impossible (j := j) (t := t)
      0 alpha beta delta epsilon zeta eta theta A B C D E
      hB0 hD0 rfl hbeta0 hdelta0 hzeta0 htheta0 hjdiv hder



/- σ-cone D -/


set_option maxHeartbeats 64000000 in
theorem degreeZeroLambdaCubicNoSigmaD610_natDegree_lt_of_loadCone
    (alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeD610 A B C D E)
    (hb : beta  = 0 ∨ 7 * (10 * A.natDegree) ≤ 18 * A.natDegree + 28 * D.natDegree)
    (hd : delta = 0 ∨ 7 * (10 * A.natDegree) ≤ 30 * A.natDegree + 28 * D.natDegree)
    (hz : zeta  = 0 ∨ 10 * A.natDegree ≤ 6 * A.natDegree + 4 * D.natDegree)
    (ht : theta = 0 ∨ 7 * (10 * A.natDegree) ≤ 54 * A.natDegree + 28 * D.natDegree) :
    (degreeZeroLambdaCubicNoSigmaD610 0 alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      A.natDegree + 2 * D.natDegree := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hDne, hBcmp, hCcmp, hEcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsAB : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAB
  have hsAC : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hAC
  have hsAD : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hAD
  have hsAE : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAE
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)

  rcases hb with rfl | hb <;> rcases hd with rfl | hd <;>
    rcases hz with rfl | hz <;> rcases ht with rfl | ht <;>
    rcases hBcmp with rfl | hBcmp <;> rcases hCcmp with rfl | hCcmp <;> rcases hEcmp with rfl | hEcmp <;>
      (simp only [degreeZeroLambdaCubicNoSigmaD610, hpow2, hpow3, hpow4, hpow5,
                  zero_mul, mul_zero, zero_smul, smul_zero,
                  add_zero, zero_add, zero_pow, Nat.succ_ne_zero,
                  sub_zero, neg_zero, natDegree_zero];
       compute_degree; omega)


set_option maxHeartbeats 64000000 in
theorem cubicLoadSigmaCone_D_impossible {j t : k}
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeD610 A B C D E)
    (hl : l = 0)
    (hb4 : (beta = 0 ∨
      7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 18 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 28 * E.natDegree))
    (hd4 : (delta = 0 ∨
      7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 30 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 28 * E.natDegree))
    (hz4 : (zeta = 0 ∨
      9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree ∨
      12 * A.natDegree ≤ 6 * A.natDegree + 6 * C.natDegree ∨
      10 * A.natDegree ≤ 6 * A.natDegree + 4 * D.natDegree ∨
      12 * A.natDegree ≤ 6 * A.natDegree + 4 * E.natDegree))
    (ht4 : (theta = 0 ∨
      7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 54 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 28 * E.natDegree))
    (hdeg : (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree = 0) :
    False := by
  subst hl
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, _⟩
    omega
  have hDne : D ≠ 0 := by
    rcases hcone with ⟨_, hDne, hBcmp, hCcmp, hEcmp⟩
    exact hDne
  have hb : beta = 0 ∨ 7 * (10 * A.natDegree) ≤ 18 * A.natDegree + 28 * D.natDegree :=
    cubicLoadSigmaConeD610_specialize_beta hcone hb4
  have hd : delta = 0 ∨ 7 * (10 * A.natDegree) ≤ 30 * A.natDegree + 28 * D.natDegree :=
    cubicLoadSigmaConeD610_specialize_delta hcone hd4
  have hz : zeta = 0 ∨ 10 * A.natDegree ≤ 6 * A.natDegree + 4 * D.natDegree :=
    cubicLoadSigmaConeD610_specialize_zeta hcone hz4
  have ht : theta = 0 ∨ 7 * (10 * A.natDegree) ≤ 54 * A.natDegree + 28 * D.natDegree :=
    cubicLoadSigmaConeD610_specialize_theta hcone ht4
  have hc : (-(5 / 27 : k)) ≠ 0 := neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead : (lambdaCubicSigmaFaceD610 A B C D E).natDegree = A.natDegree + 2 * D.natDegree := by
    simp only [lambdaCubicSigmaFaceD610]
    rw [natDegree_smul _ hc, natDegree_mul hAne (pow_ne_zero 2 hDne), natDegree_pow]
  have hrest := degreeZeroLambdaCubicNoSigmaD610_natDegree_lt_of_loadCone alpha beta delta epsilon zeta eta theta
      A B C D E hcone hb hd hz ht
  rw [degreeZeroLambdaCubic610_eq_sigmaD_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  omega



/- σ-cone E -/


set_option maxHeartbeats 64000000 in
theorem degreeZeroLambdaCubicNoSigmaE610_natDegree_lt_of_loadCone
    (alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeE610 A B C D E)
    (hb : beta  = 0 ∨ 7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 28 * E.natDegree)
    (hd : delta = 0 ∨ 7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 28 * E.natDegree)
    (hz : zeta  = 0 ∨ 12 * A.natDegree ≤ 6 * A.natDegree + 4 * E.natDegree)
    (ht : theta = 0 ∨ 7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 28 * E.natDegree)
    (hpos : 0 < 2 * E.natDegree) :
    (degreeZeroLambdaCubicNoSigmaE610 0 alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      2 * E.natDegree := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hEne, hBcmp, hCcmp, hDcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsAB : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAB
  have hsAC : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hAC
  have hsAD : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hAD
  have hsAE : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAE
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hsFace : 0 + 1 ≤ 2 * E.natDegree := Nat.succ_le_of_lt hpos

  rcases hb with rfl | hb <;> rcases hd with rfl | hd <;>
    rcases hz with rfl | hz <;> rcases ht with rfl | ht <;>
    rcases hBcmp with rfl | hBcmp <;> rcases hCcmp with rfl | hCcmp <;> rcases hDcmp with rfl | hDcmp <;>
      (simp only [degreeZeroLambdaCubicNoSigmaE610, hpow2, hpow3, hpow4, hpow5,
                  zero_mul, mul_zero, zero_smul, smul_zero,
                  add_zero, zero_add, zero_pow, Nat.succ_ne_zero,
                  sub_zero, neg_zero, natDegree_zero];
       compute_degree; omega)


set_option maxHeartbeats 64000000 in
theorem cubicLoadSigmaCone_E_impossible {j t : k}
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeE610 A B C D E)
    (hl : l = 0)
    (hb4 : (beta = 0 ∨
      7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 18 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 28 * E.natDegree))
    (hd4 : (delta = 0 ∨
      7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 30 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 28 * E.natDegree))
    (hz4 : (zeta = 0 ∨
      9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree ∨
      12 * A.natDegree ≤ 6 * A.natDegree + 6 * C.natDegree ∨
      10 * A.natDegree ≤ 6 * A.natDegree + 4 * D.natDegree ∨
      12 * A.natDegree ≤ 6 * A.natDegree + 4 * E.natDegree))
    (ht4 : (theta = 0 ∨
      7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 54 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 28 * E.natDegree))
    (hdeg : (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree = 0)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta eta
          theta A B C D E) =
        Polynomial.C (j / t)) :
    False := by
  subst hl
  have hEne : E ≠ 0 := by
    rcases hcone with ⟨_, hEne, hBcmp, hCcmp, hDcmp⟩
    exact hEne
  have hb : beta = 0 ∨ 7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 28 * E.natDegree :=
    cubicLoadSigmaConeE610_specialize_beta hcone hb4
  have hd : delta = 0 ∨ 7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 28 * E.natDegree :=
    cubicLoadSigmaConeE610_specialize_delta hcone hd4
  have hz : zeta = 0 ∨ 12 * A.natDegree ≤ 6 * A.natDegree + 4 * E.natDegree :=
    cubicLoadSigmaConeE610_specialize_zeta hcone hz4
  have ht : theta = 0 ∨ 7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 28 * E.natDegree :=
    cubicLoadSigmaConeE610_specialize_theta hcone ht4
  by_cases hpos : 0 < 2 * E.natDegree
  ·
      have hc : (5 / 9 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
      have hlead : (lambdaCubicSigmaFaceE610 A B C D E).natDegree = 2 * E.natDegree := by
        simp only [lambdaCubicSigmaFaceE610]
        rw [natDegree_smul _ hc, natDegree_pow]
      have hrest := degreeZeroLambdaCubicNoSigmaE610_natDegree_lt_of_loadCone alpha beta delta epsilon zeta eta theta
          A B C D E hcone hb hd hz ht hpos
      rw [degreeZeroLambdaCubic610_eq_sigmaE_add_rest,
        natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
      omega
  ·
    have hface0 : 2 * E.natDegree = 0 := by omega
    rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
      hEne, hBcmp, hCcmp, hDcmp⟩
    have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
    have hEdeg0 : E.natDegree = 0 := by omega
    have hB0 : B = 0 := by
      rcases hBcmp with hB0 | hBlt
      · exact hB0
      · omega
    have hD0 : D = 0 := by
      rcases hDcmp with hD0 | hDlt
      · exact hD0
      · omega
    rw [hEdeg0] at hb hd hz ht
    have hbeta0 : beta = 0 := by
      rcases hb with h | h
      · exact h
      · omega
    have hdelta0 : delta = 0 := by
      rcases hd with h | h
      · exact h
      · omega
    have hzeta0 : zeta = 0 := by
      rcases hz with h | h
      · exact h
      · omega
    have htheta0 : theta = 0 := by
      rcases ht with h | h
      · exact h
      · omega
    exact cubicLoadCompete_BD_zero_impossible (j := j) (t := t)
      0 alpha beta delta epsilon zeta eta theta A B C D E
      hB0 hD0 rfl hbeta0 hdelta0 hzeta0 htheta0 hjdiv hder



/- σ-cone BD -/


set_option maxHeartbeats 64000000 in
theorem degreeZeroLambdaCubicNoSigmaBD610_natDegree_lt_of_loadCone
    (alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeBD610 A B C D E)
    (hb : beta  = 0 ∨ 7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree)
    (hd : delta = 0 ∨ 7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree)
    (hz : zeta  = 0 ∨ 9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree)
    (ht : theta = 0 ∨ 7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree) :
    (degreeZeroLambdaCubicNoSigmaD610 0 alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      A.natDegree + 2 * D.natDegree := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hDne, heq, hCcmp, hEcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsAB : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAB
  have hsAC : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hAC
  have hsAD : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hAD
  have hsAE : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAE
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have htie : A.natDegree + 6 * B.natDegree = 4 * D.natDegree := by omega
  have hsC : 2 * C.natDegree + 1 ≤ A.natDegree + 2 * B.natDegree := by
    rcases hCcmp with h0 | hlt
    · have : C.natDegree = 0 := by simp [h0]
      omega
    · exact Nat.succ_le_of_lt hlt
  have hsE : 4 * E.natDegree + 1 ≤ 3 * A.natDegree + 6 * B.natDegree := by
    rcases hEcmp with h0 | hlt
    · have : E.natDegree = 0 := by simp [h0]
      omega
    · exact Nat.succ_le_of_lt hlt
  rcases hb with rfl | hb <;> rcases hd with rfl | hd <;>
    rcases hz with rfl | hz <;> rcases ht with rfl | ht <;>
      (simp only [degreeZeroLambdaCubicNoSigmaD610, hpow2, hpow3, hpow4, hpow5,
                  zero_mul, mul_zero, zero_smul, smul_zero,
                  add_zero, zero_add, zero_pow, Nat.succ_ne_zero,
                  sub_zero, neg_zero, natDegree_zero];
       compute_degree; omega)


set_option maxHeartbeats 64000000 in
theorem cubicLoadSigmaCone_BD_impossible {j t : k}
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeBD610 A B C D E)
    (hl : l = 0)
    (hb4 : (beta = 0 ∨
      7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 18 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 28 * E.natDegree))
    (hd4 : (delta = 0 ∨
      7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 30 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 28 * E.natDegree))
    (hz4 : (zeta = 0 ∨
      9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree ∨
      12 * A.natDegree ≤ 6 * A.natDegree + 6 * C.natDegree ∨
      10 * A.natDegree ≤ 6 * A.natDegree + 4 * D.natDegree ∨
      12 * A.natDegree ≤ 6 * A.natDegree + 4 * E.natDegree))
    (ht4 : (theta = 0 ∨
      7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 54 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 28 * E.natDegree))
    (hdeg : (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree = 0) :
    False := by
  subst hl
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, _⟩
    omega
  have hDne : D ≠ 0 := by
    rcases hcone with ⟨_, hBne, hDne, heq, hCcmp, hEcmp⟩
    exact hDne
  have hb : beta = 0 ∨ 7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree :=
    cubicLoadSigmaConeBD610_specialize_beta hcone hb4
  have hd : delta = 0 ∨ 7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree :=
    cubicLoadSigmaConeBD610_specialize_delta hcone hd4
  have hz : zeta = 0 ∨ 9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree :=
    cubicLoadSigmaConeBD610_specialize_zeta hcone hz4
  have ht : theta = 0 ∨ 7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree :=
    cubicLoadSigmaConeBD610_specialize_theta hcone ht4
  have hc : (-(5 / 27 : k)) ≠ 0 := neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead : (lambdaCubicSigmaFaceD610 A B C D E).natDegree = A.natDegree + 2 * D.natDegree := by
    simp only [lambdaCubicSigmaFaceD610]
    rw [natDegree_smul _ hc, natDegree_mul hAne (pow_ne_zero 2 hDne), natDegree_pow]
  have hrest := degreeZeroLambdaCubicNoSigmaBD610_natDegree_lt_of_loadCone alpha beta delta epsilon zeta eta theta
      A B C D E hcone hb hd hz ht
  rw [degreeZeroLambdaCubic610_eq_sigmaD_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  omega



/- σ-cone BE -/


set_option maxHeartbeats 64000000 in
theorem degreeZeroLambdaCubicNoSigmaBE610_natDegree_lt_of_loadCone
    (alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeBE610 A B C D E)
    (hb : beta  = 0 ∨ 7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree)
    (hd : delta = 0 ∨ 7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree)
    (hz : zeta  = 0 ∨ 9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree)
    (ht : theta = 0 ∨ 7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree) :
    (degreeZeroLambdaCubicNoSigmaE610 0 alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      2 * E.natDegree := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hEne, heq, hCcmp, hDcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsAB : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAB
  have hsAC : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hAC
  have hsAD : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hAD
  have hsAE : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAE
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have htie : 3 * A.natDegree + 6 * B.natDegree = 4 * E.natDegree := by omega
  have hsC : 2 * C.natDegree + 1 ≤ A.natDegree + 2 * B.natDegree := by
    rcases hCcmp with h0 | hlt
    · have : C.natDegree = 0 := by simp [h0]
      omega
    · exact Nat.succ_le_of_lt hlt
  have hsD : 4 * D.natDegree + 1 ≤ A.natDegree + 6 * B.natDegree := by
    rcases hDcmp with h0 | hlt
    · have : D.natDegree = 0 := by simp [h0]
      omega
    · exact Nat.succ_le_of_lt hlt
  rcases hb with rfl | hb <;> rcases hd with rfl | hd <;>
    rcases hz with rfl | hz <;> rcases ht with rfl | ht <;>
      (simp only [degreeZeroLambdaCubicNoSigmaE610, hpow2, hpow3, hpow4, hpow5,
                  zero_mul, mul_zero, zero_smul, smul_zero,
                  add_zero, zero_add, zero_pow, Nat.succ_ne_zero,
                  sub_zero, neg_zero, natDegree_zero];
       compute_degree; omega)


set_option maxHeartbeats 64000000 in
theorem cubicLoadSigmaCone_BE_impossible {j t : k}
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeBE610 A B C D E)
    (hl : l = 0)
    (hb4 : (beta = 0 ∨
      7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 18 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 28 * E.natDegree))
    (hd4 : (delta = 0 ∨
      7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 30 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 28 * E.natDegree))
    (hz4 : (zeta = 0 ∨
      9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree ∨
      12 * A.natDegree ≤ 6 * A.natDegree + 6 * C.natDegree ∨
      10 * A.natDegree ≤ 6 * A.natDegree + 4 * D.natDegree ∨
      12 * A.natDegree ≤ 6 * A.natDegree + 4 * E.natDegree))
    (ht4 : (theta = 0 ∨
      7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 54 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 28 * E.natDegree))
    (hdeg : (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree = 0) :
    False := by
  subst hl
  have hEne : E ≠ 0 := by
    rcases hcone with ⟨_, hBne, hEne, heq, hCcmp, hDcmp⟩
    exact hEne
  have hb : beta = 0 ∨ 7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree :=
    cubicLoadSigmaConeBE610_specialize_beta hcone hb4
  have hd : delta = 0 ∨ 7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree :=
    cubicLoadSigmaConeBE610_specialize_delta hcone hd4
  have hz : zeta = 0 ∨ 9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree :=
    cubicLoadSigmaConeBE610_specialize_zeta hcone hz4
  have ht : theta = 0 ∨ 7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree :=
    cubicLoadSigmaConeBE610_specialize_theta hcone ht4
  have hc : (5 / 9 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (lambdaCubicSigmaFaceE610 A B C D E).natDegree = 2 * E.natDegree := by
    simp only [lambdaCubicSigmaFaceE610]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest := degreeZeroLambdaCubicNoSigmaBE610_natDegree_lt_of_loadCone alpha beta delta epsilon zeta eta theta
      A B C D E hcone hb hd hz ht
  rw [degreeZeroLambdaCubic610_eq_sigmaE_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  omega



/- σ-cone CE -/


set_option maxHeartbeats 64000000 in
theorem degreeZeroOmicronCubicNoSigmaCE610_natDegree_lt_of_loadCone
    (alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeCE610 A B C D E)
    (hb : beta  = 0 ∨ 7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 42 * C.natDegree)
    (hd : delta = 0 ∨ 7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 42 * C.natDegree)
    (hz : zeta  = 0 ∨ 12 * A.natDegree ≤ 6 * A.natDegree + 6 * C.natDegree)
    (ht : theta = 0 ∨ 7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 42 * C.natDegree)
    (hpos : 0 < 2 * C.natDegree + E.natDegree) :
    (degreeZeroOmicronCubicNoSigmaCE610 0 alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      2 * C.natDegree + E.natDegree := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hCne, hEne, heq, hBcmp, hDcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsAB : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAB
  have hsAC : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hAC
  have hsAD : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hAD
  have hsAE : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAE
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hsFace : 0 + 1 ≤ 2 * C.natDegree + E.natDegree := Nat.succ_le_of_lt hpos
  have htie : 3 * C.natDegree = 2 * E.natDegree := by omega

  rcases hb with rfl | hb <;> rcases hd with rfl | hd <;>
    rcases hz with rfl | hz <;> rcases ht with rfl | ht <;>
    rcases hBcmp with rfl | hBcmp <;> rcases hDcmp with rfl | hDcmp <;>
      (simp only [degreeZeroOmicronCubicNoSigmaCE610, hpow2, hpow3, hpow4, hpow5,
                  zero_mul, mul_zero, zero_smul, smul_zero,
                  add_zero, zero_add, zero_pow, Nat.succ_ne_zero,
                  sub_zero, neg_zero, natDegree_zero];
       compute_degree; omega)


set_option maxHeartbeats 64000000 in
theorem cubicLoadSigmaCone_CE_impossible {j t : k}
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeCE610 A B C D E)
    (hl : l = 0)
    (hb4 : (beta = 0 ∨
      7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 18 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 28 * E.natDegree))
    (hd4 : (delta = 0 ∨
      7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 30 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 28 * E.natDegree))
    (hz4 : (zeta = 0 ∨
      9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree ∨
      12 * A.natDegree ≤ 6 * A.natDegree + 6 * C.natDegree ∨
      10 * A.natDegree ≤ 6 * A.natDegree + 4 * D.natDegree ∨
      12 * A.natDegree ≤ 6 * A.natDegree + 4 * E.natDegree))
    (ht4 : (theta = 0 ∨
      7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 54 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 28 * E.natDegree))
    (hdeg : (degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree = 0)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta eta
          theta A B C D E) =
        Polynomial.C (j / t)) :
    False := by
  subst hl
  have hCne : C ≠ 0 := by
    rcases hcone with ⟨_, hCne, hEne, heq, hBcmp, hDcmp⟩
    exact hCne
  have hEne : E ≠ 0 := by
    rcases hcone with ⟨_, hCne, hEne, heq, hBcmp, hDcmp⟩
    exact hEne
  have hb : beta = 0 ∨ 7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 42 * C.natDegree :=
    cubicLoadSigmaConeCE610_specialize_beta hcone hb4
  have hd : delta = 0 ∨ 7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 42 * C.natDegree :=
    cubicLoadSigmaConeCE610_specialize_delta hcone hd4
  have hz : zeta = 0 ∨ 12 * A.natDegree ≤ 6 * A.natDegree + 6 * C.natDegree :=
    cubicLoadSigmaConeCE610_specialize_zeta hcone hz4
  have ht : theta = 0 ∨ 7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 42 * C.natDegree :=
    cubicLoadSigmaConeCE610_specialize_theta hcone ht4
  by_cases hpos : 0 < 2 * C.natDegree + E.natDegree
  ·
      have hc : (-(5 / 27 : k)) ≠ 0 := neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
      have hlead : (omicronCubicSigmaFaceCE610 A B C D E).natDegree = 2 * C.natDegree + E.natDegree := by
        simp only [omicronCubicSigmaFaceCE610]
        rw [natDegree_smul _ hc, natDegree_mul (pow_ne_zero 2 hCne) hEne, natDegree_pow]
      have hrest := degreeZeroOmicronCubicNoSigmaCE610_natDegree_lt_of_loadCone alpha beta delta epsilon zeta eta theta
          A B C D E hcone hb hd hz ht hpos
      rw [degreeZeroOmicronCubic610_eq_sigmaCE_add_rest,
        natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
      omega
  ·
    have hface0 : 2 * C.natDegree + E.natDegree = 0 := by omega
    rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
      hCne, hEne, heq, hBcmp, hDcmp⟩
    have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
    have hCdeg0 : C.natDegree = 0 := by omega
    have hEdeg0 : E.natDegree = 0 := by omega
    have hB0 : B = 0 := by
      rcases hBcmp with hB0 | hBlt
      · exact hB0
      · omega
    have hD0 : D = 0 := by
      rcases hDcmp with hD0 | hDlt
      · exact hD0
      · omega
    rw [hCdeg0] at hb hd hz ht
    have hbeta0 : beta = 0 := by
      rcases hb with h | h
      · exact h
      · omega
    have hdelta0 : delta = 0 := by
      rcases hd with h | h
      · exact h
      · omega
    have hzeta0 : zeta = 0 := by
      rcases hz with h | h
      · exact h
      · omega
    have htheta0 : theta = 0 := by
      rcases ht with h | h
      · exact h
      · omega
    exact cubicLoadCompete_BD_zero_impossible (j := j) (t := t)
      0 alpha beta delta epsilon zeta eta theta A B C D E
      hB0 hD0 rfl hbeta0 hdelta0 hzeta0 htheta0 hjdiv hder



/- σ-cone DE -/


set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaCubicNoSigmaDE610_natDegree_lt_of_loadCone
    (alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeDE610 A B C D E)
    (hb : beta  = 0 ∨ 7 * (10 * A.natDegree) ≤ 18 * A.natDegree + 28 * D.natDegree)
    (hd : delta = 0 ∨ 7 * (10 * A.natDegree) ≤ 30 * A.natDegree + 28 * D.natDegree)
    (hz : zeta  = 0 ∨ 10 * A.natDegree ≤ 6 * A.natDegree + 4 * D.natDegree)
    (ht : theta = 0 ∨ 7 * (10 * A.natDegree) ≤ 54 * A.natDegree + 28 * D.natDegree) :
    (degreeZeroKappaCubicNoSigmaDE610 0 alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      D.natDegree + E.natDegree := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hDne, hEne, heq, hBcmp, hCcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsAB : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAB
  have hsAC : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hAC
  have hsAD : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hAD
  have hsAE : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAE
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have htie : A.natDegree + 2 * D.natDegree = 2 * E.natDegree := by omega

  rcases hb with rfl | hb <;> rcases hd with rfl | hd <;>
    rcases hz with rfl | hz <;> rcases ht with rfl | ht <;>
    rcases hBcmp with rfl | hBcmp <;> rcases hCcmp with rfl | hCcmp <;>
      (simp only [degreeZeroKappaCubicNoSigmaDE610, hpow2, hpow3, hpow4, hpow5,
                  zero_mul, mul_zero, zero_smul, smul_zero,
                  add_zero, zero_add, zero_pow, Nat.succ_ne_zero,
                  sub_zero, neg_zero, natDegree_zero];
       compute_degree; omega)


set_option maxHeartbeats 64000000 in
theorem cubicLoadSigmaCone_DE_impossible {j t : k}
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeDE610 A B C D E)
    (hl : l = 0)
    (hb4 : (beta = 0 ∨
      7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 18 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 28 * E.natDegree))
    (hd4 : (delta = 0 ∨
      7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 30 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 28 * E.natDegree))
    (hz4 : (zeta = 0 ∨
      9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree ∨
      12 * A.natDegree ≤ 6 * A.natDegree + 6 * C.natDegree ∨
      10 * A.natDegree ≤ 6 * A.natDegree + 4 * D.natDegree ∨
      12 * A.natDegree ≤ 6 * A.natDegree + 4 * E.natDegree))
    (ht4 : (theta = 0 ∨
      7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 54 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 28 * E.natDegree))
    (hdeg : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree = 0) :
    False := by
  subst hl
  have hDne : D ≠ 0 := by
    rcases hcone with ⟨_, hDne, hEne, heq, hBcmp, hCcmp⟩
    exact hDne
  have hEne : E ≠ 0 := by
    rcases hcone with ⟨_, hDne, hEne, heq, hBcmp, hCcmp⟩
    exact hEne
  have hb : beta = 0 ∨ 7 * (10 * A.natDegree) ≤ 18 * A.natDegree + 28 * D.natDegree :=
    cubicLoadSigmaConeDE610_specialize_beta hcone hb4
  have hd : delta = 0 ∨ 7 * (10 * A.natDegree) ≤ 30 * A.natDegree + 28 * D.natDegree :=
    cubicLoadSigmaConeDE610_specialize_delta hcone hd4
  have hz : zeta = 0 ∨ 10 * A.natDegree ≤ 6 * A.natDegree + 4 * D.natDegree :=
    cubicLoadSigmaConeDE610_specialize_zeta hcone hz4
  have ht : theta = 0 ∨ 7 * (10 * A.natDegree) ≤ 54 * A.natDegree + 28 * D.natDegree :=
    cubicLoadSigmaConeDE610_specialize_theta hcone ht4
  have hc : (10 / 9 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (kappaCubicSigmaFaceDE610 A B C D E).natDegree = D.natDegree + E.natDegree := by
    simp only [kappaCubicSigmaFaceDE610]
    rw [natDegree_smul _ hc, natDegree_mul hDne hEne]
  have hrest := degreeZeroKappaCubicNoSigmaDE610_natDegree_lt_of_loadCone alpha beta delta epsilon zeta eta theta
      A B C D E hcone hb hd hz ht
  rw [degreeZeroKappaCubic610_eq_sigmaDE_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  omega



/- σ-cone BCD -/


set_option maxHeartbeats 64000000 in
theorem degreeZeroOmicronCubicNoSigmaBCD610_natDegree_lt_of_loadCone
    (alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeBCD610 A B C D E)
    (hb : beta  = 0 ∨ 7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree)
    (hd : delta = 0 ∨ 7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree)
    (hz : zeta  = 0 ∨ 9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree)
    (ht : theta = 0 ∨ 7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree) :
    (degreeZeroOmicronCubicNoSigmaBCD610 0 alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      A.natDegree + B.natDegree + C.natDegree + D.natDegree := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hCne, hDne, heq1, heq2, hEcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsAB : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAB
  have hsAC : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hAC
  have hsAD : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hAD
  have hsAE : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAE
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have htieBC : 4 * A.natDegree + 2 * B.natDegree =
      3 * A.natDegree + 2 * C.natDegree := heq1
  have htieBD : 10 * A.natDegree + 6 * B.natDegree =
      9 * A.natDegree + 4 * D.natDegree := heq2
  have hsE : 4 * E.natDegree + 1 ≤ 3 * A.natDegree + 6 * B.natDegree := by
    rcases hEcmp with h0 | hlt
    · have : E.natDegree = 0 := by simp [h0]
      omega
    · exact Nat.succ_le_of_lt hlt
  rcases hb with rfl | hb <;> rcases hd with rfl | hd <;>
    rcases hz with rfl | hz <;> rcases ht with rfl | ht <;>
      (simp only [degreeZeroOmicronCubicNoSigmaBCD610, hpow2, hpow3, hpow4, hpow5,
                  zero_mul, mul_zero, zero_smul, smul_zero,
                  add_zero, zero_add, zero_pow, Nat.succ_ne_zero,
                  sub_zero, neg_zero, natDegree_zero];
       compute_degree; omega)


set_option maxHeartbeats 64000000 in
theorem cubicLoadSigmaCone_BCD_impossible {j t : k}
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeBCD610 A B C D E)
    (hl : l = 0)
    (hb4 : (beta = 0 ∨
      7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 18 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 28 * E.natDegree))
    (hd4 : (delta = 0 ∨
      7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 30 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 28 * E.natDegree))
    (hz4 : (zeta = 0 ∨
      9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree ∨
      12 * A.natDegree ≤ 6 * A.natDegree + 6 * C.natDegree ∨
      10 * A.natDegree ≤ 6 * A.natDegree + 4 * D.natDegree ∨
      12 * A.natDegree ≤ 6 * A.natDegree + 4 * E.natDegree))
    (ht4 : (theta = 0 ∨
      7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 54 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 28 * E.natDegree))
    (hdeg : (degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree = 0) :
    False := by
  subst hl
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, _⟩
    omega
  have hBne : B ≠ 0 := by
    rcases hcone with ⟨_, hBne, hCne, hDne, heq1, heq2, hEcmp⟩
    exact hBne
  have hCne : C ≠ 0 := by
    rcases hcone with ⟨_, hBne, hCne, hDne, heq1, heq2, hEcmp⟩
    exact hCne
  have hDne : D ≠ 0 := by
    rcases hcone with ⟨_, hBne, hCne, hDne, heq1, heq2, hEcmp⟩
    exact hDne
  have hb : beta = 0 ∨ 7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree :=
    cubicLoadSigmaConeBCD610_specialize_beta hcone hb4
  have hd : delta = 0 ∨ 7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree :=
    cubicLoadSigmaConeBCD610_specialize_delta hcone hd4
  have hz : zeta = 0 ∨ 9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree :=
    cubicLoadSigmaConeBCD610_specialize_zeta hcone hz4
  have ht : theta = 0 ∨ 7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree :=
    cubicLoadSigmaConeBCD610_specialize_theta hcone ht4
  have hc : (10 / 81 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (omicronCubicSigmaFaceBCD610 A B C D E).natDegree = A.natDegree + B.natDegree + C.natDegree + D.natDegree := by
    simp only [omicronCubicSigmaFaceBCD610]
    rw [natDegree_smul _ hc,
      natDegree_mul (mul_ne_zero (mul_ne_zero hAne hBne) hCne) hDne,
      natDegree_mul (mul_ne_zero hAne hBne) hCne, natDegree_mul hAne hBne]
  have hrest := degreeZeroOmicronCubicNoSigmaBCD610_natDegree_lt_of_loadCone alpha beta delta epsilon zeta eta theta
      A B C D E hcone hb hd hz ht
  rw [degreeZeroOmicronCubic610_eq_sigmaBCD_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  omega



/- σ-cone BDE -/


set_option maxHeartbeats 64000000 in
theorem degreeZeroOmicronCubicNoSigmaBDE610_natDegree_lt_of_loadCone
    (alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeBDE610 A B C D E)
    (hb : beta  = 0 ∨ 7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree)
    (hd : delta = 0 ∨ 7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree)
    (hz : zeta  = 0 ∨ 9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree)
    (ht : theta = 0 ∨ 7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree) :
    (degreeZeroOmicronCubicNoSigmaBDE610 0 alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      A.natDegree + 2 * B.natDegree + E.natDegree := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hDne, hEne, heq1, heq2, hCcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsAB : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAB
  have hsAC : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hAC
  have hsAD : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hAD
  have hsAE : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAE
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have htieBD : 10 * A.natDegree + 6 * B.natDegree =
      9 * A.natDegree + 4 * D.natDegree := heq1
  have htieBE : 12 * A.natDegree + 6 * B.natDegree =
      9 * A.natDegree + 4 * E.natDegree := heq2
  have hsC : 2 * C.natDegree + 1 ≤ A.natDegree + 2 * B.natDegree := by
    rcases hCcmp with h0 | hlt
    · have : C.natDegree = 0 := by simp [h0]
      omega
    · exact Nat.succ_le_of_lt hlt
  rcases hb with rfl | hb <;> rcases hd with rfl | hd <;>
    rcases hz with rfl | hz <;> rcases ht with rfl | ht <;>
      (simp only [degreeZeroOmicronCubicNoSigmaBDE610, hpow2, hpow3, hpow4, hpow5,
                  zero_mul, mul_zero, zero_smul, smul_zero,
                  add_zero, zero_add, zero_pow, Nat.succ_ne_zero,
                  sub_zero, neg_zero, natDegree_zero];
       compute_degree; omega)


set_option maxHeartbeats 64000000 in
theorem cubicLoadSigmaCone_BDE_impossible {j t : k}
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeBDE610 A B C D E)
    (hl : l = 0)
    (hb4 : (beta = 0 ∨
      7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 18 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 28 * E.natDegree))
    (hd4 : (delta = 0 ∨
      7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 30 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 28 * E.natDegree))
    (hz4 : (zeta = 0 ∨
      9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree ∨
      12 * A.natDegree ≤ 6 * A.natDegree + 6 * C.natDegree ∨
      10 * A.natDegree ≤ 6 * A.natDegree + 4 * D.natDegree ∨
      12 * A.natDegree ≤ 6 * A.natDegree + 4 * E.natDegree))
    (ht4 : (theta = 0 ∨
      7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 54 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 28 * E.natDegree))
    (hdeg : (degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree = 0) :
    False := by
  subst hl
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, _⟩
    omega
  have hBne : B ≠ 0 := by
    rcases hcone with ⟨_, hBne, hDne, hEne, heq1, heq2, hCcmp⟩
    exact hBne
  have hEne : E ≠ 0 := by
    rcases hcone with ⟨_, hBne, hDne, hEne, heq1, heq2, hCcmp⟩
    exact hEne
  have hb : beta = 0 ∨ 7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree :=
    cubicLoadSigmaConeBDE610_specialize_beta hcone hb4
  have hd : delta = 0 ∨ 7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree :=
    cubicLoadSigmaConeBDE610_specialize_delta hcone hd4
  have hz : zeta = 0 ∨ 9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree :=
    cubicLoadSigmaConeBDE610_specialize_zeta hcone hz4
  have ht : theta = 0 ∨ 7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree :=
    cubicLoadSigmaConeBDE610_specialize_theta hcone ht4
  have hc : (5 / 81 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (omicronCubicSigmaFaceBDE610 A B C D E).natDegree = A.natDegree + 2 * B.natDegree + E.natDegree := by
    simp only [omicronCubicSigmaFaceBDE610]
    rw [natDegree_smul _ hc,
      natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hEne,
      natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow]
  have hrest := degreeZeroOmicronCubicNoSigmaBDE610_natDegree_lt_of_loadCone alpha beta delta epsilon zeta eta theta
      A B C D E hcone hb hd hz ht
  rw [degreeZeroOmicronCubic610_eq_sigmaBDE_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  omega



/- σ-cone CDE -/


set_option maxHeartbeats 64000000 in
theorem degreeZeroOmicronCubicNoSigmaCDE610_natDegree_lt_of_loadCone
    (alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeCDE610 A B C D E)
    (hb : beta  = 0 ∨ 7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 42 * C.natDegree)
    (hd : delta = 0 ∨ 7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 42 * C.natDegree)
    (hz : zeta  = 0 ∨ 12 * A.natDegree ≤ 6 * A.natDegree + 6 * C.natDegree)
    (ht : theta = 0 ∨ 7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 42 * C.natDegree) :
    (degreeZeroOmicronCubicNoSigmaCE610 0 alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      2 * C.natDegree + E.natDegree := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hCne, hDne, hEne, heq1, heq2, hBcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsAB : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAB
  have hsAC : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hAC
  have hsAD : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hAD
  have hsAE : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAE
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have htieCD : A.natDegree + 2 * D.natDegree = 3 * C.natDegree := by omega
  have htieCE : 3 * C.natDegree = 2 * E.natDegree := by omega

  rcases hb with rfl | hb <;> rcases hd with rfl | hd <;>
    rcases hz with rfl | hz <;> rcases ht with rfl | ht <;>
    rcases hBcmp with rfl | hBcmp <;>
      (simp only [degreeZeroOmicronCubicNoSigmaCE610, hpow2, hpow3, hpow4, hpow5,
                  zero_mul, mul_zero, zero_smul, smul_zero,
                  add_zero, zero_add, zero_pow, Nat.succ_ne_zero,
                  sub_zero, neg_zero, natDegree_zero];
       compute_degree; omega)


set_option maxHeartbeats 64000000 in
theorem cubicLoadSigmaCone_CDE_impossible {j t : k}
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeCDE610 A B C D E)
    (hl : l = 0)
    (hb4 : (beta = 0 ∨
      7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 18 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 28 * E.natDegree))
    (hd4 : (delta = 0 ∨
      7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 30 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 28 * E.natDegree))
    (hz4 : (zeta = 0 ∨
      9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree ∨
      12 * A.natDegree ≤ 6 * A.natDegree + 6 * C.natDegree ∨
      10 * A.natDegree ≤ 6 * A.natDegree + 4 * D.natDegree ∨
      12 * A.natDegree ≤ 6 * A.natDegree + 4 * E.natDegree))
    (ht4 : (theta = 0 ∨
      7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 54 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 28 * E.natDegree))
    (hdeg : (degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree = 0) :
    False := by
  subst hl
  have hCne : C ≠ 0 := by
    rcases hcone with ⟨_, hCne, hDne, hEne, heq1, heq2, hBcmp⟩
    exact hCne
  have hEne : E ≠ 0 := by
    rcases hcone with ⟨_, hCne, hDne, hEne, heq1, heq2, hBcmp⟩
    exact hEne
  have hb : beta = 0 ∨ 7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 42 * C.natDegree :=
    cubicLoadSigmaConeCDE610_specialize_beta hcone hb4
  have hd : delta = 0 ∨ 7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 42 * C.natDegree :=
    cubicLoadSigmaConeCDE610_specialize_delta hcone hd4
  have hz : zeta = 0 ∨ 12 * A.natDegree ≤ 6 * A.natDegree + 6 * C.natDegree :=
    cubicLoadSigmaConeCDE610_specialize_zeta hcone hz4
  have ht : theta = 0 ∨ 7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 42 * C.natDegree :=
    cubicLoadSigmaConeCDE610_specialize_theta hcone ht4
  have hc : (-(5 / 27 : k)) ≠ 0 := neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead : (omicronCubicSigmaFaceCE610 A B C D E).natDegree = 2 * C.natDegree + E.natDegree := by
    simp only [omicronCubicSigmaFaceCE610]
    rw [natDegree_smul _ hc, natDegree_mul (pow_ne_zero 2 hCne) hEne, natDegree_pow]
  have hrest := degreeZeroOmicronCubicNoSigmaCDE610_natDegree_lt_of_loadCone alpha beta delta epsilon zeta eta theta
      A B C D E hcone hb hd hz ht
  rw [degreeZeroOmicronCubic610_eq_sigmaCE_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  omega


end CubicLoadSigmaSingleMonomial610


/-! ## `{C,D}` via `N₁`, with N₁/N₂ walls -/

section CubicLoadSigmaCD610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
/-- Off-wall N₁ rest bound: odd pure-`A` columns are strictly below the
`C²D` face.  Band hypotheses use strict `<` so the odd pure-`A`
columns stay below the face.  At a wall `7 T = 18a` (etc.) the
corresponding column *ties* the face — those equalities are the
N₁/N₂ 2×2, not this lemma. -/
theorem degreeZeroN1CubicNoSigmaCDNoL610_natDegree_lt_of_loadCone
    (alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hb : beta  = 0 ∨ 7 * (12 * A.natDegree) < 18 * A.natDegree + 42 * C.natDegree)
    (hd : delta = 0 ∨ 7 * (12 * A.natDegree) < 30 * A.natDegree + 42 * C.natDegree)
    (hz : zeta  = 0 ∨      12 * A.natDegree  <  6 * A.natDegree +  6 * C.natDegree)
    (ht : theta = 0 ∨ 7 * (12 * A.natDegree) < 54 * A.natDegree + 42 * C.natDegree) :
    (degreeZeroN1CubicNoSigmaCDNoL610 0 alpha beta delta epsilon zeta eta
        theta A B C D E).natDegree <
      2 * C.natDegree + D.natDegree := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hCne, hDne, heq, hBcmp, hEcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsAB : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAB
  have hsAC : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hAC
  have hsAD : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hAD
  have hsAE : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAE
  have hCD : A.natDegree + 2 * D.natDegree = 3 * C.natDegree := by omega
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  rcases hb with rfl | hb <;> rcases hd with rfl | hd <;>
    rcases hz with rfl | hz <;> rcases ht with rfl | ht <;>
    rcases hBcmp with rfl | hBcmp <;> rcases hEcmp with rfl | hEcmp <;>
      (simp only [degreeZeroN1CubicNoSigmaCDNoL610, hpow2, hpow3, hpow4, hpow5,
                  zero_mul, mul_zero, zero_smul, add_zero, zero_add, zero_pow,
                  Nat.succ_ne_zero, smul_zero, sub_zero, neg_zero,
                  natDegree_zero];
       compute_degree; omega)

set_option maxHeartbeats 64000000 in
/-- N₁ kill off the odd-column walls, on the chamber `2c+d > a`. -/
theorem cubicLoadSigmaCone_CD_offWall_impossible
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hl : l = 0)
    (hb : beta  = 0 ∨ 7 * (12 * A.natDegree) < 18 * A.natDegree + 42 * C.natDegree)
    (hd : delta = 0 ∨ 7 * (12 * A.natDegree) < 30 * A.natDegree + 42 * C.natDegree)
    (hz : zeta  = 0 ∨      12 * A.natDegree  <  6 * A.natDegree +  6 * C.natDegree)
    (ht : theta = 0 ∨ 7 * (12 * A.natDegree) < 54 * A.natDegree + 42 * C.natDegree)
    (hTpos : A.natDegree < 2 * C.natDegree + D.natDegree)
    (hmu : (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree = 0)
    (hkap : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree = 0) :
    False := by
  subst hl
  have hCne : C ≠ 0 := by
    rcases hcone with ⟨_, hCne, _⟩
    exact hCne
  have hDne : D ≠ 0 := by
    rcases hcone with ⟨_, _, hDne, _⟩
    exact hDne
  have hN1le := degreeZeroN1Cubic610_natDegree_le 0 alpha beta delta epsilon
      zeta eta theta A B C D E hmu hkap
  have hrest :=
    degreeZeroN1CubicNoSigmaCDNoL610_natDegree_lt_of_loadCone alpha beta
      delta epsilon zeta eta theta A B C D E hcone hb hd hz ht
  have hfaceDeg := n1CubicSigmaFaceCD610_natDegree A B C D E hCne hDne
  have hz0 : (degreeZeroN1Cubic610 0 alpha beta delta epsilon zeta eta theta
        A B C D E).coeff (2 * C.natDegree + D.natDegree) = 0 :=
    coeff_eq_zero_of_natDegree_lt (hN1le.trans_lt hTpos)
  rw [degreeZeroN1Cubic610_eq_sigmaCD_add_rest,
    degreeZeroN1CubicNoSigmaCD610_eq_L_add_rest, coeff_add, coeff_add] at hz0
  have hsmall :
      (degreeZeroN1CubicNoSigmaCDNoL610 0 alpha beta delta epsilon zeta eta
          theta A B C D E).coeff (2 * C.natDegree + D.natDegree) = 0 :=
    coeff_eq_zero_of_natDegree_lt hrest
  have hL0 : (n1CubicLFace610 0 A).coeff
      (2 * C.natDegree + D.natDegree) = 0 := by
    simp only [n1CubicLFace610, mul_zero, zero_smul, coeff_zero]
  rw [hsmall, hL0, add_zero, add_zero] at hz0
  exact n1CubicSigmaFaceCD610_leading_ne A B C D E hCne hDne hz0

end CubicLoadSigmaCD610


/-! ## Residual 7 -/

section CubicLoadConesAssembly610

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 64000000 in
/-- Honest leftover after the 11 single-monomial load-compete cone kills
(`B,C,D,E,BD,BE,CE,DE,BCD,BDE,CDE`).

Not closed here: the multi-monomial cones `{B,C}`, `{B,C,E}`,
`{B,C,D,E}` (File C), and `{C,D}` (N₁ odd-column walls
`7T ∈ {18a,30a,6a,54a}` and the chamber `2c+d ≤ a`, where the N₁
face does not beat `degreeZeroN1Cubic610_natDegree_le`).  Next unused
row: File C identities `cubicSigmaInner_{BC,BCE,BCDE}` plus the CD
N₁/N₂ 2×2.  No finite-root shortcut is used. -/
theorem normalized610ScaleZero_cubicResidual7
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t j lambda omicron l alpha beta gamma delta epsilon zeta eta theta
        iota cLam cKap cMu cOmi : k) (A B C D E : k[X]),
      t ≠ 0 ∧
      j ≠ 0 ∧
      j / t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      derivative
          (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta
            eta theta A B C D E) =
        Polynomial.C (j / t) ∧
      (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree = 0 ∧
      (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree = 0 ∧
      (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree = 0 ∧
      (degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree = 0 ∧
      CubicRatioConeA610 A B C D E ∧
      cubicLoadCompetes610 A B C D E ∧
      l = 0 ∧
      (cubicKappaBetaTop610 A B C D E → beta = 0) ∧
      (cubicKappaDeltaTop610 A B C D E → delta = 0) ∧
      (cubicKappaZetaTop610 A B C D E → zeta = 0) ∧
      (cubicN1BetaTop610 A B C D E → beta = 0) ∧
      (cubicN1DeltaTop610 A B C D E → delta = 0) ∧
      (cubicN1ZetaTop610 A B C D E → zeta = 0) ∧
      (cubicN1ThetaTop610 A B C D E → theta = 0) ∧
      (beta = 0 ∨
        7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree ∨
        7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 42 * C.natDegree ∨
        7 * (10 * A.natDegree) ≤ 18 * A.natDegree + 28 * D.natDegree ∨
        7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 28 * E.natDegree) ∧
      (delta = 0 ∨
        7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree ∨
        7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 42 * C.natDegree ∨
        7 * (10 * A.natDegree) ≤ 30 * A.natDegree + 28 * D.natDegree ∨
        7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 28 * E.natDegree) ∧
      (zeta = 0 ∨
        9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree ∨
        12 * A.natDegree ≤ 6 * A.natDegree + 6 * C.natDegree ∨
        10 * A.natDegree ≤ 6 * A.natDegree + 4 * D.natDegree ∨
        12 * A.natDegree ≤ 6 * A.natDegree + 4 * E.natDegree) ∧
      (theta = 0 ∨
        7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree ∨
        7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 42 * C.natDegree ∨
        7 * (10 * A.natDegree) ≤ 54 * A.natDegree + 28 * D.natDegree ∨
        7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 28 * E.natDegree) ∧
      (CubicLoadSigmaConeBC610 A B C D E ∨
        CubicLoadSigmaConeBCE610 A B C D E ∨
        CubicLoadSigmaConeBCDE610 A B C D E ∨
        CubicLoadSigmaConeCD610 A B C D E) := by
  obtain ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
      zeta, eta, theta, iota, cLam, cKap, cMu, cOmi, A, B, C, D, E, ht,
      hj, hjdiv, hHsq, hder, hlamDeg, hkapDeg, hmuDeg, homiDeg, hconeA,
      hload, hl0, hkapB, hkapD, hkapZ, hbN1, hdN1, hzN1, htN1, hbBand,
      hdBand, hzBand, htBand, hexh⟩ :=
    normalized610ScaleZero_cubicResidual6 hsource
  refine ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
    zeta, eta, theta, iota, cLam, cKap, cMu, cOmi, A, B, C, D, E, ht, hj,
    hjdiv, hHsq, hder, hlamDeg, hkapDeg, hmuDeg, homiDeg, hconeA, hload,
    hl0, hkapB, hkapD, hkapZ, hbN1, hdN1, hzN1, htN1, hbBand, hdBand,
    hzBand, htBand, ?_⟩
  cases hexh with
  | sigmaB hcone =>
    exact (cubicLoadSigmaCone_B_impossible (j := j) (t := t) l alpha beta
      delta epsilon zeta eta theta A B C D E hcone hl0 hbBand hdBand
      hzBand htBand hkapDeg).elim
  | sigmaC hcone =>
    exact (cubicLoadSigmaCone_C_impossible (j := j) (t := t) l alpha beta
      delta epsilon zeta eta theta A B C D E hcone hl0 hbBand hdBand
      hzBand htBand hlamDeg hjdiv hder).elim
  | sigmaD hcone =>
    exact (cubicLoadSigmaCone_D_impossible (j := j) (t := t) l alpha beta
      delta epsilon zeta eta theta A B C D E hcone hl0 hbBand hdBand
      hzBand htBand hlamDeg).elim
  | sigmaE hcone =>
    exact (cubicLoadSigmaCone_E_impossible (j := j) (t := t) l alpha beta
      delta epsilon zeta eta theta A B C D E hcone hl0 hbBand hdBand
      hzBand htBand hlamDeg hjdiv hder).elim
  | sigmaBC hcone => exact Or.inl hcone
  | sigmaBD hcone =>
    exact (cubicLoadSigmaCone_BD_impossible (j := j) (t := t) l alpha beta
      delta epsilon zeta eta theta A B C D E hcone hl0 hbBand hdBand
      hzBand htBand hlamDeg).elim
  | sigmaBE hcone =>
    exact (cubicLoadSigmaCone_BE_impossible (j := j) (t := t) l alpha beta
      delta epsilon zeta eta theta A B C D E hcone hl0 hbBand hdBand
      hzBand htBand hlamDeg).elim
  | sigmaCD hcone => exact Or.inr (Or.inr (Or.inr hcone))
  | sigmaCE hcone =>
    exact (cubicLoadSigmaCone_CE_impossible (j := j) (t := t) l alpha beta
      delta epsilon zeta eta theta A B C D E hcone hl0 hbBand hdBand
      hzBand htBand homiDeg hjdiv hder).elim
  | sigmaDE hcone =>
    exact (cubicLoadSigmaCone_DE_impossible (j := j) (t := t) l alpha beta
      delta epsilon zeta eta theta A B C D E hcone hl0 hbBand hdBand
      hzBand htBand hkapDeg).elim
  | sigmaBCD hcone =>
    exact (cubicLoadSigmaCone_BCD_impossible (j := j) (t := t) l alpha beta
      delta epsilon zeta eta theta A B C D E hcone hl0 hbBand hdBand
      hzBand htBand homiDeg).elim
  | sigmaBCE hcone => exact Or.inr (Or.inl hcone)
  | sigmaBDE hcone =>
    exact (cubicLoadSigmaCone_BDE_impossible (j := j) (t := t) l alpha beta
      delta epsilon zeta eta theta A B C D E hcone hl0 hbBand hdBand
      hzBand htBand homiDeg).elim
  | sigmaCDE hcone =>
    exact (cubicLoadSigmaCone_CDE_impossible (j := j) (t := t) l alpha beta
      delta epsilon zeta eta theta A B C D E hcone hl0 hbBand hdBand
      hzBand htBand homiDeg).elim
  | sigmaBCDE hcone => exact Or.inr (Or.inr (Or.inl hcone))
  | allZero h0 =>
    rcases h0 with ⟨hB0, hC0, hD0, hE0⟩
    exact (cubicADominant_allLettersZero_impossible (j := j) (t := t) l
      alpha beta delta epsilon zeta eta theta A B C D E hconeA.1 hB0 hC0
      hD0 hE0 hjdiv hder).elim

end CubicLoadConesAssembly610

#print axioms degreeZeroKappaCubicNoSigmaB610_natDegree_lt_of_loadCone
#print axioms cubicLoadSigmaCone_B_impossible
#print axioms cubicLoadSigmaCone_C_impossible
#print axioms cubicLoadSigmaCone_D_impossible
#print axioms cubicLoadSigmaCone_E_impossible
#print axioms cubicLoadSigmaCone_BD_impossible
#print axioms cubicLoadSigmaCone_BE_impossible
#print axioms cubicLoadSigmaCone_CE_impossible
#print axioms cubicLoadSigmaCone_DE_impossible
#print axioms cubicLoadSigmaCone_BCD_impossible
#print axioms cubicLoadSigmaCone_BDE_impossible
#print axioms cubicLoadSigmaCone_CDE_impossible
#print axioms cubicLoadSigmaCone_CD_offWall_impossible
#print axioms normalized610ScaleZero_cubicResidual7

end Max11DegreeRoutes
