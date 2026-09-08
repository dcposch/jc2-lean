import Grok610ScaleZeroCubicLoadLadderScratch
import Max11SpeedReflectDegLibScratch

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


end CubicLoadSigmaSingleMonomial610


/-! ## `{C,D}` via `N₁`, with N₁/N₂ walls -/

section CubicLoadSigmaCD610

variable {k : Type*} [Field k] [CharZero k]

end CubicLoadSigmaCD610


/-! ## Residual 7 -/

section CubicLoadConesAssembly610

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

end CubicLoadConesAssembly610


end Max11DegreeRoutes

