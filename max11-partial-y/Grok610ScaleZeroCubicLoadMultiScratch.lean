import Grok610ScaleZeroCubicLoadConesScratch

/-! # Scale-zero cubic load-compete multi-monomial cones, `(6,10)`, `H = 0`

Continuation of `Grok610ScaleZeroCubicLoadConesScratch`.  That file
ends at `normalized610ScaleZero_cubicResidual7`: the leftover is the
multi-monomial cones `{B,C}`, `{B,C,E}`, `{B,C,D,E}` and `{C,D}`
(N₁ odd-column walls `7T ∈ {18a,30a,42a,54a}` and the chamber
`2c+d ≤ a`).

Plan `Grok610ScaleZeroCubicLoadCompetePlanScratch.md` File C (§2,
§3.3–3.5, §4, §5 item 1): kill those cones via the identities
`cubicSigmaInner_{BC,BCE,BCDE}` and the N₁/N₂ 2×2 on the CD/BCDE
walls, then assemble `normalized610ScaleZero_impossible`.

No `sorry`, no new axioms, no finite-root shortcut.
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


section CubicLoadMultiBandSpecialize610

variable {k : Type*} [Field k] [CharZero k]

/-- Specialise residual-6 four-way bands onto cone `BC`. -/

theorem cubicLoadSigmaConeBC610_specialize_beta
    {beta : k} {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeBC610 A B C D E)
    (hband : (beta = 0 ∨
      7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 18 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 28 * E.natDegree)) :
    (beta = 0 ∨ 7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree) := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hCne, heq, hDcmp, hEcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
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
    omega
  · -- D-summand of the four-way OR
    rcases hsD with hsD | hD0
    · omega
    · omega
  · -- E-summand of the four-way OR
    rcases hsE with hsE | hE0
    · omega
    · omega


theorem cubicLoadSigmaConeBC610_specialize_delta
    {delta : k} {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeBC610 A B C D E)
    (hband : (delta = 0 ∨
      7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 30 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 28 * E.natDegree)) :
    (delta = 0 ∨ 7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree) := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hCne, heq, hDcmp, hEcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
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
    omega
  · -- D-summand of the four-way OR
    rcases hsD with hsD | hD0
    · omega
    · omega
  · -- E-summand of the four-way OR
    rcases hsE with hsE | hE0
    · omega
    · omega


theorem cubicLoadSigmaConeBC610_specialize_zeta
    {zeta : k} {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeBC610 A B C D E)
    (hband : (zeta = 0 ∨
      9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree ∨
      12 * A.natDegree ≤ 6 * A.natDegree + 6 * C.natDegree ∨
      10 * A.natDegree ≤ 6 * A.natDegree + 4 * D.natDegree ∨
      12 * A.natDegree ≤ 6 * A.natDegree + 4 * E.natDegree)) :
    (zeta = 0 ∨ 9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree) := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hCne, heq, hDcmp, hEcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
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
    omega
  · -- D-summand of the four-way OR
    rcases hsD with hsD | hD0
    · omega
    · omega
  · -- E-summand of the four-way OR
    rcases hsE with hsE | hE0
    · omega
    · omega


theorem cubicLoadSigmaConeBC610_specialize_theta
    {theta : k} {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeBC610 A B C D E)
    (hband : (theta = 0 ∨
      7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 54 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 28 * E.natDegree)) :
    (theta = 0 ∨ 7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree) := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hCne, heq, hDcmp, hEcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
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
    omega
  · -- D-summand of the four-way OR
    rcases hsD with hsD | hD0
    · omega
    · omega
  · -- E-summand of the four-way OR
    rcases hsE with hsE | hE0
    · omega
    · omega


/-- Specialise residual-6 four-way bands onto cone `BCE`. -/

theorem cubicLoadSigmaConeBCE610_specialize_beta
    {beta : k} {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeBCE610 A B C D E)
    (hband : (beta = 0 ∨
      7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 18 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 28 * E.natDegree)) :
    (beta = 0 ∨ 7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree) := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hCne, hEne, heq1, heq2, hDcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsD : 4 * D.natDegree + 1 ≤ A.natDegree + 6 * B.natDegree ∨ D.natDegree = 0 := by
    rcases hDcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  rcases hband with h | h | h | h | h
  · exact Or.inl h
  · -- B-summand of the four-way OR
    exact Or.inr h
  · -- C-summand of the four-way OR
    omega
  · -- D-summand of the four-way OR
    rcases hsD with hsD | hD0
    · omega
    · omega
  · -- E-summand of the four-way OR
    omega


theorem cubicLoadSigmaConeBCE610_specialize_delta
    {delta : k} {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeBCE610 A B C D E)
    (hband : (delta = 0 ∨
      7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 30 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 28 * E.natDegree)) :
    (delta = 0 ∨ 7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree) := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hCne, hEne, heq1, heq2, hDcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsD : 4 * D.natDegree + 1 ≤ A.natDegree + 6 * B.natDegree ∨ D.natDegree = 0 := by
    rcases hDcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  rcases hband with h | h | h | h | h
  · exact Or.inl h
  · -- B-summand of the four-way OR
    exact Or.inr h
  · -- C-summand of the four-way OR
    omega
  · -- D-summand of the four-way OR
    rcases hsD with hsD | hD0
    · omega
    · omega
  · -- E-summand of the four-way OR
    omega


theorem cubicLoadSigmaConeBCE610_specialize_zeta
    {zeta : k} {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeBCE610 A B C D E)
    (hband : (zeta = 0 ∨
      9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree ∨
      12 * A.natDegree ≤ 6 * A.natDegree + 6 * C.natDegree ∨
      10 * A.natDegree ≤ 6 * A.natDegree + 4 * D.natDegree ∨
      12 * A.natDegree ≤ 6 * A.natDegree + 4 * E.natDegree)) :
    (zeta = 0 ∨ 9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree) := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hCne, hEne, heq1, heq2, hDcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsD : 4 * D.natDegree + 1 ≤ A.natDegree + 6 * B.natDegree ∨ D.natDegree = 0 := by
    rcases hDcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  rcases hband with h | h | h | h | h
  · exact Or.inl h
  · -- B-summand of the four-way OR
    exact Or.inr h
  · -- C-summand of the four-way OR
    omega
  · -- D-summand of the four-way OR
    rcases hsD with hsD | hD0
    · omega
    · omega
  · -- E-summand of the four-way OR
    omega


theorem cubicLoadSigmaConeBCE610_specialize_theta
    {theta : k} {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeBCE610 A B C D E)
    (hband : (theta = 0 ∨
      7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 54 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 28 * E.natDegree)) :
    (theta = 0 ∨ 7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree) := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hCne, hEne, heq1, heq2, hDcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsD : 4 * D.natDegree + 1 ≤ A.natDegree + 6 * B.natDegree ∨ D.natDegree = 0 := by
    rcases hDcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  rcases hband with h | h | h | h | h
  · exact Or.inl h
  · -- B-summand of the four-way OR
    exact Or.inr h
  · -- C-summand of the four-way OR
    omega
  · -- D-summand of the four-way OR
    rcases hsD with hsD | hD0
    · omega
    · omega
  · -- E-summand of the four-way OR
    omega


/-- Specialise residual-6 four-way bands onto cone `BCDE`. -/

theorem cubicLoadSigmaConeBCDE610_specialize_beta
    {beta : k} {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeBCDE610 A B C D E)
    (hband : (beta = 0 ∨
      7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 18 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 28 * E.natDegree)) :
    (beta = 0 ∨ 7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree) := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hCne, hDne, hEne, heq1, heq2, heq3⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  rcases hband with h | h | h | h | h
  · exact Or.inl h
  · -- B-summand of the four-way OR
    exact Or.inr h
  · -- C-summand of the four-way OR
    omega
  · -- D-summand of the four-way OR
    omega
  · -- E-summand of the four-way OR
    omega


theorem cubicLoadSigmaConeBCDE610_specialize_delta
    {delta : k} {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeBCDE610 A B C D E)
    (hband : (delta = 0 ∨
      7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 30 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 28 * E.natDegree)) :
    (delta = 0 ∨ 7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree) := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hCne, hDne, hEne, heq1, heq2, heq3⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  rcases hband with h | h | h | h | h
  · exact Or.inl h
  · -- B-summand of the four-way OR
    exact Or.inr h
  · -- C-summand of the four-way OR
    omega
  · -- D-summand of the four-way OR
    omega
  · -- E-summand of the four-way OR
    omega


theorem cubicLoadSigmaConeBCDE610_specialize_zeta
    {zeta : k} {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeBCDE610 A B C D E)
    (hband : (zeta = 0 ∨
      9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree ∨
      12 * A.natDegree ≤ 6 * A.natDegree + 6 * C.natDegree ∨
      10 * A.natDegree ≤ 6 * A.natDegree + 4 * D.natDegree ∨
      12 * A.natDegree ≤ 6 * A.natDegree + 4 * E.natDegree)) :
    (zeta = 0 ∨ 9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree) := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hCne, hDne, hEne, heq1, heq2, heq3⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  rcases hband with h | h | h | h | h
  · exact Or.inl h
  · -- B-summand of the four-way OR
    exact Or.inr h
  · -- C-summand of the four-way OR
    omega
  · -- D-summand of the four-way OR
    omega
  · -- E-summand of the four-way OR
    omega


theorem cubicLoadSigmaConeBCDE610_specialize_theta
    {theta : k} {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeBCDE610 A B C D E)
    (hband : (theta = 0 ∨
      7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 54 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 28 * E.natDegree)) :
    (theta = 0 ∨ 7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree) := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hCne, hDne, hEne, heq1, heq2, heq3⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  rcases hband with h | h | h | h | h
  · exact Or.inl h
  · -- B-summand of the four-way OR
    exact Or.inr h
  · -- C-summand of the four-way OR
    omega
  · -- D-summand of the four-way OR
    omega
  · -- E-summand of the four-way OR
    omega


end CubicLoadMultiBandSpecialize610


/-! ## `{B,C}` via κ+λ -/


section CubicLoadSigmaBC610


variable {k : Type*} [Field k] [CharZero k]


set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaCubicNoSigmaBC610_natDegree_lt_of_loadCone
    (alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeBC610 A B C D E)
    (hb : beta  = 0 ∨ 7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree)
    (hd : delta = 0 ∨ 7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree)
    (hz : zeta  = 0 ∨ 9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree)
    (ht : theta = 0 ∨ 7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree) :
    (degreeZeroKappaCubicNoSigmaBC610 0 alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hCne, heq, hDcmp, hEcmp⟩
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
      3 * A.natDegree + 2 * C.natDegree := heq
  have htie : A.natDegree + 2 * B.natDegree = 2 * C.natDegree := by omega
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
      (simp only [degreeZeroKappaCubicNoSigmaBC610, hpow2, hpow3, hpow4, hpow5,
                  zero_mul, mul_zero, zero_smul, smul_zero,
                  add_zero, zero_add, zero_pow, Nat.succ_ne_zero,
                  sub_zero, neg_zero, natDegree_zero];
       compute_degree; omega)


set_option maxHeartbeats 64000000 in
theorem degreeZeroLambdaCubicNoSigmaBC610_natDegree_lt_of_loadCone
    (alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeBC610 A B C D E)
    (hb : beta  = 0 ∨ 7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree)
    (hd : delta = 0 ∨ 7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree)
    (hz : zeta  = 0 ∨ 9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree)
    (ht : theta = 0 ∨ 7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree) :
    (degreeZeroLambdaCubicNoSigmaBC610 0 alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      A.natDegree + 2 * B.natDegree + C.natDegree := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hCne, heq, hDcmp, hEcmp⟩
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
      3 * A.natDegree + 2 * C.natDegree := heq
  have htie : A.natDegree + 2 * B.natDegree = 2 * C.natDegree := by omega
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
      (simp only [degreeZeroLambdaCubicNoSigmaBC610, hpow2, hpow3, hpow4, hpow5,
                  zero_mul, mul_zero, zero_smul, smul_zero,
                  add_zero, zero_add, zero_pow, Nat.succ_ne_zero,
                  sub_zero, neg_zero, natDegree_zero];
       compute_degree; omega)

end CubicLoadSigmaBC610


/-! ## `{B,C,E}` via κ+λ+ο -/


section CubicLoadSigmaBCE610


variable {k : Type*} [Field k] [CharZero k]


set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaCubicNoSigmaBCE610_natDegree_lt_of_loadCone
    (alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeBCE610 A B C D E)
    (hb : beta  = 0 ∨ 7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree)
    (hd : delta = 0 ∨ 7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree)
    (hz : zeta  = 0 ∨ 9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree)
    (ht : theta = 0 ∨ 7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree) :
    (degreeZeroKappaCubicNoSigmaBCE610 0 alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hCne, hEne, heq1, heq2, hDcmp⟩
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
  have htieBE : 12 * A.natDegree + 6 * B.natDegree =
      9 * A.natDegree + 4 * E.natDegree := heq2
  have htie : A.natDegree + 2 * B.natDegree = 2 * C.natDegree := by omega
  have htieE : 3 * A.natDegree + 6 * B.natDegree = 4 * E.natDegree := by omega
  have hsD : 4 * D.natDegree + 1 ≤ A.natDegree + 6 * B.natDegree := by
    rcases hDcmp with h0 | hlt
    · have : D.natDegree = 0 := by simp [h0]
      omega
    · exact Nat.succ_le_of_lt hlt
  rcases hb with rfl | hb <;> rcases hd with rfl | hd <;>
    rcases hz with rfl | hz <;> rcases ht with rfl | ht <;>
      (simp only [degreeZeroKappaCubicNoSigmaBCE610, hpow2, hpow3, hpow4, hpow5,
                  zero_mul, mul_zero, zero_smul, smul_zero,
                  add_zero, zero_add, zero_pow, Nat.succ_ne_zero,
                  sub_zero, neg_zero, natDegree_zero];
       compute_degree; omega)


set_option maxHeartbeats 64000000 in
theorem degreeZeroLambdaCubicNoSigmaBCE610_natDegree_lt_of_loadCone
    (alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeBCE610 A B C D E)
    (hb : beta  = 0 ∨ 7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree)
    (hd : delta = 0 ∨ 7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree)
    (hz : zeta  = 0 ∨ 9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree)
    (ht : theta = 0 ∨ 7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree) :
    (degreeZeroLambdaCubicNoSigmaBCE610 0 alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      A.natDegree + 2 * B.natDegree + C.natDegree := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hCne, hEne, heq1, heq2, hDcmp⟩
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
  have htieBE : 12 * A.natDegree + 6 * B.natDegree =
      9 * A.natDegree + 4 * E.natDegree := heq2
  have htie : A.natDegree + 2 * B.natDegree = 2 * C.natDegree := by omega
  have htieE : 3 * A.natDegree + 6 * B.natDegree = 4 * E.natDegree := by omega
  have hsD : 4 * D.natDegree + 1 ≤ A.natDegree + 6 * B.natDegree := by
    rcases hDcmp with h0 | hlt
    · have : D.natDegree = 0 := by simp [h0]
      omega
    · exact Nat.succ_le_of_lt hlt
  rcases hb with rfl | hb <;> rcases hd with rfl | hd <;>
    rcases hz with rfl | hz <;> rcases ht with rfl | ht <;>
      (simp only [degreeZeroLambdaCubicNoSigmaBCE610, hpow2, hpow3, hpow4, hpow5,
                  zero_mul, mul_zero, zero_smul, smul_zero,
                  add_zero, zero_add, zero_pow, Nat.succ_ne_zero,
                  sub_zero, neg_zero, natDegree_zero];
       compute_degree; omega)


set_option maxHeartbeats 64000000 in
theorem degreeZeroOmicronCubicNoSigmaBCE610_natDegree_lt_of_loadCone
    (alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeBCE610 A B C D E)
    (hb : beta  = 0 ∨ 7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree)
    (hd : delta = 0 ∨ 7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree)
    (hz : zeta  = 0 ∨ 9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree)
    (ht : theta = 0 ∨ 7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree) :
    (degreeZeroOmicronCubicNoSigmaBCE610 0 alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      A.natDegree + 2 * B.natDegree + E.natDegree := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hCne, hEne, heq1, heq2, hDcmp⟩
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
  have htieBE : 12 * A.natDegree + 6 * B.natDegree =
      9 * A.natDegree + 4 * E.natDegree := heq2
  have htie : A.natDegree + 2 * B.natDegree = 2 * C.natDegree := by omega
  have htieE : 3 * A.natDegree + 6 * B.natDegree = 4 * E.natDegree := by omega
  have hsD : 4 * D.natDegree + 1 ≤ A.natDegree + 6 * B.natDegree := by
    rcases hDcmp with h0 | hlt
    · have : D.natDegree = 0 := by simp [h0]
      omega
    · exact Nat.succ_le_of_lt hlt
  rcases hb with rfl | hb <;> rcases hd with rfl | hd <;>
    rcases hz with rfl | hz <;> rcases ht with rfl | ht <;>
      (simp only [degreeZeroOmicronCubicNoSigmaBCE610, hpow2, hpow3, hpow4, hpow5,
                  zero_mul, mul_zero, zero_smul, smul_zero,
                  add_zero, zero_add, zero_pow, Nat.succ_ne_zero,
                  sub_zero, neg_zero, natDegree_zero];
       compute_degree; omega)

end CubicLoadSigmaBCE610


/-! ## `{B,C,D,E}` rest bounds -/


section CubicLoadSigmaBCDERest610


variable {k : Type*} [Field k] [CharZero k]


set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaCubicNoSigmaBCDE610_natDegree_lt_of_loadCone
    (alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeBCDE610 A B C D E)
    (hb : beta  = 0 ∨ 7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree)
    (hd : delta = 0 ∨ 7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree)
    (hz : zeta  = 0 ∨ 9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree)
    (ht : theta = 0 ∨ 7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree) :
    (degreeZeroKappaCubicNoSigmaBCDE610 0 alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hCne, hDne, hEne, heq1, heq2, heq3⟩
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
  have htieBE : 12 * A.natDegree + 6 * B.natDegree =
      9 * A.natDegree + 4 * E.natDegree := heq3
  have eqC : 2 * C.natDegree = A.natDegree + 2 * B.natDegree := by omega
  have eqD : 4 * D.natDegree = A.natDegree + 6 * B.natDegree := by omega
  have eqE : 4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree := by omega

  rcases hb with rfl | hb <;> rcases hd with rfl | hd <;>
    rcases hz with rfl | hz <;> rcases ht with rfl | ht <;>
      (simp only [degreeZeroKappaCubicNoSigmaBCDE610, hpow2, hpow3, hpow4, hpow5,
                  zero_mul, mul_zero, zero_smul, smul_zero,
                  add_zero, zero_add, zero_pow, Nat.succ_ne_zero,
                  sub_zero, neg_zero, natDegree_zero];
       compute_degree; omega)


set_option maxHeartbeats 64000000 in
theorem degreeZeroLambdaCubicNoSigmaBCDE610_natDegree_lt_of_loadCone
    (alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeBCDE610 A B C D E)
    (hb : beta  = 0 ∨ 7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree)
    (hd : delta = 0 ∨ 7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree)
    (hz : zeta  = 0 ∨ 9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree)
    (ht : theta = 0 ∨ 7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree) :
    (degreeZeroLambdaCubicNoSigmaBCDE610 0 alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      A.natDegree + 2 * B.natDegree + C.natDegree := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hCne, hDne, hEne, heq1, heq2, heq3⟩
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
  have htieBE : 12 * A.natDegree + 6 * B.natDegree =
      9 * A.natDegree + 4 * E.natDegree := heq3
  have eqC : 2 * C.natDegree = A.natDegree + 2 * B.natDegree := by omega
  have eqD : 4 * D.natDegree = A.natDegree + 6 * B.natDegree := by omega
  have eqE : 4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree := by omega

  rcases hb with rfl | hb <;> rcases hd with rfl | hd <;>
    rcases hz with rfl | hz <;> rcases ht with rfl | ht <;>
      (simp only [degreeZeroLambdaCubicNoSigmaBCDE610, hpow2, hpow3, hpow4, hpow5,
                  zero_mul, mul_zero, zero_smul, smul_zero,
                  add_zero, zero_add, zero_pow, Nat.succ_ne_zero,
                  sub_zero, neg_zero, natDegree_zero];
       compute_degree; omega)


set_option maxHeartbeats 64000000 in
theorem degreeZeroOmicronCubicNoSigmaBCDE610_natDegree_lt_of_loadCone
    (alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeBCDE610 A B C D E)
    (hb : beta  = 0 ∨ 7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree)
    (hd : delta = 0 ∨ 7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree)
    (hz : zeta  = 0 ∨ 9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree)
    (ht : theta = 0 ∨ 7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree) :
    (degreeZeroOmicronCubicNoSigmaBCDE610 0 alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      A.natDegree + 2 * B.natDegree + E.natDegree := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hCne, hDne, hEne, heq1, heq2, heq3⟩
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
  have htieBE : 12 * A.natDegree + 6 * B.natDegree =
      9 * A.natDegree + 4 * E.natDegree := heq3
  have eqC : 2 * C.natDegree = A.natDegree + 2 * B.natDegree := by omega
  have eqD : 4 * D.natDegree = A.natDegree + 6 * B.natDegree := by omega
  have eqE : 4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree := by omega

  rcases hb with rfl | hb <;> rcases hd with rfl | hd <;>
    rcases hz with rfl | hz <;> rcases ht with rfl | ht <;>
      (simp only [degreeZeroOmicronCubicNoSigmaBCDE610, hpow2, hpow3, hpow4, hpow5,
                  zero_mul, mul_zero, zero_smul, smul_zero,
                  add_zero, zero_add, zero_pow, Nat.succ_ne_zero,
                  sub_zero, neg_zero, natDegree_zero];
       compute_degree; omega)


set_option maxHeartbeats 64000000 in
theorem degreeZeroN1CubicNoSigmaBCDENoL610_natDegree_lt_of_loadCone
    (alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeBCDE610 A B C D E)
    (hb : beta  = 0 ∨ 7 * (9 * A.natDegree) < 18 * A.natDegree + 42 * B.natDegree)
    (hd : delta = 0 ∨ 7 * (9 * A.natDegree) < 30 * A.natDegree + 42 * B.natDegree)
    (hz : zeta  = 0 ∨ 9 * A.natDegree < 6 * A.natDegree + 6 * B.natDegree)
    (ht : theta = 0 ∨ 7 * (9 * A.natDegree) < 54 * A.natDegree + 42 * B.natDegree) :
    (degreeZeroN1CubicNoSigmaBCDENoL610 0 alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      A.natDegree + 2 * B.natDegree + D.natDegree := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hCne, hDne, hEne, heq1, heq2, heq3⟩
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
  have htieBE : 12 * A.natDegree + 6 * B.natDegree =
      9 * A.natDegree + 4 * E.natDegree := heq3
  have eqC : 2 * C.natDegree = A.natDegree + 2 * B.natDegree := by omega
  have eqD : 4 * D.natDegree = A.natDegree + 6 * B.natDegree := by omega
  have eqE : 4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree := by omega

  rcases hb with rfl | hb <;> rcases hd with rfl | hd <;>
    rcases hz with rfl | hz <;> rcases ht with rfl | ht <;>
      (simp only [degreeZeroN1CubicNoSigmaBCDENoL610, hpow2, hpow3, hpow4, hpow5,
                  zero_mul, mul_zero, zero_smul, smul_zero,
                  add_zero, zero_add, zero_pow, Nat.succ_ne_zero,
                  sub_zero, neg_zero, natDegree_zero];
       compute_degree; omega)

end CubicLoadSigmaBCDERest610


/-! ## `{B,C}` coefficient extraction and identity kill -/

section CubicLoadSigmaBCKill610

variable {k : Type*} [Field k] [CharZero k]

theorem kappaCubicSigmaFaceBC610_coeff_top_of_loadCone
    {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeBC610 A B C D E)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0) :
    (kappaCubicSigmaFaceBC610 A B C D E).coeff (A.natDegree + 3 * B.natDegree) =
      (1 / 243 : k) * kappaCubicSigmaInnerBC610 A.leadingCoeff B.leadingCoeff
        C.leadingCoeff := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    _, _, heq, _⟩
  have htie : A.natDegree + 2 * B.natDegree = 2 * C.natDegree := by omega
  simp only [kappaCubicSigmaFaceBC610, kappaCubicSigmaInnerBC610, coeff_add,
    coeff_sub, coeff_smul, smul_eq_mul]
  have hdeg_AB3 : ((A * B ^ 3)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 3 hBne), natDegree_pow]
  have hcf_AB3 : ((A * B ^ 3)).coeff (A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 3 := by
    rw [← hdeg_AB3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BC2 : ((B * C ^ 2)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hCne), natDegree_pow]
    omega
  have hcf_BC2 : ((B * C ^ 2)).coeff (A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hdeg_BC2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  rw [hcf_AB3, hcf_BC2]
  ring

theorem lambdaCubicSigmaFaceBC610_coeff_top_of_loadCone
    {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeBC610 A B C D E)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0) :
    (lambdaCubicSigmaFaceBC610 A B C D E).coeff
        (A.natDegree + 2 * B.natDegree + C.natDegree) =
      (1 / 81 : k) * lambdaCubicSigmaInnerBC610 A.leadingCoeff B.leadingCoeff
        C.leadingCoeff := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    _, _, heq, _⟩
  have htie : A.natDegree + 2 * B.natDegree = 2 * C.natDegree := by omega
  simp only [lambdaCubicSigmaFaceBC610, lambdaCubicSigmaInnerBC610, coeff_add,
    coeff_sub, coeff_smul, smul_eq_mul]
  have hdeg_AB2C : ((A * B ^ 2 * C)).natDegree =
      A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hCne,
      natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow]
  have hcf_AB2C : ((A * B ^ 2 * C)).coeff
        (A.natDegree + 2 * B.natDegree + C.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff := by
    rw [← hdeg_AB2C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul,
      leadingCoeff_pow]
  have hdeg_C3 : (C ^ 3).natDegree =
      A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_C3 : (C ^ 3).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      C.leadingCoeff ^ 3 := by
    rw [← hdeg_C3, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_AB2C, hcf_C3]
  ring

set_option maxHeartbeats 64000000 in
theorem cubicLoadSigmaCone_BC_impossible {j t : k}
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeBC610 A B C D E)
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
    (hlam : (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree = 0)
    (hkap : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree = 0) :
    False := by
  subst hl
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, _⟩
    omega
  have hBne : B ≠ 0 := by
    rcases hcone with ⟨_, hBne, hCne, heq, hDcmp, hEcmp⟩
    exact hBne
  have hCne : C ≠ 0 := by
    rcases hcone with ⟨_, hBne, hCne, heq, hDcmp, hEcmp⟩
    exact hCne
  have hb : beta = 0 ∨ 7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree :=
    cubicLoadSigmaConeBC610_specialize_beta hcone hb4
  have hd : delta = 0 ∨ 7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree :=
    cubicLoadSigmaConeBC610_specialize_delta hcone hd4
  have hz : zeta = 0 ∨ 9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree :=
    cubicLoadSigmaConeBC610_specialize_zeta hcone hz4
  have ht : theta = 0 ∨ 7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree :=
    cubicLoadSigmaConeBC610_specialize_theta hcone ht4
  have hkappainner :
      kappaCubicSigmaInnerBC610 A.leadingCoeff B.leadingCoeff C.leadingCoeff = 0 := by
    have hrest :=
      degreeZeroKappaCubicNoSigmaBC610_natDegree_lt_of_loadCone alpha beta
        delta epsilon zeta eta theta A B C D E hcone hb hd hz ht
    have hct := kappaCubicSigmaFaceBC610_coeff_top_of_loadCone
      (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne)
    have hz0 : (degreeZeroKappaCubic610 0 alpha beta delta epsilon zeta eta
          theta A B C D E).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hkap]
      rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, _⟩
      omega
    rw [degreeZeroKappaCubic610_eq_sigmaBC_add_rest, coeff_add,
      coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz0
    have hden : (1 / 243 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz0)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hlambdainner :
      lambdaCubicSigmaInnerBC610 A.leadingCoeff B.leadingCoeff C.leadingCoeff = 0 := by
    have hrest :=
      degreeZeroLambdaCubicNoSigmaBC610_natDegree_lt_of_loadCone alpha beta
        delta epsilon zeta eta theta A B C D E hcone hb hd hz ht
    have hct := lambdaCubicSigmaFaceBC610_coeff_top_of_loadCone
      (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne)
    have hz0 : (degreeZeroLambdaCubic610 0 alpha beta delta epsilon zeta eta
          theta A B C D E).coeff
        (A.natDegree + 2 * B.natDegree + C.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hlam]
      rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
        _, _, heq, _⟩
      omega
    rw [degreeZeroLambdaCubic610_eq_sigmaBC_add_rest, coeff_add,
      coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz0
    have hden : (1 / 81 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz0)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hid := cubicSigmaInner_BC_identity A.leadingCoeff B.leadingCoeff
      C.leadingCoeff
  have hpow : C.leadingCoeff ^ 5 = 0 := by
    rw [hkappainner, hlambdainner] at hid
    simpa using hid.symm
  have hlc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  exact hlc ((pow_eq_zero_iff (by decide : (5 : ℕ) ≠ 0)).mp hpow)

end CubicLoadSigmaBCKill610


/-! ## `{B,C,E}` coefficient extraction and identity kill -/

section CubicLoadSigmaBCEKill610

variable {k : Type*} [Field k] [CharZero k]

theorem kappaCubicSigmaFaceBCE610_coeff_top_of_loadCone
    {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeBCE610 A B C D E)
    (hAne : A ≠ 0) (hBne : B ≠ 0) (hCne : C ≠ 0) :
    (kappaCubicSigmaFaceBCE610 A B C D E).coeff (A.natDegree + 3 * B.natDegree) =
      (1 / 243 : k) * kappaCubicSigmaInnerBCE610 A.leadingCoeff B.leadingCoeff
        C.leadingCoeff E.leadingCoeff := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    _, _, _, heq1, heq2, _⟩
  have htie : A.natDegree + 2 * B.natDegree = 2 * C.natDegree := by omega
  simp only [kappaCubicSigmaFaceBCE610, kappaCubicSigmaInnerBCE610, coeff_add,
    coeff_sub, coeff_smul, smul_eq_mul]
  have hdeg_AB3 : ((A * B ^ 3)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 3 hBne), natDegree_pow]
  have hcf_AB3 : ((A * B ^ 3)).coeff (A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 3 := by
    rw [← hdeg_AB3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BC2 : ((B * C ^ 2)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hCne), natDegree_pow]
    omega
  have hcf_BC2 : ((B * C ^ 2)).coeff (A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hdeg_BC2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  rw [hcf_AB3, hcf_BC2]
  ring

theorem lambdaCubicSigmaFaceBCE610_coeff_top_of_loadCone
    {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeBCE610 A B C D E)
    (hAne : A ≠ 0) (hBne : B ≠ 0) (hCne : C ≠ 0) (hEne : E ≠ 0) :
    (lambdaCubicSigmaFaceBCE610 A B C D E).coeff
        (A.natDegree + 2 * B.natDegree + C.natDegree) =
      (1 / 81 : k) * lambdaCubicSigmaInnerBCE610 A.leadingCoeff B.leadingCoeff
        C.leadingCoeff E.leadingCoeff := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    _, _, _, heq1, heq2, _⟩
  have htie : A.natDegree + 2 * B.natDegree = 2 * C.natDegree := by omega
  have htieE : 3 * A.natDegree + 6 * B.natDegree = 4 * E.natDegree := by omega
  simp only [lambdaCubicSigmaFaceBCE610, lambdaCubicSigmaInnerBCE610, coeff_add,
    coeff_sub, coeff_smul, smul_eq_mul]
  have hdeg_AB2C : ((A * B ^ 2 * C)).natDegree =
      A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hCne,
      natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow]
  have hcf_AB2C : ((A * B ^ 2 * C)).coeff
        (A.natDegree + 2 * B.natDegree + C.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff := by
    rw [← hdeg_AB2C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul,
      leadingCoeff_pow]
  have hdeg_C3 : (C ^ 3).natDegree =
      A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_C3 : (C ^ 3).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      C.leadingCoeff ^ 3 := by
    rw [← hdeg_C3, coeff_natDegree, leadingCoeff_pow]
  have hdeg_E2 : (E ^ 2).natDegree =
      A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_E2 : (E ^ 2).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      E.leadingCoeff ^ 2 := by
    rw [← hdeg_E2, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_AB2C, hcf_C3, hcf_E2]
  ring

theorem omicronCubicSigmaFaceBCE610_coeff_top_of_loadCone
    {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeBCE610 A B C D E)
    (hAne : A ≠ 0) (hBne : B ≠ 0) (hCne : C ≠ 0) (hEne : E ≠ 0) :
    (omicronCubicSigmaFaceBCE610 A B C D E).coeff
        (A.natDegree + 2 * B.natDegree + E.natDegree) =
      (1 / 81 : k) * omicronCubicSigmaInnerBCE610 A.leadingCoeff B.leadingCoeff
        C.leadingCoeff E.leadingCoeff := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    _, _, _, heq1, heq2, _⟩
  have htie : A.natDegree + 2 * B.natDegree = 2 * C.natDegree := by omega
  have htieE : 3 * A.natDegree + 6 * B.natDegree = 4 * E.natDegree := by omega
  simp only [omicronCubicSigmaFaceBCE610, omicronCubicSigmaInnerBCE610, coeff_add,
    coeff_sub, coeff_smul, smul_eq_mul]
  have hdeg_AB2E : ((A * B ^ 2 * E)).natDegree =
      A.natDegree + 2 * B.natDegree + E.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hEne,
      natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow]
  have hcf_AB2E : ((A * B ^ 2 * E)).coeff
        (A.natDegree + 2 * B.natDegree + E.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hdeg_AB2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul,
      leadingCoeff_pow]
  have hdeg_C2E : ((C ^ 2 * E)).natDegree =
      A.natDegree + 2 * B.natDegree + E.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hEne, natDegree_pow]
    omega
  have hcf_C2E : ((C ^ 2 * E)).coeff
        (A.natDegree + 2 * B.natDegree + E.natDegree) =
      C.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hdeg_C2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  rw [hcf_AB2E, hcf_C2E]
  ring

set_option maxHeartbeats 64000000 in
theorem cubicLoadSigmaCone_BCE_impossible {j t : k}
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeBCE610 A B C D E)
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
    (hlam : (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree = 0)
    (hkap : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree = 0)
    (homi : (degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree = 0) :
    False := by
  subst hl
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, _⟩
    omega
  have hBne : B ≠ 0 := by
    rcases hcone with ⟨_, hBne, hCne, hEne, heq1, heq2, hDcmp⟩
    exact hBne
  have hCne : C ≠ 0 := by
    rcases hcone with ⟨_, hBne, hCne, hEne, heq1, heq2, hDcmp⟩
    exact hCne
  have hEne : E ≠ 0 := by
    rcases hcone with ⟨_, hBne, hCne, hEne, heq1, heq2, hDcmp⟩
    exact hEne
  have hb : beta = 0 ∨ 7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree :=
    cubicLoadSigmaConeBCE610_specialize_beta hcone hb4
  have hd : delta = 0 ∨ 7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree :=
    cubicLoadSigmaConeBCE610_specialize_delta hcone hd4
  have hz : zeta = 0 ∨ 9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree :=
    cubicLoadSigmaConeBCE610_specialize_zeta hcone hz4
  have ht : theta = 0 ∨ 7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree :=
    cubicLoadSigmaConeBCE610_specialize_theta hcone ht4
  have hkappainner :
      kappaCubicSigmaInnerBCE610 A.leadingCoeff B.leadingCoeff C.leadingCoeff
        E.leadingCoeff = 0 := by
    have hrest :=
      degreeZeroKappaCubicNoSigmaBCE610_natDegree_lt_of_loadCone alpha beta
        delta epsilon zeta eta theta A B C D E hcone hb hd hz ht
    have hct := kappaCubicSigmaFaceBCE610_coeff_top_of_loadCone
      (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne)
    have hz0 : (degreeZeroKappaCubic610 0 alpha beta delta epsilon zeta eta
          theta A B C D E).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hkap]
      rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, _⟩
      omega
    rw [degreeZeroKappaCubic610_eq_sigmaBCE_add_rest, coeff_add,
      coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz0
    have hden : (1 / 243 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz0)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hlambdainner :
      lambdaCubicSigmaInnerBCE610 A.leadingCoeff B.leadingCoeff C.leadingCoeff
        E.leadingCoeff = 0 := by
    have hrest :=
      degreeZeroLambdaCubicNoSigmaBCE610_natDegree_lt_of_loadCone alpha beta
        delta epsilon zeta eta theta A B C D E hcone hb hd hz ht
    have hct := lambdaCubicSigmaFaceBCE610_coeff_top_of_loadCone
      (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hEne := hEne)
    have hz0 : (degreeZeroLambdaCubic610 0 alpha beta delta epsilon zeta eta
          theta A B C D E).coeff
        (A.natDegree + 2 * B.natDegree + C.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hlam]
      rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
        _, _, _, heq1, heq2, _⟩
      omega
    rw [degreeZeroLambdaCubic610_eq_sigmaBCE_add_rest, coeff_add,
      coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz0
    have hden : (1 / 81 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz0)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have homicroninner :
      omicronCubicSigmaInnerBCE610 A.leadingCoeff B.leadingCoeff C.leadingCoeff
        E.leadingCoeff = 0 := by
    have hrest :=
      degreeZeroOmicronCubicNoSigmaBCE610_natDegree_lt_of_loadCone alpha beta
        delta epsilon zeta eta theta A B C D E hcone hb hd hz ht
    have hct := omicronCubicSigmaFaceBCE610_coeff_top_of_loadCone
      (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hEne := hEne)
    have hz0 : (degreeZeroOmicronCubic610 0 alpha beta delta epsilon zeta eta
          theta A B C D E).coeff
        (A.natDegree + 2 * B.natDegree + E.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [homi]
      rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
        _, _, _, heq1, heq2, _⟩
      omega
    rw [degreeZeroOmicronCubic610_eq_sigmaBCE_add_rest, coeff_add,
      coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz0
    have hden : (1 / 81 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz0)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hid := cubicSigmaInner_BCE_identity A.leadingCoeff B.leadingCoeff
      C.leadingCoeff E.leadingCoeff
  have hpow : C.leadingCoeff ^ 7 = 0 := by
    rw [hkappainner, hlambdainner, homicroninner] at hid
    simpa using hid.symm
  have hlc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  exact hlc ((pow_eq_zero_iff (by decide : (7 : ℕ) ≠ 0)).mp hpow)

end CubicLoadSigmaBCEKill610
/-! ## `{B,C,D,E}` coefficient extraction and identity kill -/

section CubicLoadSigmaBCDEKill610

variable {k : Type*} [Field k] [CharZero k]

theorem kappaCubicSigmaFaceBCDE610_coeff_top_of_loadCone
    {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeBCDE610 A B C D E)
    (hAne : A ≠ 0) (hBne : B ≠ 0) (hCne : C ≠ 0) (hDne : D ≠ 0)
    (hEne : E ≠ 0) :
    (kappaCubicSigmaFaceBCDE610 A B C D E).coeff (A.natDegree + 3 * B.natDegree) =
      (5 / 243 : k) * kappaCubicSigmaInnerBCDE610 A.leadingCoeff B.leadingCoeff
        C.leadingCoeff D.leadingCoeff E.leadingCoeff := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    _, _, _, _, heq1, heq2, heq3⟩
  have eqC : 2 * C.natDegree = A.natDegree + 2 * B.natDegree := by omega
  have eqD : 4 * D.natDegree = A.natDegree + 6 * B.natDegree := by omega
  have eqE : 4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree := by omega
  simp only [kappaCubicSigmaFaceBCDE610, kappaCubicSigmaInnerBCDE610, coeff_add,
    coeff_sub, coeff_smul, smul_eq_mul]
  have hdeg_AB3 : ((A * B ^ 3)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 3 hBne), natDegree_pow]
  have hcf_AB3 : ((A * B ^ 3)).coeff (A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 3 := by
    rw [← hdeg_AB3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BC2 : ((B * C ^ 2)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hCne), natDegree_pow]
    omega
  have hcf_BC2 : ((B * C ^ 2)).coeff (A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hdeg_BC2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_DE : ((D * E)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hDne hEne]
    omega
  have hcf_DE : ((D * E)).coeff (A.natDegree + 3 * B.natDegree) =
      D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_DE, coeff_natDegree, leadingCoeff_mul]
  rw [hcf_AB3, hcf_BC2, hcf_DE]
  ring

theorem lambdaCubicSigmaFaceBCDE610_coeff_top_of_loadCone
    {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeBCDE610 A B C D E)
    (hAne : A ≠ 0) (hBne : B ≠ 0) (hCne : C ≠ 0) (hDne : D ≠ 0)
    (hEne : E ≠ 0) :
    (lambdaCubicSigmaFaceBCDE610 A B C D E).coeff
        (A.natDegree + 2 * B.natDegree + C.natDegree) =
      (5 / 81 : k) * lambdaCubicSigmaInnerBCDE610 A.leadingCoeff B.leadingCoeff
        C.leadingCoeff D.leadingCoeff E.leadingCoeff := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    _, _, _, _, heq1, heq2, heq3⟩
  have eqC : 2 * C.natDegree = A.natDegree + 2 * B.natDegree := by omega
  have eqD : 4 * D.natDegree = A.natDegree + 6 * B.natDegree := by omega
  have eqE : 4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree := by omega
  simp only [lambdaCubicSigmaFaceBCDE610, lambdaCubicSigmaInnerBCDE610, coeff_add,
    coeff_sub, coeff_smul, smul_eq_mul]
  have hdeg_AB2C : ((A * B ^ 2 * C)).natDegree =
      A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hCne,
      natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow]
  have hcf_AB2C : ((A * B ^ 2 * C)).coeff
        (A.natDegree + 2 * B.natDegree + C.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff := by
    rw [← hdeg_AB2C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul,
      leadingCoeff_pow]
  have hdeg_AD2 : ((A * D ^ 2)).natDegree =
      A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 2 hDne), natDegree_pow]
    omega
  have hcf_AD2 : ((A * D ^ 2)).coeff
        (A.natDegree + 2 * B.natDegree + C.natDegree) =
      A.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_AD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_C3 : (C ^ 3).natDegree =
      A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_C3 : (C ^ 3).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      C.leadingCoeff ^ 3 := by
    rw [← hdeg_C3, coeff_natDegree, leadingCoeff_pow]
  have hdeg_E2 : (E ^ 2).natDegree =
      A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_E2 : (E ^ 2).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      E.leadingCoeff ^ 2 := by
    rw [← hdeg_E2, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_AB2C, hcf_AD2, hcf_C3, hcf_E2]
  ring

theorem omicronCubicSigmaFaceBCDE610_coeff_top_of_loadCone
    {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeBCDE610 A B C D E)
    (hAne : A ≠ 0) (hBne : B ≠ 0) (hCne : C ≠ 0) (hDne : D ≠ 0)
    (hEne : E ≠ 0) :
    (omicronCubicSigmaFaceBCDE610 A B C D E).coeff
        (A.natDegree + 2 * B.natDegree + E.natDegree) =
      (5 / 81 : k) * omicronCubicSigmaInnerBCDE610 A.leadingCoeff B.leadingCoeff
        C.leadingCoeff D.leadingCoeff E.leadingCoeff := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    _, _, _, _, heq1, heq2, heq3⟩
  have eqC : 2 * C.natDegree = A.natDegree + 2 * B.natDegree := by omega
  have eqD : 4 * D.natDegree = A.natDegree + 6 * B.natDegree := by omega
  have eqE : 4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree := by omega
  simp only [omicronCubicSigmaFaceBCDE610, omicronCubicSigmaInnerBCDE610, coeff_add,
    coeff_sub, coeff_smul, smul_eq_mul]
  have hdeg_AB2E : ((A * B ^ 2 * E)).natDegree =
      A.natDegree + 2 * B.natDegree + E.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hEne,
      natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow]
  have hcf_AB2E : ((A * B ^ 2 * E)).coeff
        (A.natDegree + 2 * B.natDegree + E.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hdeg_AB2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul,
      leadingCoeff_pow]
  have hdeg_ABCD : ((A * B * C * D)).natDegree =
      A.natDegree + 2 * B.natDegree + E.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hAne hBne) hCne) hDne,
      natDegree_mul (mul_ne_zero hAne hBne) hCne, natDegree_mul hAne hBne]
    omega
  have hcf_ABCD : ((A * B * C * D)).coeff
        (A.natDegree + 2 * B.natDegree + E.natDegree) =
      A.leadingCoeff * B.leadingCoeff * C.leadingCoeff * D.leadingCoeff := by
    rw [← hdeg_ABCD, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul,
      leadingCoeff_mul]
  have hdeg_C2E : ((C ^ 2 * E)).natDegree =
      A.natDegree + 2 * B.natDegree + E.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hEne, natDegree_pow]
    omega
  have hcf_C2E : ((C ^ 2 * E)).coeff
        (A.natDegree + 2 * B.natDegree + E.natDegree) =
      C.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hdeg_C2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  rw [hcf_AB2E, hcf_ABCD, hcf_C2E]
  ring

theorem n1CubicSigmaFaceBCDE610_coeff_top_of_loadCone
    {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeBCDE610 A B C D E)
    (hAne : A ≠ 0) (hBne : B ≠ 0) (hCne : C ≠ 0) (hDne : D ≠ 0)
    (hEne : E ≠ 0) :
    (n1CubicSigmaFaceBCDE610 A B C D E).coeff
        (A.natDegree + 2 * B.natDegree + D.natDegree) =
      (5 / 81 : k) * n1CubicSigmaInnerBCDE610 A.leadingCoeff B.leadingCoeff
        C.leadingCoeff D.leadingCoeff E.leadingCoeff := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    _, _, _, _, heq1, heq2, heq3⟩
  have eqC : 2 * C.natDegree = A.natDegree + 2 * B.natDegree := by omega
  have eqD : 4 * D.natDegree = A.natDegree + 6 * B.natDegree := by omega
  have eqE : 4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree := by omega
  simp only [n1CubicSigmaFaceBCDE610, n1CubicSigmaInnerBCDE610, coeff_add,
    coeff_sub, coeff_smul, smul_eq_mul]
  have hdeg_AB2D : ((A * B ^ 2 * D)).natDegree =
      A.natDegree + 2 * B.natDegree + D.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hDne,
      natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow]
  have hcf_AB2D : ((A * B ^ 2 * D)).coeff
        (A.natDegree + 2 * B.natDegree + D.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_AB2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul,
      leadingCoeff_pow]
  have hdeg_BCE : ((B * C * E)).natDegree =
      A.natDegree + 2 * B.natDegree + D.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hCne) hEne, natDegree_mul hBne hCne]
    omega
  have hcf_BCE : ((B * C * E)).coeff
        (A.natDegree + 2 * B.natDegree + D.natDegree) =
      B.leadingCoeff * C.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_BCE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_C2D : ((C ^ 2 * D)).natDegree =
      A.natDegree + 2 * B.natDegree + D.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hDne, natDegree_pow]
    omega
  have hcf_C2D : ((C ^ 2 * D)).coeff
        (A.natDegree + 2 * B.natDegree + D.natDegree) =
      C.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_C2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  rw [hcf_AB2D, hcf_BCE, hcf_C2D]
  ring

set_option maxHeartbeats 64000000 in
/-- Off-wall N₁ + κ + λ + ο identity kill.  Strict N₁ bands so the odd
pure-`A` columns stay below the σ-7 face. -/
theorem cubicLoadSigmaCone_BCDE_offWall_impossible {j t : k}
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeBCDE610 A B C D E)
    (hl : l = 0)
    (hb : beta  = 0 ∨ 7 * (9 * A.natDegree) < 18 * A.natDegree + 42 * B.natDegree)
    (hd : delta = 0 ∨ 7 * (9 * A.natDegree) < 30 * A.natDegree + 42 * B.natDegree)
    (hz : zeta  = 0 ∨ 9 * A.natDegree < 6 * A.natDegree + 6 * B.natDegree)
    (ht : theta = 0 ∨ 7 * (9 * A.natDegree) < 54 * A.natDegree + 42 * B.natDegree)
    (hlam : (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree = 0)
    (hkap : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree = 0)
    (hmu : (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta
          theta A B C D E).natDegree = 0)
    (homi : (degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree = 0) :
    False := by
  subst hl
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, _⟩
    omega
  have hBne : B ≠ 0 := by
    rcases hcone with ⟨_, hBne, hCne, hDne, hEne, heq1, heq2, heq3⟩
    exact hBne
  have hCne : C ≠ 0 := by
    rcases hcone with ⟨_, hBne, hCne, hDne, hEne, heq1, heq2, heq3⟩
    exact hCne
  have hDne : D ≠ 0 := by
    rcases hcone with ⟨_, hBne, hCne, hDne, hEne, heq1, heq2, heq3⟩
    exact hDne
  have hEne : E ≠ 0 := by
    rcases hcone with ⟨_, hBne, hCne, hDne, hEne, heq1, heq2, heq3⟩
    exact hEne
  -- κ/λ/ο rest bounds use non-strict specialised bands; strict implies ≤.
  have hbLe : beta = 0 ∨
      7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree := by
    rcases hb with h | h
    · exact Or.inl h
    · exact Or.inr (le_of_lt h)
  have hdLe : delta = 0 ∨
      7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree := by
    rcases hd with h | h
    · exact Or.inl h
    · exact Or.inr (le_of_lt h)
  have hzLe : zeta = 0 ∨
      9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree := by
    rcases hz with h | h
    · exact Or.inl h
    · exact Or.inr (le_of_lt h)
  have htLe : theta = 0 ∨
      7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree := by
    rcases ht with h | h
    · exact Or.inl h
    · exact Or.inr (le_of_lt h)
  have hG1 :
      kappaCubicSigmaInnerBCDE610 A.leadingCoeff B.leadingCoeff C.leadingCoeff
        D.leadingCoeff E.leadingCoeff = 0 := by
    have hrest :=
      degreeZeroKappaCubicNoSigmaBCDE610_natDegree_lt_of_loadCone alpha beta
        delta epsilon zeta eta theta A B C D E hcone hbLe hdLe hzLe htLe
    have hct := kappaCubicSigmaFaceBCDE610_coeff_top_of_loadCone
      (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne)
      (hDne := hDne) (hEne := hEne)
    have hz0 : (degreeZeroKappaCubic610 0 alpha beta delta epsilon zeta eta
          theta A B C D E).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hkap]
      rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, _⟩
      omega
    rw [degreeZeroKappaCubic610_eq_sigmaBCDE_add_rest, coeff_add,
      coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz0
    have hden : (5 / 243 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz0)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hG2 :
      lambdaCubicSigmaInnerBCDE610 A.leadingCoeff B.leadingCoeff C.leadingCoeff
        D.leadingCoeff E.leadingCoeff = 0 := by
    have hrest :=
      degreeZeroLambdaCubicNoSigmaBCDE610_natDegree_lt_of_loadCone alpha beta
        delta epsilon zeta eta theta A B C D E hcone hbLe hdLe hzLe htLe
    have hct := lambdaCubicSigmaFaceBCDE610_coeff_top_of_loadCone
      (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne)
      (hDne := hDne) (hEne := hEne)
    have hz0 : (degreeZeroLambdaCubic610 0 alpha beta delta epsilon zeta eta
          theta A B C D E).coeff
        (A.natDegree + 2 * B.natDegree + C.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hlam]
      rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
        _, _, _, _, heq1, heq2, heq3⟩
      omega
    rw [degreeZeroLambdaCubic610_eq_sigmaBCDE_add_rest, coeff_add,
      coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz0
    have hden : (5 / 81 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz0)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hG3 :
      omicronCubicSigmaInnerBCDE610 A.leadingCoeff B.leadingCoeff C.leadingCoeff
        D.leadingCoeff E.leadingCoeff = 0 := by
    have hrest :=
      degreeZeroOmicronCubicNoSigmaBCDE610_natDegree_lt_of_loadCone alpha beta
        delta epsilon zeta eta theta A B C D E hcone hbLe hdLe hzLe htLe
    have hct := omicronCubicSigmaFaceBCDE610_coeff_top_of_loadCone
      (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne)
      (hDne := hDne) (hEne := hEne)
    have hz0 : (degreeZeroOmicronCubic610 0 alpha beta delta epsilon zeta eta
          theta A B C D E).coeff
        (A.natDegree + 2 * B.natDegree + E.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [homi]
      rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
        _, _, _, _, heq1, heq2, heq3⟩
      omega
    rw [degreeZeroOmicronCubic610_eq_sigmaBCDE_add_rest, coeff_add,
      coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz0
    have hden : (5 / 81 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz0)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hG4 :
      n1CubicSigmaInnerBCDE610 A.leadingCoeff B.leadingCoeff C.leadingCoeff
        D.leadingCoeff E.leadingCoeff = 0 := by
    have hN1le := degreeZeroN1Cubic610_natDegree_le 0 alpha beta delta epsilon
        zeta eta theta A B C D E hmu hkap
    have hΔ : A.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree := by
      rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
        _, _, _, _, heq1, heq2, heq3⟩
      omega
    have hrest :=
      degreeZeroN1CubicNoSigmaBCDENoL610_natDegree_lt_of_loadCone alpha beta
        delta epsilon zeta eta theta A B C D E hcone hb hd hz ht
    have hz0 : (degreeZeroN1Cubic610 0 alpha beta delta epsilon zeta eta theta
          A B C D E).coeff
        (A.natDegree + 2 * B.natDegree + D.natDegree) = 0 :=
      coeff_eq_zero_of_natDegree_lt (hN1le.trans_lt hΔ)
    rw [degreeZeroN1Cubic610_eq_sigmaBCDE_add_rest,
      degreeZeroN1CubicNoSigmaBCDE610_eq_L_add_rest, coeff_add, coeff_add] at hz0
    have hsmall :
        (degreeZeroN1CubicNoSigmaBCDENoL610 0 alpha beta delta epsilon zeta
            eta theta A B C D E).coeff
          (A.natDegree + 2 * B.natDegree + D.natDegree) = 0 :=
      coeff_eq_zero_of_natDegree_lt hrest
    have hL0 : (n1CubicLFace610 0 A).coeff
        (A.natDegree + 2 * B.natDegree + D.natDegree) = 0 := by
      simp only [n1CubicLFace610, mul_zero, zero_smul, coeff_zero]
    rw [hsmall, hL0, add_zero, add_zero] at hz0
    have hct := n1CubicSigmaFaceBCDE610_coeff_top_of_loadCone
      (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne)
      (hDne := hDne) (hEne := hEne)
    have hden : (5 / 81 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz0)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hid := cubicSigmaInner_BCDE_identity A.leadingCoeff B.leadingCoeff
      C.leadingCoeff D.leadingCoeff E.leadingCoeff
  have hpow : E.leadingCoeff ^ 5 = 0 := by
    rw [hG1, hG2, hG3, hG4] at hid
    simpa using hid.symm
  have hlc : E.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hEne
  exact hlc ((pow_eq_zero_iff (by decide : (5 : ℕ) ≠ 0)).mp hpow)

end CubicLoadSigmaBCDEKill610


/-! ## `{C,D}` chamber `2c+d ≤ a` and odd-column walls -/

section CubicLoadSigmaCDFinish610

variable {k : Type*} [Field k] [CharZero k]

/-- On the CD cone, `2c+d ≤ a` forces the polynomial `B` to vanish. -/
theorem cubicLoadSigmaConeCD610_B_eq_zero_of_chamber
    {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hTle : 2 * C.natDegree + D.natDegree ≤ A.natDegree) :
    B = 0 := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hCne, hDne, heq, hBcmp, hEcmp⟩
  rcases hBcmp with hB0 | hBlt
  · exact hB0
  · have : 2 * C.natDegree ≤ A.natDegree :=
      le_trans (Nat.le_add_right _ _) hTle
    omega

/-- Chamber `2c+d ≤ a` implies `7c ≤ 3a`. -/
theorem cubicLoadSigmaConeCD610_chamber_seven_c_le
    {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hTle : 2 * C.natDegree + D.natDegree ≤ A.natDegree) :
    7 * C.natDegree ≤ 3 * A.natDegree := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hCne, hDne, heq, hBcmp, hEcmp⟩
  have hCD : A.natDegree + 2 * D.natDegree = 3 * C.natDegree := by omega
  omega

theorem cubicLoadSigmaConeCD610_chamber_n1BetaTop
    {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hTle : 2 * C.natDegree + D.natDegree ≤ A.natDegree)
    (hB0 : B = 0) :
    cubicN1BetaTop610 A B C D E := by
  rcases hcone with ⟨hload, hCne, hDne, heq, hBcmp, hEcmp⟩
  rcases hload with ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩
  have h7 : 7 * C.natDegree ≤ 3 * A.natDegree :=
    cubicLoadSigmaConeCD610_chamber_seven_c_le
      ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, hCne, hDne, heq,
        hBcmp, hEcmp⟩ hTle
  have hBdeg : B.natDegree = 0 := by simp [hB0]
  refine ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, ?_, ?_, ?_, ?_⟩
  · rw [hBdeg]; omega
  · omega
  · have hCD : A.natDegree + 2 * D.natDegree = 3 * C.natDegree := by omega
    omega
  · rcases hEcmp with hE0 | hElt
    · have hEdeg : E.natDegree = 0 := by simp [hE0]
      rw [hEdeg]; omega
    · omega

theorem cubicLoadSigmaConeCD610_chamber_n1DeltaTop
    {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hTle : 2 * C.natDegree + D.natDegree ≤ A.natDegree)
    (hB0 : B = 0) :
    cubicN1DeltaTop610 A B C D E := by
  rcases hcone with ⟨hload, hCne, hDne, heq, hBcmp, hEcmp⟩
  rcases hload with ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩
  have h7 : 7 * C.natDegree ≤ 3 * A.natDegree :=
    cubicLoadSigmaConeCD610_chamber_seven_c_le
      ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, hCne, hDne, heq,
        hBcmp, hEcmp⟩ hTle
  have hBdeg : B.natDegree = 0 := by simp [hB0]
  refine ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, ?_, ?_, ?_, ?_⟩
  · rw [hBdeg]; omega
  · omega
  · have hCD : A.natDegree + 2 * D.natDegree = 3 * C.natDegree := by omega
    omega
  · rcases hEcmp with hE0 | hElt
    · have hEdeg : E.natDegree = 0 := by simp [hE0]
      rw [hEdeg]; omega
    · omega

theorem cubicLoadSigmaConeCD610_chamber_n1ZetaTop
    {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hTle : 2 * C.natDegree + D.natDegree ≤ A.natDegree)
    (hB0 : B = 0) :
    cubicN1ZetaTop610 A B C D E := by
  rcases hcone with ⟨hload, hCne, hDne, heq, hBcmp, hEcmp⟩
  rcases hload with ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩
  have h7 : 7 * C.natDegree ≤ 3 * A.natDegree :=
    cubicLoadSigmaConeCD610_chamber_seven_c_le
      ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, hCne, hDne, heq,
        hBcmp, hEcmp⟩ hTle
  have hBdeg : B.natDegree = 0 := by simp [hB0]
  refine ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, ?_, ?_, ?_, ?_⟩
  · rw [hBdeg]; omega
  · omega
  · have hCD : A.natDegree + 2 * D.natDegree = 3 * C.natDegree := by omega
    omega
  · rcases hEcmp with hE0 | hElt
    · have hEdeg : E.natDegree = 0 := by simp [hE0]
      rw [hEdeg]; omega
    · omega

theorem cubicLoadSigmaConeCD610_chamber_n1ThetaTop
    {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hTle : 2 * C.natDegree + D.natDegree ≤ A.natDegree)
    (hB0 : B = 0) :
    cubicN1ThetaTop610 A B C D E := by
  rcases hcone with ⟨hload, hCne, hDne, heq, hBcmp, hEcmp⟩
  rcases hload with ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩
  have h7 : 7 * C.natDegree ≤ 3 * A.natDegree :=
    cubicLoadSigmaConeCD610_chamber_seven_c_le
      ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, hCne, hDne, heq,
        hBcmp, hEcmp⟩ hTle
  have hBdeg : B.natDegree = 0 := by simp [hB0]
  refine ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, ?_, ?_, ?_, ?_⟩
  · rw [hBdeg]; omega
  · omega
  · have hCD : A.natDegree + 2 * D.natDegree = 3 * C.natDegree := by omega
    omega
  · rcases hEcmp with hE0 | hElt
    · have hEdeg : E.natDegree = 0 := by simp [hE0]
      rw [hEdeg]; omega
    · omega

def lambdaCubicSigmaInnerCD610 (a c d : k) : k :=
  3 * a * d ^ 2 + c ^ 3

theorem lambdaCubicSigmaFaceCD610_coeff_top_of_loadCone
    {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hAne : A ≠ 0) (hCne : C ≠ 0) (hDne : D ≠ 0) :
    (lambdaCubicSigmaFaceCD610 A B C D E).coeff
        (A.natDegree + 2 * D.natDegree) =
      (-(5 / 81 : k)) * lambdaCubicSigmaInnerCD610 A.leadingCoeff
        C.leadingCoeff D.leadingCoeff := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    _, _, heq, _⟩
  have hCD : A.natDegree + 2 * D.natDegree = 3 * C.natDegree := by omega
  simp only [lambdaCubicSigmaFaceCD610, lambdaCubicSigmaInnerCD610, coeff_add,
    coeff_sub, coeff_smul, smul_eq_mul]
  have hdeg_AD2 : ((A * D ^ 2)).natDegree =
      A.natDegree + 2 * D.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 2 hDne), natDegree_pow]
  have hcf_AD2 : ((A * D ^ 2)).coeff (A.natDegree + 2 * D.natDegree) =
      A.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_AD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_C3 : (C ^ 3).natDegree = A.natDegree + 2 * D.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_C3 : (C ^ 3).coeff (A.natDegree + 2 * D.natDegree) =
      C.leadingCoeff ^ 3 := by
    rw [← hdeg_C3, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_AD2, hcf_C3]
  ring

/-- Substituted λ-rest on the CD chamber after `B = 0` and odd loads vanish. -/
def lambdaChamberRestCD610
    (alpha epsilon eta : k) (A C D E : k[X]) : k[X] :=
  (5 / 9 : k) • E ^ 2
  + (4 / 9 * alpha : k) • (C * E)
  + (2 / 9 * alpha : k) • D ^ 2
  + (2 / 3 * epsilon : k) • E
  + (1 / 3 * eta : k) • C

set_option maxHeartbeats 64000000 in
theorem lambdaChamberRestCD610_natDegree_lt
    (alpha epsilon eta : k) (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hB0 : B = 0)
    (hTle : 2 * C.natDegree + D.natDegree ≤ A.natDegree) :
    (lambdaChamberRestCD610 alpha epsilon eta A C D E).natDegree <
      A.natDegree + 2 * D.natDegree := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hCne, hDne, heq, hBcmp, hEcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hCD : A.natDegree + 2 * D.natDegree = 3 * C.natDegree := by omega
  have h7 : 7 * C.natDegree ≤ 3 * A.natDegree := by omega
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  rcases hEcmp with rfl | hEcmp <;>
    (simp only [lambdaChamberRestCD610, hpow2, zero_mul, mul_zero, zero_smul,
      smul_zero, add_zero, zero_add, zero_pow, Nat.succ_ne_zero, sub_zero,
      neg_zero, natDegree_zero];
     compute_degree; omega)

end CubicLoadSigmaCDFinish610

/-! ## Residual 8: `{B,C}` and `{B,C,E}` closed; `{B,C,D,E}` off-wall closed.

Leftover: `{C,D}` (N₁ walls and the chamber `2c+d ≤ a`) and `{B,C,D,E}`
on an N₁ odd-column wall.  Next unused row: CD N₁/N₂ 2×2 and the
chamber λ/ο combination. -/

section CubicLoadMultiAssembly610

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- Convert a specialised non-strict band into a strict band or an
equality wall. -/
theorem band_lt_or_eq_of_le {n m : ℕ} (h : n ≤ m) : n < m ∨ n = m :=
  lt_or_eq_of_le h

set_option maxHeartbeats 64000000 in
theorem normalized610ScaleZero_cubicResidual8
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
      (CubicLoadSigmaConeCD610 A B C D E ∨
        (CubicLoadSigmaConeBCDE610 A B C D E ∧
          (7 * (9 * A.natDegree) = 18 * A.natDegree + 42 * B.natDegree ∨
            7 * (9 * A.natDegree) = 30 * A.natDegree + 42 * B.natDegree ∨
            9 * A.natDegree = 6 * A.natDegree + 6 * B.natDegree ∨
            7 * (9 * A.natDegree) = 54 * A.natDegree + 42 * B.natDegree))) := by
  obtain ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
      zeta, eta, theta, iota, cLam, cKap, cMu, cOmi, A, B, C, D, E, ht,
      hj, hjdiv, hHsq, hder, hlamDeg, hkapDeg, hmuDeg, homiDeg, hconeA,
      hload, hl0, hkapB, hkapD, hkapZ, hbN1, hdN1, hzN1, htN1, hbBand,
      hdBand, hzBand, htBand, hexh⟩ :=
    normalized610ScaleZero_cubicResidual7 hsource
  refine ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
    zeta, eta, theta, iota, cLam, cKap, cMu, cOmi, A, B, C, D, E, ht, hj,
    hjdiv, hHsq, hder, hlamDeg, hkapDeg, hmuDeg, homiDeg, hconeA, hload,
    hl0, hkapB, hkapD, hkapZ, hbN1, hdN1, hzN1, htN1, hbBand, hdBand,
    hzBand, htBand, ?_⟩
  rcases hexh with hBC | hBCE | hBCDE | hCD
  · exact (cubicLoadSigmaCone_BC_impossible (j := j) (t := t) l alpha beta
      delta epsilon zeta eta theta A B C D E hBC hl0 hbBand hdBand hzBand
      htBand hlamDeg hkapDeg).elim
  · exact (cubicLoadSigmaCone_BCE_impossible (j := j) (t := t) l alpha beta
      delta epsilon zeta eta theta A B C D E hBCE hl0 hbBand hdBand hzBand
      htBand hlamDeg hkapDeg homiDeg).elim
  · -- `{B,C,D,E}`: off-wall identity, else an N₁ wall.
    have hb := cubicLoadSigmaConeBCDE610_specialize_beta hBCDE hbBand
    have hd := cubicLoadSigmaConeBCDE610_specialize_delta hBCDE hdBand
    have hz := cubicLoadSigmaConeBCDE610_specialize_zeta hBCDE hzBand
    have ht := cubicLoadSigmaConeBCDE610_specialize_theta hBCDE htBand
    rcases hb with hb0 | hble
    · rcases hd with hd0 | hdle
      · rcases hz with hz0 | hzle
        · rcases ht with ht0 | htle
          · exact (cubicLoadSigmaCone_BCDE_offWall_impossible (j := j)
              (t := t) l alpha beta delta epsilon zeta eta theta A B C D E
              hBCDE hl0 (Or.inl hb0) (Or.inl hd0) (Or.inl hz0) (Or.inl ht0)
              hlamDeg hkapDeg hmuDeg homiDeg).elim
          · rcases lt_or_eq_of_le htle with htlt | hteq
            · exact (cubicLoadSigmaCone_BCDE_offWall_impossible (j := j)
                (t := t) l alpha beta delta epsilon zeta eta theta A B C D E
                hBCDE hl0 (Or.inl hb0) (Or.inl hd0) (Or.inl hz0) (Or.inr htlt)
                hlamDeg hkapDeg hmuDeg homiDeg).elim
            · exact Or.inr ⟨hBCDE, Or.inr (Or.inr (Or.inr hteq))⟩
        · rcases lt_or_eq_of_le hzle with hzlt | hzeq
          · rcases ht with ht0 | htle
            · exact (cubicLoadSigmaCone_BCDE_offWall_impossible (j := j)
                (t := t) l alpha beta delta epsilon zeta eta theta A B C D E
                hBCDE hl0 (Or.inl hb0) (Or.inl hd0) (Or.inr hzlt)
                (Or.inl ht0) hlamDeg hkapDeg hmuDeg homiDeg).elim
            · rcases lt_or_eq_of_le htle with htlt | hteq
              · exact (cubicLoadSigmaCone_BCDE_offWall_impossible (j := j)
                  (t := t) l alpha beta delta epsilon zeta eta theta A B C D E
                  hBCDE hl0 (Or.inl hb0) (Or.inl hd0) (Or.inr hzlt)
                  (Or.inr htlt) hlamDeg hkapDeg hmuDeg homiDeg).elim
              · exact Or.inr ⟨hBCDE, Or.inr (Or.inr (Or.inr hteq))⟩
          · exact Or.inr ⟨hBCDE, Or.inr (Or.inr (Or.inl hzeq))⟩
      · rcases lt_or_eq_of_le hdle with hdlt | hdeq
        · rcases hz with hz0 | hzle
          · rcases ht with ht0 | htle
            · exact (cubicLoadSigmaCone_BCDE_offWall_impossible (j := j)
                (t := t) l alpha beta delta epsilon zeta eta theta A B C D E
                hBCDE hl0 (Or.inl hb0) (Or.inr hdlt) (Or.inl hz0)
                (Or.inl ht0) hlamDeg hkapDeg hmuDeg homiDeg).elim
            · rcases lt_or_eq_of_le htle with htlt | hteq
              · exact (cubicLoadSigmaCone_BCDE_offWall_impossible (j := j)
                  (t := t) l alpha beta delta epsilon zeta eta theta A B C D E
                  hBCDE hl0 (Or.inl hb0) (Or.inr hdlt) (Or.inl hz0)
                  (Or.inr htlt) hlamDeg hkapDeg hmuDeg homiDeg).elim
              · exact Or.inr ⟨hBCDE, Or.inr (Or.inr (Or.inr hteq))⟩
          · rcases lt_or_eq_of_le hzle with hzlt | hzeq
            · rcases ht with ht0 | htle
              · exact (cubicLoadSigmaCone_BCDE_offWall_impossible (j := j)
                  (t := t) l alpha beta delta epsilon zeta eta theta A B C D E
                  hBCDE hl0 (Or.inl hb0) (Or.inr hdlt) (Or.inr hzlt)
                  (Or.inl ht0) hlamDeg hkapDeg hmuDeg homiDeg).elim
              · rcases lt_or_eq_of_le htle with htlt | hteq
                · exact (cubicLoadSigmaCone_BCDE_offWall_impossible (j := j)
                    (t := t) l alpha beta delta epsilon zeta eta theta
                    A B C D E hBCDE hl0 (Or.inl hb0) (Or.inr hdlt)
                    (Or.inr hzlt) (Or.inr htlt) hlamDeg hkapDeg hmuDeg
                    homiDeg).elim
                · exact Or.inr ⟨hBCDE, Or.inr (Or.inr (Or.inr hteq))⟩
            · exact Or.inr ⟨hBCDE, Or.inr (Or.inr (Or.inl hzeq))⟩
        · exact Or.inr ⟨hBCDE, Or.inr (Or.inl hdeq)⟩
    · rcases lt_or_eq_of_le hble with hblt | hbeq
      · rcases hd with hd0 | hdle
        · rcases hz with hz0 | hzle
          · rcases ht with ht0 | htle
            · exact (cubicLoadSigmaCone_BCDE_offWall_impossible (j := j)
                (t := t) l alpha beta delta epsilon zeta eta theta A B C D E
                hBCDE hl0 (Or.inr hblt) (Or.inl hd0) (Or.inl hz0)
                (Or.inl ht0) hlamDeg hkapDeg hmuDeg homiDeg).elim
            · rcases lt_or_eq_of_le htle with htlt | hteq
              · exact (cubicLoadSigmaCone_BCDE_offWall_impossible (j := j)
                  (t := t) l alpha beta delta epsilon zeta eta theta A B C D E
                  hBCDE hl0 (Or.inr hblt) (Or.inl hd0) (Or.inl hz0)
                  (Or.inr htlt) hlamDeg hkapDeg hmuDeg homiDeg).elim
              · exact Or.inr ⟨hBCDE, Or.inr (Or.inr (Or.inr hteq))⟩
          · rcases lt_or_eq_of_le hzle with hzlt | hzeq
            · rcases ht with ht0 | htle
              · exact (cubicLoadSigmaCone_BCDE_offWall_impossible (j := j)
                  (t := t) l alpha beta delta epsilon zeta eta theta A B C D E
                  hBCDE hl0 (Or.inr hblt) (Or.inl hd0) (Or.inr hzlt)
                  (Or.inl ht0) hlamDeg hkapDeg hmuDeg homiDeg).elim
              · rcases lt_or_eq_of_le htle with htlt | hteq
                · exact (cubicLoadSigmaCone_BCDE_offWall_impossible (j := j)
                    (t := t) l alpha beta delta epsilon zeta eta theta
                    A B C D E hBCDE hl0 (Or.inr hblt) (Or.inl hd0)
                    (Or.inr hzlt) (Or.inr htlt) hlamDeg hkapDeg hmuDeg
                    homiDeg).elim
                · exact Or.inr ⟨hBCDE, Or.inr (Or.inr (Or.inr hteq))⟩
            · exact Or.inr ⟨hBCDE, Or.inr (Or.inr (Or.inl hzeq))⟩
        · rcases lt_or_eq_of_le hdle with hdlt | hdeq
          · rcases hz with hz0 | hzle
            · rcases ht with ht0 | htle
              · exact (cubicLoadSigmaCone_BCDE_offWall_impossible (j := j)
                  (t := t) l alpha beta delta epsilon zeta eta theta A B C D E
                  hBCDE hl0 (Or.inr hblt) (Or.inr hdlt) (Or.inl hz0)
                  (Or.inl ht0) hlamDeg hkapDeg hmuDeg homiDeg).elim
              · rcases lt_or_eq_of_le htle with htlt | hteq
                · exact (cubicLoadSigmaCone_BCDE_offWall_impossible (j := j)
                    (t := t) l alpha beta delta epsilon zeta eta theta
                    A B C D E hBCDE hl0 (Or.inr hblt) (Or.inr hdlt)
                    (Or.inl hz0) (Or.inr htlt) hlamDeg hkapDeg hmuDeg
                    homiDeg).elim
                · exact Or.inr ⟨hBCDE, Or.inr (Or.inr (Or.inr hteq))⟩
            · rcases lt_or_eq_of_le hzle with hzlt | hzeq
              · rcases ht with ht0 | htle
                · exact (cubicLoadSigmaCone_BCDE_offWall_impossible (j := j)
                    (t := t) l alpha beta delta epsilon zeta eta theta
                    A B C D E hBCDE hl0 (Or.inr hblt) (Or.inr hdlt)
                    (Or.inr hzlt) (Or.inl ht0) hlamDeg hkapDeg hmuDeg
                    homiDeg).elim
                · rcases lt_or_eq_of_le htle with htlt | hteq
                  · exact (cubicLoadSigmaCone_BCDE_offWall_impossible (j := j)
                      (t := t) l alpha beta delta epsilon zeta eta theta
                      A B C D E hBCDE hl0 (Or.inr hblt) (Or.inr hdlt)
                      (Or.inr hzlt) (Or.inr htlt) hlamDeg hkapDeg hmuDeg
                      homiDeg).elim
                  · exact Or.inr ⟨hBCDE, Or.inr (Or.inr (Or.inr hteq))⟩
              · exact Or.inr ⟨hBCDE, Or.inr (Or.inr (Or.inl hzeq))⟩
          · exact Or.inr ⟨hBCDE, Or.inr (Or.inl hdeq)⟩
      · exact Or.inr ⟨hBCDE, Or.inl hbeq⟩
  · exact Or.inl hCD

end CubicLoadMultiAssembly610

#print axioms cubicLoadSigmaCone_BC_impossible
#print axioms cubicLoadSigmaCone_BCE_impossible
#print axioms cubicLoadSigmaCone_BCDE_offWall_impossible
#print axioms normalized610ScaleZero_cubicResidual8

end Max11DegreeRoutes


