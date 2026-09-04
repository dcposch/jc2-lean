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

end Max11DegreeRoutes

