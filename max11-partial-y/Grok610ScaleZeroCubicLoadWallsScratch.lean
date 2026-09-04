import Grok610ScaleZeroCubicLoadMultiScratch

/-! # Scale-zero cubic load-compete walls + assembly, `(6,10)`, `H = 0`

Continuation of `Grok610ScaleZeroCubicLoadMultiScratch`.  That file
ends at `normalized610ScaleZero_cubicResidual8`: leftover is
`CubicLoadSigmaConeCD610` (N₁ odd-column walls `7T ∈ {18a,30a,42a,54a}`
and the chamber `2c+d ≤ a`) and `CubicLoadSigmaConeBCDE610` on an N₁
odd-column wall.

Plan `Grok610ScaleZeroCubicLoadCompetePlanScratch.md` §5 item 1 and §4:
N₁/N₂ 2×2 on those walls (dets `77/41472`, `7/1152`, `35/1728`, `5/72`),
then File B/C off-wall kills; CD chamber via `B = 0`, the four N₁ tops,
and the λ/ο two-face identity `c·(3ad²+c³) - 3a·(cd²) = c⁴`.  Assembly
is `normalized610ScaleZero_impossible` and
`proved_planeKellerNormalized610LowScaleRoute`.

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



section CubicLoadWallFaces610

variable {k : Type*} [Field k] [CharZero k]

def n2CubicBetaFace610 (beta : k) (A : k[X]) : k[X] :=
  (35 / 41472 * beta : k) • A ^ 6

def n2CubicDeltaFace610 (delta : k) (A : k[X]) : k[X] :=
  (7 / 2592 * delta : k) • A ^ 5

def n2CubicZetaFace610 (zeta : k) (A : k[X]) : k[X] :=
  (5 / 576 * zeta : k) • A ^ 4

def n2CubicThetaFace610 (theta : k) (A : k[X]) : k[X] :=
  (1 / 36 * theta : k) • A ^ 3

def omicronCubicSigmaInnerCD610 (c d : k) : k :=
  c * d ^ 2

/-- Two-face certificate on the CD chamber (CAS: `{3ad²+c³, cd²}`
saturates to `(1)` at `a,c,d ≠ 0`). -/
theorem cubicSigmaInner_CD_chamber_identity (a c d : k) :
    c * lambdaCubicSigmaInnerCD610 a c d
      - (3 * a) * omicronCubicSigmaInnerCD610 c d = c ^ 4 := by
  simp only [lambdaCubicSigmaInnerCD610, omicronCubicSigmaInnerCD610]
  ring

def omicronCubicSigmaFaceCD610 (A B C D E : k[X]) : k[X] :=
  (-(5 / 27 : k)) • (C * D ^ 2)

theorem n2CubicBetaFace610_coeff_top (beta : k) (A : k[X]) :
    (n2CubicBetaFace610 beta A).coeff (6 * A.natDegree) =
      (35 / 41472 * beta : k) * A.leadingCoeff ^ 6 := by
  simp only [n2CubicBetaFace610, coeff_smul, smul_eq_mul]
  have hAk : (A ^ 6).natDegree = 6 * A.natDegree := natDegree_pow _ _
  rw [← hAk, coeff_natDegree, leadingCoeff_pow]

theorem n2CubicDeltaFace610_coeff_top (delta : k) (A : k[X]) :
    (n2CubicDeltaFace610 delta A).coeff (5 * A.natDegree) =
      (7 / 2592 * delta : k) * A.leadingCoeff ^ 5 := by
  simp only [n2CubicDeltaFace610, coeff_smul, smul_eq_mul]
  have hAk : (A ^ 5).natDegree = 5 * A.natDegree := natDegree_pow _ _
  rw [← hAk, coeff_natDegree, leadingCoeff_pow]

theorem n2CubicZetaFace610_coeff_top (zeta : k) (A : k[X]) :
    (n2CubicZetaFace610 zeta A).coeff (4 * A.natDegree) =
      (5 / 576 * zeta : k) * A.leadingCoeff ^ 4 := by
  simp only [n2CubicZetaFace610, coeff_smul, smul_eq_mul]
  have hAk : (A ^ 4).natDegree = 4 * A.natDegree := natDegree_pow _ _
  rw [← hAk, coeff_natDegree, leadingCoeff_pow]

theorem n2CubicThetaFace610_coeff_top (theta : k) (A : k[X]) :
    (n2CubicThetaFace610 theta A).coeff (3 * A.natDegree) =
      (1 / 36 * theta : k) * A.leadingCoeff ^ 3 := by
  simp only [n2CubicThetaFace610, coeff_smul, smul_eq_mul]
  have hAk : (A ^ 3).natDegree = 3 * A.natDegree := natDegree_pow _ _
  rw [← hAk, coeff_natDegree, leadingCoeff_pow]

theorem n1CubicBetaFace610_coeff_top (beta : k) (A : k[X]) :
    (n1CubicBetaFace610 beta A).coeff (5 * A.natDegree) =
      (7 / 6912 * beta : k) * A.leadingCoeff ^ 5 := by
  simp only [n1CubicBetaFace610, coeff_smul, smul_eq_mul]
  have hAk : (A ^ 5).natDegree = 5 * A.natDegree := natDegree_pow _ _
  rw [← hAk, coeff_natDegree, leadingCoeff_pow]

theorem n1CubicDeltaFace610_coeff_top (delta : k) (A : k[X]) :
    (n1CubicDeltaFace610 delta A).coeff (4 * A.natDegree) =
      (35 / 10368 * delta : k) * A.leadingCoeff ^ 4 := by
  simp only [n1CubicDeltaFace610, coeff_smul, smul_eq_mul]
  have hAk : (A ^ 4).natDegree = 4 * A.natDegree := natDegree_pow _ _
  rw [← hAk, coeff_natDegree, leadingCoeff_pow]

theorem n1CubicZetaFace610_coeff_top (zeta : k) (A : k[X]) :
    (n1CubicZetaFace610 zeta A).coeff (3 * A.natDegree) =
      (5 / 432 * zeta : k) * A.leadingCoeff ^ 3 := by
  simp only [n1CubicZetaFace610, coeff_smul, smul_eq_mul]
  have hAk : (A ^ 3).natDegree = 3 * A.natDegree := natDegree_pow _ _
  rw [← hAk, coeff_natDegree, leadingCoeff_pow]

theorem n1CubicThetaFace610_coeff_top (theta : k) (A : k[X]) :
    (n1CubicThetaFace610 theta A).coeff (2 * A.natDegree) =
      (1 / 24 * theta : k) * A.leadingCoeff ^ 2 := by
  simp only [n1CubicThetaFace610, coeff_smul, smul_eq_mul]
  have hAk : (A ^ 2).natDegree = 2 * A.natDegree := natDegree_pow _ _
  rw [← hAk, coeff_natDegree, leadingCoeff_pow]

end CubicLoadWallFaces610


section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]


/-! `N1` rest on `CD` `beta` wall: 30 monomials. -/

set_option maxHeartbeats 64000000 in

def degreeZeroN1CubicCDWallBetaRest610_chunk0 (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (5 / 81 : k) • (A * B ^ 2 * D)
  + (20 / 243 : k) • (B ^ 3 * C)
  + (-(10 / 27 : k)) • (B * C * E)
  + (-(5 / 27 : k)) • (B * D ^ 2)
  + (4 / 243 * alpha : k) • (A * B ^ 3)
  + (-(4 / 27 * alpha : k)) • (B ^ 2 * D)
  + (-(4 / 27 * alpha : k)) • (B * C ^ 2)
  + (4 / 9 * alpha : k) • (D * E)
  + (35 / 2592 * beta : k) • (A ^ 3 * C)
  + (-(7 / 5184 * beta : k)) • (A ^ 2 * B ^ 2)
  + (7 / 144 * beta : k) • (A ^ 2 * E)
  + (-(7 / 216 * beta : k)) • (A * B * D)
  + (7 / 432 * beta : k) • (A * C ^ 2)
  + (-(35 / 432 * beta : k)) • (B ^ 2 * C)
  + (7 / 36 * beta : k) • (C * E)
  + (7 / 72 * beta : k) • D ^ 2

set_option maxHeartbeats 64000000 in

def degreeZeroN1CubicCDWallBetaRest610_chunk1 (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (35 / 10368 * delta : k) • A ^ 4
  + (5 / 144 * delta : k) • (A ^ 2 * C)
  + (5 / 432 * delta : k) • (A * B ^ 2)
  + (5 / 36 * delta : k) • (A * E)
  + (-(5 / 36 * delta : k)) • (B * D)
  + (-(5 / 72 * delta : k)) • C ^ 2
  + (-(2 / 9 * epsilon : k)) • (B * C)
  + (5 / 432 * zeta : k) • A ^ 3
  + (1 / 12 * zeta : k) • (A * C)
  + (-(1 / 8 * zeta : k)) • B ^ 2
  + (1 / 2 * zeta : k) • E
  + (1 / 3 * eta : k) • D
  + (1 / 24 * theta : k) • A ^ 2
  + (1 / 6 * theta : k) • C

def degreeZeroN1CubicCDWallBetaRest610 (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (degreeZeroN1CubicCDWallBetaRest610_chunk0 alpha beta delta epsilon zeta eta theta A B C D E) +
  (degreeZeroN1CubicCDWallBetaRest610_chunk1 alpha beta delta epsilon zeta eta theta A B C D E)

set_option maxHeartbeats 64000000 in
theorem degreeZeroN1CubicCDWallBetaRest610_chunk0_natDegree_lt
    (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hwall : 7 * (12 * A.natDegree) = 18 * A.natDegree + 42 * C.natDegree) :
    (degreeZeroN1CubicCDWallBetaRest610_chunk0 alpha beta delta epsilon zeta eta theta A B C D E).natDegree < 5 * A.natDegree := by
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
  have hwall' : 7 * C.natDegree = 11 * A.natDegree := by omega
  have hface : 2 * C.natDegree + D.natDegree = 5 * A.natDegree := by omega
  rcases hBcmp with rfl | hBcmp <;> rcases hEcmp with rfl | hEcmp <;>
        (simp only [degreeZeroN1CubicCDWallBetaRest610_chunk0, hpow2, hpow3, hpow4, hpow5,
          zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add,
          zero_pow, Nat.succ_ne_zero, sub_zero, neg_zero, natDegree_zero];
         compute_degree; omega)

set_option maxHeartbeats 64000000 in
theorem degreeZeroN1CubicCDWallBetaRest610_chunk1_natDegree_lt
    (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hwall : 7 * (12 * A.natDegree) = 18 * A.natDegree + 42 * C.natDegree) :
    (degreeZeroN1CubicCDWallBetaRest610_chunk1 alpha beta delta epsilon zeta eta theta A B C D E).natDegree < 5 * A.natDegree := by
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
  have hwall' : 7 * C.natDegree = 11 * A.natDegree := by omega
  have hface : 2 * C.natDegree + D.natDegree = 5 * A.natDegree := by omega
  rcases hBcmp with rfl | hBcmp <;> rcases hEcmp with rfl | hEcmp <;>
        (simp only [degreeZeroN1CubicCDWallBetaRest610_chunk1, hpow2, hpow3, hpow4, hpow5,
          zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add,
          zero_pow, Nat.succ_ne_zero, sub_zero, neg_zero, natDegree_zero];
         compute_degree; omega)

set_option maxHeartbeats 64000000 in
theorem degreeZeroN1CubicCDWallBetaRest610_natDegree_lt
    (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hwall : 7 * (12 * A.natDegree) = 18 * A.natDegree + 42 * C.natDegree) :
    (degreeZeroN1CubicCDWallBetaRest610 alpha beta delta epsilon zeta eta theta A B C D E).natDegree < 5 * A.natDegree := by
  simp only [degreeZeroN1CubicCDWallBetaRest610]
  have h0 := degreeZeroN1CubicCDWallBetaRest610_chunk0_natDegree_lt alpha beta delta epsilon zeta eta theta A B C D E hcone hwall
  have h1 := degreeZeroN1CubicCDWallBetaRest610_chunk1_natDegree_lt alpha beta delta epsilon zeta eta theta A B C D E hcone hwall
  have hadd := natDegree_add_le (degreeZeroN1CubicCDWallBetaRest610_chunk0 alpha beta delta epsilon zeta eta theta A B C D E) (degreeZeroN1CubicCDWallBetaRest610_chunk1 alpha beta delta epsilon zeta eta theta A B C D E)
  exact lt_of_le_of_lt hadd (max_lt h0 h1)


/-! `N1` rest on `CD` `delta` wall: 21 monomials. -/

set_option maxHeartbeats 64000000 in

def degreeZeroN1CubicCDWallDeltaRest610_chunk0 (alpha delta epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (5 / 81 : k) • (A * B ^ 2 * D)
  + (20 / 243 : k) • (B ^ 3 * C)
  + (-(10 / 27 : k)) • (B * C * E)
  + (-(5 / 27 : k)) • (B * D ^ 2)
  + (4 / 243 * alpha : k) • (A * B ^ 3)
  + (-(4 / 27 * alpha : k)) • (B ^ 2 * D)
  + (-(4 / 27 * alpha : k)) • (B * C ^ 2)
  + (4 / 9 * alpha : k) • (D * E)
  + (5 / 144 * delta : k) • (A ^ 2 * C)
  + (5 / 432 * delta : k) • (A * B ^ 2)
  + (5 / 36 * delta : k) • (A * E)
  + (-(5 / 36 * delta : k)) • (B * D)
  + (-(5 / 72 * delta : k)) • C ^ 2
  + (-(2 / 9 * epsilon : k)) • (B * C)
  + (5 / 432 * zeta : k) • A ^ 3
  + (1 / 12 * zeta : k) • (A * C)

set_option maxHeartbeats 64000000 in

def degreeZeroN1CubicCDWallDeltaRest610_chunk1 (alpha delta epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (-(1 / 8 * zeta : k)) • B ^ 2
  + (1 / 2 * zeta : k) • E
  + (1 / 3 * eta : k) • D
  + (1 / 24 * theta : k) • A ^ 2
  + (1 / 6 * theta : k) • C

def degreeZeroN1CubicCDWallDeltaRest610 (alpha delta epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (degreeZeroN1CubicCDWallDeltaRest610_chunk0 alpha delta epsilon zeta eta theta A B C D E) +
  (degreeZeroN1CubicCDWallDeltaRest610_chunk1 alpha delta epsilon zeta eta theta A B C D E)

set_option maxHeartbeats 64000000 in
theorem degreeZeroN1CubicCDWallDeltaRest610_chunk0_natDegree_lt
    (alpha delta epsilon zeta eta theta : k) (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hwall : 7 * (12 * A.natDegree) = 30 * A.natDegree + 42 * C.natDegree) :
    (degreeZeroN1CubicCDWallDeltaRest610_chunk0 alpha delta epsilon zeta eta theta A B C D E).natDegree < 4 * A.natDegree := by
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
  have hwall' : 7 * C.natDegree = 9 * A.natDegree := by omega
  have hface : 2 * C.natDegree + D.natDegree = 4 * A.natDegree := by omega
  rcases hBcmp with rfl | hBcmp <;> rcases hEcmp with rfl | hEcmp <;>
        (simp only [degreeZeroN1CubicCDWallDeltaRest610_chunk0, hpow2, hpow3, hpow4, hpow5,
          zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add,
          zero_pow, Nat.succ_ne_zero, sub_zero, neg_zero, natDegree_zero];
         compute_degree; omega)

set_option maxHeartbeats 64000000 in
theorem degreeZeroN1CubicCDWallDeltaRest610_chunk1_natDegree_lt
    (alpha delta epsilon zeta eta theta : k) (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hwall : 7 * (12 * A.natDegree) = 30 * A.natDegree + 42 * C.natDegree) :
    (degreeZeroN1CubicCDWallDeltaRest610_chunk1 alpha delta epsilon zeta eta theta A B C D E).natDegree < 4 * A.natDegree := by
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
  have hwall' : 7 * C.natDegree = 9 * A.natDegree := by omega
  have hface : 2 * C.natDegree + D.natDegree = 4 * A.natDegree := by omega
  rcases hBcmp with rfl | hBcmp <;> rcases hEcmp with rfl | hEcmp <;>
        (simp only [degreeZeroN1CubicCDWallDeltaRest610_chunk1, hpow2, hpow3, hpow4, hpow5,
          zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add,
          zero_pow, Nat.succ_ne_zero, sub_zero, neg_zero, natDegree_zero];
         compute_degree; omega)

set_option maxHeartbeats 64000000 in
theorem degreeZeroN1CubicCDWallDeltaRest610_natDegree_lt
    (alpha delta epsilon zeta eta theta : k) (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hwall : 7 * (12 * A.natDegree) = 30 * A.natDegree + 42 * C.natDegree) :
    (degreeZeroN1CubicCDWallDeltaRest610 alpha delta epsilon zeta eta theta A B C D E).natDegree < 4 * A.natDegree := by
  simp only [degreeZeroN1CubicCDWallDeltaRest610]
  have h0 := degreeZeroN1CubicCDWallDeltaRest610_chunk0_natDegree_lt alpha delta epsilon zeta eta theta A B C D E hcone hwall
  have h1 := degreeZeroN1CubicCDWallDeltaRest610_chunk1_natDegree_lt alpha delta epsilon zeta eta theta A B C D E hcone hwall
  have hadd := natDegree_add_le (degreeZeroN1CubicCDWallDeltaRest610_chunk0 alpha delta epsilon zeta eta theta A B C D E) (degreeZeroN1CubicCDWallDeltaRest610_chunk1 alpha delta epsilon zeta eta theta A B C D E)
  exact lt_of_le_of_lt hadd (max_lt h0 h1)


/-! `N1` rest on `CD` `zeta` wall: 15 monomials. -/

set_option maxHeartbeats 64000000 in

def degreeZeroN1CubicCDWallZetaRest610 (alpha epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (5 / 81 : k) • (A * B ^ 2 * D)
  + (20 / 243 : k) • (B ^ 3 * C)
  + (-(10 / 27 : k)) • (B * C * E)
  + (-(5 / 27 : k)) • (B * D ^ 2)
  + (4 / 243 * alpha : k) • (A * B ^ 3)
  + (-(4 / 27 * alpha : k)) • (B ^ 2 * D)
  + (-(4 / 27 * alpha : k)) • (B * C ^ 2)
  + (4 / 9 * alpha : k) • (D * E)
  + (-(2 / 9 * epsilon : k)) • (B * C)
  + (1 / 12 * zeta : k) • (A * C)
  + (-(1 / 8 * zeta : k)) • B ^ 2
  + (1 / 2 * zeta : k) • E
  + (1 / 3 * eta : k) • D
  + (1 / 24 * theta : k) • A ^ 2
  + (1 / 6 * theta : k) • C

set_option maxHeartbeats 64000000 in
theorem degreeZeroN1CubicCDWallZetaRest610_natDegree_lt
    (alpha epsilon zeta eta theta : k) (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hwall : 12 * A.natDegree = 6 * A.natDegree + 6 * C.natDegree) :
    (degreeZeroN1CubicCDWallZetaRest610 alpha epsilon zeta eta theta A B C D E).natDegree < 3 * A.natDegree := by
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
  have hwall' : C.natDegree = A.natDegree := by omega
  have hface : 2 * C.natDegree + D.natDegree = 3 * A.natDegree := by omega
  rcases hBcmp with rfl | hBcmp <;> rcases hEcmp with rfl | hEcmp <;>
        (simp only [degreeZeroN1CubicCDWallZetaRest610, hpow2, hpow3, hpow4, hpow5,
          zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add,
          zero_pow, Nat.succ_ne_zero, sub_zero, neg_zero, natDegree_zero];
         compute_degree; omega)


/-! `N1` rest on `CD` `theta` wall: 11 monomials. -/

set_option maxHeartbeats 64000000 in

def degreeZeroN1CubicCDWallThetaRest610 (alpha epsilon eta theta : k) (A B C D E : k[X]) : k[X] :=
  (5 / 81 : k) • (A * B ^ 2 * D)
  + (20 / 243 : k) • (B ^ 3 * C)
  + (-(10 / 27 : k)) • (B * C * E)
  + (-(5 / 27 : k)) • (B * D ^ 2)
  + (4 / 243 * alpha : k) • (A * B ^ 3)
  + (-(4 / 27 * alpha : k)) • (B ^ 2 * D)
  + (-(4 / 27 * alpha : k)) • (B * C ^ 2)
  + (4 / 9 * alpha : k) • (D * E)
  + (-(2 / 9 * epsilon : k)) • (B * C)
  + (1 / 3 * eta : k) • D
  + (1 / 6 * theta : k) • C

set_option maxHeartbeats 64000000 in
theorem degreeZeroN1CubicCDWallThetaRest610_natDegree_lt
    (alpha epsilon eta theta : k) (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hwall : 7 * (12 * A.natDegree) = 54 * A.natDegree + 42 * C.natDegree) :
    (degreeZeroN1CubicCDWallThetaRest610 alpha epsilon eta theta A B C D E).natDegree < 2 * A.natDegree := by
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
  have hwall' : 7 * C.natDegree = 5 * A.natDegree := by omega
  have hface : 2 * C.natDegree + D.natDegree = 2 * A.natDegree := by omega
  rcases hBcmp with rfl | hBcmp <;> rcases hEcmp with rfl | hEcmp <;>
        (simp only [degreeZeroN1CubicCDWallThetaRest610, hpow2, hpow3, hpow4, hpow5,
          zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add,
          zero_pow, Nat.succ_ne_zero, sub_zero, neg_zero, natDegree_zero];
         compute_degree; omega)


/-! `N2` rest on `CD` `beta` wall: 52 monomials. -/

set_option maxHeartbeats 64000000 in

def degreeZeroN2CubicCDWallBetaRest610_chunk0 (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (-(5 / 81 : k)) • (A ^ 2 * B ^ 2 * D)
  + (-(25 / 243 : k)) • (A * B ^ 3 * C)
  + (-(4 / 243 : k)) • B ^ 5
  + (10 / 27 : k) • (A * B * C * E)
  + (5 / 27 : k) • (A * B * D ^ 2)
  + (10 / 81 : k) • (B ^ 3 * E)
  + (5 / 9 : k) • (B ^ 2 * C * D)
  + (5 / 27 : k) • (B * C ^ 3)
  + (-(10 / 9 : k)) • (C * D * E)
  + (-(10 / 27 : k)) • D ^ 3
  + (-(4 / 243 * alpha : k)) • (A ^ 2 * B ^ 3)
  + (4 / 27 * alpha : k) • (A * B ^ 2 * D)
  + (4 / 27 * alpha : k) • (A * B * C ^ 2)
  + (4 / 27 * alpha : k) • (B ^ 3 * C)
  + (-(4 / 9 * alpha : k)) • (A * D * E)
  + (-(4 / 9 * alpha : k)) • (B * C * E)

set_option maxHeartbeats 64000000 in

def degreeZeroN2CubicCDWallBetaRest610_chunk1 (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (-(4 / 9 * alpha : k)) • (B * D ^ 2)
  + (-(4 / 9 * alpha : k)) • (C ^ 2 * D)
  + (35 / 2592 * beta : k) • (A ^ 4 * C)
  + (-(7 / 1296 * beta : k)) • (A ^ 3 * B ^ 2)
  + (7 / 216 * beta : k) • (A ^ 3 * E)
  + (-(7 / 432 * beta : k)) • (A ^ 2 * B * D)
  + (49 / 864 * beta : k) • (A ^ 2 * C ^ 2)
  + (35 / 432 * beta : k) • (A * B ^ 2 * C)
  + (35 / 1728 * beta : k) • B ^ 4
  + (7 / 36 * beta : k) • (A * C * E)
  + (-(7 / 36 * beta : k)) • (A * D ^ 2)
  + (-(7 / 72 * beta : k)) • (B ^ 2 * E)
  + (-(7 / 18 * beta : k)) • (B * C * D)
  + (-(7 / 108 * beta : k)) • C ^ 3
  + (7 / 12 * beta : k) • E ^ 2
  + (7 / 2592 * delta : k) • A ^ 5

set_option maxHeartbeats 64000000 in

def degreeZeroN2CubicCDWallBetaRest610_chunk2 (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (5 / 144 * delta : k) • (A ^ 3 * C)
  + (-(25 / 864 * delta : k)) • (A ^ 2 * B ^ 2)
  + (5 / 72 * delta : k) • (A ^ 2 * E)
  + (5 / 36 * delta : k) • (A * C ^ 2)
  + (5 / 36 * delta : k) • (B ^ 2 * C)
  + (-(5 / 12 * delta : k)) • D ^ 2
  + (2 / 9 * epsilon : k) • (A * B * C)
  + (2 / 27 * epsilon : k) • B ^ 3
  + (-(2 / 3 * epsilon : k)) • (C * D)
  + (5 / 576 * zeta : k) • A ^ 4
  + (1 / 12 * zeta : k) • (A ^ 2 * C)
  + (1 / 12 * zeta : k) • (A * B ^ 2)
  + (-(1 / 2 * zeta : k)) • (B * D)
  + (-(1 / 4 * zeta : k)) • C ^ 2
  + (-(1 / 3 * eta : k)) • (A * D)
  + (-(1 / 3 * eta : k)) • (B * C)

set_option maxHeartbeats 64000000 in

def degreeZeroN2CubicCDWallBetaRest610_chunk3 (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (1 / 36 * theta : k) • A ^ 3
  + (1 / 6 * theta : k) • (A * C)
  + (-(1 / 12 * theta : k)) • B ^ 2
  + (1 * theta : k) • E

def degreeZeroN2CubicCDWallBetaRest610 (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (degreeZeroN2CubicCDWallBetaRest610_chunk0 alpha beta delta epsilon zeta eta theta A B C D E) +
  (degreeZeroN2CubicCDWallBetaRest610_chunk1 alpha beta delta epsilon zeta eta theta A B C D E) +
  (degreeZeroN2CubicCDWallBetaRest610_chunk2 alpha beta delta epsilon zeta eta theta A B C D E) +
  (degreeZeroN2CubicCDWallBetaRest610_chunk3 alpha beta delta epsilon zeta eta theta A B C D E)

set_option maxHeartbeats 64000000 in
theorem degreeZeroN2CubicCDWallBetaRest610_chunk0_natDegree_lt
    (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hwall : 7 * (12 * A.natDegree) = 18 * A.natDegree + 42 * C.natDegree) :
    (degreeZeroN2CubicCDWallBetaRest610_chunk0 alpha beta delta epsilon zeta eta theta A B C D E).natDegree < 6 * A.natDegree := by
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
  have hwall' : 7 * C.natDegree = 11 * A.natDegree := by omega
  have hface : 2 * C.natDegree + D.natDegree = 5 * A.natDegree := by omega
  rcases hBcmp with rfl | hBcmp <;> rcases hEcmp with rfl | hEcmp <;>
        (simp only [degreeZeroN2CubicCDWallBetaRest610_chunk0, hpow2, hpow3, hpow4, hpow5,
          zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add,
          zero_pow, Nat.succ_ne_zero, sub_zero, neg_zero, natDegree_zero];
         compute_degree; omega)

set_option maxHeartbeats 64000000 in
theorem degreeZeroN2CubicCDWallBetaRest610_chunk1_natDegree_lt
    (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hwall : 7 * (12 * A.natDegree) = 18 * A.natDegree + 42 * C.natDegree) :
    (degreeZeroN2CubicCDWallBetaRest610_chunk1 alpha beta delta epsilon zeta eta theta A B C D E).natDegree < 6 * A.natDegree := by
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
  have hwall' : 7 * C.natDegree = 11 * A.natDegree := by omega
  have hface : 2 * C.natDegree + D.natDegree = 5 * A.natDegree := by omega
  rcases hBcmp with rfl | hBcmp <;> rcases hEcmp with rfl | hEcmp <;>
        (simp only [degreeZeroN2CubicCDWallBetaRest610_chunk1, hpow2, hpow3, hpow4, hpow5,
          zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add,
          zero_pow, Nat.succ_ne_zero, sub_zero, neg_zero, natDegree_zero];
         compute_degree; omega)

set_option maxHeartbeats 64000000 in
theorem degreeZeroN2CubicCDWallBetaRest610_chunk2_natDegree_lt
    (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hwall : 7 * (12 * A.natDegree) = 18 * A.natDegree + 42 * C.natDegree) :
    (degreeZeroN2CubicCDWallBetaRest610_chunk2 alpha beta delta epsilon zeta eta theta A B C D E).natDegree < 6 * A.natDegree := by
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
  have hwall' : 7 * C.natDegree = 11 * A.natDegree := by omega
  have hface : 2 * C.natDegree + D.natDegree = 5 * A.natDegree := by omega
  rcases hBcmp with rfl | hBcmp <;> rcases hEcmp with rfl | hEcmp <;>
        (simp only [degreeZeroN2CubicCDWallBetaRest610_chunk2, hpow2, hpow3, hpow4, hpow5,
          zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add,
          zero_pow, Nat.succ_ne_zero, sub_zero, neg_zero, natDegree_zero];
         compute_degree; omega)

set_option maxHeartbeats 64000000 in
theorem degreeZeroN2CubicCDWallBetaRest610_chunk3_natDegree_lt
    (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hwall : 7 * (12 * A.natDegree) = 18 * A.natDegree + 42 * C.natDegree) :
    (degreeZeroN2CubicCDWallBetaRest610_chunk3 alpha beta delta epsilon zeta eta theta A B C D E).natDegree < 6 * A.natDegree := by
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
  have hwall' : 7 * C.natDegree = 11 * A.natDegree := by omega
  have hface : 2 * C.natDegree + D.natDegree = 5 * A.natDegree := by omega
  rcases hBcmp with rfl | hBcmp <;> rcases hEcmp with rfl | hEcmp <;>
        (simp only [degreeZeroN2CubicCDWallBetaRest610_chunk3, hpow2, hpow3, hpow4, hpow5,
          zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add,
          zero_pow, Nat.succ_ne_zero, sub_zero, neg_zero, natDegree_zero];
         compute_degree; omega)

set_option maxHeartbeats 64000000 in
theorem degreeZeroN2CubicCDWallBetaRest610_natDegree_lt
    (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hwall : 7 * (12 * A.natDegree) = 18 * A.natDegree + 42 * C.natDegree) :
    (degreeZeroN2CubicCDWallBetaRest610 alpha beta delta epsilon zeta eta theta A B C D E).natDegree < 6 * A.natDegree := by
  simp only [degreeZeroN2CubicCDWallBetaRest610]
  have h0 := degreeZeroN2CubicCDWallBetaRest610_chunk0_natDegree_lt alpha beta delta epsilon zeta eta theta A B C D E hcone hwall
  have h1 := degreeZeroN2CubicCDWallBetaRest610_chunk1_natDegree_lt alpha beta delta epsilon zeta eta theta A B C D E hcone hwall
  have h2 := degreeZeroN2CubicCDWallBetaRest610_chunk2_natDegree_lt alpha beta delta epsilon zeta eta theta A B C D E hcone hwall
  have h3 := degreeZeroN2CubicCDWallBetaRest610_chunk3_natDegree_lt alpha beta delta epsilon zeta eta theta A B C D E hcone hwall
  have hadd01 := natDegree_add_le (degreeZeroN2CubicCDWallBetaRest610_chunk0 alpha beta delta epsilon zeta eta theta A B C D E) (degreeZeroN2CubicCDWallBetaRest610_chunk1 alpha beta delta epsilon zeta eta theta A B C D E)
  have hadd012 := natDegree_add_le ((degreeZeroN2CubicCDWallBetaRest610_chunk0 alpha beta delta epsilon zeta eta theta A B C D E) + (degreeZeroN2CubicCDWallBetaRest610_chunk1 alpha beta delta epsilon zeta eta theta A B C D E)) (degreeZeroN2CubicCDWallBetaRest610_chunk2 alpha beta delta epsilon zeta eta theta A B C D E)
  have hadd := natDegree_add_le (((degreeZeroN2CubicCDWallBetaRest610_chunk0 alpha beta delta epsilon zeta eta theta A B C D E) + (degreeZeroN2CubicCDWallBetaRest610_chunk1 alpha beta delta epsilon zeta eta theta A B C D E)) + (degreeZeroN2CubicCDWallBetaRest610_chunk2 alpha beta delta epsilon zeta eta theta A B C D E)) (degreeZeroN2CubicCDWallBetaRest610_chunk3 alpha beta delta epsilon zeta eta theta A B C D E)
  exact lt_of_le_of_lt hadd (max_lt (lt_of_le_of_lt hadd012 (max_lt (lt_of_le_of_lt hadd01 (max_lt h0 h1)) h2)) h3)


/-! `N2` rest on `CD` `delta` wall: 38 monomials. -/

set_option maxHeartbeats 64000000 in

def degreeZeroN2CubicCDWallDeltaRest610_chunk0 (alpha delta epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (-(5 / 81 : k)) • (A ^ 2 * B ^ 2 * D)
  + (-(25 / 243 : k)) • (A * B ^ 3 * C)
  + (-(4 / 243 : k)) • B ^ 5
  + (10 / 27 : k) • (A * B * C * E)
  + (5 / 27 : k) • (A * B * D ^ 2)
  + (10 / 81 : k) • (B ^ 3 * E)
  + (5 / 9 : k) • (B ^ 2 * C * D)
  + (5 / 27 : k) • (B * C ^ 3)
  + (-(10 / 9 : k)) • (C * D * E)
  + (-(10 / 27 : k)) • D ^ 3
  + (-(4 / 243 * alpha : k)) • (A ^ 2 * B ^ 3)
  + (4 / 27 * alpha : k) • (A * B ^ 2 * D)
  + (4 / 27 * alpha : k) • (A * B * C ^ 2)
  + (4 / 27 * alpha : k) • (B ^ 3 * C)
  + (-(4 / 9 * alpha : k)) • (A * D * E)
  + (-(4 / 9 * alpha : k)) • (B * C * E)

set_option maxHeartbeats 64000000 in

def degreeZeroN2CubicCDWallDeltaRest610_chunk1 (alpha delta epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (-(4 / 9 * alpha : k)) • (B * D ^ 2)
  + (-(4 / 9 * alpha : k)) • (C ^ 2 * D)
  + (5 / 144 * delta : k) • (A ^ 3 * C)
  + (-(25 / 864 * delta : k)) • (A ^ 2 * B ^ 2)
  + (5 / 72 * delta : k) • (A ^ 2 * E)
  + (5 / 36 * delta : k) • (A * C ^ 2)
  + (5 / 36 * delta : k) • (B ^ 2 * C)
  + (-(5 / 12 * delta : k)) • D ^ 2
  + (2 / 9 * epsilon : k) • (A * B * C)
  + (2 / 27 * epsilon : k) • B ^ 3
  + (-(2 / 3 * epsilon : k)) • (C * D)
  + (5 / 576 * zeta : k) • A ^ 4
  + (1 / 12 * zeta : k) • (A ^ 2 * C)
  + (1 / 12 * zeta : k) • (A * B ^ 2)
  + (-(1 / 2 * zeta : k)) • (B * D)
  + (-(1 / 4 * zeta : k)) • C ^ 2

set_option maxHeartbeats 64000000 in

def degreeZeroN2CubicCDWallDeltaRest610_chunk2 (alpha delta epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (-(1 / 3 * eta : k)) • (A * D)
  + (-(1 / 3 * eta : k)) • (B * C)
  + (1 / 36 * theta : k) • A ^ 3
  + (1 / 6 * theta : k) • (A * C)
  + (-(1 / 12 * theta : k)) • B ^ 2
  + (1 * theta : k) • E

def degreeZeroN2CubicCDWallDeltaRest610 (alpha delta epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (degreeZeroN2CubicCDWallDeltaRest610_chunk0 alpha delta epsilon zeta eta theta A B C D E) +
  (degreeZeroN2CubicCDWallDeltaRest610_chunk1 alpha delta epsilon zeta eta theta A B C D E) +
  (degreeZeroN2CubicCDWallDeltaRest610_chunk2 alpha delta epsilon zeta eta theta A B C D E)

set_option maxHeartbeats 64000000 in
theorem degreeZeroN2CubicCDWallDeltaRest610_chunk0_natDegree_lt
    (alpha delta epsilon zeta eta theta : k) (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hwall : 7 * (12 * A.natDegree) = 30 * A.natDegree + 42 * C.natDegree) :
    (degreeZeroN2CubicCDWallDeltaRest610_chunk0 alpha delta epsilon zeta eta theta A B C D E).natDegree < 5 * A.natDegree := by
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
  have hwall' : 7 * C.natDegree = 9 * A.natDegree := by omega
  have hface : 2 * C.natDegree + D.natDegree = 4 * A.natDegree := by omega
  rcases hBcmp with rfl | hBcmp <;> rcases hEcmp with rfl | hEcmp <;>
        (simp only [degreeZeroN2CubicCDWallDeltaRest610_chunk0, hpow2, hpow3, hpow4, hpow5,
          zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add,
          zero_pow, Nat.succ_ne_zero, sub_zero, neg_zero, natDegree_zero];
         compute_degree; omega)

set_option maxHeartbeats 64000000 in
theorem degreeZeroN2CubicCDWallDeltaRest610_chunk1_natDegree_lt
    (alpha delta epsilon zeta eta theta : k) (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hwall : 7 * (12 * A.natDegree) = 30 * A.natDegree + 42 * C.natDegree) :
    (degreeZeroN2CubicCDWallDeltaRest610_chunk1 alpha delta epsilon zeta eta theta A B C D E).natDegree < 5 * A.natDegree := by
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
  have hwall' : 7 * C.natDegree = 9 * A.natDegree := by omega
  have hface : 2 * C.natDegree + D.natDegree = 4 * A.natDegree := by omega
  rcases hBcmp with rfl | hBcmp <;> rcases hEcmp with rfl | hEcmp <;>
        (simp only [degreeZeroN2CubicCDWallDeltaRest610_chunk1, hpow2, hpow3, hpow4, hpow5,
          zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add,
          zero_pow, Nat.succ_ne_zero, sub_zero, neg_zero, natDegree_zero];
         compute_degree; omega)

set_option maxHeartbeats 64000000 in
theorem degreeZeroN2CubicCDWallDeltaRest610_chunk2_natDegree_lt
    (alpha delta epsilon zeta eta theta : k) (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hwall : 7 * (12 * A.natDegree) = 30 * A.natDegree + 42 * C.natDegree) :
    (degreeZeroN2CubicCDWallDeltaRest610_chunk2 alpha delta epsilon zeta eta theta A B C D E).natDegree < 5 * A.natDegree := by
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
  have hwall' : 7 * C.natDegree = 9 * A.natDegree := by omega
  have hface : 2 * C.natDegree + D.natDegree = 4 * A.natDegree := by omega
  rcases hBcmp with rfl | hBcmp <;> rcases hEcmp with rfl | hEcmp <;>
        (simp only [degreeZeroN2CubicCDWallDeltaRest610_chunk2, hpow2, hpow3, hpow4, hpow5,
          zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add,
          zero_pow, Nat.succ_ne_zero, sub_zero, neg_zero, natDegree_zero];
         compute_degree; omega)

set_option maxHeartbeats 64000000 in
theorem degreeZeroN2CubicCDWallDeltaRest610_natDegree_lt
    (alpha delta epsilon zeta eta theta : k) (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hwall : 7 * (12 * A.natDegree) = 30 * A.natDegree + 42 * C.natDegree) :
    (degreeZeroN2CubicCDWallDeltaRest610 alpha delta epsilon zeta eta theta A B C D E).natDegree < 5 * A.natDegree := by
  simp only [degreeZeroN2CubicCDWallDeltaRest610]
  have h0 := degreeZeroN2CubicCDWallDeltaRest610_chunk0_natDegree_lt alpha delta epsilon zeta eta theta A B C D E hcone hwall
  have h1 := degreeZeroN2CubicCDWallDeltaRest610_chunk1_natDegree_lt alpha delta epsilon zeta eta theta A B C D E hcone hwall
  have h2 := degreeZeroN2CubicCDWallDeltaRest610_chunk2_natDegree_lt alpha delta epsilon zeta eta theta A B C D E hcone hwall
  have hadd01 := natDegree_add_le (degreeZeroN2CubicCDWallDeltaRest610_chunk0 alpha delta epsilon zeta eta theta A B C D E) (degreeZeroN2CubicCDWallDeltaRest610_chunk1 alpha delta epsilon zeta eta theta A B C D E)
  have hadd := natDegree_add_le ((degreeZeroN2CubicCDWallDeltaRest610_chunk0 alpha delta epsilon zeta eta theta A B C D E) + (degreeZeroN2CubicCDWallDeltaRest610_chunk1 alpha delta epsilon zeta eta theta A B C D E)) (degreeZeroN2CubicCDWallDeltaRest610_chunk2 alpha delta epsilon zeta eta theta A B C D E)
  exact lt_of_le_of_lt hadd (max_lt (lt_of_le_of_lt hadd01 (max_lt h0 h1)) h2)


/-! `N2` rest on `CD` `zeta` wall: 31 monomials. -/

set_option maxHeartbeats 64000000 in

def degreeZeroN2CubicCDWallZetaRest610_chunk0 (alpha epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (-(5 / 81 : k)) • (A ^ 2 * B ^ 2 * D)
  + (-(25 / 243 : k)) • (A * B ^ 3 * C)
  + (-(4 / 243 : k)) • B ^ 5
  + (10 / 27 : k) • (A * B * C * E)
  + (5 / 27 : k) • (A * B * D ^ 2)
  + (10 / 81 : k) • (B ^ 3 * E)
  + (5 / 9 : k) • (B ^ 2 * C * D)
  + (5 / 27 : k) • (B * C ^ 3)
  + (-(10 / 9 : k)) • (C * D * E)
  + (-(10 / 27 : k)) • D ^ 3
  + (-(4 / 243 * alpha : k)) • (A ^ 2 * B ^ 3)
  + (4 / 27 * alpha : k) • (A * B ^ 2 * D)
  + (4 / 27 * alpha : k) • (A * B * C ^ 2)
  + (4 / 27 * alpha : k) • (B ^ 3 * C)
  + (-(4 / 9 * alpha : k)) • (A * D * E)
  + (-(4 / 9 * alpha : k)) • (B * C * E)

set_option maxHeartbeats 64000000 in

def degreeZeroN2CubicCDWallZetaRest610_chunk1 (alpha epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (-(4 / 9 * alpha : k)) • (B * D ^ 2)
  + (-(4 / 9 * alpha : k)) • (C ^ 2 * D)
  + (2 / 9 * epsilon : k) • (A * B * C)
  + (2 / 27 * epsilon : k) • B ^ 3
  + (-(2 / 3 * epsilon : k)) • (C * D)
  + (1 / 12 * zeta : k) • (A ^ 2 * C)
  + (1 / 12 * zeta : k) • (A * B ^ 2)
  + (-(1 / 2 * zeta : k)) • (B * D)
  + (-(1 / 4 * zeta : k)) • C ^ 2
  + (-(1 / 3 * eta : k)) • (A * D)
  + (-(1 / 3 * eta : k)) • (B * C)
  + (1 / 36 * theta : k) • A ^ 3
  + (1 / 6 * theta : k) • (A * C)
  + (-(1 / 12 * theta : k)) • B ^ 2
  + (1 * theta : k) • E

def degreeZeroN2CubicCDWallZetaRest610 (alpha epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (degreeZeroN2CubicCDWallZetaRest610_chunk0 alpha epsilon zeta eta theta A B C D E) +
  (degreeZeroN2CubicCDWallZetaRest610_chunk1 alpha epsilon zeta eta theta A B C D E)

set_option maxHeartbeats 64000000 in
theorem degreeZeroN2CubicCDWallZetaRest610_chunk0_natDegree_lt
    (alpha epsilon zeta eta theta : k) (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hwall : 12 * A.natDegree = 6 * A.natDegree + 6 * C.natDegree) :
    (degreeZeroN2CubicCDWallZetaRest610_chunk0 alpha epsilon zeta eta theta A B C D E).natDegree < 4 * A.natDegree := by
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
  have hwall' : C.natDegree = A.natDegree := by omega
  have hface : 2 * C.natDegree + D.natDegree = 3 * A.natDegree := by omega
  rcases hBcmp with rfl | hBcmp <;> rcases hEcmp with rfl | hEcmp <;>
        (simp only [degreeZeroN2CubicCDWallZetaRest610_chunk0, hpow2, hpow3, hpow4, hpow5,
          zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add,
          zero_pow, Nat.succ_ne_zero, sub_zero, neg_zero, natDegree_zero];
         compute_degree; omega)

set_option maxHeartbeats 64000000 in
theorem degreeZeroN2CubicCDWallZetaRest610_chunk1_natDegree_lt
    (alpha epsilon zeta eta theta : k) (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hwall : 12 * A.natDegree = 6 * A.natDegree + 6 * C.natDegree) :
    (degreeZeroN2CubicCDWallZetaRest610_chunk1 alpha epsilon zeta eta theta A B C D E).natDegree < 4 * A.natDegree := by
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
  have hwall' : C.natDegree = A.natDegree := by omega
  have hface : 2 * C.natDegree + D.natDegree = 3 * A.natDegree := by omega
  rcases hBcmp with rfl | hBcmp <;> rcases hEcmp with rfl | hEcmp <;>
        (simp only [degreeZeroN2CubicCDWallZetaRest610_chunk1, hpow2, hpow3, hpow4, hpow5,
          zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add,
          zero_pow, Nat.succ_ne_zero, sub_zero, neg_zero, natDegree_zero];
         compute_degree; omega)

set_option maxHeartbeats 64000000 in
theorem degreeZeroN2CubicCDWallZetaRest610_natDegree_lt
    (alpha epsilon zeta eta theta : k) (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hwall : 12 * A.natDegree = 6 * A.natDegree + 6 * C.natDegree) :
    (degreeZeroN2CubicCDWallZetaRest610 alpha epsilon zeta eta theta A B C D E).natDegree < 4 * A.natDegree := by
  simp only [degreeZeroN2CubicCDWallZetaRest610]
  have h0 := degreeZeroN2CubicCDWallZetaRest610_chunk0_natDegree_lt alpha epsilon zeta eta theta A B C D E hcone hwall
  have h1 := degreeZeroN2CubicCDWallZetaRest610_chunk1_natDegree_lt alpha epsilon zeta eta theta A B C D E hcone hwall
  have hadd := natDegree_add_le (degreeZeroN2CubicCDWallZetaRest610_chunk0 alpha epsilon zeta eta theta A B C D E) (degreeZeroN2CubicCDWallZetaRest610_chunk1 alpha epsilon zeta eta theta A B C D E)
  exact lt_of_le_of_lt hadd (max_lt h0 h1)


/-! `N2` rest on `CD` `theta` wall: 26 monomials. -/

set_option maxHeartbeats 64000000 in

def degreeZeroN2CubicCDWallThetaRest610_chunk0 (alpha epsilon eta theta : k) (A B C D E : k[X]) : k[X] :=
  (-(5 / 81 : k)) • (A ^ 2 * B ^ 2 * D)
  + (-(25 / 243 : k)) • (A * B ^ 3 * C)
  + (-(4 / 243 : k)) • B ^ 5
  + (10 / 27 : k) • (A * B * C * E)
  + (5 / 27 : k) • (A * B * D ^ 2)
  + (10 / 81 : k) • (B ^ 3 * E)
  + (5 / 9 : k) • (B ^ 2 * C * D)
  + (5 / 27 : k) • (B * C ^ 3)
  + (-(10 / 9 : k)) • (C * D * E)
  + (-(10 / 27 : k)) • D ^ 3
  + (-(4 / 243 * alpha : k)) • (A ^ 2 * B ^ 3)
  + (4 / 27 * alpha : k) • (A * B ^ 2 * D)
  + (4 / 27 * alpha : k) • (A * B * C ^ 2)
  + (4 / 27 * alpha : k) • (B ^ 3 * C)
  + (-(4 / 9 * alpha : k)) • (A * D * E)
  + (-(4 / 9 * alpha : k)) • (B * C * E)

set_option maxHeartbeats 64000000 in

def degreeZeroN2CubicCDWallThetaRest610_chunk1 (alpha epsilon eta theta : k) (A B C D E : k[X]) : k[X] :=
  (-(4 / 9 * alpha : k)) • (B * D ^ 2)
  + (-(4 / 9 * alpha : k)) • (C ^ 2 * D)
  + (2 / 9 * epsilon : k) • (A * B * C)
  + (2 / 27 * epsilon : k) • B ^ 3
  + (-(2 / 3 * epsilon : k)) • (C * D)
  + (-(1 / 3 * eta : k)) • (A * D)
  + (-(1 / 3 * eta : k)) • (B * C)
  + (1 / 6 * theta : k) • (A * C)
  + (-(1 / 12 * theta : k)) • B ^ 2
  + (1 * theta : k) • E

def degreeZeroN2CubicCDWallThetaRest610 (alpha epsilon eta theta : k) (A B C D E : k[X]) : k[X] :=
  (degreeZeroN2CubicCDWallThetaRest610_chunk0 alpha epsilon eta theta A B C D E) +
  (degreeZeroN2CubicCDWallThetaRest610_chunk1 alpha epsilon eta theta A B C D E)

set_option maxHeartbeats 64000000 in
theorem degreeZeroN2CubicCDWallThetaRest610_chunk0_natDegree_lt
    (alpha epsilon eta theta : k) (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hwall : 7 * (12 * A.natDegree) = 54 * A.natDegree + 42 * C.natDegree) :
    (degreeZeroN2CubicCDWallThetaRest610_chunk0 alpha epsilon eta theta A B C D E).natDegree < 3 * A.natDegree := by
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
  have hwall' : 7 * C.natDegree = 5 * A.natDegree := by omega
  have hface : 2 * C.natDegree + D.natDegree = 2 * A.natDegree := by omega
  rcases hBcmp with rfl | hBcmp <;> rcases hEcmp with rfl | hEcmp <;>
        (simp only [degreeZeroN2CubicCDWallThetaRest610_chunk0, hpow2, hpow3, hpow4, hpow5,
          zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add,
          zero_pow, Nat.succ_ne_zero, sub_zero, neg_zero, natDegree_zero];
         compute_degree; omega)

set_option maxHeartbeats 64000000 in
theorem degreeZeroN2CubicCDWallThetaRest610_chunk1_natDegree_lt
    (alpha epsilon eta theta : k) (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hwall : 7 * (12 * A.natDegree) = 54 * A.natDegree + 42 * C.natDegree) :
    (degreeZeroN2CubicCDWallThetaRest610_chunk1 alpha epsilon eta theta A B C D E).natDegree < 3 * A.natDegree := by
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
  have hwall' : 7 * C.natDegree = 5 * A.natDegree := by omega
  have hface : 2 * C.natDegree + D.natDegree = 2 * A.natDegree := by omega
  rcases hBcmp with rfl | hBcmp <;> rcases hEcmp with rfl | hEcmp <;>
        (simp only [degreeZeroN2CubicCDWallThetaRest610_chunk1, hpow2, hpow3, hpow4, hpow5,
          zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add,
          zero_pow, Nat.succ_ne_zero, sub_zero, neg_zero, natDegree_zero];
         compute_degree; omega)

set_option maxHeartbeats 64000000 in
theorem degreeZeroN2CubicCDWallThetaRest610_natDegree_lt
    (alpha epsilon eta theta : k) (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hwall : 7 * (12 * A.natDegree) = 54 * A.natDegree + 42 * C.natDegree) :
    (degreeZeroN2CubicCDWallThetaRest610 alpha epsilon eta theta A B C D E).natDegree < 3 * A.natDegree := by
  simp only [degreeZeroN2CubicCDWallThetaRest610]
  have h0 := degreeZeroN2CubicCDWallThetaRest610_chunk0_natDegree_lt alpha epsilon eta theta A B C D E hcone hwall
  have h1 := degreeZeroN2CubicCDWallThetaRest610_chunk1_natDegree_lt alpha epsilon eta theta A B C D E hcone hwall
  have hadd := natDegree_add_le (degreeZeroN2CubicCDWallThetaRest610_chunk0 alpha epsilon eta theta A B C D E) (degreeZeroN2CubicCDWallThetaRest610_chunk1 alpha epsilon eta theta A B C D E)
  exact lt_of_le_of_lt hadd (max_lt h0 h1)


/-! `N1` rest on `BCDE` `beta` wall: 28 monomials. -/

set_option maxHeartbeats 64000000 in

def degreeZeroN1CubicBCDEWallBetaRest610_chunk0 (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (20 / 243 : k) • (B ^ 3 * C)
  + (-(5 / 27 : k)) • (B * D ^ 2)
  + (4 / 243 * alpha : k) • (A * B ^ 3)
  + (-(4 / 27 * alpha : k)) • (B ^ 2 * D)
  + (-(4 / 27 * alpha : k)) • (B * C ^ 2)
  + (4 / 9 * alpha : k) • (D * E)
  + (35 / 2592 * beta : k) • (A ^ 3 * C)
  + (-(7 / 5184 * beta : k)) • (A ^ 2 * B ^ 2)
  + (7 / 144 * beta : k) • (A ^ 2 * E)
  + (-(7 / 216 * beta : k)) • (A * B * D)
  + (7 / 432 * beta : k) • (A * C ^ 2)
  + (-(35 / 432 * beta : k)) • (B ^ 2 * C)
  + (7 / 36 * beta : k) • (C * E)
  + (7 / 72 * beta : k) • D ^ 2
  + (35 / 10368 * delta : k) • A ^ 4
  + (5 / 144 * delta : k) • (A ^ 2 * C)

set_option maxHeartbeats 64000000 in

def degreeZeroN1CubicBCDEWallBetaRest610_chunk1 (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (5 / 432 * delta : k) • (A * B ^ 2)
  + (5 / 36 * delta : k) • (A * E)
  + (-(5 / 36 * delta : k)) • (B * D)
  + (-(5 / 72 * delta : k)) • C ^ 2
  + (-(2 / 9 * epsilon : k)) • (B * C)
  + (5 / 432 * zeta : k) • A ^ 3
  + (1 / 12 * zeta : k) • (A * C)
  + (-(1 / 8 * zeta : k)) • B ^ 2
  + (1 / 2 * zeta : k) • E
  + (1 / 3 * eta : k) • D
  + (1 / 24 * theta : k) • A ^ 2
  + (1 / 6 * theta : k) • C

def degreeZeroN1CubicBCDEWallBetaRest610 (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (degreeZeroN1CubicBCDEWallBetaRest610_chunk0 alpha beta delta epsilon zeta eta theta A B C D E) +
  (degreeZeroN1CubicBCDEWallBetaRest610_chunk1 alpha beta delta epsilon zeta eta theta A B C D E)

set_option maxHeartbeats 64000000 in
theorem degreeZeroN1CubicBCDEWallBetaRest610_chunk0_natDegree_lt
    (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeBCDE610 A B C D E)
    (hwall : 7 * (9 * A.natDegree) = 18 * A.natDegree + 42 * B.natDegree) :
    (degreeZeroN1CubicBCDEWallBetaRest610_chunk0 alpha beta delta epsilon zeta eta theta A B C D E).natDegree < 5 * A.natDegree := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hCne, hDne, hEne, heq1, heq2, heq3⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsAB : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAB
  have hsAC : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hAC
  have hsAD : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hAD
  have hsAE : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAE
  have eqC : 2 * C.natDegree = A.natDegree + 2 * B.natDegree := by omega
  have eqD : 4 * D.natDegree = A.natDegree + 6 * B.natDegree := by omega
  have eqE : 4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree := by omega
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hwall' : 14 * B.natDegree = 15 * A.natDegree := by omega
  have hface : A.natDegree + 2 * B.natDegree + D.natDegree = 5 * A.natDegree := by omega
  have hBpos : 0 + 1 ≤ B.natDegree := by omega
  have hCpos : 0 + 1 ≤ C.natDegree := by omega
  have hDpos : 0 + 1 ≤ D.natDegree := by omega
  have hEpos : 0 + 1 ≤ E.natDegree := by omega
  simp only [degreeZeroN1CubicBCDEWallBetaRest610_chunk0, hpow2, hpow3, hpow4, hpow5,
    zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add,
    zero_pow, Nat.succ_ne_zero, sub_zero, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem degreeZeroN1CubicBCDEWallBetaRest610_chunk1_natDegree_lt
    (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeBCDE610 A B C D E)
    (hwall : 7 * (9 * A.natDegree) = 18 * A.natDegree + 42 * B.natDegree) :
    (degreeZeroN1CubicBCDEWallBetaRest610_chunk1 alpha beta delta epsilon zeta eta theta A B C D E).natDegree < 5 * A.natDegree := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hCne, hDne, hEne, heq1, heq2, heq3⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsAB : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAB
  have hsAC : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hAC
  have hsAD : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hAD
  have hsAE : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAE
  have eqC : 2 * C.natDegree = A.natDegree + 2 * B.natDegree := by omega
  have eqD : 4 * D.natDegree = A.natDegree + 6 * B.natDegree := by omega
  have eqE : 4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree := by omega
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hwall' : 14 * B.natDegree = 15 * A.natDegree := by omega
  have hface : A.natDegree + 2 * B.natDegree + D.natDegree = 5 * A.natDegree := by omega
  have hBpos : 0 + 1 ≤ B.natDegree := by omega
  have hCpos : 0 + 1 ≤ C.natDegree := by omega
  have hDpos : 0 + 1 ≤ D.natDegree := by omega
  have hEpos : 0 + 1 ≤ E.natDegree := by omega
  simp only [degreeZeroN1CubicBCDEWallBetaRest610_chunk1, hpow2, hpow3, hpow4, hpow5,
    zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add,
    zero_pow, Nat.succ_ne_zero, sub_zero, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem degreeZeroN1CubicBCDEWallBetaRest610_natDegree_lt
    (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeBCDE610 A B C D E)
    (hwall : 7 * (9 * A.natDegree) = 18 * A.natDegree + 42 * B.natDegree) :
    (degreeZeroN1CubicBCDEWallBetaRest610 alpha beta delta epsilon zeta eta theta A B C D E).natDegree < 5 * A.natDegree := by
  simp only [degreeZeroN1CubicBCDEWallBetaRest610]
  have h0 := degreeZeroN1CubicBCDEWallBetaRest610_chunk0_natDegree_lt alpha beta delta epsilon zeta eta theta A B C D E hcone hwall
  have h1 := degreeZeroN1CubicBCDEWallBetaRest610_chunk1_natDegree_lt alpha beta delta epsilon zeta eta theta A B C D E hcone hwall
  have hadd := natDegree_add_le (degreeZeroN1CubicBCDEWallBetaRest610_chunk0 alpha beta delta epsilon zeta eta theta A B C D E) (degreeZeroN1CubicBCDEWallBetaRest610_chunk1 alpha beta delta epsilon zeta eta theta A B C D E)
  exact lt_of_le_of_lt hadd (max_lt h0 h1)


/-! `N1` rest on `BCDE` `delta` wall: 19 monomials. -/

set_option maxHeartbeats 64000000 in

def degreeZeroN1CubicBCDEWallDeltaRest610_chunk0 (alpha delta epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (20 / 243 : k) • (B ^ 3 * C)
  + (-(5 / 27 : k)) • (B * D ^ 2)
  + (4 / 243 * alpha : k) • (A * B ^ 3)
  + (-(4 / 27 * alpha : k)) • (B ^ 2 * D)
  + (-(4 / 27 * alpha : k)) • (B * C ^ 2)
  + (4 / 9 * alpha : k) • (D * E)
  + (5 / 144 * delta : k) • (A ^ 2 * C)
  + (5 / 432 * delta : k) • (A * B ^ 2)
  + (5 / 36 * delta : k) • (A * E)
  + (-(5 / 36 * delta : k)) • (B * D)
  + (-(5 / 72 * delta : k)) • C ^ 2
  + (-(2 / 9 * epsilon : k)) • (B * C)
  + (5 / 432 * zeta : k) • A ^ 3
  + (1 / 12 * zeta : k) • (A * C)
  + (-(1 / 8 * zeta : k)) • B ^ 2
  + (1 / 2 * zeta : k) • E

set_option maxHeartbeats 64000000 in

def degreeZeroN1CubicBCDEWallDeltaRest610_chunk1 (alpha delta epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (1 / 3 * eta : k) • D
  + (1 / 24 * theta : k) • A ^ 2
  + (1 / 6 * theta : k) • C

def degreeZeroN1CubicBCDEWallDeltaRest610 (alpha delta epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (degreeZeroN1CubicBCDEWallDeltaRest610_chunk0 alpha delta epsilon zeta eta theta A B C D E) +
  (degreeZeroN1CubicBCDEWallDeltaRest610_chunk1 alpha delta epsilon zeta eta theta A B C D E)

set_option maxHeartbeats 64000000 in
theorem degreeZeroN1CubicBCDEWallDeltaRest610_chunk0_natDegree_lt
    (alpha delta epsilon zeta eta theta : k) (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeBCDE610 A B C D E)
    (hwall : 7 * (9 * A.natDegree) = 30 * A.natDegree + 42 * B.natDegree) :
    (degreeZeroN1CubicBCDEWallDeltaRest610_chunk0 alpha delta epsilon zeta eta theta A B C D E).natDegree < 4 * A.natDegree := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hCne, hDne, hEne, heq1, heq2, heq3⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsAB : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAB
  have hsAC : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hAC
  have hsAD : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hAD
  have hsAE : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAE
  have eqC : 2 * C.natDegree = A.natDegree + 2 * B.natDegree := by omega
  have eqD : 4 * D.natDegree = A.natDegree + 6 * B.natDegree := by omega
  have eqE : 4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree := by omega
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hwall' : 14 * B.natDegree = 11 * A.natDegree := by omega
  have hface : A.natDegree + 2 * B.natDegree + D.natDegree = 4 * A.natDegree := by omega
  have hBpos : 0 + 1 ≤ B.natDegree := by omega
  have hCpos : 0 + 1 ≤ C.natDegree := by omega
  have hDpos : 0 + 1 ≤ D.natDegree := by omega
  have hEpos : 0 + 1 ≤ E.natDegree := by omega
  simp only [degreeZeroN1CubicBCDEWallDeltaRest610_chunk0, hpow2, hpow3, hpow4, hpow5,
    zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add,
    zero_pow, Nat.succ_ne_zero, sub_zero, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem degreeZeroN1CubicBCDEWallDeltaRest610_chunk1_natDegree_lt
    (alpha delta epsilon zeta eta theta : k) (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeBCDE610 A B C D E)
    (hwall : 7 * (9 * A.natDegree) = 30 * A.natDegree + 42 * B.natDegree) :
    (degreeZeroN1CubicBCDEWallDeltaRest610_chunk1 alpha delta epsilon zeta eta theta A B C D E).natDegree < 4 * A.natDegree := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hCne, hDne, hEne, heq1, heq2, heq3⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsAB : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAB
  have hsAC : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hAC
  have hsAD : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hAD
  have hsAE : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAE
  have eqC : 2 * C.natDegree = A.natDegree + 2 * B.natDegree := by omega
  have eqD : 4 * D.natDegree = A.natDegree + 6 * B.natDegree := by omega
  have eqE : 4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree := by omega
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hwall' : 14 * B.natDegree = 11 * A.natDegree := by omega
  have hface : A.natDegree + 2 * B.natDegree + D.natDegree = 4 * A.natDegree := by omega
  have hBpos : 0 + 1 ≤ B.natDegree := by omega
  have hCpos : 0 + 1 ≤ C.natDegree := by omega
  have hDpos : 0 + 1 ≤ D.natDegree := by omega
  have hEpos : 0 + 1 ≤ E.natDegree := by omega
  simp only [degreeZeroN1CubicBCDEWallDeltaRest610_chunk1, hpow2, hpow3, hpow4, hpow5,
    zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add,
    zero_pow, Nat.succ_ne_zero, sub_zero, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem degreeZeroN1CubicBCDEWallDeltaRest610_natDegree_lt
    (alpha delta epsilon zeta eta theta : k) (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeBCDE610 A B C D E)
    (hwall : 7 * (9 * A.natDegree) = 30 * A.natDegree + 42 * B.natDegree) :
    (degreeZeroN1CubicBCDEWallDeltaRest610 alpha delta epsilon zeta eta theta A B C D E).natDegree < 4 * A.natDegree := by
  simp only [degreeZeroN1CubicBCDEWallDeltaRest610]
  have h0 := degreeZeroN1CubicBCDEWallDeltaRest610_chunk0_natDegree_lt alpha delta epsilon zeta eta theta A B C D E hcone hwall
  have h1 := degreeZeroN1CubicBCDEWallDeltaRest610_chunk1_natDegree_lt alpha delta epsilon zeta eta theta A B C D E hcone hwall
  have hadd := natDegree_add_le (degreeZeroN1CubicBCDEWallDeltaRest610_chunk0 alpha delta epsilon zeta eta theta A B C D E) (degreeZeroN1CubicBCDEWallDeltaRest610_chunk1 alpha delta epsilon zeta eta theta A B C D E)
  exact lt_of_le_of_lt hadd (max_lt h0 h1)


/-! `N1` rest on `BCDE` `zeta` wall: 13 monomials. -/

set_option maxHeartbeats 64000000 in

def degreeZeroN1CubicBCDEWallZetaRest610 (alpha epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (20 / 243 : k) • (B ^ 3 * C)
  + (-(5 / 27 : k)) • (B * D ^ 2)
  + (4 / 243 * alpha : k) • (A * B ^ 3)
  + (-(4 / 27 * alpha : k)) • (B ^ 2 * D)
  + (-(4 / 27 * alpha : k)) • (B * C ^ 2)
  + (4 / 9 * alpha : k) • (D * E)
  + (-(2 / 9 * epsilon : k)) • (B * C)
  + (1 / 12 * zeta : k) • (A * C)
  + (-(1 / 8 * zeta : k)) • B ^ 2
  + (1 / 2 * zeta : k) • E
  + (1 / 3 * eta : k) • D
  + (1 / 24 * theta : k) • A ^ 2
  + (1 / 6 * theta : k) • C

set_option maxHeartbeats 64000000 in
theorem degreeZeroN1CubicBCDEWallZetaRest610_natDegree_lt
    (alpha epsilon zeta eta theta : k) (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeBCDE610 A B C D E)
    (hwall : 9 * A.natDegree = 6 * A.natDegree + 6 * B.natDegree) :
    (degreeZeroN1CubicBCDEWallZetaRest610 alpha epsilon zeta eta theta A B C D E).natDegree < 3 * A.natDegree := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hCne, hDne, hEne, heq1, heq2, heq3⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsAB : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAB
  have hsAC : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hAC
  have hsAD : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hAD
  have hsAE : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAE
  have eqC : 2 * C.natDegree = A.natDegree + 2 * B.natDegree := by omega
  have eqD : 4 * D.natDegree = A.natDegree + 6 * B.natDegree := by omega
  have eqE : 4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree := by omega
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hwall' : 2 * B.natDegree = A.natDegree := by omega
  have hface : A.natDegree + 2 * B.natDegree + D.natDegree = 3 * A.natDegree := by omega
  have hBpos : 0 + 1 ≤ B.natDegree := by omega
  have hCpos : 0 + 1 ≤ C.natDegree := by omega
  have hDpos : 0 + 1 ≤ D.natDegree := by omega
  have hEpos : 0 + 1 ≤ E.natDegree := by omega
  simp only [degreeZeroN1CubicBCDEWallZetaRest610, hpow2, hpow3, hpow4, hpow5,
    zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add,
    zero_pow, Nat.succ_ne_zero, sub_zero, neg_zero, natDegree_zero]
  compute_degree
  omega


/-! `N1` rest on `BCDE` `theta` wall: 9 monomials. -/

set_option maxHeartbeats 64000000 in

def degreeZeroN1CubicBCDEWallThetaRest610 (alpha epsilon eta theta : k) (A B C D E : k[X]) : k[X] :=
  (20 / 243 : k) • (B ^ 3 * C)
  + (-(5 / 27 : k)) • (B * D ^ 2)
  + (4 / 243 * alpha : k) • (A * B ^ 3)
  + (-(4 / 27 * alpha : k)) • (B ^ 2 * D)
  + (-(4 / 27 * alpha : k)) • (B * C ^ 2)
  + (4 / 9 * alpha : k) • (D * E)
  + (-(2 / 9 * epsilon : k)) • (B * C)
  + (1 / 3 * eta : k) • D
  + (1 / 6 * theta : k) • C

set_option maxHeartbeats 64000000 in
theorem degreeZeroN1CubicBCDEWallThetaRest610_natDegree_lt
    (alpha epsilon eta theta : k) (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeBCDE610 A B C D E)
    (hwall : 7 * (9 * A.natDegree) = 54 * A.natDegree + 42 * B.natDegree) :
    (degreeZeroN1CubicBCDEWallThetaRest610 alpha epsilon eta theta A B C D E).natDegree < 2 * A.natDegree := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hCne, hDne, hEne, heq1, heq2, heq3⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsAB : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAB
  have hsAC : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hAC
  have hsAD : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hAD
  have hsAE : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAE
  have eqC : 2 * C.natDegree = A.natDegree + 2 * B.natDegree := by omega
  have eqD : 4 * D.natDegree = A.natDegree + 6 * B.natDegree := by omega
  have eqE : 4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree := by omega
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hwall' : 14 * B.natDegree = 3 * A.natDegree := by omega
  have hface : A.natDegree + 2 * B.natDegree + D.natDegree = 2 * A.natDegree := by omega
  have hBpos : 0 + 1 ≤ B.natDegree := by omega
  have hCpos : 0 + 1 ≤ C.natDegree := by omega
  have hDpos : 0 + 1 ≤ D.natDegree := by omega
  have hEpos : 0 + 1 ≤ E.natDegree := by omega
  simp only [degreeZeroN1CubicBCDEWallThetaRest610, hpow2, hpow3, hpow4, hpow5,
    zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add,
    zero_pow, Nat.succ_ne_zero, sub_zero, neg_zero, natDegree_zero]
  compute_degree
  omega


/-! `N2` rest on `BCDE` `beta` wall: 50 monomials. -/

set_option maxHeartbeats 64000000 in

def degreeZeroN2CubicBCDEWallBetaRest610_chunk0 (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (-(25 / 243 : k)) • (A * B ^ 3 * C)
  + (-(4 / 243 : k)) • B ^ 5
  + (5 / 27 : k) • (A * B * D ^ 2)
  + (10 / 81 : k) • (B ^ 3 * E)
  + (5 / 9 : k) • (B ^ 2 * C * D)
  + (5 / 27 : k) • (B * C ^ 3)
  + (-(10 / 9 : k)) • (C * D * E)
  + (-(10 / 27 : k)) • D ^ 3
  + (-(4 / 243 * alpha : k)) • (A ^ 2 * B ^ 3)
  + (4 / 27 * alpha : k) • (A * B ^ 2 * D)
  + (4 / 27 * alpha : k) • (A * B * C ^ 2)
  + (4 / 27 * alpha : k) • (B ^ 3 * C)
  + (-(4 / 9 * alpha : k)) • (A * D * E)
  + (-(4 / 9 * alpha : k)) • (B * C * E)
  + (-(4 / 9 * alpha : k)) • (B * D ^ 2)
  + (-(4 / 9 * alpha : k)) • (C ^ 2 * D)

set_option maxHeartbeats 64000000 in

def degreeZeroN2CubicBCDEWallBetaRest610_chunk1 (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (35 / 2592 * beta : k) • (A ^ 4 * C)
  + (-(7 / 1296 * beta : k)) • (A ^ 3 * B ^ 2)
  + (7 / 216 * beta : k) • (A ^ 3 * E)
  + (-(7 / 432 * beta : k)) • (A ^ 2 * B * D)
  + (49 / 864 * beta : k) • (A ^ 2 * C ^ 2)
  + (35 / 432 * beta : k) • (A * B ^ 2 * C)
  + (35 / 1728 * beta : k) • B ^ 4
  + (7 / 36 * beta : k) • (A * C * E)
  + (-(7 / 36 * beta : k)) • (A * D ^ 2)
  + (-(7 / 72 * beta : k)) • (B ^ 2 * E)
  + (-(7 / 18 * beta : k)) • (B * C * D)
  + (-(7 / 108 * beta : k)) • C ^ 3
  + (7 / 12 * beta : k) • E ^ 2
  + (7 / 2592 * delta : k) • A ^ 5
  + (5 / 144 * delta : k) • (A ^ 3 * C)
  + (-(25 / 864 * delta : k)) • (A ^ 2 * B ^ 2)

set_option maxHeartbeats 64000000 in

def degreeZeroN2CubicBCDEWallBetaRest610_chunk2 (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (5 / 72 * delta : k) • (A ^ 2 * E)
  + (5 / 36 * delta : k) • (A * C ^ 2)
  + (5 / 36 * delta : k) • (B ^ 2 * C)
  + (-(5 / 12 * delta : k)) • D ^ 2
  + (2 / 9 * epsilon : k) • (A * B * C)
  + (2 / 27 * epsilon : k) • B ^ 3
  + (-(2 / 3 * epsilon : k)) • (C * D)
  + (5 / 576 * zeta : k) • A ^ 4
  + (1 / 12 * zeta : k) • (A ^ 2 * C)
  + (1 / 12 * zeta : k) • (A * B ^ 2)
  + (-(1 / 2 * zeta : k)) • (B * D)
  + (-(1 / 4 * zeta : k)) • C ^ 2
  + (-(1 / 3 * eta : k)) • (A * D)
  + (-(1 / 3 * eta : k)) • (B * C)
  + (1 / 36 * theta : k) • A ^ 3
  + (1 / 6 * theta : k) • (A * C)

set_option maxHeartbeats 64000000 in

def degreeZeroN2CubicBCDEWallBetaRest610_chunk3 (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (-(1 / 12 * theta : k)) • B ^ 2
  + (1 * theta : k) • E

def degreeZeroN2CubicBCDEWallBetaRest610 (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (degreeZeroN2CubicBCDEWallBetaRest610_chunk0 alpha beta delta epsilon zeta eta theta A B C D E) +
  (degreeZeroN2CubicBCDEWallBetaRest610_chunk1 alpha beta delta epsilon zeta eta theta A B C D E) +
  (degreeZeroN2CubicBCDEWallBetaRest610_chunk2 alpha beta delta epsilon zeta eta theta A B C D E) +
  (degreeZeroN2CubicBCDEWallBetaRest610_chunk3 alpha beta delta epsilon zeta eta theta A B C D E)

set_option maxHeartbeats 64000000 in
theorem degreeZeroN2CubicBCDEWallBetaRest610_chunk0_natDegree_lt
    (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeBCDE610 A B C D E)
    (hwall : 7 * (9 * A.natDegree) = 18 * A.natDegree + 42 * B.natDegree) :
    (degreeZeroN2CubicBCDEWallBetaRest610_chunk0 alpha beta delta epsilon zeta eta theta A B C D E).natDegree < 6 * A.natDegree := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hCne, hDne, hEne, heq1, heq2, heq3⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsAB : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAB
  have hsAC : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hAC
  have hsAD : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hAD
  have hsAE : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAE
  have eqC : 2 * C.natDegree = A.natDegree + 2 * B.natDegree := by omega
  have eqD : 4 * D.natDegree = A.natDegree + 6 * B.natDegree := by omega
  have eqE : 4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree := by omega
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hwall' : 14 * B.natDegree = 15 * A.natDegree := by omega
  have hface : A.natDegree + 2 * B.natDegree + D.natDegree = 5 * A.natDegree := by omega
  have hBpos : 0 + 1 ≤ B.natDegree := by omega
  have hCpos : 0 + 1 ≤ C.natDegree := by omega
  have hDpos : 0 + 1 ≤ D.natDegree := by omega
  have hEpos : 0 + 1 ≤ E.natDegree := by omega
  simp only [degreeZeroN2CubicBCDEWallBetaRest610_chunk0, hpow2, hpow3, hpow4, hpow5,
    zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add,
    zero_pow, Nat.succ_ne_zero, sub_zero, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem degreeZeroN2CubicBCDEWallBetaRest610_chunk1_natDegree_lt
    (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeBCDE610 A B C D E)
    (hwall : 7 * (9 * A.natDegree) = 18 * A.natDegree + 42 * B.natDegree) :
    (degreeZeroN2CubicBCDEWallBetaRest610_chunk1 alpha beta delta epsilon zeta eta theta A B C D E).natDegree < 6 * A.natDegree := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hCne, hDne, hEne, heq1, heq2, heq3⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsAB : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAB
  have hsAC : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hAC
  have hsAD : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hAD
  have hsAE : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAE
  have eqC : 2 * C.natDegree = A.natDegree + 2 * B.natDegree := by omega
  have eqD : 4 * D.natDegree = A.natDegree + 6 * B.natDegree := by omega
  have eqE : 4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree := by omega
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hwall' : 14 * B.natDegree = 15 * A.natDegree := by omega
  have hface : A.natDegree + 2 * B.natDegree + D.natDegree = 5 * A.natDegree := by omega
  have hBpos : 0 + 1 ≤ B.natDegree := by omega
  have hCpos : 0 + 1 ≤ C.natDegree := by omega
  have hDpos : 0 + 1 ≤ D.natDegree := by omega
  have hEpos : 0 + 1 ≤ E.natDegree := by omega
  simp only [degreeZeroN2CubicBCDEWallBetaRest610_chunk1, hpow2, hpow3, hpow4, hpow5,
    zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add,
    zero_pow, Nat.succ_ne_zero, sub_zero, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem degreeZeroN2CubicBCDEWallBetaRest610_chunk2_natDegree_lt
    (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeBCDE610 A B C D E)
    (hwall : 7 * (9 * A.natDegree) = 18 * A.natDegree + 42 * B.natDegree) :
    (degreeZeroN2CubicBCDEWallBetaRest610_chunk2 alpha beta delta epsilon zeta eta theta A B C D E).natDegree < 6 * A.natDegree := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hCne, hDne, hEne, heq1, heq2, heq3⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsAB : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAB
  have hsAC : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hAC
  have hsAD : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hAD
  have hsAE : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAE
  have eqC : 2 * C.natDegree = A.natDegree + 2 * B.natDegree := by omega
  have eqD : 4 * D.natDegree = A.natDegree + 6 * B.natDegree := by omega
  have eqE : 4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree := by omega
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hwall' : 14 * B.natDegree = 15 * A.natDegree := by omega
  have hface : A.natDegree + 2 * B.natDegree + D.natDegree = 5 * A.natDegree := by omega
  have hBpos : 0 + 1 ≤ B.natDegree := by omega
  have hCpos : 0 + 1 ≤ C.natDegree := by omega
  have hDpos : 0 + 1 ≤ D.natDegree := by omega
  have hEpos : 0 + 1 ≤ E.natDegree := by omega
  simp only [degreeZeroN2CubicBCDEWallBetaRest610_chunk2, hpow2, hpow3, hpow4, hpow5,
    zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add,
    zero_pow, Nat.succ_ne_zero, sub_zero, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem degreeZeroN2CubicBCDEWallBetaRest610_chunk3_natDegree_lt
    (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeBCDE610 A B C D E)
    (hwall : 7 * (9 * A.natDegree) = 18 * A.natDegree + 42 * B.natDegree) :
    (degreeZeroN2CubicBCDEWallBetaRest610_chunk3 alpha beta delta epsilon zeta eta theta A B C D E).natDegree < 6 * A.natDegree := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hCne, hDne, hEne, heq1, heq2, heq3⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsAB : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAB
  have hsAC : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hAC
  have hsAD : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hAD
  have hsAE : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAE
  have eqC : 2 * C.natDegree = A.natDegree + 2 * B.natDegree := by omega
  have eqD : 4 * D.natDegree = A.natDegree + 6 * B.natDegree := by omega
  have eqE : 4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree := by omega
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hwall' : 14 * B.natDegree = 15 * A.natDegree := by omega
  have hface : A.natDegree + 2 * B.natDegree + D.natDegree = 5 * A.natDegree := by omega
  have hBpos : 0 + 1 ≤ B.natDegree := by omega
  have hCpos : 0 + 1 ≤ C.natDegree := by omega
  have hDpos : 0 + 1 ≤ D.natDegree := by omega
  have hEpos : 0 + 1 ≤ E.natDegree := by omega
  simp only [degreeZeroN2CubicBCDEWallBetaRest610_chunk3, hpow2, hpow3, hpow4, hpow5,
    zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add,
    zero_pow, Nat.succ_ne_zero, sub_zero, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem degreeZeroN2CubicBCDEWallBetaRest610_natDegree_lt
    (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeBCDE610 A B C D E)
    (hwall : 7 * (9 * A.natDegree) = 18 * A.natDegree + 42 * B.natDegree) :
    (degreeZeroN2CubicBCDEWallBetaRest610 alpha beta delta epsilon zeta eta theta A B C D E).natDegree < 6 * A.natDegree := by
  simp only [degreeZeroN2CubicBCDEWallBetaRest610]
  have h0 := degreeZeroN2CubicBCDEWallBetaRest610_chunk0_natDegree_lt alpha beta delta epsilon zeta eta theta A B C D E hcone hwall
  have h1 := degreeZeroN2CubicBCDEWallBetaRest610_chunk1_natDegree_lt alpha beta delta epsilon zeta eta theta A B C D E hcone hwall
  have h2 := degreeZeroN2CubicBCDEWallBetaRest610_chunk2_natDegree_lt alpha beta delta epsilon zeta eta theta A B C D E hcone hwall
  have h3 := degreeZeroN2CubicBCDEWallBetaRest610_chunk3_natDegree_lt alpha beta delta epsilon zeta eta theta A B C D E hcone hwall
  have hadd01 := natDegree_add_le (degreeZeroN2CubicBCDEWallBetaRest610_chunk0 alpha beta delta epsilon zeta eta theta A B C D E) (degreeZeroN2CubicBCDEWallBetaRest610_chunk1 alpha beta delta epsilon zeta eta theta A B C D E)
  have hadd012 := natDegree_add_le ((degreeZeroN2CubicBCDEWallBetaRest610_chunk0 alpha beta delta epsilon zeta eta theta A B C D E) + (degreeZeroN2CubicBCDEWallBetaRest610_chunk1 alpha beta delta epsilon zeta eta theta A B C D E)) (degreeZeroN2CubicBCDEWallBetaRest610_chunk2 alpha beta delta epsilon zeta eta theta A B C D E)
  have hadd := natDegree_add_le (((degreeZeroN2CubicBCDEWallBetaRest610_chunk0 alpha beta delta epsilon zeta eta theta A B C D E) + (degreeZeroN2CubicBCDEWallBetaRest610_chunk1 alpha beta delta epsilon zeta eta theta A B C D E)) + (degreeZeroN2CubicBCDEWallBetaRest610_chunk2 alpha beta delta epsilon zeta eta theta A B C D E)) (degreeZeroN2CubicBCDEWallBetaRest610_chunk3 alpha beta delta epsilon zeta eta theta A B C D E)
  exact lt_of_le_of_lt hadd (max_lt (lt_of_le_of_lt hadd012 (max_lt (lt_of_le_of_lt hadd01 (max_lt h0 h1)) h2)) h3)


/-! `N2` rest on `BCDE` `delta` wall: 36 monomials. -/

set_option maxHeartbeats 64000000 in

def degreeZeroN2CubicBCDEWallDeltaRest610_chunk0 (alpha delta epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (-(25 / 243 : k)) • (A * B ^ 3 * C)
  + (-(4 / 243 : k)) • B ^ 5
  + (5 / 27 : k) • (A * B * D ^ 2)
  + (10 / 81 : k) • (B ^ 3 * E)
  + (5 / 9 : k) • (B ^ 2 * C * D)
  + (5 / 27 : k) • (B * C ^ 3)
  + (-(10 / 9 : k)) • (C * D * E)
  + (-(10 / 27 : k)) • D ^ 3
  + (-(4 / 243 * alpha : k)) • (A ^ 2 * B ^ 3)
  + (4 / 27 * alpha : k) • (A * B ^ 2 * D)
  + (4 / 27 * alpha : k) • (A * B * C ^ 2)
  + (4 / 27 * alpha : k) • (B ^ 3 * C)
  + (-(4 / 9 * alpha : k)) • (A * D * E)
  + (-(4 / 9 * alpha : k)) • (B * C * E)
  + (-(4 / 9 * alpha : k)) • (B * D ^ 2)
  + (-(4 / 9 * alpha : k)) • (C ^ 2 * D)

set_option maxHeartbeats 64000000 in

def degreeZeroN2CubicBCDEWallDeltaRest610_chunk1 (alpha delta epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (5 / 144 * delta : k) • (A ^ 3 * C)
  + (-(25 / 864 * delta : k)) • (A ^ 2 * B ^ 2)
  + (5 / 72 * delta : k) • (A ^ 2 * E)
  + (5 / 36 * delta : k) • (A * C ^ 2)
  + (5 / 36 * delta : k) • (B ^ 2 * C)
  + (-(5 / 12 * delta : k)) • D ^ 2
  + (2 / 9 * epsilon : k) • (A * B * C)
  + (2 / 27 * epsilon : k) • B ^ 3
  + (-(2 / 3 * epsilon : k)) • (C * D)
  + (5 / 576 * zeta : k) • A ^ 4
  + (1 / 12 * zeta : k) • (A ^ 2 * C)
  + (1 / 12 * zeta : k) • (A * B ^ 2)
  + (-(1 / 2 * zeta : k)) • (B * D)
  + (-(1 / 4 * zeta : k)) • C ^ 2
  + (-(1 / 3 * eta : k)) • (A * D)
  + (-(1 / 3 * eta : k)) • (B * C)

set_option maxHeartbeats 64000000 in

def degreeZeroN2CubicBCDEWallDeltaRest610_chunk2 (alpha delta epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (1 / 36 * theta : k) • A ^ 3
  + (1 / 6 * theta : k) • (A * C)
  + (-(1 / 12 * theta : k)) • B ^ 2
  + (1 * theta : k) • E

def degreeZeroN2CubicBCDEWallDeltaRest610 (alpha delta epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (degreeZeroN2CubicBCDEWallDeltaRest610_chunk0 alpha delta epsilon zeta eta theta A B C D E) +
  (degreeZeroN2CubicBCDEWallDeltaRest610_chunk1 alpha delta epsilon zeta eta theta A B C D E) +
  (degreeZeroN2CubicBCDEWallDeltaRest610_chunk2 alpha delta epsilon zeta eta theta A B C D E)

set_option maxHeartbeats 64000000 in
theorem degreeZeroN2CubicBCDEWallDeltaRest610_chunk0_natDegree_lt
    (alpha delta epsilon zeta eta theta : k) (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeBCDE610 A B C D E)
    (hwall : 7 * (9 * A.natDegree) = 30 * A.natDegree + 42 * B.natDegree) :
    (degreeZeroN2CubicBCDEWallDeltaRest610_chunk0 alpha delta epsilon zeta eta theta A B C D E).natDegree < 5 * A.natDegree := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hCne, hDne, hEne, heq1, heq2, heq3⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsAB : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAB
  have hsAC : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hAC
  have hsAD : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hAD
  have hsAE : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAE
  have eqC : 2 * C.natDegree = A.natDegree + 2 * B.natDegree := by omega
  have eqD : 4 * D.natDegree = A.natDegree + 6 * B.natDegree := by omega
  have eqE : 4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree := by omega
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hwall' : 14 * B.natDegree = 11 * A.natDegree := by omega
  have hface : A.natDegree + 2 * B.natDegree + D.natDegree = 4 * A.natDegree := by omega
  have hBpos : 0 + 1 ≤ B.natDegree := by omega
  have hCpos : 0 + 1 ≤ C.natDegree := by omega
  have hDpos : 0 + 1 ≤ D.natDegree := by omega
  have hEpos : 0 + 1 ≤ E.natDegree := by omega
  simp only [degreeZeroN2CubicBCDEWallDeltaRest610_chunk0, hpow2, hpow3, hpow4, hpow5,
    zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add,
    zero_pow, Nat.succ_ne_zero, sub_zero, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem degreeZeroN2CubicBCDEWallDeltaRest610_chunk1_natDegree_lt
    (alpha delta epsilon zeta eta theta : k) (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeBCDE610 A B C D E)
    (hwall : 7 * (9 * A.natDegree) = 30 * A.natDegree + 42 * B.natDegree) :
    (degreeZeroN2CubicBCDEWallDeltaRest610_chunk1 alpha delta epsilon zeta eta theta A B C D E).natDegree < 5 * A.natDegree := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hCne, hDne, hEne, heq1, heq2, heq3⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsAB : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAB
  have hsAC : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hAC
  have hsAD : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hAD
  have hsAE : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAE
  have eqC : 2 * C.natDegree = A.natDegree + 2 * B.natDegree := by omega
  have eqD : 4 * D.natDegree = A.natDegree + 6 * B.natDegree := by omega
  have eqE : 4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree := by omega
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hwall' : 14 * B.natDegree = 11 * A.natDegree := by omega
  have hface : A.natDegree + 2 * B.natDegree + D.natDegree = 4 * A.natDegree := by omega
  have hBpos : 0 + 1 ≤ B.natDegree := by omega
  have hCpos : 0 + 1 ≤ C.natDegree := by omega
  have hDpos : 0 + 1 ≤ D.natDegree := by omega
  have hEpos : 0 + 1 ≤ E.natDegree := by omega
  simp only [degreeZeroN2CubicBCDEWallDeltaRest610_chunk1, hpow2, hpow3, hpow4, hpow5,
    zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add,
    zero_pow, Nat.succ_ne_zero, sub_zero, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem degreeZeroN2CubicBCDEWallDeltaRest610_chunk2_natDegree_lt
    (alpha delta epsilon zeta eta theta : k) (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeBCDE610 A B C D E)
    (hwall : 7 * (9 * A.natDegree) = 30 * A.natDegree + 42 * B.natDegree) :
    (degreeZeroN2CubicBCDEWallDeltaRest610_chunk2 alpha delta epsilon zeta eta theta A B C D E).natDegree < 5 * A.natDegree := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hCne, hDne, hEne, heq1, heq2, heq3⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsAB : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAB
  have hsAC : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hAC
  have hsAD : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hAD
  have hsAE : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAE
  have eqC : 2 * C.natDegree = A.natDegree + 2 * B.natDegree := by omega
  have eqD : 4 * D.natDegree = A.natDegree + 6 * B.natDegree := by omega
  have eqE : 4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree := by omega
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hwall' : 14 * B.natDegree = 11 * A.natDegree := by omega
  have hface : A.natDegree + 2 * B.natDegree + D.natDegree = 4 * A.natDegree := by omega
  have hBpos : 0 + 1 ≤ B.natDegree := by omega
  have hCpos : 0 + 1 ≤ C.natDegree := by omega
  have hDpos : 0 + 1 ≤ D.natDegree := by omega
  have hEpos : 0 + 1 ≤ E.natDegree := by omega
  simp only [degreeZeroN2CubicBCDEWallDeltaRest610_chunk2, hpow2, hpow3, hpow4, hpow5,
    zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add,
    zero_pow, Nat.succ_ne_zero, sub_zero, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem degreeZeroN2CubicBCDEWallDeltaRest610_natDegree_lt
    (alpha delta epsilon zeta eta theta : k) (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeBCDE610 A B C D E)
    (hwall : 7 * (9 * A.natDegree) = 30 * A.natDegree + 42 * B.natDegree) :
    (degreeZeroN2CubicBCDEWallDeltaRest610 alpha delta epsilon zeta eta theta A B C D E).natDegree < 5 * A.natDegree := by
  simp only [degreeZeroN2CubicBCDEWallDeltaRest610]
  have h0 := degreeZeroN2CubicBCDEWallDeltaRest610_chunk0_natDegree_lt alpha delta epsilon zeta eta theta A B C D E hcone hwall
  have h1 := degreeZeroN2CubicBCDEWallDeltaRest610_chunk1_natDegree_lt alpha delta epsilon zeta eta theta A B C D E hcone hwall
  have h2 := degreeZeroN2CubicBCDEWallDeltaRest610_chunk2_natDegree_lt alpha delta epsilon zeta eta theta A B C D E hcone hwall
  have hadd01 := natDegree_add_le (degreeZeroN2CubicBCDEWallDeltaRest610_chunk0 alpha delta epsilon zeta eta theta A B C D E) (degreeZeroN2CubicBCDEWallDeltaRest610_chunk1 alpha delta epsilon zeta eta theta A B C D E)
  have hadd := natDegree_add_le ((degreeZeroN2CubicBCDEWallDeltaRest610_chunk0 alpha delta epsilon zeta eta theta A B C D E) + (degreeZeroN2CubicBCDEWallDeltaRest610_chunk1 alpha delta epsilon zeta eta theta A B C D E)) (degreeZeroN2CubicBCDEWallDeltaRest610_chunk2 alpha delta epsilon zeta eta theta A B C D E)
  exact lt_of_le_of_lt hadd (max_lt (lt_of_le_of_lt hadd01 (max_lt h0 h1)) h2)


/-! `N2` rest on `BCDE` `zeta` wall: 29 monomials. -/

set_option maxHeartbeats 64000000 in

def degreeZeroN2CubicBCDEWallZetaRest610_chunk0 (alpha epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (-(25 / 243 : k)) • (A * B ^ 3 * C)
  + (-(4 / 243 : k)) • B ^ 5
  + (5 / 27 : k) • (A * B * D ^ 2)
  + (10 / 81 : k) • (B ^ 3 * E)
  + (5 / 9 : k) • (B ^ 2 * C * D)
  + (5 / 27 : k) • (B * C ^ 3)
  + (-(10 / 9 : k)) • (C * D * E)
  + (-(10 / 27 : k)) • D ^ 3
  + (-(4 / 243 * alpha : k)) • (A ^ 2 * B ^ 3)
  + (4 / 27 * alpha : k) • (A * B ^ 2 * D)
  + (4 / 27 * alpha : k) • (A * B * C ^ 2)
  + (4 / 27 * alpha : k) • (B ^ 3 * C)
  + (-(4 / 9 * alpha : k)) • (A * D * E)
  + (-(4 / 9 * alpha : k)) • (B * C * E)
  + (-(4 / 9 * alpha : k)) • (B * D ^ 2)
  + (-(4 / 9 * alpha : k)) • (C ^ 2 * D)

set_option maxHeartbeats 64000000 in

def degreeZeroN2CubicBCDEWallZetaRest610_chunk1 (alpha epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (2 / 9 * epsilon : k) • (A * B * C)
  + (2 / 27 * epsilon : k) • B ^ 3
  + (-(2 / 3 * epsilon : k)) • (C * D)
  + (1 / 12 * zeta : k) • (A ^ 2 * C)
  + (1 / 12 * zeta : k) • (A * B ^ 2)
  + (-(1 / 2 * zeta : k)) • (B * D)
  + (-(1 / 4 * zeta : k)) • C ^ 2
  + (-(1 / 3 * eta : k)) • (A * D)
  + (-(1 / 3 * eta : k)) • (B * C)
  + (1 / 36 * theta : k) • A ^ 3
  + (1 / 6 * theta : k) • (A * C)
  + (-(1 / 12 * theta : k)) • B ^ 2
  + (1 * theta : k) • E

def degreeZeroN2CubicBCDEWallZetaRest610 (alpha epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (degreeZeroN2CubicBCDEWallZetaRest610_chunk0 alpha epsilon zeta eta theta A B C D E) +
  (degreeZeroN2CubicBCDEWallZetaRest610_chunk1 alpha epsilon zeta eta theta A B C D E)

set_option maxHeartbeats 64000000 in
theorem degreeZeroN2CubicBCDEWallZetaRest610_chunk0_natDegree_lt
    (alpha epsilon zeta eta theta : k) (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeBCDE610 A B C D E)
    (hwall : 9 * A.natDegree = 6 * A.natDegree + 6 * B.natDegree) :
    (degreeZeroN2CubicBCDEWallZetaRest610_chunk0 alpha epsilon zeta eta theta A B C D E).natDegree < 4 * A.natDegree := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hCne, hDne, hEne, heq1, heq2, heq3⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsAB : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAB
  have hsAC : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hAC
  have hsAD : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hAD
  have hsAE : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAE
  have eqC : 2 * C.natDegree = A.natDegree + 2 * B.natDegree := by omega
  have eqD : 4 * D.natDegree = A.natDegree + 6 * B.natDegree := by omega
  have eqE : 4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree := by omega
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hwall' : 2 * B.natDegree = A.natDegree := by omega
  have hface : A.natDegree + 2 * B.natDegree + D.natDegree = 3 * A.natDegree := by omega
  have hBpos : 0 + 1 ≤ B.natDegree := by omega
  have hCpos : 0 + 1 ≤ C.natDegree := by omega
  have hDpos : 0 + 1 ≤ D.natDegree := by omega
  have hEpos : 0 + 1 ≤ E.natDegree := by omega
  simp only [degreeZeroN2CubicBCDEWallZetaRest610_chunk0, hpow2, hpow3, hpow4, hpow5,
    zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add,
    zero_pow, Nat.succ_ne_zero, sub_zero, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem degreeZeroN2CubicBCDEWallZetaRest610_chunk1_natDegree_lt
    (alpha epsilon zeta eta theta : k) (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeBCDE610 A B C D E)
    (hwall : 9 * A.natDegree = 6 * A.natDegree + 6 * B.natDegree) :
    (degreeZeroN2CubicBCDEWallZetaRest610_chunk1 alpha epsilon zeta eta theta A B C D E).natDegree < 4 * A.natDegree := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hCne, hDne, hEne, heq1, heq2, heq3⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsAB : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAB
  have hsAC : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hAC
  have hsAD : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hAD
  have hsAE : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAE
  have eqC : 2 * C.natDegree = A.natDegree + 2 * B.natDegree := by omega
  have eqD : 4 * D.natDegree = A.natDegree + 6 * B.natDegree := by omega
  have eqE : 4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree := by omega
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hwall' : 2 * B.natDegree = A.natDegree := by omega
  have hface : A.natDegree + 2 * B.natDegree + D.natDegree = 3 * A.natDegree := by omega
  have hBpos : 0 + 1 ≤ B.natDegree := by omega
  have hCpos : 0 + 1 ≤ C.natDegree := by omega
  have hDpos : 0 + 1 ≤ D.natDegree := by omega
  have hEpos : 0 + 1 ≤ E.natDegree := by omega
  simp only [degreeZeroN2CubicBCDEWallZetaRest610_chunk1, hpow2, hpow3, hpow4, hpow5,
    zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add,
    zero_pow, Nat.succ_ne_zero, sub_zero, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem degreeZeroN2CubicBCDEWallZetaRest610_natDegree_lt
    (alpha epsilon zeta eta theta : k) (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeBCDE610 A B C D E)
    (hwall : 9 * A.natDegree = 6 * A.natDegree + 6 * B.natDegree) :
    (degreeZeroN2CubicBCDEWallZetaRest610 alpha epsilon zeta eta theta A B C D E).natDegree < 4 * A.natDegree := by
  simp only [degreeZeroN2CubicBCDEWallZetaRest610]
  have h0 := degreeZeroN2CubicBCDEWallZetaRest610_chunk0_natDegree_lt alpha epsilon zeta eta theta A B C D E hcone hwall
  have h1 := degreeZeroN2CubicBCDEWallZetaRest610_chunk1_natDegree_lt alpha epsilon zeta eta theta A B C D E hcone hwall
  have hadd := natDegree_add_le (degreeZeroN2CubicBCDEWallZetaRest610_chunk0 alpha epsilon zeta eta theta A B C D E) (degreeZeroN2CubicBCDEWallZetaRest610_chunk1 alpha epsilon zeta eta theta A B C D E)
  exact lt_of_le_of_lt hadd (max_lt h0 h1)


/-! `N2` rest on `BCDE` `theta` wall: 24 monomials. -/

set_option maxHeartbeats 64000000 in

def degreeZeroN2CubicBCDEWallThetaRest610_chunk0 (alpha epsilon eta theta : k) (A B C D E : k[X]) : k[X] :=
  (-(25 / 243 : k)) • (A * B ^ 3 * C)
  + (-(4 / 243 : k)) • B ^ 5
  + (5 / 27 : k) • (A * B * D ^ 2)
  + (10 / 81 : k) • (B ^ 3 * E)
  + (5 / 9 : k) • (B ^ 2 * C * D)
  + (5 / 27 : k) • (B * C ^ 3)
  + (-(10 / 9 : k)) • (C * D * E)
  + (-(10 / 27 : k)) • D ^ 3
  + (-(4 / 243 * alpha : k)) • (A ^ 2 * B ^ 3)
  + (4 / 27 * alpha : k) • (A * B ^ 2 * D)
  + (4 / 27 * alpha : k) • (A * B * C ^ 2)
  + (4 / 27 * alpha : k) • (B ^ 3 * C)
  + (-(4 / 9 * alpha : k)) • (A * D * E)
  + (-(4 / 9 * alpha : k)) • (B * C * E)
  + (-(4 / 9 * alpha : k)) • (B * D ^ 2)
  + (-(4 / 9 * alpha : k)) • (C ^ 2 * D)

set_option maxHeartbeats 64000000 in

def degreeZeroN2CubicBCDEWallThetaRest610_chunk1 (alpha epsilon eta theta : k) (A B C D E : k[X]) : k[X] :=
  (2 / 9 * epsilon : k) • (A * B * C)
  + (2 / 27 * epsilon : k) • B ^ 3
  + (-(2 / 3 * epsilon : k)) • (C * D)
  + (-(1 / 3 * eta : k)) • (A * D)
  + (-(1 / 3 * eta : k)) • (B * C)
  + (1 / 6 * theta : k) • (A * C)
  + (-(1 / 12 * theta : k)) • B ^ 2
  + (1 * theta : k) • E

def degreeZeroN2CubicBCDEWallThetaRest610 (alpha epsilon eta theta : k) (A B C D E : k[X]) : k[X] :=
  (degreeZeroN2CubicBCDEWallThetaRest610_chunk0 alpha epsilon eta theta A B C D E) +
  (degreeZeroN2CubicBCDEWallThetaRest610_chunk1 alpha epsilon eta theta A B C D E)

set_option maxHeartbeats 64000000 in
theorem degreeZeroN2CubicBCDEWallThetaRest610_chunk0_natDegree_lt
    (alpha epsilon eta theta : k) (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeBCDE610 A B C D E)
    (hwall : 7 * (9 * A.natDegree) = 54 * A.natDegree + 42 * B.natDegree) :
    (degreeZeroN2CubicBCDEWallThetaRest610_chunk0 alpha epsilon eta theta A B C D E).natDegree < 3 * A.natDegree := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hCne, hDne, hEne, heq1, heq2, heq3⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsAB : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAB
  have hsAC : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hAC
  have hsAD : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hAD
  have hsAE : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAE
  have eqC : 2 * C.natDegree = A.natDegree + 2 * B.natDegree := by omega
  have eqD : 4 * D.natDegree = A.natDegree + 6 * B.natDegree := by omega
  have eqE : 4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree := by omega
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hwall' : 14 * B.natDegree = 3 * A.natDegree := by omega
  have hface : A.natDegree + 2 * B.natDegree + D.natDegree = 2 * A.natDegree := by omega
  have hBpos : 0 + 1 ≤ B.natDegree := by omega
  have hCpos : 0 + 1 ≤ C.natDegree := by omega
  have hDpos : 0 + 1 ≤ D.natDegree := by omega
  have hEpos : 0 + 1 ≤ E.natDegree := by omega
  simp only [degreeZeroN2CubicBCDEWallThetaRest610_chunk0, hpow2, hpow3, hpow4, hpow5,
    zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add,
    zero_pow, Nat.succ_ne_zero, sub_zero, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem degreeZeroN2CubicBCDEWallThetaRest610_chunk1_natDegree_lt
    (alpha epsilon eta theta : k) (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeBCDE610 A B C D E)
    (hwall : 7 * (9 * A.natDegree) = 54 * A.natDegree + 42 * B.natDegree) :
    (degreeZeroN2CubicBCDEWallThetaRest610_chunk1 alpha epsilon eta theta A B C D E).natDegree < 3 * A.natDegree := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hCne, hDne, hEne, heq1, heq2, heq3⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsAB : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAB
  have hsAC : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hAC
  have hsAD : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hAD
  have hsAE : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAE
  have eqC : 2 * C.natDegree = A.natDegree + 2 * B.natDegree := by omega
  have eqD : 4 * D.natDegree = A.natDegree + 6 * B.natDegree := by omega
  have eqE : 4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree := by omega
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hwall' : 14 * B.natDegree = 3 * A.natDegree := by omega
  have hface : A.natDegree + 2 * B.natDegree + D.natDegree = 2 * A.natDegree := by omega
  have hBpos : 0 + 1 ≤ B.natDegree := by omega
  have hCpos : 0 + 1 ≤ C.natDegree := by omega
  have hDpos : 0 + 1 ≤ D.natDegree := by omega
  have hEpos : 0 + 1 ≤ E.natDegree := by omega
  simp only [degreeZeroN2CubicBCDEWallThetaRest610_chunk1, hpow2, hpow3, hpow4, hpow5,
    zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add,
    zero_pow, Nat.succ_ne_zero, sub_zero, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem degreeZeroN2CubicBCDEWallThetaRest610_natDegree_lt
    (alpha epsilon eta theta : k) (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeBCDE610 A B C D E)
    (hwall : 7 * (9 * A.natDegree) = 54 * A.natDegree + 42 * B.natDegree) :
    (degreeZeroN2CubicBCDEWallThetaRest610 alpha epsilon eta theta A B C D E).natDegree < 3 * A.natDegree := by
  simp only [degreeZeroN2CubicBCDEWallThetaRest610]
  have h0 := degreeZeroN2CubicBCDEWallThetaRest610_chunk0_natDegree_lt alpha epsilon eta theta A B C D E hcone hwall
  have h1 := degreeZeroN2CubicBCDEWallThetaRest610_chunk1_natDegree_lt alpha epsilon eta theta A B C D E hcone hwall
  have hadd := natDegree_add_le (degreeZeroN2CubicBCDEWallThetaRest610_chunk0 alpha epsilon eta theta A B C D E) (degreeZeroN2CubicBCDEWallThetaRest610_chunk1 alpha epsilon eta theta A B C D E)
  exact lt_of_le_of_lt hadd (max_lt h0 h1)


end CubicLoadWallRests610

/-! ## Split identities: integral = face + tying column + wall rest -/

section CubicLoadWallSplits610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
theorem degreeZeroN1Cubic610_eq_CD_betaWall
    (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroN1Cubic610 0 alpha beta delta epsilon zeta eta theta A B C D E =
      n1CubicSigmaFaceCD610 A B C D E +
        n1CubicBetaFace610 beta A +
          degreeZeroN1CubicCDWallBetaRest610 alpha beta delta epsilon zeta
            eta theta A B C D E := by
  simp only [degreeZeroN1Cubic610, n1CubicSigmaFaceCD610, n1CubicBetaFace610,
    degreeZeroN1CubicCDWallBetaRest610,
    degreeZeroN1CubicCDWallBetaRest610_chunk0,
    degreeZeroN1CubicCDWallBetaRest610_chunk1, zero_mul, mul_zero, zero_smul]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem degreeZeroN2Cubic610_eq_CD_betaWall
    (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroN2Cubic610 0 alpha beta delta epsilon zeta eta theta A B C D E =
      n2CubicSigmaFaceCD610 A B C D E +
        n2CubicBetaFace610 beta A +
          degreeZeroN2CubicCDWallBetaRest610 alpha beta delta epsilon zeta
            eta theta A B C D E := by
  simp only [degreeZeroN2Cubic610, n2CubicSigmaFaceCD610, n2CubicBetaFace610,
    degreeZeroN2CubicCDWallBetaRest610,
    degreeZeroN2CubicCDWallBetaRest610_chunk0,
    degreeZeroN2CubicCDWallBetaRest610_chunk1,
    degreeZeroN2CubicCDWallBetaRest610_chunk2,
    degreeZeroN2CubicCDWallBetaRest610_chunk3, zero_mul, mul_zero, zero_smul]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem degreeZeroN1Cubic610_eq_CD_deltaWall
    (alpha delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroN1Cubic610 0 alpha 0 delta epsilon zeta eta theta A B C D E =
      n1CubicSigmaFaceCD610 A B C D E +
        n1CubicDeltaFace610 delta A +
          degreeZeroN1CubicCDWallDeltaRest610 alpha delta epsilon zeta eta
            theta A B C D E := by
  simp only [degreeZeroN1Cubic610, n1CubicSigmaFaceCD610, n1CubicDeltaFace610,
    degreeZeroN1CubicCDWallDeltaRest610,
    degreeZeroN1CubicCDWallDeltaRest610_chunk0,
    degreeZeroN1CubicCDWallDeltaRest610_chunk1, zero_mul, mul_zero, zero_smul]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem degreeZeroN2Cubic610_eq_CD_deltaWall
    (alpha delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroN2Cubic610 0 alpha 0 delta epsilon zeta eta theta A B C D E =
      n2CubicSigmaFaceCD610 A B C D E +
        n2CubicDeltaFace610 delta A +
          degreeZeroN2CubicCDWallDeltaRest610 alpha delta epsilon zeta eta
            theta A B C D E := by
  simp only [degreeZeroN2Cubic610, n2CubicSigmaFaceCD610, n2CubicDeltaFace610,
    degreeZeroN2CubicCDWallDeltaRest610,
    degreeZeroN2CubicCDWallDeltaRest610_chunk0,
    degreeZeroN2CubicCDWallDeltaRest610_chunk1,
    degreeZeroN2CubicCDWallDeltaRest610_chunk2, zero_mul, mul_zero, zero_smul]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem degreeZeroN1Cubic610_eq_CD_zetaWall
    (alpha epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroN1Cubic610 0 alpha 0 0 epsilon zeta eta theta A B C D E =
      n1CubicSigmaFaceCD610 A B C D E +
        n1CubicZetaFace610 zeta A +
          degreeZeroN1CubicCDWallZetaRest610 alpha epsilon zeta eta theta
            A B C D E := by
  simp only [degreeZeroN1Cubic610, n1CubicSigmaFaceCD610, n1CubicZetaFace610,
    degreeZeroN1CubicCDWallZetaRest610, zero_mul, mul_zero, zero_smul]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem degreeZeroN2Cubic610_eq_CD_zetaWall
    (alpha epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroN2Cubic610 0 alpha 0 0 epsilon zeta eta theta A B C D E =
      n2CubicSigmaFaceCD610 A B C D E +
        n2CubicZetaFace610 zeta A +
          degreeZeroN2CubicCDWallZetaRest610 alpha epsilon zeta eta theta
            A B C D E := by
  simp only [degreeZeroN2Cubic610, n2CubicSigmaFaceCD610, n2CubicZetaFace610,
    degreeZeroN2CubicCDWallZetaRest610,
    degreeZeroN2CubicCDWallZetaRest610_chunk0,
    degreeZeroN2CubicCDWallZetaRest610_chunk1, zero_mul, mul_zero, zero_smul]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem degreeZeroN1Cubic610_eq_CD_thetaWall
    (alpha epsilon eta theta : k) (A B C D E : k[X]) :
    degreeZeroN1Cubic610 0 alpha 0 0 epsilon 0 eta theta A B C D E =
      n1CubicSigmaFaceCD610 A B C D E +
        n1CubicThetaFace610 theta A +
          degreeZeroN1CubicCDWallThetaRest610 alpha epsilon eta theta
            A B C D E := by
  simp only [degreeZeroN1Cubic610, n1CubicSigmaFaceCD610, n1CubicThetaFace610,
    degreeZeroN1CubicCDWallThetaRest610, zero_mul, mul_zero, zero_smul]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem degreeZeroN2Cubic610_eq_CD_thetaWall
    (alpha epsilon eta theta : k) (A B C D E : k[X]) :
    degreeZeroN2Cubic610 0 alpha 0 0 epsilon 0 eta theta A B C D E =
      n2CubicSigmaFaceCD610 A B C D E +
        n2CubicThetaFace610 theta A +
          degreeZeroN2CubicCDWallThetaRest610 alpha epsilon eta theta
            A B C D E := by
  simp only [degreeZeroN2Cubic610, n2CubicSigmaFaceCD610, n2CubicThetaFace610,
    degreeZeroN2CubicCDWallThetaRest610,
    degreeZeroN2CubicCDWallThetaRest610_chunk0,
    degreeZeroN2CubicCDWallThetaRest610_chunk1, zero_mul, mul_zero, zero_smul]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem degreeZeroN1Cubic610_eq_BCDE_betaWall
    (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroN1Cubic610 0 alpha beta delta epsilon zeta eta theta A B C D E =
      n1CubicSigmaFaceBCDE610 A B C D E +
        n1CubicBetaFace610 beta A +
          degreeZeroN1CubicBCDEWallBetaRest610 alpha beta delta epsilon zeta
            eta theta A B C D E := by
  simp only [degreeZeroN1Cubic610, n1CubicSigmaFaceBCDE610, n1CubicBetaFace610,
    degreeZeroN1CubicBCDEWallBetaRest610,
    degreeZeroN1CubicBCDEWallBetaRest610_chunk0,
    degreeZeroN1CubicBCDEWallBetaRest610_chunk1, zero_mul, mul_zero, zero_smul]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem degreeZeroN2Cubic610_eq_BCDE_betaWall
    (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroN2Cubic610 0 alpha beta delta epsilon zeta eta theta A B C D E =
      n2CubicSigmaFaceBCDE610 A B C D E +
        n2CubicBetaFace610 beta A +
          degreeZeroN2CubicBCDEWallBetaRest610 alpha beta delta epsilon zeta
            eta theta A B C D E := by
  simp only [degreeZeroN2Cubic610, n2CubicSigmaFaceBCDE610, n2CubicBetaFace610,
    degreeZeroN2CubicBCDEWallBetaRest610,
    degreeZeroN2CubicBCDEWallBetaRest610_chunk0,
    degreeZeroN2CubicBCDEWallBetaRest610_chunk1,
    degreeZeroN2CubicBCDEWallBetaRest610_chunk2,
    degreeZeroN2CubicBCDEWallBetaRest610_chunk3, zero_mul, mul_zero, zero_smul]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem degreeZeroN1Cubic610_eq_BCDE_deltaWall
    (alpha delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroN1Cubic610 0 alpha 0 delta epsilon zeta eta theta A B C D E =
      n1CubicSigmaFaceBCDE610 A B C D E +
        n1CubicDeltaFace610 delta A +
          degreeZeroN1CubicBCDEWallDeltaRest610 alpha delta epsilon zeta eta
            theta A B C D E := by
  simp only [degreeZeroN1Cubic610, n1CubicSigmaFaceBCDE610, n1CubicDeltaFace610,
    degreeZeroN1CubicBCDEWallDeltaRest610,
    degreeZeroN1CubicBCDEWallDeltaRest610_chunk0,
    degreeZeroN1CubicBCDEWallDeltaRest610_chunk1, zero_mul, mul_zero, zero_smul]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem degreeZeroN2Cubic610_eq_BCDE_deltaWall
    (alpha delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroN2Cubic610 0 alpha 0 delta epsilon zeta eta theta A B C D E =
      n2CubicSigmaFaceBCDE610 A B C D E +
        n2CubicDeltaFace610 delta A +
          degreeZeroN2CubicBCDEWallDeltaRest610 alpha delta epsilon zeta eta
            theta A B C D E := by
  simp only [degreeZeroN2Cubic610, n2CubicSigmaFaceBCDE610, n2CubicDeltaFace610,
    degreeZeroN2CubicBCDEWallDeltaRest610,
    degreeZeroN2CubicBCDEWallDeltaRest610_chunk0,
    degreeZeroN2CubicBCDEWallDeltaRest610_chunk1,
    degreeZeroN2CubicBCDEWallDeltaRest610_chunk2, zero_mul, mul_zero, zero_smul]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem degreeZeroN1Cubic610_eq_BCDE_zetaWall
    (alpha epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroN1Cubic610 0 alpha 0 0 epsilon zeta eta theta A B C D E =
      n1CubicSigmaFaceBCDE610 A B C D E +
        n1CubicZetaFace610 zeta A +
          degreeZeroN1CubicBCDEWallZetaRest610 alpha epsilon zeta eta theta
            A B C D E := by
  simp only [degreeZeroN1Cubic610, n1CubicSigmaFaceBCDE610, n1CubicZetaFace610,
    degreeZeroN1CubicBCDEWallZetaRest610, zero_mul, mul_zero, zero_smul]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem degreeZeroN2Cubic610_eq_BCDE_zetaWall
    (alpha epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroN2Cubic610 0 alpha 0 0 epsilon zeta eta theta A B C D E =
      n2CubicSigmaFaceBCDE610 A B C D E +
        n2CubicZetaFace610 zeta A +
          degreeZeroN2CubicBCDEWallZetaRest610 alpha epsilon zeta eta theta
            A B C D E := by
  simp only [degreeZeroN2Cubic610, n2CubicSigmaFaceBCDE610, n2CubicZetaFace610,
    degreeZeroN2CubicBCDEWallZetaRest610,
    degreeZeroN2CubicBCDEWallZetaRest610_chunk0,
    degreeZeroN2CubicBCDEWallZetaRest610_chunk1, zero_mul, mul_zero, zero_smul]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem degreeZeroN1Cubic610_eq_BCDE_thetaWall
    (alpha epsilon eta theta : k) (A B C D E : k[X]) :
    degreeZeroN1Cubic610 0 alpha 0 0 epsilon 0 eta theta A B C D E =
      n1CubicSigmaFaceBCDE610 A B C D E +
        n1CubicThetaFace610 theta A +
          degreeZeroN1CubicBCDEWallThetaRest610 alpha epsilon eta theta
            A B C D E := by
  simp only [degreeZeroN1Cubic610, n1CubicSigmaFaceBCDE610, n1CubicThetaFace610,
    degreeZeroN1CubicBCDEWallThetaRest610, zero_mul, mul_zero, zero_smul]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem degreeZeroN2Cubic610_eq_BCDE_thetaWall
    (alpha epsilon eta theta : k) (A B C D E : k[X]) :
    degreeZeroN2Cubic610 0 alpha 0 0 epsilon 0 eta theta A B C D E =
      n2CubicSigmaFaceBCDE610 A B C D E +
        n2CubicThetaFace610 theta A +
          degreeZeroN2CubicBCDEWallThetaRest610 alpha epsilon eta theta
            A B C D E := by
  simp only [degreeZeroN2Cubic610, n2CubicSigmaFaceBCDE610, n2CubicThetaFace610,
    degreeZeroN2CubicBCDEWallThetaRest610,
    degreeZeroN2CubicBCDEWallThetaRest610_chunk0,
    degreeZeroN2CubicBCDEWallThetaRest610_chunk1, zero_mul, mul_zero, zero_smul]
  all_goals module

theorem n2CubicSigmaFaceBCDE610_coeff_top_of_loadCone
    {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeBCDE610 A B C D E)
    (hAne : A ≠ 0) (hBne : B ≠ 0) (hCne : C ≠ 0) (hDne : D ≠ 0)
    (hEne : E ≠ 0) :
    (n2CubicSigmaFaceBCDE610 A B C D E).coeff
        (2 * A.natDegree + 2 * B.natDegree + D.natDegree) =
      (-(5 / 81 : k)) *
        n1CubicSigmaInnerBCDE610 A.leadingCoeff B.leadingCoeff
          C.leadingCoeff D.leadingCoeff E.leadingCoeff *
        A.leadingCoeff := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    _, _, _, _, heq1, heq2, heq3⟩
  simp only [n2CubicSigmaFaceBCDE610, n1CubicSigmaInnerBCDE610, coeff_add,
    coeff_sub, coeff_smul, smul_eq_mul]
  have hA2B2 : A ^ 2 * B ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hAne) (pow_ne_zero 2 hBne)
  have hdeg_A2B2D : ((A ^ 2 * B ^ 2 * D)).natDegree =
      2 * A.natDegree + 2 * B.natDegree + D.natDegree := by
    rw [natDegree_mul hA2B2 hDne,
      natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 2 hBne),
      natDegree_pow, natDegree_pow]
  have hcf_A2B2D : ((A ^ 2 * B ^ 2 * D)).coeff
        (2 * A.natDegree + 2 * B.natDegree + D.natDegree) =
      A.leadingCoeff ^ 2 * B.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_A2B2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul,
      leadingCoeff_pow, leadingCoeff_pow]
  have hABC : A * B * C ≠ 0 :=
    mul_ne_zero (mul_ne_zero hAne hBne) hCne
  have hdeg_ABCE : ((A * B * C * E)).natDegree =
      2 * A.natDegree + 2 * B.natDegree + D.natDegree := by
    rw [natDegree_mul hABC hEne,
      natDegree_mul (mul_ne_zero hAne hBne) hCne, natDegree_mul hAne hBne]
    omega
  have hcf_ABCE : ((A * B * C * E)).coeff
        (2 * A.natDegree + 2 * B.natDegree + D.natDegree) =
      A.leadingCoeff * B.leadingCoeff * C.leadingCoeff *
        E.leadingCoeff := by
    rw [← hdeg_ABCE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul,
      leadingCoeff_mul]
  have hAC2 : A * C ^ 2 ≠ 0 := mul_ne_zero hAne (pow_ne_zero 2 hCne)
  have hdeg_AC2D : ((A * C ^ 2 * D)).natDegree =
      2 * A.natDegree + 2 * B.natDegree + D.natDegree := by
    rw [natDegree_mul hAC2 hDne, natDegree_mul hAne (pow_ne_zero 2 hCne),
      natDegree_pow]
    omega
  have hcf_AC2D : ((A * C ^ 2 * D)).coeff
        (2 * A.natDegree + 2 * B.natDegree + D.natDegree) =
      A.leadingCoeff * C.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_AC2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul,
      leadingCoeff_pow]
  rw [hcf_A2B2D, hcf_ABCE, hcf_AC2D]
  ring

end CubicLoadWallSplits610

/-! ## N₁ tops on non-tying walls -/

section CubicLoadWallN1Tops610

variable {k : Type*} [Field k] [CharZero k]

theorem cubicLoadSigmaConeCD610_n1BetaTop_of_deltaWall
    {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hwall : 7 * (12 * A.natDegree) = 30 * A.natDegree + 42 * C.natDegree) :
    cubicN1BetaTop610 A B C D E := by
  rcases hcone with ⟨hload, hCne, hDne, heq, hBcmp, hEcmp⟩
  rcases hload with ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩
  have hCD : A.natDegree + 2 * D.natDegree = 3 * C.natDegree := by omega
  have h7c : 7 * C.natDegree = 9 * A.natDegree := by omega
  refine ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, ?_, ?_, ?_, ?_⟩
  · rcases hBcmp with hB0 | hBlt
    · have hBdeg : B.natDegree = 0 := by simp [hB0]
      rw [hBdeg]; omega
    · have : A.natDegree + 2 * B.natDegree + 1 ≤ 2 * C.natDegree :=
        Nat.succ_le_of_lt hBlt
      omega
  · omega
  · omega
  · rcases hEcmp with hE0 | hElt
    · have hEdeg : E.natDegree = 0 := by simp [hE0]
      rw [hEdeg]; omega
    · omega

theorem cubicLoadSigmaConeCD610_n1BetaTop_of_zetaWall
    {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hwall : 12 * A.natDegree = 6 * A.natDegree + 6 * C.natDegree) :
    cubicN1BetaTop610 A B C D E := by
  rcases hcone with ⟨hload, hCne, hDne, heq, hBcmp, hEcmp⟩
  rcases hload with ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩
  have hCD : A.natDegree + 2 * D.natDegree = 3 * C.natDegree := by omega
  refine ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, ?_, ?_, ?_, ?_⟩
  · rcases hBcmp with hB0 | hBlt
    · have hBdeg : B.natDegree = 0 := by simp [hB0]
      rw [hBdeg]; omega
    · have : A.natDegree + 2 * B.natDegree + 1 ≤ 2 * C.natDegree :=
        Nat.succ_le_of_lt hBlt
      omega
  · omega
  · omega
  · rcases hEcmp with hE0 | hElt
    · have hEdeg : E.natDegree = 0 := by simp [hE0]
      rw [hEdeg]; omega
    · omega

theorem cubicLoadSigmaConeCD610_n1DeltaTop_of_zetaWall
    {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hwall : 12 * A.natDegree = 6 * A.natDegree + 6 * C.natDegree) :
    cubicN1DeltaTop610 A B C D E := by
  rcases hcone with ⟨hload, hCne, hDne, heq, hBcmp, hEcmp⟩
  rcases hload with ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩
  have hCD : A.natDegree + 2 * D.natDegree = 3 * C.natDegree := by omega
  refine ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, ?_, ?_, ?_, ?_⟩
  · rcases hBcmp with hB0 | hBlt
    · have hBdeg : B.natDegree = 0 := by simp [hB0]
      rw [hBdeg]; omega
    · have : A.natDegree + 2 * B.natDegree + 1 ≤ 2 * C.natDegree :=
        Nat.succ_le_of_lt hBlt
      omega
  · omega
  · omega
  · rcases hEcmp with hE0 | hElt
    · have hEdeg : E.natDegree = 0 := by simp [hE0]
      rw [hEdeg]; omega
    · omega

theorem cubicLoadSigmaConeCD610_n1BetaTop_of_thetaWall
    {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hwall : 7 * (12 * A.natDegree) = 54 * A.natDegree + 42 * C.natDegree) :
    cubicN1BetaTop610 A B C D E := by
  rcases hcone with ⟨hload, hCne, hDne, heq, hBcmp, hEcmp⟩
  rcases hload with ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩
  have hCD : A.natDegree + 2 * D.natDegree = 3 * C.natDegree := by omega
  refine ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, ?_, ?_, ?_, ?_⟩
  · rcases hBcmp with hB0 | hBlt
    · have hBdeg : B.natDegree = 0 := by simp [hB0]
      rw [hBdeg]; omega
    · have : A.natDegree + 2 * B.natDegree + 1 ≤ 2 * C.natDegree :=
        Nat.succ_le_of_lt hBlt
      omega
  · omega
  · omega
  · rcases hEcmp with hE0 | hElt
    · have hEdeg : E.natDegree = 0 := by simp [hE0]
      rw [hEdeg]; omega
    · omega

theorem cubicLoadSigmaConeCD610_n1DeltaTop_of_thetaWall
    {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hwall : 7 * (12 * A.natDegree) = 54 * A.natDegree + 42 * C.natDegree) :
    cubicN1DeltaTop610 A B C D E := by
  rcases hcone with ⟨hload, hCne, hDne, heq, hBcmp, hEcmp⟩
  rcases hload with ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩
  have hCD : A.natDegree + 2 * D.natDegree = 3 * C.natDegree := by omega
  refine ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, ?_, ?_, ?_, ?_⟩
  · rcases hBcmp with hB0 | hBlt
    · have hBdeg : B.natDegree = 0 := by simp [hB0]
      rw [hBdeg]; omega
    · have : A.natDegree + 2 * B.natDegree + 1 ≤ 2 * C.natDegree :=
        Nat.succ_le_of_lt hBlt
      omega
  · omega
  · omega
  · rcases hEcmp with hE0 | hElt
    · have hEdeg : E.natDegree = 0 := by simp [hE0]
      rw [hEdeg]; omega
    · omega

theorem cubicLoadSigmaConeCD610_n1ZetaTop_of_thetaWall
    {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hwall : 7 * (12 * A.natDegree) = 54 * A.natDegree + 42 * C.natDegree) :
    cubicN1ZetaTop610 A B C D E := by
  rcases hcone with ⟨hload, hCne, hDne, heq, hBcmp, hEcmp⟩
  rcases hload with ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩
  have hCD : A.natDegree + 2 * D.natDegree = 3 * C.natDegree := by omega
  refine ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, ?_, ?_, ?_, ?_⟩
  · rcases hBcmp with hB0 | hBlt
    · have hBdeg : B.natDegree = 0 := by simp [hB0]
      rw [hBdeg]; omega
    · have : A.natDegree + 2 * B.natDegree + 1 ≤ 2 * C.natDegree :=
        Nat.succ_le_of_lt hBlt
      omega
  · omega
  · omega
  · rcases hEcmp with hE0 | hElt
    · have hEdeg : E.natDegree = 0 := by simp [hE0]
      rw [hEdeg]; omega
    · omega

theorem cubicLoadSigmaConeBCDE610_n1BetaTop_of_deltaWall
    {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeBCDE610 A B C D E)
    (hwall : 7 * (9 * A.natDegree) = 30 * A.natDegree + 42 * B.natDegree) :
    cubicN1BetaTop610 A B C D E := by
  rcases hcone with ⟨hload, hBne, hCne, hDne, hEne, heq1, heq2, heq3⟩
  rcases hload with ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩
  refine ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, ?_, ?_, ?_, ?_⟩
  all_goals omega

theorem cubicLoadSigmaConeBCDE610_n1BetaTop_of_zetaWall
    {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeBCDE610 A B C D E)
    (hwall : 9 * A.natDegree = 6 * A.natDegree + 6 * B.natDegree) :
    cubicN1BetaTop610 A B C D E := by
  rcases hcone with ⟨hload, hBne, hCne, hDne, hEne, heq1, heq2, heq3⟩
  rcases hload with ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩
  refine ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, ?_, ?_, ?_, ?_⟩
  all_goals omega

theorem cubicLoadSigmaConeBCDE610_n1DeltaTop_of_zetaWall
    {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeBCDE610 A B C D E)
    (hwall : 9 * A.natDegree = 6 * A.natDegree + 6 * B.natDegree) :
    cubicN1DeltaTop610 A B C D E := by
  rcases hcone with ⟨hload, hBne, hCne, hDne, hEne, heq1, heq2, heq3⟩
  rcases hload with ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩
  refine ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, ?_, ?_, ?_, ?_⟩
  all_goals omega

theorem cubicLoadSigmaConeBCDE610_n1BetaTop_of_thetaWall
    {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeBCDE610 A B C D E)
    (hwall : 7 * (9 * A.natDegree) = 54 * A.natDegree + 42 * B.natDegree) :
    cubicN1BetaTop610 A B C D E := by
  rcases hcone with ⟨hload, hBne, hCne, hDne, hEne, heq1, heq2, heq3⟩
  rcases hload with ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩
  refine ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, ?_, ?_, ?_, ?_⟩
  all_goals omega

theorem cubicLoadSigmaConeBCDE610_n1DeltaTop_of_thetaWall
    {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeBCDE610 A B C D E)
    (hwall : 7 * (9 * A.natDegree) = 54 * A.natDegree + 42 * B.natDegree) :
    cubicN1DeltaTop610 A B C D E := by
  rcases hcone with ⟨hload, hBne, hCne, hDne, hEne, heq1, heq2, heq3⟩
  rcases hload with ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩
  refine ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, ?_, ?_, ?_, ?_⟩
  all_goals omega

theorem cubicLoadSigmaConeBCDE610_n1ZetaTop_of_thetaWall
    {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeBCDE610 A B C D E)
    (hwall : 7 * (9 * A.natDegree) = 54 * A.natDegree + 42 * B.natDegree) :
    cubicN1ZetaTop610 A B C D E := by
  rcases hcone with ⟨hload, hBne, hCne, hDne, hEne, heq1, heq2, heq3⟩
  rcases hload with ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩
  refine ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, ?_, ?_, ?_, ?_⟩
  all_goals omega

end CubicLoadWallN1Tops610


/-! ## N₁/N₂ 2×2 determinants on odd-column walls -/

section CubicLoadWallDets610

variable {k : Type*} [Field k] [CharZero k]

theorem n1n2_beta_column_det610 (a x beta : k) (ha : a ≠ 0)
    (hz1 : x + (7 / 6912 * beta : k) * a ^ 5 = 0)
    (hz2 : -a * x + (35 / 41472 * beta : k) * a ^ 6 = 0) :
    beta = 0 := by
  have hcomb :
      a * (x + (7 / 6912 * beta : k) * a ^ 5) +
        (-a * x + (35 / 41472 * beta : k) * a ^ 6) = 0 := by
    rw [hz1, hz2, mul_zero, add_zero]
  have hlin : (77 / 41472 * beta : k) * a ^ 6 = 0 := by
    convert hcomb using 1
    ring
  have hden : (77 / 41472 : k) ≠ 0 :=
    div_ne_zero (by norm_num) (by norm_num)
  have ha6 : a ^ 6 ≠ 0 := pow_ne_zero _ ha
  rcases mul_eq_zero.mp hlin with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact (hden h).elim
    · exact h
  · exact (ha6 h).elim

theorem n1n2_delta_column_det610 (a x delta : k) (ha : a ≠ 0)
    (hz1 : x + (35 / 10368 * delta : k) * a ^ 4 = 0)
    (hz2 : -a * x + (7 / 2592 * delta : k) * a ^ 5 = 0) :
    delta = 0 := by
  have hcomb :
      a * (x + (35 / 10368 * delta : k) * a ^ 4) +
        (-a * x + (7 / 2592 * delta : k) * a ^ 5) = 0 := by
    rw [hz1, hz2, mul_zero, add_zero]
  have hlin : (7 / 1152 * delta : k) * a ^ 5 = 0 := by
    convert hcomb using 1
    ring
  have hden : (7 / 1152 : k) ≠ 0 :=
    div_ne_zero (by norm_num) (by norm_num)
  have ha5 : a ^ 5 ≠ 0 := pow_ne_zero _ ha
  rcases mul_eq_zero.mp hlin with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact (hden h).elim
    · exact h
  · exact (ha5 h).elim

theorem n1n2_zeta_column_det610 (a x zeta : k) (ha : a ≠ 0)
    (hz1 : x + (5 / 432 * zeta : k) * a ^ 3 = 0)
    (hz2 : -a * x + (5 / 576 * zeta : k) * a ^ 4 = 0) :
    zeta = 0 := by
  have hcomb :
      a * (x + (5 / 432 * zeta : k) * a ^ 3) +
        (-a * x + (5 / 576 * zeta : k) * a ^ 4) = 0 := by
    rw [hz1, hz2, mul_zero, add_zero]
  have hlin : (35 / 1728 * zeta : k) * a ^ 4 = 0 := by
    convert hcomb using 1
    ring
  have hden : (35 / 1728 : k) ≠ 0 :=
    div_ne_zero (by norm_num) (by norm_num)
  have ha4 : a ^ 4 ≠ 0 := pow_ne_zero _ ha
  rcases mul_eq_zero.mp hlin with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact (hden h).elim
    · exact h
  · exact (ha4 h).elim

theorem n1n2_theta_column_det610 (a x theta : k) (ha : a ≠ 0)
    (hz1 : x + (1 / 24 * theta : k) * a ^ 2 = 0)
    (hz2 : -a * x + (1 / 36 * theta : k) * a ^ 3 = 0) :
    theta = 0 := by
  have hcomb :
      a * (x + (1 / 24 * theta : k) * a ^ 2) +
        (-a * x + (1 / 36 * theta : k) * a ^ 3) = 0 := by
    rw [hz1, hz2, mul_zero, add_zero]
  have hlin : (5 / 72 * theta : k) * a ^ 3 = 0 := by
    convert hcomb using 1
    ring
  have hden : (5 / 72 : k) ≠ 0 :=
    div_ne_zero (by norm_num) (by norm_num)
  have ha3 : a ^ 3 ≠ 0 := pow_ne_zero _ ha
  rcases mul_eq_zero.mp hlin with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact (hden h).elim
    · exact h
  · exact (ha3 h).elim

end CubicLoadWallDets610


/-! ## `{C,D}` wall kills -/

section CubicLoadCDWallKills610

variable {k : Type*} [Field k] [CharZero k]

theorem CubicLoadSigmaConeCD610_A_ne
    {A B C D E : k[X]} (hcone : CubicLoadSigmaConeCD610 A B C D E) :
    A ≠ 0 := by
  intro h0
  have : A.natDegree = 0 := by simp [h0]
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, _⟩
  omega

set_option maxHeartbeats 64000000 in
theorem cubicLoadSigmaCone_CD_betaWall_impossible {j t : k}
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hl : l = 0)
    (hwall : 7 * (12 * A.natDegree) = 18 * A.natDegree + 42 * C.natDegree)
    (hmu : (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta
          theta A B C D E).natDegree = 0)
    (hkap : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree = 0)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E) =
        Polynomial.C (j / t)) :
    False := by
  subst hl
  have hAne := CubicLoadSigmaConeCD610_A_ne hcone
  have hCne : C ≠ 0 := hcone.2.1
  have hDne : D ≠ 0 := hcone.2.2.1
  have hApos : 0 < A.natDegree := hcone.1.1.1
  have hN1le := degreeZeroN1Cubic610_natDegree_le 0 alpha beta delta epsilon
      zeta eta theta A B C D E hmu hkap
  have hN2le := degreeZeroN2Cubic610_natDegree_le (j := j) (t := t) 0
      alpha beta delta epsilon zeta eta theta A B C D E hApos hkap hjdiv hder
  have hT1 : A.natDegree < 5 * A.natDegree := by
    rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, _⟩
    omega
  have hT2 : 2 * A.natDegree < 6 * A.natDegree := by
    rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, _⟩
    omega
  have hdeg1 : 5 * A.natDegree = 2 * C.natDegree + D.natDegree := by
    rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
      hCne', hDne', heq, hBcmp, hEcmp⟩
    omega
  have hdeg2 : 6 * A.natDegree =
      A.natDegree + 2 * C.natDegree + D.natDegree := by omega
  have hz1 : (degreeZeroN1Cubic610 0 alpha beta delta epsilon zeta eta
        theta A B C D E).coeff (5 * A.natDegree) = 0 :=
    coeff_eq_zero_of_natDegree_lt (hN1le.trans_lt hT1)
  have hz2 : (degreeZeroN2Cubic610 0 alpha beta delta epsilon zeta eta
        theta A B C D E).coeff (6 * A.natDegree) = 0 :=
    coeff_eq_zero_of_natDegree_lt (hN2le.trans_lt hT2)
  have hN1rest :=
    degreeZeroN1CubicCDWallBetaRest610_natDegree_lt alpha beta delta epsilon
      zeta eta theta A B C D E hcone hwall
  have hN2rest :=
    degreeZeroN2CubicCDWallBetaRest610_natDegree_lt alpha beta delta epsilon
      zeta eta theta A B C D E hcone hwall
  rw [degreeZeroN1Cubic610_eq_CD_betaWall, coeff_add, coeff_add] at hz1
  have hN1small :
      (degreeZeroN1CubicCDWallBetaRest610 alpha beta delta epsilon zeta eta
          theta A B C D E).coeff (5 * A.natDegree) = 0 :=
    coeff_eq_zero_of_natDegree_lt (hdeg1 ▸ hN1rest)
  rw [hN1small, add_zero] at hz1
  rw [degreeZeroN2Cubic610_eq_CD_betaWall, coeff_add, coeff_add] at hz2
  have hN2small :
      (degreeZeroN2CubicCDWallBetaRest610 alpha beta delta epsilon zeta eta
          theta A B C D E).coeff (6 * A.natDegree) = 0 :=
    coeff_eq_zero_of_natDegree_lt (hdeg2 ▸ hN2rest)
  rw [hN2small, add_zero] at hz2
  have hN1face := n1CubicSigmaFaceCD610_coeff_top A B C D E hCne hDne
  have hN2face := n2CubicSigmaFaceCD610_coeff_top A B C D E hAne hCne hDne
  have hN1L := n1CubicBetaFace610_coeff_top beta A
  have hN2L := n2CubicBetaFace610_coeff_top beta A
  rw [← hdeg1] at hN1face
  rw [hN1face, hN1L] at hz1
  rw [← hdeg2] at hN2face
  rw [hN2face, hN2L] at hz2
  have hx :
      beta = 0 :=
    n1n2_beta_column_det610 A.leadingCoeff
      ((-(5 / 27 : k)) * C.leadingCoeff ^ 2 * D.leadingCoeff) beta
      (leadingCoeff_ne_zero.mpr hAne)
      (by simpa [add_comm] using hz1)
      (by
        have : (5 / 27 : k) * A.leadingCoeff * C.leadingCoeff ^ 2 *
              D.leadingCoeff =
            -A.leadingCoeff *
              ((-(5 / 27 : k)) * C.leadingCoeff ^ 2 * D.leadingCoeff) := by
          ring
        rw [this] at hz2
        simpa [add_comm, sub_eq_add_neg] using hz2)
  have hTpos : A.natDegree < 2 * C.natDegree + D.natDegree := by
    rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
      hCne', hDne', heq, hBcmp, hEcmp⟩
    omega
  exact cubicLoadSigmaCone_CD_offWall_impossible 0 alpha beta delta epsilon
    zeta eta theta A B C D E hcone rfl (Or.inl hx) (Or.inr (by omega))
    (Or.inr (by omega)) (Or.inr (by omega)) hTpos hmu hkap

set_option maxHeartbeats 64000000 in
theorem cubicLoadSigmaCone_CD_deltaWall_impossible {j t : k}
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hl : l = 0)
    (hwall : 7 * (12 * A.natDegree) = 30 * A.natDegree + 42 * C.natDegree)
    (hmu : (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta
          theta A B C D E).natDegree = 0)
    (hkap : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree = 0)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E) =
        Polynomial.C (j / t)) :
    False := by
  subst hl
  have hbetaTop := cubicLoadSigmaConeCD610_n1BetaTop_of_deltaWall hcone hwall
  have hbeta0 : beta = 0 :=
    cubicN1_beta_eq_zero 0 alpha beta delta epsilon zeta eta theta
      A B C D E hbetaTop rfl hmu hkap
  subst hbeta0
  have hAne := CubicLoadSigmaConeCD610_A_ne hcone
  have hCne : C ≠ 0 := hcone.2.1
  have hDne : D ≠ 0 := hcone.2.2.1
  have hApos : 0 < A.natDegree := hcone.1.1.1
  have hN1le := degreeZeroN1Cubic610_natDegree_le 0 alpha 0 delta epsilon
      zeta eta theta A B C D E hmu hkap
  have hN2le := degreeZeroN2Cubic610_natDegree_le (j := j) (t := t) 0
      alpha 0 delta epsilon zeta eta theta A B C D E hApos hkap hjdiv hder
  have hT1 : A.natDegree < 4 * A.natDegree := by
    rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, _⟩
    omega
  have hT2 : 2 * A.natDegree < 5 * A.natDegree := by
    rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, _⟩
    omega
  have hdeg1 : 4 * A.natDegree = 2 * C.natDegree + D.natDegree := by
    rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
      hCne', hDne', heq, hBcmp, hEcmp⟩
    omega
  have hdeg2 : 5 * A.natDegree =
      A.natDegree + 2 * C.natDegree + D.natDegree := by omega
  have hz1 : (degreeZeroN1Cubic610 0 alpha 0 delta epsilon zeta eta
        theta A B C D E).coeff (4 * A.natDegree) = 0 :=
    coeff_eq_zero_of_natDegree_lt (hN1le.trans_lt hT1)
  have hz2 : (degreeZeroN2Cubic610 0 alpha 0 delta epsilon zeta eta
        theta A B C D E).coeff (5 * A.natDegree) = 0 :=
    coeff_eq_zero_of_natDegree_lt (hN2le.trans_lt hT2)
  have hN1rest :=
    degreeZeroN1CubicCDWallDeltaRest610_natDegree_lt alpha delta epsilon
      zeta eta theta A B C D E hcone hwall
  have hN2rest :=
    degreeZeroN2CubicCDWallDeltaRest610_natDegree_lt alpha delta epsilon
      zeta eta theta A B C D E hcone hwall
  rw [degreeZeroN1Cubic610_eq_CD_deltaWall, coeff_add, coeff_add] at hz1
  have hN1small :
      (degreeZeroN1CubicCDWallDeltaRest610 alpha delta epsilon zeta eta
          theta A B C D E).coeff (4 * A.natDegree) = 0 :=
    coeff_eq_zero_of_natDegree_lt (hdeg1 ▸ hN1rest)
  rw [hN1small, add_zero] at hz1
  rw [degreeZeroN2Cubic610_eq_CD_deltaWall, coeff_add, coeff_add] at hz2
  have hN2small :
      (degreeZeroN2CubicCDWallDeltaRest610 alpha delta epsilon zeta eta
          theta A B C D E).coeff (5 * A.natDegree) = 0 :=
    coeff_eq_zero_of_natDegree_lt (hdeg2 ▸ hN2rest)
  rw [hN2small, add_zero] at hz2
  have hN1face := n1CubicSigmaFaceCD610_coeff_top A B C D E hCne hDne
  have hN2face := n2CubicSigmaFaceCD610_coeff_top A B C D E hAne hCne hDne
  have hN1L := n1CubicDeltaFace610_coeff_top delta A
  have hN2L := n2CubicDeltaFace610_coeff_top delta A
  rw [← hdeg1] at hN1face
  rw [hN1face, hN1L] at hz1
  rw [← hdeg2] at hN2face
  rw [hN2face, hN2L] at hz2
  have hx : delta = 0 :=
    n1n2_delta_column_det610 A.leadingCoeff
      ((-(5 / 27 : k)) * C.leadingCoeff ^ 2 * D.leadingCoeff) delta
      (leadingCoeff_ne_zero.mpr hAne)
      (by simpa [add_comm] using hz1)
      (by
        have : (5 / 27 : k) * A.leadingCoeff * C.leadingCoeff ^ 2 *
              D.leadingCoeff =
            -A.leadingCoeff *
              ((-(5 / 27 : k)) * C.leadingCoeff ^ 2 * D.leadingCoeff) := by
          ring
        rw [this] at hz2
        simpa [add_comm, sub_eq_add_neg] using hz2)
  have hTpos : A.natDegree < 2 * C.natDegree + D.natDegree := by
    rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
      hCne', hDne', heq, hBcmp, hEcmp⟩
    omega
  exact cubicLoadSigmaCone_CD_offWall_impossible 0 alpha 0 delta epsilon
    zeta eta theta A B C D E hcone rfl (Or.inl rfl) (Or.inl hx)
    (Or.inr (by omega)) (Or.inr (by omega)) hTpos hmu hkap

set_option maxHeartbeats 64000000 in
theorem cubicLoadSigmaCone_CD_zetaWall_impossible {j t : k}
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hl : l = 0)
    (hwall : 12 * A.natDegree = 6 * A.natDegree + 6 * C.natDegree)
    (hmu : (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta
          theta A B C D E).natDegree = 0)
    (hkap : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree = 0)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E) =
        Polynomial.C (j / t)) :
    False := by
  subst hl
  have hbetaTop := cubicLoadSigmaConeCD610_n1BetaTop_of_zetaWall hcone hwall
  have hbeta0 : beta = 0 :=
    cubicN1_beta_eq_zero 0 alpha beta delta epsilon zeta eta theta
      A B C D E hbetaTop rfl hmu hkap
  subst hbeta0
  have hdeltaTop := cubicLoadSigmaConeCD610_n1DeltaTop_of_zetaWall hcone hwall
  have hdelta0 : delta = 0 :=
    cubicN1_delta_eq_zero 0 alpha 0 delta epsilon zeta eta theta
      A B C D E hdeltaTop rfl rfl hmu hkap
  subst hdelta0
  have hAne := CubicLoadSigmaConeCD610_A_ne hcone
  have hCne : C ≠ 0 := hcone.2.1
  have hDne : D ≠ 0 := hcone.2.2.1
  have hApos : 0 < A.natDegree := hcone.1.1.1
  have hN1le := degreeZeroN1Cubic610_natDegree_le 0 alpha 0 0 epsilon
      zeta eta theta A B C D E hmu hkap
  have hN2le := degreeZeroN2Cubic610_natDegree_le (j := j) (t := t) 0
      alpha 0 0 epsilon zeta eta theta A B C D E hApos hkap hjdiv hder
  have hT1 : A.natDegree < 3 * A.natDegree := by
    rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, _⟩
    omega
  have hT2 : 2 * A.natDegree < 4 * A.natDegree := by
    rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, _⟩
    omega
  have hdeg1 : 3 * A.natDegree = 2 * C.natDegree + D.natDegree := by
    rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
      hCne', hDne', heq, hBcmp, hEcmp⟩
    omega
  have hdeg2 : 4 * A.natDegree =
      A.natDegree + 2 * C.natDegree + D.natDegree := by omega
  have hz1 : (degreeZeroN1Cubic610 0 alpha 0 0 epsilon zeta eta
        theta A B C D E).coeff (3 * A.natDegree) = 0 :=
    coeff_eq_zero_of_natDegree_lt (hN1le.trans_lt hT1)
  have hz2 : (degreeZeroN2Cubic610 0 alpha 0 0 epsilon zeta eta
        theta A B C D E).coeff (4 * A.natDegree) = 0 :=
    coeff_eq_zero_of_natDegree_lt (hN2le.trans_lt hT2)
  have hN1rest :=
    degreeZeroN1CubicCDWallZetaRest610_natDegree_lt alpha epsilon zeta eta
      theta A B C D E hcone hwall
  have hN2rest :=
    degreeZeroN2CubicCDWallZetaRest610_natDegree_lt alpha epsilon zeta eta
      theta A B C D E hcone hwall
  rw [degreeZeroN1Cubic610_eq_CD_zetaWall, coeff_add, coeff_add] at hz1
  have hN1small :
      (degreeZeroN1CubicCDWallZetaRest610 alpha epsilon zeta eta theta
          A B C D E).coeff (3 * A.natDegree) = 0 :=
    coeff_eq_zero_of_natDegree_lt (hdeg1 ▸ hN1rest)
  rw [hN1small, add_zero] at hz1
  rw [degreeZeroN2Cubic610_eq_CD_zetaWall, coeff_add, coeff_add] at hz2
  have hN2small :
      (degreeZeroN2CubicCDWallZetaRest610 alpha epsilon zeta eta theta
          A B C D E).coeff (4 * A.natDegree) = 0 :=
    coeff_eq_zero_of_natDegree_lt (hdeg2 ▸ hN2rest)
  rw [hN2small, add_zero] at hz2
  have hN1face := n1CubicSigmaFaceCD610_coeff_top A B C D E hCne hDne
  have hN2face := n2CubicSigmaFaceCD610_coeff_top A B C D E hAne hCne hDne
  have hN1L := n1CubicZetaFace610_coeff_top zeta A
  have hN2L := n2CubicZetaFace610_coeff_top zeta A
  rw [← hdeg1] at hN1face
  rw [hN1face, hN1L] at hz1
  rw [← hdeg2] at hN2face
  rw [hN2face, hN2L] at hz2
  have hx : zeta = 0 :=
    n1n2_zeta_column_det610 A.leadingCoeff
      ((-(5 / 27 : k)) * C.leadingCoeff ^ 2 * D.leadingCoeff) zeta
      (leadingCoeff_ne_zero.mpr hAne)
      (by simpa [add_comm] using hz1)
      (by
        have : (5 / 27 : k) * A.leadingCoeff * C.leadingCoeff ^ 2 *
              D.leadingCoeff =
            -A.leadingCoeff *
              ((-(5 / 27 : k)) * C.leadingCoeff ^ 2 * D.leadingCoeff) := by
          ring
        rw [this] at hz2
        simpa [add_comm, sub_eq_add_neg] using hz2)
  have hTpos : A.natDegree < 2 * C.natDegree + D.natDegree := by
    rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
      hCne', hDne', heq, hBcmp, hEcmp⟩
    omega
  exact cubicLoadSigmaCone_CD_offWall_impossible 0 alpha 0 0 epsilon
    zeta eta theta A B C D E hcone rfl (Or.inl rfl) (Or.inl rfl)
    (Or.inl hx) (Or.inr (by omega)) hTpos hmu hkap

set_option maxHeartbeats 64000000 in
theorem cubicLoadSigmaCone_CD_thetaWall_impossible {j t : k}
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hl : l = 0)
    (hwall : 7 * (12 * A.natDegree) = 54 * A.natDegree + 42 * C.natDegree)
    (hmu : (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta
          theta A B C D E).natDegree = 0)
    (hkap : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree = 0)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E) =
        Polynomial.C (j / t)) :
    False := by
  subst hl
  have hbetaTop := cubicLoadSigmaConeCD610_n1BetaTop_of_thetaWall hcone hwall
  have hbeta0 : beta = 0 :=
    cubicN1_beta_eq_zero 0 alpha beta delta epsilon zeta eta theta
      A B C D E hbetaTop rfl hmu hkap
  subst hbeta0
  have hdeltaTop := cubicLoadSigmaConeCD610_n1DeltaTop_of_thetaWall hcone hwall
  have hdelta0 : delta = 0 :=
    cubicN1_delta_eq_zero 0 alpha 0 delta epsilon zeta eta theta
      A B C D E hdeltaTop rfl rfl hmu hkap
  subst hdelta0
  have hzetaTop := cubicLoadSigmaConeCD610_n1ZetaTop_of_thetaWall hcone hwall
  have hzeta0 : zeta = 0 :=
    cubicN1_zeta_eq_zero 0 alpha 0 0 epsilon zeta eta theta
      A B C D E hzetaTop rfl rfl rfl hmu hkap
  subst hzeta0
  have hAne := CubicLoadSigmaConeCD610_A_ne hcone
  have hCne : C ≠ 0 := hcone.2.1
  have hDne : D ≠ 0 := hcone.2.2.1
  have hApos : 0 < A.natDegree := hcone.1.1.1
  have hN1le := degreeZeroN1Cubic610_natDegree_le 0 alpha 0 0 epsilon
      0 eta theta A B C D E hmu hkap
  have hN2le := degreeZeroN2Cubic610_natDegree_le (j := j) (t := t) 0
      alpha 0 0 epsilon 0 eta theta A B C D E hApos hkap hjdiv hder
  have hT1 : A.natDegree < 2 * A.natDegree := by
    rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, _⟩
    omega
  have hT2 : 2 * A.natDegree < 3 * A.natDegree := by
    rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, _⟩
    omega
  have hdeg1 : 2 * A.natDegree = 2 * C.natDegree + D.natDegree := by
    rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
      hCne', hDne', heq, hBcmp, hEcmp⟩
    omega
  have hdeg2 : 3 * A.natDegree =
      A.natDegree + 2 * C.natDegree + D.natDegree := by omega
  have hz1 : (degreeZeroN1Cubic610 0 alpha 0 0 epsilon 0 eta
        theta A B C D E).coeff (2 * A.natDegree) = 0 :=
    coeff_eq_zero_of_natDegree_lt (hN1le.trans_lt hT1)
  have hz2 : (degreeZeroN2Cubic610 0 alpha 0 0 epsilon 0 eta
        theta A B C D E).coeff (3 * A.natDegree) = 0 :=
    coeff_eq_zero_of_natDegree_lt (hN2le.trans_lt hT2)
  have hN1rest :=
    degreeZeroN1CubicCDWallThetaRest610_natDegree_lt alpha epsilon eta theta
      A B C D E hcone hwall
  have hN2rest :=
    degreeZeroN2CubicCDWallThetaRest610_natDegree_lt alpha epsilon eta theta
      A B C D E hcone hwall
  rw [degreeZeroN1Cubic610_eq_CD_thetaWall, coeff_add, coeff_add] at hz1
  have hN1small :
      (degreeZeroN1CubicCDWallThetaRest610 alpha epsilon eta theta
          A B C D E).coeff (2 * A.natDegree) = 0 :=
    coeff_eq_zero_of_natDegree_lt (hdeg1 ▸ hN1rest)
  rw [hN1small, add_zero] at hz1
  rw [degreeZeroN2Cubic610_eq_CD_thetaWall, coeff_add, coeff_add] at hz2
  have hN2small :
      (degreeZeroN2CubicCDWallThetaRest610 alpha epsilon eta theta
          A B C D E).coeff (3 * A.natDegree) = 0 :=
    coeff_eq_zero_of_natDegree_lt (hdeg2 ▸ hN2rest)
  rw [hN2small, add_zero] at hz2
  have hN1face := n1CubicSigmaFaceCD610_coeff_top A B C D E hCne hDne
  have hN2face := n2CubicSigmaFaceCD610_coeff_top A B C D E hAne hCne hDne
  have hN1L := n1CubicThetaFace610_coeff_top theta A
  have hN2L := n2CubicThetaFace610_coeff_top theta A
  rw [← hdeg1] at hN1face
  rw [hN1face, hN1L] at hz1
  rw [← hdeg2] at hN2face
  rw [hN2face, hN2L] at hz2
  have hx : theta = 0 :=
    n1n2_theta_column_det610 A.leadingCoeff
      ((-(5 / 27 : k)) * C.leadingCoeff ^ 2 * D.leadingCoeff) theta
      (leadingCoeff_ne_zero.mpr hAne)
      (by simpa [add_comm] using hz1)
      (by
        have : (5 / 27 : k) * A.leadingCoeff * C.leadingCoeff ^ 2 *
              D.leadingCoeff =
            -A.leadingCoeff *
              ((-(5 / 27 : k)) * C.leadingCoeff ^ 2 * D.leadingCoeff) := by
          ring
        rw [this] at hz2
        simpa [add_comm, sub_eq_add_neg] using hz2)
  have hTpos : A.natDegree < 2 * C.natDegree + D.natDegree := by
    rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
      hCne', hDne', heq, hBcmp, hEcmp⟩
    omega
  exact cubicLoadSigmaCone_CD_offWall_impossible 0 alpha 0 0 epsilon
    0 eta theta A B C D E hcone rfl (Or.inl rfl) (Or.inl rfl)
    (Or.inl rfl) (Or.inl hx) hTpos hmu hkap

end CubicLoadCDWallKills610


/-! ## `{B,C,D,E}` wall kills -/

section CubicLoadBCDEWallKills610

variable {k : Type*} [Field k] [CharZero k]

theorem CubicLoadSigmaConeBCDE610_A_ne
    {A B C D E : k[X]} (hcone : CubicLoadSigmaConeBCDE610 A B C D E) :
    A ≠ 0 := by
  intro h0
  have : A.natDegree = 0 := by simp [h0]
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, _⟩
  omega

set_option maxHeartbeats 64000000 in
theorem cubicLoadSigmaCone_BCDE_betaWall_impossible {j t : k}
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeBCDE610 A B C D E)
    (hl : l = 0)
    (hwall : 7 * (9 * A.natDegree) = 18 * A.natDegree + 42 * B.natDegree)
    (hlam : (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree = 0)
    (hkap : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree = 0)
    (hmu : (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta
          theta A B C D E).natDegree = 0)
    (homi : (degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree = 0)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E) =
        Polynomial.C (j / t)) :
    False := by
  subst hl
  have hAne := CubicLoadSigmaConeBCDE610_A_ne hcone
  have hBne : B ≠ 0 := hcone.2.1
  have hCne : C ≠ 0 := hcone.2.2.1
  have hDne : D ≠ 0 := hcone.2.2.2.1
  have hEne : E ≠ 0 := hcone.2.2.2.2.1
  have hApos : 0 < A.natDegree := hcone.1.1.1
  have hN1le := degreeZeroN1Cubic610_natDegree_le 0 alpha beta delta epsilon
      zeta eta theta A B C D E hmu hkap
  have hN2le := degreeZeroN2Cubic610_natDegree_le (j := j) (t := t) 0
      alpha beta delta epsilon zeta eta theta A B C D E hApos hkap hjdiv hder
  have hT1 : A.natDegree < 5 * A.natDegree := by
    rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, _⟩
    omega
  have hT2 : 2 * A.natDegree < 6 * A.natDegree := by
    rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, _⟩
    omega
  have hdeg1 : 5 * A.natDegree =
      A.natDegree + 2 * B.natDegree + D.natDegree := by
    rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
      hBne', hCne', hDne', hEne', heq1, heq2, heq3⟩
    omega
  have hdeg2 : 6 * A.natDegree =
      2 * A.natDegree + 2 * B.natDegree + D.natDegree := by omega
  have hz1 : (degreeZeroN1Cubic610 0 alpha beta delta epsilon zeta eta
        theta A B C D E).coeff (5 * A.natDegree) = 0 :=
    coeff_eq_zero_of_natDegree_lt (hN1le.trans_lt hT1)
  have hz2 : (degreeZeroN2Cubic610 0 alpha beta delta epsilon zeta eta
        theta A B C D E).coeff (6 * A.natDegree) = 0 :=
    coeff_eq_zero_of_natDegree_lt (hN2le.trans_lt hT2)
  have hN1rest :=
    degreeZeroN1CubicBCDEWallBetaRest610_natDegree_lt alpha beta delta
      epsilon zeta eta theta A B C D E hcone hwall
  have hN2rest :=
    degreeZeroN2CubicBCDEWallBetaRest610_natDegree_lt alpha beta delta
      epsilon zeta eta theta A B C D E hcone hwall
  rw [degreeZeroN1Cubic610_eq_BCDE_betaWall, coeff_add, coeff_add] at hz1
  have hN1small :
      (degreeZeroN1CubicBCDEWallBetaRest610 alpha beta delta epsilon zeta
          eta theta A B C D E).coeff (5 * A.natDegree) = 0 :=
    coeff_eq_zero_of_natDegree_lt (hdeg1 ▸ hN1rest)
  rw [hN1small, add_zero] at hz1
  rw [degreeZeroN2Cubic610_eq_BCDE_betaWall, coeff_add, coeff_add] at hz2
  have hN2small :
      (degreeZeroN2CubicBCDEWallBetaRest610 alpha beta delta epsilon zeta
          eta theta A B C D E).coeff (6 * A.natDegree) = 0 :=
    coeff_eq_zero_of_natDegree_lt (hdeg2 ▸ hN2rest)
  rw [hN2small, add_zero] at hz2
  have hN1face := n1CubicSigmaFaceBCDE610_coeff_top_of_loadCone
      (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne)
      (hDne := hDne) (hEne := hEne)
  have hN2face := n2CubicSigmaFaceBCDE610_coeff_top_of_loadCone
      (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne)
      (hDne := hDne) (hEne := hEne)
  have hN1L := n1CubicBetaFace610_coeff_top beta A
  have hN2L := n2CubicBetaFace610_coeff_top beta A
  rw [← hdeg1] at hN1face
  rw [hN1face, hN1L] at hz1
  rw [← hdeg2] at hN2face
  rw [hN2face, hN2L] at hz2
  have hx : beta = 0 :=
    n1n2_beta_column_det610 A.leadingCoeff
      ((5 / 81 : k) * n1CubicSigmaInnerBCDE610 A.leadingCoeff B.leadingCoeff
        C.leadingCoeff D.leadingCoeff E.leadingCoeff) beta
      (leadingCoeff_ne_zero.mpr hAne)
      (by simpa [add_comm] using hz1)
      (by
        have :
            (-(5 / 81 : k)) *
                n1CubicSigmaInnerBCDE610 A.leadingCoeff B.leadingCoeff
                  C.leadingCoeff D.leadingCoeff E.leadingCoeff *
                A.leadingCoeff =
              -A.leadingCoeff *
                ((5 / 81 : k) *
                  n1CubicSigmaInnerBCDE610 A.leadingCoeff B.leadingCoeff
                    C.leadingCoeff D.leadingCoeff E.leadingCoeff) := by
          ring
        rw [this] at hz2
        simpa [add_comm, sub_eq_add_neg] using hz2)
  exact cubicLoadSigmaCone_BCDE_offWall_impossible (j := j) (t := t) 0
    alpha beta delta epsilon zeta eta theta A B C D E hcone rfl
    (Or.inl hx) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
    hlam hkap hmu homi

set_option maxHeartbeats 64000000 in
theorem cubicLoadSigmaCone_BCDE_deltaWall_impossible {j t : k}
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeBCDE610 A B C D E)
    (hl : l = 0)
    (hwall : 7 * (9 * A.natDegree) = 30 * A.natDegree + 42 * B.natDegree)
    (hlam : (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree = 0)
    (hkap : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree = 0)
    (hmu : (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta
          theta A B C D E).natDegree = 0)
    (homi : (degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree = 0)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E) =
        Polynomial.C (j / t)) :
    False := by
  subst hl
  have hbetaTop := cubicLoadSigmaConeBCDE610_n1BetaTop_of_deltaWall hcone hwall
  have hbeta0 : beta = 0 :=
    cubicN1_beta_eq_zero 0 alpha beta delta epsilon zeta eta theta
      A B C D E hbetaTop rfl hmu hkap
  subst hbeta0
  have hAne := CubicLoadSigmaConeBCDE610_A_ne hcone
  have hBne : B ≠ 0 := hcone.2.1
  have hCne : C ≠ 0 := hcone.2.2.1
  have hDne : D ≠ 0 := hcone.2.2.2.1
  have hEne : E ≠ 0 := hcone.2.2.2.2.1
  have hApos : 0 < A.natDegree := hcone.1.1.1
  have hN1le := degreeZeroN1Cubic610_natDegree_le 0 alpha 0 delta epsilon
      zeta eta theta A B C D E hmu hkap
  have hN2le := degreeZeroN2Cubic610_natDegree_le (j := j) (t := t) 0
      alpha 0 delta epsilon zeta eta theta A B C D E hApos hkap hjdiv hder
  have hT1 : A.natDegree < 4 * A.natDegree := by
    rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, _⟩
    omega
  have hT2 : 2 * A.natDegree < 5 * A.natDegree := by
    rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, _⟩
    omega
  have hdeg1 : 4 * A.natDegree =
      A.natDegree + 2 * B.natDegree + D.natDegree := by
    rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
      hBne', hCne', hDne', hEne', heq1, heq2, heq3⟩
    omega
  have hdeg2 : 5 * A.natDegree =
      2 * A.natDegree + 2 * B.natDegree + D.natDegree := by omega
  have hz1 : (degreeZeroN1Cubic610 0 alpha 0 delta epsilon zeta eta
        theta A B C D E).coeff (4 * A.natDegree) = 0 :=
    coeff_eq_zero_of_natDegree_lt (hN1le.trans_lt hT1)
  have hz2 : (degreeZeroN2Cubic610 0 alpha 0 delta epsilon zeta eta
        theta A B C D E).coeff (5 * A.natDegree) = 0 :=
    coeff_eq_zero_of_natDegree_lt (hN2le.trans_lt hT2)
  have hN1rest :=
    degreeZeroN1CubicBCDEWallDeltaRest610_natDegree_lt alpha delta epsilon
      zeta eta theta A B C D E hcone hwall
  have hN2rest :=
    degreeZeroN2CubicBCDEWallDeltaRest610_natDegree_lt alpha delta epsilon
      zeta eta theta A B C D E hcone hwall
  rw [degreeZeroN1Cubic610_eq_BCDE_deltaWall, coeff_add, coeff_add] at hz1
  have hN1small :
      (degreeZeroN1CubicBCDEWallDeltaRest610 alpha delta epsilon zeta eta
          theta A B C D E).coeff (4 * A.natDegree) = 0 :=
    coeff_eq_zero_of_natDegree_lt (hdeg1 ▸ hN1rest)
  rw [hN1small, add_zero] at hz1
  rw [degreeZeroN2Cubic610_eq_BCDE_deltaWall, coeff_add, coeff_add] at hz2
  have hN2small :
      (degreeZeroN2CubicBCDEWallDeltaRest610 alpha delta epsilon zeta eta
          theta A B C D E).coeff (5 * A.natDegree) = 0 :=
    coeff_eq_zero_of_natDegree_lt (hdeg2 ▸ hN2rest)
  rw [hN2small, add_zero] at hz2
  have hN1face := n1CubicSigmaFaceBCDE610_coeff_top_of_loadCone
      (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne)
      (hDne := hDne) (hEne := hEne)
  have hN2face := n2CubicSigmaFaceBCDE610_coeff_top_of_loadCone
      (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne)
      (hDne := hDne) (hEne := hEne)
  have hN1L := n1CubicDeltaFace610_coeff_top delta A
  have hN2L := n2CubicDeltaFace610_coeff_top delta A
  rw [← hdeg1] at hN1face
  rw [hN1face, hN1L] at hz1
  rw [← hdeg2] at hN2face
  rw [hN2face, hN2L] at hz2
  have hx : delta = 0 :=
    n1n2_delta_column_det610 A.leadingCoeff
      ((5 / 81 : k) * n1CubicSigmaInnerBCDE610 A.leadingCoeff B.leadingCoeff
        C.leadingCoeff D.leadingCoeff E.leadingCoeff) delta
      (leadingCoeff_ne_zero.mpr hAne)
      (by simpa [add_comm] using hz1)
      (by
        have :
            (-(5 / 81 : k)) *
                n1CubicSigmaInnerBCDE610 A.leadingCoeff B.leadingCoeff
                  C.leadingCoeff D.leadingCoeff E.leadingCoeff *
                A.leadingCoeff =
              -A.leadingCoeff *
                ((5 / 81 : k) *
                  n1CubicSigmaInnerBCDE610 A.leadingCoeff B.leadingCoeff
                    C.leadingCoeff D.leadingCoeff E.leadingCoeff) := by
          ring
        rw [this] at hz2
        simpa [add_comm, sub_eq_add_neg] using hz2)
  exact cubicLoadSigmaCone_BCDE_offWall_impossible (j := j) (t := t) 0
    alpha 0 delta epsilon zeta eta theta A B C D E hcone rfl
    (Or.inl rfl) (Or.inl hx) (Or.inr (by omega)) (Or.inr (by omega))
    hlam hkap hmu homi

set_option maxHeartbeats 64000000 in
theorem cubicLoadSigmaCone_BCDE_zetaWall_impossible {j t : k}
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeBCDE610 A B C D E)
    (hl : l = 0)
    (hwall : 9 * A.natDegree = 6 * A.natDegree + 6 * B.natDegree)
    (hlam : (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree = 0)
    (hkap : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree = 0)
    (hmu : (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta
          theta A B C D E).natDegree = 0)
    (homi : (degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree = 0)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E) =
        Polynomial.C (j / t)) :
    False := by
  subst hl
  have hbetaTop := cubicLoadSigmaConeBCDE610_n1BetaTop_of_zetaWall hcone hwall
  have hbeta0 : beta = 0 :=
    cubicN1_beta_eq_zero 0 alpha beta delta epsilon zeta eta theta
      A B C D E hbetaTop rfl hmu hkap
  subst hbeta0
  have hdeltaTop := cubicLoadSigmaConeBCDE610_n1DeltaTop_of_zetaWall hcone hwall
  have hdelta0 : delta = 0 :=
    cubicN1_delta_eq_zero 0 alpha 0 delta epsilon zeta eta theta
      A B C D E hdeltaTop rfl rfl hmu hkap
  subst hdelta0
  have hAne := CubicLoadSigmaConeBCDE610_A_ne hcone
  have hBne : B ≠ 0 := hcone.2.1
  have hCne : C ≠ 0 := hcone.2.2.1
  have hDne : D ≠ 0 := hcone.2.2.2.1
  have hEne : E ≠ 0 := hcone.2.2.2.2.1
  have hApos : 0 < A.natDegree := hcone.1.1.1
  have hN1le := degreeZeroN1Cubic610_natDegree_le 0 alpha 0 0 epsilon
      zeta eta theta A B C D E hmu hkap
  have hN2le := degreeZeroN2Cubic610_natDegree_le (j := j) (t := t) 0
      alpha 0 0 epsilon zeta eta theta A B C D E hApos hkap hjdiv hder
  have hT1 : A.natDegree < 3 * A.natDegree := by
    rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, _⟩
    omega
  have hT2 : 2 * A.natDegree < 4 * A.natDegree := by
    rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, _⟩
    omega
  have hdeg1 : 3 * A.natDegree =
      A.natDegree + 2 * B.natDegree + D.natDegree := by
    rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
      hBne', hCne', hDne', hEne', heq1, heq2, heq3⟩
    omega
  have hdeg2 : 4 * A.natDegree =
      2 * A.natDegree + 2 * B.natDegree + D.natDegree := by omega
  have hz1 : (degreeZeroN1Cubic610 0 alpha 0 0 epsilon zeta eta
        theta A B C D E).coeff (3 * A.natDegree) = 0 :=
    coeff_eq_zero_of_natDegree_lt (hN1le.trans_lt hT1)
  have hz2 : (degreeZeroN2Cubic610 0 alpha 0 0 epsilon zeta eta
        theta A B C D E).coeff (4 * A.natDegree) = 0 :=
    coeff_eq_zero_of_natDegree_lt (hN2le.trans_lt hT2)
  have hN1rest :=
    degreeZeroN1CubicBCDEWallZetaRest610_natDegree_lt alpha epsilon zeta eta
      theta A B C D E hcone hwall
  have hN2rest :=
    degreeZeroN2CubicBCDEWallZetaRest610_natDegree_lt alpha epsilon zeta eta
      theta A B C D E hcone hwall
  rw [degreeZeroN1Cubic610_eq_BCDE_zetaWall, coeff_add, coeff_add] at hz1
  have hN1small :
      (degreeZeroN1CubicBCDEWallZetaRest610 alpha epsilon zeta eta theta
          A B C D E).coeff (3 * A.natDegree) = 0 :=
    coeff_eq_zero_of_natDegree_lt (hdeg1 ▸ hN1rest)
  rw [hN1small, add_zero] at hz1
  rw [degreeZeroN2Cubic610_eq_BCDE_zetaWall, coeff_add, coeff_add] at hz2
  have hN2small :
      (degreeZeroN2CubicBCDEWallZetaRest610 alpha epsilon zeta eta theta
          A B C D E).coeff (4 * A.natDegree) = 0 :=
    coeff_eq_zero_of_natDegree_lt (hdeg2 ▸ hN2rest)
  rw [hN2small, add_zero] at hz2
  have hN1face := n1CubicSigmaFaceBCDE610_coeff_top_of_loadCone
      (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne)
      (hDne := hDne) (hEne := hEne)
  have hN2face := n2CubicSigmaFaceBCDE610_coeff_top_of_loadCone
      (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne)
      (hDne := hDne) (hEne := hEne)
  have hN1L := n1CubicZetaFace610_coeff_top zeta A
  have hN2L := n2CubicZetaFace610_coeff_top zeta A
  rw [← hdeg1] at hN1face
  rw [hN1face, hN1L] at hz1
  rw [← hdeg2] at hN2face
  rw [hN2face, hN2L] at hz2
  have hx : zeta = 0 :=
    n1n2_zeta_column_det610 A.leadingCoeff
      ((5 / 81 : k) * n1CubicSigmaInnerBCDE610 A.leadingCoeff B.leadingCoeff
        C.leadingCoeff D.leadingCoeff E.leadingCoeff) zeta
      (leadingCoeff_ne_zero.mpr hAne)
      (by simpa [add_comm] using hz1)
      (by
        have :
            (-(5 / 81 : k)) *
                n1CubicSigmaInnerBCDE610 A.leadingCoeff B.leadingCoeff
                  C.leadingCoeff D.leadingCoeff E.leadingCoeff *
                A.leadingCoeff =
              -A.leadingCoeff *
                ((5 / 81 : k) *
                  n1CubicSigmaInnerBCDE610 A.leadingCoeff B.leadingCoeff
                    C.leadingCoeff D.leadingCoeff E.leadingCoeff) := by
          ring
        rw [this] at hz2
        simpa [add_comm, sub_eq_add_neg] using hz2)
  exact cubicLoadSigmaCone_BCDE_offWall_impossible (j := j) (t := t) 0
    alpha 0 0 epsilon zeta eta theta A B C D E hcone rfl
    (Or.inl rfl) (Or.inl rfl) (Or.inl hx) (Or.inr (by omega))
    hlam hkap hmu homi

set_option maxHeartbeats 64000000 in
theorem cubicLoadSigmaCone_BCDE_thetaWall_impossible {j t : k}
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeBCDE610 A B C D E)
    (hl : l = 0)
    (hwall : 7 * (9 * A.natDegree) = 54 * A.natDegree + 42 * B.natDegree)
    (hlam : (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree = 0)
    (hkap : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree = 0)
    (hmu : (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta
          theta A B C D E).natDegree = 0)
    (homi : (degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree = 0)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E) =
        Polynomial.C (j / t)) :
    False := by
  subst hl
  have hbetaTop := cubicLoadSigmaConeBCDE610_n1BetaTop_of_thetaWall hcone hwall
  have hbeta0 : beta = 0 :=
    cubicN1_beta_eq_zero 0 alpha beta delta epsilon zeta eta theta
      A B C D E hbetaTop rfl hmu hkap
  subst hbeta0
  have hdeltaTop := cubicLoadSigmaConeBCDE610_n1DeltaTop_of_thetaWall hcone hwall
  have hdelta0 : delta = 0 :=
    cubicN1_delta_eq_zero 0 alpha 0 delta epsilon zeta eta theta
      A B C D E hdeltaTop rfl rfl hmu hkap
  subst hdelta0
  have hzetaTop := cubicLoadSigmaConeBCDE610_n1ZetaTop_of_thetaWall hcone hwall
  have hzeta0 : zeta = 0 :=
    cubicN1_zeta_eq_zero 0 alpha 0 0 epsilon zeta eta theta
      A B C D E hzetaTop rfl rfl rfl hmu hkap
  subst hzeta0
  have hAne := CubicLoadSigmaConeBCDE610_A_ne hcone
  have hBne : B ≠ 0 := hcone.2.1
  have hCne : C ≠ 0 := hcone.2.2.1
  have hDne : D ≠ 0 := hcone.2.2.2.1
  have hEne : E ≠ 0 := hcone.2.2.2.2.1
  have hApos : 0 < A.natDegree := hcone.1.1.1
  have hN1le := degreeZeroN1Cubic610_natDegree_le 0 alpha 0 0 epsilon
      0 eta theta A B C D E hmu hkap
  have hN2le := degreeZeroN2Cubic610_natDegree_le (j := j) (t := t) 0
      alpha 0 0 epsilon 0 eta theta A B C D E hApos hkap hjdiv hder
  have hT1 : A.natDegree < 2 * A.natDegree := by
    rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, _⟩
    omega
  have hT2 : 2 * A.natDegree < 3 * A.natDegree := by
    rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, _⟩
    omega
  have hdeg1 : 2 * A.natDegree =
      A.natDegree + 2 * B.natDegree + D.natDegree := by
    rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
      hBne', hCne', hDne', hEne', heq1, heq2, heq3⟩
    omega
  have hdeg2 : 3 * A.natDegree =
      2 * A.natDegree + 2 * B.natDegree + D.natDegree := by omega
  have hz1 : (degreeZeroN1Cubic610 0 alpha 0 0 epsilon 0 eta
        theta A B C D E).coeff (2 * A.natDegree) = 0 :=
    coeff_eq_zero_of_natDegree_lt (hN1le.trans_lt hT1)
  have hz2 : (degreeZeroN2Cubic610 0 alpha 0 0 epsilon 0 eta
        theta A B C D E).coeff (3 * A.natDegree) = 0 :=
    coeff_eq_zero_of_natDegree_lt (hN2le.trans_lt hT2)
  have hN1rest :=
    degreeZeroN1CubicBCDEWallThetaRest610_natDegree_lt alpha epsilon eta
      theta A B C D E hcone hwall
  have hN2rest :=
    degreeZeroN2CubicBCDEWallThetaRest610_natDegree_lt alpha epsilon eta
      theta A B C D E hcone hwall
  rw [degreeZeroN1Cubic610_eq_BCDE_thetaWall, coeff_add, coeff_add] at hz1
  have hN1small :
      (degreeZeroN1CubicBCDEWallThetaRest610 alpha epsilon eta theta
          A B C D E).coeff (2 * A.natDegree) = 0 :=
    coeff_eq_zero_of_natDegree_lt (hdeg1 ▸ hN1rest)
  rw [hN1small, add_zero] at hz1
  rw [degreeZeroN2Cubic610_eq_BCDE_thetaWall, coeff_add, coeff_add] at hz2
  have hN2small :
      (degreeZeroN2CubicBCDEWallThetaRest610 alpha epsilon eta theta
          A B C D E).coeff (3 * A.natDegree) = 0 :=
    coeff_eq_zero_of_natDegree_lt (hdeg2 ▸ hN2rest)
  rw [hN2small, add_zero] at hz2
  have hN1face := n1CubicSigmaFaceBCDE610_coeff_top_of_loadCone
      (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne)
      (hDne := hDne) (hEne := hEne)
  have hN2face := n2CubicSigmaFaceBCDE610_coeff_top_of_loadCone
      (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne)
      (hDne := hDne) (hEne := hEne)
  have hN1L := n1CubicThetaFace610_coeff_top theta A
  have hN2L := n2CubicThetaFace610_coeff_top theta A
  rw [← hdeg1] at hN1face
  rw [hN1face, hN1L] at hz1
  rw [← hdeg2] at hN2face
  rw [hN2face, hN2L] at hz2
  have hx : theta = 0 :=
    n1n2_theta_column_det610 A.leadingCoeff
      ((5 / 81 : k) * n1CubicSigmaInnerBCDE610 A.leadingCoeff B.leadingCoeff
        C.leadingCoeff D.leadingCoeff E.leadingCoeff) theta
      (leadingCoeff_ne_zero.mpr hAne)
      (by simpa [add_comm] using hz1)
      (by
        have :
            (-(5 / 81 : k)) *
                n1CubicSigmaInnerBCDE610 A.leadingCoeff B.leadingCoeff
                  C.leadingCoeff D.leadingCoeff E.leadingCoeff *
                A.leadingCoeff =
              -A.leadingCoeff *
                ((5 / 81 : k) *
                  n1CubicSigmaInnerBCDE610 A.leadingCoeff B.leadingCoeff
                    C.leadingCoeff D.leadingCoeff E.leadingCoeff) := by
          ring
        rw [this] at hz2
        simpa [add_comm, sub_eq_add_neg] using hz2)
  exact cubicLoadSigmaCone_BCDE_offWall_impossible (j := j) (t := t) 0
    alpha 0 0 epsilon 0 eta theta A B C D E hcone rfl
    (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) (Or.inl hx)
    hlam hkap hmu homi

end CubicLoadBCDEWallKills610


/-! ## `{C,D}` chamber `2c+d ≤ a` via λ + ο -/

section CubicLoadCDChamber610

variable {k : Type*} [Field k] [CharZero k]

theorem degreeZeroLambdaCubicNoSigmaCD610_eq_chamberRest
    (alpha epsilon eta : k) (A C D E : k[X]) :
    degreeZeroLambdaCubicNoSigmaCD610 0 alpha 0 0 epsilon 0 eta 0 A 0 C D E =
      lambdaChamberRestCD610 alpha epsilon eta A C D E := by
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  simp only [degreeZeroLambdaCubicNoSigmaCD610, lambdaChamberRestCD610,
    hpow2, hpow3, hpow4, zero_mul, mul_zero, zero_smul, smul_zero,
    add_zero, zero_add, sub_zero, neg_zero]
  all_goals module

def kappaChamberCD610 (alpha epsilon : k) (C D E : k[X]) : k[X] :=
  (10 / 9 : k) • (D * E)
  + (4 / 9 * alpha : k) • (C * D)
  + (2 / 3 * epsilon : k) • D

theorem degreeZeroKappaCubic610_eq_chamber
    (alpha epsilon eta : k) (A C D E : k[X]) :
    degreeZeroKappaCubic610 0 alpha 0 0 epsilon 0 eta 0 A 0 C D E =
      kappaChamberCD610 alpha epsilon C D E := by
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  simp only [degreeZeroKappaCubic610, kappaChamberCD610, hpow2, hpow3,
    zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero,
    neg_zero]
  all_goals module

def omicronChamberCD610 (alpha epsilon eta : k) (A C D E : k[X]) : k[X] :=
  (-(5 / 27 : k)) • (C ^ 2 * E)
  + (-(5 / 27 : k)) • (C * D ^ 2)
  + (-(2 / 27 * alpha : k)) • (A * D ^ 2)
  + (-(4 / 81 * alpha : k)) • C ^ 3
  + (2 / 9 * alpha : k) • E ^ 2
  + (-(1 / 9 * epsilon : k)) • C ^ 2
  + (1 / 3 * eta : k) • E

theorem degreeZeroOmicronCubic610_eq_chamber
    (alpha epsilon eta : k) (A C D E : k[X]) :
    degreeZeroOmicronCubic610 0 alpha 0 0 epsilon 0 eta 0 A 0 C D E =
      omicronChamberCD610 alpha epsilon eta A C D E := by
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  simp only [degreeZeroOmicronCubic610, omicronChamberCD610, hpow2, hpow3,
    hpow4, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add,
    sub_zero, neg_zero]
  all_goals module

theorem omicronCubicSigmaFaceCD610_coeff_top
    (A B C D E : k[X]) (hC : C ≠ 0) (hD : D ≠ 0) :
    (omicronCubicSigmaFaceCD610 A B C D E).coeff
        (C.natDegree + 2 * D.natDegree) =
      (-(5 / 27 : k)) * C.leadingCoeff * D.leadingCoeff ^ 2 := by
  simp only [omicronCubicSigmaFaceCD610, coeff_smul, smul_eq_mul]
  have hdeg : (C * D ^ 2).natDegree = C.natDegree + 2 * D.natDegree := by
    rw [natDegree_mul hC (pow_ne_zero 2 hD), natDegree_pow]
  rw [← hdeg, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  ring

theorem kappaChamberCD610_of_E_eq_zero (alpha epsilon : k) (C D : k[X]) :
    kappaChamberCD610 alpha epsilon C D 0 =
      (4 / 9 * alpha : k) • (C * D) + (2 / 3 * epsilon : k) • D := by
  simp only [kappaChamberCD610, mul_zero, smul_zero, add_zero, zero_add]

theorem kappaChamberCD610_of_alpha_eq_zero (epsilon : k) (C D E : k[X]) :
    kappaChamberCD610 0 epsilon C D E =
      (10 / 9 : k) • (D * E) + (2 / 3 * epsilon : k) • D := by
  unfold kappaChamberCD610
  have hCD : ((4 / 9 * (0 : k) : k)) • (C * D) = 0 := by
    have hz : (4 / 9 * (0 : k) : k) = 0 := by ring
    rw [hz, zero_smul]
  rw [hCD, add_zero]

theorem omicronChamberCD610_of_alpha_eq_zero
    (epsilon eta : k) (A C D E : k[X]) :
    omicronChamberCD610 0 epsilon eta A C D E =
      (-(5 / 27 : k)) • (C ^ 2 * E) +
        (-(5 / 27 : k)) • (C * D ^ 2) +
        (-(1 / 9 * epsilon : k)) • C ^ 2 +
        (1 / 3 * eta : k) • E := by
  unfold omicronChamberCD610
  have hAD2 : (-(2 / 27 * (0 : k) : k)) • (A * D ^ 2) = 0 := by
    have hz : (2 / 27 * (0 : k) : k) = 0 := by ring
    rw [hz, neg_zero, zero_smul]
  have hC3 : (-(4 / 81 * (0 : k) : k)) • C ^ 3 = 0 := by
    have hz : (4 / 81 * (0 : k) : k) = 0 := by ring
    rw [hz, neg_zero, zero_smul]
  have hE2 : ((2 / 9 * (0 : k) : k)) • E ^ 2 = 0 := by
    have hz : (2 / 9 * (0 : k) : k) = 0 := by ring
    rw [hz, zero_smul]
  rw [hAD2, hC3, hE2]
  abel

theorem omicronChamberCD610_of_alpha_eq_zero_E_eq_zero
    (epsilon eta : k) (A C D : k[X]) :
    omicronChamberCD610 0 epsilon eta A C D 0 =
      (-(5 / 27 : k)) • (C * D ^ 2) +
        (-(1 / 9 * epsilon : k)) • C ^ 2 := by
  rw [omicronChamberCD610_of_alpha_eq_zero]
  have hC2E : (-(5 / 27 : k)) • (C ^ 2 * (0 : k[X])) = 0 := by
    simp
  have hE : ((1 / 3 * eta : k)) • (0 : k[X]) = 0 := by simp
  rw [hC2E, hE]
  abel

theorem omicronC2Block_of_natDegree_E_eq_zero
    (epsilon : k) (C E : k[X])
    (he0 : E.natDegree = 0) :
    (-(5 / 27 : k)) • (C ^ 2 * E) + (-(1 / 9 * epsilon : k)) • C ^ 2 =
      ((-(5 / 27 : k)) * E.leadingCoeff +
        (-(1 / 9 * epsilon : k))) • C ^ 2 := by
  have hE : E = Polynomial.C E.leadingCoeff := by
    have hcoeff : E.coeff 0 = E.leadingCoeff := by
      rw [← coeff_natDegree, he0]
    rw [← hcoeff]
    exact eq_C_of_natDegree_eq_zero he0
  conv_lhs => rw [hE]
  rw [mul_comm (C ^ 2) (Polynomial.C _), smul_eq_C_mul, smul_eq_C_mul,
    ← mul_assoc, ← C_mul, ← add_mul, ← C_add, ← smul_eq_C_mul]

/-- On `e = c`, the ο top after the κ relation `e = -(2/5) α c` is
`(4/81) α c³` plus a multiple of the λ inner `3ad² + c³`. -/
theorem cubicChamber_ec_scalar_identity (a c d alpha e : k)
    (hrel : e = -((2 / 5 : k) * alpha * c)) :
    (-(5 / 27 : k)) * c ^ 2 * e
      + (-(2 / 27 * alpha : k)) * a * d ^ 2
      + (-(4 / 81 * alpha : k)) * c ^ 3
    = ((4 / 81 : k) * alpha) * c ^ 3
      + (-(2 / 81 : k) * alpha) * (3 * a * d ^ 2 + c ^ 3) := by
  rw [hrel]
  ring

set_option maxHeartbeats 64000000 in
/-- Chamber `E = 0`: κ kills `α`, then ο has positive degree. -/
theorem cubicLoadSigmaCone_CD_chamber_E0_impossible
    (alpha epsilon eta : k) (A C D : k[X])
    (hAne : A ≠ 0) (hCne : C ≠ 0) (hDne : D ≠ 0)
    (hApos : 0 < A.natDegree)
    (hCD : A.natDegree + 2 * D.natDegree = 3 * C.natDegree)
    (hTle : 2 * C.natDegree + D.natDegree ≤ A.natDegree)
    (hload : cubicLoadCompetes610 A 0 C D 0)
    (hlam : (degreeZeroLambdaCubic610 0 alpha 0 0 epsilon 0 eta 0
          A 0 C D 0).natDegree = 0)
    (hkap : (degreeZeroKappaCubic610 0 alpha 0 0 epsilon 0 eta 0
          A 0 C D 0).natDegree = 0)
    (homi : (degreeZeroOmicronCubic610 0 alpha 0 0 epsilon 0 eta 0
          A 0 C D 0).natDegree = 0) :
    False := by
  have hCpos : 0 < C.natDegree := by
    have : ¬ C.natDegree = 0 := by
      intro hc0
      omega
    exact Nat.pos_of_ne_zero this
  have halpha0 : alpha = 0 := by
    by_contra halpha
    have hc : (4 / 9 * alpha : k) ≠ 0 :=
      mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) halpha
    have hlead :
        ((4 / 9 * alpha : k) • (C * D)).natDegree =
          C.natDegree + D.natDegree := by
      rw [natDegree_smul _ hc, natDegree_mul hCne hDne]
    have hrest :
        ((2 / 3 * epsilon : k) • D).natDegree <
          C.natDegree + D.natDegree := by
      refine (natDegree_smul_le610 _ _).trans_lt ?_
      have : D.natDegree < C.natDegree + D.natDegree := by omega
      exact this
    have hdeg :
        ((4 / 9 * alpha : k) • (C * D) + (2 / 3 * epsilon : k) • D).natDegree =
          C.natDegree + D.natDegree := by
      rw [← hlead]
      refine natDegree_add_eq_left_of_natDegree_lt ?_
      rw [hlead]
      exact hrest
    have hkap0 := hkap
    rw [degreeZeroKappaCubic610_eq_chamber alpha epsilon eta A C D 0,
      kappaChamberCD610_of_E_eq_zero] at hkap0
    rw [hdeg] at hkap0
    omega
  subst halpha0
  have h2c_gt : C.natDegree + 2 * D.natDegree < 2 * C.natDegree := by omega
  have heps0 : epsilon = 0 := by
    by_contra heps
    have hc : (-(1 / 9 * epsilon : k)) ≠ 0 :=
      neg_ne_zero.mpr
        (mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) heps)
    have hlead :
        ((-(1 / 9 * epsilon : k)) • C ^ 2).natDegree = 2 * C.natDegree := by
      rw [natDegree_smul _ hc, natDegree_pow]
    have hrest :
        ((-(5 / 27 : k)) • (C * D ^ 2)).natDegree < 2 * C.natDegree := by
      refine (natDegree_smul_le610 _ _).trans_lt ?_
      have : (C * D ^ 2).natDegree = C.natDegree + 2 * D.natDegree := by
        rw [natDegree_mul hCne (pow_ne_zero 2 hDne), natDegree_pow]
      rw [this]
      exact h2c_gt
    have hdeg :
        ((-(5 / 27 : k)) • (C * D ^ 2) +
            (-(1 / 9 * epsilon : k)) • C ^ 2).natDegree =
          2 * C.natDegree := by
      rw [← hlead]
      refine natDegree_add_eq_right_of_natDegree_lt ?_
      rw [hlead]
      exact hrest
    have hom0 := homi
    rw [degreeZeroOmicronCubic610_eq_chamber 0 epsilon eta A C D 0,
      omicronChamberCD610_of_alpha_eq_zero_E_eq_zero] at hom0
    rw [hdeg] at hom0
    omega
  subst heps0
  have hc : (-(5 / 27 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have homi0 :
      omicronChamberCD610 0 0 eta A C D 0 =
        (-(5 / 27 : k)) • (C * D ^ 2) := by
    rw [omicronChamberCD610_of_alpha_eq_zero_E_eq_zero]
    have hC2 : (-(1 / 9 * (0 : k) : k)) • C ^ 2 = 0 := by
      have hz : (1 / 9 * (0 : k) : k) = 0 := by ring
      rw [hz, neg_zero, zero_smul]
    rw [hC2, add_zero]
  have hdeg :
      ((-(5 / 27 : k)) • (C * D ^ 2)).natDegree =
        C.natDegree + 2 * D.natDegree := by
    rw [natDegree_smul _ hc, natDegree_mul hCne (pow_ne_zero 2 hDne),
      natDegree_pow]
  have hom0 := homi
  rw [degreeZeroOmicronCubic610_eq_chamber 0 0 eta A C D 0, homi0, hdeg] at hom0
  omega

set_option maxHeartbeats 64000000 in
/-- Chamber `E ≠ 0`.  κ's `DE` column kills all but two residual
loci (`α = 0 ∧ e = 0`, and `α ≠ 0 ∧ e = c`), which are finished by
ο and the λ/ο combination at degree `3c`. -/
theorem cubicLoadSigmaCone_CD_chamber_Ene_impossible
    (alpha epsilon eta : k) (A C D E : k[X])
    (hAne : A ≠ 0) (hCne : C ≠ 0) (hDne : D ≠ 0) (hEne : E ≠ 0)
    (hApos : 0 < A.natDegree)
    (hCD : A.natDegree + 2 * D.natDegree = 3 * C.natDegree)
    (hTle : 2 * C.natDegree + D.natDegree ≤ A.natDegree)
    (hEcmp : 2 * E.natDegree < 3 * C.natDegree)
    (hlam : (degreeZeroLambdaCubic610 0 alpha 0 0 epsilon 0 eta 0
          A 0 C D E).natDegree = 0)
    (hkap : (degreeZeroKappaCubic610 0 alpha 0 0 epsilon 0 eta 0
          A 0 C D E).natDegree = 0)
    (homi : (degreeZeroOmicronCubic610 0 alpha 0 0 epsilon 0 eta 0
          A 0 C D E).natDegree = 0) :
    False := by
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hCpos : 0 < C.natDegree := by
    have : ¬ C.natDegree = 0 := by intro hc0; omega
    exact Nat.pos_of_ne_zero this
  have h2c_gt : C.natDegree + 2 * D.natDegree < 2 * C.natDegree := by omega
  -- Easy κ kills: `DE` strictly tops unless `e ≤ c`.
  by_cases hgt : C.natDegree < E.natDegree
  · -- e > c: κ face is DE
    have hc : (10 / 9 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
    have hlead :
        ((10 / 9 : k) • (D * E)).natDegree = D.natDegree + E.natDegree := by
      rw [natDegree_smul _ hc, natDegree_mul hDne hEne]
    have hrestAlpha :
        ((4 / 9 * alpha : k) • (C * D)).natDegree <
          D.natDegree + E.natDegree := by
      refine (natDegree_smul_le610 _ _).trans_lt ?_
      have : (C * D).natDegree = C.natDegree + D.natDegree :=
        natDegree_mul hCne hDne
      rw [this]; omega
    have hrestEps :
        ((2 / 3 * epsilon : k) • D).natDegree <
          D.natDegree + E.natDegree := by
      refine (natDegree_smul_le610 _ _).trans_lt ?_
      omega
    have hkap0 := hkap
    rw [degreeZeroKappaCubic610_eq_chamber alpha epsilon eta A C D E] at hkap0
    simp only [kappaChamberCD610] at hkap0
    have hsum :
        ((10 / 9 : k) • (D * E) + (4 / 9 * alpha : k) • (C * D) +
            (2 / 3 * epsilon : k) • D).natDegree =
          D.natDegree + E.natDegree := by
      have h12 :
          ((10 / 9 : k) • (D * E) + (4 / 9 * alpha : k) • (C * D)).natDegree =
            D.natDegree + E.natDegree := by
        rw [← hlead]
        refine natDegree_add_eq_left_of_natDegree_lt ?_
        rw [hlead]
        exact hrestAlpha
      rw [← h12]
      refine natDegree_add_eq_left_of_natDegree_lt ?_
      rw [h12]
      exact hrestEps
    rw [hsum] at hkap0
    omega
  -- Remaining: e ≤ c.
  have hele : E.natDegree ≤ C.natDegree := Nat.le_of_not_lt hgt
  by_cases halpha : alpha = 0
  · subst halpha
    by_cases he0 : E.natDegree = 0
    · -- α = 0, e = 0: E is a nonzero constant, so C²-terms are a scalar
      -- times C².  If that scalar is nonzero, ο has degree 2c > 0; if it
      -- vanishes, ο reduces to C D² of degree c+2d > 0.
      have hblk := omicronC2Block_of_natDegree_E_eq_zero epsilon C E he0
      have hom0 := homi
      rw [degreeZeroOmicronCubic610_eq_chamber 0 epsilon eta A C D E] at hom0
      have hpoly :
          omicronChamberCD610 0 epsilon eta A C D E =
            ((-(5 / 27 : k)) • (C ^ 2 * E) +
                (-(1 / 9 * epsilon : k)) • C ^ 2) +
              ((-(5 / 27 : k)) • (C * D ^ 2) + (1 / 3 * eta : k) • E) := by
        rw [omicronChamberCD610_of_alpha_eq_zero]
        abel
      rw [hpoly] at hom0
      by_cases hsc0 :
          (-(5 / 27 : k)) * E.leadingCoeff + (-(1 / 9 * epsilon : k)) = 0
      · -- scalar vanished: ο = (-5/27) C D² + (1/3) η E
        have hcancel :
            (-(5 / 27 : k)) • (C ^ 2 * E) +
              (-(1 / 9 * epsilon : k)) • C ^ 2 = 0 := by
          rw [hblk, hsc0, zero_smul]
        rw [hcancel, zero_add] at hom0
        have hc : (-(5 / 27 : k)) ≠ 0 :=
          neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
        have hlead :
            ((-(5 / 27 : k)) • (C * D ^ 2)).natDegree =
              C.natDegree + 2 * D.natDegree := by
          rw [natDegree_smul _ hc, natDegree_mul hCne (pow_ne_zero 2 hDne),
            natDegree_pow]
        have hrest :
            ((1 / 3 * eta : k) • E).natDegree <
              C.natDegree + 2 * D.natDegree := by
          refine (natDegree_smul_le610 _ _).trans_lt ?_
          rw [he0]; omega
        have hdeg :
            ((-(5 / 27 : k)) • (C * D ^ 2) + (1 / 3 * eta : k) • E).natDegree =
              C.natDegree + 2 * D.natDegree := by
          rw [← hlead]
          refine natDegree_add_eq_left_of_natDegree_lt ?_
          rw [hlead]
          exact hrest
        rw [hdeg] at hom0
        omega
      · -- 2c block is the top
        have hc : (-(5 / 27 : k)) * E.leadingCoeff +
            (-(1 / 9 * epsilon : k)) ≠ 0 := hsc0
        have htop :
            ((-(5 / 27 : k)) • (C ^ 2 * E) +
                (-(1 / 9 * epsilon : k)) • C ^ 2).natDegree =
              2 * C.natDegree := by
          rw [hblk, natDegree_smul _ hc, natDegree_pow]
        have hrest :
            ((-(5 / 27 : k)) • (C * D ^ 2) + (1 / 3 * eta : k) • E).natDegree <
              2 * C.natDegree := by
          have h1 : ((-(5 / 27 : k)) • (C * D ^ 2)).natDegree <
              2 * C.natDegree := by
            refine (natDegree_smul_le610 _ _).trans_lt ?_
            have : (C * D ^ 2).natDegree = C.natDegree + 2 * D.natDegree := by
              rw [natDegree_mul hCne (pow_ne_zero 2 hDne), natDegree_pow]
            rw [this]; omega
          have h2 : ((1 / 3 * eta : k) • E).natDegree < 2 * C.natDegree := by
            refine (natDegree_smul_le610 _ _).trans_lt ?_
            rw [he0]; omega
          exact lt_of_le_of_lt (natDegree_add_le _ _) (max_lt h1 h2)
        have hdeg :
            (((-(5 / 27 : k)) • (C ^ 2 * E) +
                (-(1 / 9 * epsilon : k)) • C ^ 2) +
              ((-(5 / 27 : k)) • (C * D ^ 2) + (1 / 3 * eta : k) • E)).natDegree =
              2 * C.natDegree := by
          rw [← htop]
          refine natDegree_add_eq_left_of_natDegree_lt ?_
          rw [htop]
          exact hrest
        rw [hdeg] at hom0
        omega
    · -- α = 0, e > 0: κ face is DE
      have hepos : 0 < E.natDegree := Nat.pos_of_ne_zero he0
      have hc : (10 / 9 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
      have hlead :
          ((10 / 9 : k) • (D * E)).natDegree = D.natDegree + E.natDegree := by
        rw [natDegree_smul _ hc, natDegree_mul hDne hEne]
      have hrestEps :
          ((2 / 3 * epsilon : k) • D).natDegree <
            D.natDegree + E.natDegree := by
        refine (natDegree_smul_le610 _ _).trans_lt ?_
        omega
      have hkap0 := hkap
      rw [degreeZeroKappaCubic610_eq_chamber 0 epsilon eta A C D E] at hkap0
      simp only [kappaChamberCD610, mul_zero, zero_smul, add_zero] at hkap0
      have hdeg :
          ((10 / 9 : k) • (D * E) + (2 / 3 * epsilon : k) • D).natDegree =
            D.natDegree + E.natDegree := by
        rw [← hlead]
        refine natDegree_add_eq_left_of_natDegree_lt ?_
        rw [hlead]
        exact hrestEps
      rw [hdeg] at hkap0
      omega
  · -- α ≠ 0.  If e < c, kappa face is α C D.
    by_cases hlt : E.natDegree < C.natDegree
    · have hc : (4 / 9 * alpha : k) ≠ 0 :=
        mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) halpha
      have hlead :
          ((4 / 9 * alpha : k) • (C * D)).natDegree =
            C.natDegree + D.natDegree := by
        rw [natDegree_smul _ hc, natDegree_mul hCne hDne]
      have hrestDE :
          ((10 / 9 : k) • (D * E)).natDegree <
            C.natDegree + D.natDegree := by
        refine (natDegree_smul_le610 _ _).trans_lt ?_
        have : (D * E).natDegree = D.natDegree + E.natDegree :=
          natDegree_mul hDne hEne
        rw [this]; omega
      have hrestEps :
          ((2 / 3 * epsilon : k) • D).natDegree <
            C.natDegree + D.natDegree := by
        refine (natDegree_smul_le610 _ _).trans_lt ?_
        omega
      have hkap0 := hkap
      rw [degreeZeroKappaCubic610_eq_chamber alpha epsilon eta A C D E] at hkap0
      simp only [kappaChamberCD610] at hkap0
      have h12 :
          ((10 / 9 : k) • (D * E) + (4 / 9 * alpha : k) • (C * D)).natDegree =
            C.natDegree + D.natDegree := by
        rw [← hlead]
        refine natDegree_add_eq_right_of_natDegree_lt ?_
        rw [hlead]
        exact hrestDE
      have hdeg :
          ((10 / 9 : k) • (D * E) + (4 / 9 * alpha : k) • (C * D) +
              (2 / 3 * epsilon : k) • D).natDegree =
            C.natDegree + D.natDegree := by
        rw [← h12]
        refine natDegree_add_eq_left_of_natDegree_lt ?_
        rw [h12]
        exact hrestEps
      rw [hdeg] at hkap0
      omega
    · -- e = c (since e ≤ c and ¬ e < c)
      have heq : E.natDegree = C.natDegree :=
        le_antisymm hele (Nat.le_of_not_lt hlt)
      -- lambda inner 3ad²+c³ = 0, then omicron at 3c with C²E included.
      have hfaceDeg : 0 < A.natDegree + 2 * D.natDegree := by omega
      have hltLam :
          (degreeZeroLambdaCubic610 0 alpha 0 0 epsilon 0 eta 0
              A 0 C D E).natDegree < A.natDegree + 2 * D.natDegree := by
        rw [hlam]
        exact hfaceDeg
      have hzLam : (degreeZeroLambdaCubic610 0 alpha 0 0 epsilon 0 eta 0
            A 0 C D E).coeff (A.natDegree + 2 * D.natDegree) = 0 :=
        coeff_eq_zero_of_natDegree_lt hltLam
      rw [degreeZeroLambdaCubic610_eq_sigmaCD_add_rest, coeff_add] at hzLam
      have hrestLam :
          (degreeZeroLambdaCubicNoSigmaCD610 0 alpha 0 0 epsilon 0 eta 0
              A 0 C D E).natDegree < A.natDegree + 2 * D.natDegree := by
        rw [degreeZeroLambdaCubicNoSigmaCD610_eq_chamberRest]
        simp only [lambdaChamberRestCD610]
        compute_degree
        omega
      rw [coeff_eq_zero_of_natDegree_lt hrestLam, add_zero] at hzLam
      have hinner :
          lambdaCubicSigmaInnerCD610 A.leadingCoeff C.leadingCoeff
            D.leadingCoeff = 0 := by
        have hdeg_AD2 : ((A * D ^ 2)).natDegree =
            A.natDegree + 2 * D.natDegree := by
          rw [natDegree_mul hAne (pow_ne_zero 2 hDne), natDegree_pow]
        have hcf_AD2 : ((A * D ^ 2)).coeff (A.natDegree + 2 * D.natDegree) =
            A.leadingCoeff * D.leadingCoeff ^ 2 := by
          rw [← hdeg_AD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
        have hdeg_C3 : (C ^ 3).natDegree = A.natDegree + 2 * D.natDegree := by
          rw [natDegree_pow]; omega
        have hcf_C3 : (C ^ 3).coeff (A.natDegree + 2 * D.natDegree) =
            C.leadingCoeff ^ 3 := by
          rw [← hdeg_C3, coeff_natDegree, leadingCoeff_pow]
        simp only [lambdaCubicSigmaFaceCD610, lambdaCubicSigmaInnerCD610,
          coeff_add, coeff_sub, coeff_smul, smul_eq_mul] at hzLam
        rw [hcf_AD2, hcf_C3] at hzLam
        have hden : (-(5 / 81 : k)) ≠ 0 :=
          neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
        have : (-(5 / 81 : k)) *
            (3 * A.leadingCoeff * D.leadingCoeff ^ 2 +
              C.leadingCoeff ^ 3) = 0 := by
          convert hzLam using 1
          ring
        rcases mul_eq_zero.mp this with h | h
        · exact (hden h).elim
        · exact h
      -- κ tie: (10/9) D E + (4/9)α C D at c+d
      have hltKap :
          (degreeZeroKappaCubic610 0 alpha 0 0 epsilon 0 eta 0
              A 0 C D E).natDegree < C.natDegree + D.natDegree := by
        rw [hkap]
        omega
      have hzKap : (degreeZeroKappaCubic610 0 alpha 0 0 epsilon 0 eta 0
            A 0 C D E).coeff (C.natDegree + D.natDegree) = 0 :=
        coeff_eq_zero_of_natDegree_lt hltKap
      rw [degreeZeroKappaCubic610_eq_chamber alpha epsilon eta A C D E] at hzKap
      simp only [kappaChamberCD610, coeff_add, coeff_smul, smul_eq_mul] at hzKap
      have hdeg_DE : (D * E).natDegree = C.natDegree + D.natDegree := by
        rw [natDegree_mul hDne hEne, heq, add_comm]
      have hcf_DE : (D * E).coeff (C.natDegree + D.natDegree) =
          D.leadingCoeff * E.leadingCoeff := by
        rw [← hdeg_DE, coeff_natDegree, leadingCoeff_mul]
      have hdeg_CD : (C * D).natDegree = C.natDegree + D.natDegree :=
        natDegree_mul hCne hDne
      have hcf_CD : (C * D).coeff (C.natDegree + D.natDegree) =
          C.leadingCoeff * D.leadingCoeff := by
        rw [← hdeg_CD, coeff_natDegree, leadingCoeff_mul]
      have hmiss_D : D.coeff (C.natDegree + D.natDegree) = 0 := by
        apply coeff_eq_zero_of_natDegree_lt
        omega
      simp only [hcf_DE, hcf_CD, hmiss_D, mul_zero, add_zero] at hzKap
      -- (10/9) D.lc E.lc + (4/9)α C.lc D.lc = 0
      have hrel : E.leadingCoeff =
          -((2 / 5 : k) * alpha * C.leadingCoeff) := by
        have hden : D.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hDne
        have : (10 / 9 : k) * D.leadingCoeff * E.leadingCoeff +
            (4 / 9 * alpha : k) * C.leadingCoeff * D.leadingCoeff = 0 := by
          convert hzKap using 1
          ring
        have hfac :
            D.leadingCoeff *
              ((10 / 9 : k) * E.leadingCoeff +
                (4 / 9 * alpha : k) * C.leadingCoeff) = 0 := by
          convert this using 1
          ring
        have hlin :
            (10 / 9 : k) * E.leadingCoeff +
              (4 / 9 * alpha : k) * C.leadingCoeff = 0 := by
          rcases mul_eq_zero.mp hfac with h | h
          · exact (hden h).elim
          · exact h
        have hadd : E.leadingCoeff +
            ((2 / 5 : k) * alpha * C.leadingCoeff) = 0 := by
          linear_combination (9 / 10 : k) * hlin
        exact eq_neg_of_add_eq_zero_left hadd
      -- ο at 3c = a+2d
      have hzOmi : (degreeZeroOmicronCubic610 0 alpha 0 0 epsilon 0 eta 0
            A 0 C D E).coeff (A.natDegree + 2 * D.natDegree) = 0 :=
        coeff_eq_zero_of_natDegree_lt (by rw [homi]; exact hfaceDeg)
      rw [degreeZeroOmicronCubic610_eq_chamber] at hzOmi
      simp only [omicronChamberCD610, coeff_add, coeff_smul, smul_eq_mul] at hzOmi
      have hdeg_C2E : (C ^ 2 * E).natDegree =
          A.natDegree + 2 * D.natDegree := by
        have hC2 : C ^ 2 ≠ 0 := pow_ne_zero 2 hCne
        rw [natDegree_mul hC2 hEne, natDegree_pow, heq]
        omega
      have hcf_C2E : (C ^ 2 * E).coeff (A.natDegree + 2 * D.natDegree) =
          C.leadingCoeff ^ 2 * E.leadingCoeff := by
        rw [← hdeg_C2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
      have hdeg_AD2 : (A * D ^ 2).natDegree =
          A.natDegree + 2 * D.natDegree := by
        rw [natDegree_mul hAne (pow_ne_zero 2 hDne), natDegree_pow]
      have hcf_AD2 : (A * D ^ 2).coeff (A.natDegree + 2 * D.natDegree) =
          A.leadingCoeff * D.leadingCoeff ^ 2 := by
        rw [← hdeg_AD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
      have hdeg_C3 : (C ^ 3).natDegree = A.natDegree + 2 * D.natDegree := by
        rw [natDegree_pow]; omega
      have hcf_C3 : (C ^ 3).coeff (A.natDegree + 2 * D.natDegree) =
          C.leadingCoeff ^ 3 := by
        rw [← hdeg_C3, coeff_natDegree, leadingCoeff_pow]
      have hmiss_CD2 : (C * D ^ 2).coeff (A.natDegree + 2 * D.natDegree) =
          0 := by
        apply coeff_eq_zero_of_natDegree_lt
        have : (C * D ^ 2).natDegree = C.natDegree + 2 * D.natDegree := by
          rw [natDegree_mul hCne (pow_ne_zero 2 hDne), natDegree_pow]
        rw [this]
        omega
      have hmiss_E2 : (E ^ 2).coeff (A.natDegree + 2 * D.natDegree) = 0 := by
        apply coeff_eq_zero_of_natDegree_lt
        rw [natDegree_pow, heq]
        omega
      have hmiss_C2 : (C ^ 2).coeff (A.natDegree + 2 * D.natDegree) = 0 := by
        apply coeff_eq_zero_of_natDegree_lt
        rw [natDegree_pow]; omega
      have hmiss_E : E.coeff (A.natDegree + 2 * D.natDegree) = 0 := by
        apply coeff_eq_zero_of_natDegree_lt
        rw [heq]; omega
      simp only [hcf_C2E, hcf_AD2, hcf_C3, hmiss_CD2, hmiss_E2, hmiss_C2,
        hmiss_E, mul_zero, add_zero] at hzOmi
      -- ο coeff = (-5/27) c² e + (-2/27 α) a d² + (-4/81 α) c³ = 0
      have hzOmi' :
          (-(5 / 27 : k)) * C.leadingCoeff ^ 2 * E.leadingCoeff
            + (-(2 / 27 * alpha : k)) * A.leadingCoeff * D.leadingCoeff ^ 2
            + (-(4 / 81 * alpha : k)) * C.leadingCoeff ^ 3 = 0 := by
        convert hzOmi using 1
        ring
      have hid := cubicChamber_ec_scalar_identity A.leadingCoeff
          C.leadingCoeff D.leadingCoeff alpha E.leadingCoeff hrel
      have hinner0 : 3 * A.leadingCoeff * D.leadingCoeff ^ 2 +
          C.leadingCoeff ^ 3 = 0 := by
        simpa [lambdaCubicSigmaInnerCD610] using hinner
      have hfin :
          ((4 / 81 : k) * alpha) * C.leadingCoeff ^ 3 = 0 := by
        have := hzOmi'
        rw [hid, hinner0, mul_zero, add_zero] at this
        exact this
      have hden : (4 / 81 : k) ≠ 0 :=
        div_ne_zero (by norm_num) (by norm_num)
      rcases mul_eq_zero.mp hfin with h | h
      · rcases mul_eq_zero.mp h with h | h
        · exact (hden h).elim
        · exact halpha h
      · exact leadingCoeff_ne_zero.mpr hCne
          ((pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp h)

set_option maxHeartbeats 64000000 in
theorem cubicLoadSigmaCone_CD_chamber_impossible {j t : k}
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hl : l = 0)
    (hTle : 2 * C.natDegree + D.natDegree ≤ A.natDegree)
    (hmu : (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta
          theta A B C D E).natDegree = 0)
    (hkap : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree = 0)
    (hlam : (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree = 0)
    (homi : (degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree = 0) :
    False := by
  subst hl
  have hB0 : B = 0 := cubicLoadSigmaConeCD610_B_eq_zero_of_chamber hcone hTle
  subst hB0
  have hbT := cubicLoadSigmaConeCD610_chamber_n1BetaTop hcone hTle rfl
  have hb0 : beta = 0 :=
    cubicN1_beta_eq_zero 0 alpha beta delta epsilon zeta eta theta
      A 0 C D E hbT rfl hmu hkap
  subst hb0
  have hdT := cubicLoadSigmaConeCD610_chamber_n1DeltaTop hcone hTle rfl
  have hd0 : delta = 0 :=
    cubicN1_delta_eq_zero 0 alpha 0 delta epsilon zeta eta theta
      A 0 C D E hdT rfl rfl hmu hkap
  subst hd0
  have hzT := cubicLoadSigmaConeCD610_chamber_n1ZetaTop hcone hTle rfl
  have hz0 : zeta = 0 :=
    cubicN1_zeta_eq_zero 0 alpha 0 0 epsilon zeta eta theta
      A 0 C D E hzT rfl rfl rfl hmu hkap
  subst hz0
  have htT := cubicLoadSigmaConeCD610_chamber_n1ThetaTop hcone hTle rfl
  have ht0 : theta = 0 :=
    cubicN1_theta_eq_zero 0 alpha 0 0 epsilon 0 eta theta
      A 0 C D E htT rfl rfl rfl rfl hmu hkap
  subst ht0
  have hAne := CubicLoadSigmaConeCD610_A_ne hcone
  have hCne : C ≠ 0 := hcone.2.1
  have hDne : D ≠ 0 := hcone.2.2.1
  have hApos : 0 < A.natDegree := hcone.1.1.1
  have hCD : A.natDegree + 2 * D.natDegree = 3 * C.natDegree := by
    rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
      hCne', hDne', heq, hBcmp, hEcmp⟩
    omega
  by_cases hEz : E = 0
  · subst hEz
    exact cubicLoadSigmaCone_CD_chamber_E0_impossible alpha epsilon eta
      A C D hAne hCne hDne hApos hCD hTle hcone.1 hlam hkap homi
  · have hEcmp : 2 * E.natDegree < 3 * C.natDegree := by
      rcases hcone with ⟨_, hCne', hDne', heq, hBcmp, hEcmp⟩
      rcases hEcmp with hE0 | hlt
      · exact (hEz hE0).elim
      · exact hlt
    exact cubicLoadSigmaCone_CD_chamber_Ene_impossible alpha epsilon eta
      A C D E hAne hCne hDne hEz hApos hCD hTle hEcmp hlam hkap homi

end CubicLoadCDChamber610


/-! ## Dispatchers and assembly -/

section CubicLoadWallsAssembly610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
theorem cubicLoadSigmaCone_CD_impossible {j t : k}
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
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
    (hmu : (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta
          theta A B C D E).natDegree = 0)
    (homi : (degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree = 0)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E) =
        Polynomial.C (j / t)) :
    False := by
  by_cases hch : 2 * C.natDegree + D.natDegree ≤ A.natDegree
  · exact cubicLoadSigmaCone_CD_chamber_impossible (j := j) (t := t) l
      alpha beta delta epsilon zeta eta theta A B C D E hcone hl hch
      hmu hkap hlam homi
  · have hTpos : A.natDegree < 2 * C.natDegree + D.natDegree :=
      lt_of_not_ge hch
    have hb := cubicLoadSigmaConeCD610_specialize_beta hcone hb4
    have hd := cubicLoadSigmaConeCD610_specialize_delta hcone hd4
    have hz := cubicLoadSigmaConeCD610_specialize_zeta hcone hz4
    have ht := cubicLoadSigmaConeCD610_specialize_theta hcone ht4
    rcases hb with hb0 | hble
    · rcases hd with hd0 | hdle
      · rcases hz with hz0 | hzle
        · rcases ht with ht0 | htle
          · exact cubicLoadSigmaCone_CD_offWall_impossible l alpha beta
              delta epsilon zeta eta theta A B C D E hcone hl (Or.inl hb0)
              (Or.inl hd0) (Or.inl hz0) (Or.inl ht0) hTpos hmu hkap
          · rcases lt_or_eq_of_le htle with htlt | hteq
            · exact cubicLoadSigmaCone_CD_offWall_impossible l alpha beta
                delta epsilon zeta eta theta A B C D E hcone hl
                (Or.inl hb0) (Or.inl hd0) (Or.inl hz0) (Or.inr htlt)
                hTpos hmu hkap
            · exact cubicLoadSigmaCone_CD_thetaWall_impossible (j := j)
                (t := t) l alpha beta delta epsilon zeta eta theta A B C D E
                hcone hl hteq hmu hkap hjdiv hder
        · rcases lt_or_eq_of_le hzle with hzlt | hzeq
          · rcases ht with ht0 | htle
            · exact cubicLoadSigmaCone_CD_offWall_impossible l alpha beta
                delta epsilon zeta eta theta A B C D E hcone hl
                (Or.inl hb0) (Or.inl hd0) (Or.inr hzlt) (Or.inl ht0)
                hTpos hmu hkap
            · rcases lt_or_eq_of_le htle with htlt | hteq
              · exact cubicLoadSigmaCone_CD_offWall_impossible l alpha beta
                  delta epsilon zeta eta theta A B C D E hcone hl
                  (Or.inl hb0) (Or.inl hd0) (Or.inr hzlt) (Or.inr htlt)
                  hTpos hmu hkap
              · exact cubicLoadSigmaCone_CD_thetaWall_impossible (j := j)
                  (t := t) l alpha beta delta epsilon zeta eta theta
                  A B C D E hcone hl hteq hmu hkap hjdiv hder
          · exact cubicLoadSigmaCone_CD_zetaWall_impossible (j := j)
              (t := t) l alpha beta delta epsilon zeta eta theta A B C D E
              hcone hl hzeq hmu hkap hjdiv hder
      · rcases lt_or_eq_of_le hdle with hdlt | hdeq
        · rcases hz with hz0 | hzle
          · rcases ht with ht0 | htle
            · exact cubicLoadSigmaCone_CD_offWall_impossible l alpha beta
                delta epsilon zeta eta theta A B C D E hcone hl
                (Or.inl hb0) (Or.inr hdlt) (Or.inl hz0) (Or.inl ht0)
                hTpos hmu hkap
            · rcases lt_or_eq_of_le htle with htlt | hteq
              · exact cubicLoadSigmaCone_CD_offWall_impossible l alpha beta
                  delta epsilon zeta eta theta A B C D E hcone hl
                  (Or.inl hb0) (Or.inr hdlt) (Or.inl hz0) (Or.inr htlt)
                  hTpos hmu hkap
              · exact cubicLoadSigmaCone_CD_thetaWall_impossible (j := j)
                  (t := t) l alpha beta delta epsilon zeta eta theta
                  A B C D E hcone hl hteq hmu hkap hjdiv hder
          · rcases lt_or_eq_of_le hzle with hzlt | hzeq
            · rcases ht with ht0 | htle
              · exact cubicLoadSigmaCone_CD_offWall_impossible l alpha beta
                  delta epsilon zeta eta theta A B C D E hcone hl
                  (Or.inl hb0) (Or.inr hdlt) (Or.inr hzlt) (Or.inl ht0)
                  hTpos hmu hkap
              · rcases lt_or_eq_of_le htle with htlt | hteq
                · exact cubicLoadSigmaCone_CD_offWall_impossible l alpha
                    beta delta epsilon zeta eta theta A B C D E hcone hl
                    (Or.inl hb0) (Or.inr hdlt) (Or.inr hzlt) (Or.inr htlt)
                    hTpos hmu hkap
                · exact cubicLoadSigmaCone_CD_thetaWall_impossible (j := j)
                    (t := t) l alpha beta delta epsilon zeta eta theta
                    A B C D E hcone hl hteq hmu hkap hjdiv hder
            · exact cubicLoadSigmaCone_CD_zetaWall_impossible (j := j)
                (t := t) l alpha beta delta epsilon zeta eta theta
                A B C D E hcone hl hzeq hmu hkap hjdiv hder
        · exact cubicLoadSigmaCone_CD_deltaWall_impossible (j := j)
            (t := t) l alpha beta delta epsilon zeta eta theta A B C D E
            hcone hl hdeq hmu hkap hjdiv hder
    · rcases lt_or_eq_of_le hble with hblt | hbeq
      · rcases hd with hd0 | hdle
        · rcases hz with hz0 | hzle
          · rcases ht with ht0 | htle
            · exact cubicLoadSigmaCone_CD_offWall_impossible l alpha beta
                delta epsilon zeta eta theta A B C D E hcone hl
                (Or.inr hblt) (Or.inl hd0) (Or.inl hz0) (Or.inl ht0)
                hTpos hmu hkap
            · rcases lt_or_eq_of_le htle with htlt | hteq
              · exact cubicLoadSigmaCone_CD_offWall_impossible l alpha beta
                  delta epsilon zeta eta theta A B C D E hcone hl
                  (Or.inr hblt) (Or.inl hd0) (Or.inl hz0) (Or.inr htlt)
                  hTpos hmu hkap
              · exact cubicLoadSigmaCone_CD_thetaWall_impossible (j := j)
                  (t := t) l alpha beta delta epsilon zeta eta theta
                  A B C D E hcone hl hteq hmu hkap hjdiv hder
          · rcases lt_or_eq_of_le hzle with hzlt | hzeq
            · rcases ht with ht0 | htle
              · exact cubicLoadSigmaCone_CD_offWall_impossible l alpha beta
                  delta epsilon zeta eta theta A B C D E hcone hl
                  (Or.inr hblt) (Or.inl hd0) (Or.inr hzlt) (Or.inl ht0)
                  hTpos hmu hkap
              · rcases lt_or_eq_of_le htle with htlt | hteq
                · exact cubicLoadSigmaCone_CD_offWall_impossible l alpha
                    beta delta epsilon zeta eta theta A B C D E hcone hl
                    (Or.inr hblt) (Or.inl hd0) (Or.inr hzlt) (Or.inr htlt)
                    hTpos hmu hkap
                · exact cubicLoadSigmaCone_CD_thetaWall_impossible (j := j)
                    (t := t) l alpha beta delta epsilon zeta eta theta
                    A B C D E hcone hl hteq hmu hkap hjdiv hder
            · exact cubicLoadSigmaCone_CD_zetaWall_impossible (j := j)
                (t := t) l alpha beta delta epsilon zeta eta theta
                A B C D E hcone hl hzeq hmu hkap hjdiv hder
        · rcases lt_or_eq_of_le hdle with hdlt | hdeq
          · rcases hz with hz0 | hzle
            · rcases ht with ht0 | htle
              · exact cubicLoadSigmaCone_CD_offWall_impossible l alpha beta
                  delta epsilon zeta eta theta A B C D E hcone hl
                  (Or.inr hblt) (Or.inr hdlt) (Or.inl hz0) (Or.inl ht0)
                  hTpos hmu hkap
              · rcases lt_or_eq_of_le htle with htlt | hteq
                · exact cubicLoadSigmaCone_CD_offWall_impossible l alpha
                    beta delta epsilon zeta eta theta A B C D E hcone hl
                    (Or.inr hblt) (Or.inr hdlt) (Or.inl hz0) (Or.inr htlt)
                    hTpos hmu hkap
                · exact cubicLoadSigmaCone_CD_thetaWall_impossible (j := j)
                    (t := t) l alpha beta delta epsilon zeta eta theta
                    A B C D E hcone hl hteq hmu hkap hjdiv hder
            · rcases lt_or_eq_of_le hzle with hzlt | hzeq
              · rcases ht with ht0 | htle
                · exact cubicLoadSigmaCone_CD_offWall_impossible l alpha
                    beta delta epsilon zeta eta theta A B C D E hcone hl
                    (Or.inr hblt) (Or.inr hdlt) (Or.inr hzlt) (Or.inl ht0)
                    hTpos hmu hkap
                · rcases lt_or_eq_of_le htle with htlt | hteq
                  · exact cubicLoadSigmaCone_CD_offWall_impossible l alpha
                      beta delta epsilon zeta eta theta A B C D E hcone hl
                      (Or.inr hblt) (Or.inr hdlt) (Or.inr hzlt)
                      (Or.inr htlt) hTpos hmu hkap
                  · exact cubicLoadSigmaCone_CD_thetaWall_impossible
                      (j := j) (t := t) l alpha beta delta epsilon zeta
                      eta theta A B C D E hcone hl hteq hmu hkap hjdiv hder
              · exact cubicLoadSigmaCone_CD_zetaWall_impossible (j := j)
                  (t := t) l alpha beta delta epsilon zeta eta theta
                  A B C D E hcone hl hzeq hmu hkap hjdiv hder
          · exact cubicLoadSigmaCone_CD_deltaWall_impossible (j := j)
              (t := t) l alpha beta delta epsilon zeta eta theta A B C D E
              hcone hl hdeq hmu hkap hjdiv hder
      · exact cubicLoadSigmaCone_CD_betaWall_impossible (j := j) (t := t)
          l alpha beta delta epsilon zeta eta theta A B C D E hcone hl
          hbeq hmu hkap hjdiv hder

set_option maxHeartbeats 64000000 in
theorem cubicLoadSigmaCone_BCDE_wall_impossible {j t : k}
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeBCDE610 A B C D E)
    (hl : l = 0)
    (hwall : 7 * (9 * A.natDegree) = 18 * A.natDegree + 42 * B.natDegree ∨
      7 * (9 * A.natDegree) = 30 * A.natDegree + 42 * B.natDegree ∨
      9 * A.natDegree = 6 * A.natDegree + 6 * B.natDegree ∨
      7 * (9 * A.natDegree) = 54 * A.natDegree + 42 * B.natDegree)
    (hlam : (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree = 0)
    (hkap : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree = 0)
    (hmu : (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta
          theta A B C D E).natDegree = 0)
    (homi : (degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree = 0)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E) =
        Polynomial.C (j / t)) :
    False := by
  rcases hwall with hbeq | hdeq | hzeq | hteq
  · exact cubicLoadSigmaCone_BCDE_betaWall_impossible (j := j) (t := t)
      l alpha beta delta epsilon zeta eta theta A B C D E hcone hl hbeq
      hlam hkap hmu homi hjdiv hder
  · exact cubicLoadSigmaCone_BCDE_deltaWall_impossible (j := j) (t := t)
      l alpha beta delta epsilon zeta eta theta A B C D E hcone hl hdeq
      hlam hkap hmu homi hjdiv hder
  · exact cubicLoadSigmaCone_BCDE_zetaWall_impossible (j := j) (t := t)
      l alpha beta delta epsilon zeta eta theta A B C D E hcone hl hzeq
      hlam hkap hmu homi hjdiv hder
  · exact cubicLoadSigmaCone_BCDE_thetaWall_impossible (j := j) (t := t)
      l alpha beta delta epsilon zeta eta theta A B C D E hcone hl hteq
      hlam hkap hmu homi hjdiv hder

end CubicLoadWallsAssembly610

section CubicLoadWallsClosure610

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 64000000 in
theorem normalized610ScaleZero_impossible
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) : False := by
  obtain ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
      zeta, eta, theta, iota, cLam, cKap, cMu, cOmi, A, B, C, D, E, ht,
      hj, hjdiv, hHsq, hder, hlamDeg, hkapDeg, hmuDeg, homiDeg, hconeA,
      hload, hl0, hkapB, hkapD, hkapZ, hbN1, hdN1, hzN1, htN1, hbBand,
      hdBand, hzBand, htBand, hexh⟩ :=
    normalized610ScaleZero_cubicResidual8 hsource
  rcases hexh with hCD | ⟨hBCDE, hwall⟩
  · exact cubicLoadSigmaCone_CD_impossible (j := j) (t := t) l alpha beta
      delta epsilon zeta eta theta A B C D E hCD hl0 hbBand hdBand hzBand
      htBand hlamDeg hkapDeg hmuDeg homiDeg hjdiv hder
  · exact cubicLoadSigmaCone_BCDE_wall_impossible (j := j) (t := t) l
      alpha beta delta epsilon zeta eta theta A B C D E hBCDE hl0 hwall
      hlamDeg hkapDeg hmuDeg homiDeg hjdiv hder

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

theorem proved_planeKellerNormalized610LowScaleRoute :
    PlaneKellerNormalized610LowScaleRoute (K := K) :=
  planeKellerNormalized610LowScaleRoute_of_scaleZero
    (fun _P _Q _H h => normalized610ScaleZero_impossible h)

end CubicLoadWallsClosure610

#print axioms cubicLoadSigmaCone_CD_impossible
#print axioms cubicLoadSigmaCone_BCDE_wall_impossible
#print axioms cubicLoadSigmaCone_CD_chamber_impossible
#print axioms normalized610ScaleZero_impossible
#print axioms proved_planeKellerNormalized610LowScaleRoute

end Max11DegreeRoutes











