import Grok610ScaleZeroCubicBalancedScratch

/-! # Scale-zero cubic wall finish, `(6,10)`, `H = 0`

Continuation of `Grok610ScaleZeroCubicBalancedScratch`.  That file ends at
`normalized610ScaleZero_cubicResidual3`: three chambers remain.

This file promotes `N₂ := Π + (A²/12) κ` (plan §5 / §10 F2).  Its
σ-6 part vanishes, `natDegree N₂ ≤ 2 nA`, and on each leftover wall
the σ-7 face together with the `l A⁷` column makes a 2×2 with `N₁`
whose determinant is the nonzero rational `143/248832`.  That kills
`l` on the wall, after which the off-wall theorems
`cubicSigmaCone_CD_impossible` / `cubicBalancedCell_impossible` apply.

CAS (`scripts/derive_610_scale_zero_cubic_wall.py` and
`scripts/derive_610_scale_zero_cubic_wall_mixed.py`): every nonempty
`(S, letter-face)` and `(S, odd-load mixed)` system saturates to `(1)`
after `l = 0`.  The Lean leftover after the two walls is A-dominant
load-compete with `l = 0`.

No `sorry`, no new axioms, no finite-root shortcut.  Untracked working
note.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false


/-! ## The combination `N₂ = Π + (A²/12) κ` -/

section CubicN2_610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 32000000 in
def degreeZeroN2Cubic610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (-(5 / 81 : k)) • (A ^ 2 * B ^ 2 * D)
  - (25 / 243 : k) • (A * B ^ 3 * C)
  - (4 / 243 : k) • B ^ 5
  + (10 / 27 : k) • (A * B * C * E)
  + (5 / 27 : k) • (A * B * D ^ 2)
  + (5 / 27 : k) • (A * C ^ 2 * D)
  + (10 / 81 : k) • (B ^ 3 * E)
  + (5 / 9 : k) • (B ^ 2 * C * D)
  + (5 / 27 : k) • (B * C ^ 3)
  - (10 / 9 : k) • (C * D * E)
  - (10 / 27 : k) • D ^ 3
  + (11 / 41472 * l : k) • A ^ 7
  + (35 / 6912 * l : k) • (A ^ 5 * C)
  - (23 / 13824 * l : k) • (A ^ 4 * B ^ 2)
  + (5 / 384 * l : k) • (A ^ 4 * E)
  - (1 / 144 * l : k) • (A ^ 3 * B * D)
  + (1 / 36 * l : k) • (A ^ 3 * C ^ 2)
  - (1 / 24 * l : k) • (A ^ 2 * B ^ 2 * C)
  - (1 / 32 * l : k) • (A * B ^ 4)
  + (1 / 8 * l : k) • (A ^ 2 * C * E)
  + (1 / 32 * l : k) • (A ^ 2 * D ^ 2)
  + (1 / 8 * l : k) • (A * B ^ 2 * E)
  + (3 / 8 * l : k) • (A * B * C * D)
  + (1 / 16 * l : k) • (A * C ^ 3)
  + (3 / 16 * l : k) • (B ^ 3 * D)
  + (9 / 32 * l : k) • (B ^ 2 * C ^ 2)
  - (3 / 4 * l : k) • (B * D * E)
  - (3 / 8 * l : k) • (C ^ 2 * E)
  - (3 / 4 * l : k) • (C * D ^ 2)
  - (4 / 243 * alpha : k) • (A ^ 2 * B ^ 3)
  + (4 / 27 * alpha : k) • (A * B ^ 2 * D)
  + (4 / 27 * alpha : k) • (A * B * C ^ 2)
  + (4 / 27 * alpha : k) • (B ^ 3 * C)
  - (4 / 9 * alpha : k) • (A * D * E)
  - (4 / 9 * alpha : k) • (B * C * E)
  - (4 / 9 * alpha : k) • (B * D ^ 2)
  - (4 / 9 * alpha : k) • (C ^ 2 * D)
  + (35 / 41472 * beta : k) • A ^ 6
  + (35 / 2592 * beta : k) • (A ^ 4 * C)
  - (7 / 1296 * beta : k) • (A ^ 3 * B ^ 2)
  + (7 / 216 * beta : k) • (A ^ 3 * E)
  - (7 / 432 * beta : k) • (A ^ 2 * B * D)
  + (49 / 864 * beta : k) • (A ^ 2 * C ^ 2)
  + (35 / 432 * beta : k) • (A * B ^ 2 * C)
  + (35 / 1728 * beta : k) • B ^ 4
  + (7 / 36 * beta : k) • (A * C * E)
  - (7 / 36 * beta : k) • (A * D ^ 2)
  - (7 / 72 * beta : k) • (B ^ 2 * E)
  - (7 / 18 * beta : k) • (B * C * D)
  - (7 / 108 * beta : k) • C ^ 3
  + (7 / 12 * beta : k) • E ^ 2
  + (7 / 2592 * delta : k) • A ^ 5
  + (5 / 144 * delta : k) • (A ^ 3 * C)
  - (25 / 864 * delta : k) • (A ^ 2 * B ^ 2)
  + (5 / 72 * delta : k) • (A ^ 2 * E)
  + (5 / 36 * delta : k) • (A * C ^ 2)
  + (5 / 36 * delta : k) • (B ^ 2 * C)
  - (5 / 12 * delta : k) • D ^ 2
  + (2 / 9 * epsilon : k) • (A * B * C)
  + (2 / 27 * epsilon : k) • B ^ 3
  - (2 / 3 * epsilon : k) • (C * D)
  + (5 / 576 * zeta : k) • A ^ 4
  + (1 / 12 * zeta : k) • (A ^ 2 * C)
  + (1 / 12 * zeta : k) • (A * B ^ 2)
  - (1 / 2 * zeta : k) • (B * D)
  - (1 / 4 * zeta : k) • C ^ 2
  - (1 / 3 * eta : k) • (A * D)
  - (1 / 3 * eta : k) • (B * C)
  + (1 / 36 * theta : k) • A ^ 3
  + (1 / 6 * theta : k) • (A * C)
  - (1 / 12 * theta : k) • B ^ 2
  + (1 * theta : k) • E

set_option maxHeartbeats 128000000 in
theorem degreeZeroN2Cubic610_eq_Pi_add_A2_kappa
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroN2Cubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E =
      degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta eta
          theta A B C D E +
        (1 / 12 : k) • (A ^ 2 * degreeZeroKappaCubic610 l alpha beta
          delta epsilon zeta eta theta A B C D E) := by
  rw [degreeZeroPrimitiveCubic610_eq_flat]
  simp only [degreeZeroN2Cubic610, degreeZeroPrimitiveCubicFlat610,
    degreeZeroKappaCubic610]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring

theorem degreeZeroN2Cubic610_natDegree_le
    {j t : k}
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hApos : 0 < A.natDegree)
    (hkap : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree = 0)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E) =
        Polynomial.C (j / t)) :
    (degreeZeroN2Cubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree ≤
      2 * A.natDegree := by
  rw [degreeZeroN2Cubic610_eq_Pi_add_A2_kappa]
  have hPi :
      (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta eta
          theta A B C D E).natDegree = 1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C610 _ (j / t) hjdiv hder
  have h1 :
      (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta eta
          theta A B C D E).natDegree ≤ 2 * A.natDegree := by
    rw [hPi]
    omega
  have h2 :
      ((1 / 12 : k) • (A ^ 2 * degreeZeroKappaCubic610 l alpha beta
            delta epsilon zeta eta theta A B C D E)).natDegree ≤
        2 * A.natDegree := by
    refine (natDegree_smul_le610 _ _).trans ?_
    have hpow : (A ^ 2).natDegree = 2 * A.natDegree := natDegree_pow _ _
    have hmul :
        (A ^ 2 * degreeZeroKappaCubic610 l alpha beta delta epsilon zeta
              eta theta A B C D E).natDegree ≤
          (A ^ 2).natDegree +
            (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta
                theta A B C D E).natDegree :=
      natDegree_mul_le
    rw [hpow, hkap, add_zero] at hmul
    exact hmul
  exact (natDegree_add_le _ _).trans (max_le h1 h2)

def n2CubicLFace610 (l : k) (A : k[X]) : k[X] :=
  (11 / 41472 * l : k) • A ^ 7

def n2CubicSigmaFaceCD610 (A B C D E : k[X]) : k[X] :=
  (5 / 27 : k) • (A * C ^ 2 * D)

def n2CubicSigmaFaceBCDE610 (A B C D E : k[X]) : k[X] :=
  (-(5 / 81 : k)) • (A ^ 2 * B ^ 2 * D)
  + (10 / 27 : k) • (A * B * C * E)
  + (5 / 27 : k) • (A * C ^ 2 * D)

end CubicN2_610


/-! ## `{C,D}` on the wall `6 nA = 2 nC + nD` via the `N₁`/`N₂` 2×2 -/

section CubicSigmaCDWall610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 32000000 in
def degreeZeroN2CubicNoSigmaCDNoL610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (-(5 / 81 : k)) • (A ^ 2 * B ^ 2 * D)
  - (25 / 243 : k) • (A * B ^ 3 * C)
  - (4 / 243 : k) • B ^ 5
  + (10 / 27 : k) • (A * B * C * E)
  + (5 / 27 : k) • (A * B * D ^ 2)
  + (10 / 81 : k) • (B ^ 3 * E)
  + (5 / 9 : k) • (B ^ 2 * C * D)
  + (5 / 27 : k) • (B * C ^ 3)
  - (10 / 9 : k) • (C * D * E)
  - (10 / 27 : k) • D ^ 3
  + (35 / 6912 * l : k) • (A ^ 5 * C)
  - (23 / 13824 * l : k) • (A ^ 4 * B ^ 2)
  + (5 / 384 * l : k) • (A ^ 4 * E)
  - (1 / 144 * l : k) • (A ^ 3 * B * D)
  + (1 / 36 * l : k) • (A ^ 3 * C ^ 2)
  - (1 / 24 * l : k) • (A ^ 2 * B ^ 2 * C)
  - (1 / 32 * l : k) • (A * B ^ 4)
  + (1 / 8 * l : k) • (A ^ 2 * C * E)
  + (1 / 32 * l : k) • (A ^ 2 * D ^ 2)
  + (1 / 8 * l : k) • (A * B ^ 2 * E)
  + (3 / 8 * l : k) • (A * B * C * D)
  + (1 / 16 * l : k) • (A * C ^ 3)
  + (3 / 16 * l : k) • (B ^ 3 * D)
  + (9 / 32 * l : k) • (B ^ 2 * C ^ 2)
  - (3 / 4 * l : k) • (B * D * E)
  - (3 / 8 * l : k) • (C ^ 2 * E)
  - (3 / 4 * l : k) • (C * D ^ 2)
  - (4 / 243 * alpha : k) • (A ^ 2 * B ^ 3)
  + (4 / 27 * alpha : k) • (A * B ^ 2 * D)
  + (4 / 27 * alpha : k) • (A * B * C ^ 2)
  + (4 / 27 * alpha : k) • (B ^ 3 * C)
  - (4 / 9 * alpha : k) • (A * D * E)
  - (4 / 9 * alpha : k) • (B * C * E)
  - (4 / 9 * alpha : k) • (B * D ^ 2)
  - (4 / 9 * alpha : k) • (C ^ 2 * D)
  + (35 / 41472 * beta : k) • A ^ 6
  + (35 / 2592 * beta : k) • (A ^ 4 * C)
  - (7 / 1296 * beta : k) • (A ^ 3 * B ^ 2)
  + (7 / 216 * beta : k) • (A ^ 3 * E)
  - (7 / 432 * beta : k) • (A ^ 2 * B * D)
  + (49 / 864 * beta : k) • (A ^ 2 * C ^ 2)
  + (35 / 432 * beta : k) • (A * B ^ 2 * C)
  + (35 / 1728 * beta : k) • B ^ 4
  + (7 / 36 * beta : k) • (A * C * E)
  - (7 / 36 * beta : k) • (A * D ^ 2)
  - (7 / 72 * beta : k) • (B ^ 2 * E)
  - (7 / 18 * beta : k) • (B * C * D)
  - (7 / 108 * beta : k) • C ^ 3
  + (7 / 12 * beta : k) • E ^ 2
  + (7 / 2592 * delta : k) • A ^ 5
  + (5 / 144 * delta : k) • (A ^ 3 * C)
  - (25 / 864 * delta : k) • (A ^ 2 * B ^ 2)
  + (5 / 72 * delta : k) • (A ^ 2 * E)
  + (5 / 36 * delta : k) • (A * C ^ 2)
  + (5 / 36 * delta : k) • (B ^ 2 * C)
  - (5 / 12 * delta : k) • D ^ 2
  + (2 / 9 * epsilon : k) • (A * B * C)
  + (2 / 27 * epsilon : k) • B ^ 3
  - (2 / 3 * epsilon : k) • (C * D)
  + (5 / 576 * zeta : k) • A ^ 4
  + (1 / 12 * zeta : k) • (A ^ 2 * C)
  + (1 / 12 * zeta : k) • (A * B ^ 2)
  - (1 / 2 * zeta : k) • (B * D)
  - (1 / 4 * zeta : k) • C ^ 2
  - (1 / 3 * eta : k) • (A * D)
  - (1 / 3 * eta : k) • (B * C)
  + (1 / 36 * theta : k) • A ^ 3
  + (1 / 6 * theta : k) • (A * C)
  - (1 / 12 * theta : k) • B ^ 2
  + (1 * theta : k) • E

set_option maxHeartbeats 32000000 in
theorem degreeZeroN2Cubic610_eq_sigmaCD_L_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroN2Cubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E =
      n2CubicSigmaFaceCD610 A B C D E + n2CubicLFace610 l A +
        degreeZeroN2CubicNoSigmaCDNoL610 l alpha beta delta epsilon zeta
          eta theta A B C D E := by
  simp only [degreeZeroN2Cubic610, n2CubicSigmaFaceCD610, n2CubicLFace610,
    degreeZeroN2CubicNoSigmaCDNoL610]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem degreeZeroN2CubicNoSigmaCDNoL610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicSigmaConeCD610 A B C D E) :
    (degreeZeroN2CubicNoSigmaCDNoL610 l alpha beta delta epsilon zeta
        eta theta A B C D E).natDegree <
      A.natDegree + 2 * C.natDegree + D.natDegree := by
  rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  have hs0 : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt h0
  have hs1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt h1
  have hs2 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt h2
  have hs3 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt h3
  have hs4 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt h4
  have hs5 : 0 + 1 ≤ C.natDegree := Nat.succ_le_of_lt h5
  have hs6 : 0 + 1 ≤ D.natDegree := Nat.succ_le_of_lt h6
  have hs8 : A.natDegree + 2 * B.natDegree + 1 ≤ 2 * C.natDegree :=
    Nat.succ_le_of_lt h8
  have hs9 : 2 * E.natDegree + 1 ≤ 3 * C.natDegree := Nat.succ_le_of_lt h9
  have hs10 : 11 * A.natDegree + 1 ≤ 6 * C.natDegree := Nat.succ_le_of_lt h10
  have hCD : A.natDegree + 2 * D.natDegree = 3 * C.natDegree := by omega
  simp only [degreeZeroN2CubicNoSigmaCDNoL610]
  compute_degree
  omega

theorem n2CubicSigmaFaceCD610_natDegree
    (A B C D E : k[X])
    (hA : A ≠ 0) (hC : C ≠ 0) (hD : D ≠ 0) :
    (n2CubicSigmaFaceCD610 A B C D E).natDegree =
      A.natDegree + 2 * C.natDegree + D.natDegree := by
  have hc : (5 / 27 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hAC2 : A * C ^ 2 ≠ 0 := mul_ne_zero hA (pow_ne_zero 2 hC)
  simp only [n2CubicSigmaFaceCD610]
  rw [natDegree_smul _ hc, natDegree_mul hAC2 hD,
    natDegree_mul hA (pow_ne_zero 2 hC), natDegree_pow]

theorem n2CubicSigmaFaceCD610_coeff_top
    (A B C D E : k[X])
    (hA : A ≠ 0) (hC : C ≠ 0) (hD : D ≠ 0) :
    (n2CubicSigmaFaceCD610 A B C D E).coeff
        (A.natDegree + 2 * C.natDegree + D.natDegree) =
      (5 / 27 : k) * A.leadingCoeff * C.leadingCoeff ^ 2 *
        D.leadingCoeff := by
  simp only [n2CubicSigmaFaceCD610, coeff_smul, smul_eq_mul]
  have hAC2 : A * C ^ 2 ≠ 0 := mul_ne_zero hA (pow_ne_zero 2 hC)
  have hdeg : (A * C ^ 2 * D).natDegree =
      A.natDegree + 2 * C.natDegree + D.natDegree := by
    rw [natDegree_mul hAC2 hD, natDegree_mul hA (pow_ne_zero 2 hC),
      natDegree_pow]
  rw [← hdeg, coeff_natDegree, leadingCoeff_mul,
    leadingCoeff_mul, leadingCoeff_pow]
  ring

theorem n2CubicLFace610_coeff_top
    (l : k) (A : k[X])
    (hl : l ≠ 0) (hA : A ≠ 0) :
    (n2CubicLFace610 l A).coeff (7 * A.natDegree) =
      (11 / 41472 * l : k) * A.leadingCoeff ^ 7 := by
  have hc : (11 / 41472 * l : k) ≠ 0 :=
    mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hl
  simp only [n2CubicLFace610, coeff_smul, smul_eq_mul]
  have hdeg : (A ^ 7).natDegree = 7 * A.natDegree := natDegree_pow _ _
  rw [← hdeg, coeff_natDegree, leadingCoeff_pow]

set_option maxHeartbeats 32000000 in
theorem cubicSigmaCone_CD_wall_impossible
    {j t : k}
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicSigmaConeCD610 A B C D E)
    (hwall : 6 * A.natDegree = 2 * C.natDegree + D.natDegree)
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
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    omega
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    omega
  have hApos : 0 < A.natDegree := hcone.1
  have hN1le := degreeZeroN1Cubic610_natDegree_le l alpha beta delta
      epsilon zeta eta theta A B C D E hmu hkap
  have hN2le := degreeZeroN2Cubic610_natDegree_le (j := j) (t := t) l
      alpha beta delta epsilon zeta eta theta A B C D E hApos hkap hjdiv hder
  have hT1 : A.natDegree < 6 * A.natDegree := by
    rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    omega
  have hT2 : 2 * A.natDegree < 7 * A.natDegree := by
    rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    omega
  have hdeg1 : 6 * A.natDegree = 2 * C.natDegree + D.natDegree := hwall
  have hdeg2 : 7 * A.natDegree =
      A.natDegree + 2 * C.natDegree + D.natDegree := by omega
  have hz1 : (degreeZeroN1Cubic610 l alpha beta delta epsilon zeta eta
        theta A B C D E).coeff (6 * A.natDegree) = 0 :=
    coeff_eq_zero_of_natDegree_lt (hN1le.trans_lt hT1)
  have hz2 : (degreeZeroN2Cubic610 l alpha beta delta epsilon zeta eta
        theta A B C D E).coeff (7 * A.natDegree) = 0 :=
    coeff_eq_zero_of_natDegree_lt (hN2le.trans_lt hT2)
  have hN1rest :=
    degreeZeroN1CubicNoSigmaCDNoL610_natDegree_lt l alpha beta delta
      epsilon zeta eta theta A B C D E hcone
  have hN2rest :=
    degreeZeroN2CubicNoSigmaCDNoL610_natDegree_lt l alpha beta delta
      epsilon zeta eta theta A B C D E hcone
  rw [degreeZeroN1Cubic610_eq_sigmaCD_add_rest,
    degreeZeroN1CubicNoSigmaCD610_eq_L_add_rest, coeff_add, coeff_add] at hz1
  have hN1small :
      (degreeZeroN1CubicNoSigmaCDNoL610 l alpha beta delta epsilon zeta
          eta theta A B C D E).coeff (6 * A.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    exact hdeg1 ▸ hN1rest
  rw [hN1small, add_zero] at hz1
  rw [degreeZeroN2Cubic610_eq_sigmaCD_L_add_rest, coeff_add, coeff_add] at hz2
  have hN2small :
      (degreeZeroN2CubicNoSigmaCDNoL610 l alpha beta delta epsilon zeta
          eta theta A B C D E).coeff (7 * A.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    exact hdeg2 ▸ hN2rest
  rw [hN2small, add_zero] at hz2
  have hN1face := n1CubicSigmaFaceCD610_coeff_top A B C D E hCne hDne
  have hN2face := n2CubicSigmaFaceCD610_coeff_top A B C D E hAne hCne hDne
  have hN1L : (n1CubicLFace610 l A).coeff (6 * A.natDegree) =
      (77 / 248832 * l : k) * A.leadingCoeff ^ 6 := by
    simp only [n1CubicLFace610, coeff_smul, smul_eq_mul]
    have hAk : (A ^ 6).natDegree = 6 * A.natDegree := natDegree_pow _ _
    rw [← hAk, coeff_natDegree, leadingCoeff_pow]
  have hN2L : (n2CubicLFace610 l A).coeff (7 * A.natDegree) =
      (11 / 41472 * l : k) * A.leadingCoeff ^ 7 := by
    simp only [n2CubicLFace610, coeff_smul, smul_eq_mul]
    have hAk : (A ^ 7).natDegree = 7 * A.natDegree := natDegree_pow _ _
    rw [← hAk, coeff_natDegree, leadingCoeff_pow]
  rw [← hdeg1] at hN1face
  rw [hN1face, hN1L] at hz1
  rw [← hdeg2] at hN2face
  rw [hN2face, hN2L] at hz2
  have hcomb :
      A.leadingCoeff *
          ((-(5 / 27 : k)) * C.leadingCoeff ^ 2 * D.leadingCoeff +
            (77 / 248832 * l : k) * A.leadingCoeff ^ 6) +
        ((5 / 27 : k) * A.leadingCoeff * C.leadingCoeff ^ 2 *
            D.leadingCoeff +
          (11 / 41472 * l : k) * A.leadingCoeff ^ 7) = 0 := by
    rw [hz1, mul_zero, hz2, add_zero]
  have hlin : (143 / 248832 * l : k) * A.leadingCoeff ^ 7 = 0 := by
    convert hcomb using 1
    ring
  have hden : (143 / 248832 : k) ≠ 0 :=
    div_ne_zero (by norm_num) (by norm_num)
  have ha7 : A.leadingCoeff ^ 7 ≠ 0 :=
    pow_ne_zero _ (leadingCoeff_ne_zero.mpr hAne)
  have hl0 : l = 0 := by
    rcases mul_eq_zero.mp hlin with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact (hden h).elim
      · exact h
    · exact (ha7 h).elim
  exact cubicSigmaCone_CD_impossible l alpha beta delta epsilon zeta
    eta theta A B C D E hcone hmu hkap (Or.inl hl0)

theorem cubicSigmaCone_CD_impossible_all
    {j t : k}
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicSigmaConeCD610 A B C D E)
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
  by_cases hwall : 6 * A.natDegree = 2 * C.natDegree + D.natDegree
  · exact cubicSigmaCone_CD_wall_impossible (j := j) (t := t) l alpha
      beta delta epsilon zeta eta theta A B C D E hcone hwall hmu hkap
      hjdiv hder
  · exact cubicSigmaCone_CD_impossible l alpha beta delta epsilon zeta
      eta theta A B C D E hcone hmu hkap (Or.inr hwall)

end CubicSigmaCDWall610


/-! ## Balanced cell on the wall `14 nB = 19 nA` via the `N₁`/`N₂` 2×2 -/

section CubicBalancedWall610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 32000000 in
def degreeZeroN2CubicNoSigmaBCDENoL610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (-(25 / 243 : k)) • (A * B ^ 3 * C)
  - (4 / 243 : k) • B ^ 5
  + (5 / 27 : k) • (A * B * D ^ 2)
  + (10 / 81 : k) • (B ^ 3 * E)
  + (5 / 9 : k) • (B ^ 2 * C * D)
  + (5 / 27 : k) • (B * C ^ 3)
  - (10 / 9 : k) • (C * D * E)
  - (10 / 27 : k) • D ^ 3
  + (35 / 6912 * l : k) • (A ^ 5 * C)
  - (23 / 13824 * l : k) • (A ^ 4 * B ^ 2)
  + (5 / 384 * l : k) • (A ^ 4 * E)
  - (1 / 144 * l : k) • (A ^ 3 * B * D)
  + (1 / 36 * l : k) • (A ^ 3 * C ^ 2)
  - (1 / 24 * l : k) • (A ^ 2 * B ^ 2 * C)
  - (1 / 32 * l : k) • (A * B ^ 4)
  + (1 / 8 * l : k) • (A ^ 2 * C * E)
  + (1 / 32 * l : k) • (A ^ 2 * D ^ 2)
  + (1 / 8 * l : k) • (A * B ^ 2 * E)
  + (3 / 8 * l : k) • (A * B * C * D)
  + (1 / 16 * l : k) • (A * C ^ 3)
  + (3 / 16 * l : k) • (B ^ 3 * D)
  + (9 / 32 * l : k) • (B ^ 2 * C ^ 2)
  - (3 / 4 * l : k) • (B * D * E)
  - (3 / 8 * l : k) • (C ^ 2 * E)
  - (3 / 4 * l : k) • (C * D ^ 2)
  - (4 / 243 * alpha : k) • (A ^ 2 * B ^ 3)
  + (4 / 27 * alpha : k) • (A * B ^ 2 * D)
  + (4 / 27 * alpha : k) • (A * B * C ^ 2)
  + (4 / 27 * alpha : k) • (B ^ 3 * C)
  - (4 / 9 * alpha : k) • (A * D * E)
  - (4 / 9 * alpha : k) • (B * C * E)
  - (4 / 9 * alpha : k) • (B * D ^ 2)
  - (4 / 9 * alpha : k) • (C ^ 2 * D)
  + (35 / 41472 * beta : k) • A ^ 6
  + (35 / 2592 * beta : k) • (A ^ 4 * C)
  - (7 / 1296 * beta : k) • (A ^ 3 * B ^ 2)
  + (7 / 216 * beta : k) • (A ^ 3 * E)
  - (7 / 432 * beta : k) • (A ^ 2 * B * D)
  + (49 / 864 * beta : k) • (A ^ 2 * C ^ 2)
  + (35 / 432 * beta : k) • (A * B ^ 2 * C)
  + (35 / 1728 * beta : k) • B ^ 4
  + (7 / 36 * beta : k) • (A * C * E)
  - (7 / 36 * beta : k) • (A * D ^ 2)
  - (7 / 72 * beta : k) • (B ^ 2 * E)
  - (7 / 18 * beta : k) • (B * C * D)
  - (7 / 108 * beta : k) • C ^ 3
  + (7 / 12 * beta : k) • E ^ 2
  + (7 / 2592 * delta : k) • A ^ 5
  + (5 / 144 * delta : k) • (A ^ 3 * C)
  - (25 / 864 * delta : k) • (A ^ 2 * B ^ 2)
  + (5 / 72 * delta : k) • (A ^ 2 * E)
  + (5 / 36 * delta : k) • (A * C ^ 2)
  + (5 / 36 * delta : k) • (B ^ 2 * C)
  - (5 / 12 * delta : k) • D ^ 2
  + (2 / 9 * epsilon : k) • (A * B * C)
  + (2 / 27 * epsilon : k) • B ^ 3
  - (2 / 3 * epsilon : k) • (C * D)
  + (5 / 576 * zeta : k) • A ^ 4
  + (1 / 12 * zeta : k) • (A ^ 2 * C)
  + (1 / 12 * zeta : k) • (A * B ^ 2)
  - (1 / 2 * zeta : k) • (B * D)
  - (1 / 4 * zeta : k) • C ^ 2
  - (1 / 3 * eta : k) • (A * D)
  - (1 / 3 * eta : k) • (B * C)
  + (1 / 36 * theta : k) • A ^ 3
  + (1 / 6 * theta : k) • (A * C)
  - (1 / 12 * theta : k) • B ^ 2
  + (1 * theta : k) • E

set_option maxHeartbeats 32000000 in
theorem degreeZeroN2Cubic610_eq_sigmaBCDE_L_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroN2Cubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E =
      n2CubicSigmaFaceBCDE610 A B C D E + n2CubicLFace610 l A +
        degreeZeroN2CubicNoSigmaBCDENoL610 l alpha beta delta epsilon
          zeta eta theta A B C D E := by
  simp only [degreeZeroN2Cubic610, n2CubicSigmaFaceBCDE610,
    n2CubicLFace610, degreeZeroN2CubicNoSigmaBCDENoL610]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem degreeZeroN2CubicNoSigmaBCDENoL610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicSigmaConeBCDE610 A B C D E) :
    (degreeZeroN2CubicNoSigmaBCDENoL610 l alpha beta delta epsilon zeta
        eta theta A B C D E).natDegree <
      2 * A.natDegree + 2 * B.natDegree + D.natDegree := by
  rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
  have hs0 : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt h0
  have hs1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt h1
  have hs2 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt h2
  have hs3 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt h3
  have hs4 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt h4
  have hs5 : 0 + 1 ≤ B.natDegree := Nat.succ_le_of_lt h5
  have hs6 : 0 + 1 ≤ C.natDegree := Nat.succ_le_of_lt h6
  have hs7 : 0 + 1 ≤ D.natDegree := Nat.succ_le_of_lt h7
  have hs8 : 0 + 1 ≤ E.natDegree := Nat.succ_le_of_lt h8
  have hs12 : 4 * A.natDegree + 1 ≤ 3 * B.natDegree := Nat.succ_le_of_lt h12
  have eqC : 2 * C.natDegree = A.natDegree + 2 * B.natDegree := by omega
  have eqD : 4 * D.natDegree = A.natDegree + 6 * B.natDegree := by omega
  have eqE : 4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree := by omega
  simp only [degreeZeroN2CubicNoSigmaBCDENoL610]
  compute_degree
  omega

theorem n2CubicSigmaFaceBCDE610_coeff_top
    {A B C D E : k[X]}
    (hcone : CubicSigmaConeBCDE610 A B C D E)
    (hAne : A ≠ 0) (hBne : B ≠ 0) (hCne : C ≠ 0) (hDne : D ≠ 0)
    (hEne : E ≠ 0) :
    (n2CubicSigmaFaceBCDE610 A B C D E).coeff
        (2 * A.natDegree + 2 * B.natDegree + D.natDegree) =
      (-(5 / 81 : k)) *
        n1CubicSigmaInnerBCDE610 A.leadingCoeff B.leadingCoeff
          C.leadingCoeff D.leadingCoeff E.leadingCoeff *
        A.leadingCoeff := by
  rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
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

set_option maxHeartbeats 32000000 in
theorem cubicBalancedCell_wall_impossible
    {j t : k}
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicSigmaConeBCDE610 A B C D E)
    (hwall : 14 * B.natDegree = 19 * A.natDegree)
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
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
    omega
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
    omega
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
    omega
  have hApos : 0 < A.natDegree := hcone.1
  have hN1le := degreeZeroN1Cubic610_natDegree_le l alpha beta delta
      epsilon zeta eta theta A B C D E hmu hkap
  have hN2le := degreeZeroN2Cubic610_natDegree_le (j := j) (t := t) l
      alpha beta delta epsilon zeta eta theta A B C D E hApos hkap hjdiv hder
  have hT1 : A.natDegree < 6 * A.natDegree := by
    rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
    omega
  have hT2 : 2 * A.natDegree < 7 * A.natDegree := by
    rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
    omega
  have hdeg1 : 6 * A.natDegree =
      A.natDegree + 2 * B.natDegree + D.natDegree := by
    rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
    omega
  have hdeg2 : 7 * A.natDegree =
      2 * A.natDegree + 2 * B.natDegree + D.natDegree := by omega
  have hz1 : (degreeZeroN1Cubic610 l alpha beta delta epsilon zeta eta
        theta A B C D E).coeff (6 * A.natDegree) = 0 :=
    coeff_eq_zero_of_natDegree_lt (hN1le.trans_lt hT1)
  have hz2 : (degreeZeroN2Cubic610 l alpha beta delta epsilon zeta eta
        theta A B C D E).coeff (7 * A.natDegree) = 0 :=
    coeff_eq_zero_of_natDegree_lt (hN2le.trans_lt hT2)
  have hN1rest :=
    degreeZeroN1CubicNoSigmaBCDENoL610_natDegree_lt l alpha beta delta
      epsilon zeta eta theta A B C D E hcone
  have hN2rest :=
    degreeZeroN2CubicNoSigmaBCDENoL610_natDegree_lt l alpha beta delta
      epsilon zeta eta theta A B C D E hcone
  rw [degreeZeroN1Cubic610_eq_sigmaBCDE_add_rest,
    degreeZeroN1CubicNoSigmaBCDE610_eq_L_add_rest, coeff_add, coeff_add]
    at hz1
  have hN1small :
      (degreeZeroN1CubicNoSigmaBCDENoL610 l alpha beta delta epsilon
          zeta eta theta A B C D E).coeff (6 * A.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    exact hdeg1 ▸ hN1rest
  rw [hN1small, add_zero] at hz1
  rw [degreeZeroN2Cubic610_eq_sigmaBCDE_L_add_rest, coeff_add, coeff_add]
    at hz2
  have hN2small :
      (degreeZeroN2CubicNoSigmaBCDENoL610 l alpha beta delta epsilon
          zeta eta theta A B C D E).coeff (7 * A.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    exact hdeg2 ▸ hN2rest
  rw [hN2small, add_zero] at hz2
  have hN1face := n1CubicSigmaFaceBCDE610_coeff_top (hcone := hcone)
      (hAne := hAne) (hBne := hBne) (hCne := hCne) (hDne := hDne)
      (hEne := hEne)
  have hN2face := n2CubicSigmaFaceBCDE610_coeff_top (hcone := hcone)
      (hAne := hAne) (hBne := hBne) (hCne := hCne) (hDne := hDne)
      (hEne := hEne)
  have hN1L : (n1CubicLFace610 l A).coeff (6 * A.natDegree) =
      (77 / 248832 * l : k) * A.leadingCoeff ^ 6 := by
    simp only [n1CubicLFace610, coeff_smul, smul_eq_mul]
    have hAk : (A ^ 6).natDegree = 6 * A.natDegree := natDegree_pow _ _
    rw [← hAk, coeff_natDegree, leadingCoeff_pow]
  have hN2L : (n2CubicLFace610 l A).coeff (7 * A.natDegree) =
      (11 / 41472 * l : k) * A.leadingCoeff ^ 7 := by
    simp only [n2CubicLFace610, coeff_smul, smul_eq_mul]
    have hAk : (A ^ 7).natDegree = 7 * A.natDegree := natDegree_pow _ _
    rw [← hAk, coeff_natDegree, leadingCoeff_pow]
  rw [← hdeg1] at hN1face
  rw [hN1face, hN1L] at hz1
  rw [← hdeg2] at hN2face
  rw [hN2face, hN2L] at hz2
  -- N1: (5/81) inner + (77/248832) l a^6 = 0
  -- N2: -(5/81) inner * a + (11/41472) l a^7 = 0
  have hcomb :
      A.leadingCoeff *
          ((5 / 81 : k) * n1CubicSigmaInnerBCDE610 A.leadingCoeff
              B.leadingCoeff C.leadingCoeff D.leadingCoeff
              E.leadingCoeff +
            (77 / 248832 * l : k) * A.leadingCoeff ^ 6) +
        ((-(5 / 81 : k)) * n1CubicSigmaInnerBCDE610 A.leadingCoeff
            B.leadingCoeff C.leadingCoeff D.leadingCoeff
            E.leadingCoeff * A.leadingCoeff +
          (11 / 41472 * l : k) * A.leadingCoeff ^ 7) = 0 := by
    rw [hz1, mul_zero, hz2, add_zero]
  have hlin : (143 / 248832 * l : k) * A.leadingCoeff ^ 7 = 0 := by
    convert hcomb using 1
    ring
  have hden : (143 / 248832 : k) ≠ 0 :=
    div_ne_zero (by norm_num) (by norm_num)
  have ha7 : A.leadingCoeff ^ 7 ≠ 0 :=
    pow_ne_zero _ (leadingCoeff_ne_zero.mpr hAne)
  have hl0 : l = 0 := by
    rcases mul_eq_zero.mp hlin with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact (hden h).elim
      · exact h
    · exact (ha7 h).elim
  exact cubicBalancedCell_impossible l alpha beta delta epsilon zeta
    eta theta A B C D E hcone hlam hkap hmu homi (Or.inl hl0)

theorem cubicBalancedCell_impossible_all
    {j t : k}
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicSigmaConeBCDE610 A B C D E)
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
  by_cases hwall : 14 * B.natDegree = 19 * A.natDegree
  · exact cubicBalancedCell_wall_impossible (j := j) (t := t) l alpha
      beta delta epsilon zeta eta theta A B C D E hcone hwall hlam hkap
      hmu homi hjdiv hder
  · exact cubicBalancedCell_impossible l alpha beta delta epsilon zeta
      eta theta A B C D E hcone hlam hkap hmu homi (Or.inr hwall)

end CubicBalancedWall610


/-! ## Exhaustiveness inside `R = {A}` -/

section CubicSigmaExhaust610

variable {k : Type*} [Field k] [CharZero k]

inductive CubicSigmaSupportCone610 (A B C D E : k[X]) : Prop
  | sigmaB : CubicSigmaConeB610 A B C D E → CubicSigmaSupportCone610 A B C D E
  | sigmaC : CubicSigmaConeC610 A B C D E → CubicSigmaSupportCone610 A B C D E
  | sigmaD : CubicSigmaConeD610 A B C D E → CubicSigmaSupportCone610 A B C D E
  | sigmaE : CubicSigmaConeE610 A B C D E → CubicSigmaSupportCone610 A B C D E
  | sigmaBC : CubicSigmaConeBC610 A B C D E → CubicSigmaSupportCone610 A B C D E
  | sigmaBD : CubicSigmaConeBD610 A B C D E → CubicSigmaSupportCone610 A B C D E
  | sigmaBE : CubicSigmaConeBE610 A B C D E → CubicSigmaSupportCone610 A B C D E
  | sigmaCD : CubicSigmaConeCD610 A B C D E → CubicSigmaSupportCone610 A B C D E
  | sigmaCE : CubicSigmaConeCE610 A B C D E → CubicSigmaSupportCone610 A B C D E
  | sigmaDE : CubicSigmaConeDE610 A B C D E → CubicSigmaSupportCone610 A B C D E
  | sigmaBCD : CubicSigmaConeBCD610 A B C D E → CubicSigmaSupportCone610 A B C D E
  | sigmaBCE : CubicSigmaConeBCE610 A B C D E → CubicSigmaSupportCone610 A B C D E
  | sigmaBDE : CubicSigmaConeBDE610 A B C D E → CubicSigmaSupportCone610 A B C D E
  | sigmaCDE : CubicSigmaConeCDE610 A B C D E → CubicSigmaSupportCone610 A B C D E
  | sigmaBCDE : CubicSigmaConeBCDE610 A B C D E → CubicSigmaSupportCone610 A B C D E
  | allZero : B = 0 ∧ C = 0 ∧ D = 0 ∧ E = 0 → CubicSigmaSupportCone610 A B C D E
  | loadCompete : cubicLoadCompetes610 A B C D E → CubicSigmaSupportCone610 A B C D E

set_option maxHeartbeats 64000000 in
theorem cubicSigmaSupportCone610_of
    (A B C D E : k[X])
    (hA : CubicRatioConeA610 A B C D E) :
    CubicSigmaSupportCone610 A B C D E := by
  rcases hA with ⟨hApos, hAB, hAC, hAD, hAE⟩
  by_cases hBz : B = 0
  · -- B vanishes
    have hBdeg0 : B.natDegree = 0 := by simp [hBz]
    by_cases hCz : C = 0
    · -- C vanishes
      have hCdeg0 : C.natDegree = 0 := by simp [hCz]
      by_cases hDz : D = 0
      · -- D vanishes
        have hDdeg0 : D.natDegree = 0 := by simp [hDz]
        by_cases hEz : E = 0
        · -- E vanishes
          have hEdeg0 : E.natDegree = 0 := by simp [hEz]
          exact CubicSigmaSupportCone610.allZero ⟨hBz, hCz, hDz, hEz⟩
        · -- E lives
          by_cases hpos : 0 < E.natDegree
          · by_cases hload : 11 * A.natDegree < 4 * E.natDegree
            ·
              have hEpos : 0 < E.natDegree := by omega
              refine CubicSigmaSupportCone610.sigmaE ?_
              refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
            · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
          · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
      · -- D lives
        by_cases hEz : E = 0
        · -- E vanishes
          have hEdeg0 : E.natDegree = 0 := by simp [hEz]
          by_cases hpos : 0 < D.natDegree
          · by_cases hload : 9 * A.natDegree < 4 * D.natDegree
            ·
              have hDpos : 0 < D.natDegree := by omega
              refine CubicSigmaSupportCone610.sigmaD ?_
              refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
            · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
          · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
        · -- E lives
          by_cases hlt : 2 * E.natDegree < A.natDegree + 2 * D.natDegree
          · -- D strictly outranks E (smaller τ)
            by_cases hpos : 0 < D.natDegree
            · by_cases hload : 9 * A.natDegree < 4 * D.natDegree
              ·
                have hDpos : 0 < D.natDegree := by omega
                refine CubicSigmaSupportCone610.sigmaD ?_
                refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
              · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
            · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
          · by_cases heq : 2 * E.natDegree = A.natDegree + 2 * D.natDegree
            · -- E ties D
              by_cases hpos : 0 < D.natDegree
              · by_cases hload : 9 * A.natDegree < 4 * D.natDegree
                ·
                  have hDpos : 0 < D.natDegree := by omega
                  have hEpos : 0 < E.natDegree := by omega
                  refine CubicSigmaSupportCone610.sigmaDE ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
              · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
            · -- E strictly outranks D
              by_cases hpos : 0 < E.natDegree
              · by_cases hload : 11 * A.natDegree < 4 * E.natDegree
                ·
                  have hEpos : 0 < E.natDegree := by omega
                  refine CubicSigmaSupportCone610.sigmaE ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
              · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
    · -- C lives
      by_cases hDz : D = 0
      · -- D vanishes
        have hDdeg0 : D.natDegree = 0 := by simp [hDz]
        by_cases hEz : E = 0
        · -- E vanishes
          have hEdeg0 : E.natDegree = 0 := by simp [hEz]
          by_cases hpos : 0 < C.natDegree
          · by_cases hload : 11 * A.natDegree < 6 * C.natDegree
            ·
              have hCpos : 0 < C.natDegree := by omega
              refine CubicSigmaSupportCone610.sigmaC ?_
              refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
            · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
          · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
        · -- E lives
          by_cases hlt : 2 * E.natDegree < 3 * C.natDegree
          · -- C strictly outranks E (smaller τ)
            by_cases hpos : 0 < C.natDegree
            · by_cases hload : 11 * A.natDegree < 6 * C.natDegree
              ·
                have hCpos : 0 < C.natDegree := by omega
                refine CubicSigmaSupportCone610.sigmaC ?_
                refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
              · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
            · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
          · by_cases heq : 2 * E.natDegree = 3 * C.natDegree
            · -- E ties C
              by_cases hpos : 0 < C.natDegree
              · by_cases hload : 11 * A.natDegree < 6 * C.natDegree
                ·
                  have hCpos : 0 < C.natDegree := by omega
                  have hEpos : 0 < E.natDegree := by omega
                  refine CubicSigmaSupportCone610.sigmaCE ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
              · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
            · -- E strictly outranks C
              by_cases hpos : 0 < E.natDegree
              · by_cases hload : 11 * A.natDegree < 4 * E.natDegree
                ·
                  have hEpos : 0 < E.natDegree := by omega
                  refine CubicSigmaSupportCone610.sigmaE ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
              · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
      · -- D lives
        by_cases hEz : E = 0
        · -- E vanishes
          have hEdeg0 : E.natDegree = 0 := by simp [hEz]
          by_cases hlt : A.natDegree + 2 * D.natDegree < 3 * C.natDegree
          · -- C strictly outranks D (smaller τ)
            by_cases hpos : 0 < C.natDegree
            · by_cases hload : 11 * A.natDegree < 6 * C.natDegree
              ·
                have hCpos : 0 < C.natDegree := by omega
                refine CubicSigmaSupportCone610.sigmaC ?_
                refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
              · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
            · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
          · by_cases heq : A.natDegree + 2 * D.natDegree = 3 * C.natDegree
            · -- D ties C
              by_cases hpos : 0 < C.natDegree
              · by_cases hload : 11 * A.natDegree < 6 * C.natDegree
                ·
                  have hCpos : 0 < C.natDegree := by omega
                  have hDpos : 0 < D.natDegree := by omega
                  refine CubicSigmaSupportCone610.sigmaCD ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
              · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
            · -- D strictly outranks C
              by_cases hpos : 0 < D.natDegree
              · by_cases hload : 9 * A.natDegree < 4 * D.natDegree
                ·
                  have hDpos : 0 < D.natDegree := by omega
                  refine CubicSigmaSupportCone610.sigmaD ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
              · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
        · -- E lives
          by_cases hlt : A.natDegree + 2 * D.natDegree < 3 * C.natDegree
          · -- C strictly outranks D (smaller τ)
            by_cases hlt : 2 * E.natDegree < 3 * C.natDegree
            · -- C strictly outranks E (smaller τ)
              by_cases hpos : 0 < C.natDegree
              · by_cases hload : 11 * A.natDegree < 6 * C.natDegree
                ·
                  have hCpos : 0 < C.natDegree := by omega
                  refine CubicSigmaSupportCone610.sigmaC ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
              · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
            · by_cases heq : 2 * E.natDegree = 3 * C.natDegree
              · -- E ties C
                by_cases hpos : 0 < C.natDegree
                · by_cases hload : 11 * A.natDegree < 6 * C.natDegree
                  ·
                    have hCpos : 0 < C.natDegree := by omega
                    have hEpos : 0 < E.natDegree := by omega
                    refine CubicSigmaSupportCone610.sigmaCE ?_
                    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                  · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
              · -- E strictly outranks C
                by_cases hpos : 0 < E.natDegree
                · by_cases hload : 11 * A.natDegree < 4 * E.natDegree
                  ·
                    have hEpos : 0 < E.natDegree := by omega
                    refine CubicSigmaSupportCone610.sigmaE ?_
                    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                  · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
          · by_cases heq : A.natDegree + 2 * D.natDegree = 3 * C.natDegree
            · -- D ties C
              by_cases hlt : 2 * E.natDegree < 3 * C.natDegree
              · -- C strictly outranks E (smaller τ)
                by_cases hpos : 0 < C.natDegree
                · by_cases hload : 11 * A.natDegree < 6 * C.natDegree
                  ·
                    have hCpos : 0 < C.natDegree := by omega
                    have hDpos : 0 < D.natDegree := by omega
                    refine CubicSigmaSupportCone610.sigmaCD ?_
                    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                  · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
              · by_cases heq : 2 * E.natDegree = 3 * C.natDegree
                · -- E ties CD
                  by_cases hpos : 0 < C.natDegree
                  · by_cases hload : 11 * A.natDegree < 6 * C.natDegree
                    ·
                      have hCpos : 0 < C.natDegree := by omega
                      have hDpos : 0 < D.natDegree := by omega
                      have hEpos : 0 < E.natDegree := by omega
                      refine CubicSigmaSupportCone610.sigmaCDE ?_
                      refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                    · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                  · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                · -- E strictly outranks CD
                  by_cases hpos : 0 < E.natDegree
                  · by_cases hload : 11 * A.natDegree < 4 * E.natDegree
                    ·
                      have hEpos : 0 < E.natDegree := by omega
                      refine CubicSigmaSupportCone610.sigmaE ?_
                      refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                    · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                  · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
            · -- D strictly outranks C
              by_cases hlt : 2 * E.natDegree < A.natDegree + 2 * D.natDegree
              · -- D strictly outranks E (smaller τ)
                by_cases hpos : 0 < D.natDegree
                · by_cases hload : 9 * A.natDegree < 4 * D.natDegree
                  ·
                    have hDpos : 0 < D.natDegree := by omega
                    refine CubicSigmaSupportCone610.sigmaD ?_
                    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                  · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
              · by_cases heq : 2 * E.natDegree = A.natDegree + 2 * D.natDegree
                · -- E ties D
                  by_cases hpos : 0 < D.natDegree
                  · by_cases hload : 9 * A.natDegree < 4 * D.natDegree
                    ·
                      have hDpos : 0 < D.natDegree := by omega
                      have hEpos : 0 < E.natDegree := by omega
                      refine CubicSigmaSupportCone610.sigmaDE ?_
                      refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                    · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                  · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                · -- E strictly outranks D
                  by_cases hpos : 0 < E.natDegree
                  · by_cases hload : 11 * A.natDegree < 4 * E.natDegree
                    ·
                      have hEpos : 0 < E.natDegree := by omega
                      refine CubicSigmaSupportCone610.sigmaE ?_
                      refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                    · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                  · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
  · -- B lives
    by_cases hCz : C = 0
    · -- C vanishes
      have hCdeg0 : C.natDegree = 0 := by simp [hCz]
      by_cases hDz : D = 0
      · -- D vanishes
        have hDdeg0 : D.natDegree = 0 := by simp [hDz]
        by_cases hEz : E = 0
        · -- E vanishes
          have hEdeg0 : E.natDegree = 0 := by simp [hEz]
          by_cases hpos : 0 < B.natDegree
          · by_cases hload : 4 * A.natDegree < 3 * B.natDegree
            ·
              have hBpos : 0 < B.natDegree := by omega
              refine CubicSigmaSupportCone610.sigmaB ?_
              refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
            · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
          · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
        · -- E lives
          by_cases hlt : 4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree
          · -- B strictly outranks E (smaller τ)
            by_cases hpos : 0 < B.natDegree
            · by_cases hload : 4 * A.natDegree < 3 * B.natDegree
              ·
                have hBpos : 0 < B.natDegree := by omega
                refine CubicSigmaSupportCone610.sigmaB ?_
                refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
              · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
            · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
          · by_cases heq : 4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree
            · -- E ties B
              by_cases hpos : 0 < B.natDegree
              · by_cases hload : 4 * A.natDegree < 3 * B.natDegree
                ·
                  have hBpos : 0 < B.natDegree := by omega
                  have hEpos : 0 < E.natDegree := by omega
                  refine CubicSigmaSupportCone610.sigmaBE ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
              · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
            · -- E strictly outranks B
              by_cases hpos : 0 < E.natDegree
              · by_cases hload : 11 * A.natDegree < 4 * E.natDegree
                ·
                  have hEpos : 0 < E.natDegree := by omega
                  refine CubicSigmaSupportCone610.sigmaE ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
              · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
      · -- D lives
        by_cases hEz : E = 0
        · -- E vanishes
          have hEdeg0 : E.natDegree = 0 := by simp [hEz]
          by_cases hlt : 4 * D.natDegree < A.natDegree + 6 * B.natDegree
          · -- B strictly outranks D (smaller τ)
            by_cases hpos : 0 < B.natDegree
            · by_cases hload : 4 * A.natDegree < 3 * B.natDegree
              ·
                have hBpos : 0 < B.natDegree := by omega
                refine CubicSigmaSupportCone610.sigmaB ?_
                refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
              · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
            · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
          · by_cases heq : 4 * D.natDegree = A.natDegree + 6 * B.natDegree
            · -- D ties B
              by_cases hpos : 0 < B.natDegree
              · by_cases hload : 4 * A.natDegree < 3 * B.natDegree
                ·
                  have hBpos : 0 < B.natDegree := by omega
                  have hDpos : 0 < D.natDegree := by omega
                  refine CubicSigmaSupportCone610.sigmaBD ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
              · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
            · -- D strictly outranks B
              by_cases hpos : 0 < D.natDegree
              · by_cases hload : 9 * A.natDegree < 4 * D.natDegree
                ·
                  have hDpos : 0 < D.natDegree := by omega
                  refine CubicSigmaSupportCone610.sigmaD ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
              · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
        · -- E lives
          by_cases hlt : 4 * D.natDegree < A.natDegree + 6 * B.natDegree
          · -- B strictly outranks D (smaller τ)
            by_cases hlt : 4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree
            · -- B strictly outranks E (smaller τ)
              by_cases hpos : 0 < B.natDegree
              · by_cases hload : 4 * A.natDegree < 3 * B.natDegree
                ·
                  have hBpos : 0 < B.natDegree := by omega
                  refine CubicSigmaSupportCone610.sigmaB ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
              · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
            · by_cases heq : 4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree
              · -- E ties B
                by_cases hpos : 0 < B.natDegree
                · by_cases hload : 4 * A.natDegree < 3 * B.natDegree
                  ·
                    have hBpos : 0 < B.natDegree := by omega
                    have hEpos : 0 < E.natDegree := by omega
                    refine CubicSigmaSupportCone610.sigmaBE ?_
                    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                  · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
              · -- E strictly outranks B
                by_cases hpos : 0 < E.natDegree
                · by_cases hload : 11 * A.natDegree < 4 * E.natDegree
                  ·
                    have hEpos : 0 < E.natDegree := by omega
                    refine CubicSigmaSupportCone610.sigmaE ?_
                    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                  · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
          · by_cases heq : 4 * D.natDegree = A.natDegree + 6 * B.natDegree
            · -- D ties B
              by_cases hlt : 4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree
              · -- B strictly outranks E (smaller τ)
                by_cases hpos : 0 < B.natDegree
                · by_cases hload : 4 * A.natDegree < 3 * B.natDegree
                  ·
                    have hBpos : 0 < B.natDegree := by omega
                    have hDpos : 0 < D.natDegree := by omega
                    refine CubicSigmaSupportCone610.sigmaBD ?_
                    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                  · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
              · by_cases heq : 4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree
                · -- E ties BD
                  by_cases hpos : 0 < B.natDegree
                  · by_cases hload : 4 * A.natDegree < 3 * B.natDegree
                    ·
                      have hBpos : 0 < B.natDegree := by omega
                      have hDpos : 0 < D.natDegree := by omega
                      have hEpos : 0 < E.natDegree := by omega
                      refine CubicSigmaSupportCone610.sigmaBDE ?_
                      refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                    · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                  · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                · -- E strictly outranks BD
                  by_cases hpos : 0 < E.natDegree
                  · by_cases hload : 11 * A.natDegree < 4 * E.natDegree
                    ·
                      have hEpos : 0 < E.natDegree := by omega
                      refine CubicSigmaSupportCone610.sigmaE ?_
                      refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                    · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                  · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
            · -- D strictly outranks B
              by_cases hlt : 2 * E.natDegree < A.natDegree + 2 * D.natDegree
              · -- D strictly outranks E (smaller τ)
                by_cases hpos : 0 < D.natDegree
                · by_cases hload : 9 * A.natDegree < 4 * D.natDegree
                  ·
                    have hDpos : 0 < D.natDegree := by omega
                    refine CubicSigmaSupportCone610.sigmaD ?_
                    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                  · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
              · by_cases heq : 2 * E.natDegree = A.natDegree + 2 * D.natDegree
                · -- E ties D
                  by_cases hpos : 0 < D.natDegree
                  · by_cases hload : 9 * A.natDegree < 4 * D.natDegree
                    ·
                      have hDpos : 0 < D.natDegree := by omega
                      have hEpos : 0 < E.natDegree := by omega
                      refine CubicSigmaSupportCone610.sigmaDE ?_
                      refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                    · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                  · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                · -- E strictly outranks D
                  by_cases hpos : 0 < E.natDegree
                  · by_cases hload : 11 * A.natDegree < 4 * E.natDegree
                    ·
                      have hEpos : 0 < E.natDegree := by omega
                      refine CubicSigmaSupportCone610.sigmaE ?_
                      refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                    · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                  · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
    · -- C lives
      by_cases hDz : D = 0
      · -- D vanishes
        have hDdeg0 : D.natDegree = 0 := by simp [hDz]
        by_cases hEz : E = 0
        · -- E vanishes
          have hEdeg0 : E.natDegree = 0 := by simp [hEz]
          by_cases hlt : 2 * C.natDegree < A.natDegree + 2 * B.natDegree
          · -- B strictly outranks C (smaller τ)
            by_cases hpos : 0 < B.natDegree
            · by_cases hload : 4 * A.natDegree < 3 * B.natDegree
              ·
                have hBpos : 0 < B.natDegree := by omega
                refine CubicSigmaSupportCone610.sigmaB ?_
                refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
              · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
            · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
          · by_cases heq : 2 * C.natDegree = A.natDegree + 2 * B.natDegree
            · -- C ties B
              by_cases hpos : 0 < B.natDegree
              · by_cases hload : 4 * A.natDegree < 3 * B.natDegree
                ·
                  have hBpos : 0 < B.natDegree := by omega
                  have hCpos : 0 < C.natDegree := by omega
                  refine CubicSigmaSupportCone610.sigmaBC ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
              · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
            · -- C strictly outranks B
              by_cases hpos : 0 < C.natDegree
              · by_cases hload : 11 * A.natDegree < 6 * C.natDegree
                ·
                  have hCpos : 0 < C.natDegree := by omega
                  refine CubicSigmaSupportCone610.sigmaC ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
              · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
        · -- E lives
          by_cases hlt : 2 * C.natDegree < A.natDegree + 2 * B.natDegree
          · -- B strictly outranks C (smaller τ)
            by_cases hlt : 4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree
            · -- B strictly outranks E (smaller τ)
              by_cases hpos : 0 < B.natDegree
              · by_cases hload : 4 * A.natDegree < 3 * B.natDegree
                ·
                  have hBpos : 0 < B.natDegree := by omega
                  refine CubicSigmaSupportCone610.sigmaB ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
              · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
            · by_cases heq : 4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree
              · -- E ties B
                by_cases hpos : 0 < B.natDegree
                · by_cases hload : 4 * A.natDegree < 3 * B.natDegree
                  ·
                    have hBpos : 0 < B.natDegree := by omega
                    have hEpos : 0 < E.natDegree := by omega
                    refine CubicSigmaSupportCone610.sigmaBE ?_
                    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                  · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
              · -- E strictly outranks B
                by_cases hpos : 0 < E.natDegree
                · by_cases hload : 11 * A.natDegree < 4 * E.natDegree
                  ·
                    have hEpos : 0 < E.natDegree := by omega
                    refine CubicSigmaSupportCone610.sigmaE ?_
                    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                  · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
          · by_cases heq : 2 * C.natDegree = A.natDegree + 2 * B.natDegree
            · -- C ties B
              by_cases hlt : 4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree
              · -- B strictly outranks E (smaller τ)
                by_cases hpos : 0 < B.natDegree
                · by_cases hload : 4 * A.natDegree < 3 * B.natDegree
                  ·
                    have hBpos : 0 < B.natDegree := by omega
                    have hCpos : 0 < C.natDegree := by omega
                    refine CubicSigmaSupportCone610.sigmaBC ?_
                    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                  · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
              · by_cases heq : 4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree
                · -- E ties BC
                  by_cases hpos : 0 < B.natDegree
                  · by_cases hload : 4 * A.natDegree < 3 * B.natDegree
                    ·
                      have hBpos : 0 < B.natDegree := by omega
                      have hCpos : 0 < C.natDegree := by omega
                      have hEpos : 0 < E.natDegree := by omega
                      refine CubicSigmaSupportCone610.sigmaBCE ?_
                      refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                    · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                  · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                · -- E strictly outranks BC
                  by_cases hpos : 0 < E.natDegree
                  · by_cases hload : 11 * A.natDegree < 4 * E.natDegree
                    ·
                      have hEpos : 0 < E.natDegree := by omega
                      refine CubicSigmaSupportCone610.sigmaE ?_
                      refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                    · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                  · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
            · -- C strictly outranks B
              by_cases hlt : 2 * E.natDegree < 3 * C.natDegree
              · -- C strictly outranks E (smaller τ)
                by_cases hpos : 0 < C.natDegree
                · by_cases hload : 11 * A.natDegree < 6 * C.natDegree
                  ·
                    have hCpos : 0 < C.natDegree := by omega
                    refine CubicSigmaSupportCone610.sigmaC ?_
                    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                  · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
              · by_cases heq : 2 * E.natDegree = 3 * C.natDegree
                · -- E ties C
                  by_cases hpos : 0 < C.natDegree
                  · by_cases hload : 11 * A.natDegree < 6 * C.natDegree
                    ·
                      have hCpos : 0 < C.natDegree := by omega
                      have hEpos : 0 < E.natDegree := by omega
                      refine CubicSigmaSupportCone610.sigmaCE ?_
                      refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                    · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                  · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                · -- E strictly outranks C
                  by_cases hpos : 0 < E.natDegree
                  · by_cases hload : 11 * A.natDegree < 4 * E.natDegree
                    ·
                      have hEpos : 0 < E.natDegree := by omega
                      refine CubicSigmaSupportCone610.sigmaE ?_
                      refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                    · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                  · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
      · -- D lives
        by_cases hEz : E = 0
        · -- E vanishes
          have hEdeg0 : E.natDegree = 0 := by simp [hEz]
          by_cases hlt : 2 * C.natDegree < A.natDegree + 2 * B.natDegree
          · -- B strictly outranks C (smaller τ)
            by_cases hlt : 4 * D.natDegree < A.natDegree + 6 * B.natDegree
            · -- B strictly outranks D (smaller τ)
              by_cases hpos : 0 < B.natDegree
              · by_cases hload : 4 * A.natDegree < 3 * B.natDegree
                ·
                  have hBpos : 0 < B.natDegree := by omega
                  refine CubicSigmaSupportCone610.sigmaB ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
              · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
            · by_cases heq : 4 * D.natDegree = A.natDegree + 6 * B.natDegree
              · -- D ties B
                by_cases hpos : 0 < B.natDegree
                · by_cases hload : 4 * A.natDegree < 3 * B.natDegree
                  ·
                    have hBpos : 0 < B.natDegree := by omega
                    have hDpos : 0 < D.natDegree := by omega
                    refine CubicSigmaSupportCone610.sigmaBD ?_
                    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                  · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
              · -- D strictly outranks B
                by_cases hpos : 0 < D.natDegree
                · by_cases hload : 9 * A.natDegree < 4 * D.natDegree
                  ·
                    have hDpos : 0 < D.natDegree := by omega
                    refine CubicSigmaSupportCone610.sigmaD ?_
                    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                  · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
          · by_cases heq : 2 * C.natDegree = A.natDegree + 2 * B.natDegree
            · -- C ties B
              by_cases hlt : 4 * D.natDegree < A.natDegree + 6 * B.natDegree
              · -- B strictly outranks D (smaller τ)
                by_cases hpos : 0 < B.natDegree
                · by_cases hload : 4 * A.natDegree < 3 * B.natDegree
                  ·
                    have hBpos : 0 < B.natDegree := by omega
                    have hCpos : 0 < C.natDegree := by omega
                    refine CubicSigmaSupportCone610.sigmaBC ?_
                    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                  · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
              · by_cases heq : 4 * D.natDegree = A.natDegree + 6 * B.natDegree
                · -- D ties BC
                  by_cases hpos : 0 < B.natDegree
                  · by_cases hload : 4 * A.natDegree < 3 * B.natDegree
                    ·
                      have hBpos : 0 < B.natDegree := by omega
                      have hCpos : 0 < C.natDegree := by omega
                      have hDpos : 0 < D.natDegree := by omega
                      refine CubicSigmaSupportCone610.sigmaBCD ?_
                      refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                    · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                  · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                · -- D strictly outranks BC
                  by_cases hpos : 0 < D.natDegree
                  · by_cases hload : 9 * A.natDegree < 4 * D.natDegree
                    ·
                      have hDpos : 0 < D.natDegree := by omega
                      refine CubicSigmaSupportCone610.sigmaD ?_
                      refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                    · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                  · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
            · -- C strictly outranks B
              by_cases hlt : A.natDegree + 2 * D.natDegree < 3 * C.natDegree
              · -- C strictly outranks D (smaller τ)
                by_cases hpos : 0 < C.natDegree
                · by_cases hload : 11 * A.natDegree < 6 * C.natDegree
                  ·
                    have hCpos : 0 < C.natDegree := by omega
                    refine CubicSigmaSupportCone610.sigmaC ?_
                    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                  · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
              · by_cases heq : A.natDegree + 2 * D.natDegree = 3 * C.natDegree
                · -- D ties C
                  by_cases hpos : 0 < C.natDegree
                  · by_cases hload : 11 * A.natDegree < 6 * C.natDegree
                    ·
                      have hCpos : 0 < C.natDegree := by omega
                      have hDpos : 0 < D.natDegree := by omega
                      refine CubicSigmaSupportCone610.sigmaCD ?_
                      refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                    · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                  · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                · -- D strictly outranks C
                  by_cases hpos : 0 < D.natDegree
                  · by_cases hload : 9 * A.natDegree < 4 * D.natDegree
                    ·
                      have hDpos : 0 < D.natDegree := by omega
                      refine CubicSigmaSupportCone610.sigmaD ?_
                      refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                    · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                  · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
        · -- E lives
          by_cases hlt : 2 * C.natDegree < A.natDegree + 2 * B.natDegree
          · -- B strictly outranks C (smaller τ)
            by_cases hlt : 4 * D.natDegree < A.natDegree + 6 * B.natDegree
            · -- B strictly outranks D (smaller τ)
              by_cases hlt : 4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree
              · -- B strictly outranks E (smaller τ)
                by_cases hpos : 0 < B.natDegree
                · by_cases hload : 4 * A.natDegree < 3 * B.natDegree
                  ·
                    have hBpos : 0 < B.natDegree := by omega
                    refine CubicSigmaSupportCone610.sigmaB ?_
                    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                  · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
              · by_cases heq : 4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree
                · -- E ties B
                  by_cases hpos : 0 < B.natDegree
                  · by_cases hload : 4 * A.natDegree < 3 * B.natDegree
                    ·
                      have hBpos : 0 < B.natDegree := by omega
                      have hEpos : 0 < E.natDegree := by omega
                      refine CubicSigmaSupportCone610.sigmaBE ?_
                      refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                    · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                  · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                · -- E strictly outranks B
                  by_cases hpos : 0 < E.natDegree
                  · by_cases hload : 11 * A.natDegree < 4 * E.natDegree
                    ·
                      have hEpos : 0 < E.natDegree := by omega
                      refine CubicSigmaSupportCone610.sigmaE ?_
                      refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                    · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                  · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
            · by_cases heq : 4 * D.natDegree = A.natDegree + 6 * B.natDegree
              · -- D ties B
                by_cases hlt : 4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree
                · -- B strictly outranks E (smaller τ)
                  by_cases hpos : 0 < B.natDegree
                  · by_cases hload : 4 * A.natDegree < 3 * B.natDegree
                    ·
                      have hBpos : 0 < B.natDegree := by omega
                      have hDpos : 0 < D.natDegree := by omega
                      refine CubicSigmaSupportCone610.sigmaBD ?_
                      refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                    · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                  · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                · by_cases heq : 4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree
                  · -- E ties BD
                    by_cases hpos : 0 < B.natDegree
                    · by_cases hload : 4 * A.natDegree < 3 * B.natDegree
                      ·
                        have hBpos : 0 < B.natDegree := by omega
                        have hDpos : 0 < D.natDegree := by omega
                        have hEpos : 0 < E.natDegree := by omega
                        refine CubicSigmaSupportCone610.sigmaBDE ?_
                        refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                      · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                    · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                  · -- E strictly outranks BD
                    by_cases hpos : 0 < E.natDegree
                    · by_cases hload : 11 * A.natDegree < 4 * E.natDegree
                      ·
                        have hEpos : 0 < E.natDegree := by omega
                        refine CubicSigmaSupportCone610.sigmaE ?_
                        refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                      · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                    · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
              · -- D strictly outranks B
                by_cases hlt : 2 * E.natDegree < A.natDegree + 2 * D.natDegree
                · -- D strictly outranks E (smaller τ)
                  by_cases hpos : 0 < D.natDegree
                  · by_cases hload : 9 * A.natDegree < 4 * D.natDegree
                    ·
                      have hDpos : 0 < D.natDegree := by omega
                      refine CubicSigmaSupportCone610.sigmaD ?_
                      refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                    · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                  · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                · by_cases heq : 2 * E.natDegree = A.natDegree + 2 * D.natDegree
                  · -- E ties D
                    by_cases hpos : 0 < D.natDegree
                    · by_cases hload : 9 * A.natDegree < 4 * D.natDegree
                      ·
                        have hDpos : 0 < D.natDegree := by omega
                        have hEpos : 0 < E.natDegree := by omega
                        refine CubicSigmaSupportCone610.sigmaDE ?_
                        refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                      · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                    · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                  · -- E strictly outranks D
                    by_cases hpos : 0 < E.natDegree
                    · by_cases hload : 11 * A.natDegree < 4 * E.natDegree
                      ·
                        have hEpos : 0 < E.natDegree := by omega
                        refine CubicSigmaSupportCone610.sigmaE ?_
                        refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                      · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                    · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
          · by_cases heq : 2 * C.natDegree = A.natDegree + 2 * B.natDegree
            · -- C ties B
              by_cases hlt : 4 * D.natDegree < A.natDegree + 6 * B.natDegree
              · -- B strictly outranks D (smaller τ)
                by_cases hlt : 4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree
                · -- B strictly outranks E (smaller τ)
                  by_cases hpos : 0 < B.natDegree
                  · by_cases hload : 4 * A.natDegree < 3 * B.natDegree
                    ·
                      have hBpos : 0 < B.natDegree := by omega
                      have hCpos : 0 < C.natDegree := by omega
                      refine CubicSigmaSupportCone610.sigmaBC ?_
                      refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                    · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                  · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                · by_cases heq : 4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree
                  · -- E ties BC
                    by_cases hpos : 0 < B.natDegree
                    · by_cases hload : 4 * A.natDegree < 3 * B.natDegree
                      ·
                        have hBpos : 0 < B.natDegree := by omega
                        have hCpos : 0 < C.natDegree := by omega
                        have hEpos : 0 < E.natDegree := by omega
                        refine CubicSigmaSupportCone610.sigmaBCE ?_
                        refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                      · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                    · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                  · -- E strictly outranks BC
                    by_cases hpos : 0 < E.natDegree
                    · by_cases hload : 11 * A.natDegree < 4 * E.natDegree
                      ·
                        have hEpos : 0 < E.natDegree := by omega
                        refine CubicSigmaSupportCone610.sigmaE ?_
                        refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                      · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                    · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
              · by_cases heq : 4 * D.natDegree = A.natDegree + 6 * B.natDegree
                · -- D ties BC
                  by_cases hlt : 4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree
                  · -- B strictly outranks E (smaller τ)
                    by_cases hpos : 0 < B.natDegree
                    · by_cases hload : 4 * A.natDegree < 3 * B.natDegree
                      ·
                        have hBpos : 0 < B.natDegree := by omega
                        have hCpos : 0 < C.natDegree := by omega
                        have hDpos : 0 < D.natDegree := by omega
                        refine CubicSigmaSupportCone610.sigmaBCD ?_
                        refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                      · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                    · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                  · by_cases heq : 4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree
                    · -- E ties BCD
                      by_cases hpos : 0 < B.natDegree
                      · by_cases hload : 4 * A.natDegree < 3 * B.natDegree
                        ·
                          have hBpos : 0 < B.natDegree := by omega
                          have hCpos : 0 < C.natDegree := by omega
                          have hDpos : 0 < D.natDegree := by omega
                          have hEpos : 0 < E.natDegree := by omega
                          refine CubicSigmaSupportCone610.sigmaBCDE ?_
                          refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                        · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                      · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                    · -- E strictly outranks BCD
                      by_cases hpos : 0 < E.natDegree
                      · by_cases hload : 11 * A.natDegree < 4 * E.natDegree
                        ·
                          have hEpos : 0 < E.natDegree := by omega
                          refine CubicSigmaSupportCone610.sigmaE ?_
                          refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                        · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                      · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                · -- D strictly outranks BC
                  by_cases hlt : 2 * E.natDegree < A.natDegree + 2 * D.natDegree
                  · -- D strictly outranks E (smaller τ)
                    by_cases hpos : 0 < D.natDegree
                    · by_cases hload : 9 * A.natDegree < 4 * D.natDegree
                      ·
                        have hDpos : 0 < D.natDegree := by omega
                        refine CubicSigmaSupportCone610.sigmaD ?_
                        refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                      · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                    · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                  · by_cases heq : 2 * E.natDegree = A.natDegree + 2 * D.natDegree
                    · -- E ties D
                      by_cases hpos : 0 < D.natDegree
                      · by_cases hload : 9 * A.natDegree < 4 * D.natDegree
                        ·
                          have hDpos : 0 < D.natDegree := by omega
                          have hEpos : 0 < E.natDegree := by omega
                          refine CubicSigmaSupportCone610.sigmaDE ?_
                          refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                        · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                      · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                    · -- E strictly outranks D
                      by_cases hpos : 0 < E.natDegree
                      · by_cases hload : 11 * A.natDegree < 4 * E.natDegree
                        ·
                          have hEpos : 0 < E.natDegree := by omega
                          refine CubicSigmaSupportCone610.sigmaE ?_
                          refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                        · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                      · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
            · -- C strictly outranks B
              by_cases hlt : A.natDegree + 2 * D.natDegree < 3 * C.natDegree
              · -- C strictly outranks D (smaller τ)
                by_cases hlt : 2 * E.natDegree < 3 * C.natDegree
                · -- C strictly outranks E (smaller τ)
                  by_cases hpos : 0 < C.natDegree
                  · by_cases hload : 11 * A.natDegree < 6 * C.natDegree
                    ·
                      have hCpos : 0 < C.natDegree := by omega
                      refine CubicSigmaSupportCone610.sigmaC ?_
                      refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                    · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                  · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                · by_cases heq : 2 * E.natDegree = 3 * C.natDegree
                  · -- E ties C
                    by_cases hpos : 0 < C.natDegree
                    · by_cases hload : 11 * A.natDegree < 6 * C.natDegree
                      ·
                        have hCpos : 0 < C.natDegree := by omega
                        have hEpos : 0 < E.natDegree := by omega
                        refine CubicSigmaSupportCone610.sigmaCE ?_
                        refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                      · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                    · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                  · -- E strictly outranks C
                    by_cases hpos : 0 < E.natDegree
                    · by_cases hload : 11 * A.natDegree < 4 * E.natDegree
                      ·
                        have hEpos : 0 < E.natDegree := by omega
                        refine CubicSigmaSupportCone610.sigmaE ?_
                        refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                      · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                    · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
              · by_cases heq : A.natDegree + 2 * D.natDegree = 3 * C.natDegree
                · -- D ties C
                  by_cases hlt : 2 * E.natDegree < 3 * C.natDegree
                  · -- C strictly outranks E (smaller τ)
                    by_cases hpos : 0 < C.natDegree
                    · by_cases hload : 11 * A.natDegree < 6 * C.natDegree
                      ·
                        have hCpos : 0 < C.natDegree := by omega
                        have hDpos : 0 < D.natDegree := by omega
                        refine CubicSigmaSupportCone610.sigmaCD ?_
                        refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                      · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                    · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                  · by_cases heq : 2 * E.natDegree = 3 * C.natDegree
                    · -- E ties CD
                      by_cases hpos : 0 < C.natDegree
                      · by_cases hload : 11 * A.natDegree < 6 * C.natDegree
                        ·
                          have hCpos : 0 < C.natDegree := by omega
                          have hDpos : 0 < D.natDegree := by omega
                          have hEpos : 0 < E.natDegree := by omega
                          refine CubicSigmaSupportCone610.sigmaCDE ?_
                          refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                        · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                      · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                    · -- E strictly outranks CD
                      by_cases hpos : 0 < E.natDegree
                      · by_cases hload : 11 * A.natDegree < 4 * E.natDegree
                        ·
                          have hEpos : 0 < E.natDegree := by omega
                          refine CubicSigmaSupportCone610.sigmaE ?_
                          refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                        · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                      · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                · -- D strictly outranks C
                  by_cases hlt : 2 * E.natDegree < A.natDegree + 2 * D.natDegree
                  · -- D strictly outranks E (smaller τ)
                    by_cases hpos : 0 < D.natDegree
                    · by_cases hload : 9 * A.natDegree < 4 * D.natDegree
                      ·
                        have hDpos : 0 < D.natDegree := by omega
                        refine CubicSigmaSupportCone610.sigmaD ?_
                        refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                      · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                    · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                  · by_cases heq : 2 * E.natDegree = A.natDegree + 2 * D.natDegree
                    · -- E ties D
                      by_cases hpos : 0 < D.natDegree
                      · by_cases hload : 9 * A.natDegree < 4 * D.natDegree
                        ·
                          have hDpos : 0 < D.natDegree := by omega
                          have hEpos : 0 < E.natDegree := by omega
                          refine CubicSigmaSupportCone610.sigmaDE ?_
                          refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                        · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                      · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                    · -- E strictly outranks D
                      by_cases hpos : 0 < E.natDegree
                      · by_cases hload : 11 * A.natDegree < 4 * E.natDegree
                        ·
                          have hEpos : 0 < E.natDegree := by omega
                          refine CubicSigmaSupportCone610.sigmaE ?_
                          refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                        · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩
                      · refine CubicSigmaSupportCone610.loadCompete ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, by omega, by omega, by omega, by omega⟩

end CubicSigmaExhaust610

/-! ## Assembly -/

section CubicAssemblyWall610

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- Honest leftover after the two walls.

Closed: the 13 empty σ-cones, the all-zero cell, `{C,D}` on and off
the wall `6 nA = 2 nC + nD` (det `N₁`/`N₂` = `143/248832` kills `l`,
then `cubicSigmaCone_CD_impossible` at `l = 0`), the balanced cell on
and off the wall `14 nB = 19 nA` (same determinant), and `l = 0` on
the load-compete chamber.  The A-dominant exhaust
`cubicSigmaSupportCone610_of` is constructive.

Survives: A-dominant load-compete after `l = 0`.  On a `β/δ/ζ/θ`
compete chamber the corresponding odd load vanishes by the existing
`N₁` column theorems; the remaining letter-topped mixed pairs saturate
to `(1)` in CAS.  Next unused row: Lean rest bounds extracting those
faces on the load-compete side of `6 Θ = ρ`.  No finite-root shortcut
is used. -/
theorem normalized610ScaleZero_cubicResidual4
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
      l = 0 := by
  obtain ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
      zeta, eta, theta, iota, cLam, cKap, cMu, cOmi, A, B, C, D, E, ht,
      hj, hjdiv, hHsq, hder, hlamDeg, hkapDeg, hmuDeg, homiDeg, hconeA,
      notB, notC, notD, notE, notBC, notBD, notBE, notCE, notDE, notBCD,
      notBCE, notBDE, notCDE, notZero, notCD, notBCDE⟩ :=
    normalized610ScaleZero_cubicResidual3 hsource
  have hsupp := cubicSigmaSupportCone610_of A B C D E hconeA
  have hload : cubicLoadCompetes610 A B C D E := by
    cases hsupp with
    | loadCompete h => exact h
    | sigmaB h => exact (notB h).elim
    | sigmaC h => exact (notC h).elim
    | sigmaD h => exact (notD h).elim
    | sigmaE h => exact (notE h).elim
    | sigmaBC h => exact (notBC h).elim
    | sigmaBD h => exact (notBD h).elim
    | sigmaBE h => exact (notBE h).elim
    | sigmaCD h =>
      exact (cubicSigmaCone_CD_impossible_all (j := j) (t := t) l alpha
        beta delta epsilon zeta eta theta A B C D E h hmuDeg hkapDeg
        hjdiv hder).elim
    | sigmaCE h => exact (notCE h).elim
    | sigmaDE h => exact (notDE h).elim
    | sigmaBCD h => exact (notBCD h).elim
    | sigmaBCE h => exact (notBCE h).elim
    | sigmaBDE h => exact (notBDE h).elim
    | sigmaCDE h => exact (notCDE h).elim
    | sigmaBCDE h =>
      exact (cubicBalancedCell_impossible_all (j := j) (t := t) l alpha
        beta delta epsilon zeta eta theta A B C D E h hlamDeg hkapDeg
        hmuDeg homiDeg hjdiv hder).elim
    | allZero h => exact (notZero h).elim
  have hl0 : l = 0 :=
    cubicADominant_l_eq_zero l alpha beta delta epsilon zeta eta theta
      A B C D E hload hmuDeg hkapDeg
  exact ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
    zeta, eta, theta, iota, cLam, cKap, cMu, cOmi, A, B, C, D, E, ht, hj,
    hjdiv, hHsq, hder, hlamDeg, hkapDeg, hmuDeg, homiDeg, hconeA, hload,
    hl0⟩

end CubicAssemblyWall610

#print axioms degreeZeroN2Cubic610_eq_Pi_add_A2_kappa
#print axioms degreeZeroN2Cubic610_natDegree_le
#print axioms cubicSigmaCone_CD_wall_impossible
#print axioms cubicBalancedCell_wall_impossible
#print axioms cubicSigmaCone_CD_impossible_all
#print axioms cubicBalancedCell_impossible_all
#print axioms cubicSigmaSupportCone610_of
#print axioms normalized610ScaleZero_cubicResidual4

end Max11DegreeRoutes
