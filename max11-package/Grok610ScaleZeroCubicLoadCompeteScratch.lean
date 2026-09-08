import Grok610ScaleZeroCubicWallScratch
import Grok610AlignedNonsquareDegreeZeroPrimitiveScratch

/-! # Scale-zero cubic load-compete finish, `(6,10)`, `H = 0`

Continuation of `Grok610ScaleZeroCubicWallScratch`.  That file ends at
`normalized610ScaleZero_cubicResidual4`: A-dominant load-compete after
`l = 0`.

CAS (`scripts/derive_610_scale_zero_cubic_adominant.py`,
`scripts/derive_610_scale_zero_cubic_wall_mixed.py`): every nonempty
`(S, letter-face)` and mixed odd-load pair saturates to `(1)`.  This
file extracts those faces on the load-compete side of `6 Θ = ρ` by
splitting the odd pure-`A` columns and the even-load term `α C D`
(the only rest monomial that can meet the top), then bounding the
remaining rest strictly below the face via
`natDegree_add_le` / `natDegree_smul_le` / `natDegree_mul_le` /
`natDegree_pow_le` helpers.

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

/-! ## Kappa split: odd pure-`A` columns, `α C D`, letter face, rest -/

section KappaLoadCompeteSplit610

variable {k : Type*} [Field k] [CharZero k]

def kappaCubicBetaA4610 (beta : k) (A : k[X]) : k[X] :=
  (35 / 10368 * beta : k) • A ^ 4

def kappaCubicDeltaA3610 (delta : k) (A : k[X]) : k[X] :=
  (5 / 432 * delta : k) • A ^ 3

def kappaCubicZetaA2610 (zeta : k) (A : k[X]) : k[X] :=
  (1 / 24 * zeta : k) • A ^ 2

def kappaCubicThetaA1610 (theta : k) (A : k[X]) : k[X] :=
  (1 / 6 * theta : k) • A

def kappaCubicAlphaCD610 (alpha : k) (C D : k[X]) : k[X] :=
  (4 / 9 * alpha : k) • (C * D)

def kappaCubicLetter610 (A B C D E : k[X]) : k[X] :=
  (5 / 243 : k) • (A * B ^ 3)
  + (-(5 / 27 : k)) • (B ^ 2 * D)
  + (-(5 / 27 : k)) • (B * C ^ 2)
  + (10 / 9 : k) • (D * E)

set_option maxHeartbeats 32000000 in
def degreeZeroKappaCubicNoBetaA4_l0610
    (alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (5 / 243 : k) • (A * B ^ 3)
  + (-(5 / 27 : k)) • (B ^ 2 * D)
  + (-(5 / 27 : k)) • (B * C ^ 2)
  + (10 / 9 : k) • (D * E)
  + (-(4 / 81 * alpha : k)) • B ^ 3
  + (4 / 9 * alpha : k) • (B * E)
  + (4 / 9 * alpha : k) • (C * D)
  + (7 / 144 * beta : k) • (A ^ 2 * C)
  + (-(7 / 432 * beta : k)) • (A * B ^ 2)
  + (7 / 36 * beta : k) • (A * E)
  + (7 / 36 * beta : k) • (B * D)
  + (7 / 72 * beta : k) • C ^ 2
  + (5 / 432 * delta : k) • A ^ 3
  + (5 / 36 * delta : k) • (A * C)
  + (-(5 / 72 * delta : k)) • B ^ 2
  + (5 / 6 * delta : k) • E
  + (2 / 3 * epsilon : k) • D
  + (1 / 24 * zeta : k) • A ^ 2
  + (1 / 2 * zeta : k) • C
  + (1 / 3 * eta : k) • B
  + (1 / 6 * theta : k) • A

set_option maxHeartbeats 32000000 in
theorem degreeZeroKappaCubic610_eq_betaA4_add_rest_of_l0
    (alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroKappaCubic610 0 alpha beta delta epsilon zeta eta theta
        A B C D E =
      kappaCubicBetaA4610 beta A +
        degreeZeroKappaCubicNoBetaA4_l0610 alpha beta delta epsilon
          zeta eta theta A B C D E := by
  simp only [degreeZeroKappaCubic610, kappaCubicBetaA4610,
    degreeZeroKappaCubicNoBetaA4_l0610, zero_mul, mul_zero, zero_smul]
  all_goals module

set_option maxHeartbeats 32000000 in
def degreeZeroKappaCubicNoDeltaA3_l0b0610
    (alpha delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (5 / 243 : k) • (A * B ^ 3)
  + (-(5 / 27 : k)) • (B ^ 2 * D)
  + (-(5 / 27 : k)) • (B * C ^ 2)
  + (10 / 9 : k) • (D * E)
  + (-(4 / 81 * alpha : k)) • B ^ 3
  + (4 / 9 * alpha : k) • (B * E)
  + (4 / 9 * alpha : k) • (C * D)
  + (5 / 36 * delta : k) • (A * C)
  + (-(5 / 72 * delta : k)) • B ^ 2
  + (5 / 6 * delta : k) • E
  + (2 / 3 * epsilon : k) • D
  + (1 / 24 * zeta : k) • A ^ 2
  + (1 / 2 * zeta : k) • C
  + (1 / 3 * eta : k) • B
  + (1 / 6 * theta : k) • A

set_option maxHeartbeats 32000000 in
theorem degreeZeroKappaCubic610_eq_deltaA3_add_rest_of_l0b0
    (alpha delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroKappaCubic610 0 alpha 0 delta epsilon zeta eta theta
        A B C D E =
      kappaCubicDeltaA3610 delta A +
        degreeZeroKappaCubicNoDeltaA3_l0b0610 alpha delta epsilon zeta
          eta theta A B C D E := by
  simp only [degreeZeroKappaCubic610, kappaCubicDeltaA3610,
    degreeZeroKappaCubicNoDeltaA3_l0b0610, zero_mul, mul_zero, zero_smul]
  all_goals module

set_option maxHeartbeats 32000000 in
def degreeZeroKappaCubicNoZetaA2_odds0610
    (alpha epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (5 / 243 : k) • (A * B ^ 3)
  + (-(5 / 27 : k)) • (B ^ 2 * D)
  + (-(5 / 27 : k)) • (B * C ^ 2)
  + (10 / 9 : k) • (D * E)
  + (-(4 / 81 * alpha : k)) • B ^ 3
  + (4 / 9 * alpha : k) • (B * E)
  + (4 / 9 * alpha : k) • (C * D)
  + (2 / 3 * epsilon : k) • D
  + (1 / 2 * zeta : k) • C
  + (1 / 3 * eta : k) • B
  + (1 / 6 * theta : k) • A

set_option maxHeartbeats 32000000 in
theorem degreeZeroKappaCubic610_eq_zetaA2_add_rest_of_odds0
    (alpha epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroKappaCubic610 0 alpha 0 0 epsilon zeta eta theta
        A B C D E =
      kappaCubicZetaA2610 zeta A +
        degreeZeroKappaCubicNoZetaA2_odds0610 alpha epsilon zeta eta
          theta A B C D E := by
  simp only [degreeZeroKappaCubic610, kappaCubicZetaA2610,
    degreeZeroKappaCubicNoZetaA2_odds0610, zero_mul, mul_zero, zero_smul]
  all_goals module

def cubicKappaBetaTop610 (A B C D E : k[X]) : Prop :=
  cubicLoadCompetes610 A B C D E ∧
    B.natDegree < A.natDegree ∧
    B.natDegree + 2 * C.natDegree < 4 * A.natDegree ∧
    2 * B.natDegree + D.natDegree < 4 * A.natDegree ∧
    D.natDegree + E.natDegree < 4 * A.natDegree ∧
    C.natDegree + D.natDegree < 4 * A.natDegree

def cubicKappaDeltaTop610 (A B C D E : k[X]) : Prop :=
  cubicLoadCompetes610 A B C D E ∧
    3 * B.natDegree < 2 * A.natDegree ∧
    B.natDegree + 2 * C.natDegree < 3 * A.natDegree ∧
    2 * B.natDegree + D.natDegree < 3 * A.natDegree ∧
    D.natDegree + E.natDegree < 3 * A.natDegree ∧
    C.natDegree + D.natDegree < 3 * A.natDegree ∧
    B.natDegree + E.natDegree < 3 * A.natDegree

def cubicKappaZetaTop610 (A B C D E : k[X]) : Prop :=
  cubicLoadCompetes610 A B C D E ∧
    3 * B.natDegree < A.natDegree ∧
    B.natDegree + 2 * C.natDegree < 2 * A.natDegree ∧
    2 * B.natDegree + D.natDegree < 2 * A.natDegree ∧
    D.natDegree + E.natDegree < 2 * A.natDegree ∧
    C.natDegree + D.natDegree < 2 * A.natDegree ∧
    B.natDegree + E.natDegree < 2 * A.natDegree

theorem cubicKappaDeltaTop610_to_betaTop
    {A B C D E : k[X]} (h : cubicKappaDeltaTop610 A B C D E) :
    cubicKappaBetaTop610 A B C D E := by
  rcases h with ⟨hload, hBn, hBC2, hB2D, hDE, hCD, hBE⟩
  refine ⟨hload, ?_, ?_, ?_, ?_, ?_⟩
  · have : 3 * B.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hBn
    omega
  · have : B.natDegree + 2 * C.natDegree + 1 ≤ 3 * A.natDegree :=
      Nat.succ_le_of_lt hBC2
    omega
  · have : 2 * B.natDegree + D.natDegree + 1 ≤ 3 * A.natDegree :=
      Nat.succ_le_of_lt hB2D
    omega
  · have : D.natDegree + E.natDegree + 1 ≤ 3 * A.natDegree :=
      Nat.succ_le_of_lt hDE
    omega
  · have : C.natDegree + D.natDegree + 1 ≤ 3 * A.natDegree :=
      Nat.succ_le_of_lt hCD
    omega

theorem cubicKappaZetaTop610_to_deltaTop
    {A B C D E : k[X]} (h : cubicKappaZetaTop610 A B C D E) :
    cubicKappaDeltaTop610 A B C D E := by
  rcases h with ⟨hload, hBn, hBC2, hB2D, hDE, hCD, hBE⟩
  refine ⟨hload, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : 3 * B.natDegree + 1 ≤ A.natDegree := Nat.succ_le_of_lt hBn
    omega
  · have : B.natDegree + 2 * C.natDegree + 1 ≤ 2 * A.natDegree :=
      Nat.succ_le_of_lt hBC2
    omega
  · have : 2 * B.natDegree + D.natDegree + 1 ≤ 2 * A.natDegree :=
      Nat.succ_le_of_lt hB2D
    omega
  · have : D.natDegree + E.natDegree + 1 ≤ 2 * A.natDegree :=
      Nat.succ_le_of_lt hDE
    omega
  · have : C.natDegree + D.natDegree + 1 ≤ 2 * A.natDegree :=
      Nat.succ_le_of_lt hCD
    omega
  · have : B.natDegree + E.natDegree + 1 ≤ 2 * A.natDegree :=
      Nat.succ_le_of_lt hBE
    omega

theorem cubicKappaZetaTop610_to_betaTop
    {A B C D E : k[X]} (h : cubicKappaZetaTop610 A B C D E) :
    cubicKappaBetaTop610 A B C D E :=
  cubicKappaDeltaTop610_to_betaTop (cubicKappaZetaTop610_to_deltaTop h)

end KappaLoadCompeteSplit610

/-! ## B0 load-top rest bounds (kappa) -/

section KappaLoadTopBounds610

variable {k : Type*} [Field k] [CharZero k]


set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaCubicNoBetaA4_l0610_natDegree_lt_of_betaTop
    (alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : cubicKappaBetaTop610 A B C D E) :
    (degreeZeroKappaCubicNoBetaA4_l0610 alpha beta delta epsilon zeta
        eta theta A B C D E).natDegree <
      4 * A.natDegree := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBn, hBC2, hB2D, hDE, hCD⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsAB : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAB
  have hsAC : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hAC
  have hsAD : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hAD
  have hsAE : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAE
  have hsBn : B.natDegree + 1 ≤ A.natDegree := Nat.succ_le_of_lt hBn
  have hsBC2 : B.natDegree + 2 * C.natDegree + 1 ≤ 4 * A.natDegree :=
    Nat.succ_le_of_lt hBC2
  have hsB2D : 2 * B.natDegree + D.natDegree + 1 ≤ 4 * A.natDegree :=
    Nat.succ_le_of_lt hB2D
  have hsDE : D.natDegree + E.natDegree + 1 ≤ 4 * A.natDegree :=
    Nat.succ_le_of_lt hDE
  have hsCD : C.natDegree + D.natDegree + 1 ≤ 4 * A.natDegree :=
    Nat.succ_le_of_lt hCD
  -- letter monomials
  have t0 : ((5 / 243 : k) • (A * B ^ 3)).natDegree < 4 * A.natDegree := by
    refine (natDegree_smul_le610 _ _).trans_lt ?_
    have hle : (A * B ^ 3).natDegree ≤ A.natDegree + 3 * B.natDegree :=
      (natDegree_mul_le (p := A) (q := B ^ 3)).trans
        (add_le_add le_rfl (natDegree_pow B 3).le)
    exact hle.trans_lt (by omega)
  have t1 : ((-(5 / 27 : k)) • (B ^ 2 * D)).natDegree < 4 * A.natDegree := by
    refine (natDegree_smul_le610 _ _).trans_lt ?_
    have hle : (B ^ 2 * D).natDegree ≤ 2 * B.natDegree + D.natDegree :=
      (natDegree_mul_le (p := B ^ 2) (q := D)).trans
        (add_le_add (natDegree_pow B 2).le le_rfl)
    exact hle.trans_lt (by omega)
  have t2 : ((-(5 / 27 : k)) • (B * C ^ 2)).natDegree < 4 * A.natDegree := by
    refine (natDegree_smul_le610 _ _).trans_lt ?_
    have hle : (B * C ^ 2).natDegree ≤ B.natDegree + 2 * C.natDegree :=
      (natDegree_mul_le (p := B) (q := C ^ 2)).trans
        (add_le_add le_rfl (natDegree_pow C 2).le)
    exact hle.trans_lt (by omega)
  have t3 : ((10 / 9 : k) • (D * E)).natDegree < 4 * A.natDegree := by
    refine (natDegree_smul_le610 _ _).trans_lt ?_
    have hle : (D * E).natDegree ≤ D.natDegree + E.natDegree := natDegree_mul_le
    exact hle.trans_lt (by omega)
  have t4 : ((-(4 / 81 * alpha : k)) • B ^ 3).natDegree < 4 * A.natDegree := by
    refine (natDegree_smul_le610 _ _).trans_lt ?_
    have hle : (B ^ 3).natDegree ≤ 3 * B.natDegree := (natDegree_pow B 3).le
    exact hle.trans_lt (by omega)
  have t5 : ((4 / 9 * alpha : k) • (B * E)).natDegree < 4 * A.natDegree := by
    refine (natDegree_smul_le610 _ _).trans_lt ?_
    have hle : (B * E).natDegree ≤ B.natDegree + E.natDegree := natDegree_mul_le
    exact hle.trans_lt (by omega)
  have t6 : ((4 / 9 * alpha : k) • (C * D)).natDegree < 4 * A.natDegree := by
    refine (natDegree_smul_le610 _ _).trans_lt ?_
    have hle : (C * D).natDegree ≤ C.natDegree + D.natDegree := natDegree_mul_le
    exact hle.trans_lt (by omega)
  have t7 : ((7 / 144 * beta : k) • (A ^ 2 * C)).natDegree < 4 * A.natDegree := by
    refine (natDegree_smul_le610 _ _).trans_lt ?_
    have hle : (A ^ 2 * C).natDegree ≤ 2 * A.natDegree + C.natDegree :=
      (natDegree_mul_le (p := A ^ 2) (q := C)).trans
        (add_le_add (natDegree_pow A 2).le le_rfl)
    exact hle.trans_lt (by omega)
  have t8 : ((-(7 / 432 * beta : k)) • (A * B ^ 2)).natDegree < 4 * A.natDegree := by
    refine (natDegree_smul_le610 _ _).trans_lt ?_
    have hle : (A * B ^ 2).natDegree ≤ A.natDegree + 2 * B.natDegree :=
      (natDegree_mul_le (p := A) (q := B ^ 2)).trans
        (add_le_add le_rfl (natDegree_pow B 2).le)
    exact hle.trans_lt (by omega)
  have t9 : ((7 / 36 * beta : k) • (A * E)).natDegree < 4 * A.natDegree := by
    refine (natDegree_smul_le610 _ _).trans_lt ?_
    have hle : (A * E).natDegree ≤ A.natDegree + E.natDegree := natDegree_mul_le
    exact hle.trans_lt (by omega)
  have t10 : ((7 / 36 * beta : k) • (B * D)).natDegree < 4 * A.natDegree := by
    refine (natDegree_smul_le610 _ _).trans_lt ?_
    have hle : (B * D).natDegree ≤ B.natDegree + D.natDegree := natDegree_mul_le
    exact hle.trans_lt (by omega)
  have t11 : ((7 / 72 * beta : k) • C ^ 2).natDegree < 4 * A.natDegree := by
    refine (natDegree_smul_le610 _ _).trans_lt ?_
    have hle : (C ^ 2).natDegree ≤ 2 * C.natDegree := (natDegree_pow C 2).le
    exact hle.trans_lt (by omega)
  have t12 : ((5 / 432 * delta : k) • A ^ 3).natDegree < 4 * A.natDegree := by
    refine (natDegree_smul_le610 _ _).trans_lt ?_
    have hle : (A ^ 3).natDegree ≤ 3 * A.natDegree := (natDegree_pow A 3).le
    exact hle.trans_lt (by omega)
  have t13 : ((5 / 36 * delta : k) • (A * C)).natDegree < 4 * A.natDegree := by
    refine (natDegree_smul_le610 _ _).trans_lt ?_
    have hle : (A * C).natDegree ≤ A.natDegree + C.natDegree := natDegree_mul_le
    exact hle.trans_lt (by omega)
  have t14 : ((-(5 / 72 * delta : k)) • B ^ 2).natDegree < 4 * A.natDegree := by
    refine (natDegree_smul_le610 _ _).trans_lt ?_
    have hle : (B ^ 2).natDegree ≤ 2 * B.natDegree := (natDegree_pow B 2).le
    exact hle.trans_lt (by omega)
  have t15 : ((5 / 6 * delta : k) • E).natDegree < 4 * A.natDegree := by
    refine (natDegree_smul_le610 _ _).trans_lt ?_
    exact (le_refl E.natDegree).trans_lt (by omega)
  have t16 : ((2 / 3 * epsilon : k) • D).natDegree < 4 * A.natDegree := by
    refine (natDegree_smul_le610 _ _).trans_lt ?_
    exact (le_refl D.natDegree).trans_lt (by omega)
  have t17 : ((1 / 24 * zeta : k) • A ^ 2).natDegree < 4 * A.natDegree := by
    refine (natDegree_smul_le610 _ _).trans_lt ?_
    have hle : (A ^ 2).natDegree ≤ 2 * A.natDegree := (natDegree_pow A 2).le
    exact hle.trans_lt (by omega)
  have t18 : ((1 / 2 * zeta : k) • C).natDegree < 4 * A.natDegree := by
    refine (natDegree_smul_le610 _ _).trans_lt ?_
    exact (le_refl C.natDegree).trans_lt (by omega)
  have t19 : ((1 / 3 * eta : k) • B).natDegree < 4 * A.natDegree := by
    refine (natDegree_smul_le610 _ _).trans_lt ?_
    exact (le_refl B.natDegree).trans_lt (by omega)
  have t20 : ((1 / 6 * theta : k) • A).natDegree < 4 * A.natDegree := by
    refine (natDegree_smul_le610 _ _).trans_lt ?_
    exact (le_refl A.natDegree).trans_lt (by omega)
  simp only [degreeZeroKappaCubicNoBetaA4_l0610]
  exact
    natDegree_add_lt610
      (natDegree_add_lt610
        (natDegree_add_lt610
          (natDegree_add_lt610
            (natDegree_add_lt610
              (natDegree_add_lt610
                (natDegree_add_lt610
                  (natDegree_add_lt610
                    (natDegree_add_lt610
                      (natDegree_add_lt610
                        (natDegree_add_lt610
                          (natDegree_add_lt610
                            (natDegree_add_lt610
                              (natDegree_add_lt610
                                (natDegree_add_lt610
                                  (natDegree_add_lt610
                                    (natDegree_add_lt610
                                      (natDegree_add_lt610
                                        (natDegree_add_lt610
                                          (natDegree_add_lt610 t0 t1) t2) t3) t4) t5) t6) t7) t8) t9)
                        t10) t11) t12) t13) t14) t15) t16) t17) t18) t19) t20


theorem cubicLoadCompete_beta_eq_zero_of_kappaTop
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : cubicKappaBetaTop610 A B C D E)
    (hl : l = 0)
    (hkap : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree = 0) :
    beta = 0 := by
  by_contra hb
  have hApos : 0 < A.natDegree := hcone.1.1.1
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    omega
  have hc : (35 / 10368 * beta : k) ≠ 0 :=
    mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hb
  have hlead : (kappaCubicBetaA4610 beta A).natDegree = 4 * A.natDegree := by
    simp only [kappaCubicBetaA4610]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :=
    degreeZeroKappaCubicNoBetaA4_l0610_natDegree_lt_of_betaTop alpha beta
      delta epsilon zeta eta theta A B C D E hcone
  subst hl
  have hdeg :
      (degreeZeroKappaCubic610 0 alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree =
        4 * A.natDegree := by
    rw [degreeZeroKappaCubic610_eq_betaA4_add_rest_of_l0,
      natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
  omega


set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaCubicNoDeltaA3_l0b0610_natDegree_lt_of_deltaTop
    (alpha delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : cubicKappaDeltaTop610 A B C D E) :
    (degreeZeroKappaCubicNoDeltaA3_l0b0610 alpha delta epsilon zeta eta
        theta A B C D E).natDegree <
      3 * A.natDegree := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBn, hBC2, hB2D, hDE, hCD, hBE⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsAB : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAB
  have hsAC : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hAC
  have hsAD : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hAD
  have hsAE : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAE
  have hsBn : 3 * B.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hBn
  have hsBC2 : B.natDegree + 2 * C.natDegree + 1 ≤ 3 * A.natDegree :=
    Nat.succ_le_of_lt hBC2
  have hsB2D : 2 * B.natDegree + D.natDegree + 1 ≤ 3 * A.natDegree :=
    Nat.succ_le_of_lt hB2D
  have hsDE : D.natDegree + E.natDegree + 1 ≤ 3 * A.natDegree :=
    Nat.succ_le_of_lt hDE
  have hsCD : C.natDegree + D.natDegree + 1 ≤ 3 * A.natDegree :=
    Nat.succ_le_of_lt hCD
  have hsBE : B.natDegree + E.natDegree + 1 ≤ 3 * A.natDegree :=
    Nat.succ_le_of_lt hBE
  have t0 : ((5 / 243 : k) • (A * B ^ 3)).natDegree < 3 * A.natDegree := by
    refine (natDegree_smul_le610 _ _).trans_lt ?_
    have hle : (A * B ^ 3).natDegree ≤ A.natDegree + 3 * B.natDegree :=
      (natDegree_mul_le (p := A) (q := B ^ 3)).trans
        (add_le_add le_rfl (natDegree_pow B 3).le)
    exact hle.trans_lt (by omega)
  have t1 : ((-(5 / 27 : k)) • (B ^ 2 * D)).natDegree < 3 * A.natDegree := by
    refine (natDegree_smul_le610 _ _).trans_lt ?_
    have hle : (B ^ 2 * D).natDegree ≤ 2 * B.natDegree + D.natDegree :=
      (natDegree_mul_le (p := B ^ 2) (q := D)).trans
        (add_le_add (natDegree_pow B 2).le le_rfl)
    exact hle.trans_lt (by omega)
  have t2 : ((-(5 / 27 : k)) • (B * C ^ 2)).natDegree < 3 * A.natDegree := by
    refine (natDegree_smul_le610 _ _).trans_lt ?_
    have hle : (B * C ^ 2).natDegree ≤ B.natDegree + 2 * C.natDegree :=
      (natDegree_mul_le (p := B) (q := C ^ 2)).trans
        (add_le_add le_rfl (natDegree_pow C 2).le)
    exact hle.trans_lt (by omega)
  have t3 : ((10 / 9 : k) • (D * E)).natDegree < 3 * A.natDegree := by
    refine (natDegree_smul_le610 _ _).trans_lt ?_
    have hle : (D * E).natDegree ≤ D.natDegree + E.natDegree := natDegree_mul_le
    exact hle.trans_lt (by omega)
  have t4 : ((-(4 / 81 * alpha : k)) • B ^ 3).natDegree < 3 * A.natDegree := by
    refine (natDegree_smul_le610 _ _).trans_lt ?_
    have hle : (B ^ 3).natDegree ≤ 3 * B.natDegree := (natDegree_pow B 3).le
    exact hle.trans_lt (by omega)
  have t5 : ((4 / 9 * alpha : k) • (B * E)).natDegree < 3 * A.natDegree := by
    refine (natDegree_smul_le610 _ _).trans_lt ?_
    have hle : (B * E).natDegree ≤ B.natDegree + E.natDegree := natDegree_mul_le
    exact hle.trans_lt (by omega)
  have t6 : ((4 / 9 * alpha : k) • (C * D)).natDegree < 3 * A.natDegree := by
    refine (natDegree_smul_le610 _ _).trans_lt ?_
    have hle : (C * D).natDegree ≤ C.natDegree + D.natDegree := natDegree_mul_le
    exact hle.trans_lt (by omega)
  have t7 : ((5 / 36 * delta : k) • (A * C)).natDegree < 3 * A.natDegree := by
    refine (natDegree_smul_le610 _ _).trans_lt ?_
    have hle : (A * C).natDegree ≤ A.natDegree + C.natDegree := natDegree_mul_le
    exact hle.trans_lt (by omega)
  have t8 : ((-(5 / 72 * delta : k)) • B ^ 2).natDegree < 3 * A.natDegree := by
    refine (natDegree_smul_le610 _ _).trans_lt ?_
    have hle : (B ^ 2).natDegree ≤ 2 * B.natDegree := (natDegree_pow B 2).le
    exact hle.trans_lt (by omega)
  have t9 : ((5 / 6 * delta : k) • E).natDegree < 3 * A.natDegree := by
    refine (natDegree_smul_le610 _ _).trans_lt ?_
    exact (le_refl E.natDegree).trans_lt (by omega)
  have t10 : ((2 / 3 * epsilon : k) • D).natDegree < 3 * A.natDegree := by
    refine (natDegree_smul_le610 _ _).trans_lt ?_
    exact (le_refl D.natDegree).trans_lt (by omega)
  have t11 : ((1 / 24 * zeta : k) • A ^ 2).natDegree < 3 * A.natDegree := by
    refine (natDegree_smul_le610 _ _).trans_lt ?_
    have hle : (A ^ 2).natDegree ≤ 2 * A.natDegree := (natDegree_pow A 2).le
    exact hle.trans_lt (by omega)
  have t12 : ((1 / 2 * zeta : k) • C).natDegree < 3 * A.natDegree := by
    refine (natDegree_smul_le610 _ _).trans_lt ?_
    exact (le_refl C.natDegree).trans_lt (by omega)
  have t13 : ((1 / 3 * eta : k) • B).natDegree < 3 * A.natDegree := by
    refine (natDegree_smul_le610 _ _).trans_lt ?_
    exact (le_refl B.natDegree).trans_lt (by omega)
  have t14 : ((1 / 6 * theta : k) • A).natDegree < 3 * A.natDegree := by
    refine (natDegree_smul_le610 _ _).trans_lt ?_
    exact (le_refl A.natDegree).trans_lt (by omega)
  simp only [degreeZeroKappaCubicNoDeltaA3_l0b0610]
  exact
    natDegree_add_lt610
      (natDegree_add_lt610
        (natDegree_add_lt610
          (natDegree_add_lt610
            (natDegree_add_lt610
              (natDegree_add_lt610
                (natDegree_add_lt610
                  (natDegree_add_lt610
                    (natDegree_add_lt610
                      (natDegree_add_lt610
                        (natDegree_add_lt610
                          (natDegree_add_lt610
                            (natDegree_add_lt610
                              (natDegree_add_lt610 t0 t1) t2) t3) t4) t5) t6) t7) t8) t9) t10) t11)
            t12) t13) t14


theorem cubicLoadCompete_delta_eq_zero_of_kappaTop
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : cubicKappaDeltaTop610 A B C D E)
    (hl : l = 0) (hbeta : beta = 0)
    (hkap : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree = 0) :
    delta = 0 := by
  by_contra hd
  have hApos : 0 < A.natDegree := hcone.1.1.1
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    omega
  have hc : (5 / 432 * delta : k) ≠ 0 :=
    mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hd
  have hlead : (kappaCubicDeltaA3610 delta A).natDegree = 3 * A.natDegree := by
    simp only [kappaCubicDeltaA3610]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :=
    degreeZeroKappaCubicNoDeltaA3_l0b0610_natDegree_lt_of_deltaTop alpha
      delta epsilon zeta eta theta A B C D E hcone
  subst hl
  subst hbeta
  have hdeg :
      (degreeZeroKappaCubic610 0 alpha 0 delta epsilon zeta eta theta
          A B C D E).natDegree =
        3 * A.natDegree := by
    rw [degreeZeroKappaCubic610_eq_deltaA3_add_rest_of_l0b0,
      natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
  omega


set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaCubicNoZetaA2_odds0610_natDegree_lt_of_zetaTop
    (alpha epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : cubicKappaZetaTop610 A B C D E) :
    (degreeZeroKappaCubicNoZetaA2_odds0610 alpha epsilon zeta eta theta
        A B C D E).natDegree <
      2 * A.natDegree := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBn, hBC2, hB2D, hDE, hCD, hBE⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsAB : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAB
  have hsAC : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hAC
  have hsAD : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hAD
  have hsAE : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAE
  have hsBn : 3 * B.natDegree + 1 ≤ A.natDegree := Nat.succ_le_of_lt hBn
  have hsBC2 : B.natDegree + 2 * C.natDegree + 1 ≤ 2 * A.natDegree :=
    Nat.succ_le_of_lt hBC2
  have hsB2D : 2 * B.natDegree + D.natDegree + 1 ≤ 2 * A.natDegree :=
    Nat.succ_le_of_lt hB2D
  have hsDE : D.natDegree + E.natDegree + 1 ≤ 2 * A.natDegree :=
    Nat.succ_le_of_lt hDE
  have hsCD : C.natDegree + D.natDegree + 1 ≤ 2 * A.natDegree :=
    Nat.succ_le_of_lt hCD
  have hsBE : B.natDegree + E.natDegree + 1 ≤ 2 * A.natDegree :=
    Nat.succ_le_of_lt hBE
  have t0 : ((5 / 243 : k) • (A * B ^ 3)).natDegree < 2 * A.natDegree := by
    refine (natDegree_smul_le610 _ _).trans_lt ?_
    have hle : (A * B ^ 3).natDegree ≤ A.natDegree + 3 * B.natDegree :=
      (natDegree_mul_le (p := A) (q := B ^ 3)).trans
        (add_le_add le_rfl (natDegree_pow B 3).le)
    exact hle.trans_lt (by omega)
  have t1 : ((-(5 / 27 : k)) • (B ^ 2 * D)).natDegree < 2 * A.natDegree := by
    refine (natDegree_smul_le610 _ _).trans_lt ?_
    have hle : (B ^ 2 * D).natDegree ≤ 2 * B.natDegree + D.natDegree :=
      (natDegree_mul_le (p := B ^ 2) (q := D)).trans
        (add_le_add (natDegree_pow B 2).le le_rfl)
    exact hle.trans_lt (by omega)
  have t2 : ((-(5 / 27 : k)) • (B * C ^ 2)).natDegree < 2 * A.natDegree := by
    refine (natDegree_smul_le610 _ _).trans_lt ?_
    have hle : (B * C ^ 2).natDegree ≤ B.natDegree + 2 * C.natDegree :=
      (natDegree_mul_le (p := B) (q := C ^ 2)).trans
        (add_le_add le_rfl (natDegree_pow C 2).le)
    exact hle.trans_lt (by omega)
  have t3 : ((10 / 9 : k) • (D * E)).natDegree < 2 * A.natDegree := by
    refine (natDegree_smul_le610 _ _).trans_lt ?_
    have hle : (D * E).natDegree ≤ D.natDegree + E.natDegree := natDegree_mul_le
    exact hle.trans_lt (by omega)
  have t4 : ((-(4 / 81 * alpha : k)) • B ^ 3).natDegree < 2 * A.natDegree := by
    refine (natDegree_smul_le610 _ _).trans_lt ?_
    have hle : (B ^ 3).natDegree ≤ 3 * B.natDegree := (natDegree_pow B 3).le
    exact hle.trans_lt (by omega)
  have t5 : ((4 / 9 * alpha : k) • (B * E)).natDegree < 2 * A.natDegree := by
    refine (natDegree_smul_le610 _ _).trans_lt ?_
    have hle : (B * E).natDegree ≤ B.natDegree + E.natDegree := natDegree_mul_le
    exact hle.trans_lt (by omega)
  have t6 : ((4 / 9 * alpha : k) • (C * D)).natDegree < 2 * A.natDegree := by
    refine (natDegree_smul_le610 _ _).trans_lt ?_
    have hle : (C * D).natDegree ≤ C.natDegree + D.natDegree := natDegree_mul_le
    exact hle.trans_lt (by omega)
  have t7 : ((2 / 3 * epsilon : k) • D).natDegree < 2 * A.natDegree := by
    refine (natDegree_smul_le610 _ _).trans_lt ?_
    exact (le_refl D.natDegree).trans_lt (by omega)
  have t8 : ((1 / 2 * zeta : k) • C).natDegree < 2 * A.natDegree := by
    refine (natDegree_smul_le610 _ _).trans_lt ?_
    exact (le_refl C.natDegree).trans_lt (by omega)
  have t9 : ((1 / 3 * eta : k) • B).natDegree < 2 * A.natDegree := by
    refine (natDegree_smul_le610 _ _).trans_lt ?_
    exact (le_refl B.natDegree).trans_lt (by omega)
  have t10 : ((1 / 6 * theta : k) • A).natDegree < 2 * A.natDegree := by
    refine (natDegree_smul_le610 _ _).trans_lt ?_
    exact (le_refl A.natDegree).trans_lt (by omega)
  simp only [degreeZeroKappaCubicNoZetaA2_odds0610]
  exact
    natDegree_add_lt610
      (natDegree_add_lt610
        (natDegree_add_lt610
          (natDegree_add_lt610
            (natDegree_add_lt610
              (natDegree_add_lt610
                (natDegree_add_lt610
                  (natDegree_add_lt610
                    (natDegree_add_lt610
                      (natDegree_add_lt610 t0 t1) t2) t3) t4) t5) t6) t7) t8) t9) t10


theorem cubicLoadCompete_zeta_eq_zero_of_kappaTop
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : cubicKappaZetaTop610 A B C D E)
    (hl : l = 0) (hbeta : beta = 0) (hdelta : delta = 0)
    (hkap : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree = 0) :
    zeta = 0 := by
  by_contra hz
  have hApos : 0 < A.natDegree := hcone.1.1.1
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    omega
  have hc : (1 / 24 * zeta : k) ≠ 0 :=
    mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hz
  have hlead : (kappaCubicZetaA2610 zeta A).natDegree = 2 * A.natDegree := by
    simp only [kappaCubicZetaA2610]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :=
    degreeZeroKappaCubicNoZetaA2_odds0610_natDegree_lt_of_zetaTop alpha
      epsilon zeta eta theta A B C D E hcone
  subst hl
  subst hbeta
  subst hdelta
  have hdeg :
      (degreeZeroKappaCubic610 0 alpha 0 0 epsilon zeta eta theta
          A B C D E).natDegree =
        2 * A.natDegree := by
    rw [degreeZeroKappaCubic610_eq_zetaA2_add_rest_of_odds0,
      natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
  omega

end KappaLoadTopBounds610

/-! ## Assembly -/

section CubicLoadCompeteAssembly610

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- Honest leftover after the kappa load-top rest bounds.

Closed: `l = 0` (parent).  On `cubicKappaBetaTop610` we have `β = 0`;
on `cubicKappaDeltaTop610` we have `δ = 0`; on `cubicKappaZetaTop610`
we have `ζ = 0`.  Those are the chambers where the odd pure-`A` column
strictly outranks every load-free kappa monomial and `α C D`.

Survives: A-dominant load-compete after `l = 0` that is not a kappa
`β/δ/ζ` load-top chamber — some load-free kappa monomial or `α C D`
meets or exceeds the next odd pure-`A` column (letter-topped / mixed).
CAS saturates every nonempty `(S, letter-face)` and mixed pair to
`(1)`.  Next unused row: letter-face rest bounds on that side of
`6 Θ = ρ`.  No finite-root shortcut is used. -/
theorem normalized610ScaleZero_cubicResidual5
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
      (cubicKappaZetaTop610 A B C D E → zeta = 0) := by
  obtain ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
      zeta, eta, theta, iota, cLam, cKap, cMu, cOmi, A, B, C, D, E, ht,
      hj, hjdiv, hHsq, hder, hlamDeg, hkapDeg, hmuDeg, homiDeg, hconeA,
      hload, hl0⟩ :=
    normalized610ScaleZero_cubicResidual4 hsource
  refine ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
    zeta, eta, theta, iota, cLam, cKap, cMu, cOmi, A, B, C, D, E, ht, hj,
    hjdiv, hHsq, hder, hlamDeg, hkapDeg, hmuDeg, homiDeg, hconeA, hload,
    hl0, ?hb, ?hd, ?hz⟩
  · intro htop
    exact cubicLoadCompete_beta_eq_zero_of_kappaTop l alpha beta delta
      epsilon zeta eta theta A B C D E htop hl0 hkapDeg
  · intro htop
    exact cubicLoadCompete_delta_eq_zero_of_kappaTop l alpha beta delta
      epsilon zeta eta theta A B C D E htop hl0
      (cubicLoadCompete_beta_eq_zero_of_kappaTop l alpha beta delta
        epsilon zeta eta theta A B C D E
        (cubicKappaDeltaTop610_to_betaTop htop) hl0 hkapDeg)
      hkapDeg
  · intro htop
    exact cubicLoadCompete_zeta_eq_zero_of_kappaTop l alpha beta delta
      epsilon zeta eta theta A B C D E htop hl0
      (cubicLoadCompete_beta_eq_zero_of_kappaTop l alpha beta delta
        epsilon zeta eta theta A B C D E
        (cubicKappaZetaTop610_to_betaTop htop) hl0 hkapDeg)
      (cubicLoadCompete_delta_eq_zero_of_kappaTop l alpha beta delta
        epsilon zeta eta theta A B C D E
        (cubicKappaZetaTop610_to_deltaTop htop) hl0
        (cubicLoadCompete_beta_eq_zero_of_kappaTop l alpha beta delta
          epsilon zeta eta theta A B C D E
          (cubicKappaZetaTop610_to_betaTop htop) hl0 hkapDeg)
        hkapDeg)
      hkapDeg

end CubicLoadCompeteAssembly610

#print axioms degreeZeroKappaCubic610_eq_betaA4_add_rest_of_l0
#print axioms degreeZeroKappaCubicNoBetaA4_l0610_natDegree_lt_of_betaTop
#print axioms cubicLoadCompete_beta_eq_zero_of_kappaTop
#print axioms cubicLoadCompete_delta_eq_zero_of_kappaTop
#print axioms cubicLoadCompete_zeta_eq_zero_of_kappaTop
#print axioms normalized610ScaleZero_cubicResidual5

end Max11DegreeRoutes
