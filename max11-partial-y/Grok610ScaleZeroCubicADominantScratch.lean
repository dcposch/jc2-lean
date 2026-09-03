import Grok610ScaleZeroCubicConesScratch
import Grok610AlignedNonsquareDegreeZeroPrimitiveScratch

/-! # Scale-zero cubic A-dominant Stage B+C, for normalized `(6,10)`, `H = 0`

Continuation of `Grok610ScaleZeroCubicConesScratch`.  That file ends at
`normalized610ScaleZero_cubicADominantResidual`: the source loads the
cubic letters `A,B,C,D,E` on the single cone `R = {A}`.

CAS jobs `scripts/derive_610_scale_zero_cubic_adominant.py` and
`scripts/derive_610_scale_zero_cubic_balanced.py` analyse the σ-grading
inside `R = {A}`.  Thirteen argmin cones are empty, `{C,D}` closes by
the σ-7 part of `N₁ = μ + (A/6) κ`, and the balanced cell dies by
`⟨G1,G2,G3,G4⟩`.  Odd loads vanish on the competing-load wall by the
pure-`A` column of `N₁`.

No total-degree or twice-prime theorem is used.  No `sorry`, no new
axioms, no finite-root shortcut.  Untracked working note.
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

/-! ## σ-argmin cones inside `R = {A}` -/

section CubicSigmaCones610

variable {k : Type*} [Field k] [CharZero k]

def CubicSigmaConeB610 (A B C D E : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree
    ∧ 0 < B.natDegree
    ∧ 2 * C.natDegree < A.natDegree + 2 * B.natDegree
    ∧ 4 * D.natDegree < A.natDegree + 6 * B.natDegree
    ∧ 4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree
    ∧ 4 * A.natDegree < 3 * B.natDegree


def CubicSigmaConeC610 (A B C D E : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree
    ∧ 0 < C.natDegree
    ∧ A.natDegree + 2 * B.natDegree < 2 * C.natDegree
    ∧ A.natDegree + 2 * D.natDegree < 3 * C.natDegree
    ∧ 2 * E.natDegree < 3 * C.natDegree
    ∧ 11 * A.natDegree < 6 * C.natDegree


def CubicSigmaConeD610 (A B C D E : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree
    ∧ 0 < D.natDegree
    ∧ A.natDegree + 6 * B.natDegree < 4 * D.natDegree
    ∧ 3 * C.natDegree < A.natDegree + 2 * D.natDegree
    ∧ 2 * E.natDegree < A.natDegree + 2 * D.natDegree
    ∧ 9 * A.natDegree < 4 * D.natDegree


def CubicSigmaConeE610 (A B C D E : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree
    ∧ 0 < E.natDegree
    ∧ 3 * A.natDegree + 6 * B.natDegree < 4 * E.natDegree
    ∧ 3 * C.natDegree < 2 * E.natDegree
    ∧ A.natDegree + 2 * D.natDegree < 2 * E.natDegree
    ∧ 11 * A.natDegree < 4 * E.natDegree


def CubicSigmaConeBC610 (A B C D E : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree
    ∧ 0 < B.natDegree
    ∧ 0 < C.natDegree
    ∧ 4 * A.natDegree + 2 * B.natDegree = 3 * A.natDegree + 2 * C.natDegree
    ∧ 4 * D.natDegree < A.natDegree + 6 * B.natDegree
    ∧ 4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree
    ∧ 4 * A.natDegree < 3 * B.natDegree


def CubicSigmaConeBD610 (A B C D E : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree
    ∧ 0 < B.natDegree
    ∧ 0 < D.natDegree
    ∧ 10 * A.natDegree + 6 * B.natDegree = 9 * A.natDegree + 4 * D.natDegree
    ∧ 2 * C.natDegree < A.natDegree + 2 * B.natDegree
    ∧ 4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree
    ∧ 4 * A.natDegree < 3 * B.natDegree


def CubicSigmaConeBE610 (A B C D E : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree
    ∧ 0 < B.natDegree
    ∧ 0 < E.natDegree
    ∧ 12 * A.natDegree + 6 * B.natDegree = 9 * A.natDegree + 4 * E.natDegree
    ∧ 2 * C.natDegree < A.natDegree + 2 * B.natDegree
    ∧ 4 * D.natDegree < A.natDegree + 6 * B.natDegree
    ∧ 4 * A.natDegree < 3 * B.natDegree


def CubicSigmaConeCE610 (A B C D E : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree
    ∧ 0 < C.natDegree
    ∧ 0 < E.natDegree
    ∧ 6 * A.natDegree + 3 * C.natDegree = 6 * A.natDegree + 2 * E.natDegree
    ∧ A.natDegree + 2 * B.natDegree < 2 * C.natDegree
    ∧ A.natDegree + 2 * D.natDegree < 3 * C.natDegree
    ∧ 11 * A.natDegree < 6 * C.natDegree


def CubicSigmaConeDE610 (A B C D E : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree
    ∧ 0 < D.natDegree
    ∧ 0 < E.natDegree
    ∧ 6 * A.natDegree + 2 * D.natDegree = 5 * A.natDegree + 2 * E.natDegree
    ∧ A.natDegree + 6 * B.natDegree < 4 * D.natDegree
    ∧ 3 * C.natDegree < A.natDegree + 2 * D.natDegree
    ∧ 9 * A.natDegree < 4 * D.natDegree


def CubicSigmaConeBCD610 (A B C D E : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree
    ∧ 0 < B.natDegree
    ∧ 0 < C.natDegree
    ∧ 0 < D.natDegree
    ∧ 4 * A.natDegree + 2 * B.natDegree = 3 * A.natDegree + 2 * C.natDegree
    ∧ 10 * A.natDegree + 6 * B.natDegree = 9 * A.natDegree + 4 * D.natDegree
    ∧ 4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree
    ∧ 4 * A.natDegree < 3 * B.natDegree


def CubicSigmaConeBCE610 (A B C D E : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree
    ∧ 0 < B.natDegree
    ∧ 0 < C.natDegree
    ∧ 0 < E.natDegree
    ∧ 4 * A.natDegree + 2 * B.natDegree = 3 * A.natDegree + 2 * C.natDegree
    ∧ 12 * A.natDegree + 6 * B.natDegree = 9 * A.natDegree + 4 * E.natDegree
    ∧ 4 * D.natDegree < A.natDegree + 6 * B.natDegree
    ∧ 4 * A.natDegree < 3 * B.natDegree


def CubicSigmaConeBDE610 (A B C D E : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree
    ∧ 0 < B.natDegree
    ∧ 0 < D.natDegree
    ∧ 0 < E.natDegree
    ∧ 10 * A.natDegree + 6 * B.natDegree = 9 * A.natDegree + 4 * D.natDegree
    ∧ 12 * A.natDegree + 6 * B.natDegree = 9 * A.natDegree + 4 * E.natDegree
    ∧ 2 * C.natDegree < A.natDegree + 2 * B.natDegree
    ∧ 4 * A.natDegree < 3 * B.natDegree


def CubicSigmaConeCDE610 (A B C D E : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree
    ∧ 0 < C.natDegree
    ∧ 0 < D.natDegree
    ∧ 0 < E.natDegree
    ∧ 5 * A.natDegree + 3 * C.natDegree = 6 * A.natDegree + 2 * D.natDegree
    ∧ 6 * A.natDegree + 3 * C.natDegree = 6 * A.natDegree + 2 * E.natDegree
    ∧ A.natDegree + 2 * B.natDegree < 2 * C.natDegree
    ∧ 11 * A.natDegree < 6 * C.natDegree


def CubicSigmaConeCD610 (A B C D E : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree
    ∧ 0 < C.natDegree
    ∧ 0 < D.natDegree
    ∧ 5 * A.natDegree + 3 * C.natDegree = 6 * A.natDegree + 2 * D.natDegree
    ∧ A.natDegree + 2 * B.natDegree < 2 * C.natDegree
    ∧ 2 * E.natDegree < 3 * C.natDegree
    ∧ 11 * A.natDegree < 6 * C.natDegree


def CubicSigmaConeBCDE610 (A B C D E : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree
    ∧ 0 < B.natDegree
    ∧ 0 < C.natDegree
    ∧ 0 < D.natDegree
    ∧ 0 < E.natDegree
    ∧ 4 * A.natDegree + 2 * B.natDegree = 3 * A.natDegree + 2 * C.natDegree
    ∧ 10 * A.natDegree + 6 * B.natDegree = 9 * A.natDegree + 4 * D.natDegree
    ∧ 12 * A.natDegree + 6 * B.natDegree = 9 * A.natDegree + 4 * E.natDegree
    ∧ 4 * A.natDegree < 3 * B.natDegree


def cubicLoadCompetes610 (A B C D E : k[X]) : Prop :=
  CubicRatioConeA610 A B C D E ∧
    4 * A.natDegree ≥ 3 * B.natDegree ∧
    11 * A.natDegree ≥ 6 * C.natDegree ∧
    9 * A.natDegree ≥ 4 * D.natDegree ∧
    11 * A.natDegree ≥ 4 * E.natDegree

end CubicSigmaCones610

/-! ## The combination `N₁ = μ + (A/6) κ` -/

section CubicN1_610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 32000000 in
def degreeZeroN1Cubic610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (5 / 81 : k) • (A * B ^ 2 * D)
  + (20 / 243 : k) • (B ^ 3 * C)
  - (10 / 27 : k) • (B * C * E)
  - (5 / 27 : k) • (B * D ^ 2)
  - (5 / 27 : k) • (C ^ 2 * D)
  + (77 / 248832 * l : k) • A ^ 6
  + (35 / 6912 * l : k) • (A ^ 4 * C)
  - (1 / 1152 * l : k) • (A ^ 3 * B ^ 2)
  + (5 / 288 * l : k) • (A ^ 3 * E)
  - (1 / 96 * l : k) • (A ^ 2 * B * D)
  + (1 / 64 * l : k) • (A ^ 2 * C ^ 2)
  + (1 / 32 * l : k) • (A * B ^ 2 * C)
  + (3 / 128 * l : k) • B ^ 4
  + (1 / 8 * l : k) • (A * C * E)
  - (1 / 16 * l : k) • (A * D ^ 2)
  - (3 / 16 * l : k) • (B ^ 2 * E)
  - (3 / 8 * l : k) • (B * C * D)
  - (1 / 16 * l : k) • C ^ 3
  + (3 / 8 * l : k) • E ^ 2
  + (4 / 243 * alpha : k) • (A * B ^ 3)
  - (4 / 27 * alpha : k) • (B ^ 2 * D)
  - (4 / 27 * alpha : k) • (B * C ^ 2)
  + (4 / 9 * alpha : k) • (D * E)
  + (7 / 6912 * beta : k) • A ^ 5
  + (35 / 2592 * beta : k) • (A ^ 3 * C)
  - (7 / 5184 * beta : k) • (A ^ 2 * B ^ 2)
  + (7 / 144 * beta : k) • (A ^ 2 * E)
  - (7 / 216 * beta : k) • (A * B * D)
  + (7 / 432 * beta : k) • (A * C ^ 2)
  - (35 / 432 * beta : k) • (B ^ 2 * C)
  + (7 / 36 * beta : k) • (C * E)
  + (7 / 72 * beta : k) • D ^ 2
  + (35 / 10368 * delta : k) • A ^ 4
  + (5 / 144 * delta : k) • (A ^ 2 * C)
  + (5 / 432 * delta : k) • (A * B ^ 2)
  + (5 / 36 * delta : k) • (A * E)
  - (5 / 36 * delta : k) • (B * D)
  - (5 / 72 * delta : k) • C ^ 2
  - (2 / 9 * epsilon : k) • (B * C)
  + (5 / 432 * zeta : k) • A ^ 3
  + (1 / 12 * zeta : k) • (A * C)
  - (1 / 8 * zeta : k) • B ^ 2
  + (1 / 2 * zeta : k) • E
  + (1 / 3 * eta : k) • D
  + (1 / 24 * theta : k) • A ^ 2
  + (1 / 6 * theta : k) • C

set_option maxHeartbeats 64000000 in
theorem degreeZeroN1Cubic610_eq_mu_add_A_kappa
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroN1Cubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E =
      degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E +
        (1 / 6 : k) • (A * degreeZeroKappaCubic610 l alpha beta delta
          epsilon zeta eta theta A B C D E) := by
  simp only [degreeZeroN1Cubic610, degreeZeroMuCubic610,
    degreeZeroKappaCubic610]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring

theorem degreeZeroN1Cubic610_natDegree_le
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hmu : (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta
          theta A B C D E).natDegree = 0)
    (hkap : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree = 0) :
    (degreeZeroN1Cubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree ≤
      A.natDegree := by
  rw [degreeZeroN1Cubic610_eq_mu_add_A_kappa]
  have h1 : (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta
        theta A B C D E).natDegree ≤ A.natDegree := by
    rw [hmu]
    exact Nat.zero_le _
  have h2 :
      ((1 / 6 : k) • (A * degreeZeroKappaCubic610 l alpha beta delta
            epsilon zeta eta theta A B C D E)).natDegree ≤
        A.natDegree := by
    refine (natDegree_smul_le610 _ _).trans ?_
    have hmul :
        (A * degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta
              theta A B C D E).natDegree ≤
          A.natDegree +
            (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta
                theta A B C D E).natDegree :=
      natDegree_mul_le
    rw [hkap, add_zero] at hmul
    exact hmul
  exact (natDegree_add_le _ _).trans (max_le h1 h2)

def n1CubicSigma7Face610 (A B C D E : k[X]) : k[X] :=
  (5 / 81 : k) • (A * B ^ 2 * D)
  - (10 / 27 : k) • (B * C * E)
  - (5 / 27 : k) • (C ^ 2 * D)

def n1CubicLFace610 (l : k) (A : k[X]) : k[X] :=
  (77 / 248832 * l : k) • A ^ 6

set_option maxHeartbeats 32000000 in
def degreeZeroN1CubicNoL610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (5 / 81 : k) • (A * B ^ 2 * D)
  + (20 / 243 : k) • (B ^ 3 * C)
  - (10 / 27 : k) • (B * C * E)
  - (5 / 27 : k) • (B * D ^ 2)
  - (5 / 27 : k) • (C ^ 2 * D)
  + (35 / 6912 * l : k) • (A ^ 4 * C)
  - (1 / 1152 * l : k) • (A ^ 3 * B ^ 2)
  + (5 / 288 * l : k) • (A ^ 3 * E)
  - (1 / 96 * l : k) • (A ^ 2 * B * D)
  + (1 / 64 * l : k) • (A ^ 2 * C ^ 2)
  + (1 / 32 * l : k) • (A * B ^ 2 * C)
  + (3 / 128 * l : k) • B ^ 4
  + (1 / 8 * l : k) • (A * C * E)
  - (1 / 16 * l : k) • (A * D ^ 2)
  - (3 / 16 * l : k) • (B ^ 2 * E)
  - (3 / 8 * l : k) • (B * C * D)
  - (1 / 16 * l : k) • C ^ 3
  + (3 / 8 * l : k) • E ^ 2
  + (4 / 243 * alpha : k) • (A * B ^ 3)
  - (4 / 27 * alpha : k) • (B ^ 2 * D)
  - (4 / 27 * alpha : k) • (B * C ^ 2)
  + (4 / 9 * alpha : k) • (D * E)
  + (7 / 6912 * beta : k) • A ^ 5
  + (35 / 2592 * beta : k) • (A ^ 3 * C)
  - (7 / 5184 * beta : k) • (A ^ 2 * B ^ 2)
  + (7 / 144 * beta : k) • (A ^ 2 * E)
  - (7 / 216 * beta : k) • (A * B * D)
  + (7 / 432 * beta : k) • (A * C ^ 2)
  - (35 / 432 * beta : k) • (B ^ 2 * C)
  + (7 / 36 * beta : k) • (C * E)
  + (7 / 72 * beta : k) • D ^ 2
  + (35 / 10368 * delta : k) • A ^ 4
  + (5 / 144 * delta : k) • (A ^ 2 * C)
  + (5 / 432 * delta : k) • (A * B ^ 2)
  + (5 / 36 * delta : k) • (A * E)
  - (5 / 36 * delta : k) • (B * D)
  - (5 / 72 * delta : k) • C ^ 2
  - (2 / 9 * epsilon : k) • (B * C)
  + (5 / 432 * zeta : k) • A ^ 3
  + (1 / 12 * zeta : k) • (A * C)
  - (1 / 8 * zeta : k) • B ^ 2
  + (1 / 2 * zeta : k) • E
  + (1 / 3 * eta : k) • D
  + (1 / 24 * theta : k) • A ^ 2
  + (1 / 6 * theta : k) • C

set_option maxHeartbeats 32000000 in
theorem degreeZeroN1Cubic610_eq_L_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroN1Cubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E =
      n1CubicLFace610 l A +
        degreeZeroN1CubicNoL610 l alpha beta delta epsilon zeta eta
          theta A B C D E := by
  simp only [degreeZeroN1Cubic610, n1CubicLFace610, degreeZeroN1CubicNoL610]
  all_goals module

end CubicN1_610

/-! ## The 13 empty σ-argmin cones -/

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

/- σ-cone B -/

def kappaCubicSigmaFaceB610 (A B C D E : k[X]) : k[X] :=
  (5 / 243 : k) • (A * B ^ 3)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaCubicNoSigmaB610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (-(5 / 27 : k)) • (B ^ 2 * D)
  - (5 / 27 : k) • (B * C ^ 2)
  + (10 / 9 : k) • (D * E)
  + (7 / 6912 * l : k) • A ^ 5
  + (5 / 288 * l : k) • (A ^ 3 * C)
  - (1 / 192 * l : k) • (A ^ 2 * B ^ 2)
  + (1 / 16 * l : k) • (A ^ 2 * E)
  - (1 / 8 * l : k) • (A * B * D)
  + (1 / 16 * l : k) • (A * C ^ 2)
  - (3 / 16 * l : k) • (B ^ 2 * C)
  + (3 / 4 * l : k) • (C * E)
  + (3 / 8 * l : k) • D ^ 2
  - (4 / 81 * alpha : k) • B ^ 3
  + (4 / 9 * alpha : k) • (B * E)
  + (4 / 9 * alpha : k) • (C * D)
  + (35 / 10368 * beta : k) • A ^ 4
  + (7 / 144 * beta : k) • (A ^ 2 * C)
  - (7 / 432 * beta : k) • (A * B ^ 2)
  + (7 / 36 * beta : k) • (A * E)
  + (7 / 36 * beta : k) • (B * D)
  + (7 / 72 * beta : k) • C ^ 2
  + (5 / 432 * delta : k) • A ^ 3
  + (5 / 36 * delta : k) • (A * C)
  - (5 / 72 * delta : k) • B ^ 2
  + (5 / 6 * delta : k) • E
  + (2 / 3 * epsilon : k) • D
  + (1 / 24 * zeta : k) • A ^ 2
  + (1 / 2 * zeta : k) • C
  + (1 / 3 * eta : k) • B
  + (1 / 6 * theta : k) • A

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaCubic610_eq_sigmaB_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      kappaCubicSigmaFaceB610 A B C D E +
        degreeZeroKappaCubicNoSigmaB610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroKappaCubic610, kappaCubicSigmaFaceB610, degreeZeroKappaCubicNoSigmaB610]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaCubicNoSigmaB610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicSigmaConeB610 A B C D E) :
    (degreeZeroKappaCubicNoSigmaB610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  have hs0 : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt h0
  have hs1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt h1
  have hs2 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt h2
  have hs3 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt h3
  have hs4 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt h4
  have hs5 : 0 + 1 ≤ B.natDegree := Nat.succ_le_of_lt h5
  have hs6 : 2 * C.natDegree + 1 ≤ A.natDegree + 2 * B.natDegree := Nat.succ_le_of_lt h6
  have hs7 : 4 * D.natDegree + 1 ≤ A.natDegree + 6 * B.natDegree := Nat.succ_le_of_lt h7
  have hs8 : 4 * E.natDegree + 1 ≤ 3 * A.natDegree + 6 * B.natDegree := Nat.succ_le_of_lt h8
  have hs9 : 4 * A.natDegree + 1 ≤ 3 * B.natDegree := Nat.succ_le_of_lt h9
  simp only [degreeZeroKappaCubicNoSigmaB610]
  compute_degree
  omega

theorem cubicSigmaCone_B_impossible
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicSigmaConeB610 A B C D E)
    (hdeg : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree =
        0) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    omega
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    omega
  have hc : (5 / 243 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (kappaCubicSigmaFaceB610 A B C D E).natDegree = A.natDegree + 3 * B.natDegree := by
    simp only [kappaCubicSigmaFaceB610]
    rw [natDegree_smul _ hc, natDegree_mul hAne (pow_ne_zero 3 hBne), natDegree_pow]
  have hrest := degreeZeroKappaCubicNoSigmaB610_natDegree_lt l alpha beta delta epsilon
      zeta eta theta A B C D E hcone
  rw [degreeZeroKappaCubic610_eq_sigmaB_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  omega

/- σ-cone C -/

def lambdaCubicSigmaFaceC610 (A B C D E : k[X]) : k[X] :=
  (-(5 / 81 : k)) • C ^ 3

set_option maxHeartbeats 16000000 in
def degreeZeroLambdaCubicNoSigmaC610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (5 / 81 : k) • (A * B ^ 2 * C)
  + (5 / 243 : k) • B ^ 4
  - (5 / 27 : k) • (A * D ^ 2)
  - (5 / 27 : k) • (B ^ 2 * E)
  - (10 / 27 : k) • (B * C * D)
  + (5 / 9 : k) • E ^ 2
  - (5 / 6912 * l : k) • (A ^ 4 * B)
  - (1 / 288 * l : k) • (A ^ 3 * D)
  - (1 / 96 * l : k) • (A ^ 2 * B * C)
  + (1 / 32 * l : k) • (A * B ^ 3)
  - (1 / 8 * l : k) • (A * B * E)
  - (1 / 8 * l : k) • (A * C * D)
  - (3 / 16 * l : k) • (B ^ 2 * D)
  - (3 / 16 * l : k) • (B * C ^ 2)
  + (3 / 4 * l : k) • (D * E)
  - (4 / 27 * alpha : k) • (A * B * D)
  - (4 / 27 * alpha : k) • (B ^ 2 * C)
  + (4 / 9 * alpha : k) • (C * E)
  + (2 / 9 * alpha : k) • D ^ 2
  - (7 / 2592 * beta : k) • (A ^ 3 * B)
  - (7 / 432 * beta : k) • (A ^ 2 * D)
  - (7 / 216 * beta : k) • (A * B * C)
  - (35 / 1296 * beta : k) • B ^ 3
  + (7 / 36 * beta : k) • (B * E)
  + (7 / 36 * beta : k) • (C * D)
  - (5 / 432 * delta : k) • (A ^ 2 * B)
  - (5 / 36 * delta : k) • (A * D)
  - (5 / 36 * delta : k) • (B * C)
  - (1 / 9 * epsilon : k) • B ^ 2
  + (2 / 3 * epsilon : k) • E
  - (1 / 12 * zeta : k) • (A * B)
  + (1 / 2 * zeta : k) • D
  + (1 / 3 * eta : k) • C
  + (1 / 6 * theta : k) • B

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaCubic610_eq_sigmaC_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      lambdaCubicSigmaFaceC610 A B C D E +
        degreeZeroLambdaCubicNoSigmaC610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroLambdaCubic610, lambdaCubicSigmaFaceC610, degreeZeroLambdaCubicNoSigmaC610]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaCubicNoSigmaC610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicSigmaConeC610 A B C D E) :
    (degreeZeroLambdaCubicNoSigmaC610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      3 * C.natDegree := by
  rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  have hs0 : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt h0
  have hs1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt h1
  have hs2 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt h2
  have hs3 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt h3
  have hs4 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt h4
  have hs5 : 0 + 1 ≤ C.natDegree := Nat.succ_le_of_lt h5
  have hs6 : A.natDegree + 2 * B.natDegree + 1 ≤ 2 * C.natDegree := Nat.succ_le_of_lt h6
  have hs7 : A.natDegree + 2 * D.natDegree + 1 ≤ 3 * C.natDegree := Nat.succ_le_of_lt h7
  have hs8 : 2 * E.natDegree + 1 ≤ 3 * C.natDegree := Nat.succ_le_of_lt h8
  have hs9 : 11 * A.natDegree + 1 ≤ 6 * C.natDegree := Nat.succ_le_of_lt h9
  simp only [degreeZeroLambdaCubicNoSigmaC610]
  compute_degree
  omega

theorem cubicSigmaCone_C_impossible
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicSigmaConeC610 A B C D E)
    (hdeg : (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree =
        0) :
    False := by
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    omega
  have hc : (-(5 / 81 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead : (lambdaCubicSigmaFaceC610 A B C D E).natDegree = 3 * C.natDegree := by
    simp only [lambdaCubicSigmaFaceC610]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest := degreeZeroLambdaCubicNoSigmaC610_natDegree_lt l alpha beta delta epsilon
      zeta eta theta A B C D E hcone
  rw [degreeZeroLambdaCubic610_eq_sigmaC_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  omega

/- σ-cone D -/

def lambdaCubicSigmaFaceD610 (A B C D E : k[X]) : k[X] :=
  (-(5 / 27 : k)) • (A * D ^ 2)

set_option maxHeartbeats 16000000 in
def degreeZeroLambdaCubicNoSigmaD610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (5 / 81 : k) • (A * B ^ 2 * C)
  + (5 / 243 : k) • B ^ 4
  - (5 / 27 : k) • (B ^ 2 * E)
  - (10 / 27 : k) • (B * C * D)
  - (5 / 81 : k) • C ^ 3
  + (5 / 9 : k) • E ^ 2
  - (5 / 6912 * l : k) • (A ^ 4 * B)
  - (1 / 288 * l : k) • (A ^ 3 * D)
  - (1 / 96 * l : k) • (A ^ 2 * B * C)
  + (1 / 32 * l : k) • (A * B ^ 3)
  - (1 / 8 * l : k) • (A * B * E)
  - (1 / 8 * l : k) • (A * C * D)
  - (3 / 16 * l : k) • (B ^ 2 * D)
  - (3 / 16 * l : k) • (B * C ^ 2)
  + (3 / 4 * l : k) • (D * E)
  - (4 / 27 * alpha : k) • (A * B * D)
  - (4 / 27 * alpha : k) • (B ^ 2 * C)
  + (4 / 9 * alpha : k) • (C * E)
  + (2 / 9 * alpha : k) • D ^ 2
  - (7 / 2592 * beta : k) • (A ^ 3 * B)
  - (7 / 432 * beta : k) • (A ^ 2 * D)
  - (7 / 216 * beta : k) • (A * B * C)
  - (35 / 1296 * beta : k) • B ^ 3
  + (7 / 36 * beta : k) • (B * E)
  + (7 / 36 * beta : k) • (C * D)
  - (5 / 432 * delta : k) • (A ^ 2 * B)
  - (5 / 36 * delta : k) • (A * D)
  - (5 / 36 * delta : k) • (B * C)
  - (1 / 9 * epsilon : k) • B ^ 2
  + (2 / 3 * epsilon : k) • E
  - (1 / 12 * zeta : k) • (A * B)
  + (1 / 2 * zeta : k) • D
  + (1 / 3 * eta : k) • C
  + (1 / 6 * theta : k) • B

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaCubic610_eq_sigmaD_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      lambdaCubicSigmaFaceD610 A B C D E +
        degreeZeroLambdaCubicNoSigmaD610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroLambdaCubic610, lambdaCubicSigmaFaceD610, degreeZeroLambdaCubicNoSigmaD610]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaCubicNoSigmaD610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicSigmaConeD610 A B C D E) :
    (degreeZeroLambdaCubicNoSigmaD610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      A.natDegree + 2 * D.natDegree := by
  rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  have hs0 : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt h0
  have hs1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt h1
  have hs2 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt h2
  have hs3 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt h3
  have hs4 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt h4
  have hs5 : 0 + 1 ≤ D.natDegree := Nat.succ_le_of_lt h5
  have hs6 : A.natDegree + 6 * B.natDegree + 1 ≤ 4 * D.natDegree := Nat.succ_le_of_lt h6
  have hs7 : 3 * C.natDegree + 1 ≤ A.natDegree + 2 * D.natDegree := Nat.succ_le_of_lt h7
  have hs8 : 2 * E.natDegree + 1 ≤ A.natDegree + 2 * D.natDegree := Nat.succ_le_of_lt h8
  have hs9 : 9 * A.natDegree + 1 ≤ 4 * D.natDegree := Nat.succ_le_of_lt h9
  simp only [degreeZeroLambdaCubicNoSigmaD610]
  compute_degree
  omega

theorem cubicSigmaCone_D_impossible
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicSigmaConeD610 A B C D E)
    (hdeg : (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree =
        0) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    omega
  have hc : (-(5 / 27 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead : (lambdaCubicSigmaFaceD610 A B C D E).natDegree = A.natDegree + 2 * D.natDegree := by
    simp only [lambdaCubicSigmaFaceD610]
    rw [natDegree_smul _ hc, natDegree_mul hAne (pow_ne_zero 2 hDne), natDegree_pow]
  have hrest := degreeZeroLambdaCubicNoSigmaD610_natDegree_lt l alpha beta delta epsilon
      zeta eta theta A B C D E hcone
  rw [degreeZeroLambdaCubic610_eq_sigmaD_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  omega

/- σ-cone E -/

def lambdaCubicSigmaFaceE610 (A B C D E : k[X]) : k[X] :=
  (5 / 9 : k) • E ^ 2

set_option maxHeartbeats 16000000 in
def degreeZeroLambdaCubicNoSigmaE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (5 / 81 : k) • (A * B ^ 2 * C)
  + (5 / 243 : k) • B ^ 4
  - (5 / 27 : k) • (A * D ^ 2)
  - (5 / 27 : k) • (B ^ 2 * E)
  - (10 / 27 : k) • (B * C * D)
  - (5 / 81 : k) • C ^ 3
  - (5 / 6912 * l : k) • (A ^ 4 * B)
  - (1 / 288 * l : k) • (A ^ 3 * D)
  - (1 / 96 * l : k) • (A ^ 2 * B * C)
  + (1 / 32 * l : k) • (A * B ^ 3)
  - (1 / 8 * l : k) • (A * B * E)
  - (1 / 8 * l : k) • (A * C * D)
  - (3 / 16 * l : k) • (B ^ 2 * D)
  - (3 / 16 * l : k) • (B * C ^ 2)
  + (3 / 4 * l : k) • (D * E)
  - (4 / 27 * alpha : k) • (A * B * D)
  - (4 / 27 * alpha : k) • (B ^ 2 * C)
  + (4 / 9 * alpha : k) • (C * E)
  + (2 / 9 * alpha : k) • D ^ 2
  - (7 / 2592 * beta : k) • (A ^ 3 * B)
  - (7 / 432 * beta : k) • (A ^ 2 * D)
  - (7 / 216 * beta : k) • (A * B * C)
  - (35 / 1296 * beta : k) • B ^ 3
  + (7 / 36 * beta : k) • (B * E)
  + (7 / 36 * beta : k) • (C * D)
  - (5 / 432 * delta : k) • (A ^ 2 * B)
  - (5 / 36 * delta : k) • (A * D)
  - (5 / 36 * delta : k) • (B * C)
  - (1 / 9 * epsilon : k) • B ^ 2
  + (2 / 3 * epsilon : k) • E
  - (1 / 12 * zeta : k) • (A * B)
  + (1 / 2 * zeta : k) • D
  + (1 / 3 * eta : k) • C
  + (1 / 6 * theta : k) • B

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaCubic610_eq_sigmaE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      lambdaCubicSigmaFaceE610 A B C D E +
        degreeZeroLambdaCubicNoSigmaE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroLambdaCubic610, lambdaCubicSigmaFaceE610, degreeZeroLambdaCubicNoSigmaE610]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaCubicNoSigmaE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicSigmaConeE610 A B C D E) :
    (degreeZeroLambdaCubicNoSigmaE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      2 * E.natDegree := by
  rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  have hs0 : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt h0
  have hs1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt h1
  have hs2 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt h2
  have hs3 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt h3
  have hs4 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt h4
  have hs5 : 0 + 1 ≤ E.natDegree := Nat.succ_le_of_lt h5
  have hs6 : 3 * A.natDegree + 6 * B.natDegree + 1 ≤ 4 * E.natDegree := Nat.succ_le_of_lt h6
  have hs7 : 3 * C.natDegree + 1 ≤ 2 * E.natDegree := Nat.succ_le_of_lt h7
  have hs8 : A.natDegree + 2 * D.natDegree + 1 ≤ 2 * E.natDegree := Nat.succ_le_of_lt h8
  have hs9 : 11 * A.natDegree + 1 ≤ 4 * E.natDegree := Nat.succ_le_of_lt h9
  simp only [degreeZeroLambdaCubicNoSigmaE610]
  compute_degree
  omega

theorem cubicSigmaCone_E_impossible
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicSigmaConeE610 A B C D E)
    (hdeg : (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree =
        0) :
    False := by
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    omega
  have hc : (5 / 9 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (lambdaCubicSigmaFaceE610 A B C D E).natDegree = 2 * E.natDegree := by
    simp only [lambdaCubicSigmaFaceE610]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest := degreeZeroLambdaCubicNoSigmaE610_natDegree_lt l alpha beta delta epsilon
      zeta eta theta A B C D E hcone
  rw [degreeZeroLambdaCubic610_eq_sigmaE_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  omega

/- σ-cone BC -/

def kappaCubicSigmaInnerBC610 (a b c : k) : k :=
  5 * a * b ^ 3 + (-45 : k) * b * c ^ 2

def lambdaCubicSigmaInnerBC610 (a b c : k) : k :=
  5 * a * b ^ 2 * c + (-5 : k) * c ^ 3

set_option maxHeartbeats 32000000 in
theorem cubicSigmaInner_BC_identity
    (a b c : k) :
    ((-1 / 40 : k) * a * b * c) * kappaCubicSigmaInnerBC610 a b c +
      ((1 / 40 : k) * a * b ^ 2 + (-1 / 5 : k) * c ^ 2) * lambdaCubicSigmaInnerBC610 a b c =
      c ^ 5 := by
  simp only [kappaCubicSigmaInnerBC610, lambdaCubicSigmaInnerBC610]
  ring

def kappaCubicSigmaFaceBC610 (A B C D E : k[X]) : k[X] :=
  (5 / 243 : k) • (A * B ^ 3)
  - (5 / 27 : k) • (B * C ^ 2)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaCubicNoSigmaBC610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (-(5 / 27 : k)) • (B ^ 2 * D)
  + (10 / 9 : k) • (D * E)
  + (7 / 6912 * l : k) • A ^ 5
  + (5 / 288 * l : k) • (A ^ 3 * C)
  - (1 / 192 * l : k) • (A ^ 2 * B ^ 2)
  + (1 / 16 * l : k) • (A ^ 2 * E)
  - (1 / 8 * l : k) • (A * B * D)
  + (1 / 16 * l : k) • (A * C ^ 2)
  - (3 / 16 * l : k) • (B ^ 2 * C)
  + (3 / 4 * l : k) • (C * E)
  + (3 / 8 * l : k) • D ^ 2
  - (4 / 81 * alpha : k) • B ^ 3
  + (4 / 9 * alpha : k) • (B * E)
  + (4 / 9 * alpha : k) • (C * D)
  + (35 / 10368 * beta : k) • A ^ 4
  + (7 / 144 * beta : k) • (A ^ 2 * C)
  - (7 / 432 * beta : k) • (A * B ^ 2)
  + (7 / 36 * beta : k) • (A * E)
  + (7 / 36 * beta : k) • (B * D)
  + (7 / 72 * beta : k) • C ^ 2
  + (5 / 432 * delta : k) • A ^ 3
  + (5 / 36 * delta : k) • (A * C)
  - (5 / 72 * delta : k) • B ^ 2
  + (5 / 6 * delta : k) • E
  + (2 / 3 * epsilon : k) • D
  + (1 / 24 * zeta : k) • A ^ 2
  + (1 / 2 * zeta : k) • C
  + (1 / 3 * eta : k) • B
  + (1 / 6 * theta : k) • A

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaCubic610_eq_sigmaBC_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      kappaCubicSigmaFaceBC610 A B C D E +
        degreeZeroKappaCubicNoSigmaBC610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroKappaCubic610, kappaCubicSigmaFaceBC610, degreeZeroKappaCubicNoSigmaBC610]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaCubicNoSigmaBC610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicSigmaConeBC610 A B C D E) :
    (degreeZeroKappaCubicNoSigmaBC610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  have hs0 : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt h0
  have hs1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt h1
  have hs2 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt h2
  have hs3 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt h3
  have hs4 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt h4
  have hs5 : 0 + 1 ≤ B.natDegree := Nat.succ_le_of_lt h5
  have hs6 : 0 + 1 ≤ C.natDegree := Nat.succ_le_of_lt h6
  have hs8 : 4 * D.natDegree + 1 ≤ A.natDegree + 6 * B.natDegree := Nat.succ_le_of_lt h8
  have hs9 : 4 * E.natDegree + 1 ≤ 3 * A.natDegree + 6 * B.natDegree := Nat.succ_le_of_lt h9
  have hs10 : 4 * A.natDegree + 1 ≤ 3 * B.natDegree := Nat.succ_le_of_lt h10
  simp only [degreeZeroKappaCubicNoSigmaBC610]
  compute_degree
  omega

theorem kappaCubicSigmaFaceBC610_coeff_top
    {A B C D E : k[X]}
    (hcone : CubicSigmaConeBC610 A B C D E)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    : (kappaCubicSigmaFaceBC610 A B C D E).coeff (A.natDegree + 3 * B.natDegree) =
      (1 / 243 : k) * kappaCubicSigmaInnerBC610 A.leadingCoeff B.leadingCoeff C.leadingCoeff := by
  rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  simp only [kappaCubicSigmaFaceBC610, kappaCubicSigmaInnerBC610, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
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

def lambdaCubicSigmaFaceBC610 (A B C D E : k[X]) : k[X] :=
  (5 / 81 : k) • (A * B ^ 2 * C)
  - (5 / 81 : k) • C ^ 3

set_option maxHeartbeats 16000000 in
def degreeZeroLambdaCubicNoSigmaBC610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (5 / 243 : k) • B ^ 4
  - (5 / 27 : k) • (A * D ^ 2)
  - (5 / 27 : k) • (B ^ 2 * E)
  - (10 / 27 : k) • (B * C * D)
  + (5 / 9 : k) • E ^ 2
  - (5 / 6912 * l : k) • (A ^ 4 * B)
  - (1 / 288 * l : k) • (A ^ 3 * D)
  - (1 / 96 * l : k) • (A ^ 2 * B * C)
  + (1 / 32 * l : k) • (A * B ^ 3)
  - (1 / 8 * l : k) • (A * B * E)
  - (1 / 8 * l : k) • (A * C * D)
  - (3 / 16 * l : k) • (B ^ 2 * D)
  - (3 / 16 * l : k) • (B * C ^ 2)
  + (3 / 4 * l : k) • (D * E)
  - (4 / 27 * alpha : k) • (A * B * D)
  - (4 / 27 * alpha : k) • (B ^ 2 * C)
  + (4 / 9 * alpha : k) • (C * E)
  + (2 / 9 * alpha : k) • D ^ 2
  - (7 / 2592 * beta : k) • (A ^ 3 * B)
  - (7 / 432 * beta : k) • (A ^ 2 * D)
  - (7 / 216 * beta : k) • (A * B * C)
  - (35 / 1296 * beta : k) • B ^ 3
  + (7 / 36 * beta : k) • (B * E)
  + (7 / 36 * beta : k) • (C * D)
  - (5 / 432 * delta : k) • (A ^ 2 * B)
  - (5 / 36 * delta : k) • (A * D)
  - (5 / 36 * delta : k) • (B * C)
  - (1 / 9 * epsilon : k) • B ^ 2
  + (2 / 3 * epsilon : k) • E
  - (1 / 12 * zeta : k) • (A * B)
  + (1 / 2 * zeta : k) • D
  + (1 / 3 * eta : k) • C
  + (1 / 6 * theta : k) • B

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaCubic610_eq_sigmaBC_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      lambdaCubicSigmaFaceBC610 A B C D E +
        degreeZeroLambdaCubicNoSigmaBC610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroLambdaCubic610, lambdaCubicSigmaFaceBC610, degreeZeroLambdaCubicNoSigmaBC610]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaCubicNoSigmaBC610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicSigmaConeBC610 A B C D E) :
    (degreeZeroLambdaCubicNoSigmaBC610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      A.natDegree + 2 * B.natDegree + C.natDegree := by
  rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  have hs0 : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt h0
  have hs1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt h1
  have hs2 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt h2
  have hs3 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt h3
  have hs4 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt h4
  have hs5 : 0 + 1 ≤ B.natDegree := Nat.succ_le_of_lt h5
  have hs6 : 0 + 1 ≤ C.natDegree := Nat.succ_le_of_lt h6
  have hs8 : 4 * D.natDegree + 1 ≤ A.natDegree + 6 * B.natDegree := Nat.succ_le_of_lt h8
  have hs9 : 4 * E.natDegree + 1 ≤ 3 * A.natDegree + 6 * B.natDegree := Nat.succ_le_of_lt h9
  have hs10 : 4 * A.natDegree + 1 ≤ 3 * B.natDegree := Nat.succ_le_of_lt h10
  simp only [degreeZeroLambdaCubicNoSigmaBC610]
  compute_degree
  omega

theorem lambdaCubicSigmaFaceBC610_coeff_top
    {A B C D E : k[X]}
    (hcone : CubicSigmaConeBC610 A B C D E)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    : (lambdaCubicSigmaFaceBC610 A B C D E).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      (1 / 81 : k) * lambdaCubicSigmaInnerBC610 A.leadingCoeff B.leadingCoeff C.leadingCoeff := by
  rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  simp only [lambdaCubicSigmaFaceBC610, lambdaCubicSigmaInnerBC610, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_AB2C : ((A * B ^ 2 * C)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hCne, natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow]
  have hcf_AB2C : ((A * B ^ 2 * C)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff := by
    rw [← hdeg_AB2C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_C3 : (C ^ 3).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_C3 : (C ^ 3).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      C.leadingCoeff ^ 3 := by
    rw [← hdeg_C3, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_AB2C, hcf_C3]
  ring

set_option maxHeartbeats 16000000 in
theorem cubicSigmaCone_BC_impossible
    {j t : k}
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicSigmaConeBC610 A B C D E)
    (hlam : (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree =
        0)
    (hkap : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree =
        0)
    (hmu : (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta
          theta A B C D E).natDegree =
        0)
    (homi : (degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree =
        0)
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
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    omega
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    omega

  have hprimdeg :
      (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C610 _ (j / t) hjdiv hder

  have hkappainner : kappaCubicSigmaInnerBC610 A.leadingCoeff B.leadingCoeff C.leadingCoeff = 0 := by
    have hrest := degreeZeroKappaCubicNoSigmaBC610_natDegree_lt l alpha beta delta
        epsilon zeta eta theta A B C D E hcone
    have hct := kappaCubicSigmaFaceBC610_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne)
    have hz : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hkap]
      rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
      omega
    rw [degreeZeroKappaCubic610_eq_sigmaBC_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 243 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h

  have hlambdainner : lambdaCubicSigmaInnerBC610 A.leadingCoeff B.leadingCoeff C.leadingCoeff = 0 := by
    have hrest := degreeZeroLambdaCubicNoSigmaBC610_natDegree_lt l alpha beta delta
        epsilon zeta eta theta A B C D E hcone
    have hct := lambdaCubicSigmaFaceBC610_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne)
    have hz : (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hlam]
      rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
      omega
    rw [degreeZeroLambdaCubic610_eq_sigmaBC_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 81 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h

  have hid := cubicSigmaInner_BC_identity A.leadingCoeff B.leadingCoeff C.leadingCoeff
  have hpow : C.leadingCoeff ^ 5 = 0 := by
    rw [hkappainner, hlambdainner] at hid
    simpa using hid.symm
  have hlc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  exact hlc ((pow_eq_zero_iff (by decide : (5 : ℕ) ≠ 0)).mp hpow)

/- σ-cone BD -/

def kappaCubicSigmaFaceBD610 (A B C D E : k[X]) : k[X] :=
  (5 / 243 : k) • (A * B ^ 3)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaCubicNoSigmaBD610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (-(5 / 27 : k)) • (B ^ 2 * D)
  - (5 / 27 : k) • (B * C ^ 2)
  + (10 / 9 : k) • (D * E)
  + (7 / 6912 * l : k) • A ^ 5
  + (5 / 288 * l : k) • (A ^ 3 * C)
  - (1 / 192 * l : k) • (A ^ 2 * B ^ 2)
  + (1 / 16 * l : k) • (A ^ 2 * E)
  - (1 / 8 * l : k) • (A * B * D)
  + (1 / 16 * l : k) • (A * C ^ 2)
  - (3 / 16 * l : k) • (B ^ 2 * C)
  + (3 / 4 * l : k) • (C * E)
  + (3 / 8 * l : k) • D ^ 2
  - (4 / 81 * alpha : k) • B ^ 3
  + (4 / 9 * alpha : k) • (B * E)
  + (4 / 9 * alpha : k) • (C * D)
  + (35 / 10368 * beta : k) • A ^ 4
  + (7 / 144 * beta : k) • (A ^ 2 * C)
  - (7 / 432 * beta : k) • (A * B ^ 2)
  + (7 / 36 * beta : k) • (A * E)
  + (7 / 36 * beta : k) • (B * D)
  + (7 / 72 * beta : k) • C ^ 2
  + (5 / 432 * delta : k) • A ^ 3
  + (5 / 36 * delta : k) • (A * C)
  - (5 / 72 * delta : k) • B ^ 2
  + (5 / 6 * delta : k) • E
  + (2 / 3 * epsilon : k) • D
  + (1 / 24 * zeta : k) • A ^ 2
  + (1 / 2 * zeta : k) • C
  + (1 / 3 * eta : k) • B
  + (1 / 6 * theta : k) • A

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaCubic610_eq_sigmaBD_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      kappaCubicSigmaFaceBD610 A B C D E +
        degreeZeroKappaCubicNoSigmaBD610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroKappaCubic610, kappaCubicSigmaFaceBD610, degreeZeroKappaCubicNoSigmaBD610]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaCubicNoSigmaBD610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicSigmaConeBD610 A B C D E) :
    (degreeZeroKappaCubicNoSigmaBD610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  have hs0 : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt h0
  have hs1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt h1
  have hs2 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt h2
  have hs3 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt h3
  have hs4 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt h4
  have hs5 : 0 + 1 ≤ B.natDegree := Nat.succ_le_of_lt h5
  have hs6 : 0 + 1 ≤ D.natDegree := Nat.succ_le_of_lt h6
  have hs8 : 2 * C.natDegree + 1 ≤ A.natDegree + 2 * B.natDegree := Nat.succ_le_of_lt h8
  have hs9 : 4 * E.natDegree + 1 ≤ 3 * A.natDegree + 6 * B.natDegree := Nat.succ_le_of_lt h9
  have hs10 : 4 * A.natDegree + 1 ≤ 3 * B.natDegree := Nat.succ_le_of_lt h10
  simp only [degreeZeroKappaCubicNoSigmaBD610]
  compute_degree
  omega

theorem cubicSigmaCone_BD_impossible
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicSigmaConeBD610 A B C D E)
    (hdeg : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree =
        0) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    omega
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    omega
  have hc : (5 / 243 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (kappaCubicSigmaFaceBD610 A B C D E).natDegree = A.natDegree + 3 * B.natDegree := by
    simp only [kappaCubicSigmaFaceBD610]
    rw [natDegree_smul _ hc, natDegree_mul hAne (pow_ne_zero 3 hBne), natDegree_pow]
  have hrest := degreeZeroKappaCubicNoSigmaBD610_natDegree_lt l alpha beta delta epsilon
      zeta eta theta A B C D E hcone
  rw [degreeZeroKappaCubic610_eq_sigmaBD_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  omega

/- σ-cone BE -/

def kappaCubicSigmaFaceBE610 (A B C D E : k[X]) : k[X] :=
  (5 / 243 : k) • (A * B ^ 3)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaCubicNoSigmaBE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (-(5 / 27 : k)) • (B ^ 2 * D)
  - (5 / 27 : k) • (B * C ^ 2)
  + (10 / 9 : k) • (D * E)
  + (7 / 6912 * l : k) • A ^ 5
  + (5 / 288 * l : k) • (A ^ 3 * C)
  - (1 / 192 * l : k) • (A ^ 2 * B ^ 2)
  + (1 / 16 * l : k) • (A ^ 2 * E)
  - (1 / 8 * l : k) • (A * B * D)
  + (1 / 16 * l : k) • (A * C ^ 2)
  - (3 / 16 * l : k) • (B ^ 2 * C)
  + (3 / 4 * l : k) • (C * E)
  + (3 / 8 * l : k) • D ^ 2
  - (4 / 81 * alpha : k) • B ^ 3
  + (4 / 9 * alpha : k) • (B * E)
  + (4 / 9 * alpha : k) • (C * D)
  + (35 / 10368 * beta : k) • A ^ 4
  + (7 / 144 * beta : k) • (A ^ 2 * C)
  - (7 / 432 * beta : k) • (A * B ^ 2)
  + (7 / 36 * beta : k) • (A * E)
  + (7 / 36 * beta : k) • (B * D)
  + (7 / 72 * beta : k) • C ^ 2
  + (5 / 432 * delta : k) • A ^ 3
  + (5 / 36 * delta : k) • (A * C)
  - (5 / 72 * delta : k) • B ^ 2
  + (5 / 6 * delta : k) • E
  + (2 / 3 * epsilon : k) • D
  + (1 / 24 * zeta : k) • A ^ 2
  + (1 / 2 * zeta : k) • C
  + (1 / 3 * eta : k) • B
  + (1 / 6 * theta : k) • A

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaCubic610_eq_sigmaBE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      kappaCubicSigmaFaceBE610 A B C D E +
        degreeZeroKappaCubicNoSigmaBE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroKappaCubic610, kappaCubicSigmaFaceBE610, degreeZeroKappaCubicNoSigmaBE610]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaCubicNoSigmaBE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicSigmaConeBE610 A B C D E) :
    (degreeZeroKappaCubicNoSigmaBE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  have hs0 : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt h0
  have hs1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt h1
  have hs2 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt h2
  have hs3 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt h3
  have hs4 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt h4
  have hs5 : 0 + 1 ≤ B.natDegree := Nat.succ_le_of_lt h5
  have hs6 : 0 + 1 ≤ E.natDegree := Nat.succ_le_of_lt h6
  have hs8 : 2 * C.natDegree + 1 ≤ A.natDegree + 2 * B.natDegree := Nat.succ_le_of_lt h8
  have hs9 : 4 * D.natDegree + 1 ≤ A.natDegree + 6 * B.natDegree := Nat.succ_le_of_lt h9
  have hs10 : 4 * A.natDegree + 1 ≤ 3 * B.natDegree := Nat.succ_le_of_lt h10
  simp only [degreeZeroKappaCubicNoSigmaBE610]
  compute_degree
  omega

theorem cubicSigmaCone_BE_impossible
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicSigmaConeBE610 A B C D E)
    (hdeg : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree =
        0) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    omega
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    omega
  have hc : (5 / 243 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (kappaCubicSigmaFaceBE610 A B C D E).natDegree = A.natDegree + 3 * B.natDegree := by
    simp only [kappaCubicSigmaFaceBE610]
    rw [natDegree_smul _ hc, natDegree_mul hAne (pow_ne_zero 3 hBne), natDegree_pow]
  have hrest := degreeZeroKappaCubicNoSigmaBE610_natDegree_lt l alpha beta delta epsilon
      zeta eta theta A B C D E hcone
  rw [degreeZeroKappaCubic610_eq_sigmaBE_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  omega

/- σ-cone CE -/

def omicronCubicSigmaFaceCE610 (A B C D E : k[X]) : k[X] :=
  (-(5 / 27 : k)) • (C ^ 2 * E)

set_option maxHeartbeats 32000000 in
def degreeZeroOmicronCubicNoSigmaCE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (-(5 / 486 : k)) • (A * B ^ 4)
  + (5 / 81 : k) • (A * B ^ 2 * E)
  + (10 / 81 : k) • (A * B * C * D)
  + (25 / 486 : k) • (B ^ 3 * D)
  + (5 / 54 : k) • (B ^ 2 * C ^ 2)
  - (5 / 27 : k) • (B * D * E)
  - (5 / 27 : k) • (C * D ^ 2)
  - (5 / 6912 * l : k) • (A ^ 4 * D)
  + (1 / 864 * l : k) • (A ^ 3 * B * C)
  - (1 / 288 * l : k) • (A ^ 2 * B ^ 3)
  - (1 / 96 * l : k) • (A ^ 2 * C * D)
  + (7 / 96 * l : k) • (A * B ^ 2 * D)
  + (1 / 24 * l : k) • (A * B * C ^ 2)
  + (1 / 16 * l : k) • (B ^ 3 * C)
  - (1 / 8 * l : k) • (A * D * E)
  - (1 / 4 * l : k) • (B * C * E)
  - (1 / 8 * l : k) • (B * D ^ 2)
  - (3 / 16 * l : k) • (C ^ 2 * D)
  + (4 / 81 * alpha : k) • (A * B ^ 2 * C)
  + (1 / 81 * alpha : k) • B ^ 4
  - (2 / 27 * alpha : k) • (A * D ^ 2)
  - (2 / 27 * alpha : k) • (B ^ 2 * E)
  - (2 / 9 * alpha : k) • (B * C * D)
  - (4 / 81 * alpha : k) • C ^ 3
  + (2 / 9 * alpha : k) • E ^ 2
  - (7 / 2592 * beta : k) • (A ^ 3 * D)
  + (7 / 1296 * beta : k) • (A ^ 2 * B * C)
  + (7 / 648 * beta : k) • (A * B ^ 3)
  - (7 / 216 * beta : k) • (A * C * D)
  - (7 / 144 * beta : k) • (B ^ 2 * D)
  - (7 / 108 * beta : k) • (B * C ^ 2)
  + (7 / 36 * beta : k) • (D * E)
  - (5 / 432 * delta : k) • (A ^ 2 * D)
  + (5 / 108 * delta : k) • (A * B * C)
  + (5 / 324 * delta : k) • B ^ 3
  - (5 / 36 * delta : k) • (C * D)
  + (1 / 27 * epsilon : k) • (A * B ^ 2)
  - (1 / 9 * epsilon : k) • (B * D)
  - (1 / 9 * epsilon : k) • C ^ 2
  - (1 / 12 * zeta : k) • (A * D)
  - (1 / 6 * zeta : k) • (B * C)
  - (1 / 18 * eta : k) • B ^ 2
  + (1 / 3 * eta : k) • E
  + (1 / 6 * theta : k) • D

set_option maxHeartbeats 32000000 in
theorem degreeZeroOmicronCubic610_eq_sigmaCE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      omicronCubicSigmaFaceCE610 A B C D E +
        degreeZeroOmicronCubicNoSigmaCE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroOmicronCubic610, omicronCubicSigmaFaceCE610, degreeZeroOmicronCubicNoSigmaCE610]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroOmicronCubicNoSigmaCE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicSigmaConeCE610 A B C D E) :
    (degreeZeroOmicronCubicNoSigmaCE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      2 * C.natDegree + E.natDegree := by
  rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  have hs0 : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt h0
  have hs1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt h1
  have hs2 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt h2
  have hs3 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt h3
  have hs4 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt h4
  have hs5 : 0 + 1 ≤ C.natDegree := Nat.succ_le_of_lt h5
  have hs6 : 0 + 1 ≤ E.natDegree := Nat.succ_le_of_lt h6
  have hs8 : A.natDegree + 2 * B.natDegree + 1 ≤ 2 * C.natDegree := Nat.succ_le_of_lt h8
  have hs9 : A.natDegree + 2 * D.natDegree + 1 ≤ 3 * C.natDegree := Nat.succ_le_of_lt h9
  have hs10 : 11 * A.natDegree + 1 ≤ 6 * C.natDegree := Nat.succ_le_of_lt h10
  simp only [degreeZeroOmicronCubicNoSigmaCE610]
  compute_degree
  omega

theorem cubicSigmaCone_CE_impossible
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicSigmaConeCE610 A B C D E)
    (hdeg : (degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree =
        0) :
    False := by
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    omega
  have hc : (-(5 / 27 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead : (omicronCubicSigmaFaceCE610 A B C D E).natDegree = 2 * C.natDegree + E.natDegree := by
    simp only [omicronCubicSigmaFaceCE610]
    rw [natDegree_smul _ hc, natDegree_mul (pow_ne_zero 2 hCne) hEne, natDegree_pow]
  have hrest := degreeZeroOmicronCubicNoSigmaCE610_natDegree_lt l alpha beta delta epsilon
      zeta eta theta A B C D E hcone
  rw [degreeZeroOmicronCubic610_eq_sigmaCE_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  omega

/- σ-cone DE -/

def kappaCubicSigmaFaceDE610 (A B C D E : k[X]) : k[X] :=
  (10 / 9 : k) • (D * E)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaCubicNoSigmaDE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (5 / 243 : k) • (A * B ^ 3)
  - (5 / 27 : k) • (B ^ 2 * D)
  - (5 / 27 : k) • (B * C ^ 2)
  + (7 / 6912 * l : k) • A ^ 5
  + (5 / 288 * l : k) • (A ^ 3 * C)
  - (1 / 192 * l : k) • (A ^ 2 * B ^ 2)
  + (1 / 16 * l : k) • (A ^ 2 * E)
  - (1 / 8 * l : k) • (A * B * D)
  + (1 / 16 * l : k) • (A * C ^ 2)
  - (3 / 16 * l : k) • (B ^ 2 * C)
  + (3 / 4 * l : k) • (C * E)
  + (3 / 8 * l : k) • D ^ 2
  - (4 / 81 * alpha : k) • B ^ 3
  + (4 / 9 * alpha : k) • (B * E)
  + (4 / 9 * alpha : k) • (C * D)
  + (35 / 10368 * beta : k) • A ^ 4
  + (7 / 144 * beta : k) • (A ^ 2 * C)
  - (7 / 432 * beta : k) • (A * B ^ 2)
  + (7 / 36 * beta : k) • (A * E)
  + (7 / 36 * beta : k) • (B * D)
  + (7 / 72 * beta : k) • C ^ 2
  + (5 / 432 * delta : k) • A ^ 3
  + (5 / 36 * delta : k) • (A * C)
  - (5 / 72 * delta : k) • B ^ 2
  + (5 / 6 * delta : k) • E
  + (2 / 3 * epsilon : k) • D
  + (1 / 24 * zeta : k) • A ^ 2
  + (1 / 2 * zeta : k) • C
  + (1 / 3 * eta : k) • B
  + (1 / 6 * theta : k) • A

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaCubic610_eq_sigmaDE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      kappaCubicSigmaFaceDE610 A B C D E +
        degreeZeroKappaCubicNoSigmaDE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroKappaCubic610, kappaCubicSigmaFaceDE610, degreeZeroKappaCubicNoSigmaDE610]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaCubicNoSigmaDE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicSigmaConeDE610 A B C D E) :
    (degreeZeroKappaCubicNoSigmaDE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      D.natDegree + E.natDegree := by
  rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  have hs0 : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt h0
  have hs1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt h1
  have hs2 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt h2
  have hs3 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt h3
  have hs4 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt h4
  have hs5 : 0 + 1 ≤ D.natDegree := Nat.succ_le_of_lt h5
  have hs6 : 0 + 1 ≤ E.natDegree := Nat.succ_le_of_lt h6
  have hs8 : A.natDegree + 6 * B.natDegree + 1 ≤ 4 * D.natDegree := Nat.succ_le_of_lt h8
  have hs9 : 3 * C.natDegree + 1 ≤ A.natDegree + 2 * D.natDegree := Nat.succ_le_of_lt h9
  have hs10 : 9 * A.natDegree + 1 ≤ 4 * D.natDegree := Nat.succ_le_of_lt h10
  simp only [degreeZeroKappaCubicNoSigmaDE610]
  compute_degree
  omega

theorem cubicSigmaCone_DE_impossible
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicSigmaConeDE610 A B C D E)
    (hdeg : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree =
        0) :
    False := by
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    omega
  have hc : (10 / 9 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (kappaCubicSigmaFaceDE610 A B C D E).natDegree = D.natDegree + E.natDegree := by
    simp only [kappaCubicSigmaFaceDE610]
    rw [natDegree_smul _ hc, natDegree_mul hDne hEne]
  have hrest := degreeZeroKappaCubicNoSigmaDE610_natDegree_lt l alpha beta delta epsilon
      zeta eta theta A B C D E hcone
  rw [degreeZeroKappaCubic610_eq_sigmaDE_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  omega

/- σ-cone BCD -/

def omicronCubicSigmaFaceBCD610 (A B C D E : k[X]) : k[X] :=
  (10 / 81 : k) • (A * B * C * D)

set_option maxHeartbeats 32000000 in
def degreeZeroOmicronCubicNoSigmaBCD610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (-(5 / 486 : k)) • (A * B ^ 4)
  + (5 / 81 : k) • (A * B ^ 2 * E)
  + (25 / 486 : k) • (B ^ 3 * D)
  + (5 / 54 : k) • (B ^ 2 * C ^ 2)
  - (5 / 27 : k) • (B * D * E)
  - (5 / 27 : k) • (C ^ 2 * E)
  - (5 / 27 : k) • (C * D ^ 2)
  - (5 / 6912 * l : k) • (A ^ 4 * D)
  + (1 / 864 * l : k) • (A ^ 3 * B * C)
  - (1 / 288 * l : k) • (A ^ 2 * B ^ 3)
  - (1 / 96 * l : k) • (A ^ 2 * C * D)
  + (7 / 96 * l : k) • (A * B ^ 2 * D)
  + (1 / 24 * l : k) • (A * B * C ^ 2)
  + (1 / 16 * l : k) • (B ^ 3 * C)
  - (1 / 8 * l : k) • (A * D * E)
  - (1 / 4 * l : k) • (B * C * E)
  - (1 / 8 * l : k) • (B * D ^ 2)
  - (3 / 16 * l : k) • (C ^ 2 * D)
  + (4 / 81 * alpha : k) • (A * B ^ 2 * C)
  + (1 / 81 * alpha : k) • B ^ 4
  - (2 / 27 * alpha : k) • (A * D ^ 2)
  - (2 / 27 * alpha : k) • (B ^ 2 * E)
  - (2 / 9 * alpha : k) • (B * C * D)
  - (4 / 81 * alpha : k) • C ^ 3
  + (2 / 9 * alpha : k) • E ^ 2
  - (7 / 2592 * beta : k) • (A ^ 3 * D)
  + (7 / 1296 * beta : k) • (A ^ 2 * B * C)
  + (7 / 648 * beta : k) • (A * B ^ 3)
  - (7 / 216 * beta : k) • (A * C * D)
  - (7 / 144 * beta : k) • (B ^ 2 * D)
  - (7 / 108 * beta : k) • (B * C ^ 2)
  + (7 / 36 * beta : k) • (D * E)
  - (5 / 432 * delta : k) • (A ^ 2 * D)
  + (5 / 108 * delta : k) • (A * B * C)
  + (5 / 324 * delta : k) • B ^ 3
  - (5 / 36 * delta : k) • (C * D)
  + (1 / 27 * epsilon : k) • (A * B ^ 2)
  - (1 / 9 * epsilon : k) • (B * D)
  - (1 / 9 * epsilon : k) • C ^ 2
  - (1 / 12 * zeta : k) • (A * D)
  - (1 / 6 * zeta : k) • (B * C)
  - (1 / 18 * eta : k) • B ^ 2
  + (1 / 3 * eta : k) • E
  + (1 / 6 * theta : k) • D

set_option maxHeartbeats 32000000 in
theorem degreeZeroOmicronCubic610_eq_sigmaBCD_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      omicronCubicSigmaFaceBCD610 A B C D E +
        degreeZeroOmicronCubicNoSigmaBCD610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroOmicronCubic610, omicronCubicSigmaFaceBCD610, degreeZeroOmicronCubicNoSigmaBCD610]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroOmicronCubicNoSigmaBCD610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicSigmaConeBCD610 A B C D E) :
    (degreeZeroOmicronCubicNoSigmaBCD610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      A.natDegree + B.natDegree + C.natDegree + D.natDegree := by
  rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  have hs0 : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt h0
  have hs1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt h1
  have hs2 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt h2
  have hs3 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt h3
  have hs4 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt h4
  have hs5 : 0 + 1 ≤ B.natDegree := Nat.succ_le_of_lt h5
  have hs6 : 0 + 1 ≤ C.natDegree := Nat.succ_le_of_lt h6
  have hs7 : 0 + 1 ≤ D.natDegree := Nat.succ_le_of_lt h7
  have hs10 : 4 * E.natDegree + 1 ≤ 3 * A.natDegree + 6 * B.natDegree := Nat.succ_le_of_lt h10
  have hs11 : 4 * A.natDegree + 1 ≤ 3 * B.natDegree := Nat.succ_le_of_lt h11
  simp only [degreeZeroOmicronCubicNoSigmaBCD610]
  compute_degree
  omega

theorem cubicSigmaCone_BCD_impossible
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicSigmaConeBCD610 A B C D E)
    (hdeg : (degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree =
        0) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
    omega
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
    omega
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
    omega
  have hc : (10 / 81 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (omicronCubicSigmaFaceBCD610 A B C D E).natDegree = A.natDegree + B.natDegree + C.natDegree + D.natDegree := by
    simp only [omicronCubicSigmaFaceBCD610]
    rw [natDegree_smul _ hc, natDegree_mul (mul_ne_zero (mul_ne_zero hAne hBne) hCne) hDne, natDegree_mul (mul_ne_zero hAne hBne) hCne, natDegree_mul hAne hBne]
  have hrest := degreeZeroOmicronCubicNoSigmaBCD610_natDegree_lt l alpha beta delta epsilon
      zeta eta theta A B C D E hcone
  rw [degreeZeroOmicronCubic610_eq_sigmaBCD_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  omega

/- σ-cone BCE -/

def kappaCubicSigmaInnerBCE610 (a b c e : k) : k :=
  5 * a * b ^ 3 + (-45 : k) * b * c ^ 2

def lambdaCubicSigmaInnerBCE610 (a b c e : k) : k :=
  5 * a * b ^ 2 * c + (-5 : k) * c ^ 3 + 45 * e ^ 2

def omicronCubicSigmaInnerBCE610 (a b c e : k) : k :=
  5 * a * b ^ 2 * e + (-15 : k) * c ^ 2 * e

set_option maxHeartbeats 32000000 in
theorem cubicSigmaInner_BCE_identity
    (a b c e : k) :
    ((-1 / 40 : k) * a * b * c ^ 3 + (-1 / 16 : k) * a * b * e ^ 2) * kappaCubicSigmaInnerBCE610 a b c e +
      ((1 / 40 : k) * a * b ^ 2 * c ^ 2 + (-1 / 5 : k) * c ^ 4) * lambdaCubicSigmaInnerBCE610 a b c e +
      ((1 / 16 : k) * a * b ^ 2 * e + (-3 / 5 : k) * c ^ 2 * e) * omicronCubicSigmaInnerBCE610 a b c e =
      c ^ 7 := by
  simp only [kappaCubicSigmaInnerBCE610, lambdaCubicSigmaInnerBCE610, omicronCubicSigmaInnerBCE610]
  ring

def kappaCubicSigmaFaceBCE610 (A B C D E : k[X]) : k[X] :=
  (5 / 243 : k) • (A * B ^ 3)
  - (5 / 27 : k) • (B * C ^ 2)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaCubicNoSigmaBCE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (-(5 / 27 : k)) • (B ^ 2 * D)
  + (10 / 9 : k) • (D * E)
  + (7 / 6912 * l : k) • A ^ 5
  + (5 / 288 * l : k) • (A ^ 3 * C)
  - (1 / 192 * l : k) • (A ^ 2 * B ^ 2)
  + (1 / 16 * l : k) • (A ^ 2 * E)
  - (1 / 8 * l : k) • (A * B * D)
  + (1 / 16 * l : k) • (A * C ^ 2)
  - (3 / 16 * l : k) • (B ^ 2 * C)
  + (3 / 4 * l : k) • (C * E)
  + (3 / 8 * l : k) • D ^ 2
  - (4 / 81 * alpha : k) • B ^ 3
  + (4 / 9 * alpha : k) • (B * E)
  + (4 / 9 * alpha : k) • (C * D)
  + (35 / 10368 * beta : k) • A ^ 4
  + (7 / 144 * beta : k) • (A ^ 2 * C)
  - (7 / 432 * beta : k) • (A * B ^ 2)
  + (7 / 36 * beta : k) • (A * E)
  + (7 / 36 * beta : k) • (B * D)
  + (7 / 72 * beta : k) • C ^ 2
  + (5 / 432 * delta : k) • A ^ 3
  + (5 / 36 * delta : k) • (A * C)
  - (5 / 72 * delta : k) • B ^ 2
  + (5 / 6 * delta : k) • E
  + (2 / 3 * epsilon : k) • D
  + (1 / 24 * zeta : k) • A ^ 2
  + (1 / 2 * zeta : k) • C
  + (1 / 3 * eta : k) • B
  + (1 / 6 * theta : k) • A

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaCubic610_eq_sigmaBCE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      kappaCubicSigmaFaceBCE610 A B C D E +
        degreeZeroKappaCubicNoSigmaBCE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroKappaCubic610, kappaCubicSigmaFaceBCE610, degreeZeroKappaCubicNoSigmaBCE610]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaCubicNoSigmaBCE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicSigmaConeBCE610 A B C D E) :
    (degreeZeroKappaCubicNoSigmaBCE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  have hs0 : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt h0
  have hs1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt h1
  have hs2 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt h2
  have hs3 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt h3
  have hs4 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt h4
  have hs5 : 0 + 1 ≤ B.natDegree := Nat.succ_le_of_lt h5
  have hs6 : 0 + 1 ≤ C.natDegree := Nat.succ_le_of_lt h6
  have hs7 : 0 + 1 ≤ E.natDegree := Nat.succ_le_of_lt h7
  have hs10 : 4 * D.natDegree + 1 ≤ A.natDegree + 6 * B.natDegree := Nat.succ_le_of_lt h10
  have hs11 : 4 * A.natDegree + 1 ≤ 3 * B.natDegree := Nat.succ_le_of_lt h11
  simp only [degreeZeroKappaCubicNoSigmaBCE610]
  compute_degree
  omega

theorem kappaCubicSigmaFaceBCE610_coeff_top
    {A B C D E : k[X]}
    (hcone : CubicSigmaConeBCE610 A B C D E)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    : (kappaCubicSigmaFaceBCE610 A B C D E).coeff (A.natDegree + 3 * B.natDegree) =
      (1 / 243 : k) * kappaCubicSigmaInnerBCE610 A.leadingCoeff B.leadingCoeff C.leadingCoeff E.leadingCoeff := by
  rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  simp only [kappaCubicSigmaFaceBCE610, kappaCubicSigmaInnerBCE610, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
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

def lambdaCubicSigmaFaceBCE610 (A B C D E : k[X]) : k[X] :=
  (5 / 81 : k) • (A * B ^ 2 * C)
  - (5 / 81 : k) • C ^ 3
  + (5 / 9 : k) • E ^ 2

set_option maxHeartbeats 16000000 in
def degreeZeroLambdaCubicNoSigmaBCE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (5 / 243 : k) • B ^ 4
  - (5 / 27 : k) • (A * D ^ 2)
  - (5 / 27 : k) • (B ^ 2 * E)
  - (10 / 27 : k) • (B * C * D)
  - (5 / 6912 * l : k) • (A ^ 4 * B)
  - (1 / 288 * l : k) • (A ^ 3 * D)
  - (1 / 96 * l : k) • (A ^ 2 * B * C)
  + (1 / 32 * l : k) • (A * B ^ 3)
  - (1 / 8 * l : k) • (A * B * E)
  - (1 / 8 * l : k) • (A * C * D)
  - (3 / 16 * l : k) • (B ^ 2 * D)
  - (3 / 16 * l : k) • (B * C ^ 2)
  + (3 / 4 * l : k) • (D * E)
  - (4 / 27 * alpha : k) • (A * B * D)
  - (4 / 27 * alpha : k) • (B ^ 2 * C)
  + (4 / 9 * alpha : k) • (C * E)
  + (2 / 9 * alpha : k) • D ^ 2
  - (7 / 2592 * beta : k) • (A ^ 3 * B)
  - (7 / 432 * beta : k) • (A ^ 2 * D)
  - (7 / 216 * beta : k) • (A * B * C)
  - (35 / 1296 * beta : k) • B ^ 3
  + (7 / 36 * beta : k) • (B * E)
  + (7 / 36 * beta : k) • (C * D)
  - (5 / 432 * delta : k) • (A ^ 2 * B)
  - (5 / 36 * delta : k) • (A * D)
  - (5 / 36 * delta : k) • (B * C)
  - (1 / 9 * epsilon : k) • B ^ 2
  + (2 / 3 * epsilon : k) • E
  - (1 / 12 * zeta : k) • (A * B)
  + (1 / 2 * zeta : k) • D
  + (1 / 3 * eta : k) • C
  + (1 / 6 * theta : k) • B

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaCubic610_eq_sigmaBCE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      lambdaCubicSigmaFaceBCE610 A B C D E +
        degreeZeroLambdaCubicNoSigmaBCE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroLambdaCubic610, lambdaCubicSigmaFaceBCE610, degreeZeroLambdaCubicNoSigmaBCE610]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaCubicNoSigmaBCE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicSigmaConeBCE610 A B C D E) :
    (degreeZeroLambdaCubicNoSigmaBCE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      A.natDegree + 2 * B.natDegree + C.natDegree := by
  rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  have hs0 : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt h0
  have hs1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt h1
  have hs2 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt h2
  have hs3 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt h3
  have hs4 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt h4
  have hs5 : 0 + 1 ≤ B.natDegree := Nat.succ_le_of_lt h5
  have hs6 : 0 + 1 ≤ C.natDegree := Nat.succ_le_of_lt h6
  have hs7 : 0 + 1 ≤ E.natDegree := Nat.succ_le_of_lt h7
  have hs10 : 4 * D.natDegree + 1 ≤ A.natDegree + 6 * B.natDegree := Nat.succ_le_of_lt h10
  have hs11 : 4 * A.natDegree + 1 ≤ 3 * B.natDegree := Nat.succ_le_of_lt h11
  simp only [degreeZeroLambdaCubicNoSigmaBCE610]
  compute_degree
  omega

theorem lambdaCubicSigmaFaceBCE610_coeff_top
    {A B C D E : k[X]}
    (hcone : CubicSigmaConeBCE610 A B C D E)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hEne : E ≠ 0)
    : (lambdaCubicSigmaFaceBCE610 A B C D E).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      (1 / 81 : k) * lambdaCubicSigmaInnerBCE610 A.leadingCoeff B.leadingCoeff C.leadingCoeff E.leadingCoeff := by
  rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  simp only [lambdaCubicSigmaFaceBCE610, lambdaCubicSigmaInnerBCE610, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_AB2C : ((A * B ^ 2 * C)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hCne, natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow]
  have hcf_AB2C : ((A * B ^ 2 * C)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff := by
    rw [← hdeg_AB2C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_C3 : (C ^ 3).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_C3 : (C ^ 3).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      C.leadingCoeff ^ 3 := by
    rw [← hdeg_C3, coeff_natDegree, leadingCoeff_pow]
  have hdeg_E2 : (E ^ 2).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_E2 : (E ^ 2).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      E.leadingCoeff ^ 2 := by
    rw [← hdeg_E2, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_AB2C, hcf_C3, hcf_E2]
  ring

def omicronCubicSigmaFaceBCE610 (A B C D E : k[X]) : k[X] :=
  (5 / 81 : k) • (A * B ^ 2 * E)
  - (5 / 27 : k) • (C ^ 2 * E)

set_option maxHeartbeats 32000000 in
def degreeZeroOmicronCubicNoSigmaBCE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (-(5 / 486 : k)) • (A * B ^ 4)
  + (10 / 81 : k) • (A * B * C * D)
  + (25 / 486 : k) • (B ^ 3 * D)
  + (5 / 54 : k) • (B ^ 2 * C ^ 2)
  - (5 / 27 : k) • (B * D * E)
  - (5 / 27 : k) • (C * D ^ 2)
  - (5 / 6912 * l : k) • (A ^ 4 * D)
  + (1 / 864 * l : k) • (A ^ 3 * B * C)
  - (1 / 288 * l : k) • (A ^ 2 * B ^ 3)
  - (1 / 96 * l : k) • (A ^ 2 * C * D)
  + (7 / 96 * l : k) • (A * B ^ 2 * D)
  + (1 / 24 * l : k) • (A * B * C ^ 2)
  + (1 / 16 * l : k) • (B ^ 3 * C)
  - (1 / 8 * l : k) • (A * D * E)
  - (1 / 4 * l : k) • (B * C * E)
  - (1 / 8 * l : k) • (B * D ^ 2)
  - (3 / 16 * l : k) • (C ^ 2 * D)
  + (4 / 81 * alpha : k) • (A * B ^ 2 * C)
  + (1 / 81 * alpha : k) • B ^ 4
  - (2 / 27 * alpha : k) • (A * D ^ 2)
  - (2 / 27 * alpha : k) • (B ^ 2 * E)
  - (2 / 9 * alpha : k) • (B * C * D)
  - (4 / 81 * alpha : k) • C ^ 3
  + (2 / 9 * alpha : k) • E ^ 2
  - (7 / 2592 * beta : k) • (A ^ 3 * D)
  + (7 / 1296 * beta : k) • (A ^ 2 * B * C)
  + (7 / 648 * beta : k) • (A * B ^ 3)
  - (7 / 216 * beta : k) • (A * C * D)
  - (7 / 144 * beta : k) • (B ^ 2 * D)
  - (7 / 108 * beta : k) • (B * C ^ 2)
  + (7 / 36 * beta : k) • (D * E)
  - (5 / 432 * delta : k) • (A ^ 2 * D)
  + (5 / 108 * delta : k) • (A * B * C)
  + (5 / 324 * delta : k) • B ^ 3
  - (5 / 36 * delta : k) • (C * D)
  + (1 / 27 * epsilon : k) • (A * B ^ 2)
  - (1 / 9 * epsilon : k) • (B * D)
  - (1 / 9 * epsilon : k) • C ^ 2
  - (1 / 12 * zeta : k) • (A * D)
  - (1 / 6 * zeta : k) • (B * C)
  - (1 / 18 * eta : k) • B ^ 2
  + (1 / 3 * eta : k) • E
  + (1 / 6 * theta : k) • D

set_option maxHeartbeats 32000000 in
theorem degreeZeroOmicronCubic610_eq_sigmaBCE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      omicronCubicSigmaFaceBCE610 A B C D E +
        degreeZeroOmicronCubicNoSigmaBCE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroOmicronCubic610, omicronCubicSigmaFaceBCE610, degreeZeroOmicronCubicNoSigmaBCE610]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroOmicronCubicNoSigmaBCE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicSigmaConeBCE610 A B C D E) :
    (degreeZeroOmicronCubicNoSigmaBCE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      A.natDegree + 2 * B.natDegree + E.natDegree := by
  rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  have hs0 : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt h0
  have hs1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt h1
  have hs2 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt h2
  have hs3 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt h3
  have hs4 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt h4
  have hs5 : 0 + 1 ≤ B.natDegree := Nat.succ_le_of_lt h5
  have hs6 : 0 + 1 ≤ C.natDegree := Nat.succ_le_of_lt h6
  have hs7 : 0 + 1 ≤ E.natDegree := Nat.succ_le_of_lt h7
  have hs10 : 4 * D.natDegree + 1 ≤ A.natDegree + 6 * B.natDegree := Nat.succ_le_of_lt h10
  have hs11 : 4 * A.natDegree + 1 ≤ 3 * B.natDegree := Nat.succ_le_of_lt h11
  simp only [degreeZeroOmicronCubicNoSigmaBCE610]
  compute_degree
  omega

theorem omicronCubicSigmaFaceBCE610_coeff_top
    {A B C D E : k[X]}
    (hcone : CubicSigmaConeBCE610 A B C D E)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hEne : E ≠ 0)
    : (omicronCubicSigmaFaceBCE610 A B C D E).coeff (A.natDegree + 2 * B.natDegree + E.natDegree) =
      (1 / 81 : k) * omicronCubicSigmaInnerBCE610 A.leadingCoeff B.leadingCoeff C.leadingCoeff E.leadingCoeff := by
  rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  simp only [omicronCubicSigmaFaceBCE610, omicronCubicSigmaInnerBCE610, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_AB2E : ((A * B ^ 2 * E)).natDegree = A.natDegree + 2 * B.natDegree + E.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hEne, natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow]
  have hcf_AB2E : ((A * B ^ 2 * E)).coeff (A.natDegree + 2 * B.natDegree + E.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hdeg_AB2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_C2E : ((C ^ 2 * E)).natDegree = A.natDegree + 2 * B.natDegree + E.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hEne, natDegree_pow]
    omega
  have hcf_C2E : ((C ^ 2 * E)).coeff (A.natDegree + 2 * B.natDegree + E.natDegree) =
      C.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hdeg_C2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  rw [hcf_AB2E, hcf_C2E]
  ring

set_option maxHeartbeats 16000000 in
theorem cubicSigmaCone_BCE_impossible
    {j t : k}
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicSigmaConeBCE610 A B C D E)
    (hlam : (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree =
        0)
    (hkap : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree =
        0)
    (hmu : (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta
          theta A B C D E).natDegree =
        0)
    (homi : (degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree =
        0)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E) =
        Polynomial.C (j / t)) :
    False := by

  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
    omega
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
    omega
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
    omega

  have hprimdeg :
      (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C610 _ (j / t) hjdiv hder

  have hkappainner : kappaCubicSigmaInnerBCE610 A.leadingCoeff B.leadingCoeff C.leadingCoeff E.leadingCoeff = 0 := by
    have hrest := degreeZeroKappaCubicNoSigmaBCE610_natDegree_lt l alpha beta delta
        epsilon zeta eta theta A B C D E hcone
    have hct := kappaCubicSigmaFaceBCE610_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne)
    have hz : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hkap]
      rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
      omega
    rw [degreeZeroKappaCubic610_eq_sigmaBCE_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 243 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h

  have hlambdainner : lambdaCubicSigmaInnerBCE610 A.leadingCoeff B.leadingCoeff C.leadingCoeff E.leadingCoeff = 0 := by
    have hrest := degreeZeroLambdaCubicNoSigmaBCE610_natDegree_lt l alpha beta delta
        epsilon zeta eta theta A B C D E hcone
    have hct := lambdaCubicSigmaFaceBCE610_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hEne := hEne)
    have hz : (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hlam]
      rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
      omega
    rw [degreeZeroLambdaCubic610_eq_sigmaBCE_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 81 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h

  have homicroninner : omicronCubicSigmaInnerBCE610 A.leadingCoeff B.leadingCoeff C.leadingCoeff E.leadingCoeff = 0 := by
    have hrest := degreeZeroOmicronCubicNoSigmaBCE610_natDegree_lt l alpha beta delta
        epsilon zeta eta theta A B C D E hcone
    have hct := omicronCubicSigmaFaceBCE610_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hEne := hEne)
    have hz : (degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).coeff (A.natDegree + 2 * B.natDegree + E.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [homi]
      rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
      omega
    rw [degreeZeroOmicronCubic610_eq_sigmaBCE_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 81 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h

  have hid := cubicSigmaInner_BCE_identity A.leadingCoeff B.leadingCoeff C.leadingCoeff E.leadingCoeff
  have hpow : C.leadingCoeff ^ 7 = 0 := by
    rw [hkappainner, hlambdainner, homicroninner] at hid
    simpa using hid.symm
  have hlc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  exact hlc ((pow_eq_zero_iff (by decide : (7 : ℕ) ≠ 0)).mp hpow)

/- σ-cone BDE -/

def omicronCubicSigmaFaceBDE610 (A B C D E : k[X]) : k[X] :=
  (5 / 81 : k) • (A * B ^ 2 * E)

set_option maxHeartbeats 32000000 in
def degreeZeroOmicronCubicNoSigmaBDE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (-(5 / 486 : k)) • (A * B ^ 4)
  + (10 / 81 : k) • (A * B * C * D)
  + (25 / 486 : k) • (B ^ 3 * D)
  + (5 / 54 : k) • (B ^ 2 * C ^ 2)
  - (5 / 27 : k) • (B * D * E)
  - (5 / 27 : k) • (C ^ 2 * E)
  - (5 / 27 : k) • (C * D ^ 2)
  - (5 / 6912 * l : k) • (A ^ 4 * D)
  + (1 / 864 * l : k) • (A ^ 3 * B * C)
  - (1 / 288 * l : k) • (A ^ 2 * B ^ 3)
  - (1 / 96 * l : k) • (A ^ 2 * C * D)
  + (7 / 96 * l : k) • (A * B ^ 2 * D)
  + (1 / 24 * l : k) • (A * B * C ^ 2)
  + (1 / 16 * l : k) • (B ^ 3 * C)
  - (1 / 8 * l : k) • (A * D * E)
  - (1 / 4 * l : k) • (B * C * E)
  - (1 / 8 * l : k) • (B * D ^ 2)
  - (3 / 16 * l : k) • (C ^ 2 * D)
  + (4 / 81 * alpha : k) • (A * B ^ 2 * C)
  + (1 / 81 * alpha : k) • B ^ 4
  - (2 / 27 * alpha : k) • (A * D ^ 2)
  - (2 / 27 * alpha : k) • (B ^ 2 * E)
  - (2 / 9 * alpha : k) • (B * C * D)
  - (4 / 81 * alpha : k) • C ^ 3
  + (2 / 9 * alpha : k) • E ^ 2
  - (7 / 2592 * beta : k) • (A ^ 3 * D)
  + (7 / 1296 * beta : k) • (A ^ 2 * B * C)
  + (7 / 648 * beta : k) • (A * B ^ 3)
  - (7 / 216 * beta : k) • (A * C * D)
  - (7 / 144 * beta : k) • (B ^ 2 * D)
  - (7 / 108 * beta : k) • (B * C ^ 2)
  + (7 / 36 * beta : k) • (D * E)
  - (5 / 432 * delta : k) • (A ^ 2 * D)
  + (5 / 108 * delta : k) • (A * B * C)
  + (5 / 324 * delta : k) • B ^ 3
  - (5 / 36 * delta : k) • (C * D)
  + (1 / 27 * epsilon : k) • (A * B ^ 2)
  - (1 / 9 * epsilon : k) • (B * D)
  - (1 / 9 * epsilon : k) • C ^ 2
  - (1 / 12 * zeta : k) • (A * D)
  - (1 / 6 * zeta : k) • (B * C)
  - (1 / 18 * eta : k) • B ^ 2
  + (1 / 3 * eta : k) • E
  + (1 / 6 * theta : k) • D

set_option maxHeartbeats 32000000 in
theorem degreeZeroOmicronCubic610_eq_sigmaBDE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      omicronCubicSigmaFaceBDE610 A B C D E +
        degreeZeroOmicronCubicNoSigmaBDE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroOmicronCubic610, omicronCubicSigmaFaceBDE610, degreeZeroOmicronCubicNoSigmaBDE610]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroOmicronCubicNoSigmaBDE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicSigmaConeBDE610 A B C D E) :
    (degreeZeroOmicronCubicNoSigmaBDE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      A.natDegree + 2 * B.natDegree + E.natDegree := by
  rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  have hs0 : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt h0
  have hs1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt h1
  have hs2 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt h2
  have hs3 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt h3
  have hs4 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt h4
  have hs5 : 0 + 1 ≤ B.natDegree := Nat.succ_le_of_lt h5
  have hs6 : 0 + 1 ≤ D.natDegree := Nat.succ_le_of_lt h6
  have hs7 : 0 + 1 ≤ E.natDegree := Nat.succ_le_of_lt h7
  have hs10 : 2 * C.natDegree + 1 ≤ A.natDegree + 2 * B.natDegree := Nat.succ_le_of_lt h10
  have hs11 : 4 * A.natDegree + 1 ≤ 3 * B.natDegree := Nat.succ_le_of_lt h11
  simp only [degreeZeroOmicronCubicNoSigmaBDE610]
  compute_degree
  omega

theorem cubicSigmaCone_BDE_impossible
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicSigmaConeBDE610 A B C D E)
    (hdeg : (degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree =
        0) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
    omega
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
    omega
  have hc : (5 / 81 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (omicronCubicSigmaFaceBDE610 A B C D E).natDegree = A.natDegree + 2 * B.natDegree + E.natDegree := by
    simp only [omicronCubicSigmaFaceBDE610]
    rw [natDegree_smul _ hc, natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hEne, natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow]
  have hrest := degreeZeroOmicronCubicNoSigmaBDE610_natDegree_lt l alpha beta delta epsilon
      zeta eta theta A B C D E hcone
  rw [degreeZeroOmicronCubic610_eq_sigmaBDE_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  omega

/- σ-cone CDE -/

def kappaCubicSigmaFaceCDE610 (A B C D E : k[X]) : k[X] :=
  (10 / 9 : k) • (D * E)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaCubicNoSigmaCDE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (5 / 243 : k) • (A * B ^ 3)
  - (5 / 27 : k) • (B ^ 2 * D)
  - (5 / 27 : k) • (B * C ^ 2)
  + (7 / 6912 * l : k) • A ^ 5
  + (5 / 288 * l : k) • (A ^ 3 * C)
  - (1 / 192 * l : k) • (A ^ 2 * B ^ 2)
  + (1 / 16 * l : k) • (A ^ 2 * E)
  - (1 / 8 * l : k) • (A * B * D)
  + (1 / 16 * l : k) • (A * C ^ 2)
  - (3 / 16 * l : k) • (B ^ 2 * C)
  + (3 / 4 * l : k) • (C * E)
  + (3 / 8 * l : k) • D ^ 2
  - (4 / 81 * alpha : k) • B ^ 3
  + (4 / 9 * alpha : k) • (B * E)
  + (4 / 9 * alpha : k) • (C * D)
  + (35 / 10368 * beta : k) • A ^ 4
  + (7 / 144 * beta : k) • (A ^ 2 * C)
  - (7 / 432 * beta : k) • (A * B ^ 2)
  + (7 / 36 * beta : k) • (A * E)
  + (7 / 36 * beta : k) • (B * D)
  + (7 / 72 * beta : k) • C ^ 2
  + (5 / 432 * delta : k) • A ^ 3
  + (5 / 36 * delta : k) • (A * C)
  - (5 / 72 * delta : k) • B ^ 2
  + (5 / 6 * delta : k) • E
  + (2 / 3 * epsilon : k) • D
  + (1 / 24 * zeta : k) • A ^ 2
  + (1 / 2 * zeta : k) • C
  + (1 / 3 * eta : k) • B
  + (1 / 6 * theta : k) • A

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaCubic610_eq_sigmaCDE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      kappaCubicSigmaFaceCDE610 A B C D E +
        degreeZeroKappaCubicNoSigmaCDE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroKappaCubic610, kappaCubicSigmaFaceCDE610, degreeZeroKappaCubicNoSigmaCDE610]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaCubicNoSigmaCDE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicSigmaConeCDE610 A B C D E) :
    (degreeZeroKappaCubicNoSigmaCDE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      D.natDegree + E.natDegree := by
  rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  have hs0 : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt h0
  have hs1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt h1
  have hs2 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt h2
  have hs3 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt h3
  have hs4 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt h4
  have hs5 : 0 + 1 ≤ C.natDegree := Nat.succ_le_of_lt h5
  have hs6 : 0 + 1 ≤ D.natDegree := Nat.succ_le_of_lt h6
  have hs7 : 0 + 1 ≤ E.natDegree := Nat.succ_le_of_lt h7
  have hs10 : A.natDegree + 2 * B.natDegree + 1 ≤ 2 * C.natDegree := Nat.succ_le_of_lt h10
  have hs11 : 11 * A.natDegree + 1 ≤ 6 * C.natDegree := Nat.succ_le_of_lt h11
  simp only [degreeZeroKappaCubicNoSigmaCDE610]
  compute_degree
  omega

theorem cubicSigmaCone_CDE_impossible
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicSigmaConeCDE610 A B C D E)
    (hdeg : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree =
        0) :
    False := by
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
    omega
  have hc : (10 / 9 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (kappaCubicSigmaFaceCDE610 A B C D E).natDegree = D.natDegree + E.natDegree := by
    simp only [kappaCubicSigmaFaceCDE610]
    rw [natDegree_smul _ hc, natDegree_mul hDne hEne]
  have hrest := degreeZeroKappaCubicNoSigmaCDE610_natDegree_lt l alpha beta delta epsilon
      zeta eta theta A B C D E hcone
  rw [degreeZeroKappaCubic610_eq_sigmaCDE_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  omega

end CubicSigmaKills610

/-! ## The `{C,D}` residual, closed by `N₁` -/

section CubicSigmaCD610

variable {k : Type*} [Field k] [CharZero k]

def lambdaCubicSigmaFaceCD610 (A B C D E : k[X]) : k[X] :=
  (-(5 / 27 : k)) • (A * D ^ 2)
  - (5 / 81 : k) • C ^ 3

set_option maxHeartbeats 16000000 in
def degreeZeroLambdaCubicNoSigmaCD610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (5 / 81 : k) • (A * B ^ 2 * C)
  + (5 / 243 : k) • B ^ 4
  - (5 / 27 : k) • (B ^ 2 * E)
  - (10 / 27 : k) • (B * C * D)
  + (5 / 9 : k) • E ^ 2
  - (5 / 6912 * l : k) • (A ^ 4 * B)
  - (1 / 288 * l : k) • (A ^ 3 * D)
  - (1 / 96 * l : k) • (A ^ 2 * B * C)
  + (1 / 32 * l : k) • (A * B ^ 3)
  - (1 / 8 * l : k) • (A * B * E)
  - (1 / 8 * l : k) • (A * C * D)
  - (3 / 16 * l : k) • (B ^ 2 * D)
  - (3 / 16 * l : k) • (B * C ^ 2)
  + (3 / 4 * l : k) • (D * E)
  - (4 / 27 * alpha : k) • (A * B * D)
  - (4 / 27 * alpha : k) • (B ^ 2 * C)
  + (4 / 9 * alpha : k) • (C * E)
  + (2 / 9 * alpha : k) • D ^ 2
  - (7 / 2592 * beta : k) • (A ^ 3 * B)
  - (7 / 432 * beta : k) • (A ^ 2 * D)
  - (7 / 216 * beta : k) • (A * B * C)
  - (35 / 1296 * beta : k) • B ^ 3
  + (7 / 36 * beta : k) • (B * E)
  + (7 / 36 * beta : k) • (C * D)
  - (5 / 432 * delta : k) • (A ^ 2 * B)
  - (5 / 36 * delta : k) • (A * D)
  - (5 / 36 * delta : k) • (B * C)
  - (1 / 9 * epsilon : k) • B ^ 2
  + (2 / 3 * epsilon : k) • E
  - (1 / 12 * zeta : k) • (A * B)
  + (1 / 2 * zeta : k) • D
  + (1 / 3 * eta : k) • C
  + (1 / 6 * theta : k) • B

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaCubic610_eq_sigmaCD_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      lambdaCubicSigmaFaceCD610 A B C D E +
        degreeZeroLambdaCubicNoSigmaCD610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroLambdaCubic610, lambdaCubicSigmaFaceCD610, degreeZeroLambdaCubicNoSigmaCD610]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaCubicNoSigmaCD610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicSigmaConeCD610 A B C D E) :
    (degreeZeroLambdaCubicNoSigmaCD610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      A.natDegree + 2 * D.natDegree := by
  rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  have hs0 : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt h0
  have hs1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt h1
  have hs2 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt h2
  have hs3 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt h3
  have hs4 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt h4
  have hs5 : 0 + 1 ≤ C.natDegree := Nat.succ_le_of_lt h5
  have hs6 : 0 + 1 ≤ D.natDegree := Nat.succ_le_of_lt h6
  have hs8 : A.natDegree + 2 * B.natDegree + 1 ≤ 2 * C.natDegree := Nat.succ_le_of_lt h8
  have hs9 : 2 * E.natDegree + 1 ≤ 3 * C.natDegree := Nat.succ_le_of_lt h9
  have hs10 : 11 * A.natDegree + 1 ≤ 6 * C.natDegree := Nat.succ_le_of_lt h10
  simp only [degreeZeroLambdaCubicNoSigmaCD610]
  compute_degree
  omega

def n1CubicSigmaFaceCD610 (A B C D E : k[X]) : k[X] :=
  (-(5 / 27 : k)) • (C ^ 2 * D)
set_option maxHeartbeats 32000000 in
def degreeZeroN1CubicNoSigmaCD610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (5 / 81 : k) • (A * B ^ 2 * D)
  + (20 / 243 : k) • (B ^ 3 * C)
  - (10 / 27 : k) • (B * C * E)
  - (5 / 27 : k) • (B * D ^ 2)
  + (77 / 248832 * l : k) • A ^ 6
  + (35 / 6912 * l : k) • (A ^ 4 * C)
  - (1 / 1152 * l : k) • (A ^ 3 * B ^ 2)
  + (5 / 288 * l : k) • (A ^ 3 * E)
  - (1 / 96 * l : k) • (A ^ 2 * B * D)
  + (1 / 64 * l : k) • (A ^ 2 * C ^ 2)
  + (1 / 32 * l : k) • (A * B ^ 2 * C)
  + (3 / 128 * l : k) • B ^ 4
  + (1 / 8 * l : k) • (A * C * E)
  - (1 / 16 * l : k) • (A * D ^ 2)
  - (3 / 16 * l : k) • (B ^ 2 * E)
  - (3 / 8 * l : k) • (B * C * D)
  - (1 / 16 * l : k) • C ^ 3
  + (3 / 8 * l : k) • E ^ 2
  + (4 / 243 * alpha : k) • (A * B ^ 3)
  - (4 / 27 * alpha : k) • (B ^ 2 * D)
  - (4 / 27 * alpha : k) • (B * C ^ 2)
  + (4 / 9 * alpha : k) • (D * E)
  + (7 / 6912 * beta : k) • A ^ 5
  + (35 / 2592 * beta : k) • (A ^ 3 * C)
  - (7 / 5184 * beta : k) • (A ^ 2 * B ^ 2)
  + (7 / 144 * beta : k) • (A ^ 2 * E)
  - (7 / 216 * beta : k) • (A * B * D)
  + (7 / 432 * beta : k) • (A * C ^ 2)
  - (35 / 432 * beta : k) • (B ^ 2 * C)
  + (7 / 36 * beta : k) • (C * E)
  + (7 / 72 * beta : k) • D ^ 2
  + (35 / 10368 * delta : k) • A ^ 4
  + (5 / 144 * delta : k) • (A ^ 2 * C)
  + (5 / 432 * delta : k) • (A * B ^ 2)
  + (5 / 36 * delta : k) • (A * E)
  - (5 / 36 * delta : k) • (B * D)
  - (5 / 72 * delta : k) • C ^ 2
  - (2 / 9 * epsilon : k) • (B * C)
  + (5 / 432 * zeta : k) • A ^ 3
  + (1 / 12 * zeta : k) • (A * C)
  - (1 / 8 * zeta : k) • B ^ 2
  + (1 / 2 * zeta : k) • E
  + (1 / 3 * eta : k) • D
  + (1 / 24 * theta : k) • A ^ 2
  + (1 / 6 * theta : k) • C
set_option maxHeartbeats 32000000 in
theorem degreeZeroN1Cubic610_eq_sigmaCD_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroN1Cubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E =
      n1CubicSigmaFaceCD610 A B C D E +
        degreeZeroN1CubicNoSigmaCD610 l alpha beta delta epsilon zeta
          eta theta A B C D E := by
  simp only [degreeZeroN1Cubic610, n1CubicSigmaFaceCD610,
    degreeZeroN1CubicNoSigmaCD610]
  all_goals module

end CubicSigmaCD610

/-! ## The balanced cell -/

section CubicBalanced610

variable {k : Type*} [Field k] [CharZero k]

def kappaCubicSigmaFaceBCDE610 (A B C D E : k[X]) : k[X] :=
  (5 / 243 : k) • (A * B ^ 3)
  - (5 / 27 : k) • (B * C ^ 2)
  + (10 / 9 : k) • (D * E)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaCubicNoSigmaBCDE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (-(5 / 27 : k)) • (B ^ 2 * D)
  + (7 / 6912 * l : k) • A ^ 5
  + (5 / 288 * l : k) • (A ^ 3 * C)
  - (1 / 192 * l : k) • (A ^ 2 * B ^ 2)
  + (1 / 16 * l : k) • (A ^ 2 * E)
  - (1 / 8 * l : k) • (A * B * D)
  + (1 / 16 * l : k) • (A * C ^ 2)
  - (3 / 16 * l : k) • (B ^ 2 * C)
  + (3 / 4 * l : k) • (C * E)
  + (3 / 8 * l : k) • D ^ 2
  - (4 / 81 * alpha : k) • B ^ 3
  + (4 / 9 * alpha : k) • (B * E)
  + (4 / 9 * alpha : k) • (C * D)
  + (35 / 10368 * beta : k) • A ^ 4
  + (7 / 144 * beta : k) • (A ^ 2 * C)
  - (7 / 432 * beta : k) • (A * B ^ 2)
  + (7 / 36 * beta : k) • (A * E)
  + (7 / 36 * beta : k) • (B * D)
  + (7 / 72 * beta : k) • C ^ 2
  + (5 / 432 * delta : k) • A ^ 3
  + (5 / 36 * delta : k) • (A * C)
  - (5 / 72 * delta : k) • B ^ 2
  + (5 / 6 * delta : k) • E
  + (2 / 3 * epsilon : k) • D
  + (1 / 24 * zeta : k) • A ^ 2
  + (1 / 2 * zeta : k) • C
  + (1 / 3 * eta : k) • B
  + (1 / 6 * theta : k) • A

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaCubic610_eq_sigmaBCDE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      kappaCubicSigmaFaceBCDE610 A B C D E +
        degreeZeroKappaCubicNoSigmaBCDE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroKappaCubic610, kappaCubicSigmaFaceBCDE610, degreeZeroKappaCubicNoSigmaBCDE610]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaCubicNoSigmaBCDE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicSigmaConeBCDE610 A B C D E) :
    (degreeZeroKappaCubicNoSigmaBCDE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      A.natDegree + 3 * B.natDegree := by
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
  simp only [degreeZeroKappaCubicNoSigmaBCDE610]
  compute_degree
  omega

def lambdaCubicSigmaFaceBCDE610 (A B C D E : k[X]) : k[X] :=
  (5 / 81 : k) • (A * B ^ 2 * C)
  - (5 / 27 : k) • (A * D ^ 2)
  - (5 / 81 : k) • C ^ 3
  + (5 / 9 : k) • E ^ 2

set_option maxHeartbeats 16000000 in
def degreeZeroLambdaCubicNoSigmaBCDE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (5 / 243 : k) • B ^ 4
  - (5 / 27 : k) • (B ^ 2 * E)
  - (10 / 27 : k) • (B * C * D)
  - (5 / 6912 * l : k) • (A ^ 4 * B)
  - (1 / 288 * l : k) • (A ^ 3 * D)
  - (1 / 96 * l : k) • (A ^ 2 * B * C)
  + (1 / 32 * l : k) • (A * B ^ 3)
  - (1 / 8 * l : k) • (A * B * E)
  - (1 / 8 * l : k) • (A * C * D)
  - (3 / 16 * l : k) • (B ^ 2 * D)
  - (3 / 16 * l : k) • (B * C ^ 2)
  + (3 / 4 * l : k) • (D * E)
  - (4 / 27 * alpha : k) • (A * B * D)
  - (4 / 27 * alpha : k) • (B ^ 2 * C)
  + (4 / 9 * alpha : k) • (C * E)
  + (2 / 9 * alpha : k) • D ^ 2
  - (7 / 2592 * beta : k) • (A ^ 3 * B)
  - (7 / 432 * beta : k) • (A ^ 2 * D)
  - (7 / 216 * beta : k) • (A * B * C)
  - (35 / 1296 * beta : k) • B ^ 3
  + (7 / 36 * beta : k) • (B * E)
  + (7 / 36 * beta : k) • (C * D)
  - (5 / 432 * delta : k) • (A ^ 2 * B)
  - (5 / 36 * delta : k) • (A * D)
  - (5 / 36 * delta : k) • (B * C)
  - (1 / 9 * epsilon : k) • B ^ 2
  + (2 / 3 * epsilon : k) • E
  - (1 / 12 * zeta : k) • (A * B)
  + (1 / 2 * zeta : k) • D
  + (1 / 3 * eta : k) • C
  + (1 / 6 * theta : k) • B

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaCubic610_eq_sigmaBCDE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      lambdaCubicSigmaFaceBCDE610 A B C D E +
        degreeZeroLambdaCubicNoSigmaBCDE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroLambdaCubic610, lambdaCubicSigmaFaceBCDE610, degreeZeroLambdaCubicNoSigmaBCDE610]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaCubicNoSigmaBCDE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicSigmaConeBCDE610 A B C D E) :
    (degreeZeroLambdaCubicNoSigmaBCDE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      A.natDegree + 2 * B.natDegree + C.natDegree := by
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
  simp only [degreeZeroLambdaCubicNoSigmaBCDE610]
  compute_degree
  omega

def omicronCubicSigmaFaceBCDE610 (A B C D E : k[X]) : k[X] :=
  (5 / 81 : k) • (A * B ^ 2 * E)
  + (10 / 81 : k) • (A * B * C * D)
  - (5 / 27 : k) • (C ^ 2 * E)

set_option maxHeartbeats 32000000 in
def degreeZeroOmicronCubicNoSigmaBCDE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (-(5 / 486 : k)) • (A * B ^ 4)
  + (25 / 486 : k) • (B ^ 3 * D)
  + (5 / 54 : k) • (B ^ 2 * C ^ 2)
  - (5 / 27 : k) • (B * D * E)
  - (5 / 27 : k) • (C * D ^ 2)
  - (5 / 6912 * l : k) • (A ^ 4 * D)
  + (1 / 864 * l : k) • (A ^ 3 * B * C)
  - (1 / 288 * l : k) • (A ^ 2 * B ^ 3)
  - (1 / 96 * l : k) • (A ^ 2 * C * D)
  + (7 / 96 * l : k) • (A * B ^ 2 * D)
  + (1 / 24 * l : k) • (A * B * C ^ 2)
  + (1 / 16 * l : k) • (B ^ 3 * C)
  - (1 / 8 * l : k) • (A * D * E)
  - (1 / 4 * l : k) • (B * C * E)
  - (1 / 8 * l : k) • (B * D ^ 2)
  - (3 / 16 * l : k) • (C ^ 2 * D)
  + (4 / 81 * alpha : k) • (A * B ^ 2 * C)
  + (1 / 81 * alpha : k) • B ^ 4
  - (2 / 27 * alpha : k) • (A * D ^ 2)
  - (2 / 27 * alpha : k) • (B ^ 2 * E)
  - (2 / 9 * alpha : k) • (B * C * D)
  - (4 / 81 * alpha : k) • C ^ 3
  + (2 / 9 * alpha : k) • E ^ 2
  - (7 / 2592 * beta : k) • (A ^ 3 * D)
  + (7 / 1296 * beta : k) • (A ^ 2 * B * C)
  + (7 / 648 * beta : k) • (A * B ^ 3)
  - (7 / 216 * beta : k) • (A * C * D)
  - (7 / 144 * beta : k) • (B ^ 2 * D)
  - (7 / 108 * beta : k) • (B * C ^ 2)
  + (7 / 36 * beta : k) • (D * E)
  - (5 / 432 * delta : k) • (A ^ 2 * D)
  + (5 / 108 * delta : k) • (A * B * C)
  + (5 / 324 * delta : k) • B ^ 3
  - (5 / 36 * delta : k) • (C * D)
  + (1 / 27 * epsilon : k) • (A * B ^ 2)
  - (1 / 9 * epsilon : k) • (B * D)
  - (1 / 9 * epsilon : k) • C ^ 2
  - (1 / 12 * zeta : k) • (A * D)
  - (1 / 6 * zeta : k) • (B * C)
  - (1 / 18 * eta : k) • B ^ 2
  + (1 / 3 * eta : k) • E
  + (1 / 6 * theta : k) • D

set_option maxHeartbeats 32000000 in
theorem degreeZeroOmicronCubic610_eq_sigmaBCDE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      omicronCubicSigmaFaceBCDE610 A B C D E +
        degreeZeroOmicronCubicNoSigmaBCDE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroOmicronCubic610, omicronCubicSigmaFaceBCDE610, degreeZeroOmicronCubicNoSigmaBCDE610]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroOmicronCubicNoSigmaBCDE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicSigmaConeBCDE610 A B C D E) :
    (degreeZeroOmicronCubicNoSigmaBCDE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      A.natDegree + 2 * B.natDegree + E.natDegree := by
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
  simp only [degreeZeroOmicronCubicNoSigmaBCDE610]
  compute_degree
  omega

def n1CubicSigmaFaceBCDE610 (A B C D E : k[X]) : k[X] :=
  (5 / 81 : k) • (A * B ^ 2 * D)
  - (10 / 27 : k) • (B * C * E)
  - (5 / 27 : k) • (C ^ 2 * D)
set_option maxHeartbeats 32000000 in
def degreeZeroN1CubicNoSigmaBCDE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (20 / 243 : k) • (B ^ 3 * C)
  - (5 / 27 : k) • (B * D ^ 2)
  + (77 / 248832 * l : k) • A ^ 6
  + (35 / 6912 * l : k) • (A ^ 4 * C)
  - (1 / 1152 * l : k) • (A ^ 3 * B ^ 2)
  + (5 / 288 * l : k) • (A ^ 3 * E)
  - (1 / 96 * l : k) • (A ^ 2 * B * D)
  + (1 / 64 * l : k) • (A ^ 2 * C ^ 2)
  + (1 / 32 * l : k) • (A * B ^ 2 * C)
  + (3 / 128 * l : k) • B ^ 4
  + (1 / 8 * l : k) • (A * C * E)
  - (1 / 16 * l : k) • (A * D ^ 2)
  - (3 / 16 * l : k) • (B ^ 2 * E)
  - (3 / 8 * l : k) • (B * C * D)
  - (1 / 16 * l : k) • C ^ 3
  + (3 / 8 * l : k) • E ^ 2
  + (4 / 243 * alpha : k) • (A * B ^ 3)
  - (4 / 27 * alpha : k) • (B ^ 2 * D)
  - (4 / 27 * alpha : k) • (B * C ^ 2)
  + (4 / 9 * alpha : k) • (D * E)
  + (7 / 6912 * beta : k) • A ^ 5
  + (35 / 2592 * beta : k) • (A ^ 3 * C)
  - (7 / 5184 * beta : k) • (A ^ 2 * B ^ 2)
  + (7 / 144 * beta : k) • (A ^ 2 * E)
  - (7 / 216 * beta : k) • (A * B * D)
  + (7 / 432 * beta : k) • (A * C ^ 2)
  - (35 / 432 * beta : k) • (B ^ 2 * C)
  + (7 / 36 * beta : k) • (C * E)
  + (7 / 72 * beta : k) • D ^ 2
  + (35 / 10368 * delta : k) • A ^ 4
  + (5 / 144 * delta : k) • (A ^ 2 * C)
  + (5 / 432 * delta : k) • (A * B ^ 2)
  + (5 / 36 * delta : k) • (A * E)
  - (5 / 36 * delta : k) • (B * D)
  - (5 / 72 * delta : k) • C ^ 2
  - (2 / 9 * epsilon : k) • (B * C)
  + (5 / 432 * zeta : k) • A ^ 3
  + (1 / 12 * zeta : k) • (A * C)
  - (1 / 8 * zeta : k) • B ^ 2
  + (1 / 2 * zeta : k) • E
  + (1 / 3 * eta : k) • D
  + (1 / 24 * theta : k) • A ^ 2
  + (1 / 6 * theta : k) • C
set_option maxHeartbeats 32000000 in
theorem degreeZeroN1Cubic610_eq_sigmaBCDE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroN1Cubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E =
      n1CubicSigmaFaceBCDE610 A B C D E +
        degreeZeroN1CubicNoSigmaBCDE610 l alpha beta delta epsilon zeta
          eta theta A B C D E := by
  simp only [degreeZeroN1Cubic610, n1CubicSigmaFaceBCDE610,
    degreeZeroN1CubicNoSigmaBCDE610]
  all_goals module

def kappaCubicSigmaInnerBCDE610 (a b c d e : k) : k :=
  a * b ^ 3 + (-9 : k) * b * c ^ 2 + 54 * d * e
def lambdaCubicSigmaInnerBCDE610 (a b c d e : k) : k :=
  a * b ^ 2 * c + (-3 : k) * a * d ^ 2 - c ^ 3 + 9 * e ^ 2
def omicronCubicSigmaInnerBCDE610 (a b c d e : k) : k :=
  a * b ^ 2 * e + 2 * a * b * c * d + (-3 : k) * c ^ 2 * e
def n1CubicSigmaInnerBCDE610 (a b c d e : k) : k :=
  a * b ^ 2 * d + (-6 : k) * b * c * e + (-3 : k) * c ^ 2 * d
set_option maxHeartbeats 32000000 in
theorem cubicSigmaInner_BCDE_identity (a b c d e : k) :
    ((1 / 324 : k) * a * b * c ^ 2 * e + (1 / 972 : k) * a * c ^ 3 * d + (1 / 162 : k) * a * d * e ^ 2) * kappaCubicSigmaInnerBCDE610 a b c d e +
      ((-1 / 324 : k) * a * b ^ 2 * c * e + (1 / 324 : k) * a * b * c ^ 2 * d + (1 / 9 : k) * e ^ 3) * lambdaCubicSigmaInnerBCDE610 a b c d e +
      ((-1 / 72 : k) * a * b * d * e + (1 / 216 : k) * a * c * d ^ 2 + (-1 / 27 : k) * c * e ^ 2) * omicronCubicSigmaInnerBCDE610 a b c d e +
      ((-1 / 243 : k) * a * b * c ^ 3 + (5 / 648 : k) * a * b * e ^ 2 + (1 / 72 : k) * a * c * d * e) * n1CubicSigmaInnerBCDE610 a b c d e =
      e ^ 5 := by
  simp only [kappaCubicSigmaInnerBCDE610, lambdaCubicSigmaInnerBCDE610,
    omicronCubicSigmaInnerBCDE610, n1CubicSigmaInnerBCDE610]
  ring
theorem kappaCubicSigmaFaceBCDE610_coeff_top
    {A B C D E : k[X]}
    (hcone : CubicSigmaConeBCDE610 A B C D E)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    : (kappaCubicSigmaFaceBCDE610 A B C D E).coeff (A.natDegree + 3 * B.natDegree) =
      (5 / 243 : k) * kappaCubicSigmaInnerBCDE610 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff := by
  rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
  simp only [kappaCubicSigmaFaceBCDE610, kappaCubicSigmaInnerBCDE610, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
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
theorem lambdaCubicSigmaFaceBCDE610_coeff_top
    {A B C D E : k[X]}
    (hcone : CubicSigmaConeBCDE610 A B C D E)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    : (lambdaCubicSigmaFaceBCDE610 A B C D E).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      (5 / 81 : k) * lambdaCubicSigmaInnerBCDE610 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff := by
  rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
  simp only [lambdaCubicSigmaFaceBCDE610, lambdaCubicSigmaInnerBCDE610, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_AB2C : ((A * B ^ 2 * C)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hCne, natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow]
  have hcf_AB2C : ((A * B ^ 2 * C)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff := by
    rw [← hdeg_AB2C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_AD2 : ((A * D ^ 2)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 2 hDne), natDegree_pow]
    omega
  have hcf_AD2 : ((A * D ^ 2)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      A.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_AD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_C3 : (C ^ 3).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_C3 : (C ^ 3).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      C.leadingCoeff ^ 3 := by
    rw [← hdeg_C3, coeff_natDegree, leadingCoeff_pow]
  have hdeg_E2 : (E ^ 2).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_E2 : (E ^ 2).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      E.leadingCoeff ^ 2 := by
    rw [← hdeg_E2, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_AB2C, hcf_AD2, hcf_C3, hcf_E2]
  ring
theorem omicronCubicSigmaFaceBCDE610_coeff_top
    {A B C D E : k[X]}
    (hcone : CubicSigmaConeBCDE610 A B C D E)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    : (omicronCubicSigmaFaceBCDE610 A B C D E).coeff (A.natDegree + 2 * B.natDegree + E.natDegree) =
      (5 / 81 : k) * omicronCubicSigmaInnerBCDE610 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff := by
  rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
  simp only [omicronCubicSigmaFaceBCDE610, omicronCubicSigmaInnerBCDE610, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_AB2E : ((A * B ^ 2 * E)).natDegree = A.natDegree + 2 * B.natDegree + E.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hEne, natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow]
  have hcf_AB2E : ((A * B ^ 2 * E)).coeff (A.natDegree + 2 * B.natDegree + E.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hdeg_AB2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_ABCD : ((A * B * C * D)).natDegree = A.natDegree + 2 * B.natDegree + E.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hAne hBne) hCne) hDne, natDegree_mul (mul_ne_zero hAne hBne) hCne, natDegree_mul hAne hBne]
    omega
  have hcf_ABCD : ((A * B * C * D)).coeff (A.natDegree + 2 * B.natDegree + E.natDegree) =
      A.leadingCoeff * B.leadingCoeff * C.leadingCoeff * D.leadingCoeff := by
    rw [← hdeg_ABCD, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_C2E : ((C ^ 2 * E)).natDegree = A.natDegree + 2 * B.natDegree + E.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hEne, natDegree_pow]
    omega
  have hcf_C2E : ((C ^ 2 * E)).coeff (A.natDegree + 2 * B.natDegree + E.natDegree) =
      C.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hdeg_C2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  rw [hcf_AB2E, hcf_ABCD, hcf_C2E]
  ring
theorem n1CubicSigmaFaceBCDE610_coeff_top
    {A B C D E : k[X]}
    (hcone : CubicSigmaConeBCDE610 A B C D E)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    : (n1CubicSigmaFaceBCDE610 A B C D E).coeff (A.natDegree + 2 * B.natDegree + D.natDegree) =
      (5 / 81 : k) * n1CubicSigmaInnerBCDE610 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff := by
  rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
  simp only [n1CubicSigmaFaceBCDE610, n1CubicSigmaInnerBCDE610, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_AB2D : ((A * B ^ 2 * D)).natDegree = A.natDegree + 2 * B.natDegree + D.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hDne, natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow]
  have hcf_AB2D : ((A * B ^ 2 * D)).coeff (A.natDegree + 2 * B.natDegree + D.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_AB2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BCE : ((B * C * E)).natDegree = A.natDegree + 2 * B.natDegree + D.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hCne) hEne, natDegree_mul hBne hCne]
    omega
  have hcf_BCE : ((B * C * E)).coeff (A.natDegree + 2 * B.natDegree + D.natDegree) =
      B.leadingCoeff * C.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_BCE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_C2D : ((C ^ 2 * D)).natDegree = A.natDegree + 2 * B.natDegree + D.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hDne, natDegree_pow]
    omega
  have hcf_C2D : ((C ^ 2 * D)).coeff (A.natDegree + 2 * B.natDegree + D.natDegree) =
      C.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_C2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  rw [hcf_AB2D, hcf_BCE, hcf_C2D]
  ring

end CubicBalanced610


/-! ## All of `B,C,D,E` vanish -/

section CubicAllLettersZero610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 32000000 in
theorem primitiveCubic_of_lettersBCDEzero
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hB : B = 0) (hC : C = 0) (hD : D = 0) (hE : E = 0) :
    degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E =
      (5 / 27648 * l : k) • A ^ 7 +
        (35 / 62208 * beta : k) • A ^ 6 +
        (1 / 576 * delta : k) • A ^ 5 +
        (1 / 192 * zeta : k) • A ^ 4 +
        (1 / 72 * theta : k) • A ^ 3 := by
  rw [hB, hC, hD, hE, degreeZeroPrimitiveCubic610_eq_flat]
  simp only [degreeZeroPrimitiveCubicFlat610]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one, map_zero]
  ring

theorem cubicADominant_allLettersZero_impossible
    {j t : k}
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hApos : 0 < A.natDegree)
    (hB : B = 0) (hC : C = 0) (hD : D = 0) (hE : E = 0)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta eta
          theta A B C D E) =
        Polynomial.C (j / t)) :
    False := by
  have hdeg :=
    natDegree_eq_one_of_derivative_eq_nonzero_C610
      (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta eta
        theta A B C D E) (j / t) hjdiv hder
  have hP := primitiveCubic_of_lettersBCDEzero l alpha beta delta epsilon
      zeta eta theta A B C D E hB hC hD hE
  rw [hP] at hder hdeg
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    omega
  have hle :
      ((5 / 27648 * l : k) • A ^ 7 +
          (35 / 62208 * beta : k) • A ^ 6 +
          (1 / 576 * delta : k) • A ^ 5 +
          (1 / 192 * zeta : k) • A ^ 4 +
          (1 / 72 * theta : k) • A ^ 3).natDegree ≤
        7 * A.natDegree := by
    compute_degree
  by_cases hl0 : l = 0
  · by_cases hb0 : beta = 0
    · by_cases hd0 : delta = 0
      · by_cases hz0 : zeta = 0
        · by_cases ht0 : theta = 0
          · simp only [hl0, hb0, hd0, hz0, ht0, mul_zero, zero_smul,
              add_zero] at hder
            have : derivative (0 : k[X]) = Polynomial.C (j / t) := hder
            rw [derivative_zero] at this
            exact hjdiv (C_eq_zero.mp this.symm)
          · have htheta : theta ≠ 0 := ht0
            have hc : (1 / 72 * theta : k) ≠ 0 :=
              mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) htheta
            have hcf :
                (((5 / 27648 * l : k) • A ^ 7 +
                      (35 / 62208 * beta : k) • A ^ 6 +
                      (1 / 576 * delta : k) • A ^ 5 +
                      (1 / 192 * zeta : k) • A ^ 4 +
                      (1 / 72 * theta : k) • A ^ 3).coeff (3 * A.natDegree)) ≠
                  0 := by
              simp only [hl0, hb0, hd0, hz0, mul_zero, zero_smul, zero_add]
              have hlead : ((1 / 72 * theta : k) • A ^ 3).coeff (3 * A.natDegree) =
                  (1 / 72 * theta : k) * A.leadingCoeff ^ 3 := by
                rw [coeff_smul]
                have hAk : (A ^ 3).natDegree = 3 * A.natDegree := natDegree_pow _ _
                rw [← hAk, coeff_natDegree, leadingCoeff_pow, smul_eq_mul]
              exact hlead ▸ mul_ne_zero hc
                (pow_ne_zero _ (leadingCoeff_ne_zero.mpr hAne))
            have : 3 * A.natDegree ≤ 1 :=
              (le_natDegree_of_ne_zero hcf).trans_eq hdeg
            omega
        · have hzeta : zeta ≠ 0 := hz0
          have hc : (1 / 192 * zeta : k) ≠ 0 :=
            mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hzeta
          have hcf :
              (((5 / 27648 * l : k) • A ^ 7 +
                    (35 / 62208 * beta : k) • A ^ 6 +
                    (1 / 576 * delta : k) • A ^ 5 +
                    (1 / 192 * zeta : k) • A ^ 4 +
                    (1 / 72 * theta : k) • A ^ 3).coeff (4 * A.natDegree)) ≠
                0 := by
            simp only [hl0, hb0, hd0, mul_zero, zero_smul, zero_add]
            have hz3 : ((1 / 72 * theta : k) • A ^ 3).coeff (4 * A.natDegree) = 0 := by
              apply coeff_eq_zero_of_natDegree_lt
              compute_degree
              omega
            have hlead : ((1 / 192 * zeta : k) • A ^ 4).coeff (4 * A.natDegree) =
                (1 / 192 * zeta : k) * A.leadingCoeff ^ 4 := by
              rw [coeff_smul]
              have hAk : (A ^ 4).natDegree = 4 * A.natDegree := natDegree_pow _ _
              rw [← hAk, coeff_natDegree, leadingCoeff_pow, smul_eq_mul]
            simp only [coeff_add, hz3, add_zero, hlead]
            exact mul_ne_zero hc (pow_ne_zero 4 (leadingCoeff_ne_zero.mpr hAne))
          have : 4 * A.natDegree ≤ 1 :=
            (le_natDegree_of_ne_zero hcf).trans_eq hdeg
          omega
      · have hdelta : delta ≠ 0 := hd0
        have hc : (1 / 576 * delta : k) ≠ 0 :=
          mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hdelta
        have hcf :
            (((5 / 27648 * l : k) • A ^ 7 +
                  (35 / 62208 * beta : k) • A ^ 6 +
                  (1 / 576 * delta : k) • A ^ 5 +
                  (1 / 192 * zeta : k) • A ^ 4 +
                  (1 / 72 * theta : k) • A ^ 3).coeff (5 * A.natDegree)) ≠
              0 := by
          simp only [hl0, hb0, mul_zero, zero_smul, zero_add]
          have hz4 : ((1 / 192 * zeta : k) • A ^ 4).coeff (5 * A.natDegree) = 0 := by
            apply coeff_eq_zero_of_natDegree_lt
            compute_degree
            omega
          have hz3 : ((1 / 72 * theta : k) • A ^ 3).coeff (5 * A.natDegree) = 0 := by
            apply coeff_eq_zero_of_natDegree_lt
            compute_degree
            omega
          have hlead : ((1 / 576 * delta : k) • A ^ 5).coeff (5 * A.natDegree) =
              (1 / 576 * delta : k) * A.leadingCoeff ^ 5 := by
            rw [coeff_smul]
            have hAk : (A ^ 5).natDegree = 5 * A.natDegree := natDegree_pow _ _
            rw [← hAk, coeff_natDegree, leadingCoeff_pow, smul_eq_mul]
          simp only [coeff_add, hz4, hz3, add_zero, hlead]
          exact mul_ne_zero hc (pow_ne_zero 5 (leadingCoeff_ne_zero.mpr hAne))
        have : 5 * A.natDegree ≤ 1 :=
          (le_natDegree_of_ne_zero hcf).trans_eq hdeg
        omega
    · have hbeta : beta ≠ 0 := hb0
      have hc : (35 / 62208 * beta : k) ≠ 0 :=
        mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hbeta
      have hcf :
          (((5 / 27648 * l : k) • A ^ 7 +
                (35 / 62208 * beta : k) • A ^ 6 +
                (1 / 576 * delta : k) • A ^ 5 +
                (1 / 192 * zeta : k) • A ^ 4 +
                (1 / 72 * theta : k) • A ^ 3).coeff (6 * A.natDegree)) ≠
            0 := by
        simp only [hl0, mul_zero, zero_smul, zero_add]
        have hz5 : ((1 / 576 * delta : k) • A ^ 5).coeff (6 * A.natDegree) = 0 := by
          apply coeff_eq_zero_of_natDegree_lt
          compute_degree
          omega
        have hz4 : ((1 / 192 * zeta : k) • A ^ 4).coeff (6 * A.natDegree) = 0 := by
          apply coeff_eq_zero_of_natDegree_lt
          compute_degree
          omega
        have hz3 : ((1 / 72 * theta : k) • A ^ 3).coeff (6 * A.natDegree) = 0 := by
          apply coeff_eq_zero_of_natDegree_lt
          compute_degree
          omega
        have hlead : ((35 / 62208 * beta : k) • A ^ 6).coeff (6 * A.natDegree) =
            (35 / 62208 * beta : k) * A.leadingCoeff ^ 6 := by
          rw [coeff_smul]
          have hAk : (A ^ 6).natDegree = 6 * A.natDegree := natDegree_pow _ _
          rw [← hAk, coeff_natDegree, leadingCoeff_pow, smul_eq_mul]
        simp only [coeff_add, hz5, hz4, hz3, add_zero, hlead]
        exact mul_ne_zero hc (pow_ne_zero 6 (leadingCoeff_ne_zero.mpr hAne))
      have : 6 * A.natDegree ≤ 1 :=
        (le_natDegree_of_ne_zero hcf).trans_eq hdeg
      omega
  · have hl : l ≠ 0 := hl0
    have hc : (5 / 27648 * l : k) ≠ 0 :=
      mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hl
    have hcf :
        (((5 / 27648 * l : k) • A ^ 7 +
              (35 / 62208 * beta : k) • A ^ 6 +
              (1 / 576 * delta : k) • A ^ 5 +
              (1 / 192 * zeta : k) • A ^ 4 +
              (1 / 72 * theta : k) • A ^ 3).coeff (7 * A.natDegree)) ≠
          0 := by
      have hz6 : ((35 / 62208 * beta : k) • A ^ 6).coeff (7 * A.natDegree) = 0 := by
        apply coeff_eq_zero_of_natDegree_lt
        compute_degree
        omega
      have hz5 : ((1 / 576 * delta : k) • A ^ 5).coeff (7 * A.natDegree) = 0 := by
        apply coeff_eq_zero_of_natDegree_lt
        compute_degree
        omega
      have hz4 : ((1 / 192 * zeta : k) • A ^ 4).coeff (7 * A.natDegree) = 0 := by
        apply coeff_eq_zero_of_natDegree_lt
        compute_degree
        omega
      have hz3 : ((1 / 72 * theta : k) • A ^ 3).coeff (7 * A.natDegree) = 0 := by
        apply coeff_eq_zero_of_natDegree_lt
        compute_degree
        omega
      have hlead : ((5 / 27648 * l : k) • A ^ 7).coeff (7 * A.natDegree) =
          (5 / 27648 * l : k) * A.leadingCoeff ^ 7 := by
        rw [coeff_smul]
        have hAk : (A ^ 7).natDegree = 7 * A.natDegree := natDegree_pow _ _
        rw [← hAk, coeff_natDegree, leadingCoeff_pow, smul_eq_mul]
      simp only [coeff_add, hz6, hz5, hz4, hz3, add_zero, hlead]
      exact mul_ne_zero hc (pow_ne_zero 7 (leadingCoeff_ne_zero.mpr hAne))
    have : 7 * A.natDegree ≤ 1 :=
      (le_natDegree_of_ne_zero hcf).trans_eq hdeg
    omega

end CubicAllLettersZero610


/-! ## B0: competing odd loads vanish -/

section CubicLoadB0_610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 32000000 in
theorem degreeZeroN1CubicNoL610_natDegree_lt_of_loadCompete
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : cubicLoadCompetes610 A B C D E) :
    (degreeZeroN1CubicNoL610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      6 * A.natDegree := by
  rcases hcone with ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩
  have hB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAB
  have hC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hAC
  have hD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hAD
  have hE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAE
  simp only [degreeZeroN1CubicNoL610]
  compute_degree
  omega

theorem cubicADominant_l_eq_zero
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : cubicLoadCompetes610 A B C D E)
    (hmu : (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta
          theta A B C D E).natDegree = 0)
    (hkap : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree = 0) :
    l = 0 := by
  by_contra hl
  have hApos : 0 < A.natDegree := hcone.1.1
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    omega
  have hc : (77 / 248832 * l : k) ≠ 0 :=
    mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hl
  have hlead : (n1CubicLFace610 l A).natDegree = 6 * A.natDegree := by
    simp only [n1CubicLFace610]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :=
    degreeZeroN1CubicNoL610_natDegree_lt_of_loadCompete l alpha beta delta
      epsilon zeta eta theta A B C D E hcone
  have hN1le := degreeZeroN1Cubic610_natDegree_le l alpha beta delta epsilon
      zeta eta theta A B C D E hmu hkap
  have hN1deg :
      (degreeZeroN1Cubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree =
        6 * A.natDegree := by
    rw [degreeZeroN1Cubic610_eq_L_add_rest,
      natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
  omega

/-- β-column of `N₁` is `7/6912 · β · A⁵`.  Competes when `6 Θ ≥ 3 ρ`. -/
def cubicLoadCompetesBeta610 (A B C D E : k[X]) : Prop :=
  CubicRatioConeA610 A B C D E ∧
    4 * A.natDegree ≥ 9 * B.natDegree ∧
    11 * A.natDegree ≥ 18 * C.natDegree ∧
    3 * A.natDegree ≥ 4 * D.natDegree ∧
    11 * A.natDegree ≥ 12 * E.natDegree

/-- δ-column of `N₁` is `35/10368 · δ · A⁴`.  Competes when `6 Θ ≥ 5 ρ`. -/
def cubicLoadCompetesDelta610 (A B C D E : k[X]) : Prop :=
  CubicRatioConeA610 A B C D E ∧
    4 * A.natDegree ≥ 15 * B.natDegree ∧
    11 * A.natDegree ≥ 30 * C.natDegree ∧
    9 * A.natDegree ≥ 20 * D.natDegree ∧
    11 * A.natDegree ≥ 20 * E.natDegree

/-- ζ-column of `N₁` is `5/432 · ζ · A³`.  Competes when `6 Θ ≥ 7 ρ`. -/
def cubicLoadCompetesZeta610 (A B C D E : k[X]) : Prop :=
  CubicRatioConeA610 A B C D E ∧
    4 * A.natDegree ≥ 21 * B.natDegree ∧
    11 * A.natDegree ≥ 42 * C.natDegree ∧
    9 * A.natDegree ≥ 28 * D.natDegree ∧
    11 * A.natDegree ≥ 28 * E.natDegree

/-- θ-column of `N₁` is `1/24 · θ · A²`.  Competes when `6 Θ ≥ 9 ρ`. -/
def cubicLoadCompetesTheta610 (A B C D E : k[X]) : Prop :=
  CubicRatioConeA610 A B C D E ∧
    4 * A.natDegree ≥ 27 * B.natDegree ∧
    11 * A.natDegree ≥ 54 * C.natDegree ∧
    9 * A.natDegree ≥ 36 * D.natDegree ∧
    11 * A.natDegree ≥ 36 * E.natDegree

end CubicLoadB0_610



/-! ## Stage B residual: A-dominant minus the killed σ-cones -/

section CubicAssembly610

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- Honest leftover of Stage B+C: the source is still on `R = {A}`,
none of the 13 empty σ-argmin cones, and not the all-constant cell.
The `{C,D}` refinement and the balanced cell are not yet closed in Lean
(`N₁` rest bounds did not finish under `compute_degree`+`omega`).
Load-compete chambers after `l = 0` likewise remain. -/
theorem normalized610ScaleZero_cubicADominantResidual2
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
      ¬ CubicSigmaConeB610 A B C D E ∧
      ¬ CubicSigmaConeC610 A B C D E ∧
      ¬ CubicSigmaConeD610 A B C D E ∧
      ¬ CubicSigmaConeE610 A B C D E ∧
      ¬ CubicSigmaConeBC610 A B C D E ∧
      ¬ CubicSigmaConeBD610 A B C D E ∧
      ¬ CubicSigmaConeBE610 A B C D E ∧
      ¬ CubicSigmaConeCE610 A B C D E ∧
      ¬ CubicSigmaConeDE610 A B C D E ∧
      ¬ CubicSigmaConeBCD610 A B C D E ∧
      ¬ CubicSigmaConeBCE610 A B C D E ∧
      ¬ CubicSigmaConeBDE610 A B C D E ∧
      ¬ CubicSigmaConeCDE610 A B C D E ∧
      ¬ (B = 0 ∧ C = 0 ∧ D = 0 ∧ E = 0) := by
  obtain ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
      zeta, eta, theta, iota, cLam, cKap, cMu, cOmi, A, B, C, D, E, ht,
      hj, hjdiv, hHsq, hder, hlamDeg, hkapDeg, hmuDeg, homiDeg, hconeA⟩ :=
    normalized610ScaleZero_cubicADominantResidual hsource
  refine ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
    zeta, eta, theta, iota, cLam, cKap, cMu, cOmi, A, B, C, D, E, ht, hj,
    hjdiv, hHsq, hder, hlamDeg, hkapDeg, hmuDeg, homiDeg, hconeA,
    ?notB, ?notC, ?notD, ?notE, ?notBC, ?notBD, ?notBE, ?notCE, ?notDE,
    ?notBCD, ?notBCE, ?notBDE, ?notCDE, ?notZero⟩
  · intro h; exact cubicSigmaCone_B_impossible l alpha beta delta epsilon
      zeta eta theta A B C D E h hkapDeg
  · intro h; exact cubicSigmaCone_C_impossible l alpha beta delta epsilon
      zeta eta theta A B C D E h hlamDeg
  · intro h; exact cubicSigmaCone_D_impossible l alpha beta delta epsilon
      zeta eta theta A B C D E h hlamDeg
  · intro h; exact cubicSigmaCone_E_impossible l alpha beta delta epsilon
      zeta eta theta A B C D E h hlamDeg
  · intro h; exact cubicSigmaCone_BC_impossible (j := j) (t := t) l alpha
      beta delta epsilon zeta eta theta A B C D E h hlamDeg hkapDeg hmuDeg
      homiDeg hjdiv hder
  · intro h; exact cubicSigmaCone_BD_impossible l alpha beta delta epsilon
      zeta eta theta A B C D E h hkapDeg
  · intro h; exact cubicSigmaCone_BE_impossible l alpha beta delta epsilon
      zeta eta theta A B C D E h hkapDeg
  · intro h; exact cubicSigmaCone_CE_impossible l alpha beta delta epsilon
      zeta eta theta A B C D E h homiDeg
  · intro h; exact cubicSigmaCone_DE_impossible l alpha beta delta epsilon
      zeta eta theta A B C D E h hkapDeg
  · intro h; exact cubicSigmaCone_BCD_impossible l alpha beta delta epsilon
      zeta eta theta A B C D E h homiDeg
  · intro h; exact cubicSigmaCone_BCE_impossible (j := j) (t := t) l alpha
      beta delta epsilon zeta eta theta A B C D E h hlamDeg hkapDeg hmuDeg
      homiDeg hjdiv hder
  · intro h; exact cubicSigmaCone_BDE_impossible l alpha beta delta epsilon
      zeta eta theta A B C D E h homiDeg
  · intro h; exact cubicSigmaCone_CDE_impossible l alpha beta delta epsilon
      zeta eta theta A B C D E h hkapDeg
  · intro h; exact cubicADominant_allLettersZero_impossible (j := j) (t := t)
      l alpha beta delta epsilon zeta eta theta A B C D E hconeA.1 h.1 h.2.1
      h.2.2.1 h.2.2.2 hjdiv hder

end CubicAssembly610

#print axioms degreeZeroN1Cubic610_eq_mu_add_A_kappa
#print axioms cubicADominant_l_eq_zero
#print axioms cubicADominant_allLettersZero_impossible
#print axioms cubicSigmaCone_B_impossible
#print axioms cubicSigmaCone_BCE_impossible
#print axioms normalized610ScaleZero_cubicADominantResidual2

end Max11DegreeRoutes
