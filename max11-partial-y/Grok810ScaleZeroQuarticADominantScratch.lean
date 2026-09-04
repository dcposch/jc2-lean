import Grok810ScaleZeroQuarticConesScratch

/-! # Scale-zero quartic A-dominant Stage B, for normalized `(8,10)`, `H = 0`

Continuation of `Grok810ScaleZeroQuarticConesScratch`.  That file ends at
`normalized810ScaleZero_quarticADominantResidual`: the source loads the
quartic letters `A,B,C,D,E,F,G` on the disjunction
`QuarticRatioConeA810 ∨ QuarticRatioConeABCDEFG810`.  This file treats
the cone `A` branch only.

CAS `scripts/derive_810_scale_zero_quartic_adominant.py` computes the
odd `4×3` matrix of pure-`A` columns (rank 0: quartic substitution
cancelled every linear-odd face, plan risk 4), the σ-grading (every
load-free monomial has letter-count ≥ 2), the 63 equal-σ argmin
systems (all saturate to `(1)`), A-freeness of `μ,ξ,π` on the even
core `B = D = F = 0` including the `γ,ε,η` columns, the seven even
cones, and the `θ`-column of `Π`.

Lean rest bounds for the 63 σ-faces OOM `compute_degree` on the
expanded packets, so those cones remain named residuals.  This file
closes: the constant-letter cell when `l`, `β`, `δ` or `ζ` is live
(unique pure-`A` columns of `Π`), and the even-core chambers `{C}`
and `{E}` (`μ` after `B = D = F = 0`).

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

section QuarticSigmaCones810

variable {k : Type*} [Field k] [CharZero k]

def QuarticSigmaConeB810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree
    ∧ 2 * F.natDegree < 7 * A.natDegree
    ∧ G.natDegree < 4 * A.natDegree
    ∧ 0 < B.natDegree
    ∧ 2 * C.natDegree < A.natDegree + 2 * B.natDegree
    ∧ D.natDegree < A.natDegree + B.natDegree
    ∧ 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
    ∧ F.natDegree < 2 * A.natDegree + B.natDegree
    ∧ 2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree
    ∧ 4 * A.natDegree < 3 * B.natDegree

def QuarticSigmaConeC810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree
    ∧ 2 * F.natDegree < 7 * A.natDegree
    ∧ G.natDegree < 4 * A.natDegree
    ∧ 0 < C.natDegree
    ∧ A.natDegree + 2 * B.natDegree < 2 * C.natDegree
    ∧ 2 * D.natDegree < A.natDegree + 2 * C.natDegree
    ∧ E.natDegree < A.natDegree + C.natDegree
    ∧ 2 * F.natDegree < 3 * A.natDegree + 2 * C.natDegree
    ∧ G.natDegree < 2 * A.natDegree + C.natDegree
    ∧ 11 * A.natDegree < 6 * C.natDegree

def QuarticSigmaConeD810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree
    ∧ 2 * F.natDegree < 7 * A.natDegree
    ∧ G.natDegree < 4 * A.natDegree
    ∧ 0 < D.natDegree
    ∧ A.natDegree + B.natDegree < D.natDegree
    ∧ A.natDegree + 2 * C.natDegree < 2 * D.natDegree
    ∧ 2 * E.natDegree < A.natDegree + 2 * D.natDegree
    ∧ F.natDegree < A.natDegree + D.natDegree
    ∧ 2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree
    ∧ 9 * A.natDegree < 4 * D.natDegree

def QuarticSigmaConeE810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree
    ∧ 2 * F.natDegree < 7 * A.natDegree
    ∧ G.natDegree < 4 * A.natDegree
    ∧ 0 < E.natDegree
    ∧ 3 * A.natDegree + 2 * B.natDegree < 2 * E.natDegree
    ∧ A.natDegree + C.natDegree < E.natDegree
    ∧ A.natDegree + 2 * D.natDegree < 2 * E.natDegree
    ∧ 2 * F.natDegree < A.natDegree + 2 * E.natDegree
    ∧ G.natDegree < A.natDegree + E.natDegree
    ∧ 11 * A.natDegree < 4 * E.natDegree

def QuarticSigmaConeF810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree
    ∧ 2 * F.natDegree < 7 * A.natDegree
    ∧ G.natDegree < 4 * A.natDegree
    ∧ 0 < F.natDegree
    ∧ 2 * A.natDegree + B.natDegree < F.natDegree
    ∧ 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
    ∧ A.natDegree + D.natDegree < F.natDegree
    ∧ A.natDegree + 2 * E.natDegree < 2 * F.natDegree
    ∧ 2 * G.natDegree < A.natDegree + 2 * F.natDegree
    ∧ 13 * A.natDegree < 4 * F.natDegree

def QuarticSigmaConeG810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree
    ∧ 2 * F.natDegree < 7 * A.natDegree
    ∧ G.natDegree < 4 * A.natDegree
    ∧ 0 < G.natDegree
    ∧ 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
    ∧ 2 * A.natDegree + C.natDegree < G.natDegree
    ∧ 3 * A.natDegree + 2 * D.natDegree < 2 * G.natDegree
    ∧ A.natDegree + E.natDegree < G.natDegree
    ∧ A.natDegree + 2 * F.natDegree < 2 * G.natDegree
    ∧ 15 * A.natDegree < 4 * G.natDegree

end QuarticSigmaCones810


/-! ## B2: even core `B = D = F = 0` -/

section QuarticEvenCore810

variable {k : Type*} [Field k] [CharZero k]

def muEvenCoreCFace810 (C : k[X]) : k[X] :=
  (-(5 / 128 : k)) • C ^ 3

def muEvenCoreCRest810 (gamma epsilon eta : k) (C E G : k[X]) : k[X] :=
  (-(3 / 32 * gamma : k)) • C ^ 2
  + (1 / 4 * eta : k) • C
  + (5 / 16 : k) • (C * G)
  + (5 / 32 : k) • E ^ 2
  + (1 / 2 * epsilon : k) • E
  + (3 / 4 * gamma : k) • G

def muEvenCoreEFace810 (E : k[X]) : k[X] :=
  (5 / 32 : k) • E ^ 2

def muEvenCoreERest810 (gamma epsilon eta : k) (C E G : k[X]) : k[X] :=
  (-(5 / 128 : k)) • C ^ 3
  - (3 / 32 * gamma : k) • C ^ 2
  + (1 / 4 * eta : k) • C
  + (5 / 16 : k) • (C * G)
  + (1 / 2 * epsilon : k) • E
  + (3 / 4 * gamma : k) • G

set_option maxHeartbeats 32000000 in
theorem degreeZeroMuQuartic810_evenCore
    (l beta gamma delta epsilon zeta eta theta : k)
    (A C E G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
        A 0 C 0 E 0 G =
      (-(5 / 128 : k)) • C ^ 3
      - (3 / 32 * gamma : k) • C ^ 2
      + (1 / 4 * eta : k) • C
      + (5 / 16 : k) • (C * G)
      + (5 / 32 : k) • E ^ 2
      + (1 / 2 * epsilon : k) • E
      + (3 / 4 * gamma : k) • G := by
  simp only [degreeZeroMuQuartic810]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 32000000 in
theorem degreeZeroXiQuartic810_evenCore
    (l beta gamma delta epsilon zeta eta theta : k)
    (A C E G : k[X]) :
    degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
        A 0 C 0 E 0 G =
      (-(15 / 128 : k)) • (C ^ 2 * E)
      - (1 / 8 * epsilon : k) • C ^ 2
      - (3 / 16 * gamma : k) • (C * E)
      + (1 / 4 * eta : k) • E
      + (5 / 16 : k) • (E * G)
      + (1 / 2 * epsilon : k) • G := by
  simp only [degreeZeroXiQuartic810]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring

theorem muEvenCore_eq_C_add_rest
    (gamma epsilon eta : k) (C E G : k[X]) :
    (-(5 / 128 : k)) • C ^ 3
      - (3 / 32 * gamma : k) • C ^ 2
      + (1 / 4 * eta : k) • C
      + (5 / 16 : k) • (C * G)
      + (5 / 32 : k) • E ^ 2
      + (1 / 2 * epsilon : k) • E
      + (3 / 4 * gamma : k) • G =
      muEvenCoreCFace810 C + muEvenCoreCRest810 gamma epsilon eta C E G := by
  simp only [muEvenCoreCFace810, muEvenCoreCRest810, neg_smul, sub_eq_add_neg]
  abel

theorem muEvenCore_eq_E_add_rest
    (gamma epsilon eta : k) (C E G : k[X]) :
    (-(5 / 128 : k)) • C ^ 3
      - (3 / 32 * gamma : k) • C ^ 2
      + (1 / 4 * eta : k) • C
      + (5 / 16 : k) • (C * G)
      + (5 / 32 : k) • E ^ 2
      + (1 / 2 * epsilon : k) • E
      + (3 / 4 * gamma : k) • G =
      muEvenCoreEFace810 E + muEvenCoreERest810 gamma epsilon eta C E G := by
  simp only [muEvenCoreEFace810, muEvenCoreERest810]
  abel

set_option maxHeartbeats 16000000 in
theorem quarticEvenCore_C_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A C E G : k[X])
    (hCpos : 0 < C.natDegree)
    (hElt : 2 * E.natDegree < 3 * C.natDegree)
    (hGlt : G.natDegree < 2 * C.natDegree)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A 0 C 0 E 0 G).natDegree =
        0) :
    False := by
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    omega
  have hc : (-(5 / 128 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hE1 : 2 * E.natDegree + 1 ≤ 3 * C.natDegree := Nat.succ_le_of_lt hElt
  have hG1 : G.natDegree + 1 ≤ 2 * C.natDegree := Nat.succ_le_of_lt hGlt
  have hlead : (muEvenCoreCFace810 C).natDegree = 3 * C.natDegree := by
    simp only [muEvenCoreCFace810]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :
      (muEvenCoreCRest810 gamma epsilon eta C E G).natDegree <
        3 * C.natDegree := by
    simp only [muEvenCoreCRest810]
    compute_degree
    omega
  rw [degreeZeroMuQuartic810_evenCore, muEvenCore_eq_C_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hmu
  omega

set_option maxHeartbeats 16000000 in
theorem quarticEvenCore_E_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A C E G : k[X])
    (hEpos : 0 < E.natDegree)
    (hClt : 3 * C.natDegree < 2 * E.natDegree)
    (hGlt : 3 * G.natDegree < 2 * E.natDegree)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A 0 C 0 E 0 G).natDegree =
        0) :
    False := by
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    omega
  have hc : (5 / 32 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hC1 : 3 * C.natDegree + 1 ≤ 2 * E.natDegree := Nat.succ_le_of_lt hClt
  have hG1 : 3 * G.natDegree + 1 ≤ 2 * E.natDegree := Nat.succ_le_of_lt hGlt
  have hlead : (muEvenCoreEFace810 E).natDegree = 2 * E.natDegree := by
    simp only [muEvenCoreEFace810]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :
      (muEvenCoreERest810 gamma epsilon eta C E G).natDegree <
        2 * E.natDegree := by
    simp only [muEvenCoreERest810]
    compute_degree
    omega
  rw [degreeZeroMuQuartic810_evenCore, muEvenCore_eq_E_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hmu
  omega

end QuarticEvenCore810

/-! ## B3: `B,…,G` of degree `0`, univariate in `A` -/

section QuarticADominantB3_810

variable {k : Type*} [Field k] [CharZero k]

theorem natDegree_lt_of_le_mul810 {p : k[X]} {a n d : ℕ}
    (hp : p.natDegree ≤ a * n) (ha : a < d) (hn : 0 < n) :
    p.natDegree < d * n :=
  hp.trans_lt (Nat.mul_lt_mul_of_pos_right ha hn)

theorem natDegree_add4_lt810 {p q r s : k[X]} {d : ℕ}
    (hp : p.natDegree < d) (hq : q.natDegree < d)
    (hr : r.natDegree < d) (hs : s.natDegree < d) :
    (p + q + r + s).natDegree < d :=
  natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hp hq) hr) hs

def primitiveQuarticLFace810 (l : k) (A : k[X]) : k[X] :=
  (1575 / 268435456 * l : k) • A ^ 8

def primitiveQuarticBetaA7Face810 (beta : k) (A : k[X]) : k[X] :=
  (25 / 1048576 * beta : k) • A ^ 7

def primitiveQuarticDeltaA6Face810 (delta : k) (A : k[X]) : k[X] :=
  (25 / 262144 * delta : k) • A ^ 6

def primitiveQuarticZetaA5Face810 (zeta : k) (A : k[X]) : k[X] :=
  (3 / 8192 * zeta : k) • A ^ 5

set_option maxHeartbeats 16000000 in
def rhoBaseLetters1Quartic810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 65536 : k)) • (A ^ 4 * B ^ 3)
  - (15 / 16384 : k) • (A ^ 3 * B ^ 2 * D)
  + (15 / 16384 : k) • (A ^ 3 * B * C ^ 2)
  + (15 / 8192 : k) • (A ^ 2 * B ^ 3 * C)
  + (65 / 8192 : k) • (A * B ^ 5)
  - (5 / 2048 : k) • (A ^ 3 * B * G)
  - (5 / 2048 : k) • (A ^ 3 * C * F)
  - (5 / 2048 : k) • (A ^ 3 * D * E)
  - (5 / 2048 : k) • (A ^ 2 * B ^ 2 * F)
  + (15 / 1024 : k) • (A ^ 2 * B * C * E)
  - (25 / 2048 : k) • (A ^ 2 * B * D ^ 2)
  + (15 / 2048 : k) • (A ^ 2 * C ^ 2 * D)
  - (25 / 512 : k) • (A * B ^ 3 * E)
  - (135 / 1024 : k) • (A * B ^ 2 * C * D)
  - (15 / 1024 : k) • (A * B * C ^ 3)
  - (125 / 2048 : k) • (B ^ 4 * D)
  - (265 / 2048 : k) • (B ^ 3 * C ^ 2)
  - (5 / 256 : k) • (A ^ 2 * D * G)
  - (5 / 256 : k) • (A ^ 2 * E * F)

set_option maxHeartbeats 16000000 in
def rhoBaseLetters2Quartic810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 128 : k) • (A * B * C * G)
  + (5 / 32 : k) • (A * B * D * F)
  + (5 / 64 : k) • (A * B * E ^ 2)
  + (15 / 128 : k) • (A * C * D * E)
  + (5 / 128 : k) • (A * D ^ 3)
  + (15 / 256 : k) • (B ^ 3 * G)
  + (85 / 256 : k) • (B ^ 2 * C * F)
  + (85 / 256 : k) • (B ^ 2 * D * E)
  + (45 / 128 : k) • (B * C ^ 2 * E)
  + (45 / 128 : k) • (B * C * D ^ 2)
  + (15 / 128 : k) • (C ^ 3 * D)
  - (5 / 16 : k) • (A * F * G)
  - (5 / 16 : k) • (B * E * G)
  - (5 / 16 : k) • (B * F ^ 2)
  - (5 / 16 : k) • (C * D * G)
  - (5 / 8 : k) • (C * E * F)
  - (5 / 16 : k) • (D ^ 2 * F)
  - (5 / 16 : k) • (D * E ^ 2)

set_option maxHeartbeats 16000000 in
def rhoBaseLoadNoA8aQuartic810
    (l : k) (A B C D E F G : k[X]) : k[X] :=
  (765 / 4194304 * l : k) • (A ^ 6 * C)
  - (369 / 4194304 * l : k) • (A ^ 5 * B ^ 2)
  + (171 / 262144 * l : k) • (A ^ 5 * E)
  - (153 / 262144 * l : k) • (A ^ 4 * B * D)
  + (855 / 524288 * l : k) • (A ^ 4 * C ^ 2)
  - (81 / 131072 * l : k) • (A ^ 3 * B ^ 2 * C)
  + (261 / 262144 * l : k) • (A ^ 2 * B ^ 4)
  + (45 / 32768 * l : k) • (A ^ 4 * G)
  - (9 / 4096 * l : k) • (A ^ 3 * B * F)
  + (99 / 8192 * l : k) • (A ^ 3 * C * E)
  - (9 / 4096 * l : k) • (A ^ 3 * D ^ 2)
  - (9 / 4096 * l : k) • (A ^ 2 * B ^ 2 * E)
  + (9 / 8192 * l : k) • (A ^ 2 * B * C * D)
  + (27 / 16384 * l : k) • (A ^ 2 * C ^ 3)
  - (243 / 8192 * l : k) • (A * B ^ 3 * D)
  - (387 / 16384 * l : k) • (A * B ^ 2 * C ^ 2)
  - (567 / 16384 * l : k) • (B ^ 4 * C)
  + (27 / 1024 * l : k) • (A ^ 2 * C * G)
  - (9 / 512 * l : k) • (A ^ 2 * D * F)
  + (27 / 1024 * l : k) • (A ^ 2 * E ^ 2)

set_option maxHeartbeats 16000000 in
def rhoBaseLoadNoA8bQuartic810
    (l : k) (A B C D E F G : k[X]) : k[X] :=
  (9 / 1024 * l : k) • (A * B ^ 2 * G)
  + (9 / 256 * l : k) • (A * B * C * F)
  + (45 / 512 * l : k) • (A * B * D * E)
  + (9 / 1024 * l : k) • (A * C ^ 2 * E)
  + (9 / 256 * l : k) • (A * C * D ^ 2)
  + (27 / 512 * l : k) • (B ^ 3 * F)
  + (45 / 256 * l : k) • (B ^ 2 * C * E)
  + (45 / 512 * l : k) • (B ^ 2 * D ^ 2)
  + (189 / 1024 * l : k) • (B * C ^ 2 * D)
  + (63 / 4096 * l : k) • C ^ 4
  + (9 / 64 * l : k) • (A * E * G)
  - (9 / 64 * l : k) • (A * F ^ 2)
  - (9 / 64 * l : k) • (B * D * G)
  - (9 / 32 * l : k) • (B * E * F)
  - (9 / 128 * l : k) • (C ^ 2 * G)
  - (9 / 32 * l : k) • (C * D * F)
  - (9 / 64 * l : k) • (C * E ^ 2)
  - (9 / 64 * l : k) • (D ^ 2 * E)
  + (9 / 16 * l : k) • G ^ 2

set_option maxHeartbeats 16000000 in
def rhoBetaGroupQuarticNoA7810
    (A B C D E F : k[X]) : k[X] :=
  (21 / 32768 : k) • (A ^ 5 * C)
  - (119 / 262144 : k) • (A ^ 4 * B ^ 2)
  + (35 / 16384 : k) • (A ^ 4 * E)
  - (7 / 2048 : k) • (A ^ 3 * B * D)
  + (21 / 4096 : k) • (A ^ 3 * C ^ 2)
  - (21 / 8192 : k) • (A ^ 2 * B ^ 2 * C)
  + (119 / 16384 : k) • (A * B ^ 4)
  + (21 / 512 : k) • (A ^ 2 * C * E)
  - (7 / 512 : k) • (A ^ 2 * D ^ 2)
  - (21 / 512 : k) • (A * B ^ 2 * E)
  - (7 / 128 : k) • (A * B * C * D)
  - (7 / 128 : k) • (B ^ 3 * D)
  - (91 / 1024 : k) • (B ^ 2 * C ^ 2)
  + (7 / 64 : k) • (A * E ^ 2)
  + (7 / 32 : k) • (B * C * F)
  + (7 / 32 : k) • (B * D * E)
  + (7 / 64 : k) • (C ^ 2 * E)
  + (7 / 64 : k) • (C * D ^ 2)
  - (7 / 16 : k) • F ^ 2

set_option maxHeartbeats 16000000 in
def rhoDeltaGroupQuarticNoA6810
    (A B C D E F : k[X]) : k[X] :=
  (35 / 16384 : k) • (A ^ 4 * C)
  - (25 / 16384 : k) • (A ^ 3 * B ^ 2)
  + (5 / 1024 : k) • (A ^ 3 * E)
  - (5 / 512 : k) • (A ^ 2 * B * D)
  + (15 / 1024 : k) • (A ^ 2 * C ^ 2)
  - (65 / 1024 : k) • (A * B ^ 2 * C)
  - (135 / 4096 : k) • B ^ 4
  + (5 / 64 : k) • (A * C * E)
  + (5 / 64 : k) • (A * D ^ 2)
  + (25 / 128 : k) • (B ^ 2 * E)
  + (15 / 32 : k) • (B * C * D)
  + (5 / 64 : k) • C ^ 3
  - (5 / 8 : k) • (D * F)
  - (5 / 16 : k) • E ^ 2

set_option maxHeartbeats 16000000 in
def rhoZetaGroupQuarticNoA5810
    (A B C D E F : k[X]) : k[X] :=
  (3 / 512 : k) • (A ^ 3 * C)
  - (3 / 2048 : k) • (A ^ 2 * B ^ 2)
  + (3 / 128 : k) • (A ^ 2 * E)
  + (3 / 32 : k) • (A * B * D)
  + (27 / 128 : k) • (B ^ 2 * C)
  - (3 / 8 : k) • (B * F)
  - (3 / 8 : k) • (C * E)
  - (3 / 16 : k) • D ^ 2


def rhoBaseGroupQuarticNoA8810
    (l : k) (A B C D E F G : k[X]) : k[X] :=
  rhoBaseLetters1Quartic810 A B C D E F G +
    rhoBaseLetters2Quartic810 A B C D E F G +
    rhoBaseLoadNoA8aQuartic810 l A B C D E F G +
    rhoBaseLoadNoA8bQuartic810 l A B C D E F G

def degreeZeroPrimitiveQuarticNoA8810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  rhoBaseGroupQuarticNoA8810 l A B C D E F G +
    beta • rhoBetaGroupQuartic810 A B C D E F +
    gamma • rhoGammaGroupQuartic810 A B C D E F +
    delta • rhoDeltaGroupQuartic810 A B C D E F +
    epsilon • rhoEpsilonGroupQuartic810 A B C D E F +
    zeta • rhoZetaGroupQuartic810 A B C D E F +
    eta • rhoEtaGroupQuartic810 A B C D E F +
    theta • rhoThetaGroupQuartic810 A B C D E G

def degreeZeroPrimitiveQuarticNoBetaA7_l0810
    (beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  rhoBaseLetters1Quartic810 A B C D E F G +
    rhoBaseLetters2Quartic810 A B C D E F G +
    beta • rhoBetaGroupQuarticNoA7810 A B C D E F +
    gamma • rhoGammaGroupQuartic810 A B C D E F +
    delta • rhoDeltaGroupQuartic810 A B C D E F +
    epsilon • rhoEpsilonGroupQuartic810 A B C D E F +
    zeta • rhoZetaGroupQuartic810 A B C D E F +
    eta • rhoEtaGroupQuartic810 A B C D E F +
    theta • rhoThetaGroupQuartic810 A B C D E G

def degreeZeroPrimitiveQuarticNoDeltaA6_l0beta0810
    (gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  rhoBaseLetters1Quartic810 A B C D E F G +
    rhoBaseLetters2Quartic810 A B C D E F G +
    gamma • rhoGammaGroupQuartic810 A B C D E F +
    delta • rhoDeltaGroupQuarticNoA6810 A B C D E F +
    epsilon • rhoEpsilonGroupQuartic810 A B C D E F +
    zeta • rhoZetaGroupQuartic810 A B C D E F +
    eta • rhoEtaGroupQuartic810 A B C D E F +
    theta • rhoThetaGroupQuartic810 A B C D E G

def degreeZeroPrimitiveQuarticNoZetaA5_l0beta0delta0810
    (gamma epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (rhoBaseLetters1Quartic810 A B C D E F G +
      rhoBaseLetters2Quartic810 A B C D E F G +
      gamma • rhoGammaGroupQuartic810 A B C D E F +
      epsilon • rhoEpsilonGroupQuartic810 A B C D E F) +
    (zeta • rhoZetaGroupQuarticNoA5810 A B C D E F +
      (eta • rhoEtaGroupQuartic810 A B C D E F +
        theta • rhoThetaGroupQuartic810 A B C D E G))

set_option maxHeartbeats 32000000 in
theorem rhoBaseGroupQuartic810_eq_A8_add_rest
    (l : k) (A B C D E F G : k[X]) :
    rhoBaseGroupQuartic810 l A B C D E F G =
      primitiveQuarticLFace810 l A +
        rhoBaseGroupQuarticNoA8810 l A B C D E F G := by
  simp only [rhoBaseGroupQuartic810, primitiveQuarticLFace810,
    rhoBaseGroupQuarticNoA8810, rhoBaseLetters1Quartic810,
    rhoBaseLetters2Quartic810, rhoBaseLoadNoA8aQuartic810,
    rhoBaseLoadNoA8bQuartic810]
  module

set_option maxHeartbeats 16000000 in
theorem degreeZeroPrimitiveQuartic810_eq_A8_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G =
      primitiveQuarticLFace810 l A +
        degreeZeroPrimitiveQuarticNoA8810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G := by
  simp only [degreeZeroPrimitiveQuartic810, primitiveQuarticLFace810,
    degreeZeroPrimitiveQuarticNoA8810, rhoBaseGroupQuartic810_eq_A8_add_rest]
  module

set_option maxHeartbeats 16000000 in
theorem rhoBetaGroupQuartic810_eq_A7_add_rest
    (A B C D E F : k[X]) :
    rhoBetaGroupQuartic810 A B C D E F =
      (25 / 1048576 : k) • A ^ 7 +
        rhoBetaGroupQuarticNoA7810 A B C D E F := by
  simp only [rhoBetaGroupQuartic810, rhoBetaGroupQuarticNoA7810]
  module

set_option maxHeartbeats 16000000 in
theorem rhoDeltaGroupQuartic810_eq_A6_add_rest
    (A B C D E F : k[X]) :
    rhoDeltaGroupQuartic810 A B C D E F =
      (25 / 262144 : k) • A ^ 6 +
        rhoDeltaGroupQuarticNoA6810 A B C D E F := by
  simp only [rhoDeltaGroupQuartic810, rhoDeltaGroupQuarticNoA6810]
  module

set_option maxHeartbeats 16000000 in
theorem rhoZetaGroupQuartic810_eq_A5_add_rest
    (A B C D E F : k[X]) :
    rhoZetaGroupQuartic810 A B C D E F =
      (3 / 8192 : k) • A ^ 5 +
        rhoZetaGroupQuarticNoA5810 A B C D E F := by
  simp only [rhoZetaGroupQuartic810, rhoZetaGroupQuarticNoA5810]
  module

set_option maxHeartbeats 16000000 in
theorem rhoBaseGroupQuartic810_eq_letters_of_l_zero
    (A B C D E F G : k[X]) :
    rhoBaseGroupQuartic810 0 A B C D E F G =
      rhoBaseLetters1Quartic810 A B C D E F G +
        rhoBaseLetters2Quartic810 A B C D E F G := by
  simp only [rhoBaseGroupQuartic810, rhoBaseLetters1Quartic810,
    rhoBaseLetters2Quartic810, zero_mul, mul_zero, zero_smul, smul_zero]
  module

set_option maxHeartbeats 16000000 in
theorem degreeZeroPrimitiveQuartic810_eq_betaA7_of_l_zero
    (beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroPrimitiveQuartic810 0 beta gamma delta epsilon zeta eta theta
        A B C D E F G =
      primitiveQuarticBetaA7Face810 beta A +
        degreeZeroPrimitiveQuarticNoBetaA7_l0810 beta gamma delta epsilon zeta
          eta theta A B C D E F G := by
  simp only [degreeZeroPrimitiveQuartic810, primitiveQuarticBetaA7Face810,
    degreeZeroPrimitiveQuarticNoBetaA7_l0810,
    rhoBaseGroupQuartic810_eq_letters_of_l_zero,
    rhoBetaGroupQuartic810_eq_A7_add_rest, smul_add, smul_smul, mul_comm]
  module

set_option maxHeartbeats 16000000 in
theorem degreeZeroPrimitiveQuartic810_eq_deltaA6_of_l_beta_zero
    (gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroPrimitiveQuartic810 0 0 gamma delta epsilon zeta eta theta
        A B C D E F G =
      primitiveQuarticDeltaA6Face810 delta A +
        degreeZeroPrimitiveQuarticNoDeltaA6_l0beta0810 gamma delta epsilon zeta
          eta theta A B C D E F G := by
  simp only [degreeZeroPrimitiveQuartic810, primitiveQuarticDeltaA6Face810,
    degreeZeroPrimitiveQuarticNoDeltaA6_l0beta0810,
    rhoBaseGroupQuartic810_eq_letters_of_l_zero,
    rhoDeltaGroupQuartic810_eq_A6_add_rest, zero_smul, smul_add, smul_smul,
    mul_comm]
  module

set_option maxHeartbeats 16000000 in
theorem degreeZeroPrimitiveQuartic810_eq_zetaA5_of_l_beta_delta_zero
    (gamma epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroPrimitiveQuartic810 0 0 gamma 0 epsilon zeta eta theta
        A B C D E F G =
      primitiveQuarticZetaA5Face810 zeta A +
        degreeZeroPrimitiveQuarticNoZetaA5_l0beta0delta0810 gamma epsilon zeta
          eta theta A B C D E F G := by
  simp only [degreeZeroPrimitiveQuartic810, primitiveQuarticZetaA5Face810,
    degreeZeroPrimitiveQuarticNoZetaA5_l0beta0delta0810,
    rhoBaseGroupQuartic810_eq_letters_of_l_zero,
    rhoZetaGroupQuartic810_eq_A5_add_rest, zero_smul, smul_add, smul_smul,
    mul_comm]
  module

set_option maxHeartbeats 16000000 in
theorem rhoBaseLetters1Quartic810_natDegree_le
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hB : B.natDegree = 0) (hC : C.natDegree = 0)
    (hD : D.natDegree = 0) (hE : E.natDegree = 0)
    (hF : F.natDegree = 0) (hG : G.natDegree = 0) :
    (rhoBaseLetters1Quartic810 A B C D E F G).natDegree ≤ 4 * A.natDegree := by
  have hA1 : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  simp only [rhoBaseLetters1Quartic810]
  compute_degree
  omega

set_option maxHeartbeats 16000000 in
theorem rhoBaseLetters2Quartic810_natDegree_le
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hB : B.natDegree = 0) (hC : C.natDegree = 0)
    (hD : D.natDegree = 0) (hE : E.natDegree = 0)
    (hF : F.natDegree = 0) (hG : G.natDegree = 0) :
    (rhoBaseLetters2Quartic810 A B C D E F G).natDegree ≤ 4 * A.natDegree := by
  have hA1 : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  simp only [rhoBaseLetters2Quartic810]
  compute_degree
  omega

set_option maxHeartbeats 16000000 in
theorem rhoBaseLoadNoA8aQuartic810_natDegree_le
    (l : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hB : B.natDegree = 0) (hC : C.natDegree = 0)
    (hD : D.natDegree = 0) (hE : E.natDegree = 0)
    (hF : F.natDegree = 0) (hG : G.natDegree = 0) :
    (rhoBaseLoadNoA8aQuartic810 l A B C D E F G).natDegree ≤ 6 * A.natDegree := by
  have hA1 : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  simp only [rhoBaseLoadNoA8aQuartic810]
  compute_degree
  omega

set_option maxHeartbeats 16000000 in
theorem rhoBaseLoadNoA8bQuartic810_natDegree_le
    (l : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hB : B.natDegree = 0) (hC : C.natDegree = 0)
    (hD : D.natDegree = 0) (hE : E.natDegree = 0)
    (hF : F.natDegree = 0) (hG : G.natDegree = 0) :
    (rhoBaseLoadNoA8bQuartic810 l A B C D E F G).natDegree ≤ 6 * A.natDegree := by
  have hA1 : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  simp only [rhoBaseLoadNoA8bQuartic810]
  compute_degree
  omega

set_option maxHeartbeats 16000000 in
theorem rhoBetaGroupQuartic810_natDegree_le
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hB : B.natDegree = 0) (hC : C.natDegree = 0)
    (hD : D.natDegree = 0) (hE : E.natDegree = 0)
    (hF : F.natDegree = 0) (hG : G.natDegree = 0) :
    (rhoBetaGroupQuartic810 A B C D E F).natDegree ≤ 7 * A.natDegree := by
  have hA1 : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  simp only [rhoBetaGroupQuartic810]
  compute_degree
  omega

set_option maxHeartbeats 16000000 in
theorem rhoBetaGroupQuarticNoA7810_natDegree_le
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hB : B.natDegree = 0) (hC : C.natDegree = 0)
    (hD : D.natDegree = 0) (hE : E.natDegree = 0)
    (hF : F.natDegree = 0) (hG : G.natDegree = 0) :
    (rhoBetaGroupQuarticNoA7810 A B C D E F).natDegree ≤ 5 * A.natDegree := by
  have hA1 : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  simp only [rhoBetaGroupQuarticNoA7810]
  compute_degree
  omega

set_option maxHeartbeats 16000000 in
theorem rhoGammaGroupQuartic810_natDegree_le
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hB : B.natDegree = 0) (hC : C.natDegree = 0)
    (hD : D.natDegree = 0) (hE : E.natDegree = 0)
    (hF : F.natDegree = 0) (hG : G.natDegree = 0) :
    (rhoGammaGroupQuartic810 A B C D E F).natDegree ≤ 3 * A.natDegree := by
  have hA1 : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  simp only [rhoGammaGroupQuartic810]
  compute_degree
  omega

set_option maxHeartbeats 16000000 in
theorem rhoDeltaGroupQuartic810_natDegree_le
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hB : B.natDegree = 0) (hC : C.natDegree = 0)
    (hD : D.natDegree = 0) (hE : E.natDegree = 0)
    (hF : F.natDegree = 0) (hG : G.natDegree = 0) :
    (rhoDeltaGroupQuartic810 A B C D E F).natDegree ≤ 6 * A.natDegree := by
  have hA1 : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  simp only [rhoDeltaGroupQuartic810]
  compute_degree
  omega

set_option maxHeartbeats 16000000 in
theorem rhoDeltaGroupQuarticNoA6810_natDegree_le
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hB : B.natDegree = 0) (hC : C.natDegree = 0)
    (hD : D.natDegree = 0) (hE : E.natDegree = 0)
    (hF : F.natDegree = 0) (hG : G.natDegree = 0) :
    (rhoDeltaGroupQuarticNoA6810 A B C D E F).natDegree ≤ 4 * A.natDegree := by
  have hA1 : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  simp only [rhoDeltaGroupQuarticNoA6810]
  compute_degree
  omega

set_option maxHeartbeats 16000000 in
theorem rhoEpsilonGroupQuartic810_natDegree_le
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hB : B.natDegree = 0) (hC : C.natDegree = 0)
    (hD : D.natDegree = 0) (hE : E.natDegree = 0)
    (hF : F.natDegree = 0) (hG : G.natDegree = 0) :
    (rhoEpsilonGroupQuartic810 A B C D E F).natDegree ≤ 3 * A.natDegree := by
  have hA1 : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  simp only [rhoEpsilonGroupQuartic810]
  compute_degree
  omega

set_option maxHeartbeats 16000000 in
theorem rhoZetaGroupQuartic810_natDegree_le
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hB : B.natDegree = 0) (hC : C.natDegree = 0)
    (hD : D.natDegree = 0) (hE : E.natDegree = 0)
    (hF : F.natDegree = 0) (hG : G.natDegree = 0) :
    (rhoZetaGroupQuartic810 A B C D E F).natDegree ≤ 5 * A.natDegree := by
  have hA1 : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  simp only [rhoZetaGroupQuartic810]
  compute_degree
  omega

set_option maxHeartbeats 16000000 in
theorem rhoZetaGroupQuarticNoA5810_natDegree_le
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hB : B.natDegree = 0) (hC : C.natDegree = 0)
    (hD : D.natDegree = 0) (hE : E.natDegree = 0)
    (hF : F.natDegree = 0) (hG : G.natDegree = 0) :
    (rhoZetaGroupQuarticNoA5810 A B C D E F).natDegree ≤ 3 * A.natDegree := by
  have hA1 : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  simp only [rhoZetaGroupQuarticNoA5810]
  compute_degree
  omega

set_option maxHeartbeats 16000000 in
theorem rhoEtaGroupQuartic810_natDegree_le
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hB : B.natDegree = 0) (hC : C.natDegree = 0)
    (hD : D.natDegree = 0) (hE : E.natDegree = 0)
    (hF : F.natDegree = 0) (hG : G.natDegree = 0) :
    (rhoEtaGroupQuartic810 A B C D E F).natDegree ≤ 3 * A.natDegree := by
  have hA1 : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  simp only [rhoEtaGroupQuartic810]
  compute_degree
  omega

set_option maxHeartbeats 16000000 in
theorem rhoThetaGroupQuartic810_natDegree_le
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hB : B.natDegree = 0) (hC : C.natDegree = 0)
    (hD : D.natDegree = 0) (hE : E.natDegree = 0)
    (hF : F.natDegree = 0) (hG : G.natDegree = 0) :
    (rhoThetaGroupQuartic810 A B C D E G).natDegree ≤ 4 * A.natDegree := by
  have hA1 : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  simp only [rhoThetaGroupQuartic810]
  compute_degree
  omega

set_option maxHeartbeats 16000000 in
theorem rhoBaseGroupQuarticNoA8810_natDegree_lt
    (l : k) {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hB : B.natDegree = 0) (hC : C.natDegree = 0)
    (hD : D.natDegree = 0) (hE : E.natDegree = 0)
    (hF : F.natDegree = 0) (hG : G.natDegree = 0) :
    (rhoBaseGroupQuarticNoA8810 l A B C D E F G).natDegree <
      8 * A.natDegree := by
  have hL1 := natDegree_lt_of_le_mul810
    (rhoBaseLetters1Quartic810_natDegree_le hApos hB hC hD hE hF hG)
    (by omega : 4 < 8) hApos
  have hL2 := natDegree_lt_of_le_mul810
    (rhoBaseLetters2Quartic810_natDegree_le hApos hB hC hD hE hF hG)
    (by omega : 4 < 8) hApos
  have hNa := natDegree_lt_of_le_mul810
    (rhoBaseLoadNoA8aQuartic810_natDegree_le l hApos hB hC hD hE hF hG)
    (by omega : 6 < 8) hApos
  have hNb := natDegree_lt_of_le_mul810
    (rhoBaseLoadNoA8bQuartic810_natDegree_le l hApos hB hC hD hE hF hG)
    (by omega : 6 < 8) hApos
  simp only [rhoBaseGroupQuarticNoA8810]
  exact natDegree_add4_lt810 hL1 hL2 hNa hNb

set_option maxHeartbeats 16000000 in
theorem degreeZeroPrimitiveQuarticNoA8810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hB : B.natDegree = 0) (hC : C.natDegree = 0)
    (hD : D.natDegree = 0) (hE : E.natDegree = 0)
    (hF : F.natDegree = 0) (hG : G.natDegree = 0) :
    (degreeZeroPrimitiveQuarticNoA8810 l beta gamma delta epsilon zeta eta
        theta A B C D E F G).natDegree <
      8 * A.natDegree := by
  have hbase :=
    rhoBaseGroupQuarticNoA8810_natDegree_lt l hApos hB hC hD hE hF hG
  have hbeta := natDegree_smul_lt810 beta
    (natDegree_lt_of_le_mul810
      (rhoBetaGroupQuartic810_natDegree_le hApos hB hC hD hE hF hG)
      (by omega : 7 < 8) hApos)
  have hgamma := natDegree_smul_lt810 gamma
    (natDegree_lt_of_le_mul810
      (rhoGammaGroupQuartic810_natDegree_le hApos hB hC hD hE hF hG)
      (by omega : 3 < 8) hApos)
  have hdelta := natDegree_smul_lt810 delta
    (natDegree_lt_of_le_mul810
      (rhoDeltaGroupQuartic810_natDegree_le hApos hB hC hD hE hF hG)
      (by omega : 6 < 8) hApos)
  have heps := natDegree_smul_lt810 epsilon
    (natDegree_lt_of_le_mul810
      (rhoEpsilonGroupQuartic810_natDegree_le hApos hB hC hD hE hF hG)
      (by omega : 3 < 8) hApos)
  have hzeta := natDegree_smul_lt810 zeta
    (natDegree_lt_of_le_mul810
      (rhoZetaGroupQuartic810_natDegree_le hApos hB hC hD hE hF hG)
      (by omega : 5 < 8) hApos)
  have heta := natDegree_smul_lt810 eta
    (natDegree_lt_of_le_mul810
      (rhoEtaGroupQuartic810_natDegree_le hApos hB hC hD hE hF hG)
      (by omega : 3 < 8) hApos)
  have htheta := natDegree_smul_lt810 theta
    (natDegree_lt_of_le_mul810
      (rhoThetaGroupQuartic810_natDegree_le hApos hB hC hD hE hF hG)
      (by omega : 4 < 8) hApos)
  simp only [degreeZeroPrimitiveQuarticNoA8810]
  exact natDegree_add8_lt810 hbase hbeta hgamma hdelta heps hzeta heta htheta

set_option maxHeartbeats 16000000 in
theorem degreeZeroPrimitiveQuarticNoBetaA7_l0810_natDegree_lt
    (beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hB : B.natDegree = 0) (hC : C.natDegree = 0)
    (hD : D.natDegree = 0) (hE : E.natDegree = 0)
    (hF : F.natDegree = 0) (hG : G.natDegree = 0) :
    (degreeZeroPrimitiveQuarticNoBetaA7_l0810 beta gamma delta epsilon zeta
        eta theta A B C D E F G).natDegree <
      7 * A.natDegree := by
  have hL1 := natDegree_lt_of_le_mul810
    (rhoBaseLetters1Quartic810_natDegree_le hApos hB hC hD hE hF hG)
    (by omega : 4 < 7) hApos
  have hL2 := natDegree_lt_of_le_mul810
    (rhoBaseLetters2Quartic810_natDegree_le hApos hB hC hD hE hF hG)
    (by omega : 4 < 7) hApos
  have hbeta := natDegree_smul_lt810 beta
    (natDegree_lt_of_le_mul810
      (rhoBetaGroupQuarticNoA7810_natDegree_le hApos hB hC hD hE hF hG)
      (by omega : 5 < 7) hApos)
  have hgamma := natDegree_smul_lt810 gamma
    (natDegree_lt_of_le_mul810
      (rhoGammaGroupQuartic810_natDegree_le hApos hB hC hD hE hF hG)
      (by omega : 3 < 7) hApos)
  have hdelta := natDegree_smul_lt810 delta
    (natDegree_lt_of_le_mul810
      (rhoDeltaGroupQuartic810_natDegree_le hApos hB hC hD hE hF hG)
      (by omega : 6 < 7) hApos)
  have heps := natDegree_smul_lt810 epsilon
    (natDegree_lt_of_le_mul810
      (rhoEpsilonGroupQuartic810_natDegree_le hApos hB hC hD hE hF hG)
      (by omega : 3 < 7) hApos)
  have hzeta := natDegree_smul_lt810 zeta
    (natDegree_lt_of_le_mul810
      (rhoZetaGroupQuartic810_natDegree_le hApos hB hC hD hE hF hG)
      (by omega : 5 < 7) hApos)
  have heta := natDegree_smul_lt810 eta
    (natDegree_lt_of_le_mul810
      (rhoEtaGroupQuartic810_natDegree_le hApos hB hC hD hE hF hG)
      (by omega : 3 < 7) hApos)
  have htheta := natDegree_smul_lt810 theta
    (natDegree_lt_of_le_mul810
      (rhoThetaGroupQuartic810_natDegree_le hApos hB hC hD hE hF hG)
      (by omega : 4 < 7) hApos)
  have hletters := natDegree_add_lt810 hL1 hL2
  simp only [degreeZeroPrimitiveQuarticNoBetaA7_l0810]
  exact natDegree_add8_lt810 hletters hbeta hgamma hdelta heps hzeta heta htheta

set_option maxHeartbeats 16000000 in
theorem degreeZeroPrimitiveQuarticNoDeltaA6_l0beta0810_natDegree_lt
    (gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hB : B.natDegree = 0) (hC : C.natDegree = 0)
    (hD : D.natDegree = 0) (hE : E.natDegree = 0)
    (hF : F.natDegree = 0) (hG : G.natDegree = 0) :
    (degreeZeroPrimitiveQuarticNoDeltaA6_l0beta0810 gamma delta epsilon zeta
        eta theta A B C D E F G).natDegree <
      6 * A.natDegree := by
  have hL1 := natDegree_lt_of_le_mul810
    (rhoBaseLetters1Quartic810_natDegree_le hApos hB hC hD hE hF hG)
    (by omega : 4 < 6) hApos
  have hL2 := natDegree_lt_of_le_mul810
    (rhoBaseLetters2Quartic810_natDegree_le hApos hB hC hD hE hF hG)
    (by omega : 4 < 6) hApos
  have hgamma := natDegree_smul_lt810 gamma
    (natDegree_lt_of_le_mul810
      (rhoGammaGroupQuartic810_natDegree_le hApos hB hC hD hE hF hG)
      (by omega : 3 < 6) hApos)
  have hdelta := natDegree_smul_lt810 delta
    (natDegree_lt_of_le_mul810
      (rhoDeltaGroupQuarticNoA6810_natDegree_le hApos hB hC hD hE hF hG)
      (by omega : 4 < 6) hApos)
  have heps := natDegree_smul_lt810 epsilon
    (natDegree_lt_of_le_mul810
      (rhoEpsilonGroupQuartic810_natDegree_le hApos hB hC hD hE hF hG)
      (by omega : 3 < 6) hApos)
  have hzeta := natDegree_smul_lt810 zeta
    (natDegree_lt_of_le_mul810
      (rhoZetaGroupQuartic810_natDegree_le hApos hB hC hD hE hF hG)
      (by omega : 5 < 6) hApos)
  have heta := natDegree_smul_lt810 eta
    (natDegree_lt_of_le_mul810
      (rhoEtaGroupQuartic810_natDegree_le hApos hB hC hD hE hF hG)
      (by omega : 3 < 6) hApos)
  have htheta := natDegree_smul_lt810 theta
    (natDegree_lt_of_le_mul810
      (rhoThetaGroupQuartic810_natDegree_le hApos hB hC hD hE hF hG)
      (by omega : 4 < 6) hApos)
  simp only [degreeZeroPrimitiveQuarticNoDeltaA6_l0beta0810]
  exact natDegree_add8_lt810 hL1 hL2 hgamma hdelta heps hzeta heta htheta

set_option maxHeartbeats 32000000 in
theorem degreeZeroPrimitiveQuarticNoZetaA5_l0beta0delta0810_natDegree_lt
    (gamma epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hB : B.natDegree = 0) (hC : C.natDegree = 0)
    (hD : D.natDegree = 0) (hE : E.natDegree = 0)
    (hF : F.natDegree = 0) (hG : G.natDegree = 0) :
    (degreeZeroPrimitiveQuarticNoZetaA5_l0beta0delta0810 gamma epsilon zeta
        eta theta A B C D E F G).natDegree <
      5 * A.natDegree := by
  have hL1 := natDegree_lt_of_le_mul810
    (rhoBaseLetters1Quartic810_natDegree_le hApos hB hC hD hE hF hG)
    (by omega : 4 < 5) hApos
  have hL2 := natDegree_lt_of_le_mul810
    (rhoBaseLetters2Quartic810_natDegree_le hApos hB hC hD hE hF hG)
    (by omega : 4 < 5) hApos
  have hgamma := natDegree_smul_lt810 gamma
    (natDegree_lt_of_le_mul810
      (rhoGammaGroupQuartic810_natDegree_le hApos hB hC hD hE hF hG)
      (by omega : 3 < 5) hApos)
  have heps := natDegree_smul_lt810 epsilon
    (natDegree_lt_of_le_mul810
      (rhoEpsilonGroupQuartic810_natDegree_le hApos hB hC hD hE hF hG)
      (by omega : 3 < 5) hApos)
  have hzeta := natDegree_smul_lt810 zeta
    (natDegree_lt_of_le_mul810
      (rhoZetaGroupQuarticNoA5810_natDegree_le hApos hB hC hD hE hF hG)
      (by omega : 3 < 5) hApos)
  have heta := natDegree_smul_lt810 eta
    (natDegree_lt_of_le_mul810
      (rhoEtaGroupQuartic810_natDegree_le hApos hB hC hD hE hF hG)
      (by omega : 3 < 5) hApos)
  have htheta := natDegree_smul_lt810 theta
    (natDegree_lt_of_le_mul810
      (rhoThetaGroupQuartic810_natDegree_le hApos hB hC hD hE hF hG)
      (by omega : 4 < 5) hApos)
  simp only [degreeZeroPrimitiveQuarticNoZetaA5_l0beta0delta0810]
  exact natDegree_add_lt810 (natDegree_add4_lt810 hL1 hL2 hgamma heps)
    (natDegree_add_lt810 hzeta (natDegree_add_lt810 heta htheta))

set_option maxHeartbeats 32000000 in
theorem quarticADominant_constantLetters_impossible_of_l
    {j t : k}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hApos : 0 < A.natDegree)
    (hB : B.natDegree = 0) (hC : C.natDegree = 0)
    (hD : D.natDegree = 0) (hE : E.natDegree = 0)
    (hF : F.natDegree = 0) (hG : G.natDegree = 0)
    (hl : l ≠ 0)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G) =
        Polynomial.C (j / t)) :
    False := by
  have hdeg :
      (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C810 _ (j / t) hjdiv hder
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    omega
  have hc : (1575 / 268435456 * l : k) ≠ 0 :=
    mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hl
  have hlead : (primitiveQuarticLFace810 l A).natDegree = 8 * A.natDegree := by
    simp only [primitiveQuarticLFace810]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :=
    degreeZeroPrimitiveQuarticNoA8810_natDegree_lt l beta gamma delta epsilon
      zeta eta theta hApos hB hC hD hE hF hG
  rw [degreeZeroPrimitiveQuartic810_eq_A8_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  omega

set_option maxHeartbeats 32000000 in
theorem quarticADominant_constantLetters_impossible_of_beta
    {j t : k}
    (beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hApos : 0 < A.natDegree)
    (hB : B.natDegree = 0) (hC : C.natDegree = 0)
    (hD : D.natDegree = 0) (hE : E.natDegree = 0)
    (hF : F.natDegree = 0) (hG : G.natDegree = 0)
    (hbeta : beta ≠ 0)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveQuartic810 0 beta gamma delta epsilon zeta
          eta theta A B C D E F G) =
        Polynomial.C (j / t)) :
    False := by
  have hdeg :
      (degreeZeroPrimitiveQuartic810 0 beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C810 _ (j / t) hjdiv hder
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    omega
  have hc : (25 / 1048576 * beta : k) ≠ 0 :=
    mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hbeta
  have hlead :
      (primitiveQuarticBetaA7Face810 beta A).natDegree = 7 * A.natDegree := by
    simp only [primitiveQuarticBetaA7Face810]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :=
    degreeZeroPrimitiveQuarticNoBetaA7_l0810_natDegree_lt beta gamma delta
      epsilon zeta eta theta hApos hB hC hD hE hF hG
  rw [degreeZeroPrimitiveQuartic810_eq_betaA7_of_l_zero,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  omega

set_option maxHeartbeats 32000000 in
theorem quarticADominant_constantLetters_impossible_of_delta
    {j t : k}
    (gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hApos : 0 < A.natDegree)
    (hB : B.natDegree = 0) (hC : C.natDegree = 0)
    (hD : D.natDegree = 0) (hE : E.natDegree = 0)
    (hF : F.natDegree = 0) (hG : G.natDegree = 0)
    (hdelta : delta ≠ 0)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveQuartic810 0 0 gamma delta epsilon zeta
          eta theta A B C D E F G) =
        Polynomial.C (j / t)) :
    False := by
  have hdeg :
      (degreeZeroPrimitiveQuartic810 0 0 gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C810 _ (j / t) hjdiv hder
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    omega
  have hc : (25 / 262144 * delta : k) ≠ 0 :=
    mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hdelta
  have hlead :
      (primitiveQuarticDeltaA6Face810 delta A).natDegree = 6 * A.natDegree := by
    simp only [primitiveQuarticDeltaA6Face810]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :=
    degreeZeroPrimitiveQuarticNoDeltaA6_l0beta0810_natDegree_lt gamma delta
      epsilon zeta eta theta hApos hB hC hD hE hF hG
  rw [degreeZeroPrimitiveQuartic810_eq_deltaA6_of_l_beta_zero,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  omega

set_option maxHeartbeats 32000000 in
theorem quarticADominant_constantLetters_impossible_of_zeta
    {j t : k}
    (gamma epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hApos : 0 < A.natDegree)
    (hB : B.natDegree = 0) (hC : C.natDegree = 0)
    (hD : D.natDegree = 0) (hE : E.natDegree = 0)
    (hF : F.natDegree = 0) (hG : G.natDegree = 0)
    (hzeta : zeta ≠ 0)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveQuartic810 0 0 gamma 0 epsilon zeta
          eta theta A B C D E F G) =
        Polynomial.C (j / t)) :
    False := by
  have hdeg :
      (degreeZeroPrimitiveQuartic810 0 0 gamma 0 epsilon zeta eta
          theta A B C D E F G).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C810 _ (j / t) hjdiv hder
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    omega
  have hc : (3 / 8192 * zeta : k) ≠ 0 :=
    mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hzeta
  have hlead :
      (primitiveQuarticZetaA5Face810 zeta A).natDegree = 5 * A.natDegree := by
    simp only [primitiveQuarticZetaA5Face810]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :=
    degreeZeroPrimitiveQuarticNoZetaA5_l0beta0delta0810_natDegree_lt gamma
      epsilon zeta eta theta hApos hB hC hD hE hF hG
  rw [degreeZeroPrimitiveQuartic810_eq_zetaA5_of_l_beta_delta_zero,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  omega

end QuarticADominantB3_810

/-! ## Stage B residual (cone `A` branch) -/

section QuarticADominantAssembly810

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 64000000 in
/-- Honest leftover of Stage B on cone `A`.  Closed: the all-constant
`B,…,G` cell when `l`, `β`, `δ` or `ζ` is live, and the even-core
chambers `{C}` and `{E}` after `B = D = F = 0`.  Remaining: the six
singleton σ-argmin cones, mixed σ-argmin cones, load-compete chambers,
the constant-letter cell with `l = β = δ = ζ = 0` (the `θ`/`B³` tie
on `A⁴`), even-core `{G}`, `{C,E}`, `{E,G}`, `{C,G}`, `{C,E,G}`, and
the sibling cone `ABCDEFG`. -/
theorem quarticConeA810_residual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    ∃ (t j lambda cleared l beta gamma delta epsilon zeta eta theta
        cXi cMu cOm : k) (A B C D E F G : k[X]),
      t ≠ 0 ∧
      j ≠ 0 ∧
      j / t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      derivative
          (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
            eta theta A B C D E F G) =
        Polynomial.C (j / t) ∧
      (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0 ∧
      (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0 ∧
      (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree = 0 ∧
      (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree = 0 ∧
      (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0 ∧
      (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0 ∧
      (
        (QuarticRatioConeA810 A B C D E F G ∧
          ((l = 0 ∧ beta = 0 ∧ delta = 0 ∧ zeta = 0) ∨
            ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
                E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0)) ∧
          ¬ (B = 0 ∧ D = 0 ∧ F = 0 ∧ 0 < C.natDegree ∧
              2 * E.natDegree < 3 * C.natDegree ∧
              G.natDegree < 2 * C.natDegree) ∧
          ¬ (B = 0 ∧ D = 0 ∧ F = 0 ∧ 0 < E.natDegree ∧
              3 * C.natDegree < 2 * E.natDegree ∧
              3 * G.natDegree < 2 * E.natDegree)) ∨
        QuarticRatioConeABCDEFG810 A B C D E F G) := by
  obtain ⟨t, j, lambda, cleared, l, beta, gamma, delta, epsilon, zeta,
      eta, theta, cXi, cMu, cOm, A, B, C, D, E, F, G, ht, hj, hjdiv,
      hHsq, hder, hxiDeg, hmuDeg, homiDeg, hkapDeg, hnuDeg, hpiDeg, hdisj⟩ :=
    normalized810ScaleZero_quarticADominantResidual hsource
  refine ⟨t, j, lambda, cleared, l, beta, gamma, delta, epsilon, zeta,
    eta, theta, cXi, cMu, cOm, A, B, C, D, E, F, G, ht, hj, hjdiv, hHsq,
    hder, hxiDeg, hmuDeg, homiDeg, hkapDeg, hnuDeg, hpiDeg, ?_⟩
  rcases hdisj with hA | hABCDEFG
  · refine Or.inl ⟨hA, ?_, ?_, ?_⟩
    · by_cases hconst :
          B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
            E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0
      · rcases hconst with ⟨hB0, hC0, hD0, hE0, hF0, hG0⟩
        by_cases hl0 : l = 0
        · by_cases hb0 : beta = 0
          · by_cases hd0 : delta = 0
            · by_cases hz0 : zeta = 0
              · exact Or.inl ⟨hl0, hb0, hd0, hz0⟩
              · exact (quarticADominant_constantLetters_impossible_of_zeta
                  (j := j) (t := t) gamma epsilon zeta eta theta
                  A B C D E F G hA.1 hB0 hC0 hD0 hE0 hF0 hG0 hz0 hjdiv
                  (by simpa [hl0, hb0, hd0] using hder)).elim
            · exact (quarticADominant_constantLetters_impossible_of_delta
                (j := j) (t := t) gamma delta epsilon zeta eta theta
                A B C D E F G hA.1 hB0 hC0 hD0 hE0 hF0 hG0 hd0 hjdiv
                (by simpa [hl0, hb0] using hder)).elim
          · exact (quarticADominant_constantLetters_impossible_of_beta
              (j := j) (t := t) beta gamma delta epsilon zeta eta theta
              A B C D E F G hA.1 hB0 hC0 hD0 hE0 hF0 hG0 hb0 hjdiv
              (by simpa [hl0] using hder)).elim
        · exact (quarticADominant_constantLetters_impossible_of_l
            (j := j) (t := t) l beta gamma delta epsilon zeta eta theta
            A B C D E F G hA.1 hB0 hC0 hD0 hE0 hF0 hG0 hl0 hjdiv hder).elim
      · exact Or.inr hconst
    · intro hevenC
      rcases hevenC with ⟨hB0, hD0, hF0, hCpos, hElt, hGlt⟩
      have hmu0 :
          (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
              A 0 C 0 E 0 G).natDegree =
            0 := by
        simpa [hB0, hD0, hF0] using hmuDeg
      exact quarticEvenCore_C_impossible l beta gamma delta epsilon zeta eta
        theta A C E G hCpos hElt hGlt hmu0
    · intro hevenE
      rcases hevenE with ⟨hB0, hD0, hF0, hEpos, hClt, hGlt⟩
      have hmu0 :
          (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
              A 0 C 0 E 0 G).natDegree =
            0 := by
        simpa [hB0, hD0, hF0] using hmuDeg
      exact quarticEvenCore_E_impossible l beta gamma delta epsilon zeta eta
        theta A C E G hEpos hClt hGlt hmu0
  · exact Or.inr hABCDEFG

end QuarticADominantAssembly810

#print axioms degreeZeroMuQuartic810_evenCore
#print axioms degreeZeroXiQuartic810_evenCore
#print axioms quarticEvenCore_C_impossible
#print axioms quarticEvenCore_E_impossible
#print axioms quarticADominant_constantLetters_impossible_of_l
#print axioms quarticADominant_constantLetters_impossible_of_beta
#print axioms quarticADominant_constantLetters_impossible_of_delta
#print axioms quarticADominant_constantLetters_impossible_of_zeta
#print axioms quarticConeA810_residual

end Max11DegreeRoutes
