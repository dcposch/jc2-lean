import Grok810ScaleZeroFinalRowScratch
import Grok810RouteAdapterScratch
import Max11SpeedReflectDegLibScratch

/-! # Scale-zero cone elimination for the normalized `(8,10)`, `H = 0` leaf

Continuation of `Grok810ScaleZeroFinalRowScratch` on the constant core
`H = (C t)²`.  That file attached the degree-`0` Keller row on both
constant faces of `N` and reduced `normalized810ScaleZero_impossible` to
the two named residuals `Normalized810ScaleZeroAlignedFinalResidual`
(`λ = 0`) and `Normalized810ScaleZeroNonzeroFinalResidual` (`λ ≠ 0`).
The missing input was the polynomial-trajectory valuation of the free
octic core `(A, B, C₀, D₀, E₀, F₀, G₀)` against `d ρ = C (j / t) ≠ 0`.

This file supplies that trajectory, modelled on the closed `(6,10)`
scale-zero cone chain.  At constant scale the monic octic depression is
a polynomial substitution, so every free-core letter has a representative
in `k[x]`.  The triangular residuals `β,…,θ` of the depressed decic
descend to the ground field, and the grouped primitive is a polynomial
in the core and those ground loads.  Its derivative is the nonzero
constant `j / t`, so the primitive has Newton degree one.

CAS enumeration (`derive_810_scale_zero_cone_elimination.py`) of the
Newton faces of `ρ` on both constant faces of `N` (outer degrees
`(8,10)`, leading `h⁴`, `h⁵` with `h = C t`) identifies unique faces of
degree greater than one, which this file closes by leading-term
elimination.

* Unique-`A` with `L ≠ 0`: the face `A⁸ L` is unique of degree
  `8 deg A ≥ 8`.
* Unique-`A` with `L = 0` and `B` nonconstant: the face `A⁷ B` is unique
  of degree `7 deg A + deg B ≥ 8`.
* Unique-`A` with `L = 0` and `deg B = 0` and combined `A⁷` coefficient
  `51 (385 B + 51 β)` nonzero: the face `A⁷` is unique of degree
  `7 deg A ≥ 7`.
* Unique nonconstant `C₀` with `L ≠ 0`: the face `C₀⁴ L` is unique of
  degree `4 deg C₀ ≥ 4`.
* Unique nonconstant `G₀` with `L ≠ 0`: the face `G₀² L` is unique of
  degree `2 deg G₀ ≥ 2`.
* A constant free core makes the primitive constant, contradicting
  degree one.

The leaf is not closed.  Named remaining cones are recorded by
`normalized810ScaleZero_coneEliminationResidual`.  No total-degree or
twice-prime theorem is used.  No finite-root shortcut is used.  The
theorems `normalized810ScaleZero_impossible` and
`planeKeller810ScaleZeroExclusion_closed` are not claimed.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## Degree bookkeeping -/

section DegreeLemmas810

variable {k : Type*} [Field k] [CharZero k]
set_option maxHeartbeats 64000000 in

theorem natDegree_eq_one_of_derivative_eq_nonzero_C810
    (P : k[X]) (j : k) (hj : j ≠ 0) (h : derivative P = C j) :
    P.natDegree = 1 := by
  have hder : derivative P ≠ 0 := by
    intro hz
    rw [hz] at h
    exact hj (C_eq_zero.mp h.symm)
  have hdegder : (derivative P).natDegree = 0 := by
    rw [h, natDegree_C]
  have hpositive : 0 < P.natDegree :=
    Nat.pos_of_ne_zero (derivative_ne_zero.mp hder)
  rw [natDegree_derivative] at hdegder
  omega
set_option maxHeartbeats 64000000 in

theorem natDegree_add_lt810 {p q : k[X]} {d : ℕ}
    (hp : p.natDegree < d) (hq : q.natDegree < d) :
    (p + q).natDegree < d :=
  (natDegree_add_le p q).trans_lt (max_lt hp hq)
set_option maxHeartbeats 64000000 in

theorem natDegree_add_le810 {p q : k[X]} {d : ℕ}
    (hp : p.natDegree ≤ d) (hq : q.natDegree ≤ d) :
    (p + q).natDegree ≤ d :=
  (natDegree_add_le p q).trans (max_le hp hq)
set_option maxHeartbeats 64000000 in

theorem natDegree_smul_le810 (c : k) (p : k[X]) :
    (c • p).natDegree ≤ p.natDegree := by
  by_cases hc : c = 0
  · rw [hc, zero_smul, natDegree_zero]
    exact Nat.zero_le _
  · rw [natDegree_smul _ hc]
set_option maxHeartbeats 64000000 in

theorem natDegree_smul_lt810 (c : k) {p : k[X]} {d : ℕ}
    (hp : p.natDegree < d) : (c • p).natDegree < d :=
  (natDegree_smul_le810 c p).trans_lt hp
set_option maxHeartbeats 64000000 in

theorem natDegree_smul_le_of_le810 (c : k) {p : k[X]} {d : ℕ}
    (hp : p.natDegree ≤ d) : (c • p).natDegree ≤ d :=
  (natDegree_smul_le810 c p).trans hp
set_option maxHeartbeats 64000000 in

theorem natDegree_eq_zero_of_le_zero {p : k[X]} (h : p.natDegree ≤ 0) :
    p.natDegree = 0 :=
  Nat.eq_zero_of_le_zero h
set_option maxHeartbeats 64000000 in

theorem natDegree_add8_lt810
    {p1 p2 p3 p4 p5 p6 p7 p8 : k[X]} {d : ℕ}
    (h1 : p1.natDegree < d) (h2 : p2.natDegree < d)
    (h3 : p3.natDegree < d) (h4 : p4.natDegree < d)
    (h5 : p5.natDegree < d) (h6 : p6.natDegree < d)
    (h7 : p7.natDegree < d) (h8 : p8.natDegree < d) :
    (p1 + p2 + p3 + p4 + p5 + p6 + p7 + p8).natDegree < d :=
  natDegree_add_lt810
    (natDegree_add_lt810
      (natDegree_add_lt810
        (natDegree_add_lt810
          (natDegree_add_lt810
            (natDegree_add_lt810 (natDegree_add_lt810 h1 h2) h3) h4) h5)
        h6)
      h7)
    h8
set_option maxHeartbeats 64000000 in

theorem natDegree_add8_le810
    {p1 p2 p3 p4 p5 p6 p7 p8 : k[X]} {d : ℕ}
    (h1 : p1.natDegree ≤ d) (h2 : p2.natDegree ≤ d)
    (h3 : p3.natDegree ≤ d) (h4 : p4.natDegree ≤ d)
    (h5 : p5.natDegree ≤ d) (h6 : p6.natDegree ≤ d)
    (h7 : p7.natDegree ≤ d) (h8 : p8.natDegree ≤ d) :
    (p1 + p2 + p3 + p4 + p5 + p6 + p7 + p8).natDegree ≤ d :=
  natDegree_add_le810
    (natDegree_add_le810
      (natDegree_add_le810
        (natDegree_add_le810
          (natDegree_add_le810
            (natDegree_add_le810 (natDegree_add_le810 h1 h2) h3) h4) h5)
        h6)
      h7)
    h8

set_option maxHeartbeats 64000000 in
/-- Unique-max `A` cone: `A` strictly outranks the other six free letters. -/
def UniqueHighACone810 (A B C0 D0 E0 F0 G0 : k[X]) : Prop :=
  0 < A.natDegree ∧
    B.natDegree < A.natDegree ∧
    C0.natDegree < A.natDegree ∧
    D0.natDegree < A.natDegree ∧
    E0.natDegree < A.natDegree ∧
    F0.natDegree < A.natDegree ∧
    G0.natDegree < A.natDegree

set_option maxHeartbeats 64000000 in
/-- Combined `A⁷` coefficient on the unique-`A` chamber `L = 0`,
`deg B = 0`.  CAS: `51 (385 B + 51 β) / 1048576`. -/
def highA_l0_A7Coefficient810 (beta : k) (B : k[X]) : k[X] :=
  (19635 / 1048576 : k) • B + C (2601 / 1048576 * beta : k)

end DegreeLemmas810

/-! ## Polynomial pullback of the grouped primitive -/

section PrimitivePolynomial810

variable {k : Type*} [Field k] [CharZero k]
set_option maxHeartbeats 64000000 in

def rhoBetaGroupPolynomial810 (A B C0 D0 E0 F0 : k[X]) : k[X] :=
  (2601 / 1048576 : k) • A ^ 7
    - (15687 / 262144 : k) • (A ^ 4 * B ^ 2)
    - (189 / 8192 : k) • (A ^ 5 * C0)
    + (567 / 16384 : k) • (A * B ^ 4)
    + (1701 / 8192 : k) • (A ^ 2 * B ^ 2 * C0)
    + (273 / 4096 : k) • (A ^ 3 * C0 ^ 2)
    + (273 / 2048 : k) • (A ^ 3 * B * D0)
    + (483 / 16384 : k) • (A ^ 4 * E0)
    - (91 / 1024 : k) • (B ^ 2 * C0 ^ 2)
    - (7 / 128 : k) • (B ^ 3 * D0)
    - (7 / 128 : k) • (A * C0 ^ 3)
    - (21 / 64 : k) • (A * B * C0 * D0)
    - (77 / 512 : k) • (A * B ^ 2 * E0)
    - (21 / 256 : k) • (A ^ 2 * D0 ^ 2)
    - (77 / 512 : k) • (A ^ 2 * C0 * E0)
    - (35 / 256 : k) • (A ^ 2 * B * F0)
    + (7 / 64 : k) • (C0 * D0 ^ 2)
    + (7 / 64 : k) • (C0 ^ 2 * E0)
    + (7 / 32 : k) • (B * D0 * E0)
    + (7 / 32 : k) • (B * C0 * F0)
    + (7 / 64 : k) • (A * E0 ^ 2)
    + (7 / 32 : k) • (A * D0 * F0)
    - (7 / 16 : k) • F0 ^ 2
set_option maxHeartbeats 64000000 in

def rhoGammaGroupPolynomial810 (A B C0 D0 E0 F0 : k[X]) : k[X] :=
  -(765 / 16384 : k) • (A ^ 5 * B)
    + (135 / 1024 : k) • (A ^ 2 * B ^ 3)
    + (531 / 2048 : k) • (A ^ 3 * B * C0)
    + (63 / 1024 : k) • (A ^ 4 * D0)
    - (27 / 256 : k) • (B ^ 3 * C0)
    - (39 / 128 : k) • (A * B * C0 ^ 2)
    - (75 / 256 : k) • (A * B ^ 2 * D0)
    - (75 / 256 : k) • (A ^ 2 * C0 * D0)
    - (69 / 256 : k) • (A ^ 2 * B * E0)
    - (33 / 512 : k) • (A ^ 3 * F0)
    + (3 / 16 : k) • (C0 ^ 2 * D0)
    + (3 / 16 : k) • (B * D0 ^ 2)
    + (3 / 8 : k) • (B * C0 * E0)
    + (9 / 64 : k) • (B ^ 2 * F0)
    + (3 / 8 : k) • (A * D0 * E0)
    + (9 / 32 : k) • (A * C0 * F0)
    - (3 / 4 : k) • (E0 * F0)
set_option maxHeartbeats 64000000 in

def rhoDeltaGroupPolynomial810 (A B C0 D0 E0 F0 : k[X]) : k[X] :=
  -(2805 / 262144 : k) • A ^ 6
    + (2925 / 16384 : k) • (A ^ 3 * B ^ 2)
    + (1395 / 16384 : k) • (A ^ 4 * C0)
    - (135 / 4096 : k) • B ^ 4
    - (405 / 1024 : k) • (A * B ^ 2 * C0)
    - (195 / 1024 : k) • (A ^ 2 * C0 ^ 2)
    - (195 / 512 : k) • (A ^ 2 * B * D0)
    - (105 / 1024 : k) • (A ^ 3 * E0)
    + (5 / 64 : k) • C0 ^ 3
    + (15 / 32 : k) • (B * C0 * D0)
    + (25 / 128 : k) • (B ^ 2 * E0)
    + (15 / 64 : k) • (A * D0 ^ 2)
    + (25 / 64 : k) • (A * C0 * E0)
    + (5 / 16 : k) • (A * B * F0)
    - (5 / 16 : k) • E0 ^ 2
    - (5 / 8 : k) • (D0 * F0)
set_option maxHeartbeats 64000000 in

def rhoEpsilonGroupPolynomial810 (A B C0 D0 E0 F0 : k[X]) : k[X] :=
  (51 / 512 : k) • (A ^ 4 * B)
    - (9 / 64 : k) • (A * B ^ 3)
    - (27 / 64 : k) • (A ^ 2 * B * C0)
    - (33 / 256 : k) • (A ^ 3 * D0)
    + (1 / 4 : k) • (B * C0 ^ 2)
    + (7 / 32 : k) • (B ^ 2 * D0)
    + (7 / 16 : k) • (A * C0 * D0)
    + (3 / 8 : k) • (A * B * E0)
    + (5 / 32 : k) • (A ^ 2 * F0)
    - (1 / 2 : k) • (D0 * E0)
    - (1 / 2 : k) • (C0 * F0)
set_option maxHeartbeats 64000000 in

def rhoZetaGroupPolynomial810 (A B C0 D0 E0 F0 : k[X]) : k[X] :=
  (153 / 8192 : k) • A ^ 5
    - (405 / 2048 : k) • (A ^ 2 * B ^ 2)
    - (63 / 512 : k) • (A ^ 3 * C0)
    + (27 / 128 : k) • (B ^ 2 * C0)
    + (3 / 16 : k) • (A * C0 ^ 2)
    + (3 / 8 : k) • (A * B * D0)
    + (21 / 128 : k) • (A ^ 2 * E0)
    - (3 / 16 : k) • D0 ^ 2
    - (3 / 8 : k) • (C0 * E0)
    - (3 / 8 : k) • (B * F0)
set_option maxHeartbeats 64000000 in

def rhoEtaGroupPolynomial810 (A B C0 D0 E0 F0 : k[X]) : k[X] :=
  -(51 / 512 : k) • (A ^ 3 * B)
    + (3 / 64 : k) • B ^ 3
    + (9 / 32 : k) • (A * B * C0)
    + (9 / 64 : k) • (A ^ 2 * D0)
    - (1 / 4 : k) • (C0 * D0)
    - (1 / 4 : k) • (B * E0)
    - (1 / 4 : k) • (A * F0)
set_option maxHeartbeats 64000000 in

def rhoThetaGroupPolynomial810 (A B C0 D0 E0 G0 : k[X]) : k[X] :=
  -(51 / 4096 : k) • A ^ 4
    + (9 / 128 : k) • (A * B ^ 2)
    + (9 / 128 : k) • (A ^ 2 * C0)
    - (1 / 16 : k) • C0 ^ 2
    - (1 / 8 : k) • (B * D0)
    - (1 / 8 : k) • (A * E0)
    + (1 / 1 : k) • G0

set_option maxHeartbeats 64000000 in
def rhoBaseGroupPolynomial810 (l : k) (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  (19635 / 1048576 : k) • (A ^ 7 * B)
    + (369495 / 268435456 * l : k) • A ^ 8
    - (17115 / 131072 : k) • (A ^ 4 * B ^ 3)
    - (315 / 2048 : k) • (A ^ 5 * B * C0)
    - (189945 / 4194304 * l : k) • (A ^ 5 * B ^ 2)
    - (3255 / 131072 : k) • (A ^ 6 * D0)
    - (61425 / 4194304 * l : k) • (A ^ 6 * C0)
    + (315 / 8192 : k) • (A * B ^ 5)
    + (1575 / 4096 : k) • (A ^ 2 * B ^ 3 * C0)
    + (14175 / 262144 * l : k) • (A ^ 2 * B ^ 4)
    + (6185 / 16384 : k) • (A ^ 3 * B * C0 ^ 2)
    + (6115 / 16384 : k) • (A ^ 3 * B ^ 2 * D0)
    + (28161 / 131072 * l : k) • (A ^ 3 * B ^ 2 * C0)
    + (1495 / 8192 : k) • (A ^ 4 * C0 * D0)
    + (27279 / 524288 * l : k) • (A ^ 4 * C0 ^ 2)
    + (1425 / 8192 : k) • (A ^ 4 * B * E0)
    + (27279 / 262144 * l : k) • (A ^ 4 * B * D0)
    + (515 / 16384 : k) • (A ^ 5 * F0)
    + (4977 / 262144 * l : k) • (A ^ 5 * E0)
    - (265 / 2048 : k) • (B ^ 3 * C0 ^ 2)
    - (125 / 2048 : k) • (B ^ 4 * D0)
    - (567 / 16384 * l : k) • (B ^ 4 * C0)
    - (255 / 1024 : k) • (A * B * C0 ^ 3)
    - (375 / 512 : k) • (A * B ^ 2 * C0 * D0)
    - (3339 / 16384 * l : k) • (A * B ^ 2 * C0 ^ 2)
    - (235 / 1024 : k) • (A * B ^ 3 * E0)
    - (1071 / 8192 * l : k) • (A * B ^ 3 * D0)
    - (735 / 2048 : k) • (A ^ 2 * C0 ^ 2 * D0)
    - (1071 / 16384 * l : k) • (A ^ 2 * C0 ^ 3)
    - (735 / 2048 : k) • (A ^ 2 * B * D0 ^ 2)
    - (705 / 1024 : k) • (A ^ 2 * B * C0 * E0)
    - (3213 / 8192 * l : k) • (A ^ 2 * B * C0 * D0)
    - (165 / 512 : k) • (A ^ 2 * B ^ 2 * F0)
    - (189 / 1024 * l : k) • (A ^ 2 * B ^ 2 * E0)
    - (455 / 2048 : k) • (A ^ 3 * D0 * E0)
    - (261 / 4096 * l : k) • (A ^ 3 * D0 ^ 2)
    - (425 / 2048 : k) • (A ^ 3 * C0 * F0)
    - (981 / 8192 * l : k) • (A ^ 3 * C0 * E0)
    - (255 / 2048 : k) • (A ^ 3 * B * G0)
    - (459 / 4096 * l : k) • (A ^ 3 * B * F0)
    - (459 / 32768 * l : k) • (A ^ 4 * G0)
    + (15 / 128 : k) • (C0 ^ 3 * D0)
    + (63 / 4096 * l : k) • C0 ^ 4
    + (45 / 128 : k) • (B * C0 * D0 ^ 2)
    + (45 / 128 : k) • (B * C0 ^ 2 * E0)
    + (189 / 1024 * l : k) • (B * C0 ^ 2 * D0)
    + (85 / 256 : k) • (B ^ 2 * D0 * E0)
    + (45 / 512 * l : k) • (B ^ 2 * D0 ^ 2)
    + (85 / 256 : k) • (B ^ 2 * C0 * F0)
    + (45 / 256 * l : k) • (B ^ 2 * C0 * E0)
    + (15 / 256 : k) • (B ^ 3 * G0)
    + (27 / 512 * l : k) • (B ^ 3 * F0)
    + (15 / 128 : k) • (A * D0 ^ 3)
    + (85 / 128 : k) • (A * C0 * D0 * E0)
    + (45 / 256 * l : k) • (A * C0 * D0 ^ 2)
    + (5 / 16 : k) • (A * C0 ^ 2 * F0)
    + (171 / 1024 * l : k) • (A * C0 ^ 2 * E0)
    + (5 / 16 : k) • (A * B * E0 ^ 2)
    + (5 / 8 : k) • (A * B * D0 * F0)
    + (171 / 512 * l : k) • (A * B * D0 * E0)
    + (45 / 128 : k) • (A * B * C0 * G0)
    + (81 / 256 * l : k) • (A * B * C0 * F0)
    + (81 / 1024 * l : k) • (A * B ^ 2 * G0)
    + (75 / 256 : k) • (A ^ 2 * E0 * F0)
    + (81 / 1024 * l : k) • (A ^ 2 * E0 ^ 2)
    + (45 / 256 : k) • (A ^ 2 * D0 * G0)
    + (81 / 512 * l : k) • (A ^ 2 * D0 * F0)
    + (81 / 1024 * l : k) • (A ^ 2 * C0 * G0)
    - (5 / 16 : k) • (D0 * E0 ^ 2)
    - (5 / 16 : k) • (D0 ^ 2 * F0)
    - (9 / 64 * l : k) • (D0 ^ 2 * E0)
    - (5 / 8 : k) • (C0 * E0 * F0)
    - (9 / 64 * l : k) • (C0 * E0 ^ 2)
    - (5 / 16 : k) • (C0 * D0 * G0)
    - (9 / 32 * l : k) • (C0 * D0 * F0)
    - (9 / 128 * l : k) • (C0 ^ 2 * G0)
    - (5 / 16 : k) • (B * F0 ^ 2)
    - (5 / 16 : k) • (B * E0 * G0)
    - (9 / 32 * l : k) • (B * E0 * F0)
    - (9 / 64 * l : k) • (B * D0 * G0)
    - (5 / 16 : k) • (A * F0 * G0)
    - (9 / 64 * l : k) • (A * F0 ^ 2)
    - (9 / 64 * l : k) • (A * E0 * G0)
    + (9 / 16 * l : k) • G0 ^ 2

set_option maxHeartbeats 64000000 in
def rhoBaseGroupHighARest810 (l : k) (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  (19635 / 1048576 : k) • (A ^ 7 * B)
    - (17115 / 131072 : k) • (A ^ 4 * B ^ 3)
    - (315 / 2048 : k) • (A ^ 5 * B * C0)
    - (189945 / 4194304 * l : k) • (A ^ 5 * B ^ 2)
    - (3255 / 131072 : k) • (A ^ 6 * D0)
    - (61425 / 4194304 * l : k) • (A ^ 6 * C0)
    + (315 / 8192 : k) • (A * B ^ 5)
    + (1575 / 4096 : k) • (A ^ 2 * B ^ 3 * C0)
    + (14175 / 262144 * l : k) • (A ^ 2 * B ^ 4)
    + (6185 / 16384 : k) • (A ^ 3 * B * C0 ^ 2)
    + (6115 / 16384 : k) • (A ^ 3 * B ^ 2 * D0)
    + (28161 / 131072 * l : k) • (A ^ 3 * B ^ 2 * C0)
    + (1495 / 8192 : k) • (A ^ 4 * C0 * D0)
    + (27279 / 524288 * l : k) • (A ^ 4 * C0 ^ 2)
    + (1425 / 8192 : k) • (A ^ 4 * B * E0)
    + (27279 / 262144 * l : k) • (A ^ 4 * B * D0)
    + (515 / 16384 : k) • (A ^ 5 * F0)
    + (4977 / 262144 * l : k) • (A ^ 5 * E0)
    - (265 / 2048 : k) • (B ^ 3 * C0 ^ 2)
    - (125 / 2048 : k) • (B ^ 4 * D0)
    - (567 / 16384 * l : k) • (B ^ 4 * C0)
    - (255 / 1024 : k) • (A * B * C0 ^ 3)
    - (375 / 512 : k) • (A * B ^ 2 * C0 * D0)
    - (3339 / 16384 * l : k) • (A * B ^ 2 * C0 ^ 2)
    - (235 / 1024 : k) • (A * B ^ 3 * E0)
    - (1071 / 8192 * l : k) • (A * B ^ 3 * D0)
    - (735 / 2048 : k) • (A ^ 2 * C0 ^ 2 * D0)
    - (1071 / 16384 * l : k) • (A ^ 2 * C0 ^ 3)
    - (735 / 2048 : k) • (A ^ 2 * B * D0 ^ 2)
    - (705 / 1024 : k) • (A ^ 2 * B * C0 * E0)
    - (3213 / 8192 * l : k) • (A ^ 2 * B * C0 * D0)
    - (165 / 512 : k) • (A ^ 2 * B ^ 2 * F0)
    - (189 / 1024 * l : k) • (A ^ 2 * B ^ 2 * E0)
    - (455 / 2048 : k) • (A ^ 3 * D0 * E0)
    - (261 / 4096 * l : k) • (A ^ 3 * D0 ^ 2)
    - (425 / 2048 : k) • (A ^ 3 * C0 * F0)
    - (981 / 8192 * l : k) • (A ^ 3 * C0 * E0)
    - (255 / 2048 : k) • (A ^ 3 * B * G0)
    - (459 / 4096 * l : k) • (A ^ 3 * B * F0)
    - (459 / 32768 * l : k) • (A ^ 4 * G0)
    + (15 / 128 : k) • (C0 ^ 3 * D0)
    + (63 / 4096 * l : k) • C0 ^ 4
    + (45 / 128 : k) • (B * C0 * D0 ^ 2)
    + (45 / 128 : k) • (B * C0 ^ 2 * E0)
    + (189 / 1024 * l : k) • (B * C0 ^ 2 * D0)
    + (85 / 256 : k) • (B ^ 2 * D0 * E0)
    + (45 / 512 * l : k) • (B ^ 2 * D0 ^ 2)
    + (85 / 256 : k) • (B ^ 2 * C0 * F0)
    + (45 / 256 * l : k) • (B ^ 2 * C0 * E0)
    + (15 / 256 : k) • (B ^ 3 * G0)
    + (27 / 512 * l : k) • (B ^ 3 * F0)
    + (15 / 128 : k) • (A * D0 ^ 3)
    + (85 / 128 : k) • (A * C0 * D0 * E0)
    + (45 / 256 * l : k) • (A * C0 * D0 ^ 2)
    + (5 / 16 : k) • (A * C0 ^ 2 * F0)
    + (171 / 1024 * l : k) • (A * C0 ^ 2 * E0)
    + (5 / 16 : k) • (A * B * E0 ^ 2)
    + (5 / 8 : k) • (A * B * D0 * F0)
    + (171 / 512 * l : k) • (A * B * D0 * E0)
    + (45 / 128 : k) • (A * B * C0 * G0)
    + (81 / 256 * l : k) • (A * B * C0 * F0)
    + (81 / 1024 * l : k) • (A * B ^ 2 * G0)
    + (75 / 256 : k) • (A ^ 2 * E0 * F0)
    + (81 / 1024 * l : k) • (A ^ 2 * E0 ^ 2)
    + (45 / 256 : k) • (A ^ 2 * D0 * G0)
    + (81 / 512 * l : k) • (A ^ 2 * D0 * F0)
    + (81 / 1024 * l : k) • (A ^ 2 * C0 * G0)
    - (5 / 16 : k) • (D0 * E0 ^ 2)
    - (5 / 16 : k) • (D0 ^ 2 * F0)
    - (9 / 64 * l : k) • (D0 ^ 2 * E0)
    - (5 / 8 : k) • (C0 * E0 * F0)
    - (9 / 64 * l : k) • (C0 * E0 ^ 2)
    - (5 / 16 : k) • (C0 * D0 * G0)
    - (9 / 32 * l : k) • (C0 * D0 * F0)
    - (9 / 128 * l : k) • (C0 ^ 2 * G0)
    - (5 / 16 : k) • (B * F0 ^ 2)
    - (5 / 16 : k) • (B * E0 * G0)
    - (9 / 32 * l : k) • (B * E0 * F0)
    - (9 / 64 * l : k) • (B * D0 * G0)
    - (5 / 16 : k) • (A * F0 * G0)
    - (9 / 64 * l : k) • (A * F0 ^ 2)
    - (9 / 64 * l : k) • (A * E0 * G0)
    + (9 / 16 * l : k) • G0 ^ 2

set_option maxHeartbeats 64000000 in
def rhoBaseGroupHighA_noA7B_Rest810 (l : k) (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(17115 / 131072 : k) • (A ^ 4 * B ^ 3)
    - (315 / 2048 : k) • (A ^ 5 * B * C0)
    - (189945 / 4194304 * l : k) • (A ^ 5 * B ^ 2)
    - (3255 / 131072 : k) • (A ^ 6 * D0)
    - (61425 / 4194304 * l : k) • (A ^ 6 * C0)
    + (315 / 8192 : k) • (A * B ^ 5)
    + (1575 / 4096 : k) • (A ^ 2 * B ^ 3 * C0)
    + (14175 / 262144 * l : k) • (A ^ 2 * B ^ 4)
    + (6185 / 16384 : k) • (A ^ 3 * B * C0 ^ 2)
    + (6115 / 16384 : k) • (A ^ 3 * B ^ 2 * D0)
    + (28161 / 131072 * l : k) • (A ^ 3 * B ^ 2 * C0)
    + (1495 / 8192 : k) • (A ^ 4 * C0 * D0)
    + (27279 / 524288 * l : k) • (A ^ 4 * C0 ^ 2)
    + (1425 / 8192 : k) • (A ^ 4 * B * E0)
    + (27279 / 262144 * l : k) • (A ^ 4 * B * D0)
    + (515 / 16384 : k) • (A ^ 5 * F0)
    + (4977 / 262144 * l : k) • (A ^ 5 * E0)
    - (265 / 2048 : k) • (B ^ 3 * C0 ^ 2)
    - (125 / 2048 : k) • (B ^ 4 * D0)
    - (567 / 16384 * l : k) • (B ^ 4 * C0)
    - (255 / 1024 : k) • (A * B * C0 ^ 3)
    - (375 / 512 : k) • (A * B ^ 2 * C0 * D0)
    - (3339 / 16384 * l : k) • (A * B ^ 2 * C0 ^ 2)
    - (235 / 1024 : k) • (A * B ^ 3 * E0)
    - (1071 / 8192 * l : k) • (A * B ^ 3 * D0)
    - (735 / 2048 : k) • (A ^ 2 * C0 ^ 2 * D0)
    - (1071 / 16384 * l : k) • (A ^ 2 * C0 ^ 3)
    - (735 / 2048 : k) • (A ^ 2 * B * D0 ^ 2)
    - (705 / 1024 : k) • (A ^ 2 * B * C0 * E0)
    - (3213 / 8192 * l : k) • (A ^ 2 * B * C0 * D0)
    - (165 / 512 : k) • (A ^ 2 * B ^ 2 * F0)
    - (189 / 1024 * l : k) • (A ^ 2 * B ^ 2 * E0)
    - (455 / 2048 : k) • (A ^ 3 * D0 * E0)
    - (261 / 4096 * l : k) • (A ^ 3 * D0 ^ 2)
    - (425 / 2048 : k) • (A ^ 3 * C0 * F0)
    - (981 / 8192 * l : k) • (A ^ 3 * C0 * E0)
    - (255 / 2048 : k) • (A ^ 3 * B * G0)
    - (459 / 4096 * l : k) • (A ^ 3 * B * F0)
    - (459 / 32768 * l : k) • (A ^ 4 * G0)
    + (15 / 128 : k) • (C0 ^ 3 * D0)
    + (63 / 4096 * l : k) • C0 ^ 4
    + (45 / 128 : k) • (B * C0 * D0 ^ 2)
    + (45 / 128 : k) • (B * C0 ^ 2 * E0)
    + (189 / 1024 * l : k) • (B * C0 ^ 2 * D0)
    + (85 / 256 : k) • (B ^ 2 * D0 * E0)
    + (45 / 512 * l : k) • (B ^ 2 * D0 ^ 2)
    + (85 / 256 : k) • (B ^ 2 * C0 * F0)
    + (45 / 256 * l : k) • (B ^ 2 * C0 * E0)
    + (15 / 256 : k) • (B ^ 3 * G0)
    + (27 / 512 * l : k) • (B ^ 3 * F0)
    + (15 / 128 : k) • (A * D0 ^ 3)
    + (85 / 128 : k) • (A * C0 * D0 * E0)
    + (45 / 256 * l : k) • (A * C0 * D0 ^ 2)
    + (5 / 16 : k) • (A * C0 ^ 2 * F0)
    + (171 / 1024 * l : k) • (A * C0 ^ 2 * E0)
    + (5 / 16 : k) • (A * B * E0 ^ 2)
    + (5 / 8 : k) • (A * B * D0 * F0)
    + (171 / 512 * l : k) • (A * B * D0 * E0)
    + (45 / 128 : k) • (A * B * C0 * G0)
    + (81 / 256 * l : k) • (A * B * C0 * F0)
    + (81 / 1024 * l : k) • (A * B ^ 2 * G0)
    + (75 / 256 : k) • (A ^ 2 * E0 * F0)
    + (81 / 1024 * l : k) • (A ^ 2 * E0 ^ 2)
    + (45 / 256 : k) • (A ^ 2 * D0 * G0)
    + (81 / 512 * l : k) • (A ^ 2 * D0 * F0)
    + (81 / 1024 * l : k) • (A ^ 2 * C0 * G0)
    - (5 / 16 : k) • (D0 * E0 ^ 2)
    - (5 / 16 : k) • (D0 ^ 2 * F0)
    - (9 / 64 * l : k) • (D0 ^ 2 * E0)
    - (5 / 8 : k) • (C0 * E0 * F0)
    - (9 / 64 * l : k) • (C0 * E0 ^ 2)
    - (5 / 16 : k) • (C0 * D0 * G0)
    - (9 / 32 * l : k) • (C0 * D0 * F0)
    - (9 / 128 * l : k) • (C0 ^ 2 * G0)
    - (5 / 16 : k) • (B * F0 ^ 2)
    - (5 / 16 : k) • (B * E0 * G0)
    - (9 / 32 * l : k) • (B * E0 * F0)
    - (9 / 64 * l : k) • (B * D0 * G0)
    - (5 / 16 : k) • (A * F0 * G0)
    - (9 / 64 * l : k) • (A * F0 ^ 2)
    - (9 / 64 * l : k) • (A * E0 * G0)
    + (9 / 16 * l : k) • G0 ^ 2
set_option maxHeartbeats 64000000 in

def rhoBetaGroupNoA7Polynomial810 (A B C0 D0 E0 F0 : k[X]) : k[X] :=
  -(15687 / 262144 : k) • (A ^ 4 * B ^ 2)
    - (189 / 8192 : k) • (A ^ 5 * C0)
    + (567 / 16384 : k) • (A * B ^ 4)
    + (1701 / 8192 : k) • (A ^ 2 * B ^ 2 * C0)
    + (273 / 4096 : k) • (A ^ 3 * C0 ^ 2)
    + (273 / 2048 : k) • (A ^ 3 * B * D0)
    + (483 / 16384 : k) • (A ^ 4 * E0)
    - (91 / 1024 : k) • (B ^ 2 * C0 ^ 2)
    - (7 / 128 : k) • (B ^ 3 * D0)
    - (7 / 128 : k) • (A * C0 ^ 3)
    - (21 / 64 : k) • (A * B * C0 * D0)
    - (77 / 512 : k) • (A * B ^ 2 * E0)
    - (21 / 256 : k) • (A ^ 2 * D0 ^ 2)
    - (77 / 512 : k) • (A ^ 2 * C0 * E0)
    - (35 / 256 : k) • (A ^ 2 * B * F0)
    + (7 / 64 : k) • (C0 * D0 ^ 2)
    + (7 / 64 : k) • (C0 ^ 2 * E0)
    + (7 / 32 : k) • (B * D0 * E0)
    + (7 / 32 : k) • (B * C0 * F0)
    + (7 / 64 : k) • (A * E0 ^ 2)
    + (7 / 32 : k) • (A * D0 * F0)
    - (7 / 16 : k) • F0 ^ 2


set_option maxHeartbeats 64000000 in
def rhoBaseGroupHighC0Rest810 (l : k) (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  (19635 / 1048576 : k) • (A ^ 7 * B)
    + (369495 / 268435456 * l : k) • A ^ 8
    - (17115 / 131072 : k) • (A ^ 4 * B ^ 3)
    - (315 / 2048 : k) • (A ^ 5 * B * C0)
    - (189945 / 4194304 * l : k) • (A ^ 5 * B ^ 2)
    - (3255 / 131072 : k) • (A ^ 6 * D0)
    - (61425 / 4194304 * l : k) • (A ^ 6 * C0)
    + (315 / 8192 : k) • (A * B ^ 5)
    + (1575 / 4096 : k) • (A ^ 2 * B ^ 3 * C0)
    + (14175 / 262144 * l : k) • (A ^ 2 * B ^ 4)
    + (6185 / 16384 : k) • (A ^ 3 * B * C0 ^ 2)
    + (6115 / 16384 : k) • (A ^ 3 * B ^ 2 * D0)
    + (28161 / 131072 * l : k) • (A ^ 3 * B ^ 2 * C0)
    + (1495 / 8192 : k) • (A ^ 4 * C0 * D0)
    + (27279 / 524288 * l : k) • (A ^ 4 * C0 ^ 2)
    + (1425 / 8192 : k) • (A ^ 4 * B * E0)
    + (27279 / 262144 * l : k) • (A ^ 4 * B * D0)
    + (515 / 16384 : k) • (A ^ 5 * F0)
    + (4977 / 262144 * l : k) • (A ^ 5 * E0)
    - (265 / 2048 : k) • (B ^ 3 * C0 ^ 2)
    - (125 / 2048 : k) • (B ^ 4 * D0)
    - (567 / 16384 * l : k) • (B ^ 4 * C0)
    - (255 / 1024 : k) • (A * B * C0 ^ 3)
    - (375 / 512 : k) • (A * B ^ 2 * C0 * D0)
    - (3339 / 16384 * l : k) • (A * B ^ 2 * C0 ^ 2)
    - (235 / 1024 : k) • (A * B ^ 3 * E0)
    - (1071 / 8192 * l : k) • (A * B ^ 3 * D0)
    - (735 / 2048 : k) • (A ^ 2 * C0 ^ 2 * D0)
    - (1071 / 16384 * l : k) • (A ^ 2 * C0 ^ 3)
    - (735 / 2048 : k) • (A ^ 2 * B * D0 ^ 2)
    - (705 / 1024 : k) • (A ^ 2 * B * C0 * E0)
    - (3213 / 8192 * l : k) • (A ^ 2 * B * C0 * D0)
    - (165 / 512 : k) • (A ^ 2 * B ^ 2 * F0)
    - (189 / 1024 * l : k) • (A ^ 2 * B ^ 2 * E0)
    - (455 / 2048 : k) • (A ^ 3 * D0 * E0)
    - (261 / 4096 * l : k) • (A ^ 3 * D0 ^ 2)
    - (425 / 2048 : k) • (A ^ 3 * C0 * F0)
    - (981 / 8192 * l : k) • (A ^ 3 * C0 * E0)
    - (255 / 2048 : k) • (A ^ 3 * B * G0)
    - (459 / 4096 * l : k) • (A ^ 3 * B * F0)
    - (459 / 32768 * l : k) • (A ^ 4 * G0)
    + (15 / 128 : k) • (C0 ^ 3 * D0)
    + (45 / 128 : k) • (B * C0 * D0 ^ 2)
    + (45 / 128 : k) • (B * C0 ^ 2 * E0)
    + (189 / 1024 * l : k) • (B * C0 ^ 2 * D0)
    + (85 / 256 : k) • (B ^ 2 * D0 * E0)
    + (45 / 512 * l : k) • (B ^ 2 * D0 ^ 2)
    + (85 / 256 : k) • (B ^ 2 * C0 * F0)
    + (45 / 256 * l : k) • (B ^ 2 * C0 * E0)
    + (15 / 256 : k) • (B ^ 3 * G0)
    + (27 / 512 * l : k) • (B ^ 3 * F0)
    + (15 / 128 : k) • (A * D0 ^ 3)
    + (85 / 128 : k) • (A * C0 * D0 * E0)
    + (45 / 256 * l : k) • (A * C0 * D0 ^ 2)
    + (5 / 16 : k) • (A * C0 ^ 2 * F0)
    + (171 / 1024 * l : k) • (A * C0 ^ 2 * E0)
    + (5 / 16 : k) • (A * B * E0 ^ 2)
    + (5 / 8 : k) • (A * B * D0 * F0)
    + (171 / 512 * l : k) • (A * B * D0 * E0)
    + (45 / 128 : k) • (A * B * C0 * G0)
    + (81 / 256 * l : k) • (A * B * C0 * F0)
    + (81 / 1024 * l : k) • (A * B ^ 2 * G0)
    + (75 / 256 : k) • (A ^ 2 * E0 * F0)
    + (81 / 1024 * l : k) • (A ^ 2 * E0 ^ 2)
    + (45 / 256 : k) • (A ^ 2 * D0 * G0)
    + (81 / 512 * l : k) • (A ^ 2 * D0 * F0)
    + (81 / 1024 * l : k) • (A ^ 2 * C0 * G0)
    - (5 / 16 : k) • (D0 * E0 ^ 2)
    - (5 / 16 : k) • (D0 ^ 2 * F0)
    - (9 / 64 * l : k) • (D0 ^ 2 * E0)
    - (5 / 8 : k) • (C0 * E0 * F0)
    - (9 / 64 * l : k) • (C0 * E0 ^ 2)
    - (5 / 16 : k) • (C0 * D0 * G0)
    - (9 / 32 * l : k) • (C0 * D0 * F0)
    - (9 / 128 * l : k) • (C0 ^ 2 * G0)
    - (5 / 16 : k) • (B * F0 ^ 2)
    - (5 / 16 : k) • (B * E0 * G0)
    - (9 / 32 * l : k) • (B * E0 * F0)
    - (9 / 64 * l : k) • (B * D0 * G0)
    - (5 / 16 : k) • (A * F0 * G0)
    - (9 / 64 * l : k) • (A * F0 ^ 2)
    - (9 / 64 * l : k) • (A * E0 * G0)
    + (9 / 16 * l : k) • G0 ^ 2

set_option maxHeartbeats 64000000 in
def rhoBaseGroupHighG0Rest810 (l : k) (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  (19635 / 1048576 : k) • (A ^ 7 * B)
    + (369495 / 268435456 * l : k) • A ^ 8
    - (17115 / 131072 : k) • (A ^ 4 * B ^ 3)
    - (315 / 2048 : k) • (A ^ 5 * B * C0)
    - (189945 / 4194304 * l : k) • (A ^ 5 * B ^ 2)
    - (3255 / 131072 : k) • (A ^ 6 * D0)
    - (61425 / 4194304 * l : k) • (A ^ 6 * C0)
    + (315 / 8192 : k) • (A * B ^ 5)
    + (1575 / 4096 : k) • (A ^ 2 * B ^ 3 * C0)
    + (14175 / 262144 * l : k) • (A ^ 2 * B ^ 4)
    + (6185 / 16384 : k) • (A ^ 3 * B * C0 ^ 2)
    + (6115 / 16384 : k) • (A ^ 3 * B ^ 2 * D0)
    + (28161 / 131072 * l : k) • (A ^ 3 * B ^ 2 * C0)
    + (1495 / 8192 : k) • (A ^ 4 * C0 * D0)
    + (27279 / 524288 * l : k) • (A ^ 4 * C0 ^ 2)
    + (1425 / 8192 : k) • (A ^ 4 * B * E0)
    + (27279 / 262144 * l : k) • (A ^ 4 * B * D0)
    + (515 / 16384 : k) • (A ^ 5 * F0)
    + (4977 / 262144 * l : k) • (A ^ 5 * E0)
    - (265 / 2048 : k) • (B ^ 3 * C0 ^ 2)
    - (125 / 2048 : k) • (B ^ 4 * D0)
    - (567 / 16384 * l : k) • (B ^ 4 * C0)
    - (255 / 1024 : k) • (A * B * C0 ^ 3)
    - (375 / 512 : k) • (A * B ^ 2 * C0 * D0)
    - (3339 / 16384 * l : k) • (A * B ^ 2 * C0 ^ 2)
    - (235 / 1024 : k) • (A * B ^ 3 * E0)
    - (1071 / 8192 * l : k) • (A * B ^ 3 * D0)
    - (735 / 2048 : k) • (A ^ 2 * C0 ^ 2 * D0)
    - (1071 / 16384 * l : k) • (A ^ 2 * C0 ^ 3)
    - (735 / 2048 : k) • (A ^ 2 * B * D0 ^ 2)
    - (705 / 1024 : k) • (A ^ 2 * B * C0 * E0)
    - (3213 / 8192 * l : k) • (A ^ 2 * B * C0 * D0)
    - (165 / 512 : k) • (A ^ 2 * B ^ 2 * F0)
    - (189 / 1024 * l : k) • (A ^ 2 * B ^ 2 * E0)
    - (455 / 2048 : k) • (A ^ 3 * D0 * E0)
    - (261 / 4096 * l : k) • (A ^ 3 * D0 ^ 2)
    - (425 / 2048 : k) • (A ^ 3 * C0 * F0)
    - (981 / 8192 * l : k) • (A ^ 3 * C0 * E0)
    - (255 / 2048 : k) • (A ^ 3 * B * G0)
    - (459 / 4096 * l : k) • (A ^ 3 * B * F0)
    - (459 / 32768 * l : k) • (A ^ 4 * G0)
    + (15 / 128 : k) • (C0 ^ 3 * D0)
    + (63 / 4096 * l : k) • C0 ^ 4
    + (45 / 128 : k) • (B * C0 * D0 ^ 2)
    + (45 / 128 : k) • (B * C0 ^ 2 * E0)
    + (189 / 1024 * l : k) • (B * C0 ^ 2 * D0)
    + (85 / 256 : k) • (B ^ 2 * D0 * E0)
    + (45 / 512 * l : k) • (B ^ 2 * D0 ^ 2)
    + (85 / 256 : k) • (B ^ 2 * C0 * F0)
    + (45 / 256 * l : k) • (B ^ 2 * C0 * E0)
    + (15 / 256 : k) • (B ^ 3 * G0)
    + (27 / 512 * l : k) • (B ^ 3 * F0)
    + (15 / 128 : k) • (A * D0 ^ 3)
    + (85 / 128 : k) • (A * C0 * D0 * E0)
    + (45 / 256 * l : k) • (A * C0 * D0 ^ 2)
    + (5 / 16 : k) • (A * C0 ^ 2 * F0)
    + (171 / 1024 * l : k) • (A * C0 ^ 2 * E0)
    + (5 / 16 : k) • (A * B * E0 ^ 2)
    + (5 / 8 : k) • (A * B * D0 * F0)
    + (171 / 512 * l : k) • (A * B * D0 * E0)
    + (45 / 128 : k) • (A * B * C0 * G0)
    + (81 / 256 * l : k) • (A * B * C0 * F0)
    + (81 / 1024 * l : k) • (A * B ^ 2 * G0)
    + (75 / 256 : k) • (A ^ 2 * E0 * F0)
    + (81 / 1024 * l : k) • (A ^ 2 * E0 ^ 2)
    + (45 / 256 : k) • (A ^ 2 * D0 * G0)
    + (81 / 512 * l : k) • (A ^ 2 * D0 * F0)
    + (81 / 1024 * l : k) • (A ^ 2 * C0 * G0)
    - (5 / 16 : k) • (D0 * E0 ^ 2)
    - (5 / 16 : k) • (D0 ^ 2 * F0)
    - (9 / 64 * l : k) • (D0 ^ 2 * E0)
    - (5 / 8 : k) • (C0 * E0 * F0)
    - (9 / 64 * l : k) • (C0 * E0 ^ 2)
    - (5 / 16 : k) • (C0 * D0 * G0)
    - (9 / 32 * l : k) • (C0 * D0 * F0)
    - (9 / 128 * l : k) • (C0 ^ 2 * G0)
    - (5 / 16 : k) • (B * F0 ^ 2)
    - (5 / 16 : k) • (B * E0 * G0)
    - (9 / 32 * l : k) • (B * E0 * F0)
    - (9 / 64 * l : k) • (B * D0 * G0)
    - (5 / 16 : k) • (A * F0 * G0)
    - (9 / 64 * l : k) • (A * F0 ^ 2)
    - (9 / 64 * l : k) • (A * E0 * G0)


set_option maxHeartbeats 64000000 in
/-- Integrated grouped primitive after the triangular residuals are
ground constants. -/
def degreeZeroIntegratedPrimitive810
    {F : Type*} [Field F] [CharZero F]
    (L A B C0 D0 E0 F0 G0 beta gamma delta epsilon zeta eta theta : F) : F :=
  rhoBaseGroup810 L A B C0 D0 E0 F0 G0 +
    beta * rhoBetaGroup810 A B C0 D0 E0 F0 +
    gamma * rhoGammaGroup810 A B C0 D0 E0 F0 +
    delta * rhoDeltaGroup810 A B C0 D0 E0 F0 +
    epsilon * rhoEpsilonGroup810 A B C0 D0 E0 F0 +
    zeta * rhoZetaGroup810 A B C0 D0 E0 F0 +
    eta * rhoEtaGroup810 A B C0 D0 E0 F0 +
    theta * rhoThetaGroup810 A B C0 D0 E0 G0

set_option maxHeartbeats 64000000 in
/-- Polynomial representative of the integrated primitive. -/
def degreeZeroPrimitivePolynomial810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  rhoBaseGroupPolynomial810 l A B C0 D0 E0 F0 G0 +
    beta • rhoBetaGroupPolynomial810 A B C0 D0 E0 F0 +
    gamma • rhoGammaGroupPolynomial810 A B C0 D0 E0 F0 +
    delta • rhoDeltaGroupPolynomial810 A B C0 D0 E0 F0 +
    epsilon • rhoEpsilonGroupPolynomial810 A B C0 D0 E0 F0 +
    zeta • rhoZetaGroupPolynomial810 A B C0 D0 E0 F0 +
    eta • rhoEtaGroupPolynomial810 A B C0 D0 E0 F0 +
    theta • rhoThetaGroupPolynomial810 A B C0 D0 E0 G0

set_option maxHeartbeats 64000000 in
/-- Primitive with the unique-`A` face `A⁸ L` deleted. -/
def degreeZeroPrimitiveHighARest810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  rhoBaseGroupHighARest810 l A B C0 D0 E0 F0 G0 +
    beta • rhoBetaGroupPolynomial810 A B C0 D0 E0 F0 +
    gamma • rhoGammaGroupPolynomial810 A B C0 D0 E0 F0 +
    delta • rhoDeltaGroupPolynomial810 A B C0 D0 E0 F0 +
    epsilon • rhoEpsilonGroupPolynomial810 A B C0 D0 E0 F0 +
    zeta • rhoZetaGroupPolynomial810 A B C0 D0 E0 F0 +
    eta • rhoEtaGroupPolynomial810 A B C0 D0 E0 F0 +
    theta • rhoThetaGroupPolynomial810 A B C0 D0 E0 G0

set_option maxHeartbeats 64000000 in
/-- Primitive with `A⁸ L` and `A⁷ B` deleted. -/
def degreeZeroPrimitiveHighA_noA7B_Rest810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  rhoBaseGroupHighA_noA7B_Rest810 l A B C0 D0 E0 F0 G0 +
    beta • rhoBetaGroupPolynomial810 A B C0 D0 E0 F0 +
    gamma • rhoGammaGroupPolynomial810 A B C0 D0 E0 F0 +
    delta • rhoDeltaGroupPolynomial810 A B C0 D0 E0 F0 +
    epsilon • rhoEpsilonGroupPolynomial810 A B C0 D0 E0 F0 +
    zeta • rhoZetaGroupPolynomial810 A B C0 D0 E0 F0 +
    eta • rhoEtaGroupPolynomial810 A B C0 D0 E0 F0 +
    theta • rhoThetaGroupPolynomial810 A B C0 D0 E0 G0

set_option maxHeartbeats 64000000 in
/-- Primitive at `L = 0` with both `A⁷` faces (`A⁷ B` and `β A⁷`) deleted. -/
def degreeZeroPrimitiveHighA_l0_noA7_Rest810
    (beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  rhoBaseGroupHighA_noA7B_Rest810 0 A B C0 D0 E0 F0 G0 +
    beta • rhoBetaGroupNoA7Polynomial810 A B C0 D0 E0 F0 +
    gamma • rhoGammaGroupPolynomial810 A B C0 D0 E0 F0 +
    delta • rhoDeltaGroupPolynomial810 A B C0 D0 E0 F0 +
    epsilon • rhoEpsilonGroupPolynomial810 A B C0 D0 E0 F0 +
    zeta • rhoZetaGroupPolynomial810 A B C0 D0 E0 F0 +
    eta • rhoEtaGroupPolynomial810 A B C0 D0 E0 F0 +
    theta • rhoThetaGroupPolynomial810 A B C0 D0 E0 G0

set_option maxHeartbeats 64000000 in
/-- Primitive with the unique-`C₀` face `C₀⁴ L` deleted. -/
def degreeZeroPrimitiveHighC0Rest810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  rhoBaseGroupHighC0Rest810 l A B C0 D0 E0 F0 G0 +
    beta • rhoBetaGroupPolynomial810 A B C0 D0 E0 F0 +
    gamma • rhoGammaGroupPolynomial810 A B C0 D0 E0 F0 +
    delta • rhoDeltaGroupPolynomial810 A B C0 D0 E0 F0 +
    epsilon • rhoEpsilonGroupPolynomial810 A B C0 D0 E0 F0 +
    zeta • rhoZetaGroupPolynomial810 A B C0 D0 E0 F0 +
    eta • rhoEtaGroupPolynomial810 A B C0 D0 E0 F0 +
    theta • rhoThetaGroupPolynomial810 A B C0 D0 E0 G0

set_option maxHeartbeats 64000000 in
/-- Primitive with the unique-`G₀` face `G₀² L` deleted. -/
def degreeZeroPrimitiveHighG0Rest810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  rhoBaseGroupHighG0Rest810 l A B C0 D0 E0 F0 G0 +
    beta • rhoBetaGroupPolynomial810 A B C0 D0 E0 F0 +
    gamma • rhoGammaGroupPolynomial810 A B C0 D0 E0 F0 +
    delta • rhoDeltaGroupPolynomial810 A B C0 D0 E0 F0 +
    epsilon • rhoEpsilonGroupPolynomial810 A B C0 D0 E0 F0 +
    zeta • rhoZetaGroupPolynomial810 A B C0 D0 E0 F0 +
    eta • rhoEtaGroupPolynomial810 A B C0 D0 E0 F0 +
    theta • rhoThetaGroupPolynomial810 A B C0 D0 E0 G0

set_option maxHeartbeats 64000000 in
theorem rhoBaseGroupPolynomial810_eq_A8_add_rest
    (l : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    rhoBaseGroupPolynomial810 l A B C0 D0 E0 F0 G0 =
      (369495 / 268435456 * l : k) • A ^ 8 +
        rhoBaseGroupHighARest810 l A B C0 D0 E0 F0 G0 := by
  simp only [rhoBaseGroupPolynomial810, rhoBaseGroupHighARest810]
  abel

set_option maxHeartbeats 64000000 in
theorem degreeZeroPrimitivePolynomial810_eq_A8_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroPrimitivePolynomial810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0 =
      (369495 / 268435456 * l : k) • A ^ 8 +
        degreeZeroPrimitiveHighARest810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0 := by
  simp only [degreeZeroPrimitivePolynomial810,
    degreeZeroPrimitiveHighARest810,
    rhoBaseGroupPolynomial810_eq_A8_add_rest]
  abel

set_option maxHeartbeats 64000000 in
theorem rhoBaseGroupPolynomial810_eq_A7B_add_rest
    (A B C0 D0 E0 F0 G0 : k[X]) :
    rhoBaseGroupPolynomial810 0 A B C0 D0 E0 F0 G0 =
      (19635 / 1048576 : k) • (A ^ 7 * B) +
        rhoBaseGroupHighA_noA7B_Rest810 0 A B C0 D0 E0 F0 G0 := by
  simp only [rhoBaseGroupPolynomial810, rhoBaseGroupHighA_noA7B_Rest810,
    zero_mul, mul_zero, zero_smul, smul_zero]
  simp only [neg_smul]
  abel

set_option maxHeartbeats 64000000 in
theorem degreeZeroPrimitivePolynomial810_eq_A7B_add_rest
    (beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroPrimitivePolynomial810 0 beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0 =
      (19635 / 1048576 : k) • (A ^ 7 * B) +
        degreeZeroPrimitiveHighA_noA7B_Rest810 0 beta gamma delta epsilon
          zeta eta theta A B C0 D0 E0 F0 G0 := by
  simp only [degreeZeroPrimitivePolynomial810,
    degreeZeroPrimitiveHighA_noA7B_Rest810,
    rhoBaseGroupPolynomial810_eq_A7B_add_rest]
  abel
set_option maxHeartbeats 64000000 in

theorem highA_l0_A7_combined_eq (beta : k) (A B : k[X]) :
    (19635 / 1048576 : k) • (A ^ 7 * B) +
        (2601 / 1048576 * beta : k) • A ^ 7 =
      A ^ 7 * highA_l0_A7Coefficient810 beta B := by
  simp only [highA_l0_A7Coefficient810, smul_eq_C_mul]
  ring

set_option maxHeartbeats 64000000 in
theorem rhoBetaGroupPolynomial810_eq_A7_add_rest
    (A B C0 D0 E0 F0 : k[X]) :
    rhoBetaGroupPolynomial810 A B C0 D0 E0 F0 =
      (2601 / 1048576 : k) • A ^ 7 +
        rhoBetaGroupNoA7Polynomial810 A B C0 D0 E0 F0 := by
  simp only [rhoBetaGroupPolynomial810, rhoBetaGroupNoA7Polynomial810]
  simp only [neg_smul]
  abel

set_option maxHeartbeats 64000000 in
theorem degreeZeroPrimitivePolynomial810_eq_A7_combined_add_rest
    (beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroPrimitivePolynomial810 0 beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0 =
      (19635 / 1048576 : k) • (A ^ 7 * B) +
        (2601 / 1048576 * beta : k) • A ^ 7 +
          degreeZeroPrimitiveHighA_l0_noA7_Rest810 beta gamma delta epsilon
            zeta eta theta A B C0 D0 E0 F0 G0 := by
  simp only [degreeZeroPrimitivePolynomial810,
    degreeZeroPrimitiveHighA_l0_noA7_Rest810,
    rhoBaseGroupPolynomial810_eq_A7B_add_rest,
    rhoBetaGroupPolynomial810_eq_A7_add_rest, smul_add]
  module

set_option maxHeartbeats 64000000 in
theorem rhoBaseGroupPolynomial810_eq_C04_add_rest
    (l : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    rhoBaseGroupPolynomial810 l A B C0 D0 E0 F0 G0 =
      (63 / 4096 * l : k) • C0 ^ 4 +
        rhoBaseGroupHighC0Rest810 l A B C0 D0 E0 F0 G0 := by
  simp only [rhoBaseGroupPolynomial810, rhoBaseGroupHighC0Rest810]
  abel

set_option maxHeartbeats 64000000 in
theorem degreeZeroPrimitivePolynomial810_eq_C04_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroPrimitivePolynomial810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0 =
      (63 / 4096 * l : k) • C0 ^ 4 +
        degreeZeroPrimitiveHighC0Rest810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0 := by
  simp only [degreeZeroPrimitivePolynomial810,
    degreeZeroPrimitiveHighC0Rest810,
    rhoBaseGroupPolynomial810_eq_C04_add_rest]
  abel

set_option maxHeartbeats 64000000 in
theorem rhoBaseGroupPolynomial810_eq_G02_add_rest
    (l : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    rhoBaseGroupPolynomial810 l A B C0 D0 E0 F0 G0 =
      (9 / 16 * l : k) • G0 ^ 2 +
        rhoBaseGroupHighG0Rest810 l A B C0 D0 E0 F0 G0 := by
  simp only [rhoBaseGroupPolynomial810, rhoBaseGroupHighG0Rest810]
  abel

set_option maxHeartbeats 64000000 in
theorem degreeZeroPrimitivePolynomial810_eq_G02_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroPrimitivePolynomial810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0 =
      (9 / 16 * l : k) • G0 ^ 2 +
        degreeZeroPrimitiveHighG0Rest810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0 := by
  simp only [degreeZeroPrimitivePolynomial810,
    degreeZeroPrimitiveHighG0Rest810,
    rhoBaseGroupPolynomial810_eq_G02_add_rest]
  abel

end PrimitivePolynomial810


#print axioms UniqueHighACone810.eq_1
#print axioms highA_l0_A7Coefficient810.eq_1
#print axioms rhoBetaGroupPolynomial810.eq_1
#print axioms rhoGammaGroupPolynomial810.eq_1
#print axioms rhoDeltaGroupPolynomial810.eq_1
#print axioms rhoEpsilonGroupPolynomial810.eq_1
#print axioms rhoZetaGroupPolynomial810.eq_1
#print axioms rhoEtaGroupPolynomial810.eq_1
#print axioms rhoThetaGroupPolynomial810.eq_1
#print axioms rhoBaseGroupPolynomial810.eq_1
#print axioms rhoBaseGroupHighARest810.eq_1
#print axioms rhoBaseGroupHighA_noA7B_Rest810.eq_1
#print axioms rhoBetaGroupNoA7Polynomial810.eq_1
#print axioms rhoBaseGroupHighC0Rest810.eq_1
#print axioms rhoBaseGroupHighG0Rest810.eq_1
#print axioms degreeZeroIntegratedPrimitive810.eq_1
#print axioms degreeZeroPrimitivePolynomial810.eq_1
#print axioms degreeZeroPrimitiveHighARest810.eq_1
#print axioms degreeZeroPrimitiveHighA_noA7B_Rest810.eq_1
#print axioms degreeZeroPrimitiveHighA_l0_noA7_Rest810.eq_1
#print axioms degreeZeroPrimitiveHighC0Rest810.eq_1
#print axioms degreeZeroPrimitiveHighG0Rest810.eq_1

end Max11DegreeRoutes
