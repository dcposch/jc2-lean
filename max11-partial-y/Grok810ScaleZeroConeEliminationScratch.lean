import Grok810ScaleZeroFinalRowScratch
import Grok810RouteAdapterScratch

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

theorem natDegree_add_lt810 {p q : k[X]} {d : ℕ}
    (hp : p.natDegree < d) (hq : q.natDegree < d) :
    (p + q).natDegree < d :=
  (natDegree_add_le p q).trans_lt (max_lt hp hq)

theorem natDegree_add_le810 {p q : k[X]} {d : ℕ}
    (hp : p.natDegree ≤ d) (hq : q.natDegree ≤ d) :
    (p + q).natDegree ≤ d :=
  (natDegree_add_le p q).trans (max_le hp hq)

theorem natDegree_smul_le810 (c : k) (p : k[X]) :
    (c • p).natDegree ≤ p.natDegree := by
  by_cases hc : c = 0
  · rw [hc, zero_smul, natDegree_zero]
    exact Nat.zero_le _
  · rw [natDegree_smul _ hc]

theorem natDegree_smul_lt810 (c : k) {p : k[X]} {d : ℕ}
    (hp : p.natDegree < d) : (c • p).natDegree < d :=
  (natDegree_smul_le810 c p).trans_lt hp

theorem natDegree_smul_le_of_le810 (c : k) {p : k[X]} {d : ℕ}
    (hp : p.natDegree ≤ d) : (c • p).natDegree ≤ d :=
  (natDegree_smul_le810 c p).trans hp

theorem natDegree_eq_zero_of_le_zero {p : k[X]} (h : p.natDegree ≤ 0) :
    p.natDegree = 0 :=
  Nat.eq_zero_of_le_zero h

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

/-- Unique-max `A` cone: `A` strictly outranks the other six free letters. -/
def UniqueHighACone810 (A B C0 D0 E0 F0 G0 : k[X]) : Prop :=
  0 < A.natDegree ∧
    B.natDegree < A.natDegree ∧
    C0.natDegree < A.natDegree ∧
    D0.natDegree < A.natDegree ∧
    E0.natDegree < A.natDegree ∧
    F0.natDegree < A.natDegree ∧
    G0.natDegree < A.natDegree

/-- Combined `A⁷` coefficient on the unique-`A` chamber `L = 0`,
`deg B = 0`.  CAS: `51 (385 B + 51 β) / 1048576`. -/
def highA_l0_A7Coefficient810 (beta : k) (B : k[X]) : k[X] :=
  (19635 / 1048576 : k) • B + C (2601 / 1048576 * beta : k)

end DegreeLemmas810

/-! ## Polynomial pullback of the grouped primitive -/

section PrimitivePolynomial810

variable {k : Type*} [Field k] [CharZero k]

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

def rhoEtaGroupPolynomial810 (A B C0 D0 E0 F0 : k[X]) : k[X] :=
  -(51 / 512 : k) • (A ^ 3 * B)
    + (3 / 64 : k) • B ^ 3
    + (9 / 32 : k) • (A * B * C0)
    + (9 / 64 : k) • (A ^ 2 * D0)
    - (1 / 4 : k) • (C0 * D0)
    - (1 / 4 : k) • (B * E0)
    - (1 / 4 : k) • (A * F0)

def rhoThetaGroupPolynomial810 (A B C0 D0 E0 G0 : k[X]) : k[X] :=
  -(51 / 4096 : k) • A ^ 4
    + (9 / 128 : k) • (A * B ^ 2)
    + (9 / 128 : k) • (A ^ 2 * C0)
    - (1 / 16 : k) • C0 ^ 2
    - (1 / 8 : k) • (B * D0)
    - (1 / 8 : k) • (A * E0)
    + (1 / 1 : k) • G0

set_option maxHeartbeats 8000000 in
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

set_option maxHeartbeats 8000000 in
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

set_option maxHeartbeats 8000000 in
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


set_option maxHeartbeats 8000000 in
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

set_option maxHeartbeats 8000000 in
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

set_option maxHeartbeats 16000000 in
theorem rhoBaseGroupPolynomial810_eq_A8_add_rest
    (l : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    rhoBaseGroupPolynomial810 l A B C0 D0 E0 F0 G0 =
      (369495 / 268435456 * l : k) • A ^ 8 +
        rhoBaseGroupHighARest810 l A B C0 D0 E0 F0 G0 := by
  simp only [rhoBaseGroupPolynomial810, rhoBaseGroupHighARest810]
  module

set_option maxHeartbeats 16000000 in
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
  module

set_option maxHeartbeats 16000000 in
theorem rhoBaseGroupPolynomial810_eq_A7B_add_rest
    (A B C0 D0 E0 F0 G0 : k[X]) :
    rhoBaseGroupPolynomial810 0 A B C0 D0 E0 F0 G0 =
      (19635 / 1048576 : k) • (A ^ 7 * B) +
        rhoBaseGroupHighA_noA7B_Rest810 0 A B C0 D0 E0 F0 G0 := by
  simp only [rhoBaseGroupPolynomial810, rhoBaseGroupHighA_noA7B_Rest810,
    zero_mul, mul_zero, zero_smul, smul_zero]
  module

set_option maxHeartbeats 16000000 in
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
  module

theorem highA_l0_A7_combined_eq (beta : k) (A B : k[X]) :
    (19635 / 1048576 : k) • (A ^ 7 * B) +
        (2601 / 1048576 * beta : k) • A ^ 7 =
      A ^ 7 * highA_l0_A7Coefficient810 beta B := by
  simp only [highA_l0_A7Coefficient810, smul_eq_C_mul]
  ring

set_option maxHeartbeats 16000000 in
theorem rhoBetaGroupPolynomial810_eq_A7_add_rest
    (A B C0 D0 E0 F0 : k[X]) :
    rhoBetaGroupPolynomial810 A B C0 D0 E0 F0 =
      (2601 / 1048576 : k) • A ^ 7 +
        rhoBetaGroupNoA7Polynomial810 A B C0 D0 E0 F0 := by
  simp only [rhoBetaGroupPolynomial810, rhoBetaGroupNoA7Polynomial810]
  module

set_option maxHeartbeats 16000000 in
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

set_option maxHeartbeats 16000000 in
theorem rhoBaseGroupPolynomial810_eq_C04_add_rest
    (l : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    rhoBaseGroupPolynomial810 l A B C0 D0 E0 F0 G0 =
      (63 / 4096 * l : k) • C0 ^ 4 +
        rhoBaseGroupHighC0Rest810 l A B C0 D0 E0 F0 G0 := by
  simp only [rhoBaseGroupPolynomial810, rhoBaseGroupHighC0Rest810]
  module

set_option maxHeartbeats 16000000 in
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
  module

set_option maxHeartbeats 16000000 in
theorem rhoBaseGroupPolynomial810_eq_G02_add_rest
    (l : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    rhoBaseGroupPolynomial810 l A B C0 D0 E0 F0 G0 =
      (9 / 16 * l : k) • G0 ^ 2 +
        rhoBaseGroupHighG0Rest810 l A B C0 D0 E0 F0 G0 := by
  simp only [rhoBaseGroupPolynomial810, rhoBaseGroupHighG0Rest810]
  module

set_option maxHeartbeats 16000000 in
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
  module

end PrimitivePolynomial810

/-! ## Algebra map of the polynomial groups -/

section AlgebraMap810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000 in
theorem algebraMap_rhoBetaGroupPolynomial810
    (A B C0 D0 E0 F0 : k[X]) :
    algebraMap k[X] (RatFunc k)
        (rhoBetaGroupPolynomial810 A B C0 D0 E0 F0) =
      rhoBetaGroup810
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0)
        (algebraMap k[X] (RatFunc k) E0)
        (algebraMap k[X] (RatFunc k) F0) := by
  simp only [rhoBetaGroupPolynomial810, rhoBetaGroup810, map_add, map_sub,
    map_neg, map_mul, map_pow, Polynomial.smul_eq_C_mul,
    RatFunc.algebraMap_C, map_div₀, map_ofNat, map_one]
  ring

set_option maxHeartbeats 16000000 in
theorem algebraMap_rhoGammaGroupPolynomial810
    (A B C0 D0 E0 F0 : k[X]) :
    algebraMap k[X] (RatFunc k)
        (rhoGammaGroupPolynomial810 A B C0 D0 E0 F0) =
      rhoGammaGroup810
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0)
        (algebraMap k[X] (RatFunc k) E0)
        (algebraMap k[X] (RatFunc k) F0) := by
  simp only [rhoGammaGroupPolynomial810, rhoGammaGroup810, map_add, map_sub,
    map_neg, map_mul, map_pow, Polynomial.smul_eq_C_mul,
    RatFunc.algebraMap_C, map_div₀, map_ofNat, map_one]
  ring

set_option maxHeartbeats 16000000 in
theorem algebraMap_rhoDeltaGroupPolynomial810
    (A B C0 D0 E0 F0 : k[X]) :
    algebraMap k[X] (RatFunc k)
        (rhoDeltaGroupPolynomial810 A B C0 D0 E0 F0) =
      rhoDeltaGroup810
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0)
        (algebraMap k[X] (RatFunc k) E0)
        (algebraMap k[X] (RatFunc k) F0) := by
  simp only [rhoDeltaGroupPolynomial810, rhoDeltaGroup810, map_add, map_sub,
    map_neg, map_mul, map_pow, Polynomial.smul_eq_C_mul,
    RatFunc.algebraMap_C, map_div₀, map_ofNat, map_one]
  ring

set_option maxHeartbeats 8000000 in
theorem algebraMap_rhoEpsilonGroupPolynomial810
    (A B C0 D0 E0 F0 : k[X]) :
    algebraMap k[X] (RatFunc k)
        (rhoEpsilonGroupPolynomial810 A B C0 D0 E0 F0) =
      rhoEpsilonGroup810
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0)
        (algebraMap k[X] (RatFunc k) E0)
        (algebraMap k[X] (RatFunc k) F0) := by
  simp only [rhoEpsilonGroupPolynomial810, rhoEpsilonGroup810, map_add,
    map_sub, map_neg, map_mul, map_pow, Polynomial.smul_eq_C_mul,
    RatFunc.algebraMap_C, map_div₀, map_ofNat, map_one]
  ring

set_option maxHeartbeats 8000000 in
theorem algebraMap_rhoZetaGroupPolynomial810
    (A B C0 D0 E0 F0 : k[X]) :
    algebraMap k[X] (RatFunc k)
        (rhoZetaGroupPolynomial810 A B C0 D0 E0 F0) =
      rhoZetaGroup810
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0)
        (algebraMap k[X] (RatFunc k) E0)
        (algebraMap k[X] (RatFunc k) F0) := by
  simp only [rhoZetaGroupPolynomial810, rhoZetaGroup810, map_add, map_sub,
    map_neg, map_mul, map_pow, Polynomial.smul_eq_C_mul,
    RatFunc.algebraMap_C, map_div₀, map_ofNat, map_one]
  ring

set_option maxHeartbeats 8000000 in
theorem algebraMap_rhoEtaGroupPolynomial810
    (A B C0 D0 E0 F0 : k[X]) :
    algebraMap k[X] (RatFunc k)
        (rhoEtaGroupPolynomial810 A B C0 D0 E0 F0) =
      rhoEtaGroup810
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0)
        (algebraMap k[X] (RatFunc k) E0)
        (algebraMap k[X] (RatFunc k) F0) := by
  simp only [rhoEtaGroupPolynomial810, rhoEtaGroup810, map_add, map_sub,
    map_neg, map_mul, map_pow, Polynomial.smul_eq_C_mul,
    RatFunc.algebraMap_C, map_div₀, map_ofNat, map_one]
  ring

set_option maxHeartbeats 8000000 in
theorem algebraMap_rhoThetaGroupPolynomial810
    (A B C0 D0 E0 G0 : k[X]) :
    algebraMap k[X] (RatFunc k)
        (rhoThetaGroupPolynomial810 A B C0 D0 E0 G0) =
      rhoThetaGroup810
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0)
        (algebraMap k[X] (RatFunc k) E0)
        (algebraMap k[X] (RatFunc k) G0) := by
  simp only [rhoThetaGroupPolynomial810, rhoThetaGroup810, map_add, map_sub,
    map_neg, map_mul, map_pow, Polynomial.smul_eq_C_mul,
    RatFunc.algebraMap_C, map_div₀, map_ofNat, map_one]
  ring

set_option maxHeartbeats 64000000 in
theorem algebraMap_rhoBaseGroupPolynomial810
    (l : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    algebraMap k[X] (RatFunc k)
        (rhoBaseGroupPolynomial810 l A B C0 D0 E0 F0 G0) =
      rhoBaseGroup810 (RatFunc.C l)
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0)
        (algebraMap k[X] (RatFunc k) E0)
        (algebraMap k[X] (RatFunc k) F0)
        (algebraMap k[X] (RatFunc k) G0) := by
  simp only [rhoBaseGroupPolynomial810, rhoBaseGroup810, map_add, map_sub,
    map_neg, map_mul, map_pow, Polynomial.smul_eq_C_mul,
    RatFunc.algebraMap_C, map_div₀, map_ofNat, map_one]
  ring

set_option maxHeartbeats 16000000 in
theorem algebraMap_degreeZeroPrimitivePolynomial810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    algebraMap k[X] (RatFunc k)
        (degreeZeroPrimitivePolynomial810 l beta gamma delta epsilon zeta
          eta theta A B C0 D0 E0 F0 G0) =
      degreeZeroIntegratedPrimitive810 (RatFunc.C l)
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0)
        (algebraMap k[X] (RatFunc k) E0)
        (algebraMap k[X] (RatFunc k) F0)
        (algebraMap k[X] (RatFunc k) G0)
        (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
        (RatFunc.C epsilon) (RatFunc.C zeta) (RatFunc.C eta)
        (RatFunc.C theta) := by
  simp only [degreeZeroPrimitivePolynomial810,
    degreeZeroIntegratedPrimitive810, map_add, Polynomial.smul_eq_C_mul,
    map_mul, RatFunc.algebraMap_C,
    algebraMap_rhoBaseGroupPolynomial810,
    algebraMap_rhoBetaGroupPolynomial810,
    algebraMap_rhoGammaGroupPolynomial810,
    algebraMap_rhoDeltaGroupPolynomial810,
    algebraMap_rhoEpsilonGroupPolynomial810,
    algebraMap_rhoZetaGroupPolynomial810,
    algebraMap_rhoEtaGroupPolynomial810,
    algebraMap_rhoThetaGroupPolynomial810]

theorem rhoResidual810_eq_integrated
    {F : Type*} [Field F] [CharZero F]
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0
      beta gamma delta epsilon zeta eta theta : F)
    (hbeta : betaResidual810 L A B Q = beta)
    (hgamma : gammaResidual810 L A B C0 P R = gamma)
    (hdelta : deltaResidual810 L A B C0 D0 P Q S0 = delta)
    (hepsilon : epsilonResidual810 L A B C0 D0 E0 P Q R T0 = epsilon)
    (hzeta : zetaResidual810 L A B C0 D0 E0 F0 P Q R S0 U0 = zeta)
    (heta : etaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 V0 = eta)
    (htheta : thetaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 W0 =
      theta) :
    rhoResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 =
      degreeZeroIntegratedPrimitive810 L A B C0 D0 E0 F0 G0 beta gamma
        delta epsilon zeta eta theta := by
  simp only [rhoResidual810, degreeZeroIntegratedPrimitive810, hbeta,
    hgamma, hdelta, hepsilon, hzeta, heta, htheta]

end AlgebraMap810

/-! ## Polynomial core and ground loads -/

section PolynomialCore810

variable {k : Type*} [Field k] [CharZero k]

theorem octicDepressionR810_constantScale_eq_algebraMap
    (p : k[X][X]) (t : k) :
    octicDepressionR810 (RatFunc.C t)
        (algebraMap k[X] (RatFunc k) (p.coeff 7)) =
      algebraMap k[X] (RatFunc k)
        (C ((8 * t ^ 7) ⁻¹) * p.coeff 7) := by
  simp only [octicDepressionR810, map_mul, RatFunc.algebraMap_C,
    div_eq_mul_inv]
  rw [map_inv₀, map_mul, map_ofNat, map_pow]
  ring

theorem constantScale_monicOctic_polynomialCore810
    (p : k[X][X]) (t : k) (ht : t ≠ 0) :
    let r0 : k[X] := C ((8 * t ^ 7)⁻¹) * p.coeff 7
    let p0 : k[X][X] := p.comp ((X - C r0) * C (C t⁻¹))
    let f : (RatFunc k)[X] :=
      affineDepress68 (RatFunc.C t)
        (octicDepressionR810 (RatFunc.C t)
          (algebraMap k[X] (RatFunc k) (p.coeff 7)))
        (sourceToRatFunc68 p)
    algebraMap k[X] (RatFunc k) (p0.coeff 6) = f.coeff 6 ∧
      algebraMap k[X] (RatFunc k) (p0.coeff 5) = f.coeff 5 ∧
      algebraMap k[X] (RatFunc k) (p0.coeff 4) = f.coeff 4 ∧
      algebraMap k[X] (RatFunc k) (p0.coeff 3) = f.coeff 3 ∧
      algebraMap k[X] (RatFunc k) (p0.coeff 2) = f.coeff 2 ∧
      algebraMap k[X] (RatFunc k) (p0.coeff 1) = f.coeff 1 ∧
      algebraMap k[X] (RatFunc k) (p0.coeff 0) = f.coeff 0 := by
  intro r0 p0 f
  have hcenter :
      octicDepressionR810 (RatFunc.C t)
          (algebraMap k[X] (RatFunc k) (p.coeff 7)) =
        algebraMap k[X] (RatFunc k) r0 :=
    octicDepressionR810_constantScale_eq_algebraMap p t
  have hf_eq : f = p0.map (algebraMap k[X] (RatFunc k)) := by
    dsimp only [f, p0]
    rw [hcenter]
    exact affineDepress_source_constantScale_map68 p t r0 ht
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [hf_eq, Polynomial.coeff_map])

theorem ratFuncDerivation68_C (a : k) :
    ratFuncDerivation68 (RatFunc.C a) = 0 := by
  have hp := ratFuncDerivation46_polynomial (C a : k[X])
  simpa [ratFuncDerivation68, RatFunc.algebraMap_C] using hp

theorem ratFuncDerivation68_exists_C {c : RatFunc k}
    (hc : ratFuncDerivation68 c = 0) :
    ∃ a : k, c = RatFunc.C a := by
  apply GCD369RatFuncConstantsOfPolynomialDerivative
    ratFuncDerivation46_polynomial
  simpa [ratFuncDerivation68, ratFuncDerivation46_apply] using hc

set_option maxHeartbeats 64000000 in
theorem monicOcticDecic_rhoLoads_exist_ground810
    (f g : (RatFunc k)[X]) (terminal : k)
    (hf_high : ∀ n, 8 < n → f.coeff n = 0) (hf8 : f.coeff 8 = 1)
    (hf7 : f.coeff 7 = 0)
    (hg_high : ∀ n, 10 < n → g.coeff n = 0) (hg10 : g.coeff 10 = 1)
    (hL : ratFuncDerivation68 (g.coeff 9) = 0)
    (hjac : differentialJacobian ratFuncDerivation68 f g =
      Polynomial.C (RatFunc.C terminal)) :
    ∃ l beta gamma delta epsilon zeta eta theta : k,
      g.coeff 9 = RatFunc.C l ∧
      betaResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5) (g.coeff 7) =
        RatFunc.C beta ∧
      gammaResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5) (f.coeff 4)
          (g.coeff 8) (g.coeff 6) = RatFunc.C gamma ∧
      deltaResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5) (f.coeff 4)
          (f.coeff 3) (g.coeff 8) (g.coeff 7) (g.coeff 5) =
        RatFunc.C delta ∧
      epsilonResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5) (f.coeff 4)
          (f.coeff 3) (f.coeff 2) (g.coeff 8) (g.coeff 7) (g.coeff 6)
          (g.coeff 4) = RatFunc.C epsilon ∧
      zetaResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5) (f.coeff 4)
          (f.coeff 3) (f.coeff 2) (f.coeff 1) (g.coeff 8) (g.coeff 7)
          (g.coeff 6) (g.coeff 5) (g.coeff 3) = RatFunc.C zeta ∧
      etaResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5) (f.coeff 4)
          (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8)
          (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 2) =
        RatFunc.C eta ∧
      thetaResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5) (f.coeff 4)
          (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8)
          (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
          (g.coeff 1) = RatFunc.C theta := by
  let d := ratFuncDerivation68 (k := k)
  have hcoeff (n : ℕ) (hn : n ≠ 0) :
      (differentialJacobian d f g).coeff n = 0 := by
    rw [hjac]
    simp [Polynomial.coeff_C, hn]
  have h15 := (differentialJacobian_coeff_15_monicOcticDecic d f g
    hf_high hf8 hf7 hg_high hg10 hL).symm.trans (hcoeff 15 (by norm_num))
  have h14 := (differentialJacobian_coeff_14_monicOcticDecic d f g
    hf_high hf8 hf7 hg_high hg10 hL).symm.trans (hcoeff 14 (by norm_num))
  have h13 := (differentialJacobian_coeff_13_monicOcticDecic d f g
    hf_high hf8 hf7 hg_high hg10 hL).symm.trans (hcoeff 13 (by norm_num))
  have h12 := (differentialJacobian_coeff_12_monicOcticDecic d f g
    hf_high hf8 hf7 hg_high hg10 hL).symm.trans (hcoeff 12 (by norm_num))
  have h11 := (differentialJacobian_coeff_11_monicOcticDecic d f g
    hf_high hf8 hf7 hg_high hg10 hL).symm.trans (hcoeff 11 (by norm_num))
  have h10 := (differentialJacobian_coeff_10_monicOcticDecic d f g
    hf_high hf8 hf7 hg_high hg10 hL).symm.trans (hcoeff 10 (by norm_num))
  have h9 := (differentialJacobian_coeff_9_monicOcticDecic d f g
    hf_high hf8 hf7 hg_high hg10 hL).symm.trans (hcoeff 9 (by norm_num))
  have h8 := (differentialJacobian_coeff_8_monicOcticDecic d f g
    hf_high hf8 hf7 hg_high hg10 hL).symm.trans (hcoeff 8 (by norm_num))
  have halpha := alphaResidual810_deriv_zero d (f.coeff 6) (g.coeff 8)
    (by linear_combination h15)
  have hbeta := betaResidual810_deriv_zero d (g.coeff 9) (f.coeff 6)
    (f.coeff 5) (g.coeff 7) hL (by linear_combination h14)
  have hgamma := gammaResidual810_deriv_zero d (g.coeff 9) (f.coeff 6)
    (f.coeff 5) (f.coeff 4) (g.coeff 8) (g.coeff 6) hL halpha
    (by linear_combination h13)
  have hdelta := deltaResidual810_deriv_zero d (g.coeff 9) (f.coeff 6)
    (f.coeff 5) (f.coeff 4) (f.coeff 3) (g.coeff 8) (g.coeff 7)
    (g.coeff 5) hL halpha hbeta (by linear_combination h12)
  have hepsilon := epsilonResidual810_deriv_zero d (g.coeff 9)
    (f.coeff 6) (f.coeff 5) (f.coeff 4) (f.coeff 3) (f.coeff 2)
    (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 4) hL halpha hbeta
    hgamma (by linear_combination h11)
  have hzeta := zetaResidual810_deriv_zero d (g.coeff 9) (f.coeff 6)
    (f.coeff 5) (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1)
    (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 3) hL
    halpha hbeta hgamma hdelta (by linear_combination h10)
  have heta := etaResidual810_deriv_zero d (g.coeff 9) (f.coeff 6)
    (f.coeff 5) (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1)
    (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5)
    (g.coeff 4) (g.coeff 2) hL halpha hbeta hgamma hdelta hepsilon
    (by linear_combination h9)
  have htheta := thetaResidual810_deriv_zero d (g.coeff 9) (f.coeff 6)
    (f.coeff 5) (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1)
    (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5)
    (g.coeff 4) (g.coeff 3) (g.coeff 1) hL halpha hbeta hgamma hdelta
    hepsilon hzeta (by linear_combination h8)
  obtain ⟨l, hl⟩ := ratFuncDerivation68_exists_C hL
  obtain ⟨beta, hbetaC⟩ := ratFuncDerivation68_exists_C hbeta
  obtain ⟨gamma, hgammaC⟩ := ratFuncDerivation68_exists_C hgamma
  obtain ⟨delta, hdeltaC⟩ := ratFuncDerivation68_exists_C hdelta
  obtain ⟨epsilon, hepsilonC⟩ := ratFuncDerivation68_exists_C hepsilon
  obtain ⟨zeta, hzetaC⟩ := ratFuncDerivation68_exists_C hzeta
  obtain ⟨eta, hetaC⟩ := ratFuncDerivation68_exists_C heta
  obtain ⟨theta, hthetaC⟩ := ratFuncDerivation68_exists_C htheta
  exact ⟨l, beta, gamma, delta, epsilon, zeta, eta, theta, hl, hbetaC,
    hgammaC, hdeltaC, hepsilonC, hzetaC, hetaC, hthetaC⟩

end PolynomialCore810

/-! ## Source-facing polynomial trajectory -/

section SourcePrimitive810

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 64000000 in
/-- The monic constant-scale depression of a normalized scale-zero
`(8,10)` source has polynomial free-core letters, ground residual loads,
and grouped primitive of Newton degree one. -/
theorem normalized810ScaleZero_exists_primitivePolynomial
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    ∃ (t j lambda cleared l beta gamma delta epsilon zeta eta theta : k)
      (A B C0 D0 E0 F0 G0 : k[X]),
      t ≠ 0 ∧
      j ≠ 0 ∧
      j / t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      (p.coeff 0).derivative * q.coeff 1 -
        p.coeff 1 * (q.coeff 0).derivative = Polynomial.C j ∧
      localClearedFifteenthDefect810 (Polynomial.C t)
          (p.coeff 7) (p.coeff 6) (p.coeff 5) (p.coeff 4) (p.coeff 3)
          (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
          (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
          (q.coeff 1) lambda =
        Polynomial.C cleared ∧
      let hRF : RatFunc k := RatFunc.C t
      let a7 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 7)
      let f : (RatFunc k)[X] :=
        affineDepress68 hRF (octicDepressionR810 hRF a7)
          (sourceToRatFunc68 p)
      let g : (RatFunc k)[X] :=
        affineDepress68 hRF (octicDepressionR810 hRF a7)
          (sourceToRatFunc68 q)
      algebraMap k[X] (RatFunc k) A = f.coeff 6 ∧
        algebraMap k[X] (RatFunc k) B = f.coeff 5 ∧
        algebraMap k[X] (RatFunc k) C0 = f.coeff 4 ∧
        algebraMap k[X] (RatFunc k) D0 = f.coeff 3 ∧
        algebraMap k[X] (RatFunc k) E0 = f.coeff 2 ∧
        algebraMap k[X] (RatFunc k) F0 = f.coeff 1 ∧
        algebraMap k[X] (RatFunc k) G0 = f.coeff 0 ∧
        g.coeff 9 = RatFunc.C l ∧
        derivative
            (degreeZeroPrimitivePolynomial810 l beta gamma delta epsilon
              zeta eta theta A B C0 D0 E0 F0 G0) =
          C (j / t) ∧
        (degreeZeroPrimitivePolynomial810 l beta gamma delta epsilon zeta
            eta theta A B C0 D0 E0 F0 G0).natDegree =
          1 := by
  dsimp only
  obtain ⟨t, j, lambda, cleared, ht, hj, hHsq, hrow, hX, hN, hprim⟩ :=
    normalized810ScaleZero_exists_degreeZeroPrimitive hsource
  rcases hsource with
    ⟨_hH, _hHdegree, hPdegree, hQdegree, hp8, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
  have hp : p.natDegree = 8 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  have hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j) := by
    obtain ⟨j0, _hj0, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
    have hrow0 :
        (p.coeff 0).derivative * q.coeff 1 -
          p.coeff 1 * (q.coeff 0).derivative = Polynomial.C j0 :=
      degreeZeroCoefficientJacobianRow_810 hp hq hjac
    have hj0 : j0 = j :=
      Polynomial.C_injective (hrow0.symm.trans (by simpa [p, q] using hrow))
    simpa [hj0, bivariateJacobian, xderiv, GCD369SourceXDeriv] using hjac
  let hRF : RatFunc k := RatFunc.C t
  let a7 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 7)
  let f : (RatFunc k)[X] :=
    affineDepress68 hRF (octicDepressionR810 hRF a7)
      (sourceToRatFunc68 p)
  let g : (RatFunc k)[X] :=
    affineDepress68 hRF (octicDepressionR810 hRF a7)
      (sourceToRatFunc68 q)
  obtain ⟨hAmap, hBmap, hCmap, hDmap, hEmap, hFmap, hGmap⟩ :=
    constantScale_monicOctic_polynomialCore810 p t ht
  let r0 : k[X] := C ((8 * t ^ 7)⁻¹) * p.coeff 7
  let p0 : k[X][X] := p.comp ((X - C r0) * C (C t⁻¹))
  let A : k[X] := p0.coeff 6
  let B : k[X] := p0.coeff 5
  let C0p : k[X] := p0.coeff 4
  let D0 : k[X] := p0.coeff 3
  let E0 : k[X] := p0.coeff 2
  let F0 : k[X] := p0.coeff 1
  let G0 : k[X] := p0.coeff 0
  have hA : algebraMap k[X] (RatFunc k) A = f.coeff 6 := by
    simpa [A, p0, r0, f, hRF, a7] using hAmap
  have hB : algebraMap k[X] (RatFunc k) B = f.coeff 5 := by
    simpa [B, p0, r0, f, hRF, a7] using hBmap
  have hC : algebraMap k[X] (RatFunc k) C0p = f.coeff 4 := by
    simpa [C0p, p0, r0, f, hRF, a7] using hCmap
  have hD0 : algebraMap k[X] (RatFunc k) D0 = f.coeff 3 := by
    simpa [D0, p0, r0, f, hRF, a7] using hDmap
  have hE : algebraMap k[X] (RatFunc k) E0 = f.coeff 2 := by
    simpa [E0, p0, r0, f, hRF, a7] using hEmap
  have hF : algebraMap k[X] (RatFunc k) F0 = f.coeff 1 := by
    simpa [F0, p0, r0, f, hRF, a7] using hFmap
  have hG : algebraMap k[X] (RatFunc k) G0 = f.coeff 0 := by
    simpa [G0, p0, r0, f, hRF, a7] using hGmap
  have hh : hRF ≠ 0 := by
    intro hzero
    apply ht
    apply RatFunc.C_injective
    simpa only [hRF, map_zero] using hzero
  have hp8' : p.coeff 8 = H ^ 4 := by simpa [p] using hp8
  have hq10' : q.coeff 10 = H ^ 5 := by simpa [q] using hq10
  have hpTop : algebraMap k[X] (RatFunc k) (p.coeff 8) = hRF ^ 8 := by
    have hpow : (C t ^ 2) ^ 4 = (C t : k[X]) ^ 8 := by
      rw [← pow_mul]
    simp only [hp8', hHsq, hpow, hRF, map_pow, RatFunc.algebraMap_C]
  have hqTop : algebraMap k[X] (RatFunc k) (q.coeff 10) = hRF ^ 10 := by
    have hpow : (C t ^ 2) ^ 5 = (C t : k[X]) ^ 10 := by
      rw [← pow_mul]
    simp only [hq10', hHsq, hpow, hRF, map_pow, RatFunc.algebraMap_C]
  have hpDep := affineDepress_sourceOctic68 p hRF
    (octicDepressionR810 hRF a7) hp hh hpTop
  have hL0 : depressedL68 hRF (octicDepressionR810 hRF a7) a7 = 0 :=
    depressedL68_eq_zero_of_octicCenter hRF a7 hh
  have hf7 : f.coeff 7 = 0 := by
    dsimp only [f]; rw [hpDep, coeff_depressedOctic68_seven, hL0]
  have hf8 : f.coeff 8 = 1 := by
    dsimp only [f]; rw [hpDep, coeff_depressedOctic68_eight]
  have hf_high : ∀ n, 8 < n → f.coeff n = 0 := by
    intro n hn
    dsimp only [f]
    rw [hpDep, coeff_depressedOctic68_of_gt_eight _ _ _ _ _ _ _ _ hn]
  have hg_high_src : ∀ n, 10 < n →
      (sourceToRatFunc68 q).coeff n = 0 := by
    intro n hn
    simp [sourceToRatFunc68, sourceToRatFunc46,
      Polynomial.coeff_eq_zero_of_natDegree_lt
        (by omega : q.natDegree < n)]
  have hgTop : (sourceToRatFunc68 q).coeff 10 = hRF ^ 10 := by
    simpa [sourceToRatFunc68, sourceToRatFunc46] using hqTop
  obtain ⟨hg10, hg9, _hg8, hg_high⟩ :=
    affineDepress_degreeTen_highCoeffs810 (sourceToRatFunc68 q) hRF
      (octicDepressionR810 hRF a7) hh hgTop hg_high_src
  have hbracket := differentialJacobian_affineDepress_sourceToRatFunc68
    p q j hRF (octicDepressionR810 hRF a7) hh hD
  have hdiv : RatFunc.C j / hRF = RatFunc.C (j / t) := by
    simp only [hRF, map_div₀]
  have hjacC : differentialJacobian ratFuncDerivation68 f g =
      Polynomial.C (RatFunc.C (j / t)) := by
    have hbr : differentialJacobian ratFuncDerivation68 f g =
        Polynomial.C (RatFunc.C j / hRF) := by
      simpa only [f, g] using hbracket
    simpa [hdiv] using hbr
  have hNrat :
      (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
        Polynomial.C lambda * (Polynomial.C t) ^ 9 := by
    simpa only [p, q] using hN
  have hLval :
      depressedL810 hRF (octicDepressionR810 hRF a7)
          (algebraMap k[X] (RatFunc k) (q.coeff 9)) =
        RatFunc.C (-lambda / 4) := by
    have hNmapped := congrArg (algebraMap k[X] (RatFunc k)) hNrat
    have hNrf :
        5 * a7 * hRF ^ 2 - 4 * algebraMap k[X] (RatFunc k) (q.coeff 9) =
          RatFunc.C lambda * hRF ^ 9 := by
      simpa only [hHsq, hRF, a7, map_sub, map_mul, map_pow, map_ofNat,
        RatFunc.algebraMap_C] using hNmapped
    have hL := depressedL810_eq_of_ninthPower hRF a7
      (algebraMap k[X] (RatFunc k) (q.coeff 9)) (RatFunc.C lambda) hh
      (by simpa using hNrf)
    simpa [map_neg, map_div₀, map_ofNat] using hL
  have hg9L : g.coeff 9 =
      depressedL810 hRF (octicDepressionR810 hRF a7)
        (algebraMap k[X] (RatFunc k) (q.coeff 9)) := by
    dsimp only [g]
    rw [hg9]
    simp [depressedL810, octicDepressionR810, sourceToRatFunc68,
      sourceToRatFunc46]
  have hg9const : g.coeff 9 = RatFunc.C (-lambda / 4) := by
    rw [hg9L, hLval]
  have hLconst : ratFuncDerivation68 (g.coeff 9) = 0 := by
    rw [hg9const]
    exact ratFuncDerivation68_C (-lambda / 4)
  obtain ⟨l, beta, gamma, delta, epsilon, zeta, eta, theta, hl, hbeta,
      hgamma, hdelta, hepsilon, hzeta, heta, htheta⟩ :=
    monicOcticDecic_rhoLoads_exist_ground810 f g (j / t) hf_high hf8 hf7
      hg_high hg10 hLconst hjacC
  have hrho :
      rhoResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5) (f.coeff 4)
          (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8)
          (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
          (g.coeff 2) (g.coeff 1) =
        degreeZeroIntegratedPrimitive810 (RatFunc.C l)
          (algebraMap k[X] (RatFunc k) A)
          (algebraMap k[X] (RatFunc k) B)
          (algebraMap k[X] (RatFunc k) C0p)
          (algebraMap k[X] (RatFunc k) D0)
          (algebraMap k[X] (RatFunc k) E0)
          (algebraMap k[X] (RatFunc k) F0)
          (algebraMap k[X] (RatFunc k) G0)
          (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
          (RatFunc.C epsilon) (RatFunc.C zeta) (RatFunc.C eta)
          (RatFunc.C theta) := by
    rw [← hA, ← hB, ← hC, ← hD0, ← hE, ← hF, ← hG, hl]
    exact rhoResidual810_eq_integrated (RatFunc.C l)
      (algebraMap k[X] (RatFunc k) A)
      (algebraMap k[X] (RatFunc k) B)
      (algebraMap k[X] (RatFunc k) C0p)
      (algebraMap k[X] (RatFunc k) D0)
      (algebraMap k[X] (RatFunc k) E0)
      (algebraMap k[X] (RatFunc k) F0)
      (algebraMap k[X] (RatFunc k) G0)
      (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
      (g.coeff 3) (g.coeff 2) (g.coeff 1)
      (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
      (RatFunc.C epsilon) (RatFunc.C zeta) (RatFunc.C eta)
      (RatFunc.C theta)
      (by simpa [hA, hB, hl] using hbeta)
      (by simpa [hA, hB, hC, hl] using hgamma)
      (by simpa [hA, hB, hC, hD0, hl] using hdelta)
      (by simpa [hA, hB, hC, hD0, hE, hl] using hepsilon)
      (by simpa [hA, hB, hC, hD0, hE, hF, hl] using hzeta)
      (by simpa [hA, hB, hC, hD0, hE, hF, hG, hl] using heta)
      (by simpa [hA, hB, hC, hD0, hE, hF, hG, hl] using htheta)
  let prim : k[X] :=
    degreeZeroPrimitivePolynomial810 l beta gamma delta epsilon zeta eta
      theta A B C0p D0 E0 F0 G0
  have hmap :
      algebraMap k[X] (RatFunc k) prim =
        rhoResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5) (f.coeff 4)
          (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8)
          (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
          (g.coeff 2) (g.coeff 1) := by
    rw [hrho]
    exact algebraMap_degreeZeroPrimitivePolynomial810 l beta gamma delta
      epsilon zeta eta theta A B C0p D0 E0 F0 G0
  have hder :
      algebraMap k[X] (RatFunc k) (derivative prim) =
        algebraMap k[X] (RatFunc k) (C (j / t)) := by
    rw [← ratFuncDerivation46_polynomial]
    have hderiv :
        ratFuncDerivation68 (algebraMap k[X] (RatFunc k) prim) =
          RatFunc.C (j / t) := by
      rw [hmap]
      dsimp [p, q, f, g, hRF, a7]
      exact hprim
    simpa [ratFuncDerivation68, ratFuncDerivation46_apply,
      RatFunc.algebraMap_C] using hderiv
  have hpolyder : derivative prim = C (j / t) :=
    (RatFunc.algebraMap_injective k) hder
  have hdeg : prim.natDegree = 1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C810 prim (j / t)
      (div_ne_zero hj ht) hpolyder
  refine ⟨t, j, lambda, cleared, l, beta, gamma, delta, epsilon, zeta, eta,
    theta, A, B, C0p, D0, E0, F0, G0, ht, hj, div_ne_zero hj ht, hHsq,
    ?_, ?_, ?_⟩
  · simpa [p, q] using hrow
  · simpa [p, q] using hX
  · exact ⟨hA, hB, hC, hD0, hE, hF, hG, hl, hpolyder, hdeg⟩

end SourcePrimitive810

/-! ## Unique-face elimination -/

section UniqueFaces810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000 in
theorem degreeZeroPrimitivePolynomial810_false_of_constant_core
    (l beta gamma delta epsilon zeta eta theta j : k)
    (A B C0 D0 E0 F0 G0 : k[X]) (hj : j ≠ 0)
    (hA : A.natDegree = 0) (hB : B.natDegree = 0)
    (hC : C0.natDegree = 0) (hD : D0.natDegree = 0)
    (hE : E0.natDegree = 0) (hF : F0.natDegree = 0)
    (hG : G0.natDegree = 0)
    (hder :
      derivative
          (degreeZeroPrimitivePolynomial810 l beta gamma delta epsilon
            zeta eta theta A B C0 D0 E0 F0 G0) =
        C j) :
    False := by
  have hdeg :
      (degreeZeroPrimitivePolynomial810 l beta gamma delta epsilon zeta
          eta theta A B C0 D0 E0 F0 G0).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C810 _ j hj hder
  have hle :
      (degreeZeroPrimitivePolynomial810 l beta gamma delta epsilon zeta
          eta theta A B C0 D0 E0 F0 G0).natDegree ≤
        0 := by
    have hbase :
        (rhoBaseGroupPolynomial810 l A B C0 D0 E0 F0 G0).natDegree ≤ 0 := by
      simp only [rhoBaseGroupPolynomial810]
      compute_degree
      omega
    have hbetaG :
        (rhoBetaGroupPolynomial810 A B C0 D0 E0 F0).natDegree ≤ 0 := by
      simp only [rhoBetaGroupPolynomial810]
      compute_degree
      omega
    have hgammaG :
        (rhoGammaGroupPolynomial810 A B C0 D0 E0 F0).natDegree ≤ 0 := by
      simp only [rhoGammaGroupPolynomial810]
      compute_degree
      omega
    have hdeltaG :
        (rhoDeltaGroupPolynomial810 A B C0 D0 E0 F0).natDegree ≤ 0 := by
      simp only [rhoDeltaGroupPolynomial810]
      compute_degree
      omega
    have hepsilonG :
        (rhoEpsilonGroupPolynomial810 A B C0 D0 E0 F0).natDegree ≤ 0 := by
      simp only [rhoEpsilonGroupPolynomial810]
      compute_degree
      omega
    have hzetaG :
        (rhoZetaGroupPolynomial810 A B C0 D0 E0 F0).natDegree ≤ 0 := by
      simp only [rhoZetaGroupPolynomial810]
      compute_degree
      omega
    have hetaG :
        (rhoEtaGroupPolynomial810 A B C0 D0 E0 F0).natDegree ≤ 0 := by
      simp only [rhoEtaGroupPolynomial810]
      compute_degree
      omega
    have hthetaG :
        (rhoThetaGroupPolynomial810 A B C0 D0 E0 G0).natDegree ≤ 0 := by
      simp only [rhoThetaGroupPolynomial810]
      compute_degree
      omega
    simp only [degreeZeroPrimitivePolynomial810]
    exact natDegree_add8_le810 hbase (natDegree_smul_le_of_le810 beta hbetaG)
      (natDegree_smul_le_of_le810 gamma hgammaG)
      (natDegree_smul_le_of_le810 delta hdeltaG)
      (natDegree_smul_le_of_le810 epsilon hepsilonG)
      (natDegree_smul_le_of_le810 zeta hzetaG)
      (natDegree_smul_le_of_le810 eta hetaG)
      (natDegree_smul_le_of_le810 theta hthetaG)
  omega

set_option maxHeartbeats 32000000 in
theorem degreeZeroPrimitiveHighARest810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : UniqueHighACone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroPrimitiveHighARest810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0).natDegree <
      8 * A.natDegree := by
  rcases hcone with ⟨hApos, hB, hC, hD, hE, hF, hG⟩
  have hbase :
      (rhoBaseGroupHighARest810 l A B C0 D0 E0 F0 G0).natDegree <
        8 * A.natDegree := by
    simp only [rhoBaseGroupHighARest810]
    compute_degree
    omega
  have hbetaG :
      (rhoBetaGroupPolynomial810 A B C0 D0 E0 F0).natDegree <
        8 * A.natDegree := by
    simp only [rhoBetaGroupPolynomial810]
    compute_degree
    omega
  have hgammaG :
      (rhoGammaGroupPolynomial810 A B C0 D0 E0 F0).natDegree <
        8 * A.natDegree := by
    simp only [rhoGammaGroupPolynomial810]
    compute_degree
    omega
  have hdeltaG :
      (rhoDeltaGroupPolynomial810 A B C0 D0 E0 F0).natDegree <
        8 * A.natDegree := by
    simp only [rhoDeltaGroupPolynomial810]
    compute_degree
    omega
  have hepsilonG :
      (rhoEpsilonGroupPolynomial810 A B C0 D0 E0 F0).natDegree <
        8 * A.natDegree := by
    simp only [rhoEpsilonGroupPolynomial810]
    compute_degree
    omega
  have hzetaG :
      (rhoZetaGroupPolynomial810 A B C0 D0 E0 F0).natDegree <
        8 * A.natDegree := by
    simp only [rhoZetaGroupPolynomial810]
    compute_degree
    omega
  have hetaG :
      (rhoEtaGroupPolynomial810 A B C0 D0 E0 F0).natDegree <
        8 * A.natDegree := by
    simp only [rhoEtaGroupPolynomial810]
    compute_degree
    omega
  have hthetaG :
      (rhoThetaGroupPolynomial810 A B C0 D0 E0 G0).natDegree <
        8 * A.natDegree := by
    simp only [rhoThetaGroupPolynomial810]
    compute_degree
    omega
  simp only [degreeZeroPrimitiveHighARest810]
  exact natDegree_add8_lt810 hbase (natDegree_smul_lt810 beta hbetaG)
    (natDegree_smul_lt810 gamma hgammaG) (natDegree_smul_lt810 delta hdeltaG)
    (natDegree_smul_lt810 epsilon hepsilonG) (natDegree_smul_lt810 zeta hzetaG)
    (natDegree_smul_lt810 eta hetaG) (natDegree_smul_lt810 theta hthetaG)

theorem uniqueHighA_impossible_of_l_ne
    (l beta gamma delta epsilon zeta eta theta j : k)
    (A B C0 D0 E0 F0 G0 : k[X]) (hl : l ≠ 0) (hj : j ≠ 0)
    (hcone : UniqueHighACone810 A B C0 D0 E0 F0 G0)
    (hder :
      derivative
          (degreeZeroPrimitivePolynomial810 l beta gamma delta epsilon
            zeta eta theta A B C0 D0 E0 F0 G0) =
        C j) :
    False := by
  have hdeg :
      (degreeZeroPrimitivePolynomial810 l beta gamma delta epsilon zeta
          eta theta A B C0 D0 E0 F0 G0).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C810 _ j hj hder
  have hA : A ≠ 0 := by
    intro hA0
    rcases hcone with ⟨hApos, _⟩
    simp [hA0] at hApos
  have hc : (369495 / 268435456 * l : k) ≠ 0 :=
    mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hl
  have hlead :
      ((369495 / 268435456 * l : k) • A ^ 8).natDegree =
        8 * A.natDegree := by
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :=
    degreeZeroPrimitiveHighARest810_natDegree_lt l beta gamma delta
      epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone
  rw [degreeZeroPrimitivePolynomial810_eq_A8_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead])] at hdeg
  rw [hlead] at hdeg
  rcases hcone with ⟨hApos, _⟩
  omega

set_option maxHeartbeats 32000000 in
theorem uniqueHighA_impossible_of_l_zero_B_pos
    (beta gamma delta epsilon zeta eta theta j : k)
    (A B C0 D0 E0 F0 G0 : k[X]) (hj : j ≠ 0)
    (hcone : UniqueHighACone810 A B C0 D0 E0 F0 G0)
    (hBpos : 0 < B.natDegree)
    (hder :
      derivative
          (degreeZeroPrimitivePolynomial810 0 beta gamma delta epsilon
            zeta eta theta A B C0 D0 E0 F0 G0) =
        C j) :
    False := by
  have hdeg :
      (degreeZeroPrimitivePolynomial810 0 beta gamma delta epsilon zeta
          eta theta A B C0 D0 E0 F0 G0).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C810 _ j hj hder
  have hA : A ≠ 0 := by
    intro hA0
    rcases hcone with ⟨hApos, _⟩
    simp [hA0] at hApos
  have hBne : B ≠ 0 := by
    intro hB0
    simp [hB0] at hBpos
  have hc : (19635 / 1048576 : k) ≠ 0 :=
    div_ne_zero (by norm_num) (by norm_num)
  have hlead :
      ((19635 / 1048576 : k) • (A ^ 7 * B)).natDegree =
        7 * A.natDegree + B.natDegree := by
    rw [natDegree_smul _ hc, natDegree_mul (pow_ne_zero 7 hA) hBne,
      natDegree_pow]
  have hrest :
      (degreeZeroPrimitiveHighA_noA7B_Rest810 0 beta gamma delta epsilon
          zeta eta theta A B C0 D0 E0 F0 G0).natDegree <
        7 * A.natDegree + B.natDegree := by
    rcases hcone with ⟨hApos, hBlt, hC, hD, hE, hF, hG⟩
    have hbase :
        (rhoBaseGroupHighA_noA7B_Rest810 0 A B C0 D0 E0 F0 G0).natDegree <
          7 * A.natDegree + B.natDegree := by
      simp only [rhoBaseGroupHighA_noA7B_Rest810, zero_mul, mul_zero,
        zero_smul, smul_zero]
      compute_degree
      omega
    have hbetaG :
        (rhoBetaGroupPolynomial810 A B C0 D0 E0 F0).natDegree <
          7 * A.natDegree + B.natDegree := by
      simp only [rhoBetaGroupPolynomial810]
      compute_degree
      omega
    have hgammaG :
        (rhoGammaGroupPolynomial810 A B C0 D0 E0 F0).natDegree <
          7 * A.natDegree + B.natDegree := by
      simp only [rhoGammaGroupPolynomial810]
      compute_degree
      omega
    have hdeltaG :
        (rhoDeltaGroupPolynomial810 A B C0 D0 E0 F0).natDegree <
          7 * A.natDegree + B.natDegree := by
      simp only [rhoDeltaGroupPolynomial810]
      compute_degree
      omega
    have hepsilonG :
        (rhoEpsilonGroupPolynomial810 A B C0 D0 E0 F0).natDegree <
          7 * A.natDegree + B.natDegree := by
      simp only [rhoEpsilonGroupPolynomial810]
      compute_degree
      omega
    have hzetaG :
        (rhoZetaGroupPolynomial810 A B C0 D0 E0 F0).natDegree <
          7 * A.natDegree + B.natDegree := by
      simp only [rhoZetaGroupPolynomial810]
      compute_degree
      omega
    have hetaG :
        (rhoEtaGroupPolynomial810 A B C0 D0 E0 F0).natDegree <
          7 * A.natDegree + B.natDegree := by
      simp only [rhoEtaGroupPolynomial810]
      compute_degree
      omega
    have hthetaG :
        (rhoThetaGroupPolynomial810 A B C0 D0 E0 G0).natDegree <
          7 * A.natDegree + B.natDegree := by
      simp only [rhoThetaGroupPolynomial810]
      compute_degree
      omega
    simp only [degreeZeroPrimitiveHighA_noA7B_Rest810]
    exact natDegree_add8_lt810 hbase (natDegree_smul_lt810 beta hbetaG)
      (natDegree_smul_lt810 gamma hgammaG)
      (natDegree_smul_lt810 delta hdeltaG)
      (natDegree_smul_lt810 epsilon hepsilonG)
      (natDegree_smul_lt810 zeta hzetaG) (natDegree_smul_lt810 eta hetaG)
      (natDegree_smul_lt810 theta hthetaG)
  rw [degreeZeroPrimitivePolynomial810_eq_A7B_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, _⟩
  omega

theorem highA_l0_A7Coefficient810_natDegree_eq_zero
    (beta : k) {B : k[X]} (hB : B.natDegree = 0) :
    (highA_l0_A7Coefficient810 beta B).natDegree = 0 := by
  have hsmul : ((19635 / 1048576 : k) • B).natDegree ≤ 0 :=
    (natDegree_smul_le810 _ B).trans hB.le
  have hc : (C (2601 / 1048576 * beta : k) : k[X]).natDegree = 0 :=
    natDegree_C _
  change ((19635 / 1048576 : k) • B +
      C (2601 / 1048576 * beta : k)).natDegree = 0
  exact natDegree_eq_zero_of_le_zero <|
    (natDegree_add_le _ _).trans (max_le hsmul hc.le)

set_option maxHeartbeats 32000000 in
theorem uniqueHighA_impossible_of_l_zero_B_const_A7_ne
    (beta gamma delta epsilon zeta eta theta j : k)
    (A B C0 D0 E0 F0 G0 : k[X]) (hj : j ≠ 0)
    (hcone : UniqueHighACone810 A B C0 D0 E0 F0 G0)
    (hB : B.natDegree = 0)
    (hK : highA_l0_A7Coefficient810 beta B ≠ 0)
    (hder :
      derivative
          (degreeZeroPrimitivePolynomial810 0 beta gamma delta epsilon
            zeta eta theta A B C0 D0 E0 F0 G0) =
        C j) :
    False := by
  have hdeg :
      (degreeZeroPrimitivePolynomial810 0 beta gamma delta epsilon zeta
          eta theta A B C0 D0 E0 F0 G0).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C810 _ j hj hder
  have hA : A ≠ 0 := by
    intro hA0
    rcases hcone with ⟨hApos, _⟩
    simp [hA0] at hApos
  have hKdeg :
      (highA_l0_A7Coefficient810 beta B).natDegree = 0 :=
    highA_l0_A7Coefficient810_natDegree_eq_zero beta hB
  have hlead :
      (A ^ 7 * highA_l0_A7Coefficient810 beta B).natDegree =
        7 * A.natDegree := by
    rw [natDegree_mul (pow_ne_zero 7 hA) hK, natDegree_pow, hKdeg, add_zero]
  have hrest :
      (degreeZeroPrimitiveHighA_l0_noA7_Rest810 beta gamma delta epsilon
          zeta eta theta A B C0 D0 E0 F0 G0).natDegree <
        7 * A.natDegree := by
    rcases hcone with ⟨hApos, hBlt, hC, hD, hE, hF, hG⟩
    have hbase :
        (rhoBaseGroupHighA_noA7B_Rest810 0 A B C0 D0 E0 F0 G0).natDegree <
          7 * A.natDegree := by
      simp only [rhoBaseGroupHighA_noA7B_Rest810, zero_mul, mul_zero,
        zero_smul, smul_zero]
      compute_degree
      omega
    have hbetaG :
        (rhoBetaGroupNoA7Polynomial810 A B C0 D0 E0 F0).natDegree <
          7 * A.natDegree := by
      simp only [rhoBetaGroupNoA7Polynomial810]
      compute_degree
      omega
    have hgammaG :
        (rhoGammaGroupPolynomial810 A B C0 D0 E0 F0).natDegree <
          7 * A.natDegree := by
      simp only [rhoGammaGroupPolynomial810]
      compute_degree
      omega
    have hdeltaG :
        (rhoDeltaGroupPolynomial810 A B C0 D0 E0 F0).natDegree <
          7 * A.natDegree := by
      simp only [rhoDeltaGroupPolynomial810]
      compute_degree
      omega
    have hepsilonG :
        (rhoEpsilonGroupPolynomial810 A B C0 D0 E0 F0).natDegree <
          7 * A.natDegree := by
      simp only [rhoEpsilonGroupPolynomial810]
      compute_degree
      omega
    have hzetaG :
        (rhoZetaGroupPolynomial810 A B C0 D0 E0 F0).natDegree <
          7 * A.natDegree := by
      simp only [rhoZetaGroupPolynomial810]
      compute_degree
      omega
    have hetaG :
        (rhoEtaGroupPolynomial810 A B C0 D0 E0 F0).natDegree <
          7 * A.natDegree := by
      simp only [rhoEtaGroupPolynomial810]
      compute_degree
      omega
    have hthetaG :
        (rhoThetaGroupPolynomial810 A B C0 D0 E0 G0).natDegree <
          7 * A.natDegree := by
      simp only [rhoThetaGroupPolynomial810]
      compute_degree
      omega
    simp only [degreeZeroPrimitiveHighA_l0_noA7_Rest810]
    exact natDegree_add8_lt810 hbase (natDegree_smul_lt810 beta hbetaG)
      (natDegree_smul_lt810 gamma hgammaG)
      (natDegree_smul_lt810 delta hdeltaG)
      (natDegree_smul_lt810 epsilon hepsilonG)
      (natDegree_smul_lt810 zeta hzetaG) (natDegree_smul_lt810 eta hetaG)
      (natDegree_smul_lt810 theta hthetaG)
  rw [degreeZeroPrimitivePolynomial810_eq_A7_combined_add_rest,
    highA_l0_A7_combined_eq,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, _⟩
  omega

set_option maxHeartbeats 32000000 in
theorem uniqueNonconstantC0_impossible_of_l_ne
    (l beta gamma delta epsilon zeta eta theta j : k)
    (A B C0 D0 E0 F0 G0 : k[X]) (hl : l ≠ 0) (hj : j ≠ 0)
    (hA : A.natDegree = 0) (hB : B.natDegree = 0)
    (hCpos : 0 < C0.natDegree) (hD : D0.natDegree = 0)
    (hE : E0.natDegree = 0) (hF : F0.natDegree = 0)
    (hG : G0.natDegree = 0)
    (hder :
      derivative
          (degreeZeroPrimitivePolynomial810 l beta gamma delta epsilon
            zeta eta theta A B C0 D0 E0 F0 G0) =
        C j) :
    False := by
  have hdeg :
      (degreeZeroPrimitivePolynomial810 l beta gamma delta epsilon zeta
          eta theta A B C0 D0 E0 F0 G0).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C810 _ j hj hder
  have hCne : C0 ≠ 0 := by
    intro hC0
    simp [hC0] at hCpos
  have hc : (63 / 4096 * l : k) ≠ 0 :=
    mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hl
  have hlead :
      ((63 / 4096 * l : k) • C0 ^ 4).natDegree =
        4 * C0.natDegree := by
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :
      (degreeZeroPrimitiveHighC0Rest810 l beta gamma delta epsilon zeta
          eta theta A B C0 D0 E0 F0 G0).natDegree <
        4 * C0.natDegree := by
    have hbase :
        (rhoBaseGroupHighC0Rest810 l A B C0 D0 E0 F0 G0).natDegree <
          4 * C0.natDegree := by
      simp only [rhoBaseGroupHighC0Rest810]
      compute_degree
      omega
    have hbetaG :
        (rhoBetaGroupPolynomial810 A B C0 D0 E0 F0).natDegree <
          4 * C0.natDegree := by
      simp only [rhoBetaGroupPolynomial810]
      compute_degree
      omega
    have hgammaG :
        (rhoGammaGroupPolynomial810 A B C0 D0 E0 F0).natDegree <
          4 * C0.natDegree := by
      simp only [rhoGammaGroupPolynomial810]
      compute_degree
      omega
    have hdeltaG :
        (rhoDeltaGroupPolynomial810 A B C0 D0 E0 F0).natDegree <
          4 * C0.natDegree := by
      simp only [rhoDeltaGroupPolynomial810]
      compute_degree
      omega
    have hepsilonG :
        (rhoEpsilonGroupPolynomial810 A B C0 D0 E0 F0).natDegree <
          4 * C0.natDegree := by
      simp only [rhoEpsilonGroupPolynomial810]
      compute_degree
      omega
    have hzetaG :
        (rhoZetaGroupPolynomial810 A B C0 D0 E0 F0).natDegree <
          4 * C0.natDegree := by
      simp only [rhoZetaGroupPolynomial810]
      compute_degree
      omega
    have hetaG :
        (rhoEtaGroupPolynomial810 A B C0 D0 E0 F0).natDegree <
          4 * C0.natDegree := by
      simp only [rhoEtaGroupPolynomial810]
      compute_degree
      omega
    have hthetaG :
        (rhoThetaGroupPolynomial810 A B C0 D0 E0 G0).natDegree <
          4 * C0.natDegree := by
      simp only [rhoThetaGroupPolynomial810]
      compute_degree
      omega
    simp only [degreeZeroPrimitiveHighC0Rest810]
    exact natDegree_add8_lt810 hbase (natDegree_smul_lt810 beta hbetaG)
      (natDegree_smul_lt810 gamma hgammaG)
      (natDegree_smul_lt810 delta hdeltaG)
      (natDegree_smul_lt810 epsilon hepsilonG)
      (natDegree_smul_lt810 zeta hzetaG) (natDegree_smul_lt810 eta hetaG)
      (natDegree_smul_lt810 theta hthetaG)
  rw [degreeZeroPrimitivePolynomial810_eq_C04_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  omega

set_option maxHeartbeats 32000000 in
theorem uniqueNonconstantG0_impossible_of_l_ne
    (l beta gamma delta epsilon zeta eta theta j : k)
    (A B C0 D0 E0 F0 G0 : k[X]) (hl : l ≠ 0) (hj : j ≠ 0)
    (hA : A.natDegree = 0) (hB : B.natDegree = 0)
    (hC : C0.natDegree = 0) (hD : D0.natDegree = 0)
    (hE : E0.natDegree = 0) (hF : F0.natDegree = 0)
    (hGpos : 0 < G0.natDegree)
    (hder :
      derivative
          (degreeZeroPrimitivePolynomial810 l beta gamma delta epsilon
            zeta eta theta A B C0 D0 E0 F0 G0) =
        C j) :
    False := by
  have hdeg :
      (degreeZeroPrimitivePolynomial810 l beta gamma delta epsilon zeta
          eta theta A B C0 D0 E0 F0 G0).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C810 _ j hj hder
  have hGne : G0 ≠ 0 := by
    intro hG0
    simp [hG0] at hGpos
  have hc : (9 / 16 * l : k) ≠ 0 :=
    mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hl
  have hlead :
      ((9 / 16 * l : k) • G0 ^ 2).natDegree =
        2 * G0.natDegree := by
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :
      (degreeZeroPrimitiveHighG0Rest810 l beta gamma delta epsilon zeta
          eta theta A B C0 D0 E0 F0 G0).natDegree <
        2 * G0.natDegree := by
    have hbase :
        (rhoBaseGroupHighG0Rest810 l A B C0 D0 E0 F0 G0).natDegree <
          2 * G0.natDegree := by
      simp only [rhoBaseGroupHighG0Rest810]
      compute_degree
      omega
    have hbetaG :
        (rhoBetaGroupPolynomial810 A B C0 D0 E0 F0).natDegree <
          2 * G0.natDegree := by
      simp only [rhoBetaGroupPolynomial810]
      compute_degree
      omega
    have hgammaG :
        (rhoGammaGroupPolynomial810 A B C0 D0 E0 F0).natDegree <
          2 * G0.natDegree := by
      simp only [rhoGammaGroupPolynomial810]
      compute_degree
      omega
    have hdeltaG :
        (rhoDeltaGroupPolynomial810 A B C0 D0 E0 F0).natDegree <
          2 * G0.natDegree := by
      simp only [rhoDeltaGroupPolynomial810]
      compute_degree
      omega
    have hepsilonG :
        (rhoEpsilonGroupPolynomial810 A B C0 D0 E0 F0).natDegree <
          2 * G0.natDegree := by
      simp only [rhoEpsilonGroupPolynomial810]
      compute_degree
      omega
    have hzetaG :
        (rhoZetaGroupPolynomial810 A B C0 D0 E0 F0).natDegree <
          2 * G0.natDegree := by
      simp only [rhoZetaGroupPolynomial810]
      compute_degree
      omega
    have hetaG :
        (rhoEtaGroupPolynomial810 A B C0 D0 E0 F0).natDegree <
          2 * G0.natDegree := by
      simp only [rhoEtaGroupPolynomial810]
      compute_degree
      omega
    have hthetaG :
        (rhoThetaGroupPolynomial810 A B C0 D0 E0 G0).natDegree <
          2 * G0.natDegree := by
      simp only [rhoThetaGroupPolynomial810]
      compute_degree
      omega
    simp only [degreeZeroPrimitiveHighG0Rest810]
    exact natDegree_add8_lt810 hbase (natDegree_smul_lt810 beta hbetaG)
      (natDegree_smul_lt810 gamma hgammaG)
      (natDegree_smul_lt810 delta hdeltaG)
      (natDegree_smul_lt810 epsilon hepsilonG)
      (natDegree_smul_lt810 zeta hzetaG) (natDegree_smul_lt810 eta hetaG)
      (natDegree_smul_lt810 theta hthetaG)
  rw [degreeZeroPrimitivePolynomial810_eq_G02_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  omega

end UniqueFaces810

/-! ## Honest residual -/

section Residual810

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- Exact residual after the first unique-face layer of the `(8,10)`
scale-zero cone tree.

The free core has polynomial representatives and the grouped primitive
has Newton degree one.  A constant core is empty; the unique-`A` cone is
empty except the leftover chamber `L = 0`, `deg B = 0`, and vanishing
combined `A⁷` coefficient `51 (385 B + 51 β)`; a unique nonconstant
`C₀` with `L ≠ 0` is empty; a unique nonconstant `G₀` with `L ≠ 0` is
empty.

Remaining named cones: unique-`A` after `A⁷` cancellation
(`L = 0`, `deg B = 0`, `385 B + 51 β = 0`), whose next unused datum is
the combined `A⁶` coefficient `15 (-434 D₀ - 187 δ)`; unique-`B` with
`A = 0`; unique-`C₀` with `L = 0` (or with `L ≠ 0` and `A` high enough
that `A⁸ L` competes with `C₀⁴ L`); unique-`D₀` with `A = 0`; unique
`E₀`/`F₀` chambers whose quadratic leading coefficient vanishes;
unique-`G₀` with `L = 0` and `deg G₀ = 1` with nonzero linear
coefficient (Newton degree one, allowed by `d ρ = C (j / t)`); and every
cone in which two or more letters share the maximal degree.  The
weight-`105` defect remains a ground constant and is not consumed. -/
theorem normalized810ScaleZero_coneEliminationResidual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    ∃ (t j lambda cleared l beta gamma delta epsilon zeta eta theta : k)
      (A B C0 D0 E0 F0 G0 : k[X]),
      t ≠ 0 ∧
      j ≠ 0 ∧
      j / t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      derivative
          (degreeZeroPrimitivePolynomial810 l beta gamma delta epsilon
            zeta eta theta A B C0 D0 E0 F0 G0) =
        C (j / t) ∧
      (degreeZeroPrimitivePolynomial810 l beta gamma delta epsilon zeta
          eta theta A B C0 D0 E0 F0 G0).natDegree =
        1 ∧
      ¬ (A.natDegree = 0 ∧ B.natDegree = 0 ∧ C0.natDegree = 0 ∧
          D0.natDegree = 0 ∧ E0.natDegree = 0 ∧ F0.natDegree = 0 ∧
          G0.natDegree = 0) ∧
      (UniqueHighACone810 A B C0 D0 E0 F0 G0 →
        l = 0 ∧ B.natDegree = 0 ∧
          highA_l0_A7Coefficient810 beta B = 0) ∧
      ¬ (A.natDegree = 0 ∧ B.natDegree = 0 ∧ 0 < C0.natDegree ∧
          D0.natDegree = 0 ∧ E0.natDegree = 0 ∧ F0.natDegree = 0 ∧
          G0.natDegree = 0 ∧ l ≠ 0) ∧
      ¬ (A.natDegree = 0 ∧ B.natDegree = 0 ∧ C0.natDegree = 0 ∧
          D0.natDegree = 0 ∧ E0.natDegree = 0 ∧ F0.natDegree = 0 ∧
          0 < G0.natDegree ∧ l ≠ 0) := by
  obtain ⟨t, j, lambda, cleared, l, beta, gamma, delta, epsilon, zeta, eta,
      theta, A, B, C0, D0, E0, F0, G0, ht, hj, hjdiv, hHsq, _hrow, _hX,
      hcore⟩ :=
    normalized810ScaleZero_exists_primitivePolynomial hsource
  obtain ⟨hA, hB, hC, hD, hE, hF, hG, hl, hder, hdeg⟩ := hcore
  refine ⟨t, j, lambda, cleared, l, beta, gamma, delta, epsilon, zeta, eta,
    theta, A, B, C0, D0, E0, F0, G0, ht, hj, hjdiv, hHsq, hder, hdeg, ?_,
    ?_, ?_, ?_⟩
  · intro hconst
    exact degreeZeroPrimitivePolynomial810_false_of_constant_core
      l beta gamma delta epsilon zeta eta theta (j / t) A B C0 D0 E0 F0
      G0 hjdiv hconst.1 hconst.2.1 hconst.2.2.1 hconst.2.2.2.1
      hconst.2.2.2.2.1 hconst.2.2.2.2.2.1 hconst.2.2.2.2.2.2 hder
  · intro hcone
    refine ⟨?_, ?_, ?_⟩
    · by_contra hlne
      exact uniqueHighA_impossible_of_l_ne l beta gamma delta epsilon
        zeta eta theta (j / t) A B C0 D0 E0 F0 G0 hlne hjdiv hcone hder
    · by_contra hBpos
      have hpos : 0 < B.natDegree := Nat.pos_of_ne_zero hBpos
      have hl0 : l = 0 := by
        by_contra hlne
        exact uniqueHighA_impossible_of_l_ne l beta gamma delta epsilon
          zeta eta theta (j / t) A B C0 D0 E0 F0 G0 hlne hjdiv hcone hder
      subst hl0
      exact uniqueHighA_impossible_of_l_zero_B_pos beta gamma delta
        epsilon zeta eta theta (j / t) A B C0 D0 E0 F0 G0 hjdiv hcone
        hpos hder
    · have hl0 : l = 0 := by
        by_contra hlne
        exact uniqueHighA_impossible_of_l_ne l beta gamma delta epsilon
          zeta eta theta (j / t) A B C0 D0 E0 F0 G0 hlne hjdiv hcone hder
      have hB0 : B.natDegree = 0 := by
        by_contra hBpos
        have hpos : 0 < B.natDegree := Nat.pos_of_ne_zero hBpos
        subst hl0
        exact uniqueHighA_impossible_of_l_zero_B_pos beta gamma delta
          epsilon zeta eta theta (j / t) A B C0 D0 E0 F0 G0 hjdiv hcone
          hpos hder
      subst hl0
      by_contra hKne
      exact uniqueHighA_impossible_of_l_zero_B_const_A7_ne beta gamma
        delta epsilon zeta eta theta (j / t) A B C0 D0 E0 F0 G0 hjdiv
        hcone hB0 hKne hder
  · intro hC
    exact uniqueNonconstantC0_impossible_of_l_ne l beta gamma delta
      epsilon zeta eta theta (j / t) A B C0 D0 E0 F0 G0 hC.2.2.2.2.2.2.2
      hjdiv hC.1 hC.2.1 hC.2.2.1 hC.2.2.2.1 hC.2.2.2.2.1 hC.2.2.2.2.2.1
      hC.2.2.2.2.2.2.1 hder
  · intro hG
    exact uniqueNonconstantG0_impossible_of_l_ne l beta gamma delta
      epsilon zeta eta theta (j / t) A B C0 D0 E0 F0 G0 hG.2.2.2.2.2.2.2
      hjdiv hG.1 hG.2.1 hG.2.2.1 hG.2.2.2.1 hG.2.2.2.2.1 hG.2.2.2.2.2.1
      hG.2.2.2.2.2.2.1 hder

/-- Glue of the two constant faces through the cone residual: the
scale-zero source is empty once the named leftover cones are excluded.
Neither leftover cone is claimed empty here. -/
theorem normalized810ScaleZero_impossible_of_coneResidual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0)
    (hres :
      (∃ (t j lambda cleared l beta gamma delta epsilon zeta eta theta : k)
        (A B C0 D0 E0 F0 G0 : k[X]),
        t ≠ 0 ∧ j ≠ 0 ∧ j / t ≠ 0 ∧ H = (Polynomial.C t) ^ 2 ∧
          derivative
              (degreeZeroPrimitivePolynomial810 l beta gamma delta epsilon
                zeta eta theta A B C0 D0 E0 F0 G0) =
            C (j / t) ∧
          (degreeZeroPrimitivePolynomial810 l beta gamma delta epsilon zeta
              eta theta A B C0 D0 E0 F0 G0).natDegree =
            1 ∧
          ¬ (A.natDegree = 0 ∧ B.natDegree = 0 ∧ C0.natDegree = 0 ∧
              D0.natDegree = 0 ∧ E0.natDegree = 0 ∧ F0.natDegree = 0 ∧
              G0.natDegree = 0) ∧
          (UniqueHighACone810 A B C0 D0 E0 F0 G0 →
            l = 0 ∧ B.natDegree = 0 ∧
              highA_l0_A7Coefficient810 beta B = 0) ∧
          ¬ (A.natDegree = 0 ∧ B.natDegree = 0 ∧ 0 < C0.natDegree ∧
              D0.natDegree = 0 ∧ E0.natDegree = 0 ∧ F0.natDegree = 0 ∧
              G0.natDegree = 0 ∧ l ≠ 0) ∧
          ¬ (A.natDegree = 0 ∧ B.natDegree = 0 ∧ C0.natDegree = 0 ∧
              D0.natDegree = 0 ∧ E0.natDegree = 0 ∧ F0.natDegree = 0 ∧
              0 < G0.natDegree ∧ l ≠ 0)) →
        False) :
    False :=
  hres (normalized810ScaleZero_coneEliminationResidual hsource)

/-- Identity glue: a source-facing `False` theorem is exactly the
tracked scale-zero exclusion.  No face is closed here. -/
theorem planeKeller810ScaleZeroExclusion_of_impossible
    {K : Type*} [Field K]
    (himpossible :
      ∀ (P Q : MvPolynomial (Fin 2) K) (H : K[X]),
        Normalized810LeadingCoreSource P Q H 0 → False) :
    PlaneKeller810ScaleZeroExclusion (K := K) :=
  himpossible

end Residual810

#print axioms natDegree_eq_one_of_derivative_eq_nonzero_C810
#print axioms UniqueHighACone810
#print axioms highA_l0_A7Coefficient810
#print axioms degreeZeroPrimitivePolynomial810
#print axioms octicDepressionR810_constantScale_eq_algebraMap
#print axioms constantScale_monicOctic_polynomialCore810
#print axioms monicOcticDecic_rhoLoads_exist_ground810
#print axioms algebraMap_degreeZeroPrimitivePolynomial810
#print axioms normalized810ScaleZero_exists_primitivePolynomial
#print axioms degreeZeroPrimitivePolynomial810_false_of_constant_core
#print axioms uniqueHighA_impossible_of_l_ne
#print axioms uniqueHighA_impossible_of_l_zero_B_pos
#print axioms uniqueHighA_impossible_of_l_zero_B_const_A7_ne
#print axioms uniqueNonconstantC0_impossible_of_l_ne
#print axioms uniqueNonconstantG0_impossible_of_l_ne
#print axioms normalized810ScaleZero_coneEliminationResidual
#print axioms normalized810ScaleZero_impossible_of_coneResidual
#print axioms planeKeller810ScaleZeroExclusion_of_impossible

end Max11DegreeRoutes
