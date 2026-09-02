import Grok810ScaleZeroClosureScratch

/-! # Scale-zero mixed-cone closure for normalized `(8,10)`, `H = 0`

Continuation of `Grok810ScaleZeroClosureScratch` on the constant core
`H = (C t)²`.  That file emptied the unique-`G₀` degree-one chamber with
`l = 0` by the degree-one Jacobian coefficient, reducing
`normalized810ScaleZero_impossible` to
`normalized810ScaleZero_coneClosureResidual`: mixed cones in which at
least one of `A, B, C₀, D₀, E₀, F₀` is nonconstant, after the unique
weighted `ξ`/`μ`/`ο` faces and the `A`-ratio faces.

CAS job `derive_810_scale_zero_mixed_cones.py` (extending
`derive_810_scale_zero_cone_ratio_ties.py`; outer degrees `(8,10)`,
leading `h⁴`, `h⁵`) enumerates mixed families by support and weighted
degree order.  On each cone a constant first integral has a leading
weighted face of positive degree unless the cone is a ratio-tie of its
face monomials.  On a tie, `μ` and `ξ` (or `ο`) have different face
coefficient vectors; a linear combination is a power of a nonzero tied
leading coefficient (Groebner / Euclidean identity, not a finite-root
count).

Named leftover families of the parent:

* unique-high `B` with `deg A > 0` (`BLeadsOmicronCone810` required
  `deg A = 0`): `B⁵` of `ο` if `3 deg A < 2 deg B`, the mixed face
  `A⁶ B` of `ο` if `3 deg A > 2 deg B`, and the ratio-tie
  `3 deg A = 2 deg B`;
* `C₀`–`D₀` and the other non-`A` pair ties: a unique load-free
  monomial of `μ` or `ξ` or `ο`, or a two-integral Groebner power;
* unique-`G₀` with another letter nonconstant: the same unique faces
  (`B⁵`, `C₀³`, `E₀²`, `F₀²`, `A⁷`) still strictly lead.

The unused integrals `κ` and `ν` are spent as companions on the
ratio-ties (their load-free faces have the same Newton weights); the
Lean transcription uses the already pulled-back `ξ`, `μ`, and `ο`.
No total-degree or twice-prime theorem is used.  No `sorry`, no new
axioms, no finite-root shortcut.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false


/-! ## Mixed and ratio-tie cones -/

section MixedCones810

variable {k : Type*} [Field k] [CharZero k]

/-- Unique-high `B` with `A` nonconstant, the other five letters
constant, and `3 deg A < 2 deg B`.  CAS: `B⁵` of `ο` strictly leads. -/
def B5LeadsMixedAPosCone810 (A B C0 D0 E0 F0 G0 : k[X]) : Prop :=
  0 < B.natDegree ∧
    0 < A.natDegree ∧
    3 * A.natDegree < 2 * B.natDegree ∧
    C0.natDegree = 0 ∧
    D0.natDegree = 0 ∧
    E0.natDegree = 0 ∧
    F0.natDegree = 0 ∧
    G0.natDegree = 0

/-- Unique-high `B` with `A` nonconstant, the other five letters
constant, and `3 deg A > 2 deg B`.  CAS: `A⁶ B` of `ο` strictly leads. -/
def A6BLeadsOmicronCone810 (A B C0 D0 E0 F0 G0 : k[X]) : Prop :=
  0 < A.natDegree ∧
    0 < B.natDegree ∧
    A.natDegree < B.natDegree ∧
    2 * B.natDegree < 3 * A.natDegree ∧
    C0.natDegree = 0 ∧
    D0.natDegree = 0 ∧
    E0.natDegree = 0 ∧
    F0.natDegree = 0 ∧
    G0.natDegree = 0

/-- Ratio-tie `3 deg A = 2 deg B` with the other five letters constant.
CAS: the load-free `μ` face is `11 A⁶ - 176 A³ B² + 32 B⁴`; with `ξ`
the Groebner ideal contains `B⁵` and a power of `A`. -/
def AB23RatioTieCone810 (A B C0 D0 E0 F0 G0 : k[X]) : Prop :=
  0 < A.natDegree ∧
    0 < B.natDegree ∧
    3 * A.natDegree = 2 * B.natDegree ∧
    C0.natDegree = 0 ∧
    D0.natDegree = 0 ∧
    E0.natDegree = 0 ∧
    F0.natDegree = 0 ∧
    G0.natDegree = 0

/-- Unique-high `C₀` with `A` nonconstant, `B` and the other four
letters constant, and `2 deg A < deg C₀`.  CAS: `C₀³` of `μ` strictly
leads. -/
def C03LeadsMixedAPosCone810 (A B C0 D0 E0 F0 G0 : k[X]) : Prop :=
  0 < C0.natDegree ∧
    0 < A.natDegree ∧
    B.natDegree = 0 ∧
    2 * A.natDegree < C0.natDegree ∧
    D0.natDegree = 0 ∧
    E0.natDegree = 0 ∧
    F0.natDegree = 0 ∧
    G0.natDegree = 0

/-- Unique-high `C₀` with `A` nonconstant, `2 deg A > deg C₀`, and the
other five letters constant.  CAS: `A⁶` of `μ` strictly leads. -/
def A6LeadsMuMixedC0Cone810 (A B C0 D0 E0 F0 G0 : k[X]) : Prop :=
  0 < A.natDegree ∧
    0 < C0.natDegree ∧
    A.natDegree < C0.natDegree ∧
    C0.natDegree < 2 * A.natDegree ∧
    B.natDegree = 0 ∧
    D0.natDegree = 0 ∧
    E0.natDegree = 0 ∧
    F0.natDegree = 0 ∧
    G0.natDegree = 0

/-- Ratio-tie `deg C₀ = 2 deg A` with the other five letters constant. -/
def AC02RatioTieCone810 (A B C0 D0 E0 F0 G0 : k[X]) : Prop :=
  0 < A.natDegree ∧
    0 < C0.natDegree ∧
    C0.natDegree = 2 * A.natDegree ∧
    B.natDegree = 0 ∧
    D0.natDegree = 0 ∧
    E0.natDegree = 0 ∧
    F0.natDegree = 0 ∧
    G0.natDegree = 0

/-- Unique-high `C₀` with `B` nonconstant, `A` and the other four
letters constant.  CAS: `C₀³` of `μ` strictly leads on `5 deg B < 3 deg C₀`. -/
def C03LeadsMixedBPosCone810 (A B C0 D0 E0 F0 G0 : k[X]) : Prop :=
  0 < C0.natDegree ∧
    0 < B.natDegree ∧
    A.natDegree = 0 ∧
    4 * B.natDegree < 3 * C0.natDegree ∧
    D0.natDegree = 0 ∧
    E0.natDegree = 0 ∧
    F0.natDegree = 0 ∧
    G0.natDegree = 0

/-- Unique-high `D₀` with `A` nonconstant and the other five letters
constant.  Named-weight comparison `7 deg A < 3 deg D₀` is not enough
for the mixed monomial `A⁵ D₀` of `ο` (degree `5 deg A + deg D₀`); the
stricter `5 deg A < 2 deg D₀` makes `D₀³` strictly lead. -/
def D03LeadsMixedAPosCone810 (A B C0 D0 E0 F0 G0 : k[X]) : Prop :=
  0 < D0.natDegree ∧
    0 < A.natDegree ∧
    B.natDegree = 0 ∧
    C0.natDegree = 0 ∧
    7 * A.natDegree < 3 * D0.natDegree ∧
    5 * A.natDegree < 2 * D0.natDegree ∧
    E0.natDegree = 0 ∧
    F0.natDegree = 0 ∧
    G0.natDegree = 0

/-- Unique `E₀²` of `μ` with the other six letters of degree zero except
possibly `G₀` of degree at most `1`.  CAS: `E₀²` still strictly leads
on unique-`G₀` of degree one with nonconstant `E₀`. -/
def E02LeadsMixedCone810 (A B C0 D0 E0 F0 G0 : k[X]) : Prop :=
  0 < E0.natDegree ∧
    A.natDegree = 0 ∧
    B.natDegree = 0 ∧
    C0.natDegree = 0 ∧
    D0.natDegree = 0 ∧
    F0.natDegree = 0 ∧
    G0.natDegree < 2 * E0.natDegree

/-- Unique `F₀²` of `ξ` with the other six letters of degree zero except
possibly `G₀` of degree at most `1`. -/
def F02LeadsMixedCone810 (A B C0 D0 E0 F0 G0 : k[X]) : Prop :=
  0 < F0.natDegree ∧
    A.natDegree = 0 ∧
    B.natDegree = 0 ∧
    C0.natDegree = 0 ∧
    D0.natDegree = 0 ∧
    E0.natDegree = 0 ∧
    G0.natDegree < 2 * F0.natDegree

/-- Ratio-tie `2 deg E₀ = 3 deg A` with the other five letters constant. -/
def AE03RatioTieCone810 (A B C0 D0 E0 F0 G0 : k[X]) : Prop :=
  0 < A.natDegree ∧
    0 < E0.natDegree ∧
    2 * E0.natDegree = 3 * A.natDegree ∧
    B.natDegree = 0 ∧
    C0.natDegree = 0 ∧
    D0.natDegree = 0 ∧
    F0.natDegree = 0 ∧
    G0.natDegree = 0

/-- Ratio-tie `2 deg E₀ = 2 deg B` wait: `deg E₀ = 2 deg B`. -/
def BE02RatioTieCone810 (A B C0 D0 E0 F0 G0 : k[X]) : Prop :=
  0 < B.natDegree ∧
    0 < E0.natDegree ∧
    E0.natDegree = 2 * B.natDegree ∧
    A.natDegree = 0 ∧
    C0.natDegree = 0 ∧
    D0.natDegree = 0 ∧
    F0.natDegree = 0 ∧
    G0.natDegree = 0

/-- Ratio-tie `2 deg E₀ = 3 deg C₀` with the other five letters constant. -/
def C0E0RatioTieCone810 (A B C0 D0 E0 F0 G0 : k[X]) : Prop :=
  0 < C0.natDegree ∧
    0 < E0.natDegree ∧
    2 * E0.natDegree = 3 * C0.natDegree ∧
    A.natDegree = 0 ∧
    B.natDegree = 0 ∧
    D0.natDegree = 0 ∧
    F0.natDegree = 0 ∧
    G0.natDegree = 0

/-- Ratio-tie `2 deg F₀ = 7 deg A` with the other five letters constant. -/
def AF07RatioTieCone810 (A B C0 D0 E0 F0 G0 : k[X]) : Prop :=
  0 < A.natDegree ∧
    0 < F0.natDegree ∧
    2 * F0.natDegree = 7 * A.natDegree ∧
    B.natDegree = 0 ∧
    C0.natDegree = 0 ∧
    D0.natDegree = 0 ∧
    E0.natDegree = 0 ∧
    G0.natDegree = 0

/-- Ratio-tie `3 deg D₀ = 5 deg B` with the other five letters constant. -/
def BD03RatioTieCone810 (A B C0 D0 E0 F0 G0 : k[X]) : Prop :=
  0 < B.natDegree ∧
    0 < D0.natDegree ∧
    3 * D0.natDegree = 5 * B.natDegree ∧
    A.natDegree = 0 ∧
    C0.natDegree = 0 ∧
    E0.natDegree = 0 ∧
    F0.natDegree = 0 ∧
    G0.natDegree = 0

/-- Pair `B`–`C₀` with `5 deg B = 3 deg C₀` and the other five constant. -/
def BC03RatioTieCone810 (A B C0 D0 E0 F0 G0 : k[X]) : Prop :=
  0 < B.natDegree ∧
    0 < C0.natDegree ∧
    5 * B.natDegree = 3 * C0.natDegree ∧
    A.natDegree = 0 ∧
    D0.natDegree = 0 ∧
    E0.natDegree = 0 ∧
    F0.natDegree = 0 ∧
    G0.natDegree = 0

/-- Pair `C₀`–`D₀` with equal unweighted degree, others constant. -/
def C0D0RatioTieCone810 (A B C0 D0 E0 F0 G0 : k[X]) : Prop :=
  0 < C0.natDegree ∧
    D0.natDegree = C0.natDegree ∧
    A.natDegree = 0 ∧
    B.natDegree = 0 ∧
    E0.natDegree = 0 ∧
    F0.natDegree = 0 ∧
    G0.natDegree = 0

/-- Unique-`G₀` of degree one with exactly one other letter nonconstant
of positive degree.  Parent unique-`G₀` required the other six of
degree zero. -/
def UniqueG0WithBCone810 (A B C0 D0 E0 F0 G0 : k[X]) : Prop :=
  G0.natDegree = 1 ∧
    0 < B.natDegree ∧
    A.natDegree = 0 ∧
    C0.natDegree = 0 ∧
    D0.natDegree = 0 ∧
    E0.natDegree = 0 ∧
    F0.natDegree = 0

private theorem zero_pow_two_rt {R : Type*} [Semiring R] : (0 : R) ^ 2 = 0 :=
  zero_pow (by decide : (2 : ℕ) ≠ 0)

private theorem zero_pow_three_rt {R : Type*} [Semiring R] : (0 : R) ^ 3 = 0 :=
  zero_pow (by decide : (3 : ℕ) ≠ 0)

private theorem zero_pow_four_rt {R : Type*} [Semiring R] : (0 : R) ^ 4 = 0 :=
  zero_pow (by decide : (4 : ℕ) ≠ 0)

private theorem zero_pow_five_rt {R : Type*} [Semiring R] : (0 : R) ^ 5 = 0 :=
  zero_pow (by decide : (5 : ℕ) ≠ 0)

private theorem zero_pow_six_rt {R : Type*} [Semiring R] : (0 : R) ^ 6 = 0 :=
  zero_pow (by decide : (6 : ℕ) ≠ 0)

private theorem zero_pow_seven_rt {R : Type*} [Semiring R] : (0 : R) ^ 7 = 0 :=
  zero_pow (by decide : (7 : ℕ) ≠ 0)

end MixedCones810


/-! ## Euclidean identities on tied leading coefficients -/

section MixedTieIdentities810

variable {k : Type*} [Field k] [CharZero k]

/-- On the `A`–`B` weight-tie `3 deg A = 2 deg B`, a linear combination
of the load-free `μ` and `ξ` inner forms is `121 r³ (r³ - 14 s²)`.
Parentheses on `r³ s²` match the `leadingCoeff_mul` expansion. -/
theorem mu_xi_AB23_inner_identity (r s : k) :
    (14 : k) * (11 * r ^ 6 - 176 * (r ^ 3 * s ^ 2) + 32 * s ^ 4) -
        (33 * r ^ 6 - 770 * (r ^ 3 * s ^ 2) + 448 * s ^ 4) =
      121 * r ^ 3 * (r ^ 3 - 14 * s ^ 2) := by
  ring

/-- Substituting the `ξ` companion factor `r³ = 14 s²` into the `μ`
inner form yields `-(276 s⁴)`. -/
theorem mu_AB23_of_xi_companion_factor (s : k) :
    (11 : k) * (14 * s ^ 2) ^ 2 - 176 * ((14 * s ^ 2) * s ^ 2) + 32 * s ^ 4 =
      -(276 * s ^ 4) := by
  ring

/-- If the `μ` inner form vanishes and `r ≠ 0`, the `ξ` inner form
cannot vanish. -/
theorem xi_AB23_inner_ne_of_mu_zero (r s : k)
    (hr : r ≠ 0)
    (hmu : (11 : k) * r ^ 6 - 176 * (r ^ 3 * s ^ 2) + 32 * s ^ 4 = 0) :
    (33 : k) * r ^ 6 - 770 * (r ^ 3 * s ^ 2) + 448 * s ^ 4 ≠ 0 := by
  intro hxi
  have hid := mu_xi_AB23_inner_identity (k := k) r s
  have hcomb : (121 : k) * r ^ 3 * (r ^ 3 - 14 * s ^ 2) = 0 := by
    rw [← hid, hmu, hxi]
    simp
  have h121 : (121 : k) ≠ 0 := by norm_num
  have hr3 : r ^ 3 ≠ 0 := pow_ne_zero 3 hr
  have hfac : r ^ 3 - 14 * s ^ 2 = 0 :=
    (mul_eq_zero.mp hcomb).resolve_left (mul_ne_zero h121 hr3)
  have hr3eq : r ^ 3 = 14 * s ^ 2 := eq_of_sub_eq_zero hfac
  have hpow : r ^ 6 = (r ^ 3) ^ 2 := by ring
  have hmu' :
      (11 : k) * (14 * s ^ 2) ^ 2 - 176 * ((14 * s ^ 2) * s ^ 2) +
          32 * s ^ 4 = 0 := by
    rw [← hr3eq, ← hpow]
    exact hmu
  have h276 : (276 : k) * s ^ 4 = 0 := by
    have h1 := mu_AB23_of_xi_companion_factor (k := k) s
    rw [hmu'] at h1
    exact neg_eq_zero.mp h1.symm
  have h276ne : (276 : k) ≠ 0 := by norm_num
  have hs4 : s ^ 4 = 0 := (mul_eq_zero.mp h276).resolve_left h276ne
  have hs : s = 0 :=
    (pow_eq_zero_iff (by decide : (4 : ℕ) ≠ 0)).mp hs4
  have hr0 : r ^ 3 = 0 := by simp [hr3eq, hs]
  exact hr3 hr0

end MixedTieIdentities810


/-! ## Combined faces -/

section MixedCombinedFaces810

variable {k : Type*} [Field k] [CharZero k]

/-- Load-free `μ` face on the `A`–`B` tie `3 deg A = 2 deg B`. -/
def muAB23Combined810 (A B : k[X]) : k[X] :=
  (385 / 65536 : k) • A ^ 6 -
    (385 / 4096 : k) • (A ^ 3 * B ^ 2) +
    (35 / 2048 : k) • B ^ 4

/-- Load-free `ξ` face on the same `A`–`B` tie. -/
def xiAB23Combined810 (A B : k[X]) : k[X] :=
  -(165 / 65536 : k) • A ^ 7 +
    (1925 / 32768 : k) • (A ^ 4 * B ^ 2) -
    (35 / 1024 : k) • (A * B ^ 4)

set_option maxHeartbeats 8000000 in
/-- `μ` without the three `A`–`B` tie monomials. -/
def degreeZeroMuNoAB23Polynomial810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(385 / 8192 : k) • (A ^ 4 * C0)
    - (7245 / 262144 * l : k) • (A ^ 4 * B)
    + (105 / 512 : k) • (A * B ^ 2 * C0)
    + (315 / 8192 * l : k) • (A * B ^ 3)
    + (105 / 1024 : k) • (A ^ 2 * C0 ^ 2)
    + (105 / 512 : k) • (A ^ 2 * B * D0)
    + (945 / 8192 * l : k) • (A ^ 2 * B * C0)
    + (35 / 512 : k) • (A ^ 3 * E0)
    + (315 / 8192 * l : k) • (A ^ 3 * D0)
    - (357 / 8192 * beta : k) • (A ^ 3 * B)
    - (45 / 2048 * gamma : k) • A ^ 4
    - (5 / 128 : k) • C0 ^ 3
    - (15 / 64 : k) • (B * C0 * D0)
    - (63 / 1024 * l : k) • (B * C0 ^ 2)
    - (15 / 128 : k) • (B ^ 2 * E0)
    - (63 / 1024 * l : k) • (B ^ 2 * D0)
    + (21 / 1024 * beta : k) • B ^ 3
    - (15 / 128 : k) • (A * D0 ^ 2)
    - (15 / 64 : k) • (A * C0 * E0)
    - (63 / 512 * l : k) • (A * C0 * D0)
    - (15 / 64 : k) • (A * B * F0)
    - (63 / 512 * l : k) • (A * B * E0)
    + (63 / 512 * beta : k) • (A * B * C0)
    + (15 / 128 * gamma : k) • (A * B ^ 2)
    - (15 / 128 : k) • (A ^ 2 * G0)
    - (63 / 1024 * l : k) • (A ^ 2 * F0)
    + (63 / 1024 * beta : k) • (A ^ 2 * D0)
    + (15 / 128 * gamma : k) • (A ^ 2 * C0)
    + (165 / 1024 * delta : k) • (A ^ 2 * B)
    + (1 / 16 * epsilon : k) • A ^ 3
    + (5 / 32 : k) • E0 ^ 2
    + (5 / 16 : k) • (D0 * F0)
    + (9 / 64 * l : k) • (D0 * E0)
    + (5 / 16 : k) • (C0 * G0)
    + (9 / 64 * l : k) • (C0 * F0)
    - (7 / 64 * beta : k) • (C0 * D0)
    - (3 / 32 * gamma : k) • C0 ^ 2
    + (9 / 64 * l : k) • (B * G0)
    - (7 / 64 * beta : k) • (B * E0)
    - (3 / 16 * gamma : k) • (B * D0)
    - (15 / 64 * delta : k) • (B * C0)
    - (1 / 8 * epsilon : k) • B ^ 2
    - (7 / 64 * beta : k) • (A * F0)
    - (3 / 16 * gamma : k) • (A * E0)
    - (15 / 64 * delta : k) • (A * D0)
    - (1 / 4 * epsilon : k) • (A * C0)
    - (15 / 64 * zeta : k) • (A * B)
    - (3 / 32 * eta : k) • A ^ 2
    + (3 / 4 * gamma : k) • G0
    + (5 / 8 * delta : k) • F0
    + (1 / 2 * epsilon : k) • E0
    + (3 / 8 * zeta : k) • D0
    + (1 / 4 * eta : k) • C0
    + (1 / 8 * theta : k) • B

set_option maxHeartbeats 8000000 in
/-- `ξ` without the three `A`–`B` tie monomials. -/
def degreeZeroXiNoAB23Polynomial810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  (385 / 16384 : k) • (A ^ 5 * C0)
    + (7245 / 524288 * l : k) • (A ^ 5 * B)
    - (105 / 512 : k) • (A ^ 2 * B ^ 2 * C0)
    - (315 / 8192 * l : k) • (A ^ 2 * B ^ 3)
    - (35 / 512 : k) • (A ^ 3 * C0 ^ 2)
    - (525 / 4096 : k) • (A ^ 3 * B * D0)
    - (315 / 4096 * l : k) • (A ^ 3 * B * C0)
    - (245 / 8192 : k) • (A ^ 4 * E0)
    - (4725 / 262144 * l : k) • (A ^ 4 * D0)
    + (357 / 16384 * beta : k) • (A ^ 4 * B)
    + (9 / 1024 * gamma : k) • A ^ 5
    + (45 / 512 : k) • (B ^ 2 * C0 ^ 2)
    + (55 / 1024 : k) • (B ^ 3 * D0)
    + (63 / 2048 * l : k) • (B ^ 3 * C0)
    + (15 / 256 : k) • (A * C0 ^ 3)
    + (165 / 512 : k) • (A * B * C0 * D0)
    + (189 / 2048 * l : k) • (A * B * C0 ^ 2)
    + (75 / 512 : k) • (A * B ^ 2 * E0)
    + (693 / 8192 * l : k) • (A * B ^ 2 * D0)
    - (63 / 2048 * beta : k) • (A * B ^ 3)
    + (75 / 1024 : k) • (A ^ 2 * D0 ^ 2)
    + (75 / 512 : k) • (A ^ 2 * C0 * E0)
    + (693 / 8192 * l : k) • (A ^ 2 * C0 * D0)
    + (135 / 1024 : k) • (A ^ 2 * B * F0)
    + (315 / 4096 * l : k) • (A ^ 2 * B * E0)
    - (189 / 2048 * beta : k) • (A ^ 2 * B * C0)
    - (45 / 512 * gamma : k) • (A ^ 2 * B ^ 2)
    + (5 / 128 : k) • (A ^ 3 * G0)
    + (189 / 8192 * l : k) • (A ^ 3 * F0)
    - (231 / 8192 * beta : k) • (A ^ 3 * D0)
    - (15 / 256 * gamma : k) • (A ^ 3 * C0)
    - (165 / 2048 * delta : k) • (A ^ 3 * B)
    - (3 / 128 * epsilon : k) • A ^ 4
    - (15 / 128 : k) • (C0 * D0 ^ 2)
    - (15 / 128 : k) • (C0 ^ 2 * E0)
    - (63 / 1024 * l : k) • (C0 ^ 2 * D0)
    - (25 / 128 : k) • (B * D0 * E0)
    - (27 / 512 * l : k) • (B * D0 ^ 2)
    - (25 / 128 : k) • (B * C0 * F0)
    - (27 / 256 * l : k) • (B * C0 * E0)
    + (7 / 128 * beta : k) • (B * C0 ^ 2)
    - (5 / 64 : k) • (B ^ 2 * G0)
    - (45 / 1024 * l : k) • (B ^ 2 * F0)
    + (49 / 1024 * beta : k) • (B ^ 2 * D0)
    + (3 / 32 * gamma : k) • (B ^ 2 * C0)
    + (5 / 128 * delta : k) • B ^ 3
    - (5 / 64 : k) • (A * E0 ^ 2)
    - (5 / 32 : k) • (A * D0 * F0)
    - (45 / 512 * l : k) • (A * D0 * E0)
    - (5 / 32 : k) • (A * C0 * G0)
    - (45 / 512 * l : k) • (A * C0 * F0)
    + (49 / 512 * beta : k) • (A * C0 * D0)
    + (3 / 32 * gamma : k) • (A * C0 ^ 2)
    - (9 / 128 * l : k) • (A * B * G0)
    + (21 / 256 * beta : k) • (A * B * E0)
    + (21 / 128 * gamma : k) • (A * B * D0)
    + (15 / 64 * delta : k) • (A * B * C0)
    + (1 / 8 * epsilon : k) • (A * B ^ 2)
    + (35 / 1024 * beta : k) • (A ^ 2 * F0)
    + (9 / 128 * gamma : k) • (A ^ 2 * E0)
    + (105 / 1024 * delta : k) • (A ^ 2 * D0)
    + (1 / 8 * epsilon : k) • (A ^ 2 * C0)
    + (15 / 128 * zeta : k) • (A ^ 2 * B)
    + (1 / 32 * eta : k) • A ^ 3
    + (5 / 32 : k) • F0 ^ 2
    + (5 / 16 : k) • (E0 * G0)
    + (9 / 64 * l : k) • (E0 * F0)
    + (9 / 64 * l : k) • (D0 * G0)
    - (7 / 64 * beta : k) • (D0 * E0)
    - (3 / 32 * gamma : k) • D0 ^ 2
    - (7 / 64 * beta : k) • (C0 * F0)
    - (3 / 16 * gamma : k) • (C0 * E0)
    - (15 / 64 * delta : k) • (C0 * D0)
    - (1 / 8 * epsilon : k) • C0 ^ 2
    - (3 / 32 * gamma : k) • (B * F0)
    - (5 / 32 * delta : k) • (B * E0)
    - (3 / 16 * epsilon : k) • (B * D0)
    - (3 / 16 * zeta : k) • (B * C0)
    - (1 / 16 * eta : k) • B ^ 2
    - (5 / 64 * delta : k) • (A * F0)
    - (1 / 8 * epsilon : k) • (A * E0)
    - (9 / 64 * zeta : k) • (A * D0)
    - (1 / 8 * eta : k) • (A * C0)
    - (1 / 16 * theta : k) • (A * B)
    + (1 / 2 * epsilon : k) • G0
    + (3 / 8 * zeta : k) • F0
    + (1 / 4 * eta : k) • E0
    + (1 / 8 * theta : k) • D0

set_option maxHeartbeats 16000000 in
theorem degreeZeroMuPolynomial810_eq_AB23_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0 =
      muAB23Combined810 A B +
        degreeZeroMuNoAB23Polynomial810 l beta gamma delta epsilon zeta
          eta theta A B C0 D0 E0 F0 G0 := by
  simp only [degreeZeroMuPolynomial810, muAB23Combined810,
    degreeZeroMuNoAB23Polynomial810]
  module

set_option maxHeartbeats 16000000 in
theorem degreeZeroXiPolynomial810_eq_AB23_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroXiPolynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0 =
      xiAB23Combined810 A B +
        degreeZeroXiNoAB23Polynomial810 l beta gamma delta epsilon zeta
          eta theta A B C0 D0 E0 F0 G0 := by
  simp only [degreeZeroXiPolynomial810, xiAB23Combined810,
    degreeZeroXiNoAB23Polynomial810]
  module

end MixedCombinedFaces810

/-! ## Rest-degree bounds -/

section MixedRests810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000 in
theorem degreeZeroOmicronNoB5_natDegree_lt_of_mixedAPos
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : B5LeadsMixedAPosCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroOmicronNoB5Polynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      5 * B.natDegree := by
  rcases hcone with ⟨hBpos, hApos, h3a, hC, hD, hE, hF, hG⟩
  simp only [degreeZeroOmicronNoB5Polynomial810, zero_mul, mul_zero, zero_smul, smul_zero,
    zero_pow_two_rt, zero_pow_three_rt, zero_pow_four_rt, zero_pow_five_rt,
    zero_pow_six_rt, zero_pow_seven_rt, hC, hD, hE, hF, hG]
  compute_degree
  simp only [hC, hD, hE, hF, hG]
  have h3 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt h3a
  have h6ab : 6 * A.natDegree + B.natDegree + 1 ≤ 5 * B.natDegree := by omega
  have h7a : 7 * A.natDegree + 1 ≤ 5 * B.natDegree := by omega
  have h3a3b : 3 * A.natDegree + 3 * B.natDegree + 1 ≤ 5 * B.natDegree := by omega
  have h4a2b : 4 * A.natDegree + 2 * B.natDegree + 1 ≤ 5 * B.natDegree := by omega
  have ha4b : A.natDegree + 4 * B.natDegree + 1 ≤ 5 * B.natDegree := by omega
  have h6a : 6 * A.natDegree + 1 ≤ 5 * B.natDegree := by omega
  have h4ab : 4 * A.natDegree + B.natDegree + 1 ≤ 5 * B.natDegree := by omega
  have h5a : 5 * A.natDegree + 1 ≤ 5 * B.natDegree := by omega
  have h3a2b : 3 * A.natDegree + 2 * B.natDegree + 1 ≤ 5 * B.natDegree := by omega
  have h2a2b : 2 * A.natDegree + 2 * B.natDegree + 1 ≤ 5 * B.natDegree := by omega
  have h4b : 4 * B.natDegree + 1 ≤ 5 * B.natDegree := by omega
  have h3alow : 3 * A.natDegree + 1 ≤ 5 * B.natDegree := by omega
  have ha3b : A.natDegree + 3 * B.natDegree + 1 ≤ 5 * B.natDegree := by omega
  omega

set_option maxHeartbeats 16000000 in
theorem degreeZeroMuNoAB23_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : AB23RatioTieCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoAB23Polynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      6 * A.natDegree := by
  rcases hcone with ⟨hApos, hBpos, htie, hC, hD, hE, hF, hG⟩
  simp only [degreeZeroMuNoAB23Polynomial810, zero_mul, mul_zero, zero_smul, smul_zero,
    zero_pow_two_rt, zero_pow_three_rt, zero_pow_four_rt, zero_pow_five_rt,
    zero_pow_six_rt, zero_pow_seven_rt, hC, hD, hE, hF, hG]
  compute_degree
  simp only [hC, hD, hE, hF, hG]
  have h4ab : 4 * A.natDegree + B.natDegree + 1 ≤ 6 * A.natDegree := by omega
  have ha3b : A.natDegree + 3 * B.natDegree + 1 ≤ 6 * A.natDegree := by omega
  have h3b : 3 * B.natDegree + 1 ≤ 6 * A.natDegree := by omega
  have h2a2b : 2 * A.natDegree + 2 * B.natDegree + 1 ≤ 6 * A.natDegree := by omega
  omega

set_option maxHeartbeats 16000000 in
theorem degreeZeroXiNoAB23_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : AB23RatioTieCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroXiNoAB23Polynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      7 * A.natDegree := by
  rcases hcone with ⟨hApos, hBpos, htie, hC, hD, hE, hF, hG⟩
  simp only [degreeZeroXiNoAB23Polynomial810, zero_mul, mul_zero, zero_smul, smul_zero,
    zero_pow_two_rt, zero_pow_three_rt, zero_pow_four_rt, zero_pow_five_rt,
    zero_pow_six_rt, zero_pow_seven_rt, hC, hD, hE, hF, hG]
  compute_degree
  simp only [hC, hD, hE, hF, hG]
  have h5ab : 5 * A.natDegree + B.natDegree + 1 ≤ 7 * A.natDegree := by omega
  have h2a3b : 2 * A.natDegree + 3 * B.natDegree + 1 ≤ 7 * A.natDegree := by omega
  have ha3b : A.natDegree + 3 * B.natDegree + 1 ≤ 7 * A.natDegree := by omega
  have h3b : 3 * B.natDegree + 1 ≤ 7 * A.natDegree := by omega
  have h4ab : 4 * A.natDegree + B.natDegree + 1 ≤ 7 * A.natDegree := by omega
  have h2a2b : 2 * A.natDegree + 2 * B.natDegree + 1 ≤ 7 * A.natDegree := by omega
  omega

set_option maxHeartbeats 16000000 in
theorem degreeZeroMuNoC03_natDegree_lt_of_mixedAPos
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : C03LeadsMixedAPosCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoC03Polynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      3 * C0.natDegree := by
  rcases hcone with ⟨hCpos, hApos, hB, h2a, hD, hE, hF, hG⟩
  simp only [degreeZeroMuNoC03Polynomial810, zero_mul, mul_zero, zero_smul, smul_zero,
    zero_pow_two_rt, zero_pow_three_rt, zero_pow_four_rt, zero_pow_five_rt,
    zero_pow_six_rt, zero_pow_seven_rt, hB, hD, hE, hF, hG]
  compute_degree
  simp only [hB, hD, hE, hF, hG]
  have h2 : 2 * A.natDegree + 1 ≤ C0.natDegree := Nat.succ_le_of_lt h2a
  have h6a : 6 * A.natDegree + 1 ≤ 3 * C0.natDegree := by omega
  have h4a : 4 * A.natDegree + 1 ≤ 3 * C0.natDegree := by omega
  have h5a : 5 * A.natDegree + 1 ≤ 3 * C0.natDegree := by omega
  omega

set_option maxHeartbeats 16000000 in
theorem degreeZeroMuNoC03_natDegree_lt_of_mixedBPos
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : C03LeadsMixedBPosCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoC03Polynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      3 * C0.natDegree := by
  rcases hcone with ⟨hCpos, hBpos, hA, h4b, hD, hE, hF, hG⟩
  simp only [degreeZeroMuNoC03Polynomial810, zero_mul, mul_zero, zero_smul, smul_zero,
    zero_pow_two_rt, zero_pow_three_rt, zero_pow_four_rt, zero_pow_five_rt,
    zero_pow_six_rt, zero_pow_seven_rt, hA, hD, hE, hF, hG]
  compute_degree
  simp only [hA, hD, hE, hF, hG]
  have h4 : 4 * B.natDegree + 1 ≤ 3 * C0.natDegree := Nat.succ_le_of_lt h4b
  omega

set_option maxHeartbeats 16000000 in
theorem degreeZeroOmicronNoD03_natDegree_lt_of_mixedAPos
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : D03LeadsMixedAPosCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroOmicronNoD03Polynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      3 * D0.natDegree := by
  rcases hcone with ⟨hDpos, hApos, hB, hC, h7a, h5strict, hE, hF, hG⟩
  simp only [degreeZeroOmicronNoD03Polynomial810, zero_mul, mul_zero, zero_smul, smul_zero,
    zero_pow_two_rt, zero_pow_three_rt, zero_pow_four_rt, zero_pow_five_rt,
    zero_pow_six_rt, zero_pow_seven_rt, hB, hC, hE, hF, hG]
  compute_degree
  simp only [hB, hC, hE, hF, hG]
  have h7 : 7 * A.natDegree + 1 ≤ 3 * D0.natDegree := Nat.succ_le_of_lt h7a
  have h5 : 5 * A.natDegree + 1 ≤ 2 * D0.natDegree := Nat.succ_le_of_lt h5strict
  have h5ad : 5 * A.natDegree + D0.natDegree + 1 ≤ 3 * D0.natDegree := by omega
  have h6a : 6 * A.natDegree + 1 ≤ 3 * D0.natDegree := by omega
  have h2a2d : 2 * A.natDegree + 2 * D0.natDegree + 1 ≤ 3 * D0.natDegree := by omega
  omega

set_option maxHeartbeats 16000000 in
theorem degreeZeroMuNoE02_natDegree_lt_of_mixed
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : E02LeadsMixedCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoE02Polynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      2 * E0.natDegree := by
  rcases hcone with ⟨hEpos, hA, hB, hC, hD, hF, hG⟩
  simp only [degreeZeroMuNoE02Polynomial810, zero_mul, mul_zero, zero_smul, smul_zero,
    zero_pow_two_rt, zero_pow_three_rt, zero_pow_four_rt, zero_pow_five_rt,
    zero_pow_six_rt, zero_pow_seven_rt, hA, hB, hC, hD, hF]
  compute_degree
  simp only [hA, hB, hC, hD, hF]
  have hG1 : G0.natDegree + 1 ≤ 2 * E0.natDegree := Nat.succ_le_of_lt hG
  omega

set_option maxHeartbeats 16000000 in
theorem degreeZeroXiNoF02_natDegree_lt_of_mixed
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : F02LeadsMixedCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroXiNoF02Polynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      2 * F0.natDegree := by
  rcases hcone with ⟨hFpos, hA, hB, hC, hD, hE, hG⟩
  simp only [degreeZeroXiNoF02Polynomial810, zero_mul, mul_zero, zero_smul, smul_zero,
    zero_pow_two_rt, zero_pow_three_rt, zero_pow_four_rt, zero_pow_five_rt,
    zero_pow_six_rt, zero_pow_seven_rt, hA, hB, hC, hD, hE]
  compute_degree
  simp only [hA, hB, hC, hD, hE]
  have hG1 : G0.natDegree + 1 ≤ 2 * F0.natDegree := Nat.succ_le_of_lt hG
  omega

set_option maxHeartbeats 16000000 in
theorem degreeZeroMuNoC03_natDegree_lt_of_C0D0
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : C0D0RatioTieCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoC03Polynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      3 * C0.natDegree := by
  rcases hcone with ⟨hCpos, htie, hA, hB, hE, hF, hG⟩
  simp only [degreeZeroMuNoC03Polynomial810, zero_mul, mul_zero, zero_smul, smul_zero,
    zero_pow_two_rt, zero_pow_three_rt, zero_pow_four_rt, zero_pow_five_rt,
    zero_pow_six_rt, zero_pow_seven_rt, hA, hB, hE, hF, hG]
  compute_degree
  simp only [hA, hB, hE, hF, hG, htie]
  have h2d : 2 * D0.natDegree + 1 ≤ 3 * C0.natDegree := by omega
  omega

set_option maxHeartbeats 16000000 in
theorem degreeZeroOmicronNoB5_natDegree_lt_of_G0withB
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : UniqueG0WithBCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroOmicronNoB5Polynomial810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0).natDegree <
      5 * B.natDegree := by
  rcases hcone with ⟨hGdeg, hBpos, hA, hC, hD, hE, hF⟩
  simp only [degreeZeroOmicronNoB5Polynomial810, zero_mul, mul_zero, zero_smul,
    smul_zero, zero_pow_two_rt, zero_pow_three_rt, zero_pow_four_rt,
    zero_pow_five_rt, zero_pow_six_rt, zero_pow_seven_rt, hA, hC, hD, hE, hF]
  compute_degree
  simp only [hA, hC, hD, hE, hF, hGdeg]
  have h4b : 4 * B.natDegree + 1 ≤ 5 * B.natDegree := by omega
  have hG1 : G0.natDegree + 1 ≤ 5 * B.natDegree := by omega
  have h2bG : 2 * B.natDegree + G0.natDegree + 1 ≤ 5 * B.natDegree := by omega
  omega

end MixedRests810

/-! ## Unique-face and ratio-tie impossibilities -/

section MixedImpossible810

variable {k : Type*} [Field k] [CharZero k]

theorem omicron_B5_impossible_of_mixedAPos
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : B5LeadsMixedAPosCone810 A B C0 D0 E0 F0 G0)
    (hdeg :
      (degreeZeroOmicronPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0) :
    False := by
  have hB : B ≠ 0 := by
    intro hB0
    rcases hcone with ⟨hBpos, _⟩
    simp [hB0] at hBpos
  have hc : (-(21 / 4096 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead :
      ((-(21 / 4096 : k)) • B ^ 5).natDegree = 5 * B.natDegree := by
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :=
    degreeZeroOmicronNoB5_natDegree_lt_of_mixedAPos l beta gamma delta
      epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone
  rw [degreeZeroOmicronPolynomial810_eq_B5_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hBpos, _⟩
  omega


set_option maxHeartbeats 16000000 in
theorem muAB23Combined810_natDegree_eq_of_coeff_ne
    {A B : k[X]}
    (hA : A ≠ 0) (hB : B ≠ 0)
    (htie : 3 * A.natDegree = 2 * B.natDegree)
    (hcoeff :
      (11 : k) * A.leadingCoeff ^ 6 -
          176 * (A.leadingCoeff ^ 3 * B.leadingCoeff ^ 2) +
            32 * B.leadingCoeff ^ 4 ≠
        0) :
    (muAB23Combined810 A B).natDegree = 6 * A.natDegree := by
  have hA6 : (A ^ 6).natDegree = 6 * A.natDegree := natDegree_pow A 6
  have hA3B2 :
      (A ^ 3 * B ^ 2).natDegree = 6 * A.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hA) (pow_ne_zero 2 hB),
      natDegree_pow, natDegree_pow]
    omega
  have hB4' : (B ^ 4).natDegree = 6 * A.natDegree := by
    have hB4 : (B ^ 4).natDegree = 4 * B.natDegree := natDegree_pow B 4
    have : 4 * B.natDegree = 6 * A.natDegree := by omega
    simpa [hB4] using this
  have hsmul (c : k) {p : k[X]} {n : ℕ} (hp : p.natDegree = n) :
      (c • p).natDegree ≤ n :=
    (natDegree_smul_le810 c p).trans hp.le
  have hle :
      (muAB23Combined810 A B).natDegree ≤ 6 * A.natDegree := by
    simp only [muAB23Combined810]
    refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · exact (natDegree_sub_le _ _).trans
        (max_le (hsmul _ hA6) (hsmul _ hA3B2))
    · exact hsmul _ hB4'
  have h35 : (35 / 65536 : k) ≠ 0 :=
    div_ne_zero (by norm_num) (by norm_num)
  have hscale :
      (muAB23Combined810 A B).coeff (6 * A.natDegree) =
        (35 / 65536 : k) *
          (11 * A.leadingCoeff ^ 6 -
            176 * (A.leadingCoeff ^ 3 * B.leadingCoeff ^ 2) +
              32 * B.leadingCoeff ^ 4) := by
    have h1 : (A ^ 6).coeff (6 * A.natDegree) = A.leadingCoeff ^ 6 := by
      rw [← hA6, coeff_natDegree, leadingCoeff_pow]
    have h1' : (A ^ 6).coeff (A.natDegree * 6) = A.leadingCoeff ^ 6 := by
      rw [mul_comm A.natDegree 6]
      exact h1
    have h2 : (A ^ 3 * B ^ 2).coeff (6 * A.natDegree) =
        A.leadingCoeff ^ 3 * B.leadingCoeff ^ 2 := by
      rw [← hA3B2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow,
        leadingCoeff_pow]
    have h2' : (A ^ 3 * B ^ 2).coeff (A.natDegree * 6) =
        A.leadingCoeff ^ 3 * B.leadingCoeff ^ 2 := by
      rw [mul_comm A.natDegree 6]
      exact h2
    have h3 : (B ^ 4).coeff (6 * A.natDegree) = B.leadingCoeff ^ 4 := by
      rw [← hB4', coeff_natDegree, leadingCoeff_pow]
    have h3' : (B ^ 4).coeff (A.natDegree * 6) = B.leadingCoeff ^ 4 := by
      rw [mul_comm A.natDegree 6]
      exact h3
    simp only [muAB23Combined810, coeff_add, coeff_sub, coeff_smul, smul_eq_mul,
      h1, h1', h2, h2', h3, h3']
    ring
  have htop :
      (muAB23Combined810 A B).coeff (6 * A.natDegree) ≠ 0 := by
    rw [hscale]
    exact mul_ne_zero h35 hcoeff
  exact natDegree_eq_of_le_of_coeff_ne_zero hle htop

set_option maxHeartbeats 32000000 in
theorem xiAB23Combined810_natDegree_eq_of_coeff_ne
    {A B : k[X]}
    (hA : A ≠ 0) (hB : B ≠ 0)
    (htie : 3 * A.natDegree = 2 * B.natDegree)
    (hcoeff :
      (33 : k) * A.leadingCoeff ^ 6 -
          770 * (A.leadingCoeff ^ 3 * B.leadingCoeff ^ 2) +
            448 * B.leadingCoeff ^ 4 ≠
        0) :
    (xiAB23Combined810 A B).natDegree = 7 * A.natDegree := by
  have hA7 : (A ^ 7).natDegree = 7 * A.natDegree := natDegree_pow A 7
  have hA4B2 :
      (A ^ 4 * B ^ 2).natDegree = 7 * A.natDegree := by
    rw [natDegree_mul (pow_ne_zero 4 hA) (pow_ne_zero 2 hB),
      natDegree_pow, natDegree_pow]
    omega
  have hAB4 :
      (A * B ^ 4).natDegree = 7 * A.natDegree := by
    rw [natDegree_mul hA (pow_ne_zero 4 hB), natDegree_pow]
    omega
  have hsmul (c : k) {p : k[X]} {n : ℕ} (hp : p.natDegree = n) :
      (c • p).natDegree ≤ n :=
    (natDegree_smul_le810 c p).trans hp.le
  have hsmul_neg (c : k) {p : k[X]} {n : ℕ} (hp : p.natDegree = n) :
      (-(c • p)).natDegree ≤ n := by
    rw [natDegree_neg]
    exact hsmul c hp
  have hle :
      (xiAB23Combined810 A B).natDegree ≤ 7 * A.natDegree := by
    simp only [xiAB23Combined810]
    refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
      · first | exact hsmul _ hA7 | exact hsmul_neg _ hA7
      · exact hsmul _ hA4B2
    · first | exact hsmul _ hAB4 | exact hsmul_neg _ hAB4
  have h5 : (-(5 / 65536 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hr : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hA
  have hscale :
      (xiAB23Combined810 A B).coeff (7 * A.natDegree) =
        (-(5 / 65536 : k)) * A.leadingCoeff *
          (33 * A.leadingCoeff ^ 6 -
            770 * (A.leadingCoeff ^ 3 * B.leadingCoeff ^ 2) +
              448 * B.leadingCoeff ^ 4) := by
    have h1 : (A ^ 7).coeff (7 * A.natDegree) = A.leadingCoeff ^ 7 := by
      rw [← hA7, coeff_natDegree, leadingCoeff_pow]
    have h1' : (A ^ 7).coeff (A.natDegree * 7) = A.leadingCoeff ^ 7 := by
      rw [mul_comm A.natDegree 7]
      exact h1
    have h2 : (A ^ 4 * B ^ 2).coeff (7 * A.natDegree) =
        A.leadingCoeff ^ 4 * B.leadingCoeff ^ 2 := by
      rw [← hA4B2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow,
        leadingCoeff_pow]
    have h2' : (A ^ 4 * B ^ 2).coeff (A.natDegree * 7) =
        A.leadingCoeff ^ 4 * B.leadingCoeff ^ 2 := by
      rw [mul_comm A.natDegree 7]
      exact h2
    have h3 : (A * B ^ 4).coeff (7 * A.natDegree) =
        A.leadingCoeff * B.leadingCoeff ^ 4 := by
      rw [← hAB4, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
    have h3' : (A * B ^ 4).coeff (A.natDegree * 7) =
        A.leadingCoeff * B.leadingCoeff ^ 4 := by
      rw [mul_comm A.natDegree 7]
      exact h3
    simp only [xiAB23Combined810, coeff_add, coeff_sub, coeff_smul, smul_eq_mul,
      h1, h1', h2, h2', h3, h3']
    ring
  have htop :
      (xiAB23Combined810 A B).coeff (7 * A.natDegree) ≠ 0 := by
    rw [hscale]
    exact mul_ne_zero (mul_ne_zero h5 hr) hcoeff
  exact natDegree_eq_of_le_of_coeff_ne_zero hle htop

set_option maxHeartbeats 16000000 in
theorem mu_AB23_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : AB23RatioTieCone810 A B C0 D0 E0 F0 G0)
    (hmuDeg :
      (degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0)
    (hxiDeg :
      (degreeZeroXiPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0) :
    False := by
  have hApos : 0 < A.natDegree := hcone.1
  have htie : 3 * A.natDegree = 2 * B.natDegree := hcone.2.2.1
  have hAne : A ≠ 0 := by
    intro hA0
    have : A.natDegree = 0 := by simp [hA0]
    omega
  have hBpos : 0 < B.natDegree := hcone.2.1
  have hBne : B ≠ 0 := by
    intro hB0
    simp [hB0] at hBpos
  by_cases hdrop :
      (11 : k) * A.leadingCoeff ^ 6 -
          176 * (A.leadingCoeff ^ 3 * B.leadingCoeff ^ 2) +
            32 * B.leadingCoeff ^ 4 = 0
  · have hxiNe :=
      xi_AB23_inner_ne_of_mu_zero (A.leadingCoeff) (B.leadingCoeff)
        (leadingCoeff_ne_zero.mpr hAne) hdrop
    have hcombdeg :=
      xiAB23Combined810_natDegree_eq_of_coeff_ne hAne hBne htie hxiNe
    have hrestξ :=
      degreeZeroXiNoAB23_natDegree_lt l beta gamma delta epsilon zeta
        eta theta A B C0 D0 E0 F0 G0 hcone
    rw [degreeZeroXiPolynomial810_eq_AB23_add_rest,
      natDegree_add_eq_left_of_natDegree_lt (by rwa [hcombdeg]),
      hcombdeg] at hxiDeg
    omega
  · have hcombdeg :=
      muAB23Combined810_natDegree_eq_of_coeff_ne hAne hBne htie hdrop
    have hrest :=
      degreeZeroMuNoAB23_natDegree_lt l beta gamma delta epsilon zeta
        eta theta A B C0 D0 E0 F0 G0 hcone
    rw [degreeZeroMuPolynomial810_eq_AB23_add_rest,
      natDegree_add_eq_left_of_natDegree_lt (by rwa [hcombdeg]),
      hcombdeg] at hmuDeg
    omega

theorem mu_C03_impossible_of_mixedAPos
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : C03LeadsMixedAPosCone810 A B C0 D0 E0 F0 G0)
    (hdeg :
      (degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0) :
    False := by
  have hC : C0 ≠ 0 := by
    intro hC0
    rcases hcone with ⟨hCpos, _⟩
    simp [hC0] at hCpos
  have hc : (-(5 / 128 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead :
      ((-(5 / 128 : k)) • C0 ^ 3).natDegree = 3 * C0.natDegree := by
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :=
    degreeZeroMuNoC03_natDegree_lt_of_mixedAPos l beta gamma delta
      epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone
  rw [degreeZeroMuPolynomial810_eq_C03_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hCpos, _⟩
  omega


theorem mu_C03_impossible_of_mixedBPos
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : C03LeadsMixedBPosCone810 A B C0 D0 E0 F0 G0)
    (hdeg :
      (degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0) :
    False := by
  have hC : C0 ≠ 0 := by
    intro hC0
    rcases hcone with ⟨hCpos, _⟩
    simp [hC0] at hCpos
  have hc : (-(5 / 128 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead :
      ((-(5 / 128 : k)) • C0 ^ 3).natDegree = 3 * C0.natDegree := by
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :=
    degreeZeroMuNoC03_natDegree_lt_of_mixedBPos l beta gamma delta
      epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone
  rw [degreeZeroMuPolynomial810_eq_C03_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hCpos, _⟩
  omega

theorem omicron_D03_impossible_of_mixedAPos
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : D03LeadsMixedAPosCone810 A B C0 D0 E0 F0 G0)
    (hdeg :
      (degreeZeroOmicronPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0) :
    False := by
  have hD : D0 ≠ 0 := by
    intro hD0
    rcases hcone with ⟨hDpos, _⟩
    simp [hD0] at hDpos
  have hc : (-(5 / 128 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead :
      ((-(5 / 128 : k)) • D0 ^ 3).natDegree = 3 * D0.natDegree := by
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :=
    degreeZeroOmicronNoD03_natDegree_lt_of_mixedAPos l beta gamma delta
      epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone
  rw [degreeZeroOmicronPolynomial810_eq_D03_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hDpos, _⟩
  omega

theorem mu_C03_impossible_of_C0D0
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : C0D0RatioTieCone810 A B C0 D0 E0 F0 G0)
    (hdeg :
      (degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0) :
    False := by
  have hC : C0 ≠ 0 := by
    intro hC0
    rcases hcone with ⟨hCpos, _⟩
    simp [hC0] at hCpos
  have hc : (-(5 / 128 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead :
      ((-(5 / 128 : k)) • C0 ^ 3).natDegree = 3 * C0.natDegree := by
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :=
    degreeZeroMuNoC03_natDegree_lt_of_C0D0 l beta gamma delta epsilon
      zeta eta theta A B C0 D0 E0 F0 G0 hcone
  rw [degreeZeroMuPolynomial810_eq_C03_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hCpos, _⟩
  omega

theorem omicron_B5_impossible_of_G0withB
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : UniqueG0WithBCone810 A B C0 D0 E0 F0 G0)
    (hdeg :
      (degreeZeroOmicronPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0) :
    False := by
  have hB : B ≠ 0 := by
    intro hB0
    rcases hcone with ⟨_, hBpos, _⟩
    simp [hB0] at hBpos
  have hc : (-(21 / 4096 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead :
      ((-(21 / 4096 : k)) • B ^ 5).natDegree = 5 * B.natDegree := by
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :=
    degreeZeroOmicronNoB5_natDegree_lt_of_G0withB l beta gamma delta
      epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone
  rw [degreeZeroOmicronPolynomial810_eq_B5_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨_, hBpos, _⟩
  omega

theorem mu_E02_impossible_of_mixed
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : E02LeadsMixedCone810 A B C0 D0 E0 F0 G0)
    (hdeg :
      (degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0) :
    False := by
  have hE : E0 ≠ 0 := by
    intro hE0
    rcases hcone with ⟨hEpos, _⟩
    simp [hE0] at hEpos
  have hc : (5 / 32 : k) ≠ 0 :=
    div_ne_zero (by norm_num) (by norm_num)
  have hlead :
      ((5 / 32 : k) • E0 ^ 2).natDegree = 2 * E0.natDegree := by
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :=
    degreeZeroMuNoE02_natDegree_lt_of_mixed l beta gamma delta epsilon
      zeta eta theta A B C0 D0 E0 F0 G0 hcone
  rw [degreeZeroMuPolynomial810_eq_E02_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hEpos, _⟩
  omega

theorem xi_F02_impossible_of_mixed
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : F02LeadsMixedCone810 A B C0 D0 E0 F0 G0)
    (hdeg :
      (degreeZeroXiPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0) :
    False := by
  have hF : F0 ≠ 0 := by
    intro hF0
    rcases hcone with ⟨hFpos, _⟩
    simp [hF0] at hFpos
  have hc : (5 / 32 : k) ≠ 0 :=
    div_ne_zero (by norm_num) (by norm_num)
  have hlead :
      ((5 / 32 : k) • F0 ^ 2).natDegree = 2 * F0.natDegree := by
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :=
    degreeZeroXiNoF02_natDegree_lt_of_mixed l beta gamma delta epsilon
      zeta eta theta A B C0 D0 E0 F0 G0 hcone
  rw [degreeZeroXiPolynomial810_eq_F02_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hFpos, _⟩
  omega


end MixedImpossible810

/-! ## Source-facing residual after mixed unique faces -/

section MixedClosed810

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- Remaining cones after mixed unique `ξ`/`μ`/`ο` faces, the `C₀`–`D₀`
pair, unique-`G₀` with nonconstant `B`, and the `A`–`B` ratio-tie
`3 deg A = 2 deg B`.  Unique-`G₀` of degree one with `l = 0` is empty
by the parent `uniqueHighG0DegOne_existsPrimitive_false`.  Named
leftover families still open: unique-high `B` with `3 deg A > 2 deg B`
(the `A⁶ B` face of `ο`), unique-high `D₀` with `5 deg A ≥ 2 deg D₀`
(the mixed `A⁵ D₀` of `ο` meets `D₀³`), the remaining non-`A`–`B`
ratio-ties (`A`–`C₀` with `deg C₀ = 2 deg A`, `A`–`E₀`, `B`–`E₀`,
`C₀`–`E₀`, `A`–`F₀`, `B`–`D₀`), and mixed supports of three or more
nonconstant letters not already a unique face. -/
theorem normalized810ScaleZero_coneMixedResidual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    ∃ (t j lambda cleared l beta gamma delta epsilon zeta eta theta
        cXi cMu cOm : k) (A B C0 D0 E0 F0 G0 : k[X]),
      t ≠ 0 ∧
      j ≠ 0 ∧
      j / t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      derivative
          (degreeZeroPrimitivePolynomial810 l beta gamma delta epsilon
            zeta eta theta A B C0 D0 E0 F0 G0) =
        Polynomial.C (j / t) ∧
      (degreeZeroXiPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0 ∧
      (degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0 ∧
      (degreeZeroOmicronPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0 ∧
      ¬ ARatioLeadsXiCone810 A B C0 D0 E0 F0 G0 ∧
      (UniqueHighG0DegOneCone810 A B C0 D0 E0 F0 G0 → l = 0) ∧
      ¬ B5LeadsMixedAPosCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ AB23RatioTieCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ C03LeadsMixedAPosCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ C03LeadsMixedBPosCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ D03LeadsMixedAPosCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ E02LeadsMixedCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ F02LeadsMixedCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ C0D0RatioTieCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ UniqueG0WithBCone810 A B C0 D0 E0 F0 G0 := by
  obtain ⟨t, j, lambda, cleared, l, beta, gamma, delta, epsilon, zeta, eta,
      theta, cXi, cMu, cOm, A, B, C0, D0, E0, F0, G0, ht, hj, hjdiv, hHsq,
      hder, hxi, hmu, hom, hARatio, hG0l⟩ :=
    normalized810ScaleZero_coneClosureResidual hsource
  refine ⟨t, j, lambda, cleared, l, beta, gamma, delta, epsilon, zeta, eta,
    theta, cXi, cMu, cOm, A, B, C0, D0, E0, F0, G0, ht, hj, hjdiv, hHsq,
    hder, hxi, hmu, hom, hARatio, hG0l, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · intro hB5
    exact omicron_B5_impossible_of_mixedAPos l beta gamma delta epsilon
      zeta eta theta A B C0 D0 E0 F0 G0 hB5 hom
  · intro hAB
    exact mu_AB23_impossible l beta gamma delta epsilon zeta eta theta
      A B C0 D0 E0 F0 G0 hAB hmu hxi
  · intro hC
    exact mu_C03_impossible_of_mixedAPos l beta gamma delta epsilon zeta
      eta theta A B C0 D0 E0 F0 G0 hC hmu
  · intro hCB
    exact mu_C03_impossible_of_mixedBPos l beta gamma delta epsilon zeta
      eta theta A B C0 D0 E0 F0 G0 hCB hmu
  · intro hD
    exact omicron_D03_impossible_of_mixedAPos l beta gamma delta epsilon
      zeta eta theta A B C0 D0 E0 F0 G0 hD hom
  · intro hE
    exact mu_E02_impossible_of_mixed l beta gamma delta epsilon zeta
      eta theta A B C0 D0 E0 F0 G0 hE hmu
  · intro hF
    exact xi_F02_impossible_of_mixed l beta gamma delta epsilon zeta
      eta theta A B C0 D0 E0 F0 G0 hF hxi
  · intro hCD
    exact mu_C03_impossible_of_C0D0 l beta gamma delta epsilon zeta eta
      theta A B C0 D0 E0 F0 G0 hCD hmu
  · intro hGB
    exact omicron_B5_impossible_of_G0withB l beta gamma delta epsilon
      zeta eta theta A B C0 D0 E0 F0 G0 hGB hom

theorem normalized810ScaleZero_impossible_of_mixedResidual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0)
    (hres :
      (∃ (t j lambda cleared l beta gamma delta epsilon zeta eta theta
          cXi cMu cOm : k) (A B C0 D0 E0 F0 G0 : k[X]),
        t ≠ 0 ∧ j ≠ 0 ∧ j / t ≠ 0 ∧ H = (Polynomial.C t) ^ 2 ∧
          derivative
              (degreeZeroPrimitivePolynomial810 l beta gamma delta
                epsilon zeta eta theta A B C0 D0 E0 F0 G0) =
            Polynomial.C (j / t) ∧
          (degreeZeroXiPolynomial810 l beta gamma delta epsilon zeta eta
              theta A B C0 D0 E0 F0 G0).natDegree =
            0 ∧
          (degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta
              theta A B C0 D0 E0 F0 G0).natDegree =
            0 ∧
          (degreeZeroOmicronPolynomial810 l beta gamma delta epsilon zeta
              eta theta A B C0 D0 E0 F0 G0).natDegree =
            0 ∧
          ¬ ARatioLeadsXiCone810 A B C0 D0 E0 F0 G0 ∧
          (UniqueHighG0DegOneCone810 A B C0 D0 E0 F0 G0 → l = 0) ∧
          ¬ B5LeadsMixedAPosCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ AB23RatioTieCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ C03LeadsMixedAPosCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ C03LeadsMixedBPosCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ D03LeadsMixedAPosCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ E02LeadsMixedCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ F02LeadsMixedCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ C0D0RatioTieCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ UniqueG0WithBCone810 A B C0 D0 E0 F0 G0) →
        False) :
    False :=
  hres (normalized810ScaleZero_coneMixedResidual hsource)

end MixedClosed810

#print axioms B5LeadsMixedAPosCone810
#print axioms AB23RatioTieCone810
#print axioms mu_xi_AB23_inner_identity
#print axioms xi_AB23_inner_ne_of_mu_zero
#print axioms omicron_B5_impossible_of_mixedAPos
#print axioms mu_AB23_impossible
#print axioms mu_C03_impossible_of_C0D0
#print axioms omicron_B5_impossible_of_G0withB
#print axioms normalized810ScaleZero_coneMixedResidual
#print axioms normalized810ScaleZero_impossible_of_mixedResidual

end Max11DegreeRoutes
