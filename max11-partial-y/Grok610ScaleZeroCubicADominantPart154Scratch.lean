import Grok610ScaleZeroCubicConesScratch
import Grok610AlignedNonsquareDegreeZeroPrimitiveScratch
import Grok610ScaleZeroCubicADominantPart153Scratch
import Max11SpeedReflectDegLibScratch

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

section CubicBalanced610

variable {k : Type*} [Field k] [CharZero k]

def n1CubicSigmaFaceBCDE610 (A B C D E : k[X]) : k[X] :=
  (5 / 81 : k) • (A * B ^ 2 * D)
  - (10 / 27 : k) • (B * C * E)
  - (5 / 27 : k) • (C ^ 2 * D)

end CubicBalanced610

end Max11DegreeRoutes
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

section CubicBalanced610

variable {k : Type*} [Field k] [CharZero k]

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

end CubicBalanced610

end Max11DegreeRoutes
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

section CubicBalanced610

variable {k : Type*} [Field k] [CharZero k]

def kappaCubicSigmaInnerBCDE610 (a b c d e : k) : k :=
  a * b ^ 3 + (-9 : k) * b * c ^ 2 + 54 * d * e

end CubicBalanced610

end Max11DegreeRoutes
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

section CubicBalanced610

variable {k : Type*} [Field k] [CharZero k]

def lambdaCubicSigmaInnerBCDE610 (a b c d e : k) : k :=
  a * b ^ 2 * c + (-3 : k) * a * d ^ 2 - c ^ 3 + 9 * e ^ 2

end CubicBalanced610

end Max11DegreeRoutes
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

section CubicBalanced610

variable {k : Type*} [Field k] [CharZero k]

def omicronCubicSigmaInnerBCDE610 (a b c d e : k) : k :=
  a * b ^ 2 * e + 2 * a * b * c * d + (-3 : k) * c ^ 2 * e

end CubicBalanced610

end Max11DegreeRoutes
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

section CubicBalanced610

variable {k : Type*} [Field k] [CharZero k]

def n1CubicSigmaInnerBCDE610 (a b c d e : k) : k :=
  a * b ^ 2 * d + (-6 : k) * b * c * e + (-3 : k) * c ^ 2 * d

end CubicBalanced610

end Max11DegreeRoutes
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

end CubicAllLettersZero610

end Max11DegreeRoutes
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

section CubicLoadB0_610

variable {k : Type*} [Field k] [CharZero k]

/-- β-column of `N₁` is `7/6912 · β · A⁵`.  Competes when `6 Θ ≥ 3 ρ`. -/
def cubicLoadCompetesBeta610 (A B C D E : k[X]) : Prop :=
  CubicRatioConeA610 A B C D E ∧
    4 * A.natDegree ≥ 9 * B.natDegree ∧
    11 * A.natDegree ≥ 18 * C.natDegree ∧
    3 * A.natDegree ≥ 4 * D.natDegree ∧
    11 * A.natDegree ≥ 12 * E.natDegree

end CubicLoadB0_610

end Max11DegreeRoutes
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

section CubicLoadB0_610

variable {k : Type*} [Field k] [CharZero k]

/-- δ-column of `N₁` is `35/10368 · δ · A⁴`.  Competes when `6 Θ ≥ 5 ρ`. -/
def cubicLoadCompetesDelta610 (A B C D E : k[X]) : Prop :=
  CubicRatioConeA610 A B C D E ∧
    4 * A.natDegree ≥ 15 * B.natDegree ∧
    11 * A.natDegree ≥ 30 * C.natDegree ∧
    9 * A.natDegree ≥ 20 * D.natDegree ∧
    11 * A.natDegree ≥ 20 * E.natDegree

end CubicLoadB0_610

end Max11DegreeRoutes
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

section CubicLoadB0_610

variable {k : Type*} [Field k] [CharZero k]

/-- ζ-column of `N₁` is `5/432 · ζ · A³`.  Competes when `6 Θ ≥ 7 ρ`. -/
def cubicLoadCompetesZeta610 (A B C D E : k[X]) : Prop :=
  CubicRatioConeA610 A B C D E ∧
    4 * A.natDegree ≥ 21 * B.natDegree ∧
    11 * A.natDegree ≥ 42 * C.natDegree ∧
    9 * A.natDegree ≥ 28 * D.natDegree ∧
    11 * A.natDegree ≥ 28 * E.natDegree

end CubicLoadB0_610

end Max11DegreeRoutes
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

section CubicLoadB0_610

variable {k : Type*} [Field k] [CharZero k]

/-- θ-column of `N₁` is `1/24 · θ · A²`.  Competes when `6 Θ ≥ 9 ρ`. -/
def cubicLoadCompetesTheta610 (A B C D E : k[X]) : Prop :=
  CubicRatioConeA610 A B C D E ∧
    4 * A.natDegree ≥ 27 * B.natDegree ∧
    11 * A.natDegree ≥ 54 * C.natDegree ∧
    9 * A.natDegree ≥ 36 * D.natDegree ∧
    11 * A.natDegree ≥ 36 * E.natDegree

end CubicLoadB0_610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicN1_610

variable {k : Type*} [Field k] [CharZero k]

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

end CubicN1_610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicN1_610

variable {k : Type*} [Field k] [CharZero k]

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

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

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

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
/-- Reflect the unchanged polynomial literal into coefficient/exponent data. -/
private theorem round4_astra4p_part27_polyOf
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroKappaCubicNoSigmaB610 l alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (-(5 / 27 : k)), (-(5 / 27 : k)), (10 / 9 : k),
      (7 / 6912 * l : k), (5 / 288 * l : k), (-(1 / 192 * l : k)),
      (1 / 16 * l : k), (-(1 / 8 * l : k)), (1 / 16 * l : k),
      (-(3 / 16 * l : k)), (3 / 4 * l : k), (3 / 8 * l : k),
      (-(4 / 81 * alpha : k)), (4 / 9 * alpha : k), (4 / 9 * alpha : k),
      (35 / 10368 * beta : k), (7 / 144 * beta : k), (-(7 / 432 * beta : k)),
      (7 / 36 * beta : k), (7 / 36 * beta : k), (7 / 72 * beta : k),
      (5 / 432 * delta : k), (5 / 36 * delta : k), (-(5 / 72 * delta : k)),
      (5 / 6 * delta : k), (2 / 3 * epsilon : k), (1 / 24 * zeta : k),
      (1 / 2 * zeta : k), (1 / 3 * eta : k), (1 / 6 * theta : k)]
      [
      [0, 2, 0, 1, 0], [0, 1, 2, 0, 0], [0, 0, 0, 1, 1], [5, 0, 0, 0, 0],
      [3, 0, 1, 0, 0], [2, 2, 0, 0, 0], [2, 0, 0, 0, 1], [1, 1, 0, 1, 0],
      [1, 0, 2, 0, 0], [0, 2, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 2, 0],
      [0, 3, 0, 0, 0], [0, 1, 0, 0, 1], [0, 0, 1, 1, 0], [4, 0, 0, 0, 0],
      [2, 0, 1, 0, 0], [1, 2, 0, 0, 0], [1, 0, 0, 0, 1], [0, 1, 0, 1, 0],
      [0, 0, 2, 0, 0], [3, 0, 0, 0, 0], [1, 0, 1, 0, 0], [0, 2, 0, 0, 0],
      [0, 0, 0, 0, 1], [0, 0, 0, 1, 0], [2, 0, 0, 0, 0], [0, 0, 1, 0, 0],
      [0, 1, 0, 0, 0], [1, 0, 0, 0, 0]] := by
  unfold degreeZeroKappaCubicNoSigmaB610
  simp only [Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc,
    sub_eq_add_neg, neg_smul, add_assoc]

set_option maxHeartbeats 64000000 in
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
  rw [round4_astra4p_part27_polyOf]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

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

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
/-- Reflect the unchanged polynomial literal into coefficient/exponent data. -/
private theorem round4_astra4p_part32_polyOf
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroLambdaCubicNoSigmaC610 l alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (5 / 81 : k), (5 / 243 : k), (-(5 / 27 : k)),
      (-(5 / 27 : k)), (-(10 / 27 : k)), (5 / 9 : k),
      (-(5 / 6912 * l : k)), (-(1 / 288 * l : k)), (-(1 / 96 * l : k)),
      (1 / 32 * l : k), (-(1 / 8 * l : k)), (-(1 / 8 * l : k)),
      (-(3 / 16 * l : k)), (-(3 / 16 * l : k)), (3 / 4 * l : k),
      (-(4 / 27 * alpha : k)), (-(4 / 27 * alpha : k)), (4 / 9 * alpha : k),
      (2 / 9 * alpha : k), (-(7 / 2592 * beta : k)), (-(7 / 432 * beta : k)),
      (-(7 / 216 * beta : k)), (-(35 / 1296 * beta : k)), (7 / 36 * beta : k),
      (7 / 36 * beta : k), (-(5 / 432 * delta : k)), (-(5 / 36 * delta : k)),
      (-(5 / 36 * delta : k)), (-(1 / 9 * epsilon : k)), (2 / 3 * epsilon : k),
      (-(1 / 12 * zeta : k)), (1 / 2 * zeta : k), (1 / 3 * eta : k),
      (1 / 6 * theta : k)]
      [
      [1, 2, 1, 0, 0], [0, 4, 0, 0, 0], [1, 0, 0, 2, 0], [0, 2, 0, 0, 1],
      [0, 1, 1, 1, 0], [0, 0, 0, 0, 2], [4, 1, 0, 0, 0], [3, 0, 0, 1, 0],
      [2, 1, 1, 0, 0], [1, 3, 0, 0, 0], [1, 1, 0, 0, 1], [1, 0, 1, 1, 0],
      [0, 2, 0, 1, 0], [0, 1, 2, 0, 0], [0, 0, 0, 1, 1], [1, 1, 0, 1, 0],
      [0, 2, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 2, 0], [3, 1, 0, 0, 0],
      [2, 0, 0, 1, 0], [1, 1, 1, 0, 0], [0, 3, 0, 0, 0], [0, 1, 0, 0, 1],
      [0, 0, 1, 1, 0], [2, 1, 0, 0, 0], [1, 0, 0, 1, 0], [0, 1, 1, 0, 0],
      [0, 2, 0, 0, 0], [0, 0, 0, 0, 1], [1, 1, 0, 0, 0], [0, 0, 0, 1, 0],
      [0, 0, 1, 0, 0], [0, 1, 0, 0, 0]] := by
  unfold degreeZeroLambdaCubicNoSigmaC610
  simp only [Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc,
    sub_eq_add_neg, neg_smul, add_assoc]

set_option maxHeartbeats 64000000 in
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
  rw [round4_astra4p_part32_polyOf]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

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

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
/-- Reflect the unchanged polynomial literal into coefficient/exponent data. -/
private theorem round4_astra4p_part37_polyOf
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroLambdaCubicNoSigmaD610 l alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (5 / 81 : k), (5 / 243 : k), (-(5 / 27 : k)),
      (-(10 / 27 : k)), (-(5 / 81 : k)), (5 / 9 : k),
      (-(5 / 6912 * l : k)), (-(1 / 288 * l : k)), (-(1 / 96 * l : k)),
      (1 / 32 * l : k), (-(1 / 8 * l : k)), (-(1 / 8 * l : k)),
      (-(3 / 16 * l : k)), (-(3 / 16 * l : k)), (3 / 4 * l : k),
      (-(4 / 27 * alpha : k)), (-(4 / 27 * alpha : k)), (4 / 9 * alpha : k),
      (2 / 9 * alpha : k), (-(7 / 2592 * beta : k)), (-(7 / 432 * beta : k)),
      (-(7 / 216 * beta : k)), (-(35 / 1296 * beta : k)), (7 / 36 * beta : k),
      (7 / 36 * beta : k), (-(5 / 432 * delta : k)), (-(5 / 36 * delta : k)),
      (-(5 / 36 * delta : k)), (-(1 / 9 * epsilon : k)), (2 / 3 * epsilon : k),
      (-(1 / 12 * zeta : k)), (1 / 2 * zeta : k), (1 / 3 * eta : k),
      (1 / 6 * theta : k)]
      [
      [1, 2, 1, 0, 0], [0, 4, 0, 0, 0], [0, 2, 0, 0, 1], [0, 1, 1, 1, 0],
      [0, 0, 3, 0, 0], [0, 0, 0, 0, 2], [4, 1, 0, 0, 0], [3, 0, 0, 1, 0],
      [2, 1, 1, 0, 0], [1, 3, 0, 0, 0], [1, 1, 0, 0, 1], [1, 0, 1, 1, 0],
      [0, 2, 0, 1, 0], [0, 1, 2, 0, 0], [0, 0, 0, 1, 1], [1, 1, 0, 1, 0],
      [0, 2, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 2, 0], [3, 1, 0, 0, 0],
      [2, 0, 0, 1, 0], [1, 1, 1, 0, 0], [0, 3, 0, 0, 0], [0, 1, 0, 0, 1],
      [0, 0, 1, 1, 0], [2, 1, 0, 0, 0], [1, 0, 0, 1, 0], [0, 1, 1, 0, 0],
      [0, 2, 0, 0, 0], [0, 0, 0, 0, 1], [1, 1, 0, 0, 0], [0, 0, 0, 1, 0],
      [0, 0, 1, 0, 0], [0, 1, 0, 0, 0]] := by
  unfold degreeZeroLambdaCubicNoSigmaD610
  simp only [Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc,
    sub_eq_add_neg, neg_smul, add_assoc]

set_option maxHeartbeats 64000000 in
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
  rw [round4_astra4p_part37_polyOf]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

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

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
/-- Reflect the unchanged polynomial literal into coefficient/exponent data. -/
private theorem round4_astra4p_part42_polyOf
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroLambdaCubicNoSigmaE610 l alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (5 / 81 : k), (5 / 243 : k), (-(5 / 27 : k)),
      (-(5 / 27 : k)), (-(10 / 27 : k)), (-(5 / 81 : k)),
      (-(5 / 6912 * l : k)), (-(1 / 288 * l : k)), (-(1 / 96 * l : k)),
      (1 / 32 * l : k), (-(1 / 8 * l : k)), (-(1 / 8 * l : k)),
      (-(3 / 16 * l : k)), (-(3 / 16 * l : k)), (3 / 4 * l : k),
      (-(4 / 27 * alpha : k)), (-(4 / 27 * alpha : k)), (4 / 9 * alpha : k),
      (2 / 9 * alpha : k), (-(7 / 2592 * beta : k)), (-(7 / 432 * beta : k)),
      (-(7 / 216 * beta : k)), (-(35 / 1296 * beta : k)), (7 / 36 * beta : k),
      (7 / 36 * beta : k), (-(5 / 432 * delta : k)), (-(5 / 36 * delta : k)),
      (-(5 / 36 * delta : k)), (-(1 / 9 * epsilon : k)), (2 / 3 * epsilon : k),
      (-(1 / 12 * zeta : k)), (1 / 2 * zeta : k), (1 / 3 * eta : k),
      (1 / 6 * theta : k)]
      [
      [1, 2, 1, 0, 0], [0, 4, 0, 0, 0], [1, 0, 0, 2, 0], [0, 2, 0, 0, 1],
      [0, 1, 1, 1, 0], [0, 0, 3, 0, 0], [4, 1, 0, 0, 0], [3, 0, 0, 1, 0],
      [2, 1, 1, 0, 0], [1, 3, 0, 0, 0], [1, 1, 0, 0, 1], [1, 0, 1, 1, 0],
      [0, 2, 0, 1, 0], [0, 1, 2, 0, 0], [0, 0, 0, 1, 1], [1, 1, 0, 1, 0],
      [0, 2, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 2, 0], [3, 1, 0, 0, 0],
      [2, 0, 0, 1, 0], [1, 1, 1, 0, 0], [0, 3, 0, 0, 0], [0, 1, 0, 0, 1],
      [0, 0, 1, 1, 0], [2, 1, 0, 0, 0], [1, 0, 0, 1, 0], [0, 1, 1, 0, 0],
      [0, 2, 0, 0, 0], [0, 0, 0, 0, 1], [1, 1, 0, 0, 0], [0, 0, 0, 1, 0],
      [0, 0, 1, 0, 0], [0, 1, 0, 0, 0]] := by
  unfold degreeZeroLambdaCubicNoSigmaE610
  simp only [Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc,
    sub_eq_add_neg, neg_smul, add_assoc]

set_option maxHeartbeats 64000000 in
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
  rw [round4_astra4p_part42_polyOf]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 32000000 in
theorem cubicSigmaInner_BC_identity
    (a b c : k) :
    ((-1 / 40 : k) * a * b * c) * kappaCubicSigmaInnerBC610 a b c +
      ((1 / 40 : k) * a * b ^ 2 + (-1 / 5 : k) * c ^ 2) * lambdaCubicSigmaInnerBC610 a b c =
      c ^ 5 := by
  simp only [kappaCubicSigmaInnerBC610, lambdaCubicSigmaInnerBC610]
  ring

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

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

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
/-- Reflect the unchanged polynomial literal into coefficient/exponent data. -/
private theorem round4_astra4p_part50_polyOf
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroKappaCubicNoSigmaBC610 l alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (-(5 / 27 : k)), (10 / 9 : k), (7 / 6912 * l : k),
      (5 / 288 * l : k), (-(1 / 192 * l : k)), (1 / 16 * l : k),
      (-(1 / 8 * l : k)), (1 / 16 * l : k), (-(3 / 16 * l : k)),
      (3 / 4 * l : k), (3 / 8 * l : k), (-(4 / 81 * alpha : k)),
      (4 / 9 * alpha : k), (4 / 9 * alpha : k), (35 / 10368 * beta : k),
      (7 / 144 * beta : k), (-(7 / 432 * beta : k)), (7 / 36 * beta : k),
      (7 / 36 * beta : k), (7 / 72 * beta : k), (5 / 432 * delta : k),
      (5 / 36 * delta : k), (-(5 / 72 * delta : k)), (5 / 6 * delta : k),
      (2 / 3 * epsilon : k), (1 / 24 * zeta : k), (1 / 2 * zeta : k),
      (1 / 3 * eta : k), (1 / 6 * theta : k)]
      [
      [0, 2, 0, 1, 0], [0, 0, 0, 1, 1], [5, 0, 0, 0, 0], [3, 0, 1, 0, 0],
      [2, 2, 0, 0, 0], [2, 0, 0, 0, 1], [1, 1, 0, 1, 0], [1, 0, 2, 0, 0],
      [0, 2, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 2, 0], [0, 3, 0, 0, 0],
      [0, 1, 0, 0, 1], [0, 0, 1, 1, 0], [4, 0, 0, 0, 0], [2, 0, 1, 0, 0],
      [1, 2, 0, 0, 0], [1, 0, 0, 0, 1], [0, 1, 0, 1, 0], [0, 0, 2, 0, 0],
      [3, 0, 0, 0, 0], [1, 0, 1, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 1],
      [0, 0, 0, 1, 0], [2, 0, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0],
      [1, 0, 0, 0, 0]] := by
  unfold degreeZeroKappaCubicNoSigmaBC610
  simp only [Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc,
    sub_eq_add_neg, neg_smul, add_assoc]

set_option maxHeartbeats 64000000 in
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
  rw [round4_astra4p_part50_polyOf]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

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

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

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

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
/-- Reflect the unchanged polynomial literal into coefficient/exponent data. -/
private theorem round4_astra4p_part55_polyOf
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroLambdaCubicNoSigmaBC610 l alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (5 / 243 : k), (-(5 / 27 : k)), (-(5 / 27 : k)),
      (-(10 / 27 : k)), (5 / 9 : k), (-(5 / 6912 * l : k)),
      (-(1 / 288 * l : k)), (-(1 / 96 * l : k)), (1 / 32 * l : k),
      (-(1 / 8 * l : k)), (-(1 / 8 * l : k)), (-(3 / 16 * l : k)),
      (-(3 / 16 * l : k)), (3 / 4 * l : k), (-(4 / 27 * alpha : k)),
      (-(4 / 27 * alpha : k)), (4 / 9 * alpha : k), (2 / 9 * alpha : k),
      (-(7 / 2592 * beta : k)), (-(7 / 432 * beta : k)), (-(7 / 216 * beta : k)),
      (-(35 / 1296 * beta : k)), (7 / 36 * beta : k), (7 / 36 * beta : k),
      (-(5 / 432 * delta : k)), (-(5 / 36 * delta : k)), (-(5 / 36 * delta : k)),
      (-(1 / 9 * epsilon : k)), (2 / 3 * epsilon : k), (-(1 / 12 * zeta : k)),
      (1 / 2 * zeta : k), (1 / 3 * eta : k), (1 / 6 * theta : k)]
      [
      [0, 4, 0, 0, 0], [1, 0, 0, 2, 0], [0, 2, 0, 0, 1], [0, 1, 1, 1, 0],
      [0, 0, 0, 0, 2], [4, 1, 0, 0, 0], [3, 0, 0, 1, 0], [2, 1, 1, 0, 0],
      [1, 3, 0, 0, 0], [1, 1, 0, 0, 1], [1, 0, 1, 1, 0], [0, 2, 0, 1, 0],
      [0, 1, 2, 0, 0], [0, 0, 0, 1, 1], [1, 1, 0, 1, 0], [0, 2, 1, 0, 0],
      [0, 0, 1, 0, 1], [0, 0, 0, 2, 0], [3, 1, 0, 0, 0], [2, 0, 0, 1, 0],
      [1, 1, 1, 0, 0], [0, 3, 0, 0, 0], [0, 1, 0, 0, 1], [0, 0, 1, 1, 0],
      [2, 1, 0, 0, 0], [1, 0, 0, 1, 0], [0, 1, 1, 0, 0], [0, 2, 0, 0, 0],
      [0, 0, 0, 0, 1], [1, 1, 0, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0],
      [0, 1, 0, 0, 0]] := by
  unfold degreeZeroLambdaCubicNoSigmaBC610
  simp only [Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc,
    sub_eq_add_neg, neg_smul, add_assoc]

set_option maxHeartbeats 64000000 in
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
  rw [round4_astra4p_part55_polyOf]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

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

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

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

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
/-- Reflect the unchanged polynomial literal into coefficient/exponent data. -/
private theorem round4_astra4p_part61_polyOf
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroKappaCubicNoSigmaBD610 l alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (-(5 / 27 : k)), (-(5 / 27 : k)), (10 / 9 : k),
      (7 / 6912 * l : k), (5 / 288 * l : k), (-(1 / 192 * l : k)),
      (1 / 16 * l : k), (-(1 / 8 * l : k)), (1 / 16 * l : k),
      (-(3 / 16 * l : k)), (3 / 4 * l : k), (3 / 8 * l : k),
      (-(4 / 81 * alpha : k)), (4 / 9 * alpha : k), (4 / 9 * alpha : k),
      (35 / 10368 * beta : k), (7 / 144 * beta : k), (-(7 / 432 * beta : k)),
      (7 / 36 * beta : k), (7 / 36 * beta : k), (7 / 72 * beta : k),
      (5 / 432 * delta : k), (5 / 36 * delta : k), (-(5 / 72 * delta : k)),
      (5 / 6 * delta : k), (2 / 3 * epsilon : k), (1 / 24 * zeta : k),
      (1 / 2 * zeta : k), (1 / 3 * eta : k), (1 / 6 * theta : k)]
      [
      [0, 2, 0, 1, 0], [0, 1, 2, 0, 0], [0, 0, 0, 1, 1], [5, 0, 0, 0, 0],
      [3, 0, 1, 0, 0], [2, 2, 0, 0, 0], [2, 0, 0, 0, 1], [1, 1, 0, 1, 0],
      [1, 0, 2, 0, 0], [0, 2, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 2, 0],
      [0, 3, 0, 0, 0], [0, 1, 0, 0, 1], [0, 0, 1, 1, 0], [4, 0, 0, 0, 0],
      [2, 0, 1, 0, 0], [1, 2, 0, 0, 0], [1, 0, 0, 0, 1], [0, 1, 0, 1, 0],
      [0, 0, 2, 0, 0], [3, 0, 0, 0, 0], [1, 0, 1, 0, 0], [0, 2, 0, 0, 0],
      [0, 0, 0, 0, 1], [0, 0, 0, 1, 0], [2, 0, 0, 0, 0], [0, 0, 1, 0, 0],
      [0, 1, 0, 0, 0], [1, 0, 0, 0, 0]] := by
  unfold degreeZeroKappaCubicNoSigmaBD610
  simp only [Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc,
    sub_eq_add_neg, neg_smul, add_assoc]

set_option maxHeartbeats 64000000 in
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
  rw [round4_astra4p_part61_polyOf]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

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

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
/-- Reflect the unchanged polynomial literal into coefficient/exponent data. -/
private theorem round4_astra4p_part66_polyOf
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroKappaCubicNoSigmaBE610 l alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (-(5 / 27 : k)), (-(5 / 27 : k)), (10 / 9 : k),
      (7 / 6912 * l : k), (5 / 288 * l : k), (-(1 / 192 * l : k)),
      (1 / 16 * l : k), (-(1 / 8 * l : k)), (1 / 16 * l : k),
      (-(3 / 16 * l : k)), (3 / 4 * l : k), (3 / 8 * l : k),
      (-(4 / 81 * alpha : k)), (4 / 9 * alpha : k), (4 / 9 * alpha : k),
      (35 / 10368 * beta : k), (7 / 144 * beta : k), (-(7 / 432 * beta : k)),
      (7 / 36 * beta : k), (7 / 36 * beta : k), (7 / 72 * beta : k),
      (5 / 432 * delta : k), (5 / 36 * delta : k), (-(5 / 72 * delta : k)),
      (5 / 6 * delta : k), (2 / 3 * epsilon : k), (1 / 24 * zeta : k),
      (1 / 2 * zeta : k), (1 / 3 * eta : k), (1 / 6 * theta : k)]
      [
      [0, 2, 0, 1, 0], [0, 1, 2, 0, 0], [0, 0, 0, 1, 1], [5, 0, 0, 0, 0],
      [3, 0, 1, 0, 0], [2, 2, 0, 0, 0], [2, 0, 0, 0, 1], [1, 1, 0, 1, 0],
      [1, 0, 2, 0, 0], [0, 2, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 2, 0],
      [0, 3, 0, 0, 0], [0, 1, 0, 0, 1], [0, 0, 1, 1, 0], [4, 0, 0, 0, 0],
      [2, 0, 1, 0, 0], [1, 2, 0, 0, 0], [1, 0, 0, 0, 1], [0, 1, 0, 1, 0],
      [0, 0, 2, 0, 0], [3, 0, 0, 0, 0], [1, 0, 1, 0, 0], [0, 2, 0, 0, 0],
      [0, 0, 0, 0, 1], [0, 0, 0, 1, 0], [2, 0, 0, 0, 0], [0, 0, 1, 0, 0],
      [0, 1, 0, 0, 0], [1, 0, 0, 0, 0]] := by
  unfold degreeZeroKappaCubicNoSigmaBE610
  simp only [Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc,
    sub_eq_add_neg, neg_smul, add_assoc]

set_option maxHeartbeats 64000000 in
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
  rw [round4_astra4p_part66_polyOf]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

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

end CubicSigmaKills610

end Max11DegreeRoutes
