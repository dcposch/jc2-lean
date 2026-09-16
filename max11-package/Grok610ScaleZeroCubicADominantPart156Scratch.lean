import Max11SpeedReflectDegLibScratch
import Grok610ScaleZeroCubicADominantPart153Scratch
import Grok610ScaleZeroCubicADominantPart154Scratch
import Grok610ScaleZeroCubicADominantPart155Scratch

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

set_option maxHeartbeats 64000000 in
/-- Reflect the unchanged polynomial literal into coefficient/exponent data. -/
private theorem round4_astra4p_part127_polyOf
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroLambdaCubicNoSigmaBCDE610 l alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (5 / 243 : k), (-(5 / 27 : k)), (-(10 / 27 : k)),
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
      [0, 4, 0, 0, 0], [0, 2, 0, 0, 1], [0, 1, 1, 1, 0], [4, 1, 0, 0, 0],
      [3, 0, 0, 1, 0], [2, 1, 1, 0, 0], [1, 3, 0, 0, 0], [1, 1, 0, 0, 1],
      [1, 0, 1, 1, 0], [0, 2, 0, 1, 0], [0, 1, 2, 0, 0], [0, 0, 0, 1, 1],
      [1, 1, 0, 1, 0], [0, 2, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 2, 0],
      [3, 1, 0, 0, 0], [2, 0, 0, 1, 0], [1, 1, 1, 0, 0], [0, 3, 0, 0, 0],
      [0, 1, 0, 0, 1], [0, 0, 1, 1, 0], [2, 1, 0, 0, 0], [1, 0, 0, 1, 0],
      [0, 1, 1, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 1], [1, 1, 0, 0, 0],
      [0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0]] := by
  unfold degreeZeroLambdaCubicNoSigmaBCDE610
  simp only [Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc,
    sub_eq_add_neg, neg_smul, add_assoc]

set_option maxHeartbeats 64000000 in
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
  rw [round4_astra4p_part127_polyOf]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

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
theorem degreeZeroOmicronCubic610_eq_sigmaBCDE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      omicronCubicSigmaFaceBCDE610 A B C D E +
        degreeZeroOmicronCubicNoSigmaBCDE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroOmicronCubic610, omicronCubicSigmaFaceBCDE610, degreeZeroOmicronCubicNoSigmaBCDE610]
  all_goals module

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

set_option maxHeartbeats 64000000 in
/-- Reflect the unchanged polynomial literal into coefficient/exponent data. -/
private theorem round4_astra4f_part131_polyOf
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroOmicronCubicNoSigmaBCDE610 l alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (-(5 / 486 : k)), (25 / 486 : k), (5 / 54 : k),
      (-(5 / 27 : k)), (-(5 / 27 : k)), (-(5 / 6912 * l : k)),
      (1 / 864 * l : k), (-(1 / 288 * l : k)), (-(1 / 96 * l : k)),
      (7 / 96 * l : k), (1 / 24 * l : k), (1 / 16 * l : k),
      (-(1 / 8 * l : k)), (-(1 / 4 * l : k)), (-(1 / 8 * l : k)),
      (-(3 / 16 * l : k)), (4 / 81 * alpha : k), (1 / 81 * alpha : k),
      (-(2 / 27 * alpha : k)), (-(2 / 27 * alpha : k)), (-(2 / 9 * alpha : k)),
      (-(4 / 81 * alpha : k)), (2 / 9 * alpha : k), (-(7 / 2592 * beta : k)),
      (7 / 1296 * beta : k), (7 / 648 * beta : k), (-(7 / 216 * beta : k)),
      (-(7 / 144 * beta : k)), (-(7 / 108 * beta : k)), (7 / 36 * beta : k),
      (-(5 / 432 * delta : k)), (5 / 108 * delta : k), (5 / 324 * delta : k),
      (-(5 / 36 * delta : k)), (1 / 27 * epsilon : k), (-(1 / 9 * epsilon : k)),
      (-(1 / 9 * epsilon : k)), (-(1 / 12 * zeta : k)), (-(1 / 6 * zeta : k)),
      (-(1 / 18 * eta : k)), (1 / 3 * eta : k), (1 / 6 * theta : k)]
      [
      [1, 4, 0, 0, 0], [0, 3, 0, 1, 0], [0, 2, 2, 0, 0], [0, 1, 0, 1, 1],
      [0, 0, 1, 2, 0], [4, 0, 0, 1, 0], [3, 1, 1, 0, 0], [2, 3, 0, 0, 0],
      [2, 0, 1, 1, 0], [1, 2, 0, 1, 0], [1, 1, 2, 0, 0], [0, 3, 1, 0, 0],
      [1, 0, 0, 1, 1], [0, 1, 1, 0, 1], [0, 1, 0, 2, 0], [0, 0, 2, 1, 0],
      [1, 2, 1, 0, 0], [0, 4, 0, 0, 0], [1, 0, 0, 2, 0], [0, 2, 0, 0, 1],
      [0, 1, 1, 1, 0], [0, 0, 3, 0, 0], [0, 0, 0, 0, 2], [3, 0, 0, 1, 0],
      [2, 1, 1, 0, 0], [1, 3, 0, 0, 0], [1, 0, 1, 1, 0], [0, 2, 0, 1, 0],
      [0, 1, 2, 0, 0], [0, 0, 0, 1, 1], [2, 0, 0, 1, 0], [1, 1, 1, 0, 0],
      [0, 3, 0, 0, 0], [0, 0, 1, 1, 0], [1, 2, 0, 0, 0], [0, 1, 0, 1, 0],
      [0, 0, 2, 0, 0], [1, 0, 0, 1, 0], [0, 1, 1, 0, 0], [0, 2, 0, 0, 0],
      [0, 0, 0, 0, 1], [0, 0, 0, 1, 0]] := by
  unfold degreeZeroOmicronCubicNoSigmaBCDE610
  simp only [Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc,
    sub_eq_add_neg, neg_smul, add_assoc]

set_option maxHeartbeats 64000000 in
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
  rw [round4_astra4f_part131_polyOf]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

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
theorem cubicSigmaInner_BCDE_identity (a b c d e : k) :
    ((1 / 324 : k) * a * b * c ^ 2 * e + (1 / 972 : k) * a * c ^ 3 * d + (1 / 162 : k) * a * d * e ^ 2) * kappaCubicSigmaInnerBCDE610 a b c d e +
      ((-1 / 324 : k) * a * b ^ 2 * c * e + (1 / 324 : k) * a * b * c ^ 2 * d + (1 / 9 : k) * e ^ 3) * lambdaCubicSigmaInnerBCDE610 a b c d e +
      ((-1 / 72 : k) * a * b * d * e + (1 / 216 : k) * a * c * d ^ 2 + (-1 / 27 : k) * c * e ^ 2) * omicronCubicSigmaInnerBCDE610 a b c d e +
      ((-1 / 243 : k) * a * b * c ^ 3 + (5 / 648 : k) * a * b * e ^ 2 + (1 / 72 : k) * a * c * d * e) * n1CubicSigmaInnerBCDE610 a b c d e =
      e ^ 5 := by
  simp only [kappaCubicSigmaInnerBCDE610, lambdaCubicSigmaInnerBCDE610,
    omicronCubicSigmaInnerBCDE610, n1CubicSigmaInnerBCDE610]
  ring

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

set_option maxHeartbeats 64000000 in
/-- Reflect the unchanged polynomial literal into coefficient/exponent data. -/
private theorem round4_astra4f_part146_polyOf
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroN1CubicNoL610 l alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (5 / 81 : k), (20 / 243 : k), (-(10 / 27 : k)),
      (-(5 / 27 : k)), (-(5 / 27 : k)), (35 / 6912 * l : k),
      (-(1 / 1152 * l : k)), (5 / 288 * l : k), (-(1 / 96 * l : k)),
      (1 / 64 * l : k), (1 / 32 * l : k), (3 / 128 * l : k),
      (1 / 8 * l : k), (-(1 / 16 * l : k)), (-(3 / 16 * l : k)),
      (-(3 / 8 * l : k)), (-(1 / 16 * l : k)), (3 / 8 * l : k),
      (4 / 243 * alpha : k), (-(4 / 27 * alpha : k)), (-(4 / 27 * alpha : k)),
      (4 / 9 * alpha : k), (7 / 6912 * beta : k), (35 / 2592 * beta : k),
      (-(7 / 5184 * beta : k)), (7 / 144 * beta : k), (-(7 / 216 * beta : k)),
      (7 / 432 * beta : k), (-(35 / 432 * beta : k)), (7 / 36 * beta : k),
      (7 / 72 * beta : k), (35 / 10368 * delta : k), (5 / 144 * delta : k),
      (5 / 432 * delta : k), (5 / 36 * delta : k), (-(5 / 36 * delta : k)),
      (-(5 / 72 * delta : k)), (-(2 / 9 * epsilon : k)), (5 / 432 * zeta : k),
      (1 / 12 * zeta : k), (-(1 / 8 * zeta : k)), (1 / 2 * zeta : k),
      (1 / 3 * eta : k), (1 / 24 * theta : k), (1 / 6 * theta : k)]
      [
      [1, 2, 0, 1, 0], [0, 3, 1, 0, 0], [0, 1, 1, 0, 1], [0, 1, 0, 2, 0],
      [0, 0, 2, 1, 0], [4, 0, 1, 0, 0], [3, 2, 0, 0, 0], [3, 0, 0, 0, 1],
      [2, 1, 0, 1, 0], [2, 0, 2, 0, 0], [1, 2, 1, 0, 0], [0, 4, 0, 0, 0],
      [1, 0, 1, 0, 1], [1, 0, 0, 2, 0], [0, 2, 0, 0, 1], [0, 1, 1, 1, 0],
      [0, 0, 3, 0, 0], [0, 0, 0, 0, 2], [1, 3, 0, 0, 0], [0, 2, 0, 1, 0],
      [0, 1, 2, 0, 0], [0, 0, 0, 1, 1], [5, 0, 0, 0, 0], [3, 0, 1, 0, 0],
      [2, 2, 0, 0, 0], [2, 0, 0, 0, 1], [1, 1, 0, 1, 0], [1, 0, 2, 0, 0],
      [0, 2, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 2, 0], [4, 0, 0, 0, 0],
      [2, 0, 1, 0, 0], [1, 2, 0, 0, 0], [1, 0, 0, 0, 1], [0, 1, 0, 1, 0],
      [0, 0, 2, 0, 0], [0, 1, 1, 0, 0], [3, 0, 0, 0, 0], [1, 0, 1, 0, 0],
      [0, 2, 0, 0, 0], [0, 0, 0, 0, 1], [0, 0, 0, 1, 0], [2, 0, 0, 0, 0],
      [0, 0, 1, 0, 0]] := by
  unfold degreeZeroN1CubicNoL610
  simp only [Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc,
    sub_eq_add_neg, neg_smul, add_assoc]

set_option maxHeartbeats 64000000 in
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
  rw [round4_astra4f_part146_polyOf]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

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

end CubicSigmaKills610

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

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

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

end CubicSigmaKills610

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

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

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

end CubicSigmaKills610

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

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

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

end Max11DegreeRoutes
