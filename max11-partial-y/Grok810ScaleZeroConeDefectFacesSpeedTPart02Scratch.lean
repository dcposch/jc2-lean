import Grok810ScaleZeroConeDefectFacesSpeedTPart01Scratch

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## Splittings -/

section DefectSplittings810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
theorem degreeZeroXiPolynomial810_eq_A7_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroXiPolynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0 =
      (-(165 / 65536 : k)) • A ^ 7 +
        degreeZeroXiNoA7Polynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0 := by
  simp only [degreeZeroXiPolynomial810, degreeZeroXiNoA7Polynomial810]
  simp only [neg_smul]
  abel

set_option maxHeartbeats 64000000 in
theorem degreeZeroXiPolynomial810_eq_F02_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroXiPolynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0 =
      (5 / 32 : k) • F0 ^ 2 +
        degreeZeroXiNoF02Polynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0 := by
  simp only [degreeZeroXiPolynomial810, degreeZeroXiNoF02Polynomial810]
  simp only [neg_smul]
  abel

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuPolynomial810_eq_B4_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0 =
      (35 / 2048 : k) • B ^ 4 +
        degreeZeroMuNoB4Polynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0 := by
  simp only [degreeZeroMuPolynomial810, degreeZeroMuNoB4Polynomial810]
  abel

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuPolynomial810_eq_C03_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0 =
      (-(5 / 128 : k)) • C0 ^ 3 +
        degreeZeroMuNoC03Polynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0 := by
  simp only [degreeZeroMuPolynomial810, degreeZeroMuNoC03Polynomial810]
  simp only [neg_smul]
  abel

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuPolynomial810_eq_E02_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0 =
      (5 / 32 : k) • E0 ^ 2 +
        degreeZeroMuNoE02Polynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0 := by
  simp only [degreeZeroMuPolynomial810, degreeZeroMuNoE02Polynomial810]
  abel

set_option maxHeartbeats 64000000 in
theorem degreeZeroOmicronPolynomial810_eq_B5_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroOmicronPolynomial810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0 =
      (-(21 / 4096 : k)) • B ^ 5 +
        degreeZeroOmicronNoB5Polynomial810 l beta gamma delta epsilon zeta
          eta theta A B C0 D0 E0 F0 G0 := by
  simp only [degreeZeroOmicronPolynomial810,
    degreeZeroOmicronNoB5Polynomial810]
  simp only [neg_smul]
  abel

set_option maxHeartbeats 64000000 in
theorem degreeZeroOmicronPolynomial810_eq_D03_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroOmicronPolynomial810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0 =
      (-(5 / 128 : k)) • D0 ^ 3 +
        degreeZeroOmicronNoD03Polynomial810 l beta gamma delta epsilon zeta
          eta theta A B C0 D0 E0 F0 G0 := by
  simp only [degreeZeroOmicronPolynomial810,
    degreeZeroOmicronNoD03Polynomial810]
  simp only [neg_smul]
  abel

end DefectSplittings810




end Max11DegreeRoutes
