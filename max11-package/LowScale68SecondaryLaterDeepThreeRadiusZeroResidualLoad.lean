import LowScale68SecondaryLaterDeepThreeRadiusZeroResidualAlgebra

/-! # Primitive load data on the zero residual leaf `2g = 3n` -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepThreeRadiusZeroResidualLoad68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def threeRadiusZeroResidualD68 (A B : k[X]) : k[X] :=
  (1 / 3 : k) • (A * B)

def threeRadiusZeroResidualUr68
    (gamma delta zeta : k) (A B c : k[X]) : k[X] :=
  cubicLoadUAlphaRestPolynomial68 0 gamma delta zeta A B c

def threeRadiusZeroResidualVr68
    (alpha gamma delta epsilon eta : k) (A B c : k[X]) : k[X] :=
  cubicLoadVAlphaRestPolynomial68 alpha 0 gamma delta epsilon eta
    A B c (threeRadiusZeroResidualD68 A B) 0

def threeRadiusZeroResidualVlow68
    (gamma delta epsilon eta : k) (A B c : k[X]) : k[X] :=
  cubicLoadVAlphaLowPolynomial68 0 gamma delta epsilon eta
    A B c (threeRadiusZeroResidualD68 A B)

def threeRadiusZeroResidualC0c68 (A : k[X]) : k[X] :=
  (1 / 3 : k) • A ^ 2

def threeRadiusZeroResidualEr68 (A c : k[X]) : k[X] :=
  (1 / 3 : k) • (A * c)

def threeRadiusZeroResidualE68 (A c : k[X]) : k[X] :=
  (1 / 27 : k) • A ^ 3 + threeRadiusZeroResidualEr68 A c

def threeRadiusZeroResidualLoadRowOne68
    (alpha gamma delta epsilon zeta eta : k) (A B c : k[X]) : k[X] :=
  cubicLoadRowOneDeepGapRestPolynomial68 alpha 0 gamma delta epsilon
    zeta eta A B c (threeRadiusZeroResidualD68 A B) 0

set_option maxHeartbeats 4000000 in
theorem cubicLoadRowOnePolynomial68_eq_threeRadiusZeroResidualLoad
    (alpha gamma delta epsilon zeta eta : k) (A B c : k[X]) :
    cubicLoadRowOnePolynomial68 0 alpha 0 gamma delta epsilon zeta eta
        A B c (threeRadiusZeroResidualD68 A B) 0 =
      threeRadiusZeroResidualLoadRowOne68
        alpha gamma delta epsilon zeta eta A B c := by
  rw [cubicLoadRowOnePolynomial68_eq_alphaRest 0 alpha 0 gamma delta
      epsilon zeta eta A B c (threeRadiusZeroResidualD68 A B) 0 rfl,
    cubicLoadRowOneAlphaRestPolynomial68_eq_deepGapRest']
  rfl

theorem threeRadiusZeroResidualD68_degree_le
    (A B : k[X]) (n g : ℕ) (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree < 3 * n - g) :
    (threeRadiusZeroResidualD68 A B).natDegree ≤ 5 * n - g := by
  simp only [threeRadiusZeroResidualD68]
  compute_degree
  omega

theorem threeRadiusZeroResidualUr68_degree_le
    (gamma delta zeta : k) (A B c : k[X]) (n g : ℕ)
    (hwall : 2 * g = 3 * n) (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree < 3 * n - g) :
    (threeRadiusZeroResidualUr68 gamma delta zeta A B c).natDegree ≤
      2 * n := by
  simp only [threeRadiusZeroResidualUr68,
    cubicLoadUAlphaRestPolynomial68, zero_mul, mul_zero, zero_smul, add_zero]
  compute_degree
  omega

theorem threeRadiusZeroResidualVr68_degree_le
    (alpha gamma delta epsilon eta : k) (A B c : k[X]) (n g : ℕ)
    (hn : 0 < n) (hwall : 2 * g = 3 * n)
    (hA : A.natDegree ≤ 2 * n) (hB : B.natDegree < 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g) :
    (threeRadiusZeroResidualVr68 alpha gamma delta epsilon eta A B c).natDegree
      ≤ 6 * n - g := by
  simp only [threeRadiusZeroResidualVr68,
    cubicLoadVAlphaRestPolynomial68, zero_mul, mul_zero, zero_smul,
    smul_zero, add_zero, sub_zero]
  compute_degree
  omega

theorem threeRadiusZeroResidualVlow68_degree_le
    (gamma delta epsilon eta : k) (A B c : k[X]) (n g : ℕ)
    (hn : 0 < n) (hwall : 2 * g = 3 * n)
    (hA : A.natDegree ≤ 2 * n) (hB : B.natDegree < 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g) :
    (threeRadiusZeroResidualVlow68 gamma delta epsilon eta A B c).natDegree
      ≤ 4 * n - g := by
  simp only [threeRadiusZeroResidualVlow68,
    cubicLoadVAlphaLowPolynomial68, zero_mul, mul_zero, zero_smul, add_zero]
  compute_degree
  omega

theorem threeRadiusZeroResidualC0c68_degree_le
    (A : k[X]) (n : ℕ) (hA : A.natDegree ≤ 2 * n) :
    (threeRadiusZeroResidualC0c68 A).natDegree ≤ 4 * n := by
  simp only [threeRadiusZeroResidualC0c68]
  compute_degree
  omega

theorem threeRadiusZeroResidualEr68_degree_le
    (A c : k[X]) (n g : ℕ) (hn : 0 < n) (hwall : 2 * g = 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hc : c.natDegree ≤ 4 * n - g) :
    (threeRadiusZeroResidualEr68 A c).natDegree ≤ 6 * n - g := by
  simp only [threeRadiusZeroResidualEr68]
  compute_degree
  omega

theorem threeRadiusZeroResidualE68_degree_le
    (A c : k[X]) (n g : ℕ) (hA : A.natDegree ≤ 2 * n)
    (hc : c.natDegree ≤ 4 * n - g) :
    (threeRadiusZeroResidualE68 A c).natDegree ≤ 6 * n := by
  simp only [threeRadiusZeroResidualE68, threeRadiusZeroResidualEr68]
  compute_degree
  omega

#print axioms cubicLoadRowOnePolynomial68_eq_threeRadiusZeroResidualLoad
#print axioms threeRadiusZeroResidualD68_degree_le
#print axioms threeRadiusZeroResidualUr68_degree_le
#print axioms threeRadiusZeroResidualVr68_degree_le
#print axioms threeRadiusZeroResidualVlow68_degree_le
#print axioms threeRadiusZeroResidualC0c68_degree_le
#print axioms threeRadiusZeroResidualEr68_degree_le
#print axioms threeRadiusZeroResidualE68_degree_le

end LaterDeepThreeRadiusZeroResidualLoad68

end Max11DegreeRoutes
