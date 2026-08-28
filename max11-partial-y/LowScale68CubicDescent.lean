import LowScale68Expansion

/-! # First descent below the `(6,8)` cubic boundary

The maximal expanded boundary is the triple-root sextic
`(y^2 + A/3)^3`.  The four transverse coordinates are therefore `B`, `D`,
and the two translated even coefficients below.  This module proves that all
four have degree strictly below their old weighted bounds, while `A` attains
its bound.  These strict inequalities are the input to the next Newton face.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section CubicDescent68

variable {k : Type*} [Field k] [CharZero k]

section FieldIdentities68

variable {F : Type*} [Field F] [CharZero F]

/-- Compact form of the first exact invariant after translating away the
cubic core. -/
def cubicFirstIntegralFour68
    (L beta gamma delta epsilon zeta A B c D e : F) : F :=
  (-8 / 27 : F) * B ^ 3 - (8 / 9 : F) * A * B * c +
    (8 / 3 : F) * B * e + (8 / 3 : F) * D * c + zeta * A +
    2 * epsilon * B + delta * ((1 / 4 : F) * A ^ 2 + 3 * c) +
    gamma * (4 * D - (4 / 3 : F) * A * B) +
    beta * (5 * e + (5 / 6 : F) * A * c - (5 / 12 : F) * B ^ 2 +
      (5 / 72 : F) * A ^ 3) +
    L * ((35 / 1728 : F) * A ^ 4 + (7 / 24 : F) * A ^ 2 * c -
      (35 / 72 : F) * A * B ^ 2 + (7 / 6 : F) * A * e +
      (7 / 6 : F) * B * D + (7 / 12 : F) * c ^ 2)

/-- Compact form of the second exact invariant in the same coordinates. -/
def cubicFirstIntegralThree68
    (L beta gamma delta epsilon zeta A B c D e : F) : F :=
  (4 / 9 : F) * (A ^ 2 * B ^ 2 - 4 * A * B * D -
      2 * B ^ 2 * c + 3 * D ^ 2 + 6 * c * e) +
    zeta * B + 2 * epsilon * c + gamma * (4 * e - (2 / 3 : F) * B ^ 2) +
    delta * (3 * D - (3 / 2 : F) * A * B) +
    beta * ((5 / 24 : F) * A ^ 2 * B - (5 / 6 : F) * A * D -
      (5 / 6 : F) * B * c) +
    L * ((7 / 432 : F) * A ^ 3 * B - (7 / 72 : F) * A ^ 2 * D -
      (7 / 12 : F) * A * B * c - (35 / 216 : F) * B ^ 3 +
      (7 / 6 : F) * B * e + (7 / 6 : F) * D * c)

set_option maxHeartbeats 1000000 in
theorem firstIntegralFour68_cubicCoordinates
    (L beta gamma delta epsilon zeta A B c D e : F) :
    firstIntegralFour68 L A B (A ^ 2 / 3 + c) D
      (A ^ 3 / 27 + A * c / 3 + e) beta gamma delta epsilon zeta =
        cubicFirstIntegralFour68 L beta gamma delta epsilon zeta A B c D e := by
  simp only [firstIntegralFour68, cubicFirstIntegralFour68]
  ring

set_option maxHeartbeats 1000000 in
theorem firstIntegralThree68_cubicCoordinates
    (L beta gamma delta epsilon zeta A B c D e : F) :
    firstIntegralThree68 L A B (A ^ 2 / 3 + c) D
      (A ^ 3 / 27 + A * c / 3 + e) beta gamma delta epsilon zeta =
        cubicFirstIntegralThree68 L beta gamma delta epsilon zeta A B c D e := by
  simp only [firstIntegralThree68, cubicFirstIntegralThree68]
  ring

end FieldIdentities68

/-- The coefficient of `w` after translating the even cubic by
`w = y^2 + A/3`. -/
def cubicCDefectPolynomial68 (A C0 : k[X]) : k[X] :=
  C0 - (1 / 3 : k) • A ^ 2

/-- The constant coefficient after the same translation. -/
def cubicEDefectPolynomial68 (A C0 E : k[X]) : k[X] :=
  E - (1 / 3 : k) • (A * C0) + (2 / 27 : k) • A ^ 3

theorem cubicCDefectPolynomial68_reconstruct (A C0 : k[X]) :
    C0 = (1 / 3 : k) • A ^ 2 + cubicCDefectPolynomial68 A C0 := by
  simp only [cubicCDefectPolynomial68]
  abel

theorem cubicEDefectPolynomial68_reconstruct (A C0 E : k[X]) :
    E = (1 / 3 : k) • (A * C0) - (2 / 27 : k) • A ^ 3 +
      cubicEDefectPolynomial68 A C0 E := by
  simp only [cubicEDefectPolynomial68]
  abel

set_option maxHeartbeats 1000000 in
/-- On the exact cubic core, the first invariant becomes a quartic polynomial
in the sole remaining load `A`. -/
theorem firstIntegralFourPolynomial68_exactCubic
    (l beta gamma delta epsilon zeta : k) (A : k[X]) :
    firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta A 0
      ((1 / 3 : k) • A ^ 2) 0 ((1 / 27 : k) • A ^ 3) =
      zeta • A + (1 / 4 * delta : k) • A ^ 2 +
        (5 / 72 * beta : k) • A ^ 3 + (35 / 1728 * l : k) • A ^ 4 := by
  have hA3 : A * A ^ 2 = A ^ 3 := by ring
  have hA4a : (A ^ 2) ^ 2 = A ^ 4 := by ring
  have hA4b : A ^ 2 * A ^ 2 = A ^ 4 := by ring
  have hA4c : A * A ^ 3 = A ^ 4 := by ring
  simp only [firstIntegralFourPolynomial68, zero_mul, mul_zero, smul_zero,
    add_zero, sub_zero]
  simp only [mul_smul_comm, smul_smul, _root_.smul_pow]
  simp only [hA3, hA4a, hA4b, hA4c]
  norm_num
  module

set_option maxHeartbeats 1000000 in
/-- The integrated octic linear coefficient on the exact cubic core. -/
theorem integratedUPolynomial68_exactCubic
    (l alpha beta gamma delta zeta : k) (A : k[X]) :
    integratedUPolynomial68 l alpha beta gamma delta zeta A 0
      ((1 / 3 : k) • A ^ 2) 0 ((1 / 27 : k) • A ^ 3) =
      C zeta + ((1 / 2 * delta : k) • A +
        (5 / 24 * beta : k) • A ^ 2 + (35 / 432 * l : k) • A ^ 3) := by
  have hA3 : A * A ^ 2 = A ^ 3 := by ring
  simp only [integratedUPolynomial68, zero_mul, mul_zero, smul_zero, add_zero,
    zero_add, sub_zero, mul_smul_comm, smul_smul, hA3]
  norm_num
  module

set_option maxHeartbeats 2000000 in
/-- The lower system cannot remain exactly on the cubic-core locus: its first
invariant forces all four coefficients of `U` to vanish, contradicting the
nonzero terminal one-form. -/
theorem exactCubicIntegratedPolynomialLowerSystem_impossible68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X])
    (hterminal : terminal ≠ 0)
    (hApos : 0 < A.natDegree)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hB : B = 0) (hC : C0 = (1 / 3 : k) • A ^ 2)
    (hD : D = 0) (hE : E = (1 / 27 : k) • A ^ 3) : False := by
  obtain ⟨i4, hi4⟩ := hsys.firstFour
  rw [hB, hC, hD, hE, firstIntegralFourPolynomial68_exactCubic] at hi4
  let g : k[X] := C zeta * X + C (1 / 4 * delta) * X ^ 2 +
    C (5 / 72 * beta) * X ^ 3 + C (35 / 1728 * l) * X ^ 4 - C i4
  have hAne : A ≠ 0 := by
    intro hAzero
    simp [hAzero] at hApos
  have htrans : Transcendental k A := by
    apply Polynomial.transcendental A (Nat.ne_of_gt hApos)
    exact mem_nonZeroDivisors_iff_ne_zero.mpr
      (leadingCoeff_ne_zero.mpr hAne)
  have hgeval : Polynomial.aeval A g = 0 := by
    simp only [g, map_sub, map_add, map_mul, map_pow, aeval_def,
      eval₂_C, eval₂_X]
    simpa [Polynomial.smul_eq_C_mul] using sub_eq_zero.mpr hi4
  have hg : g = 0 := by
    apply (transcendental_iff_injective.mp htrans)
    simpa using hgeval
  have hl0 : l = 0 := by
    have h := congrArg (fun p : k[X] => p.coeff 4) hg
    simp only [g, coeff_sub, coeff_add, coeff_C_mul_X_pow, coeff_C] at h
    norm_num at h
    exact h
  have hbeta0 : beta = 0 := by
    have h := congrArg (fun p : k[X] => p.coeff 3) hg
    simp only [g, coeff_sub, coeff_add, coeff_C_mul_X_pow, coeff_C] at h
    norm_num at h
    exact h
  have hdelta0 : delta = 0 := by
    have h := congrArg (fun p : k[X] => p.coeff 2) hg
    simp only [g, coeff_sub, coeff_add, coeff_C_mul_X_pow, coeff_C] at h
    norm_num at h
    exact h
  have hzeta0 : zeta = 0 := by
    have h := congrArg (fun p : k[X] => p.coeff 1) hg
    simp only [g, coeff_sub, coeff_add, coeff_C_mul_X_pow, coeff_C] at h
    norm_num at h
    exact h
  have hU : integratedUPolynomial68 l alpha beta gamma delta zeta
      A B C0 D E = 0 := by
    rw [hB, hC, hD, hE, integratedUPolynomial68_exactCubic,
      hl0, hbeta0, hdelta0, hzeta0]
    simp
  have hrow := hsys.rowZero
  rw [hU, hD] at hrow
  simp only [lowerRowZeroPolynomial68, zero_mul, sub_zero] at hrow
  have hterminal0 : terminal = 0 := C_injective (by simpa using hrow.symm)
  exact hterminal hterminal0

set_option maxHeartbeats 1000000 in
/-- A nontrivial cubic-core boundary removes the old top coefficient from all
four transverse coordinates.  In particular `A` is the unique coordinate
that still attains its original weighted bound. -/
theorem cubicCoreBoundary_degreeDrop68
    (A B C0 D E : k[X]) (n : ℕ) (hn : 0 < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n)
    (hC : C0.natDegree ≤ 4 * n)
    (hD : D.natDegree ≤ 5 * n)
    (hE : E.natDegree ≤ 6 * n)
    (hBtop : B.coeff (3 * n) = 0)
    (hDtop : D.coeff (5 * n) = 0)
    (hCtop : C0.coeff (4 * n) = A.coeff (2 * n) ^ 2 / 3)
    (hEtop : E.coeff (6 * n) = A.coeff (2 * n) ^ 3 / 27)
    (hAtop : A.coeff (2 * n) ≠ 0) :
    A.natDegree = 2 * n ∧
    B.natDegree < 3 * n ∧
    (cubicCDefectPolynomial68 A C0).natDegree < 4 * n ∧
    D.natDegree < 5 * n ∧
    (cubicEDefectPolynomial68 A C0 E).natDegree < 6 * n := by
  have hAeq : A.natDegree = 2 * n :=
    natDegree_eq_of_le_of_coeff_ne_zero hA hAtop
  have hBlt : B.natDegree < 3 * n := by
    have hp := natDegree_le_pred hB hBtop
    omega
  have hDlt : D.natDegree < 5 * n := by
    have hp := natDegree_le_pred hD hDtop
    omega
  have hA2 := coeff_pow_weightedBoundary68 A 2 2 n hA
  have hCdefDegree : (cubicCDefectPolynomial68 A C0).natDegree ≤ 4 * n := by
    simp only [cubicCDefectPolynomial68]
    compute_degree
    omega
  have hCdefCoeff :
      (cubicCDefectPolynomial68 A C0).coeff (4 * n) = 0 := by
    simp only [cubicCDefectPolynomial68, coeff_sub, coeff_smul, smul_eq_mul]
    rw [hCtop, hA2]
    ring
  have hClt : (cubicCDefectPolynomial68 A C0).natDegree < 4 * n := by
    have hp := natDegree_le_pred hCdefDegree hCdefCoeff
    omega
  have hAC := coeff_mul_weightedBoundary68 A C0 2 4 n hA hC
  have hA3 := coeff_pow_weightedBoundary68 A 2 3 n hA
  have hEdefDegree :
      (cubicEDefectPolynomial68 A C0 E).natDegree ≤ 6 * n := by
    simp only [cubicEDefectPolynomial68]
    compute_degree
    omega
  have hEdefCoeff :
      (cubicEDefectPolynomial68 A C0 E).coeff (6 * n) = 0 := by
    simp only [cubicEDefectPolynomial68, coeff_add, coeff_sub, coeff_smul,
      smul_eq_mul]
    rw [hEtop, hAC, hA3, hCtop]
    ring
  have hElt : (cubicEDefectPolynomial68 A C0 E).natDegree < 6 * n := by
    have hp := natDegree_le_pred hEdefDegree hEdefCoeff
    omega
  exact ⟨hAeq, hBlt, hClt, hDlt, hElt⟩

set_option maxHeartbeats 2000000 in
/-- Apply the strict cubic-core degree drop at the canonical maximal expansion
of an exact polynomial lower system. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_degreeDrop68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E) :
    let n := weightedRadius68 A B C0 D E
    let Ae := expand k 60 A
    let Be := expand k 60 B
    let Ce := expand k 60 C0
    let De := expand k 60 D
    let Ee := expand k 60 E
    Ae.natDegree = 2 * n ∧
    Be.natDegree < 3 * n ∧
    (cubicCDefectPolynomial68 Ae Ce).natDegree < 4 * n ∧
    De.natDegree < 5 * n ∧
    (cubicEDefectPolynomial68 Ae Ce Ee).natDegree < 6 * n := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let De := expand k 60 D
  let Ee := expand k 60 E
  have hcore := maximalExpandedIntegratedPolynomialLowerSystem_cubicCore68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have hbounds := weightedRadius68_degreeBounds A B C0 D E
  exact cubicCoreBoundary_degreeDrop68 Ae Be Ce De Ee n hcore.1
    hbounds.1 hbounds.2.1 hbounds.2.2.1 hbounds.2.2.2.1
    hbounds.2.2.2.2 hcore.2.1 hcore.2.2.1 hcore.2.2.2.1
    hcore.2.2.2.2.1 hcore.2.2.2.2.2

end CubicDescent68

#print axioms cubicCDefectPolynomial68_reconstruct
#print axioms cubicEDefectPolynomial68_reconstruct
#print axioms firstIntegralFour68_cubicCoordinates
#print axioms firstIntegralThree68_cubicCoordinates
#print axioms firstIntegralFourPolynomial68_exactCubic
#print axioms integratedUPolynomial68_exactCubic
#print axioms exactCubicIntegratedPolynomialLowerSystem_impossible68
#print axioms cubicCoreBoundary_degreeDrop68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_degreeDrop68

end Max11DegreeRoutes
