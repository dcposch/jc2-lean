import Astra810ScaleZeroQuarticChamberBCDEFG12Part16Scratch

/-! # BCDEFG12 chamber, part 17

One piece of the `Astra810ScaleZeroQuarticChamberBCDEFG12Scratch` module, split out so each
compilation unit stays inside the runner memory budget.  Public statements
are byte-identical to the single-module version.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

set_option maxRecDepth 1000000

variable {k : Type*} [Field k] [CharZero k]


set_option maxHeartbeats 64000000 in
/-- Coefficient of the chamber face at its common monomial degree. -/
theorem bcdefg12Pi_face_coeff810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G) :
    (bcdefg12PiFace810 A B C D E F G).coeff (2 * G.natDegree) =
      (5 / 4096 : k) * piQuarticOpenIIFace810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  obtain ⟨hcone, hBne, hCne, hDne, hEne, hFne, hGne, heq0, heq1, heq2, heq3, heq4, heq5, heq6, heq7, heq8, heq9, hlt0, hlt1, hlt2, hlt3, hlt4, hlt5, hlt6, hlt7, hlt8, hlt9, hlt10, hlt11, hlt12⟩ := hc
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hcone
  have hAne : A ≠ 0 := by intro h; simp [h] at hApos
  have hd0 : (A ^ 2 * B ^ 4).natDegree = 2 * G.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 4 hBne), natDegree_pow] <;> (try simp only [natDegree_pow]) <;> omega
  have hm0 : (A ^ 2 * B ^ 4).coeff (2 * G.natDegree) = A.leadingCoeff ^ 2 * B.leadingCoeff ^ 4 := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : (A * B ^ 2 * C ^ 2).natDegree = 2 * G.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) (pow_ne_zero 2 hCne), natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow] <;> (try simp only [natDegree_pow]) <;> omega
  have hm1 : (A * B ^ 2 * C ^ 2).coeff (2 * G.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff ^ 2 := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : (A * B ^ 2 * G).natDegree = 2 * G.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hGne, natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow] <;> (try simp only [natDegree_pow]) <;> omega
  have hm2 : (A * B ^ 2 * G).coeff (2 * G.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 2 * G.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd3 : (A * B * C * F).natDegree = 2 * G.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hAne hBne) hCne) hFne, natDegree_mul (mul_ne_zero hAne hBne) hCne, natDegree_mul hAne hBne] <;> (try simp only [natDegree_pow]) <;> omega
  have hm3 : (A * B * C * F).coeff (2 * G.natDegree) = A.leadingCoeff * B.leadingCoeff * C.leadingCoeff * F.leadingCoeff := by
    rw [← hd3, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd4 : (A * B * D * E).natDegree = 2 * G.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hAne hBne) hDne) hEne, natDegree_mul (mul_ne_zero hAne hBne) hDne, natDegree_mul hAne hBne] <;> (try simp only [natDegree_pow]) <;> omega
  have hm4 : (A * B * D * E).coeff (2 * G.natDegree) = A.leadingCoeff * B.leadingCoeff * D.leadingCoeff * E.leadingCoeff := by
    rw [← hd4, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd5 : (A * C * D ^ 2).natDegree = 2 * G.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hCne) (pow_ne_zero 2 hDne), natDegree_mul hAne hCne, natDegree_pow] <;> (try simp only [natDegree_pow]) <;> omega
  have hm5 : (A * C * D ^ 2).coeff (2 * G.natDegree) = A.leadingCoeff * C.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hd5, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd6 : (A * F ^ 2).natDegree = 2 * G.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 2 hFne), natDegree_pow] <;> (try simp only [natDegree_pow]) <;> omega
  have hm6 : (A * F ^ 2).coeff (2 * G.natDegree) = A.leadingCoeff * F.leadingCoeff ^ 2 := by
    rw [← hd6, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd7 : (C ^ 4).natDegree = 2 * G.natDegree := by
    rw [natDegree_pow] <;> omega
  have hm7 : (C ^ 4).coeff (2 * G.natDegree) = C.leadingCoeff ^ 4 := by
    rw [← hd7, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd8 : (C ^ 2 * G).natDegree = 2 * G.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hGne, natDegree_pow] <;> (try simp only [natDegree_pow]) <;> omega
  have hm8 : (C ^ 2 * G).coeff (2 * G.natDegree) = C.leadingCoeff ^ 2 * G.leadingCoeff := by
    rw [← hd8, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd9 : (C * E ^ 2).natDegree = 2 * G.natDegree := by
    rw [natDegree_mul hCne (pow_ne_zero 2 hEne), natDegree_pow] <;> (try simp only [natDegree_pow]) <;> omega
  have hm9 : (C * E ^ 2).coeff (2 * G.natDegree) = C.leadingCoeff * E.leadingCoeff ^ 2 := by
    rw [← hd9, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd10 : (G ^ 2).natDegree = 2 * G.natDegree := by
    rw [natDegree_pow] <;> omega
  have hm10 : (G ^ 2).coeff (2 * G.natDegree) = G.leadingCoeff ^ 2 := by
    rw [← hd10, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  simp only [bcdefg12PiFace810, coeff_add, coeff_smul, smul_eq_mul, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, piQuarticOpenIIFace810]
  ring

set_option maxHeartbeats 64000000 in
/-- The scalar chamber face vanishes, using the full constant-integral hypothesis. -/
theorem bcdefg12PiFace_zero810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hbl : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree)
    (hbbeta : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree)
    (hbdelta : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree)
    (hbzeta : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree)
    (hbtheta : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree)
    (hz : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0) :
    piQuarticOpenIIFace810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
  have hr := bcdefg12Pi_rest_lt810 l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbl hbbeta hbdelta hbzeta hbtheta
  have ht := bcdefg12Pi_face_coeff810 A B C D E F G hc
  have hd : 0 < 2 * G.natDegree := by
    obtain ⟨hcone, hBne, hCne, hDne, hEne, hFne, hGne, heq0, heq1, heq2, heq3, heq4, heq5, heq6, heq7, heq8, heq9, hlt0, hlt1, hlt2, hlt3, hlt4, hlt5, hlt6, hlt7, hlt8, hlt9, hlt10, hlt11, hlt12⟩ := hc
    obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hcone
    omega
  have hh := coeff_eq_zero_of_natDegree_lt (show (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree by omega)
  rw [bcdefg12Pi_split810, coeff_add, coeff_eq_zero_of_natDegree_lt hr, add_zero, ht] at hh
  exact (mul_eq_zero.mp hh).resolve_left (by norm_num)

end Max11DegreeRoutes
