import Astra810ScaleZeroQuarticChamberBCDEFG12Part05Scratch
import Astra810ScaleZeroQuarticChamberBCDEFG12Part08Scratch
import Astra810ScaleZeroQuarticChamberBCDEFG12Part11Scratch
import Astra810ScaleZeroQuarticChamberBCDEFG12Part14Scratch
import Astra810ScaleZeroQuarticChamberBCDEFG12Part17Scratch
import Astra810ScaleZeroQuarticChamberBCDEFG12Part21Scratch
import Astra810ScaleZeroQuarticChamberBCDEFG12Part26Scratch

/-! # BCDEFG12 chamber, part 27

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
/-- Coefficient of the homogeneous polynomial face. -/
theorem bcdefg12N6Face_coeff
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G) :
    (bcdefg12N6Face A B C D E F G).coeff (2 * A.natDegree + 3 * B.natDegree + C.natDegree) =
      (5 / 12288 : k) * A.leadingCoeff * n6QuarticOpenIIFace810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  have hA : A ≠ 0 := by intro hz; simp [hz] at hApos
  have hd0 : (A ^ 2 * B ^ 3 * C).natDegree = 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hA) (pow_ne_zero 3 hB)) hC, natDegree_mul (pow_ne_zero 2 hA) (pow_ne_zero 3 hB)] <;> (try simp only [natDegree_pow]) <;> omega
  have hcf0 : (A ^ 2 * B ^ 3 * C).coeff (2 * A.natDegree + 3 * B.natDegree + C.natDegree) = A.leadingCoeff ^ 2 * B.leadingCoeff ^ 3 * C.leadingCoeff := by
    rw [← hd0, coeff_natDegree] <;> simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : (A ^ 2 * B ^ 2 * F).natDegree = 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hA) (pow_ne_zero 2 hB)) hF, natDegree_mul (pow_ne_zero 2 hA) (pow_ne_zero 2 hB)] <;> (try simp only [natDegree_pow]) <;> omega
  have hcf1 : (A ^ 2 * B ^ 2 * F).coeff (2 * A.natDegree + 3 * B.natDegree + C.natDegree) = A.leadingCoeff ^ 2 * B.leadingCoeff ^ 2 * F.leadingCoeff := by
    rw [← hd1, coeff_natDegree] <;> simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : (A ^ 2 * B * D ^ 2).natDegree = 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hA) hB) (pow_ne_zero 2 hD), natDegree_mul (pow_ne_zero 2 hA) hB] <;> (try simp only [natDegree_pow]) <;> omega
  have hcf2 : (A ^ 2 * B * D ^ 2).coeff (2 * A.natDegree + 3 * B.natDegree + C.natDegree) = A.leadingCoeff ^ 2 * B.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hd2, coeff_natDegree] <;> simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd3 : (A * B * C ^ 3).natDegree = 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hA hB) (pow_ne_zero 3 hC), natDegree_mul hA hB] <;> (try simp only [natDegree_pow]) <;> omega
  have hcf3 : (A * B * C ^ 3).coeff (2 * A.natDegree + 3 * B.natDegree + C.natDegree) = A.leadingCoeff * B.leadingCoeff * C.leadingCoeff ^ 3 := by
    rw [← hd3, coeff_natDegree] <;> simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd4 : (A * B * C * G).natDegree = 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hA hB) hC) hG, natDegree_mul (mul_ne_zero hA hB) hC, natDegree_mul hA hB] <;> (try simp only [natDegree_pow]) <;> omega
  have hcf4 : (A * B * C * G).coeff (2 * A.natDegree + 3 * B.natDegree + C.natDegree) = A.leadingCoeff * B.leadingCoeff * C.leadingCoeff * G.leadingCoeff := by
    rw [← hd4, coeff_natDegree] <;> simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd5 : (A * B * E ^ 2).natDegree = 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hA hB) (pow_ne_zero 2 hE), natDegree_mul hA hB] <;> (try simp only [natDegree_pow]) <;> omega
  have hcf5 : (A * B * E ^ 2).coeff (2 * A.natDegree + 3 * B.natDegree + C.natDegree) = A.leadingCoeff * B.leadingCoeff * E.leadingCoeff ^ 2 := by
    rw [← hd5, coeff_natDegree] <;> simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd6 : (A * C * D * E).natDegree = 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hA hC) hD) hE, natDegree_mul (mul_ne_zero hA hC) hD, natDegree_mul hA hC] <;> (try simp only [natDegree_pow]) <;> omega
  have hcf6 : (A * C * D * E).coeff (2 * A.natDegree + 3 * B.natDegree + C.natDegree) = A.leadingCoeff * C.leadingCoeff * D.leadingCoeff * E.leadingCoeff := by
    rw [← hd6, coeff_natDegree] <;> simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd7 : (A * F * G).natDegree = 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hA hF) hG, natDegree_mul hA hF] <;> (try simp only [natDegree_pow]) <;> omega
  have hcf7 : (A * F * G).coeff (2 * A.natDegree + 3 * B.natDegree + C.natDegree) = A.leadingCoeff * F.leadingCoeff * G.leadingCoeff := by
    rw [← hd7, coeff_natDegree] <;> simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd8 : (A * C ^ 2 * F).natDegree = 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hA (pow_ne_zero 2 hC)) hF, natDegree_mul hA (pow_ne_zero 2 hC)] <;> (try simp only [natDegree_pow]) <;> omega
  have hcf8 : (A * C ^ 2 * F).coeff (2 * A.natDegree + 3 * B.natDegree + C.natDegree) = A.leadingCoeff * C.leadingCoeff ^ 2 * F.leadingCoeff := by
    rw [← hd8, coeff_natDegree] <;> simp only [leadingCoeff_mul, leadingCoeff_pow]
  simp only [bcdefg12N6Face, n6QuarticOpenIIFace810, coeff_add, coeff_smul, smul_eq_mul, hcf0, hcf1, hcf2, hcf3, hcf4, hcf5, hcf6, hcf7, hcf8]
  ring

set_option maxHeartbeats 64000000 in
/-- Vanishing of the scalar N6 face under the strict load bands. -/
theorem bcdefg12N6Face_zero
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hbL : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree)
    (hbBeta : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree)
    (hbDelta : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree)
    (hbZeta : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree)
    (hbTheta : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree)
    (hprim : (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 1)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0) :
    n6QuarticOpenIIFace810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
  have hrest := bcdefg12N6Rest_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbL hbBeta hbDelta hbZeta hbTheta
  have hface := bcdefg12N6Face_coeff A B C D E F G hc
  have hApos := hc.1.1
  have hcarrier := degreeZeroN6TowerQuartic810_natDegree_le l beta gamma delta epsilon zeta eta theta A B C D E F G hApos hprim homi hnu
  have htop : 2 * A.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
    rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
    have hApos := hcone.1
    omega
  have hz := coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hcarrier htop)
  rw [bcdefg12N6_split, coeff_add, coeff_eq_zero_of_natDegree_lt hrest, add_zero, hface] at hz
  have hA : A ≠ 0 := by intro hz; simp [hz] at hApos
  exact (mul_eq_zero.mp hz).resolve_left
    (mul_ne_zero (by norm_num : (5 / 12288 : k) ≠ 0) (leadingCoeff_ne_zero.mpr hA))

end Max11DegreeRoutes
