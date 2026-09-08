import Astra810ScaleZeroQuarticChamberBCDEFG12Part20Scratch

/-! # BCDEFG12 chamber, part 21

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
theorem bcdefg12N2Face_coeff
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G) :
    (bcdefg12N2Face A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + D.natDegree) =
      (5 / 512 : k) * n2QuarticOpenIIFace810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  have hA : A ≠ 0 := by intro hz; simp [hz] at hApos
  have hd0 : (A * B ^ 2 * D).natDegree = A.natDegree + 2 * B.natDegree + D.natDegree := by
    rw [natDegree_mul (mul_ne_zero hA (pow_ne_zero 2 hB)) hD, natDegree_mul hA (pow_ne_zero 2 hB)] <;> (try simp only [natDegree_pow]) <;> omega
  have hcf0 : (A * B ^ 2 * D).coeff (A.natDegree + 2 * B.natDegree + D.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hd0, coeff_natDegree] <;> simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : (B * C * E).natDegree = A.natDegree + 2 * B.natDegree + D.natDegree := by
    rw [natDegree_mul (mul_ne_zero hB hC) hE, natDegree_mul hB hC] <;> (try simp only [natDegree_pow]) <;> omega
  have hcf1 : (B * C * E).coeff (A.natDegree + 2 * B.natDegree + D.natDegree) = B.leadingCoeff * C.leadingCoeff * E.leadingCoeff := by
    rw [← hd1, coeff_natDegree] <;> simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : (C ^ 2 * D).natDegree = A.natDegree + 2 * B.natDegree + D.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hC) hD] <;> (try simp only [natDegree_pow]) <;> omega
  have hcf2 : (C ^ 2 * D).coeff (A.natDegree + 2 * B.natDegree + D.natDegree) = C.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hd2, coeff_natDegree] <;> simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd3 : (D * G).natDegree = A.natDegree + 2 * B.natDegree + D.natDegree := by
    rw [natDegree_mul hD hG] <;> (try simp only [natDegree_pow]) <;> omega
  have hcf3 : (D * G).coeff (A.natDegree + 2 * B.natDegree + D.natDegree) = D.leadingCoeff * G.leadingCoeff := by
    rw [← hd3, coeff_natDegree] <;> simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd4 : (E * F).natDegree = A.natDegree + 2 * B.natDegree + D.natDegree := by
    rw [natDegree_mul hE hF] <;> (try simp only [natDegree_pow]) <;> omega
  have hcf4 : (E * F).coeff (A.natDegree + 2 * B.natDegree + D.natDegree) = E.leadingCoeff * F.leadingCoeff := by
    rw [← hd4, coeff_natDegree] <;> simp only [leadingCoeff_mul, leadingCoeff_pow]
  simp only [bcdefg12N2Face, n2QuarticOpenIIFace810, coeff_add, coeff_smul, smul_eq_mul, hcf0, hcf1, hcf2, hcf3, hcf4]
  ring

set_option maxHeartbeats 64000000 in
/-- Vanishing of the scalar N2 face under the strict load bands. -/
theorem bcdefg12N2Face_zero
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hbL : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree)
    (hbBeta : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree)
    (hbDelta : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree)
    (hbZeta : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree)
    (hbTheta : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0) :
    n2QuarticOpenIIFace810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
  have hrest := bcdefg12N2Rest_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbL hbBeta hbDelta hbZeta hbTheta
  have hface := bcdefg12N2Face_coeff A B C D E F G hc
  have hApos := hc.1.1
  have hcarrier := degreeZeroN2Quartic810_natDegree_le l beta gamma delta epsilon zeta eta theta A B C D E F G hnu hkap
  have htop : A.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree := by
    rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
    have hApos := hcone.1
    omega
  have hz := coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hcarrier htop)
  rw [bcdefg12N2_split, coeff_add, coeff_eq_zero_of_natDegree_lt hrest, add_zero, hface] at hz
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num : (5 / 512 : k) ≠ 0)

end Max11DegreeRoutes
