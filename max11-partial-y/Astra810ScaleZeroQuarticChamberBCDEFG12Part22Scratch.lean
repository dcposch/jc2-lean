import Grok810ScaleZeroQuarticChamberDefs4Scratch

/-! # BCDEFG12 chamber, part 22

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
/-- The polynomial face of N6 on BCDEFG12. -/
def bcdefg12N6Face
    (A B C D E F G : k[X]) : k[X] :=
  (145 / 12288 : k) • (A ^ 2 * B ^ 3 * C)
  + (-25 / 1536 : k) • (A ^ 2 * B ^ 2 * F)
  + (-25 / 768 : k) • (A ^ 2 * B * D ^ 2)
  + (-45 / 1024 : k) • (A * B * C ^ 3)
  + (15 / 128 : k) • (A * B * C * G)
  + (25 / 192 : k) • (A * B * E ^ 2)
  + (95 / 384 : k) • (A * C * D * E)
  + (-25 / 48 : k) • (A * F * G)
  + (5 / 96 : k) • (A * C ^ 2 * F)

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N6RestLF0
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (93 / 8192 : k) • (A * B ^ 5)
  + (-115 / 1536 : k) • (A * B ^ 3 * E)
  + (-225 / 1024 : k) • (A * B ^ 2 * C * D)
  + (-125 / 2048 : k) • (B ^ 4 * D)
  + (-265 / 2048 : k) • (B ^ 3 * C ^ 2)
  + (25 / 96 : k) • (A * B * D * F)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N6RestLF0_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G) :
    (bcdefg12N6RestLF0 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  simp only [bcdefg12N6RestLF0]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N6RestLF1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (25 / 384 : k) • (A * D ^ 3)
  + (15 / 256 : k) • (B ^ 3 * G)
  + (85 / 256 : k) • (B ^ 2 * C * F)
  + (85 / 256 : k) • (B ^ 2 * D * E)
  + (45 / 128 : k) • (B * C ^ 2 * E)
  + (45 / 128 : k) • (B * C * D ^ 2)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N6RestLF1_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G) :
    (bcdefg12N6RestLF1 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  simp only [bcdefg12N6RestLF1]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N6RestLF2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 128 : k) • (C ^ 3 * D)
  + (-5 / 16 : k) • (B * E * G)
  + (-5 / 16 : k) • (B * F ^ 2)
  + (-5 / 16 : k) • (C * D * G)
  + (-5 / 8 : k) • (C * E * F)
  + (-5 / 16 : k) • (D ^ 2 * F)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N6RestLF2_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G) :
    (bcdefg12N6RestLF2 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  simp only [bcdefg12N6RestLF2]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N6RestLF3
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-5 / 16 : k) • (D * E ^ 2)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N6RestLF3_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G) :
    (bcdefg12N6RestLF3 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  simp only [bcdefg12N6RestLF3]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N6RestL0
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (715 / 268435456 * l : k) • (A ^ 8)
  + (105 / 1048576 * l : k) • (A ^ 6 * C)
  + (-255 / 4194304 * l : k) • (A ^ 5 * B ^ 2)
  + (105 / 262144 * l : k) • (A ^ 5 * E)
  + (-135 / 262144 * l : k) • (A ^ 4 * B * D)
  + (585 / 524288 * l : k) • (A ^ 4 * C ^ 2)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N6RestL0_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hb : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N6RestL0 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  rcases hb with hz | hb
  · subst l
    simp only [bcdefg12N6RestL0, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  · simp only [bcdefg12N6RestL0]
    compute_degree
    omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N6RestL1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-93 / 131072 * l : k) • (A ^ 3 * B ^ 2 * C)
  + (1425 / 524288 * l : k) • (A ^ 2 * B ^ 4)
  + (15 / 32768 * l : k) • (A ^ 4 * G)
  + (81 / 8192 * l : k) • (A ^ 3 * C * E)
  + (-15 / 8192 * l : k) • (A ^ 3 * D ^ 2)
  + (-135 / 16384 * l : k) • (A ^ 2 * B ^ 2 * E)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N6RestL1_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hb : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N6RestL1 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  rcases hb with hz | hb
  · subst l
    simp only [bcdefg12N6RestL1, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  · simp only [bcdefg12N6RestL1]
    compute_degree
    omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N6RestL2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-51 / 4096 * l : k) • (A ^ 2 * B * C * D)
  + (11 / 8192 * l : k) • (A ^ 2 * C ^ 3)
  + (-369 / 8192 * l : k) • (A * B ^ 3 * D)
  + (-765 / 16384 * l : k) • (A * B ^ 2 * C ^ 2)
  + (-567 / 16384 * l : k) • (B ^ 4 * C)
  + (3 / 256 * l : k) • (A ^ 2 * C * G)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N6RestL2_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hb : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N6RestL2 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  rcases hb with hz | hb
  · subst l
    simp only [bcdefg12N6RestL2, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  · simp only [bcdefg12N6RestL2]
    compute_degree
    omega

end Max11DegreeRoutes
