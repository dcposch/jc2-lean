import Grok810ScaleZeroQuarticChamberDefs4Scratch

/-! # BCDEFG12 chamber, part 23

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
/-- A chunk with at most six monomials. -/
def bcdefg12N6RestL3
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (3 / 1024 * l : k) • (A ^ 2 * D * F)
  + (51 / 2048 * l : k) • (A ^ 2 * E ^ 2)
  + (27 / 1024 * l : k) • (A * B ^ 2 * G)
  + (21 / 256 * l : k) • (A * B * C * F)
  + (75 / 512 * l : k) • (A * B * D * E)
  + (39 / 1024 * l : k) • (A * C ^ 2 * E)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N6RestL3_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hb : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N6RestL3 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  rcases hb with hz | hb
  · subst l
    simp only [bcdefg12N6RestL3, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  · simp only [bcdefg12N6RestL3]
    compute_degree
    omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N6RestL4
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (9 / 128 * l : k) • (A * C * D ^ 2)
  + (27 / 512 * l : k) • (B ^ 3 * F)
  + (45 / 256 * l : k) • (B ^ 2 * C * E)
  + (45 / 512 * l : k) • (B ^ 2 * D ^ 2)
  + (189 / 1024 * l : k) • (B * C ^ 2 * D)
  + (63 / 4096 * l : k) • (C ^ 4)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N6RestL4_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hb : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N6RestL4 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  rcases hb with hz | hb
  · subst l
    simp only [bcdefg12N6RestL4, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  · simp only [bcdefg12N6RestL4]
    compute_degree
    omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N6RestL5
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (3 / 64 * l : k) • (A * E * G)
  + (-3 / 16 * l : k) • (A * F ^ 2)
  + (-9 / 64 * l : k) • (B * D * G)
  + (-9 / 32 * l : k) • (B * E * F)
  + (-9 / 128 * l : k) • (C ^ 2 * G)
  + (-9 / 32 * l : k) • (C * D * F)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N6RestL5_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hb : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N6RestL5 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  rcases hb with hz | hb
  · subst l
    simp only [bcdefg12N6RestL5, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  · simp only [bcdefg12N6RestL5]
    compute_degree
    omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N6RestL6
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-9 / 64 * l : k) • (C * E ^ 2)
  + (-9 / 64 * l : k) • (D ^ 2 * E)
  + (9 / 16 * l : k) • (G ^ 2)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N6RestL6_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hb : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N6RestL6 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  rcases hb with hz | hb
  · subst l
    simp only [bcdefg12N6RestL6, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  · simp only [bcdefg12N6RestL6]
    compute_degree
    omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N6RestBeta0
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (11 / 1048576 * beta : k) • (A ^ 7)
  + (35 / 98304 * beta : k) • (A ^ 5 * C)
  + (-35 / 131072 * beta : k) • (A ^ 4 * B ^ 2)
  + (35 / 24576 * beta : k) • (A ^ 4 * E)
  + (-35 / 12288 * beta : k) • (A ^ 3 * B * D)
  + (7 / 2048 * beta : k) • (A ^ 3 * C ^ 2)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N6RestBeta0_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hb : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N6RestBeta0 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  rcases hb with hz | hb
  · subst beta
    simp only [bcdefg12N6RestBeta0, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  · simp only [bcdefg12N6RestBeta0]
    compute_degree
    omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N6RestBeta1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (175 / 49152 * beta : k) • (A ^ 2 * B ^ 2 * C)
  + (91 / 8192 * beta : k) • (A * B ^ 4)
  + (35 / 1024 * beta : k) • (A ^ 2 * C * E)
  + (-133 / 6144 * beta : k) • (A ^ 2 * D ^ 2)
  + (-49 / 768 * beta : k) • (A * B ^ 2 * E)
  + (-7 / 64 * beta : k) • (A * B * C * D)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N6RestBeta1_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hb : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N6RestBeta1 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  rcases hb with hz | hb
  · subst beta
    simp only [bcdefg12N6RestBeta1, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  · simp only [bcdefg12N6RestBeta1]
    compute_degree
    omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N6RestBeta2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-7 / 128 * beta : k) • (B ^ 3 * D)
  + (-91 / 1024 * beta : k) • (B ^ 2 * C ^ 2)
  + (7 / 48 * beta : k) • (A * E ^ 2)
  + (7 / 32 * beta : k) • (B * C * F)
  + (7 / 32 * beta : k) • (B * D * E)
  + (7 / 64 * beta : k) • (C ^ 2 * E)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N6RestBeta2_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hb : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N6RestBeta2 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  rcases hb with hz | hb
  · subst beta
    simp only [bcdefg12N6RestBeta2, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  · simp only [bcdefg12N6RestBeta2]
    compute_degree
    omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N6RestBeta3
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (7 / 64 * beta : k) • (C * D ^ 2)
  + (-7 / 16 * beta : k) • (F ^ 2)
  + (-7 / 768 * beta : k) • (A * C ^ 3)
  + (7 / 96 * beta : k) • (A * D * F)
  + (7 / 3072 * beta : k) • (A ^ 2 * B * F)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N6RestBeta3_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hb : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N6RestBeta3 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  rcases hb with hz | hb
  · subst beta
    simp only [bcdefg12N6RestBeta3, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  · simp only [bcdefg12N6RestBeta3]
    compute_degree
    omega

end Max11DegreeRoutes
