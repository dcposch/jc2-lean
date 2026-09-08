import Astra810ScaleZeroQuarticChamberBCDEFG12Part18Scratch

/-! # BCDEFG12 chamber, part 19

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
def bcdefg12N2RestDelta0
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (35 / 32768 * delta : k) • (A ^ 4)
  + (15 / 1024 * delta : k) • (A ^ 2 * C)
  + (15 / 1024 * delta : k) • (A * B ^ 2)
  + (-15 / 64 * delta : k) • (B * D)
  + (-15 / 128 * delta : k) • (C ^ 2)
  + (5 / 8 * delta : k) • (G)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N2RestDelta0_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hb : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N2RestDelta0 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      A.natDegree + 2 * B.natDegree + D.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  rcases hb with hz | hb
  · subst delta
    simp only [bcdefg12N2RestDelta0, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  · simp only [bcdefg12N2RestDelta0]
    compute_degree
    omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N2RestDelta1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 64 * delta : k) • (A * E)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N2RestDelta1_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hb : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N2RestDelta1 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      A.natDegree + 2 * B.natDegree + D.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  rcases hb with hz | hb
  · subst delta
    simp only [bcdefg12N2RestDelta1, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  · simp only [bcdefg12N2RestDelta1]
    compute_degree
    omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N2RestEpsilon0
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-1 / 4 * epsilon : k) • (B * C)
  + (1 / 2 * epsilon : k) • (F)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N2RestEpsilon0_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G) :
    (bcdefg12N2RestEpsilon0 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      A.natDegree + 2 * B.natDegree + D.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  simp only [bcdefg12N2RestEpsilon0]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N2RestZeta0
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 1024 * zeta : k) • (A ^ 3)
  + (-15 / 128 * zeta : k) • (B ^ 2)
  + (3 / 8 * zeta : k) • (E)
  + (3 / 64 * zeta : k) • (A * C)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N2RestZeta0_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hb : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N2RestZeta0 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      A.natDegree + 2 * B.natDegree + D.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  rcases hb with hz | hb
  · subst zeta
    simp only [bcdefg12N2RestZeta0, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  · simp only [bcdefg12N2RestZeta0]
    compute_degree
    omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N2RestEta0
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1 / 4 * eta : k) • (D)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N2RestEta0_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G) :
    (bcdefg12N2RestEta0 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      A.natDegree + 2 * B.natDegree + D.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  simp only [bcdefg12N2RestEta0]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N2RestTheta0
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (3 / 128 * theta : k) • (A ^ 2)
  + (1 / 8 * theta : k) • (C)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N2RestTheta0_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hb : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N2RestTheta0 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      A.natDegree + 2 * B.natDegree + D.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  rcases hb with hz | hb
  · subst theta
    simp only [bcdefg12N2RestTheta0, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  · simp only [bcdefg12N2RestTheta0]
    compute_degree
    omega

end Max11DegreeRoutes
