import Grok810ScaleZeroQuarticChamberDefs4Scratch
import Max11SpeedReflectDegLibScratch

/-! # BCDEFG12 chamber, part 24

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
def bcdefg12N6RestGamma0
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 768 * gamma : k) • (A ^ 2 * B ^ 3)
  + (-15 / 128 * gamma : k) • (A * B ^ 2 * D)
  + (-9 / 128 * gamma : k) • (A * B * C ^ 2)
  + (-27 / 256 * gamma : k) • (B ^ 3 * C)
  + (-1 / 32 * gamma : k) • (A * C * F)
  + (5 / 16 * gamma : k) • (A * D * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bcdefg12N6RestGamma0` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4aaChamberRefl_ChamberBCDEFG12Part102_bcdefg12N6RestGamma0
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bcdefg12N6RestGamma0 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (5 / 768 * gamma : k), (-15 / 128 * gamma : k), (-9 / 128 * gamma : k),
      (-27 / 256 * gamma : k), (-1 / 32 * gamma : k), (5 / 16 * gamma : k)
      ]
      [
      [2, 3, 0, 0, 0, 0, 0], [1, 2, 0, 1, 0, 0, 0], [1, 1, 2, 0, 0, 0, 0], [0, 3, 1, 0, 0, 0, 0],
      [1, 0, 1, 0, 0, 1, 0], [1, 0, 0, 1, 1, 0, 0]
      ] := by
  simp only [bcdefg12N6RestGamma0, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N6RestGamma0_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G) :
    (bcdefg12N6RestGamma0 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  rw [astra4aaChamberRefl_ChamberBCDEFG12Part102_bcdefg12N6RestGamma0]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N6RestGamma1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (9 / 64 * gamma : k) • (B ^ 2 * F)
  + (3 / 8 * gamma : k) • (B * C * E)
  + (3 / 16 * gamma : k) • (B * D ^ 2)
  + (3 / 16 * gamma : k) • (C ^ 2 * D)
  + (-3 / 4 * gamma : k) • (E * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bcdefg12N6RestGamma1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4aaChamberRefl_ChamberBCDEFG12Part102_bcdefg12N6RestGamma1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bcdefg12N6RestGamma1 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (9 / 64 * gamma : k), (3 / 8 * gamma : k), (3 / 16 * gamma : k),
      (3 / 16 * gamma : k), (-3 / 4 * gamma : k)
      ]
      [
      [0, 2, 0, 0, 0, 1, 0], [0, 1, 1, 0, 1, 0, 0], [0, 1, 0, 2, 0, 0, 0], [0, 0, 2, 1, 0, 0, 0],
      [0, 0, 0, 0, 1, 1, 0]
      ] := by
  simp only [bcdefg12N6RestGamma1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N6RestGamma1_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G) :
    (bcdefg12N6RestGamma1 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  rw [astra4aaChamberRefl_ChamberBCDEFG12Part102_bcdefg12N6RestGamma1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N6RestDelta0
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (21 / 524288 * delta : k) • (A ^ 6)
  + (5 / 4096 * delta : k) • (A ^ 4 * C)
  + (-65 / 49152 * delta : k) • (A ^ 3 * B ^ 2)
  + (5 / 1024 * delta : k) • (A ^ 3 * E)
  + (-95 / 3072 * delta : k) • (A ^ 2 * B * D)
  + (65 / 6144 * delta : k) • (A ^ 2 * C ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bcdefg12N6RestDelta0` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4aaChamberRefl_ChamberBCDEFG12Part102_bcdefg12N6RestDelta0
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bcdefg12N6RestDelta0 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (21 / 524288 * delta : k), (5 / 4096 * delta : k), (-65 / 49152 * delta : k),
      (5 / 1024 * delta : k), (-95 / 3072 * delta : k), (65 / 6144 * delta : k)
      ]
      [
      [6, 0, 0, 0, 0, 0, 0], [4, 0, 1, 0, 0, 0, 0], [3, 2, 0, 0, 0, 0, 0], [3, 0, 0, 0, 1, 0, 0],
      [2, 1, 0, 1, 0, 0, 0], [2, 0, 2, 0, 0, 0, 0]
      ] := by
  simp only [bcdefg12N6RestDelta0, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N6RestDelta0_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hb : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N6RestDelta0 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  rcases hb with hz | hb
  · subst delta
    simp only [bcdefg12N6RestDelta0, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  ·
    rw [astra4aaChamberRefl_ChamberBCDEFG12Part102_bcdefg12N6RestDelta0]
    apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
    simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
      Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
      Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
      Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
      max_lt_iff]
    repeat' apply And.intro
    all_goals omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N6RestDelta1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-125 / 1024 * delta : k) • (A * B ^ 2 * C)
  + (-135 / 4096 * delta : k) • (B ^ 4)
  + (35 / 192 * delta : k) • (A * C * E)
  + (5 / 32 * delta : k) • (A * D ^ 2)
  + (25 / 128 * delta : k) • (B ^ 2 * E)
  + (15 / 32 * delta : k) • (B * C * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bcdefg12N6RestDelta1` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4aaChamberRefl_ChamberBCDEFG12Part102_bcdefg12N6RestDelta1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bcdefg12N6RestDelta1 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-125 / 1024 * delta : k), (-135 / 4096 * delta : k), (35 / 192 * delta : k),
      (5 / 32 * delta : k), (25 / 128 * delta : k), (15 / 32 * delta : k)
      ]
      [
      [1, 2, 1, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [1, 0, 1, 0, 1, 0, 0], [1, 0, 0, 2, 0, 0, 0],
      [0, 2, 0, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0, 0]
      ] := by
  simp only [bcdefg12N6RestDelta1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N6RestDelta1_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hb : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N6RestDelta1 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  rcases hb with hz | hb
  · subst delta
    simp only [bcdefg12N6RestDelta1, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  ·
    rw [astra4aaChamberRefl_ChamberBCDEFG12Part102_bcdefg12N6RestDelta1]
    apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
    simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
      Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
      Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
      Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
      max_lt_iff]
    repeat' apply And.intro
    all_goals omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N6RestDelta2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 64 * delta : k) • (C ^ 3)
  + (-5 / 8 * delta : k) • (D * F)
  + (-5 / 16 * delta : k) • (E ^ 2)
  + (5 / 96 * delta : k) • (A * B * F)
  + (-5 / 384 * delta : k) • (A ^ 2 * G)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bcdefg12N6RestDelta2` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4aaChamberRefl_ChamberBCDEFG12Part102_bcdefg12N6RestDelta2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bcdefg12N6RestDelta2 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (5 / 64 * delta : k), (-5 / 8 * delta : k), (-5 / 16 * delta : k),
      (5 / 96 * delta : k), (-5 / 384 * delta : k)
      ]
      [
      [0, 0, 3, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0], [1, 1, 0, 0, 0, 1, 0],
      [2, 0, 0, 0, 0, 0, 1]
      ] := by
  simp only [bcdefg12N6RestDelta2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N6RestDelta2_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hb : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N6RestDelta2 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  rcases hb with hz | hb
  · subst delta
    simp only [bcdefg12N6RestDelta2, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  ·
    rw [astra4aaChamberRefl_ChamberBCDEFG12Part102_bcdefg12N6RestDelta2]
    apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
    simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
      Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
      Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
      Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
      max_lt_iff]
    repeat' apply And.intro
    all_goals omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N6RestEpsilon0
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-5 / 96 * epsilon : k) • (A * B ^ 3)
  + (5 / 24 * epsilon : k) • (A * B * E)
  + (3 / 16 * epsilon : k) • (A * C * D)
  + (7 / 32 * epsilon : k) • (B ^ 2 * D)
  + (1 / 4 * epsilon : k) • (B * C ^ 2)
  + (-1 / 2 * epsilon : k) • (C * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bcdefg12N6RestEpsilon0` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4aaChamberRefl_ChamberBCDEFG12Part102_bcdefg12N6RestEpsilon0
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bcdefg12N6RestEpsilon0 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-5 / 96 * epsilon : k), (5 / 24 * epsilon : k), (3 / 16 * epsilon : k),
      (7 / 32 * epsilon : k), (1 / 4 * epsilon : k), (-1 / 2 * epsilon : k)
      ]
      [
      [1, 3, 0, 0, 0, 0, 0], [1, 1, 0, 0, 1, 0, 0], [1, 0, 1, 1, 0, 0, 0], [0, 2, 0, 1, 0, 0, 0],
      [0, 1, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0]
      ] := by
  simp only [bcdefg12N6RestEpsilon0, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N6RestEpsilon0_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G) :
    (bcdefg12N6RestEpsilon0 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  rw [astra4aaChamberRefl_ChamberBCDEFG12Part102_bcdefg12N6RestEpsilon0]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N6RestEpsilon1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-1 / 2 * epsilon : k) • (D * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bcdefg12N6RestEpsilon1` (1 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4aaChamberRefl_ChamberBCDEFG12Part102_bcdefg12N6RestEpsilon1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bcdefg12N6RestEpsilon1 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-1 / 2 * epsilon : k)
      ]
      [
      [0, 0, 0, 1, 1, 0, 0]
      ] := by
  simp only [bcdefg12N6RestEpsilon1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N6RestEpsilon1_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G) :
    (bcdefg12N6RestEpsilon1 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  rw [astra4aaChamberRefl_ChamberBCDEFG12Part102_bcdefg12N6RestEpsilon1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N6RestZeta0
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (7 / 49152 * zeta : k) • (A ^ 5)
  + (1 / 256 * zeta : k) • (A ^ 3 * C)
  + (-11 / 1024 * zeta : k) • (A ^ 2 * B ^ 2)
  + (1 / 64 * zeta : k) • (A ^ 2 * E)
  + (3 / 16 * zeta : k) • (A * B * D)
  + (27 / 128 * zeta : k) • (B ^ 2 * C)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bcdefg12N6RestZeta0` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4aaChamberRefl_ChamberBCDEFG12Part102_bcdefg12N6RestZeta0
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bcdefg12N6RestZeta0 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (7 / 49152 * zeta : k), (1 / 256 * zeta : k), (-11 / 1024 * zeta : k),
      (1 / 64 * zeta : k), (3 / 16 * zeta : k), (27 / 128 * zeta : k)
      ]
      [
      [5, 0, 0, 0, 0, 0, 0], [3, 0, 1, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0], [2, 0, 0, 0, 1, 0, 0],
      [1, 1, 0, 1, 0, 0, 0], [0, 2, 1, 0, 0, 0, 0]
      ] := by
  simp only [bcdefg12N6RestZeta0, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N6RestZeta0_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hb : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N6RestZeta0 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  rcases hb with hz | hb
  · subst zeta
    simp only [bcdefg12N6RestZeta0, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  ·
    rw [astra4aaChamberRefl_ChamberBCDEFG12Part102_bcdefg12N6RestZeta0]
    apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
    simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
      Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
      Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
      Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
      max_lt_iff]
    repeat' apply And.intro
    all_goals omega

end Max11DegreeRoutes
/-! # BCDEFG12 chamber, part 25

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
def bcdefg12N6RestZeta1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-3 / 8 * zeta : k) • (B * F)
  + (-3 / 8 * zeta : k) • (C * E)
  + (-3 / 16 * zeta : k) • (D ^ 2)
  + (3 / 64 * zeta : k) • (A * C ^ 2)
  + (-1 / 4 * zeta : k) • (A * G)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bcdefg12N6RestZeta1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4aaChamberRefl_ChamberBCDEFG12Part102_bcdefg12N6RestZeta1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bcdefg12N6RestZeta1 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-3 / 8 * zeta : k), (-3 / 8 * zeta : k), (-3 / 16 * zeta : k),
      (3 / 64 * zeta : k), (-1 / 4 * zeta : k)
      ]
      [
      [0, 1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0], [1, 0, 2, 0, 0, 0, 0],
      [1, 0, 0, 0, 0, 0, 1]
      ] := by
  simp only [bcdefg12N6RestZeta1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N6RestZeta1_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hb : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N6RestZeta1 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  rcases hb with hz | hb
  · subst zeta
    simp only [bcdefg12N6RestZeta1, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  ·
    rw [astra4aaChamberRefl_ChamberBCDEFG12Part102_bcdefg12N6RestZeta1]
    apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
    simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
      Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
      Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
      Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
      max_lt_iff]
    repeat' apply And.intro
    all_goals omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N6RestEta0
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (3 / 32 * eta : k) • (A * B * C)
  + (3 / 64 * eta : k) • (B ^ 3)
  + (-5 / 12 * eta : k) • (A * F)
  + (-1 / 4 * eta : k) • (B * E)
  + (-1 / 4 * eta : k) • (C * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bcdefg12N6RestEta0` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4aaChamberRefl_ChamberBCDEFG12Part102_bcdefg12N6RestEta0
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bcdefg12N6RestEta0 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (3 / 32 * eta : k), (3 / 64 * eta : k), (-5 / 12 * eta : k),
      (-1 / 4 * eta : k), (-1 / 4 * eta : k)
      ]
      [
      [1, 1, 1, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0], [0, 1, 0, 0, 1, 0, 0],
      [0, 0, 1, 1, 0, 0, 0]
      ] := by
  simp only [bcdefg12N6RestEta0, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N6RestEta0_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G) :
    (bcdefg12N6RestEta0 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  rw [astra4aaChamberRefl_ChamberBCDEFG12Part102_bcdefg12N6RestEta0]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N6RestTheta0
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 12288 * theta : k) • (A ^ 4)
  + (1 / 96 * theta : k) • (A ^ 2 * C)
  + (3 / 128 * theta : k) • (A * B ^ 2)
  + (1 / 24 * theta : k) • (A * E)
  + (-1 / 8 * theta : k) • (B * D)
  + (-1 / 16 * theta : k) • (C ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bcdefg12N6RestTheta0` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4aaChamberRefl_ChamberBCDEFG12Part102_bcdefg12N6RestTheta0
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bcdefg12N6RestTheta0 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (5 / 12288 * theta : k), (1 / 96 * theta : k), (3 / 128 * theta : k),
      (1 / 24 * theta : k), (-1 / 8 * theta : k), (-1 / 16 * theta : k)
      ]
      [
      [4, 0, 0, 0, 0, 0, 0], [2, 0, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 0],
      [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0]
      ] := by
  simp only [bcdefg12N6RestTheta0, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N6RestTheta0_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hb : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N6RestTheta0 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  rcases hb with hz | hb
  · subst theta
    simp only [bcdefg12N6RestTheta0, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  ·
    rw [astra4aaChamberRefl_ChamberBCDEFG12Part102_bcdefg12N6RestTheta0]
    apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
    simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
      Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
      Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
      Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
      max_lt_iff]
    repeat' apply And.intro
    all_goals omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N6RestTheta1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1 * theta : k) • (G)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bcdefg12N6RestTheta1` (1 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4aaChamberRefl_ChamberBCDEFG12Part102_bcdefg12N6RestTheta1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bcdefg12N6RestTheta1 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (1 * theta : k)
      ]
      [
      [0, 0, 0, 0, 0, 0, 1]
      ] := by
  simp only [bcdefg12N6RestTheta1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N6RestTheta1_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hb : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N6RestTheta1 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  rcases hb with hz | hb
  · subst theta
    simp only [bcdefg12N6RestTheta1, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  ·
    rw [astra4aaChamberRefl_ChamberBCDEFG12Part102_bcdefg12N6RestTheta1]
    apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
    simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
      Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
      Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
      Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
      max_lt_iff]
    repeat' apply And.intro
    all_goals omega

end Max11DegreeRoutes
