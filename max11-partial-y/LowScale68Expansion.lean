import LowScale68WeightedRadius

/-! # Expansion transport for the `(6,8)` polynomial lower system

Polynomial expansion by `x ↦ x^60` is an algebra homomorphism, so the two
exact invariants commute with it.  Each of the three one-form rows acquires
the same chain-rule factor `60*x^59`.  The first two rows therefore remain
zero, while the expanded terminal constant has degree only 59 and vanishes at
the positive maximal boundary selected in `LowScale68WeightedRadius`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section Expansion68

variable {k : Type*} [Field k] [CharZero k]

/-- Exact five-row polynomial system before denominator-clearing expansion. -/
structure IntegratedPolynomialLowerSystem68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) : Prop where
  firstFour : ∃ i4 : k,
    firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
      A B C0 D E = C i4
  firstThree : ∃ i3 : k,
    firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
      A B C0 D E = C i3
  rowTwo : lowerRowTwoPolynomial68
      (integratedSPolynomial68 l alpha beta delta A B C0 D)
      (integratedTPolynomial68 l alpha beta gamma epsilon A B C0 D E)
      (integratedUPolynomial68 l alpha beta gamma delta zeta A B C0 D E)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        A B C0 D E) B C0 D E = 0
  rowOne : lowerRowOnePolynomial68
      (integratedTPolynomial68 l alpha beta gamma epsilon A B C0 D E)
      (integratedUPolynomial68 l alpha beta gamma delta zeta A B C0 D E)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        A B C0 D E) C0 D E = 0
  rowZero : lowerRowZeroPolynomial68
      (integratedUPolynomial68 l alpha beta gamma delta zeta A B C0 D E)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        A B C0 D E) D E = C terminal

set_option maxHeartbeats 2000000 in
/-- Pull the exact rational lower system back to any chosen polynomial
representatives.  This packages the source-facing argument used by the
boundary theorem in the form needed for expansion and later descent. -/
theorem integratedRationalLowerSystem_polynomialLowerSystem68
    (A B C0 D E : RatFunc k) (A0 B0 C00 D0 E0 : k[X])
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (hA0 : algebraMap k[X] (RatFunc k) A0 = A)
    (hB0 : algebraMap k[X] (RatFunc k) B0 = B)
    (hC0 : algebraMap k[X] (RatFunc k) C00 = C0)
    (hD0 : algebraMap k[X] (RatFunc k) D0 = D)
    (hE0 : algebraMap k[X] (RatFunc k) E0 = E)
    (hbracket :
      let P := integratedP68 A (RatFunc.C alpha)
      let Q := integratedQ68 (RatFunc.C l) A B (RatFunc.C beta)
      let R := integratedR68 (RatFunc.C l) A B C0 (RatFunc.C alpha)
        (RatFunc.C gamma)
      let S := integratedS68 (RatFunc.C l) A B C0 D (RatFunc.C alpha)
        (RatFunc.C beta) (RatFunc.C delta)
      let T := integratedT68 (RatFunc.C l) A B C0 D E (RatFunc.C alpha)
        (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C epsilon)
      let U := integratedU68 (RatFunc.C l) A B C0 D E (RatFunc.C alpha)
        (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
        (RatFunc.C zeta)
      let V := integratedV68 (RatFunc.C l) A B C0 D E (RatFunc.C alpha)
        (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
        (RatFunc.C epsilon) (RatFunc.C eta)
      differentialJacobian ratFuncDerivation68 (depressedSextic68 A B C0 D E)
        (depressedOctic68 (RatFunc.C l) P Q R S T U V) =
          C (RatFunc.C terminal)) :
    IntegratedPolynomialLowerSystem68 l alpha beta gamma delta epsilon zeta
      eta terminal A0 B0 C00 D0 E0 := by
  let S0 := integratedSPolynomial68 l alpha beta delta A0 B0 C00 D0
  let T0 := integratedTPolynomial68 l alpha beta gamma epsilon
    A0 B0 C00 D0 E0
  let U0 := integratedUPolynomial68 l alpha beta gamma delta zeta
    A0 B0 C00 D0 E0
  let V0 := integratedVPolynomial68 l alpha beta gamma delta epsilon eta
    A0 B0 C00 D0 E0
  have hSmap : algebraMap k[X] (RatFunc k) S0 =
      integratedS68 (RatFunc.C l) A B C0 D (RatFunc.C alpha)
        (RatFunc.C beta) (RatFunc.C delta) := by
    dsimp only [S0]
    rw [algebraMap_integratedSPolynomial68, hA0, hB0, hC0, hD0]
  have hTmap : algebraMap k[X] (RatFunc k) T0 =
      integratedT68 (RatFunc.C l) A B C0 D E (RatFunc.C alpha)
        (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C epsilon) := by
    dsimp only [T0]
    rw [algebraMap_integratedTPolynomial68, hA0, hB0, hC0, hD0, hE0]
  have hUmap : algebraMap k[X] (RatFunc k) U0 =
      integratedU68 (RatFunc.C l) A B C0 D E (RatFunc.C alpha)
        (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
        (RatFunc.C zeta) := by
    dsimp only [U0]
    rw [algebraMap_integratedUPolynomial68, hA0, hB0, hC0, hD0, hE0]
  have hVmap : algebraMap k[X] (RatFunc k) V0 =
      integratedV68 (RatFunc.C l) A B C0 D E (RatFunc.C alpha)
        (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
        (RatFunc.C epsilon) (RatFunc.C eta) := by
    dsimp only [V0]
    rw [algebraMap_integratedVPolynomial68, hA0, hB0, hC0, hD0, hE0]
  obtain ⟨i4, i3, hi4, hi3⟩ := integratedFirstIntegrals_exist_ground68
    A B C0 D E (RatFunc.C terminal) l alpha beta gamma delta epsilon zeta eta
    hbracket
  simp only [RatFunc.algebraMap_eq_C] at hi4 hi3
  have hconst (a : k) : ratFuncDerivation68 (RatFunc.C a) = 0 := by
    have hp := ratFuncDerivation46_polynomial (C a : k[X])
    simpa [ratFuncDerivation68, RatFunc.algebraMap_C] using hp
  have hlow := constantBracket_integrated68_lowerSystem
    ratFuncDerivation68 (RatFunc.C l) A B C0 D E (RatFunc.C alpha)
      (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
      (RatFunc.C epsilon) (RatFunc.C zeta) (RatFunc.C eta)
      (RatFunc.C terminal) (hconst l) (hconst alpha) (hconst beta)
      (hconst gamma) (hconst delta) (hconst epsilon) (hconst zeta)
      (hconst eta) hbracket
  dsimp only at hlow
  have hI4poly : firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
      A0 B0 C00 D0 E0 = C i4 := by
    apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
    rw [algebraMap_firstIntegralFourPolynomial68, RatFunc.algebraMap_C,
      hA0, hB0, hC0, hD0, hE0]
    exact hi4
  have hI3poly : firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
      A0 B0 C00 D0 E0 = C i3 := by
    apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
    rw [algebraMap_firstIntegralThreePolynomial68, RatFunc.algebraMap_C,
      hA0, hB0, hC0, hD0, hE0]
    exact hi3
  have h2poly : lowerRowTwoPolynomial68 S0 T0 U0 V0 B0 C00 D0 E0 = 0 := by
    apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
    rw [algebraMap_lowerRowTwoPolynomial68, map_zero, hSmap, hTmap, hUmap,
      hVmap, hB0, hC0, hD0, hE0]
    exact hlow.2.2.1
  have h1poly : lowerRowOnePolynomial68 T0 U0 V0 C00 D0 E0 = 0 := by
    apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
    rw [algebraMap_lowerRowOnePolynomial68, map_zero, hTmap, hUmap, hVmap,
      hC0, hD0, hE0]
    exact hlow.2.2.2.1
  have h0poly : lowerRowZeroPolynomial68 U0 V0 D0 E0 = C terminal := by
    apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
    rw [algebraMap_lowerRowZeroPolynomial68, RatFunc.algebraMap_C,
      hUmap, hVmap, hD0, hE0]
    exact hlow.2.2.2.2
  exact {
    firstFour := ⟨i4, hI4poly⟩
    firstThree := ⟨i3, hI3poly⟩
    rowTwo := h2poly
    rowOne := h1poly
    rowZero := h0poly }

theorem expand_integratedSPolynomial68
    (m : ℕ) (l alpha beta delta : k) (A B C0 D : k[X]) :
    expand k m (integratedSPolynomial68 l alpha beta delta A B C0 D) =
      integratedSPolynomial68 l alpha beta delta
        (expand k m A) (expand k m B) (expand k m C0) (expand k m D) := by
  simp [integratedSPolynomial68]

theorem expand_integratedTPolynomial68
    (m : ℕ) (l alpha beta gamma epsilon : k) (A B C0 D E : k[X]) :
    expand k m
        (integratedTPolynomial68 l alpha beta gamma epsilon A B C0 D E) =
      integratedTPolynomial68 l alpha beta gamma epsilon
        (expand k m A) (expand k m B) (expand k m C0)
        (expand k m D) (expand k m E) := by
  simp [integratedTPolynomial68]

theorem expand_integratedUPolynomial68
    (m : ℕ) (l alpha beta gamma delta zeta : k) (A B C0 D E : k[X]) :
    expand k m
        (integratedUPolynomial68 l alpha beta gamma delta zeta A B C0 D E) =
      integratedUPolynomial68 l alpha beta gamma delta zeta
        (expand k m A) (expand k m B) (expand k m C0)
        (expand k m D) (expand k m E) := by
  simp [integratedUPolynomial68]

theorem expand_integratedVPolynomial68
    (m : ℕ) (l alpha beta gamma delta epsilon eta : k)
    (A B C0 D E : k[X]) :
    expand k m (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        A B C0 D E) =
      integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        (expand k m A) (expand k m B) (expand k m C0)
        (expand k m D) (expand k m E) := by
  simp [integratedVPolynomial68]

theorem expand_firstIntegralFourPolynomial68
    (m : ℕ) (l beta gamma delta epsilon zeta : k) (A B C0 D E : k[X]) :
    expand k m (firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
        A B C0 D E) =
      firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
        (expand k m A) (expand k m B) (expand k m C0)
        (expand k m D) (expand k m E) := by
  simp [firstIntegralFourPolynomial68]

theorem expand_firstIntegralThreePolynomial68
    (m : ℕ) (l beta gamma delta epsilon zeta : k) (A B C0 D E : k[X]) :
    expand k m (firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
        A B C0 D E) =
      firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
        (expand k m A) (expand k m B) (expand k m C0)
        (expand k m D) (expand k m E) := by
  simp [firstIntegralThreePolynomial68]

/-- The first one-form row transforms by the common chain-rule factor. -/
theorem lowerRowTwoPolynomial68_expand
    (m : ℕ) (S T U V B C0 D E : k[X]) :
    lowerRowTwoPolynomial68 (expand k m S) (expand k m T)
        (expand k m U) (expand k m V) (expand k m B) (expand k m C0)
        (expand k m D) (expand k m E) =
      expand k m (lowerRowTwoPolynomial68 S T U V B C0 D E) *
        (m * (X ^ (m - 1) : k[X])) := by
  simp only [lowerRowTwoPolynomial68, derivative_expand, map_add, map_sub,
    map_mul, map_smul, Polynomial.smul_eq_C_mul, expand_C]
  ring

/-- The second one-form row transforms by the common chain-rule factor. -/
theorem lowerRowOnePolynomial68_expand
    (m : ℕ) (T U V C0 D E : k[X]) :
    lowerRowOnePolynomial68 (expand k m T) (expand k m U)
        (expand k m V) (expand k m C0) (expand k m D) (expand k m E) =
      expand k m (lowerRowOnePolynomial68 T U V C0 D E) *
        (m * (X ^ (m - 1) : k[X])) := by
  simp only [lowerRowOnePolynomial68, derivative_expand, map_add, map_sub,
    map_mul, map_smul, Polynomial.smul_eq_C_mul, expand_C]
  ring

/-- The terminal one-form row transforms by the common chain-rule factor. -/
theorem lowerRowZeroPolynomial68_expand
    (m : ℕ) (U V D E : k[X]) :
    lowerRowZeroPolynomial68 (expand k m U) (expand k m V)
        (expand k m D) (expand k m E) =
      expand k m (lowerRowZeroPolynomial68 U V D E) *
        (m * (X ^ (m - 1) : k[X])) := by
  simp only [lowerRowZeroPolynomial68, derivative_expand, map_sub, map_mul]
  ring

set_option maxHeartbeats 2000000 in
/-- The exact lower system survives expansion strongly enough for the
polynomial boundary theorem: the expanded terminal row has no coefficient at
the selected boundary. -/
theorem expandedIntegratedPolynomialLowerSystem_cubicCore68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X])
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (n : ℕ) (hn : 0 < n) (hnlarge : 5 ≤ n)
    (hA : (expand k 60 A).natDegree ≤ 2 * n)
    (hB : (expand k 60 B).natDegree ≤ 3 * n)
    (hC : (expand k 60 C0).natDegree ≤ 4 * n)
    (hD : (expand k 60 D).natDegree ≤ 5 * n)
    (hE : (expand k 60 E).natDegree ≤ 6 * n) :
    (expand k 60 B).coeff (3 * n) = 0 ∧
    (expand k 60 D).coeff (5 * n) = 0 ∧
    (expand k 60 C0).coeff (4 * n) =
      (expand k 60 A).coeff (2 * n) ^ 2 / 3 ∧
    (expand k 60 E).coeff (6 * n) =
      (expand k 60 A).coeff (2 * n) ^ 3 / 27 := by
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let De := expand k 60 D
  let Ee := expand k 60 E
  let Se := integratedSPolynomial68 l alpha beta delta Ae Be Ce De
  let Te := integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee
  let Ue := integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee
  let Ve := integratedVPolynomial68 l alpha beta gamma delta epsilon eta
    Ae Be Ce De Ee
  obtain ⟨i4, hi4⟩ := hsys.firstFour
  obtain ⟨i3, hi3⟩ := hsys.firstThree
  have hdegrees := integratedPolynomial68_degreeBounds
    l alpha beta gamma delta epsilon zeta eta Ae Be Ce De Ee n
    hA hB hC hD hE
  have htop : IntegratedBoundaryCoefficients68 Ae Be Ce De Ee Se Te Ue Ve n := by
    dsimp only [Se, Te, Ue, Ve]
    exact integratedPolynomial68_boundaryCoefficients
      l alpha beta gamma delta epsilon zeta eta Ae Be Ce De Ee n hn
      hA hB hC hD hE
  have hi4e : firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i4 := by
    have h := congrArg (expand k 60) hi4
    simpa [Ae, Be, Ce, De, Ee, expand_firstIntegralFourPolynomial68] using h
  have hi3e : firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i3 := by
    have h := congrArg (expand k 60) hi3
    simpa [Ae, Be, Ce, De, Ee, expand_firstIntegralThreePolynomial68] using h
  have h2e : lowerRowTwoPolynomial68 Se Te Ue Ve Be Ce De Ee = 0 := by
    dsimp only [Se, Te, Ue, Ve, Ae, Be, Ce, De, Ee]
    rw [← expand_integratedSPolynomial68, ← expand_integratedTPolynomial68,
      ← expand_integratedUPolynomial68, ← expand_integratedVPolynomial68,
      lowerRowTwoPolynomial68_expand, hsys.rowTwo, map_zero, zero_mul]
  have h1e : lowerRowOnePolynomial68 Te Ue Ve Ce De Ee = 0 := by
    dsimp only [Te, Ue, Ve, Ae, Be, Ce, De, Ee]
    rw [← expand_integratedTPolynomial68, ← expand_integratedUPolynomial68,
      ← expand_integratedVPolynomial68, lowerRowOnePolynomial68_expand,
      hsys.rowOne, map_zero, zero_mul]
  have h0e : lowerRowZeroPolynomial68 Ue Ve De Ee =
      C terminal * (60 * (X ^ 59 : k[X])) := by
    dsimp only [Ue, Ve, Ae, Be, Ce, De, Ee]
    rw [← expand_integratedUPolynomial68, ← expand_integratedVPolynomial68,
      lowerRowZeroPolynomial68_expand, hsys.rowZero, expand_C]
    norm_num
  have h0top : (lowerRowZeroPolynomial68 Ue Ve De Ee).coeff (13 * n - 1) = 0 := by
    rw [h0e]
    apply coeff_eq_zero_of_natDegree_lt
    have hdeg : (C terminal * (60 * (X ^ 59 : k[X]))).natDegree ≤ 59 := by
      compute_degree
    exact hdeg.trans_lt (by omega)
  exact polynomialLowerSystem_cubicCore68_of_terminalCoeff_zero
    l beta gamma delta epsilon zeta i4 i3 Ae Be Ce De Ee Se Te Ue Ve n hn
    hA hB hC hD hE hdegrees.1 hdegrees.2.1 hdegrees.2.2.1
    hdegrees.2.2.2 htop hi4e hi3e h2e h1e h0top

set_option maxHeartbeats 2000000 in
/-- The canonical maximal expansion has a nontrivial cubic top face: its
`A`-coefficient is nonzero, while the other four coefficients are the forced
cubic powers. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_cubicCore68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E) :
    let n := weightedRadius68 A B C0 D E
    0 < n ∧
    (expand k 60 B).coeff (3 * n) = 0 ∧
    (expand k 60 D).coeff (5 * n) = 0 ∧
    (expand k 60 C0).coeff (4 * n) =
      (expand k 60 A).coeff (2 * n) ^ 2 / 3 ∧
    (expand k 60 E).coeff (6 * n) =
      (expand k 60 A).coeff (2 * n) ^ 3 / 27 ∧
    (expand k 60 A).coeff (2 * n) ≠ 0 := by
  let n := weightedRadius68 A B C0 D E
  have hload := terminalRow68_forces_nonconstant_load
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys.rowZero
  have hn : 0 < n := weightedRadius68_pos A B C0 D E hload
  have hnlarge : 5 ≤ n := by
    dsimp only [n, weightedRadius68] at hn ⊢
    omega
  have hbounds := weightedRadius68_degreeBounds A B C0 D E
  have hcore := expandedIntegratedPolynomialLowerSystem_cubicCore68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E hsys n hn
    hnlarge hbounds.1 hbounds.2.1 hbounds.2.2.1 hbounds.2.2.2.1
    hbounds.2.2.2.2
  have hattained := weightedRadius68_boundary_attained A B C0 D E hn
  have hAne : (expand k 60 A).coeff (2 * n) ≠ 0 := by
    intro hAzero
    have hCzero : (expand k 60 C0).coeff (4 * n) = 0 := by
      rw [hcore.2.2.1, hAzero]
      norm_num
    have hEzero : (expand k 60 E).coeff (6 * n) = 0 := by
      rw [hcore.2.2.2, hAzero]
      norm_num
    rcases hattained with hA | hB | hC | hD | hE
    · exact hA hAzero
    · exact hB hcore.1
    · exact hC hCzero
    · exact hD hcore.2.1
    · exact hE hEzero
  exact ⟨hn, hcore.1, hcore.2.1, hcore.2.2.1, hcore.2.2.2, hAne⟩

set_option maxHeartbeats 2000000 in
/-- Source-facing maximal-boundary theorem.  An exact rational lower system,
polynomial representatives, and a nonzero Keller terminal row canonically
produce a nontrivial expanded cubic top face. -/
theorem integratedRationalLowerSystem_maximalExpanded_cubicCore68
    (A B C0 D E : RatFunc k) (A0 B0 C00 D0 E0 : k[X])
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (hterminal : terminal ≠ 0)
    (hA0 : algebraMap k[X] (RatFunc k) A0 = A)
    (hB0 : algebraMap k[X] (RatFunc k) B0 = B)
    (hC0 : algebraMap k[X] (RatFunc k) C00 = C0)
    (hD0 : algebraMap k[X] (RatFunc k) D0 = D)
    (hE0 : algebraMap k[X] (RatFunc k) E0 = E)
    (hbracket :
      let P := integratedP68 A (RatFunc.C alpha)
      let Q := integratedQ68 (RatFunc.C l) A B (RatFunc.C beta)
      let R := integratedR68 (RatFunc.C l) A B C0 (RatFunc.C alpha)
        (RatFunc.C gamma)
      let S := integratedS68 (RatFunc.C l) A B C0 D (RatFunc.C alpha)
        (RatFunc.C beta) (RatFunc.C delta)
      let T := integratedT68 (RatFunc.C l) A B C0 D E (RatFunc.C alpha)
        (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C epsilon)
      let U := integratedU68 (RatFunc.C l) A B C0 D E (RatFunc.C alpha)
        (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
        (RatFunc.C zeta)
      let V := integratedV68 (RatFunc.C l) A B C0 D E (RatFunc.C alpha)
        (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
        (RatFunc.C epsilon) (RatFunc.C eta)
      differentialJacobian ratFuncDerivation68 (depressedSextic68 A B C0 D E)
        (depressedOctic68 (RatFunc.C l) P Q R S T U V) =
          C (RatFunc.C terminal)) :
    let n := weightedRadius68 A0 B0 C00 D0 E0
    0 < n ∧
    (expand k 60 B0).coeff (3 * n) = 0 ∧
    (expand k 60 D0).coeff (5 * n) = 0 ∧
    (expand k 60 C00).coeff (4 * n) =
      (expand k 60 A0).coeff (2 * n) ^ 2 / 3 ∧
    (expand k 60 E0).coeff (6 * n) =
      (expand k 60 A0).coeff (2 * n) ^ 3 / 27 ∧
    (expand k 60 A0).coeff (2 * n) ≠ 0 := by
  have hsys := integratedRationalLowerSystem_polynomialLowerSystem68
    A B C0 D E A0 B0 C00 D0 E0 l alpha beta gamma delta epsilon zeta eta
    terminal hA0 hB0 hC0 hD0 hE0 hbracket
  exact maximalExpandedIntegratedPolynomialLowerSystem_cubicCore68
    l alpha beta gamma delta epsilon zeta eta terminal A0 B0 C00 D0 E0
    hterminal hsys

end Expansion68

#print axioms expand_firstIntegralFourPolynomial68
#print axioms integratedRationalLowerSystem_polynomialLowerSystem68
#print axioms lowerRowTwoPolynomial68_expand
#print axioms lowerRowOnePolynomial68_expand
#print axioms lowerRowZeroPolynomial68_expand
#print axioms expandedIntegratedPolynomialLowerSystem_cubicCore68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_cubicCore68
#print axioms integratedRationalLowerSystem_maximalExpanded_cubicCore68

end Max11DegreeRoutes
