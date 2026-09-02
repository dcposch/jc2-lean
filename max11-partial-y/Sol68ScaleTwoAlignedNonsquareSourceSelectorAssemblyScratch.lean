import Sol68ScaleTwoAlignedNonsquareSourceConditionalInputScratch

/-! # Exact same-witness selector assembly

The source transports are now automatic.  This file isolates only the
remaining root/component choices and uses the existing conjugate/component-II
machinery to construct the complete conditional final-input record.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000

section SameWitnessSelectorAssembly68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]
  {p q : k[X][X]} {j : k}

/-- The genuinely unproved selector after source transport.  It contains no
quotient polynomial or transport identity: those are constructed uniquely by
the source and component-II theorems. -/
structure NonsquareAlignedSameWitnessSelector68
    (p : k[X][X]) (r t X0 B D w phi K : k[X]) (j : k) where
  a : k
  ha : H.eval a = 0
  hwa : w.eval a = 0
  hphia : phi.eval a = 0
  hDa : D.eval a = 0
  hKa : K.eval a = 0
  hclass : ∀ x : k, H.eval x = 0 →
    terminalPhiDivisorLowerThirdClassification68
      ((cubicANumerator68 t r).eval x) (H.derivative.eval x)
      (6 * j * H.derivative.eval x ^ 3) B D w phi
      (terminalEDerivativeNumerator68 H
        (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) t r)) K x
  hrefined : B.eval a ≠ 0 →
    terminalPhiDivisorRefinedIIIResidual68 r B D w phi
      (terminalEDerivativeNumerator68 H
        (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) t r)) K a
      (6 * j * H.derivative.eval a ^ 3)
  hcomponentII : ∀ c : k, c ≠ a → H.eval c = 0 →
    terminalRefinedIIIConjugateMatching68 H (cubicANumerator68 t r)
      B D w phi
      (terminalEDerivativeNumerator68 H
        (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) t r)) K j c →
    B.eval c = 0 ∧ D.eval c = 0
  hnormalizedF : ∀ c : k, c ≠ a → H.eval c = 0 →
    terminalRefinedIIIConjugateMatching68 H (cubicANumerator68 t r)
      B D w phi
      (terminalEDerivativeNumerator68 H
        (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) t r)) K j c →
    B.derivative.eval c = 0 ∧
      (cubicANumerator68 t r).eval c * B.derivative.eval c -
        3 * D.derivative.eval c = 0 ∧
      (cubicANumerator68 t r).eval c * B.derivative.derivative.eval c -
        3 * D.derivative.derivative.eval c = 0 ∧
      terminalRefinedIIIConjugateIIFThirdCorrected68
        ((cubicANumerator68 t r).eval c) (H.derivative.eval c)
        (H.derivative.derivative.eval c)
        (B.derivative.derivative.eval c)
        (B.derivative.derivative.derivative.eval c)
        (D.derivative.derivative.derivative.eval c) = 0
  hcommonSelector : B.eval a = 0 ∨
    (phi.derivative.eval a = 0 ∧
      ((cubicANumerator68 t r).eval a = 0 ∨ w.derivative.eval a = 0))

/-- Existing root matching and component-II APIs convert the selector into a
full conditional final-input record.  All quotient and lower-zero witnesses
are those of `T`; none are reselected. -/
theorem NonsquareAlignedSourceCurveData68.conditionalFinalInputs_of_sameWitnessSelector
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hdeg : H.natDegree = 2) (hj : j ≠ 0)
    (r t X0 Yd B D w phi1 k1 phi K : k[X])
    (T : terminalPhiDivisorSameWitnessSourceTransport68 H S
      r t X0 Yd B D w phi1 k1 phi K)
    (R : NonsquareAlignedSameWitnessSelector68 H p r t X0 B D w phi K j) :
    Nonempty (NonsquareAlignedFinalStableConditionalSourceInputs68 H S) := by
  rcases T with ⟨hp4, hX, hY, hW, hPhi, hwitness, hI4, hrow, hlower⟩
  let A0 := cubicANumerator68 t r
  let C0 := cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r
  let E0 := cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
    (p.coeff 3) t r
  let eDot := terminalEDerivativeNumerator68 H E0
  have hsimple : ∀ x : k, H.eval x = 0 → H.derivative.eval x ≠ 0 :=
    fun x hx => nonsquare_natDegree_two_derivative_ne_zero hdeg
      NonsquarePolynomial46.not_sq hx
  obtain ⟨c, hca, hc, hmatch⟩ := terminalRefinedIII_conjugate_matching_68
    H A0 B D w phi eDot K j R.a hdeg hsimple R.ha R.hwa R.hphia
      R.hDa R.hKa (by simpa only [A0, E0, eDot] using R.hclass)
  have hac : R.a ≠ c := hca.symm
  obtain ⟨hBc, hDc⟩ := R.hcomponentII c hca hc
    (by simpa only [A0, E0, eDot] using hmatch)
  obtain ⟨D1, BW, hDshape, hBWshape, hI4q, hrowq, hnext⟩ :=
    terminalRefinedIII_conjugateII_next_68 H A0 B D w phi eDot K j
      R.a c hdeg hsimple R.ha hc hac R.hwa R.hDa hI4 hrow hmatch hBc hDc
  obtain ⟨hB1, hF1, hF2, hL3⟩ := R.hnormalizedF c hca hc
    (by simpa only [A0, E0, eDot] using hmatch)
  obtain ⟨B2, F3, hB, hF, hnormalized⟩ :=
    terminalRefinedIII_conjugateII_L3_normalized_68 H A0 B D c
      hBc hB1 hDc hF1 hF2 hL3
  have hF0 : A0.eval c * B.eval c - 3 * D.eval c = 0 := by
    rw [hBc, hDc]
    ring
  have commonNext (hG : phi.eval c + 2 * A0.eval c * w.eval c = 0) :
      terminalRefinedIIIConjugateCommonTransverseNext68 H A0 B D w phi
        eDot K j R.a c := by
    have hprev := terminalRefinedIII_conjugateCommon_transverse_68 H
      A0 B D w phi eDot K j R.a c hdeg hsimple R.ha hc hac R.hwa
      R.hphia R.hDa R.hKa hI4 hrow R.hcommonSelector hF0 hG
    exact terminalRefinedIII_conjugateCommon_transverseNext_68 H
      A0 B D w phi eDot K j R.a c hdeg hsimple R.ha hc hac R.hwa
      R.hphia R.hDa R.hKa hI4 hrow hF0 hprev
  have componentIIRoute
      (_hII : B.eval c = 0 ∧ D.eval c = 0 ∧ H ∣ D) :
      r.eval c = 0 ∨
        terminalRefinedIIIConjugateCommonTransverseNext68 H A0 B D w phi
          eDot K j R.a c := by
    exact S.terminalRefinedIIIConjugateIIIntoCommonTransverseNext (H := H)
      t r X0 C0 E0 (H * B) B D w phi K D1 BW B2 F3 R.a c
      hdeg R.ha hc hac R.hwa R.hphia R.hDa R.hKa rfl
      (by simpa only [A0, C0] using hW)
      (by simpa only [A0, C0, E0] using hPhi) hX hB
      (by simpa only [A0] using hF) hDshape hBWshape hI4q hrowq hI4
      (by simpa only [E0, eDot] using hrow) R.hcommonSelector
      hnormalized hj
  have hinventory : terminalRefinedIIIConjugateCommonIIResidual68 H
      A0 B D w phi eDot K r j R.a c :=
    terminalRefinedIII_conjugate_commonII_inventory_68 H A0 B D w phi
      eDot K r j R.a c hmatch (fun _hF hG => commonNext hG)
      componentIIRoute
  have hcoordinate (hrc : r.eval c = 0) :
      terminalRefinedIIIConjugateCoordinateResidual68 H t r X0 B D w phi
        eDot K R.a c (6 * j * H.derivative.eval R.a ^ 3) := by
    exact S.terminalRefinedIIIConjugateCoordinateSibling (H := H)
      t r X0 B D w phi eDot K R.a c hdeg R.ha hc hac hX R.hwa
      R.hphia R.hDa
      ⟨R.hclass R.a R.ha, fun _ _ _ hBne => R.hrefined hBne⟩ hrc
  refine ⟨{
    t := t
    r := r
    X0 := X0
    Yd := Yd
    b1 := H * B
    B := B
    D := D
    w := w
    phi := phi
    K := K
    D1 := D1
    BW := BW
    B2 := B2
    F3 := F3
    phi1 := phi1
    k1 := k1
    a := R.a
    c := c
    ha := R.ha
    hc := hc
    hac := hac
    hwa := R.hwa
    hphia := R.hphia
    hDa := R.hDa
    hKa := R.hKa
    hb := rfl
    hW := by simpa only [A0, C0] using hW
    hPhi := by simpa only [A0, C0, E0] using hPhi
    hp4 := hp4
    hX := hX
    hY := hY
    hB := hB
    hF := by simpa only [A0] using hF
    hDshape := hDshape
    hBWshape := hBWshape
    hI4q := hI4q
    hrowq := by simpa only [E0, eDot] using hrowq
    hI4 := hI4
    hrow := by simpa only [E0, eDot] using hrow
    hnormalized := hnormalized
    hwitness := hwitness
    hlower := by simpa only [A0, C0, E0] using hlower
    hinventory := by simpa only [A0, E0, eDot] using hinventory
    hcoordinate := by simpa only [E0, eDot] using hcoordinate }⟩

end SameWitnessSelectorAssembly68

end Max11DegreeRoutes
