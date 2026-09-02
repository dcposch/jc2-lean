import Sol68ScaleTwoAlignedNonsquareSourceRefinedPacketScratch

/-! # Provenance-preserving nonsquare source split

This file performs the complete finite root/component split on the literal
witnesses of `terminalPhiDivisorSameWitnessSourceTransport68`.  It deliberately
does not identify those witnesses with the independent existential tuple of
`terminalAfterLowerOneCoordinateSplitPacket`.
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

section FixedWitnessComprehensiveSplit68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]
  {p q : k[X][X]} {j : k}

/-- The finite alternatives left by the fixed-witness conjugate analysis.
The first leaf records that no deep refined-III root exists.  The next two
retain the common and component-III conjugate allocations literally.  The
last three leaves are, respectively, the global `w` divisor, the deep
coordinate sibling, and the complete geometric selector. -/
def terminalPhiDivisorFixedGeometricSplit68
    (p : k[X][X]) (r t X0 B D w phi K : k[X]) (j : k) : Prop :=
  (∀ a : k, H.eval a = 0 →
      ¬ (w.eval a = 0 ∧ phi.eval a = 0 ∧ D.eval a = 0 ∧ K.eval a = 0)) ∨
    ∃ a c : k,
      c ≠ a ∧ H.eval a = 0 ∧ H.eval c = 0 ∧
      w.eval a = 0 ∧ phi.eval a = 0 ∧ D.eval a = 0 ∧ K.eval a = 0 ∧
      (((cubicANumerator68 t r).eval c * B.eval c - 3 * D.eval c = 0 ∧
          phi.eval c + 2 * (cubicANumerator68 t r).eval c * w.eval c = 0) ∨
        (w.eval c = 0 ∧ phi.eval c = 0 ∧ H ∣ w ∧ H ∣ phi ∧
          ((D.eval c = 0 ∧ H ∣ D) ∨ (K.eval c = 0 ∧ H ∣ K))) ∨
        H ∣ w ∨ r.eval a = 0 ∨
        Nonempty
          (NonsquareAlignedGeometricSelector68 H p r t X0 B D w phi K j))

/-- The source identities and the fixed root-classification packet reduce the
`H ∣ phi1` branch to a finite, provenance-preserving geometric split. -/
theorem NonsquareAlignedSourceCurveData68.fixedWitnessComprehensiveSplit
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hdeg : H.natDegree = 2)
    (r t X0 Yd B D w phi1 k1 phi K : k[X])
    (T : terminalPhiDivisorSameWitnessSourceTransport68 H S
      r t X0 Yd B D w phi1 k1 phi K) :
    terminalPhiDivisorFixedGeometricSplit68 H p r t X0 B D w phi K j := by
  classical
  rcases T with ⟨hp4, hX, hY, hW, hPhi, hwitness, hI4, hrow, hlower⟩
  let A0 := cubicANumerator68 t r
  let C0 := cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r
  let E0 := cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
    (p.coeff 3) t r
  let eDot := terminalEDerivativeNumerator68 H E0
  have hroot := S.fixedWitnessRefinedIIIRootPacket (H := H) hdeg
    r t X0 Yd B D w phi1 k1 phi K
    ⟨hp4, hX, hY, hW, hPhi, hwitness, hI4, hrow, hlower⟩
  have hsimple : ∀ x : k, H.eval x = 0 → H.derivative.eval x ≠ 0 :=
    fun x hx => nonsquare_natDegree_two_derivative_ne_zero hdeg
      NonsquarePolynomial46.not_sq hx
  by_cases hdeep : ∃ a : k, H.eval a = 0 ∧ w.eval a = 0 ∧
      phi.eval a = 0 ∧ D.eval a = 0 ∧ K.eval a = 0
  · right
    obtain ⟨a, ha, hwa, hphia, hDa, hKa⟩ := hdeep
    obtain ⟨c, hca, hc, hmatch⟩ := terminalRefinedIII_conjugate_matching_68
      H A0 B D w phi eDot K j a hdeg hsimple ha hwa hphia hDa hKa
      (by
        intro x hx
        simpa only [A0, E0, eDot] using (hroot x hx).1)
    refine ⟨a, c, hca, ha, hc, hwa, hphia, hDa, hKa, ?_⟩
    rcases hmatch.2 with hcommon | hrest
    · exact Or.inl hcommon
    rcases hrest with hII | hIII
    · obtain ⟨hBc, hDc, hdvdD⟩ := hII
      have hac : a ≠ c := hca.symm
      obtain ⟨D1, BW, hDshape, hBWshape, hI4q, hrowq, hnext⟩ :=
        terminalRefinedIII_conjugateII_next_68 H A0 B D w phi eDot K j
          a c hdeg hsimple ha hc hac hwa hDa hI4 hrow hmatch hBc hDc
      have hH : H ≠ 0 := H_ne_zero_of_nonsquare68 (H := H)
      have hfactor := terminalLowerZero_factor_one_68 H A0 (H * B) C0
        (H * D) E0 B D S.alpha S.gamma S.epsilon S.eta rfl rfl
      have hlower1 : terminalLowerZeroOne68 H A0 B C0 D E0
          S.alpha S.gamma S.epsilon S.eta = 0 := by
        have hz : H * terminalLowerZeroOne68 H A0 B C0 D E0
            S.alpha S.gamma S.epsilon S.eta = 0 := by
          rw [← hfactor]
          simpa only [A0, C0, E0] using hlower
        exact (mul_eq_zero.mp hz).resolve_left hH
      have hcoordinate :=
        S.terminalRefinedIIIConjugateIICoordinatePacket (H := H)
          A0 C0 E0 (H * B) B D w phi K D1 BW a c hdeg rfl
          (by simpa only [A0, C0] using hW)
          (by simpa only [A0, C0, E0] using hPhi)
          ha hc hac hwa hphia hBc hDc hDshape hmatch hnext hlower1
          (by simpa only [E0, eDot] using hrowq)
      rcases hcoordinate.1 with hFG | hcoordinate
      · exact Or.inl ⟨by simp [A0, hBc, hDc], hFG.2⟩
      rcases hcoordinate with hF | hG
      · rcases hF with ⟨hF1, hB1, hdvdW | hF2⟩
        · exact Or.inr (Or.inr (Or.inl hdvdW))
        · have hmult :=
            S.terminalRefinedIIIConjugateIIFMultiplicityPacket (H := H)
              A0 C0 E0 (H * B) B D w phi K D1 BW c rfl
              (by simpa only [A0, C0] using hW)
              (by simpa only [A0, C0, E0] using hPhi)
              hc hBc hB1 hDc hF1 hF2 hmatch hlower1
              (by simpa only [E0, eDot] using hrowq)
          rcases hmult.1 with hGc | hL3
          · exact Or.inl ⟨by simp [A0, hBc, hDc], hGc⟩
          · have hnormalized := terminalRefinedIII_conjugateII_L3_normalized_68
              H A0 B D c hBc hB1 hDc hF1 hF2 hL3
            have hcommonSelector : r.eval a = 0 ∨
                (B.eval a = 0 ∨
                  (phi.derivative.eval a = 0 ∧
                    (A0.eval a = 0 ∨ w.derivative.eval a = 0))) := by
              by_cases hBa : B.eval a = 0
              · exact Or.inr (Or.inl hBa)
              · rcases (hroot a ha).2 hwa hphia hDa hBa with hra | hrefined
                · exact Or.inl hra
                · exact Or.inr (Or.inr ⟨hrefined.2.1, Or.inr hrefined.1⟩)
            rcases hcommonSelector with hra | hcommonA
            · exact Or.inr (Or.inr (Or.inr (Or.inl hra)))
            · have hcomponentII : ∀ z : k, z ≠ a → H.eval z = 0 →
                  terminalRefinedIIIConjugateMatching68 H A0 B D w phi
                    eDot K j z → B.eval z = 0 ∧ D.eval z = 0 := by
                intro z hza hz _hmatchz
                rcases natDegree_two_roots_exhaust_68 H hdeg a c z hac ha hc hz with
                  rfl | rfl
                · exact (hza rfl).elim
                · exact ⟨hBc, hDc⟩
              have hnormalizedF : ∀ z : k, z ≠ a → H.eval z = 0 →
                  terminalRefinedIIIConjugateMatching68 H A0 B D w phi
                    eDot K j z →
                  B.derivative.eval z = 0 ∧
                    A0.eval z * B.derivative.eval z -
                        3 * D.derivative.eval z = 0 ∧
                    A0.eval z * B.derivative.derivative.eval z -
                        3 * D.derivative.derivative.eval z = 0 ∧
                    terminalRefinedIIIConjugateIIFThirdCorrected68
                      (A0.eval z) (H.derivative.eval z)
                      (H.derivative.derivative.eval z)
                      (B.derivative.derivative.eval z)
                      (B.derivative.derivative.derivative.eval z)
                      (D.derivative.derivative.derivative.eval z) = 0 := by
                intro z hza hz _hmatchz
                rcases natDegree_two_roots_exhaust_68 H hdeg a c z hac ha hc hz with
                  rfl | rfl
                · exact (hza rfl).elim
                · exact ⟨hB1, hF1, hF2, hL3⟩
              have G : NonsquareAlignedGeometricSelector68 H p r t X0
                  B D w phi K j := {
                a := a
                ha := ha
                hwa := hwa
                hphia := hphia
                hDa := hDa
                hKa := hKa
                hcomponentII := by
                  simpa only [A0, E0, eDot] using hcomponentII
                hnormalizedF := by
                  simpa only [A0, E0, eDot] using hnormalizedF
                hcommonSelector := by simpa only [A0] using hcommonA }
              exact Or.inr (Or.inr (Or.inr (Or.inr ⟨G⟩)))
      · exact Or.inr (Or.inr (Or.inl hG.2.2.1))
    · exact Or.inr (Or.inl hIII)
  · left
    intro a ha hzeros
    exact hdeep ⟨a, ha, hzeros.1, hzeros.2.1, hzeros.2.2.1, hzeros.2.2.2⟩

end FixedWitnessComprehensiveSplit68

end Max11DegreeRoutes
