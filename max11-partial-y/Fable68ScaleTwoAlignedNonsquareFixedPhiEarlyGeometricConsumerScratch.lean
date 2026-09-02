import Sol68ScaleTwoAlignedNonsquareSourceFixedAssemblyScratch

/-! # Early geometric consumers for the fixed `H ∣ phi1` split

Only the two earliest leaves of `terminalPhiDivisorFixedGeometricSplit68`
are attacked, on the literal witnesses of the same-witness transport:

* the no-deep-root leaf is refined into a per-root loaded classification
  with the deep-kill negation distributed through the three flavors: every
  component-III root gains an exclusive `D`/`K` unit pin, the `D`-side pin
  chains into the refined component-III residual, apex zeros are converted
  to coordinate zeros, and the two simple core roots are produced
  explicitly with their exhaustiveness certificate;
* the first common-conjugate matching leaf is fed to the existing
  witness-compatible transverse consumers
  (`terminalRefinedIII_conjugateCommon_transverse_68` and its `Next`
  refinement), reconstructing the global `G`-face `phi + 2*A*w = H*G` and
  the cancelled row `H*b*G = 2*w*(A*b - 3*D)` on the fixed tuple.

The component-III, `H ∣ w`, `r(a) = 0` and full-selector alternatives are
retained verbatim, as are the `H ∣ r` and mixed coordinate siblings and the
complete selector consumer of the fixed assembly.  No witness is reselected.
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

section FixedPhiEarlyGeometricAlgebra68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- Refined per-root face of the no-deep-root leaf.  The first conjunct
restates the deep-kill negation; the disjunction distributes it through the
loaded lower-third classification: a common root keeps the full loaded face
with its apex zero converted to a coordinate zero, a component-II root keeps
the left-zero load together with the componentII lower row and a three-way
unit disjunction, and a component-III root gains the exclusive `K`/`D` unit
pin, the `D`-side chaining into the refined component-III residual. -/
def terminalFixedPhiNoDeepRootFace68
    (H A r B D w phi e K : k[X]) (j x : k) : Prop :=
  (w.eval x ≠ 0 ∨ phi.eval x ≠ 0 ∨ D.eval x ≠ 0 ∨ K.eval x ≠ 0) ∧
    ((A.eval x * B.eval x - 3 * D.eval x = 0 ∧
        phi.eval x + 2 * A.eval x * w.eval x = 0 ∧
        ((A.eval x = 0 ∧ r.eval x = 0) ∨ B.eval x = 0 ∨
          H.derivative.eval x * A.eval x ^ 2 * w.eval x +
            3 * K.eval x = 0) ∧
        terminalThirdTripleAt68 B w e x - terminalThirdPairAt68 D K x =
          6 * j * H.derivative.eval x ^ 3) ∨
      (B.eval x = 0 ∧ D.eval x = 0 ∧
        (w.eval x ≠ 0 ∨ phi.eval x ≠ 0 ∨ K.eval x ≠ 0) ∧
        2 * A.eval x * w.eval x *
            (A.eval x * B.derivative.eval x - 3 * D.derivative.eval x) -
          3 * D.derivative.eval x *
            (phi.eval x + 2 * A.eval x * w.eval x) = 0 ∧
        terminalThirdTripleLeftZeroAt68 B w e x -
          terminalThirdPairLeftZeroAt68 D K x =
            6 * j * H.derivative.eval x ^ 3) ∨
      (w.eval x = 0 ∧ phi.eval x = 0 ∧ D.eval x = 0 ∧ K.eval x ≠ 0 ∧
        2 * A.eval x ^ 2 * w.derivative.eval x * B.eval x = 0 ∧
        terminalThirdTripleMiddleZeroAt68 B w e x -
          terminalThirdPairLeftZeroAt68 D K x =
            6 * j * H.derivative.eval x ^ 3 ∧
        (B.eval x = 0 ∨
          (B.eval x ≠ 0 ∧ phi.derivative.eval x = 0 ∧
            ((A.eval x = 0 ∧ r.eval x = 0) ∨ w.derivative.eval x = 0) ∧
            terminalPhiDivisorRefinedIIIResidual68 r B D w phi e K x
              (6 * j * H.derivative.eval x ^ 3)))) ∨
      (w.eval x = 0 ∧ phi.eval x = 0 ∧ K.eval x = 0 ∧ D.eval x ≠ 0 ∧
        B.eval x * phi.derivative.eval x +
          6 * w.derivative.eval x * D.eval x = 0 ∧
        2 * A.eval x * w.derivative.eval x *
            (A.eval x * B.eval x - 3 * D.eval x) -
          3 * D.eval x *
            (phi.derivative.eval x +
              2 * A.eval x * w.derivative.eval x) = 0 ∧
        terminalThirdTripleMiddleZeroAt68 B w e x -
          terminalThirdPairRightZeroAt68 D K x =
            6 * j * H.derivative.eval x ^ 3))

/-- The lower-third classification, the conditional refined residual and the
deep-kill negation produce the refined face at one core root.  Only retained
faces, the apex conversion and order-zero unit logic are used; no new row is
opened. -/
theorem terminalFixedPhi_noDeepRootFace_68
    (H t r X0 B D w phi e K : k[X]) (j x : k)
    (hx : H.eval x = 0)
    (hX : C 3 * t - r ^ 2 = H * X0)
    (hclass : terminalPhiDivisorLowerThirdClassification68
      ((cubicANumerator68 t r).eval x) (H.derivative.eval x)
      (6 * j * H.derivative.eval x ^ 3) B D w phi e K x)
    (hresid : w.eval x = 0 → phi.eval x = 0 → D.eval x = 0 →
      B.eval x ≠ 0 →
      terminalPhiDivisorRefinedIIIResidual68 r B D w phi e K x
        (6 * j * H.derivative.eval x ^ 3))
    (hnodeep : ¬ (w.eval x = 0 ∧ phi.eval x = 0 ∧ D.eval x = 0 ∧
      K.eval x = 0)) :
    terminalFixedPhiNoDeepRootFace68 H (cubicANumerator68 t r) r
      B D w phi e K j x := by
  classical
  have hXnum : (3 : k[X]) * t - r ^ 2 = H * X0 := by
    rw [show (3 : k[X]) = C (3 : k) from (C_ofNat 3).symm]
    exact hX
  have hapex : (cubicANumerator68 t r).eval x = 0 → r.eval x = 0 :=
    fun hAx => commonTransverse_apex_zero_is_coordinate_zero_68
      H t r X0 (cubicANumerator68 t r) x rfl hXnum hx hAx
  dsimp only [terminalPhiDivisorLowerThirdClassification68] at hclass
  obtain ⟨hloaded, hjets, hcondII, hcondIII, hleft⟩ := hclass
  have hunits : w.eval x ≠ 0 ∨ phi.eval x ≠ 0 ∨ D.eval x ≠ 0 ∨
      K.eval x ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hnodeep hall
  refine ⟨hunits, ?_⟩
  rcases hloaded with hcommon | hII | hIII
  · -- common flavor: convert the apex zero of the loaded pin
    obtain ⟨hF, hG, hpin, hload⟩ := hcommon
    left
    refine ⟨hF, hG, ?_, hload⟩
    rcases hpin with hA0 | hb0 | hk
    · exact Or.inl ⟨hA0, hapex hA0⟩
    · exact Or.inr (Or.inl hb0)
    · exact Or.inr (Or.inr hk)
  · -- component-II flavor: attach the componentII lower row and units
    obtain ⟨hF, hb0, hd0, hload⟩ := hII
    right; left
    have hthree : w.eval x ≠ 0 ∨ phi.eval x ≠ 0 ∨ K.eval x ≠ 0 := by
      by_contra hall
      push_neg at hall
      exact hnodeep ⟨hall.1, hall.2.1, hd0, hall.2.2⟩
    exact ⟨hb0, hd0, hthree, hcondII hb0 hd0, hload⟩
  · -- component-III flavor: exclusive unit pins from the deep-kill negation
    obtain ⟨hG, hw0, hphi0, hsub⟩ := hIII
    have hrow3 := hcondIII hw0 hphi0
    rcases hsub with ⟨hd0, hload⟩ | ⟨hk0, hload⟩
    · -- `D` dies at the root: `K` is a unit and the residual chains
      right; right; left
      have hKne : K.eval x ≠ 0 := fun hK0 =>
        hnodeep ⟨hw0, hphi0, hd0, hK0⟩
      have hcube : 2 * (cubicANumerator68 t r).eval x ^ 2 *
          w.derivative.eval x * B.eval x = 0 := by
        linear_combination hrow3 +
          (12 * (cubicANumerator68 t r).eval x * w.derivative.eval x +
            3 * phi.derivative.eval x) * hd0
      refine ⟨hw0, hphi0, hd0, hKne, hcube, hload, ?_⟩
      rcases eq_or_ne (B.eval x) 0 with hb0 | hbne
      · exact Or.inl hb0
      · have hsel := (hleft hw0 hphi0 hd0).resolve_left hbne
        obtain ⟨hphi', hAW⟩ := hsel
        refine Or.inr ⟨hbne, hphi', ?_, hresid hw0 hphi0 hd0 hbne⟩
        rcases hAW with hA0 | hw'
        · exact Or.inl ⟨hA0, hapex hA0⟩
        · exact Or.inr hw'
    · -- `K` dies at the root: `D` is a unit
      right; right; right
      have hDne : D.eval x ≠ 0 := fun hD0 =>
        hnodeep ⟨hw0, hphi0, hD0, hk0⟩
      have hjet1 := (terminalI4JetPacket68_componentIII B D w phi x
        hw0 hphi0 hjets).1
      exact ⟨hw0, hphi0, hk0, hDne, hjet1, hrow3, hload⟩

end FixedPhiEarlyGeometricAlgebra68

section FixedPhiEarlyGeometricSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]
  {p q : k[X][X]} {j : k}

/-- Consumed no-deep-root leaf: the two simple core roots are produced
explicitly with their exhaustiveness certificate, and every core root
carries the refined loaded face. -/
def terminalFixedPhiNoDeepRootConsumed68
    (p : k[X][X]) (r t B D w phi K : k[X]) (j : k) : Prop :=
  ∃ a c : k, c ≠ a ∧ H.eval a = 0 ∧ H.eval c = 0 ∧
    (∀ x : k, H.eval x = 0 → x = a ∨ x = c) ∧
    ∀ x : k, H.eval x = 0 →
      terminalFixedPhiNoDeepRootFace68 H (cubicANumerator68 t r) r
        B D w phi
        (terminalEDerivativeNumerator68 H
          (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) t r)) K j x

/-- The fixed-witness root packet turns the bare no-deep-root negation into
the consumed per-root packet. -/
theorem NonsquareAlignedSourceCurveData68.fixedPhiNoDeepRootConsumed_of_transport
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hdeg : H.natDegree = 2)
    (r t X0 Yd B D w phi1 k1 phi K : k[X])
    (T : terminalPhiDivisorSameWitnessSourceTransport68 H S
      r t X0 Yd B D w phi1 k1 phi K)
    (hnodeep : ∀ x : k, H.eval x = 0 →
      ¬ (w.eval x = 0 ∧ phi.eval x = 0 ∧ D.eval x = 0 ∧
        K.eval x = 0)) :
    terminalFixedPhiNoDeepRootConsumed68 H p r t B D w phi K j := by
  classical
  have hroot := S.fixedWitnessRefinedIIIRootPacket (H := H) hdeg
    r t X0 Yd B D w phi1 k1 phi K T
  have hH : H ≠ 0 := H_ne_zero_of_nonsquare68 (H := H)
  have hsimple : ∀ x : k, H.eval x = 0 → H.derivative.eval x ≠ 0 :=
    fun x hx => nonsquare_natDegree_two_derivative_ne_zero hdeg
      NonsquarePolynomial46.not_sq hx
  have hX : C 3 * t - r ^ 2 = H * X0 := T.2.1
  have hdegree : H.degree ≠ 0 := by
    rw [degree_eq_natDegree hH, hdeg]
    decide
  obtain ⟨a, haR⟩ := IsAlgClosed.exists_root H hdegree
  have ha : H.eval a = 0 := IsRoot.eq_zero haR
  obtain ⟨c, hca, hc⟩ := simpleQuadratic_exists_other_root_68 H hdeg
    hsimple a ha
  refine ⟨a, c, hca, ha, hc, ?_, ?_⟩
  · intro z hz
    exact natDegree_two_roots_exhaust_68 H hdeg a c z hca.symm ha hc hz
  · intro x hx
    exact terminalFixedPhi_noDeepRootFace_68 H t r X0 B D w phi
      (terminalEDerivativeNumerator68 H
        (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) t r)) K j x hx hX
      ((hroot x hx).1) ((hroot x hx).2) (hnodeep x hx)

/-- Consumed first common-conjugate matching leaf: the fixed witnesses feed
the existing transverse common consumer and its `Next` refinement without
any tuple reselection. -/
theorem NonsquareAlignedSourceCurveData68.fixedPhiCommonConjugateConsumed_of_transport
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hdeg : H.natDegree = 2)
    (r t X0 Yd B D w phi1 k1 phi K : k[X])
    (T : terminalPhiDivisorSameWitnessSourceTransport68 H S
      r t X0 Yd B D w phi1 k1 phi K)
    (a c : k) (hca : c ≠ a)
    (ha : H.eval a = 0) (hc : H.eval c = 0)
    (hwa : w.eval a = 0) (hphia : phi.eval a = 0)
    (hDa : D.eval a = 0) (hKa : K.eval a = 0)
    (hFc : (cubicANumerator68 t r).eval c * B.eval c -
      3 * D.eval c = 0)
    (hGc : phi.eval c + 2 * (cubicANumerator68 t r).eval c *
      w.eval c = 0) :
    terminalRefinedIIIConjugateCommonTransverseNext68 H
      (cubicANumerator68 t r) B D w phi
      (terminalEDerivativeNumerator68 H
        (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) t r)) K j a c := by
  classical
  have hroot := S.fixedWitnessRefinedIIIRootPacket (H := H) hdeg
    r t X0 Yd B D w phi1 k1 phi K T
  have hsimple : ∀ x : k, H.eval x = 0 → H.derivative.eval x ≠ 0 :=
    fun x hx => nonsquare_natDegree_two_derivative_ne_zero hdeg
      NonsquarePolynomial46.not_sq hx
  obtain ⟨_hp4, _hX, _hY, _hW, _hPhi, _hwitness, hI4, hrow, _hlower⟩ := T
  have hI4' : B * phi + 6 * w * D = 0 := by
    rw [show (6 : k[X]) = C (6 : k) from (C_ofNat 6).symm]
    exact hI4
  have hcls := (hroot a ha).1
  dsimp only [terminalPhiDivisorLowerThirdClassification68] at hcls
  have hsplita := hcls.2.2.2.2 hwa hphia hDa
  have hprev := terminalRefinedIII_conjugateCommon_transverse_68 H
    (cubicANumerator68 t r) B D w phi
    (terminalEDerivativeNumerator68 H
      (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
        (p.coeff 3) t r)) K j a c hdeg hsimple ha hc hca.symm
    hwa hphia hDa hKa hI4' hrow hsplita hFc hGc
  exact terminalRefinedIII_conjugateCommon_transverseNext_68 H
    (cubicANumerator68 t r) B D w phi
    (terminalEDerivativeNumerator68 H
      (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
        (p.coeff 3) t r)) K j a c hdeg hsimple ha hc hca.symm
    hwa hphia hDa hKa hI4' hrow hFc hprev

/-- The fixed geometric split with its two earliest leaves consumed.  The
no-deep-root leaf keeps its literal negation and gains the per-root refined
packet; the common-conjugate leaf keeps its literal matching evaluations and
gains the chained transverse consumer.  The component-III, `H ∣ w`,
`r(a) = 0` and full-selector alternatives are verbatim. -/
def terminalPhiDivisorFixedEarlyGeometricSplit68
    (p : k[X][X]) (r t X0 B D w phi K : k[X]) (j : k) : Prop :=
  ((∀ a : k, H.eval a = 0 →
      ¬ (w.eval a = 0 ∧ phi.eval a = 0 ∧ D.eval a = 0 ∧
        K.eval a = 0)) ∧
    terminalFixedPhiNoDeepRootConsumed68 H p r t B D w phi K j) ∨
    ∃ a c : k,
      c ≠ a ∧ H.eval a = 0 ∧ H.eval c = 0 ∧
      w.eval a = 0 ∧ phi.eval a = 0 ∧ D.eval a = 0 ∧ K.eval a = 0 ∧
      ((((cubicANumerator68 t r).eval c * B.eval c - 3 * D.eval c = 0 ∧
          phi.eval c + 2 * (cubicANumerator68 t r).eval c *
            w.eval c = 0) ∧
         terminalRefinedIIIConjugateCommonTransverseNext68 H
           (cubicANumerator68 t r) B D w phi
           (terminalEDerivativeNumerator68 H
             (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
               (p.coeff 3) t r)) K j a c) ∨
        (w.eval c = 0 ∧ phi.eval c = 0 ∧ H ∣ w ∧ H ∣ phi ∧
          ((D.eval c = 0 ∧ H ∣ D) ∨ (K.eval c = 0 ∧ H ∣ K))) ∨
        H ∣ w ∨ r.eval a = 0 ∨
        Nonempty
          (NonsquareAlignedGeometricSelector68 H p r t X0 B D w phi K j))

/-- Early-geometric refinement of the fixed split on the same witnesses. -/
theorem NonsquareAlignedSourceCurveData68.fixedPhiEarlyGeometricSplit_of_transport
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hdeg : H.natDegree = 2)
    (r t X0 Yd B D w phi1 k1 phi K : k[X])
    (T : terminalPhiDivisorSameWitnessSourceTransport68 H S
      r t X0 Yd B D w phi1 k1 phi K)
    (hgeom : terminalPhiDivisorFixedGeometricSplit68 H p
      r t X0 B D w phi K j) :
    terminalPhiDivisorFixedEarlyGeometricSplit68 H p
      r t X0 B D w phi K j := by
  rcases hgeom with hnodeep | ⟨a, c, hca, ha, hc, hwa, hphia, hDa, hKa,
    hleaf⟩
  · exact Or.inl ⟨hnodeep,
      S.fixedPhiNoDeepRootConsumed_of_transport (H := H) hdeg
        r t X0 Yd B D w phi1 k1 phi K T hnodeep⟩
  · right
    refine ⟨a, c, hca, ha, hc, hwa, hphia, hDa, hKa, ?_⟩
    rcases hleaf with hcommon | hrest
    · exact Or.inl ⟨hcommon,
        S.fixedPhiCommonConjugateConsumed_of_transport (H := H) hdeg
          r t X0 Yd B D w phi1 k1 phi K T a c hca ha hc
          hwa hphia hDa hKa hcommon.1 hcommon.2⟩
    · exact Or.inr hrest

/-- Fixed assembly with the early-geometric split in place of the raw
geometric split; transport and the complete selector consumer are
verbatim. -/
def terminalFixedPhiEarlyGeometricAssembly68
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (r t X0 Yd B D w phi1 k1 : k[X]) : Prop :=
  ∃ phi K : k[X],
    terminalPhiDivisorSameWitnessSourceTransport68 H S
      r t X0 Yd B D w phi1 k1 phi K ∧
    terminalPhiDivisorFixedEarlyGeometricSplit68 H p
      r t X0 B D w phi K j ∧
    ∀ G : NonsquareAlignedGeometricSelector68 H p r t X0 B D w phi K j,
      ∃ I : NonsquareAlignedFinalStableConditionalSourceInputs68 H S,
        terminalRefinedIIIConjugateFinalStableSourceResidual68 H
          I.r I.t I.X0 I.Yd
          (p.coeff 3) (p.coeff 4) (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (cubicANumerator68 I.t I.r) I.B I.D I.w I.phi
          (terminalEDerivativeNumerator68 H
            (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
              (p.coeff 3) I.t I.r)) I.K I.phi1 I.k1
          S.alpha S.gamma S.epsilon S.eta j I.a I.c

/-- The verified fixed assembly upgrades to its early-geometric form on the
same `phi`, `K` witnesses. -/
theorem NonsquareAlignedSourceCurveData68.fixedPhiEarlyGeometricAssembly_of_fixedAssembly
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hdeg : H.natDegree = 2)
    (r t X0 Yd B D w phi1 k1 : k[X])
    (hassembly : terminalFixedPhiFinalAssembly68 H S
      r t X0 Yd B D w phi1 k1) :
    terminalFixedPhiEarlyGeometricAssembly68 H S
      r t X0 Yd B D w phi1 k1 := by
  obtain ⟨phi, K, T, hgeom, hcons⟩ := hassembly
  exact ⟨phi, K, T,
    S.fixedPhiEarlyGeometricSplit_of_transport (H := H) hdeg
      r t X0 Yd B D w phi1 k1 phi K T hgeom, hcons⟩

/-- Fixed-coordinate residual with the early-geometric assembly in the
`H ∣ phi1` branch; the `H ∣ r` and mixed siblings are verbatim. -/
def terminalFixedCoordinateEarlyGeometricResidual68
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (r t X0 Yd B D w phi1 k1 : k[X]) : Prop :=
  H ∣ r ∨
    terminalFixedCoordinateMixed68 H r phi1 B D w
      (terminalEDerivativeNumerator68 H
        (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) t r)) k1 ∨
    terminalFixedPhiEarlyGeometricAssembly68 H S r t X0 Yd B D w phi1 k1

/-- Source-facing early-geometric packet.  The same tuple returned by the
verified fixed assembly is retained in all three branches. -/
theorem NonsquareAlignedSourceCurveData68.fixedCoordinateEarlyGeometricAssemblyPacket
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hdeg : H.natDegree = 2)
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hp6 : p.coeff 6 = H ^ 3) (hq8 : q.coeff 8 = H ^ 4)
    (haligned :
      (4 : k[X]) * p.coeff 5 * H - (3 : k[X]) * q.coeff 7 = 0)
    (hjac : bivariateJacobian p q = C (C j)) (hj : j ≠ 0) :
    ∃ r t X0 Yd B D w phi1 k1 : k[X],
      p.coeff 4 = H * t ∧ C 3 * t - r ^ 2 = H * X0 ∧
      C 27 * p.coeff 3 - r ^ 3 = H * Yd ∧
      B * phi1 + C 6 * H * w * D = 0 ∧
      H * B * w * terminalEDerivativeNumerator68 H
          (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) t r) - D * k1 = C j * H ^ 4 ∧
      H ∣ r * phi1 ∧
      terminalFixedCoordinateEarlyGeometricResidual68 H S
        r t X0 Yd B D w phi1 k1 := by
  obtain ⟨r, t, X0, Yd, B, D, w, phi1, k1,
      hp4, hX, hY, hI4, hrow, hdvd, hres⟩ :=
    S.fixedCoordinateFinalAssemblyPacket (H := H)
      hdeg hp hq hp6 hq8 haligned hjac hj
  refine ⟨r, t, X0, Yd, B, D, w, phi1, k1,
    hp4, hX, hY, hI4, hrow, hdvd, ?_⟩
  rcases hres with hr | hmixed | hphi
  · exact Or.inl hr
  · exact Or.inr (Or.inl hmixed)
  · exact Or.inr (Or.inr
      (S.fixedPhiEarlyGeometricAssembly_of_fixedAssembly (H := H) hdeg
        r t X0 Yd B D w phi1 k1 hphi))

end FixedPhiEarlyGeometricSource68

section NormalizedEarlyGeometricAssembly68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- Normalized aligned-nonsquare handoff to the early-geometric
fixed-coordinate residual.  Identical to the verified fixed-coordinate
assembly except that the `H ∣ phi1` branch carries the consumed
no-deep-root and common-conjugate leaves. -/
theorem normalized68ScaleTwo_alignedNonsquare_fixedPhiEarlyGeometricAssembly
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized68LeadingCoreSource P Q H 2)
    (hnsq : ∀ h0 : k[X], H ≠ h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      (4 : k[X]) * p.coeff 5 * H - (3 : k[X]) * q.coeff 7 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    let _inst : NonsquarePolynomial46 H := ⟨hnsq⟩
    ∃ (j : k) (S : NonsquareAlignedSourceCurveData68 H p q j),
      j ≠ 0 ∧
      ∃ r t X0 Yd B D w phi1 k1 : k[X],
        p.coeff 4 = H * t ∧ C 3 * t - r ^ 2 = H * X0 ∧
        C 27 * p.coeff 3 - r ^ 3 = H * Yd ∧
        B * phi1 + C 6 * H * w * D = 0 ∧
        H * B * w * terminalEDerivativeNumerator68 H
            (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
              (p.coeff 3) t r) - D * k1 = C j * H ^ 4 ∧
        H ∣ r * phi1 ∧
        terminalFixedCoordinateEarlyGeometricResidual68 H S
          r t X0 Yd B D w phi1 k1 := by
  dsimp only
  letI : NonsquarePolynomial46 H := ⟨hnsq⟩
  rcases hsource with
    ⟨_hHne, _hHdegree, hPdegree, hQdegree, hp6, hq8, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
  have hp : p.natDegree = 6 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 8 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  have hp6' : p.coeff 6 = H ^ 3 := by simpa only [p] using hp6
  have hq8' : q.coeff 8 = H ^ 4 := by simpa only [q] using hq8
  have haligned' : (4 : k[X]) * p.coeff 5 * H -
      (3 : k[X]) * q.coeff 7 = 0 := by
    simpa only [p, q] using haligned
  obtain ⟨j, hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q = C (C j) := by
    simpa only [p, q, bivariateJacobian, xderiv, GCD369SourceXDeriv]
      using hjac
  obtain ⟨S⟩ := nonsquareAlignedSourceCurveData68 (H := H) p q j
    hp hq hp6' hq8' haligned' hD
  refine ⟨j, S, hj, ?_⟩
  exact S.fixedCoordinateEarlyGeometricAssemblyPacket (H := H)
    _hHdegree hp hq hp6' hq8' haligned' hjac hj

end NormalizedEarlyGeometricAssembly68

end Max11DegreeRoutes
