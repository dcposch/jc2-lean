import Sol68ScaleTwoAlignedNonsquareSourceFixedCoordinateSplitScratch

/-! # Fixed-coordinate source assembly

This file connects the provenance-preserving coordinate split to the existing
selector and final-stable consumer.  The `H ∣ r` and mixed-root siblings are
retained literally; neither is replaced by an unrelated source existential.
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

section FixedPhiFinalAssembly68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]
  {p q : k[X][X]} {j : k}

/-- The fixed `H ∣ phi1` source packet, together with its exhaustive geometric
inventory and an explicit consumer for every occurrence of the complete
geometric selector. -/
def terminalFixedPhiFinalAssembly68
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (r t X0 Yd B D w phi1 k1 : k[X]) : Prop :=
  ∃ phi K : k[X],
    terminalPhiDivisorSameWitnessSourceTransport68 H S
      r t X0 Yd B D w phi1 k1 phi K ∧
    terminalPhiDivisorFixedGeometricSplit68 H p r t X0 B D w phi K j ∧
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

/-- Main fixed-coordinate residual after connecting its only complete selector
leaf to the final-stable source consumer. -/
def terminalFixedCoordinateFinalAssemblyResidual68
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (r t X0 Yd B D w phi1 k1 : k[X]) : Prop :=
  H ∣ r ∨
    terminalFixedCoordinateMixed68 H r phi1 B D w
      (terminalEDerivativeNumerator68 H
        (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) t r)) k1 ∨
    terminalFixedPhiFinalAssembly68 H S r t X0 Yd B D w phi1 k1

theorem NonsquareAlignedSourceCurveData68.fixedPhiFinalAssembly_of_transport
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hdeg : H.natDegree = 2) (hj : j ≠ 0)
    (r t X0 Yd B D w phi1 k1 phi K : k[X])
    (T : terminalPhiDivisorSameWitnessSourceTransport68 H S
      r t X0 Yd B D w phi1 k1 phi K)
    (hgeom : terminalPhiDivisorFixedGeometricSplit68 H p
      r t X0 B D w phi K j) :
    terminalFixedPhiFinalAssembly68 H S r t X0 Yd B D w phi1 k1 := by
  refine ⟨phi, K, T, hgeom, ?_⟩
  intro G
  let R := S.sameWitnessSelector_of_geometric (H := H) hdeg
    r t X0 Yd B D w phi1 k1 phi K T G
  obtain ⟨I⟩ := S.conditionalFinalInputs_of_sameWitnessSelector (H := H)
    hdeg hj r t X0 Yd B D w phi1 k1 phi K T R
  exact ⟨I, S.finalStableSourceResidual_of_conditional_inputs
    (H := H) hdeg hj I⟩

/-- Source-facing fixed assembly.  The same tuple returned by the coordinate
split is retained in all three branches. -/
theorem NonsquareAlignedSourceCurveData68.fixedCoordinateFinalAssemblyPacket
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
      terminalFixedCoordinateFinalAssemblyResidual68 H S
        r t X0 Yd B D w phi1 k1 := by
  obtain ⟨r, t, X0, Yd, B, D, w, phi1, k1,
      hp4, hX, hY, hI4, hrow, hdvd, hres⟩ :=
    S.fixedCoordinateComprehensivePacket (H := H)
      hdeg hp hq hp6 hq8 haligned hjac hj
  refine ⟨r, t, X0, Yd, B, D, w, phi1, k1,
    hp4, hX, hY, hI4, hrow, hdvd, ?_⟩
  rcases hres with hr | hmixed | hphi
  · exact Or.inl hr
  · exact Or.inr (Or.inl hmixed)
  · right
    right
    obtain ⟨phi, K, T, hgeom⟩ := hphi
    exact S.fixedPhiFinalAssembly_of_transport (H := H) hdeg hj
      r t X0 Yd B D w phi1 k1 phi K T hgeom

end FixedPhiFinalAssembly68

section NormalizedFixedAssembly68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- Normalized aligned-nonsquare handoff to the authoritative fixed-coordinate
residual.  Unlike the older final-source wrapper, this theorem has no missing
source-selector existential: the only remaining alternatives are explicit
mathematical branches. -/
theorem normalized68ScaleTwo_alignedNonsquare_fixedCoordinateAssembly
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
        terminalFixedCoordinateFinalAssemblyResidual68 H S
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
  exact S.fixedCoordinateFinalAssemblyPacket (H := H)
    _hHdegree hp hq hp6' hq8' haligned' hjac hj

end NormalizedFixedAssembly68

end Max11DegreeRoutes
