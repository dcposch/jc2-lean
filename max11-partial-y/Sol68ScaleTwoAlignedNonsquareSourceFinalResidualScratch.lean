import Sol68ScaleTwoAlignedNonsquareAfterLowerOnePhiDivisorRefinedIIIConjugateFinalStableSourceAssemblyScratch

/-! # Normalized-source handoff to the final aligned-nonsquare residual

The normalized source already constructs `NonsquareAlignedSourceCurveData68`.
The current API does not yet construct, in one provenance-preserving packet,
the selected deep root, its conjugate component-II quotients, and the
lower-zero witnesses required by the final stable assembly.  This file names
that exact missing packet, proves that it is sufficient, and exposes an
unconditional normalized-source residual: nonaligned, square core, the exact
missing packet, or the verified final stable residual.  No monolithic Fable
existential witness packet is used.
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

section FinalStableSourceInput68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]
  {p q : k[X][X]} {j : k}

/-- The exact currently missing source API.  Every field is an argument of
`terminalRefinedIIIConjugateFinalStableSourceAssembly`; no stronger closure
or degree hypothesis is included. -/
structure NonsquareAlignedFinalStableSourceInputs68
    (S : NonsquareAlignedSourceCurveData68 H p q j) where
  t : k[X]
  r : k[X]
  X0 : k[X]
  Yd : k[X]
  b1 : k[X]
  B : k[X]
  D : k[X]
  w : k[X]
  phi : k[X]
  K : k[X]
  D1 : k[X]
  BW : k[X]
  B2 : k[X]
  F3 : k[X]
  phi1 : k[X]
  k1 : k[X]
  a : k
  c : k
  ha : H.eval a = 0
  hc : H.eval c = 0
  hac : a ≠ c
  hwa : w.eval a = 0
  hphia : phi.eval a = 0
  hDa : D.eval a = 0
  hKa : K.eval a = 0
  hb : b1 = H * B
  hW : terminalScaledW68 H (cubicANumerator68 t r)
      (cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r) S.gamma = H ^ 2 * w
  hPhi : terminalScaledPhi68 H (cubicANumerator68 t r) b1
      (cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r)
      (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
        (p.coeff 3) t r) S.gamma S.epsilon = H ^ 2 * phi
  hp4 : p.coeff 4 = H * t
  hX : C 3 * t - r ^ 2 = H * X0
  hY : C 27 * p.coeff 3 - r ^ 3 = H * Yd
  hB : B = (X - C c) ^ 2 * B2
  hF : cubicANumerator68 t r * B - C 3 * D = (X - C c) ^ 3 * F3
  hDshape : D = H * D1
  hBWshape : B * w = H * BW
  hI4q : B * phi + C 6 * H * w * D1 = 0
  hrowq : BW * terminalEDerivativeNumerator68 H
      (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
        (p.coeff 3) t r) - D1 * K = C j * H ^ 2
  hI4 : B * phi + C 6 * w * D = 0
  hrow : B * w * terminalEDerivativeNumerator68 H
      (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
        (p.coeff 3) t r) - D * K = C j * H ^ 3
  hnormalized :
    3 * H.derivative.eval c * F3.eval c =
      (2 * (cubicANumerator68 t r).eval c *
          H.derivative.derivative.eval c +
        3 * H.derivative.eval c *
          (cubicANumerator68 t r).derivative.eval c) * B2.eval c
  hwitness : terminalRefinedIIIConjugateRDivisorPreDivisionWitnesses68
    H phi K phi1 k1
  hlower : terminalLowerZeroCleared68 H (cubicANumerator68 t r) (H * B)
    (cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r) (H * D)
    (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
      (p.coeff 3) t r) S.alpha S.gamma S.epsilon S.eta = 0
  hinventory : terminalRefinedIIIConjugateCommonIIResidual68 H
    (cubicANumerator68 t r) B D w phi
    (terminalEDerivativeNumerator68 H
      (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
        (p.coeff 3) t r)) K r j a c
  hcoordinate : terminalRefinedIIIConjugateCoordinateResidual68 H t r X0
    B D w phi
    (terminalEDerivativeNumerator68 H
      (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
        (p.coeff 3) t r)) K a c (6 * j * H.derivative.eval a ^ 3)

/-- The named source-input packet is exactly sufficient for the final stable
residual, with no witness reselection. -/
theorem NonsquareAlignedSourceCurveData68.finalStableSourceResidual_of_inputs
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hdeg : H.natDegree = 2) (hj : j ≠ 0)
    (I : NonsquareAlignedFinalStableSourceInputs68 H S) :
    terminalRefinedIIIConjugateFinalStableSourceResidual68 H I.r I.t I.X0 I.Yd
      (p.coeff 3) (p.coeff 4) (p.coeff 0) (p.coeff 1) (p.coeff 2)
      (cubicANumerator68 I.t I.r) I.B I.D I.w I.phi
      (terminalEDerivativeNumerator68 H
        (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) I.t I.r)) I.K I.phi1 I.k1
      S.alpha S.gamma S.epsilon S.eta j I.a I.c := by
  exact S.terminalRefinedIIIConjugateFinalStableSourceAssembly (H := H)
    I.t I.r I.X0 I.Yd
    (cubicCNumerator68 H (p.coeff 2) (p.coeff 3) I.t I.r)
    (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
      (p.coeff 3) I.t I.r)
    I.b1 I.B I.D I.w I.phi I.K I.D1 I.BW I.B2 I.F3 I.phi1 I.k1
    I.a I.c hdeg I.ha I.hc I.hac I.hwa I.hphia I.hDa I.hKa I.hb
    I.hW I.hPhi I.hp4 I.hX I.hY rfl rfl I.hB I.hF I.hDshape
    I.hBWshape I.hI4q I.hrowq I.hI4 I.hrow I.hnormalized hj
    I.hwitness I.hlower I.hinventory I.hcoordinate

end FinalStableSourceInput68

section NormalizedSourceFinalResidual68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- Narrow aligned-nonsquare normalized-source residual.  The source bridge
is complete; the only API boundary is construction of the named stable-input
packet. -/
theorem normalized68ScaleTwo_alignedNonsquare_sourceFinalResidual
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
      (¬ Nonempty (NonsquareAlignedFinalStableSourceInputs68 H S) ∨
        ∃ I : NonsquareAlignedFinalStableSourceInputs68 H S,
          terminalRefinedIIIConjugateFinalStableSourceResidual68 H
            I.r I.t I.X0 I.Yd
            (p.coeff 3) (p.coeff 4) (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (cubicANumerator68 I.t I.r) I.B I.D I.w I.phi
            (terminalEDerivativeNumerator68 H
              (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
                (p.coeff 3) I.t I.r)) I.K I.phi1 I.k1
            S.alpha S.gamma S.epsilon S.eta j I.a I.c) := by
  dsimp only
  letI : NonsquarePolynomial46 H := ⟨hnsq⟩
  obtain ⟨j, hj, ⟨S⟩⟩ :=
    normalized68ScaleTwo_alignedNonsquare_quadraticSourceData
      hsource hnsq haligned
  refine ⟨j, S, hj, ?_⟩
  classical
  by_cases hinput : Nonempty (NonsquareAlignedFinalStableSourceInputs68 H S)
  · right
    obtain ⟨I⟩ := hinput
    exact ⟨I, S.finalStableSourceResidual_of_inputs (H := H)
      hsource.2.1 hj I⟩
  · exact Or.inl hinput

/-- Full normalized scale-two source handoff.  The nonaligned and square-core
siblings are preserved literally; only the aligned nonsquare chamber enters
the source packet above. -/
theorem normalized68ScaleTwo_sourceFinalResidual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized68LeadingCoreSource P Q H 2) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    let N := (4 : k[X]) * p.coeff 5 * H - (3 : k[X]) * q.coeff 7
    N ≠ 0 ∨ (∃ h0 : k[X], H = h0 ^ 2) ∨
      ∃ hnsq : ∀ h0 : k[X], H ≠ h0 ^ 2,
        let _inst : NonsquarePolynomial46 H := ⟨hnsq⟩
        ∃ (j : k) (S : NonsquareAlignedSourceCurveData68 H p q j),
          j ≠ 0 ∧
          (¬ Nonempty (NonsquareAlignedFinalStableSourceInputs68 H S) ∨
            ∃ I : NonsquareAlignedFinalStableSourceInputs68 H S,
              terminalRefinedIIIConjugateFinalStableSourceResidual68 H
                I.r I.t I.X0 I.Yd
                (p.coeff 3) (p.coeff 4) (p.coeff 0) (p.coeff 1)
                (p.coeff 2) (cubicANumerator68 I.t I.r)
                I.B I.D I.w I.phi
                (terminalEDerivativeNumerator68 H
                  (cubicENumerator68 H (p.coeff 0) (p.coeff 1)
                    (p.coeff 2) (p.coeff 3) I.t I.r)) I.K I.phi1 I.k1
                S.alpha S.gamma S.epsilon S.eta j I.a I.c) := by
  dsimp only
  by_cases hnonaligned :
      (4 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5 * H -
        (3 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7 ≠ 0
  · exact Or.inl hnonaligned
  right
  by_cases hsquare : ∃ h0 : k[X], H = h0 ^ 2
  · exact Or.inl hsquare
  right
  have hnsq : ∀ h0 : k[X], H ≠ h0 ^ 2 := by
    intro h0 hsq
    exact hsquare ⟨h0, hsq⟩
  have haligned :
      (4 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5 * H -
        (3 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7 = 0 :=
    not_ne_iff.mp hnonaligned
  refine ⟨hnsq, ?_⟩
  exact normalized68ScaleTwo_alignedNonsquare_sourceFinalResidual
    hsource hnsq haligned

end NormalizedSourceFinalResidual68

end Max11DegreeRoutes
