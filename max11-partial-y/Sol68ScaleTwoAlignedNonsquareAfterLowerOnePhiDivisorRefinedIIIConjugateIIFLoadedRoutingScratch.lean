import Sol68ScaleTwoAlignedNonsquareAfterLowerOnePhiDivisorRefinedIIIConjugateIIFNormalizedLoadedScratch

/-! # Routing the two finite leaves of the normalized conjugate F packet -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 5000000

section RefinedIIIConjugateIIFLoadedRoutingAlgebra68

variable {k : Type*} [Field k] [CharZero k]

/-- The part of the common loaded component which is already forced on the
normalized component-II leaf.  The separate common `G` face is deliberately
not included: it is not a consequence of the normalized loaded quotient. -/
def terminalRefinedIIIConjugateCommonLoadedFactor68
    (H A B D w K : k[X]) (c : k) : Prop :=
  A.eval c * B.eval c - 3 * D.eval c = 0 ∧
    H.derivative.eval c * A.eval c ^ 2 * w.eval c + 3 * K.eval c = 0

/-- At a core root, vanishing of the actual cubic `A` numerator routes to the
existing coordinate locus `r(c)=0`. -/
theorem cubicANumerator_root_zero_forces_r_root_68
    (H t r X : k[X]) (c : k)
    (hc : H.eval c = 0)
    (hX : C 3 * t - r ^ 2 = H * X)
    (hA : (cubicANumerator68 t r).eval c = 0) :
    r.eval c = 0 := by
  dsimp only [cubicANumerator68] at hA
  have hxa := congrArg (fun P : k[X] => P.eval c) hX
  simp only [eval_sub, eval_mul, eval_pow, eval_C, eval_ofNat, hc,
    zero_mul] at hxa hA
  have hrsq : r.eval c ^ 2 = 0 := by
    linear_combination -12 * hA + 4 * hxa
  exact sq_eq_zero_iff.mp hrsq

/-- The normalized loaded split has only one genuine higher-multiplicity
child.  Its `A=0` child is the coordinate locus, and its loaded child is the
common `F` plus loaded scalar face. -/
theorem terminalRefinedIII_normalized_loaded_route_68
    (H t r X A B D w K B2 : k[X]) (c : k)
    (hc : H.eval c = 0)
    (hX : C 3 * t - r ^ 2 = H * X)
    (hA : A = cubicANumerator68 t r)
    (hB0 : B.eval c = 0) (hD0 : D.eval c = 0)
    (hsplit : B2.eval c = 0 ∨ A.eval c = 0 ∨
      H.derivative.eval c * A.eval c ^ 2 * w.eval c +
        3 * K.eval c = 0) :
    B2.eval c = 0 ∨ r.eval c = 0 ∨
      terminalRefinedIIIConjugateCommonLoadedFactor68 H A B D w K c := by
  rcases hsplit with hB2 | hAorLoad
  · exact Or.inl hB2
  rcases hAorLoad with hA0 | hload
  · right; left
    apply cubicANumerator_root_zero_forces_r_root_68 H t r X c hc hX
    simpa only [hA] using hA0
  · right; right
    exact ⟨by simp [hB0, hD0], hload⟩

/-- If the independently retained common `G` face is available, the loaded
factor above is exactly the three scalar faces of the common degeneracy. -/
theorem terminalRefinedIII_common_loaded_face_of_factor_68
    (H A B D w phi K : k[X]) (c : k)
    (hfactor : terminalRefinedIIIConjugateCommonLoadedFactor68
      H A B D w K c)
    (hG : phi.eval c + 2 * A.eval c * w.eval c = 0) :
    (A.eval c * B.eval c - 3 * D.eval c = 0) ∧
      (phi.eval c + 2 * A.eval c * w.eval c = 0) ∧
      (H.derivative.eval c * A.eval c ^ 2 * w.eval c +
        3 * K.eval c = 0) :=
  ⟨hfactor.1, hG, hfactor.2⟩

end RefinedIIIConjugateIIFLoadedRoutingAlgebra68

section RefinedIIIConjugateIIFLoadedRoutingSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Actual-source routing of the normalized loaded packet.  All three local
quotient identities are retained; only the finite scalar split is sharpened.
The sole unresolved multiplicity child is `B2(c)=0`. -/
theorem NonsquareAlignedSourceCurveData68.terminalRefinedIIIConjugateIIFLoadedRoutingPacket
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (t r X0 C0 E0 b1 B D w phi K D1 BW B2 F3 : k[X]) (c : k)
    (hb : b1 = H * B)
    (hW : terminalScaledW68 H (cubicANumerator68 t r) C0 S.gamma =
      H ^ 2 * w)
    (hPhi : terminalScaledPhi68 H (cubicANumerator68 t r) b1 C0 E0
      S.gamma S.epsilon = H ^ 2 * phi)
    (hX : C 3 * t - r ^ 2 = H * X0)
    (hc : H.eval c = 0) (hh : H.derivative.eval c ≠ 0)
    (hB : B = (X - C c) ^ 2 * B2)
    (hF : cubicANumerator68 t r * B - C 3 * D =
      (X - C c) ^ 3 * F3)
    (hDshape : D = H * D1)
    (hBWshape : B * w = H * BW)
    (hrow : BW * terminalEDerivativeNumerator68 H E0 - D1 * K =
      C j * H ^ 2)
    (hnormalized :
      3 * H.derivative.eval c * F3.eval c =
        (2 * (cubicANumerator68 t r).eval c *
            H.derivative.derivative.eval c +
          3 * H.derivative.eval c *
            (cubicANumerator68 t r).derivative.eval c) * B2.eval c) :
    terminalRefinedIIIConjugateIIFNormalizedPacket68 H
        (cubicANumerator68 t r) B D c ∧
      (∃ M D2 BW1 : k[X],
        H = (X - C c) * M ∧ M.eval c = H.derivative.eval c ∧
        D1 = (X - C c) * D2 ∧ BW = (X - C c) * BW1 ∧
        C 3 * M * D2 = cubicANumerator68 t r * B2 -
          (X - C c) * F3 ∧
        M * BW1 = B2 * w ∧
        BW1 * terminalEDerivativeNumerator68 H E0 - D2 * K =
          C j * (X - C c) * M ^ 2 ∧
        (B2.eval c = 0 ∨ r.eval c = 0 ∨
          terminalRefinedIIIConjugateCommonLoadedFactor68 H
            (cubicANumerator68 t r) B D w K c)) := by
  obtain ⟨hnorm, M, D2, BW1, hHM, hMc, hD2, hBW1, hDcore,
      hBWcore, hrow1, hsplit⟩ :=
    S.terminalRefinedIIIConjugateIIFNormalizedLoadedPacket (H := H)
      (cubicANumerator68 t r) C0 E0 b1 B D w phi K D1 BW B2 F3 c
      hb hW hPhi hc hh hB hF hDshape hBWshape hrow hnormalized
  refine ⟨hnorm, M, D2, BW1, hHM, hMc, hD2, hBW1, hDcore,
    hBWcore, hrow1, ?_⟩
  exact terminalRefinedIII_normalized_loaded_route_68 H t r X0
    (cubicANumerator68 t r) B D w K B2 c hc hX rfl
      (by
        have hb0 := congrArg (fun P : k[X] => P.eval c) hB
        simpa only [eval_mul, eval_pow, eval_sub, eval_X, eval_C, sub_self,
          pow_two, zero_mul] using hb0)
      (by
        have hd := congrArg (fun P : k[X] => P.eval c) hDshape
        simpa [hc] using hd)
      hsplit

end RefinedIIIConjugateIIFLoadedRoutingSource68

end Max11DegreeRoutes
