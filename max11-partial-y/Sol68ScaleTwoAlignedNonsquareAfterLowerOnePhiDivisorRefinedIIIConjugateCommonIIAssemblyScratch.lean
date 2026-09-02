import Sol68ScaleTwoAlignedNonsquareAfterLowerOnePhiDivisorRefinedIIIConjugateIIAssemblyScratch
import Fable68ScaleTwoRefinedIIIConjugateCommonTransverseNextScratch

/-! # Merged common-or-component-II conjugate reduction -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 5000000

section RefinedIIIConjugateCommonIIAlgebra68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- Exact surviving inventory after the common and component-II routes are
merged.  Component III is retained verbatim from conjugate matching. -/
def terminalRefinedIIIConjugateCommonIIResidual68
    (H A b D w phi e K r : k[X]) (j a c : k) : Prop :=
  r.eval c = 0 ∨
    terminalRefinedIIIConjugateCommonTransverseNext68
      H A b D w phi e K j a c ∨
    (w.eval c = 0 ∧ phi.eval c = 0 ∧ H ∣ w ∧ H ∣ phi ∧
      ((D.eval c = 0 ∧ H ∣ D) ∨ (K.eval c = 0 ∧ H ∣ K)))

/-- Pure merger of the exact conjugate matching allocation.  Repeated common
leaves from component II are sent through the same common-transverse packet;
the coordinate leaf and the two component-III allocations remain distinct. -/
theorem terminalRefinedIII_conjugate_commonII_inventory_68
    (H A b D w phi e K r : k[X]) (j a c : k)
    (hmatch : terminalRefinedIIIConjugateMatching68
      H A b D w phi e K j c)
    (hcommon : A.eval c * b.eval c - 3 * D.eval c = 0 →
      phi.eval c + 2 * A.eval c * w.eval c = 0 →
      terminalRefinedIIIConjugateCommonTransverseNext68
        H A b D w phi e K j a c)
    (hII : b.eval c = 0 ∧ D.eval c = 0 ∧ H ∣ D →
      r.eval c = 0 ∨
        terminalRefinedIIIConjugateCommonTransverseNext68
          H A b D w phi e K j a c) :
    terminalRefinedIIIConjugateCommonIIResidual68
      H A b D w phi e K r j a c := by
  rcases hmatch.2 with hC | hrest
  · exact Or.inr (Or.inl (hcommon hC.1 hC.2))
  rcases hrest with hCII | hCIII
  · rcases hII hCII with hr | hnext
    · exact Or.inl hr
    · exact Or.inr (Or.inl hnext)
  · exact Or.inr (Or.inr hCIII)

end RefinedIIIConjugateCommonIIAlgebra68

section RefinedIIIConjugateCommonIIExactFaces68

variable {k : Type*} [Field k] [CharZero k]

/-- Exact `G`-face behind the nonmultiplicity loaded child. -/
theorem terminalRefinedIII_normalized_loaded_factor_I4_G_68
    (H A B D w phi D1 B2 F3 M D2 : k[X]) (c : k)
    (hHM : H = (X - C c) * M)
    (hMc : M.eval c = H.derivative.eval c)
    (hB : B = (X - C c) ^ 2 * B2)
    (hD2 : D1 = (X - C c) * D2)
    (hDcore : C 3 * M * D2 = A * B2 - (X - C c) * F3)
    (hI4 : B * phi + C 6 * H * w * D1 = 0)
    (hB2ne : B2.eval c ≠ 0) :
    phi.eval c + 2 * A.eval c * w.eval c = 0 := by
  let L : k[X] := X - C c
  have hL : L ≠ 0 := X_sub_C_ne_zero c
  change H = L * M at hHM
  change B = L ^ 2 * B2 at hB
  change D1 = L * D2 at hD2
  have hI4q : B2 * phi + C 6 * M * w * D2 = 0 := by
    rw [hB, hHM, hD2] at hI4
    have hz : L ^ 2 * (B2 * phi + C 6 * M * w * D2) = 0 := by
      linear_combination hI4
    exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero 2 hL)
  have hDroot : 3 * H.derivative.eval c * D2.eval c =
      A.eval c * B2.eval c := by
    have hd := congrArg (fun P : k[X] => P.eval c) hDcore
    simp only [eval_sub, eval_mul, eval_X, eval_C, sub_self, zero_mul,
      eval_C] at hd
    simpa only [hMc, sub_zero] using hd
  have hI4root : B2.eval c * phi.eval c +
      6 * H.derivative.eval c * w.eval c * D2.eval c = 0 := by
    have hi := congrArg (fun P : k[X] => P.eval c) hI4q
    simp only [eval_add, eval_mul, eval_C, eval_ofNat, eval_zero] at hi
    simpa only [hMc] using hi
  have hprod : B2.eval c *
      (phi.eval c + 2 * A.eval c * w.eval c) = 0 := by
    linear_combination hI4root - 2 * w.eval c * hDroot
  exact (mul_eq_zero.mp hprod).resolve_left hB2ne

end RefinedIIIConjugateCommonIIExactFaces68

section RefinedIIIConjugateCommonIISource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- The component-II source chain with its common output kept as exact `F`
and `G` faces, rather than hidden inside the broader degeneracy type. -/
theorem NonsquareAlignedSourceCurveData68.terminalRefinedIIIConjugateIIExactFaces
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (t r X0 C0 E0 b1 B D w phi K D1 BW B2 F3 : k[X]) (c : k)
    (hb : b1 = H * B)
    (hW : terminalScaledW68 H (cubicANumerator68 t r) C0 S.gamma =
      H ^ 2 * w)
    (hPhi : terminalScaledPhi68 H (cubicANumerator68 t r) b1 C0 E0
      S.gamma S.epsilon = H ^ 2 * phi)
    (hX : C 3 * t - r ^ 2 = H * X0)
    (hc : H.eval c = 0) (hh : H.derivative.eval c ≠ 0) (hj : j ≠ 0)
    (hB : B = (X - C c) ^ 2 * B2)
    (hF : cubicANumerator68 t r * B - C 3 * D =
      (X - C c) ^ 3 * F3)
    (hDshape : D = H * D1)
    (hBWshape : B * w = H * BW)
    (hI4 : B * phi + C 6 * H * w * D1 = 0)
    (hrow : BW * terminalEDerivativeNumerator68 H E0 - D1 * K =
      C j * H ^ 2)
    (hnormalized :
      3 * H.derivative.eval c * F3.eval c =
        (2 * (cubicANumerator68 t r).eval c *
            H.derivative.derivative.eval c +
          3 * H.derivative.eval c *
            (cubicANumerator68 t r).derivative.eval c) * B2.eval c) :
    r.eval c = 0 ∨
      ((cubicANumerator68 t r).eval c * B.eval c -
          3 * D.eval c = 0 ∧
        phi.eval c + 2 * (cubicANumerator68 t r).eval c * w.eval c = 0) := by
  obtain ⟨_, M, D2, BW1, hHM, hMc, hD2, hBW1, hDcore,
      hBWcore, hrow1, hsplit⟩ :=
    S.terminalRefinedIIIConjugateIIFLoadedRoutingPacket (H := H)
      t r X0 C0 E0 b1 B D w phi K D1 BW B2 F3 c hb hW hPhi hX
      hc hh hB hF hDshape hBWshape hrow hnormalized
  have hF0 : (cubicANumerator68 t r).eval c * B.eval c -
      3 * D.eval c = 0 := by
    have hf := congrArg (fun P : k[X] => P.eval c) hF
    simp [eval_sub, eval_mul, eval_pow, eval_X, eval_C] at hf
    exact hf
  rcases hsplit with hB2 | hrOrFactor
  · right
    have hpacket := S.terminalRefinedIIIConjugateIIFB2MultiplicityPacket
      (H := H) t r X0 C0 E0 b1 B D w phi K D1 BW B2 F3 c hb hW
      hPhi hX hc hh hB hF hDshape hBWshape hrow hnormalized hB2
    exact ⟨hF0, terminalRefinedIII_B2_multiplicity_I4_common_68 H
      (cubicANumerator68 t r) B D w phi
        (terminalEDerivativeNumerator68 H E0) K D1 BW B2 F3 j c
        hh hj hI4 hpacket⟩
  rcases hrOrFactor with hr | hfactor
  · exact Or.inl hr
  · by_cases hB2zero : B2.eval c = 0
    · right
      have hpacket := S.terminalRefinedIIIConjugateIIFB2MultiplicityPacket
        (H := H) t r X0 C0 E0 b1 B D w phi K D1 BW B2 F3 c hb hW
        hPhi hX hc hh hB hF hDshape hBWshape hrow hnormalized hB2zero
      exact ⟨hF0, terminalRefinedIII_B2_multiplicity_I4_common_68 H
        (cubicANumerator68 t r) B D w phi
          (terminalEDerivativeNumerator68 H E0) K D1 BW B2 F3 j c
          hh hj hI4 hpacket⟩
    · right
      exact ⟨hF0, terminalRefinedIII_normalized_loaded_factor_I4_G_68 H
        (cubicANumerator68 t r) B D w phi D1 B2 F3 M D2 c
        hHM hMc hB hD2 hDcore hI4 hB2zero⟩

/-- Source-facing merger with the verified common-transverse refinement.
Every component-II leaf becomes either the existing coordinate sibling or
the same common packet used by a genuine common conjugate allocation. -/
theorem NonsquareAlignedSourceCurveData68.terminalRefinedIIIConjugateIIIntoCommonTransverseNext
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (t r X0 C0 E0 b1 B D w phi K D1 BW B2 F3 : k[X]) (a c : k)
    (hdeg : H.natDegree = 2)
    (ha : H.eval a = 0) (hc : H.eval c = 0) (hac : a ≠ c)
    (hwa : w.eval a = 0) (hphia : phi.eval a = 0)
    (hDa : D.eval a = 0) (hKa : K.eval a = 0)
    (hb : b1 = H * B)
    (hW : terminalScaledW68 H (cubicANumerator68 t r) C0 S.gamma =
      H ^ 2 * w)
    (hPhi : terminalScaledPhi68 H (cubicANumerator68 t r) b1 C0 E0
      S.gamma S.epsilon = H ^ 2 * phi)
    (hX : C 3 * t - r ^ 2 = H * X0)
    (hB : B = (X - C c) ^ 2 * B2)
    (hF : cubicANumerator68 t r * B - C 3 * D =
      (X - C c) ^ 3 * F3)
    (hDshape : D = H * D1)
    (hBWshape : B * w = H * BW)
    (hI4q : B * phi + C 6 * H * w * D1 = 0)
    (hrowq : BW * terminalEDerivativeNumerator68 H E0 - D1 * K =
      C j * H ^ 2)
    (hI4 : B * phi + C 6 * w * D = 0)
    (hrow : B * w * terminalEDerivativeNumerator68 H E0 - D * K =
      C j * H ^ 3)
    (hsplita : B.eval a = 0 ∨
      (phi.derivative.eval a = 0 ∧
        ((cubicANumerator68 t r).eval a = 0 ∨ w.derivative.eval a = 0)))
    (hnormalized :
      3 * H.derivative.eval c * F3.eval c =
        (2 * (cubicANumerator68 t r).eval c *
            H.derivative.derivative.eval c +
          3 * H.derivative.eval c *
            (cubicANumerator68 t r).derivative.eval c) * B2.eval c)
    (hj : j ≠ 0) :
    r.eval c = 0 ∨
      terminalRefinedIIIConjugateCommonTransverseNext68 H
        (cubicANumerator68 t r) B D w phi
        (terminalEDerivativeNumerator68 H E0) K j a c := by
  have hsimple : ∀ x : k, H.eval x = 0 → H.derivative.eval x ≠ 0 :=
    fun x hx => nonsquare_natDegree_two_derivative_ne_zero hdeg
      NonsquarePolynomial46.not_sq hx
  have hfaces := S.terminalRefinedIIIConjugateIIExactFaces (H := H)
    t r X0 C0 E0 b1 B D w phi K D1 BW B2 F3 c hb hW hPhi hX
    hc (hsimple c hc) hj hB hF hDshape hBWshape hI4q hrowq hnormalized
  rcases hfaces with hr | hcommon
  · exact Or.inl hr
  · right
    have hprev := terminalRefinedIII_conjugateCommon_transverse_68 H
      (cubicANumerator68 t r) B D w phi
      (terminalEDerivativeNumerator68 H E0) K j a c hdeg hsimple
      ha hc hac hwa hphia hDa hKa hI4 hrow hsplita hcommon.1 hcommon.2
    exact terminalRefinedIII_conjugateCommon_transverseNext_68 H
      (cubicANumerator68 t r) B D w phi
      (terminalEDerivativeNumerator68 H E0) K j a c hdeg hsimple
      ha hc hac hwa hphia hDa hKa hI4 hrow hcommon.1 hprev

end RefinedIIIConjugateCommonIISource68

end Max11DegreeRoutes
