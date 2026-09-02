import Sol68ScaleTwoAlignedNonsquareSourceSelectorAssemblyScratch

/-! # Refined-III root packet on the fixed source witnesses

The older refined theorem hid its quotient witnesses behind a second
existential.  Here the same root classification is reconstructed directly
from the verified source-transport packet, eliminating that API mismatch by
proof rather than by witness reselection.
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

section FixedWitnessRefinedPacket68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]
  {p q : k[X][X]} {j : k}

/-- The loaded classification and its refined component-III consequence,
proved for the literal witnesses of `T`. -/
theorem NonsquareAlignedSourceCurveData68.fixedWitnessRefinedIIIRootPacket
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hdeg : H.natDegree = 2)
    (r t X0 Yd B D w phi1 k1 phi K : k[X])
    (T : terminalPhiDivisorSameWitnessSourceTransport68 H S
      r t X0 Yd B D w phi1 k1 phi K) :
    let E0 := cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
      (p.coeff 3) t r
    let eDot := terminalEDerivativeNumerator68 H E0
    ∀ a : k, H.eval a = 0 →
      terminalPhiDivisorLowerThirdClassification68
        ((cubicANumerator68 t r).eval a) (H.derivative.eval a)
        (6 * j * H.derivative.eval a ^ 3) B D w phi eDot K a ∧
      (w.eval a = 0 → phi.eval a = 0 → D.eval a = 0 →
        B.eval a ≠ 0 →
        terminalPhiDivisorRefinedIIIResidual68 r B D w phi eDot K a
          (6 * j * H.derivative.eval a ^ 3)) := by
  rcases T with ⟨_hp4, _hX, _hY, hW, hPhi, _hwitness, hI4, hrow, hlower⟩
  let A0 := cubicANumerator68 t r
  let C0 := cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r
  let E0 := cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
    (p.coeff 3) t r
  let eDot := terminalEDerivativeNumerator68 H E0
  have hH : H ≠ 0 := H_ne_zero_of_nonsquare68 (H := H)
  have hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero hdeg
      NonsquarePolynomial46.not_sq ha
  have hCshape : C0 = C (1 / 3 : k) * A0 ^ 2 +
      H ^ 2 * (C (9 / 4 : k) * w - C (3 / 2 * S.gamma : k)) := by
    apply FaithfulSMul.algebraMap_injective k[X] (RatFunc k)
    have hm := congrArg (algebraMap k[X] (RatFunc k)) hW
    dsimp only [A0, C0, terminalScaledW68] at hm
    simp only [map_add, map_sub, map_mul, map_pow, RatFunc.algebraMap_C,
      map_div₀, map_ofNat, map_one] at hm ⊢
    linear_combination (9 / 4 : RatFunc k) * hm
  have hEshape : E0 = C (1 / 27 : k) * A0 ^ 3 +
      H ^ 2 * (C (3 / 8 : k) * phi + C (3 / 2 : k) * A0 * w -
        C (1 / 2 * S.gamma : k) * A0) -
      C (3 / 4 * S.epsilon : k) * H ^ 3 +
      C (1 / 9 : k) * H ^ 4 * B ^ 2 := by
    apply FaithfulSMul.algebraMap_injective k[X] (RatFunc k)
    have hPm := congrArg (algebraMap k[X] (RatFunc k)) hPhi
    have hCm := congrArg (algebraMap k[X] (RatFunc k)) hCshape
    dsimp only [A0, C0, E0, terminalScaledPhi68] at hPm
    simp only [map_add, map_sub, map_neg, map_mul, map_pow,
      RatFunc.algebraMap_C, map_div₀, map_ofNat, map_one] at hPm hCm ⊢
    linear_combination (3 / 8 : RatFunc k) * hPm +
      (2 / 3 * algebraMap k[X] (RatFunc k) A0) * hCm
  have hfactor := terminalLowerZero_factor_one_68 H A0 (H * B) C0
    (H * D) E0 B D S.alpha S.gamma S.epsilon S.eta rfl rfl
  have hlower1 : terminalLowerZeroOne68 H A0 B C0 D E0
      S.alpha S.gamma S.epsilon S.eta = 0 := by
    have hz : H * terminalLowerZeroOne68 H A0 B C0 D E0
        S.alpha S.gamma S.epsilon S.eta = 0 := by
      rw [← hfactor]
      simpa only [A0, C0, E0] using hlower
    exact (mul_eq_zero.mp hz).resolve_left hH
  dsimp only
  intro a ha
  have hlowshape : terminalLowerZeroOne68 H A0 B
      (C (1 / 3 : k) * A0 ^ 2 +
        H ^ 2 * (C (9 / 4 : k) * w - C (3 / 2 * S.gamma : k))) D
      (C (1 / 27 : k) * A0 ^ 3 +
        H ^ 2 * (C (3 / 8 : k) * phi + C (3 / 2 : k) * A0 * w -
          C (1 / 2 * S.gamma : k) * A0) -
        C (3 / 4 * S.epsilon : k) * H ^ 3 +
        C (1 / 9 : k) * H ^ 4 * B ^ 2)
      S.alpha S.gamma S.epsilon S.eta = 0 := by
    rw [← hCshape, ← hEshape]
    exact hlower1
  have hface := terminalLowerZeroOne_next_split_68 H A0 B D phi w
    S.alpha S.gamma S.epsilon S.eta a ha (hsimple a ha) hlowshape
  have hI4a := congrArg (fun P : k[X] => P.eval a) hI4
  have hrowa := congrArg (fun P : k[X] => P.eval a) hrow
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_ofNat,
    eval_zero, ha, zero_pow, mul_zero] at hI4a hrowa
  have hEroot : E0.eval a = A0.eval a ^ 3 / 27 := by
    have hm := congrArg (fun P : k[X] => P.eval a) hEshape
    simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_ofNat,
      ha, zero_pow, zero_mul, mul_zero, zero_add, add_zero] at hm
    simpa [div_eq_mul_inv, mul_comm] using hm
  have he := terminalEDerivativeNumerator_eval_root_68 H A0 E0 a ha hEroot
  have hrowa0 : B.eval a * w.eval a * eDot.eval a -
      D.eval a * K.eval a = 0 := by
    simpa only [E0, eDot, zero_pow (by norm_num : (3 : Nat) ≠ 0),
      mul_zero] using hrowa
  have hdegenerate := terminalPhiDivisor_degeneracy_68 (A0.eval a)
    (B.eval a) (D.eval a) (w.eval a) (phi.eval a) (eDot.eval a)
    (K.eval a) (H.derivative.eval a) hI4a hrowa0
    (by simpa only [E0, eDot] using he) hface
  have hdiff := congrArg
    (fun P : k[X] => P.derivative.derivative.derivative.eval a) hrow
  simp only [derivative_sub, eval_sub] at hdiff
  rw [terminalThirdTripleAt68_eq B w eDot a,
    terminalThirdPairAt68_eq D K a,
    terminalThirdCoreLoad68_eq H j a ha] at hdiff
  have hloaded := terminalPhiDivisor_loadedDegeneracy_68 (A0.eval a)
    (H.derivative.eval a) (6 * j * H.derivative.eval a ^ 3)
    B D w phi eDot K a hdegenerate hdiff
  have hjets := terminalI4JetPacket68_of_identity B D w phi a hI4
  have hclass : terminalPhiDivisorLowerThirdClassification68
      (A0.eval a) (H.derivative.eval a)
      (6 * j * H.derivative.eval a ^ 3) B D w phi eDot K a := by
    refine ⟨hloaded, hjets, ?_, ?_, ?_⟩
    · intro hb hd
      have hII := terminalI4JetPacket68_componentII B D w phi a hb hd hjets
      exact terminalLowerZeroOne_third_componentII_68 H A0 B D phi w
        S.alpha S.gamma S.epsilon S.eta a ha (hsimple a ha) hb hd hII
        hlowshape
    · intro hw hph
      have hIII := terminalI4JetPacket68_componentIII B D w phi a hw hph hjets
      exact terminalLowerZeroOne_third_componentIII_68 H A0 B D phi w
        S.alpha S.gamma S.epsilon S.eta a ha (hsimple a ha) hw hph hIII
        hlowshape
    · intro hw hph hd
      have hIII := terminalI4JetPacket68_componentIII B D w phi a hw hph hjets
      have hI4first : B.eval a * phi.derivative.eval a = 0 := by
        have hf := hIII.1
        simpa [hd] using hf
      have hlowIII := terminalLowerZeroOne_third_componentIII_68 H A0 B D
        phi w S.alpha S.gamma S.epsilon S.eta a ha (hsimple a ha) hw hph
        hIII hlowshape
      have hlowScalar : 2 * A0.eval a * w.derivative.eval a *
          (A0.eval a * B.eval a) = 0 := by simpa [hd] using hlowIII
      exact terminalLowerZeroOne_third_componentIII_leftZero_split_68
        (A0.eval a) (B.eval a) (w.derivative.eval a)
        (phi.derivative.eval a) hI4first hlowScalar
  refine ⟨hclass, ?_⟩
  intro hw hph hd hbne
  dsimp only [terminalPhiDivisorLowerThirdClassification68] at hclass
  have hrefined := hclass.2.2.2.2 hw hph hd
  rcases hrefined with hb0 | ⟨hphi1a, hAorW⟩
  · exact (hbne hb0).elim
  rcases hAorW with hA0 | hw1
  · left
    dsimp only [A0, cubicANumerator68] at hA0
    have hxa := congrArg (fun P : k[X] => P.eval a) _hX
    simp only [eval_sub, eval_mul, eval_pow, eval_C, eval_ofNat, ha,
      zero_mul] at hxa hA0
    have hrsq : r.eval a ^ 2 = 0 := by
      linear_combination -12 * hA0 + 4 * hxa
    exact sq_eq_zero_iff.mp hrsq
  · right
    have hjets' := hclass.2.1
    have hIII := terminalI4JetPacket68_componentIII B D w phi a hw hph hjets'
    have hsecond := hIII.2.1
    have hphi2a : phi.derivative.derivative.eval a = 0 := by
      simp only [hphi1a, hw1, hd, zero_mul, mul_zero, zero_add, add_zero]
        at hsecond
      exact (mul_eq_zero.mp hsecond).resolve_left hbne
    have hthird := hIII.2.2
    have hI4three : B.eval a * phi.derivative.derivative.derivative.eval a +
        18 * w.derivative.derivative.eval a * D.derivative.eval a = 0 := by
      simp only [hphi1a, hphi2a, hw1, hd, zero_mul, mul_zero, zero_add,
        add_zero] at hthird
      linear_combination hthird
    have htMid := terminalThirdTripleAt68_of_middle_zero B w eDot a hw
    have htDouble := terminalThirdTripleMiddleZeroAt68_of_derivative_zero
      B w eDot a hw1
    have hpLeft := terminalThirdPairAt68_of_left_zero D K a hd
    have hload : terminalThirdTripleMiddleDoubleZeroAt68 B w eDot a -
        terminalThirdPairLeftZeroAt68 D K a =
          6 * j * H.derivative.eval a ^ 3 := by
      rw [← htDouble, ← htMid, ← hpLeft]
      exact hdiff
    exact ⟨hw1, hphi1a, hphi2a, hI4three, hload⟩

/-- What remains after tuple reconciliation is purely the mathematical
root/component selection. -/
structure NonsquareAlignedGeometricSelector68
    (p : k[X][X]) (r t X0 B D w phi K : k[X]) (j : k) where
  a : k
  ha : H.eval a = 0
  hwa : w.eval a = 0
  hphia : phi.eval a = 0
  hDa : D.eval a = 0
  hKa : K.eval a = 0
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

/-- The fixed-witness root theorem supplies exactly the two fields which used
to live behind the mismatched refined existential. -/
def NonsquareAlignedSourceCurveData68.sameWitnessSelector_of_geometric
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hdeg : H.natDegree = 2)
    (r t X0 Yd B D w phi1 k1 phi K : k[X])
    (T : terminalPhiDivisorSameWitnessSourceTransport68 H S
      r t X0 Yd B D w phi1 k1 phi K)
    (G : NonsquareAlignedGeometricSelector68 H p r t X0 B D w phi K j) :
    NonsquareAlignedSameWitnessSelector68 H p r t X0 B D w phi K j := by
  have hroot := S.fixedWitnessRefinedIIIRootPacket (H := H) hdeg
    r t X0 Yd B D w phi1 k1 phi K T
  refine {
    a := G.a
    ha := G.ha
    hwa := G.hwa
    hphia := G.hphia
    hDa := G.hDa
    hKa := G.hKa
    hclass := fun x hx => (hroot x hx).1
    hrefined := fun hBne => (hroot G.a G.ha).2 G.hwa G.hphia G.hDa hBne
    hcomponentII := G.hcomponentII
    hnormalizedF := G.hnormalizedF
    hcommonSelector := G.hcommonSelector }

end FixedWitnessRefinedPacket68

end Max11DegreeRoutes
