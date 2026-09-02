import Sol68ScaleTwoAlignedNonsquareAfterLowerOnePhiDivisorRefinedIIIConjugateIIScratch

/-! # Coordinate leaves of the conjugate component II -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

section RefinedIIIConjugateIICoordinateAlgebra68

variable {k : Type*} [Field k] [CharZero k]

def terminalRefinedIIIConjugateIIFourthScalar68
    (A b2 w d2 phi : k) : k :=
  -(1 / 3 : k) * A ^ 2 * b2 * w +
    (1 / 2 : k) * A * b2 * phi + 5 * A * d2 * w +
    (1 / 2 : k) * d2 * phi

/-- On the double-zero component-II leaf, the second jet of the reduced
lower-zero row is a simple-root unit times this five-variable scalar. -/
theorem terminalLowerZeroReduced_second_componentII_doubleZero_68
    (H A B D phi w : k[X]) (gamma c : k)
    (hc : H.eval c = 0)
    (hB0 : B.eval c = 0) (hB1 : B.derivative.eval c = 0)
    (hD0 : D.eval c = 0) (hD1 : D.derivative.eval c = 0) :
    (terminalLowerZeroReduced68 H A B D phi w gamma).derivative.derivative.eval c =
      H.derivative.eval c * terminalRefinedIIIConjugateIIFourthScalar68
        (A.eval c) (B.derivative.derivative.eval c) (w.eval c)
        (D.derivative.derivative.eval c) (phi.eval c) := by
  dsimp only [terminalLowerZeroReduced68,
    terminalRefinedIIIConjugateIIFourthScalar68]
  simp only [derivative_add, derivative_sub, derivative_neg, derivative_mul,
    derivative_pow, derivative_C, derivative_ofNat, C_ofNat_poly, eval_add,
    eval_sub, eval_neg, eval_mul, eval_pow, eval_C, eval_ofNat, eval_zero,
    hc, hB0, hB1, hD0, hD1, zero_mul, mul_zero, zero_add, add_zero,
    zero_pow]
  ring

/-- The resultant of divided-I4 order two and the fourth lower-zero scalar is
`w * (A*b₂ - 3*d₂)^2`. -/
theorem terminalRefinedIII_conjugateII_fourth_resultant_68
    (A b2 w d2 phi : k)
    (hI4two : b2 * phi + 6 * w * d2 = 0)
    (hlower : terminalRefinedIIIConjugateIIFourthScalar68
      A b2 w d2 phi = 0) :
    w = 0 ∨ A * b2 - 3 * d2 = 0 := by
  have hres : w * (A * b2 - 3 * d2) ^ 2 = 0 := by
    dsimp only [terminalRefinedIIIConjugateIIFourthScalar68] at hlower
    linear_combination -3 * b2 * hlower + (3 / 2 : k) *
      (A * b2 + d2) * hI4two
  rcases mul_eq_zero.mp hres with hw | hF
  · exact Or.inl hw
  · exact Or.inr (sq_eq_zero_iff.mp hF)

def terminalRefinedIIIConjugateIICoordinateRefinement68
    (H A B D w phi : k[X]) (c : k) : Prop :=
  ((A.eval c * B.derivative.eval c -
        3 * H.derivative.eval c *
          (D.derivative.eval c / H.derivative.eval c) = 0) ∧
      (phi.eval c + 2 * A.eval c * w.eval c = 0)) ∨
    ((A.eval c * B.derivative.eval c -
        3 * H.derivative.eval c *
          (D.derivative.eval c / H.derivative.eval c) = 0) ∧
      B.derivative.eval c = 0 ∧
      (H ∣ w ∨
        A.eval c * B.derivative.derivative.eval c -
          3 * D.derivative.derivative.eval c = 0)) ∨
    ((phi.eval c + 2 * A.eval c * w.eval c = 0) ∧
      w.eval c = 0 ∧ H ∣ w ∧ H ∣ phi)

end RefinedIIIConjugateIICoordinateAlgebra68

section RefinedIIIConjugateIICoordinatePolynomial68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- Exact source-shape transport to the globally zero reduced lower row. -/
theorem NonsquareAlignedSourceCurveData68.terminalLowerZeroReduced_source_68
    (H : k[X]) [NonsquarePolynomial46 H]
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (A C0 E0 b1 B D phi w : k[X])
    (hb : b1 = H * B)
    (hW : terminalScaledW68 H A C0 S.gamma = H ^ 2 * w)
    (hPhi : terminalScaledPhi68 H A b1 C0 E0 S.gamma S.epsilon =
      H ^ 2 * phi)
    (hlower : terminalLowerZeroOne68 H A B C0 D E0
      S.alpha S.gamma S.epsilon S.eta = 0) :
    terminalLowerZeroReduced68 H A B D phi w S.gamma = 0 := by
  have hH : H ≠ 0 := H_ne_zero_of_nonsquare68 (H := H)
  have hCshape : C0 = C (1 / 3 : k) * A ^ 2 +
      H ^ 2 * (C (9 / 4 : k) * w - C (3 / 2 * S.gamma : k)) := by
    apply FaithfulSMul.algebraMap_injective k[X] (RatFunc k)
    have hm := congrArg (algebraMap k[X] (RatFunc k)) hW
    dsimp only [terminalScaledW68] at hm
    simp only [map_add, map_sub, map_mul, map_pow, RatFunc.algebraMap_C,
      map_div₀, map_ofNat, map_one] at hm ⊢
    linear_combination (9 / 4 : RatFunc k) * hm
  have hEshape := S.terminalActualEShape68 (H := H)
    A C0 E0 b1 B w phi hb hW hPhi
  have hshape : terminalLowerZeroOne68 H A B
      (C (1 / 3 : k) * A ^ 2 +
        H ^ 2 * (C (9 / 4 : k) * w - C (3 / 2 * S.gamma : k))) D
      (C (1 / 27 : k) * A ^ 3 +
        H ^ 2 * (C (3 / 8 : k) * phi + C (3 / 2 : k) * A * w -
          C (1 / 2 * S.gamma : k) * A) -
        C (3 / 4 * S.epsilon : k) * H ^ 3 +
        C (1 / 9 : k) * H ^ 4 * B ^ 2)
      S.alpha S.gamma S.epsilon S.eta = 0 := by
    rw [← hCshape, ← hEshape]
    exact hlower
  have hfac := terminalLowerZeroOne_eq_Hsq_reduced_68 H A B D phi w
    S.alpha S.gamma S.epsilon S.eta
  have hz : H ^ 2 * terminalLowerZeroReduced68 H A B D phi w S.gamma = 0 := by
    rw [← hfac]
    exact hshape
  exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero 2 hH)

/-- The `F=0, B'=0` coordinate leaf.  Its next lower-zero coefficient either
globalizes the `w` zero to the core or kills the second `F` jet. -/
theorem terminalRefinedIII_conjugateII_Fcoordinate_68
    (H A B D w phi : k[X]) (gamma a c : k)
    (hdeg : H.natDegree = 2)
    (hsimple : ∀ x : k, H.eval x = 0 → H.derivative.eval x ≠ 0)
    (ha : H.eval a = 0) (hc : H.eval c = 0) (hac : a ≠ c)
    (hwa : w.eval a = 0)
    (hB0 : B.eval c = 0) (hD0 : D.eval c = 0)
    (hF1 : A.eval c * B.derivative.eval c -
      3 * D.derivative.eval c = 0)
    (hB1 : B.derivative.eval c = 0)
    (hjets : terminalI4JetPacket68 B D w phi c)
    (hR : terminalLowerZeroReduced68 H A B D phi w gamma = 0) :
    H ∣ w ∨ A.eval c * B.derivative.derivative.eval c -
      3 * D.derivative.derivative.eval c = 0 := by
  have hh := hsimple c hc
  have hD1 : D.derivative.eval c = 0 := by
    rw [hB1, mul_zero, zero_sub] at hF1
    have hthree : (3 : k) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp (by linear_combination -hF1)).resolve_left hthree
  have hR2 := congrArg
    (fun P : k[X] => P.derivative.derivative.eval c) hR
  rw [derivative_zero, derivative_zero, eval_zero,
    terminalLowerZeroReduced_second_componentII_doubleZero_68
      H A B D phi w gamma c hc hB0 hB1 hD0 hD1] at hR2
  have hscalar : terminalRefinedIIIConjugateIIFourthScalar68
      (A.eval c) (B.derivative.derivative.eval c) (w.eval c)
      (D.derivative.derivative.eval c) (phi.eval c) = 0 :=
    (mul_eq_zero.mp hR2).resolve_left hh
  have hII := terminalI4JetPacket68_componentII B D w phi c hB0 hD0 hjets
  have hI4two : B.derivative.derivative.eval c * phi.eval c +
      6 * w.eval c * D.derivative.derivative.eval c = 0 := by
    have htwo := hII.2.1
    simp only [hB1, hD1, zero_mul, mul_zero, zero_add, add_zero] at htwo
    linear_combination htwo
  rcases terminalRefinedIII_conjugateII_fourth_resultant_68
      (A.eval c) (B.derivative.derivative.eval c) (w.eval c)
      (D.derivative.derivative.eval c) (phi.eval c) hI4two hscalar with
    hwc | hF2
  · left
    exact dvd_of_two_simple_root_evals_68 H w hdeg hsimple
      a c hac ha hc hwa hwc
  · exact Or.inr hF2

/-- The `G=0, w=0` coordinate leaf immediately gives both global core
divisibilities, with no degree assumption. -/
theorem terminalRefinedIII_conjugateII_Gcoordinate_68
    (H A w phi : k[X]) (a c : k)
    (hdeg : H.natDegree = 2)
    (hsimple : ∀ x : k, H.eval x = 0 → H.derivative.eval x ≠ 0)
    (ha : H.eval a = 0) (hc : H.eval c = 0) (hac : a ≠ c)
    (hwa : w.eval a = 0) (hphia : phi.eval a = 0)
    (hG : phi.eval c + 2 * A.eval c * w.eval c = 0)
    (hwc : w.eval c = 0) : H ∣ w ∧ H ∣ phi := by
  have hphic : phi.eval c = 0 := by rw [hwc, mul_zero, add_zero] at hG; exact hG
  exact ⟨dvd_of_two_simple_root_evals_68 H w hdeg hsimple
      a c hac ha hc hwa hwc,
    dvd_of_two_simple_root_evals_68 H phi hdeg hsimple
      a c hac ha hc hphia hphic⟩

def terminalRefinedIIIConjugateIICoordinatePacket68
    (H A B D w phi : k[X]) (c : k) : Prop :=
  ((A.eval c * B.derivative.eval c - 3 * D.derivative.eval c = 0) ∧
      (phi.eval c + 2 * A.eval c * w.eval c = 0)) ∨
    ((A.eval c * B.derivative.eval c - 3 * D.derivative.eval c = 0) ∧
      B.derivative.eval c = 0 ∧
      (H ∣ w ∨ A.eval c * B.derivative.derivative.eval c -
        3 * D.derivative.derivative.eval c = 0)) ∨
    ((phi.eval c + 2 * A.eval c * w.eval c = 0) ∧
      w.eval c = 0 ∧ H ∣ w ∧ H ∣ phi)

/-- Assembly of the two coordinate refinements while retaining the common
`F=G=0` leaf exactly. -/
theorem terminalRefinedIII_conjugateII_coordinate_packet_68
    (H A B D w phi : k[X]) (gamma a c : k)
    (D1 : k[X])
    (hdeg : H.natDegree = 2)
    (hsimple : ∀ x : k, H.eval x = 0 → H.derivative.eval x ≠ 0)
    (ha : H.eval a = 0) (hc : H.eval c = 0) (hac : a ≠ c)
    (hwa : w.eval a = 0) (hphia : phi.eval a = 0)
    (hB0 : B.eval c = 0) (hD0 : D.eval c = 0)
    (hDshape : D = H * D1)
    (hjets : terminalI4JetPacket68 B D w phi c)
    (hnext : terminalRefinedIIIConjugateIINextSplit68
      (A.eval c) (H.derivative.eval c) (B.derivative.eval c)
      (w.eval c) (D1.eval c) (phi.eval c))
    (hR : terminalLowerZeroReduced68 H A B D phi w gamma = 0) :
    terminalRefinedIIIConjugateIICoordinatePacket68 H A B D w phi c := by
  have hDderiv : D.derivative.eval c =
      H.derivative.eval c * D1.eval c := by
    have hd := congrArg (fun P : k[X] => P.derivative.eval c) hDshape
    simpa [derivative_mul, eval_add, eval_mul, hc] using hd
  rcases hnext with ⟨hF, hB1 | hG⟩ | ⟨hG, hwc | hF⟩
  · right; left
    have hF' : A.eval c * B.derivative.eval c - 3 * D.derivative.eval c = 0 := by
      rw [hDderiv]
      linear_combination hF
    refine ⟨hF', hB1, ?_⟩
    exact terminalRefinedIII_conjugateII_Fcoordinate_68 H A B D w phi
      gamma a c hdeg hsimple ha hc hac hwa hB0 hD0 hF' hB1 hjets hR
  · left
    refine ⟨?_, hG⟩
    rw [hDderiv]
    linear_combination hF
  · right; right
    obtain ⟨hdvdW, hdvdPhi⟩ := terminalRefinedIII_conjugateII_Gcoordinate_68
      H A w phi a c hdeg hsimple ha hc hac hwa hphia hG hwc
    exact ⟨hG, hwc, hdvdW, hdvdPhi⟩
  · left
    refine ⟨?_, hG⟩
    rw [hDderiv]
    linear_combination hF

end RefinedIIIConjugateIICoordinatePolynomial68

section RefinedIIIConjugateIICoordinateSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Local source wrapper for the coordinate refinement.  Its hypotheses are
the literal canonical source shapes already produced upstream, and the
preserved `H²` loaded quotient is returned unchanged. -/
theorem NonsquareAlignedSourceCurveData68.terminalRefinedIIIConjugateIICoordinatePacket
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (A C0 E0 b1 B D w phi K D1 BW : k[X]) (a c : k)
    (hdeg : H.natDegree = 2)
    (hb : b1 = H * B)
    (hW : terminalScaledW68 H A C0 S.gamma = H ^ 2 * w)
    (hPhi : terminalScaledPhi68 H A b1 C0 E0 S.gamma S.epsilon =
      H ^ 2 * phi)
    (ha : H.eval a = 0) (hc : H.eval c = 0) (hac : a ≠ c)
    (hwa : w.eval a = 0) (hphia : phi.eval a = 0)
    (hB0 : B.eval c = 0) (hD0 : D.eval c = 0)
    (hDshape : D = H * D1)
    (hmatch : terminalRefinedIIIConjugateMatching68
      H A B D w phi (terminalEDerivativeNumerator68 H E0) K j c)
    (hnext : terminalRefinedIIIConjugateIINextSplit68
      (A.eval c) (H.derivative.eval c) (B.derivative.eval c)
      (w.eval c) (D1.eval c) (phi.eval c))
    (hlower : terminalLowerZeroOne68 H A B C0 D E0
      S.alpha S.gamma S.epsilon S.eta = 0)
    (hrowq : BW * terminalEDerivativeNumerator68 H E0 - D1 * K =
      C j * H ^ 2) :
    terminalRefinedIIIConjugateIICoordinatePacket68 H A B D w phi c ∧
      BW * terminalEDerivativeNumerator68 H E0 - D1 * K = C j * H ^ 2 := by
  have hsimple : ∀ x : k, H.eval x = 0 → H.derivative.eval x ≠ 0 :=
    fun x hx => nonsquare_natDegree_two_derivative_ne_zero hdeg
      NonsquarePolynomial46.not_sq hx
  have hR := S.terminalLowerZeroReduced_source_68 H A C0 E0 b1 B D phi w
    hb hW hPhi hlower
  refine ⟨terminalRefinedIII_conjugateII_coordinate_packet_68
    H A B D w phi S.gamma a c D1 hdeg hsimple ha hc hac hwa hphia
      hB0 hD0 hDshape hmatch.1.2.1 hnext hR, hrowq⟩

end RefinedIIIConjugateIICoordinateSource68

end Max11DegreeRoutes
