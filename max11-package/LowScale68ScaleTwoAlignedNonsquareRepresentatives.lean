import LowScale68ScaleTwoAlignedNonsquareEndgame

/-! # Polynomial representatives for aligned nonsquare `(6,8)` square cores

The quadratic polynomial `Z²-H`, deck involution, fixed-field descent,
polynomial derivative, square-root normality, and the nonsquare
unit-product lemma are independent of the outer pair.  They are taken from
`LowScale46QuadraticField` / `LowScale46Integrality`.  The descended
packet `NonsquareAlignedSourceCurveData68.descendedPacket` is the input.

Degree-specific `(4,6)` residuals are not used: not the aligned shift
`V=0`, not the boundary quartic, not `K=B²` reconstruction from that
quartic, and not the last-row restriction to `(-3/4) B² dB`.  The `(6,8)`
replacements below are the even auxiliaries `W,Φ,BD`, the linear
reconstructions of `K_B=B²` from `Φ=0` and of `K_D=D²` from `I₃`, the
normality handoff `K` polynomial ⇒ `M=√H B` polynomial with `M²=HK`, the
last-row `W`-form in `k(x)`, and the unit-product close once a last-row
`c M K'=j` is available.

No twice-prime or total-degree argument is used.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

section AlignedNonsquareRepresentativesAlgebra68

variable {F : Type*} [Field F] [CharZero F]

/-- The first integral `I₃` after removing the displayed square `D²`. -/
def alignedFirstIntegralThreeWithoutDsq68
    (A B C0 D E gamma epsilon : F) : F :=
  (-16 / 243 : F) * A ^ 5 + 2 * C0 * epsilon + 4 * E * gamma -
    (8 / 9 : F) * A * C0 ^ 2 - (8 / 9 : F) * B ^ 2 * C0 -
    (8 / 9 : F) * A ^ 2 * E - (2 / 3 : F) * A ^ 2 * epsilon -
    (2 / 3 : F) * B ^ 2 * gamma + (8 / 3 : F) * C0 * E +
    (8 / 27 : F) * A ^ 3 * gamma + (20 / 27 : F) * A ^ 2 * B ^ 2 +
    (40 / 81 : F) * A ^ 3 * C0 - (16 / 9 : F) * A * B * D -
    (4 / 3 : F) * A * C0 * gamma

/-- Exact split of the aligned first integral `I₃` as `(4/3) D²` plus an
even remainder. -/
theorem firstIntegralThree68_aligned_Dsq
    (A B C0 D E gamma epsilon : F) :
    firstIntegralThree68 0 A B C0 D E 0 gamma 0 epsilon 0 =
      (4 / 3 : F) * D ^ 2 +
        alignedFirstIntegralThreeWithoutDsq68 A B C0 D E gamma epsilon := by
  simp only [firstIntegralThree68, alignedFirstIntegralThreeWithoutDsq68]
  ring

/-- On `Φ=0`, the odd first-integral factor reconstructs `B²` linearly
from the even coordinates `A,C₀,E` and the ground constants.  This is the
`(6,8)` replacement of the `(4,6)` reconstruction of `K` from the second
boundary. -/
theorem alignedFirstIntegralFourOddPart68_Bsq
    (A B C0 E gamma epsilon : F)
    (hΦ : alignedFirstIntegralFourOddPart68 A B C0 E gamma epsilon = 0) :
    B ^ 2 =
      9 * E + (27 / 4 : F) * epsilon + (5 / 3 : F) * A ^ 3 -
        6 * A * C0 - (9 / 2 : F) * A * gamma := by
  simp only [alignedFirstIntegralFourOddPart68] at hΦ
  linear_combination -(27 / 8 : F) * hΦ

/-- On a constant `I₃` value, `D²` is likewise linear in the remaining
even combination. -/
theorem Dsq_of_firstIntegralThree68
    (A B C0 D E gamma epsilon i3 : F)
    (hI : firstIntegralThree68 0 A B C0 D E 0 gamma 0 epsilon 0 = i3) :
    D ^ 2 =
      (3 / 4 : F) * (i3 -
        alignedFirstIntegralThreeWithoutDsq68 A B C0 D E gamma epsilon) := by
  have hshape := firstIntegralThree68_aligned_Dsq A B C0 D E gamma epsilon
  rw [hI] at hshape
  linear_combination (3 / 4 : F) * hshape.symm

/-- The even product `BD` is recovered from the factored first integral
`I₄` after multiplying through by `B`. -/
theorem I4_even_Bsq_BD
    (A B C0 D E gamma epsilon : F)
    (hI4 :
      B * alignedFirstIntegralFourOddPart68 A B C0 E gamma epsilon +
        (6 : F) * alignedLastRowShiftW68 A C0 gamma * D = 0) :
    B ^ 2 * alignedFirstIntegralFourOddPart68 A B C0 E gamma epsilon +
      (6 : F) * alignedLastRowShiftW68 A C0 gamma * (B * D) = 0 := by
  linear_combination B * hI4

end AlignedNonsquareRepresentativesAlgebra68

section RatFuncRepresentatives68

variable {k : Type*} [Field k] [CharZero k]

/-- Direct reconstruction: if `K_B` is the displayed linear combination of
polynomial even coordinates, then `K_B` is polynomial.  This is the
`(6,8)` analogue of `ratFunc_K_isPolynomial_of_alignedBoundaryE46`. -/
theorem ratFunc_KB_of_Phi_zero_polynomial68
    (aR cR eR kB : RatFunc k) (A0 C0p E0 : k[X])
    (gamma epsilon : k)
    (hA : algebraMap k[X] (RatFunc k) A0 = aR)
    (hC : algebraMap k[X] (RatFunc k) C0p = cR)
    (hE : algebraMap k[X] (RatFunc k) E0 = eR)
    (hkB :
      kB =
        9 * eR + (27 / 4 : RatFunc k) *
            algebraMap k (RatFunc k) epsilon +
          (5 / 3 : RatFunc k) * aR ^ 3 - 6 * aR * cR -
          (9 / 2 : RatFunc k) * aR * algebraMap k (RatFunc k) gamma) :
    ∃ K0 : k[X], algebraMap k[X] (RatFunc k) K0 = kB := by
  refine ⟨C (9 : k) * E0 + C ((27 / 4 : k) * epsilon) +
      C (5 / 3 : k) * A0 ^ 3 - C (6 : k) * A0 * C0p -
      C (9 / 2 : k) * A0 * C gamma, ?_⟩
  simp only [map_add, map_sub, map_mul, map_pow, RatFunc.algebraMap_C,
    hA, hC, hE]
  simp only [← RatFunc.algebraMap_eq_C]
  have h9 : algebraMap k (RatFunc k) (9 : k) = (9 : RatFunc k) := by
    rw [map_ofNat]
  have h6 : algebraMap k (RatFunc k) (6 : k) = (6 : RatFunc k) := by
    rw [map_ofNat]
  have h274 : algebraMap k (RatFunc k) (27 / 4 : k) =
      (27 / 4 : RatFunc k) := by
    rw [map_div₀, map_ofNat, map_ofNat]
  have h53 : algebraMap k (RatFunc k) (5 / 3 : k) =
      (5 / 3 : RatFunc k) := by
    rw [map_div₀, map_ofNat, map_ofNat]
  have h92 : algebraMap k (RatFunc k) (9 / 2 : k) =
      (9 / 2 : RatFunc k) := by
    rw [map_div₀, map_ofNat, map_ofNat]
  rw [h9, h6, h274, h53, h92]
  exact hkB.symm

/-- Linear reconstruction of `K_D` from a constant `I₃` once the remaining
even combination is polynomial. -/
theorem ratFunc_KD_of_I3_polynomial68
    (remR kD : RatFunc k) (Rem0 : k[X]) (i3 : k)
    (hRem : algebraMap k[X] (RatFunc k) Rem0 = remR)
    (hkD :
      kD =
        (3 / 4 : RatFunc k) *
          (algebraMap k (RatFunc k) i3 - remR)) :
    ∃ K0 : k[X], algebraMap k[X] (RatFunc k) K0 = kD := by
  refine ⟨C (3 / 4 : k) * (C i3 - Rem0), ?_⟩
  simp only [map_mul, map_sub, RatFunc.algebraMap_C, hRem]
  have h34 : RatFunc.C (3 / 4 : k) = (3 / 4 : RatFunc k) := by
    calc
      RatFunc.C (3 / 4 : k) = algebraMap k (RatFunc k) (3 / 4 : k) := by
        rw [RatFunc.algebraMap_eq_C]
      _ = algebraMap k (RatFunc k) (3 : k) /
            algebraMap k (RatFunc k) (4 : k) := by
          rw [map_div₀]
      _ = (3 / 4 : RatFunc k) := by rw [map_ofNat, map_ofNat]
  have hCi3 : RatFunc.C i3 = algebraMap k (RatFunc k) i3 := by
    rw [RatFunc.algebraMap_eq_C]
  rw [h34, hCi3, hkD]

end RatFuncRepresentatives68

section UnitProductRepresentatives68

variable {k F : Type*} [Field k] [Field F] [CharZero k] [CharZero F]
  [Algebra k F] [Algebra k[X] F] [IsScalarTower k k[X] F]

/-- Pair-independent descent: polynomial `K=B²`, `M=hB` with `M²=HK` turn
a last row `h (c B² dB) = j` into the nonsquare unit product
`(c/2) M K' = j`. -/
theorem nonsquare_aligned_descent_Bsq_lastRow_impossible68
    (d : Derivation k F F)
    (hd : ∀ P : k[X],
      d (algebraMap k[X] F P) = algebraMap k[X] F P.derivative)
    (hι : Function.Injective (algebraMap k[X] F))
    (H0 K0 M0 : k[X]) (h B : F) (j c : k) (hj : j ≠ 0)
    (hK : algebraMap k[X] F K0 = B ^ 2)
    (hM : algebraMap k[X] F M0 = h * B)
    (hMK : M0 ^ 2 = H0 * K0)
    (hlast : h * (algebraMap k F c * B ^ 2 * d B) =
      algebraMap k F j) : False := by
  have hc2 : algebraMap k F (c / 2 : k) = algebraMap k F c / 2 := by
    have hdiv : algebraMap k F (c / 2 : k) =
        algebraMap k F c / algebraMap k F (2 : k) :=
      map_div₀ _ _ _
    have h2 : algebraMap k F (2 : k) = (2 : F) :=
      map_ofNat _ 2
    rw [h2] at hdiv
    exact hdiv
  have hC2 : algebraMap k[X] F (C (c / 2 : k)) =
      algebraMap k F c / 2 := by
    calc
      algebraMap k[X] F (C (c / 2 : k)) =
          algebraMap k F (c / 2 : k) := by
            simpa using (IsScalarTower.algebraMap_apply k k[X] F
              (c / 2 : k)).symm
      _ = _ := hc2
  have hCj : algebraMap k[X] F (C j) = algebraMap k F j := by
    simpa using (IsScalarTower.algebraMap_apply k k[X] F j).symm
  have hrestrict :
      algebraMap k[X] F (C (c / 2 : k) * M0 * K0.derivative) =
        h * (algebraMap k F c * B ^ 2 * d B) := by
    simp only [map_mul, hC2, hM]
    rw [← hd K0, hK]
    simp only [Derivation.leibniz_pow, nsmul_eq_mul, smul_eq_mul]
    field_simp
    ring
  have hpolyMap :
      algebraMap k[X] F (C (c / 2 : k) * M0 * K0.derivative) =
        algebraMap k[X] F (C j) := by
    exact hrestrict.trans (hlast.trans hCj.symm)
  have hpoly : C (c / 2 : k) * M0 * K0.derivative = C j :=
    hι hpolyMap
  exact nonsquare_aligned_unitProduct_impossible46
    H0 K0 M0 j (c / 2 : k) hj hMK hpoly

/-- Direct polynomial unit-product close, with no further field
identification required. -/
theorem nonsquare_aligned_polynomial_unitProduct_impossible68
    (H0 K0 M0 : k[X]) (j c : k) (hj : j ≠ 0)
    (hMK : M0 ^ 2 = H0 * K0)
    (hlast : C c * M0 * derivative K0 = C j) : False :=
  nonsquare_aligned_unitProduct_impossible46 H0 K0 M0 j c hj hMK hlast

end UnitProductRepresentatives68

section QuadraticRepresentatives68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

local notation "F68" => AdjoinRoot (alignedQuadraticPolynomial46 H)

local instance quadraticRepresentativesCharZero68 : CharZero F68 :=
  charZero_of_injective_ringHom (algebraMap (RatFunc k) F68).injective

/-- Deck-evenness of the aligned last-row shift `W`. -/
theorem NonsquareAlignedSourceCurveData68.W_even
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j) :
    alignedQuadraticDeck46 H
        (alignedLastRowShiftW68 S.A S.C0 (algebraMap k F68 S.gamma)) =
      alignedLastRowShiftW68 S.A S.C0 (algebraMap k F68 S.gamma) := by
  simp only [alignedLastRowShiftW68, map_add, map_sub, map_mul, map_div₀,
    map_pow, map_ofNat, S.A_even, S.C_even, alignedQuadraticDeck46_ground]

set_option maxHeartbeats 2000000 in
/-- Deck-evenness of the odd first-integral factor `Φ`. -/
theorem NonsquareAlignedSourceCurveData68.Phi_even
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j) :
    alignedQuadraticDeck46 H
        (alignedFirstIntegralFourOddPart68 S.A S.B S.C0 S.E
          (algebraMap k F68 S.gamma) (algebraMap k F68 S.epsilon)) =
      alignedFirstIntegralFourOddPart68 S.A S.B S.C0 S.E
        (algebraMap k F68 S.gamma) (algebraMap k F68 S.epsilon) := by
  have hA := S.A_even
  have hB := S.B_odd
  have hC := S.C_even
  have hE := S.E_even
  simp only [alignedFirstIntegralFourOddPart68, map_add, map_sub, map_neg,
    map_mul, map_div₀, map_pow, map_ofNat, hA, hB, hC, hE,
    alignedQuadraticDeck46_ground]
  ring

/-- Deck-evenness of the mixed odd product `B D`. -/
theorem NonsquareAlignedSourceCurveData68.BD_even
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j) :
    alignedQuadraticDeck46 H (S.B * S.D) = S.B * S.D := by
  simp only [map_mul, S.B_odd, S.D_odd]
  ring

/-- The even auxiliaries `W`, `Φ`, and `BD` descend to `k(x)`. -/
theorem NonsquareAlignedSourceCurveData68.evenAuxiliariesDescend
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j) :
    (∃ wR : RatFunc k,
        alignedLastRowShiftW68 S.A S.C0 (algebraMap k F68 S.gamma) =
          algebraMap (RatFunc k) F68 wR) ∧
    (∃ φR : RatFunc k,
        alignedFirstIntegralFourOddPart68 S.A S.B S.C0 S.E
            (algebraMap k F68 S.gamma) (algebraMap k F68 S.epsilon) =
          algebraMap (RatFunc k) F68 φR) ∧
    (∃ bdR : RatFunc k,
        S.B * S.D = algebraMap (RatFunc k) F68 bdR) := by
  refine ⟨?_, ?_, ?_⟩
  · exact alignedQuadraticFixedElementDescends46 H _ S.W_even
  · exact alignedQuadraticFixedElementDescends46 H _ S.Phi_even
  · exact alignedQuadraticFixedElementDescends46 H _ S.BD_even

/-- Even form of `I₄` among the descended coordinates:
`K_B Φ + 6 W (BD) = 0` in `k(x)`. -/
theorem NonsquareAlignedSourceCurveData68.I4_even_ratFunc
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j) :
    ∃ kB φR wR bdR : RatFunc k,
      S.B ^ 2 = algebraMap (RatFunc k) F68 kB ∧
      alignedFirstIntegralFourOddPart68 S.A S.B S.C0 S.E
          (algebraMap k F68 S.gamma) (algebraMap k F68 S.epsilon) =
        algebraMap (RatFunc k) F68 φR ∧
      alignedLastRowShiftW68 S.A S.C0 (algebraMap k F68 S.gamma) =
        algebraMap (RatFunc k) F68 wR ∧
      S.B * S.D = algebraMap (RatFunc k) F68 bdR ∧
      kB * φR + 6 * wR * bdR = 0 := by
  obtain ⟨⟨wR, hwR⟩, ⟨φR, hφR⟩, ⟨bdR, hbdR⟩⟩ := S.evenAuxiliariesDescend
  obtain ⟨_ha, _hc, _he, _hq, ⟨kB, hkB⟩, _hkD, _hwB, _hwD, _hmB, _hmD⟩ :=
    S.evenCoordinatesDescend
  have hι : Function.Injective (algebraMap (RatFunc k) F68) :=
    (algebraMap (RatFunc k) F68).injective
  refine ⟨kB, φR, wR, bdR, hkB, hφR, hwR, hbdR, ?_⟩
  apply hι
  simp only [map_add, map_mul, map_ofNat, map_zero]
  rw [← hkB, ← hφR, ← hwR, ← hbdR]
  exact I4_even_Bsq_BD S.A S.B S.C0 S.D S.E
    (algebraMap k F68 S.gamma) (algebraMap k F68 S.epsilon) S.I4_factor

/-- Last-row `W`-form in `k(x)`:
`M_B W E' - M_D (V' - ((4/9)A+α) E') = j`.  This is the `(6,8)`
replacement of the `(4,6)` restriction `(-3/4) B² dB`; no vanishing of
an aligned shift is used. -/
theorem NonsquareAlignedSourceCurveData68.lastRow_W_ratFunc
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j) :
    ∃ mB wR eR mD aR vR : RatFunc k,
      AdjoinRoot.root (alignedQuadraticPolynomial46 H) * S.B =
        algebraMap (RatFunc k) F68 mB ∧
      alignedLastRowShiftW68 S.A S.C0 (algebraMap k F68 S.gamma) =
        algebraMap (RatFunc k) F68 wR ∧
      S.E = algebraMap (RatFunc k) F68 eR ∧
      AdjoinRoot.root (alignedQuadraticPolynomial46 H) * S.D =
        algebraMap (RatFunc k) F68 mD ∧
      S.A = algebraMap (RatFunc k) F68 aR ∧
      integratedV68 0 S.A S.B S.C0 S.D S.E
          (algebraMap k F68 S.alpha) 0 (algebraMap k F68 S.gamma) 0
          (algebraMap k F68 S.epsilon) (algebraMap k F68 S.eta) =
        algebraMap (RatFunc k) F68 vR ∧
      mB * wR * Differential.deriv eR -
          mD *
            (Differential.deriv vR -
              ((4 / 9 : RatFunc k) * aR +
                algebraMap k (RatFunc k) S.alpha) *
                Differential.deriv eR) =
        algebraMap k (RatFunc k) j := by
  obtain ⟨mU, eR, mD, vR, hmU, heR, hmD, hvR, hlast⟩ := S.lastRow_descends
  obtain ⟨⟨aR, haR⟩, _hc, _he, _hq, _hkB, _hkD, _hwB, _hwD, ⟨mB, hmB⟩,
      _hmD'⟩ := S.evenCoordinatesDescend
  obtain ⟨⟨wR, hwR⟩, _hφ, _hbd⟩ := S.evenAuxiliariesDescend
  have hι : Function.Injective (algebraMap (RatFunc k) F68) :=
    (algebraMap (RatFunc k) F68).injective
  have hU := integratedU68_aligned_factor S.A S.B S.C0 S.D S.E
    (algebraMap k F68 S.alpha) (algebraMap k F68 S.gamma)
  have hmU' :
      algebraMap (RatFunc k) F68 mU =
        algebraMap (RatFunc k) F68
          (mB * wR +
            mD * ((4 / 9 : RatFunc k) * aR +
              algebraMap k (RatFunc k) S.alpha)) := by
    have hsplit :
        AdjoinRoot.root (alignedQuadraticPolynomial46 H) *
            integratedU68 0 S.A S.B S.C0 S.D S.E
              (algebraMap k F68 S.alpha) 0 (algebraMap k F68 S.gamma) 0 0 =
          (AdjoinRoot.root (alignedQuadraticPolynomial46 H) * S.B) *
              alignedLastRowShiftW68 S.A S.C0 (algebraMap k F68 S.gamma) +
            (AdjoinRoot.root (alignedQuadraticPolynomial46 H) * S.D) *
              ((4 / 9 : F68) * S.A + algebraMap k F68 S.alpha) := by
      rw [hU]
      ring
    have hα : algebraMap k F68 S.alpha =
        algebraMap (RatFunc k) F68 (algebraMap k (RatFunc k) S.alpha) :=
      (IsScalarTower.algebraMap_apply k (RatFunc k) F68 S.alpha).symm
    calc
      algebraMap (RatFunc k) F68 mU =
          AdjoinRoot.root (alignedQuadraticPolynomial46 H) *
            integratedU68 0 S.A S.B S.C0 S.D S.E
              (algebraMap k F68 S.alpha) 0 (algebraMap k F68 S.gamma) 0 0 :=
        hmU.symm
      _ = (AdjoinRoot.root (alignedQuadraticPolynomial46 H) * S.B) *
              alignedLastRowShiftW68 S.A S.C0 (algebraMap k F68 S.gamma) +
            (AdjoinRoot.root (alignedQuadraticPolynomial46 H) * S.D) *
              ((4 / 9 : F68) * S.A + algebraMap k F68 S.alpha) :=
        hsplit
      _ = algebraMap (RatFunc k) F68 mB *
              algebraMap (RatFunc k) F68 wR +
            algebraMap (RatFunc k) F68 mD *
              ((4 / 9 : F68) * algebraMap (RatFunc k) F68 aR +
                algebraMap (RatFunc k) F68
                  (algebraMap k (RatFunc k) S.alpha)) := by
          rw [hmB, hwR, hmD, haR, hα]
      _ = algebraMap (RatFunc k) F68
            (mB * wR +
              mD * ((4 / 9 : RatFunc k) * aR +
                algebraMap k (RatFunc k) S.alpha)) := by
          simp only [map_add, map_mul, map_div₀, map_ofNat]
  have hmUeq :
      mU =
        mB * wR +
          mD * ((4 / 9 : RatFunc k) * aR +
            algebraMap k (RatFunc k) S.alpha) :=
    hι hmU'
  refine ⟨mB, wR, eR, mD, aR, vR, hmB, hwR, heR, hmD, haR, hvR, ?_⟩
  rw [hmUeq] at hlast
  convert hlast using 1
  ring

/-- On the face `D=0`, last-row nonvanishing forces `B≠0` and `W≠0`, the
factor `Φ` vanishes, and the descended last row is the single product
`M_B W E' = j`. -/
theorem NonsquareAlignedSourceCurveData68.lastRow_D_zero_W
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j) (hj : j ≠ 0)
    (hD : S.D = 0) :
    S.B ≠ 0 ∧
      alignedLastRowShiftW68 S.A S.C0 (algebraMap k F68 S.gamma) ≠ 0 ∧
      alignedFirstIntegralFourOddPart68 S.A S.B S.C0 S.E
          (algebraMap k F68 S.gamma) (algebraMap k F68 S.epsilon) = 0 ∧
      ∃ mB wR eR : RatFunc k,
        AdjoinRoot.root (alignedQuadraticPolynomial46 H) * S.B =
          algebraMap (RatFunc k) F68 mB ∧
        alignedLastRowShiftW68 S.A S.C0 (algebraMap k F68 S.gamma) =
          algebraMap (RatFunc k) F68 wR ∧
        S.E = algebraMap (RatFunc k) F68 eR ∧
        mB * wR * Differential.deriv eR =
          algebraMap k (RatFunc k) j := by
  have hBne : S.B ≠ 0 := by
    intro hB0
    exact NonsquareAlignedSourceCurveData68.B_D_ne (H := H) S hj ⟨hB0, hD⟩
  have hU :
      integratedU68 0 S.A S.B S.C0 S.D S.E
        (algebraMap k F68 S.alpha) 0 (algebraMap k F68 S.gamma) 0 0 =
        S.B * alignedLastRowShiftW68 S.A S.C0
          (algebraMap k F68 S.gamma) := by
    rw [integratedU68_aligned_factor, hD]
    ring
  have hWne :
      alignedLastRowShiftW68 S.A S.C0 (algebraMap k F68 S.gamma) ≠ 0 := by
    intro hW0
    have hU0 :
        integratedU68 0 S.A S.B S.C0 S.D S.E
          (algebraMap k F68 S.alpha) 0 (algebraMap k F68 S.gamma) 0 0 = 0 := by
      rw [hU, hW0]
      simp
    exact NonsquareAlignedSourceCurveData68.lastRow_U_D_ne (H := H) S hj
      ⟨hU0, hD⟩
  have hΦ :
      alignedFirstIntegralFourOddPart68 S.A S.B S.C0 S.E
          (algebraMap k F68 S.gamma) (algebraMap k F68 S.epsilon) = 0 := by
    have hI4 := S.I4_factor
    rw [hD] at hI4
    simp only [mul_zero, add_zero] at hI4
    exact (mul_eq_zero.mp hI4).resolve_left hBne
  obtain ⟨mB, wR, eR, mD, _aR, _vR, hmB, hwR, heR, hmD, _haR, _hvR,
      hlast⟩ := S.lastRow_W_ratFunc
  have hmD0 : mD = 0 := by
    have hι : Function.Injective (algebraMap (RatFunc k) F68) :=
      (algebraMap (RatFunc k) F68).injective
    apply hι
    rw [← hmD, hD]
    simp
  refine ⟨hBne, hWne, hΦ, mB, wR, eR, hmB, hwR, heR, ?_⟩
  simpa [hmD0] using hlast

/-- Polynomial `K_B=B²` produces a polynomial representative of `M_B=√H B`
satisfying the square relation `M²=HK`.  This is the `(6,8)` normality
handoff for the `B`-core. -/
theorem NonsquareAlignedSourceCurveData68.polynomialMB_of_polynomialKB
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (K0 : k[X])
    (hK : algebraMap k[X] F68 K0 = S.B ^ 2) :
    ∃ M0 : k[X],
      algebraMap k[X] F68 M0 =
        AdjoinRoot.root (alignedQuadraticPolynomial46 H) * S.B ∧
      M0 ^ 2 = H * K0 := by
  let h : F68 := AdjoinRoot.root (alignedQuadraticPolynomial46 H)
  have hroot : h ^ 2 = quadraticCoefficientMap46 H H :=
    alignedQuadraticRoot_sq46 H
  obtain ⟨_ha, _hc, _he, _hq, _hkB, _hkD, _hwB, _hwD, ⟨mR, hmR⟩, _hmD⟩ :=
    S.evenCoordinatesDescend
  have hmSq : mR ^ 2 = algebraMap k[X] (RatFunc k) (H * K0) := by
    apply (algebraMap (RatFunc k) F68).injective
    simp only [map_pow, map_mul]
    rw [← hmR]
    change (h * S.B) ^ 2 =
      quadraticCoefficientMap46 H H * algebraMap k[X] F68 K0
    rw [← hroot, hK]
    simp only [h]
    ring
  obtain ⟨M0, hM0⟩ :=
    ratFunc_isPolynomial_of_sq_isPolynomial46 mR (H * K0) hmSq
  have hMField : algebraMap k[X] F68 M0 = h * S.B := by
    change algebraMap (RatFunc k) F68
      (algebraMap k[X] (RatFunc k) M0) = h * S.B
    rw [hM0, ← hmR]
  have hMK : M0 ^ 2 = H * K0 := by
    apply alignedQuadraticPolynomialMap_injective46 H
      NonsquarePolynomial46.not_sq
    simp only [map_pow, map_mul]
    rw [hMField, hK,
      ← quadraticCoefficientMap46_eq_algebraMap H H, ← hroot]
    simp only [h]
    ring
  exact ⟨M0, hMField, hMK⟩

/-- The same normality handoff for the `D`-core. -/
theorem NonsquareAlignedSourceCurveData68.polynomialMD_of_polynomialKD
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (K0 : k[X])
    (hK : algebraMap k[X] F68 K0 = S.D ^ 2) :
    ∃ M0 : k[X],
      algebraMap k[X] F68 M0 =
        AdjoinRoot.root (alignedQuadraticPolynomial46 H) * S.D ∧
      M0 ^ 2 = H * K0 := by
  let h : F68 := AdjoinRoot.root (alignedQuadraticPolynomial46 H)
  have hroot : h ^ 2 = quadraticCoefficientMap46 H H :=
    alignedQuadraticRoot_sq46 H
  obtain ⟨_ha, _hc, _he, _hq, _hkB, _hkD, _hwB, _hwD, _hmB, ⟨mR, hmR⟩⟩ :=
    S.evenCoordinatesDescend
  have hmSq : mR ^ 2 = algebraMap k[X] (RatFunc k) (H * K0) := by
    apply (algebraMap (RatFunc k) F68).injective
    simp only [map_pow, map_mul]
    rw [← hmR]
    change (h * S.D) ^ 2 =
      quadraticCoefficientMap46 H H * algebraMap k[X] F68 K0
    rw [← hroot, hK]
    simp only [h]
    ring
  obtain ⟨M0, hM0⟩ :=
    ratFunc_isPolynomial_of_sq_isPolynomial46 mR (H * K0) hmSq
  have hMField : algebraMap k[X] F68 M0 = h * S.D := by
    change algebraMap (RatFunc k) F68
      (algebraMap k[X] (RatFunc k) M0) = h * S.D
    rw [hM0, ← hmR]
  have hMK : M0 ^ 2 = H * K0 := by
    apply alignedQuadraticPolynomialMap_injective46 H
      NonsquarePolynomial46.not_sq
    simp only [map_pow, map_mul]
    rw [hMField, hK,
      ← quadraticCoefficientMap46_eq_algebraMap H H, ← hroot]
    simp only [h]
    ring
  exact ⟨M0, hMField, hMK⟩

/-- On `Φ=0`, polynomial even coordinates `A,C₀,E` produce a polynomial
representative of `K_B=B²`. -/
theorem NonsquareAlignedSourceCurveData68.polynomialKB_of_Phi_zero
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (A0 C0p E0 : k[X])
    (hA : algebraMap k[X] F68 A0 = S.A)
    (hC : algebraMap k[X] F68 C0p = S.C0)
    (hE : algebraMap k[X] F68 E0 = S.E)
    (hΦ :
      alignedFirstIntegralFourOddPart68 S.A S.B S.C0 S.E
          (algebraMap k F68 S.gamma) (algebraMap k F68 S.epsilon) = 0) :
    ∃ K0 : k[X], algebraMap k[X] F68 K0 = S.B ^ 2 := by
  obtain ⟨_ha, _hc, _he, _hq, ⟨kB, hkB⟩, _hkD, _hwB, _hwD, _hmB, _hmD⟩ :=
    S.evenCoordinatesDescend
  have hBsq := alignedFirstIntegralFourOddPart68_Bsq S.A S.B S.C0 S.E
    (algebraMap k F68 S.gamma) (algebraMap k F68 S.epsilon) hΦ
  have hι : Function.Injective (algebraMap (RatFunc k) F68) :=
    (algebraMap (RatFunc k) F68).injective
  have hkBform :
      kB =
        9 *
            (algebraMap k[X] (RatFunc k) E0) +
          (27 / 4 : RatFunc k) * algebraMap k (RatFunc k) S.epsilon +
            (5 / 3 : RatFunc k) *
                (algebraMap k[X] (RatFunc k) A0) ^ 3 -
              6 * algebraMap k[X] (RatFunc k) A0 *
                algebraMap k[X] (RatFunc k) C0p -
              (9 / 2 : RatFunc k) * algebraMap k[X] (RatFunc k) A0 *
                algebraMap k (RatFunc k) S.gamma := by
    apply hι
    simp only [map_add, map_sub, map_mul, map_pow, map_div₀, map_ofNat]
    have hA' : algebraMap k[X] F68 A0 =
        algebraMap (RatFunc k) F68 (algebraMap k[X] (RatFunc k) A0) :=
      (IsScalarTower.algebraMap_apply k[X] (RatFunc k) F68 A0).symm
    have hC' : algebraMap k[X] F68 C0p =
        algebraMap (RatFunc k) F68 (algebraMap k[X] (RatFunc k) C0p) :=
      (IsScalarTower.algebraMap_apply k[X] (RatFunc k) F68 C0p).symm
    have hE' : algebraMap k[X] F68 E0 =
        algebraMap (RatFunc k) F68 (algebraMap k[X] (RatFunc k) E0) :=
      (IsScalarTower.algebraMap_apply k[X] (RatFunc k) F68 E0).symm
    have hγ : algebraMap k F68 S.gamma =
        algebraMap (RatFunc k) F68 (algebraMap k (RatFunc k) S.gamma) :=
      (IsScalarTower.algebraMap_apply k (RatFunc k) F68 S.gamma).symm
    have hε : algebraMap k F68 S.epsilon =
        algebraMap (RatFunc k) F68 (algebraMap k (RatFunc k) S.epsilon) :=
      (IsScalarTower.algebraMap_apply k (RatFunc k) F68 S.epsilon).symm
    rw [← hkB, hBsq, ← hA', ← hC', ← hE', hA, hC, hE, hγ, hε]
  obtain ⟨K0, hK0⟩ :=
    ratFunc_KB_of_Phi_zero_polynomial68
      (algebraMap k[X] (RatFunc k) A0)
      (algebraMap k[X] (RatFunc k) C0p)
      (algebraMap k[X] (RatFunc k) E0) kB A0 C0p E0 S.gamma S.epsilon
      rfl rfl rfl hkBform
  refine ⟨K0, ?_⟩
  change algebraMap (RatFunc k) F68 (algebraMap k[X] (RatFunc k) K0) =
    S.B ^ 2
  rw [hK0, ← hkB]

/-- Conditional close: polynomial `K_B`, `M_B` and a last row
`h (c B² dB) = j` contradict `j≠0`. -/
theorem NonsquareAlignedSourceCurveData68.impossible_of_Bsq_lastRow
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j) (hj : j ≠ 0)
    (K0 M0 : k[X]) (c : k)
    (hK : algebraMap k[X] F68 K0 = S.B ^ 2)
    (hM : algebraMap k[X] F68 M0 =
      AdjoinRoot.root (alignedQuadraticPolynomial46 H) * S.B)
    (hMK : M0 ^ 2 = H * K0)
    (hlast :
      AdjoinRoot.root (alignedQuadraticPolynomial46 H) *
          (algebraMap k F68 c * S.B ^ 2 *
            quadraticDerivation46 H S.B) =
        algebraMap k F68 j) : False := by
  have hd : ∀ P : k[X],
      quadraticDerivation46 H (algebraMap k[X] F68 P) =
        algebraMap k[X] F68 P.derivative := by
    intro P
    rw [quadraticDerivation46_apply]
    exact alignedQuadraticDeriv_polynomial46 H
      NonsquarePolynomial46.not_sq P
  exact nonsquare_aligned_descent_Bsq_lastRow_impossible68
    (quadraticDerivation46 H) hd
    (alignedQuadraticPolynomialMap_injective46 H
      NonsquarePolynomial46.not_sq)
    H K0 M0
    (AdjoinRoot.root (alignedQuadraticPolynomial46 H)) S.B j c hj
    hK hM hMK hlast

/-- Conditional close from a polynomial unit product `c M K'=j`. -/
theorem NonsquareAlignedSourceCurveData68.impossible_of_unitProduct
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j) (hj : j ≠ 0)
    (K0 M0 : k[X]) (c : k)
    (hMK : M0 ^ 2 = H * K0)
    (hlast : C c * M0 * derivative K0 = C j) : False :=
  nonsquare_aligned_polynomial_unitProduct_impossible68
    H K0 M0 j c hj hMK hlast

/-- Residual packet after the `(6,8)` representative layer: even
auxiliaries and last-row `W`-form in `k(x)`, linear reconstructions of
`K_B` and `K_D`, normality `K` polynomial ⇒ `M` polynomial, and the
unit-product close.  Polynomial representatives of `K_B` and `K_D` still
require polynomial even coordinates `A,C₀,E` (or a monic eliminant), and
the last row is not yet a scalar unit product `c M K'=j`. -/
theorem NonsquareAlignedSourceCurveData68.representativesPacket
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j) (hj : j ≠ 0) :
    firstIntegralFour68 0 S.A S.B S.C0 S.D S.E 0
        (algebraMap k F68 S.gamma) 0 (algebraMap k F68 S.epsilon) 0 = 0 ∧
    (∃ i3 : k,
      firstIntegralThree68 0 S.A S.B S.C0 S.D S.E 0
          (algebraMap k F68 S.gamma) 0 (algebraMap k F68 S.epsilon) 0 =
        algebraMap k F68 i3) ∧
    ¬ (S.B = 0 ∧ S.D = 0) ∧
    (∃ kB φR wR bdR : RatFunc k,
      S.B ^ 2 = algebraMap (RatFunc k) F68 kB ∧
      alignedFirstIntegralFourOddPart68 S.A S.B S.C0 S.E
          (algebraMap k F68 S.gamma) (algebraMap k F68 S.epsilon) =
        algebraMap (RatFunc k) F68 φR ∧
      alignedLastRowShiftW68 S.A S.C0 (algebraMap k F68 S.gamma) =
        algebraMap (RatFunc k) F68 wR ∧
      S.B * S.D = algebraMap (RatFunc k) F68 bdR ∧
      kB * φR + 6 * wR * bdR = 0) ∧
    (∃ mB wR eR mD aR vR : RatFunc k,
      AdjoinRoot.root (alignedQuadraticPolynomial46 H) * S.B =
        algebraMap (RatFunc k) F68 mB ∧
      alignedLastRowShiftW68 S.A S.C0 (algebraMap k F68 S.gamma) =
        algebraMap (RatFunc k) F68 wR ∧
      S.E = algebraMap (RatFunc k) F68 eR ∧
      AdjoinRoot.root (alignedQuadraticPolynomial46 H) * S.D =
        algebraMap (RatFunc k) F68 mD ∧
      S.A = algebraMap (RatFunc k) F68 aR ∧
      integratedV68 0 S.A S.B S.C0 S.D S.E
          (algebraMap k F68 S.alpha) 0 (algebraMap k F68 S.gamma) 0
          (algebraMap k F68 S.epsilon) (algebraMap k F68 S.eta) =
        algebraMap (RatFunc k) F68 vR ∧
      mB * wR * Differential.deriv eR -
          mD *
            (Differential.deriv vR -
              ((4 / 9 : RatFunc k) * aR +
                algebraMap k (RatFunc k) S.alpha) *
                Differential.deriv eR) =
        algebraMap k (RatFunc k) j) ∧
    (S.D = 0 →
      alignedFirstIntegralFourOddPart68 S.A S.B S.C0 S.E
          (algebraMap k F68 S.gamma) (algebraMap k F68 S.epsilon) = 0) := by
  refine ⟨(S.residualPacket).1, (S.residualPacket).2.1,
      NonsquareAlignedSourceCurveData68.B_D_ne (H := H) S hj,
      S.I4_even_ratFunc, S.lastRow_W_ratFunc, ?_⟩
  intro hD
  exact (NonsquareAlignedSourceCurveData68.lastRow_D_zero_W
    (H := H) S hj hD).2.2.1

end QuadraticRepresentatives68

#print axioms firstIntegralThree68_aligned_Dsq
#print axioms alignedFirstIntegralFourOddPart68_Bsq
#print axioms Dsq_of_firstIntegralThree68
#print axioms I4_even_Bsq_BD
#print axioms ratFunc_KB_of_Phi_zero_polynomial68
#print axioms ratFunc_KD_of_I3_polynomial68
#print axioms nonsquare_aligned_descent_Bsq_lastRow_impossible68
#print axioms nonsquare_aligned_polynomial_unitProduct_impossible68
#print axioms NonsquareAlignedSourceCurveData68.W_even
#print axioms NonsquareAlignedSourceCurveData68.Phi_even
#print axioms NonsquareAlignedSourceCurveData68.BD_even
#print axioms NonsquareAlignedSourceCurveData68.evenAuxiliariesDescend
#print axioms NonsquareAlignedSourceCurveData68.I4_even_ratFunc
#print axioms NonsquareAlignedSourceCurveData68.lastRow_W_ratFunc
#print axioms NonsquareAlignedSourceCurveData68.lastRow_D_zero_W
#print axioms NonsquareAlignedSourceCurveData68.polynomialMB_of_polynomialKB
#print axioms NonsquareAlignedSourceCurveData68.polynomialMD_of_polynomialKD
#print axioms NonsquareAlignedSourceCurveData68.polynomialKB_of_Phi_zero
#print axioms NonsquareAlignedSourceCurveData68.impossible_of_Bsq_lastRow
#print axioms NonsquareAlignedSourceCurveData68.impossible_of_unitProduct
#print axioms NonsquareAlignedSourceCurveData68.representativesPacket

end Max11DegreeRoutes
