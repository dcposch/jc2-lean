import LowScale68ScaleTwoAlignedNonsquareBridge

/-! # Quadratic-field endgame for aligned nonsquare `(6,8)`, scale two

Untracked working note. No tracked file was edited.

The quadratic polynomial `Z²-H`, its deck involution, fixed-field descent,
polynomial derivative, and nonsquare unit-product lemma are independent of
the outer pair.  They are taken from `LowScale46QuadraticField` /
`LowScale46Integrality`.  Source mapping, deck parity of the depressed
coordinates, and `beta = delta = zeta = 0` are already canonical in
`LowScale68ScaleTwoAlignedNonsquareBridge` and are not repeated.

Degree-specific `(4,6)` residuals, the aligned shift `V=0`, the boundary
quartic, `M²=HK` polynomial representatives, and the last-row restriction
to `(-3/4) B² dB` are not used.  Their `(6,8)` replacements are proved
here from `NonsquareAlignedSourceCurveData68` with `j ≠ 0`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

section AlignedNonsquareEndgameAlgebra68

variable {F : Type*} [Field F] [CharZero F]

/-- Shifted even combination that factors the aligned last-row coefficient
`U` after `L = beta = delta = zeta = 0`. -/
def alignedLastRowShiftW68 (A C0 gamma : F) : F :=
  (4 / 9 : F) * C0 - (4 / 27 : F) * A ^ 2 + (2 / 3 : F) * gamma

/-- The `B`-factor of the aligned first integral `I₄`. -/
def alignedFirstIntegralFourOddPart68
    (A B C0 E gamma epsilon : F) : F :=
  (-8 / 27 : F) * B ^ 2 + (8 / 3 : F) * E + 2 * epsilon +
    (40 / 81 : F) * A ^ 3 - (16 / 9 : F) * A * C0 -
    (4 / 3 : F) * A * gamma

/-- Exact factorization of the aligned last integrated coefficient. -/
theorem integratedU68_aligned_factor
    (A B C0 D E alpha gamma : F) :
    integratedU68 0 A B C0 D E alpha 0 gamma 0 0 =
      B * alignedLastRowShiftW68 A C0 gamma +
        D * ((4 / 9 : F) * A + alpha) := by
  simp only [integratedU68, alignedLastRowShiftW68]
  ring

/-- Exact factorization of the aligned first integral `I₄`. -/
theorem firstIntegralFour68_aligned_factor
    (A B C0 D E gamma epsilon : F) :
    firstIntegralFour68 0 A B C0 D E 0 gamma 0 epsilon 0 =
      B * alignedFirstIntegralFourOddPart68 A B C0 E gamma epsilon +
        (6 : F) * alignedLastRowShiftW68 A C0 gamma * D := by
  simp only [firstIntegralFour68, alignedFirstIntegralFourOddPart68,
    alignedLastRowShiftW68]
  ring

/-- Polynomial evaluation of a depressed sextic. -/
theorem eval_depressedSextic68
    (A B C0 D E r : F) :
    (depressedSextic68 A B C0 D E).eval r =
      r ^ 6 + A * r ^ 4 + B * r ^ 3 + C0 * r ^ 2 + D * r + E := by
  simp [depressedSextic68]

/-- The depressed-sextic center value is the even combination of `r²`,
`r B`, and `r D`. -/
theorem eval_depressedSextic68_evenCoordinates
    (A B C0 D E r : F) :
    (depressedSextic68 A B C0 D E).eval r =
      (r ^ 2) ^ 3 + A * (r ^ 2) ^ 2 + (r * B) * (r ^ 2) +
        C0 * (r ^ 2) + (r * D) + E := by
  simp [depressedSextic68]
  ring

/-- Polynomial evaluation of a depressed octic. -/
theorem eval_depressedOctic68
    (L P0 Q0 R0 S0 T0 U0 V0 r : F) :
    (depressedOctic68 L P0 Q0 R0 S0 T0 U0 V0).eval r =
      r ^ 8 + L * r ^ 7 + P0 * r ^ 6 + Q0 * r ^ 5 + R0 * r ^ 4 +
        S0 * r ^ 3 + T0 * r ^ 2 + U0 * r + V0 := by
  simp [depressedOctic68]

/-- After `L = 0`, the octic center value is likewise even. -/
theorem eval_depressedOctic68_evenCoordinates
    (P0 Q0 R0 S0 T0 U0 V0 r : F) :
    (depressedOctic68 0 P0 Q0 R0 S0 T0 U0 V0).eval r =
      (r ^ 2) ^ 4 + P0 * (r ^ 2) ^ 3 + (r * Q0) * (r ^ 2) ^ 2 +
        R0 * (r ^ 2) ^ 2 + (r * S0) * (r ^ 2) + T0 * (r ^ 2) +
        (r * U0) + V0 := by
  simp [depressedOctic68]
  ring

variable {k : Type*} [Field k] [Algebra k F]

/-- Last-row rearrangement: the `dE` coefficient is exactly `B W`. -/
theorem lastRow_aligned_dE_coeff68
    (d : Derivation k F F)
    (A B C0 D E alpha gamma epsilon eta : F) :
    let U := integratedU68 0 A B C0 D E alpha 0 gamma 0 0
    let V := integratedV68 0 A B C0 D E alpha 0 gamma 0 epsilon eta
    let W := alignedLastRowShiftW68 A C0 gamma
    U * d E - D * d V =
      B * W * d E -
        D * (d V - ((4 / 9 : F) * A + alpha) * d E) := by
  intro U V W
  have hU := integratedU68_aligned_factor A B C0 D E alpha gamma
  simp only [U, V, W] at hU ⊢
  rw [hU]
  ring

end AlignedNonsquareEndgameAlgebra68

section QuadraticEndgame68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

local notation "F68" => AdjoinRoot (alignedQuadraticPolynomial46 H)

local instance quadraticEndgameCharZero68 : CharZero F68 :=
  charZero_of_injective_ringHom (algebraMap (RatFunc k) F68).injective

/-- The quadratic differential restricts to the standard derivative of
`k(x)` along the coefficient embedding. -/
theorem quadraticDerivation46_algebraMap_ratFunc68 (z : RatFunc k) :
    quadraticDerivation46 H
        (algebraMap (RatFunc k) F68 z) =
      algebraMap (RatFunc k) F68 (Differential.deriv z) := by
  simp only [quadraticDerivation46_apply]
  exact deriv_algebraMap z

/-- Deck-oddness of the aligned last integrated coefficient. -/
theorem NonsquareAlignedSourceCurveData68.U_odd
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j) :
    alignedQuadraticDeck46 H
        (integratedU68 0 S.A S.B S.C0 S.D S.E
          (algebraMap k F68 S.alpha) 0 (algebraMap k F68 S.gamma) 0 0) =
      - integratedU68 0 S.A S.B S.C0 S.D S.E
          (algebraMap k F68 S.alpha) 0 (algebraMap k F68 S.gamma) 0 0 := by
  simp only [integratedU68, map_add, map_sub, map_mul, map_div₀, map_pow,
    map_ofNat, map_zero, S.A_even, S.B_odd, S.C_even, S.D_odd, S.E_even,
    alignedQuadraticDeck46_ground]
  ring

set_option maxHeartbeats 2000000 in
/-- Deck-evenness of the aligned constant octic coefficient. -/
theorem NonsquareAlignedSourceCurveData68.V_even
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j) :
    alignedQuadraticDeck46 H
        (integratedV68 0 S.A S.B S.C0 S.D S.E
          (algebraMap k F68 S.alpha) 0 (algebraMap k F68 S.gamma) 0
          (algebraMap k F68 S.epsilon) (algebraMap k F68 S.eta)) =
      integratedV68 0 S.A S.B S.C0 S.D S.E
        (algebraMap k F68 S.alpha) 0 (algebraMap k F68 S.gamma) 0
        (algebraMap k F68 S.epsilon) (algebraMap k F68 S.eta) := by
  have hA := S.A_even
  have hB := S.B_odd
  have hC := S.C_even
  have hD := S.D_odd
  have hE := S.E_even
  simp only [integratedV68, map_add, map_sub, map_neg, map_mul, map_div₀,
    map_pow, map_ofNat, map_zero, map_one, hA, hB, hC, hD, hE,
    alignedQuadraticDeck46_ground]
  ring

/-- Deck-evenness of the aligned quadratic octic coefficient. -/
theorem NonsquareAlignedSourceCurveData68.T_even
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j) :
    alignedQuadraticDeck46 H
        (integratedT68 0 S.A S.B S.C0 S.D S.E
          (algebraMap k F68 S.alpha) 0 (algebraMap k F68 S.gamma)
          (algebraMap k F68 S.epsilon)) =
      integratedT68 0 S.A S.B S.C0 S.D S.E
        (algebraMap k F68 S.alpha) 0 (algebraMap k F68 S.gamma)
        (algebraMap k F68 S.epsilon) := by
  simp only [integratedT68, map_add, map_sub, map_mul, map_div₀, map_pow,
    map_ofNat, map_zero, S.A_even, S.B_odd, S.C_even, S.D_odd, S.E_even,
    alignedQuadraticDeck46_ground]
  ring

/-- Deck-oddness of the aligned cubic octic coefficient. -/
theorem NonsquareAlignedSourceCurveData68.S_odd
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j) :
    alignedQuadraticDeck46 H
        (integratedS68 0 S.A S.B S.C0 S.D
          (algebraMap k F68 S.alpha) 0 0) =
      - integratedS68 0 S.A S.B S.C0 S.D
          (algebraMap k F68 S.alpha) 0 0 := by
  simp only [integratedS68, map_add, map_mul, map_div₀, map_pow,
    map_ofNat, map_zero, S.A_even, S.B_odd, S.D_odd,
    alignedQuadraticDeck46_ground]
  ring

/-- Deck-oddness of the aligned quintic octic coefficient. -/
theorem NonsquareAlignedSourceCurveData68.Q_odd
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j) :
    alignedQuadraticDeck46 H
        (integratedQ68 0 S.A S.B 0) =
      - integratedQ68 0 S.A S.B 0 := by
  simp only [integratedQ68, map_add, map_mul, map_div₀, map_ofNat,
    map_zero, S.B_odd, alignedQuadraticDeck46_ground]
  ring

/-- Deck-evenness of the aligned sextic octic coefficient. -/
theorem NonsquareAlignedSourceCurveData68.P_even
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j) :
    alignedQuadraticDeck46 H
        (integratedP68 S.A (algebraMap k F68 S.alpha)) =
      integratedP68 S.A (algebraMap k F68 S.alpha) := by
  simp only [integratedP68, map_add, map_mul, map_div₀, map_ofNat,
    S.A_even, alignedQuadraticDeck46_ground]

/-- Deck-evenness of the aligned quartic octic coefficient. -/
theorem NonsquareAlignedSourceCurveData68.R_even
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j) :
    alignedQuadraticDeck46 H
        (integratedR68 0 S.A S.B S.C0 (algebraMap k F68 S.alpha)
          (algebraMap k F68 S.gamma)) =
      integratedR68 0 S.A S.B S.C0 (algebraMap k F68 S.alpha)
        (algebraMap k F68 S.gamma) := by
  simp only [integratedR68, map_add, map_mul, map_div₀, map_pow,
    map_ofNat, map_zero, S.A_even, S.B_odd, S.C_even,
    alignedQuadraticDeck46_ground]
  ring

/-- The mixed last-row scale `√H · U` is deck-even, hence descends. -/
theorem NonsquareAlignedSourceCurveData68.hU_even
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j) :
    alignedQuadraticDeck46 H
        (AdjoinRoot.root (alignedQuadraticPolynomial46 H) *
          integratedU68 0 S.A S.B S.C0 S.D S.E
            (algebraMap k F68 S.alpha) 0 (algebraMap k F68 S.gamma) 0 0) =
      AdjoinRoot.root (alignedQuadraticPolynomial46 H) *
        integratedU68 0 S.A S.B S.C0 S.D S.E
          (algebraMap k F68 S.alpha) 0 (algebraMap k F68 S.gamma) 0 0 := by
  simp only [map_mul, alignedQuadraticDeck46_root, S.U_odd]
  ring

/-- Square-core identity ` (√H B)² = H B² ` in the quadratic field. -/
theorem NonsquareAlignedSourceCurveData68.squareCoreB
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j) :
    (AdjoinRoot.root (alignedQuadraticPolynomial46 H) * S.B) ^ 2 =
      algebraMap (RatFunc k) F68 (algebraMap k[X] (RatFunc k) H) *
        S.B ^ 2 := by
  rw [mul_pow, alignedQuadraticRoot_sq46]

/-- Square-core identity ` (√H D)² = H D² `. -/
theorem NonsquareAlignedSourceCurveData68.squareCoreD
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j) :
    (AdjoinRoot.root (alignedQuadraticPolynomial46 H) * S.D) ^ 2 =
      algebraMap (RatFunc k) F68 (algebraMap k[X] (RatFunc k) H) *
        S.D ^ 2 := by
  rw [mul_pow, alignedQuadraticRoot_sq46]

/-- Mixed identity `(r B)² = r² B²`. -/
theorem NonsquareAlignedSourceCurveData68.wSquareB
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j) :
    (S.r * S.B) ^ 2 = S.r ^ 2 * S.B ^ 2 := by
  ring

/-- Mixed identity `(r D)² = r² D²`. -/
theorem NonsquareAlignedSourceCurveData68.wSquareD
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j) :
    (S.r * S.D) ^ 2 = S.r ^ 2 * S.D ^ 2 := by
  ring

/-- Last-row nonvanishing: `U` and `D` cannot vanish together. -/
theorem NonsquareAlignedSourceCurveData68.lastRow_U_D_ne
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j) (hj : j ≠ 0) :
    ¬ (integratedU68 0 S.A S.B S.C0 S.D S.E
          (algebraMap k F68 S.alpha) 0 (algebraMap k F68 S.gamma) 0 0 = 0 ∧
        S.D = 0) := by
  intro hUD
  rcases hUD with ⟨hU0, hD0⟩
  have hlast := (S.residualPacket).2.2.2.2
  rw [hU0, hD0] at hlast
  simp at hlast
  exact hj ((algebraMap k F68).injective (by simpa using hlast.symm))

/-- Coordinate nonvanishing: `B` and `D` cannot vanish together. -/
theorem NonsquareAlignedSourceCurveData68.B_D_ne
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j) (hj : j ≠ 0) :
    ¬ (S.B = 0 ∧ S.D = 0) := by
  intro hBD
  rcases hBD with ⟨hB0, hD0⟩
  have hU :
      integratedU68 0 S.A S.B S.C0 S.D S.E
        (algebraMap k F68 S.alpha) 0 (algebraMap k F68 S.gamma) 0 0 = 0 := by
    rw [integratedU68_aligned_factor, hB0, hD0]
    simp
  exact NonsquareAlignedSourceCurveData68.lastRow_U_D_ne (H := H) S hj
    ⟨hU, hD0⟩

/-- On the source, `I₄ = 0` is the bilinear relation `B Φ + 6 W D = 0`. -/
theorem NonsquareAlignedSourceCurveData68.I4_factor
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j) :
    S.B * alignedFirstIntegralFourOddPart68 S.A S.B S.C0 S.E
          (algebraMap k F68 S.gamma) (algebraMap k F68 S.epsilon) +
        (6 : F68) * alignedLastRowShiftW68 S.A S.C0
          (algebraMap k F68 S.gamma) * S.D = 0 := by
  have hI4 := (S.residualPacket).1
  rw [← firstIntegralFour68_aligned_factor]
  exact hI4

/-- The last Keller row rearranges so that the coefficient of `dE` is
`B W`. -/
theorem NonsquareAlignedSourceCurveData68.lastRow_dE_coeff
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j) :
    let ck := algebraMap k F68
    let d := quadraticDerivation46 H
    let U := integratedU68 0 S.A S.B S.C0 S.D S.E (ck S.alpha) 0
      (ck S.gamma) 0 0
    let V := integratedV68 0 S.A S.B S.C0 S.D S.E (ck S.alpha) 0
      (ck S.gamma) 0 (ck S.epsilon) (ck S.eta)
    let W := alignedLastRowShiftW68 S.A S.C0 (ck S.gamma)
    U * d S.E - S.D * d V =
      S.B * W * d S.E -
        S.D * (d V - ((4 / 9 : F68) * S.A + ck S.alpha) * d S.E) := by
  intro ck d U V W
  simpa only [ck, d, U, V, W] using
    lastRow_aligned_dE_coeff68 (quadraticDerivation46 H)
      S.A S.B S.C0 S.D S.E (algebraMap k F68 S.alpha)
      (algebraMap k F68 S.gamma) (algebraMap k F68 S.epsilon)
      (algebraMap k F68 S.eta)

/-- Last-row ingredients `√H U` and `V` descend to `k(x)`. -/
theorem NonsquareAlignedSourceCurveData68.lastRowCoordinatesDescend
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j) :
    (∃ mU : RatFunc k,
        AdjoinRoot.root (alignedQuadraticPolynomial46 H) *
            integratedU68 0 S.A S.B S.C0 S.D S.E
              (algebraMap k F68 S.alpha) 0 (algebraMap k F68 S.gamma) 0 0 =
          algebraMap (RatFunc k) F68 mU) ∧
    (∃ vR : RatFunc k,
        integratedV68 0 S.A S.B S.C0 S.D S.E
            (algebraMap k F68 S.alpha) 0 (algebraMap k F68 S.gamma) 0
            (algebraMap k F68 S.epsilon) (algebraMap k F68 S.eta) =
          algebraMap (RatFunc k) F68 vR) ∧
    (∃ tR : RatFunc k,
        integratedT68 0 S.A S.B S.C0 S.D S.E
            (algebraMap k F68 S.alpha) 0 (algebraMap k F68 S.gamma)
            (algebraMap k F68 S.epsilon) =
          algebraMap (RatFunc k) F68 tR) ∧
    (∃ pR : RatFunc k,
        integratedP68 S.A (algebraMap k F68 S.alpha) =
          algebraMap (RatFunc k) F68 pR) ∧
    (∃ rR : RatFunc k,
        integratedR68 0 S.A S.B S.C0 (algebraMap k F68 S.alpha)
            (algebraMap k F68 S.gamma) =
          algebraMap (RatFunc k) F68 rR) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact alignedQuadraticFixedElementDescends46 H _ S.hU_even
  · exact alignedQuadraticFixedElementDescends46 H _ S.V_even
  · exact alignedQuadraticFixedElementDescends46 H _ S.T_even
  · exact alignedQuadraticFixedElementDescends46 H _ S.P_even
  · exact alignedQuadraticFixedElementDescends46 H _ S.R_even

/-- The last Keller row is already a `k(x)` identity:
`(√H U) E' - (√H D) V' = j`. -/
theorem NonsquareAlignedSourceCurveData68.lastRow_descends
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j) :
    ∃ mU eR mD vR : RatFunc k,
      AdjoinRoot.root (alignedQuadraticPolynomial46 H) *
          integratedU68 0 S.A S.B S.C0 S.D S.E
            (algebraMap k F68 S.alpha) 0 (algebraMap k F68 S.gamma) 0 0 =
        algebraMap (RatFunc k) F68 mU ∧
      S.E = algebraMap (RatFunc k) F68 eR ∧
      AdjoinRoot.root (alignedQuadraticPolynomial46 H) * S.D =
        algebraMap (RatFunc k) F68 mD ∧
      integratedV68 0 S.A S.B S.C0 S.D S.E
          (algebraMap k F68 S.alpha) 0 (algebraMap k F68 S.gamma) 0
          (algebraMap k F68 S.epsilon) (algebraMap k F68 S.eta) =
        algebraMap (RatFunc k) F68 vR ∧
      mU * Differential.deriv eR - mD * Differential.deriv vR =
        algebraMap k (RatFunc k) j := by
  obtain ⟨⟨mU, hmU⟩, ⟨vR, hvR⟩, _hT, _hP, _hR⟩ :=
    S.lastRowCoordinatesDescend
  obtain ⟨_ha, _hc, ⟨eR, heR⟩, _hq, _hkb, _hkd, _hwb, _hwd, _hmb,
      ⟨mD, hmD⟩⟩ := S.evenCoordinatesDescend
  refine ⟨mU, eR, mD, vR, hmU, heR, hmD, hvR, ?_⟩
  have hlast := (S.residualPacket).2.2.2.2
  have hsplit :
      AdjoinRoot.root (alignedQuadraticPolynomial46 H) *
          (integratedU68 0 S.A S.B S.C0 S.D S.E
              (algebraMap k F68 S.alpha) 0 (algebraMap k F68 S.gamma) 0 0 *
            quadraticDerivation46 H S.E -
            S.D * quadraticDerivation46 H
              (integratedV68 0 S.A S.B S.C0 S.D S.E
                (algebraMap k F68 S.alpha) 0 (algebraMap k F68 S.gamma) 0
                (algebraMap k F68 S.epsilon) (algebraMap k F68 S.eta))) =
        (AdjoinRoot.root (alignedQuadraticPolynomial46 H) *
            integratedU68 0 S.A S.B S.C0 S.D S.E
              (algebraMap k F68 S.alpha) 0 (algebraMap k F68 S.gamma) 0 0) *
          quadraticDerivation46 H S.E -
          (AdjoinRoot.root (alignedQuadraticPolynomial46 H) * S.D) *
            quadraticDerivation46 H
              (integratedV68 0 S.A S.B S.C0 S.D S.E
                (algebraMap k F68 S.alpha) 0 (algebraMap k F68 S.gamma) 0
                (algebraMap k F68 S.epsilon) (algebraMap k F68 S.eta)) := by
    ring
  have hdE : quadraticDerivation46 H S.E =
      algebraMap (RatFunc k) F68 (Differential.deriv eR) := by
    rw [heR]
    exact quadraticDerivation46_algebraMap_ratFunc68 H eR
  have hdV :
      quadraticDerivation46 H
          (integratedV68 0 S.A S.B S.C0 S.D S.E
            (algebraMap k F68 S.alpha) 0 (algebraMap k F68 S.gamma) 0
            (algebraMap k F68 S.epsilon) (algebraMap k F68 S.eta)) =
        algebraMap (RatFunc k) F68 (Differential.deriv vR) := by
    rw [hvR]
    exact quadraticDerivation46_algebraMap_ratFunc68 H vR
  have hF :
      algebraMap (RatFunc k) F68
          (mU * Differential.deriv eR - mD * Differential.deriv vR) =
        algebraMap k F68 j := by
    simp only [map_sub, map_mul]
    rw [← hmU, ← hmD, ← hdE, ← hdV, ← hsplit, hlast]
  have hι : Function.Injective (algebraMap (RatFunc k) F68) :=
    (algebraMap (RatFunc k) F68).injective
  have hjR : algebraMap k F68 j =
      algebraMap (RatFunc k) F68 (algebraMap k (RatFunc k) j) :=
    (IsScalarTower.algebraMap_apply k (RatFunc k) F68 j).symm
  exact hι (hF.trans hjR)

/-- Square relations among the descended even coordinates. -/
theorem NonsquareAlignedSourceCurveData68.squareRelations_ratFunc
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j) :
    ∃ qR kB kD wB wD mB mD : RatFunc k,
      S.r ^ 2 = algebraMap (RatFunc k) F68 qR ∧
      S.B ^ 2 = algebraMap (RatFunc k) F68 kB ∧
      S.D ^ 2 = algebraMap (RatFunc k) F68 kD ∧
      S.r * S.B = algebraMap (RatFunc k) F68 wB ∧
      S.r * S.D = algebraMap (RatFunc k) F68 wD ∧
      AdjoinRoot.root (alignedQuadraticPolynomial46 H) * S.B =
        algebraMap (RatFunc k) F68 mB ∧
      AdjoinRoot.root (alignedQuadraticPolynomial46 H) * S.D =
        algebraMap (RatFunc k) F68 mD ∧
      wB ^ 2 = qR * kB ∧
      wD ^ 2 = qR * kD ∧
      mB ^ 2 = algebraMap k[X] (RatFunc k) H * kB ∧
      mD ^ 2 = algebraMap k[X] (RatFunc k) H * kD := by
  obtain ⟨_ha, _hc, _he, ⟨qR, hqR⟩, ⟨kB, hkB⟩, ⟨kD, hkD⟩, ⟨wB, hwB⟩,
      ⟨wD, hwD⟩, ⟨mB, hmB⟩, ⟨mD, hmD⟩⟩ := S.evenCoordinatesDescend
  have hι : Function.Injective (algebraMap (RatFunc k) F68) :=
    (algebraMap (RatFunc k) F68).injective
  refine ⟨qR, kB, kD, wB, wD, mB, mD, hqR, hkB, hkD, hwB, hwD, hmB, hmD,
      ?_, ?_, ?_, ?_⟩
  · apply hι
    simp only [map_mul, map_pow]
    rw [← hwB, ← hqR, ← hkB]
    exact S.wSquareB
  · apply hι
    simp only [map_mul, map_pow]
    rw [← hwD, ← hqR, ← hkD]
    exact S.wSquareD
  · apply hι
    simp only [map_mul, map_pow]
    rw [← hmB, ← hkB, S.squareCoreB]
  · apply hι
    simp only [map_mul, map_pow]
    rw [← hmD, ← hkD, S.squareCoreD]

/-- The sextic center evaluation is a polynomial image of the even
combination of descended coordinates. -/
theorem NonsquareAlignedSourceCurveData68.centerSextic_even
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j) :
    (S.r ^ 2) ^ 3 + S.A * (S.r ^ 2) ^ 2 + (S.r * S.B) * (S.r ^ 2) +
        S.C0 * (S.r ^ 2) + (S.r * S.D) + S.E =
      quadraticCoefficientMap46 H (p.coeff 0) := by
  have hcenter := S.centerSextic
  rw [eval_depressedSextic68_evenCoordinates] at hcenter
  exact hcenter

/-- Residual packet after quadratic-field descent: last row in `k(x)`,
square relations `M² = H K`, the factored first integral, last-row
`dE`-coefficient `B W`, and last-row nonvanishing.  No polynomial
representatives or unit-product contradiction is claimed. -/
theorem NonsquareAlignedSourceCurveData68.descendedPacket
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j) (hj : j ≠ 0) :
    firstIntegralFour68 0 S.A S.B S.C0 S.D S.E 0
        (algebraMap k F68 S.gamma) 0 (algebraMap k F68 S.epsilon) 0 = 0 ∧
    (∃ i3 : k,
      firstIntegralThree68 0 S.A S.B S.C0 S.D S.E 0
          (algebraMap k F68 S.gamma) 0 (algebraMap k F68 S.epsilon) 0 =
        algebraMap k F68 i3) ∧
    S.B * alignedFirstIntegralFourOddPart68 S.A S.B S.C0 S.E
          (algebraMap k F68 S.gamma) (algebraMap k F68 S.epsilon) +
        (6 : F68) * alignedLastRowShiftW68 S.A S.C0
          (algebraMap k F68 S.gamma) * S.D = 0 ∧
    ¬ (S.B = 0 ∧ S.D = 0) ∧
    ¬ (integratedU68 0 S.A S.B S.C0 S.D S.E
          (algebraMap k F68 S.alpha) 0 (algebraMap k F68 S.gamma) 0 0 = 0 ∧
        S.D = 0) ∧
    (∃ qR kB kD wB wD mB mD : RatFunc k,
      S.r ^ 2 = algebraMap (RatFunc k) F68 qR ∧
      S.B ^ 2 = algebraMap (RatFunc k) F68 kB ∧
      S.D ^ 2 = algebraMap (RatFunc k) F68 kD ∧
      S.r * S.B = algebraMap (RatFunc k) F68 wB ∧
      S.r * S.D = algebraMap (RatFunc k) F68 wD ∧
      AdjoinRoot.root (alignedQuadraticPolynomial46 H) * S.B =
        algebraMap (RatFunc k) F68 mB ∧
      AdjoinRoot.root (alignedQuadraticPolynomial46 H) * S.D =
        algebraMap (RatFunc k) F68 mD ∧
      wB ^ 2 = qR * kB ∧
      wD ^ 2 = qR * kD ∧
      mB ^ 2 = algebraMap k[X] (RatFunc k) H * kB ∧
      mD ^ 2 = algebraMap k[X] (RatFunc k) H * kD) ∧
    (∃ mU eR mD vR : RatFunc k,
      AdjoinRoot.root (alignedQuadraticPolynomial46 H) *
          integratedU68 0 S.A S.B S.C0 S.D S.E
            (algebraMap k F68 S.alpha) 0 (algebraMap k F68 S.gamma) 0 0 =
        algebraMap (RatFunc k) F68 mU ∧
      S.E = algebraMap (RatFunc k) F68 eR ∧
      AdjoinRoot.root (alignedQuadraticPolynomial46 H) * S.D =
        algebraMap (RatFunc k) F68 mD ∧
      integratedV68 0 S.A S.B S.C0 S.D S.E
          (algebraMap k F68 S.alpha) 0 (algebraMap k F68 S.gamma) 0
          (algebraMap k F68 S.epsilon) (algebraMap k F68 S.eta) =
        algebraMap (RatFunc k) F68 vR ∧
      mU * Differential.deriv eR - mD * Differential.deriv vR =
        algebraMap k (RatFunc k) j) := by
  refine ⟨(S.residualPacket).1, (S.residualPacket).2.1, S.I4_factor,
      NonsquareAlignedSourceCurveData68.B_D_ne (H := H) S hj,
      NonsquareAlignedSourceCurveData68.lastRow_U_D_ne (H := H) S hj,
      S.squareRelations_ratFunc, S.lastRow_descends⟩

end QuadraticEndgame68

#print axioms integratedU68_aligned_factor
#print axioms firstIntegralFour68_aligned_factor
#print axioms eval_depressedSextic68
#print axioms eval_depressedSextic68_evenCoordinates
#print axioms eval_depressedOctic68
#print axioms eval_depressedOctic68_evenCoordinates
#print axioms lastRow_aligned_dE_coeff68
#print axioms quadraticDerivation46_algebraMap_ratFunc68
#print axioms NonsquareAlignedSourceCurveData68.U_odd
#print axioms NonsquareAlignedSourceCurveData68.V_even
#print axioms NonsquareAlignedSourceCurveData68.T_even
#print axioms NonsquareAlignedSourceCurveData68.S_odd
#print axioms NonsquareAlignedSourceCurveData68.Q_odd
#print axioms NonsquareAlignedSourceCurveData68.P_even
#print axioms NonsquareAlignedSourceCurveData68.R_even
#print axioms NonsquareAlignedSourceCurveData68.hU_even
#print axioms NonsquareAlignedSourceCurveData68.squareCoreB
#print axioms NonsquareAlignedSourceCurveData68.squareCoreD
#print axioms NonsquareAlignedSourceCurveData68.wSquareB
#print axioms NonsquareAlignedSourceCurveData68.wSquareD
#print axioms NonsquareAlignedSourceCurveData68.lastRow_U_D_ne
#print axioms NonsquareAlignedSourceCurveData68.B_D_ne
#print axioms NonsquareAlignedSourceCurveData68.I4_factor
#print axioms NonsquareAlignedSourceCurveData68.lastRow_dE_coeff
#print axioms NonsquareAlignedSourceCurveData68.lastRowCoordinatesDescend
#print axioms NonsquareAlignedSourceCurveData68.lastRow_descends
#print axioms NonsquareAlignedSourceCurveData68.squareRelations_ratFunc
#print axioms NonsquareAlignedSourceCurveData68.centerSextic_even
#print axioms NonsquareAlignedSourceCurveData68.descendedPacket

end Max11DegreeRoutes
