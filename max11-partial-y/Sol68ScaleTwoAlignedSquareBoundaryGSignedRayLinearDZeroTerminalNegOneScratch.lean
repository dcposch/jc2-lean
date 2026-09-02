import Sol68ScaleTwoAlignedSquareBoundaryGSignedRayLinearDZeroI4FiveCrossScratch

/-! # The terminal leading coefficient on the signed linear `D=0` cells

Unlike terminal coefficient `-2`, coefficient `-1` is not zero: it is the
leading coefficient of the nonzero Keller terminal `j / h0`.  This packet
keeps that source-sensitive scalar exact and distributes its nonvanishing
over both cells of the already verified `K` split.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareBoundaryGSignedRayLinearDZeroTerminalNegOne68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- The literal coefficient `-1` of the source terminal after the rho-one
main-tangent substitution.  Derivatives are retained as actual source
derivatives; no local-coordinate jet is postulated. -/
def rhoOne_boundaryG_terminalNegOneSourceRow68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : k :=
  let A : RatFunc k := T.source.A
  let B : RatFunc k := T.source.B
  let C : RatFunc k := T.source.C0 - RatFunc.C (1 / 3 : k) * A ^ 2
  let F : RatFunc k := T.source.D - RatFunc.C (1 / 3 : k) * A * B
  let E : RatFunc k := T.source.E - RatFunc.C (1 / 27 : k) * A ^ 3
  let G : RatFunc k := E - RatFunc.C (1 / 3 : k) * A * C
  (rhoOneMainTangentTerminal68 (HahnSeries.C T.source.gamma)
    (HahnSeries.C T.source.epsilon)
    (ratFuncAtHahn46 T.root A) (ratFuncAtHahn46 T.root B)
    (ratFuncAtHahn46 T.root C) (ratFuncAtHahn46 T.root F)
    (ratFuncAtHahn46 T.root G)
    (ratFuncAtHahn46 T.root (Differential.deriv A))
    (ratFuncAtHahn46 T.root (Differential.deriv B))
    (ratFuncAtHahn46 T.root (Differential.deriv C))
    (ratFuncAtHahn46 T.root (Differential.deriv F))
    (ratFuncAtHahn46 T.root (Differential.deriv G))).coeff (-1)

omit [IsAlgClosed k] in
/-- The source terminal identity at coefficient `-1`.  Its right side has
order exactly `-1`, hence this coefficient is nonzero. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_terminal_negOne_source_ne68
    {p q : k[X][X]} {j : k} {h0 g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (Q : RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u) :
    rhoOne_boundaryG_terminalNegOneSourceRow68 T ≠ 0 := by
  have Qc := Q
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68] at Qc
  rcases Qc with ⟨Rm, hquadratic⟩
  have Rmc := Rm
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryMinor68] at Rmc
  rcases Rmc with ⟨Rtf, hminor⟩
  have Rtfc := Rtf
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryTerminalFollowing68] at Rtfc
  rcases Rtfc with ⟨Rt, i3two, i4three, hi3twoSrc, hi4threeSrc, hdet⟩
  have Rtc := Rt
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryTerminalNext68] at Rtc
  rcases Rtc with ⟨Rterm, i4two, hi4twoSrc, hi4two, hprev⟩
  have Rtermc := Rterm
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryTerminal68] at Rtermc
  rcases Rtermc with ⟨Rfol, i3one, hi3oneSrc, hi3one, hprevOne⟩
  have Rfolc := Rfol
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryFollowing68] at Rfolc
  rcases Rfolc with ⟨Rn, i4one, hi4oneSrc, hi4one, hcross⟩
  have Rnc := Rn
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryNext68] at Rnc
  rcases Rnc with ⟨Rbase, hi3zero, htermFour⟩
  have Rbasec := Rbase
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryResidual68] at Rbasec
  rcases Rbasec with ⟨P, hbeta, hdelta, hzeta, hB, hC, hF, hG,
    hfneg, hgneg, hb1, hS0, hscalar, hi4base⟩
  let A : RatFunc k := T.source.A
  let B : RatFunc k := T.source.B
  let C : RatFunc k := T.source.C0 - RatFunc.C (1 / 3 : k) * A ^ 2
  let F : RatFunc k := T.source.D - RatFunc.C (1 / 3 : k) * A * B
  let E : RatFunc k := T.source.E - RatFunc.C (1 / 27 : k) * A ^ 3
  let G : RatFunc k := E - RatFunc.C (1 / 3 : k) * A * C
  have hconst (x : k) : ratFuncDerivation68 (RatFunc.C x) = 0 := by
    have hx := GCD369RatFuncDerivative (Polynomial.C x)
    simpa [ratFuncDerivation68, RatFunc.algebraMap_C] using hx
  have hlow := constantBracket_integrated68_lowerSystem
    ratFuncDerivation68 (RatFunc.C 0) T.source.A T.source.B
      T.source.C0 T.source.D T.source.E (RatFunc.C T.source.alpha)
      (RatFunc.C T.source.beta) (RatFunc.C T.source.gamma)
      (RatFunc.C T.source.delta) (RatFunc.C T.source.epsilon)
      (RatFunc.C T.source.zeta) (RatFunc.C T.source.eta)
      (RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
      (hconst 0) (hconst T.source.alpha) (hconst T.source.beta)
      (hconst T.source.gamma) (hconst T.source.delta)
      (hconst T.source.epsilon) (hconst T.source.zeta)
      (hconst T.source.eta) T.source.bracket_eq
  rw [hbeta, hdelta, hzeta] at hlow
  have hCrec : A ^ 2 / 3 + C = T.source.C0 := by
    dsimp only [C, A]
    simp only [map_div₀, map_one, map_ofNat]
    ring
  have hDrec : A * B / 3 + F = T.source.D := by
    dsimp only [F, A, B]
    simp only [map_div₀, map_one, map_ofNat]
    ring
  have hErec : A ^ 3 / 27 + A * C / 3 + G = T.source.E := by
    dsimp only [G, E, C, A]
    simp only [map_div₀, map_one, map_ofNat]
    ring
  have hfactor := integratedTerminal_mainTangent_factorization68
    ratFuncDerivation68 (RatFunc.C T.source.alpha)
      (RatFunc.C T.source.gamma) (RatFunc.C T.source.epsilon)
      (RatFunc.C T.source.eta) A B C F G
      (hconst T.source.alpha) (hconst T.source.gamma)
      (hconst T.source.epsilon) (hconst T.source.eta)
  have hsparseR : rhoOneMainTangentTerminal68 (RatFunc.C T.source.gamma)
      (RatFunc.C T.source.epsilon) A B C F G
      (ratFuncDerivation68 A) (ratFuncDerivation68 B)
      (ratFuncDerivation68 C) (ratFuncDerivation68 F)
      (ratFuncDerivation68 G) =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0 := by
    rw [← hfactor, hCrec, hDrec, hErec]
    simpa only [map_zero] using hlow.2.2.2.2
  have hsparseH := congrArg (ratFuncAtHahn46 T.root) hsparseR
  have hsparseH' :
      rhoOneMainTangentTerminal68 (HahnSeries.C T.source.gamma)
        (HahnSeries.C T.source.epsilon)
        (ratFuncAtHahn46 T.root A) (ratFuncAtHahn46 T.root B)
        (ratFuncAtHahn46 T.root C) (ratFuncAtHahn46 T.root F)
        (ratFuncAtHahn46 T.root G)
        (ratFuncAtHahn46 T.root (Differential.deriv A))
        (ratFuncAtHahn46 T.root (Differential.deriv B))
        (ratFuncAtHahn46 T.root (Differential.deriv C))
        (ratFuncAtHahn46 T.root (Differential.deriv F))
        (ratFuncAtHahn46 T.root (Differential.deriv G)) =
      ratFuncAtHahn46 T.root
        (RatFunc.C j / algebraMap k[X] (RatFunc k) h0) := by
    simpa only [rhoOneMainTangentTerminal68, ratFuncDerivation68,
      ratFuncDerivation46_apply, map_add, map_mul, map_pow,
      ratFuncAtHahn46_C, map_div₀, map_neg, map_ofNat, map_one]
      using hsparseH
  have hlead : (ratFuncAtHahn46 T.root
      (RatFunc.C j / algebraMap k[X] (RatFunc k) h0)).coeff (-1) ≠ 0 :=
    HahnSeries.coeff_orderTop_ne T.terminal_order
  have hcoeff := congrArg
    (fun X : HahnSeries ℚ k => X.coeff (-1 : ℚ)) hsparseH'
  dsimp only [rhoOne_boundaryG_terminalNegOneSourceRow68]
  rw [hcoeff]
  exact hlead

/-- The exact two-cell reduction after adjoining terminal coefficient `-1`.
The row is nonzero on both cells; all earlier `I3(5)` and `I4(5)` equations
are retained literally. -/
def rhoOne_boundaryG_signedRayLinearDZeroTerminalNegOneCells68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (sigma r : k) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  let D0 := 3 * F.coeff 1 - A.coeff (-1) * B.coeff 2
  let K := r ^ 4 * B.coeff 2 ^ 2 - 162 * C.coeff 2 * G.coeff (-2)
  let T0 := rhoOne_boundaryG_signedRayLinearDZeroTerminalAtB6Residual68
    T sigma r 0
  let I0 := rhoOne_boundaryG_signedRayLinearDZeroI3FourAtB6Residual68
    T sigma r 0
  let I4b := rhoOne_boundaryG_signedRayLinearDZeroI4FiveBase68 T sigma r
  D0 = 0 →
    ((K = 0 ∧ C.coeff 2 ≠ 0 ∧ I0 = 0 ∧
        rhoOne_boundaryG_terminalNegOneSourceRow68 T ≠ 0 ∧
        I4b + (sigma * r ^ 3 * B.coeff 2 / 27) * B.coeff 6 = 0 ∧
        39366 * G.coeff (-2) ^ 2 * I4b +
          r ^ 2 * B.coeff 2 ^ 2 * T0 = 0 ∧
        8 * K * I4b - 9 * sigma * r ^ 3 * B.coeff 2 ^ 2 * I0 = 0) ∨
      (K ≠ 0 ∧ (T0 = 0 ↔ I0 = 0) ∧
        rhoOne_boundaryG_terminalNegOneSourceRow68 T ≠ 0 ∧
        I4b + (sigma * r ^ 3 * B.coeff 2 / 27) * B.coeff 6 = 0 ∧
        39366 * G.coeff (-2) ^ 2 * I4b +
          r ^ 2 * B.coeff 2 ^ 2 * T0 = 0 ∧
        8 * K * I4b - 9 * sigma * r ^ 3 * B.coeff 2 ^ 2 * I0 = 0))

/-- Source-facing terminal-leading packet. -/
def RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalNegOne68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroI4FiveCross68 T ∧
  rhoOne_boundaryG_terminalNegOneSourceRow68 T ≠ 0 ∧
  ∃ sigma r : k, sigma ^ 2 = 1 ∧ r ≠ 0 ∧ B.coeff 2 ≠ 0 ∧
    G.coeff (-2) ≠ 0 ∧ r ^ 2 = -3 * A.coeff (-2) ∧
    27 * G.coeff (-1) = sigma * r ^ 3 * B.coeff 2 ∧
    r * F.coeff 0 = 3 * sigma * G.coeff (-1) ∧
    3 * C.coeff 1 + sigma * r * B.coeff 2 = 0 ∧ B.coeff 3 = 0 ∧
    rhoOne_boundaryG_signedRayLinearDZeroKWallWitness68 T sigma r ∧
    rhoOne_boundaryG_signedRayLinearDZeroTerminalNegOneCells68 T sigma r

omit [IsAlgClosed k] in
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_signedRay_linear_dZero_terminal_negOne68
    {p q : k[X][X]} {j : k} {h0 g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (Q : RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u)
    (R : RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroI4FiveCross68 T) :
    RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalNegOne68 T := by
  have hlead := T.rhoOne_boundaryG_terminal_negOne_source_ne68 Q
  have Rc := R
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroI4FiveCross68] at Rc
  rcases Rc with ⟨Rkeep, hi4five, sigma, r, hsigma, hr0, hb, hgm2,
    hr, hray, hrf, hlinear, hb3, hwitness, hcross⟩
  have hcells :
      rhoOne_boundaryG_signedRayLinearDZeroTerminalNegOneCells68
        T sigma r := by
    dsimp only [rhoOne_boundaryG_signedRayLinearDZeroTerminalNegOneCells68]
    intro hD
    have hc := hcross hD
    have hw := hwitness
    dsimp only [rhoOne_boundaryG_signedRayLinearDZeroKWallWitness68] at hw
    rcases hw with hzero | hnon
    · rcases hzero with ⟨hbase, hsplit⟩
      rcases hsplit with hk | hnk
      · exact Or.inl ⟨hk.1, hk.2.1, hk.2.2, hlead,
          hc.1, hc.2.1, hc.2.2⟩
      · exact Or.inr ⟨hnk.1, hnk.2, hlead,
          hc.1, hc.2.1, hc.2.2⟩
    · exact (hnon.1 hD).elim
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalNegOne68]
  exact ⟨R, hlead, sigma, r, hsigma, hr0, hb, hgm2, hr, hray,
    hrf, hlinear, hb3, hwitness, hcells⟩

/-- Outer selector: coordinate, QR, and nonsingular leaves are unchanged. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_signedRay_linear_dZero_terminal_negOne_selector68
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (Q : RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u) :
    RhoOneAlignedSquareGNegTwoCoordinateGain68 T g u ∨
      (RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u ∧
        (RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalNegOne68 T ∨
          RhoOneAlignedSquareGNegTwoSignedRayQRResidual68 T)) ∨
      (RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u ∧
        let A := ratFuncAtHahn46 T.root T.source.A
        let B := ratFuncAtHahn46 T.root T.source.B
        let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
        let G := rhoOneTangentEDefectHahn68 A C
          (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
        A.coeff (-2) ^ 3 * B.coeff 2 ^ 2 + 27 * G.coeff (-1) ^ 2 ≠ 0) := by
  rcases T.rhoOne_boundaryG_signedRay_linear_dZero_i4five_cross_selector68
      hp hH hp6 hp5 hp4 Q with hcoord | hsigned | hnon
  · exact Or.inl hcoord
  · rcases hsigned.2 with hzero | hqr
    · exact Or.inr (Or.inl ⟨hsigned.1,
        Or.inl (T.rhoOne_boundaryG_signedRay_linear_dZero_terminal_negOne68
          hsigned.1 hzero)⟩)
    · exact Or.inr (Or.inl ⟨hsigned.1, Or.inr hqr⟩)
  · exact Or.inr (Or.inr hnon)

end AlignedSquareBoundaryGSignedRayLinearDZeroTerminalNegOne68

end Max11DegreeRoutes
