import Sol68ScaleTwoAlignedSquareBoundaryGSignedRayLinearDZeroB6EliminationScratch

/-! # Split the final `B[6]` resultant by its `I3(4)` coefficient wall -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareBoundaryGSignedRayLinearDZeroKWallSplit68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- The genuinely next unused source coefficient after `I3(4)`, retained in
its compact factored form.  This deliberately does not expand the fifth jet. -/
def rhoOne_boundaryG_i3fiveSourceCoefficient68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : k :=
  let A : RatFunc k := T.source.A
  let B : RatFunc k := T.source.B
  let C : RatFunc k := T.source.C0 - RatFunc.C (1 / 3 : k) * A ^ 2
  let F : RatFunc k := T.source.D - RatFunc.C (1 / 3 : k) * A * B
  let E : RatFunc k := T.source.E - RatFunc.C (1 / 27 : k) * A ^ 3
  let G : RatFunc k := E - RatFunc.C (1 / 3 : k) * A * C
  (ratFuncAtHahn46 T.root
    (rhoOneI3CapFactored68 (RatFunc.C T.source.gamma)
      (RatFunc.C T.source.epsilon) A B C F G)).coeff 5

/-- The factored fifth coefficient is source-backed directly by the global
constant `I3`; no new order or septic hypothesis is used. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_i3five_source68
    {p q : k[X][X]} {j : k} {h0 g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (Q : RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u) :
    rhoOne_boundaryG_i3fiveSourceCoefficient68 T = 0 := by
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
  obtain ⟨i4, i3, hi4f, hi3f, hi4src, hi3src⟩ :=
    T.rhoOne_boundary_integral_factors P hbeta hdelta hzeta
  have hc := congrArg
    (fun X : RatFunc k => (ratFuncAtHahn46 T.root X).coeff (5 : ℚ)) hi3f
  change (ratFuncAtHahn46 T.root
    (rhoOneI3CapFactored68 (RatFunc.C T.source.gamma)
      (RatFunc.C T.source.epsilon) A B C F G)).coeff 5 = 0
  rw [hi3f]
  simp [ratFuncAtHahn46_C]

/-- The exact refinement of the determinant-zero leaf after splitting
`K = r^4 B[2]^2 - 162 C[2] G[-2]`. -/
def rhoOne_boundaryG_signedRayLinearDZeroKWallWitness68
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
  ((D0 = 0 ∧
      1458 * sigma * G.coeff (-2) ^ 2 * r * B.coeff 6 =
        B.coeff 2 * T0 ∧
      4 * K * T0 + 177147 * sigma * G.coeff (-2) ^ 2 * r * I0 = 0) ∧
    ((K = 0 ∧ C.coeff 2 ≠ 0 ∧ I0 = 0) ∨
      (K ≠ 0 ∧ (T0 = 0 ↔ I0 = 0)))) ∨
  (D0 ≠ 0 ∧
    4 * D0 * rhoOne_boundaryG_signedRayLinearTerminalBase68 sigma r
      (A.coeff (-1)) (A.coeff 0) (B.coeff 2) (B.coeff 4)
      (C.coeff 2) (G.coeff (-2)) =
    -243 * G.coeff (-2) ^ 2 *
      rhoOne_boundaryG_signedRayLinearI3ThreeBase68 sigma r
        (A.coeff (-1)) (A.coeff 0) (A.coeff 1) (B.coeff 2)
        (B.coeff 4) (B.coeff 5) (C.coeff 2) (C.coeff 3)
        (C.coeff 4) (C.coeff 5) (F.coeff 1) (F.coeff 3)
        (G.coeff 2) (G.coeff 1) (G.coeff 0) (G.coeff (-2))
        T.source.epsilon)

/-- Source-facing K-wall split, with the minimal next `I3(5)` coefficient
recorded but not artificially expanded into a new jet tower. -/
def RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroKWallSplit68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroB6Elimination68 T ∧
  rhoOne_boundaryG_i3fiveSourceCoefficient68 T = 0 ∧
  ∃ sigma r : k, sigma ^ 2 = 1 ∧ r ≠ 0 ∧ B.coeff 2 ≠ 0 ∧
    G.coeff (-2) ≠ 0 ∧ r ^ 2 = -3 * A.coeff (-2) ∧
    27 * G.coeff (-1) = sigma * r ^ 3 * B.coeff 2 ∧
    r * F.coeff 0 = 3 * sigma * G.coeff (-1) ∧
    3 * C.coeff 1 + sigma * r * B.coeff 2 = 0 ∧ B.coeff 3 = 0 ∧
    rhoOne_boundaryG_signedRayLinearDZeroKWallWitness68 T sigma r

/-- Split the B6-free resultant.  On the wall, `C[2]` is nonzero and the
`I3(4)` base residual vanishes.  Off the wall, the terminal and `I3(4)`
base residuals vanish simultaneously. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_signedRay_linear_dZero_kwall_split68
    {p q : k[X][X]} {j : k} {h0 g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (Q : RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u)
    (R : RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroB6Elimination68 T) :
    RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroKWallSplit68 T := by
  have hrow := T.rhoOne_boundaryG_i3five_source68 Q
  have Rc := R
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroB6Elimination68] at Rc
  rcases Rc with ⟨Rkeep, sigma, r, hsigma, hr0, hb, hgm2, hr, hray,
    hrf, hlinear, hb3, hsplit⟩
  have hs0 : sigma ≠ 0 := by
    intro hs
    rw [hs] at hsigma
    norm_num at hsigma
  have hfinal :
      rhoOne_boundaryG_signedRayLinearDZeroKWallWitness68 T sigma r := by
    dsimp only [rhoOne_boundaryG_signedRayLinearDZeroKWallWitness68]
    rcases hsplit with hzero | hnon
    · left
      refine ⟨hzero, ?_⟩
      by_cases hk :
          r ^ 4 * (ratFuncAtHahn46 T.root T.source.B).coeff 2 ^ 2 -
            162 * (rhoOneCDefectHahn68
              (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.C0)).coeff 2 *
              (rhoOneTangentEDefectHahn68
                (ratFuncAtHahn46 T.root T.source.A)
                (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                  (ratFuncAtHahn46 T.root T.source.C0))
                (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                  (ratFuncAtHahn46 T.root T.source.E))).coeff (-2) = 0
      · left
        have hc2 : (rhoOneCDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.C0)).coeff 2 ≠ 0 := by
          intro hc
          have hleft : r ^ 4 *
              (ratFuncAtHahn46 T.root T.source.B).coeff 2 ^ 2 ≠ 0 :=
            mul_ne_zero (pow_ne_zero 4 hr0) (pow_ne_zero 2 hb)
          apply hleft
          calc
            r ^ 4 * (ratFuncAtHahn46 T.root T.source.B).coeff 2 ^ 2 =
                r ^ 4 * (ratFuncAtHahn46 T.root T.source.B).coeff 2 ^ 2 -
                  162 * (rhoOneCDefectHahn68
                    (ratFuncAtHahn46 T.root T.source.A)
                    (ratFuncAtHahn46 T.root T.source.C0)).coeff 2 *
                    (rhoOneTangentEDefectHahn68
                      (ratFuncAtHahn46 T.root T.source.A)
                      (rhoOneCDefectHahn68
                        (ratFuncAtHahn46 T.root T.source.A)
                        (ratFuncAtHahn46 T.root T.source.C0))
                      (rhoOneEDefectHahn68
                        (ratFuncAtHahn46 T.root T.source.A)
                        (ratFuncAtHahn46 T.root T.source.E))).coeff (-2) := by
                          rw [hc]
                          ring
            _ = 0 := hk
        have hi0 := hzero.2.2
        rw [hk] at hi0
        norm_num at hi0
        have hi0z :
            rhoOne_boundaryG_signedRayLinearDZeroI3FourAtB6Residual68
              T sigma r 0 = 0 := by
          rcases hi0 with (((hs | hg) | hrz) | hi0z)
          · exact (hs0 hs).elim
          · exact (hgm2 hg).elim
          · exact (hr0 hrz).elim
          · exact hi0z
        exact ⟨hk, hc2, hi0z⟩
      · right
        refine ⟨hk, ?_⟩
        constructor
        · intro ht0
          have hi0 := hzero.2.2
          rw [ht0] at hi0
          norm_num at hi0
          rcases hi0 with (((hs | hg) | hrz) | hi0z)
          · exact (hs0 hs).elim
          · exact (hgm2 hg).elim
          · exact (hr0 hrz).elim
          · exact hi0z
        · intro hi0
          have ht0 := hzero.2.2
          rw [hi0] at ht0
          norm_num at ht0
          exact ht0.resolve_left hk
    · exact Or.inr hnon
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroKWallSplit68]
  exact ⟨R, hrow, sigma, r, hsigma, hr0, hb, hgm2, hr, hray,
    hrf, hlinear, hb3, hfinal⟩

/-- Outer source selector; coordinate, QR, and nonsingular leaves are copied
literally, and only the determinant-zero signed-ray leaf is refined. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_signedRay_linear_dZero_kwall_split_selector68
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (Q : RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u) :
    RhoOneAlignedSquareGNegTwoCoordinateGain68 T g u ∨
      (RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u ∧
        (RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroKWallSplit68 T ∨
          RhoOneAlignedSquareGNegTwoSignedRayQRResidual68 T)) ∨
      (RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u ∧
        let A := ratFuncAtHahn46 T.root T.source.A
        let B := ratFuncAtHahn46 T.root T.source.B
        let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
        let G := rhoOneTangentEDefectHahn68 A C
          (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
        A.coeff (-2) ^ 3 * B.coeff 2 ^ 2 + 27 * G.coeff (-1) ^ 2 ≠ 0) := by
  rcases T.rhoOne_boundaryG_signedRay_linear_dZero_b6_elimination_selector68
      hp hH hp6 hp5 hp4 Q with hcoord | hsigned | hnon
  · exact Or.inl hcoord
  · rcases hsigned.2 with hzero | hqr
    · exact Or.inr (Or.inl ⟨hsigned.1,
        Or.inl (T.rhoOne_boundaryG_signedRay_linear_dZero_kwall_split68
          hsigned.1 hzero)⟩)
    · exact Or.inr (Or.inl ⟨hsigned.1, Or.inr hqr⟩)
  · exact Or.inr (Or.inr hnon)

end AlignedSquareBoundaryGSignedRayLinearDZeroKWallSplit68

end Max11DegreeRoutes
