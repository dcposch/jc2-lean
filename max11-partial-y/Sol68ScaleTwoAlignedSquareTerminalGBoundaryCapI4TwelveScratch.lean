import Sol68ScaleTwoAlignedSquareTerminalGBoundaryCapI3EightScratch

/-! # The `I₄[12]` jet and second cap transport -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareTerminalGBoundaryCapI4Twelve68

variable {k : Type*} [Field k] [CharZero k]

local instance alignedSquareTerminalGBoundaryCapI4TwelveHahnCharZero68 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-- Exact coefficient twelve of the fourth first integral at the cap. -/
theorem rhoOneI4ZeroFactored_cap_coeff_twelve68
    (root gamma epsilon : k) (B C F G : RatFunc k)
    (hB : (↑(11 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 root B).orderTop)
    (hF : (↑(3 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 root F).orderTop)
    (hG : (↑(-1 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 root G).orderTop)
    (hS : (↑(7 : ℚ) : WithTop ℚ) ≤
      (2 * ratFuncAtHahn46 root C + HahnSeries.C (3 * gamma)).orderTop)
    (hfactor : rhoOneI4ZeroFactored68
      (RatFunc.C gamma) (RatFunc.C epsilon) B C F G = 0) :
    4 * ((ratFuncAtHahn46 root B).coeff (11 : ℚ) *
          (ratFuncAtHahn46 root G).coeff (1 : ℚ) +
        (ratFuncAtHahn46 root B).coeff (12 : ℚ) *
          (ratFuncAtHahn46 root G).coeff (0 : ℚ) +
        (ratFuncAtHahn46 root B).coeff (13 : ℚ) *
          (ratFuncAtHahn46 root G).coeff (-1 : ℚ)) +
      4 * ((ratFuncAtHahn46 root C).coeff (7 : ℚ) *
          (ratFuncAtHahn46 root F).coeff (5 : ℚ) +
        (ratFuncAtHahn46 root C).coeff (8 : ℚ) *
          (ratFuncAtHahn46 root F).coeff (4 : ℚ) +
        (ratFuncAtHahn46 root C).coeff (9 : ℚ) *
          (ratFuncAtHahn46 root F).coeff (3 : ℚ)) +
      3 * epsilon * (ratFuncAtHahn46 root B).coeff (12 : ℚ) = 0 := by
  let BL : LaurentSeries k := ratFuncAtLaurent46 root B
  let CL : LaurentSeries k := ratFuncAtLaurent46 root C
  let FL : LaurentSeries k := ratFuncAtLaurent46 root F
  let Gser : LaurentSeries k := ratFuncAtLaurent46 root G
  let SR : RatFunc k := 2 * C + RatFunc.C (3 * gamma)
  let SL : LaurentSeries k := 2 * CL + HahnSeries.C (3 * gamma)
  have hBL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root B 11 hB
  have hFL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root F 3 hF
  have hGL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root G (-1) hG
  have hSRH : ratFuncAtHahn46 root SR =
      2 * ratFuncAtHahn46 root C + HahnSeries.C (3 * gamma) := by
    dsimp only [SR]
    simp only [map_add, map_mul, map_ofNat, ratFuncAtHahn46_C]
  have hSRL : ratFuncAtLaurent46 root SR = SL := by
    dsimp only [SR, SL, CL]
    simp only [map_add, map_mul, map_ofNat, ratFuncAtLaurent46_C68]
  have hSL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root SR 7 (by
    rw [hSRH]
    exact hS)
  rw [hSRL] at hSL
  have hBG := laurent_coeff_mul_lower_two68 BL Gser 11 (-1) hBL hGL
  have hSF := laurent_coeff_mul_lower_two68 SL FL 7 3 hSL hFL
  norm_num at hBG hSF
  have hBcubeOrder : (↑(33 : ℤ) : WithTop ℤ) ≤ (BL ^ 3).orderTop := by
    have hp := HahnSeries.orderTop_nsmul_le_orderTop_pow (x := BL) (n := 3)
    have htriple := nsmul_le_nsmul_right hBL 3
    norm_num at htriple
    exact le_trans htriple hp
  have hBcube : (BL ^ 3).coeff (12 : ℤ) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hBcubeOrder)
  have hfactorL := congrArg (ratFuncAtLaurent46 root) hfactor
  have hfactorL' : rhoOneI4ZeroFactored68
      (HahnSeries.C gamma) (HahnSeries.C epsilon) BL CL FL Gser = 0 := by
    simpa only [rhoOneI4ZeroFactored68, BL, CL, FL, Gser, map_add,
      map_mul, map_pow, map_neg, map_div₀, map_ofNat, map_zero, map_one,
      ratFuncAtLaurent46_C68] using hfactorL
  have hSLform : 2 * CL + 3 * HahnSeries.C gamma = SL := by
    dsimp only [SL]
    congr 1
    rw [HahnSeries.C_eq_algebraMap, map_mul, map_ofNat]
  rw [rhoOneI4ZeroFactored68, hSLform] at hfactorL'
  have hc := congrArg (fun X : LaurentSeries k => X.coeff (12 : ℤ)) hfactorL'
  simp only [HahnSeries.coeff_add, HahnSeries.coeff_zero] at hc
  have hscale (s : k) (X : LaurentSeries k) (r : ℤ) :
      (HahnSeries.C s * X).coeff r = s * X.coeff r := by
    rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]
  have hsc1 : ((-8 / 27 : LaurentSeries k) * BL ^ 3).coeff 12 = 0 := by
    have hcst : (-8 / 27 : LaurentSeries k) =
        HahnSeries.C (-8 / 27 : k) := by
      rw [HahnSeries.C_eq_algebraMap, map_div₀, map_neg, map_ofNat, map_ofNat]
    rw [hcst, hscale, hBcube, mul_zero]
  have hsc2 : ((8 / 3 : LaurentSeries k) * BL * Gser).coeff 12 =
      (8 / 3 : k) * (BL * Gser).coeff 12 := by
    have hcst : (8 / 3 : LaurentSeries k) = HahnSeries.C (8 / 3 : k) := by
      rw [HahnSeries.C_eq_algebraMap, map_div₀, map_ofNat, map_ofNat]
    rw [mul_assoc, hcst, hscale]
  have hsc3 : ((4 / 3 : LaurentSeries k) * SL * FL).coeff 12 =
      (4 / 3 : k) * (SL * FL).coeff 12 := by
    have hcst : (4 / 3 : LaurentSeries k) = HahnSeries.C (4 / 3 : k) := by
      rw [HahnSeries.C_eq_algebraMap, map_div₀, map_ofNat, map_ofNat]
    rw [mul_assoc, hcst, hscale]
  have hsc4 : ((2 : LaurentSeries k) * HahnSeries.C epsilon * BL).coeff 12 =
      (2 * epsilon) * BL.coeff 12 := by
    have h2 : (2 : LaurentSeries k) = HahnSeries.C (2 : k) := by
      rw [HahnSeries.C_eq_algebraMap, map_ofNat]
    rw [h2, ← map_mul, hscale]
  rw [hsc1, hsc2, hsc3, hsc4, hBG, hSF] at hc
  have hSL7 : SL.coeff 7 = 2 * CL.coeff 7 := by
    dsimp only [SL]
    simp [HahnSeries.C_apply, two_mul]
  have hSL8 : SL.coeff 8 = 2 * CL.coeff 8 := by
    dsimp only [SL]
    simp [HahnSeries.C_apply, two_mul]
  have hSL9 : SL.coeff 9 = 2 * CL.coeff 9 := by
    dsimp only [SL]
    simp [HahnSeries.C_apply, two_mul]
  rw [hSL7, hSL8, hSL9] at hc
  have hB11 := ratFuncAtHahn46_coeff_int68 root B 11
  have hB12 := ratFuncAtHahn46_coeff_int68 root B 12
  have hB13 := ratFuncAtHahn46_coeff_int68 root B 13
  have hC7 := ratFuncAtHahn46_coeff_int68 root C 7
  have hC8 := ratFuncAtHahn46_coeff_int68 root C 8
  have hC9 := ratFuncAtHahn46_coeff_int68 root C 9
  have hF3 := ratFuncAtHahn46_coeff_int68 root F 3
  have hF4 := ratFuncAtHahn46_coeff_int68 root F 4
  have hF5 := ratFuncAtHahn46_coeff_int68 root F 5
  have hGm1 := ratFuncAtHahn46_coeff_int68 root G (-1)
  have hG0 := ratFuncAtHahn46_coeff_int68 root G 0
  have hG1 := ratFuncAtHahn46_coeff_int68 root G 1
  norm_num at hB11 hB12 hB13 hC7 hC8 hC9 hF3 hF4 hF5 hGm1 hG0 hG1
  dsimp only [BL, CL, FL, Gser] at hc
  rw [← hB11, ← hB12, ← hB13, ← hC7, ← hC8, ← hC9,
    ← hF3, ← hF4, ← hF5, ← hGm1, ← hG0, ← hG1] at hc
  linear_combination (3 / 2 : k) * hc

/-- The second scale-free cap transport obtained from `I₃[7]`, `I₃[8]`,
`I₄[12]`, and the first transport. -/
theorem rhoOneI3I4_coordinate_cap_second_transport68
    (b b' b'' c c' c'' f f' f'' g g' g'' epsilon : k)
    (hb : b ≠ 0) (hg : g ≠ 0)
    (hcap : b * g + c * f = 0)
    (hscalar : b * f = 2 * c ^ 2)
    (htransport : c * f' - b' * g - 2 * c' * f = 0)
    (hi3seven : 4 * (c * g' + c' * g + f * f') + 3 * epsilon * c = 0)
    (hi3eight : 4 * (c * g'' + c' * g' + c'' * g + f * f'') +
      2 * f' ^ 2 + 3 * epsilon * c' = 0)
    (hi4twelve : 4 * (b * g'' + b' * g' + b'' * g) +
      4 * (c * f'' + c' * f' + c'' * f) + 3 * epsilon * b' = 0) :
    2 * c' ^ 2 + 4 * c * c'' - b'' * f - b' * f' - b * f'' = 0 := by
  let T := 2 * c' ^ 2 + 4 * c * c'' - b'' * f - b' * f' - b * f''
  have hdet :
      c * (b * (4 * (c * g'' + c' * g' + c'' * g + f * f'') +
            2 * f' ^ 2 + 3 * epsilon * c') -
          c * (4 * (b * g'' + b' * g' + b'' * g) +
            4 * (c * f'' + c' * f' + c'' * f) + 3 * epsilon * b')) -
        (b * c' - c * b') *
          (4 * (c * g' + c' * g + f * f') + 3 * epsilon * c) = 0 := by
    linear_combination c * b * hi3eight - c ^ 2 * hi4twelve -
      (b * c' - c * b') * hi3seven
  have hprod : 2 * b * g * T = 0 := by
    linear_combination hdet -
      (-8 * c' ^ 2 - 4 * c * c'' + 4 * b' * f' + 2 * b * f'') * hcap -
      (2 * c * f'' + 2 * b'' * g) * hscalar -
      (-4 * c * c' + 2 * b * f') * htransport
  have htwo : (2 : k) ≠ 0 := by norm_num
  have hnonzero : 2 * b * g ≠ 0 := mul_ne_zero (mul_ne_zero htwo hb) hg
  have hT := (mul_eq_zero.mp hprod).resolve_left hnonzero
  simpa only [T] using hT

/-- Multiplying the cleared-source scalar by `F₄` and using the second
transport removes the product `B₁₂F₄`. -/
theorem rhoOneTerminal_cap_second_transport_source68
    (s source a1 b b' b'' c c' c'' f f' f'' g d3 : k)
    (hsource :
      2 * s ^ 2 * g * d3 * (b' * g + c' * f) - f ^ 3 * source +
          2 * s ^ 2 * f ^ 3 * a1 -
        2 * s ^ 2 * f ^ 2 * f' * d3 = 0)
    (htransport :
      2 * c' ^ 2 + 4 * c * c'' - b'' * f - b' * f' - b * f'' = 0) :
    2 * s ^ 2 * g * d3 *
          (g * (2 * c' ^ 2 + 4 * c * c'' - b'' * f - b * f'') +
            c' * f * f') -
        f ^ 3 * f' * source + 2 * s ^ 2 * f ^ 3 * f' * a1 -
      2 * s ^ 2 * f ^ 2 * f' ^ 2 * d3 = 0 := by
  linear_combination f' * hsource + 2 * s ^ 2 * g ^ 2 * d3 * htransport

/-- The cap packet after `I₄[12]`, its second transport, and the resulting
source-sensitive scalar. -/
def RhoOneDoubleZeroTerminalGBoundaryCapI4TwelvePacket68
    (gamma epsilon i3 s source : k)
    (A B C F G dA : HahnSeries ℚ k) : Prop :=
  RhoOneDoubleZeroTerminalGBoundaryCapI3EightPacket68
      gamma epsilon i3 s source A B C F G dA ∧
    4 * (B.coeff (11 : ℚ) * G.coeff (1 : ℚ) +
          B.coeff (12 : ℚ) * G.coeff (0 : ℚ) +
          B.coeff (13 : ℚ) * G.coeff (-1 : ℚ)) +
        4 * (C.coeff (7 : ℚ) * F.coeff (5 : ℚ) +
          C.coeff (8 : ℚ) * F.coeff (4 : ℚ) +
          C.coeff (9 : ℚ) * F.coeff (3 : ℚ)) +
      3 * epsilon * B.coeff (12 : ℚ) = 0 ∧
    2 * C.coeff (8 : ℚ) ^ 2 +
        4 * C.coeff (7 : ℚ) * C.coeff (9 : ℚ) -
        B.coeff (13 : ℚ) * F.coeff (3 : ℚ) -
        B.coeff (12 : ℚ) * F.coeff (4 : ℚ) -
      B.coeff (11 : ℚ) * F.coeff (5 : ℚ) = 0 ∧
    2 * s ^ 2 * G.coeff (-1 : ℚ) * dA.coeff (-3 : ℚ) *
          (G.coeff (-1 : ℚ) *
              (2 * C.coeff (8 : ℚ) ^ 2 +
                4 * C.coeff (7 : ℚ) * C.coeff (9 : ℚ) -
                B.coeff (13 : ℚ) * F.coeff (3 : ℚ) -
                B.coeff (11 : ℚ) * F.coeff (5 : ℚ)) +
            C.coeff (8 : ℚ) * F.coeff (3 : ℚ) *
              F.coeff (4 : ℚ)) -
        F.coeff (3 : ℚ) ^ 3 * F.coeff (4 : ℚ) * source +
        2 * s ^ 2 * F.coeff (3 : ℚ) ^ 3 * F.coeff (4 : ℚ) *
          A.coeff (-1 : ℚ) -
      2 * s ^ 2 * F.coeff (3 : ℚ) ^ 2 * F.coeff (4 : ℚ) ^ 2 *
        dA.coeff (-3 : ℚ) = 0

/-- Only the already isolated cap child is refined; the C2 consolidation
and every non-cap sibling remain in the predecessor residual. -/
def RhoOneDoubleZeroTerminalGBoundaryCapI4TwelveResidual68
    (root j gamma epsilon : k) (A0 : k[X])
    (h0R AR BR CR FR GR : RatFunc k)
    (A B C F G : HahnSeries ℚ k) : Prop :=
  RhoOneDoubleZeroTerminalGBoundaryCapI3EightResidual68
      root j gamma epsilon A0 h0R AR BR CR FR GR A B C F G ∧
    ((B.coeff (1 : ℚ) = 0 ∧
        2 * C.coeff (0 : ℚ) + 3 * gamma = 0) →
      C.coeff (1 : ℚ) = 0 → C.coeff (2 : ℚ) = 0 →
      ∃ i3 s : k, RhoOneDoubleZeroTerminalGBoundaryCapI4TwelvePacket68
        gamma epsilon i3 s (A0.derivative.eval root) A B C F G
          (ratFuncAtHahn46 root (Differential.deriv AR)))

/-- Literal source backwire of `I₄[12]` and both new transport relations. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_exceptional_doubleZero_refinedGZero_terminalGBoundaryCapI4TwelveResidual
    [IsAlgClosed k]
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (P : RhoOneZeroLCubicNextSourcePacket68 T g u)
    (hB : (↑(1 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root T.source.B).orderTop)
    (hC : (0 : WithTop ℚ) ≤
      (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0)).orderTop)
    (hF : (0 : WithTop ℚ) ≤
      (rhoOneTangentDDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.B)
        (ratFuncAtHahn46 T.root T.source.D)).orderTop)
    (hG : (↑(-1 : ℚ) : WithTop ℚ) ≤
      (rhoOneTangentEDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0))
        (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.E))).orderTop)
    (hbeta : T.source.beta = 0) (hdelta : T.source.delta = 0)
    (hzeta : T.source.zeta = 0) :
    let AR : RatFunc k := T.source.A
    let BR : RatFunc k := T.source.B
    let CR : RatFunc k := T.source.C0 - RatFunc.C (1 / 3 : k) * AR ^ 2
    let FR : RatFunc k := T.source.D - RatFunc.C (1 / 3 : k) * AR * BR
    let GR : RatFunc k :=
      (T.source.E - RatFunc.C (1 / 27 : k) * AR ^ 3) -
        RatFunc.C (1 / 3 : k) * AR * CR
    let A := ratFuncAtHahn46 T.root T.source.A
    let B := ratFuncAtHahn46 T.root T.source.B
    let C := rhoOneCDefectHahn68 A
      (ratFuncAtHahn46 T.root T.source.C0)
    let F := rhoOneTangentDDefectHahn68 A B
      (ratFuncAtHahn46 T.root T.source.D)
    let G := rhoOneTangentEDefectHahn68 A C
      (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
    RhoOneDoubleZeroTerminalGBoundaryCapI4TwelveResidual68
        T.root j T.source.gamma T.source.epsilon
        (localClearedA68RhoOne g u)
        (algebraMap k[X] (RatFunc k) h0) AR BR CR FR GR A B C F G ∨
      (G.coeff (-1 : ℚ) = 0 ∧ (0 : WithTop ℚ) ≤ G.orderTop ∧
        (RhoOneDoubleZeroRefinedGZeroTerminalBGainChild68
            T.source.gamma B C F ∨
         RhoOneDoubleZeroRefinedGZeroTerminalFGainChild68
            T.source.gamma B C F)) := by
  dsimp only [RhoOneDoubleZeroTerminalGBoundaryCapI4TwelveResidual68]
  have hnext := T.rhoOne_exceptional_doubleZero_refined_gZero
    P hB hC hF hG hbeta hdelta hzeta
  dsimp only at hnext
  rcases hnext with ⟨_, _, _, _, _, _, hsplit⟩
  rcases hsplit with hGne | ⟨hGzero, hG0, htail⟩
  · have hprevRaw :=
      T.rhoOne_exceptional_doubleZero_refinedGZero_terminalGBoundaryCapI3EightResidual
        hp hH hp6 hp5 hp4 P hB hC hF hG hbeta hdelta hzeta
    rcases hprevRaw with hprev | hbad
    · left
      refine ⟨hprev, ?_⟩
      intro hcoord hc1 hc2
      obtain ⟨i3, s, hpacket⟩ := hprev.2.2 hcoord hc1 hc2
      have hparts := hpacket
      dsimp only [RhoOneDoubleZeroTerminalGBoundaryCapI3EightPacket68,
        RhoOneDoubleZeroTerminalGBoundaryCapDerivativeNextPacket68,
        RhoOneDoubleZeroTerminalGBoundaryCapTerminalNextPacket68,
        RhoOneDoubleZeroTerminalGBoundaryCapNextJetPacket68,
        RhoOneDoubleZeroTerminalGBoundaryCI3CapPacket68] at hparts
      rcases hparts with
        ⟨⟨⟨⟨⟨hi3H, hc3, hc4, hc5, hc6, hb7, hb8, hb9, hb10,
                hS7, hB11, hcap3, hc7ne, hcap4, hb11ne, hBexact⟩,
              hscalar, hrow7, hrow11, htransport⟩,
            hterminal, hdependency⟩,
          hs, hsource, hsourceScalar⟩,
        hrow8, hscaleFree⟩
      have hfinite := hprev.1.1.1.1.1.1.1
      dsimp only [RhoOneDoubleZeroTerminalGBoundaryFiniteResidual68] at hfinite
      rcases hfinite with ⟨hfact, hboundary | hrays⟩
      · rcases hboundary with ⟨hcurrent, hf2, hF3, hb4, hB5,
          hi4three, hf3ne⟩
        let AR : RatFunc k := T.source.A
        let BR : RatFunc k := T.source.B
        let CR : RatFunc k :=
          T.source.C0 - RatFunc.C (1 / 3 : k) * AR ^ 2
        let FR : RatFunc k :=
          T.source.D - RatFunc.C (1 / 3 : k) * AR * BR
        let GR : RatFunc k :=
          (T.source.E - RatFunc.C (1 / 27 : k) * AR ^ 3) -
            RatFunc.C (1 / 3 : k) * AR * CR
        have hCRmap : ratFuncAtHahn46 T.root CR =
            rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.C0) := by
          dsimp only [CR, AR, rhoOneCDefectHahn68]
          simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
        have hFRmap : ratFuncAtHahn46 T.root FR =
            rhoOneTangentDDefectHahn68
              (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.B)
              (ratFuncAtHahn46 T.root T.source.D) := by
          dsimp only [FR, AR, BR, rhoOneTangentDDefectHahn68]
          simp only [map_sub, map_mul, ratFuncAtHahn46_C]
        have hGRmap : ratFuncAtHahn46 T.root GR =
            rhoOneTangentEDefectHahn68
              (ratFuncAtHahn46 T.root T.source.A)
              (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                (ratFuncAtHahn46 T.root T.source.C0))
              (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                (ratFuncAtHahn46 T.root T.source.E)) := by
          dsimp only [GR, CR, AR, rhoOneTangentEDefectHahn68,
            rhoOneCDefectHahn68, rhoOneEDefectHahn68]
          simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
        change rhoOneI4ZeroFactored68
          (RatFunc.C T.source.gamma) (RatFunc.C T.source.epsilon)
          BR CR FR GR = 0 at hfact
        have hrow12raw := rhoOneI4ZeroFactored_cap_coeff_twelve68
          T.root T.source.gamma T.source.epsilon BR CR FR GR
          (by simpa only [BR] using hB11) (by rw [hFRmap]; exact hF3)
          (by rw [hGRmap]; exact hG) (by rw [hCRmap]; exact hS7) hfact
        rw [hCRmap, hFRmap, hGRmap] at hrow12raw
        have hrow12 := by simpa only [AR, BR] using hrow12raw
        have hsecond := rhoOneI3I4_coordinate_cap_second_transport68
          ((ratFuncAtHahn46 T.root T.source.B).coeff (11 : ℚ))
          ((ratFuncAtHahn46 T.root T.source.B).coeff (12 : ℚ))
          ((ratFuncAtHahn46 T.root T.source.B).coeff (13 : ℚ))
          ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.C0)).coeff (7 : ℚ))
          ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.C0)).coeff (8 : ℚ))
          ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.C0)).coeff (9 : ℚ))
          ((rhoOneTangentDDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.B)
            (ratFuncAtHahn46 T.root T.source.D)).coeff (3 : ℚ))
          ((rhoOneTangentDDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.B)
            (ratFuncAtHahn46 T.root T.source.D)).coeff (4 : ℚ))
          ((rhoOneTangentDDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.B)
            (ratFuncAtHahn46 T.root T.source.D)).coeff (5 : ℚ))
          ((rhoOneTangentEDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.C0))
            (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.E))).coeff (-1 : ℚ))
          ((rhoOneTangentEDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.C0))
            (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.E))).coeff (0 : ℚ))
          ((rhoOneTangentEDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.C0))
            (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.E))).coeff (1 : ℚ))
          T.source.epsilon hb11ne hGne hcap4 hscalar htransport
          hrow7 hrow8 hrow12
        have hsourceSecond := rhoOneTerminal_cap_second_transport_source68
          s ((localClearedA68RhoOne g u).derivative.eval T.root)
          ((ratFuncAtHahn46 T.root T.source.A).coeff (-1 : ℚ))
          ((ratFuncAtHahn46 T.root T.source.B).coeff (11 : ℚ))
          ((ratFuncAtHahn46 T.root T.source.B).coeff (12 : ℚ))
          ((ratFuncAtHahn46 T.root T.source.B).coeff (13 : ℚ))
          ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.C0)).coeff (7 : ℚ))
          ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.C0)).coeff (8 : ℚ))
          ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.C0)).coeff (9 : ℚ))
          ((rhoOneTangentDDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.B)
            (ratFuncAtHahn46 T.root T.source.D)).coeff (3 : ℚ))
          ((rhoOneTangentDDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.B)
            (ratFuncAtHahn46 T.root T.source.D)).coeff (4 : ℚ))
          ((rhoOneTangentDDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.B)
            (ratFuncAtHahn46 T.root T.source.D)).coeff (5 : ℚ))
          ((rhoOneTangentEDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.C0))
            (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.E))).coeff (-1 : ℚ))
          ((ratFuncAtHahn46 T.root
            (Differential.deriv T.source.A)).coeff (-3 : ℚ))
          hsourceScalar hsecond
        refine ⟨i3, s, ?_⟩
        dsimp only [RhoOneDoubleZeroTerminalGBoundaryCapI4TwelvePacket68]
        exact ⟨hpacket, hrow12, hsecond, hsourceSecond⟩
      · exact (hrays.1 hcoord.1).elim
    · exact (hGne hbad.1).elim
  · right
    refine ⟨hGzero, hG0, ?_⟩
    have hres :=
      T.rhoOne_exceptional_doubleZero_refinedGZero_terminalBGainResidual
        hp hH hp6 hp5 hp4 P hB hC hF hG hbeta hdelta hzeta
    dsimp only [RhoOneDoubleZeroRefinedGZeroTerminalBGainResidual68] at hres
    rcases hres with hbad | ⟨_, _, htail'⟩
    · exact (hbad hGzero).elim
    · exact htail'

end AlignedSquareTerminalGBoundaryCapI4Twelve68

end Max11DegreeRoutes
