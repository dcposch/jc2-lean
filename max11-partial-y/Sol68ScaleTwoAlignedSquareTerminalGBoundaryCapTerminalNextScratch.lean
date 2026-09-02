import Sol68ScaleTwoAlignedSquareTerminalGBoundaryCapNextJetScratch

/-! # The terminal coefficient above the `C₇/B₁₁` cap -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareTerminalGBoundaryCapTerminalNext68

variable {k : Type*} [Field k] [CharZero k]

local instance alignedSquareTerminalGBoundaryCapTerminalNextHahnCharZero68 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-- Under the cap orders, only `F dA` and the first successor of `F G dA`
can contribute to terminal coefficient zero. -/
theorem rhoOneMainTangentTerminalFourHahn_coeff_zero_cap68
    (gamma epsilon : k)
    (A B C F G dA dB dC dF dG : HahnSeries ℚ k)
    (hA : (↑(-2 : ℚ) : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(11 : ℚ) : WithTop ℚ) ≤ B.orderTop)
    (hC : (0 : WithTop ℚ) ≤ C.orderTop)
    (hF : (↑(3 : ℚ) : WithTop ℚ) ≤ F.orderTop)
    (hG : (↑(-1 : ℚ) : WithTop ℚ) ≤ G.orderTop)
    (hS : (↑(7 : ℚ) : WithTop ℚ) ≤
      (2 * C + HahnSeries.C (3 * gamma)).orderTop)
    (hdA : (↑(-3 : ℚ) : WithTop ℚ) ≤ dA.orderTop)
    (hdB : (0 : WithTop ℚ) ≤ dB.orderTop)
    (hdC : (0 : WithTop ℚ) ≤ dC.orderTop)
    (hdF : (0 : WithTop ℚ) ≤ dF.orderTop)
    (hdG : (↑(-2 : ℚ) : WithTop ℚ) ≤ dG.orderTop)
    (hFGdA :
      (weightedMonomial68 (-(4 / 9 : k)) F G dA A B 1 1 1 0 0).coeff 0 =
        (-(4 / 9 : k)) *
          (F.coeff 4 * G.coeff (-1 : ℚ) * dA.coeff (-3 : ℚ) +
           F.coeff 3 * G.coeff 0 * dA.coeff (-3 : ℚ) +
           F.coeff 3 * G.coeff (-1 : ℚ) * dA.coeff (-2 : ℚ))) :
    (rhoOneMainTangentTerminalFourHahn68 gamma epsilon
      A B C F G dA dB dC dF dG).coeff 0 =
      (-((1 / 3 : k) * epsilon)) * F.coeff 3 * dA.coeff (-3 : ℚ) +
      (-(4 / 9 : k)) *
        (F.coeff 4 * G.coeff (-1 : ℚ) * dA.coeff (-3 : ℚ) +
         F.coeff 3 * G.coeff 0 * dA.coeff (-3 : ℚ) +
         F.coeff 3 * G.coeff (-1 : ℚ) * dA.coeff (-2 : ℚ)) := by
  let S : HahnSeries ℚ k := 2 * C + HahnSeries.C (3 * gamma)
  have hS' : (↑(7 : ℚ) : WithTop ℚ) ≤ S.orderTop := by
    simpa only [S] using hS
  have hz (s : k) (X1 X2 X3 X4 X5 : HahnSeries ℚ k)
      (n1 n2 n3 n4 n5 : ℕ) (r1 r2 r3 r4 r5 : ℚ)
      (h1 : (↑r1 : WithTop ℚ) ≤ X1.orderTop)
      (h2 : (↑r2 : WithTop ℚ) ≤ X2.orderTop)
      (h3 : (↑r3 : WithTop ℚ) ≤ X3.orderTop)
      (h4 : (↑r4 : WithTop ℚ) ≤ X4.orderTop)
      (h5 : (↑r5 : WithTop ℚ) ≤ X5.orderTop)
      (hlt : (0 : ℚ) < (n1 : ℚ) * r1 + (n2 : ℚ) * r2 +
        (n3 : ℚ) * r3 + (n4 : ℚ) * r4 + (n5 : ℚ) * r5) :
      (weightedMonomial68 s X1 X2 X3 X4 X5
        n1 n2 n3 n4 n5).coeff 0 = 0 :=
    weightedMonomial68_coeff_zero_of_general_lower s X1 X2 X3 X4 X5
      n1 n2 n3 n4 n5 r1 r2 r3 r4 r5 0 h1 h2 h3 h4 h5 hlt
  have lead (s : k) (X1 X2 X3 X4 X5 : HahnSeries ℚ k)
      (n1 n2 n3 n4 n5 : ℕ) (r1 r2 r3 r4 r5 : ℚ)
      (h1 : (↑r1 : WithTop ℚ) ≤ X1.orderTop)
      (h2 : (↑r2 : WithTop ℚ) ≤ X2.orderTop)
      (h3 : (↑r3 : WithTop ℚ) ≤ X3.orderTop)
      (h4 : (↑r4 : WithTop ℚ) ≤ X4.orderTop)
      (h5 : (↑r5 : WithTop ℚ) ≤ X5.orderTop) :=
    weightedMonomial68_coeff_at_general_lower_next s X1 X2 X3 X4 X5
      n1 n2 n3 n4 n5 r1 r2 r3 r4 r5 h1 h2 h3 h4 h5
  have h1 := hz (-((2 / 3 : k) * gamma)) F dC A B C 1 1 0 0 0
    3 0 (-2) 11 0 hF hdC hA hB hC (by norm_num)
  have h2raw := lead (-((1 / 3 : k) * epsilon)) F dA A B C 1 1 0 0 0
    3 (-3) (-2) 11 0 hF hdA hA hB hC
  have h2 :
      (weightedMonomial68 (-((1 / 3 : k) * epsilon))
        F dA A B C 1 1 0 0 0).coeff 0 =
        (-((1 / 3 : k) * epsilon)) * F.coeff 3 * dA.coeff (-3 : ℚ) := by
    convert h2raw using 1 <;> ring
  have h4 := hz (-(4 / 9 : k)) F F dB A B 1 1 1 0 0
    3 3 0 (-2) 11 hF hF hdB hA hB (by norm_num)
  have h5 := hz (-(4 / 9 : k)) C F dC A B 1 1 1 0 0
    0 3 0 (-2) 11 hC hF hdC hA hB (by norm_num)
  have h6 := hz ((2 / 3 : k) * gamma) B dG A C F 1 1 0 0 0
    11 (-2) (-2) 0 3 hB hdG hA hC hF (by norm_num)
  have h7 := hz (-(4 / 9 : k)) B F dF A C 1 1 1 0 0
    11 3 0 (-2) 0 hB hF hdF hA hC (by norm_num)
  have h8 := hz (4 / 9 : k) B C dG A F 1 1 1 0 0
    11 0 (-2) (-2) 3 hB hC hdG hA hF (by norm_num)
  have h9 := hz ((2 / 9 : k) * gamma) B C dA A F 1 1 1 0 0
    11 0 (-3) (-2) 3 hB hC hdA hA hF (by norm_num)
  have h10 := hz (4 / 27 : k) B C C dA A 1 1 1 1 0
    11 0 0 (-3) (-2) hB hC hC hdA hA (by norm_num)
  have h11 := hz (-(2 / 27 : k)) A F dA S B 1 1 1 1 0
    (-2) 3 (-3) 7 11 hA hF hdA hS' hB (by norm_num)
  have h13 := hz (-((1 / 9 : k) * epsilon)) A B dA C F 1 1 1 0 0
    (-2) 11 (-3) 0 3 hA hB hdA hC hF (by norm_num)
  have h14 := hz (-(4 / 27 : k)) A B G dA C 1 1 1 1 0
    (-2) 11 (-1) (-3) 0 hA hB hG hdA hC (by norm_num)
  have h15 := hz (-(4 / 27 : k)) A B F dB C 1 1 1 1 0
    (-2) 11 3 0 0 hA hB hF hdB hC (by norm_num)
  have h16 := hz (-(4 / 27 : k)) A B B dF C 1 1 1 1 0
    (-2) 11 11 0 0 hA hB hB hdF hC (by norm_num)
  have hrewrite : rhoOneMainTangentTerminalFourHahn68 gamma epsilon
      A B C F G dA dB dC dF dG =
      weightedMonomial68 (-((2 / 3 : k) * gamma)) F dC A B C 1 1 0 0 0 +
      weightedMonomial68 (-((1 / 3 : k) * epsilon)) F dA A B C 1 1 0 0 0 +
      weightedMonomial68 (-(4 / 9 : k)) F G dA A B 1 1 1 0 0 +
      weightedMonomial68 (-(4 / 9 : k)) F F dB A B 1 1 1 0 0 +
      weightedMonomial68 (-(4 / 9 : k)) C F dC A B 1 1 1 0 0 +
      weightedMonomial68 ((2 / 3 : k) * gamma) B dG A C F 1 1 0 0 0 +
      weightedMonomial68 (-(4 / 9 : k)) B F dF A C 1 1 1 0 0 +
      weightedMonomial68 (4 / 9 : k) B C dG A F 1 1 1 0 0 +
      weightedMonomial68 ((2 / 9 : k) * gamma) B C dA A F 1 1 1 0 0 +
      weightedMonomial68 (4 / 27 : k) B C C dA A 1 1 1 1 0 +
      weightedMonomial68 (-(2 / 27 : k)) A F dA S B 1 1 1 1 0 +
      weightedMonomial68 (-((1 / 9 : k) * epsilon)) A B dA C F 1 1 1 0 0 +
      weightedMonomial68 (-(4 / 27 : k)) A B G dA C 1 1 1 1 0 +
      weightedMonomial68 (-(4 / 27 : k)) A B F dB C 1 1 1 1 0 +
      weightedMonomial68 (-(4 / 27 : k)) A B B dF C 1 1 1 1 0 := by
    simp only [rhoOneMainTangentTerminalFourHahn68, S, weightedMonomial68,
      pow_zero, pow_one, mul_one, map_add, map_mul, map_neg, map_div₀,
      map_ofNat, map_one]
    ring
  rw [hrewrite]
  simp only [HahnSeries.coeff_add]
  rw [h1, h2, hFGdA, h4, h5, h6, h7, h8, h9, h10, h11, h13, h14,
    h15, h16]
  ring

/-- Integral support of rational functions gives the exact successor of the
triple product entering terminal coefficient zero. -/
theorem rhoOneTerminal_cap_FGdA_next68
    (root : k) (F G dA : RatFunc k)
    (hF : (↑(3 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 root F).orderTop)
    (hG : (↑(-1 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 root G).orderTop)
    (hdA : (↑(-3 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 root dA).orderTop) :
    (weightedMonomial68 (-(4 / 9 : k))
      (ratFuncAtHahn46 root F) (ratFuncAtHahn46 root G)
      (ratFuncAtHahn46 root dA) (ratFuncAtHahn46 root F)
      (ratFuncAtHahn46 root G) 1 1 1 0 0).coeff 0 =
      (-(4 / 9 : k)) *
        ((ratFuncAtHahn46 root F).coeff 4 *
            (ratFuncAtHahn46 root G).coeff (-1 : ℚ) *
            (ratFuncAtHahn46 root dA).coeff (-3 : ℚ) +
         (ratFuncAtHahn46 root F).coeff 3 *
            (ratFuncAtHahn46 root G).coeff 0 *
            (ratFuncAtHahn46 root dA).coeff (-3 : ℚ) +
         (ratFuncAtHahn46 root F).coeff 3 *
            (ratFuncAtHahn46 root G).coeff (-1 : ℚ) *
            (ratFuncAtHahn46 root dA).coeff (-2 : ℚ)) := by
  let FL : LaurentSeries k := ratFuncAtLaurent46 root F
  let Gser : LaurentSeries k := ratFuncAtLaurent46 root G
  let dAL : LaurentSeries k := ratFuncAtLaurent46 root dA
  have hFL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root F 3 hF
  have hGL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root G (-1) hG
  have hdAL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root dA (-3) hdA
  have htri := laurent_coeff_mul_three_lower_succ68
    FL Gser dAL 3 (-1) (-3) hFL hGL hdAL
  norm_num at htri
  have hp := ratFuncAtHahn46_coeff_int68 root (F * G * dA) 0
  have hF3 := ratFuncAtHahn46_coeff_int68 root F 3
  have hF4 := ratFuncAtHahn46_coeff_int68 root F 4
  have hGm1 := ratFuncAtHahn46_coeff_int68 root G (-1)
  have hG0 := ratFuncAtHahn46_coeff_int68 root G 0
  have hdAm3 := ratFuncAtHahn46_coeff_int68 root dA (-3)
  have hdAm2 := ratFuncAtHahn46_coeff_int68 root dA (-2)
  norm_num at hp hF3 hF4 hGm1 hG0 hdAm3 hdAm2
  dsimp only [FL, Gser, dAL] at htri
  rw [← hF3, ← hF4, ← hGm1, ← hG0, ← hdAm3, ← hdAm2] at htri
  have hprod :
      ((ratFuncAtHahn46 root F) * (ratFuncAtHahn46 root G) *
        (ratFuncAtHahn46 root dA)).coeff 0 =
        (ratFuncAtHahn46 root F).coeff 4 *
            (ratFuncAtHahn46 root G).coeff (-1 : ℚ) *
            (ratFuncAtHahn46 root dA).coeff (-3 : ℚ) +
         (ratFuncAtHahn46 root F).coeff 3 *
            (ratFuncAtHahn46 root G).coeff 0 *
            (ratFuncAtHahn46 root dA).coeff (-3 : ℚ) +
         (ratFuncAtHahn46 root F).coeff 3 *
            (ratFuncAtHahn46 root G).coeff (-1 : ℚ) *
            (ratFuncAtHahn46 root dA).coeff (-2 : ℚ) := by
    have hp' := hp
    rw [hp']
    exact htri
  simp only [weightedMonomial68, pow_one, pow_zero, mul_one]
  have hscale (s : k) (X : HahnSeries ℚ k) :
      (HahnSeries.C s * X).coeff 0 = s * X.coeff 0 := by
    rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]
  have hreassoc :
      HahnSeries.C (-(4 / 9 : k)) * (ratFuncAtHahn46 root F) *
          (ratFuncAtHahn46 root G) * (ratFuncAtHahn46 root dA) =
        HahnSeries.C (-(4 / 9 : k)) *
          ((ratFuncAtHahn46 root F) * (ratFuncAtHahn46 root G) *
            (ratFuncAtHahn46 root dA)) := by ring
  rw [hreassoc]
  rw [hscale, hprod]

/-- The coefficient-zero terminal row combined with `I₃[7]` eliminates
epsilon and `G[0]`. -/
theorem rhoOneTerminal_cap_next_dependency68
    (c c' f f' g g' d3 d2 epsilon : k)
    (hcap : 2 * c * g + f ^ 2 = 0)
    (hi3 : 4 * (c * g' + c' * g + f * f') + 3 * epsilon * c = 0)
    (hterminal : 3 * epsilon * f * d3 +
      4 * (f' * g * d3 + f * g' * d3 + f * g * d2) = 0) :
    2 * g * d3 * (c * f' - f * c') - f ^ 3 * d2 -
      2 * f ^ 2 * f' * d3 = 0 := by
  linear_combination (1 / 2 : k) * c * hterminal -
    (1 / 2 : k) * f * d3 * hi3 - f * d2 * hcap

/-- Source transport of terminal coefficient zero at the cap. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_exceptional_doubleZero_gBoundary_terminal_cap_coeff_zero
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (P : RhoOneZeroLCubicNextSourcePacket68 T g u)
    (hB : (↑(11 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root T.source.B).orderTop)
    (hC : (0 : WithTop ℚ) ≤
      (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0)).orderTop)
    (hF : (↑(3 : ℚ) : WithTop ℚ) ≤
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
    (hS : (↑(7 : ℚ) : WithTop ℚ) ≤
      (2 * rhoOneCDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0) +
        HahnSeries.C (3 * T.source.gamma)).orderTop)
    (hbeta : T.source.beta = 0) (hdelta : T.source.delta = 0)
    (hzeta : T.source.zeta = 0) :
    let AR : RatFunc k := T.source.A
    let BR : RatFunc k := T.source.B
    let CR : RatFunc k := T.source.C0 - RatFunc.C (1 / 3 : k) * AR ^ 2
    let FR : RatFunc k := T.source.D - RatFunc.C (1 / 3 : k) * AR * BR
    let GR : RatFunc k :=
      (T.source.E - RatFunc.C (1 / 27 : k) * AR ^ 3) -
        RatFunc.C (1 / 3 : k) * AR * CR
    let F := ratFuncAtHahn46 T.root FR
    let G := ratFuncAtHahn46 T.root GR
    let dA := ratFuncAtHahn46 T.root (Differential.deriv AR)
    3 * T.source.epsilon * F.coeff (3 : ℚ) * dA.coeff (-3 : ℚ) +
      4 * (F.coeff (4 : ℚ) * G.coeff (-1 : ℚ) *
            dA.coeff (-3 : ℚ) +
        F.coeff (3 : ℚ) * G.coeff (0 : ℚ) *
            dA.coeff (-3 : ℚ) +
        F.coeff (3 : ℚ) * G.coeff (-1 : ℚ) *
            dA.coeff (-2 : ℚ)) = 0 := by
  obtain ⟨c, t, v, z, hc, hsingle, ht, hv, hzdef, hz, hvcore, htcore⟩ := P.1
  let AR : RatFunc k := T.source.A
  let BR : RatFunc k := T.source.B
  let C0R : RatFunc k := T.source.C0
  let DR : RatFunc k := T.source.D
  let E0R : RatFunc k := T.source.E
  let CR : RatFunc k := C0R - RatFunc.C (1 / 3 : k) * AR ^ 2
  let ER : RatFunc k := E0R - RatFunc.C (1 / 27 : k) * AR ^ 3
  let FR : RatFunc k := DR - RatFunc.C (1 / 3 : k) * AR * BR
  let GR : RatFunc k := ER - RatFunc.C (1 / 3 : k) * AR * CR
  let A0 := localClearedA68RhoOne g u
  have hAclear := (T.source.clearedCoordinatesRhoOne hp T.scale_ne_zero
    hH hp6 hp5 hp4).1
  change algebraMap k[X] (RatFunc k) A0 =
    (algebraMap k[X] (RatFunc k) h0) ^ 2 * AR at hAclear
  obtain ⟨c', hc', hsingle', hderiv'⟩ :=
    ratFuncAtHahn68_linearRoot_single_deriv h0 T.root T.scale_degree T.root_eq
  have hcEq : c' = c := by
    have heq := congrArg (fun X : HahnSeries ℚ k => X.coeff (1 : ℚ))
      (hsingle'.symm.trans hsingle)
    simpa only [HahnSeries.coeff_single_same] using heq
  subst c'
  have hconst (x : k) : ratFuncDerivation68 (RatFunc.C x) = 0 := by
    have hx := GCD369RatFuncDerivative (C x : k[X])
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
  have hCrec : AR ^ 2 / 3 + CR = C0R := by
    dsimp only [CR, AR, C0R]
    simp only [map_div₀, map_one, map_ofNat]
    ring
  have hDrec : AR * BR / 3 + FR = DR := by
    dsimp only [FR, AR, BR, DR]
    simp only [map_div₀, map_one, map_ofNat]
    ring
  have hErec : AR ^ 3 / 27 + AR * CR / 3 + GR = E0R := by
    dsimp only [GR, ER, CR, AR, C0R, E0R]
    simp only [map_div₀, map_one, map_ofNat]
    ring
  have hfactor := integratedTerminal_mainTangent_factorization68
    ratFuncDerivation68 (RatFunc.C T.source.alpha)
      (RatFunc.C T.source.gamma) (RatFunc.C T.source.epsilon)
      (RatFunc.C T.source.eta) AR BR CR FR GR
      (hconst T.source.alpha) (hconst T.source.gamma)
      (hconst T.source.epsilon) (hconst T.source.eta)
  have hsparseR :
      rhoOneMainTangentTerminal68 (RatFunc.C T.source.gamma)
        (RatFunc.C T.source.epsilon) AR BR CR FR GR
        (ratFuncDerivation68 AR) (ratFuncDerivation68 BR)
        (ratFuncDerivation68 CR) (ratFuncDerivation68 FR)
        (ratFuncDerivation68 GR) =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0 := by
    rw [← hfactor, hCrec, hDrec, hErec]
    simpa only [map_zero] using hlow.2.2.2.2
  have hsparseH := congrArg (ratFuncAtHahn46 T.root) hsparseR
  have hsparseH' :
      rhoOneMainTangentTerminal68 (HahnSeries.C T.source.gamma)
        (HahnSeries.C T.source.epsilon)
        (ratFuncAtHahn46 T.root AR) (ratFuncAtHahn46 T.root BR)
        (ratFuncAtHahn46 T.root CR) (ratFuncAtHahn46 T.root FR)
        (ratFuncAtHahn46 T.root GR)
        (ratFuncAtHahn46 T.root (Differential.deriv AR))
        (ratFuncAtHahn46 T.root (Differential.deriv BR))
        (ratFuncAtHahn46 T.root (Differential.deriv CR))
        (ratFuncAtHahn46 T.root (Differential.deriv FR))
        (ratFuncAtHahn46 T.root (Differential.deriv GR)) =
      ratFuncAtHahn46 T.root
        (RatFunc.C j / algebraMap k[X] (RatFunc k) h0) := by
    simpa only [rhoOneMainTangentTerminal68, ratFuncDerivation68,
      ratFuncDerivation46_apply, map_add, map_mul, map_pow,
      ratFuncAtHahn46_C, map_div₀, map_neg, map_ofNat, map_one] using hsparseH
  have hbounds := P.2.1
  dsimp only [RhoOneZeroLCubicImprovedHahnBounds68] at hbounds
  have hAH : (↑(-2 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root AR).orderTop := by
    simpa only [AR] using hbounds.1
  have hCRmap : ratFuncAtHahn46 T.root CR =
      rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0) := by
    dsimp only [CR, C0R, AR, rhoOneCDefectHahn68]
    simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
  have hFRmap : ratFuncAtHahn46 T.root FR =
      rhoOneTangentDDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.B)
        (ratFuncAtHahn46 T.root T.source.D) := by
    dsimp only [FR, DR, AR, BR, rhoOneTangentDDefectHahn68]
    simp only [map_sub, map_mul, ratFuncAtHahn46_C]
  have hERmap : ratFuncAtHahn46 T.root ER =
      rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.E) := by
    dsimp only [ER, E0R, AR, rhoOneEDefectHahn68]
    simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
  have hGRmap : ratFuncAtHahn46 T.root GR =
      rhoOneTangentEDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0))
        (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.E)) := by
    dsimp only [GR, rhoOneTangentEDefectHahn68]
    rw [map_sub, map_mul, hERmap, hCRmap]
    rw [map_mul, ratFuncAtHahn46_C]
  have hBR : (↑(11 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root BR).orderTop := by simpa only [BR] using hB
  have hCR : (0 : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root CR).orderTop := by rw [hCRmap]; exact hC
  have hFR : (↑(3 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root FR).orderTop := by rw [hFRmap]; exact hF
  have hGR : (↑(-1 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root GR).orderTop := by rw [hGRmap]; exact hG
  have hdA : (↑(-3 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root (Differential.deriv AR)).orderTop := by
    dsimp only [AR]
    convert localHahn_deriv_orderTop_ge_of_cleared T.root h0 A0
      T.source.A 2 T.scale_order hAclear using 1 <;> norm_num
  have hdB : (0 : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root (Differential.deriv BR)).orderTop :=
    ratFuncAtHahn46_deriv_orderTop_nonneg_of_nonneg T.root BR
      (le_trans (WithTop.coe_le_coe.mpr (by norm_num)) hBR)
  have hdC : (0 : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root (Differential.deriv CR)).orderTop :=
    ratFuncAtHahn46_deriv_orderTop_nonneg_of_nonneg T.root CR hCR
  have hdF : (0 : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root (Differential.deriv FR)).orderTop :=
    ratFuncAtHahn46_deriv_orderTop_nonneg_of_nonneg T.root FR
      (le_trans (WithTop.coe_le_coe.mpr (by norm_num)) hFR)
  have hdG : (↑(-2 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root (Differential.deriv GR)).orderTop :=
    ratFuncAtHahn68_deriv_orderTop_ge_negTwo_of_ge_negOne
      T.root h0 GR T.scale_order hGR
  have htri := rhoOneTerminal_cap_FGdA_next68 T.root FR GR
    (Differential.deriv AR) hFR hGR hdA
  have hcoeff := rhoOneMainTangentTerminalFourHahn_coeff_zero_cap68
    T.source.gamma T.source.epsilon
    (ratFuncAtHahn46 T.root AR) (ratFuncAtHahn46 T.root BR)
    (ratFuncAtHahn46 T.root CR) (ratFuncAtHahn46 T.root FR)
    (ratFuncAtHahn46 T.root GR)
    (ratFuncAtHahn46 T.root (Differential.deriv AR))
    (ratFuncAtHahn46 T.root (Differential.deriv BR))
    (ratFuncAtHahn46 T.root (Differential.deriv CR))
    (ratFuncAtHahn46 T.root (Differential.deriv FR))
    (ratFuncAtHahn46 T.root (Differential.deriv GR))
    hAH hBR hCR hFR hGR (by rw [hCRmap]; exact hS)
    hdA hdB hdC hdF hdG htri
  have hterminal0 :
      (ratFuncAtHahn46 T.root
        (RatFunc.C j / algebraMap k[X] (RatFunc k) h0)).coeff 0 = 0 := by
    rw [map_div₀, ratFuncAtHahn46_C, hsingle, div_eq_mul_inv,
      HahnSeries.inv_single, HahnSeries.C_apply, HahnSeries.single_mul_single]
    norm_num
  have hfourrow : rhoOneMainTangentTerminalFourHahn68
      T.source.gamma T.source.epsilon
      (ratFuncAtHahn46 T.root AR) (ratFuncAtHahn46 T.root BR)
      (ratFuncAtHahn46 T.root CR) (ratFuncAtHahn46 T.root FR)
      (ratFuncAtHahn46 T.root GR)
      (ratFuncAtHahn46 T.root (Differential.deriv AR))
      (ratFuncAtHahn46 T.root (Differential.deriv BR))
      (ratFuncAtHahn46 T.root (Differential.deriv CR))
      (ratFuncAtHahn46 T.root (Differential.deriv FR))
      (ratFuncAtHahn46 T.root (Differential.deriv GR)) =
      ratFuncAtHahn46 T.root
        (RatFunc.C j / algebraMap k[X] (RatFunc k) h0) := by
    rw [← rhoOneMainTangentTerminalFourHahn_eq68]
    exact hsparseH'
  have hzero := congrArg (fun X : HahnSeries ℚ k => X.coeff 0) hfourrow
  rw [hcoeff, hterminal0] at hzero
  linear_combination (-9 : k) * hzero

/-- The source-facing cap packet after consuming terminal coefficient zero. -/
def RhoOneDoubleZeroTerminalGBoundaryCapTerminalNextPacket68
    (gamma epsilon i3 : k) (A B C F G dA : HahnSeries ℚ k) : Prop :=
  RhoOneDoubleZeroTerminalGBoundaryCapNextJetPacket68
      gamma epsilon i3 A B C F G ∧
    3 * epsilon * F.coeff (3 : ℚ) * dA.coeff (-3 : ℚ) +
      4 * (F.coeff (4 : ℚ) * G.coeff (-1 : ℚ) *
            dA.coeff (-3 : ℚ) +
        F.coeff (3 : ℚ) * G.coeff (0 : ℚ) *
            dA.coeff (-3 : ℚ) +
        F.coeff (3 : ℚ) * G.coeff (-1 : ℚ) *
            dA.coeff (-2 : ℚ)) = 0 ∧
    2 * G.coeff (-1 : ℚ) * dA.coeff (-3 : ℚ) *
        (C.coeff (7 : ℚ) * F.coeff (4 : ℚ) -
          F.coeff (3 : ℚ) * C.coeff (8 : ℚ)) -
      F.coeff (3 : ℚ) ^ 3 * dA.coeff (-2 : ℚ) -
      2 * F.coeff (3 : ℚ) ^ 2 * F.coeff (4 : ℚ) *
        dA.coeff (-3 : ℚ) = 0

/-- Only the `C[1]=C[2]=0` cap child is refined; every sibling remains in
the predecessor conjunct. -/
def RhoOneDoubleZeroTerminalGBoundaryCapTerminalNextResidual68
    (root j gamma epsilon : k) (h0R AR BR CR FR GR : RatFunc k)
    (A B C F G : HahnSeries ℚ k) : Prop :=
  RhoOneDoubleZeroTerminalGBoundaryCapNextJetResidual68
      root j gamma epsilon h0R BR CR FR GR A B C F G ∧
    ((B.coeff (1 : ℚ) = 0 ∧
        2 * C.coeff (0 : ℚ) + 3 * gamma = 0) →
      C.coeff (1 : ℚ) = 0 → C.coeff (2 : ℚ) = 0 →
      ∃ i3 : k, RhoOneDoubleZeroTerminalGBoundaryCapTerminalNextPacket68
        gamma epsilon i3 A B C F G
          (ratFuncAtHahn46 root (Differential.deriv AR)))

/-- Literal source backwire of terminal coefficient zero and its
epsilon/`G[0]`-free dependency with `I₃[7]`. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_exceptional_doubleZero_refinedGZero_terminalGBoundaryCapTerminalNextResidual
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
    RhoOneDoubleZeroTerminalGBoundaryCapTerminalNextResidual68
        T.root j T.source.gamma T.source.epsilon
        (algebraMap k[X] (RatFunc k) h0) AR BR CR FR GR A B C F G ∨
      (G.coeff (-1 : ℚ) = 0 ∧ (0 : WithTop ℚ) ≤ G.orderTop ∧
        (RhoOneDoubleZeroRefinedGZeroTerminalBGainChild68
            T.source.gamma B C F ∨
         RhoOneDoubleZeroRefinedGZeroTerminalFGainChild68
            T.source.gamma B C F)) := by
  dsimp only [RhoOneDoubleZeroTerminalGBoundaryCapTerminalNextResidual68]
  have hnext := T.rhoOne_exceptional_doubleZero_refined_gZero
    P hB hC hF hG hbeta hdelta hzeta
  dsimp only at hnext
  rcases hnext with ⟨_, _, _, _, _, _, hsplit⟩
  rcases hsplit with hGne | ⟨hGzero, hG0, htail⟩
  · have hprev :=
      T.rhoOne_exceptional_doubleZero_refinedGZero_terminalGBoundaryCapNextJetResidual
        hp hH hp6 hp5 hp4 P hB hC hF hG hbeta hdelta hzeta
    rcases hprev with hcapResidual | hbad
    · left
      refine ⟨hcapResidual, ?_⟩
      intro hcoord hc1 hc2
      obtain ⟨i3, hpacket⟩ := hcapResidual.2 hcoord hc1 hc2
      have hpacket' := hpacket
      dsimp only [RhoOneDoubleZeroTerminalGBoundaryCapNextJetPacket68,
        RhoOneDoubleZeroTerminalGBoundaryCI3CapPacket68] at hpacket'
      rcases hpacket' with
        ⟨⟨hi3H, hc3, hc4, hc5, hc6, hb7, hb8, hb9, hb10, hS7, hB11,
          hcap3, hc7ne, hcap4, hb11ne, hBexact⟩,
          hscalar, hrow3, hrow4, htransport⟩
      have hfinite := hcapResidual.1.1.1.1
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
        have hterminal :=
          T.rhoOne_exceptional_doubleZero_gBoundary_terminal_cap_coeff_zero
            hp hH hp6 hp5 hp4 P (by simpa only [BR] using hB11) hC hF3 hG
            hS7 hbeta hdelta hzeta
        dsimp only at hterminal
        rw [hFRmap, hGRmap] at hterminal
        have hterminal' := by simpa only [AR] using hterminal
        have hdependency := rhoOneTerminal_cap_next_dependency68
          ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.C0)).coeff (7 : ℚ))
          ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.C0)).coeff (8 : ℚ))
          ((rhoOneTangentDDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.B)
            (ratFuncAtHahn46 T.root T.source.D)).coeff (3 : ℚ))
          ((rhoOneTangentDDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.B)
            (ratFuncAtHahn46 T.root T.source.D)).coeff (4 : ℚ))
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
          ((ratFuncAtHahn46 T.root
            (Differential.deriv T.source.A)).coeff (-3 : ℚ))
          ((ratFuncAtHahn46 T.root
            (Differential.deriv T.source.A)).coeff (-2 : ℚ))
          T.source.epsilon hcap3 hrow3 hterminal'
        refine ⟨i3, ?_⟩
        dsimp only [RhoOneDoubleZeroTerminalGBoundaryCapTerminalNextPacket68]
        exact ⟨hpacket, hterminal', hdependency⟩
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

end AlignedSquareTerminalGBoundaryCapTerminalNext68

end Max11DegreeRoutes
