import Sol68ScaleTwoAlignedSquareTerminalGainTowerScratch

/-! # Terminal deletion of the fourth aligned-square gain box -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareTerminalFourBox68

variable {k : Type*} [Field k] [CharZero k]

local instance alignedSquareTerminalFourBoxHahnCharZero68 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-- Weighted-monomial presentation of the sparse terminal row. -/
def rhoOneMainTangentTerminalFourHahn68
    (gamma epsilon : k)
    (A B C F G dA dB dC dF dG : HahnSeries ℚ k) : HahnSeries ℚ k :=
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
  weightedMonomial68 (-((2 / 9 : k) * gamma)) A F dA B C 1 1 1 0 0 +
  weightedMonomial68 (-(4 / 27 : k)) A C F dA B 1 1 1 1 0 +
  weightedMonomial68 (-((1 / 9 : k) * epsilon)) A B dA C F 1 1 1 0 0 +
  weightedMonomial68 (-(4 / 27 : k)) A B G dA C 1 1 1 1 0 +
  weightedMonomial68 (-(4 / 27 : k)) A B F dB C 1 1 1 1 0 +
  weightedMonomial68 (-(4 / 27 : k)) A B B dF C 1 1 1 1 0

/-- The weighted presentation is exactly the terminal factorization already
obtained from the source row. -/
theorem rhoOneMainTangentTerminalFourHahn_eq68
    (gamma epsilon : k)
    (A B C F G dA dB dC dF dG : HahnSeries ℚ k) :
    rhoOneMainTangentTerminal68 (HahnSeries.C gamma)
        (HahnSeries.C epsilon) A B C F G dA dB dC dF dG =
      rhoOneMainTangentTerminalFourHahn68 gamma epsilon
        A B C F G dA dB dC dF dG := by
  simp only [rhoOneMainTangentTerminal68,
    rhoOneMainTangentTerminalFourHahn68, weightedMonomial68,
    pow_zero, pow_one, mul_one, map_mul, map_neg, map_div₀, map_ofNat,
    map_one]
  ring

/-- At order four, the coefficient at the Keller pole is a scalar multiple
of the same sparse `I₄` face. -/
theorem rhoOneMainTangentTerminalFourHahn_coeff_negOne68
    (gamma epsilon : k)
    (A B C F G dA dB dC dF dG : HahnSeries ℚ k)
    (hA : (↑(-2 : ℚ) : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(4 : ℚ) : WithTop ℚ) ≤ B.orderTop)
    (hC : (0 : WithTop ℚ) ≤ C.orderTop)
    (hF : (↑(4 : ℚ) : WithTop ℚ) ≤ F.orderTop)
    (hG : (0 : WithTop ℚ) ≤ G.orderTop)
    (hdA : (↑(-3 : ℚ) : WithTop ℚ) ≤ dA.orderTop)
    (hdB : (0 : WithTop ℚ) ≤ dB.orderTop)
    (hdC : (0 : WithTop ℚ) ≤ dC.orderTop)
    (hdF : (0 : WithTop ℚ) ≤ dF.orderTop)
    (hdG : (0 : WithTop ℚ) ≤ dG.orderTop)
    (hdAco : dA.coeff (-3 : ℚ) = (-2 : k) * A.coeff (-2 : ℚ)) :
    (rhoOneMainTangentTerminalFourHahn68 gamma epsilon
      A B C F G dA dB dC dF dG).coeff (-1 : ℚ) =
      (2 / 27 : k) * A.coeff (-2 : ℚ) ^ 2 *
        rhoOneZeroLCubicDoubleZeroDoubleGainFour68 gamma epsilon
          (B.coeff (4 : ℚ)) (C.coeff (0 : ℚ))
          (F.coeff (4 : ℚ)) (G.coeff (0 : ℚ)) := by
  have hz (s : k) (X1 X2 X3 X4 X5 : HahnSeries ℚ k)
      (n1 n2 n3 n4 n5 : ℕ) (r1 r2 r3 r4 r5 : ℚ)
      (h1 : (↑r1 : WithTop ℚ) ≤ X1.orderTop)
      (h2 : (↑r2 : WithTop ℚ) ≤ X2.orderTop)
      (h3 : (↑r3 : WithTop ℚ) ≤ X3.orderTop)
      (h4 : (↑r4 : WithTop ℚ) ≤ X4.orderTop)
      (h5 : (↑r5 : WithTop ℚ) ≤ X5.orderTop)
      (hlt : (-1 : ℚ) < (n1 : ℚ) * r1 + (n2 : ℚ) * r2 +
        (n3 : ℚ) * r3 + (n4 : ℚ) * r4 + (n5 : ℚ) * r5) :
      (weightedMonomial68 s X1 X2 X3 X4 X5
        n1 n2 n3 n4 n5).coeff (-1 : ℚ) = 0 :=
    weightedMonomial68_coeff_zero_of_general_lower s X1 X2 X3 X4 X5
      n1 n2 n3 n4 n5 r1 r2 r3 r4 r5 (-1)
      h1 h2 h3 h4 h5 hlt
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
    4 0 (-2) 4 0 hF hdC hA hB hC (by norm_num)
  have h2 := hz (-((1 / 3 : k) * epsilon)) F dA A B C 1 1 0 0 0
    4 (-3) (-2) 4 0 hF hdA hA hB hC (by norm_num)
  have h3 := hz (-(4 / 9 : k)) F G dA A B 1 1 1 0 0
    4 0 (-3) (-2) 4 hF hG hdA hA hB (by norm_num)
  have h4 := hz (-(4 / 9 : k)) F F dB A B 1 1 1 0 0
    4 4 0 (-2) 4 hF hF hdB hA hB (by norm_num)
  have h5 := hz (-(4 / 9 : k)) C F dC A B 1 1 1 0 0
    0 4 0 (-2) 4 hC hF hdC hA hB (by norm_num)
  have h6 := hz ((2 / 3 : k) * gamma) B dG A C F 1 1 0 0 0
    4 0 (-2) 0 4 hB hdG hA hC hF (by norm_num)
  have h7 := hz (-(4 / 9 : k)) B F dF A C 1 1 1 0 0
    4 4 0 (-2) 0 hB hF hdF hA hC (by norm_num)
  have h8 := hz (4 / 9 : k) B C dG A F 1 1 1 0 0
    4 0 0 (-2) 4 hB hC hdG hA hF (by norm_num)
  have h9 := hz ((2 / 9 : k) * gamma) B C dA A F 1 1 1 0 0
    4 0 (-3) (-2) 4 hB hC hdA hA hF (by norm_num)
  have h10 := hz (4 / 27 : k) B C C dA A 1 1 1 1 0
    4 0 0 (-3) (-2) hB hC hC hdA hA (by norm_num)
  have h11 := lead (-((2 / 9 : k) * gamma)) A F dA B C 1 1 1 0 0
    (-2) 4 (-3) 4 0 hA hF hdA hB hC
  have h12 := lead (-(4 / 27 : k)) A C F dA B 1 1 1 1 0
    (-2) 0 4 (-3) 4 hA hC hF hdA hB
  have h13 := lead (-((1 / 9 : k) * epsilon)) A B dA C F 1 1 1 0 0
    (-2) 4 (-3) 0 4 hA hB hdA hC hF
  have h14 := lead (-(4 / 27 : k)) A B G dA C 1 1 1 1 0
    (-2) 4 0 (-3) 0 hA hB hG hdA hC
  have h15 := hz (-(4 / 27 : k)) A B F dB C 1 1 1 1 0
    (-2) 4 4 0 0 hA hB hF hdB hC (by norm_num)
  have h16 := hz (-(4 / 27 : k)) A B B dF C 1 1 1 1 0
    (-2) 4 4 0 0 hA hB hB hdF hC (by norm_num)
  norm_num at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
  simp only [rhoOneMainTangentTerminalFourHahn68, HahnSeries.coeff_add]
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14,
    h15, h16, hdAco]
  simp only [rhoOneZeroLCubicDoubleZeroDoubleGainFour68]
  ring

/-- The order-four sparse face cannot equal a Keller terminal of order
minus one. -/
theorem rhoOneMainTangentTerminal_fourBox_impossible68
    (gamma epsilon : k)
    (A B C F G dA dB dC dF dG terminal : HahnSeries ℚ k)
    (hA : (↑(-2 : ℚ) : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(4 : ℚ) : WithTop ℚ) ≤ B.orderTop)
    (hC : (0 : WithTop ℚ) ≤ C.orderTop)
    (hF : (↑(4 : ℚ) : WithTop ℚ) ≤ F.orderTop)
    (hG : (0 : WithTop ℚ) ≤ G.orderTop)
    (hdA : (↑(-3 : ℚ) : WithTop ℚ) ≤ dA.orderTop)
    (hdB : (0 : WithTop ℚ) ≤ dB.orderTop)
    (hdC : (0 : WithTop ℚ) ≤ dC.orderTop)
    (hdF : (0 : WithTop ℚ) ≤ dF.orderTop)
    (hdG : (0 : WithTop ℚ) ≤ dG.orderTop)
    (hdAco : dA.coeff (-3 : ℚ) = (-2 : k) * A.coeff (-2 : ℚ))
    (hface : rhoOneZeroLCubicDoubleZeroDoubleGainFour68 gamma epsilon
      (B.coeff (4 : ℚ)) (C.coeff (0 : ℚ))
      (F.coeff (4 : ℚ)) (G.coeff (0 : ℚ)) = 0)
    (hrow : rhoOneMainTangentTerminal68 (HahnSeries.C gamma)
      (HahnSeries.C epsilon) A B C F G dA dB dC dF dG = terminal)
    (hterminal : terminal.orderTop = (↑(-1 : ℚ) : WithTop ℚ)) : False := by
  have hcoeff := rhoOneMainTangentTerminalFourHahn_coeff_negOne68
    gamma epsilon A B C F G dA dB dC dF dG
      hA hB hC hF hG hdA hdB hdC hdF hdG hdAco
  rw [hface, mul_zero] at hcoeff
  have hleftzero :
      (rhoOneMainTangentTerminal68 (HahnSeries.C gamma)
        (HahnSeries.C epsilon) A B C F G dA dB dC dF dG).coeff
          (-1 : ℚ) = 0 := by
    rw [rhoOneMainTangentTerminalFourHahn_eq68]
    exact hcoeff
  have hrightzero : terminal.coeff (-1 : ℚ) = 0 := by
    rw [← hrow]
    exact hleftzero
  exact HahnSeries.coeff_orderTop_ne hterminal hrightzero

/-- Source-facing deletion of the whole fourth-gain box.  This strengthens
the quintuple result: neither its nonzero-`B[4]` sibling nor its affine-wall
sibling survives the terminal coefficient. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_exceptional_doubleZero_fourBox_impossible
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (P : RhoOneZeroLCubicNextSourcePacket68 T g u)
    (hB :
      (↑(4 : ℚ) : WithTop ℚ) ≤
        (ratFuncAtHahn46 T.root T.source.B).orderTop)
    (hC :
      (0 : WithTop ℚ) ≤
        (rhoOneCDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0)).orderTop)
    (hF :
      (↑(4 : ℚ) : WithTop ℚ) ≤
        (rhoOneTangentDDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.B)
          (ratFuncAtHahn46 T.root T.source.D)).orderTop)
    (hG :
      (0 : WithTop ℚ) ≤
        (rhoOneTangentEDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (rhoOneCDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.C0))
          (rhoOneEDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.E))).orderTop)
    (hbeta : T.source.beta = 0) (hdelta : T.source.delta = 0)
    (hzeta : T.source.zeta = 0) : False := by
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
    ratFuncAtHahn68_linearRoot_single_deriv
      h0 T.root T.scale_degree T.root_eq
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
      ratFuncAtHahn46_C, map_div₀, map_neg, map_ofNat, map_one]
      using hsparseH
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
        (rhoOneCDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0))
        (rhoOneEDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.E)) := by
    dsimp only [GR, rhoOneTangentEDefectHahn68]
    rw [map_sub, map_mul, hERmap, hCRmap]
    rw [map_mul, ratFuncAtHahn46_C]
  have hBR : (↑(4 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root BR).orderTop := by simpa only [BR] using hB
  have hCR : (0 : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root CR).orderTop := by rw [hCRmap]; exact hC
  have hFR : (↑(4 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root FR).orderTop := by rw [hFRmap]; exact hF
  have hGR : (0 : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root GR).orderTop := by rw [hGRmap]; exact hG
  have hdA : (↑(-3 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root (Differential.deriv AR)).orderTop := by
    dsimp only [AR]
    convert localHahn_deriv_orderTop_ge_of_cleared T.root h0 A0
      T.source.A 2 T.scale_order hAclear using 1 <;> norm_num
  have hdAco :
      (ratFuncAtHahn46 T.root (Differential.deriv AR)).coeff (-3 : ℚ) =
        (-2 : k) * (ratFuncAtHahn46 T.root AR).coeff (-2 : ℚ) := by
    dsimp only [AR]
    convert localHahn_deriv_coeff_neg_succ_of_cleared T.root c h0 A0
      T.source.A 2 hc hsingle hderiv' hAclear using 1 <;> norm_num
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
  have hdG : (0 : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root (Differential.deriv GR)).orderTop :=
    ratFuncAtHahn46_deriv_orderTop_nonneg_of_nonneg T.root GR hGR
  have hnext := T.rhoOne_exceptional_doubleZero_quadrupleGain_next
    P hB hC hF hG hbeta hdelta hzeta
  dsimp only at hnext
  have hface := hnext.2.2.2.2.2.1
  have hface' :
      rhoOneZeroLCubicDoubleZeroDoubleGainFour68 T.source.gamma
        T.source.epsilon
        ((ratFuncAtHahn46 T.root BR).coeff (4 : ℚ))
        ((ratFuncAtHahn46 T.root CR).coeff (0 : ℚ))
        ((ratFuncAtHahn46 T.root FR).coeff (4 : ℚ))
        ((ratFuncAtHahn46 T.root GR).coeff (0 : ℚ)) = 0 := by
    rw [hCRmap, hFRmap, hGRmap]
    simpa only [BR] using hface
  exact rhoOneMainTangentTerminal_fourBox_impossible68
    T.source.gamma T.source.epsilon
      (ratFuncAtHahn46 T.root AR) (ratFuncAtHahn46 T.root BR)
      (ratFuncAtHahn46 T.root CR) (ratFuncAtHahn46 T.root FR)
      (ratFuncAtHahn46 T.root GR)
      (ratFuncAtHahn46 T.root (Differential.deriv AR))
      (ratFuncAtHahn46 T.root (Differential.deriv BR))
      (ratFuncAtHahn46 T.root (Differential.deriv CR))
      (ratFuncAtHahn46 T.root (Differential.deriv FR))
      (ratFuncAtHahn46 T.root (Differential.deriv GR))
      (ratFuncAtHahn46 T.root
        (RatFunc.C j / algebraMap k[X] (RatFunc k) h0))
      hAH hBR hCR hFR hGR hdA hdB hdC hdF hdG hdAco hface' hsparseH'
      T.terminal_order

end AlignedSquareTerminalFourBox68

end Max11DegreeRoutes
