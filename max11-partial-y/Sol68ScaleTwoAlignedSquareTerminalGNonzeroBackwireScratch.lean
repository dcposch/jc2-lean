import Sol68ScaleTwoAlignedSquareTerminalGNonzeroSourceScratch

/-! # Source transport and backwire for the nonzero `G[-1]` child -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareTerminalGNonzeroBackwire68

variable {k : Type*} [Field k] [CharZero k]

/-- The raw aligned-square source transports the terminal minus-five face
on the `G[-1] ≠ 0` child to the exact quadratic scalar wall. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_exceptional_doubleZero_gNonzero_terminal_quadraticWall
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (P : RhoOneZeroLCubicNextSourcePacket68 T g u)
    (hB :
      (↑(1 : ℚ) : WithTop ℚ) ≤
        (ratFuncAtHahn46 T.root T.source.B).orderTop)
    (hC :
      (0 : WithTop ℚ) ≤
        (rhoOneCDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0)).orderTop)
    (hF :
      (0 : WithTop ℚ) ≤
        (rhoOneTangentDDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.B)
          (ratFuncAtHahn46 T.root T.source.D)).orderTop)
    (hG :
      (↑(-1 : ℚ) : WithTop ℚ) ≤
        (rhoOneTangentEDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (rhoOneCDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.C0))
          (rhoOneEDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.E))).orderTop)
    (hGne :
      (rhoOneTangentEDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (rhoOneCDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0))
        (rhoOneEDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.E))).coeff (-1 : ℚ) ≠ 0)
    (hi3 :
      rhoOneZeroLCubicDoubleZeroGZeroThree68 T.source.gamma
        ((ratFuncAtHahn46 T.root T.source.A).coeff (-2 : ℚ))
        ((ratFuncAtHahn46 T.root T.source.B).coeff (1 : ℚ))
        ((rhoOneCDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0)).coeff (0 : ℚ))
        ((rhoOneTangentDDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.B)
          (ratFuncAtHahn46 T.root T.source.D)).coeff (0 : ℚ))
        ((rhoOneTangentEDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (rhoOneCDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.C0))
          (rhoOneEDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.E))).coeff (-1 : ℚ)) = 0)
    (hbeta : T.source.beta = 0) (hdelta : T.source.delta = 0)
    (hzeta : T.source.zeta = 0) :
    let A := ratFuncAtHahn46 T.root T.source.A
    let B := ratFuncAtHahn46 T.root T.source.B
    let C := rhoOneCDefectHahn68 A
      (ratFuncAtHahn46 T.root T.source.C0)
    3 * (2 * C.coeff (0 : ℚ) + 3 * T.source.gamma) ^ 2 +
      4 * A.coeff (-2 : ℚ) * B.coeff (1 : ℚ) ^ 2 = 0 := by
  dsimp only
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
  have hAne : (ratFuncAtHahn46 T.root AR).coeff (-2 : ℚ) ≠ 0 := by
    simpa only [AR] using P.2.2.1
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
  have hBR : (↑(1 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root BR).orderTop := by simpa only [BR] using hB
  have hCR : (0 : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root CR).orderTop := by rw [hCRmap]; exact hC
  have hFR : (0 : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root FR).orderTop := by rw [hFRmap]; exact hF
  have hGR : (↑(-1 : ℚ) : WithTop ℚ) ≤
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
    ratFuncAtHahn46_deriv_orderTop_nonneg_of_nonneg T.root FR hFR
  have hdG : (↑(-2 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root (Differential.deriv GR)).orderTop :=
    ratFuncAtHahn68_deriv_orderTop_ge_negTwo_of_ge_negOne
      T.root h0 GR T.scale_order hGR
  have hwall := rhoOneMainTangentTerminal_gNonzero_quadraticWall68
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
      hAH hBR hCR hFR hGR hdA hdB hdC hdF hdG hdAco hAne
      (by rw [hGRmap]; exact hGne)
      (by rw [hCRmap, hFRmap, hGRmap]; simpa only [AR, BR] using hi3)
      hsparseH' T.terminal_order
  rw [hCRmap] at hwall
  simpa only [AR, BR] using hwall

/-- The refined selector with its formerly independent `G[-1] ≠ 0`
child replaced by the exact terminal/I3 quadratic wall. -/
def RhoOneDoubleZeroRefinedGZeroTerminalGResidual68
    (gamma : k) (A B C F G : HahnSeries ℚ k) : Prop :=
  3 * (2 * C.coeff (0 : ℚ) + 3 * gamma) ^ 2 +
      4 * A.coeff (-2 : ℚ) * B.coeff (1 : ℚ) ^ 2 = 0 ∨
    (G.coeff (-1 : ℚ) = 0 ∧ (0 : WithTop ℚ) ≤ G.orderTop ∧
      (RhoOneDoubleZeroRefinedGZeroTerminalBGainChild68 gamma B C F ∨
       RhoOneDoubleZeroRefinedGZeroTerminalFGainChild68 gamma B C F))

theorem SquareZeroLIntegratedLocalRootData68.rhoOne_exceptional_doubleZero_refinedGZero_terminalGResidual
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
    let A := ratFuncAtHahn46 T.root T.source.A
    let B := ratFuncAtHahn46 T.root T.source.B
    let C := rhoOneCDefectHahn68 A
      (ratFuncAtHahn46 T.root T.source.C0)
    let F := rhoOneTangentDDefectHahn68 A B
      (ratFuncAtHahn46 T.root T.source.D)
    let G := rhoOneTangentEDefectHahn68 A C
      (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
    RhoOneDoubleZeroRefinedGZeroTerminalGResidual68
      T.source.gamma A B C F G := by
  dsimp only [RhoOneDoubleZeroRefinedGZeroTerminalGResidual68]
  have hnext := T.rhoOne_exceptional_doubleZero_refined_gZero
    P hB hC hF hG hbeta hdelta hzeta
  dsimp only at hnext
  rcases hnext with ⟨_, _, _, _, _, hi3, hsplit⟩
  rcases hsplit with hg | ⟨hg, hG0, htail⟩
  · left
    exact T.rhoOne_exceptional_doubleZero_gNonzero_terminal_quadraticWall
      hp hH hp6 hp5 hp4 P hB hC hF hG hg hi3 hbeta hdelta hzeta
  · right
    refine ⟨hg, hG0, ?_⟩
    have hres := T.rhoOne_exceptional_doubleZero_refinedGZero_terminalBGainResidual
      hp hH hp6 hp5 hp4 P hB hC hF hG hbeta hdelta hzeta
    dsimp only [RhoOneDoubleZeroRefinedGZeroTerminalBGainResidual68] at hres
    rcases hres with hgne | ⟨_, _, htail'⟩
    · exact (hgne hg).elim
    · exact htail'

end AlignedSquareTerminalGNonzeroBackwire68

end Max11DegreeRoutes
