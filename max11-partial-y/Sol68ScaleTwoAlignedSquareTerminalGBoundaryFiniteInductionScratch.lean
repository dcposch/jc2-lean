import Sol68ScaleTwoAlignedSquareTerminalGBoundaryInductionScratch

/-! # Finite exhaustion of the nonzero-`G[-1]` zero boundary -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareTerminalGBoundaryFiniteInduction68

variable {k : Type*} [Field k] [CharZero k]

local instance alignedSquareTerminalGBoundaryFiniteInductionHahnCharZero68 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-- At `r=3` the indexed terminal face reaches, rather than lies below, the
Keller pole.  Thus the same face proves that `F[3]` is nonzero. -/
theorem rhoOneMainTangentTerminal_gBoundary_induction_fThree_ne68
    (gamma epsilon : k)
    (A B C F G dA dB dC dF dG terminal : HahnSeries ℚ k)
    (hA : (↑(-2 : ℚ) : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(5 : ℚ) : WithTop ℚ) ≤ B.orderTop)
    (hC : (0 : WithTop ℚ) ≤ C.orderTop)
    (hF : (↑(3 : ℚ) : WithTop ℚ) ≤ F.orderTop)
    (hG : (↑(-1 : ℚ) : WithTop ℚ) ≤ G.orderTop)
    (hS : (↑(1 : ℚ) : WithTop ℚ) ≤
      (2 * C + HahnSeries.C (3 * gamma)).orderTop)
    (hdA : (↑(-3 : ℚ) : WithTop ℚ) ≤ dA.orderTop)
    (hdB : (0 : WithTop ℚ) ≤ dB.orderTop)
    (hdC : (0 : WithTop ℚ) ≤ dC.orderTop)
    (hdF : (0 : WithTop ℚ) ≤ dF.orderTop)
    (hdG : (↑(-2 : ℚ) : WithTop ℚ) ≤ dG.orderTop)
    (hdAco : dA.coeff (-3 : ℚ) = (-2 : k) * A.coeff (-2 : ℚ))
    (hAne : A.coeff (-2 : ℚ) ≠ 0)
    (hGne : G.coeff (-1 : ℚ) ≠ 0)
    (hi4next : B.coeff (5 : ℚ) * G.coeff (-1 : ℚ) +
      C.coeff (1 : ℚ) * F.coeff (3 : ℚ) = 0)
    (hrow : rhoOneMainTangentTerminal68 (HahnSeries.C gamma)
      (HahnSeries.C epsilon) A B C F G dA dB dC dF dG = terminal)
    (hterminal : terminal.orderTop = (↑(-1 : ℚ) : WithTop ℚ)) :
    F.coeff (3 : ℚ) ≠ 0 := by
  have hcoeff := rhoOneMainTangentTerminalFourHahn_coeff_gBoundary_induction68
    3 (by norm_num) gamma epsilon A B C F G dA dB dC dF dG hA
      (by convert hB using 1 <;> norm_num) hC
      (by convert hF using 1 <;> norm_num) hG hS
      hdA hdB hdC hdF hdG hdAco
  norm_num at hcoeff
  intro hf3
  have hfourzero :
      (rhoOneMainTangentTerminalFourHahn68 gamma epsilon
        A B C F G dA dB dC dF dG).coeff (-1 : ℚ) = 0 := by
    rw [hcoeff, hi4next, hf3]
    ring
  have hterminalzero : terminal.coeff (-1 : ℚ) = 0 := by
    have hfourrow : rhoOneMainTangentTerminalFourHahn68 gamma epsilon
        A B C F G dA dB dC dF dG = terminal := by
      rw [← rhoOneMainTangentTerminalFourHahn_eq68, hrow]
    rw [← hfourrow]
    convert hfourzero using 1 <;> norm_num
  exact (HahnSeries.orderTop_ne_of_coeff_eq_zero hterminalzero) hterminal

/-- The final valid zero step (`r=2`) and the pole step (`r=3`) in one
source-facing packet.  This is the complete consequence of the indexed
terminal recurrence before it reaches the Keller pole. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_exceptional_doubleZero_gBoundary_terminal_finiteCap
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (P : RhoOneZeroLCubicNextSourcePacket68 T g u)
    (hB : (↑(4 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root T.source.B).orderTop)
    (hC : (0 : WithTop ℚ) ≤
      (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0)).orderTop)
    (hF : (↑(2 : ℚ) : WithTop ℚ) ≤
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
    (hS : (↑(1 : ℚ) : WithTop ℚ) ≤
      (2 * rhoOneCDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0) +
        HahnSeries.C (3 * T.source.gamma)).orderTop)
    (hGne : (rhoOneTangentEDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0))
        (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.E))).coeff (-1 : ℚ) ≠ 0)
    (hi4two :
      (ratFuncAtHahn46 T.root T.source.B).coeff (4 : ℚ) *
          (rhoOneTangentEDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.C0))
            (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.E))).coeff (-1 : ℚ) +
        (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0)).coeff (1 : ℚ) *
          (rhoOneTangentDDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.B)
            (ratFuncAtHahn46 T.root T.source.D)).coeff (2 : ℚ) = 0)
    (hfact :
      let AR : RatFunc k := T.source.A
      let BR : RatFunc k := T.source.B
      let CR : RatFunc k := T.source.C0 - RatFunc.C (1 / 3 : k) * AR ^ 2
      let FR : RatFunc k := T.source.D - RatFunc.C (1 / 3 : k) * AR * BR
      let GR : RatFunc k :=
        (T.source.E - RatFunc.C (1 / 27 : k) * AR ^ 3) -
          RatFunc.C (1 / 3 : k) * AR * CR
      rhoOneI4ZeroFactored68 (RatFunc.C T.source.gamma)
        (RatFunc.C T.source.epsilon) BR CR FR GR = 0)
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
    F.coeff (2 : ℚ) = 0 ∧
      (↑(3 : ℚ) : WithTop ℚ) ≤ F.orderTop ∧
      B.coeff (4 : ℚ) = 0 ∧
      (↑(5 : ℚ) : WithTop ℚ) ≤ B.orderTop ∧
      B.coeff (5 : ℚ) * G.coeff (-1 : ℚ) +
        C.coeff (1 : ℚ) * F.coeff (3 : ℚ) = 0 ∧
      F.coeff (3 : ℚ) ≠ 0 := by
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
  have hterminalFactor := integratedTerminal_mainTangent_factorization68
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
    rw [← hterminalFactor, hCrec, hDrec, hErec]
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
        (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0))
        (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.E)) := by
    dsimp only [GR, rhoOneTangentEDefectHahn68]
    rw [map_sub, map_mul, hERmap, hCRmap]
    rw [map_mul, ratFuncAtHahn46_C]
  have hBR : (↑(4 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root BR).orderTop := by simpa only [BR] using hB
  have hCR : (0 : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root CR).orderTop := by rw [hCRmap]; exact hC
  have hFR : (↑(2 : ℚ) : WithTop ℚ) ≤
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
    ratFuncAtHahn46_deriv_orderTop_nonneg_of_nonneg T.root FR
      (le_trans (WithTop.coe_le_coe.mpr (by norm_num)) hFR)
  have hdG : (↑(-2 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root (Differential.deriv GR)).orderTop :=
    ratFuncAtHahn68_deriv_orderTop_ge_negTwo_of_ge_negOne
      T.root h0 GR T.scale_order hGR
  have hf2 := rhoOneMainTangentTerminal_gBoundary_induction_fZero68
    2 (by norm_num) (by norm_num) T.source.gamma T.source.epsilon
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
      hAH (by convert hBR using 1 <;> norm_num) hCR
      (by convert hFR using 1 <;> norm_num) hGR
      (by rw [hCRmap]; exact hS) hdA hdB hdC hdF hdG hdAco hAne
      (by rw [hGRmap]; exact hGne)
      (by
        rw [hCRmap, hFRmap, hGRmap]
        norm_num
        simpa only [BR] using hi4two)
      hsparseH' T.terminal_order
  rw [hFRmap] at hf2
  have hf2raw : (ratFuncAtHahn46 T.root FR).coeff ((2 : ℤ) : ℚ) = 0 := by
    norm_num
    rw [hFRmap]
    exact hf2
  have hF3raw := ratFuncAtHahn46_orderTop_ge_int_succ_of_coeff_zero
    T.root FR 2 hFR hf2raw
  norm_num at hF3raw
  have hF3 : (↑(3 : ℚ) : WithTop ℚ) ≤
      (rhoOneTangentDDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.B)
        (ratFuncAtHahn46 T.root T.source.D)).orderTop := by
    rw [← hFRmap]
    exact hF3raw
  have hb4 : (ratFuncAtHahn46 T.root T.source.B).coeff (4 : ℚ) = 0 := by
    rw [hf2] at hi4two
    norm_num at hi4two
    rcases hi4two with hb | hg
    · exact hb
    · exact (hGne hg).elim
  have hB5 := ratFuncAtHahn46_orderTop_ge_int_succ_of_coeff_zero
    T.root T.source.B 4 hB (by norm_num; exact hb4)
  norm_num at hB5
  change rhoOneI4ZeroFactored68
    (RatFunc.C T.source.gamma) (RatFunc.C T.source.epsilon)
    BR CR FR GR = 0 at hfact
  have hfactH := congrArg (ratFuncAtHahn46 T.root) hfact
  have hfactH' : rhoOneI4ZeroFactored68
      (HahnSeries.C T.source.gamma) (HahnSeries.C T.source.epsilon)
      (ratFuncAtHahn46 T.root BR) (ratFuncAtHahn46 T.root CR)
      (ratFuncAtHahn46 T.root FR) (ratFuncAtHahn46 T.root GR) = 0 := by
    simpa only [rhoOneI4ZeroFactored68, map_add, map_mul, map_pow,
      map_neg, map_div₀, map_ofNat, map_zero, map_one,
      ratFuncAtHahn46_C] using hfactH
  have hi4three := rhoOneI4ZeroFactored_gBoundary_induction68
    2 (by norm_num) T.source.gamma T.source.epsilon
      (ratFuncAtHahn46 T.root BR) (ratFuncAtHahn46 T.root CR)
      (ratFuncAtHahn46 T.root FR) (ratFuncAtHahn46 T.root GR)
      (by dsimp only [BR]; convert hB5 using 1 <;> norm_num)
      (by rw [hFRmap]; convert hF3 using 1 <;> norm_num)
      (by rw [hGRmap]; exact hG) (by rw [hCRmap]; exact hS) hfactH'
  rw [hCRmap, hFRmap, hGRmap] at hi4three
  norm_num at hi4three
  have hf3ne := rhoOneMainTangentTerminal_gBoundary_induction_fThree_ne68
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
      hAH (by dsimp only [BR]; convert hB5 using 1 <;> norm_num) hCR
      (by rw [hFRmap]; exact hF3) hGR (by rw [hCRmap]; exact hS)
      hdA hdB hdC hdF hdG hdAco hAne (by rw [hGRmap]; exact hGne)
      (by
        rw [hCRmap, hFRmap, hGRmap]
        simpa only [BR] using hi4three)
      hsparseH' T.terminal_order
  rw [hFRmap] at hf3ne
  exact ⟨hf2, hF3, hb4, (by convert hB5 using 1 <;> norm_num),
    by simpa only [BR] using hi4three, hf3ne⟩

/-- The zero-boundary leaf after exhausting every terminal coefficient below
the pole and recording the first coefficient at the pole. -/
def RhoOneDoubleZeroTerminalGBoundaryFiniteResidual68
    (gamma epsilon : k) (BR CR FR GR : RatFunc k)
    (A B C F G : HahnSeries ℚ k) : Prop :=
  rhoOneI4ZeroFactored68 (RatFunc.C gamma) (RatFunc.C epsilon)
      BR CR FR GR = 0 ∧
    (((((((((B.coeff (1 : ℚ) = 0 ∧
                  2 * C.coeff (0 : ℚ) + 3 * gamma = 0) ∧
                (↑(2 : ℚ) : WithTop ℚ) ≤ B.orderTop ∧
                (↑(1 : ℚ) : WithTop ℚ) ≤
                  (2 * C + HahnSeries.C (3 * gamma)).orderTop ∧
                B.coeff (2 : ℚ) * G.coeff (-1 : ℚ) +
                  C.coeff (1 : ℚ) * F.coeff (0 : ℚ) = 0) ∧
              F.coeff (0 : ℚ) = 0 ∧
              (↑(1 : ℚ) : WithTop ℚ) ≤ F.orderTop) ∧
            B.coeff (2 : ℚ) = 0 ∧
            (↑(3 : ℚ) : WithTop ℚ) ≤ B.orderTop ∧
            B.coeff (3 : ℚ) * G.coeff (-1 : ℚ) +
              C.coeff (1 : ℚ) * F.coeff (1 : ℚ) = 0) ∧
          F.coeff (1 : ℚ) = 0 ∧
          (↑(2 : ℚ) : WithTop ℚ) ≤ F.orderTop) ∧
        B.coeff (3 : ℚ) = 0 ∧
        (↑(4 : ℚ) : WithTop ℚ) ≤ B.orderTop ∧
        B.coeff (4 : ℚ) * G.coeff (-1 : ℚ) +
          C.coeff (1 : ℚ) * F.coeff (2 : ℚ) = 0) ∧
      F.coeff (2 : ℚ) = 0 ∧
      (↑(3 : ℚ) : WithTop ℚ) ≤ F.orderTop ∧
      B.coeff (4 : ℚ) = 0 ∧
      (↑(5 : ℚ) : WithTop ℚ) ≤ B.orderTop ∧
      B.coeff (5 : ℚ) * G.coeff (-1 : ℚ) +
        C.coeff (1 : ℚ) * F.coeff (3 : ℚ) = 0 ∧
      F.coeff (3 : ℚ) ≠ 0) ∨
      (B.coeff (1 : ℚ) ≠ 0 ∧
        2 * C.coeff (0 : ℚ) + 3 * gamma ≠ 0 ∧
        ∃ r : k, r ≠ 0 ∧ r ^ 2 = -3 * A.coeff (-2 : ℚ) ∧
          (3 * (2 * C.coeff (0 : ℚ) + 3 * gamma) =
              2 * r * B.coeff (1 : ℚ) ∨
           3 * (2 * C.coeff (0 : ℚ) + 3 * gamma) =
              -(2 * r * B.coeff (1 : ℚ))))))

/-- Exact backwire of the finite induction cap.  The two nonzero quadratic
rays and the full `G[-1]=0` sibling are intentionally preserved. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_exceptional_doubleZero_refinedGZero_terminalGBoundaryFiniteResidual
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
    RhoOneDoubleZeroTerminalGBoundaryFiniteResidual68
        T.source.gamma T.source.epsilon BR CR FR GR A B C F G ∨
      (G.coeff (-1 : ℚ) = 0 ∧ (0 : WithTop ℚ) ≤ G.orderTop ∧
        (RhoOneDoubleZeroRefinedGZeroTerminalBGainChild68
            T.source.gamma B C F ∨
         RhoOneDoubleZeroRefinedGZeroTerminalFGainChild68
            T.source.gamma B C F)) := by
  dsimp only [RhoOneDoubleZeroTerminalGBoundaryFiniteResidual68]
  have hnext := T.rhoOne_exceptional_doubleZero_refined_gZero
    P hB hC hF hG hbeta hdelta hzeta
  dsimp only at hnext
  rcases hnext with ⟨_, _, _, _, _, _, hsplit⟩
  rcases hsplit with hGne | ⟨hGzero, hG0, htail⟩
  · have hprev :=
      T.rhoOne_exceptional_doubleZero_refinedGZero_terminalGBoundaryInductionResidual
        hp hH hp6 hp5 hp4 P hB hC hF hG hbeta hdelta hzeta
    dsimp only [RhoOneDoubleZeroTerminalGBoundaryInductionResidual68] at hprev
    rcases hprev with ⟨hfact, hshape⟩ | hbad
    · left
      refine ⟨hfact, ?_⟩
      rcases hshape with hboundary | hrays
      · left
        rcases hboundary with ⟨hprev4, hb3, hB4, hi4two⟩
        rcases hprev4 with ⟨hprev3, hf1, hF2⟩
        rcases hprev3 with ⟨hprev2, hb2, hB3, hi4one⟩
        rcases hprev2 with ⟨hprev1, hf0, hF1⟩
        rcases hprev1 with ⟨hcoord, hB2, hS1, hi4zero⟩
        have hcap := T.rhoOne_exceptional_doubleZero_gBoundary_terminal_finiteCap
          hp hH hp6 hp5 hp4 P hB4 hC hF2 hG hS1 hGne hi4two
            (by simpa only using hfact) hbeta hdelta hzeta
        dsimp only at hcap
        rcases hcap with ⟨hf2, hF3, hb4, hB5, hi4three, hf3ne⟩
        exact ⟨⟨⟨⟨⟨⟨hcoord, hB2, hS1, hi4zero⟩, hf0, hF1⟩,
          hb2, hB3, hi4one⟩, hf1, hF2⟩, hb3, hB4, hi4two⟩,
          hf2, hF3, hb4, hB5, hi4three, hf3ne⟩
      · right
        exact hrays
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

end AlignedSquareTerminalGBoundaryFiniteInduction68

end Max11DegreeRoutes
