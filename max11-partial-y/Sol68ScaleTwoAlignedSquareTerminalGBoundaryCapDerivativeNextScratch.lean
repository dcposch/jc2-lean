import Sol68ScaleTwoAlignedSquareTerminalGBoundaryCapTerminalNextScratch

/-! # The first source derivative above the `C₇/B₁₁` cap -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareTerminalGBoundaryCapDerivativeNext68

variable {k : Type*} [Field k] [CharZero k]

local instance alignedSquareTerminalGBoundaryCapDerivativeNextHahnCharZero68 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-- The next derivative coefficient of a coordinate with a quadratic local
denominator records the derivative of its cleared numerator. -/
theorem localHahn_deriv_coeff_next_of_cleared_two68
    (a c : k) (h0 A0 : k[X]) (A : RatFunc k) (hc : c ≠ 0)
    (hsingle :
      ratFuncAtHahn46 a (algebraMap k[X] (RatFunc k) h0) =
        HahnSeries.single (1 : ℚ) c)
    (hderiv :
      ratFuncAtHahn46 a
          (Differential.deriv (algebraMap k[X] (RatFunc k) h0)) =
        HahnSeries.C c)
    (hclear : algebraMap k[X] (RatFunc k) A0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 2 * A) :
    A0.derivative.eval a =
      c ^ 2 * (ratFuncAtHahn46 a (Differential.deriv A)).coeff (-2 : ℚ) +
        2 * c ^ 2 * (ratFuncAtHahn46 a A).coeff (-1 : ℚ) := by
  let h : RatFunc k := algebraMap k[X] (RatFunc k) h0
  let AH : HahnSeries ℚ k := ratFuncAtHahn46 a A
  let dAH : HahnSeries ℚ k :=
    ratFuncAtHahn46 a (Differential.deriv A)
  have hdclear := congrArg Differential.deriv hclear
  rw [GCD369RatFuncDerivative] at hdclear
  simp only [Derivation.leibniz, Derivation.leibniz_pow, nsmul_eq_mul,
    smul_eq_mul] at hdclear
  have hmapped' := congrArg (ratFuncAtHahn46 a) hdclear
  simp only [map_add, map_mul, map_pow, map_natCast, hsingle,
    hderiv] at hmapped'
  norm_num [HahnSeries.C_apply, HahnSeries.single_mul_single, pow_two]
    at hmapped'
  have htwoSingle :
      (2 : HahnSeries ℚ k) * HahnSeries.single (1 : ℚ) (c * c) =
        HahnSeries.single (1 : ℚ) (2 * c ^ 2) := by
    rw [two_mul, ← HahnSeries.single_add]
    congr 1
    ring
  rw [htwoSingle] at hmapped'
  have hcoeff := congrArg
    (fun x : HahnSeries ℚ k => x.coeff (0 : ℚ)) hmapped'
  rw [ratFuncAtHahn46_algebraMap_coeff_zero, HahnSeries.coeff_add] at hcoeff
  simp only [HahnSeries.single_pow, HahnSeries.coeff_single_mul,
    HahnSeries.coeff_mul_single, nsmul_eq_mul] at hcoeff
  convert hcoeff using 1 <;> norm_num <;> ring

/-- The transport row substitutes `B₁₂ G₋₁+C₈F₃` for the terminal
minor, and the cleared-source derivative substitutes for `dA[-2]`. -/
theorem rhoOneTerminal_cap_transport_cleared_source68
    (s source a1 b' c c' f f' g d3 d2 : k)
    (htransport : c * f' - b' * g - 2 * c' * f = 0)
    (hdependency :
      2 * g * d3 * (c * f' - f * c') - f ^ 3 * d2 -
        2 * f ^ 2 * f' * d3 = 0)
    (hsource : source = s ^ 2 * d2 + 2 * s ^ 2 * a1) :
    2 * s ^ 2 * g * d3 * (b' * g + c' * f) - f ^ 3 * source +
        2 * s ^ 2 * f ^ 3 * a1 -
      2 * s ^ 2 * f ^ 2 * f' * d3 = 0 := by
  linear_combination s ^ 2 * hdependency -
    2 * s ^ 2 * g * d3 * htransport - f ^ 3 * hsource

/-- The cap packet after the first genuinely source-sensitive derivative
coefficient. -/
def RhoOneDoubleZeroTerminalGBoundaryCapDerivativeNextPacket68
    (gamma epsilon i3 s source : k)
    (A B C F G dA : HahnSeries ℚ k) : Prop :=
  RhoOneDoubleZeroTerminalGBoundaryCapTerminalNextPacket68
      gamma epsilon i3 A B C F G dA ∧
    s ≠ 0 ∧
    source = s ^ 2 * dA.coeff (-2 : ℚ) +
      2 * s ^ 2 * A.coeff (-1 : ℚ) ∧
    2 * s ^ 2 * G.coeff (-1 : ℚ) * dA.coeff (-3 : ℚ) *
          (B.coeff (12 : ℚ) * G.coeff (-1 : ℚ) +
            C.coeff (8 : ℚ) * F.coeff (3 : ℚ)) -
        F.coeff (3 : ℚ) ^ 3 * source +
          2 * s ^ 2 * F.coeff (3 : ℚ) ^ 3 * A.coeff (-1 : ℚ) -
      2 * s ^ 2 * F.coeff (3 : ℚ) ^ 2 * F.coeff (4 : ℚ) *
        dA.coeff (-3 : ℚ) = 0

/-- Only the `C[1]=C[2]=0` cap child is refined; all upstream siblings are
kept literally in the predecessor residual. -/
def RhoOneDoubleZeroTerminalGBoundaryCapDerivativeNextResidual68
    (root j gamma epsilon : k) (A0 : k[X])
    (h0R AR BR CR FR GR : RatFunc k)
    (A B C F G : HahnSeries ℚ k) : Prop :=
  RhoOneDoubleZeroTerminalGBoundaryCapTerminalNextResidual68
      root j gamma epsilon h0R AR BR CR FR GR A B C F G ∧
    ((B.coeff (1 : ℚ) = 0 ∧
        2 * C.coeff (0 : ℚ) + 3 * gamma = 0) →
      C.coeff (1 : ℚ) = 0 → C.coeff (2 : ℚ) = 0 →
      ∃ i3 s : k, RhoOneDoubleZeroTerminalGBoundaryCapDerivativeNextPacket68
        gamma epsilon i3 s (A0.derivative.eval root) A B C F G
          (ratFuncAtHahn46 root (Differential.deriv AR)))

/-- Literal source backwire of the cleared-numerator derivative and the
transported terminal dependency. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_exceptional_doubleZero_refinedGZero_terminalGBoundaryCapDerivativeNextResidual
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
    RhoOneDoubleZeroTerminalGBoundaryCapDerivativeNextResidual68
        T.root j T.source.gamma T.source.epsilon
        (localClearedA68RhoOne g u)
        (algebraMap k[X] (RatFunc k) h0) AR BR CR FR GR A B C F G ∨
      (G.coeff (-1 : ℚ) = 0 ∧ (0 : WithTop ℚ) ≤ G.orderTop ∧
        (RhoOneDoubleZeroRefinedGZeroTerminalBGainChild68
            T.source.gamma B C F ∨
         RhoOneDoubleZeroRefinedGZeroTerminalFGainChild68
            T.source.gamma B C F)) := by
  dsimp only [RhoOneDoubleZeroTerminalGBoundaryCapDerivativeNextResidual68]
  have hprev :=
    T.rhoOne_exceptional_doubleZero_refinedGZero_terminalGBoundaryCapTerminalNextResidual
      hp hH hp6 hp5 hp4 P hB hC hF hG hbeta hdelta hzeta
  rcases hprev with hcapResidual | hsibling
  · left
    refine ⟨hcapResidual, ?_⟩
    intro hcoord hc1 hc2
    obtain ⟨i3, hpacket⟩ := hcapResidual.2 hcoord hc1 hc2
    have hparts := hpacket
    dsimp only [RhoOneDoubleZeroTerminalGBoundaryCapTerminalNextPacket68,
      RhoOneDoubleZeroTerminalGBoundaryCapNextJetPacket68] at hparts
    rcases hparts with
      ⟨⟨_, _, _, _, htransport⟩, _, hdependency⟩
    obtain ⟨s, t, v, z, hs, hsingle, ht, hv, hzdef, hz, hvcore,
      htcore⟩ := P.1
    let A0 : k[X] := localClearedA68RhoOne g u
    have hAclear := (T.source.clearedCoordinatesRhoOne hp T.scale_ne_zero
      hH hp6 hp5 hp4).1
    change algebraMap k[X] (RatFunc k) A0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 2 * T.source.A at hAclear
    obtain ⟨s', hs', hsingle', hderiv'⟩ :=
      ratFuncAtHahn68_linearRoot_single_deriv
        h0 T.root T.scale_degree T.root_eq
    have hsEq : s' = s := by
      have heq := congrArg (fun X : HahnSeries ℚ k => X.coeff (1 : ℚ))
        (hsingle'.symm.trans hsingle)
      simpa only [HahnSeries.coeff_single_same] using heq
    subst s'
    have hsource := localHahn_deriv_coeff_next_of_cleared_two68
      T.root s h0 A0 T.source.A hs hsingle hderiv' hAclear
    have hcombined := rhoOneTerminal_cap_transport_cleared_source68
      s (A0.derivative.eval T.root)
      ((ratFuncAtHahn46 T.root T.source.A).coeff (-1 : ℚ))
      ((ratFuncAtHahn46 T.root T.source.B).coeff (12 : ℚ))
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
      ((ratFuncAtHahn46 T.root
        (Differential.deriv T.source.A)).coeff (-3 : ℚ))
      ((ratFuncAtHahn46 T.root
        (Differential.deriv T.source.A)).coeff (-2 : ℚ))
      htransport hdependency hsource
    refine ⟨i3, s, ?_⟩
    dsimp only [RhoOneDoubleZeroTerminalGBoundaryCapDerivativeNextPacket68]
    simpa only [A0] using ⟨hpacket, hs, hsource, hcombined⟩
  · exact Or.inr hsibling

end AlignedSquareTerminalGBoundaryCapDerivativeNext68

end Max11DegreeRoutes
