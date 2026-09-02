import Sol68ScaleTwoAlignedSquareTerminalGBoundaryCapDeterminantConsolidationScratch

/-! # Third-transport source scalar above the terminal-two cap -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareTerminalGBoundaryCapThirdSourceScalar68

variable {k : Type*} [Field k] [CharZero k]

/-- The apparent `B₁₄/F₆/C₁₀` bracket collapses to a multiple of
the first transport bracket.  Thus the third source scalar is consistent but
does not itself delete the cap. -/
theorem rhoOneThirdTransport_high_jet_elimination68
    (b' b'' b''' c c' c'' c''' f f' f'' f''' g : k)
    (htransport : 4 * c * c''' + 4 * c' * c'' -
      b''' * f - b'' * f' - b' * f'' - b * f''' = 0) :
    g * (4 * c * c''' + 4 * c' * c'' -
          b''' * f - b'' * f' - b * f''') + c' * f * f'' =
      f'' * (b' * g + c' * f) := by
  linear_combination g * htransport

/-- The third-transport source scalar, in its smallest high-jet-free form.
It is exactly `F₅` times the actual-scale first source scalar. -/
theorem rhoOneTerminal_cap_third_transport_source68
    (s source a1 b' c' f f' f'' g d3 : k)
    (hsource :
      2 * s ^ 2 * g * d3 * (b' * g + c' * f) - f ^ 3 * source +
          2 * s ^ 2 * f ^ 3 * a1 -
        2 * s ^ 2 * f ^ 2 * f' * d3 = 0) :
    2 * s ^ 2 * g * d3 * (f'' * (b' * g + c' * f)) -
        f ^ 3 * f'' * source + 2 * s ^ 2 * f ^ 3 * f'' * a1 -
      2 * s ^ 2 * f ^ 2 * f' * f'' * d3 = 0 := by
  linear_combination f'' * hsource

/-- Expanded high-jet form and its exact collapse through the third
transport. -/
theorem rhoOneTerminal_cap_third_transport_source_high68
    (s source a1 b b' b'' b''' c c' c'' c''' f f' f'' f'''
      g d3 : k)
    (hsource :
      2 * s ^ 2 * g * d3 * (b' * g + c' * f) - f ^ 3 * source +
          2 * s ^ 2 * f ^ 3 * a1 -
        2 * s ^ 2 * f ^ 2 * f' * d3 = 0)
    (htransport : 4 * c * c''' + 4 * c' * c'' -
      b''' * f - b'' * f' - b' * f'' - b * f''' = 0) :
    2 * s ^ 2 * g * d3 *
          (g * (4 * c * c''' + 4 * c' * c'' -
              b''' * f - b'' * f' - b * f''') + c' * f * f'') -
        f ^ 3 * f'' * source + 2 * s ^ 2 * f ^ 3 * f'' * a1 -
      2 * s ^ 2 * f ^ 2 * f' * f'' * d3 = 0 := by
  linear_combination f'' * hsource + 2 * s ^ 2 * g ^ 2 * d3 * htransport

def RhoOneDoubleZeroTerminalGBoundaryCapThirdSourcePacket68
    (gamma epsilon i3 sold cs source0 source1 source2 : k)
    (A B C F G dA : HahnSeries ℚ k) : Prop :=
  RhoOneDoubleZeroTerminalGBoundaryCapDeterminantPacket68
      gamma epsilon i3 sold cs source0 source1 source2 A B C F G dA ∧
    2 * cs ^ 2 * G.coeff (-1 : ℚ) * dA.coeff (-3 : ℚ) *
          (F.coeff 5 *
            (B.coeff 12 * G.coeff (-1 : ℚ) + C.coeff 8 * F.coeff 3)) -
        F.coeff 3 ^ 3 * F.coeff 5 * source0 +
        2 * cs ^ 2 * F.coeff 3 ^ 3 * F.coeff 5 * A.coeff (-1 : ℚ) -
      2 * cs ^ 2 * F.coeff 3 ^ 2 * F.coeff 4 * F.coeff 5 *
        dA.coeff (-3 : ℚ) = 0

def RhoOneDoubleZeroTerminalGBoundaryCapThirdSourceResidual68
    (root j gamma epsilon : k) (A0 : k[X])
    (h0R AR BR CR FR GR : RatFunc k)
    (A B C F G : HahnSeries ℚ k) : Prop :=
  RhoOneDoubleZeroTerminalGBoundaryCapDeterminantResidual68
      root j gamma epsilon A0 h0R AR BR CR FR GR A B C F G ∧
    ((B.coeff (1 : ℚ) = 0 ∧ 2 * C.coeff 0 + 3 * gamma = 0) →
      C.coeff (1 : ℚ) = 0 → C.coeff (2 : ℚ) = 0 →
      ∃ i3 sold cs : k,
        RhoOneDoubleZeroTerminalGBoundaryCapThirdSourcePacket68
          gamma epsilon i3 sold cs (A0.derivative.eval root)
            (A0.derivative.derivative.eval root)
            (A0.derivative.derivative.derivative.eval root)
            A B C F G (ratFuncAtHahn46 root (Differential.deriv AR)))

end AlignedSquareTerminalGBoundaryCapThirdSourceScalar68

end Max11DegreeRoutes

namespace Max11DegreeRoutes

section AlignedSquareTerminalGBoundaryCapThirdSourceBackwire68

variable {k : Type*} [Field k] [CharZero k]

/-- Literal source backwire of the third transport scalar.  The added row is
kept even though it is exactly the old cleared-source scalar multiplied by
`F[5]`; all predecessor siblings are preserved. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_exceptional_doubleZero_refinedGZero_terminalGBoundaryCapThirdSourceResidual
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
    RhoOneDoubleZeroTerminalGBoundaryCapThirdSourceResidual68
        T.root j T.source.gamma T.source.epsilon
        (localClearedA68RhoOne g u)
        (algebraMap k[X] (RatFunc k) h0) AR BR CR FR GR A B C F G ∨
      (G.coeff (-1 : ℚ) = 0 ∧ (0 : WithTop ℚ) ≤ G.orderTop ∧
        (RhoOneDoubleZeroRefinedGZeroTerminalBGainChild68
            T.source.gamma B C F ∨
         RhoOneDoubleZeroRefinedGZeroTerminalFGainChild68
            T.source.gamma B C F)) := by
  dsimp only [RhoOneDoubleZeroTerminalGBoundaryCapThirdSourceResidual68]
  have hprevRaw :=
    T.rhoOne_exceptional_doubleZero_refinedGZero_terminalGBoundaryCapDeterminantResidual
      hp hH hp6 hp5 hp4 P hB hC hF hG hbeta hdelta hzeta
  rcases hprevRaw with hprev | htail
  · left
    refine ⟨hprev, ?_⟩
    intro hcoord hc1 hc2
    obtain ⟨i3, sold, cs, hpacket⟩ := hprev.2 hcoord hc1 hc2
    have hI4packet := hpacket.1
    have hI3packet := hI4packet.1
    have hT2packet := hI3packet.1
    have hT1packet := hT2packet.1
    have hbase := hT1packet.1
    have hterminalNext := hbase.1.1.1
    have hnext := hterminalNext.1
    have htransport1 := hnext.2.2.2.2
    have hdependency := hterminalNext.2.2
    have hsource0 := hT1packet.2.2.1
    have hcleared := rhoOneTerminal_cap_transport_cleared_source68
      cs ((localClearedA68RhoOne g u).derivative.eval T.root)
      ((ratFuncAtHahn46 T.root T.source.A).coeff (-1 : ℚ))
      ((ratFuncAtHahn46 T.root T.source.B).coeff 12)
      ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0)).coeff 7)
      ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0)).coeff 8)
      ((rhoOneTangentDDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.B)
        (ratFuncAtHahn46 T.root T.source.D)).coeff 3)
      ((rhoOneTangentDDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.B)
        (ratFuncAtHahn46 T.root T.source.D)).coeff 4)
      ((rhoOneTangentEDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0))
        (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.E))).coeff (-1 : ℚ))
      ((ratFuncAtHahn46 T.root (Differential.deriv T.source.A)).coeff (-3 : ℚ))
      ((ratFuncAtHahn46 T.root (Differential.deriv T.source.A)).coeff (-2 : ℚ))
      htransport1 hdependency hsource0
    have hthirdSource := rhoOneTerminal_cap_third_transport_source68
      cs ((localClearedA68RhoOne g u).derivative.eval T.root)
      ((ratFuncAtHahn46 T.root T.source.A).coeff (-1 : ℚ))
      ((ratFuncAtHahn46 T.root T.source.B).coeff 12)
      ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0)).coeff 8)
      ((rhoOneTangentDDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.B)
        (ratFuncAtHahn46 T.root T.source.D)).coeff 3)
      ((rhoOneTangentDDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.B)
        (ratFuncAtHahn46 T.root T.source.D)).coeff 4)
      ((rhoOneTangentDDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.B)
        (ratFuncAtHahn46 T.root T.source.D)).coeff 5)
      ((rhoOneTangentEDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0))
        (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.E))).coeff (-1 : ℚ))
      ((ratFuncAtHahn46 T.root (Differential.deriv T.source.A)).coeff (-3 : ℚ))
      hcleared
    refine ⟨i3, sold, cs, ?_⟩
    dsimp only [RhoOneDoubleZeroTerminalGBoundaryCapThirdSourcePacket68]
    exact ⟨hpacket, hthirdSource⟩
  · exact Or.inr htail

end AlignedSquareTerminalGBoundaryCapThirdSourceBackwire68

end Max11DegreeRoutes
