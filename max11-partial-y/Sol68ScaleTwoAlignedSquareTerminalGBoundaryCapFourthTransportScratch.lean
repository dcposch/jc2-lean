import Sol68ScaleTwoAlignedSquareTerminalGBoundaryCapLowerFourBackwireScratch

/-! # Fourth coordinate transport from the lower-four cap jets -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareTerminalGBoundaryCapFourthTransport68

variable {k : Type*} [Field k] [CharZero k]

/-- The coefficient-21 instance of
`B(4CG+2F²+3εC)-C(4BG+4CF+3εB)=-2F(2C²-BF)`.
The first transport supplies the only lower coefficient not already stored
as a literal coefficient of `2C²-BF`. -/
theorem rhoOneI3I4_coordinate_cap_fourth_transport68
    (b b1 b2 b3 b4 c c1 c2 c3 c4 f f1 f2 f3 f4
      g g1 g2 g3 g4 epsilon : k)
    (hf : f ≠ 0) (hg : g ≠ 0)
    (hcap3 : 2 * c * g + f ^ 2 = 0)
    (hcap4 : b * g + c * f = 0)
    (hscalar : b * f - 2 * c ^ 2 = 0)
    (htransport1 : c * f1 - b1 * g - 2 * c1 * f = 0)
    (htransport2 : 2 * c1 ^ 2 + 4 * c * c2 -
      b2 * f - b1 * f1 - b * f2 = 0)
    (htransport3 : 4 * c * c3 + 4 * c1 * c2 -
      b3 * f - b2 * f1 - b1 * f2 - b * f3 = 0)
    (hI37 : 4 * (c * g1 + c1 * g + f * f1) + 3 * epsilon * c = 0)
    (hI38 : 4 * (c * g2 + c1 * g1 + c2 * g + f * f2) +
      2 * f1 ^ 2 + 3 * epsilon * c1 = 0)
    (hI39 : 4 * (c * g3 + c1 * g2 + c2 * g1 + c3 * g +
      f * f3 + f1 * f2) + 3 * epsilon * c2 = 0)
    (hI310 : 4 * (c * g4 + c1 * g3 + c2 * g2 + c3 * g1 + c4 * g +
      f * f4 + f1 * f3 + (1 / 2 : k) * f2 ^ 2) +
      3 * epsilon * c3 = 0)
    (hI411 : 4 * (b * g1 + b1 * g) +
      4 * (c * f1 + c1 * f) + 3 * epsilon * b = 0)
    (hI412 : 4 * (b * g2 + b1 * g1 + b2 * g) +
      4 * (c * f2 + c1 * f1 + c2 * f) + 3 * epsilon * b1 = 0)
    (hI413 : 4 * (b * g3 + b1 * g2 + b2 * g1 + b3 * g) +
      4 * (c * f3 + c1 * f2 + c2 * f1 + c3 * f) +
      3 * epsilon * b2 = 0)
    (hI414 : 4 * (b * g4 + b1 * g3 + b2 * g2 + b3 * g1 + b4 * g) +
      4 * (c * f4 + c1 * f3 + c2 * f2 + c3 * f1 + c4 * f) +
      3 * epsilon * b3 = 0) :
    4 * c * c4 + 4 * c1 * c3 + 2 * c2 ^ 2 -
      b4 * f - b3 * f1 - b2 * f2 - b1 * f3 - b * f4 = 0 := by
  let H0 := 2 * c ^ 2 - b * f
  let H1 := 4 * c * c1 - b1 * f - b * f1
  let H2 := 2 * c1 ^ 2 + 4 * c * c2 -
    b2 * f - b1 * f1 - b * f2
  let H3 := 4 * c * c3 + 4 * c1 * c2 -
    b3 * f - b2 * f1 - b1 * f2 - b * f3
  let H4 := 4 * c * c4 + 4 * c1 * c3 + 2 * c2 ^ 2 -
    b4 * f - b3 * f1 - b2 * f2 - b1 * f3 - b * f4
  have hH0 : H0 = 0 := by
    dsimp only [H0]
    linear_combination -hscalar
  have hgH1 : g * H1 = 0 := by
    dsimp only [H1]
    linear_combination 2 * c1 * hcap3 + f * htransport1 - f1 * hcap4
  have hH1 : H1 = 0 := by
    exact (mul_eq_zero.mp hgH1).resolve_left hg
  have hH2 : H2 = 0 := by simpa only [H2] using htransport2
  have hH3 : H3 = 0 := by simpa only [H3] using htransport3
  let R36 := 4 * c * g + 2 * f ^ 2
  let R37 := 4 * (c * g1 + c1 * g + f * f1) + 3 * epsilon * c
  let R38 := 4 * (c * g2 + c1 * g1 + c2 * g + f * f2) +
    2 * f1 ^ 2 + 3 * epsilon * c1
  let R39 := 4 * (c * g3 + c1 * g2 + c2 * g1 + c3 * g +
    f * f3 + f1 * f2) + 3 * epsilon * c2
  let R310 := 4 * (c * g4 + c1 * g3 + c2 * g2 + c3 * g1 + c4 * g +
    f * f4 + f1 * f3 + (1 / 2 : k) * f2 ^ 2) + 3 * epsilon * c3
  let R410 := 4 * (b * g + c * f)
  let R411 := 4 * (b * g1 + b1 * g) +
    4 * (c * f1 + c1 * f) + 3 * epsilon * b
  let R412 := 4 * (b * g2 + b1 * g1 + b2 * g) +
    4 * (c * f2 + c1 * f1 + c2 * f) + 3 * epsilon * b1
  let R413 := 4 * (b * g3 + b1 * g2 + b2 * g1 + b3 * g) +
    4 * (c * f3 + c1 * f2 + c2 * f1 + c3 * f) + 3 * epsilon * b2
  let R414 := 4 * (b * g4 + b1 * g3 + b2 * g2 + b3 * g1 + b4 * g) +
    4 * (c * f4 + c1 * f3 + c2 * f2 + c3 * f1 + c4 * f) +
      3 * epsilon * b3
  have hR36 : R36 = 0 := by
    dsimp only [R36]
    linear_combination 2 * hcap3
  have hR37 : R37 = 0 := by simpa only [R37] using hI37
  have hR38 : R38 = 0 := by simpa only [R38] using hI38
  have hR39 : R39 = 0 := by simpa only [R39] using hI39
  have hR310 : R310 = 0 := by simpa only [R310] using hI310
  have hR410 : R410 = 0 := by
    dsimp only [R410]
    linear_combination 4 * hcap4
  have hR411 : R411 = 0 := by simpa only [R411] using hI411
  have hR412 : R412 = 0 := by simpa only [R412] using hI412
  have hR413 : R413 = 0 := by simpa only [R413] using hI413
  have hR414 : R414 = 0 := by simpa only [R414] using hI414
  have hid :
      b * R310 + b1 * R39 + b2 * R38 + b3 * R37 + b4 * R36 -
        (c * R414 + c1 * R413 + c2 * R412 + c3 * R411 + c4 * R410) =
      -2 * (f * H4 + f1 * H3 + f2 * H2 + f3 * H1 + f4 * H0) := by
    dsimp only [R36, R37, R38, R39, R310, R410, R411, R412, R413,
      R414, H0, H1, H2, H3, H4]
    ring
  rw [hR36, hR37, hR38, hR39, hR310, hR410, hR411, hR412,
    hR413, hR414, hH0, hH1, hH2, hH3] at hid
  have hfH4 : f * H4 = 0 := by linear_combination (1 / 2 : k) * hid
  have hH4 := (mul_eq_zero.mp hfH4).resolve_left hf
  simpa only [H4] using hH4

def RhoOneDoubleZeroTerminalGBoundaryCapFourthTransportPacket68
    (gamma epsilon i3 sold cs source0 source1 source2 : k)
    (A B C F G dA : HahnSeries ℚ k) : Prop :=
  RhoOneDoubleZeroTerminalGBoundaryCapI3TenI4FourteenPacket68
      gamma epsilon i3 sold cs source0 source1 source2 A B C F G dA ∧
    4 * C.coeff 7 * C.coeff 11 + 4 * C.coeff 8 * C.coeff 10 +
      2 * C.coeff 9 ^ 2 - B.coeff 15 * F.coeff 3 -
      B.coeff 14 * F.coeff 4 - B.coeff 13 * F.coeff 5 -
      B.coeff 12 * F.coeff 6 - B.coeff 11 * F.coeff 7 = 0

def RhoOneDoubleZeroTerminalGBoundaryCapFourthTransportResidual68
    (root j gamma epsilon : k) (A0 : k[X])
    (h0R AR BR CR FR GR : RatFunc k)
    (A B C F G : HahnSeries ℚ k) : Prop :=
  RhoOneDoubleZeroTerminalGBoundaryCapLowerFourResidual68
      root j gamma epsilon A0 h0R AR BR CR FR GR A B C F G ∧
    ((B.coeff (1 : ℚ) = 0 ∧ 2 * C.coeff 0 + 3 * gamma = 0) →
      C.coeff (1 : ℚ) = 0 → C.coeff (2 : ℚ) = 0 →
      ∃ i3 sold cs : k,
        RhoOneDoubleZeroTerminalGBoundaryCapFourthTransportPacket68
          gamma epsilon i3 sold cs (A0.derivative.eval root)
            (A0.derivative.derivative.eval root)
            (A0.derivative.derivative.derivative.eval root)
            A B C F G (ratFuncAtHahn46 root (Differential.deriv AR)))

end AlignedSquareTerminalGBoundaryCapFourthTransport68

end Max11DegreeRoutes

namespace Max11DegreeRoutes

section AlignedSquareTerminalGBoundaryCapFourthTransportBackwire68

variable {k : Type*} [Field k] [CharZero k]

theorem SquareZeroLIntegratedLocalRootData68.rhoOne_exceptional_doubleZero_refinedGZero_terminalGBoundaryCapFourthTransportResidual
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
      (rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.B)
        (ratFuncAtHahn46 T.root T.source.D)).orderTop)
    (hG : (↑(-1 : ℚ) : WithTop ℚ) ≤
      (rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
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
    let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
    let F := rhoOneTangentDDefectHahn68 A B
      (ratFuncAtHahn46 T.root T.source.D)
    let G := rhoOneTangentEDefectHahn68 A C
      (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
    RhoOneDoubleZeroTerminalGBoundaryCapFourthTransportResidual68
        T.root j T.source.gamma T.source.epsilon (localClearedA68RhoOne g u)
        (algebraMap k[X] (RatFunc k) h0) AR BR CR FR GR A B C F G ∨
      (G.coeff (-1 : ℚ) = 0 ∧ (0 : WithTop ℚ) ≤ G.orderTop ∧
        (RhoOneDoubleZeroRefinedGZeroTerminalBGainChild68 T.source.gamma B C F ∨
         RhoOneDoubleZeroRefinedGZeroTerminalFGainChild68 T.source.gamma B C F)) := by
  dsimp only [RhoOneDoubleZeroTerminalGBoundaryCapFourthTransportResidual68]
  have hprevRaw :=
    T.rhoOne_exceptional_doubleZero_refinedGZero_terminalGBoundaryCapLowerFourResidual
      hp hH hp6 hp5 hp4 P hB hC hF hG hbeta hdelta hzeta
  rcases hprevRaw with hprev | htail
  · left
    refine ⟨hprev, ?_⟩
    intro hcoord hc1 hc2
    obtain ⟨i3, sold, cs, hpacket⟩ := hprev.2 hcoord hc1 hc2
    have hI3ten := hpacket.1
    have hthirdSource := hI3ten.1
    have hdet := hthirdSource.1
    have hI4thirteen := hdet.1
    have hI3nine := hI4thirteen.1
    have hT2 := hI3nine.1
    have hT1 := hT2.1
    have hI4twelve := hT1.1
    have hI3eight := hI4twelve.1
    have hderivative := hI3eight.1
    have hterminal := hderivative.1
    have hnext := hterminal.1
    have hci3 := hnext.1
    dsimp only [RhoOneDoubleZeroTerminalGBoundaryCI3CapPacket68] at hci3
    rcases hci3 with
      ⟨hi3H, hc3, hc4, hc5, hc6, hb7, hb8, hb9, hb10,
        hS7, hB11, hcap3, hc7ne, hcap4, hb11ne, hBexact⟩
    have hscalar : (ratFuncAtHahn46 T.root T.source.B).coeff 11 *
          (rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.B)
            (ratFuncAtHahn46 T.root T.source.D)).coeff 3 -
        2 * (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0)).coeff 7 ^ 2 = 0 := by
      linear_combination hnext.2.1
    have hfne : (rhoOneTangentDDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.B)
        (ratFuncAtHahn46 T.root T.source.D)).coeff 3 ≠ 0 := by
      have hbfne : (ratFuncAtHahn46 T.root T.source.B).coeff 11 *
          (rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.B)
            (ratFuncAtHahn46 T.root T.source.D)).coeff 3 ≠ 0 := by
        rw [hnext.2.1]
        exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hc7ne)
      exact (mul_ne_zero_iff.mp hbfne).2
    have hgne : (rhoOneTangentEDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0))
        (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.E))).coeff (-1 : ℚ) ≠ 0 := by
      intro hg0
      rw [hg0, mul_zero, zero_add] at hcap4
      exact (mul_ne_zero hc7ne hfne) hcap4
    have hrow8 := hI3eight.2.1
    have hrow12 := hI4twelve.2.1
    have hrow9 := hI3nine.2.1
    have hrow13 := hI4thirteen.2.1
    have hrow10 := hI3ten.2.1
    have hrow14 := hpacket.2.1
    have hfourth := rhoOneI3I4_coordinate_cap_fourth_transport68
      ((ratFuncAtHahn46 T.root T.source.B).coeff 11)
      ((ratFuncAtHahn46 T.root T.source.B).coeff 12)
      ((ratFuncAtHahn46 T.root T.source.B).coeff 13)
      ((ratFuncAtHahn46 T.root T.source.B).coeff 14)
      ((ratFuncAtHahn46 T.root T.source.B).coeff 15)
      ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0)).coeff 7)
      ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0)).coeff 8)
      ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0)).coeff 9)
      ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0)).coeff 10)
      ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0)).coeff 11)
      ((rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.B)
        (ratFuncAtHahn46 T.root T.source.D)).coeff 3)
      ((rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.B)
        (ratFuncAtHahn46 T.root T.source.D)).coeff 4)
      ((rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.B)
        (ratFuncAtHahn46 T.root T.source.D)).coeff 5)
      ((rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.B)
        (ratFuncAtHahn46 T.root T.source.D)).coeff 6)
      ((rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.B)
        (ratFuncAtHahn46 T.root T.source.D)).coeff 7)
      ((rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0))
        (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.E))).coeff (-1 : ℚ))
      ((rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0))
        (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.E))).coeff 0)
      ((rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0))
        (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.E))).coeff 1)
      ((rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0))
        (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.E))).coeff 2)
      ((rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0))
        (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.E))).coeff 3)
      T.source.epsilon hfne hgne hcap3 hcap4 hscalar hnext.2.2.2.2
      hI4twelve.2.2.1 hdet.2.2.2.2 hnext.2.2.1 hrow8 hrow9 (by
        dsimp only [rhoOneI3CapTenCore68] at hrow10
        exact hrow10) hnext.2.2.2.1 hrow12 (by
        dsimp only [rhoOneI4CapThirteenCore68] at hrow13
        linear_combination hrow13) (by
        dsimp only [rhoOneI4CapFourteenCore68] at hrow14
        linear_combination hrow14)
    refine ⟨i3, sold, cs, ?_⟩
    dsimp only [RhoOneDoubleZeroTerminalGBoundaryCapFourthTransportPacket68]
    exact ⟨hpacket, hfourth⟩
  · exact Or.inr htail

end AlignedSquareTerminalGBoundaryCapFourthTransportBackwire68

end Max11DegreeRoutes
