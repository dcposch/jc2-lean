import Sol68ScaleTwoAlignedSquareTerminalGBoundaryCapI3TwelveRestoredScratch

/-! # Source backwire and honest split at restored I₃[12] -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareTerminalGBoundaryCapI3TwelveBackwire68

variable {k : Type*} [Field k] [CharZero k]

def rhoOneI3CapTwelveReducedCore68
    (C F G : HahnSeries ℚ k) : k :=
  C.coeff 7 * G.coeff 5 + C.coeff 8 * G.coeff 4 +
    C.coeff 9 * G.coeff 3 + C.coeff 10 * G.coeff 2 +
    C.coeff 11 * G.coeff 1 + C.coeff 12 * G.coeff 0 +
    C.coeff 13 * G.coeff (-1 : ℚ) + F.coeff 3 * F.coeff 9 +
    F.coeff 4 * F.coeff 8 + F.coeff 5 * F.coeff 7 +
    (1 / 2 : k) * F.coeff 6 ^ 2

def RhoOneDoubleZeroTerminalGBoundaryCapI3TwelvePacket68
    (gamma epsilon i3 sold cs source0 source1 source2 : k)
    (A B C F G dA : HahnSeries ℚ k) : Prop :=
  RhoOneDoubleZeroTerminalGBoundaryCapEndpointFivePacket68
      gamma epsilon i3 sold cs source0 source1 source2 A B C F G dA ∧
    RhoOneDoubleZeroTerminalGBoundaryCapI3TwelveRestoredTarget68
      epsilon A B C F G ∧
    (rhoOneI3CapTwelveReducedCore68 C F G ≠ 0 ∨
      (epsilon ≠ 0 ∧ C.coeff 12 ≠ 0))

def RhoOneDoubleZeroTerminalGBoundaryCapI3TwelveResidual68
    (root j gamma epsilon : k) (A0 : k[X])
    (h0R AR BR CR FR GR : RatFunc k)
    (A B C F G : HahnSeries ℚ k) : Prop :=
  RhoOneDoubleZeroTerminalGBoundaryCapEndpointFiveResidual68
      root j gamma epsilon A0 h0R AR BR CR FR GR A B C F G ∧
    ((B.coeff (1 : ℚ) = 0 ∧ 2 * C.coeff 0 + 3 * gamma = 0) →
      C.coeff (1 : ℚ) = 0 → C.coeff (2 : ℚ) = 0 →
      ∃ i3 sold cs : k,
        RhoOneDoubleZeroTerminalGBoundaryCapI3TwelvePacket68
          gamma epsilon i3 sold cs (A0.derivative.eval root)
            (A0.derivative.derivative.eval root)
            (A0.derivative.derivative.derivative.eval root)
            A B C F G (ratFuncAtHahn46 root (Differential.deriv AR)))

theorem SquareZeroLIntegratedLocalRootData68.rhoOne_exceptional_doubleZero_refinedGZero_terminalGBoundaryCapI3TwelveResidual
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
    RhoOneDoubleZeroTerminalGBoundaryCapI3TwelveResidual68
        T.root j T.source.gamma T.source.epsilon (localClearedA68RhoOne g u)
        (algebraMap k[X] (RatFunc k) h0) AR BR CR FR GR A B C F G ∨
      (G.coeff (-1 : ℚ) = 0 ∧ (0 : WithTop ℚ) ≤ G.orderTop ∧
        (RhoOneDoubleZeroRefinedGZeroTerminalBGainChild68 T.source.gamma B C F ∨
         RhoOneDoubleZeroRefinedGZeroTerminalFGainChild68 T.source.gamma B C F)) := by
  dsimp only [RhoOneDoubleZeroTerminalGBoundaryCapI3TwelveResidual68]
  have hprevRaw :=
    T.rhoOne_exceptional_doubleZero_refinedGZero_terminalGBoundaryCapEndpointFiveResidual
      hp hH hp6 hp5 hp4 P hB hC hF hG hbeta hdelta hzeta
  rcases hprevRaw with hprev | htail
  · left
    refine ⟨hprev, ?_⟩
    intro hcoord hc1 hc2
    obtain ⟨i3, sold, cs, hpacket⟩ := hprev.2 hcoord hc1 hc2
    have hfourth := hpacket.1.1.1
    have hI3ten := hfourth.1.1
    have hthirdSource := hI3ten.1
    have hdet := hthirdSource.1
    have hI4thirteen := hdet.1
    have hI3nine := hI4thirteen.1
    have hT2packet := hI3nine.1
    have hT1packet := hT2packet.1
    have hI4twelve := hT1packet.1
    have hI3eight := hI4twelve.1
    have hderivative := hI3eight.1
    have hterminal := hderivative.1
    have hnext := hterminal.1
    have hci3 := hnext.1
    dsimp only [RhoOneDoubleZeroTerminalGBoundaryCI3CapPacket68] at hci3
    rcases hci3 with
      ⟨hi3H, hc3, hc4, hc5, hc6, hb7, hb8, hb9, hb10,
        hS7, hB11, hcap3, hc7ne, hcap4, hb11ne, hBexact⟩
    have hterminalTwoResidual := hprev.1.1.1.1.1.1.1
    have hi4res := hterminalTwoResidual.1.1
    have hfinite := hi4res.1.1.1.1.1.1.1.1
    dsimp only [RhoOneDoubleZeroTerminalGBoundaryFiniteResidual68] at hfinite
    rcases hfinite with ⟨hfact, hboundary | hrays⟩
    · rcases hboundary with ⟨hcurrent, hf2, hF3, hb4, hB5,
        hi4three, hf3ne⟩
      let AR : RatFunc k := T.source.A
      let BR : RatFunc k := T.source.B
      let CR : RatFunc k := T.source.C0 - RatFunc.C (1 / 3 : k) * AR ^ 2
      let FR : RatFunc k := T.source.D - RatFunc.C (1 / 3 : k) * AR * BR
      let GR : RatFunc k :=
        (T.source.E - RatFunc.C (1 / 27 : k) * AR ^ 3) -
          RatFunc.C (1 / 3 : k) * AR * CR
      have hCRmap : ratFuncAtHahn46 T.root CR =
          rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.C0) := by
        dsimp only [CR, AR, rhoOneCDefectHahn68]
        simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
      have hFRmap : ratFuncAtHahn46 T.root FR =
          rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.B)
            (ratFuncAtHahn46 T.root T.source.D) := by
        dsimp only [FR, AR, BR, rhoOneTangentDDefectHahn68]
        simp only [map_sub, map_mul, ratFuncAtHahn46_C]
      have hGRmap : ratFuncAtHahn46 T.root GR =
          rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.C0))
            (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.E)) := by
        dsimp only [GR, CR, AR, rhoOneTangentEDefectHahn68,
          rhoOneCDefectHahn68, rhoOneEDefectHahn68]
        simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
      have hbounds := P.2.1
      dsimp only [RhoOneZeroLCubicImprovedHahnBounds68] at hbounds
      have hAH : (↑(-2 : ℚ) : WithTop ℚ) ≤
          (ratFuncAtHahn46 T.root AR).orderTop := by
        simpa only [AR] using hbounds.1
      have hi3R : rhoOneI3CapFactored68
          (RatFunc.C T.source.gamma) (RatFunc.C T.source.epsilon)
          AR BR CR FR GR = RatFunc.C i3 := by
        apply ratFuncAtHahn46_injective T.root
        simpa only [rhoOneI3CapFactored68, map_add, map_sub, map_mul,
          map_pow, map_neg, map_div₀, map_ofNat, map_one,
          ratFuncAtHahn46_C, hCRmap, hFRmap, hGRmap, AR, BR] using hi3H
      have hrowraw := rhoOneI3CapFactored_cap_coeff_twelve_restored68
        T.root T.source.gamma T.source.epsilon i3 AR BR CR FR GR
        hAH (by simpa only [BR] using hB11)
        (by rw [hCRmap]; exact hC) (by rw [hFRmap]; exact hF3)
        (by rw [hGRmap]; exact hG) (by rw [hCRmap]; exact hS7) hi3R
      rw [hCRmap, hFRmap, hGRmap] at hrowraw
      have hrow : RhoOneDoubleZeroTerminalGBoundaryCapI3TwelveRestoredTarget68
          T.source.epsilon (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.B)
          (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.C0))
          (rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.B)
            (ratFuncAtHahn46 T.root T.source.D))
          (rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.C0))
            (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.E))) := by
        dsimp only [AR, BR] at hrowraw
        exact hrowraw
      have hsplit :
          rhoOneI3CapTwelveReducedCore68
              (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                (ratFuncAtHahn46 T.root T.source.C0))
              (rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                (ratFuncAtHahn46 T.root T.source.B)
                (ratFuncAtHahn46 T.root T.source.D))
              (rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                  (ratFuncAtHahn46 T.root T.source.C0))
                (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                  (ratFuncAtHahn46 T.root T.source.E))) ≠ 0 ∨
            (T.source.epsilon ≠ 0 ∧
              (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                (ratFuncAtHahn46 T.root T.source.C0)).coeff 12 ≠ 0) := by
        apply rhoOneI3CapTwelve_restored_nonzero_split68
          ((ratFuncAtHahn46 T.root T.source.A).coeff (-2 : ℚ))
          ((ratFuncAtHahn46 T.root T.source.B).coeff 11)
          ((rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.B)
            (ratFuncAtHahn46 T.root T.source.D)).coeff 3)
          (rhoOneI3CapTwelveReducedCore68
            (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.C0))
            (rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.B)
              (ratFuncAtHahn46 T.root T.source.D))
            (rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                (ratFuncAtHahn46 T.root T.source.C0))
              (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                (ratFuncAtHahn46 T.root T.source.E))))
          T.source.epsilon
          ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.C0)).coeff 12)
          P.2.2.1 hb11ne hf3ne
        dsimp only [RhoOneDoubleZeroTerminalGBoundaryCapI3TwelveRestoredTarget68,
          rhoOneI3CapTwelveRestoredCore68,
          rhoOneI3CapTwelveReducedCore68] at hrow ⊢
        exact hrow
      refine ⟨i3, sold, cs, ?_⟩
      dsimp only [RhoOneDoubleZeroTerminalGBoundaryCapI3TwelvePacket68]
      exact ⟨hpacket, hrow, hsplit⟩
    · exact (hrays.1 hcoord.1).elim
  · exact Or.inr htail

end AlignedSquareTerminalGBoundaryCapI3TwelveBackwire68

end Max11DegreeRoutes
