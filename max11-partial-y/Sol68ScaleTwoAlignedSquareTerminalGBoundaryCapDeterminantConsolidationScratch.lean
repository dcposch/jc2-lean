import Sol68ScaleTwoAlignedSquareTerminalGBoundaryCapI4ThirteenScratch

/-! # Determinant consolidation above the terminal-two cap -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareTerminalGBoundaryCapDeterminants68

variable {k : Type*} [Field k] [CharZero k]

def rhoOneTerminalCapTwoECore68 (F dA : HahnSeries ℚ k) : k :=
  F.coeff 3 * dA.coeff (-1 : ℚ) + F.coeff 4 * dA.coeff (-2 : ℚ) +
    F.coeff 5 * dA.coeff (-3 : ℚ)

def rhoOneTerminalCapTwoGCore68 (F G dA : HahnSeries ℚ k) : k :=
  F.coeff 3 * G.coeff (-1 : ℚ) * dA.coeff 0 +
    (F.coeff 3 * G.coeff 0 + F.coeff 4 * G.coeff (-1 : ℚ)) *
      dA.coeff (-1 : ℚ) +
    (F.coeff 3 * G.coeff 1 + F.coeff 4 * G.coeff 0 +
      F.coeff 5 * G.coeff (-1 : ℚ)) * dA.coeff (-2 : ℚ) +
    (F.coeff 3 * G.coeff 2 + F.coeff 4 * G.coeff 1 +
      F.coeff 5 * G.coeff 0 + F.coeff 6 * G.coeff (-1 : ℚ)) *
        dA.coeff (-3 : ℚ)

/-- Three rows with the same epsilon give all three pairwise determinants. -/
theorem rhoOne_cap_three_row_determinants68
    (c b x y t z epsilon : k)
    (hX : 4 * x + 3 * epsilon * c = 0)
    (hY : 4 * y + 3 * epsilon * b = 0)
    (hT : 3 * epsilon * t + 4 * z = 0) :
    c * y - b * x = 0 ∧ c * z - t * x = 0 ∧ b * z - t * y = 0 := by
  constructor
  · linear_combination (1 / 4 : k) * c * hY - (1 / 4 : k) * b * hX
  constructor
  · linear_combination (1 / 4 : k) * c * hT - (1 / 4 : k) * t * hX
  · linear_combination (1 / 4 : k) * b * hT - (1 / 4 : k) * t * hY

/-- The third coefficient of `2 C² = B F` follows from the first three
`I₃/I₄` jets after localizing only at the already nonzero `B₁₁G₋₁` face.
The certificate is kept factored by the preceding two transports. -/
theorem rhoOneI3I4_coordinate_cap_third_transport68
    (b b' b'' b''' c c' c'' c''' f f' f'' f'''
      g g' g'' g''' epsilon : k)
    (hb : b ≠ 0) (hg : g ≠ 0)
    (hcap : b * g + c * f = 0)
    (hscalar : b * f - 2 * c ^ 2 = 0)
    (htransport1 : c * f' - b' * g - 2 * c' * f = 0)
    (htransport2 : 2 * c' ^ 2 + 4 * c * c'' -
      b'' * f - b' * f' - b * f'' = 0)
    (hI37 : 4 * (c * g' + c' * g + f * f') + 3 * epsilon * c = 0)
    (hI38 : 4 * (c * g'' + c' * g' + c'' * g + f * f'') +
      2 * f' ^ 2 + 3 * epsilon * c' = 0)
    (hI39 : 4 * (c * g''' + c' * g'' + c'' * g' + c''' * g +
      f * f''' + f' * f'') + 3 * epsilon * c'' = 0)
    (hI411 : 4 * (b * g' + b' * g) +
      4 * (c * f' + c' * f) + 3 * epsilon * b = 0)
    (hI412 : 4 * (b * g'' + b' * g' + b'' * g) +
      4 * (c * f'' + c' * f' + c'' * f) + 3 * epsilon * b' = 0)
    (hI413 : 4 * (b * g''' + b' * g'' + b'' * g' + b''' * g) +
      4 * (c * f''' + c' * f'' + c'' * f' + c''' * f) +
      3 * epsilon * b'' = 0) :
    4 * c * c''' + 4 * c' * c'' -
      b''' * f - b'' * f' - b' * f'' - b * f''' = 0 := by
  let T := 4 * c * c''' + 4 * c' * c'' -
    b''' * f - b'' * f' - b' * f'' - b * f'''
  have hprod : b * g * T = 0 := by
    linear_combination
      (4 * c' * c'' + 2 * c * c''' - b'' * f' - 2 * b' * f'' - b * f''') * hcap +
      (-2 * c' * f'' - c * f''' - b''' * g) * hscalar +
      ((4 / 3 : k) * c' ^ 2 + (8 / 3 : k) * c * c'' -
        (2 / 3 : k) * b'' * f - (2 / 3 : k) * b' * f' -
        (5 / 3 : k) * b * f'') * htransport1 +
      (-c * f' - (2 / 3 : k) * b' * g - (4 / 3 : k) * b * g' -
        b * epsilon) * htransport2 +
      (1 / 2 : k) * b'' * c * hI37 +
      (1 / 2 : k) * b' * c * hI38 +
      (1 / 2 : k) * b * c * hI39 +
      ((2 / 3 : k) * c' ^ 2 + (5 / 6 : k) * c * c'' -
        (1 / 3 : k) * b'' * f - (1 / 3 : k) * b' * f' -
        (1 / 3 : k) * b * f'') * hI411 -
      (1 / 2 : k) * c * c' * hI412 -
      (1 / 2 : k) * c ^ 2 * hI413
  have hbg : b * g ≠ 0 := mul_ne_zero hb hg
  exact (mul_eq_zero.mp hprod).resolve_left hbg

def RhoOneDoubleZeroTerminalGBoundaryCapDeterminantPacket68
    (gamma epsilon i3 sold cs source0 source1 source2 : k)
    (A B C F G dA : HahnSeries ℚ k) : Prop :=
  RhoOneDoubleZeroTerminalGBoundaryCapI4ThirteenPacket68
      gamma epsilon i3 sold cs source0 source1 source2 A B C F G dA ∧
    C.coeff 9 * rhoOneI4CapThirteenCore68 B C F G -
      B.coeff 13 * rhoOneI3CapNineCore68 C F G = 0 ∧
    C.coeff 9 * rhoOneTerminalCapTwoGCore68 F G dA -
      rhoOneTerminalCapTwoECore68 F dA * rhoOneI3CapNineCore68 C F G = 0 ∧
    B.coeff 13 * rhoOneTerminalCapTwoGCore68 F G dA -
      rhoOneTerminalCapTwoECore68 F dA *
        rhoOneI4CapThirteenCore68 B C F G = 0 ∧
    4 * C.coeff 7 * C.coeff 10 + 4 * C.coeff 8 * C.coeff 9 -
      B.coeff 14 * F.coeff 3 - B.coeff 13 * F.coeff 4 -
      B.coeff 12 * F.coeff 5 - B.coeff 11 * F.coeff 6 = 0

def RhoOneDoubleZeroTerminalGBoundaryCapDeterminantResidual68
    (root j gamma epsilon : k) (A0 : k[X])
    (h0R AR BR CR FR GR : RatFunc k)
    (A B C F G : HahnSeries ℚ k) : Prop :=
  RhoOneDoubleZeroTerminalGBoundaryCapI4ThirteenResidual68
      root j gamma epsilon A0 h0R AR BR CR FR GR A B C F G ∧
    ((B.coeff (1 : ℚ) = 0 ∧ 2 * C.coeff 0 + 3 * gamma = 0) →
      C.coeff (1 : ℚ) = 0 → C.coeff (2 : ℚ) = 0 →
      ∃ i3 sold cs : k,
        RhoOneDoubleZeroTerminalGBoundaryCapDeterminantPacket68
          gamma epsilon i3 sold cs (A0.derivative.eval root)
            (A0.derivative.derivative.eval root)
            (A0.derivative.derivative.derivative.eval root)
            A B C F G (ratFuncAtHahn46 root (Differential.deriv AR)))

end AlignedSquareTerminalGBoundaryCapDeterminants68

end Max11DegreeRoutes

namespace Max11DegreeRoutes

section AlignedSquareTerminalGBoundaryCapDeterminantBackwire68

variable {k : Type*} [Field k] [CharZero k]

theorem SquareZeroLIntegratedLocalRootData68.rhoOne_exceptional_doubleZero_refinedGZero_terminalGBoundaryCapDeterminantResidual
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
    RhoOneDoubleZeroTerminalGBoundaryCapDeterminantResidual68
        T.root j T.source.gamma T.source.epsilon (localClearedA68RhoOne g u)
        (algebraMap k[X] (RatFunc k) h0) AR BR CR FR GR A B C F G ∨
      (G.coeff (-1 : ℚ) = 0 ∧ (0 : WithTop ℚ) ≤ G.orderTop ∧
        (RhoOneDoubleZeroRefinedGZeroTerminalBGainChild68 T.source.gamma B C F ∨
         RhoOneDoubleZeroRefinedGZeroTerminalFGainChild68 T.source.gamma B C F)) := by
  dsimp only [RhoOneDoubleZeroTerminalGBoundaryCapDeterminantResidual68]
  have hprevRaw :=
    T.rhoOne_exceptional_doubleZero_refinedGZero_terminalGBoundaryCapI4ThirteenResidual
      hp hH hp6 hp5 hp4 P hB hC hF hG hbeta hdelta hzeta
  rcases hprevRaw with hprev | htail
  · left
    refine ⟨hprev, ?_⟩
    intro hcoord hc1 hc2
    obtain ⟨i3, sold, cs, hpacket⟩ := hprev.2 hcoord hc1 hc2
    have hI3packet := hpacket.1
    have hT2packet := hI3packet.1
    have hT1packet := hT2packet.1
    have hbase := hT1packet.1
    have hI39 := hI3packet.2.1
    have hI413 := hpacket.2.1
    have hI38 := hbase.1.2.1
    have hI412 := hbase.2.1
    have htransport2 := hbase.2.2.1
    have hnext := hbase.1.1.1.1
    dsimp only [RhoOneDoubleZeroTerminalGBoundaryCapNextJetPacket68] at hnext
    rcases hnext with ⟨hci3, hscalarEq, hI37, hI411, htransport1⟩
    dsimp only [RhoOneDoubleZeroTerminalGBoundaryCI3CapPacket68] at hci3
    rcases hci3 with
      ⟨hi3H, hc3, hc4, hc5, hc6, hb7, hb8, hb9, hb10,
        hS7, hB11, hcap3, hc7ne, hcap4, hb11ne, hBexact⟩
    have hscalar :
        (ratFuncAtHahn46 T.root T.source.B).coeff 11 *
            (rhoOneTangentDDefectHahn68
              (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.B)
              (ratFuncAtHahn46 T.root T.source.D)).coeff 3 -
          2 * (rhoOneCDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.C0)).coeff 7 ^ 2 = 0 := by
      linear_combination hscalarEq
    have hfne : (rhoOneTangentDDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.B)
        (ratFuncAtHahn46 T.root T.source.D)).coeff 3 ≠ 0 := by
      have hbfne : (ratFuncAtHahn46 T.root T.source.B).coeff 11 *
          (rhoOneTangentDDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.B)
            (ratFuncAtHahn46 T.root T.source.D)).coeff 3 ≠ 0 := by
        rw [hscalarEq]
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
    have hI39core : 4 * rhoOneI3CapNineCore68
          (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.C0))
          (rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.B)
            (ratFuncAtHahn46 T.root T.source.D))
          (rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.C0))
            (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.E))) +
        3 * T.source.epsilon *
          (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.C0)).coeff 9 = 0 := hI39
    have hI413core : 4 * rhoOneI4CapThirteenCore68
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
              (ratFuncAtHahn46 T.root T.source.E))) +
        3 * T.source.epsilon *
          (ratFuncAtHahn46 T.root T.source.B).coeff 13 = 0 := hI413
    have hterminal2 := hT2packet.2.2.1
    have hTcore : 3 * T.source.epsilon * rhoOneTerminalCapTwoECore68
          (rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.B)
            (ratFuncAtHahn46 T.root T.source.D))
          (ratFuncAtHahn46 T.root (Differential.deriv T.source.A)) +
        4 * rhoOneTerminalCapTwoGCore68
          (rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.B)
            (ratFuncAtHahn46 T.root T.source.D))
          (rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.C0))
            (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.E)))
          (ratFuncAtHahn46 T.root (Differential.deriv T.source.A)) = 0 := by
      dsimp only [rhoOneTerminalCapTwoECore68, rhoOneTerminalCapTwoGCore68]
      linear_combination hterminal2
    have hdets := rhoOne_cap_three_row_determinants68
      ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0)).coeff 9)
      ((ratFuncAtHahn46 T.root T.source.B).coeff 13)
      (rhoOneI3CapNineCore68
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
      (rhoOneI4CapThirteenCore68
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
            (ratFuncAtHahn46 T.root T.source.E))))
      (rhoOneTerminalCapTwoECore68
        (rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.B)
          (ratFuncAtHahn46 T.root T.source.D))
        (ratFuncAtHahn46 T.root (Differential.deriv T.source.A)))
      (rhoOneTerminalCapTwoGCore68
        (rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.B)
          (ratFuncAtHahn46 T.root T.source.D))
        (rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.C0))
          (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.E)))
        (ratFuncAtHahn46 T.root (Differential.deriv T.source.A)))
      T.source.epsilon hI39core hI413core hTcore
    have hthird := rhoOneI3I4_coordinate_cap_third_transport68
      ((ratFuncAtHahn46 T.root T.source.B).coeff 11)
      ((ratFuncAtHahn46 T.root T.source.B).coeff 12)
      ((ratFuncAtHahn46 T.root T.source.B).coeff 13)
      ((ratFuncAtHahn46 T.root T.source.B).coeff 14)
      ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0)).coeff 7)
      ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0)).coeff 8)
      ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0)).coeff 9)
      ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0)).coeff 10)
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
      T.source.epsilon hb11ne hgne hcap4 hscalar htransport1 htransport2
      hI37 hI38 (by
        dsimp only [rhoOneI3CapNineCore68] at hI39core
        exact hI39core)
      hI411 hI412 (by
        dsimp only [rhoOneI4CapThirteenCore68] at hI413core
        linear_combination hI413core)
    refine ⟨i3, sold, cs, ?_⟩
    dsimp only [RhoOneDoubleZeroTerminalGBoundaryCapDeterminantPacket68]
    exact ⟨hpacket, hdets.1, hdets.2.1, hdets.2.2, hthird⟩
  · exact Or.inr htail

end AlignedSquareTerminalGBoundaryCapDeterminantBackwire68

end Max11DegreeRoutes
