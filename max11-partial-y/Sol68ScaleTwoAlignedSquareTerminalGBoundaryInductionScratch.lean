import Sol68ScaleTwoAlignedSquareTerminalGBoundaryBGainScratch

/-! # Indexed terminal/I4 induction on the nonzero-`G[-1]` boundary -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareTerminalGBoundaryInduction68

variable {k : Type*} [Field k] [CharZero k]

local instance alignedSquareTerminalGBoundaryInductionHahnCharZero68 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-- Indexed form of the repeating terminal face. -/
theorem rhoOneMainTangentTerminalFourHahn_coeff_gBoundary_induction68
    (r : ℚ) (hr : 0 ≤ r) (gamma epsilon : k)
    (A B C F G dA dB dC dF dG : HahnSeries ℚ k)
    (hA : (↑(-2 : ℚ) : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(r + 2) : WithTop ℚ) ≤ B.orderTop)
    (hC : (0 : WithTop ℚ) ≤ C.orderTop)
    (hF : (↑r : WithTop ℚ) ≤ F.orderTop)
    (hG : (↑(-1 : ℚ) : WithTop ℚ) ≤ G.orderTop)
    (hS : (↑(1 : ℚ) : WithTop ℚ) ≤
      (2 * C + HahnSeries.C (3 * gamma)).orderTop)
    (hdA : (↑(-3 : ℚ) : WithTop ℚ) ≤ dA.orderTop)
    (hdB : (0 : WithTop ℚ) ≤ dB.orderTop)
    (hdC : (0 : WithTop ℚ) ≤ dC.orderTop)
    (hdF : (0 : WithTop ℚ) ≤ dF.orderTop)
    (hdG : (↑(-2 : ℚ) : WithTop ℚ) ≤ dG.orderTop)
    (hdAco : dA.coeff (-3 : ℚ) = (-2 : k) * A.coeff (-2 : ℚ)) :
    (rhoOneMainTangentTerminalFourHahn68 gamma epsilon
      A B C F G dA dB dC dF dG).coeff (r - 4) =
      (8 / 9 : k) * A.coeff (-2 : ℚ) * F.coeff r *
          G.coeff (-1 : ℚ) +
        (8 / 27 : k) * A.coeff (-2 : ℚ) ^ 2 *
          (B.coeff (r + 2) * G.coeff (-1 : ℚ) +
            C.coeff (1 : ℚ) * F.coeff r) := by
  let S : HahnSeries ℚ k := 2 * C + HahnSeries.C (3 * gamma)
  have hS' : (↑(1 : ℚ) : WithTop ℚ) ≤ S.orderTop := by
    simpa only [S] using hS
  have hz (s : k) (X1 X2 X3 X4 X5 : HahnSeries ℚ k)
      (n1 n2 n3 n4 n5 : ℕ) (r1 r2 r3 r4 r5 : ℚ)
      (h1 : (↑r1 : WithTop ℚ) ≤ X1.orderTop)
      (h2 : (↑r2 : WithTop ℚ) ≤ X2.orderTop)
      (h3 : (↑r3 : WithTop ℚ) ≤ X3.orderTop)
      (h4 : (↑r4 : WithTop ℚ) ≤ X4.orderTop)
      (h5 : (↑r5 : WithTop ℚ) ≤ X5.orderTop)
      (hlt : r - 4 < (n1 : ℚ) * r1 + (n2 : ℚ) * r2 +
        (n3 : ℚ) * r3 + (n4 : ℚ) * r4 + (n5 : ℚ) * r5) :
      (weightedMonomial68 s X1 X2 X3 X4 X5
        n1 n2 n3 n4 n5).coeff (r - 4) = 0 :=
    weightedMonomial68_coeff_zero_of_general_lower s X1 X2 X3 X4 X5
      n1 n2 n3 n4 n5 r1 r2 r3 r4 r5 (r - 4)
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
  have h1 := hz (-((2 / 3 : k) * gamma)) F dC A B C 1 1 0 0 0
    r 0 (-2) (r + 2) 0 hF hdC hA hB hC (by norm_num)
  have h2 := hz (-((1 / 3 : k) * epsilon)) F dA A B C 1 1 0 0 0
    r (-3) (-2) (r + 2) 0 hF hdA hA hB hC (by norm_num; linarith)
  have h3raw := lead (-(4 / 9 : k)) F G dA A B 1 1 1 0 0
    r (-1) (-3) (-2) (r + 2) hF hG hdA hA hB
  have h3 :
      (weightedMonomial68 (-(4 / 9 : k)) F G dA A B 1 1 1 0 0).coeff
        (r - 4) = (-(4 / 9 : k)) * F.coeff r * G.coeff (-1 : ℚ) *
          dA.coeff (-3 : ℚ) := by
    convert h3raw using 1 <;> ring
  have h4 := hz (-(4 / 9 : k)) F F dB A B 1 1 1 0 0
    r r 0 (-2) (r + 2) hF hF hdB hA hB (by norm_num; linarith)
  have h5 := hz (-(4 / 9 : k)) C F dC A B 1 1 1 0 0
    0 r 0 (-2) (r + 2) hC hF hdC hA hB (by norm_num)
  have h6 := hz ((2 / 3 : k) * gamma) B dG A C F 1 1 0 0 0
    (r + 2) (-2) (-2) 0 r hB hdG hA hC hF (by norm_num)
  have h7 := hz (-(4 / 9 : k)) B F dF A C 1 1 1 0 0
    (r + 2) r 0 (-2) 0 hB hF hdF hA hC (by norm_num; linarith)
  have h8 := hz (4 / 9 : k) B C dG A F 1 1 1 0 0
    (r + 2) 0 (-2) (-2) r hB hC hdG hA hF (by norm_num)
  have h9 := hz ((2 / 9 : k) * gamma) B C dA A F 1 1 1 0 0
    (r + 2) 0 (-3) (-2) r hB hC hdA hA hF (by norm_num; linarith)
  have h10 := hz (4 / 27 : k) B C C dA A 1 1 1 1 0
    (r + 2) 0 0 (-3) (-2) hB hC hC hdA hA (by norm_num; linarith)
  have hSraw := lead (-(2 / 27 : k)) A F dA S B 1 1 1 1 0
    (-2) r (-3) 1 (r + 2) hA hF hdA hS' hB
  have hSterm :
      (weightedMonomial68 (-(2 / 27 : k)) A F dA S B 1 1 1 1 0).coeff
        (r - 4) = (-(2 / 27 : k)) * A.coeff (-2 : ℚ) * F.coeff r *
          dA.coeff (-3 : ℚ) * S.coeff (1 : ℚ) := by
    convert hSraw using 1 <;> ring
  have h13 := hz (-((1 / 9 : k) * epsilon)) A B dA C F 1 1 1 0 0
    (-2) (r + 2) (-3) 0 r hA hB hdA hC hF (by norm_num; linarith)
  have h14raw := lead (-(4 / 27 : k)) A B G dA C 1 1 1 1 0
    (-2) (r + 2) (-1) (-3) 0 hA hB hG hdA hC
  have h14 :
      (weightedMonomial68 (-(4 / 27 : k)) A B G dA C 1 1 1 1 0).coeff
        (r - 4) = (-(4 / 27 : k)) * A.coeff (-2 : ℚ) *
          B.coeff (r + 2) * G.coeff (-1 : ℚ) * dA.coeff (-3 : ℚ) := by
    convert h14raw using 1 <;> ring
  have h15 := hz (-(4 / 27 : k)) A B F dB C 1 1 1 1 0
    (-2) (r + 2) r 0 0 hA hB hF hdB hC (by norm_num; linarith)
  have h16 := hz (-(4 / 27 : k)) A B B dF C 1 1 1 1 0
    (-2) (r + 2) (r + 2) 0 0 hA hB hB hdF hC (by norm_num; linarith)
  have hSco : S.coeff (1 : ℚ) = 2 * C.coeff (1 : ℚ) := by
    dsimp only [S]
    rw [HahnSeries.coeff_add]
    have htwo : (2 * C).coeff (1 : ℚ) = 2 * C.coeff (1 : ℚ) := by
      rw [two_mul, HahnSeries.coeff_add]
      ring
    rw [htwo]
    simp [HahnSeries.C_apply]
  rw [hrewrite]
  simp only [HahnSeries.coeff_add]
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hSterm, h13,
    h14, h15, h16, hdAco, hSco]
  ring

/-- Indexed terminal deletion while the target exponent remains below the
Keller pole. -/
theorem rhoOneMainTangentTerminal_gBoundary_induction_fZero68
    (r : ℚ) (hr : 0 ≤ r) (hrt : r - 4 < -1)
    (gamma epsilon : k)
    (A B C F G dA dB dC dF dG terminal : HahnSeries ℚ k)
    (hA : (↑(-2 : ℚ) : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(r + 2) : WithTop ℚ) ≤ B.orderTop)
    (hC : (0 : WithTop ℚ) ≤ C.orderTop)
    (hF : (↑r : WithTop ℚ) ≤ F.orderTop)
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
    (hi4next : B.coeff (r + 2) * G.coeff (-1 : ℚ) +
      C.coeff (1 : ℚ) * F.coeff r = 0)
    (hrow : rhoOneMainTangentTerminal68 (HahnSeries.C gamma)
      (HahnSeries.C epsilon) A B C F G dA dB dC dF dG = terminal)
    (hterminal : terminal.orderTop = (↑(-1 : ℚ) : WithTop ℚ)) :
    F.coeff r = 0 := by
  have hcoeff := rhoOneMainTangentTerminalFourHahn_coeff_gBoundary_induction68
    r hr gamma epsilon A B C F G dA dB dC dF dG hA hB hC hF hG hS
      hdA hdB hdC hdF hdG hdAco
  have hterminalr : terminal.coeff (r - 4) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop (by
      rw [hterminal]
      exact WithTop.coe_lt_coe.mpr hrt)
  have hleft :
      (rhoOneMainTangentTerminalFourHahn68 gamma epsilon
        A B C F G dA dB dC dF dG).coeff (r - 4) = 0 := by
    rw [← rhoOneMainTangentTerminalFourHahn_eq68, hrow]
    exact hterminalr
  rw [hcoeff, hi4next] at hleft
  norm_num at hleft
  rcases hleft with (ha | hf) | hg
  · exact (hAne ha).elim
  · exact hf
  · exact (hGne hg).elim

/-- Indexed next coefficient of the global zero-`I₄` factor. -/
theorem rhoOneI4ZeroFactored_gBoundary_induction68
    (r : ℚ) (hr : 0 ≤ r) (gamma epsilon : k)
    (B C F G : HahnSeries ℚ k)
    (hB : (↑(r + 3) : WithTop ℚ) ≤ B.orderTop)
    (hF : (↑(r + 1) : WithTop ℚ) ≤ F.orderTop)
    (hG : (↑(-1 : ℚ) : WithTop ℚ) ≤ G.orderTop)
    (hS : (↑(1 : ℚ) : WithTop ℚ) ≤
      (2 * C + HahnSeries.C (3 * gamma)).orderTop)
    (hfactor : rhoOneI4ZeroFactored68
      (HahnSeries.C gamma) (HahnSeries.C epsilon) B C F G = 0) :
    B.coeff (r + 3) * G.coeff (-1 : ℚ) +
      C.coeff (1 : ℚ) * F.coeff (r + 1) = 0 := by
  let S : HahnSeries ℚ k := 2 * C + HahnSeries.C (3 * gamma)
  have hS' : (↑(1 : ℚ) : WithTop ℚ) ≤ S.orderTop := by
    simpa only [S] using hS
  have hz (s : k) (X1 X2 X3 X4 X5 : HahnSeries ℚ k)
      (n1 n2 n3 n4 n5 : ℕ) (r1 r2 r3 r4 r5 : ℚ)
      (h1 : (↑r1 : WithTop ℚ) ≤ X1.orderTop)
      (h2 : (↑r2 : WithTop ℚ) ≤ X2.orderTop)
      (h3 : (↑r3 : WithTop ℚ) ≤ X3.orderTop)
      (h4 : (↑r4 : WithTop ℚ) ≤ X4.orderTop)
      (h5 : (↑r5 : WithTop ℚ) ≤ X5.orderTop)
      (hlt : r + 2 < (n1 : ℚ) * r1 + (n2 : ℚ) * r2 +
        (n3 : ℚ) * r3 + (n4 : ℚ) * r4 + (n5 : ℚ) * r5) :
      (weightedMonomial68 s X1 X2 X3 X4 X5
        n1 n2 n3 n4 n5).coeff (r + 2) = 0 :=
    weightedMonomial68_coeff_zero_of_general_lower s X1 X2 X3 X4 X5
      n1 n2 n3 n4 n5 r1 r2 r3 r4 r5 (r + 2)
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
  have hB3 := hz (-8 / 27) B B B B B 3 0 0 0 0
    (r + 3) (r + 3) (r + 3) (r + 3) (r + 3)
      hB hB hB hB hB (by norm_num; linarith)
  have hBGraw := lead (8 / 3) B G B F S 1 1 0 0 0
    (r + 3) (-1) (r + 3) (r + 1) 1 hB hG hB hF hS'
  have hBG :
      (weightedMonomial68 (8 / 3 : k) B G B F S 1 1 0 0 0).coeff
        (r + 2) = (8 / 3 : k) * B.coeff (r + 3) * G.coeff (-1 : ℚ) := by
    convert hBGraw using 1 <;> ring
  have hSFraw := lead (4 / 3) S F B S G 1 1 0 0 0
    1 (r + 1) (r + 3) 1 (-1) hS' hF hB hS' hG
  have hSF :
      (weightedMonomial68 (4 / 3 : k) S F B S G 1 1 0 0 0).coeff
        (r + 2) = (4 / 3 : k) * S.coeff (1 : ℚ) * F.coeff (r + 1) := by
    convert hSFraw using 1 <;> ring
  have heB := hz (2 * epsilon) B B B B B 1 0 0 0 0
    (r + 3) (r + 3) (r + 3) (r + 3) (r + 3)
      hB hB hB hB hB (by norm_num)
  have hfactor' :
      weightedMonomial68 (-8 / 27 : k) B B B B B 3 0 0 0 0 +
        weightedMonomial68 (8 / 3 : k) B G B F S 1 1 0 0 0 +
        weightedMonomial68 (4 / 3 : k) S F B S G 1 1 0 0 0 +
        weightedMonomial68 (2 * epsilon) B B B B B 1 0 0 0 0 = 0 := by
    simpa only [rhoOneI4ZeroFactored68, S, weightedMonomial68,
      pow_zero, pow_one, mul_one, map_add, map_mul, map_div₀, map_neg,
      map_ofNat, map_one] using hfactor
  have hc := congrArg (fun X : HahnSeries ℚ k => X.coeff (r + 2)) hfactor'
  simp only [HahnSeries.coeff_add, HahnSeries.coeff_zero] at hc
  rw [hB3, hBG, hSF, heB] at hc
  have hSco : S.coeff (1 : ℚ) = 2 * C.coeff (1 : ℚ) := by
    dsimp only [S]
    rw [HahnSeries.coeff_add]
    have htwo : (2 * C).coeff (1 : ℚ) = 2 * C.coeff (1 : ℚ) := by
      rw [two_mul, HahnSeries.coeff_add]
      ring
    rw [htwo]
    simp [HahnSeries.C_apply]
  rw [hSco] at hc
  linear_combination (3 / 8 : k) * hc

/-- Source transport of the indexed terminal deletion at the next boundary
stage (`r = 1`). -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_exceptional_doubleZero_gBoundary_terminal_fOne
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (P : RhoOneZeroLCubicNextSourcePacket68 T g u)
    (hB : (↑(3 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root T.source.B).orderTop)
    (hC : (0 : WithTop ℚ) ≤
      (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0)).orderTop)
    (hF : (↑(1 : ℚ) : WithTop ℚ) ≤
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
    (hi4next :
      (ratFuncAtHahn46 T.root T.source.B).coeff (3 : ℚ) *
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
            (ratFuncAtHahn46 T.root T.source.D)).coeff (1 : ℚ) = 0)
    (hbeta : T.source.beta = 0) (hdelta : T.source.delta = 0)
    (hzeta : T.source.zeta = 0) :
    (rhoOneTangentDDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.B)
      (ratFuncAtHahn46 T.root T.source.D)).coeff (1 : ℚ) = 0 := by
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
  have hBR : (↑(3 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root BR).orderTop := by simpa only [BR] using hB
  have hCR : (0 : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root CR).orderTop := by rw [hCRmap]; exact hC
  have hFR : (↑(1 : ℚ) : WithTop ℚ) ≤
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
  have hf1 := rhoOneMainTangentTerminal_gBoundary_induction_fZero68
    1 (by norm_num) (by norm_num) T.source.gamma T.source.epsilon
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
      hAH (by convert hBR using 1 <;> norm_num) hCR hFR hGR
      (by rw [hCRmap]; exact hS)
      hdA hdB hdC hdF hdG hdAco hAne (by rw [hGRmap]; exact hGne)
      (by
        rw [hCRmap, hFRmap, hGRmap]
        norm_num
        simpa only [BR] using hi4next)
      hsparseH' T.terminal_order
  rw [hFRmap] at hf1
  exact hf1

/-- Residual after one full repeat of the boundary terminal/`I₄` step. -/
def RhoOneDoubleZeroTerminalGBoundaryInductionResidual68
    (gamma epsilon : k) (BR CR FR GR : RatFunc k)
    (A B C F G : HahnSeries ℚ k) : Prop :=
  rhoOneI4ZeroFactored68 (RatFunc.C gamma) (RatFunc.C epsilon)
      BR CR FR GR = 0 ∧
    (((((((B.coeff (1 : ℚ) = 0 ∧
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
        C.coeff (1 : ℚ) * F.coeff (2 : ℚ) = 0) ∨
      (B.coeff (1 : ℚ) ≠ 0 ∧
        2 * C.coeff (0 : ℚ) + 3 * gamma ≠ 0 ∧
        ∃ r : k, r ≠ 0 ∧ r ^ 2 = -3 * A.coeff (-2 : ℚ) ∧
          (3 * (2 * C.coeff (0 : ℚ) + 3 * gamma) =
              2 * r * B.coeff (1 : ℚ) ∨
           3 * (2 * C.coeff (0 : ℚ) + 3 * gamma) =
              -(2 * r * B.coeff (1 : ℚ)))))

/-- Source-facing repeat: `F[1]=B[3]=0`, orders rise to `F≥2`, `B≥4`,
and the next exact `I₄` face is exposed. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_exceptional_doubleZero_refinedGZero_terminalGBoundaryInductionResidual
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
    RhoOneDoubleZeroTerminalGBoundaryInductionResidual68
        T.source.gamma T.source.epsilon BR CR FR GR A B C F G ∨
      (G.coeff (-1 : ℚ) = 0 ∧ (0 : WithTop ℚ) ≤ G.orderTop ∧
        (RhoOneDoubleZeroRefinedGZeroTerminalBGainChild68
            T.source.gamma B C F ∨
         RhoOneDoubleZeroRefinedGZeroTerminalFGainChild68
            T.source.gamma B C F)) := by
  dsimp only [RhoOneDoubleZeroTerminalGBoundaryInductionResidual68]
  have hnext := T.rhoOne_exceptional_doubleZero_refined_gZero
    P hB hC hF hG hbeta hdelta hzeta
  dsimp only at hnext
  rcases hnext with ⟨_, _, _, _, _, _, hsplit⟩
  rcases hsplit with hGne | ⟨hGzero, hG0, htail⟩
  · have hprev :=
      T.rhoOne_exceptional_doubleZero_refinedGZero_terminalGBoundaryBGainResidual
        hp hH hp6 hp5 hp4 P hB hC hF hG hbeta hdelta hzeta
    dsimp only [RhoOneDoubleZeroTerminalGBoundaryBGainResidual68] at hprev
    rcases hprev with ⟨hfact, hshape⟩ | hbad
    · left
      refine ⟨hfact, ?_⟩
      rcases hshape with hboundary | hrays
      · left
        rcases hboundary with ⟨hstage, hb2, hB3, hi4one⟩
        rcases hstage with ⟨hstage0, hf0, hF1⟩
        rcases hstage0 with ⟨hcoord, hB2, hS1, hi4zero⟩
        have hf1 := T.rhoOne_exceptional_doubleZero_gBoundary_terminal_fOne
          hp hH hp6 hp5 hp4 P hB3 hC hF1 hG hS1 hGne hi4one
            hbeta hdelta hzeta
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
        have hFR1 : (↑(1 : ℚ) : WithTop ℚ) ≤
            (ratFuncAtHahn46 T.root FR).orderTop := by
          rw [hFRmap]
          exact hF1
        have hf1raw :
            (ratFuncAtHahn46 T.root FR).coeff ((1 : ℤ) : ℚ) = 0 := by
          norm_num
          rw [hFRmap]
          exact hf1
        have hF2raw := ratFuncAtHahn46_orderTop_ge_int_succ_of_coeff_zero
          T.root FR 1 hFR1 hf1raw
        norm_num at hF2raw
        have hF2 : (↑(2 : ℚ) : WithTop ℚ) ≤
            (rhoOneTangentDDefectHahn68
              (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.B)
              (ratFuncAtHahn46 T.root T.source.D)).orderTop := by
          rw [← hFRmap]
          exact hF2raw
        have hb3 : (ratFuncAtHahn46 T.root T.source.B).coeff (3 : ℚ) = 0 := by
          rw [hf1] at hi4one
          norm_num at hi4one
          rcases hi4one with hb | hg
          · exact hb
          · exact (hGne hg).elim
        have hB4 := ratFuncAtHahn46_orderTop_ge_int_succ_of_coeff_zero
          T.root T.source.B 3 hB3 (by norm_num; exact hb3)
        norm_num at hB4
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
        have hi4two := rhoOneI4ZeroFactored_gBoundary_induction68
          1 (by norm_num) T.source.gamma T.source.epsilon
          (ratFuncAtHahn46 T.root BR) (ratFuncAtHahn46 T.root CR)
          (ratFuncAtHahn46 T.root FR) (ratFuncAtHahn46 T.root GR)
          (by dsimp only [BR]; convert hB4 using 1 <;> norm_num)
          (by rw [hFRmap]; convert hF2 using 1 <;> norm_num)
          (by rw [hGRmap]; exact hG)
          (by rw [hCRmap]; exact hS1) hfactH'
        rw [hCRmap, hFRmap, hGRmap] at hi4two
        norm_num at hi4two
        exact ⟨⟨⟨⟨⟨hcoord, hB2, hS1, hi4zero⟩, hf0, hF1⟩,
          hb2, hB3, hi4one⟩, hf1, hF2⟩, hb3,
          (by convert hB4 using 1 <;> norm_num),
          by simpa only [BR] using hi4two⟩
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

end AlignedSquareTerminalGBoundaryInduction68

end Max11DegreeRoutes
