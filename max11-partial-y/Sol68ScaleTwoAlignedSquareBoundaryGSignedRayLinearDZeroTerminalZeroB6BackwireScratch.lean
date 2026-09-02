import Sol68ScaleTwoAlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6IsolationScratch

/-! # Source backwire for the terminal-zero `B[6]` convolution -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6Backwire68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

omit [IsAlgClosed k] in
theorem ratFunc_terminalZero_product_laurent_eq_hahn68
    (root gamma epsilon : k)
    (A B C F G dA dB dC dF dG : RatFunc k) :
    rhoOne_boundaryG_terminalZeroProductLaurentRow68 gamma epsilon
      (ratFuncAtLaurent46 root A) (ratFuncAtLaurent46 root B)
      (ratFuncAtLaurent46 root C) (ratFuncAtLaurent46 root F)
      (ratFuncAtLaurent46 root G) (ratFuncAtLaurent46 root dA)
      (ratFuncAtLaurent46 root dB) (ratFuncAtLaurent46 root dC)
      (ratFuncAtLaurent46 root dF) (ratFuncAtLaurent46 root dG) =
    rhoOne_boundaryG_terminalZeroProductRow68 gamma epsilon
      (ratFuncAtHahn46 root A) (ratFuncAtHahn46 root B)
      (ratFuncAtHahn46 root C) (ratFuncAtHahn46 root F)
      (ratFuncAtHahn46 root G) (ratFuncAtHahn46 root dA)
      (ratFuncAtHahn46 root dB) (ratFuncAtHahn46 root dC)
      (ratFuncAtHahn46 root dF) (ratFuncAtHahn46 root dG) := by
  have h2 (X Y : RatFunc k) :
      (ratFuncAtLaurent46 root X * ratFuncAtLaurent46 root Y).coeff (0 : ℤ) =
        (ratFuncAtHahn46 root X * ratFuncAtHahn46 root Y).coeff (0 : ℚ) := by
    calc
      _ = (ratFuncAtLaurent46 root (X * Y)).coeff 0 := by rw [map_mul]
      _ = (ratFuncAtHahn46 root (X * Y)).coeff 0 :=
        (ratFuncAtHahn46_coeff_int68 root (X * Y) 0).symm
      _ = _ := by rw [map_mul]
  have h3 (X Y Z : RatFunc k) :
      (ratFuncAtLaurent46 root X * ratFuncAtLaurent46 root Y *
          ratFuncAtLaurent46 root Z).coeff (0 : ℤ) =
        (ratFuncAtHahn46 root X * ratFuncAtHahn46 root Y *
          ratFuncAtHahn46 root Z).coeff (0 : ℚ) := by
    have ht := (ratFuncAtHahn46_coeff_int68 root (X * Y * Z) 0).symm
    simp only [map_mul] at ht
    norm_num at ht ⊢
    exact ht
  have h4 (X Y Z W : RatFunc k) :
      (ratFuncAtLaurent46 root X * ratFuncAtLaurent46 root Y *
          ratFuncAtLaurent46 root Z * ratFuncAtLaurent46 root W).coeff (0 : ℤ) =
        (ratFuncAtHahn46 root X * ratFuncAtHahn46 root Y *
          ratFuncAtHahn46 root Z * ratFuncAtHahn46 root W).coeff (0 : ℚ) := by
    have ht := (ratFuncAtHahn46_coeff_int68 root (X * Y * Z * W) 0).symm
    simp only [map_mul] at ht
    norm_num at ht ⊢
    exact ht
  dsimp only [rhoOne_boundaryG_terminalZeroProductLaurentRow68,
    rhoOne_boundaryG_terminalZeroProductRow68]
  rw [h2 F dC, h2 F dA, h3 F G dA, h3 F F dB, h3 C F dC,
    h2 B dG, h3 B F dF, h3 B C dG, h3 B C dA, h4 B C C dA,
    h3 A F dA, h4 A F dA C, h3 A B dA, h4 A B G dA,
    h4 A B F dB, h4 A B B dF]

def rhoOne_boundaryG_terminalZeroB6SourceRow68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : k :=
  let A : RatFunc k := T.source.A
  let B : RatFunc k := T.source.B
  let C : RatFunc k := T.source.C0 - RatFunc.C (1 / 3 : k) * A ^ 2
  let F : RatFunc k := T.source.D - RatFunc.C (1 / 3 : k) * A * B
  let E : RatFunc k := T.source.E - RatFunc.C (1 / 27 : k) * A ^ 3
  let G : RatFunc k := E - RatFunc.C (1 / 3 : k) * A * C
  rhoOne_boundaryG_terminalZeroAtB6_68 T.source.gamma T.source.epsilon
    ((ratFuncAtLaurent46 T.root B).coeff 6)
    (ratFuncAtLaurent46 T.root A) (ratFuncAtLaurent46 T.root B)
    (ratFuncAtLaurent46 T.root C) (ratFuncAtLaurent46 T.root F)
    (ratFuncAtLaurent46 T.root G)
    (ratFuncAtLaurent46 T.root (Differential.deriv A))
    (ratFuncAtLaurent46 T.root (Differential.deriv B))
    (ratFuncAtLaurent46 T.root (Differential.deriv C))
    (ratFuncAtLaurent46 T.root (Differential.deriv F))
    (ratFuncAtLaurent46 T.root (Differential.deriv G))

theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_terminal_zero_B6_source68
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (Q : RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u)
    (hexpanded : rhoOne_boundaryG_terminalZeroExpandedSourceRow68 T = 0) :
    rhoOne_boundaryG_terminalZeroB6SourceRow68 T = 0 := by
  have Qc := Q
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68] at Qc
  rcases Qc with ⟨Rm, hquadratic⟩
  have Rmc := Rm
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryMinor68] at Rmc
  rcases Rmc with ⟨Rtf, hminor⟩
  have Rtfc := Rtf
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryTerminalFollowing68] at Rtfc
  rcases Rtfc with ⟨Rt, i3two, i4three, hi3twoSrc, hi4threeSrc, hdet⟩
  have Rtc := Rt
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryTerminalNext68] at Rtc
  rcases Rtc with ⟨Rterm, i4two, hi4twoSrc, hi4two, hprev⟩
  have Rtermc := Rterm
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryTerminal68] at Rtermc
  rcases Rtermc with ⟨Rfol, i3one, hi3oneSrc, hi3one, hprevOne⟩
  have Rfolc := Rfol
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryFollowing68] at Rfolc
  rcases Rfolc with ⟨Rn, i4one, hi4oneSrc, hi4one, hcross⟩
  have Rnc := Rn
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryNext68] at Rnc
  rcases Rnc with ⟨Rbase, hi3zero, htermFour⟩
  have Rbasec := Rbase
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryResidual68] at Rbasec
  rcases Rbasec with ⟨P, hbeta, hdelta, hzeta, hB, hC, hF, hG,
    hfneg, hgneg, hb1, hS0, hscalar, hi4base⟩
  obtain ⟨c, t, v, z, hc, hsingle, ht, hv, hzdef, hz, hvcore, htcore⟩ := P.1
  let A : RatFunc k := T.source.A
  let B : RatFunc k := T.source.B
  let C : RatFunc k := T.source.C0 - RatFunc.C (1 / 3 : k) * A ^ 2
  let F : RatFunc k := T.source.D - RatFunc.C (1 / 3 : k) * A * B
  let E : RatFunc k := T.source.E - RatFunc.C (1 / 27 : k) * A ^ 3
  let G : RatFunc k := E - RatFunc.C (1 / 3 : k) * A * C
  let A0 := localClearedA68RhoOne g u
  have hAclear := (T.source.clearedCoordinatesRhoOne hp T.scale_ne_zero
    hH hp6 hp5 hp4).1
  change algebraMap k[X] (RatFunc k) A0 =
    (algebraMap k[X] (RatFunc k) h0) ^ 2 * A at hAclear
  have hCmap : ratFuncAtHahn46 T.root C =
      rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0) := by
    dsimp only [C, A, rhoOneCDefectHahn68]
    simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
  have hFmap : ratFuncAtHahn46 T.root F =
      rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.B)
        (ratFuncAtHahn46 T.root T.source.D) := by
    dsimp only [F, A, B, rhoOneTangentDDefectHahn68]
    simp only [map_sub, map_mul, ratFuncAtHahn46_C]
  have hEmap : ratFuncAtHahn46 T.root E =
      rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.E) := by
    dsimp only [E, A, rhoOneEDefectHahn68]
    simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
  have hGmap : ratFuncAtHahn46 T.root G =
      rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0))
        (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.E)) := by
    dsimp only [G, rhoOneTangentEDefectHahn68]
    rw [map_sub, map_mul, hEmap, hCmap, map_mul, ratFuncAtHahn46_C]
  have hAH : (↑(-2 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root A).orderTop := by simpa only [A] using P.2.1.1
  have hBH : (↑(2 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root B).orderTop := by simpa only [B] using hB
  have hCH : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root C).orderTop := by
    rw [hCmap]; exact hC
  have hFH : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root F).orderTop := by
    rw [hFmap]; exact hF
  have hGH : (↑(-2 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root G).orderTop := by rw [hGmap]; exact hG
  have hdAH : (↑(-3 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root (Differential.deriv A)).orderTop := by
    dsimp only [A]
    convert localHahn_deriv_orderTop_ge_of_cleared T.root h0 A0
      T.source.A 2 T.scale_order hAclear using 1 <;> norm_num
  have hdBH : (0 : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root (Differential.deriv B)).orderTop :=
    ratFuncAtHahn46_deriv_orderTop_nonneg_of_nonneg T.root B
      (le_trans (WithTop.coe_le_coe.mpr (by norm_num)) hBH)
  have hdCH : (0 : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root (Differential.deriv C)).orderTop :=
    ratFuncAtHahn46_deriv_orderTop_nonneg_of_nonneg T.root C hCH
  have hdFH : (0 : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root (Differential.deriv F)).orderTop :=
    ratFuncAtHahn46_deriv_orderTop_nonneg_of_nonneg T.root F hFH
  have hdGH : (↑(-3 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root (Differential.deriv G)).orderTop :=
    ratFuncAtHahn68_deriv_orderTop_ge_negThree_of_ge_negTwo
      T.root h0 G T.scale_order hGH
  have hAL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root A (-2) hAH
  have hBL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root B 2 hBH
  have hCL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root C 0 hCH
  have hFL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root F 0 hFH
  have hGL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root G (-2) hGH
  have hdAL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root
    (Differential.deriv A) (-3) hdAH
  have hdBL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root
    (Differential.deriv B) 0 hdBH
  have hdCL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root
    (Differential.deriv C) 0 hdCH
  have hdFL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root
    (Differential.deriv F) 0 hdFH
  have hdGL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root
    (Differential.deriv G) (-3) hdGH
  have htransport := ratFunc_terminalZero_product_laurent_eq_hahn68
    T.root T.source.gamma T.source.epsilon A B C F G
      (Differential.deriv A) (Differential.deriv B) (Differential.deriv C)
      (Differential.deriv F) (Differential.deriv G)
  have hconv := rhoOne_boundaryG_terminal_zero_B6_convolution68
    T.source.gamma T.source.epsilon
    (ratFuncAtLaurent46 T.root A) (ratFuncAtLaurent46 T.root B)
    (ratFuncAtLaurent46 T.root C) (ratFuncAtLaurent46 T.root F)
    (ratFuncAtLaurent46 T.root G)
    (ratFuncAtLaurent46 T.root (Differential.deriv A))
    (ratFuncAtLaurent46 T.root (Differential.deriv B))
    (ratFuncAtLaurent46 T.root (Differential.deriv C))
    (ratFuncAtLaurent46 T.root (Differential.deriv F))
    (ratFuncAtLaurent46 T.root (Differential.deriv G))
    hAL hBL hCL hFL hGL hdAL hdBL hdCL hdFL hdGL
  dsimp only [rhoOne_boundaryG_terminalZeroExpandedSourceRow68] at hexpanded
  dsimp only [rhoOne_boundaryG_terminalZeroB6SourceRow68]
  rw [htransport] at hconv
  linear_combination hexpanded - hconv

end AlignedSquareBoundaryGSignedRayLinearDZeroTerminalZeroB6Backwire68

end Max11DegreeRoutes
