import Sol68ScaleTwoAlignedNonsquareAfterLowerOnePhiDivisorRefinedIIIFifthScratch

/-! # The next loaded row on refined component III -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

section LoadedNextAlgebra68

variable {k : Type*} [Field k] [CharZero k]

/-- The exact second jet of the cleared `E` derivative on the refined box. -/
theorem terminalEDerivativeNumerator_second_eval_root_shape_68
    (H A B phi w E : k[X]) (gamma epsilon a : k)
    (ha : H.eval a = 0) (hw : w.eval a = 0) (hphi : phi.eval a = 0)
    (hE : E = C (1 / 27 : k) * A ^ 3 +
      H ^ 2 * (C (3 / 8 : k) * phi + C (3 / 2 : k) * A * w -
        C (1 / 2 * gamma : k) * A) - C (3 / 4 * epsilon : k) * H ^ 3 +
      C (1 / 9 : k) * H ^ 4 * B ^ 2) :
    (terminalEDerivativeNumerator68 H E).derivative.derivative.eval a =
      -(2 / 9 : k) * H.derivative.eval a * A.eval a *
          A.derivative.eval a ^ 2 -
        (1 / 9 : k) * H.derivative.eval a * A.eval a ^ 2 *
          A.derivative.derivative.eval a -
        (5 / 9 : k) * H.derivative.derivative.eval a * A.eval a ^ 2 *
          A.derivative.eval a -
        (1 / 9 : k) * H.derivative.derivative.derivative.eval a *
          A.eval a ^ 3 +
        gamma * A.eval a * H.derivative.eval a ^ 3 := by
  rw [hE]
  simp only [terminalEDerivativeNumerator68, derivative_add, derivative_sub,
    derivative_neg, derivative_mul, derivative_pow, derivative_C,
    derivative_ofNat, C_ofNat_poly, eval_add, eval_sub, eval_neg, eval_mul,
    eval_pow, eval_C, eval_ofNat, eval_zero, ha, hw, hphi, zero_mul,
    mul_zero, zero_add, add_zero, zero_pow]
  ring_nf

def terminalFourthTripleMiddleDoubleZeroAt68
    (b w e : k[X]) (a : k) : k :=
  6 * b.derivative.derivative.eval a * w.derivative.derivative.eval a *
      e.eval a +
    4 * b.derivative.eval a * w.derivative.derivative.derivative.eval a *
      e.eval a +
    b.eval a * w.derivative.derivative.derivative.derivative.eval a *
      e.eval a +
    12 * b.derivative.eval a * w.derivative.derivative.eval a *
      e.derivative.eval a +
    4 * b.eval a * w.derivative.derivative.derivative.eval a *
      e.derivative.eval a +
    6 * b.eval a * w.derivative.derivative.eval a *
      e.derivative.derivative.eval a

def terminalFourthPairLeftZeroAt68 (d K : k[X]) (a : k) : k :=
  d.derivative.derivative.derivative.derivative.eval a * K.eval a +
    4 * d.derivative.derivative.derivative.eval a * K.derivative.eval a +
    6 * d.derivative.derivative.eval a * K.derivative.derivative.eval a +
    4 * d.derivative.eval a * K.derivative.derivative.derivative.eval a

theorem eval_fourth_triple_middle_double_zero_68
    (b w e : k[X]) (a : k) (hw : w.eval a = 0)
    (hw1 : w.derivative.eval a = 0) :
    (b * w * e).derivative.derivative.derivative.derivative.eval a =
      terminalFourthTripleMiddleDoubleZeroAt68 b w e a := by
  simp only [terminalFourthTripleMiddleDoubleZeroAt68, derivative_add,
    derivative_mul, eval_add, eval_mul, eval_ofNat, hw, hw1, zero_mul,
    mul_zero, zero_add, add_zero]
  ring

theorem eval_fourth_pair_left_zero_68
    (d K : k[X]) (a : k) (hd : d.eval a = 0) :
    (d * K).derivative.derivative.derivative.derivative.eval a =
      terminalFourthPairLeftZeroAt68 d K a := by
  simp only [terminalFourthPairLeftZeroAt68, derivative_add, derivative_mul,
    eval_add, eval_mul, eval_ofNat, hd, zero_mul, add_zero]
  ring

theorem eval_fourth_C_mul_cube_at_root_68
    (H : k[X]) (j a : k) (ha : H.eval a = 0) :
    (C j * H ^ 3).derivative.derivative.derivative.derivative.eval a =
      36 * j * H.derivative.eval a ^ 2 *
        H.derivative.derivative.eval a := by
  simp [derivative_mul, derivative_pow, ha]
  ring

/-- The first loaded coefficient after the previously used cubic load. -/
theorem terminalLoadedFourth_of_row_68
    (H b w e d K : k[X]) (j a : k)
    (ha : H.eval a = 0) (hw : w.eval a = 0)
    (hw1 : w.derivative.eval a = 0) (hd : d.eval a = 0)
    (hrow : b * w * e - d * K = C j * H ^ 3) :
    terminalFourthTripleMiddleDoubleZeroAt68 b w e a -
        terminalFourthPairLeftZeroAt68 d K a =
      36 * j * H.derivative.eval a ^ 2 *
        H.derivative.derivative.eval a := by
  have h4 := congrArg (fun P : k[X] =>
    P.derivative.derivative.derivative.derivative.eval a) hrow
  simp only [derivative_sub, eval_sub,
    eval_fourth_triple_middle_double_zero_68 b w e a hw hw1,
    eval_fourth_pair_left_zero_68 d K a hd,
    eval_fourth_C_mul_cube_at_root_68 H j a ha] at h4
  exact h4

/-- Eliminate the two transient jets `w'''` and `d'` from I4 orders three
and four and the fifth lower-zero face. -/
theorem terminalRefinedIII_I4_fifth_elimination_68
    (A b b' h h' W P Q x y d'' L : k)
    (h3 : b * P + 18 * W * y = 0)
    (h5 : -6 * A ^ 2 * x + L + 64 * b * h ^ 2 * y = 0)
    (h4 : 4 * b' * P + b * Q + 24 * x * y + 36 * W * d'' = 0) :
    let M := 4 * b' * P + b * Q + 36 * W * d''
    18 * b * P * L * W - 81 * A ^ 2 * W ^ 2 * M -
        64 * b ^ 3 * h ^ 2 * P ^ 2 = 0 := by
  dsimp only
  have hx : 18 * W * (4 * b' * P + b * Q + 36 * W * d'') -
      24 * b * P * x = 0 := by
    linear_combination 18 * W * h4 - 24 * x * h3
  have hy : 4 * b * P * L + 256 * b ^ 2 * h ^ 2 * P * y -
      18 * A ^ 2 * W * (4 * b' * P + b * Q + 36 * W * d'') = 0 := by
    linear_combination 4 * b * P * h5 - A ^ 2 * hx
  have hz : 72 * b * P * L * W -
      324 * A ^ 2 * W ^ 2 * (4 * b' * P + b * Q + 36 * W * d'') -
      256 * b ^ 3 * h ^ 2 * P ^ 2 = 0 := by
    linear_combination 18 * W * hy - 256 * b ^ 2 * h ^ 2 * P * h3
  linear_combination (1 / 4 : k) * hz

/-- The old loaded scalar also becomes independent of `w'''` and `d'` after
the same elimination. -/
theorem terminalRefinedIII_loaded_fifth_elimination_68
    (A b h W P x y L N K2 : k)
    (h3 : b * P + 18 * W * y = 0)
    (h5 : -6 * A ^ 2 * x + L + 64 * b * h ^ 2 * y = 0)
    (hload : N - h * A ^ 3 * b * x - 27 * y * K2 = 0) :
    let c := h * A ^ 3 * b
    54 * A ^ 2 * W * N - 9 * W * c * L +
      b * P * (32 * c * b * h ^ 2 + 81 * A ^ 2 * K2) = 0 := by
  dsimp only
  have hy : 6 * A ^ 2 * N - (h * A ^ 3 * b) * L -
      (162 * A ^ 2 * K2 + 64 * (h * A ^ 3 * b) * b * h ^ 2) * y = 0 := by
    linear_combination 6 * A ^ 2 * hload - (h * A ^ 3 * b) * h5
  have hz : 108 * A ^ 2 * W * N - 18 * W * (h * A ^ 3 * b) * L +
      b * P * (162 * A ^ 2 * K2 +
        64 * (h * A ^ 3 * b) * b * h ^ 2) = 0 := by
    linear_combination 18 * W * hy +
      (162 * A ^ 2 * K2 + 64 * (h * A ^ 3 * b) * b * h ^ 2) * h3
  linear_combination (1 / 2 : k) * hz

end LoadedNextAlgebra68

section LoadedNextSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Source-facing next-loaded packet.  Its final field retains the entire
previous packet, including the original loaded scalar and all branch data. -/
theorem NonsquareAlignedSourceCurveData68.terminalRefinedIIILoadedNextPacket
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (A0 C0 E0 b1 b2 D phi w K : k[X]) (a : k)
    (hb : b1 = H * b2)
    (hW : terminalScaledW68 H A0 C0 S.gamma = H ^ 2 * w)
    (hPhi : terminalScaledPhi68 H A0 b1 C0 E0 S.gamma S.epsilon =
      H ^ 2 * phi)
    (ha : H.eval a = 0) (hh : H.derivative.eval a ≠ 0)
    (hA : A0.eval a ≠ 0) (hB : b2.eval a ≠ 0)
    (hw : w.eval a = 0) (hph : phi.eval a = 0) (hD : D.eval a = 0)
    (hw1 : w.derivative.eval a = 0)
    (hph1 : phi.derivative.eval a = 0)
    (hph2 : phi.derivative.derivative.eval a = 0)
    (hI4 : b2 * phi + C 6 * w * D = 0)
    (hrow : b2 * w * terminalEDerivativeNumerator68 H E0 - D * K =
      C j * H ^ 3)
    (hlower : terminalLowerZeroOne68 H A0 b2 C0 D E0
      S.alpha S.gamma S.epsilon S.eta = 0) :
    let eDot := terminalEDerivativeNumerator68 H E0
    eDot.derivative.derivative.eval a =
      -(2 / 9 : k) * H.derivative.eval a * A0.eval a *
          A0.derivative.eval a ^ 2 -
        (1 / 9 : k) * H.derivative.eval a * A0.eval a ^ 2 *
          A0.derivative.derivative.eval a -
        (5 / 9 : k) * H.derivative.derivative.eval a * A0.eval a ^ 2 *
          A0.derivative.eval a -
        (1 / 9 : k) * H.derivative.derivative.derivative.eval a *
          A0.eval a ^ 3 +
        S.gamma * A0.eval a * H.derivative.eval a ^ 3 ∧
    terminalFourthTripleMiddleDoubleZeroAt68 b2 w eDot a -
        terminalFourthPairLeftZeroAt68 D K a =
      36 * j * H.derivative.eval a ^ 2 *
        H.derivative.derivative.eval a ∧
    (let L := 16 * A0.eval a * b2.eval a ^ 2 * H.derivative.eval a *
          H.derivative.derivative.eval a +
        32 * A0.eval a * b2.eval a * b2.derivative.eval a *
          H.derivative.eval a ^ 2 -
        16 * A0.derivative.eval a * b2.eval a ^ 2 *
          H.derivative.eval a ^ 2
     let M := 4 * b2.derivative.eval a *
          phi.derivative.derivative.derivative.eval a +
        b2.eval a * phi.derivative.derivative.derivative.derivative.eval a +
        36 * w.derivative.derivative.eval a * D.derivative.derivative.eval a
     18 * b2.eval a * phi.derivative.derivative.derivative.eval a * L *
          w.derivative.derivative.eval a -
        81 * A0.eval a ^ 2 * w.derivative.derivative.eval a ^ 2 * M -
        64 * b2.eval a ^ 3 * H.derivative.eval a ^ 2 *
          phi.derivative.derivative.derivative.eval a ^ 2 = 0) ∧
    (let L := 16 * A0.eval a * b2.eval a ^ 2 * H.derivative.eval a *
          H.derivative.derivative.eval a +
        32 * A0.eval a * b2.eval a * b2.derivative.eval a *
          H.derivative.eval a ^ 2 -
        16 * A0.derivative.eval a * b2.eval a ^ 2 *
          H.derivative.eval a ^ 2
     let N := -3 * H.derivative.eval a * A0.eval a ^ 3 *
          b2.derivative.eval a * w.derivative.derivative.eval a -
        6 * H.derivative.eval a * A0.eval a ^ 2 * A0.derivative.eval a *
          b2.eval a * w.derivative.derivative.eval a -
        3 * H.derivative.derivative.eval a * A0.eval a ^ 3 * b2.eval a *
          w.derivative.derivative.eval a -
        9 * (D.derivative.derivative.derivative.eval a * K.eval a +
          3 * D.derivative.derivative.eval a * K.derivative.eval a) -
        54 * j * H.derivative.eval a ^ 3
     let c := H.derivative.eval a * A0.eval a ^ 3 * b2.eval a
     54 * A0.eval a ^ 2 * w.derivative.derivative.eval a * N -
        9 * w.derivative.derivative.eval a * c * L +
        b2.eval a * phi.derivative.derivative.derivative.eval a *
          (32 * c * b2.eval a * H.derivative.eval a ^ 2 +
            81 * A0.eval a ^ 2 * K.derivative.derivative.eval a) = 0) ∧
    (-3 * H.derivative.eval a * A0.eval a ^ 3 * b2.derivative.eval a *
          w.derivative.derivative.eval a -
        H.derivative.eval a * A0.eval a ^ 3 * b2.eval a *
          w.derivative.derivative.derivative.eval a -
        6 * H.derivative.eval a * A0.eval a ^ 2 * A0.derivative.eval a *
          b2.eval a * w.derivative.derivative.eval a -
        3 * H.derivative.derivative.eval a * A0.eval a ^ 3 * b2.eval a *
          w.derivative.derivative.eval a -
        9 * (D.derivative.derivative.derivative.eval a * K.eval a +
          3 * D.derivative.derivative.eval a * K.derivative.eval a +
          3 * D.derivative.eval a * K.derivative.derivative.eval a) =
      54 * j * H.derivative.eval a ^ 3) := by
  dsimp only
  have hE := S.terminalActualEShape68 (H := H) A0 C0 E0 b1 b2 w phi
    hb hW hPhi
  have he2 := terminalEDerivativeNumerator_second_eval_root_shape_68
    H A0 b2 phi w E0 S.gamma S.epsilon a ha hw hph hE
  let eDot := terminalEDerivativeNumerator68 H E0
  have hload4 := terminalLoadedFourth_of_row_68 H b2 w eDot D K j a ha hw hw1
    hD (by simpa only [eDot] using hrow)
  have h3 := congrArg (fun P : k[X] =>
    P.derivative.derivative.derivative.eval a) hrow
  simp only [derivative_sub, eval_sub] at h3
  rw [terminalThirdTripleAt68_eq,
    terminalThirdPairAt68_eq, terminalThirdCoreLoad68_eq H j a ha] at h3
  rw [terminalThirdTripleAt68_of_middle_zero b2 w eDot a hw,
    terminalThirdTripleMiddleZeroAt68_of_derivative_zero b2 w eDot a hw1,
    terminalThirdPairAt68_of_left_zero D K a hD] at h3
  have hprev := S.terminalRefinedIIIFifthLocalPacket (H := H)
    A0 C0 E0 b1 b2 D phi w K a hb hW hPhi ha hh hA hB hw hph hD hw1
      hph1 hph2 hI4 (by simpa only [eDot] using h3) hlower
  have hI4three := terminalI4_third_refinedIII_68 b2 D w phi a hw hph hD
    hw1 hph1 hph2 hI4
  let L := 16 * A0.eval a * b2.eval a ^ 2 * H.derivative.eval a *
        H.derivative.derivative.eval a +
      32 * A0.eval a * b2.eval a * b2.derivative.eval a *
        H.derivative.eval a ^ 2 -
      16 * A0.derivative.eval a * b2.eval a ^ 2 *
        H.derivative.eval a ^ 2
  have hfive : -6 * A0.eval a ^ 2 * w.derivative.derivative.derivative.eval a +
      L + 64 * b2.eval a * H.derivative.eval a ^ 2 * D.derivative.eval a = 0 := by
    dsimp only [L]
    linear_combination hprev.2.2.2.2.1
  have helim := terminalRefinedIII_I4_fifth_elimination_68
    (A0.eval a) (b2.eval a) (b2.derivative.eval a) (H.derivative.eval a)
      (H.derivative.derivative.eval a) (w.derivative.derivative.eval a)
      (phi.derivative.derivative.derivative.eval a)
      (phi.derivative.derivative.derivative.derivative.eval a)
      (w.derivative.derivative.derivative.eval a) (D.derivative.eval a)
      (D.derivative.derivative.eval a) L hI4three hfive hprev.2.2.2.1
  let N := -3 * H.derivative.eval a * A0.eval a ^ 3 *
        b2.derivative.eval a * w.derivative.derivative.eval a -
      6 * H.derivative.eval a * A0.eval a ^ 2 * A0.derivative.eval a *
        b2.eval a * w.derivative.derivative.eval a -
      3 * H.derivative.derivative.eval a * A0.eval a ^ 3 * b2.eval a *
        w.derivative.derivative.eval a -
      9 * (D.derivative.derivative.derivative.eval a * K.eval a +
        3 * D.derivative.derivative.eval a * K.derivative.eval a) -
      54 * j * H.derivative.eval a ^ 3
  have hloadN : N - H.derivative.eval a * A0.eval a ^ 3 * b2.eval a *
        w.derivative.derivative.derivative.eval a -
      27 * D.derivative.eval a * K.derivative.derivative.eval a = 0 := by
    dsimp only [N]
    linear_combination hprev.2.2.2.2.2
  have helimLoad := terminalRefinedIII_loaded_fifth_elimination_68
    (A0.eval a) (b2.eval a) (H.derivative.eval a)
      (w.derivative.derivative.eval a)
      (phi.derivative.derivative.derivative.eval a)
      (w.derivative.derivative.derivative.eval a) (D.derivative.eval a) L N
      (K.derivative.derivative.eval a) hI4three hfive hloadN
  exact ⟨he2, hload4, helim, helimLoad, hprev.2.2.2.2.2⟩

end LoadedNextSource68

end Max11DegreeRoutes
