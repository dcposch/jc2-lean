import Grok610AlignedSquareTowerOrders61to68Scratch

/-! # Orders `69` through `75` of the aligned-square `(6,10)` bounded tower

Untracked working note.  No tracked file was edited.

`Grok610AlignedSquareTowerOrders61to68Scratch` landed orders `61`–`68`
on both live MixedPair limbs, with remaining pole `6` (`21 - 15`) and
`h₀^{15}` dividing each specialised jet.  This file continues the
tower through the native ceiling `alignedSquareTowerCeiling610 = 75`.

Each order `k ∈ {69,…,75}` is the `h^{k-61}` coefficient of the
order-`61` tower (equivalently `h^{k-54}` of
`alignedSquareJetQuotient610`) on that limb.  Vanishing of the
remaining-numerator head is recorded in the same
`zero_of_remaining_pole` shape as the parent.  After order `74` the
remaining pole is `1`; the last linear factor cancels, remaining pole
`0`, and the leftover numerator *is* `rho`.  A polynomial cannot have
derivative `C j / h₀` with `j ≠ 0`, so each specialised jet is False
under the parent clearing hypothesis.

The packet `alignedSquareFace610_order75Grandchildren` is that
cancel-and-expose contradiction on the MixedPair jet.  The
source-primitive identity `algebraMap jet = h₀^{21} · (scale · ρ)`
is not re-proved here, so the chamber is not closed on the raw
hypotheses of `normalized610ScaleTwo_alignedSquare_m1m2Reduction`.
There is no unused compact-numerator order after `75`.

CAS: `derive_610_aligned_square_tower_orders69to75.py` (job
`20260902T085942Z-aligned-square-tower-69to75-21629`).  No `sorry`, no new axioms, no finite-root shortcut, no
closure overclaim.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option maxHeartbeats 1600000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Bookkeeping: ceiling order `75`, remaining pole `0` -/

/-- Last compact-numerator order of the aligned-square tower. -/
def alignedSquareTowerCeilingLastOrder610 : ℕ := 75

/-- Vanishing multiplicity of the MixedPair jet through the ceiling:
orders `54` through `74` plus the holomorphic remainder, i.e. `h₀^{21}`. -/
def alignedSquareTowerCeilingDivisibility610 : ℕ := 21

/-- Remaining pole after the ceiling order. -/
def alignedSquareTowerRemainingPoleAfterCeiling610 : ℕ := 0

theorem alignedSquareTowerCeilingLastOrder610_eq :
    alignedSquareTowerCeilingLastOrder610 = 75 :=
  rfl

theorem alignedSquareTowerCeilingDivisibility610_eq :
    alignedSquareTowerCeilingDivisibility610 = 21 :=
  rfl

theorem alignedSquareTowerRemainingPoleAfterCeiling610_eq :
    alignedSquareTowerRemainingPoleAfterCeiling610 = 0 :=
  rfl

theorem alignedSquareTowerCeilingLastOrder610_eq_ceiling :
    alignedSquareTowerCeilingLastOrder610 =
      alignedSquareTowerCeiling610 :=
  rfl

theorem alignedSquareTowerCeilingDivisibility610_eq_remaining :
    alignedSquareTowerCeilingDivisibility610 =
      alignedSquareRemainingPole610 :=
  rfl

theorem alignedSquareTowerCeilingLastOrder610_eq_add :
    alignedSquareTowerCeilingLastOrder610 =
      alignedSquareBaseOrder610 + alignedSquareRemainingPole610 :=
  rfl

#print axioms alignedSquareTowerCeilingLastOrder610_eq_ceiling
#print axioms alignedSquareTowerCeilingDivisibility610_eq_remaining
/-! ## Holomorphic remainder (remaining pole `0`) -/

section AlignedSquarePoleZero610

variable {k : Type*} [Field k] [CharZero k]

/-- Cancel every polynomial power from a pole-`n` clearing.  The
remaining factor *is* `rho`. -/
theorem alignedSquare_algebraMap_cancel_all_clearing610
    (h0 Q : k[X]) (rho : RatFunc k) (n : ℕ) (hh0 : h0 ≠ 0)
    (hquot :
      algebraMap k[X] (RatFunc k) (h0 ^ n * Q) =
        (algebraMap k[X] (RatFunc k) h0) ^ n * rho) :
    algebraMap k[X] (RatFunc k) Q = rho := by
  let hRF : RatFunc k := algebraMap k[X] (RatFunc k) h0
  have hhRF : hRF ≠ 0 := RatFunc.algebraMap_ne_zero hh0
  apply mul_left_cancel₀ (pow_ne_zero n hhRF)
  have hmapPow :
      algebraMap k[X] (RatFunc k) (h0 ^ n * Q) =
        hRF ^ n * algebraMap k[X] (RatFunc k) Q := by
    simp only [hRF, map_mul, map_pow]
  calc
    hRF ^ n * algebraMap k[X] (RatFunc k) Q =
        algebraMap k[X] (RatFunc k) (h0 ^ n * Q) := hmapPow.symm
    _ = hRF ^ n * rho := hquot

/-- A rational function that is the image of a polynomial cannot have
derivative `C j / h0` with `j ≠ 0`: evaluating `h0 * (remaining)' = C j`
at the simple root forces `j = 0`.  Adapted from
`localLinearPoleZero_C_eq_zero_of_deriv_eq_simplePole610`. -/
theorem alignedSquare_C_eq_zero_of_deriv_eq_simplePole610
    (a j : k) (h0 A0 : k[X]) (rho : RatFunc k) (hh0 : h0 ≠ 0)
    (hroot : h0.eval a = 0)
    (hclear : algebraMap k[X] (RatFunc k) A0 = rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    j = 0 := by
  have hhRF : algebraMap k[X] (RatFunc k) h0 ≠ 0 :=
    RatFunc.algebraMap_ne_zero hh0
  have hderivA :
      algebraMap k[X] (RatFunc k) (derivative A0) =
        RatFunc.C j / algebraMap k[X] (RatFunc k) h0 := by
    rw [← hderiv, ← hclear, GCD369RatFuncDerivative]
  have hpoly : h0 * derivative A0 = Polynomial.C j := by
    apply FaithfulSMul.algebraMap_injective k[X] (RatFunc k)
    rw [map_mul, hderivA, mul_div_cancel₀ _ hhRF]
    simp only [RatFunc.algebraMap_C]
  have heval := congrArg (fun p : k[X] ↦ p.eval a) hpoly
  have heval' : (0 : k) = j := by
    simpa [hroot, Polynomial.eval_mul, Polynomial.eval_C] using heval
  exact heval'.symm

/-- Cancel-and-expose: if `h0^n` divides the cleared numerator, the
remaining factor *is* `rho`, so the simple-pole equation forces `j = 0`. -/
theorem alignedSquare_of_pow_dvd_simplePole_eval610
    (a j : k) (h0 A0 Q : k[X]) (rho : RatFunc k) (n : ℕ)
    (hh0 : h0 ≠ 0) (hroot : h0.eval a = 0) (hA : A0 = h0 ^ n * Q)
    (hclear : algebraMap k[X] (RatFunc k) A0 =
      (algebraMap k[X] (RatFunc k) h0) ^ n * rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    j = 0 :=
  alignedSquare_C_eq_zero_of_deriv_eq_simplePole610 a j h0 Q rho hh0
    hroot
    (alignedSquare_algebraMap_cancel_all_clearing610 h0 Q rho n hh0
      (by simpa [hA] using hclear))
    hderiv

/-- Same holomorphic remainder, with `j ≠ 0`, is False. -/
theorem alignedSquare_of_pow_dvd_simplePole_ne_zero610
    (a j : k) (h0 A0 Q : k[X]) (rho : RatFunc k) (n : ℕ)
    (hh0 : h0 ≠ 0) (hroot : h0.eval a = 0) (hA : A0 = h0 ^ n * Q)
    (hclear : algebraMap k[X] (RatFunc k) A0 =
      (algebraMap k[X] (RatFunc k) h0) ^ n * rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
    (hj : j ≠ 0) : False :=
  hj (alignedSquare_of_pow_dvd_simplePole_eval610 a j h0 A0 Q rho n hh0
    hroot hA hclear hderiv)

/-- Successive remaining-numerator peels: a pole-`n` numerator of a
simple-pole rational function is divisible by `h₀^n`.  Each successor
step is the parent head obstruction plus one linear cancellation; the
`n = 0` remainder is the holomorphic case. -/
theorem alignedSquare_pow_dvd_of_remaining_pole610
    (h0 Q : k[X]) (rho : RatFunc k) (j a : k) (n : ℕ)
    (hh0 : h0 ≠ 0) (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear : algebraMap k[X] (RatFunc k) Q =
      (algebraMap k[X] (RatFunc k) h0) ^ n * rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    h0 ^ n ∣ Q := by
  induction n generalizing Q with
  | zero =>
    refine ⟨Q, ?_⟩
    simp
  | succ n ih =>
    have hQ0 : Q.eval a = 0 :=
      alignedSquare_localLinearPole_head_eval_zero610 (n + 1)
        (Nat.succ_ne_zero n) a j h0 Q rho hdegree hroot
        (by simpa [Nat.succ_eq_add_one] using hclear) hderiv
    obtain ⟨Qnew, hfact⟩ :=
      alignedSquare_linearPolynomial_dvd_of_eval_eq_zero610 h0 Q a
        hdegree hroot hQ0
    have hclear' :
        algebraMap k[X] (RatFunc k) Qnew =
          (algebraMap k[X] (RatFunc k) h0) ^ n * rho :=
      alignedSquare_algebraMap_cancel_one_clearing610 h0 Q Qnew rho n
        hh0 hfact
        (by simpa [Nat.succ_eq_add_one, add_comm n 1] using hclear)
    obtain ⟨R, hR⟩ := ih Qnew hclear'
    refine ⟨R, ?_⟩
    calc
      Q = h0 * Qnew := hfact
      _ = h0 * (h0 ^ n * R) := by rw [hR]
      _ = h0 ^ (n + 1) * R := by ring

#print axioms alignedSquare_algebraMap_cancel_all_clearing610
#print axioms alignedSquare_C_eq_zero_of_deriv_eq_simplePole610
#print axioms alignedSquare_of_pow_dvd_simplePole_eval610
#print axioms alignedSquare_of_pow_dvd_simplePole_ne_zero610
#print axioms alignedSquare_pow_dvd_of_remaining_pole610

end AlignedSquarePoleZero610
/-! ## Order `69` (MixedPair `h^15`, order-`61` tower `h^8`) -/
set_option maxHeartbeats 1600000000 in
/-- Frozen order-`69` coefficient of the MixedPair jet (`h^15` of `alignedSquareJetQuotient610`). -/
def alignedSquareMixedPairOrder69610 {R : Type*} [CommRing R] (w1 e1 e3 a2 a1 a0 b4 b3 b2 b1 : R) : R :=
    - (2544319940198400 : R) * w1 ^ 4 * e1 * e3 * a0
    + (65825897840640 : R) * w1 ^ 4 * e1 * b1
    - (1873464648007680 : R) * w1 ^ 3 * e1 ^ 3 * a0
    + (57049111461888000 : R) * w1 ^ 3 * e1 * a2 * a0
    + (28524555730944000 : R) * w1 ^ 3 * e1 * a1 ^ 2
    - (44606301143040 : R) * w1 ^ 2 * e1 * e3 ^ 2 * a1
    - (210642873090048 : R) * w1 ^ 2 * e1 * e3 * b2
    - (475800545525760 : R) * w1 * e1 ^ 3 * e3 * a1
    - (304261927796736 : R) * w1 * e1 ^ 3 * b2
    - (54389637120 : R) * w1 * e1 * e3 ^ 4
    + (5071032129945600 : R) * w1 * e1 * e3 * a2 * a1
    + (7583143431241728 : R) * w1 * e1 * a2 * b2
    + (11374715146862592 : R) * w1 * e1 * a1 * b3
    + (15166286862483456 : R) * w1 * e1 * a0 * b4
    - (111515752857600 : R) * e1 ^ 5 * a1
    - (169967616000 : R) * e1 ^ 3 * e3 ^ 3
    + (4817480523448320 : R) * e1 ^ 3 * a2 * a1
    + (2202780303360 : R) * e1 * e3 ^ 3 * a2
    + (7801587892224 : R) * e1 * e3 ^ 2 * b3
    - (41075360252559360 : R) * e1 * a2 ^ 2 * a1
/-- Order-`69` coefficient of the MixedPair jet on `w₁ = 0` (frozen, no Taylor of `w₁`). -/
def alignedSquareW1ZeroOrder69610 {R : Type*} [CommRing R] (e1 e3 a2 a1 b3 : R) : R :=
    - (111515752857600 : R) * e1 ^ 5 * a1
    - (169967616000 : R) * e1 ^ 3 * e3 ^ 3
    + (4817480523448320 : R) * e1 ^ 3 * a2 * a1
    + (2202780303360 : R) * e1 * e3 ^ 3 * a2
    + (7801587892224 : R) * e1 * e3 ^ 2 * b3
    - (41075360252559360 : R) * e1 * a2 ^ 2 * a1
set_option maxHeartbeats 1600000000 in
/-- Order-`69` mixed coefficient after `w₁ = h w₁n`. -/
def alignedSquareW1PeelOrder69610 {R : Type*} [CommRing R] (w1n e1 e3 a2 a1 a0 b6 b5 b4 b3 : R) : R :=
    (884317824 : R) * w1n ^ 11 * b6
    + (2918248819200 : R) * w1n ^ 8 * e1 * b5
    - (1037599580160 : R) * w1n ^ 7 * e3 * b5
    + (313770113040384 : R) * w1n ^ 5 * e1 ^ 2 * b4
    - (236973232226304 : R) * w1n ^ 5 * a2 * b4
    - (296216540282880 : R) * w1n ^ 5 * a1 * b5
    - (355459848339456 : R) * w1n ^ 5 * a0 * b6
    - (139453383573504 : R) * w1n ^ 4 * e1 * e3 * b4
    + (39122296012800 : R) * w1n ^ 3 * e1 ^ 6
    - (418184073216000 : R) * w1n ^ 3 * e1 ^ 4 * a2
    - (8430590916034560 : R) * w1n ^ 3 * e1 ^ 2 * a2 ^ 2
    + (14302911135744 : R) * w1n ^ 3 * e3 ^ 2 * b4
    + (28524555730944000 : R) * w1n ^ 3 * a2 ^ 3
    - (26674292736000 : R) * w1n ^ 2 * e1 ^ 5 * e3
    + (557578764288000 : R) * w1n ^ 2 * e1 ^ 3 * e3 * a2
    + (570491114618880 : R) * w1n ^ 2 * e1 ^ 3 * b3
    - (1204370130862080 : R) * w1n ^ 2 * e1 * e3 * a2 ^ 2
    - (8531036360146944 : R) * w1n ^ 2 * e1 * a2 * b3
    - (11374715146862592 : R) * w1n ^ 2 * e1 * a1 * b4
    - (14218393933578240 : R) * w1n ^ 2 * e1 * a0 * b5
    + (4206698496000 : R) * w1n * e1 ^ 4 * e3 ^ 2
    - (79300090920960 : R) * w1n * e1 ^ 2 * e3 ^ 2 * a2
    - (152130963898368 : R) * w1n * e1 ^ 2 * e3 * b3
    + (140862003609600 : R) * w1n * e3 ^ 2 * a2 ^ 2
    + (1263857238540288 : R) * w1n * e3 * a2 * b3
    + (1685142984720384 : R) * w1n * e3 * a1 * b4
    + (2106428730900480 : R) * w1n * e3 * a0 * b5
    - (111515752857600 : R) * e1 ^ 5 * a1
    - (169967616000 : R) * e1 ^ 3 * e3 ^ 3
    + (4817480523448320 : R) * e1 ^ 3 * a2 * a1
    + (2202780303360 : R) * e1 * e3 ^ 3 * a2
    + (7801587892224 : R) * e1 * e3 ^ 2 * b3
    - (41075360252559360 : R) * e1 * a2 ^ 2 * a1
set_option maxHeartbeats 1600000000 in
/-- Order-`69` coefficient on the `w₁ = 0` complement peel `w₁ = h w₁n`, `e₁ = h e₁b`, `e₃ = h e₃b`, `a₂ = h a₂b`. -/
def alignedSquareW1ComplementOrder69610 {R : Type*} [CommRing R] (w1n e1b e3b a2b a1 a0 b6 b5 b4 : R) : R :=
    (884317824 : R) * w1n ^ 11 * b6
    - (1102449553920 : R) * w1n ^ 9 * e1b * b6
    + (389099842560 : R) * w1n ^ 8 * e3b * b6
    + (100543399317504 : R) * w1n ^ 7 * e1b ^ 2 * b6
    - (49389740015616 : R) * w1n ^ 6 * e1b * e3b * b6
    + (90510609530880 : R) * w1n ^ 6 * a2b * b5
    - (597166856552448 : R) * w1n ^ 5 * e1b ^ 3 * b6
    + (5810557648896 : R) * w1n ^ 5 * e3b ^ 2 * b6
    - (296216540282880 : R) * w1n ^ 5 * a1 * b5
    - (355459848339456 : R) * w1n ^ 5 * a0 * b6
    + (284365169786880 : R) * w1n ^ 4 * e1b ^ 2 * e3b * b6
    - (4706551695605760 : R) * w1n ^ 4 * e1b * a2b * b5
    + (538621086302208 : R) * w1n ^ 3 * e1b ^ 4 * b6
    - (39910901022720 : R) * w1n ^ 3 * e1b * e3b ^ 2 * b6
    + (8689018514964480 : R) * w1n ^ 3 * e1b * a1 * b5
    + (10426822217957376 : R) * w1n ^ 3 * e1b * a0 * b6
    + (965446501662720 : R) * w1n ^ 3 * e3b * a2b * b5
    - (187346464800768 : R) * w1n ^ 2 * e1b ^ 3 * e3b * b6
    + (8557366719283200 : R) * w1n ^ 2 * e1b ^ 2 * a2b * b5
    + (1565133373440 : R) * w1n ^ 2 * e3b ^ 3 * b6
    - (1579821548175360 : R) * w1n ^ 2 * e3b * a1 * b5
    - (1895785857810432 : R) * w1n ^ 2 * e3b * a0 * b6
    - (66909451714560 : R) * w1n * e1b ^ 5 * b6
    + (17842520457216 : R) * w1n * e1b ^ 2 * e3b ^ 2 * b6
    - (6845893375426560 : R) * w1n * e1b ^ 2 * a1 * b5
    - (8215072050511872 : R) * w1n * e1b ^ 2 * a0 * b6
    - (1521309638983680 : R) * w1n * e1b * e3b * a2b * b5
    + (22749430293725184 : R) * w1n * a2b ^ 2 * b4
    + (8921260228608 : R) * e1b ^ 4 * e3b * b6
    - (760654819491840 : R) * e1b ^ 3 * a2b * b5
    - (417368899584 : R) * e1b * e3b ^ 3 * b6
    + (702142910300160 : R) * e1b * e3b * a1 * b5
    + (842571492360192 : R) * e1b * e3b * a0 * b6
    + (39007939461120 : R) * e3b ^ 2 * a2b * b5
    - (38999023360671744 : R) * a2b * a1 * b4
    - (48748779200839680 : R) * a2b * a0 * b5
/-- Order-`69` mixed coefficient on `μ = 0` after the pole-`21` `q₈` peel: `e₁ = h e₁n`, `b₈ = h b₈n`. -/
def alignedSquareMuZeroQ8Order69610 {R : Type*} [CommRing R] (w1 : R) : R :=
    0
/-! ## Order `70` (MixedPair `h^16`, order-`61` tower `h^9`) -/
set_option maxHeartbeats 1600000000 in
/-- Frozen order-`70` coefficient of the MixedPair jet (`h^16` of `alignedSquareJetQuotient610`). -/
def alignedSquareMixedPairOrder70610 {R : Type*} [CommRing R] (w1 e1 e3 a2 a1 a0 b4 b3 b2 b1 : R) : R :=
    (49961856461045760 : R) * w1 ^ 4 * a1 * a0
    + (117385003008000 : R) * w1 ^ 3 * e3 ^ 2 * a0
    - (25076532510720 : R) * w1 ^ 3 * e3 * b1
    - (401456710287360 : R) * w1 ^ 2 * e1 ^ 2 * e3 * a0
    - (473946464452608 : R) * w1 ^ 2 * e1 ^ 2 * b1
    - (2281964458475520 : R) * w1 ^ 2 * e3 * a2 * a0
    - (1140982229237760 : R) * w1 ^ 2 * e3 * a1 ^ 2
    + (2437438960041984 : R) * w1 ^ 2 * a2 * b1
    + (4874877920083968 : R) * w1 ^ 2 * a1 * b2
    + (7312316880125952 : R) * w1 ^ 2 * a0 * b3
    - (1070551227432960 : R) * w1 * e1 ^ 4 * a0
    + (22819644584755200 : R) * w1 * e1 ^ 2 * a2 * a0
    + (11409822292377600 : R) * w1 * e1 ^ 2 * a1 ^ 2
    + (3478074163200 : R) * w1 * e3 ^ 3 * a1
    + (15603175784448 : R) * w1 * e3 ^ 2 * b2
    - (37915717156208640 : R) * w1 * a2 ^ 2 * a0
    - (37915717156208640 : R) * w1 * a2 * a1 ^ 2
    + (29737534095360 : R) * e1 ^ 2 * e3 ^ 2 * a1
    + (46809527353344 : R) * e1 ^ 2 * e3 * b2
    + (453246976 : R) * e3 ^ 5
    - (169034404331520 : R) * e3 ^ 2 * a2 * a1
    - (722204136308736 : R) * e3 * a2 * b2
    - (1083306204463104 : R) * e3 * a1 * b3
    - (1444408272617472 : R) * e3 * a0 * b4
/-- Order-`70` coefficient of the MixedPair jet on `w₁ = 0` (frozen, no Taylor of `w₁`). -/
def alignedSquareW1ZeroOrder70610 {R : Type*} [CommRing R] (e1 e3 a2 a1 a0 b4 b3 b2 : R) : R :=
    (29737534095360 : R) * e1 ^ 2 * e3 ^ 2 * a1
    + (46809527353344 : R) * e1 ^ 2 * e3 * b2
    + (453246976 : R) * e3 ^ 5
    - (169034404331520 : R) * e3 ^ 2 * a2 * a1
    - (722204136308736 : R) * e3 * a2 * b2
    - (1083306204463104 : R) * e3 * a1 * b3
    - (1444408272617472 : R) * e3 * a0 * b4
set_option maxHeartbeats 1600000000 in
/-- Order-`70` mixed coefficient after `w₁ = h w₁n`. -/
def alignedSquareW1PeelOrder70610 {R : Type*} [CommRing R] (w1n e1 e3 a2 a1 a0 b5 b4 b3 b2 : R) : R :=
    - (3242498688 : R) * w1n ^ 10 * b5
    - (7470716977152 : R) * w1n ^ 7 * e1 * b4
    + (2681795837952 : R) * w1n ^ 6 * e3 * b4
    + (208859712122880 : R) * w1n ^ 5 * e1 ^ 5
    - (6732763578777600 : R) * w1n ^ 5 * e1 ^ 3 * a2
    + (30711438336983040 : R) * w1n ^ 5 * e1 * a2 ^ 2
    - (46787569920000 : R) * w1n ^ 4 * e1 ^ 4 * e3
    + (1645786652590080 : R) * w1n ^ 4 * e1 ^ 2 * e3 * a2
    - (470655169560576 : R) * w1n ^ 4 * e1 ^ 2 * b3
    - (3816479910297600 : R) * w1n ^ 4 * e3 * a2 ^ 2
    + (592433080565760 : R) * w1n ^ 4 * a2 * b3
    + (789910774087680 : R) * w1n ^ 4 * a1 * b4
    + (987388467609600 : R) * w1n ^ 4 * a0 * b5
    - (3441844224000 : R) * w1n ^ 3 * e1 ^ 3 * e3 ^ 2
    - (69387579555840 : R) * w1n ^ 3 * e1 * e3 ^ 2 * a2
    + (193089300332544 : R) * w1n ^ 3 * e1 * e3 * b3
    + (1254552219648000 : R) * w1n ^ 2 * e1 ^ 4 * a1
    + (1147281408000 : R) * w1n ^ 2 * e1 ^ 2 * e3 ^ 3
    - (10839331177758720 : R) * w1n ^ 2 * e1 ^ 2 * a2 * a1
    - (1652085227520 : R) * w1n ^ 2 * e3 ^ 3 * a2
    - (17553572757504 : R) * w1n ^ 2 * e3 ^ 2 * b3
    - (30806520189419520 : R) * w1n ^ 2 * a2 ^ 2 * a1
    - (475800545525760 : R) * w1n * e1 ^ 3 * e3 * a1
    - (304261927796736 : R) * w1n * e1 ^ 3 * b2
    - (54389637120 : R) * w1n * e1 * e3 ^ 4
    + (5071032129945600 : R) * w1n * e1 * e3 * a2 * a1
    + (7583143431241728 : R) * w1n * e1 * a2 * b2
    + (11374715146862592 : R) * w1n * e1 * a1 * b3
    + (15166286862483456 : R) * w1n * e1 * a0 * b4
    + (29737534095360 : R) * e1 ^ 2 * e3 ^ 2 * a1
    + (46809527353344 : R) * e1 ^ 2 * e3 * b2
    + (453246976 : R) * e3 ^ 5
    - (169034404331520 : R) * e3 ^ 2 * a2 * a1
    - (722204136308736 : R) * e3 * a2 * b2
    - (1083306204463104 : R) * e3 * a1 * b3
    - (1444408272617472 : R) * e3 * a0 * b4
set_option maxHeartbeats 1600000000 in
/-- Order-`70` coefficient on the `w₁ = 0` complement peel `w₁ = h w₁n`, `e₁ = h e₁b`, `e₃ = h e₃b`, `a₂ = h a₂b`. -/
def alignedSquareW1ComplementOrder70610 {R : Type*} [CommRing R] (w1n e1b e3b a2b a1 a0 b5 b4 b3 : R) : R :=
    - (3242498688 : R) * w1n ^ 10 * b5
    + (2918248819200 : R) * w1n ^ 8 * e1b * b5
    - (1037599580160 : R) * w1n ^ 7 * e3b * b5
    - (185211525058560 : R) * w1n ^ 6 * e1b ^ 2 * b5
    + (87158364733440 : R) * w1n ^ 5 * e1b * e3b * b5
    - (236973232226304 : R) * w1n ^ 5 * a2b * b4
    + (710912924467200 : R) * w1n ^ 4 * e1b ^ 3 * b5
    - (9684262748160 : R) * w1n ^ 4 * e3b ^ 2 * b5
    + (789910774087680 : R) * w1n ^ 4 * a1 * b4
    + (987388467609600 : R) * w1n ^ 4 * a0 * b5
    - (299331757670400 : R) * w1n ^ 3 * e1b ^ 2 * e3b * b5
    + (6951214811971584 : R) * w1n ^ 3 * e1b * a2b * b4
    - (351274621501440 : R) * w1n ^ 2 * e1b ^ 4 * b5
    + (35215500902400 : R) * w1n ^ 2 * e1b * e3b ^ 2 * b5
    - (11374715146862592 : R) * w1n ^ 2 * e1b * a1 * b4
    - (14218393933578240 : R) * w1n ^ 2 * e1b * a0 * b5
    - (1263857238540288 : R) * w1n ^ 2 * e3b * a2b * b4
    + (89212602286080 : R) * w1n * e1b ^ 3 * e3b * b5
    - (5476714700341248 : R) * w1n * e1b ^ 2 * a2b * b4
    - (1043422248960 : R) * w1n * e3b ^ 3 * b5
    + (1685142984720384 : R) * w1n * e3b * a1 * b4
    + (2106428730900480 : R) * w1n * e3b * a0 * b5
    + (13381890342912 : R) * e1b ^ 5 * b5
    - (4695400120320 : R) * e1b ^ 2 * e3b ^ 2 * b5
    + (2527714477080576 : R) * e1b ^ 2 * a1 * b4
    + (3159643096350720 : R) * e1b ^ 2 * a0 * b5
    + (561714328240128 : R) * e1b * e3b * a2b * b4
    - (14624633760251904 : R) * a2b ^ 2 * b3
set_option maxHeartbeats 1600000000 in
/-- Order-`70` mixed coefficient on `μ = 0` after the pole-`21` `q₈` peel: `e₁ = h e₁n`, `b₈ = h b₈n`. -/
def alignedSquareMuZeroQ8Order70610 {R : Type*} [CommRing R] (w1 e1n e3 a2 a1 a0 b5 b4 b3 b2 b1 : R) : R :=
    (208859712122880 : R) * w1 ^ 5 * e1n ^ 5
    + (10237146112327680 : R) * w1 ^ 5 * e1n ^ 2 * a0
    - (46787569920000 : R) * w1 ^ 4 * e1n ^ 4 * e3
    + (4937359957770240 : R) * w1 ^ 4 * e1n ^ 3 * a1
    - (2544319940198400 : R) * w1 ^ 4 * e1n * e3 * a0
    + (65825897840640 : R) * w1 ^ 4 * e1n * b1
    + (49961856461045760 : R) * w1 ^ 4 * a1 * a0
    - (418184073216000 : R) * w1 ^ 3 * e1n ^ 4 * a2
    - (3441844224000 : R) * w1 ^ 3 * e1n ^ 3 * e3 ^ 2
    - (624488216002560 : R) * w1 ^ 3 * e1n ^ 2 * e3 * a1
    + (579267900997632 : R) * w1 ^ 3 * e1n ^ 2 * b2
    + (57049111461888000 : R) * w1 ^ 3 * e1n * a2 * a0
    + (28524555730944000 : R) * w1 ^ 3 * e1n * a1 ^ 2
    + (117385003008000 : R) * w1 ^ 3 * e3 ^ 2 * a0
    - (25076532510720 : R) * w1 ^ 3 * e3 * b1
    + (557578764288000 : R) * w1 ^ 2 * e1n ^ 3 * e3 * a2
    + (570491114618880 : R) * w1 ^ 2 * e1n ^ 3 * b3
    + (1147281408000 : R) * w1 ^ 2 * e1n ^ 2 * e3 ^ 3
    - (10839331177758720 : R) * w1 ^ 2 * e1n ^ 2 * a2 * a1
    - (44606301143040 : R) * w1 ^ 2 * e1n * e3 ^ 2 * a1
    - (210642873090048 : R) * w1 ^ 2 * e1n * e3 * b2
    - (2281964458475520 : R) * w1 ^ 2 * e3 * a2 * a0
    - (1140982229237760 : R) * w1 ^ 2 * e3 * a1 ^ 2
    + (2437438960041984 : R) * w1 ^ 2 * a2 * b1
    + (4874877920083968 : R) * w1 ^ 2 * a1 * b2
    + (7312316880125952 : R) * w1 ^ 2 * a0 * b3
    + (160582684114944 : R) * w1 * e1n ^ 4 * b4
    - (6423307364597760 : R) * w1 * e1n ^ 3 * a2 ^ 2
    - (79300090920960 : R) * w1 * e1n ^ 2 * e3 ^ 2 * a2
    - (152130963898368 : R) * w1 * e1n ^ 2 * e3 * b3
    - (54389637120 : R) * w1 * e1n * e3 ^ 4
    + (5071032129945600 : R) * w1 * e1n * e3 * a2 * a1
    + (7583143431241728 : R) * w1 * e1n * a2 * b2
    + (11374715146862592 : R) * w1 * e1n * a1 * b3
    + (15166286862483456 : R) * w1 * e1n * a0 * b4
    + (3478074163200 : R) * w1 * e3 ^ 3 * a1
    + (15603175784448 : R) * w1 * e3 ^ 2 * b2
    - (37915717156208640 : R) * w1 * a2 ^ 2 * a0
    - (37915717156208640 : R) * w1 * a2 * a1 ^ 2
    + (13381890342912 : R) * e1n ^ 5 * b5
    - (22537920577536 : R) * e1n ^ 3 * e3 * b4
    + (802913420574720 : R) * e1n ^ 2 * e3 * a2 ^ 2
    + (1895785857810432 : R) * e1n ^ 2 * a2 * b3
    + (2527714477080576 : R) * e1n ^ 2 * a1 * b4
    + (3159643096350720 : R) * e1n ^ 2 * a0 * b5
    + (2202780303360 : R) * e1n * e3 ^ 3 * a2
    + (7801587892224 : R) * e1n * e3 ^ 2 * b3
    - (41075360252559360 : R) * e1n * a2 ^ 2 * a1
    + (453246976 : R) * e3 ^ 5
    - (169034404331520 : R) * e3 ^ 2 * a2 * a1
    - (722204136308736 : R) * e3 * a2 * b2
    - (1083306204463104 : R) * e3 * a1 * b3
    - (1444408272617472 : R) * e3 * a0 * b4
/-! ## Order `71` (MixedPair `h^17`, order-`61` tower `h^10`) -/
set_option maxHeartbeats 1600000000 in
/-- Frozen order-`71` coefficient of the MixedPair jet (`h^17` of `alignedSquareJetQuotient610`). -/
def alignedSquareMixedPairOrder71610 {R : Type*} [CommRing R] (w1 e1 e3 a2 a1 a0 b3 b2 b1 : R) : R :=
    - (20537680126279680 : R) * w1 ^ 2 * e1 * a1 * a0
    + (93908002406400 : R) * w1 * e1 * e3 ^ 2 * a0
    + (140428582060032 : R) * w1 * e1 * e3 * b1
    + (178425204572160 : R) * e1 ^ 3 * e3 * a0
    + (70214291030016 : R) * e1 ^ 3 * b1
    - (3042619277967360 : R) * e1 * e3 * a2 * a0
    - (1521309638983680 : R) * e1 * e3 * a1 ^ 2
    - (3249918613389312 : R) * e1 * a2 * b1
    - (6499837226778624 : R) * e1 * a1 * b2
    - (9749755840167936 : R) * e1 * a0 * b3
/-- Order-`71` coefficient of the MixedPair jet on `w₁ = 0` (frozen, no Taylor of `w₁`). -/
def alignedSquareW1ZeroOrder71610 {R : Type*} [CommRing R] (e1 e3 a2 a1 a0 b3 b2 b1 : R) : R :=
    (178425204572160 : R) * e1 ^ 3 * e3 * a0
    + (70214291030016 : R) * e1 ^ 3 * b1
    - (3042619277967360 : R) * e1 * e3 * a2 * a0
    - (1521309638983680 : R) * e1 * e3 * a1 ^ 2
    - (3249918613389312 : R) * e1 * a2 * b1
    - (6499837226778624 : R) * e1 * a1 * b2
    - (9749755840167936 : R) * e1 * a0 * b3
set_option maxHeartbeats 1600000000 in
/-- Order-`71` mixed coefficient after `w₁ = h w₁n`. -/
def alignedSquareW1PeelOrder71610 {R : Type*} [CommRing R] (w1n e1 e3 a2 a1 a0 b4 b3 b2 b1 : R) : R :=
    (11972302848 : R) * w1n ^ 9 * b4
    - (516534771916800 : R) * w1n ^ 7 * e1 ^ 4
    + (5177815799869440 : R) * w1n ^ 7 * e1 ^ 2 * a2
    - (3492560186818560 : R) * w1n ^ 7 * a2 ^ 2
    + (259751681280000 : R) * w1n ^ 6 * e1 ^ 3 * e3
    - (1714090051215360 : R) * w1n ^ 6 * e1 * e3 * a2
    + (18102121906176 : R) * w1n ^ 6 * e1 * b3
    - (41560269004800 : R) * w1n ^ 5 * e1 ^ 2 * e3 ^ 2
    + (126384519905280 : R) * w1n ^ 5 * e3 ^ 2 * a2
    - (6582589784064 : R) * w1n ^ 5 * e3 * b3
    + (4937359957770240 : R) * w1n ^ 4 * e1 ^ 3 * a1
    + (2257594859520 : R) * w1n ^ 4 * e1 * e3 ^ 3
    - (68696638385356800 : R) * w1n ^ 4 * e1 * a2 * a1
    - (624488216002560 : R) * w1n ^ 3 * e1 ^ 2 * e3 * a1
    + (579267900997632 : R) * w1n ^ 3 * e1 ^ 2 * b2
    - (23795466240 : R) * w1n ^ 3 * e3 ^ 4
    + (6338790162432000 : R) * w1n ^ 3 * e3 * a2 * a1
    - (1354132755578880 : R) * w1n ^ 3 * a2 * b2
    - (2031199133368320 : R) * w1n ^ 3 * a1 * b3
    - (2708265511157760 : R) * w1n ^ 3 * a0 * b4
    - (44606301143040 : R) * w1n ^ 2 * e1 * e3 ^ 2 * a1
    - (210642873090048 : R) * w1n ^ 2 * e1 * e3 * b2
    - (1070551227432960 : R) * w1n * e1 ^ 4 * a0
    + (22819644584755200 : R) * w1n * e1 ^ 2 * a2 * a0
    + (11409822292377600 : R) * w1n * e1 ^ 2 * a1 ^ 2
    + (3478074163200 : R) * w1n * e3 ^ 3 * a1
    + (15603175784448 : R) * w1n * e3 ^ 2 * b2
    - (37915717156208640 : R) * w1n * a2 ^ 2 * a0
    - (37915717156208640 : R) * w1n * a2 * a1 ^ 2
    + (178425204572160 : R) * e1 ^ 3 * e3 * a0
    + (70214291030016 : R) * e1 ^ 3 * b1
    - (3042619277967360 : R) * e1 * e3 * a2 * a0
    - (1521309638983680 : R) * e1 * e3 * a1 ^ 2
    - (3249918613389312 : R) * e1 * a2 * b1
    - (6499837226778624 : R) * e1 * a1 * b2
    - (9749755840167936 : R) * e1 * a0 * b3
set_option maxHeartbeats 1600000000 in
/-- Order-`71` coefficient on the `w₁ = 0` complement peel `w₁ = h w₁n`, `e₁ = h e₁b`, `e₃ = h e₃b`, `a₂ = h a₂b`. -/
def alignedSquareW1ComplementOrder71610 {R : Type*} [CommRing R] (w1n e1b e3b a2b a1 a0 b4 b3 : R) : R :=
    (11972302848 : R) * w1n ^ 9 * b4
    - (7470716977152 : R) * w1n ^ 7 * e1b * b4
    + (2681795837952 : R) * w1n ^ 6 * e3b * b4
    + (313770113040384 : R) * w1n ^ 5 * e1b ^ 2 * b4
    - (139453383573504 : R) * w1n ^ 4 * e1b * e3b * b4
    + (592433080565760 : R) * w1n ^ 4 * a2b * b3
    - (718396218408960 : R) * w1n ^ 3 * e1b ^ 3 * b4
    + (14302911135744 : R) * w1n ^ 3 * e3b ^ 2 * b4
    - (2031199133368320 : R) * w1n ^ 3 * a1 * b3
    - (2708265511157760 : R) * w1n ^ 3 * a0 * b4
    + (253551606497280 : R) * w1n ^ 2 * e1b ^ 2 * e3b * b4
    - (8531036360146944 : R) * w1n ^ 2 * e1b * a2b * b3
    + (160582684114944 : R) * w1n * e1b ^ 4 * b4
    - (22537920577536 : R) * w1n * e1b * e3b ^ 2 * b4
    + (11374715146862592 : R) * w1n * e1b * a1 * b3
    + (15166286862483456 : R) * w1n * e1b * a0 * b4
    + (1263857238540288 : R) * w1n * e3b * a2b * b3
    - (22537920577536 : R) * e1b ^ 3 * e3b * b4
    + (1895785857810432 : R) * e1b ^ 2 * a2b * b3
    + (385263599616 : R) * e3b ^ 3 * b4
    - (1083306204463104 : R) * e3b * a1 * b3
    - (1444408272617472 : R) * e3b * a0 * b4
/-- Order-`71` mixed coefficient on `μ = 0` after the pole-`21` `q₈` peel: `e₁ = h e₁n`, `b₈ = h b₈n`. -/
def alignedSquareMuZeroQ8Order71610 {R : Type*} [CommRing R] (w1 : R) : R :=
    0
/-! ## Order `72` (MixedPair `h^18`, order-`61` tower `h^11`) -/
/-- Frozen order-`72` coefficient of the MixedPair jet (`h^18` of `alignedSquareJetQuotient610`). -/
def alignedSquareMixedPairOrder72610 {R : Type*} [CommRing R] (w1 e1 e3 a2 a1 a0 b2 b1 : R) : R :=
    - (37915717156208640 : R) * w1 ^ 3 * a0 ^ 2
    - (2808571641200640 : R) * w1 * e3 * a1 * a0
    - (9749755840167936 : R) * w1 * a1 * b1
    - (19499511680335872 : R) * w1 * a0 * b2
    - (13691786750853120 : R) * e1 ^ 2 * a1 * a0
    - (2086844497920 : R) * e3 ^ 3 * a0
    - (6687075336192 : R) * e3 ^ 2 * b1
    + (113747151468625920 : R) * a2 * a1 * a0
    + (18957858578104320 : R) * a1 ^ 3
/-- Order-`72` coefficient of the MixedPair jet on `w₁ = 0` (frozen, no Taylor of `w₁`). -/
def alignedSquareW1ZeroOrder72610 {R : Type*} [CommRing R] (e1 e3 a2 a1 a0 b1 : R) : R :=
    - (13691786750853120 : R) * e1 ^ 2 * a1 * a0
    - (2086844497920 : R) * e3 ^ 3 * a0
    - (6687075336192 : R) * e3 ^ 2 * b1
    + (113747151468625920 : R) * a2 * a1 * a0
    + (18957858578104320 : R) * a1 ^ 3
set_option maxHeartbeats 1600000000 in
/-- Order-`72` mixed coefficient after `w₁ = h w₁n`. -/
def alignedSquareW1PeelOrder72610 {R : Type*} [CommRing R] (w1n e1 e3 a2 a1 a0 b3 b2 b1 : R) : R :=
    (205018291296000 : R) * w1n ^ 9 * e1 ^ 3
    - (472460881052160 : R) * w1n ^ 9 * e1 * a2
    - (118279783440000 : R) * w1n ^ 8 * e1 ^ 2 * e3
    + (118697068638720 : R) * w1n ^ 8 * e3 * a2
    - (44079842304 : R) * w1n ^ 8 * b3
    + (21307883950080 : R) * w1n ^ 7 * e1 * e3 ^ 2
    - (7713405230469120 : R) * w1n ^ 6 * e1 ^ 2 * a1
    - (1175644753920 : R) * w1n ^ 6 * e3 ^ 3
    + (14511867728117760 : R) * w1n ^ 6 * a2 * a1
    + (2274921358295040 : R) * w1n ^ 5 * e1 * e3 * a1
    - (39495538704384 : R) * w1n ^ 5 * e1 * b2
    - (141351107788800 : R) * w1n ^ 4 * e3 ^ 2 * a1
    + (14627977297920 : R) * w1n ^ 4 * e3 * b2
    - (1873464648007680 : R) * w1n ^ 3 * e1 ^ 3 * a0
    + (57049111461888000 : R) * w1n ^ 3 * e1 * a2 * a0
    + (28524555730944000 : R) * w1n ^ 3 * e1 * a1 ^ 2
    - (401456710287360 : R) * w1n ^ 2 * e1 ^ 2 * e3 * a0
    - (473946464452608 : R) * w1n ^ 2 * e1 ^ 2 * b1
    - (2281964458475520 : R) * w1n ^ 2 * e3 * a2 * a0
    - (1140982229237760 : R) * w1n ^ 2 * e3 * a1 ^ 2
    + (2437438960041984 : R) * w1n ^ 2 * a2 * b1
    + (4874877920083968 : R) * w1n ^ 2 * a1 * b2
    + (7312316880125952 : R) * w1n ^ 2 * a0 * b3
    + (93908002406400 : R) * w1n * e1 * e3 ^ 2 * a0
    + (140428582060032 : R) * w1n * e1 * e3 * b1
    - (13691786750853120 : R) * e1 ^ 2 * a1 * a0
    - (2086844497920 : R) * e3 ^ 3 * a0
    - (6687075336192 : R) * e3 ^ 2 * b1
    + (113747151468625920 : R) * a2 * a1 * a0
    + (18957858578104320 : R) * a1 ^ 3
set_option maxHeartbeats 1600000000 in
/-- Order-`72` coefficient on the `w₁ = 0` complement peel `w₁ = h w₁n`, `e₁ = h e₁b`, `e₃ = h e₃b`, `a₂ = h a₂b`. -/
def alignedSquareW1ComplementOrder72610 {R : Type*} [CommRing R] (w1n e1b e3b a2b a1 a0 b3 b2 : R) : R :=
    - (44079842304 : R) * w1n ^ 8 * b3
    + (18102121906176 : R) * w1n ^ 6 * e1b * b3
    - (6582589784064 : R) * w1n ^ 5 * e3b * b3
    - (470655169560576 : R) * w1n ^ 4 * e1b ^ 2 * b3
    + (193089300332544 : R) * w1n ^ 3 * e1b * e3b * b3
    + (28524555730944000 : R) * w1n ^ 3 * a2b ^ 3
    - (1354132755578880 : R) * w1n ^ 3 * a2b * b2
    + (570491114618880 : R) * w1n ^ 2 * e1b ^ 3 * b3
    - (17553572757504 : R) * w1n ^ 2 * e3b ^ 2 * b3
    - (30806520189419520 : R) * w1n ^ 2 * a2b ^ 2 * a1
    + (4874877920083968 : R) * w1n ^ 2 * a1 * b2
    + (7312316880125952 : R) * w1n ^ 2 * a0 * b3
    - (152130963898368 : R) * w1n * e1b ^ 2 * e3b * b3
    + (22819644584755200 : R) * w1n * e1b * a2b ^ 3
    + (7583143431241728 : R) * w1n * e1b * a2b * b2
    - (37915717156208640 : R) * w1n * a2b * a1 ^ 2
    - (38032740974592 : R) * e1b ^ 4 * b3
    + (7801587892224 : R) * e1b * e3b ^ 2 * b3
    - (41075360252559360 : R) * e1b * a2b ^ 2 * a1
    - (6499837226778624 : R) * e1b * a1 * b2
    - (9749755840167936 : R) * e1b * a0 * b3
    - (1521309638983680 : R) * e3b * a2b ^ 3
    - (722204136308736 : R) * e3b * a2b * b2
    + (18957858578104320 : R) * a1 ^ 3
set_option maxHeartbeats 1600000000 in
/-- Order-`72` mixed coefficient on `μ = 0` after the pole-`21` `q₈` peel: `e₁ = h e₁n`, `b₈ = h b₈n`. -/
def alignedSquareMuZeroQ8Order72610 {R : Type*} [CommRing R] (w1 e1n e3 a2 a1 a0 b3 b2 b1 : R) : R :=
    (39122296012800 : R) * w1 ^ 3 * e1n ^ 6
    - (1873464648007680 : R) * w1 ^ 3 * e1n ^ 3 * a0
    - (37915717156208640 : R) * w1 ^ 3 * a0 ^ 2
    - (26674292736000 : R) * w1 ^ 2 * e1n ^ 5 * e3
    + (1254552219648000 : R) * w1 ^ 2 * e1n ^ 4 * a1
    - (401456710287360 : R) * w1 ^ 2 * e1n ^ 2 * e3 * a0
    - (473946464452608 : R) * w1 ^ 2 * e1n ^ 2 * b1
    - (20537680126279680 : R) * w1 ^ 2 * e1n * a1 * a0
    + (408891093811200 : R) * w1 * e1n ^ 5 * a2
    + (4206698496000 : R) * w1 * e1n ^ 4 * e3 ^ 2
    - (475800545525760 : R) * w1 * e1n ^ 3 * e3 * a1
    - (304261927796736 : R) * w1 * e1n ^ 3 * b2
    + (22819644584755200 : R) * w1 * e1n ^ 2 * a2 * a0
    + (11409822292377600 : R) * w1 * e1n ^ 2 * a1 ^ 2
    + (93908002406400 : R) * w1 * e1n * e3 ^ 2 * a0
    + (140428582060032 : R) * w1 * e1n * e3 * b1
    - (2808571641200640 : R) * w1 * e3 * a1 * a0
    - (9749755840167936 : R) * w1 * a1 * b1
    - (19499511680335872 : R) * w1 * a0 * b2
    - (61953196032000 : R) * e1n ^ 4 * e3 * a2
    - (38032740974592 : R) * e1n ^ 4 * b3
    - (169967616000 : R) * e1n ^ 3 * e3 ^ 3
    + (4817480523448320 : R) * e1n ^ 3 * a2 * a1
    + (29737534095360 : R) * e1n ^ 2 * e3 ^ 2 * a1
    + (46809527353344 : R) * e1n ^ 2 * e3 * b2
    - (3042619277967360 : R) * e1n * e3 * a2 * a0
    - (1521309638983680 : R) * e1n * e3 * a1 ^ 2
    - (3249918613389312 : R) * e1n * a2 * b1
    - (6499837226778624 : R) * e1n * a1 * b2
    - (9749755840167936 : R) * e1n * a0 * b3
    - (2086844497920 : R) * e3 ^ 3 * a0
    - (6687075336192 : R) * e3 ^ 2 * b1
    + (113747151468625920 : R) * a2 * a1 * a0
    + (18957858578104320 : R) * a1 ^ 3
/-! ## Order `73` (MixedPair `h^19`, order-`61` tower `h^12`) -/
/-- Frozen order-`73` coefficient of the MixedPair jet (`h^19` of `alignedSquareJetQuotient610`). -/
def alignedSquareMixedPairOrder73610 {R : Type*} [CommRing R] (w1 e1 a0 : R) : R :=
    - (12638572385402880 : R) * w1 * e1 * a0 ^ 2
/-- Order-`73` coefficient of the MixedPair jet on `w₁ = 0` (frozen, no Taylor of `w₁`). -/
def alignedSquareW1ZeroOrder73610 {R : Type*} [CommRing R] (e1 : R) : R :=
    0
set_option maxHeartbeats 1600000000 in
/-- Order-`73` mixed coefficient after `w₁ = h w₁n`. -/
def alignedSquareW1PeelOrder73610 {R : Type*} [CommRing R] (w1n e1 e3 a2 a1 a0 b2 b1 : R) : R :=
    - (14193574012800 : R) * w1n ^ 11 * e1 ^ 2
    + (2062916968320 : R) * w1n ^ 11 * a2
    + (7517337347520 : R) * w1n ^ 10 * e1 * e3
    - (972141730560 : R) * w1n ^ 9 * e3 ^ 2
    + (1068273617748480 : R) * w1n ^ 8 * e1 * a1
    - (258708161986560 : R) * w1n ^ 7 * e3 * a1
    + (156728328192 : R) * w1n ^ 7 * b2
    + (10237146112327680 : R) * w1n ^ 5 * e1 ^ 2 * a0
    - (28239310173634560 : R) * w1n ^ 5 * a2 * a0
    - (14119655086817280 : R) * w1n ^ 5 * a1 ^ 2
    - (2544319940198400 : R) * w1n ^ 4 * e1 * e3 * a0
    + (65825897840640 : R) * w1n ^ 4 * e1 * b1
    + (117385003008000 : R) * w1n ^ 3 * e3 ^ 2 * a0
    - (25076532510720 : R) * w1n ^ 3 * e3 * b1
    - (20537680126279680 : R) * w1n ^ 2 * e1 * a1 * a0
    - (2808571641200640 : R) * w1n * e3 * a1 * a0
    - (9749755840167936 : R) * w1n * a1 * b1
    - (19499511680335872 : R) * w1n * a0 * b2
set_option maxHeartbeats 1600000000 in
/-- Order-`73` coefficient on the `w₁ = 0` complement peel `w₁ = h w₁n`, `e₁ = h e₁b`, `e₃ = h e₃b`, `a₂ = h a₂b`. -/
def alignedSquareW1ComplementOrder73610 {R : Type*} [CommRing R] (w1n e1b e3b a2b a1 a0 b2 b1 : R) : R :=
    - (3492560186818560 : R) * w1n ^ 7 * a2b ^ 2
    + (156728328192 : R) * w1n ^ 7 * b2
    + (14511867728117760 : R) * w1n ^ 6 * a2b * a1
    + (30711438336983040 : R) * w1n ^ 5 * e1b * a2b ^ 2
    - (39495538704384 : R) * w1n ^ 5 * e1b * b2
    - (14119655086817280 : R) * w1n ^ 5 * a1 ^ 2
    - (68696638385356800 : R) * w1n ^ 4 * e1b * a2b * a1
    - (3816479910297600 : R) * w1n ^ 4 * e3b * a2b ^ 2
    + (14627977297920 : R) * w1n ^ 4 * e3b * b2
    - (8430590916034560 : R) * w1n ^ 3 * e1b ^ 2 * a2b ^ 2
    + (579267900997632 : R) * w1n ^ 3 * e1b ^ 2 * b2
    + (28524555730944000 : R) * w1n ^ 3 * e1b * a1 ^ 2
    + (6338790162432000 : R) * w1n ^ 3 * e3b * a2b * a1
    - (10839331177758720 : R) * w1n ^ 2 * e1b ^ 2 * a2b * a1
    - (1204370130862080 : R) * w1n ^ 2 * e1b * e3b * a2b ^ 2
    - (210642873090048 : R) * w1n ^ 2 * e1b * e3b * b2
    - (1140982229237760 : R) * w1n ^ 2 * e3b * a1 ^ 2
    + (2437438960041984 : R) * w1n ^ 2 * a2b * b1
    - (6423307364597760 : R) * w1n * e1b ^ 3 * a2b ^ 2
    - (304261927796736 : R) * w1n * e1b ^ 3 * b2
    + (11409822292377600 : R) * w1n * e1b ^ 2 * a1 ^ 2
    + (5071032129945600 : R) * w1n * e1b * e3b * a2b * a1
    + (140862003609600 : R) * w1n * e3b ^ 2 * a2b ^ 2
    + (15603175784448 : R) * w1n * e3b ^ 2 * b2
    - (37915717156208640 : R) * w1n * a2b ^ 2 * a0
    - (9749755840167936 : R) * w1n * a1 * b1
    - (19499511680335872 : R) * w1n * a0 * b2
    + (4817480523448320 : R) * e1b ^ 3 * a2b * a1
    + (802913420574720 : R) * e1b ^ 2 * e3b * a2b ^ 2
    + (46809527353344 : R) * e1b ^ 2 * e3b * b2
    - (1521309638983680 : R) * e1b * e3b * a1 ^ 2
    - (3249918613389312 : R) * e1b * a2b * b1
    - (169034404331520 : R) * e3b ^ 2 * a2b * a1
    + (113747151468625920 : R) * a2b * a1 * a0
/-- Order-`73` mixed coefficient on `μ = 0` after the pole-`21` `q₈` peel: `e₁ = h e₁n`, `b₈ = h b₈n`. -/
def alignedSquareMuZeroQ8Order73610 {R : Type*} [CommRing R] (w1 : R) : R :=
    0
/-! ## Order `74` (MixedPair `h^20`, order-`61` tower `h^13`) -/
/-- Frozen order-`74` coefficient of the MixedPair jet (`h^20` of `alignedSquareJetQuotient610`). -/
def alignedSquareMixedPairOrder74610 {R : Type*} [CommRing R] (e3 a0 b1 : R) : R :=
    (2106428730900480 : R) * e3 * a0 ^ 2
    + (58498535041007616 : R) * a0 * b1
/-- Order-`74` coefficient of the MixedPair jet on `w₁ = 0` (frozen, no Taylor of `w₁`). -/
def alignedSquareW1ZeroOrder74610 {R : Type*} [CommRing R] (e3 a0 b1 : R) : R :=
    (2106428730900480 : R) * e3 * a0 ^ 2
    + (58498535041007616 : R) * a0 * b1
set_option maxHeartbeats 1600000000 in
/-- Order-`74` mixed coefficient after `w₁ = h w₁n`. -/
def alignedSquareW1PeelOrder74610 {R : Type*} [CommRing R] (w1n e1 e3 a1 a0 b1 : R) : R :=
    (69754744080 : R) * w1n ^ 13 * e1
    - (24284496600 : R) * w1n ^ 12 * e3
    - (6522826527360 : R) * w1n ^ 10 * a1
    - (2328373457879040 : R) * w1n ^ 7 * e1 * a0
    + (537476582522880 : R) * w1n ^ 6 * e3 * a0
    - (470184984576 : R) * w1n ^ 6 * b1
    + (49961856461045760 : R) * w1n ^ 4 * a1 * a0
    - (12638572385402880 : R) * w1n * e1 * a0 ^ 2
    + (2106428730900480 : R) * e3 * a0 ^ 2
    + (58498535041007616 : R) * a0 * b1
set_option maxHeartbeats 1600000000 in
/-- Order-`74` coefficient on the `w₁ = 0` complement peel `w₁ = h w₁n`, `e₁ = h e₁b`, `e₃ = h e₃b`, `a₂ = h a₂b`. -/
def alignedSquareW1ComplementOrder74610 {R : Type*} [CommRing R] (w1n e1b e3b a2b a1 a0 b1 : R) : R :=
    (2062916968320 : R) * w1n ^ 11 * a2b
    - (6522826527360 : R) * w1n ^ 10 * a1
    - (472460881052160 : R) * w1n ^ 9 * e1b * a2b
    + (1068273617748480 : R) * w1n ^ 8 * e1b * a1
    + (118697068638720 : R) * w1n ^ 8 * e3b * a2b
    + (5177815799869440 : R) * w1n ^ 7 * e1b ^ 2 * a2b
    - (258708161986560 : R) * w1n ^ 7 * e3b * a1
    - (7713405230469120 : R) * w1n ^ 6 * e1b ^ 2 * a1
    - (1714090051215360 : R) * w1n ^ 6 * e1b * e3b * a2b
    - (470184984576 : R) * w1n ^ 6 * b1
    - (6732763578777600 : R) * w1n ^ 5 * e1b ^ 3 * a2b
    + (2274921358295040 : R) * w1n ^ 5 * e1b * e3b * a1
    + (126384519905280 : R) * w1n ^ 5 * e3b ^ 2 * a2b
    - (28239310173634560 : R) * w1n ^ 5 * a2b * a0
    + (4937359957770240 : R) * w1n ^ 4 * e1b ^ 3 * a1
    + (1645786652590080 : R) * w1n ^ 4 * e1b ^ 2 * e3b * a2b
    + (65825897840640 : R) * w1n ^ 4 * e1b * b1
    - (141351107788800 : R) * w1n ^ 4 * e3b ^ 2 * a1
    + (49961856461045760 : R) * w1n ^ 4 * a1 * a0
    - (418184073216000 : R) * w1n ^ 3 * e1b ^ 4 * a2b
    - (624488216002560 : R) * w1n ^ 3 * e1b ^ 2 * e3b * a1
    - (69387579555840 : R) * w1n ^ 3 * e1b * e3b ^ 2 * a2b
    + (57049111461888000 : R) * w1n ^ 3 * e1b * a2b * a0
    - (25076532510720 : R) * w1n ^ 3 * e3b * b1
    + (1254552219648000 : R) * w1n ^ 2 * e1b ^ 4 * a1
    + (557578764288000 : R) * w1n ^ 2 * e1b ^ 3 * e3b * a2b
    - (473946464452608 : R) * w1n ^ 2 * e1b ^ 2 * b1
    - (44606301143040 : R) * w1n ^ 2 * e1b * e3b ^ 2 * a1
    - (20537680126279680 : R) * w1n ^ 2 * e1b * a1 * a0
    - (1652085227520 : R) * w1n ^ 2 * e3b ^ 3 * a2b
    - (2281964458475520 : R) * w1n ^ 2 * e3b * a2b * a0
    + (408891093811200 : R) * w1n * e1b ^ 5 * a2b
    - (475800545525760 : R) * w1n * e1b ^ 3 * e3b * a1
    - (79300090920960 : R) * w1n * e1b ^ 2 * e3b ^ 2 * a2b
    + (22819644584755200 : R) * w1n * e1b ^ 2 * a2b * a0
    + (140428582060032 : R) * w1n * e1b * e3b * b1
    + (3478074163200 : R) * w1n * e3b ^ 3 * a1
    - (2808571641200640 : R) * w1n * e3b * a1 * a0
    - (111515752857600 : R) * e1b ^ 5 * a1
    - (61953196032000 : R) * e1b ^ 4 * e3b * a2b
    + (70214291030016 : R) * e1b ^ 3 * b1
    + (29737534095360 : R) * e1b ^ 2 * e3b ^ 2 * a1
    - (13691786750853120 : R) * e1b ^ 2 * a1 * a0
    + (2202780303360 : R) * e1b * e3b ^ 3 * a2b
    - (3042619277967360 : R) * e1b * e3b * a2b * a0
    - (6687075336192 : R) * e3b ^ 2 * b1
    + (58498535041007616 : R) * a0 * b1
set_option maxHeartbeats 1600000000 in
/-- Order-`74` mixed coefficient on `μ = 0` after the pole-`21` `q₈` peel: `e₁ = h e₁n`, `b₈ = h b₈n`. -/
def alignedSquareMuZeroQ8Order74610 {R : Type*} [CommRing R] (w1 e1n e3 a1 a0 b1 : R) : R :=
    - (7113144729600 : R) * w1 * e1n ^ 7
    - (1070551227432960 : R) * w1 * e1n ^ 4 * a0
    - (12638572385402880 : R) * w1 * e1n * a0 ^ 2
    + (1185524121600 : R) * e1n ^ 6 * e3
    - (111515752857600 : R) * e1n ^ 5 * a1
    + (178425204572160 : R) * e1n ^ 3 * e3 * a0
    + (70214291030016 : R) * e1n ^ 3 * b1
    - (13691786750853120 : R) * e1n ^ 2 * a1 * a0
    + (2106428730900480 : R) * e3 * a0 ^ 2
    + (58498535041007616 : R) * a0 * b1
/-! ## Order `75` (MixedPair `h^21`, order-`61` tower `h^14`) -/
/-- Frozen order-`75` coefficient of the MixedPair jet (`h^21` of `alignedSquareJetQuotient610`). -/
def alignedSquareMixedPairOrder75610 {R : Type*} [CommRing R] (w1 : R) : R :=
    0
/-- Order-`75` coefficient of the MixedPair jet on `w₁ = 0` (frozen, no Taylor of `w₁`). -/
def alignedSquareW1ZeroOrder75610 {R : Type*} [CommRing R] (e1 : R) : R :=
    0
/-- Order-`75` mixed coefficient after `w₁ = h w₁n`. -/
def alignedSquareW1PeelOrder75610 {R : Type*} [CommRing R] (w1n a0 : R) : R :=
    - (26372304 : R) * w1n ^ 15
    + (20751991603200 : R) * w1n ^ 9 * a0
    - (37915717156208640 : R) * w1n ^ 3 * a0 ^ 2
set_option maxHeartbeats 1600000000 in
/-- Order-`75` coefficient on the `w₁ = 0` complement peel `w₁ = h w₁n`, `e₁ = h e₁b`, `e₃ = h e₃b`, `a₂ = h a₂b`. -/
def alignedSquareW1ComplementOrder75610 {R : Type*} [CommRing R] (w1n e1b e3b a0 : R) : R :=
    - (26372304 : R) * w1n ^ 15
    + (69754744080 : R) * w1n ^ 13 * e1b
    - (24284496600 : R) * w1n ^ 12 * e3b
    - (14193574012800 : R) * w1n ^ 11 * e1b ^ 2
    + (7517337347520 : R) * w1n ^ 10 * e1b * e3b
    + (205018291296000 : R) * w1n ^ 9 * e1b ^ 3
    - (972141730560 : R) * w1n ^ 9 * e3b ^ 2
    + (20751991603200 : R) * w1n ^ 9 * a0
    - (118279783440000 : R) * w1n ^ 8 * e1b ^ 2 * e3b
    - (516534771916800 : R) * w1n ^ 7 * e1b ^ 4
    + (21307883950080 : R) * w1n ^ 7 * e1b * e3b ^ 2
    - (2328373457879040 : R) * w1n ^ 7 * e1b * a0
    + (259751681280000 : R) * w1n ^ 6 * e1b ^ 3 * e3b
    - (1175644753920 : R) * w1n ^ 6 * e3b ^ 3
    + (537476582522880 : R) * w1n ^ 6 * e3b * a0
    + (208859712122880 : R) * w1n ^ 5 * e1b ^ 5
    - (41560269004800 : R) * w1n ^ 5 * e1b ^ 2 * e3b ^ 2
    + (10237146112327680 : R) * w1n ^ 5 * e1b ^ 2 * a0
    - (46787569920000 : R) * w1n ^ 4 * e1b ^ 4 * e3b
    + (2257594859520 : R) * w1n ^ 4 * e1b * e3b ^ 3
    - (2544319940198400 : R) * w1n ^ 4 * e1b * e3b * a0
    + (39122296012800 : R) * w1n ^ 3 * e1b ^ 6
    - (3441844224000 : R) * w1n ^ 3 * e1b ^ 3 * e3b ^ 2
    - (1873464648007680 : R) * w1n ^ 3 * e1b ^ 3 * a0
    - (23795466240 : R) * w1n ^ 3 * e3b ^ 4
    + (117385003008000 : R) * w1n ^ 3 * e3b ^ 2 * a0
    - (37915717156208640 : R) * w1n ^ 3 * a0 ^ 2
    - (26674292736000 : R) * w1n ^ 2 * e1b ^ 5 * e3b
    + (1147281408000 : R) * w1n ^ 2 * e1b ^ 2 * e3b ^ 3
    - (401456710287360 : R) * w1n ^ 2 * e1b ^ 2 * e3b * a0
    - (7113144729600 : R) * w1n * e1b ^ 7
    + (4206698496000 : R) * w1n * e1b ^ 4 * e3b ^ 2
    - (1070551227432960 : R) * w1n * e1b ^ 4 * a0
    - (54389637120 : R) * w1n * e1b * e3b ^ 4
    + (93908002406400 : R) * w1n * e1b * e3b ^ 2 * a0
    - (12638572385402880 : R) * w1n * e1b * a0 ^ 2
    + (1185524121600 : R) * e1b ^ 6 * e3b
    - (169967616000 : R) * e1b ^ 3 * e3b ^ 3
    + (178425204572160 : R) * e1b ^ 3 * e3b * a0
    + (453246976 : R) * e3b ^ 5
    - (2086844497920 : R) * e3b ^ 3 * a0
    + (2106428730900480 : R) * e3b * a0 ^ 2
/-- Order-`75` mixed coefficient on `μ = 0` after the pole-`21` `q₈` peel: `e₁ = h e₁n`, `b₈ = h b₈n`. -/
def alignedSquareMuZeroQ8Order75610 {R : Type*} [CommRing R] (w1 : R) : R :=
    0
/-! ## Order-`68` Plus remainders as orders `69`–`75` -/
set_option maxHeartbeats 1600000000 in
/-- The order-`68` Plus remainder is the order-`69`–`75` tower. -/
theorem alignedSquareW1ZeroOrder68Plus610_of_orders69to75
    {R : Type*} [CommRing R] (h e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) :
    alignedSquareW1ZeroOrder68Plus610 h e1 e3 a2 a1 a0 b4 b3 b2 b1 =
      alignedSquareW1ZeroOrder69610 e1 e3 a2 a1 b3
        + h * alignedSquareW1ZeroOrder70610 e1 e3 a2 a1 a0 b4 b3 b2
        + h ^ 2 * alignedSquareW1ZeroOrder71610 e1 e3 a2 a1 a0 b3 b2 b1
        + h ^ 3 * alignedSquareW1ZeroOrder72610 e1 e3 a2 a1 a0 b1
        + h ^ 4 * alignedSquareW1ZeroOrder73610 e1
        + h ^ 5 * alignedSquareW1ZeroOrder74610 e3 a0 b1
        + h ^ 6 * alignedSquareW1ZeroOrder75610 e1 := by
  simp only [alignedSquareW1ZeroOrder68Plus610, alignedSquareW1ZeroOrder69610, alignedSquareW1ZeroOrder70610, alignedSquareW1ZeroOrder71610, alignedSquareW1ZeroOrder72610, alignedSquareW1ZeroOrder73610, alignedSquareW1ZeroOrder74610, alignedSquareW1ZeroOrder75610]
  ring

#print axioms alignedSquareW1ZeroOrder68Plus610_of_orders69to75
set_option maxHeartbeats 1600000000 in
/-- The order-`68` Plus remainder is the order-`69`–`75` tower. -/
theorem alignedSquareW1PeelOrder68Plus610_of_orders69to75
    {R : Type*} [CommRing R] (h w1n e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) :
    alignedSquareW1PeelOrder68Plus610 h w1n e1 e3 a2 a1 a0 b6 b5 b4 b3 b2 b1 =
      alignedSquareW1PeelOrder69610 w1n e1 e3 a2 a1 a0 b6 b5 b4 b3
        + h * alignedSquareW1PeelOrder70610 w1n e1 e3 a2 a1 a0 b5 b4 b3 b2
        + h ^ 2 * alignedSquareW1PeelOrder71610 w1n e1 e3 a2 a1 a0 b4 b3 b2 b1
        + h ^ 3 * alignedSquareW1PeelOrder72610 w1n e1 e3 a2 a1 a0 b3 b2 b1
        + h ^ 4 * alignedSquareW1PeelOrder73610 w1n e1 e3 a2 a1 a0 b2 b1
        + h ^ 5 * alignedSquareW1PeelOrder74610 w1n e1 e3 a1 a0 b1
        + h ^ 6 * alignedSquareW1PeelOrder75610 w1n a0 := by
  simp only [alignedSquareW1PeelOrder68Plus610, alignedSquareW1PeelOrder69610, alignedSquareW1PeelOrder70610, alignedSquareW1PeelOrder71610, alignedSquareW1PeelOrder72610, alignedSquareW1PeelOrder73610, alignedSquareW1PeelOrder74610, alignedSquareW1PeelOrder75610]
  ring

#print axioms alignedSquareW1PeelOrder68Plus610_of_orders69to75
set_option maxHeartbeats 1600000000 in
/-- The order-`68` Plus remainder is the order-`69`–`75` tower. -/
theorem alignedSquareW1ComplementOrder68Plus610_of_orders69to75
    {R : Type*} [CommRing R] (h w1n e1b e3b a2b a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) :
    alignedSquareW1ComplementOrder68Plus610 h w1n e1b e3b a2b a1 a0 b6 b5 b4 b3 b2 b1 =
      alignedSquareW1ComplementOrder69610 w1n e1b e3b a2b a1 a0 b6 b5 b4
        + h * alignedSquareW1ComplementOrder70610 w1n e1b e3b a2b a1 a0 b5 b4 b3
        + h ^ 2 * alignedSquareW1ComplementOrder71610 w1n e1b e3b a2b a1 a0 b4 b3
        + h ^ 3 * alignedSquareW1ComplementOrder72610 w1n e1b e3b a2b a1 a0 b3 b2
        + h ^ 4 * alignedSquareW1ComplementOrder73610 w1n e1b e3b a2b a1 a0 b2 b1
        + h ^ 5 * alignedSquareW1ComplementOrder74610 w1n e1b e3b a2b a1 a0 b1
        + h ^ 6 * alignedSquareW1ComplementOrder75610 w1n e1b e3b a0 := by
  simp only [alignedSquareW1ComplementOrder68Plus610, alignedSquareW1ComplementOrder69610, alignedSquareW1ComplementOrder70610, alignedSquareW1ComplementOrder71610, alignedSquareW1ComplementOrder72610, alignedSquareW1ComplementOrder73610, alignedSquareW1ComplementOrder74610, alignedSquareW1ComplementOrder75610]
  ring

#print axioms alignedSquareW1ComplementOrder68Plus610_of_orders69to75
set_option maxHeartbeats 1600000000 in
/-- The order-`68` Plus remainder is the order-`69`–`75` tower. -/
theorem alignedSquareMuZeroQ8Order68Plus610_of_orders69to75
    {R : Type*} [CommRing R] (h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 : R) :
    alignedSquareMuZeroQ8Order68Plus610 h w1 e1n e3 a2 a1 a0 b5 b4 b3 b2 b1 =
      alignedSquareMuZeroQ8Order69610 w1
        + h * alignedSquareMuZeroQ8Order70610 w1 e1n e3 a2 a1 a0 b5 b4 b3 b2 b1
        + h ^ 2 * alignedSquareMuZeroQ8Order71610 w1
        + h ^ 3 * alignedSquareMuZeroQ8Order72610 w1 e1n e3 a2 a1 a0 b3 b2 b1
        + h ^ 4 * alignedSquareMuZeroQ8Order73610 w1
        + h ^ 5 * alignedSquareMuZeroQ8Order74610 w1 e1n e3 a1 a0 b1
        + h ^ 6 * alignedSquareMuZeroQ8Order75610 w1 := by
  simp only [alignedSquareMuZeroQ8Order68Plus610, alignedSquareMuZeroQ8Order69610, alignedSquareMuZeroQ8Order70610, alignedSquareMuZeroQ8Order71610, alignedSquareMuZeroQ8Order72610, alignedSquareMuZeroQ8Order73610, alignedSquareMuZeroQ8Order74610, alignedSquareMuZeroQ8Order75610]
  ring

#print axioms alignedSquareMuZeroQ8Order68Plus610_of_orders69to75
/-! ## Identically vanishing coefficients -/
theorem alignedSquareMuZeroQ8Order69610_eq_zero {R : Type*} [CommRing R]
    (w1 : R) :
    alignedSquareMuZeroQ8Order69610 w1 = 0 :=
  rfl

#print axioms alignedSquareMuZeroQ8Order69610_eq_zero
theorem alignedSquareMuZeroQ8Order71610_eq_zero {R : Type*} [CommRing R]
    (w1 : R) :
    alignedSquareMuZeroQ8Order71610 w1 = 0 :=
  rfl

#print axioms alignedSquareMuZeroQ8Order71610_eq_zero
theorem alignedSquareW1ZeroOrder73610_eq_zero {R : Type*} [CommRing R]
    (e1 : R) :
    alignedSquareW1ZeroOrder73610 e1 = 0 :=
  rfl

#print axioms alignedSquareW1ZeroOrder73610_eq_zero
theorem alignedSquareMuZeroQ8Order73610_eq_zero {R : Type*} [CommRing R]
    (w1 : R) :
    alignedSquareMuZeroQ8Order73610 w1 = 0 :=
  rfl

#print axioms alignedSquareMuZeroQ8Order73610_eq_zero
theorem alignedSquareMixedPairOrder75610_eq_zero {R : Type*} [CommRing R]
    (w1 : R) :
    alignedSquareMixedPairOrder75610 w1 = 0 :=
  rfl

#print axioms alignedSquareMixedPairOrder75610_eq_zero
theorem alignedSquareW1ZeroOrder75610_eq_zero {R : Type*} [CommRing R]
    (e1 : R) :
    alignedSquareW1ZeroOrder75610 e1 = 0 :=
  rfl

#print axioms alignedSquareW1ZeroOrder75610_eq_zero
theorem alignedSquareMuZeroQ8Order75610_eq_zero {R : Type*} [CommRing R]
    (w1 : R) :
    alignedSquareMuZeroQ8Order75610 w1 = 0 :=
  rfl

#print axioms alignedSquareMuZeroQ8Order75610_eq_zero
/-! ## Ring maps and evaluation -/
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareMixedPairOrder69610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (w1 e1 e3 a2 a1 a0 b4 b3 b2 b1 : R) :
    phi (alignedSquareMixedPairOrder69610 w1 e1 e3 a2 a1 a0 b4 b3 b2 b1) =
      alignedSquareMixedPairOrder69610 (phi w1) (phi e1) (phi e3) (phi a2) (phi a1) (phi a0) (phi b4) (phi b3) (phi b2) (phi b1) := by
  simp only [alignedSquareMixedPairOrder69610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareMixedPairOrder69610
theorem alignedSquareMixedPairOrder69610_eval
    {k : Type*} [CommRing k]
    (w1 e1 e3 a2 a1 a0 b4 b3 b2 b1 : k[X]) (a : k) :
    (alignedSquareMixedPairOrder69610 w1 e1 e3 a2 a1 a0 b4 b3 b2 b1).eval a =
      alignedSquareMixedPairOrder69610 (w1.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b4.eval a) (b3.eval a) (b2.eval a) (b1.eval a) :=
  map_alignedSquareMixedPairOrder69610 (Polynomial.evalRingHom a) w1 e1 e3 a2 a1 a0 b4 b3 b2 b1

#print axioms alignedSquareMixedPairOrder69610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareW1ZeroOrder69610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (e1 e3 a2 a1 b3 : R) :
    phi (alignedSquareW1ZeroOrder69610 e1 e3 a2 a1 b3) =
      alignedSquareW1ZeroOrder69610 (phi e1) (phi e3) (phi a2) (phi a1) (phi b3) := by
  simp only [alignedSquareW1ZeroOrder69610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareW1ZeroOrder69610
theorem alignedSquareW1ZeroOrder69610_eval
    {k : Type*} [CommRing k]
    (e1 e3 a2 a1 b3 : k[X]) (a : k) :
    (alignedSquareW1ZeroOrder69610 e1 e3 a2 a1 b3).eval a =
      alignedSquareW1ZeroOrder69610 (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (b3.eval a) :=
  map_alignedSquareW1ZeroOrder69610 (Polynomial.evalRingHom a) e1 e3 a2 a1 b3

#print axioms alignedSquareW1ZeroOrder69610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareW1PeelOrder69610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (w1n e1 e3 a2 a1 a0 b6 b5 b4 b3 : R) :
    phi (alignedSquareW1PeelOrder69610 w1n e1 e3 a2 a1 a0 b6 b5 b4 b3) =
      alignedSquareW1PeelOrder69610 (phi w1n) (phi e1) (phi e3) (phi a2) (phi a1) (phi a0) (phi b6) (phi b5) (phi b4) (phi b3) := by
  simp only [alignedSquareW1PeelOrder69610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareW1PeelOrder69610
theorem alignedSquareW1PeelOrder69610_eval
    {k : Type*} [CommRing k]
    (w1n e1 e3 a2 a1 a0 b6 b5 b4 b3 : k[X]) (a : k) :
    (alignedSquareW1PeelOrder69610 w1n e1 e3 a2 a1 a0 b6 b5 b4 b3).eval a =
      alignedSquareW1PeelOrder69610 (w1n.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b6.eval a) (b5.eval a) (b4.eval a) (b3.eval a) :=
  map_alignedSquareW1PeelOrder69610 (Polynomial.evalRingHom a) w1n e1 e3 a2 a1 a0 b6 b5 b4 b3

#print axioms alignedSquareW1PeelOrder69610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareW1ComplementOrder69610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (w1n e1b e3b a2b a1 a0 b6 b5 b4 : R) :
    phi (alignedSquareW1ComplementOrder69610 w1n e1b e3b a2b a1 a0 b6 b5 b4) =
      alignedSquareW1ComplementOrder69610 (phi w1n) (phi e1b) (phi e3b) (phi a2b) (phi a1) (phi a0) (phi b6) (phi b5) (phi b4) := by
  simp only [alignedSquareW1ComplementOrder69610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareW1ComplementOrder69610
theorem alignedSquareW1ComplementOrder69610_eval
    {k : Type*} [CommRing k]
    (w1n e1b e3b a2b a1 a0 b6 b5 b4 : k[X]) (a : k) :
    (alignedSquareW1ComplementOrder69610 w1n e1b e3b a2b a1 a0 b6 b5 b4).eval a =
      alignedSquareW1ComplementOrder69610 (w1n.eval a) (e1b.eval a) (e3b.eval a) (a2b.eval a) (a1.eval a) (a0.eval a) (b6.eval a) (b5.eval a) (b4.eval a) :=
  map_alignedSquareW1ComplementOrder69610 (Polynomial.evalRingHom a) w1n e1b e3b a2b a1 a0 b6 b5 b4

#print axioms alignedSquareW1ComplementOrder69610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareMuZeroQ8Order69610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (w1 : R) :
    phi (alignedSquareMuZeroQ8Order69610 w1) =
      alignedSquareMuZeroQ8Order69610 (phi w1) := by
  simp only [alignedSquareMuZeroQ8Order69610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareMuZeroQ8Order69610
theorem alignedSquareMuZeroQ8Order69610_eval
    {k : Type*} [CommRing k]
    (w1 : k[X]) (a : k) :
    (alignedSquareMuZeroQ8Order69610 w1).eval a =
      alignedSquareMuZeroQ8Order69610 (w1.eval a) :=
  map_alignedSquareMuZeroQ8Order69610 (Polynomial.evalRingHom a) w1

#print axioms alignedSquareMuZeroQ8Order69610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareMixedPairOrder70610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (w1 e1 e3 a2 a1 a0 b4 b3 b2 b1 : R) :
    phi (alignedSquareMixedPairOrder70610 w1 e1 e3 a2 a1 a0 b4 b3 b2 b1) =
      alignedSquareMixedPairOrder70610 (phi w1) (phi e1) (phi e3) (phi a2) (phi a1) (phi a0) (phi b4) (phi b3) (phi b2) (phi b1) := by
  simp only [alignedSquareMixedPairOrder70610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareMixedPairOrder70610
theorem alignedSquareMixedPairOrder70610_eval
    {k : Type*} [CommRing k]
    (w1 e1 e3 a2 a1 a0 b4 b3 b2 b1 : k[X]) (a : k) :
    (alignedSquareMixedPairOrder70610 w1 e1 e3 a2 a1 a0 b4 b3 b2 b1).eval a =
      alignedSquareMixedPairOrder70610 (w1.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b4.eval a) (b3.eval a) (b2.eval a) (b1.eval a) :=
  map_alignedSquareMixedPairOrder70610 (Polynomial.evalRingHom a) w1 e1 e3 a2 a1 a0 b4 b3 b2 b1

#print axioms alignedSquareMixedPairOrder70610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareW1ZeroOrder70610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (e1 e3 a2 a1 a0 b4 b3 b2 : R) :
    phi (alignedSquareW1ZeroOrder70610 e1 e3 a2 a1 a0 b4 b3 b2) =
      alignedSquareW1ZeroOrder70610 (phi e1) (phi e3) (phi a2) (phi a1) (phi a0) (phi b4) (phi b3) (phi b2) := by
  simp only [alignedSquareW1ZeroOrder70610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareW1ZeroOrder70610
theorem alignedSquareW1ZeroOrder70610_eval
    {k : Type*} [CommRing k]
    (e1 e3 a2 a1 a0 b4 b3 b2 : k[X]) (a : k) :
    (alignedSquareW1ZeroOrder70610 e1 e3 a2 a1 a0 b4 b3 b2).eval a =
      alignedSquareW1ZeroOrder70610 (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b4.eval a) (b3.eval a) (b2.eval a) :=
  map_alignedSquareW1ZeroOrder70610 (Polynomial.evalRingHom a) e1 e3 a2 a1 a0 b4 b3 b2

#print axioms alignedSquareW1ZeroOrder70610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareW1PeelOrder70610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (w1n e1 e3 a2 a1 a0 b5 b4 b3 b2 : R) :
    phi (alignedSquareW1PeelOrder70610 w1n e1 e3 a2 a1 a0 b5 b4 b3 b2) =
      alignedSquareW1PeelOrder70610 (phi w1n) (phi e1) (phi e3) (phi a2) (phi a1) (phi a0) (phi b5) (phi b4) (phi b3) (phi b2) := by
  simp only [alignedSquareW1PeelOrder70610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareW1PeelOrder70610
theorem alignedSquareW1PeelOrder70610_eval
    {k : Type*} [CommRing k]
    (w1n e1 e3 a2 a1 a0 b5 b4 b3 b2 : k[X]) (a : k) :
    (alignedSquareW1PeelOrder70610 w1n e1 e3 a2 a1 a0 b5 b4 b3 b2).eval a =
      alignedSquareW1PeelOrder70610 (w1n.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b5.eval a) (b4.eval a) (b3.eval a) (b2.eval a) :=
  map_alignedSquareW1PeelOrder70610 (Polynomial.evalRingHom a) w1n e1 e3 a2 a1 a0 b5 b4 b3 b2

#print axioms alignedSquareW1PeelOrder70610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareW1ComplementOrder70610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (w1n e1b e3b a2b a1 a0 b5 b4 b3 : R) :
    phi (alignedSquareW1ComplementOrder70610 w1n e1b e3b a2b a1 a0 b5 b4 b3) =
      alignedSquareW1ComplementOrder70610 (phi w1n) (phi e1b) (phi e3b) (phi a2b) (phi a1) (phi a0) (phi b5) (phi b4) (phi b3) := by
  simp only [alignedSquareW1ComplementOrder70610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareW1ComplementOrder70610
theorem alignedSquareW1ComplementOrder70610_eval
    {k : Type*} [CommRing k]
    (w1n e1b e3b a2b a1 a0 b5 b4 b3 : k[X]) (a : k) :
    (alignedSquareW1ComplementOrder70610 w1n e1b e3b a2b a1 a0 b5 b4 b3).eval a =
      alignedSquareW1ComplementOrder70610 (w1n.eval a) (e1b.eval a) (e3b.eval a) (a2b.eval a) (a1.eval a) (a0.eval a) (b5.eval a) (b4.eval a) (b3.eval a) :=
  map_alignedSquareW1ComplementOrder70610 (Polynomial.evalRingHom a) w1n e1b e3b a2b a1 a0 b5 b4 b3

#print axioms alignedSquareW1ComplementOrder70610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareMuZeroQ8Order70610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (w1 e1n e3 a2 a1 a0 b5 b4 b3 b2 b1 : R) :
    phi (alignedSquareMuZeroQ8Order70610 w1 e1n e3 a2 a1 a0 b5 b4 b3 b2 b1) =
      alignedSquareMuZeroQ8Order70610 (phi w1) (phi e1n) (phi e3) (phi a2) (phi a1) (phi a0) (phi b5) (phi b4) (phi b3) (phi b2) (phi b1) := by
  simp only [alignedSquareMuZeroQ8Order70610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareMuZeroQ8Order70610
theorem alignedSquareMuZeroQ8Order70610_eval
    {k : Type*} [CommRing k]
    (w1 e1n e3 a2 a1 a0 b5 b4 b3 b2 b1 : k[X]) (a : k) :
    (alignedSquareMuZeroQ8Order70610 w1 e1n e3 a2 a1 a0 b5 b4 b3 b2 b1).eval a =
      alignedSquareMuZeroQ8Order70610 (w1.eval a) (e1n.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b5.eval a) (b4.eval a) (b3.eval a) (b2.eval a) (b1.eval a) :=
  map_alignedSquareMuZeroQ8Order70610 (Polynomial.evalRingHom a) w1 e1n e3 a2 a1 a0 b5 b4 b3 b2 b1

#print axioms alignedSquareMuZeroQ8Order70610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareMixedPairOrder71610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (w1 e1 e3 a2 a1 a0 b3 b2 b1 : R) :
    phi (alignedSquareMixedPairOrder71610 w1 e1 e3 a2 a1 a0 b3 b2 b1) =
      alignedSquareMixedPairOrder71610 (phi w1) (phi e1) (phi e3) (phi a2) (phi a1) (phi a0) (phi b3) (phi b2) (phi b1) := by
  simp only [alignedSquareMixedPairOrder71610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareMixedPairOrder71610
theorem alignedSquareMixedPairOrder71610_eval
    {k : Type*} [CommRing k]
    (w1 e1 e3 a2 a1 a0 b3 b2 b1 : k[X]) (a : k) :
    (alignedSquareMixedPairOrder71610 w1 e1 e3 a2 a1 a0 b3 b2 b1).eval a =
      alignedSquareMixedPairOrder71610 (w1.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b3.eval a) (b2.eval a) (b1.eval a) :=
  map_alignedSquareMixedPairOrder71610 (Polynomial.evalRingHom a) w1 e1 e3 a2 a1 a0 b3 b2 b1

#print axioms alignedSquareMixedPairOrder71610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareW1ZeroOrder71610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (e1 e3 a2 a1 a0 b3 b2 b1 : R) :
    phi (alignedSquareW1ZeroOrder71610 e1 e3 a2 a1 a0 b3 b2 b1) =
      alignedSquareW1ZeroOrder71610 (phi e1) (phi e3) (phi a2) (phi a1) (phi a0) (phi b3) (phi b2) (phi b1) := by
  simp only [alignedSquareW1ZeroOrder71610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareW1ZeroOrder71610
theorem alignedSquareW1ZeroOrder71610_eval
    {k : Type*} [CommRing k]
    (e1 e3 a2 a1 a0 b3 b2 b1 : k[X]) (a : k) :
    (alignedSquareW1ZeroOrder71610 e1 e3 a2 a1 a0 b3 b2 b1).eval a =
      alignedSquareW1ZeroOrder71610 (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b3.eval a) (b2.eval a) (b1.eval a) :=
  map_alignedSquareW1ZeroOrder71610 (Polynomial.evalRingHom a) e1 e3 a2 a1 a0 b3 b2 b1

#print axioms alignedSquareW1ZeroOrder71610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareW1PeelOrder71610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (w1n e1 e3 a2 a1 a0 b4 b3 b2 b1 : R) :
    phi (alignedSquareW1PeelOrder71610 w1n e1 e3 a2 a1 a0 b4 b3 b2 b1) =
      alignedSquareW1PeelOrder71610 (phi w1n) (phi e1) (phi e3) (phi a2) (phi a1) (phi a0) (phi b4) (phi b3) (phi b2) (phi b1) := by
  simp only [alignedSquareW1PeelOrder71610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareW1PeelOrder71610
theorem alignedSquareW1PeelOrder71610_eval
    {k : Type*} [CommRing k]
    (w1n e1 e3 a2 a1 a0 b4 b3 b2 b1 : k[X]) (a : k) :
    (alignedSquareW1PeelOrder71610 w1n e1 e3 a2 a1 a0 b4 b3 b2 b1).eval a =
      alignedSquareW1PeelOrder71610 (w1n.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b4.eval a) (b3.eval a) (b2.eval a) (b1.eval a) :=
  map_alignedSquareW1PeelOrder71610 (Polynomial.evalRingHom a) w1n e1 e3 a2 a1 a0 b4 b3 b2 b1

#print axioms alignedSquareW1PeelOrder71610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareW1ComplementOrder71610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (w1n e1b e3b a2b a1 a0 b4 b3 : R) :
    phi (alignedSquareW1ComplementOrder71610 w1n e1b e3b a2b a1 a0 b4 b3) =
      alignedSquareW1ComplementOrder71610 (phi w1n) (phi e1b) (phi e3b) (phi a2b) (phi a1) (phi a0) (phi b4) (phi b3) := by
  simp only [alignedSquareW1ComplementOrder71610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareW1ComplementOrder71610
theorem alignedSquareW1ComplementOrder71610_eval
    {k : Type*} [CommRing k]
    (w1n e1b e3b a2b a1 a0 b4 b3 : k[X]) (a : k) :
    (alignedSquareW1ComplementOrder71610 w1n e1b e3b a2b a1 a0 b4 b3).eval a =
      alignedSquareW1ComplementOrder71610 (w1n.eval a) (e1b.eval a) (e3b.eval a) (a2b.eval a) (a1.eval a) (a0.eval a) (b4.eval a) (b3.eval a) :=
  map_alignedSquareW1ComplementOrder71610 (Polynomial.evalRingHom a) w1n e1b e3b a2b a1 a0 b4 b3

#print axioms alignedSquareW1ComplementOrder71610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareMuZeroQ8Order71610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (w1 : R) :
    phi (alignedSquareMuZeroQ8Order71610 w1) =
      alignedSquareMuZeroQ8Order71610 (phi w1) := by
  simp only [alignedSquareMuZeroQ8Order71610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareMuZeroQ8Order71610
theorem alignedSquareMuZeroQ8Order71610_eval
    {k : Type*} [CommRing k]
    (w1 : k[X]) (a : k) :
    (alignedSquareMuZeroQ8Order71610 w1).eval a =
      alignedSquareMuZeroQ8Order71610 (w1.eval a) :=
  map_alignedSquareMuZeroQ8Order71610 (Polynomial.evalRingHom a) w1

#print axioms alignedSquareMuZeroQ8Order71610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareMixedPairOrder72610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (w1 e1 e3 a2 a1 a0 b2 b1 : R) :
    phi (alignedSquareMixedPairOrder72610 w1 e1 e3 a2 a1 a0 b2 b1) =
      alignedSquareMixedPairOrder72610 (phi w1) (phi e1) (phi e3) (phi a2) (phi a1) (phi a0) (phi b2) (phi b1) := by
  simp only [alignedSquareMixedPairOrder72610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareMixedPairOrder72610
theorem alignedSquareMixedPairOrder72610_eval
    {k : Type*} [CommRing k]
    (w1 e1 e3 a2 a1 a0 b2 b1 : k[X]) (a : k) :
    (alignedSquareMixedPairOrder72610 w1 e1 e3 a2 a1 a0 b2 b1).eval a =
      alignedSquareMixedPairOrder72610 (w1.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b2.eval a) (b1.eval a) :=
  map_alignedSquareMixedPairOrder72610 (Polynomial.evalRingHom a) w1 e1 e3 a2 a1 a0 b2 b1

#print axioms alignedSquareMixedPairOrder72610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareW1ZeroOrder72610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (e1 e3 a2 a1 a0 b1 : R) :
    phi (alignedSquareW1ZeroOrder72610 e1 e3 a2 a1 a0 b1) =
      alignedSquareW1ZeroOrder72610 (phi e1) (phi e3) (phi a2) (phi a1) (phi a0) (phi b1) := by
  simp only [alignedSquareW1ZeroOrder72610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareW1ZeroOrder72610
theorem alignedSquareW1ZeroOrder72610_eval
    {k : Type*} [CommRing k]
    (e1 e3 a2 a1 a0 b1 : k[X]) (a : k) :
    (alignedSquareW1ZeroOrder72610 e1 e3 a2 a1 a0 b1).eval a =
      alignedSquareW1ZeroOrder72610 (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b1.eval a) :=
  map_alignedSquareW1ZeroOrder72610 (Polynomial.evalRingHom a) e1 e3 a2 a1 a0 b1

#print axioms alignedSquareW1ZeroOrder72610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareW1PeelOrder72610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (w1n e1 e3 a2 a1 a0 b3 b2 b1 : R) :
    phi (alignedSquareW1PeelOrder72610 w1n e1 e3 a2 a1 a0 b3 b2 b1) =
      alignedSquareW1PeelOrder72610 (phi w1n) (phi e1) (phi e3) (phi a2) (phi a1) (phi a0) (phi b3) (phi b2) (phi b1) := by
  simp only [alignedSquareW1PeelOrder72610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareW1PeelOrder72610
theorem alignedSquareW1PeelOrder72610_eval
    {k : Type*} [CommRing k]
    (w1n e1 e3 a2 a1 a0 b3 b2 b1 : k[X]) (a : k) :
    (alignedSquareW1PeelOrder72610 w1n e1 e3 a2 a1 a0 b3 b2 b1).eval a =
      alignedSquareW1PeelOrder72610 (w1n.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b3.eval a) (b2.eval a) (b1.eval a) :=
  map_alignedSquareW1PeelOrder72610 (Polynomial.evalRingHom a) w1n e1 e3 a2 a1 a0 b3 b2 b1

#print axioms alignedSquareW1PeelOrder72610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareW1ComplementOrder72610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (w1n e1b e3b a2b a1 a0 b3 b2 : R) :
    phi (alignedSquareW1ComplementOrder72610 w1n e1b e3b a2b a1 a0 b3 b2) =
      alignedSquareW1ComplementOrder72610 (phi w1n) (phi e1b) (phi e3b) (phi a2b) (phi a1) (phi a0) (phi b3) (phi b2) := by
  simp only [alignedSquareW1ComplementOrder72610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareW1ComplementOrder72610
theorem alignedSquareW1ComplementOrder72610_eval
    {k : Type*} [CommRing k]
    (w1n e1b e3b a2b a1 a0 b3 b2 : k[X]) (a : k) :
    (alignedSquareW1ComplementOrder72610 w1n e1b e3b a2b a1 a0 b3 b2).eval a =
      alignedSquareW1ComplementOrder72610 (w1n.eval a) (e1b.eval a) (e3b.eval a) (a2b.eval a) (a1.eval a) (a0.eval a) (b3.eval a) (b2.eval a) :=
  map_alignedSquareW1ComplementOrder72610 (Polynomial.evalRingHom a) w1n e1b e3b a2b a1 a0 b3 b2

#print axioms alignedSquareW1ComplementOrder72610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareMuZeroQ8Order72610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (w1 e1n e3 a2 a1 a0 b3 b2 b1 : R) :
    phi (alignedSquareMuZeroQ8Order72610 w1 e1n e3 a2 a1 a0 b3 b2 b1) =
      alignedSquareMuZeroQ8Order72610 (phi w1) (phi e1n) (phi e3) (phi a2) (phi a1) (phi a0) (phi b3) (phi b2) (phi b1) := by
  simp only [alignedSquareMuZeroQ8Order72610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareMuZeroQ8Order72610
theorem alignedSquareMuZeroQ8Order72610_eval
    {k : Type*} [CommRing k]
    (w1 e1n e3 a2 a1 a0 b3 b2 b1 : k[X]) (a : k) :
    (alignedSquareMuZeroQ8Order72610 w1 e1n e3 a2 a1 a0 b3 b2 b1).eval a =
      alignedSquareMuZeroQ8Order72610 (w1.eval a) (e1n.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b3.eval a) (b2.eval a) (b1.eval a) :=
  map_alignedSquareMuZeroQ8Order72610 (Polynomial.evalRingHom a) w1 e1n e3 a2 a1 a0 b3 b2 b1

#print axioms alignedSquareMuZeroQ8Order72610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareMixedPairOrder73610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (w1 e1 a0 : R) :
    phi (alignedSquareMixedPairOrder73610 w1 e1 a0) =
      alignedSquareMixedPairOrder73610 (phi w1) (phi e1) (phi a0) := by
  simp only [alignedSquareMixedPairOrder73610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareMixedPairOrder73610
theorem alignedSquareMixedPairOrder73610_eval
    {k : Type*} [CommRing k]
    (w1 e1 a0 : k[X]) (a : k) :
    (alignedSquareMixedPairOrder73610 w1 e1 a0).eval a =
      alignedSquareMixedPairOrder73610 (w1.eval a) (e1.eval a) (a0.eval a) :=
  map_alignedSquareMixedPairOrder73610 (Polynomial.evalRingHom a) w1 e1 a0

#print axioms alignedSquareMixedPairOrder73610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareW1ZeroOrder73610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (e1 : R) :
    phi (alignedSquareW1ZeroOrder73610 e1) =
      alignedSquareW1ZeroOrder73610 (phi e1) := by
  simp only [alignedSquareW1ZeroOrder73610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareW1ZeroOrder73610
theorem alignedSquareW1ZeroOrder73610_eval
    {k : Type*} [CommRing k]
    (e1 : k[X]) (a : k) :
    (alignedSquareW1ZeroOrder73610 e1).eval a =
      alignedSquareW1ZeroOrder73610 (e1.eval a) :=
  map_alignedSquareW1ZeroOrder73610 (Polynomial.evalRingHom a) e1

#print axioms alignedSquareW1ZeroOrder73610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareW1PeelOrder73610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (w1n e1 e3 a2 a1 a0 b2 b1 : R) :
    phi (alignedSquareW1PeelOrder73610 w1n e1 e3 a2 a1 a0 b2 b1) =
      alignedSquareW1PeelOrder73610 (phi w1n) (phi e1) (phi e3) (phi a2) (phi a1) (phi a0) (phi b2) (phi b1) := by
  simp only [alignedSquareW1PeelOrder73610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareW1PeelOrder73610
theorem alignedSquareW1PeelOrder73610_eval
    {k : Type*} [CommRing k]
    (w1n e1 e3 a2 a1 a0 b2 b1 : k[X]) (a : k) :
    (alignedSquareW1PeelOrder73610 w1n e1 e3 a2 a1 a0 b2 b1).eval a =
      alignedSquareW1PeelOrder73610 (w1n.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b2.eval a) (b1.eval a) :=
  map_alignedSquareW1PeelOrder73610 (Polynomial.evalRingHom a) w1n e1 e3 a2 a1 a0 b2 b1

#print axioms alignedSquareW1PeelOrder73610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareW1ComplementOrder73610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (w1n e1b e3b a2b a1 a0 b2 b1 : R) :
    phi (alignedSquareW1ComplementOrder73610 w1n e1b e3b a2b a1 a0 b2 b1) =
      alignedSquareW1ComplementOrder73610 (phi w1n) (phi e1b) (phi e3b) (phi a2b) (phi a1) (phi a0) (phi b2) (phi b1) := by
  simp only [alignedSquareW1ComplementOrder73610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareW1ComplementOrder73610
theorem alignedSquareW1ComplementOrder73610_eval
    {k : Type*} [CommRing k]
    (w1n e1b e3b a2b a1 a0 b2 b1 : k[X]) (a : k) :
    (alignedSquareW1ComplementOrder73610 w1n e1b e3b a2b a1 a0 b2 b1).eval a =
      alignedSquareW1ComplementOrder73610 (w1n.eval a) (e1b.eval a) (e3b.eval a) (a2b.eval a) (a1.eval a) (a0.eval a) (b2.eval a) (b1.eval a) :=
  map_alignedSquareW1ComplementOrder73610 (Polynomial.evalRingHom a) w1n e1b e3b a2b a1 a0 b2 b1

#print axioms alignedSquareW1ComplementOrder73610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareMuZeroQ8Order73610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (w1 : R) :
    phi (alignedSquareMuZeroQ8Order73610 w1) =
      alignedSquareMuZeroQ8Order73610 (phi w1) := by
  simp only [alignedSquareMuZeroQ8Order73610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareMuZeroQ8Order73610
theorem alignedSquareMuZeroQ8Order73610_eval
    {k : Type*} [CommRing k]
    (w1 : k[X]) (a : k) :
    (alignedSquareMuZeroQ8Order73610 w1).eval a =
      alignedSquareMuZeroQ8Order73610 (w1.eval a) :=
  map_alignedSquareMuZeroQ8Order73610 (Polynomial.evalRingHom a) w1

#print axioms alignedSquareMuZeroQ8Order73610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareMixedPairOrder74610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (e3 a0 b1 : R) :
    phi (alignedSquareMixedPairOrder74610 e3 a0 b1) =
      alignedSquareMixedPairOrder74610 (phi e3) (phi a0) (phi b1) := by
  simp only [alignedSquareMixedPairOrder74610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareMixedPairOrder74610
theorem alignedSquareMixedPairOrder74610_eval
    {k : Type*} [CommRing k]
    (e3 a0 b1 : k[X]) (a : k) :
    (alignedSquareMixedPairOrder74610 e3 a0 b1).eval a =
      alignedSquareMixedPairOrder74610 (e3.eval a) (a0.eval a) (b1.eval a) :=
  map_alignedSquareMixedPairOrder74610 (Polynomial.evalRingHom a) e3 a0 b1

#print axioms alignedSquareMixedPairOrder74610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareW1ZeroOrder74610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (e3 a0 b1 : R) :
    phi (alignedSquareW1ZeroOrder74610 e3 a0 b1) =
      alignedSquareW1ZeroOrder74610 (phi e3) (phi a0) (phi b1) := by
  simp only [alignedSquareW1ZeroOrder74610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareW1ZeroOrder74610
theorem alignedSquareW1ZeroOrder74610_eval
    {k : Type*} [CommRing k]
    (e3 a0 b1 : k[X]) (a : k) :
    (alignedSquareW1ZeroOrder74610 e3 a0 b1).eval a =
      alignedSquareW1ZeroOrder74610 (e3.eval a) (a0.eval a) (b1.eval a) :=
  map_alignedSquareW1ZeroOrder74610 (Polynomial.evalRingHom a) e3 a0 b1

#print axioms alignedSquareW1ZeroOrder74610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareW1PeelOrder74610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (w1n e1 e3 a1 a0 b1 : R) :
    phi (alignedSquareW1PeelOrder74610 w1n e1 e3 a1 a0 b1) =
      alignedSquareW1PeelOrder74610 (phi w1n) (phi e1) (phi e3) (phi a1) (phi a0) (phi b1) := by
  simp only [alignedSquareW1PeelOrder74610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareW1PeelOrder74610
theorem alignedSquareW1PeelOrder74610_eval
    {k : Type*} [CommRing k]
    (w1n e1 e3 a1 a0 b1 : k[X]) (a : k) :
    (alignedSquareW1PeelOrder74610 w1n e1 e3 a1 a0 b1).eval a =
      alignedSquareW1PeelOrder74610 (w1n.eval a) (e1.eval a) (e3.eval a) (a1.eval a) (a0.eval a) (b1.eval a) :=
  map_alignedSquareW1PeelOrder74610 (Polynomial.evalRingHom a) w1n e1 e3 a1 a0 b1

#print axioms alignedSquareW1PeelOrder74610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareW1ComplementOrder74610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (w1n e1b e3b a2b a1 a0 b1 : R) :
    phi (alignedSquareW1ComplementOrder74610 w1n e1b e3b a2b a1 a0 b1) =
      alignedSquareW1ComplementOrder74610 (phi w1n) (phi e1b) (phi e3b) (phi a2b) (phi a1) (phi a0) (phi b1) := by
  simp only [alignedSquareW1ComplementOrder74610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareW1ComplementOrder74610
theorem alignedSquareW1ComplementOrder74610_eval
    {k : Type*} [CommRing k]
    (w1n e1b e3b a2b a1 a0 b1 : k[X]) (a : k) :
    (alignedSquareW1ComplementOrder74610 w1n e1b e3b a2b a1 a0 b1).eval a =
      alignedSquareW1ComplementOrder74610 (w1n.eval a) (e1b.eval a) (e3b.eval a) (a2b.eval a) (a1.eval a) (a0.eval a) (b1.eval a) :=
  map_alignedSquareW1ComplementOrder74610 (Polynomial.evalRingHom a) w1n e1b e3b a2b a1 a0 b1

#print axioms alignedSquareW1ComplementOrder74610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareMuZeroQ8Order74610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (w1 e1n e3 a1 a0 b1 : R) :
    phi (alignedSquareMuZeroQ8Order74610 w1 e1n e3 a1 a0 b1) =
      alignedSquareMuZeroQ8Order74610 (phi w1) (phi e1n) (phi e3) (phi a1) (phi a0) (phi b1) := by
  simp only [alignedSquareMuZeroQ8Order74610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareMuZeroQ8Order74610
theorem alignedSquareMuZeroQ8Order74610_eval
    {k : Type*} [CommRing k]
    (w1 e1n e3 a1 a0 b1 : k[X]) (a : k) :
    (alignedSquareMuZeroQ8Order74610 w1 e1n e3 a1 a0 b1).eval a =
      alignedSquareMuZeroQ8Order74610 (w1.eval a) (e1n.eval a) (e3.eval a) (a1.eval a) (a0.eval a) (b1.eval a) :=
  map_alignedSquareMuZeroQ8Order74610 (Polynomial.evalRingHom a) w1 e1n e3 a1 a0 b1

#print axioms alignedSquareMuZeroQ8Order74610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareMixedPairOrder75610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (w1 : R) :
    phi (alignedSquareMixedPairOrder75610 w1) =
      alignedSquareMixedPairOrder75610 (phi w1) := by
  simp only [alignedSquareMixedPairOrder75610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareMixedPairOrder75610
theorem alignedSquareMixedPairOrder75610_eval
    {k : Type*} [CommRing k]
    (w1 : k[X]) (a : k) :
    (alignedSquareMixedPairOrder75610 w1).eval a =
      alignedSquareMixedPairOrder75610 (w1.eval a) :=
  map_alignedSquareMixedPairOrder75610 (Polynomial.evalRingHom a) w1

#print axioms alignedSquareMixedPairOrder75610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareW1ZeroOrder75610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (e1 : R) :
    phi (alignedSquareW1ZeroOrder75610 e1) =
      alignedSquareW1ZeroOrder75610 (phi e1) := by
  simp only [alignedSquareW1ZeroOrder75610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareW1ZeroOrder75610
theorem alignedSquareW1ZeroOrder75610_eval
    {k : Type*} [CommRing k]
    (e1 : k[X]) (a : k) :
    (alignedSquareW1ZeroOrder75610 e1).eval a =
      alignedSquareW1ZeroOrder75610 (e1.eval a) :=
  map_alignedSquareW1ZeroOrder75610 (Polynomial.evalRingHom a) e1

#print axioms alignedSquareW1ZeroOrder75610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareW1PeelOrder75610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (w1n a0 : R) :
    phi (alignedSquareW1PeelOrder75610 w1n a0) =
      alignedSquareW1PeelOrder75610 (phi w1n) (phi a0) := by
  simp only [alignedSquareW1PeelOrder75610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareW1PeelOrder75610
theorem alignedSquareW1PeelOrder75610_eval
    {k : Type*} [CommRing k]
    (w1n a0 : k[X]) (a : k) :
    (alignedSquareW1PeelOrder75610 w1n a0).eval a =
      alignedSquareW1PeelOrder75610 (w1n.eval a) (a0.eval a) :=
  map_alignedSquareW1PeelOrder75610 (Polynomial.evalRingHom a) w1n a0

#print axioms alignedSquareW1PeelOrder75610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareW1ComplementOrder75610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (w1n e1b e3b a0 : R) :
    phi (alignedSquareW1ComplementOrder75610 w1n e1b e3b a0) =
      alignedSquareW1ComplementOrder75610 (phi w1n) (phi e1b) (phi e3b) (phi a0) := by
  simp only [alignedSquareW1ComplementOrder75610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareW1ComplementOrder75610
theorem alignedSquareW1ComplementOrder75610_eval
    {k : Type*} [CommRing k]
    (w1n e1b e3b a0 : k[X]) (a : k) :
    (alignedSquareW1ComplementOrder75610 w1n e1b e3b a0).eval a =
      alignedSquareW1ComplementOrder75610 (w1n.eval a) (e1b.eval a) (e3b.eval a) (a0.eval a) :=
  map_alignedSquareW1ComplementOrder75610 (Polynomial.evalRingHom a) w1n e1b e3b a0

#print axioms alignedSquareW1ComplementOrder75610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareMuZeroQ8Order75610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (w1 : R) :
    phi (alignedSquareMuZeroQ8Order75610 w1) =
      alignedSquareMuZeroQ8Order75610 (phi w1) := by
  simp only [alignedSquareMuZeroQ8Order75610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareMuZeroQ8Order75610
theorem alignedSquareMuZeroQ8Order75610_eval
    {k : Type*} [CommRing k]
    (w1 : k[X]) (a : k) :
    (alignedSquareMuZeroQ8Order75610 w1).eval a =
      alignedSquareMuZeroQ8Order75610 (w1.eval a) :=
  map_alignedSquareMuZeroQ8Order75610 (Polynomial.evalRingHom a) w1

#print axioms alignedSquareMuZeroQ8Order75610_eval
/-! ## Pole obstruction and `h₀`-divisibility

Each limb theorem assumes the MixedPair jet is the remaining pole-`21`
numerator of a rational function with simple-pole derivative, matching
`alignedSquare_poleTwentyOne_head_eval_zero610`.  The source-primitive
clearing identity is not re-proved here.
-/

section AlignedSquareTowerCeilingHeads610

variable {k : Type*} [Field k] [CharZero k]

/-- Named `h^8` coefficient, forced if it is the remaining
pole-`6` head after cancelling `h₀^15`. -/
theorem alignedSquareW1PeelOrder69610_zero_of_remaining_pole
    (h0 w1n e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 Q : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hfact :
      alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 =
        h0 ^ 15 * Q)
    (hhead : Q.eval a = alignedSquareW1PeelOrder69610 (w1n.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b6.eval a) (b5.eval a) (b4.eval a) (b3.eval a))
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    alignedSquareW1PeelOrder69610 (w1n.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b6.eval a) (b5.eval a) (b4.eval a) (b3.eval a) = 0 := by
  have hclear_mn :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ (15 + 6) * rho := by
    have hpow : alignedSquareRemainingPole610 = 15 + 6 := rfl
    rwa [hpow] at hclear
  exact alignedSquare_remainingHead_eval_zero610 h0
    (alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1)
    Q rho j a (alignedSquareW1PeelOrder69610 (w1n.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b6.eval a) (b5.eval a) (b4.eval a) (b3.eval a)) 15 6 (by decide) hh0 hdegree hroot hfact
    hhead hclear_mn hderiv

#print axioms alignedSquareW1PeelOrder69610_zero_of_remaining_pole
/-- Named `h^8` coefficient, forced if it is the remaining
pole-`6` head after cancelling `h₀^15`. -/
theorem alignedSquareW1ZeroOrder69610_zero_of_remaining_pole
    (h0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 Q : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hfact :
      alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 =
        h0 ^ 15 * Q)
    (hhead : Q.eval a = alignedSquareW1ZeroOrder69610 (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (b3.eval a))
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    alignedSquareW1ZeroOrder69610 (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (b3.eval a) = 0 := by
  have hclear_mn :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ (15 + 6) * rho := by
    have hpow : alignedSquareRemainingPole610 = 15 + 6 := rfl
    rwa [hpow] at hclear
  exact alignedSquare_remainingHead_eval_zero610 h0
    (alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1)
    Q rho j a (alignedSquareW1ZeroOrder69610 (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (b3.eval a)) 15 6 (by decide) hh0 hdegree hroot hfact
    hhead hclear_mn hderiv

#print axioms alignedSquareW1ZeroOrder69610_zero_of_remaining_pole
/-- Named `h^8` coefficient, forced if it is the remaining
pole-`6` head after cancelling `h₀^15`. -/
theorem alignedSquareMuZeroQ8Order69610_zero_of_remaining_pole
    (h0 w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 Q : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hfact :
      alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0 (h0 * b8n) b7 b6 b5 b4 b3 b2 b1 =
        h0 ^ 15 * Q)
    (hhead : Q.eval a = alignedSquareMuZeroQ8Order69610 (w1.eval a))
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0 (h0 * b8n) b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    alignedSquareMuZeroQ8Order69610 (w1.eval a) = 0 := by
  have hclear_mn :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0 (h0 * b8n) b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ (15 + 6) * rho := by
    have hpow : alignedSquareRemainingPole610 = 15 + 6 := rfl
    rwa [hpow] at hclear
  exact alignedSquare_remainingHead_eval_zero610 h0
    (alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0 (h0 * b8n) b7 b6 b5 b4 b3 b2 b1)
    Q rho j a (alignedSquareMuZeroQ8Order69610 (w1.eval a)) 15 6 (by decide) hh0 hdegree hroot hfact
    hhead hclear_mn hderiv

#print axioms alignedSquareMuZeroQ8Order69610_zero_of_remaining_pole
/-- Named `h^9` coefficient, forced if it is the remaining
pole-`5` head after cancelling `h₀^16`. -/
theorem alignedSquareW1PeelOrder70610_zero_of_remaining_pole
    (h0 w1n e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 Q : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hfact :
      alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 =
        h0 ^ 16 * Q)
    (hhead : Q.eval a = alignedSquareW1PeelOrder70610 (w1n.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b5.eval a) (b4.eval a) (b3.eval a) (b2.eval a))
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    alignedSquareW1PeelOrder70610 (w1n.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b5.eval a) (b4.eval a) (b3.eval a) (b2.eval a) = 0 := by
  have hclear_mn :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ (16 + 5) * rho := by
    have hpow : alignedSquareRemainingPole610 = 16 + 5 := rfl
    rwa [hpow] at hclear
  exact alignedSquare_remainingHead_eval_zero610 h0
    (alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1)
    Q rho j a (alignedSquareW1PeelOrder70610 (w1n.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b5.eval a) (b4.eval a) (b3.eval a) (b2.eval a)) 16 5 (by decide) hh0 hdegree hroot hfact
    hhead hclear_mn hderiv

#print axioms alignedSquareW1PeelOrder70610_zero_of_remaining_pole
/-- Named `h^9` coefficient, forced if it is the remaining
pole-`5` head after cancelling `h₀^16`. -/
theorem alignedSquareW1ZeroOrder70610_zero_of_remaining_pole
    (h0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 Q : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hfact :
      alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 =
        h0 ^ 16 * Q)
    (hhead : Q.eval a = alignedSquareW1ZeroOrder70610 (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b4.eval a) (b3.eval a) (b2.eval a))
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    alignedSquareW1ZeroOrder70610 (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b4.eval a) (b3.eval a) (b2.eval a) = 0 := by
  have hclear_mn :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ (16 + 5) * rho := by
    have hpow : alignedSquareRemainingPole610 = 16 + 5 := rfl
    rwa [hpow] at hclear
  exact alignedSquare_remainingHead_eval_zero610 h0
    (alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1)
    Q rho j a (alignedSquareW1ZeroOrder70610 (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b4.eval a) (b3.eval a) (b2.eval a)) 16 5 (by decide) hh0 hdegree hroot hfact
    hhead hclear_mn hderiv

#print axioms alignedSquareW1ZeroOrder70610_zero_of_remaining_pole
/-- Named `h^9` coefficient, forced if it is the remaining
pole-`5` head after cancelling `h₀^16`. -/
theorem alignedSquareMuZeroQ8Order70610_zero_of_remaining_pole
    (h0 w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 Q : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hfact :
      alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0 (h0 * b8n) b7 b6 b5 b4 b3 b2 b1 =
        h0 ^ 16 * Q)
    (hhead : Q.eval a = alignedSquareMuZeroQ8Order70610 (w1.eval a) (e1n.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b5.eval a) (b4.eval a) (b3.eval a) (b2.eval a) (b1.eval a))
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0 (h0 * b8n) b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    alignedSquareMuZeroQ8Order70610 (w1.eval a) (e1n.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b5.eval a) (b4.eval a) (b3.eval a) (b2.eval a) (b1.eval a) = 0 := by
  have hclear_mn :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0 (h0 * b8n) b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ (16 + 5) * rho := by
    have hpow : alignedSquareRemainingPole610 = 16 + 5 := rfl
    rwa [hpow] at hclear
  exact alignedSquare_remainingHead_eval_zero610 h0
    (alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0 (h0 * b8n) b7 b6 b5 b4 b3 b2 b1)
    Q rho j a (alignedSquareMuZeroQ8Order70610 (w1.eval a) (e1n.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b5.eval a) (b4.eval a) (b3.eval a) (b2.eval a) (b1.eval a)) 16 5 (by decide) hh0 hdegree hroot hfact
    hhead hclear_mn hderiv

#print axioms alignedSquareMuZeroQ8Order70610_zero_of_remaining_pole
/-- Named `h^10` coefficient, forced if it is the remaining
pole-`4` head after cancelling `h₀^17`. -/
theorem alignedSquareW1PeelOrder71610_zero_of_remaining_pole
    (h0 w1n e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 Q : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hfact :
      alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 =
        h0 ^ 17 * Q)
    (hhead : Q.eval a = alignedSquareW1PeelOrder71610 (w1n.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b4.eval a) (b3.eval a) (b2.eval a) (b1.eval a))
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    alignedSquareW1PeelOrder71610 (w1n.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b4.eval a) (b3.eval a) (b2.eval a) (b1.eval a) = 0 := by
  have hclear_mn :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ (17 + 4) * rho := by
    have hpow : alignedSquareRemainingPole610 = 17 + 4 := rfl
    rwa [hpow] at hclear
  exact alignedSquare_remainingHead_eval_zero610 h0
    (alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1)
    Q rho j a (alignedSquareW1PeelOrder71610 (w1n.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b4.eval a) (b3.eval a) (b2.eval a) (b1.eval a)) 17 4 (by decide) hh0 hdegree hroot hfact
    hhead hclear_mn hderiv

#print axioms alignedSquareW1PeelOrder71610_zero_of_remaining_pole
/-- Named `h^10` coefficient, forced if it is the remaining
pole-`4` head after cancelling `h₀^17`. -/
theorem alignedSquareW1ZeroOrder71610_zero_of_remaining_pole
    (h0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 Q : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hfact :
      alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 =
        h0 ^ 17 * Q)
    (hhead : Q.eval a = alignedSquareW1ZeroOrder71610 (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b3.eval a) (b2.eval a) (b1.eval a))
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    alignedSquareW1ZeroOrder71610 (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b3.eval a) (b2.eval a) (b1.eval a) = 0 := by
  have hclear_mn :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ (17 + 4) * rho := by
    have hpow : alignedSquareRemainingPole610 = 17 + 4 := rfl
    rwa [hpow] at hclear
  exact alignedSquare_remainingHead_eval_zero610 h0
    (alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1)
    Q rho j a (alignedSquareW1ZeroOrder71610 (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b3.eval a) (b2.eval a) (b1.eval a)) 17 4 (by decide) hh0 hdegree hroot hfact
    hhead hclear_mn hderiv

#print axioms alignedSquareW1ZeroOrder71610_zero_of_remaining_pole
/-- Named `h^10` coefficient, forced if it is the remaining
pole-`4` head after cancelling `h₀^17`. -/
theorem alignedSquareMuZeroQ8Order71610_zero_of_remaining_pole
    (h0 w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 Q : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hfact :
      alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0 (h0 * b8n) b7 b6 b5 b4 b3 b2 b1 =
        h0 ^ 17 * Q)
    (hhead : Q.eval a = alignedSquareMuZeroQ8Order71610 (w1.eval a))
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0 (h0 * b8n) b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    alignedSquareMuZeroQ8Order71610 (w1.eval a) = 0 := by
  have hclear_mn :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0 (h0 * b8n) b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ (17 + 4) * rho := by
    have hpow : alignedSquareRemainingPole610 = 17 + 4 := rfl
    rwa [hpow] at hclear
  exact alignedSquare_remainingHead_eval_zero610 h0
    (alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0 (h0 * b8n) b7 b6 b5 b4 b3 b2 b1)
    Q rho j a (alignedSquareMuZeroQ8Order71610 (w1.eval a)) 17 4 (by decide) hh0 hdegree hroot hfact
    hhead hclear_mn hderiv

#print axioms alignedSquareMuZeroQ8Order71610_zero_of_remaining_pole
/-- Named `h^11` coefficient, forced if it is the remaining
pole-`3` head after cancelling `h₀^18`. -/
theorem alignedSquareW1PeelOrder72610_zero_of_remaining_pole
    (h0 w1n e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 Q : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hfact :
      alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 =
        h0 ^ 18 * Q)
    (hhead : Q.eval a = alignedSquareW1PeelOrder72610 (w1n.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b3.eval a) (b2.eval a) (b1.eval a))
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    alignedSquareW1PeelOrder72610 (w1n.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b3.eval a) (b2.eval a) (b1.eval a) = 0 := by
  have hclear_mn :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ (18 + 3) * rho := by
    have hpow : alignedSquareRemainingPole610 = 18 + 3 := rfl
    rwa [hpow] at hclear
  exact alignedSquare_remainingHead_eval_zero610 h0
    (alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1)
    Q rho j a (alignedSquareW1PeelOrder72610 (w1n.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b3.eval a) (b2.eval a) (b1.eval a)) 18 3 (by decide) hh0 hdegree hroot hfact
    hhead hclear_mn hderiv

#print axioms alignedSquareW1PeelOrder72610_zero_of_remaining_pole
/-- Named `h^11` coefficient, forced if it is the remaining
pole-`3` head after cancelling `h₀^18`. -/
theorem alignedSquareW1ZeroOrder72610_zero_of_remaining_pole
    (h0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 Q : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hfact :
      alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 =
        h0 ^ 18 * Q)
    (hhead : Q.eval a = alignedSquareW1ZeroOrder72610 (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b1.eval a))
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    alignedSquareW1ZeroOrder72610 (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b1.eval a) = 0 := by
  have hclear_mn :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ (18 + 3) * rho := by
    have hpow : alignedSquareRemainingPole610 = 18 + 3 := rfl
    rwa [hpow] at hclear
  exact alignedSquare_remainingHead_eval_zero610 h0
    (alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1)
    Q rho j a (alignedSquareW1ZeroOrder72610 (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b1.eval a)) 18 3 (by decide) hh0 hdegree hroot hfact
    hhead hclear_mn hderiv

#print axioms alignedSquareW1ZeroOrder72610_zero_of_remaining_pole
/-- Named `h^11` coefficient, forced if it is the remaining
pole-`3` head after cancelling `h₀^18`. -/
theorem alignedSquareMuZeroQ8Order72610_zero_of_remaining_pole
    (h0 w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 Q : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hfact :
      alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0 (h0 * b8n) b7 b6 b5 b4 b3 b2 b1 =
        h0 ^ 18 * Q)
    (hhead : Q.eval a = alignedSquareMuZeroQ8Order72610 (w1.eval a) (e1n.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b3.eval a) (b2.eval a) (b1.eval a))
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0 (h0 * b8n) b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    alignedSquareMuZeroQ8Order72610 (w1.eval a) (e1n.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b3.eval a) (b2.eval a) (b1.eval a) = 0 := by
  have hclear_mn :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0 (h0 * b8n) b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ (18 + 3) * rho := by
    have hpow : alignedSquareRemainingPole610 = 18 + 3 := rfl
    rwa [hpow] at hclear
  exact alignedSquare_remainingHead_eval_zero610 h0
    (alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0 (h0 * b8n) b7 b6 b5 b4 b3 b2 b1)
    Q rho j a (alignedSquareMuZeroQ8Order72610 (w1.eval a) (e1n.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b3.eval a) (b2.eval a) (b1.eval a)) 18 3 (by decide) hh0 hdegree hroot hfact
    hhead hclear_mn hderiv

#print axioms alignedSquareMuZeroQ8Order72610_zero_of_remaining_pole
/-- Named `h^12` coefficient, forced if it is the remaining
pole-`2` head after cancelling `h₀^19`. -/
theorem alignedSquareW1PeelOrder73610_zero_of_remaining_pole
    (h0 w1n e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 Q : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hfact :
      alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 =
        h0 ^ 19 * Q)
    (hhead : Q.eval a = alignedSquareW1PeelOrder73610 (w1n.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b2.eval a) (b1.eval a))
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    alignedSquareW1PeelOrder73610 (w1n.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b2.eval a) (b1.eval a) = 0 := by
  have hclear_mn :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ (19 + 2) * rho := by
    have hpow : alignedSquareRemainingPole610 = 19 + 2 := rfl
    rwa [hpow] at hclear
  exact alignedSquare_remainingHead_eval_zero610 h0
    (alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1)
    Q rho j a (alignedSquareW1PeelOrder73610 (w1n.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b2.eval a) (b1.eval a)) 19 2 (by decide) hh0 hdegree hroot hfact
    hhead hclear_mn hderiv

#print axioms alignedSquareW1PeelOrder73610_zero_of_remaining_pole
/-- Named `h^12` coefficient, forced if it is the remaining
pole-`2` head after cancelling `h₀^19`. -/
theorem alignedSquareW1ZeroOrder73610_zero_of_remaining_pole
    (h0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 Q : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hfact :
      alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 =
        h0 ^ 19 * Q)
    (hhead : Q.eval a = alignedSquareW1ZeroOrder73610 (e1.eval a))
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    alignedSquareW1ZeroOrder73610 (e1.eval a) = 0 := by
  have hclear_mn :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ (19 + 2) * rho := by
    have hpow : alignedSquareRemainingPole610 = 19 + 2 := rfl
    rwa [hpow] at hclear
  exact alignedSquare_remainingHead_eval_zero610 h0
    (alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1)
    Q rho j a (alignedSquareW1ZeroOrder73610 (e1.eval a)) 19 2 (by decide) hh0 hdegree hroot hfact
    hhead hclear_mn hderiv

#print axioms alignedSquareW1ZeroOrder73610_zero_of_remaining_pole
/-- Named `h^12` coefficient, forced if it is the remaining
pole-`2` head after cancelling `h₀^19`. -/
theorem alignedSquareMuZeroQ8Order73610_zero_of_remaining_pole
    (h0 w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 Q : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hfact :
      alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0 (h0 * b8n) b7 b6 b5 b4 b3 b2 b1 =
        h0 ^ 19 * Q)
    (hhead : Q.eval a = alignedSquareMuZeroQ8Order73610 (w1.eval a))
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0 (h0 * b8n) b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    alignedSquareMuZeroQ8Order73610 (w1.eval a) = 0 := by
  have hclear_mn :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0 (h0 * b8n) b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ (19 + 2) * rho := by
    have hpow : alignedSquareRemainingPole610 = 19 + 2 := rfl
    rwa [hpow] at hclear
  exact alignedSquare_remainingHead_eval_zero610 h0
    (alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0 (h0 * b8n) b7 b6 b5 b4 b3 b2 b1)
    Q rho j a (alignedSquareMuZeroQ8Order73610 (w1.eval a)) 19 2 (by decide) hh0 hdegree hroot hfact
    hhead hclear_mn hderiv

#print axioms alignedSquareMuZeroQ8Order73610_zero_of_remaining_pole
/-- Named `h^13` coefficient, forced if it is the remaining
pole-`1` head after cancelling `h₀^20`. -/
theorem alignedSquareW1PeelOrder74610_zero_of_remaining_pole
    (h0 w1n e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 Q : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hfact :
      alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 =
        h0 ^ 20 * Q)
    (hhead : Q.eval a = alignedSquareW1PeelOrder74610 (w1n.eval a) (e1.eval a) (e3.eval a) (a1.eval a) (a0.eval a) (b1.eval a))
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    alignedSquareW1PeelOrder74610 (w1n.eval a) (e1.eval a) (e3.eval a) (a1.eval a) (a0.eval a) (b1.eval a) = 0 := by
  have hclear_mn :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ (20 + 1) * rho := by
    have hpow : alignedSquareRemainingPole610 = 20 + 1 := rfl
    rwa [hpow] at hclear
  exact alignedSquare_remainingHead_eval_zero610 h0
    (alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1)
    Q rho j a (alignedSquareW1PeelOrder74610 (w1n.eval a) (e1.eval a) (e3.eval a) (a1.eval a) (a0.eval a) (b1.eval a)) 20 1 (by decide) hh0 hdegree hroot hfact
    hhead hclear_mn hderiv

#print axioms alignedSquareW1PeelOrder74610_zero_of_remaining_pole
/-- Named `h^13` coefficient, forced if it is the remaining
pole-`1` head after cancelling `h₀^20`. -/
theorem alignedSquareW1ZeroOrder74610_zero_of_remaining_pole
    (h0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 Q : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hfact :
      alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 =
        h0 ^ 20 * Q)
    (hhead : Q.eval a = alignedSquareW1ZeroOrder74610 (e3.eval a) (a0.eval a) (b1.eval a))
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    alignedSquareW1ZeroOrder74610 (e3.eval a) (a0.eval a) (b1.eval a) = 0 := by
  have hclear_mn :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ (20 + 1) * rho := by
    have hpow : alignedSquareRemainingPole610 = 20 + 1 := rfl
    rwa [hpow] at hclear
  exact alignedSquare_remainingHead_eval_zero610 h0
    (alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1)
    Q rho j a (alignedSquareW1ZeroOrder74610 (e3.eval a) (a0.eval a) (b1.eval a)) 20 1 (by decide) hh0 hdegree hroot hfact
    hhead hclear_mn hderiv

#print axioms alignedSquareW1ZeroOrder74610_zero_of_remaining_pole
/-- Named `h^13` coefficient, forced if it is the remaining
pole-`1` head after cancelling `h₀^20`. -/
theorem alignedSquareMuZeroQ8Order74610_zero_of_remaining_pole
    (h0 w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 Q : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hfact :
      alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0 (h0 * b8n) b7 b6 b5 b4 b3 b2 b1 =
        h0 ^ 20 * Q)
    (hhead : Q.eval a = alignedSquareMuZeroQ8Order74610 (w1.eval a) (e1n.eval a) (e3.eval a) (a1.eval a) (a0.eval a) (b1.eval a))
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0 (h0 * b8n) b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    alignedSquareMuZeroQ8Order74610 (w1.eval a) (e1n.eval a) (e3.eval a) (a1.eval a) (a0.eval a) (b1.eval a) = 0 := by
  have hclear_mn :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0 (h0 * b8n) b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ (20 + 1) * rho := by
    have hpow : alignedSquareRemainingPole610 = 20 + 1 := rfl
    rwa [hpow] at hclear
  exact alignedSquare_remainingHead_eval_zero610 h0
    (alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0 (h0 * b8n) b7 b6 b5 b4 b3 b2 b1)
    Q rho j a (alignedSquareMuZeroQ8Order74610 (w1.eval a) (e1n.eval a) (e3.eval a) (a1.eval a) (a0.eval a) (b1.eval a)) 20 1 (by decide) hh0 hdegree hroot hfact
    hhead hclear_mn hderiv

#print axioms alignedSquareMuZeroQ8Order74610_zero_of_remaining_pole
/-- Named `h^14` coefficient, remaining pole `0`.  The
pole obstruction no longer applies; cancel-and-expose with `j ≠ 0`
makes the holomorphic remainder impossible, so the named head vanishes. -/
theorem alignedSquareW1PeelOrder75610_zero_of_remaining_pole
    (h0 w1n e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 Q : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hfact :
      alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 =
        h0 ^ 21 * Q)
    (hhead : Q.eval a = alignedSquareW1PeelOrder75610 (w1n.eval a) (a0.eval a))
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
    (hj : j ≠ 0) :
    alignedSquareW1PeelOrder75610 (w1n.eval a) (a0.eval a) = 0 :=
  (alignedSquare_of_pow_dvd_simplePole_ne_zero610 a j h0
      (alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1) Q rho 21 hh0 hroot hfact
      (by
        have hpow : alignedSquareRemainingPole610 = 21 + 0 := rfl
        simpa [hpow, add_zero] using hclear)
      hderiv hj).elim

#print axioms alignedSquareW1PeelOrder75610_zero_of_remaining_pole
/-- Named `h^14` coefficient, remaining pole `0`.  The
pole obstruction no longer applies; cancel-and-expose with `j ≠ 0`
makes the holomorphic remainder impossible, so the named head vanishes. -/
theorem alignedSquareW1ZeroOrder75610_zero_of_remaining_pole
    (h0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 Q : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hfact :
      alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 =
        h0 ^ 21 * Q)
    (hhead : Q.eval a = alignedSquareW1ZeroOrder75610 (e1.eval a))
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
    (hj : j ≠ 0) :
    alignedSquareW1ZeroOrder75610 (e1.eval a) = 0 :=
  (alignedSquare_of_pow_dvd_simplePole_ne_zero610 a j h0
      (alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1) Q rho 21 hh0 hroot hfact
      (by
        have hpow : alignedSquareRemainingPole610 = 21 + 0 := rfl
        simpa [hpow, add_zero] using hclear)
      hderiv hj).elim

#print axioms alignedSquareW1ZeroOrder75610_zero_of_remaining_pole
/-- Named `h^14` coefficient, remaining pole `0`.  The
pole obstruction no longer applies; cancel-and-expose with `j ≠ 0`
makes the holomorphic remainder impossible, so the named head vanishes. -/
theorem alignedSquareMuZeroQ8Order75610_zero_of_remaining_pole
    (h0 w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 Q : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hfact :
      alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0 (h0 * b8n) b7 b6 b5 b4 b3 b2 b1 =
        h0 ^ 21 * Q)
    (hhead : Q.eval a = alignedSquareMuZeroQ8Order75610 (w1.eval a))
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0 (h0 * b8n) b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
    (hj : j ≠ 0) :
    alignedSquareMuZeroQ8Order75610 (w1.eval a) = 0 :=
  (alignedSquare_of_pow_dvd_simplePole_ne_zero610 a j h0
      (alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0 (h0 * b8n) b7 b6 b5 b4 b3 b2 b1) Q rho 21 hh0 hroot hfact
      (by
        have hpow : alignedSquareRemainingPole610 = 21 + 0 := rfl
        simpa [hpow, add_zero] using hclear)
      hderiv hj).elim

#print axioms alignedSquareMuZeroQ8Order75610_zero_of_remaining_pole
set_option maxHeartbeats 1600000000 in
/-- Remaining-numerator peels of orders `69` through `75` on this limb,
starting from the parent order-`68` vanishing.  After order `74` the
remaining pole is `1`; the last linear factor exposes `rho` as a
polynomial. -/
theorem alignedSquareW1Peel_orders69to75_remaining_dvd
    (h0 w1n e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    ∃ Q68 Q69 Q70 Q71 Q72 Q73 Q74 Q75 : k[X],
      alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 =
        h0 ^ 14 * Q68 ∧ Q68.eval a = 0 ∧
      Q68 = h0 * Q69 ∧ Q69.eval a = 0 ∧
      Q69 = h0 * Q70 ∧ Q70.eval a = 0 ∧
      Q70 = h0 * Q71 ∧ Q71.eval a = 0 ∧
      Q71 = h0 * Q72 ∧ Q72.eval a = 0 ∧
      Q72 = h0 * Q73 ∧ Q73.eval a = 0 ∧
      Q73 = h0 * Q74 ∧ Q74.eval a = 0 ∧
      Q74 = h0 * Q75 ∧
      algebraMap k[X] (RatFunc k) Q75 = rho := by
  obtain ⟨Q61, Q62, Q63, Q64, Q65, Q66, Q67, Q68, hjet, h61z, h62f, h62z,
      h63f, h63z, h64f, h64z, h65f, h65z, h66f, h66z, h67f, h67z, h68f,
      h68z, hdvd68⟩ :=
    alignedSquareW1Peel_orders61to68_remaining_dvd h0 w1n e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 rho j a hh0 hdegree hroot hclear hderiv
  have hjet14 :
      alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 = h0 ^ 14 * Q68 := by
    simp only [hjet, h62f, h63f, h64f, h65f, h66f, h67f, h68f]
    ring
  have hclear7 :
      algebraMap k[X] (RatFunc k) Q68 =
        (algebraMap k[X] (RatFunc k) h0) ^ (6 + 1) * rho :=
    alignedSquare_algebraMap_cancel_pow610 h0 Q68 rho 14 7 hh0
      (by
        have hpow : alignedSquareRemainingPole610 = 14 + 7 := rfl
        rw [hpow] at hclear
        simpa [hjet14] using hclear)
  obtain ⟨Q69, h69f, hclear6, h69z, _hdvd69⟩ :=
    alignedSquare_remainingNumerator_succ_dvd610 h0 Q68 rho j a 6
      (by decide) hh0 hdegree hroot h68z hclear7 hderiv
  obtain ⟨Q70, h70f, hclear5, h70z, _hdvd70⟩ :=
    alignedSquare_remainingNumerator_succ_dvd610 h0 Q69 rho j a 5
      (by decide) hh0 hdegree hroot h69z hclear6 hderiv
  obtain ⟨Q71, h71f, hclear4, h71z, _hdvd71⟩ :=
    alignedSquare_remainingNumerator_succ_dvd610 h0 Q70 rho j a 4
      (by decide) hh0 hdegree hroot h70z hclear5 hderiv
  obtain ⟨Q72, h72f, hclear3, h72z, _hdvd72⟩ :=
    alignedSquare_remainingNumerator_succ_dvd610 h0 Q71 rho j a 3
      (by decide) hh0 hdegree hroot h71z hclear4 hderiv
  obtain ⟨Q73, h73f, hclear2, h73z, _hdvd73⟩ :=
    alignedSquare_remainingNumerator_succ_dvd610 h0 Q72 rho j a 2
      (by decide) hh0 hdegree hroot h72z hclear3 hderiv
  obtain ⟨Q74, h74f, hclear1, h74z, _hdvd74⟩ :=
    alignedSquare_remainingNumerator_succ_dvd610 h0 Q73 rho j a 1
      (by decide) hh0 hdegree hroot h73z hclear2 hderiv
  obtain ⟨Q75, h75f⟩ :=
    alignedSquare_linearPolynomial_dvd_of_eval_eq_zero610 h0 Q74 a
      hdegree hroot h74z
  have hclear0 :
      algebraMap k[X] (RatFunc k) Q75 = rho := by
    simpa [pow_zero, one_mul] using
      alignedSquare_algebraMap_cancel_one_clearing610 h0 Q74 Q75 rho 0
        hh0 h75f (by simpa [zero_add, pow_one] using hclear1)
  exact ⟨Q68, Q69, Q70, Q71, Q72, Q73, Q74, Q75, hjet14, h68z, h69f,
    h69z, h70f, h70z, h71f, h71z, h72f, h72z, h73f, h73z, h74f, h74z,
    h75f, hclear0⟩

#print axioms alignedSquareW1Peel_orders69to75_remaining_dvd

theorem alignedSquareW1Peel_orders69to75_pow_dvd
    (h0 w1n e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    h0 ^ alignedSquareTowerCeilingDivisibility610 ∣
      alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 := by
  obtain ⟨Q68, Q69, Q70, Q71, Q72, Q73, Q74, Q75, hjet14, _h68z, h69f,
      _h69z, h70f, _h70z, h71f, _h71z, h72f, _h72z, h73f, _h73z, h74f,
      _h74z, h75f, _hclear0⟩ :=
    alignedSquareW1Peel_orders69to75_remaining_dvd h0 w1n e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 rho j a hh0
      hdegree hroot hclear hderiv
  refine ⟨Q75, ?_⟩
  simp only [alignedSquareTowerCeilingDivisibility610, hjet14, h69f,
    h70f, h71f, h72f, h73f, h74f, h75f]
  ring

#print axioms alignedSquareW1Peel_orders69to75_pow_dvd

/-- **CLOSED** on this limb, under the parent pole-`21` clearing.
Frozen exhaustion is `h₀^{21}`; the remaining factor is `rho` and
`j ≠ 0` is impossible. -/
theorem alignedSquareW1Peel_order75_false_of_simplePole
    (h0 w1n e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
    (hj : j ≠ 0) : False := by
  obtain ⟨Q68, Q69, Q70, Q71, Q72, Q73, Q74, Q75, hjet14, _h68z, h69f,
      _h69z, h70f, _h70z, h71f, _h71z, h72f, _h72z, h73f, _h73z, h74f,
      _h74z, h75f, hclear0⟩ :=
    alignedSquareW1Peel_orders69to75_remaining_dvd h0 w1n e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 rho j a hh0
      hdegree hroot hclear hderiv
  have hA :
      alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 = h0 ^ 21 * Q75 := by
    simp only [hjet14, h69f, h70f, h71f, h72f, h73f, h74f, h75f]
    ring
  have hclear21 :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ 21 * rho := by
    simpa [alignedSquareRemainingPole610] using hclear
  exact alignedSquare_of_pow_dvd_simplePole_ne_zero610 a j h0
    (alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1) Q75 rho 21 hh0 hroot hA hclear21 hderiv hj

#print axioms alignedSquareW1Peel_order75_false_of_simplePole
set_option maxHeartbeats 1600000000 in
/-- Remaining-numerator peels of orders `69` through `75` on this limb,
starting from the parent order-`68` vanishing.  After order `74` the
remaining pole is `1`; the last linear factor exposes `rho` as a
polynomial. -/
theorem alignedSquareW1Zero_orders69to75_remaining_dvd
    (h0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    ∃ Q68 Q69 Q70 Q71 Q72 Q73 Q74 Q75 : k[X],
      alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 =
        h0 ^ 14 * Q68 ∧ Q68.eval a = 0 ∧
      Q68 = h0 * Q69 ∧ Q69.eval a = 0 ∧
      Q69 = h0 * Q70 ∧ Q70.eval a = 0 ∧
      Q70 = h0 * Q71 ∧ Q71.eval a = 0 ∧
      Q71 = h0 * Q72 ∧ Q72.eval a = 0 ∧
      Q72 = h0 * Q73 ∧ Q73.eval a = 0 ∧
      Q73 = h0 * Q74 ∧ Q74.eval a = 0 ∧
      Q74 = h0 * Q75 ∧
      algebraMap k[X] (RatFunc k) Q75 = rho := by
  obtain ⟨Q61, Q62, Q63, Q64, Q65, Q66, Q67, Q68, hjet, h61z, h62f, h62z,
      h63f, h63z, h64f, h64z, h65f, h65z, h66f, h66z, h67f, h67z, h68f,
      h68z, hdvd68⟩ :=
    alignedSquareW1Zero_orders61to68_remaining_dvd h0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 rho j a hh0 hdegree hroot hclear hderiv
  have hjet14 :
      alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 = h0 ^ 14 * Q68 := by
    simp only [hjet, h62f, h63f, h64f, h65f, h66f, h67f, h68f]
    ring
  have hclear7 :
      algebraMap k[X] (RatFunc k) Q68 =
        (algebraMap k[X] (RatFunc k) h0) ^ (6 + 1) * rho :=
    alignedSquare_algebraMap_cancel_pow610 h0 Q68 rho 14 7 hh0
      (by
        have hpow : alignedSquareRemainingPole610 = 14 + 7 := rfl
        rw [hpow] at hclear
        simpa [hjet14] using hclear)
  obtain ⟨Q69, h69f, hclear6, h69z, _hdvd69⟩ :=
    alignedSquare_remainingNumerator_succ_dvd610 h0 Q68 rho j a 6
      (by decide) hh0 hdegree hroot h68z hclear7 hderiv
  obtain ⟨Q70, h70f, hclear5, h70z, _hdvd70⟩ :=
    alignedSquare_remainingNumerator_succ_dvd610 h0 Q69 rho j a 5
      (by decide) hh0 hdegree hroot h69z hclear6 hderiv
  obtain ⟨Q71, h71f, hclear4, h71z, _hdvd71⟩ :=
    alignedSquare_remainingNumerator_succ_dvd610 h0 Q70 rho j a 4
      (by decide) hh0 hdegree hroot h70z hclear5 hderiv
  obtain ⟨Q72, h72f, hclear3, h72z, _hdvd72⟩ :=
    alignedSquare_remainingNumerator_succ_dvd610 h0 Q71 rho j a 3
      (by decide) hh0 hdegree hroot h71z hclear4 hderiv
  obtain ⟨Q73, h73f, hclear2, h73z, _hdvd73⟩ :=
    alignedSquare_remainingNumerator_succ_dvd610 h0 Q72 rho j a 2
      (by decide) hh0 hdegree hroot h72z hclear3 hderiv
  obtain ⟨Q74, h74f, hclear1, h74z, _hdvd74⟩ :=
    alignedSquare_remainingNumerator_succ_dvd610 h0 Q73 rho j a 1
      (by decide) hh0 hdegree hroot h73z hclear2 hderiv
  obtain ⟨Q75, h75f⟩ :=
    alignedSquare_linearPolynomial_dvd_of_eval_eq_zero610 h0 Q74 a
      hdegree hroot h74z
  have hclear0 :
      algebraMap k[X] (RatFunc k) Q75 = rho := by
    simpa [pow_zero, one_mul] using
      alignedSquare_algebraMap_cancel_one_clearing610 h0 Q74 Q75 rho 0
        hh0 h75f (by simpa [zero_add, pow_one] using hclear1)
  exact ⟨Q68, Q69, Q70, Q71, Q72, Q73, Q74, Q75, hjet14, h68z, h69f,
    h69z, h70f, h70z, h71f, h71z, h72f, h72z, h73f, h73z, h74f, h74z,
    h75f, hclear0⟩

#print axioms alignedSquareW1Zero_orders69to75_remaining_dvd

theorem alignedSquareW1Zero_orders69to75_pow_dvd
    (h0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    h0 ^ alignedSquareTowerCeilingDivisibility610 ∣
      alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 := by
  obtain ⟨Q68, Q69, Q70, Q71, Q72, Q73, Q74, Q75, hjet14, _h68z, h69f,
      _h69z, h70f, _h70z, h71f, _h71z, h72f, _h72z, h73f, _h73z, h74f,
      _h74z, h75f, _hclear0⟩ :=
    alignedSquareW1Zero_orders69to75_remaining_dvd h0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 rho j a hh0
      hdegree hroot hclear hderiv
  refine ⟨Q75, ?_⟩
  simp only [alignedSquareTowerCeilingDivisibility610, hjet14, h69f,
    h70f, h71f, h72f, h73f, h74f, h75f]
  ring

#print axioms alignedSquareW1Zero_orders69to75_pow_dvd

/-- **CLOSED** on this limb, under the parent pole-`21` clearing.
Frozen exhaustion is `h₀^{21}`; the remaining factor is `rho` and
`j ≠ 0` is impossible. -/
theorem alignedSquareW1Zero_order75_false_of_simplePole
    (h0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
    (hj : j ≠ 0) : False := by
  obtain ⟨Q68, Q69, Q70, Q71, Q72, Q73, Q74, Q75, hjet14, _h68z, h69f,
      _h69z, h70f, _h70z, h71f, _h71z, h72f, _h72z, h73f, _h73z, h74f,
      _h74z, h75f, hclear0⟩ :=
    alignedSquareW1Zero_orders69to75_remaining_dvd h0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 rho j a hh0
      hdegree hroot hclear hderiv
  have hA :
      alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 = h0 ^ 21 * Q75 := by
    simp only [hjet14, h69f, h70f, h71f, h72f, h73f, h74f, h75f]
    ring
  have hclear21 :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ 21 * rho := by
    simpa [alignedSquareRemainingPole610] using hclear
  exact alignedSquare_of_pow_dvd_simplePole_ne_zero610 a j h0
    (alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1) Q75 rho 21 hh0 hroot hA hclear21 hderiv hj

#print axioms alignedSquareW1Zero_order75_false_of_simplePole
set_option maxHeartbeats 1600000000 in
/-- Remaining-numerator peels of orders `69` through `75` on `μ = 0`
after the `q₈` peel. -/
theorem alignedSquareMuZeroQ8_orders69to75_remaining_dvd
    (h0 w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0 (h0 * b8n) b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    ∃ Q68 Q69 Q70 Q71 Q72 Q73 Q74 Q75 : k[X],
      alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0 (h0 * b8n) b7 b6 b5 b4 b3 b2 b1 =
        h0 ^ 14 * Q68 ∧ Q68.eval a = 0 ∧
      Q68 = h0 * Q69 ∧ Q69.eval a = 0 ∧
      Q69 = h0 * Q70 ∧ Q70.eval a = 0 ∧
      Q70 = h0 * Q71 ∧ Q71.eval a = 0 ∧
      Q71 = h0 * Q72 ∧ Q72.eval a = 0 ∧
      Q72 = h0 * Q73 ∧ Q73.eval a = 0 ∧
      Q73 = h0 * Q74 ∧ Q74.eval a = 0 ∧
      Q74 = h0 * Q75 ∧
      algebraMap k[X] (RatFunc k) Q75 = rho := by
  obtain ⟨Q55, Q56, Q57, Q58, Q59, Q60, Q61, Q62, Q63, Q64, Q65, Q66, Q67,
      Q68, hjet, h55z, h56f, h56z, h57f, h57z, h58f, h58z, h59f, h59z,
      h60f, h60z, h61f, h61z, h62f, h62z, h63f, h63z, h64f, h64z, h65f,
      h65z, h66f, h66z, h67f, h67z, h68f, h68z, hdvd68⟩ :=
    alignedSquareMuZeroQ8_orders55to68_remaining_dvd h0 w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1
      rho j a hh0 hdegree hroot hclear hderiv
  have hjet14 :
      alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0 (h0 * b8n) b7 b6 b5 b4 b3 b2 b1 = h0 ^ 14 * Q68 := by
    simp only [hjet, h56f, h57f, h58f, h59f, h60f, h61f, h62f, h63f,
      h64f, h65f, h66f, h67f, h68f]
    ring
  have hclear7 :
      algebraMap k[X] (RatFunc k) Q68 =
        (algebraMap k[X] (RatFunc k) h0) ^ (6 + 1) * rho :=
    alignedSquare_algebraMap_cancel_pow610 h0 Q68 rho 14 7 hh0
      (by
        have hpow : alignedSquareRemainingPole610 = 14 + 7 := rfl
        rw [hpow] at hclear
        simpa [hjet14] using hclear)
  obtain ⟨Q69, h69f, hclear6, h69z, _hdvd69⟩ :=
    alignedSquare_remainingNumerator_succ_dvd610 h0 Q68 rho j a 6
      (by decide) hh0 hdegree hroot h68z hclear7 hderiv
  obtain ⟨Q70, h70f, hclear5, h70z, _hdvd70⟩ :=
    alignedSquare_remainingNumerator_succ_dvd610 h0 Q69 rho j a 5
      (by decide) hh0 hdegree hroot h69z hclear6 hderiv
  obtain ⟨Q71, h71f, hclear4, h71z, _hdvd71⟩ :=
    alignedSquare_remainingNumerator_succ_dvd610 h0 Q70 rho j a 4
      (by decide) hh0 hdegree hroot h70z hclear5 hderiv
  obtain ⟨Q72, h72f, hclear3, h72z, _hdvd72⟩ :=
    alignedSquare_remainingNumerator_succ_dvd610 h0 Q71 rho j a 3
      (by decide) hh0 hdegree hroot h71z hclear4 hderiv
  obtain ⟨Q73, h73f, hclear2, h73z, _hdvd73⟩ :=
    alignedSquare_remainingNumerator_succ_dvd610 h0 Q72 rho j a 2
      (by decide) hh0 hdegree hroot h72z hclear3 hderiv
  obtain ⟨Q74, h74f, hclear1, h74z, _hdvd74⟩ :=
    alignedSquare_remainingNumerator_succ_dvd610 h0 Q73 rho j a 1
      (by decide) hh0 hdegree hroot h73z hclear2 hderiv
  obtain ⟨Q75, h75f⟩ :=
    alignedSquare_linearPolynomial_dvd_of_eval_eq_zero610 h0 Q74 a
      hdegree hroot h74z
  have hclear0 :
      algebraMap k[X] (RatFunc k) Q75 = rho := by
    simpa [pow_zero, one_mul] using
      alignedSquare_algebraMap_cancel_one_clearing610 h0 Q74 Q75 rho 0
        hh0 h75f (by simpa [zero_add, pow_one] using hclear1)
  exact ⟨Q68, Q69, Q70, Q71, Q72, Q73, Q74, Q75, hjet14, h68z, h69f,
    h69z, h70f, h70z, h71f, h71z, h72f, h72z, h73f, h73z, h74f, h74z,
    h75f, hclear0⟩

#print axioms alignedSquareMuZeroQ8_orders69to75_remaining_dvd

theorem alignedSquareMuZeroQ8_orders69to75_pow_dvd
    (h0 w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0 (h0 * b8n) b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    h0 ^ alignedSquareTowerCeilingDivisibility610 ∣
      alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0 (h0 * b8n) b7 b6 b5 b4 b3 b2 b1 := by
  obtain ⟨Q68, Q69, Q70, Q71, Q72, Q73, Q74, Q75, hjet14, _h68z, h69f,
      _h69z, h70f, _h70z, h71f, _h71z, h72f, _h72z, h73f, _h73z, h74f,
      _h74z, h75f, _hclear0⟩ :=
    alignedSquareMuZeroQ8_orders69to75_remaining_dvd h0 w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1
      rho j a hh0 hdegree hroot hclear hderiv
  refine ⟨Q75, ?_⟩
  simp only [alignedSquareTowerCeilingDivisibility610, hjet14, h69f,
    h70f, h71f, h72f, h73f, h74f, h75f]
  ring

#print axioms alignedSquareMuZeroQ8_orders69to75_pow_dvd

theorem alignedSquareMuZeroQ8_order75_false_of_simplePole
    (h0 w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0 (h0 * b8n) b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
    (hj : j ≠ 0) : False := by
  obtain ⟨Q68, Q69, Q70, Q71, Q72, Q73, Q74, Q75, hjet14, _h68z, h69f,
      _h69z, h70f, _h70z, h71f, _h71z, h72f, _h72z, h73f, _h73z, h74f,
      _h74z, h75f, hclear0⟩ :=
    alignedSquareMuZeroQ8_orders69to75_remaining_dvd h0 w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1
      rho j a hh0 hdegree hroot hclear hderiv
  have hA :
      alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0 (h0 * b8n) b7 b6 b5 b4 b3 b2 b1 = h0 ^ 21 * Q75 := by
    simp only [hjet14, h69f, h70f, h71f, h72f, h73f, h74f, h75f]
    ring
  have hclear21 :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0 (h0 * b8n) b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ 21 * rho := by
    simpa [alignedSquareRemainingPole610] using hclear
  exact alignedSquare_of_pow_dvd_simplePole_ne_zero610 a j h0
    (alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0 (h0 * b8n) b7 b6 b5 b4 b3 b2 b1) Q75 rho 21 hh0 hroot hA hclear21 hderiv hj

#print axioms alignedSquareMuZeroQ8_order75_false_of_simplePole
set_option maxHeartbeats 1600000000 in
theorem alignedSquareW1Complement_orders69to75_remaining_dvd
    (h0 w1n e1b e3b a2b a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 (h0 * w1n) (h0 * e1b) (h0 * e3b) (h0 * a2b) a1 a0 b8 b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    ∃ Q68 Q69 Q70 Q71 Q72 Q73 Q74 Q75 : k[X],
      alignedSquareJetQuotient610 h0 (h0 * w1n) (h0 * e1b) (h0 * e3b) (h0 * a2b) a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 =
        h0 ^ 14 * Q68 ∧ Q68.eval a = 0 ∧
      Q68 = h0 * Q69 ∧ Q69.eval a = 0 ∧
      Q69 = h0 * Q70 ∧ Q70.eval a = 0 ∧
      Q70 = h0 * Q71 ∧ Q71.eval a = 0 ∧
      Q71 = h0 * Q72 ∧ Q72.eval a = 0 ∧
      Q72 = h0 * Q73 ∧ Q73.eval a = 0 ∧
      Q73 = h0 * Q74 ∧ Q74.eval a = 0 ∧
      Q74 = h0 * Q75 ∧
      algebraMap k[X] (RatFunc k) Q75 = rho := by
  obtain ⟨Q64, Q65, Q66, Q67, Q68, hjet, h64z, h65f, h65z, h66f, h66z,
      h67f, h67z, h68f, h68z, hdvd68⟩ :=
    alignedSquareW1Complement_orders64to68_remaining_dvd h0 w1n e1b e3b a2b a1 a0 b8 b7 b6 b5 b4 b3 b2 b1
      rho j a hh0 hdegree hroot hclear hderiv
  have hjet14 :
      alignedSquareJetQuotient610 h0 (h0 * w1n) (h0 * e1b) (h0 * e3b) (h0 * a2b) a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 = h0 ^ 14 * Q68 := by
    simp only [hjet, h65f, h66f, h67f, h68f]
    ring
  have hclear7 :
      algebraMap k[X] (RatFunc k) Q68 =
        (algebraMap k[X] (RatFunc k) h0) ^ (6 + 1) * rho :=
    alignedSquare_algebraMap_cancel_pow610 h0 Q68 rho 14 7 hh0
      (by
        have hpow : alignedSquareRemainingPole610 = 14 + 7 := rfl
        rw [hpow] at hclear
        simpa [hjet14] using hclear)
  obtain ⟨Q69, h69f, hclear6, h69z, _hdvd69⟩ :=
    alignedSquare_remainingNumerator_succ_dvd610 h0 Q68 rho j a 6
      (by decide) hh0 hdegree hroot h68z hclear7 hderiv
  obtain ⟨Q70, h70f, hclear5, h70z, _hdvd70⟩ :=
    alignedSquare_remainingNumerator_succ_dvd610 h0 Q69 rho j a 5
      (by decide) hh0 hdegree hroot h69z hclear6 hderiv
  obtain ⟨Q71, h71f, hclear4, h71z, _hdvd71⟩ :=
    alignedSquare_remainingNumerator_succ_dvd610 h0 Q70 rho j a 4
      (by decide) hh0 hdegree hroot h70z hclear5 hderiv
  obtain ⟨Q72, h72f, hclear3, h72z, _hdvd72⟩ :=
    alignedSquare_remainingNumerator_succ_dvd610 h0 Q71 rho j a 3
      (by decide) hh0 hdegree hroot h71z hclear4 hderiv
  obtain ⟨Q73, h73f, hclear2, h73z, _hdvd73⟩ :=
    alignedSquare_remainingNumerator_succ_dvd610 h0 Q72 rho j a 2
      (by decide) hh0 hdegree hroot h72z hclear3 hderiv
  obtain ⟨Q74, h74f, hclear1, h74z, _hdvd74⟩ :=
    alignedSquare_remainingNumerator_succ_dvd610 h0 Q73 rho j a 1
      (by decide) hh0 hdegree hroot h73z hclear2 hderiv
  obtain ⟨Q75, h75f⟩ :=
    alignedSquare_linearPolynomial_dvd_of_eval_eq_zero610 h0 Q74 a
      hdegree hroot h74z
  have hclear0 :
      algebraMap k[X] (RatFunc k) Q75 = rho := by
    simpa [pow_zero, one_mul] using
      alignedSquare_algebraMap_cancel_one_clearing610 h0 Q74 Q75 rho 0
        hh0 h75f (by simpa [zero_add, pow_one] using hclear1)
  exact ⟨Q68, Q69, Q70, Q71, Q72, Q73, Q74, Q75, hjet14, h68z, h69f,
    h69z, h70f, h70z, h71f, h71z, h72f, h72z, h73f, h73z, h74f, h74z,
    h75f, hclear0⟩

#print axioms alignedSquareW1Complement_orders69to75_remaining_dvd

theorem alignedSquareW1Complement_order75_false_of_simplePole
    (h0 w1n e1b e3b a2b a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 (h0 * w1n) (h0 * e1b) (h0 * e3b) (h0 * a2b) a1 a0 b8 b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
    (hj : j ≠ 0) : False := by
  obtain ⟨Q68, Q69, Q70, Q71, Q72, Q73, Q74, Q75, hjet14, _h68z, h69f,
      _h69z, h70f, _h70z, h71f, _h71z, h72f, _h72z, h73f, _h73z, h74f,
      _h74z, h75f, hclear0⟩ :=
    alignedSquareW1Complement_orders69to75_remaining_dvd h0 w1n e1b e3b a2b a1 a0 b8 b7 b6 b5 b4 b3 b2 b1
      rho j a hh0 hdegree hroot hclear hderiv
  have hA :
      alignedSquareJetQuotient610 h0 (h0 * w1n) (h0 * e1b) (h0 * e3b) (h0 * a2b) a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 = h0 ^ 21 * Q75 := by
    simp only [hjet14, h69f, h70f, h71f, h72f, h73f, h74f, h75f]
    ring
  have hclear21 :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 (h0 * w1n) (h0 * e1b) (h0 * e3b) (h0 * a2b) a1 a0 b8 b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ 21 * rho := by
    simpa [alignedSquareRemainingPole610] using hclear
  exact alignedSquare_of_pow_dvd_simplePole_ne_zero610 a j h0
    (alignedSquareJetQuotient610 h0 (h0 * w1n) (h0 * e1b) (h0 * e3b) (h0 * a2b) a1 a0 b8 b7 b6 b5 b4 b3 b2 b1) Q75 rho 21 hh0 hroot hA hclear21 hderiv hj

#print axioms alignedSquareW1Complement_order75_false_of_simplePole
/-! ### Generic MixedPair jet: cancel-and-expose at the ceiling -/

/-- The MixedPair jet, as a pole-`21` numerator of a simple-pole
rational function, is divisible by `h₀^{21}`. -/
theorem alignedSquareJetQuotient610_pow_twentyOne_dvd
    (h0 w1 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 w1 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    h0 ^ alignedSquareTowerCeilingDivisibility610 ∣
      alignedSquareJetQuotient610 h0 w1 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 := by
  simpa [alignedSquareTowerCeilingDivisibility610,
    alignedSquareRemainingPole610] using
    alignedSquare_pow_dvd_of_remaining_pole610 h0 (alignedSquareJetQuotient610 h0 w1 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1) rho j a
      21 hh0 hdegree hroot hclear hderiv

#print axioms alignedSquareJetQuotient610_pow_twentyOne_dvd

/-- Source-facing joint order-`75` packet of the aligned-square
`(6,10)` MixedPair jet.  After `h₀^{21}` the remaining factor is
`rho`; `j ≠ 0` is impossible.  Both live MixedPair limbs are special
cases of this clearing (the `w₁ = 0` peel and the `μ = 0` `q₈` peel).
The chamber is not closed on the raw M1M2 hypotheses: the
source-primitive identity identifying the jet with a clearing of
`alignedSquarePeeledPrimitive610` is not in this file. -/
theorem alignedSquareFace610_order75Grandchildren
    (h0 w1 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 w1 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
    (hj : j ≠ 0) : False := by
  obtain ⟨Q, hQ⟩ :=
    alignedSquareJetQuotient610_pow_twentyOne_dvd h0 w1 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 rho
      j a hh0 hdegree hroot hclear hderiv
  have hclear21 :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 w1 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ 21 * rho := by
    simpa [alignedSquareRemainingPole610] using hclear
  exact alignedSquare_of_pow_dvd_simplePole_ne_zero610 a j h0
    (alignedSquareJetQuotient610 h0 w1 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1) Q rho 21 hh0 hroot hQ hclear21 hderiv hj

#print axioms alignedSquareFace610_order75Grandchildren

/-- Same contradiction on the `w₁ = h₀ w₁n` peel, as a special case
of the generic packet. -/
theorem alignedSquareFace610_order75Grandchildren_w1Peel
    (h0 w1n e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
    (hj : j ≠ 0) : False :=
  alignedSquareW1Peel_order75_false_of_simplePole h0 w1n e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 rho
    j a hh0 hdegree hroot hclear hderiv hj

#print axioms alignedSquareFace610_order75Grandchildren_w1Peel

/-- Same contradiction on the frozen `w₁ = 0` limb. -/
theorem alignedSquareFace610_order75Grandchildren_w1Zero
    (h0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
    (hj : j ≠ 0) : False :=
  alignedSquareW1Zero_order75_false_of_simplePole h0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 rho
    j a hh0 hdegree hroot hclear hderiv hj

#print axioms alignedSquareFace610_order75Grandchildren_w1Zero

/-- Same contradiction on the `μ = 0` limb after the pole-`21` `q₈`
peel. -/
theorem alignedSquareFace610_order75Grandchildren_muZeroQ8
    (h0 w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0 (h0 * b8n) b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
    (hj : j ≠ 0) : False :=
  alignedSquareMuZeroQ8_order75_false_of_simplePole h0 w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 rho
    j a hh0 hdegree hroot hclear hderiv hj

#print axioms alignedSquareFace610_order75Grandchildren_muZeroQ8

end AlignedSquareTowerCeilingHeads610

end Max11DegreeRoutes
