import Fable810ScaleTwoAlignedSeventhFaceScratch

/-! # Repair of the ninth-row weighted-derivative identity for the
normalized `(8,10)` scale-two leaf

Untracked working note.  No tracked file was edited.  This file does
**not** import the invalid `Fable810ScaleTwoAlignedEighthFaceScratch`;
it imports only the verified predecessor
`Fable810ScaleTwoAlignedSeventhFaceScratch` and re-proves, under fresh
names, exactly the multiplier identity that failed there
(`Fable810ScaleTwoAlignedEighthFaceScratch.lean:348:46: error:
unsolved goals`).

The retained failure normal form (the `ring_nf` residual of that
unsolved goal) shows both sides agreeing on every `a`-monomial
(`268435456 H²⁸ a₇' b₂ + … − 134217728 H²⁸ a₁ b₈'`) and differing only
in the `b₁` (= `q₁`) tail:

* left side: `+ 536870912 H³¹ H' b₁ − 1073741824 H³² b₁'`;
* right side: `− (eval (-536870912)) H³¹ H' b₁
  + 2 (eval (derivative (-536870912))) H³² b₁
  + 2 (eval (-536870912)) H³² b₁'`.

Substituting the two retained atoms (`eval x (-536870912)
= -536870912` and `derivative (-536870912) = 0`) makes the two sides
literally equal: `−(−536870912) = 536870912 = 4 · 134217728` (the
`63 − 2·31 = 1` weighted-derivative trace) and `2 · (−536870912)
= −1073741824 = −8 · 134217728`.  The stated polynomial identity is
therefore **correct as written**: the leading defect coefficient
`−536870912 q₁ H³¹` has the right magnitude and the right sign.  The
failure was purely tactical.  The ninth defect is the first in the
aligned chain whose body *begins* with a unary-negated numeral
(`-(536870912 : K[X]) * b1 * H ^ 31`; every predecessor defect begins
with a positive term), and the two `simp only` sets of the inherited
proof idiom contain neither `Polynomial.derivative_neg`/`neg_zero`
nor `Polynomial.eval_neg`, so `derivative (-536870912)` and
`eval x (-536870912)` reached the `ring` stage as opaque atoms and
`ring` could not identify them with `0` and `-536870912`.

Exact delta needed to repair the original file: in the proof of
`alignedNinthDefect_weightedDerivative_identity_810` (original lines
349–361) add `Polynomial.derivative_neg, neg_zero` to the derivative
`simp only` set and `Polynomial.eval_neg` to the evaluation
`simp only` set.  No coefficient, sign, statement, or definition
change is needed anywhere.  This file applies exactly that delta to
verbatim copies of `alignedNinthDefect810` (here
`alignedNinthDefectRepair810`) and of the identity theorem (here
`alignedNinthDefectRepair_weightedDerivative_identity_810`).

No closure is claimed.  Only the defect definition and the multiplier
identity are repaired here; the row-consumption, power-relation,
chamber, and root-jet statements of the invalid file are not copied
and remain unverified there.  The next unused Keller row on the
aligned face is still the degree-`7` Jacobian coefficient (the first
row that sees `q₀`; weight-seventy defect, even exponent, hence
chamber-free).  No total-degree or twice-prime theorem is used, no
finite-root shortcut is taken, and no new axiom or `sorry` is
introduced.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

/-! ## Aligned ninth defect (verbatim copy under a fresh name) -/

set_option maxHeartbeats 1600000000 in
/-- Weight-sixty-three defect of the degree-`8` aligned `(8,10)` row.
On the aligned face its square is a polynomial first integral of odd
weight sixty-three, hence chambered.  The only new coefficient is
`q₁`; no `p₀` monomial occurs. -/
def alignedNinthDefectRepair810 {K : Type*} [CommRing K]
    (H a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5 b6 b7 : K[X]) (κ : K) :
    K[X] :=
    -(536870912 : K[X]) * b1 * H ^ 31 -
    (83886080 : K[X]) * a1 * a6 * H ^ 28 -
    (754974720 : K[X]) * a2 * a5 * H ^ 28 -
    (754974720 : K[X]) * a3 * a4 * H ^ 28 +
    (469762048 : K[X]) * a2 * b7 * H ^ 27 +
    (402653184 : K[X]) * a3 * b6 * H ^ 27 +
    (335544320 : K[X]) * a4 * b5 * H ^ 27 +
    (268435456 : K[X]) * a5 * b4 * H ^ 27 +
    (201326592 : K[X]) * a6 * b3 * H ^ 27 +
    (134217728 : K[X]) * a7 * b2 * H ^ 27 +
    (36700160 : K[X]) * a1 * a7 ^ 2 * H ^ 24 +
    (754974720 : K[X]) * a3 * a5 * a7 * H ^ 24 +
    (47185920 : K[X]) * a3 * a6 ^ 2 * H ^ 24 +
    (377487360 : K[X]) * a4 ^ 2 * a7 * H ^ 24 +
    (849346560 : K[X]) * a4 * a5 * a6 * H ^ 24 +
    (267386880 : K[X]) * a5 ^ 3 * H ^ 24 -
    (528482304 : K[X]) * a3 * a7 * b7 * H ^ 23 -
    (528482304 : K[X]) * a4 * a6 * b7 * H ^ 23 -
    (452984832 : K[X]) * a4 * a7 * b6 * H ^ 23 -
    (264241152 : K[X]) * a5 ^ 2 * b7 * H ^ 23 -
    (452984832 : K[X]) * a5 * a6 * b6 * H ^ 23 -
    (377487360 : K[X]) * a5 * a7 * b5 * H ^ 23 -
    (188743680 : K[X]) * a6 ^ 2 * b5 * H ^ 23 -
    (301989888 : K[X]) * a6 * a7 * b4 * H ^ 23 -
    (113246208 : K[X]) * a7 ^ 2 * b3 * H ^ 23 -
    (27525120 : K[X]) * a2 * a7 ^ 3 * H ^ 20 +
    (5898240 : K[X]) * a3 * a6 * a7 ^ 2 * H ^ 20 -
    (796262400 : K[X]) * a4 * a5 * a7 ^ 2 * H ^ 20 -
    (802160640 : K[X]) * a5 ^ 2 * a6 * a7 * H ^ 20 -
    (33423360 : K[X]) * a5 * a6 ^ 3 * H ^ 20 +
    (561512448 : K[X]) * a4 * a7 ^ 2 * b7 * H ^ 19 +
    (1123024896 : K[X]) * a5 * a6 * a7 * b7 * H ^ 19 +
    (481296384 : K[X]) * a5 * a7 ^ 2 * b6 * H ^ 19 +
    (187170816 : K[X]) * a6 ^ 3 * b7 * H ^ 19 +
    (481296384 : K[X]) * a6 ^ 2 * a7 * b6 * H ^ 19 +
    (401080320 : K[X]) * a6 * a7 ^ 2 * b5 * H ^ 19 +
    (106954752 : K[X]) * a7 ^ 3 * b4 * H ^ 19 +
    (21934080 : K[X]) * a3 * a7 ^ 4 * H ^ 16 -
    (8355840 : K[X]) * a4 * a6 * a7 ^ 3 * H ^ 16 +
    (413614080 : K[X]) * a5 ^ 2 * a7 ^ 3 * H ^ 16 -
    (56401920 : K[X]) * a5 * a6 ^ 2 * a7 ^ 2 * H ^ 16 -
    (208896000 : K[X]) * a6 ^ 4 * a7 * H ^ 16 -
    (584908800 : K[X]) * a5 * a7 ^ 3 * b7 * H ^ 15 -
    (877363200 : K[X]) * a6 ^ 2 * a7 ^ 2 * b7 * H ^ 15 -
    (501350400 : K[X]) * a6 * a7 ^ 3 * b6 * H ^ 15 -
    (104448000 : K[X]) * a7 ^ 4 * b5 * H ^ 15 -
    (18278400 : K[X]) * a4 * a7 ^ 5 * H ^ 12 +
    (9792000 : K[X]) * a5 * a6 * a7 ^ 4 * H ^ 12 +
    (613632000 : K[X]) * a6 ^ 3 * a7 ^ 3 * H ^ 12 +
    (603187200 : K[X]) * a6 * a7 ^ 4 * b7 * H ^ 11 +
    (103403520 : K[X]) * a7 ^ 5 * b6 * H ^ 11 +
    (15708000 : K[X]) * a5 * a7 ^ 6 * H ^ 8 -
    (447004800 : K[X]) * a6 ^ 2 * a7 ^ 5 * H ^ 8 -
    (103044480 : K[X]) * a7 ^ 6 * b7 * H ^ 7 +
    (115005000 : K[X]) * a6 * a7 ^ 7 * H ^ 4 -
    (9392075 : K[X]) * a7 ^ 9 +
    Polynomial.C κ *
      ((16777216 : K[X]) * a1 * H ^ 31 -
        (18874368 : K[X]) * a2 * a7 * H ^ 27 -
        (18874368 : K[X]) * a3 * a6 * H ^ 27 -
        (18874368 : K[X]) * a4 * a5 * H ^ 27 +
        (20054016 : K[X]) * a3 * a7 ^ 2 * H ^ 23 +
        (40108032 : K[X]) * a4 * a6 * a7 * H ^ 23 +
        (20054016 : K[X]) * a5 ^ 2 * a7 * H ^ 23 +
        (20054016 : K[X]) * a5 * a6 ^ 2 * H ^ 23 -
        (20889600 : K[X]) * a4 * a7 ^ 3 * H ^ 19 -
        (62668800 : K[X]) * a5 * a6 * a7 ^ 2 * H ^ 19 -
        (20889600 : K[X]) * a6 ^ 3 * a7 * H ^ 19 +
        (21542400 : K[X]) * a5 * a7 ^ 4 * H ^ 15 +
        (43084800 : K[X]) * a6 ^ 2 * a7 ^ 3 * H ^ 15 -
        (22080960 : K[X]) * a6 * a7 ^ 5 * H ^ 11 +
        (3220140 : K[X]) * a7 ^ 7 * H ^ 7)

/-! ## Repaired weighted-derivative identity -/

set_option maxHeartbeats 1600000000 in
/-- Exact combination of the degree-`8` Jacobian expression with the
weighted derivative of `L`.  Every correction on the right-hand side
vanishes on the aligned face with the consumed degree-`15`,
degree-`14`, degree-`13`, degree-`12`, degree-`11`, degree-`10`, and
degree-`9` rows. -/
theorem alignedNinthDefectRepair_weightedDerivative_identity_810 {K : Type*}
    [Field K] [CharZero K]
    (H a0 a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5 b6 b7 b8 b9 : K[X])
    (κ : K) :
    (134217728 : K[X]) * H ^ 28 *
        ((H ^ 4).derivative * b1 +
          a7.derivative * (b2 * (2 : K[X])) +
          a6.derivative * (b3 * (3 : K[X])) +
          a5.derivative * (b4 * (4 : K[X])) +
          a4.derivative * (b5 * (5 : K[X])) +
          a3.derivative * (b6 * (6 : K[X])) +
          a2.derivative * (b7 * (7 : K[X])) +
          a1.derivative * (b8 * (8 : K[X])) +
          a0.derivative * (b9 * (9 : K[X])) -
        ((H ^ 4 * (8 : K[X])) * b1.derivative +
          (a7 * (7 : K[X])) * b2.derivative +
          (a6 * (6 : K[X])) * b3.derivative +
          (a5 * (5 : K[X])) * b4.derivative +
          (a4 * (4 : K[X])) * b5.derivative +
          (a3 * (3 : K[X])) * b6.derivative +
          (a2 * (2 : K[X])) * b7.derivative +
          a1 * b8.derivative)) =
      ((2 : K[X]) * H *
          (alignedNinthDefectRepair810 H a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5
            b6 b7 κ).derivative -
        (63 : K[X]) *
          alignedNinthDefectRepair810 H a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5
            b6 b7 κ * H.derivative) -
        (301989888 : K[X]) * H ^ 28 * a0.derivative *
          ((5 : K[X]) * a7 * H - (4 : K[X]) * b9) +
        ((33554432 : K[X]) * H ^ 25 * a1.derivative +
            (12582912 : K[X]) * a1 * H ^ 24 * H.derivative) *
          ((32 : K[X]) * b8 * H ^ 3 - (40 : K[X]) * a6 * H ^ 4 -
            (5 : K[X]) * a7 ^ 2 - Polynomial.C κ * H ^ 7) -
        (4194304 : K[X]) * H ^ 25 * a1 *
          ((32 : K[X]) * b8 * H ^ 3 - (40 : K[X]) * a6 * H ^ 4 -
            (5 : K[X]) * a7 ^ 2 -
            Polynomial.C κ * H ^ 7).derivative +
        ((4718592 : K[X]) * a2 * H ^ 20 +
            (4128768 : K[X]) * a3 * a7 * H ^ 16 +
            (4128768 : K[X]) * a4 * a6 * H ^ 16 +
            (2064384 : K[X]) * a5 ^ 2 * H ^ 16 -
            (258048 : K[X]) * a4 * a7 ^ 2 * H ^ 12 -
            (516096 : K[X]) * a5 * a6 * a7 * H ^ 12 -
            (86016 : K[X]) * a6 ^ 3 * H ^ 12 +
            (96768 : K[X]) * a5 * a7 ^ 3 * H ^ 8 +
            (145152 : K[X]) * a6 ^ 2 * a7 ^ 2 * H ^ 8 -
            (51408 : K[X]) * a6 * a7 ^ 4 * H ^ 4 +
            (5355 : K[X]) * a7 ^ 6) *
          ((2 : K[X]) * H *
              (alignedThirdDefect810 H a5 a6 a7 b7 κ).derivative -
            (21 : K[X]) * alignedThirdDefect810 H a5 a6 a7 b7 κ *
              H.derivative) +
        ((589824 : K[X]) * a3 * H ^ 16 +
            (442368 : K[X]) * a4 * a7 * H ^ 12 +
            (442368 : K[X]) * a5 * a6 * H ^ 12 -
            (55296 : K[X]) * a5 * a7 ^ 2 * H ^ 8 -
            (55296 : K[X]) * a6 ^ 2 * a7 * H ^ 8 +
            (23040 : K[X]) * a6 * a7 ^ 3 * H ^ 4 -
            (2592 : K[X]) * a7 ^ 5) *
          (H * (alignedFourthDefect810 H a4 a5 a6 a7 b6 b7 κ).derivative -
            (14 : K[X]) * alignedFourthDefect810 H a4 a5 a6 a7 b6 b7 κ *
              H.derivative) +
        ((36864 : K[X]) * a4 * H ^ 12 +
            (23040 : K[X]) * a5 * a7 * H ^ 8 +
            (11520 : K[X]) * a6 ^ 2 * H ^ 8 -
            (4320 : K[X]) * a6 * a7 ^ 2 * H ^ 4 +
            (495 : K[X]) * a7 ^ 4) *
          ((2 : K[X]) * H *
              (alignedFifthDefect810 H a3 a4 a5 a6 a7 b5 b6 b7
                κ).derivative -
            (35 : K[X]) * alignedFifthDefect810 H a3 a4 a5 a6 a7 b5 b6 b7
              κ * H.derivative) +
        ((18432 : K[X]) * a5 * H ^ 8 + (9216 : K[X]) * a6 * a7 * H ^ 4 -
            (768 : K[X]) * a7 ^ 3) *
          (H * (alignedSixthDefect810 H a2 a3 a4 a5 a6 a7 b4 b5 b6 b7
                κ).derivative -
            (21 : K[X]) * alignedSixthDefect810 H a2 a3 a4 a5 a6 a7 b4 b5
              b6 b7 κ * H.derivative) +
        ((144 : K[X]) * a6 * H ^ 4 + (27 : K[X]) * a7 ^ 2) *
          ((2 : K[X]) * H *
              (alignedSeventhDefect810 H a1 a2 a3 a4 a5 a6 a7 b3 b4 b5
                b6 b7 κ).derivative -
            (49 : K[X]) *
              alignedSeventhDefect810 H a1 a2 a3 a4 a5 a6 a7 b3 b4 b5
                b6 b7 κ * H.derivative) +
        (36 : K[X]) * a7 *
          (H * (alignedEighthDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b2 b3
                b4 b5 b6 b7 κ).derivative -
            (28 : K[X]) *
              alignedEighthDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b2 b3 b4
                b5 b6 b7 κ * H.derivative) := by
  simp only [alignedNinthDefectRepair810, alignedEighthDefect810,
    alignedSeventhDefect810, alignedSixthDefect810, alignedFifthDefect810,
    alignedFourthDefect810, alignedThirdDefect810,
    Polynomial.derivative_sub, Polynomial.derivative_add,
    Polynomial.derivative_mul, Polynomial.derivative_pow,
    Polynomial.derivative_neg, Polynomial.derivative_ofNat,
    Polynomial.derivative_C, neg_zero, nsmul_eq_mul,
    zero_mul, mul_zero, zero_add, add_zero]
  apply Polynomial.funext
  intro x
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_neg, Polynomial.eval_C,
    Polynomial.eval_natCast, Polynomial.eval_ofNat]
  ring

#print axioms alignedNinthDefectRepair_weightedDerivative_identity_810

end Max11DegreeRoutes
