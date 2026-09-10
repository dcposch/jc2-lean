import Fable610ScaleZeroTwelfthDefectSpeedTPart02Scratch

/-! # Scale-zero twelfth cleared defect for the normalized `(6,10)`, `H = 0` leaf

Continuation of `Fable610ScaleZeroEleventhDefectScratch` on the constant
core `H = (C t)²`.  The eleventh packet already forces the discriminator
`N`, the weight-fifty-five defect `κ`, and the weight-sixty defect `λ`
to ground constants, including the exact selectors
`3134566563840 p₀ q₅ h⁵⁰` and `172186884 p₀ q₄ h⁵⁶`.  This file
consumes the next unused Keller coefficient, the degree-`2` Jacobian
row

```
(p₂)' (1 q₁) + (p₁)' (2 q₂) + (p₀)' (3 q₃)
  - (3 p₃) q₀' - (2 p₂) q₁' - (1 p₁) q₂' = 0
```

of the same monic depression.  After the sextic change that kills `z⁵`,
that row is `3 U E' + 2 V D' + W C' - D V' - 2 C W' - 3 B X' = 0`.
The derivative `X'` is eliminated through the degree-`5` row and `W'`
through the degree-`6` row.  Unlike the higher rows, the reduced
`1`-form of the degree-`2` row is not exact on its own: its exterior
derivative is `-3 dA ∧ dκ`, so the already-consumed degree-`4` row
re-enters with the polynomial coefficient `-(1/12) A`, and the first
integral `μ` obeys `d μ = (1/6)·row₂ - (1/12)·A·row₄`.  The `μ`
formula, its weight-sixty-five clearing by `12582912 h⁶⁵`, the solved
derivative forms, and the aligned `227`-monomial specialization were
derived and cross-checked independently (closedness of the corrected
`1`-form, the identity `d μ = (1/6) row₂ - (1/12) A row₄`, and a
rational end-to-end evaluation of the cleared `285`-monomial
polynomial).  The derivation-in-zero reduction keeps the sub-residuals
opaque so the tower hypotheses fire, and supplies the complete
constant-derivative kill set from `d (1/2) = 0` through
`d (77/15552) = 0` and `d (A⁶)`, `d (B⁴)`, `d (C³)`.

The degree-`5` iota first integral, the exact `18 q₀ h⁵⁰` residual, the
weight-fifty-five kappa selector `3134566563840 p₀ q₅ h⁵⁰`, and the
weight-sixty lambda selector `172186884 p₀ q₄ h⁵⁶` are preserved and
not cleared to zero.  No total-degree or twice-prime theorem is used.
A constant scale has no finite root, so no root-jet packet exists at
this scale.  Both the vanishing and the nonzero constant branches of
`λ` and of the weight-sixty and weight-sixty-five defects are kept.
The packet does not close the leaf: unused Jacobian coefficients start
at degree `1`.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

set_option maxRecDepth 1000000

section ScaleZeroTwelfthDefect610

variable {k : Type*} [Field k] [CharZero k]

/-! ## Literal next Keller coefficient -/


section Depression610Thirteenth

variable {F : Type*} [Field F] [CharZero F]


-- Fix the scalar carrier before elaborating the large arithmetic tree.
local infixl:65 (priority := high) " + " => (HAdd.hAdd (α := F) (β := F) (γ := F))
local infixl:65 (priority := high) " - " => (HSub.hSub (α := F) (β := F) (γ := F))
local infixl:70 (priority := high) " * " => (HMul.hMul (α := F) (β := F) (γ := F))
local infixl:70 (priority := high) " / " => (HDiv.hDiv (α := F) (β := F) (γ := F))
local infixr:80 (priority := high) " ^ " => (HPow.hPow (α := F) (β := Nat) (γ := F))
local prefix:75 (priority := high) "-" => (Neg.neg (α := F))

set_option maxHeartbeats 64000000 in
/-- Clearing the first integral `μ` of the degree-`2` row against `h⁶⁵`
on the ninth-power face. -/
theorem thirteenthDefect_eq_clearedMu610
    (h a5 a4 a3 a2 a1 a0 b9 b8 b7 b6 b5 b4 b3 b2 b1 lambda : F)
    (hh : h ≠ 0)
    (hN : 5 * a5 * h ^ 4 - 3 * b9 = lambda * h ^ 9) :
    (12582912 : F) * h ^ 65 *
        muResidual610
          (depressedL610 h (sexticDepressionR610 h a5) b9)
          (depressedA610 h (sexticDepressionR610 h a5) a5 a4)
          (depressedB610 h (sexticDepressionR610 h a5) a5 a4 a3)
          (depressedC610 h (sexticDepressionR610 h a5) a5 a4 a3 a2)
          (depressedD610 h (sexticDepressionR610 h a5) a5 a4 a3 a2 a1)
          (depressedE610 h (sexticDepressionR610 h a5) a5 a4 a3 a2 a1
            a0)
          (depressedP610 h (sexticDepressionR610 h a5) b9 b8)
          (depressedQ610 h (sexticDepressionR610 h a5) b9 b8 b7)
          (depressedR610 h (sexticDepressionR610 h a5) b9 b8 b7 b6)
          (depressedS610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5)
          (depressedT610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5
            b4)
          (depressedU610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5
            b4 b3)
          (depressedV610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5
            b4 b3 b2)
          (depressedW610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5
            b4 b3 b2 b1) =
    -(180880 : F) * a5 ^ 13
    + (88179 : F) * a5 ^ 12 * h ^ 5 * lambda
    + (2015520 : F) * a4 * a5 ^ 11 * h ^ 6
    + (268736 : F) * a5 ^ 11 * b8 * h ^ 2
    - (2139280 : F) * a3 * a5 ^ 10 * h ^ 12
    - (1108536 : F) * a4 * a5 ^ 10 * h ^ 11 * lambda
    - (272272 : F) * a5 ^ 10 * b7 * h ^ 8
    + (2288000 : F) * a2 * a5 ^ 9 * h ^ 18
    + (1166880 : F) * a3 * a5 ^ 9 * h ^ 17 * lambda
    - (7779200 : F) * a4 ^ 2 * a5 ^ 9 * h ^ 12
    - (3111680 : F) * a4 * a5 ^ 9 * b8 * h ^ 8
    + (274560 : F) * a5 ^ 9 * b6 * h ^ 14
    - (2471040 : F) * a1 * a5 ^ 8 * h ^ 24
    - (1235520 : F) * a2 * a5 ^ 8 * h ^ 23 * lambda
    + (14414400 : F) * a3 * a4 * a5 ^ 8 * h ^ 18
    + (3294720 : F) * a3 * a5 ^ 8 * b8 * h ^ 14
    + (5250960 : F) * a4 ^ 2 * a5 ^ 8 * h ^ 17 * lambda
    + (2882880 : F) * a4 * a5 ^ 8 * b7 * h ^ 14
    - (274560 : F) * a5 ^ 8 * b5 * h ^ 20
    + (2703360 : F) * a0 * a5 ^ 7 * h ^ 30
    + (1317888 : F) * a1 * a5 ^ 7 * h ^ 29 * lambda
    - (13178880 : F) * a2 * a4 * a5 ^ 7 * h ^ 24
    - (3514368 : F) * a2 * a5 ^ 7 * b8 * h ^ 20
    - (6589440 : F) * a3 ^ 2 * a5 ^ 7 * h ^ 24
    - (9884160 : F) * a3 * a4 * a5 ^ 7 * h ^ 23 * lambda
    - (3075072 : F) * a3 * a5 ^ 7 * b7 * h ^ 20
    + (10982400 : F) * a4 ^ 3 * a5 ^ 7 * h ^ 18
    + (13178880 : F) * a4 ^ 2 * a5 ^ 7 * b8 * h ^ 14
    - (2635776 : F) * a4 * a5 ^ 7 * b6 * h ^ 20
    + (270336 : F) * a5 ^ 7 * b4 * h ^ 26
    - (1419264 : F) * a0 * a5 ^ 6 * h ^ 35 * lambda
    + (11827200 : F) * a1 * a4 * a5 ^ 6 * h ^ 30
    + (3784704 : F) * a1 * a5 ^ 6 * b8 * h ^ 26
    + (11827200 : F) * a2 * a3 * a5 ^ 6 * h ^ 30
    + (9225216 : F) * a2 * a4 * a5 ^ 6 * h ^ 29 * lambda
    + (3311616 : F) * a2 * a5 ^ 6 * b7 * h ^ 26
    + (4612608 : F) * a3 ^ 2 * a5 ^ 6 * h ^ 29 * lambda
    - (23063040 : F) * a3 * a4 ^ 2 * a5 ^ 6 * h ^ 24
    - (24600576 : F) * a3 * a4 * a5 ^ 6 * b8 * h ^ 20
    + (2838528 : F) * a3 * a5 ^ 6 * b6 * h ^ 26
    - (11531520 : F) * a4 ^ 3 * a5 ^ 6 * h ^ 23 * lambda
    - (10762752 : F) * a4 ^ 2 * a5 ^ 6 * b7 * h ^ 20
    + (2365440 : F) * a4 * a5 ^ 6 * b5 * h ^ 26
    - (258048 : F) * a5 ^ 6 * b3 * h ^ 32
    - (10321920 : F) * a0 * a4 * a5 ^ 5 * h ^ 36
    - (4128768 : F) * a0 * a5 ^ 5 * b8 * h ^ 32
    - (10321920 : F) * a1 * a3 * a5 ^ 5 * h ^ 36
    - (8515584 : F) * a1 * a4 * a5 ^ 5 * h ^ 35 * lambda
    - (3612672 : F) * a1 * a5 ^ 5 * b7 * h ^ 32
    - (5160960 : F) * a2 ^ 2 * a5 ^ 5 * h ^ 36
    - (8515584 : F) * a2 * a3 * a5 ^ 5 * h ^ 35 * lambda
    + (14192640 : F) * a2 * a4 ^ 2 * a5 ^ 5 * h ^ 30
    + (22708224 : F) * a2 * a4 * a5 ^ 5 * b8 * h ^ 26
    - (3096576 : F) * a2 * a5 ^ 5 * b6 * h ^ 32
    + (14192640 : F) * a3 ^ 2 * a4 * a5 ^ 5 * h ^ 30
    + (11354112 : F) * a3 ^ 2 * a5 ^ 5 * b8 * h ^ 26
    + (27675648 : F) * a3 * a4 ^ 2 * a5 ^ 5 * h ^ 29 * lambda
    + (19869696 : F) * a3 * a4 * a5 ^ 5 * b7 * h ^ 26
    - (2580480 : F) * a3 * a5 ^ 5 * b5 * h ^ 32
    - (24600576 : F) * a4 ^ 3 * a5 ^ 5 * b8 * h ^ 20
    + (8515584 : F) * a4 ^ 2 * a5 ^ 5 * b6 * h ^ 26
    - (2064384 : F) * a4 * a5 ^ 5 * b4 * h ^ 32
    + (229376 : F) * a5 ^ 5 * b2 * h ^ 38
    + (8601600 : F) * a0 * a3 * a5 ^ 4 * h ^ 42
    + (7741440 : F) * a0 * a4 * a5 ^ 4 * h ^ 41 * lambda
    + (4014080 : F) * a0 * a5 ^ 4 * b7 * h ^ 38
    + (8601600 : F) * a1 * a2 * a5 ^ 4 * h ^ 42
    + (7741440 : F) * a1 * a3 * a5 ^ 4 * h ^ 41 * lambda
    - (6451200 : F) * a1 * a4 ^ 2 * a5 ^ 4 * h ^ 36
    - (20643840 : F) * a1 * a4 * a5 ^ 4 * b8 * h ^ 32
    + (3440640 : F) * a1 * a5 ^ 4 * b6 * h ^ 38
    + (3870720 : F) * a2 ^ 2 * a5 ^ 4 * h ^ 41 * lambda
    - (12902400 : F) * a2 * a3 * a4 * a5 ^ 4 * h ^ 36
    - (20643840 : F) * a2 * a3 * a5 ^ 4 * b8 * h ^ 32
    - (21288960 : F) * a2 * a4 ^ 2 * a5 ^ 4 * h ^ 35 * lambda
    - (18063360 : F) * a2 * a4 * a5 ^ 4 * b7 * h ^ 32
    + (2867200 : F) * a2 * a5 ^ 4 * b5 * h ^ 38
    - (2150400 : F) * a3 ^ 3 * a5 ^ 4 * h ^ 36
    - (21288960 : F) * a3 ^ 2 * a4 * a5 ^ 4 * h ^ 35 * lambda
    - (9031680 : F) * a3 ^ 2 * a5 ^ 4 * b7 * h ^ 32
    - (11827200 : F) * a3 * a4 ^ 3 * a5 ^ 4 * h ^ 30
    + (56770560 : F) * a3 * a4 ^ 2 * a5 ^ 4 * b8 * h ^ 26
    - (15482880 : F) * a3 * a4 * a5 ^ 4 * b6 * h ^ 32
    + (2293760 : F) * a3 * a5 ^ 4 * b4 * h ^ 38
    + (11531520 : F) * a4 ^ 4 * a5 ^ 4 * h ^ 29 * lambda
    + (16558080 : F) * a4 ^ 3 * a5 ^ 4 * b7 * h ^ 26
    - (6451200 : F) * a4 ^ 2 * a5 ^ 4 * b5 * h ^ 32
    + (1720320 : F) * a4 * a5 ^ 4 * b3 * h ^ 38
    - (163840 : F) * a5 ^ 4 * b1 * h ^ 44
    - (6553600 : F) * a0 * a2 * a5 ^ 3 * h ^ 48
    - (6881280 : F) * a0 * a3 * a5 ^ 3 * h ^ 47 * lambda
    + (18350080 : F) * a0 * a4 * a5 ^ 3 * b8 * h ^ 38
    - (3932160 : F) * a0 * a5 ^ 3 * b6 * h ^ 44
    - (3276800 : F) * a1 ^ 2 * a5 ^ 3 * h ^ 48
    - (6881280 : F) * a1 * a2 * a5 ^ 3 * h ^ 47 * lambda
    + (18350080 : F) * a1 * a3 * a5 ^ 3 * b8 * h ^ 38
    + (15482880 : F) * a1 * a4 ^ 2 * a5 ^ 3 * h ^ 41 * lambda
    + (16056320 : F) * a1 * a4 * a5 ^ 3 * b7 * h ^ 38
    - (3276800 : F) * a1 * a5 ^ 3 * b5 * h ^ 44
    + (9175040 : F) * a2 ^ 2 * a5 ^ 3 * b8 * h ^ 38
    + (30965760 : F) * a2 * a3 * a4 * a5 ^ 3 * h ^ 41 * lambda
    + (16056320 : F) * a2 * a3 * a5 ^ 3 * b7 * h ^ 38
    + (17203200 : F) * a2 * a4 ^ 3 * a5 ^ 3 * h ^ 36
    - (41287680 : F) * a2 * a4 ^ 2 * a5 ^ 3 * b8 * h ^ 32
    + (13762560 : F) * a2 * a4 * a5 ^ 3 * b6 * h ^ 38
    - (2621440 : F) * a2 * a5 ^ 3 * b4 * h ^ 44
    + (5160960 : F) * a3 ^ 3 * a5 ^ 3 * h ^ 41 * lambda
    + (25804800 : F) * a3 ^ 2 * a4 ^ 2 * a5 ^ 3 * h ^ 36
    - (41287680 : F) * a3 ^ 2 * a4 * a5 ^ 3 * b8 * h ^ 32
    + (6881280 : F) * a3 ^ 2 * a5 ^ 3 * b6 * h ^ 38
    - (28385280 : F) * a3 * a4 ^ 3 * a5 ^ 3 * h ^ 35 * lambda
    - (36126720 : F) * a3 * a4 ^ 2 * a5 ^ 3 * b7 * h ^ 32
    + (11468800 : F) * a3 * a4 * a5 ^ 3 * b5 * h ^ 38
    - (1966080 : F) * a3 * a5 ^ 3 * b3 * h ^ 44
    - (9461760 : F) * a4 ^ 5 * a5 ^ 3 * h ^ 30
    + (18923520 : F) * a4 ^ 4 * a5 ^ 3 * b8 * h ^ 26
    - (10321920 : F) * a4 ^ 3 * a5 ^ 3 * b6 * h ^ 32
    + (4587520 : F) * a4 ^ 2 * a5 ^ 3 * b4 * h ^ 38
    - (1310720 : F) * a4 * a5 ^ 3 * b2 * h ^ 44
    + (3932160 : F) * a0 * a1 * a5 ^ 2 * h ^ 54
    + (5898240 : F) * a0 * a2 * a5 ^ 2 * h ^ 53 * lambda
    + (9830400 : F) * a0 * a3 * a4 * a5 ^ 2 * h ^ 48
    - (15728640 : F) * a0 * a3 * a5 ^ 2 * b8 * h ^ 44
    - (10321920 : F) * a0 * a4 ^ 2 * a5 ^ 2 * h ^ 47 * lambda
    - (13762560 : F) * a0 * a4 * a5 ^ 2 * b7 * h ^ 44
    + (3932160 : F) * a0 * a5 ^ 2 * b5 * h ^ 50
    + (2949120 : F) * a1 ^ 2 * a5 ^ 2 * h ^ 53 * lambda
    + (9830400 : F) * a1 * a2 * a4 * a5 ^ 2 * h ^ 48
    - (15728640 : F) * a1 * a2 * a5 ^ 2 * b8 * h ^ 44
    + (4915200 : F) * a1 * a3 ^ 2 * a5 ^ 2 * h ^ 48
    - (20643840 : F) * a1 * a3 * a4 * a5 ^ 2 * h ^ 47 * lambda
    - (13762560 : F) * a1 * a3 * a5 ^ 2 * b7 * h ^ 44
    - (17203200 : F) * a1 * a4 ^ 3 * a5 ^ 2 * h ^ 42
    + (27525120 : F) * a1 * a4 ^ 2 * a5 ^ 2 * b8 * h ^ 38
    - (11796480 : F) * a1 * a4 * a5 ^ 2 * b6 * h ^ 44
    + (3145728 : F) * a1 * a5 ^ 2 * b4 * h ^ 50
    + (4915200 : F) * a2 ^ 2 * a3 * a5 ^ 2 * h ^ 48
    - (10321920 : F) * a2 ^ 2 * a4 * a5 ^ 2 * h ^ 47 * lambda
    - (6881280 : F) * a2 ^ 2 * a5 ^ 2 * b7 * h ^ 44
    - (10321920 : F) * a2 * a3 ^ 2 * a5 ^ 2 * h ^ 47 * lambda
    - (51609600 : F) * a2 * a3 * a4 ^ 2 * a5 ^ 2 * h ^ 42
    + (55050240 : F) * a2 * a3 * a4 * a5 ^ 2 * b8 * h ^ 38
    - (11796480 : F) * a2 * a3 * a5 ^ 2 * b6 * h ^ 44
    + (15482880 : F) * a2 * a4 ^ 3 * a5 ^ 2 * h ^ 41 * lambda
    + (24084480 : F) * a2 * a4 ^ 2 * a5 ^ 2 * b7 * h ^ 38
    - (9830400 : F) * a2 * a4 * a5 ^ 2 * b5 * h ^ 44
    + (2359296 : F) * a2 * a5 ^ 2 * b3 * h ^ 50
    - (17203200 : F) * a3 ^ 3 * a4 * a5 ^ 2 * h ^ 42
    + (9175040 : F) * a3 ^ 3 * a5 ^ 2 * b8 * h ^ 38
    + (23224320 : F) * a3 ^ 2 * a4 ^ 2 * a5 ^ 2 * h ^ 41 * lambda
    + (24084480 : F) * a3 ^ 2 * a4 * a5 ^ 2 * b7 * h ^ 38
    - (4915200 : F) * a3 ^ 2 * a5 ^ 2 * b5 * h ^ 44
    + (32256000 : F) * a3 * a4 ^ 4 * a5 ^ 2 * h ^ 36
    - (41287680 : F) * a3 * a4 ^ 3 * a5 ^ 2 * b8 * h ^ 32
    + (20643840 : F) * a3 * a4 ^ 2 * a5 ^ 2 * b6 * h ^ 38
    - (7864320 : F) * a3 * a4 * a5 ^ 2 * b4 * h ^ 44
    + (1572864 : F) * a3 * a5 ^ 2 * b2 * h ^ 50
    - (4257792 : F) * a4 ^ 5 * a5 ^ 2 * h ^ 35 * lambda
    - (9031680 : F) * a4 ^ 4 * a5 ^ 2 * b7 * h ^ 32
    + (5734400 : F) * a4 ^ 3 * a5 ^ 2 * b5 * h ^ 38
    - (2949120 : F) * a4 ^ 2 * a5 ^ 2 * b3 * h ^ 44
    + (786432 : F) * a4 * a5 ^ 2 * b1 * h ^ 50
    - (4718592 : F) * a0 * a1 * a5 * h ^ 59 * lambda
    - (15728640 : F) * a0 * a2 * a4 * a5 * h ^ 54
    + (12582912 : F) * a0 * a2 * a5 * b8 * h ^ 50
    - (7864320 : F) * a0 * a3 ^ 2 * a5 * h ^ 54
    + (11796480 : F) * a0 * a3 * a4 * a5 * h ^ 53 * lambda
    + (11010048 : F) * a0 * a3 * a5 * b7 * h ^ 50
    + (13107200 : F) * a0 * a4 ^ 3 * a5 * h ^ 48
    - (15728640 : F) * a0 * a4 ^ 2 * a5 * b8 * h ^ 44
    + (9437184 : F) * a0 * a4 * a5 * b6 * h ^ 50
    - (4194304 : F) * a0 * a5 * b4 * h ^ 56
    - (7864320 : F) * a1 ^ 2 * a4 * a5 * h ^ 54
    + (6291456 : F) * a1 ^ 2 * a5 * b8 * h ^ 50
    - (15728640 : F) * a1 * a2 * a3 * a5 * h ^ 54
    + (11796480 : F) * a1 * a2 * a4 * a5 * h ^ 53 * lambda
    + (11010048 : F) * a1 * a2 * a5 * b7 * h ^ 50
    + (5898240 : F) * a1 * a3 ^ 2 * a5 * h ^ 53 * lambda
    + (39321600 : F) * a1 * a3 * a4 ^ 2 * a5 * h ^ 48
    - (31457280 : F) * a1 * a3 * a4 * a5 * b8 * h ^ 44
    + (9437184 : F) * a1 * a3 * a5 * b6 * h ^ 50
    - (6881280 : F) * a1 * a4 ^ 3 * a5 * h ^ 47 * lambda
    - (13762560 : F) * a1 * a4 ^ 2 * a5 * b7 * h ^ 44
    + (7864320 : F) * a1 * a4 * a5 * b5 * h ^ 50
    - (3145728 : F) * a1 * a5 * b3 * h ^ 56
    - (2621440 : F) * a2 ^ 3 * a5 * h ^ 54
    + (5898240 : F) * a2 ^ 2 * a3 * a5 * h ^ 53 * lambda
    + (19660800 : F) * a2 ^ 2 * a4 ^ 2 * a5 * h ^ 48
    - (15728640 : F) * a2 ^ 2 * a4 * a5 * b8 * h ^ 44
    + (4718592 : F) * a2 ^ 2 * a5 * b6 * h ^ 50
    + (39321600 : F) * a2 * a3 ^ 2 * a4 * a5 * h ^ 48
    - (15728640 : F) * a2 * a3 ^ 2 * a5 * b8 * h ^ 44
    - (20643840 : F) * a2 * a3 * a4 ^ 2 * a5 * h ^ 47 * lambda
    - (27525120 : F) * a2 * a3 * a4 * a5 * b7 * h ^ 44
    + (7864320 : F) * a2 * a3 * a5 * b5 * h ^ 50
    - (17203200 : F) * a2 * a4 ^ 4 * a5 * h ^ 42
    + (18350080 : F) * a2 * a4 ^ 3 * a5 * b8 * h ^ 38
    - (11796480 : F) * a2 * a4 ^ 2 * a5 * b6 * h ^ 44
    + (6291456 : F) * a2 * a4 * a5 * b4 * h ^ 50
    - (2097152 : F) * a2 * a5 * b2 * h ^ 56
    + (3276800 : F) * a3 ^ 4 * a5 * h ^ 48
    - (6881280 : F) * a3 ^ 3 * a4 * a5 * h ^ 47 * lambda
    - (4587520 : F) * a3 ^ 3 * a5 * b7 * h ^ 44
    - (34406400 : F) * a3 ^ 2 * a4 ^ 3 * a5 * h ^ 42
    + (27525120 : F) * a3 ^ 2 * a4 ^ 2 * a5 * b8 * h ^ 38
    - (11796480 : F) * a3 ^ 2 * a4 * a5 * b6 * h ^ 44
    + (3145728 : F) * a3 ^ 2 * a5 * b4 * h ^ 50
    + (7741440 : F) * a3 * a4 ^ 4 * a5 * h ^ 41 * lambda
    + (16056320 : F) * a3 * a4 ^ 3 * a5 * b7 * h ^ 38
    - (9830400 : F) * a3 * a4 ^ 2 * a5 * b5 * h ^ 44
    + (4718592 : F) * a3 * a4 * a5 * b3 * h ^ 50
    - (1048576 : F) * a3 * a5 * b1 * h ^ 56
    + (3440640 : F) * a4 ^ 6 * a5 * h ^ 36
    - (4128768 : F) * a4 ^ 5 * a5 * b8 * h ^ 32
    + (3440640 : F) * a4 ^ 4 * a5 * b6 * h ^ 38
    - (2621440 : F) * a4 ^ 3 * a5 * b4 * h ^ 44
    + (1572864 : F) * a4 ^ 2 * a5 * b2 * h ^ 50
    + (1572864 : F) * a0 ^ 2 * h ^ 65 * lambda
    + (15728640 : F) * a0 * a1 * a4 * h ^ 60
    - (8388608 : F) * a0 * a1 * b8 * h ^ 56
    + (15728640 : F) * a0 * a2 * a3 * h ^ 60
    - (4718592 : F) * a0 * a2 * a4 * h ^ 59 * lambda
    - (7340032 : F) * a0 * a2 * b7 * h ^ 56
    - (2359296 : F) * a0 * a3 ^ 2 * h ^ 59 * lambda
    - (19660800 : F) * a0 * a3 * a4 ^ 2 * h ^ 54
    + (12582912 : F) * a0 * a3 * a4 * b8 * h ^ 50
    - (6291456 : F) * a0 * a3 * b6 * h ^ 56
    + (1966080 : F) * a0 * a4 ^ 3 * h ^ 53 * lambda
    + (5505024 : F) * a0 * a4 ^ 2 * b7 * h ^ 50
    - (5242880 : F) * a0 * a4 * b5 * h ^ 56
    + (6291456 : F) * a0 * b3 * h ^ 62
    + (7864320 : F) * a1 ^ 2 * a3 * h ^ 60
    - (2359296 : F) * a1 ^ 2 * a4 * h ^ 59 * lambda
    - (3670016 : F) * a1 ^ 2 * b7 * h ^ 56
    + (7864320 : F) * a1 * a2 ^ 2 * h ^ 60
    - (4718592 : F) * a1 * a2 * a3 * h ^ 59 * lambda
    - (19660800 : F) * a1 * a2 * a4 ^ 2 * h ^ 54
    + (12582912 : F) * a1 * a2 * a4 * b8 * h ^ 50
    - (6291456 : F) * a1 * a2 * b6 * h ^ 56
    - (19660800 : F) * a1 * a3 ^ 2 * a4 * h ^ 54
    + (6291456 : F) * a1 * a3 ^ 2 * b8 * h ^ 50
    + (5898240 : F) * a1 * a3 * a4 ^ 2 * h ^ 53 * lambda
    + (11010048 : F) * a1 * a3 * a4 * b7 * h ^ 50
    - (5242880 : F) * a1 * a3 * b5 * h ^ 56
    + (5734400 : F) * a1 * a4 ^ 4 * h ^ 48
    - (5242880 : F) * a1 * a4 ^ 3 * b8 * h ^ 44
    + (4718592 : F) * a1 * a4 ^ 2 * b6 * h ^ 50
    - (4194304 : F) * a1 * a4 * b4 * h ^ 56
    + (4194304 : F) * a1 * b2 * h ^ 62
    - (786432 : F) * a2 ^ 3 * h ^ 59 * lambda
    - (19660800 : F) * a2 ^ 2 * a3 * a4 * h ^ 54
    + (6291456 : F) * a2 ^ 2 * a3 * b8 * h ^ 50
    + (2949120 : F) * a2 ^ 2 * a4 ^ 2 * h ^ 53 * lambda
    + (5505024 : F) * a2 ^ 2 * a4 * b7 * h ^ 50
    - (2621440 : F) * a2 ^ 2 * b5 * h ^ 56
    - (6553600 : F) * a2 * a3 ^ 3 * h ^ 54
    + (5898240 : F) * a2 * a3 ^ 2 * a4 * h ^ 53 * lambda
    + (5505024 : F) * a2 * a3 ^ 2 * b7 * h ^ 50
    + (22937600 : F) * a2 * a3 * a4 ^ 3 * h ^ 48
    - (15728640 : F) * a2 * a3 * a4 ^ 2 * b8 * h ^ 44
    + (9437184 : F) * a2 * a3 * a4 * b6 * h ^ 50
    - (4194304 : F) * a2 * a3 * b4 * h ^ 56
    - (1720320 : F) * a2 * a4 ^ 4 * h ^ 47 * lambda
    - (4587520 : F) * a2 * a4 ^ 3 * b7 * h ^ 44
    + (3932160 : F) * a2 * a4 ^ 2 * b5 * h ^ 50
    - (3145728 : F) * a2 * a4 * b3 * h ^ 56
    + (2097152 : F) * a2 * b1 * h ^ 62
    + (491520 : F) * a3 ^ 4 * h ^ 53 * lambda
    + (11468800 : F) * a3 ^ 3 * a4 ^ 2 * h ^ 48
    - (5242880 : F) * a3 ^ 3 * a4 * b8 * h ^ 44
    + (1572864 : F) * a3 ^ 3 * b6 * h ^ 50
    - (3440640 : F) * a3 ^ 2 * a4 ^ 3 * h ^ 47 * lambda
    - (6881280 : F) * a3 ^ 2 * a4 ^ 2 * b7 * h ^ 44
    + (3932160 : F) * a3 ^ 2 * a4 * b5 * h ^ 50
    - (1572864 : F) * a3 ^ 2 * b3 * h ^ 56
    - (5160960 : F) * a3 * a4 ^ 5 * h ^ 42
    + (4587520 : F) * a3 * a4 ^ 4 * b8 * h ^ 38
    - (3932160 : F) * a3 * a4 ^ 3 * b6 * h ^ 44
    + (3145728 : F) * a3 * a4 ^ 2 * b4 * h ^ 50
    - (2097152 : F) * a3 * a4 * b2 * h ^ 56
    + (258048 : F) * a4 ^ 6 * h ^ 41 * lambda
    + (802816 : F) * a4 ^ 5 * b7 * h ^ 38
    - (819200 : F) * a4 ^ 4 * b5 * h ^ 44
    + (786432 : F) * a4 ^ 3 * b3 * h ^ 50
    - (524288 : F) * a4 ^ 2 * b1 * h ^ 56     := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h3 : (3 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h5 : (5 : F) ≠ 0 := by norm_num
  have h6 : (6 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h9 : (9 : F) ≠ 0 := by norm_num
  have h12 : (12 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h18 : (18 : F) ≠ 0 := by norm_num
  have h24 : (24 : F) ≠ 0 := by norm_num
  have h27 : (27 : F) ≠ 0 := by norm_num
  have h32 : (32 : F) ≠ 0 := by norm_num
  have h36 : (36 : F) ≠ 0 := by norm_num
  have h54 : (54 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have h72 : (72 : F) ≠ 0 := by norm_num
  have h81 : (81 : F) ≠ 0 := by norm_num
  have h108 : (108 : F) ≠ 0 := by norm_num
  have h128 : (128 : F) ≠ 0 := by norm_num
  have h144 : (144 : F) ≠ 0 := by norm_num
  have h162 : (162 : F) ≠ 0 := by norm_num
  have h216 : (216 : F) ≠ 0 := by norm_num
  have h243 : (243 : F) ≠ 0 := by norm_num
  have h256 : (256 : F) ≠ 0 := by norm_num
  have h324 : (324 : F) ≠ 0 := by norm_num
  have h432 : (432 : F) ≠ 0 := by norm_num
  have h576 : (576 : F) ≠ 0 := by norm_num
  have h648 : (648 : F) ≠ 0 := by norm_num
  have h729 : (729 : F) ≠ 0 := by norm_num
  have h972 : (972 : F) ≠ 0 := by norm_num
  have h1024 : (1024 : F) ≠ 0 := by norm_num
  have h1296 : (1296 : F) ≠ 0 := by norm_num
  have h1458 : (1458 : F) ≠ 0 := by norm_num
  have h3456 : (3456 : F) ≠ 0 := by norm_num
  have h6561 : (6561 : F) ≠ 0 := by norm_num
  have h7776 : (7776 : F) ≠ 0 := by norm_num
  have h11664 : (11664 : F) ≠ 0 := by norm_num
  have h15552 : (15552 : F) ≠ 0 := by norm_num
  have h31104 : (31104 : F) ≠ 0 := by norm_num
  have h46656 : (46656 : F) ≠ 0 := by norm_num
  have h93312 : (93312 : F) ≠ 0 := by norm_num
  have h186624 : (186624 : F) ≠ 0 := by norm_num
  have h5038848 : (5038848 : F) ≠ 0 := by norm_num
  have h12582912 : (12582912 : F) ≠ 0 := by norm_num
  have hh10 : h ^ 10 ≠ 0 := pow_ne_zero 10 hh
  have hh15 : h ^ 15 ≠ 0 := pow_ne_zero 15 hh
  have hh20 : h ^ 20 ≠ 0 := pow_ne_zero 20 hh
  have hh25 : h ^ 25 ≠ 0 := pow_ne_zero 25 hh
  have hh30 : h ^ 30 ≠ 0 := pow_ne_zero 30 hh
  have hh35 : h ^ 35 ≠ 0 := pow_ne_zero 35 hh
  have hh40 : h ^ 40 ≠ 0 := pow_ne_zero 40 hh
  have hh45 : h ^ 45 ≠ 0 := pow_ne_zero 45 hh
  have hh50 : h ^ 50 ≠ 0 := pow_ne_zero 50 hh
  have hh55 : h ^ 55 ≠ 0 := pow_ne_zero 55 hh
  have hh60 : h ^ 60 ≠ 0 := pow_ne_zero 60 hh
  have hh65 : h ^ 65 ≠ 0 := pow_ne_zero 65 hh
  have hL :
      depressedL610 h (sexticDepressionR610 h a5) b9 = -lambda / 3 :=
    depressedL610_eq_of_ninthPower h a5 b9 lambda hh hN
  have hA :
      depressedA610 h (sexticDepressionR610 h a5) a5 a4 =
        (12 * a4 * h ^ 6 - 5 * a5 ^ 2) / (12 * h ^ 10) :=
    depressedA610_eq_cleared h a5 a4 hh
  have hB :
      depressedB610 h (sexticDepressionR610 h a5) a5 a4 a3 =
        (54 * a3 * h ^ 12 - 36 * a4 * a5 * h ^ 6 + 10 * a5 ^ 3) /
          (54 * h ^ 15) :=
    depressedB610_eq_cleared h a5 a4 a3 hh
  have hC :
      depressedC610 h (sexticDepressionR610 h a5) a5 a4 a3 a2 =
        (144 * a2 * h ^ 18 - 72 * a3 * a5 * h ^ 12 +
            24 * a4 * a5 ^ 2 * h ^ 6 - 5 * a5 ^ 4) /
          (144 * h ^ 20) :=
    depressedC610_eq_cleared h a5 a4 a3 a2 hh
  have hD0 :
      depressedD610 h (sexticDepressionR610 h a5) a5 a4 a3 a2 a1 =
        (324 * a1 * h ^ 24 - 108 * a2 * a5 * h ^ 18 +
            27 * a3 * a5 ^ 2 * h ^ 12 - 6 * a4 * a5 ^ 3 * h ^ 6 +
            a5 ^ 5) /
          (324 * h ^ 25) :=
    depressedD610_eq_cleared h a5 a4 a3 a2 a1 hh
  have hE0 :
      depressedE610 h (sexticDepressionR610 h a5) a5 a4 a3 a2 a1 a0 =
        (46656 * a0 * h ^ 30 - 7776 * a1 * a5 * h ^ 24 +
            1296 * a2 * a5 ^ 2 * h ^ 18 - 216 * a3 * a5 ^ 3 * h ^ 12 +
            36 * a4 * a5 ^ 4 * h ^ 6 - 5 * a5 ^ 6) /
          (46656 * h ^ 30) :=
    depressedE610_eq_cleared h a5 a4 a3 a2 a1 a0 hh
  have hS :
      depressedS610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5 =
        (28 * a5 ^ 5 - 7 * lambda * a5 ^ 4 * h ^ 5 -
            56 * a5 ^ 3 * b8 * h ^ 2 + 126 * a5 ^ 2 * b7 * h ^ 8 -
            216 * a5 * b6 * h ^ 14 + 216 * b5 * h ^ 20) /
          (216 * h ^ 25) :=
    depressedS610_eq_cleared h a5 b9 b8 b7 b6 b5 lambda hh hN
  have hT :
      depressedT610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5 b4 =
        (-175 * a5 ^ 6 + 42 * lambda * a5 ^ 5 * h ^ 5 +
            420 * a5 ^ 4 * b8 * h ^ 2 - 1260 * a5 ^ 3 * b7 * h ^ 8 +
            3240 * a5 ^ 2 * b6 * h ^ 14 - 6480 * a5 * b5 * h ^ 20 +
            7776 * b4 * h ^ 26) /
          (7776 * h ^ 30) :=
    depressedT610_eq_cleared h a5 b9 b8 b7 b6 b5 b4 lambda hh hN
  have hU :
      depressedU610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5 b4
          b3 =
        (30 * a5 ^ 7 - 7 * lambda * a5 ^ 6 * h ^ 5 -
            84 * a5 ^ 5 * b8 * h ^ 2 + 315 * a5 ^ 4 * b7 * h ^ 8 -
            1080 * a5 ^ 3 * b6 * h ^ 14 + 3240 * a5 ^ 2 * b5 * h ^ 20 -
            7776 * a5 * b4 * h ^ 26 + 11664 * b3 * h ^ 32) /
          (11664 * h ^ 35) :=
    depressedU610_eq_cleared h a5 b9 b8 b7 b6 b5 b4 b3 lambda hh hN
  have hV :
      depressedV610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5 b4
          b3 b2 =
        (-35 * a5 ^ 8 + 8 * lambda * a5 ^ 7 * h ^ 5 +
            112 * a5 ^ 6 * b8 * h ^ 2 - 504 * a5 ^ 5 * b7 * h ^ 8 +
            2160 * a5 ^ 4 * b6 * h ^ 14 - 8640 * a5 ^ 3 * b5 * h ^ 20 +
            31104 * a5 ^ 2 * b4 * h ^ 26 - 93312 * a5 * b3 * h ^ 32 +
            186624 * b2 * h ^ 38) /
          (186624 * h ^ 40) :=
    depressedV610_eq_cleared h a5 b9 b8 b7 b6 b5 b4 b3 b2 lambda hh hN
  have hW :
      depressedW610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5 b4
          b3 b2 b1 =
        (40 * a5 ^ 9 - 9 * lambda * a5 ^ 8 * h ^ 5 -
            144 * a5 ^ 7 * b8 * h ^ 2 + 756 * a5 ^ 6 * b7 * h ^ 8 -
            3888 * a5 ^ 5 * b6 * h ^ 14 + 19440 * a5 ^ 4 * b5 * h ^ 20 -
            93312 * a5 ^ 3 * b4 * h ^ 26 + 419904 * a5 ^ 2 * b3 * h ^ 32 -
            1679616 * a5 * b2 * h ^ 38 + 5038848 * b1 * h ^ 44) /
          (5038848 * h ^ 45) :=
    depressedW610_eq_cleared h a5 b9 b8 b7 b6 b5 b4 b3 b2 b1 lambda hh hN
  have hP :
      depressedP610 h (sexticDepressionR610 h a5) b9 b8 =
        (-5 * a5 ^ 2 + 2 * lambda * a5 * h ^ 5 + 4 * b8 * h ^ 2) /
          (4 * h ^ 10) :=
    depressedP610_eq_cleared_ninthPower h a5 b9 b8 lambda hh hN
  have hQ :
      depressedQ610 h (sexticDepressionR610 h a5) b9 b8 b7 =
        (10 * a5 ^ 3 - 3 * lambda * a5 ^ 2 * h ^ 5 -
            12 * a5 * b8 * h ^ 2 + 9 * b7 * h ^ 8) /
          (9 * h ^ 15) :=
    depressedQ610_eq_cleared h a5 b9 b8 b7 lambda hh hN
  have hR :
      depressedR610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 =
        (-210 * a5 ^ 4 + 56 * lambda * a5 ^ 3 * h ^ 5 +
            336 * a5 ^ 2 * b8 * h ^ 2 - 504 * a5 * b7 * h ^ 8 +
            432 * b6 * h ^ 14) /
          (432 * h ^ 20) :=
    depressedR610_eq_cleared h a5 b9 b8 b7 b6 lambda hh hN
  rw [hL, hA, hB, hC, hD0, hE0, hP, hQ, hR, hS, hT, hU, hV, hW,
    speedMuResidual610Scaled65_eq h hh]
  simp only [speedMuResidual610Scaled65]
  ring


end Depression610Thirteenth

end ScaleZeroTwelfthDefect610
end Max11DegreeRoutes
end
