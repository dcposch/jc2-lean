import Fable410ScaleTwoAlignedTenthFacePart01Scratch

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

/-! ## Aligned eleventh defect -/

set_option maxHeartbeats 64000000 in
/-- Cleared eleventh defect of the degree-`2` aligned `(4,10)` row,
kept in factored form through the third through tenth defects.  Every
monomial has exact `H`-weight `33/2`.  The factored head is PURE in
the `p`-letters: no `q`-letter and no `κ`-module at all, and neither
`M₈` nor `M₁₆` appears among the corrections — the first aligned
defect with an empty head module. -/
def alignedEleventhDefect410 {K : Type*} [CommRing K]
    (H a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7 : K[X]) (κ : K) : K[X] :=
  (125829120 : K[X]) * H ^ 16 * a0 ^ 2 * a1 -
    (20971520 : K[X]) * H ^ 14 * a1 ^ 3 * a2 -
    (62914560 : K[X]) * H ^ 14 * a0 * a1 * a2 ^ 2 -
    (62914560 : K[X]) * H ^ 14 * a0 * a1 ^ 2 * a3 -
    (62914560 : K[X]) * H ^ 14 * a0 ^ 2 * a2 * a3 +
    (7864320 : K[X]) * H ^ 12 * a1 * a2 ^ 4 +
    (47185920 : K[X]) * H ^ 12 * a1 ^ 2 * a2 ^ 2 * a3 +
    (15728640 : K[X]) * H ^ 12 * a1 ^ 3 * a3 ^ 2 +
    (31457280 : K[X]) * H ^ 12 * a0 * a2 ^ 3 * a3 +
    (94371840 : K[X]) * H ^ 12 * a0 * a1 * a2 * a3 ^ 2 +
    (15728640 : K[X]) * H ^ 12 * a0 ^ 2 * a3 ^ 3 -
    (3932160 : K[X]) * H ^ 10 * a2 ^ 5 * a3 -
    (39321600 : K[X]) * H ^ 10 * a1 * a2 ^ 3 * a3 ^ 2 -
    (39321600 : K[X]) * H ^ 10 * a1 ^ 2 * a2 * a3 ^ 3 -
    (39321600 : K[X]) * H ^ 10 * a0 * a2 ^ 2 * a3 ^ 3 -
    (19660800 : K[X]) * H ^ 10 * a0 * a1 * a3 ^ 4 +
    (11468800 : K[X]) * H ^ 8 * a2 ^ 4 * a3 ^ 3 +
    (34406400 : K[X]) * H ^ 8 * a1 * a2 ^ 2 * a3 ^ 4 +
    (6881280 : K[X]) * H ^ 8 * a1 ^ 2 * a3 ^ 5 +
    (13762560 : K[X]) * H ^ 8 * a0 * a2 * a3 ^ 5 -
    (10321920 : K[X]) * H ^ 6 * a2 ^ 3 * a3 ^ 5 -
    (10321920 : K[X]) * H ^ 6 * a1 * a2 * a3 ^ 6 -
    (1474560 : K[X]) * H ^ 6 * a0 * a3 ^ 7 +
    (4055040 : K[X]) * H ^ 4 * a2 ^ 2 * a3 ^ 7 +
    (1013760 : K[X]) * H ^ 4 * a1 * a3 ^ 8 -
    (732160 : K[X]) * H ^ 2 * a2 * a3 ^ 9 + (49920 : K[X]) * a3 ^ 11 -
    ((32 : K[X]) * H ^ 2 * a2 - (12 : K[X]) * a3 ^ 2) *
      alignedNinthDefect410 H a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7 κ -
    ((512 : K[X]) * H ^ 4 * a1 - (256 : K[X]) * H ^ 2 * a2 * a3 +
      (64 : K[X]) * a3 ^ 3) *
      alignedEighthDefect410 H a0 a1 a2 a3 b2 b3 b4 b5 b6 b7 κ -
    ((3072 : K[X]) * H ^ 6 * a0 - (384 : K[X]) * H ^ 4 * a2 ^ 2 -
      (768 : K[X]) * H ^ 4 * a1 * a3 + (480 : K[X]) * H ^ 2 * a2 * a3 ^ 2 -
      (90 : K[X]) * a3 ^ 4) *
      alignedSeventhDefect410 H a0 a1 a2 a3 b3 b4 b5 b6 b7 κ -
    ((40960 : K[X]) * H ^ 8 * a1 ^ 2 + (81920 : K[X]) * H ^ 8 * a0 * a2 -
      (10240 : K[X]) * H ^ 6 * a2 ^ 3 -
      (61440 : K[X]) * H ^ 6 * a1 * a2 * a3 -
      (30720 : K[X]) * H ^ 6 * a0 * a3 ^ 2 +
      (26880 : K[X]) * H ^ 4 * a2 ^ 2 * a3 ^ 2 +
      (17920 : K[X]) * H ^ 4 * a1 * a3 ^ 3 -
      (12320 : K[X]) * H ^ 2 * a2 * a3 ^ 4 + (1540 : K[X]) * a3 ^ 6) *
      alignedFifthDefect410 H a0 a1 a2 a3 b5 b6 b7 κ -
    ((786432 : K[X]) * H ^ 10 * a0 * a1 -
      (196608 : K[X]) * H ^ 8 * a1 * a2 ^ 2 -
      (196608 : K[X]) * H ^ 8 * a1 ^ 2 * a3 -
      (393216 : K[X]) * H ^ 8 * a0 * a2 * a3 +
      (98304 : K[X]) * H ^ 6 * a2 ^ 3 * a3 +
      (294912 : K[X]) * H ^ 6 * a1 * a2 * a3 ^ 2 +
      (98304 : K[X]) * H ^ 6 * a0 * a3 ^ 3 -
      (122880 : K[X]) * H ^ 4 * a2 ^ 2 * a3 ^ 3 -
      (61440 : K[X]) * H ^ 4 * a1 * a3 ^ 4 +
      (43008 : K[X]) * H ^ 2 * a2 * a3 ^ 5 - (4608 : K[X]) * a3 ^ 7) *
      alignedFourthDefect410 H a0 a1 a2 a3 b6 b7 κ -
    ((5505024 : K[X]) * H ^ 12 * a0 ^ 2 -
      (1376256 : K[X]) * H ^ 10 * a1 ^ 2 * a2 -
      (1376256 : K[X]) * H ^ 10 * a0 * a2 ^ 2 -
      (2752512 : K[X]) * H ^ 10 * a0 * a1 * a3 +
      (143360 : K[X]) * H ^ 8 * a2 ^ 4 +
      (1720320 : K[X]) * H ^ 8 * a1 * a2 ^ 2 * a3 +
      (860160 : K[X]) * H ^ 8 * a1 ^ 2 * a3 ^ 2 +
      (1720320 : K[X]) * H ^ 8 * a0 * a2 * a3 ^ 2 -
      (645120 : K[X]) * H ^ 6 * a2 ^ 3 * a3 ^ 2 -
      (1290240 : K[X]) * H ^ 6 * a1 * a2 * a3 ^ 3 -
      (322560 : K[X]) * H ^ 6 * a0 * a3 ^ 4 +
      (524160 : K[X]) * H ^ 4 * a2 ^ 2 * a3 ^ 4 +
      (209664 : K[X]) * H ^ 4 * a1 * a3 ^ 5 -
      (148512 : K[X]) * H ^ 2 * a2 * a3 ^ 6 + (13923 : K[X]) * a3 ^ 8) *
      alignedThirdDefect410 H a1 a2 a3 b7 κ

end Max11DegreeRoutes
