import Fable810ScaleZeroFourteenthDefectPart19Scratch

/-! Part 20 of 40 of `Fable810ScaleZeroFourteenthDefectScratch`, split so that no single module elaborates them all
at once.  Statements are unchanged. -/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

set_option maxRecDepth 1000000

section Depression810FifteenthClearing

variable {F : Type*} [Field F] [CharZero F]


set_option maxHeartbeats 400000000 in
/-- SPEED (recipe R2, `scripts/coord/LEAN_SPEED_REPORT.md` §7): the weight-`105`
clearing of `ο` carried out on the *atoms* `n_L, …, n_W` rather than on the
expanded source polynomials.  Because `omicronResidual810` is weighted
homogeneous, substituting `X_i = n_i / (d_i h^{e_i})` makes
`2^55 · h^105 · ο` a polynomial in `h, n_L, …, n_W` — 139 monomials. -/
def speedOmicronScaled810 (h nL nA nB nC nD nE nF nG nP nQ nR nS nT nU nV nW : F) : F :=
    (727947 : F) * h ^ 7 * nL * nA ^ 7
    - (711018 : F) * h ^ 7 * nL * nA ^ 5 * nC
    - (56881440 : F) * h ^ 7 * nL * nA ^ 4 * nB ^ 2
    + (406296 : F) * h ^ 7 * nL * nA ^ 4 * nE
    + (52005888 : F) * h ^ 7 * nL * nA ^ 3 * nB * nD
    + (203148 : F) * h ^ 7 * nL * nA ^ 3 * nC ^ 2
    - (30096 : F) * h ^ 7 * nL * nA ^ 3 * nG
    + (19502208 : F) * h ^ 7 * nL * nA ^ 2 * nB ^ 2 * nC
    - (5778432 : F) * h ^ 7 * nL * nA ^ 2 * nB * nF
    - (180576 : F) * h ^ 7 * nL * nA ^ 2 * nC * nE
    - (11556864 : F) * h ^ 7 * nL * nA ^ 2 * nD ^ 2
    + (104011776 : F) * h ^ 7 * nL * nA * nB ^ 4
    - (5778432 : F) * h ^ 7 * nL * nA * nB ^ 2 * nE
    - (11556864 : F) * h ^ 7 * nL * nA * nB * nC * nD
    - (15048 : F) * h ^ 7 * nL * nA * nC ^ 3
    + (9504 : F) * h ^ 7 * nL * nA * nC * nG
    + (2433024 : F) * h ^ 7 * nL * nA * nD * nF
    + (38016 : F) * h ^ 7 * nL * nA * nE ^ 2
    - (61636608 : F) * h ^ 7 * nL * nB ^ 3 * nD
    - (722304 : F) * h ^ 7 * nL * nB ^ 2 * nC ^ 2
    + (152064 : F) * h ^ 7 * nL * nB ^ 2 * nG
    + (608256 : F) * h ^ 7 * nL * nB * nC * nF
    + (2433024 : F) * h ^ 7 * nL * nB * nD * nE
    + (9504 : F) * h ^ 7 * nL * nC ^ 2 * nE
    + (1216512 : F) * h ^ 7 * nL * nC * nD ^ 2
    - (3456 : F) * h ^ 7 * nL * nE * nG
    - (110592 : F) * h ^ 7 * nL * nF ^ 2
    + (11323620 : F) * nA ^ 6 * nB
    - (737352 : F) * nA ^ 6 * nQ
    - (2528064 : F) * nA ^ 5 * nB * nP
    - (6320160 : F) * nA ^ 5 * nD
    + (90288 : F) * nA ^ 5 * nS
    - (7900200 : F) * nA ^ 4 * nB * nC
    + (1083456 : F) * nA ^ 4 * nB * nR
    + (632016 : F) * nA ^ 4 * nC * nQ
    + (1444608 : F) * nA ^ 4 * nD * nP
    + (902880 : F) * nA ^ 4 * nF
    - (40128 : F) * nA ^ 4 * nU
    - (168537600 : F) * nA ^ 3 * nB ^ 3
    + (40449024 : F) * nA ^ 3 * nB ^ 2 * nQ
    + (1444608 : F) * nA ^ 3 * nB * nC * nP
    + (3611520 : F) * nA ^ 3 * nB * nE
    - (214016 : F) * nA ^ 3 * nB * nT
    + (3611520 : F) * nA ^ 3 * nC * nD
    - (66880 : F) * nA ^ 3 * nC * nS
    - (642048 : F) * nA ^ 3 * nD * nR
    - (374528 : F) * nA ^ 3 * nE * nQ
    - (214016 : F) * nA ^ 3 * nF * nP
    + (1408 : F) * nA ^ 3 * nW
    + (23113728 : F) * nA ^ 2 * nB ^ 3 * nP
    + (173352960 : F) * nA ^ 2 * nB ^ 2 * nD
    - (3210240 : F) * nA ^ 2 * nB ^ 2 * nS
    + (1354320 : F) * nA ^ 2 * nB * nC ^ 2
    - (481536 : F) * nA ^ 2 * nB * nC * nR
    - (35954688 : F) * nA ^ 2 * nB * nD * nQ
    - (642048 : F) * nA ^ 2 * nB * nE * nP
    - (200640 : F) * nA ^ 2 * nB * nG
    + (16896 : F) * nA ^ 2 * nB * nV
    - (140448 : F) * nA ^ 2 * nC ^ 2 * nQ
    - (642048 : F) * nA ^ 2 * nC * nD * nP
    - (401280 : F) * nA ^ 2 * nC * nF
    + (25344 : F) * nA ^ 2 * nC * nU
    - (1605120 : F) * nA ^ 2 * nD * nE
    + (135168 : F) * nA ^ 2 * nD * nT
    + (42240 : F) * nA ^ 2 * nE * nS
    + (101376 : F) * nA ^ 2 * nF * nR
    + (29568 : F) * nA ^ 2 * nG * nQ
    + (28892160 : F) * nA * nB ^ 3 * nC
    - (5136384 : F) * nA * nB ^ 3 * nR
    - (8988672 : F) * nA * nB ^ 2 * nC * nQ
    - (20545536 : F) * nA * nB ^ 2 * nD * nP
    - (12840960 : F) * nA * nB ^ 2 * nF
    + (811008 : F) * nA * nB ^ 2 * nU
    - (160512 : F) * nA * nB * nC ^ 2 * nP
    - (802560 : F) * nA * nB * nC * nE
    + (67584 : F) * nA * nB * nC * nT
    - (51363840 : F) * nA * nB * nD ^ 2
    + (2703360 : F) * nA * nB * nD * nS
    + (202752 : F) * nA * nB * nE * nR
    + (3784704 : F) * nA * nB * nF * nQ
    + (33792 : F) * nA * nB * nG * nP
    - (401280 : F) * nA * nC ^ 2 * nD
    + (10560 : F) * nA * nC ^ 2 * nS
    + (202752 : F) * nA * nC * nD * nR
    + (118272 : F) * nA * nC * nE * nQ
    + (67584 : F) * nA * nC * nF * nP
    - (768 : F) * nA * nC * nW
    + (7569408 : F) * nA * nD ^ 2 * nQ
    + (270336 : F) * nA * nD * nE * nP
    + (84480 : F) * nA * nD * nG
    - (12288 : F) * nA * nD * nV
    + (168960 : F) * nA * nE * nF
    - (18432 : F) * nA * nE * nU
    - (24576 : F) * nA * nF * nT
    - (3840 : F) * nA * nG * nS
    + (46227456 : F) * nB ^ 5
    - (23969792 : F) * nB ^ 4 * nQ
    - (1712128 : F) * nB ^ 3 * nC * nP
    - (4280320 : F) * nB ^ 3 * nE
    + (360448 : F) * nB ^ 3 * nT
    - (12840960 : F) * nB ^ 2 * nC * nD
    + (337920 : F) * nB ^ 2 * nC * nS
    + (3244032 : F) * nB ^ 2 * nD * nR
    + (1892352 : F) * nB ^ 2 * nE * nQ
    + (1081344 : F) * nB ^ 2 * nF * nP
    - (12288 : F) * nB ^ 2 * nW
    - (33440 : F) * nB * nC ^ 3
    + (25344 : F) * nB * nC ^ 2 * nR
    + (3784704 : F) * nB * nC * nD * nQ
    + (67584 : F) * nB * nC * nE * nP
    + (21120 : F) * nB * nC * nG
    - (3072 : F) * nB * nC * nV
    + (4325376 : F) * nB * nD ^ 2 * nP
    + (5406720 : F) * nB * nD * nF
    - (589824 : F) * nB * nD * nU
    + (84480 : F) * nB * nE ^ 2
    - (24576 : F) * nB * nE * nT
    - (245760 : F) * nB * nF * nS
    - (9216 : F) * nB * nG * nR
    + (4928 : F) * nC ^ 3 * nQ
    + (33792 : F) * nC ^ 2 * nD * nP
    + (21120 : F) * nC ^ 2 * nF
    - (2304 : F) * nC ^ 2 * nU
    + (168960 : F) * nC * nD * nE
    - (24576 : F) * nC * nD * nT
    - (7680 : F) * nC * nE * nS
    - (18432 : F) * nC * nF * nR
    - (5376 : F) * nC * nG * nQ
    + (3604480 : F) * nD ^ 3
    - (491520 : F) * nD ^ 2 * nS
    - (73728 : F) * nD * nE * nR
    - (1376256 : F) * nD * nF * nQ
    - (12288 : F) * nD * nG * nP
    - (21504 : F) * nE ^ 2 * nQ
    - (24576 : F) * nE * nF * nP
    + (1024 : F) * nE * nW
    - (7680 : F) * nF * nG
    + (4096 : F) * nF * nV
    + (3072 : F) * nG * nU


end Depression810FifteenthClearing
end Max11DegreeRoutes
end
