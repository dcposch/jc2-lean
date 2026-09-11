import Fable810ScaleZeroTwelfthDefectScratch

/-! Part 17 of 37 of `Fable810ScaleZeroThirteenthDefectScratch`, split so that no single module elaborates them all
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

section Depression810FourteenthClearing

variable {F : Type*} [Field F] [CharZero F]


set_option maxHeartbeats 400000000 in
/-- SPEED (recipe R2, `scripts/coord/LEAN_SPEED_REPORT.md` §7): the weight-`98`
clearing of `xiResidual810` carried out on the *atoms* rather than on the fully
substituted source polynomials.  `xiResidual810` is weighted homogeneous, so
substituting `X_i = n_i / (d_i h^(e_i))` makes `8796093022208 * h^98 * xiResidual810`
a polynomial in `h, n_*` — 111 monomials. -/
def speedXiResidual810Scaled98 (h nL nA nB nC nD nE nF nG nP nQ nR nS nT nU nV nW : F) : F :=
    - (18144 : F) * h ^ 7 * nL * nA ^ 5 * nB
    + (10080 : F) * h ^ 7 * nL * nA ^ 4 * nD
    + (10080 : F) * h ^ 7 * nL * nA ^ 3 * nB * nC
    - (1440 : F) * h ^ 7 * nL * nA ^ 3 * nF
    + (161280 : F) * h ^ 7 * nL * nA ^ 2 * nB ^ 3
    - (4320 : F) * h ^ 7 * nL * nA ^ 2 * nB * nE
    - (4320 : F) * h ^ 7 * nL * nA ^ 2 * nC * nD
    - (138240 : F) * h ^ 7 * nL * nA * nB ^ 2 * nD
    - (1080 : F) * h ^ 7 * nL * nA * nB * nC ^ 2
    + (216 : F) * h ^ 7 * nL * nA * nB * nG
    + (432 : F) * h ^ 7 * nL * nA * nC * nF
    + (1728 : F) * h ^ 7 * nL * nA * nD * nE
    - (11520 : F) * h ^ 7 * nL * nB ^ 3 * nC
    + (6912 : F) * h ^ 7 * nL * nB ^ 2 * nF
    + (432 : F) * h ^ 7 * nL * nB * nC * nE
    + (27648 : F) * h ^ 7 * nL * nB * nD ^ 2
    + (216 : F) * h ^ 7 * nL * nC ^ 2 * nD
    - (72 : F) * h ^ 7 * nL * nD * nG
    - (144 : F) * h ^ 7 * nL * nE * nF
    + (1320 : F) * nA ^ 7
    - (336 : F) * nA ^ 6 * nP
    - (1260 : F) * nA ^ 5 * nC
    + (168 : F) * nA ^ 5 * nR
    - (100800 : F) * nA ^ 4 * nB ^ 2
    + (15680 : F) * nA ^ 4 * nB * nQ
    + (280 : F) * nA ^ 4 * nC * nP
    + (700 : F) * nA ^ 4 * nE
    - (40 : F) * nA ^ 4 * nT
    + (17920 : F) * nA ^ 3 * nB ^ 2 * nP
    + (89600 : F) * nA ^ 3 * nB * nD
    - (1600 : F) * nA ^ 3 * nB * nS
    + (350 : F) * nA ^ 3 * nC ^ 2
    - (120 : F) * nA ^ 3 * nC * nR
    - (8960 : F) * nA ^ 3 * nD * nQ
    - (160 : F) * nA ^ 3 * nE * nP
    - (50 : F) * nA ^ 3 * nG
    + (4 : F) * nA ^ 3 * nV
    + (33600 : F) * nA ^ 2 * nB ^ 2 * nC
    - (5760 : F) * nA ^ 2 * nB ^ 2 * nR
    - (6720 : F) * nA ^ 2 * nB * nC * nQ
    - (15360 : F) * nA ^ 2 * nB * nD * nP
    - (9600 : F) * nA ^ 2 * nB * nF
    + (576 : F) * nA ^ 2 * nB * nU
    - (60 : F) * nA ^ 2 * nC ^ 2 * nP
    - (300 : F) * nA ^ 2 * nC * nE
    + (24 : F) * nA ^ 2 * nC * nT
    - (19200 : F) * nA ^ 2 * nD ^ 2
    + (960 : F) * nA ^ 2 * nD * nS
    + (72 : F) * nA ^ 2 * nE * nR
    + (1344 : F) * nA ^ 2 * nF * nQ
    + (12 : F) * nA ^ 2 * nG * nP
    + (179200 : F) * nA * nB ^ 4
    - (71680 : F) * nA * nB ^ 3 * nQ
    - (3840 : F) * nA * nB ^ 2 * nC * nP
    - (9600 : F) * nA * nB ^ 2 * nE
    + (768 : F) * nA * nB ^ 2 * nT
    - (19200 : F) * nA * nB * nC * nD
    + (480 : F) * nA * nB * nC * nS
    + (4608 : F) * nA * nB * nD * nR
    + (2688 : F) * nA * nB * nE * nQ
    + (1536 : F) * nA * nB * nF * nP
    - (16 : F) * nA * nB * nW
    - (25 : F) * nA * nC ^ 3
    + (18 : F) * nA * nC ^ 2 * nR
    + (2688 : F) * nA * nC * nD * nQ
    + (48 : F) * nA * nC * nE * nP
    + (15 : F) * nA * nC * nG
    - (2 : F) * nA * nC * nV
    + (3072 : F) * nA * nD ^ 2 * nP
    + (3840 : F) * nA * nD * nF
    - (384 : F) * nA * nD * nU
    + (60 : F) * nA * nE ^ 2
    - (16 : F) * nA * nE * nT
    - (160 : F) * nA * nF * nS
    - (6 : F) * nA * nG * nR
    - (10240 : F) * nB ^ 4 * nP
    - (102400 : F) * nB ^ 3 * nD
    + (2560 : F) * nB ^ 3 * nS
    - (1200 : F) * nB ^ 2 * nC ^ 2
    + (576 : F) * nB ^ 2 * nC * nR
    + (43008 : F) * nB ^ 2 * nD * nQ
    + (768 : F) * nB ^ 2 * nE * nP
    + (240 : F) * nB ^ 2 * nG
    - (32 : F) * nB ^ 2 * nV
    + (336 : F) * nB * nC ^ 2 * nQ
    + (1536 : F) * nB * nC * nD * nP
    + (960 : F) * nB * nC * nF
    - (96 : F) * nB * nC * nU
    + (3840 : F) * nB * nD * nE
    - (512 : F) * nB * nD * nT
    - (160 : F) * nB * nE * nS
    - (384 : F) * nB * nF * nR
    - (112 : F) * nB * nG * nQ
    + (2 : F) * nC ^ 3 * nP
    + (15 : F) * nC ^ 2 * nE
    - (2 : F) * nC ^ 2 * nT
    + (1920 : F) * nC * nD ^ 2
    - (160 : F) * nC * nD * nS
    - (12 : F) * nC * nE * nR
    - (224 : F) * nC * nF * nQ
    - (2 : F) * nC * nG * nP
    - (768 : F) * nD ^ 2 * nR
    - (896 : F) * nD * nE * nQ
    - (512 : F) * nD * nF * nP
    + (16 : F) * nD * nW
    - (8 : F) * nE ^ 2 * nP
    - (5 : F) * nE * nG
    + (2 : F) * nE * nV
    - (160 : F) * nF ^ 2
    + (96 : F) * nF * nU
    + (2 : F) * nG * nT


end Depression810FourteenthClearing
end Max11DegreeRoutes
end
