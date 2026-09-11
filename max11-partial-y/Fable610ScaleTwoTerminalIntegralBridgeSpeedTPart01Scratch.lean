import Fable610ScaleTwoFifteenthFinalRowScratch
import Grok610ScaleZeroSeventhDefectScratch

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000

section BridgeIotaDepression610

variable {F : Type*} [Field F] [CharZero F]

local infixl:65 (priority := high) " + " => (HAdd.hAdd (α := F[X]) (β := F[X]) (γ := F[X]))
local infixl:65 (priority := high) " - " => (HSub.hSub (α := F[X]) (β := F[X]) (γ := F[X]))
local infixl:70 (priority := high) " * " => (HMul.hMul (α := F[X]) (β := F[X]) (γ := F[X]))
local infixr:80 (priority := high) " ^ " => (HPow.hPow (α := F[X]) (β := Nat) (γ := F[X]))
local prefix:75 (priority := high) "-" => (Neg.neg (α := F[X]))

set_option maxHeartbeats 64000000 in
/-- Polynomial numerator of `18 h⁵⁰ ι` on the ninth-power face. -/
def terminalClearedIotaDefect610
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 b0 : F[X]) (lambda : F) : F[X] :=
    (30 : F[X]) * a0 * a2 * h ^ 48
    - (15 : F[X]) * a0 * a3 * a5 * h ^ 42
    - (9 : F[X]) * a0 * a3 * h ^ 47 * Polynomial.C lambda
    - (30 : F[X]) * a0 * a4 ^ 2 * h ^ 42
    + (18 : F[X]) * a0 * a4 * a5 * h ^ 41 * Polynomial.C lambda
    + (24 : F[X]) * a0 * a4 * b8 * h ^ 38
    + (15 : F[X]) * a0 * a5 ^ 4 * h ^ 30
    - (9 : F[X]) * a0 * a5 ^ 3 * h ^ 35 * Polynomial.C lambda
    - (24 : F[X]) * a0 * a5 ^ 2 * b8 * h ^ 32
    + (21 : F[X]) * a0 * a5 * b7 * h ^ 38
    - (18 : F[X]) * a0 * b6 * h ^ 44
    + (15 : F[X]) * a1 ^ 2 * h ^ 48
    - (15 : F[X]) * a1 * a2 * a5 * h ^ 42
    - (9 : F[X]) * a1 * a2 * h ^ 47 * Polynomial.C lambda
    - (60 : F[X]) * a1 * a3 * a4 * h ^ 42
    + (18 : F[X]) * a1 * a3 * a5 * h ^ 41 * Polynomial.C lambda
    + (24 : F[X]) * a1 * a3 * b8 * h ^ 38
    + (45 : F[X]) * a1 * a4 ^ 2 * a5 * h ^ 36
    + (9 : F[X]) * a1 * a4 ^ 2 * h ^ 41 * Polynomial.C lambda
    + (15 : F[X]) * a1 * a4 * a5 ^ 3 * h ^ 30
    - (27 : F[X]) * a1 * a4 * a5 ^ 2 * h ^ 35 * Polynomial.C lambda
    - (48 : F[X]) * a1 * a4 * a5 * b8 * h ^ 32
    + (21 : F[X]) * a1 * a4 * b7 * h ^ 38
    - (15 : F[X]) * a1 * a5 ^ 5 * h ^ 24
    + (9 : F[X]) * a1 * a5 ^ 4 * h ^ 29 * Polynomial.C lambda
    + (24 : F[X]) * a1 * a5 ^ 3 * b8 * h ^ 26
    - (21 : F[X]) * a1 * a5 ^ 2 * b7 * h ^ 32
    + (18 : F[X]) * a1 * a5 * b6 * h ^ 38
    - (15 : F[X]) * a1 * b5 * h ^ 44
    - (30 : F[X]) * a2 ^ 2 * a4 * h ^ 42
    + (9 : F[X]) * a2 ^ 2 * a5 * h ^ 41 * Polynomial.C lambda
    + (12 : F[X]) * a2 ^ 2 * b8 * h ^ 38
    - (30 : F[X]) * a2 * a3 ^ 2 * h ^ 42
    + (90 : F[X]) * a2 * a3 * a4 * a5 * h ^ 36
    + (18 : F[X]) * a2 * a3 * a4 * h ^ 41 * Polynomial.C lambda
    + (15 : F[X]) * a2 * a3 * a5 ^ 3 * h ^ 30
    - (27 : F[X]) * a2 * a3 * a5 ^ 2 * h ^ 35 * Polynomial.C lambda
    - (48 : F[X]) * a2 * a3 * a5 * b8 * h ^ 32
    + (21 : F[X]) * a2 * a3 * b7 * h ^ 38
    + (30 : F[X]) * a2 * a4 ^ 3 * h ^ 36
    - (45 : F[X]) * a2 * a4 ^ 2 * a5 ^ 2 * h ^ 30
    - (27 : F[X]) * a2 * a4 ^ 2 * a5 * h ^ 35 * Polynomial.C lambda
    - (24 : F[X]) * a2 * a4 ^ 2 * b8 * h ^ 32
    - (30 : F[X]) * a2 * a4 * a5 ^ 4 * h ^ 24
    + (36 : F[X]) * a2 * a4 * a5 ^ 3 * h ^ 29 * Polynomial.C lambda
    + (72 : F[X]) * a2 * a4 * a5 ^ 2 * b8 * h ^ 26
    - (42 : F[X]) * a2 * a4 * a5 * b7 * h ^ 32
    + (18 : F[X]) * a2 * a4 * b6 * h ^ 38
    + (15 : F[X]) * a2 * a5 ^ 6 * h ^ 18
    - (9 : F[X]) * a2 * a5 ^ 5 * h ^ 23 * Polynomial.C lambda
    - (24 : F[X]) * a2 * a5 ^ 4 * b8 * h ^ 20
    + (21 : F[X]) * a2 * a5 ^ 3 * b7 * h ^ 26
    - (18 : F[X]) * a2 * a5 ^ 2 * b6 * h ^ 32
    + (15 : F[X]) * a2 * a5 * b5 * h ^ 38
    - (12 : F[X]) * a2 * b4 * h ^ 44
    + (15 : F[X]) * a3 ^ 3 * a5 * h ^ 36
    + (3 : F[X]) * a3 ^ 3 * h ^ 41 * Polynomial.C lambda
    + (45 : F[X]) * a3 ^ 2 * a4 ^ 2 * h ^ 36
    - (45 : F[X]) * a3 ^ 2 * a4 * a5 ^ 2 * h ^ 30
    - (27 : F[X]) * a3 ^ 2 * a4 * a5 * h ^ 35 * Polynomial.C lambda
    - (24 : F[X]) * a3 ^ 2 * a4 * b8 * h ^ 32
    - (15 : F[X]) * a3 ^ 2 * a5 ^ 4 * h ^ 24
    + (18 : F[X]) * a3 ^ 2 * a5 ^ 3 * h ^ 29 * Polynomial.C lambda
    + (36 : F[X]) * a3 ^ 2 * a5 ^ 2 * b8 * h ^ 26
    - (21 : F[X]) * a3 ^ 2 * a5 * b7 * h ^ 32
    + (9 : F[X]) * a3 ^ 2 * b6 * h ^ 38
    - (75 : F[X]) * a3 * a4 ^ 3 * a5 * h ^ 30
    - (9 : F[X]) * a3 * a4 ^ 3 * h ^ 35 * Polynomial.C lambda
    + (30 : F[X]) * a3 * a4 ^ 2 * a5 ^ 3 * h ^ 24
    + (54 : F[X]) * a3 * a4 ^ 2 * a5 ^ 2 * h ^ 29 * Polynomial.C lambda
    + (72 : F[X]) * a3 * a4 ^ 2 * a5 * b8 * h ^ 26
    - (21 : F[X]) * a3 * a4 ^ 2 * b7 * h ^ 32
    + (45 : F[X]) * a3 * a4 * a5 ^ 5 * h ^ 18
    - (45 : F[X]) * a3 * a4 * a5 ^ 4 * h ^ 23 * Polynomial.C lambda
    - (96 : F[X]) * a3 * a4 * a5 ^ 3 * b8 * h ^ 20
    + (63 : F[X]) * a3 * a4 * a5 ^ 2 * b7 * h ^ 26
    - (36 : F[X]) * a3 * a4 * a5 * b6 * h ^ 32
    + (15 : F[X]) * a3 * a4 * b5 * h ^ 38
    - (15 : F[X]) * a3 * a5 ^ 7 * h ^ 12
    + (9 : F[X]) * a3 * a5 ^ 6 * h ^ 17 * Polynomial.C lambda
    + (24 : F[X]) * a3 * a5 ^ 5 * b8 * h ^ 14
    - (21 : F[X]) * a3 * a5 ^ 4 * b7 * h ^ 20
    + (18 : F[X]) * a3 * a5 ^ 3 * b6 * h ^ 26
    - (15 : F[X]) * a3 * a5 ^ 2 * b5 * h ^ 32
    + (12 : F[X]) * a3 * a5 * b4 * h ^ 38
    - (9 : F[X]) * a3 * b3 * h ^ 44
    - (6 : F[X]) * a4 ^ 5 * h ^ 30
    + (30 : F[X]) * a4 ^ 4 * a5 ^ 2 * h ^ 24
    + (9 : F[X]) * a4 ^ 4 * a5 * h ^ 29 * Polynomial.C lambda
    + (6 : F[X]) * a4 ^ 4 * b8 * h ^ 26
    - (30 : F[X]) * a4 ^ 3 * a5 ^ 3 * h ^ 23 * Polynomial.C lambda
    - (48 : F[X]) * a4 ^ 3 * a5 ^ 2 * b8 * h ^ 20
    + (21 : F[X]) * a4 ^ 3 * a5 * b7 * h ^ 26
    - (6 : F[X]) * a4 ^ 3 * b6 * h ^ 32
    - (30 : F[X]) * a4 ^ 2 * a5 ^ 6 * h ^ 12
    + (27 : F[X]) * a4 ^ 2 * a5 ^ 5 * h ^ 17 * Polynomial.C lambda
    + (60 : F[X]) * a4 ^ 2 * a5 ^ 4 * b8 * h ^ 14
    - (42 : F[X]) * a4 ^ 2 * a5 ^ 3 * b7 * h ^ 20
    + (27 : F[X]) * a4 ^ 2 * a5 ^ 2 * b6 * h ^ 26
    - (15 : F[X]) * a4 ^ 2 * a5 * b5 * h ^ 32
    + (6 : F[X]) * a4 ^ 2 * b4 * h ^ 38
    + (15 : F[X]) * a4 * a5 ^ 8 * h ^ 6
    - (9 : F[X]) * a4 * a5 ^ 7 * h ^ 11 * Polynomial.C lambda
    - (24 : F[X]) * a4 * a5 ^ 6 * b8 * h ^ 8
    + (21 : F[X]) * a4 * a5 ^ 5 * b7 * h ^ 14
    - (18 : F[X]) * a4 * a5 ^ 4 * b6 * h ^ 20
    + (15 : F[X]) * a4 * a5 ^ 3 * b5 * h ^ 26
    - (12 : F[X]) * a4 * a5 ^ 2 * b4 * h ^ 32
    + (9 : F[X]) * a4 * a5 * b3 * h ^ 38
    - (6 : F[X]) * a4 * b2 * h ^ 44
    - (2 : F[X]) * a5 ^ 10
    + (1 : F[X]) * a5 ^ 9 * h ^ 5 * Polynomial.C lambda
    + (3 : F[X]) * a5 ^ 8 * b8 * h ^ 2
    - (3 : F[X]) * a5 ^ 7 * b7 * h ^ 8
    + (3 : F[X]) * a5 ^ 6 * b6 * h ^ 14
    - (3 : F[X]) * a5 ^ 5 * b5 * h ^ 20
    + (3 : F[X]) * a5 ^ 4 * b4 * h ^ 26
    - (3 : F[X]) * a5 ^ 3 * b3 * h ^ 32
    + (3 : F[X]) * a5 ^ 2 * b2 * h ^ 38
    - (3 : F[X]) * a5 * b1 * h ^ 44
    + (18 : F[X]) * b0 * h ^ 50


end BridgeIotaDepression610

end Max11DegreeRoutes
