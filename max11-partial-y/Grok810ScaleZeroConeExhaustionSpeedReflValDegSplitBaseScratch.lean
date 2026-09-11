import Grok810ScaleZeroMixedConesScratch

/-! # Scale-zero cone exhaustion for normalized `(8,10)`, `H = 0`

Continuation of `Grok810ScaleZeroMixedConesScratch` on the constant core
`H = (C t)²`.  That file reduced `normalized810ScaleZero_impossible` to
`normalized810ScaleZero_coneMixedResidual`.  This file closes every
named remaining unique face and Newton tie that has a rest bound and a
leading-form identity, and records an honest residual for the leftover
chambers.

CAS jobs `derive_810_scale_zero_mixed_cones.py` (job
`20260902T145703Z`, `mixed_soft=0`) and
`derive_810_scale_zero_cone_exhaustion.py` enumerate mixed cones by
support and weighted degree.  Unique faces of `ξ`/`μ`/`ο` kill every
non-tie sample.  On a tie the leading forms of the constant integrals
are polynomials in the tied leading coefficients, which are nonzero by
definition of the tie.  A Groebner basis containing `lc^k` is the
certificate: the transcribed `linear_combination` identity gives
`lc^k = 0`, hence `lc = 0`.  The basis is not required to be `(1)`.

Named leftover families:

* unique-high `B` with `3 deg A > 2 deg B`: pure-power `A⁶` of `μ`;
* unique-high `D₀` with `5 deg A > 2 deg D₀`: pure-power `A⁶` of `μ`;
  equality `5 deg A = 2 deg D₀`: Groebner identity `A⁷` from `μ` and `ξ`;
* pair ties `A`–`C₀` (`deg C₀ = 2 deg A`; Groebner contains `C₀⁶`,
  saturations `(1)`), `A`–`E₀` Newton tie `deg E₀ = 3 deg A` (`E₀⁴`),
  `B`–`E₀` (`E₀⁴`), triple `A,B,C₀` (same `μ` inner form as `A`–`C₀`),
  and the other pairs (`C₀`–`E₀` unique `C₀² E₀` of `ξ`, `A`–`F₀`
  unique `A⁶` of `μ`, `B`–`D₀` unique `B⁴` of `μ`, `B`–`C₀` unique
  `C₀³` of `μ`);
* supports of three or more nonconstant letters: a unique face still
  strictly leads, or the `A`–`C₀` identity applies;
* unique-`G₀` of degree greater than one with `l = 0`: the primitive is
  affine in `G₀`, so `d ρ = C j` forces `deg G₀ = 1`;
* unique-`G₀` of degree one with `l = 0` on a source-mapped core: routed
  through the parent `uniqueHighG0DegOne_existsPrimitive_false`.  The
  mixed-residual existential dropped those maps, so a unique-`G₀`
  degree-one witness without maps is not claimed empty here.

Unused integrals `κ` and `ν` were spent as CAS companions; the Lean
transcription uses the already pulled-back `ξ`, `μ`, and `ο`.  No
total-degree or twice-prime theorem is used.  No `sorry`, no new
axioms, no finite-root shortcut.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false


/-! ## Remaining mixed and Newton-tie cones -/

section ExhaustCones810

variable {k : Type*} [Field k] [CharZero k]

/-- Unique `A⁶` of `μ` with `A` and `B` nonconstant, `3 deg A > 2 deg B`,
and the other five letters constant.  This is the pure-power face on
`A6BLeadsOmicronCone810`. -/
def A6LeadsMuMixedBCone810 (A B C0 D0 E0 F0 G0 : k[X]) : Prop :=
  0 < A.natDegree ∧
    0 < B.natDegree ∧
    2 * B.natDegree < 3 * A.natDegree ∧
    C0.natDegree = 0 ∧
    D0.natDegree = 0 ∧
    E0.natDegree = 0 ∧
    F0.natDegree = 0 ∧
    G0.natDegree = 0

/-- Unique-high `D₀` with `A` nonconstant, `5 deg A > 2 deg D₀`, and the
other five letters constant.  CAS: `A⁶` of `μ` strictly leads. -/
def A6LeadsMuMixedD0Cone810 (A B C0 D0 E0 F0 G0 : k[X]) : Prop :=
  0 < A.natDegree ∧
    0 < D0.natDegree ∧
    2 * D0.natDegree < 5 * A.natDegree ∧
    B.natDegree = 0 ∧
    C0.natDegree = 0 ∧
    E0.natDegree = 0 ∧
    F0.natDegree = 0 ∧
    G0.natDegree = 0

/-- Ratio-tie `5 deg A = 2 deg D₀` with the other five letters constant.
CAS: `μ` and `ξ` give the Groebner identity `A⁷`. -/
def AD05RatioTieCone810 (A B C0 D0 E0 F0 G0 : k[X]) : Prop :=
  0 < A.natDegree ∧
    0 < D0.natDegree ∧
    5 * A.natDegree = 2 * D0.natDegree ∧
    B.natDegree = 0 ∧
    C0.natDegree = 0 ∧
    E0.natDegree = 0 ∧
    F0.natDegree = 0 ∧
    G0.natDegree = 0

/-- Newton tie `deg E₀ = 3 deg A` (so `2 deg E₀ = 6 deg A`) with the
other five letters constant.  Distinct from the named-weight cone
`AE03RatioTieCone810` (`2 deg E₀ = 3 deg A`), on which `A⁶` of `μ`
strictly leads.  CAS: Groebner contains `E₀⁴`. -/
def AE06RatioTieCone810 (A B C0 D0 E0 F0 G0 : k[X]) : Prop :=
  0 < A.natDegree ∧
    0 < E0.natDegree ∧
    E0.natDegree = 3 * A.natDegree ∧
    B.natDegree = 0 ∧
    C0.natDegree = 0 ∧
    D0.natDegree = 0 ∧
    F0.natDegree = 0 ∧
    G0.natDegree = 0

/-- Triple `A,B,C₀` with `deg C₀ = 2 deg A` and the other four letters
constant.  The load-free `μ` face is independent of `B` and is the
`A`–`C₀` inner form; Groebner still contains `C₀⁶`. -/
def ABC0RatioTieCone810 (A B C0 D0 E0 F0 G0 : k[X]) : Prop :=
  0 < A.natDegree ∧
    0 < B.natDegree ∧
    0 < C0.natDegree ∧
    C0.natDegree = 2 * A.natDegree ∧
    4 * B.natDegree < 6 * A.natDegree ∧
    5 * B.natDegree < 7 * A.natDegree ∧
    D0.natDegree = 0 ∧
    E0.natDegree = 0 ∧
    F0.natDegree = 0 ∧
    G0.natDegree = 0

/-- Unique `C₀² E₀` of `ξ` on the named-weight `C₀`–`E₀` pair. -/
def C0E0XiLeadsCone810 (A B C0 D0 E0 F0 G0 : k[X]) : Prop :=
  C0E0RatioTieCone810 A B C0 D0 E0 F0 G0

/-- Unique-`G₀` of degree greater than one, other six letters of degree
zero, and `l = 0`.  The primitive is `θ G₀`. -/
def UniqueHighG0DegGtOneL0Cone810 (A B C0 D0 E0 F0 G0 : k[X]) : Prop :=
  1 < G0.natDegree ∧
    A.natDegree = 0 ∧
    B.natDegree = 0 ∧
    C0.natDegree = 0 ∧
    D0.natDegree = 0 ∧
    E0.natDegree = 0 ∧
    F0.natDegree = 0

private theorem zero_pow_two_ex {R : Type*} [Semiring R] : (0 : R) ^ 2 = 0 :=
  zero_pow (by decide : (2 : ℕ) ≠ 0)

private theorem zero_pow_three_ex {R : Type*} [Semiring R] : (0 : R) ^ 3 = 0 :=
  zero_pow (by decide : (3 : ℕ) ≠ 0)

private theorem zero_pow_four_ex {R : Type*} [Semiring R] : (0 : R) ^ 4 = 0 :=
  zero_pow (by decide : (4 : ℕ) ≠ 0)

private theorem zero_pow_five_ex {R : Type*} [Semiring R] : (0 : R) ^ 5 = 0 :=
  zero_pow (by decide : (5 : ℕ) ≠ 0)

private theorem zero_pow_six_ex {R : Type*} [Semiring R] : (0 : R) ^ 6 = 0 :=
  zero_pow (by decide : (6 : ℕ) ≠ 0)

private theorem zero_pow_seven_ex {R : Type*} [Semiring R] : (0 : R) ^ 7 = 0 :=
  zero_pow (by decide : (7 : ℕ) ≠ 0)

end ExhaustCones810


/-! ## Groebner / Euclidean identities in tied leading coefficients -/

section ExhaustIdentities810

variable {k : Type*} [Field k] [CharZero k]

/-- Load-free `μ` inner form on `deg C₀ = 2 deg A`. -/
def muAC02Inner810 (r s : k) : k :=
  (77 : k) * r ^ 6 - 616 * r ^ 4 * s + 1344 * r ^ 2 * s ^ 2 - 512 * s ^ 3

/-- Load-free `ξ` inner form on the same cone (including the overall
factor of `r`). -/
def xiAC02Inner810 (r s : k) : k :=
  r * (r ^ 2 - 4 * s) * (33 * r ^ 4 - 176 * r ^ 2 * s + 192 * s ^ 2)

/-- Load-free `μ` inner form on `deg E₀ = 3 deg A`. -/
def muAE06Inner810 (r v : k) : k :=
  (77 : k) * r ^ 6 + 896 * r ^ 3 * v + 2048 * v ^ 2

def xiAE06Inner810 (r v : k) : k :=
  r * (r ^ 3 + 8 * v) * (33 * r ^ 3 + 128 * v)

/-- Load-free `μ` inner form on `deg E₀ = 2 deg B`. -/
def muBE02Inner810 (s w : k) : k :=
  (7 : k) * s ^ 4 - 48 * s ^ 2 * w + 64 * w ^ 2

def omicronBE02Inner810 (s w : k) : k :=
  s * (21 * s ^ 4 - 160 * s ^ 2 * w + 320 * w ^ 2)

/-- Cleared `μ`/`ξ` inner forms on `5 deg A = 2 deg D₀`. -/
def muAD05Inner810 (r d : k) : k :=
  (5 : k) * r * (77 * r ^ 5 - 1536 * d ^ 2)

def xiAD05Inner810 (r d : k) : k :=
  (-(15 : k)) * r ^ 2 * (11 * r ^ 5 - 320 * d ^ 2)

end ExhaustIdentities810


/-! ## Combined faces and rest polynomials -/

section ExhaustCombined810

variable {k : Type*} [Field k] [CharZero k]

def muA6Face810 (A : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A]
    [
    (385 / 65536 : k)]
    [
    [6]]

def muAC02Combined810 (A C0 : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, C0]
    [
    (385 / 65536 : k), (-(385 / 8192) : k), (105 / 1024 : k),
    (-(5 / 128) : k)]
    [
    [6, 0], [4, 1], [2, 2], [0, 3]]

def xiAC02Combined810 (A C0 : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, C0]
    [
    (-(165 / 65536) : k), (385 / 16384 : k), (-(35 / 512) : k),
    (15 / 256 : k)]
    [
    [7, 0], [5, 1], [3, 2], [1, 3]]

def muAE06Combined810 (A E0 : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, E0]
    [
    (385 / 65536 : k), (35 / 512 : k), (5 / 32 : k)]
    [
    [6, 0], [3, 1], [0, 2]]

def xiAE06Combined810 (A E0 : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, E0]
    [
    (-(165 / 65536) : k), (-(245 / 8192) : k), (-(5 / 64) : k)]
    [
    [7, 0], [4, 1], [1, 2]]

def muBE02Combined810 (B E0 : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [B, E0]
    [
    (35 / 2048 : k), (-(15 / 128) : k), (5 / 32 : k)]
    [
    [4, 0], [2, 1], [0, 2]]

def omicronBE02Combined810 (B E0 : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [B, E0]
    [
    (-(21 / 4096) : k), (5 / 128 : k), (-(5 / 64) : k)]
    [
    [5, 0], [3, 1], [1, 2]]

def muAD05Combined810 (A D0 : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, D0]
    [
    (385 / 65536 : k), (-(15 / 128) : k)]
    [
    [6, 0], [1, 2]]

def xiAD05Combined810 (A D0 : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, D0]
    [
    (-(165 / 65536) : k), (75 / 1024 : k)]
    [
    [7, 0], [2, 2]]

def xiC0E0Face810 (C0 E0 : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [C0, E0]
    [
    (-(15 / 128) : k)]
    [
    [2, 1]]


set_option maxHeartbeats 8000000 in
/-- `μ` with the unique `A⁶` face deleted. -/
def degreeZeroMuNoA6Polynomial810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
    [
    (-(385 / 4096) : k), (-(385 / 8192) : k), (-(7245 / 262144 * l) : k),
    (35 / 2048 : k), (105 / 512 : k), (315 / 8192 * l : k),
    (105 / 1024 : k), (105 / 512 : k), (945 / 8192 * l : k),
    (35 / 512 : k), (315 / 8192 * l : k), (-(357 / 8192 * beta) : k),
    (-(45 / 2048 * gamma) : k), (-(5 / 128) : k), (-(15 / 64) : k),
    (-(63 / 1024 * l) : k), (-(15 / 128) : k), (-(63 / 1024 * l) : k),
    (21 / 1024 * beta : k), (-(15 / 128) : k), (-(15 / 64) : k),
    (-(63 / 512 * l) : k), (-(15 / 64) : k), (-(63 / 512 * l) : k),
    (63 / 512 * beta : k), (15 / 128 * gamma : k), (-(15 / 128) : k),
    (-(63 / 1024 * l) : k), (63 / 1024 * beta : k), (15 / 128 * gamma : k),
    (165 / 1024 * delta : k), (1 / 16 * epsilon : k), (5 / 32 : k),
    (5 / 16 : k), (9 / 64 * l : k), (5 / 16 : k),
    (9 / 64 * l : k), (-(7 / 64 * beta) : k), (-(3 / 32 * gamma) : k),
    (9 / 64 * l : k), (-(7 / 64 * beta) : k), (-(3 / 16 * gamma) : k),
    (-(15 / 64 * delta) : k), (-(1 / 8 * epsilon) : k), (-(7 / 64 * beta) : k),
    (-(3 / 16 * gamma) : k), (-(15 / 64 * delta) : k), (-(1 / 4 * epsilon) : k),
    (-(15 / 64 * zeta) : k), (-(3 / 32 * eta) : k), (3 / 4 * gamma : k),
    (5 / 8 * delta : k), (1 / 2 * epsilon : k), (3 / 8 * zeta : k),
    (1 / 4 * eta : k), (1 / 8 * theta : k)]
    [
    [3, 2, 0, 0, 0, 0, 0], [4, 0, 1, 0, 0, 0, 0], [4, 1, 0, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0],
    [1, 2, 1, 0, 0, 0, 0], [1, 3, 0, 0, 0, 0, 0], [2, 0, 2, 0, 0, 0, 0], [2, 1, 0, 1, 0, 0, 0],
    [2, 1, 1, 0, 0, 0, 0], [3, 0, 0, 0, 1, 0, 0], [3, 0, 0, 1, 0, 0, 0], [3, 1, 0, 0, 0, 0, 0],
    [4, 0, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0], [0, 1, 1, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0],
    [0, 2, 0, 0, 1, 0, 0], [0, 2, 0, 1, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0], [1, 0, 0, 2, 0, 0, 0],
    [1, 0, 1, 0, 1, 0, 0], [1, 0, 1, 1, 0, 0, 0], [1, 1, 0, 0, 0, 1, 0], [1, 1, 0, 0, 1, 0, 0],
    [1, 1, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0, 1], [2, 0, 0, 0, 0, 1, 0],
    [2, 0, 0, 1, 0, 0, 0], [2, 0, 1, 0, 0, 0, 0], [2, 1, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 1, 1, 0, 0], [0, 0, 1, 0, 0, 0, 1],
    [0, 0, 1, 0, 0, 1, 0], [0, 0, 1, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 1],
    [0, 1, 0, 0, 1, 0, 0], [0, 1, 0, 1, 0, 0, 0], [0, 1, 1, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0],
    [1, 0, 0, 0, 0, 1, 0], [1, 0, 0, 0, 1, 0, 0], [1, 0, 0, 1, 0, 0, 0], [1, 0, 1, 0, 0, 0, 0],
    [1, 1, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0],
    [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0]]

set_option maxHeartbeats 8000000 in
/-- `μ` without the four `A`–`C₀` tie monomials. -/
def degreeZeroMuNoAC02Polynomial810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
    [
    (-(385 / 4096) : k), (-(7245 / 262144 * l) : k), (35 / 2048 : k),
    (105 / 512 : k), (315 / 8192 * l : k), (105 / 512 : k),
    (945 / 8192 * l : k), (35 / 512 : k), (315 / 8192 * l : k),
    (-(357 / 8192 * beta) : k), (-(45 / 2048 * gamma) : k), (-(15 / 64) : k),
    (-(63 / 1024 * l) : k), (-(15 / 128) : k), (-(63 / 1024 * l) : k),
    (21 / 1024 * beta : k), (-(15 / 128) : k), (-(15 / 64) : k),
    (-(63 / 512 * l) : k), (-(15 / 64) : k), (-(63 / 512 * l) : k),
    (63 / 512 * beta : k), (15 / 128 * gamma : k), (-(15 / 128) : k),
    (-(63 / 1024 * l) : k), (63 / 1024 * beta : k), (15 / 128 * gamma : k),
    (165 / 1024 * delta : k), (1 / 16 * epsilon : k), (5 / 32 : k),
    (5 / 16 : k), (9 / 64 * l : k), (5 / 16 : k),
    (9 / 64 * l : k), (-(7 / 64 * beta) : k), (-(3 / 32 * gamma) : k),
    (9 / 64 * l : k), (-(7 / 64 * beta) : k), (-(3 / 16 * gamma) : k),
    (-(15 / 64 * delta) : k), (-(1 / 8 * epsilon) : k), (-(7 / 64 * beta) : k),
    (-(3 / 16 * gamma) : k), (-(15 / 64 * delta) : k), (-(1 / 4 * epsilon) : k),
    (-(15 / 64 * zeta) : k), (-(3 / 32 * eta) : k), (3 / 4 * gamma : k),
    (5 / 8 * delta : k), (1 / 2 * epsilon : k), (3 / 8 * zeta : k),
    (1 / 4 * eta : k), (1 / 8 * theta : k)]
    [
    [3, 2, 0, 0, 0, 0, 0], [4, 1, 0, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0],
    [1, 3, 0, 0, 0, 0, 0], [2, 1, 0, 1, 0, 0, 0], [2, 1, 1, 0, 0, 0, 0], [3, 0, 0, 0, 1, 0, 0],
    [3, 0, 0, 1, 0, 0, 0], [3, 1, 0, 0, 0, 0, 0], [4, 0, 0, 0, 0, 0, 0], [0, 1, 1, 1, 0, 0, 0],
    [0, 1, 2, 0, 0, 0, 0], [0, 2, 0, 0, 1, 0, 0], [0, 2, 0, 1, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0],
    [1, 0, 0, 2, 0, 0, 0], [1, 0, 1, 0, 1, 0, 0], [1, 0, 1, 1, 0, 0, 0], [1, 1, 0, 0, 0, 1, 0],
    [1, 1, 0, 0, 1, 0, 0], [1, 1, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0, 1],
    [2, 0, 0, 0, 0, 1, 0], [2, 0, 0, 1, 0, 0, 0], [2, 0, 1, 0, 0, 0, 0], [2, 1, 0, 0, 0, 0, 0],
    [3, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 1, 1, 0, 0],
    [0, 0, 1, 0, 0, 0, 1], [0, 0, 1, 0, 0, 1, 0], [0, 0, 1, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0],
    [0, 1, 0, 0, 0, 0, 1], [0, 1, 0, 0, 1, 0, 0], [0, 1, 0, 1, 0, 0, 0], [0, 1, 1, 0, 0, 0, 0],
    [0, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0], [1, 0, 0, 0, 1, 0, 0], [1, 0, 0, 1, 0, 0, 0],
    [1, 0, 1, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1],
    [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0],
    [0, 1, 0, 0, 0, 0, 0]]

set_option maxHeartbeats 8000000 in
/-- `μ` without the three `A`–`E₀` Newton-tie monomials. -/
def degreeZeroMuNoAE06Polynomial810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
    [
    (-(385 / 4096) : k), (-(385 / 8192) : k), (-(7245 / 262144 * l) : k),
    (35 / 2048 : k), (105 / 512 : k), (315 / 8192 * l : k),
    (105 / 1024 : k), (105 / 512 : k), (945 / 8192 * l : k),
    (315 / 8192 * l : k), (-(357 / 8192 * beta) : k), (-(45 / 2048 * gamma) : k),
    (-(5 / 128) : k), (-(15 / 64) : k), (-(63 / 1024 * l) : k),
    (-(15 / 128) : k), (-(63 / 1024 * l) : k), (21 / 1024 * beta : k),
    (-(15 / 128) : k), (-(15 / 64) : k), (-(63 / 512 * l) : k),
    (-(15 / 64) : k), (-(63 / 512 * l) : k), (63 / 512 * beta : k),
    (15 / 128 * gamma : k), (-(15 / 128) : k), (-(63 / 1024 * l) : k),
    (63 / 1024 * beta : k), (15 / 128 * gamma : k), (165 / 1024 * delta : k),
    (1 / 16 * epsilon : k), (5 / 16 : k), (9 / 64 * l : k),
    (5 / 16 : k), (9 / 64 * l : k), (-(7 / 64 * beta) : k),
    (-(3 / 32 * gamma) : k), (9 / 64 * l : k), (-(7 / 64 * beta) : k),
    (-(3 / 16 * gamma) : k), (-(15 / 64 * delta) : k), (-(1 / 8 * epsilon) : k),
    (-(7 / 64 * beta) : k), (-(3 / 16 * gamma) : k), (-(15 / 64 * delta) : k),
    (-(1 / 4 * epsilon) : k), (-(15 / 64 * zeta) : k), (-(3 / 32 * eta) : k),
    (3 / 4 * gamma : k), (5 / 8 * delta : k), (1 / 2 * epsilon : k),
    (3 / 8 * zeta : k), (1 / 4 * eta : k), (1 / 8 * theta : k)]
    [
    [3, 2, 0, 0, 0, 0, 0], [4, 0, 1, 0, 0, 0, 0], [4, 1, 0, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0],
    [1, 2, 1, 0, 0, 0, 0], [1, 3, 0, 0, 0, 0, 0], [2, 0, 2, 0, 0, 0, 0], [2, 1, 0, 1, 0, 0, 0],
    [2, 1, 1, 0, 0, 0, 0], [3, 0, 0, 1, 0, 0, 0], [3, 1, 0, 0, 0, 0, 0], [4, 0, 0, 0, 0, 0, 0],
    [0, 0, 3, 0, 0, 0, 0], [0, 1, 1, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0], [0, 2, 0, 0, 1, 0, 0],
    [0, 2, 0, 1, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0], [1, 0, 0, 2, 0, 0, 0], [1, 0, 1, 0, 1, 0, 0],
    [1, 0, 1, 1, 0, 0, 0], [1, 1, 0, 0, 0, 1, 0], [1, 1, 0, 0, 1, 0, 0], [1, 1, 1, 0, 0, 0, 0],
    [1, 2, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0, 1], [2, 0, 0, 0, 0, 1, 0], [2, 0, 0, 1, 0, 0, 0],
    [2, 0, 1, 0, 0, 0, 0], [2, 1, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0],
    [0, 0, 0, 1, 1, 0, 0], [0, 0, 1, 0, 0, 0, 1], [0, 0, 1, 0, 0, 1, 0], [0, 0, 1, 1, 0, 0, 0],
    [0, 0, 2, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 1], [0, 1, 0, 0, 1, 0, 0], [0, 1, 0, 1, 0, 0, 0],
    [0, 1, 1, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0], [1, 0, 0, 0, 1, 0, 0],
    [1, 0, 0, 1, 0, 0, 0], [1, 0, 1, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, 0, 0],
    [0, 0, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0]]

set_option maxHeartbeats 8000000 in
/-- `μ` without the three `B`–`E₀` tie monomials. -/
def degreeZeroMuNoBE02Polynomial810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
    [
    (385 / 65536 : k), (-(385 / 4096) : k), (-(385 / 8192) : k),
    (-(7245 / 262144 * l) : k), (105 / 512 : k), (315 / 8192 * l : k),
    (105 / 1024 : k), (105 / 512 : k), (945 / 8192 * l : k),
    (35 / 512 : k), (315 / 8192 * l : k), (-(357 / 8192 * beta) : k),
    (-(45 / 2048 * gamma) : k), (-(5 / 128) : k), (-(15 / 64) : k),
    (-(63 / 1024 * l) : k), (-(63 / 1024 * l) : k), (21 / 1024 * beta : k),
    (-(15 / 128) : k), (-(15 / 64) : k), (-(63 / 512 * l) : k),
    (-(15 / 64) : k), (-(63 / 512 * l) : k), (63 / 512 * beta : k),
    (15 / 128 * gamma : k), (-(15 / 128) : k), (-(63 / 1024 * l) : k),
    (63 / 1024 * beta : k), (15 / 128 * gamma : k), (165 / 1024 * delta : k),
    (1 / 16 * epsilon : k), (5 / 16 : k), (9 / 64 * l : k),
    (5 / 16 : k), (9 / 64 * l : k), (-(7 / 64 * beta) : k),
    (-(3 / 32 * gamma) : k), (9 / 64 * l : k), (-(7 / 64 * beta) : k),
    (-(3 / 16 * gamma) : k), (-(15 / 64 * delta) : k), (-(1 / 8 * epsilon) : k),
    (-(7 / 64 * beta) : k), (-(3 / 16 * gamma) : k), (-(15 / 64 * delta) : k),
    (-(1 / 4 * epsilon) : k), (-(15 / 64 * zeta) : k), (-(3 / 32 * eta) : k),
    (3 / 4 * gamma : k), (5 / 8 * delta : k), (1 / 2 * epsilon : k),
    (3 / 8 * zeta : k), (1 / 4 * eta : k), (1 / 8 * theta : k)]
    [
    [6, 0, 0, 0, 0, 0, 0], [3, 2, 0, 0, 0, 0, 0], [4, 0, 1, 0, 0, 0, 0], [4, 1, 0, 0, 0, 0, 0],
    [1, 2, 1, 0, 0, 0, 0], [1, 3, 0, 0, 0, 0, 0], [2, 0, 2, 0, 0, 0, 0], [2, 1, 0, 1, 0, 0, 0],
    [2, 1, 1, 0, 0, 0, 0], [3, 0, 0, 0, 1, 0, 0], [3, 0, 0, 1, 0, 0, 0], [3, 1, 0, 0, 0, 0, 0],
    [4, 0, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0], [0, 1, 1, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0],
    [0, 2, 0, 1, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0], [1, 0, 0, 2, 0, 0, 0], [1, 0, 1, 0, 1, 0, 0],
    [1, 0, 1, 1, 0, 0, 0], [1, 1, 0, 0, 0, 1, 0], [1, 1, 0, 0, 1, 0, 0], [1, 1, 1, 0, 0, 0, 0],
    [1, 2, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0, 1], [2, 0, 0, 0, 0, 1, 0], [2, 0, 0, 1, 0, 0, 0],
    [2, 0, 1, 0, 0, 0, 0], [2, 1, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0],
    [0, 0, 0, 1, 1, 0, 0], [0, 0, 1, 0, 0, 0, 1], [0, 0, 1, 0, 0, 1, 0], [0, 0, 1, 1, 0, 0, 0],
    [0, 0, 2, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 1], [0, 1, 0, 0, 1, 0, 0], [0, 1, 0, 1, 0, 0, 0],
    [0, 1, 1, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0], [1, 0, 0, 0, 1, 0, 0],
    [1, 0, 0, 1, 0, 0, 0], [1, 0, 1, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, 0, 0],
    [0, 0, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0]]

set_option maxHeartbeats 8000000 in
/-- `μ` without the `A⁶` / `A D₀²` tie monomials. -/
def degreeZeroMuNoAD05Polynomial810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
    [
    (-(385 / 4096) : k), (-(385 / 8192) : k), (-(7245 / 262144 * l) : k),
    (35 / 2048 : k), (105 / 512 : k), (315 / 8192 * l : k),
    (105 / 1024 : k), (105 / 512 : k), (945 / 8192 * l : k),
    (35 / 512 : k), (315 / 8192 * l : k), (-(357 / 8192 * beta) : k),
    (-(45 / 2048 * gamma) : k), (-(5 / 128) : k), (-(15 / 64) : k),
    (-(63 / 1024 * l) : k), (-(15 / 128) : k), (-(63 / 1024 * l) : k),
    (21 / 1024 * beta : k), (-(15 / 64) : k), (-(63 / 512 * l) : k),
    (-(15 / 64) : k), (-(63 / 512 * l) : k), (63 / 512 * beta : k),
    (15 / 128 * gamma : k), (-(15 / 128) : k), (-(63 / 1024 * l) : k),
    (63 / 1024 * beta : k), (15 / 128 * gamma : k), (165 / 1024 * delta : k),
    (1 / 16 * epsilon : k), (5 / 32 : k), (5 / 16 : k),
    (9 / 64 * l : k), (5 / 16 : k), (9 / 64 * l : k),
    (-(7 / 64 * beta) : k), (-(3 / 32 * gamma) : k), (9 / 64 * l : k),
    (-(7 / 64 * beta) : k), (-(3 / 16 * gamma) : k), (-(15 / 64 * delta) : k),
    (-(1 / 8 * epsilon) : k), (-(7 / 64 * beta) : k), (-(3 / 16 * gamma) : k),
    (-(15 / 64 * delta) : k), (-(1 / 4 * epsilon) : k), (-(15 / 64 * zeta) : k),
    (-(3 / 32 * eta) : k), (3 / 4 * gamma : k), (5 / 8 * delta : k),
    (1 / 2 * epsilon : k), (3 / 8 * zeta : k), (1 / 4 * eta : k),
    (1 / 8 * theta : k)]
    [
    [3, 2, 0, 0, 0, 0, 0], [4, 0, 1, 0, 0, 0, 0], [4, 1, 0, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0],
    [1, 2, 1, 0, 0, 0, 0], [1, 3, 0, 0, 0, 0, 0], [2, 0, 2, 0, 0, 0, 0], [2, 1, 0, 1, 0, 0, 0],
    [2, 1, 1, 0, 0, 0, 0], [3, 0, 0, 0, 1, 0, 0], [3, 0, 0, 1, 0, 0, 0], [3, 1, 0, 0, 0, 0, 0],
    [4, 0, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0], [0, 1, 1, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0],
    [0, 2, 0, 0, 1, 0, 0], [0, 2, 0, 1, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0], [1, 0, 1, 0, 1, 0, 0],
    [1, 0, 1, 1, 0, 0, 0], [1, 1, 0, 0, 0, 1, 0], [1, 1, 0, 0, 1, 0, 0], [1, 1, 1, 0, 0, 0, 0],
    [1, 2, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0, 1], [2, 0, 0, 0, 0, 1, 0], [2, 0, 0, 1, 0, 0, 0],
    [2, 0, 1, 0, 0, 0, 0], [2, 1, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0],
    [0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 1, 1, 0, 0], [0, 0, 1, 0, 0, 0, 1], [0, 0, 1, 0, 0, 1, 0],
    [0, 0, 1, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 1], [0, 1, 0, 0, 1, 0, 0],
    [0, 1, 0, 1, 0, 0, 0], [0, 1, 1, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0],
    [1, 0, 0, 0, 1, 0, 0], [1, 0, 0, 1, 0, 0, 0], [1, 0, 1, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0],
    [2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 1, 0, 0],
    [0, 0, 0, 1, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0]]

set_option maxHeartbeats 8000000 in
/-- `ξ` without the four `A`–`C₀` tie monomials. -/
def degreeZeroXiNoAC02Polynomial810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
    [
    (1925 / 32768 : k), (7245 / 524288 * l : k), (-(35 / 1024) : k),
    (-(105 / 512) : k), (-(315 / 8192 * l) : k), (-(525 / 4096) : k),
    (-(315 / 4096 * l) : k), (-(245 / 8192) : k), (-(4725 / 262144 * l) : k),
    (357 / 16384 * beta : k), (9 / 1024 * gamma : k), (45 / 512 : k),
    (55 / 1024 : k), (63 / 2048 * l : k), (165 / 512 : k),
    (189 / 2048 * l : k), (75 / 512 : k), (693 / 8192 * l : k),
    (-(63 / 2048 * beta) : k), (75 / 1024 : k), (75 / 512 : k),
    (693 / 8192 * l : k), (135 / 1024 : k), (315 / 4096 * l : k),
    (-(189 / 2048 * beta) : k), (-(45 / 512 * gamma) : k), (5 / 128 : k),
    (189 / 8192 * l : k), (-(231 / 8192 * beta) : k), (-(15 / 256 * gamma) : k),
    (-(165 / 2048 * delta) : k), (-(3 / 128 * epsilon) : k), (-(15 / 128) : k),
    (-(15 / 128) : k), (-(63 / 1024 * l) : k), (-(25 / 128) : k),
    (-(27 / 512 * l) : k), (-(25 / 128) : k), (-(27 / 256 * l) : k),
    (7 / 128 * beta : k), (-(5 / 64) : k), (-(45 / 1024 * l) : k),
    (49 / 1024 * beta : k), (3 / 32 * gamma : k), (5 / 128 * delta : k),
    (-(5 / 64) : k), (-(5 / 32) : k), (-(45 / 512 * l) : k),
    (-(5 / 32) : k), (-(45 / 512 * l) : k), (49 / 512 * beta : k),
    (3 / 32 * gamma : k), (-(9 / 128 * l) : k), (21 / 256 * beta : k),
    (21 / 128 * gamma : k), (15 / 64 * delta : k), (1 / 8 * epsilon : k),
    (35 / 1024 * beta : k), (9 / 128 * gamma : k), (105 / 1024 * delta : k),
    (1 / 8 * epsilon : k), (15 / 128 * zeta : k), (1 / 32 * eta : k),
    (5 / 32 : k), (5 / 16 : k), (9 / 64 * l : k),
    (9 / 64 * l : k), (-(7 / 64 * beta) : k), (-(3 / 32 * gamma) : k),
    (-(7 / 64 * beta) : k), (-(3 / 16 * gamma) : k), (-(15 / 64 * delta) : k),
    (-(1 / 8 * epsilon) : k), (-(3 / 32 * gamma) : k), (-(5 / 32 * delta) : k),
    (-(3 / 16 * epsilon) : k), (-(3 / 16 * zeta) : k), (-(1 / 16 * eta) : k),
    (-(5 / 64 * delta) : k), (-(1 / 8 * epsilon) : k), (-(9 / 64 * zeta) : k),
    (-(1 / 8 * eta) : k), (-(1 / 16 * theta) : k), (1 / 2 * epsilon : k),
    (3 / 8 * zeta : k), (1 / 4 * eta : k), (1 / 8 * theta : k)]
    [
    [4, 2, 0, 0, 0, 0, 0], [5, 1, 0, 0, 0, 0, 0], [1, 4, 0, 0, 0, 0, 0], [2, 2, 1, 0, 0, 0, 0],
    [2, 3, 0, 0, 0, 0, 0], [3, 1, 0, 1, 0, 0, 0], [3, 1, 1, 0, 0, 0, 0], [4, 0, 0, 0, 1, 0, 0],
    [4, 0, 0, 1, 0, 0, 0], [4, 1, 0, 0, 0, 0, 0], [5, 0, 0, 0, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0],
    [0, 3, 0, 1, 0, 0, 0], [0, 3, 1, 0, 0, 0, 0], [1, 1, 1, 1, 0, 0, 0], [1, 1, 2, 0, 0, 0, 0],
    [1, 2, 0, 0, 1, 0, 0], [1, 2, 0, 1, 0, 0, 0], [1, 3, 0, 0, 0, 0, 0], [2, 0, 0, 2, 0, 0, 0],
    [2, 0, 1, 0, 1, 0, 0], [2, 0, 1, 1, 0, 0, 0], [2, 1, 0, 0, 0, 1, 0], [2, 1, 0, 0, 1, 0, 0],
    [2, 1, 1, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 0, 1], [3, 0, 0, 0, 0, 1, 0],
    [3, 0, 0, 1, 0, 0, 0], [3, 0, 1, 0, 0, 0, 0], [3, 1, 0, 0, 0, 0, 0], [4, 0, 0, 0, 0, 0, 0],
    [0, 0, 1, 2, 0, 0, 0], [0, 0, 2, 0, 1, 0, 0], [0, 0, 2, 1, 0, 0, 0], [0, 1, 0, 1, 1, 0, 0],
    [0, 1, 0, 2, 0, 0, 0], [0, 1, 1, 0, 0, 1, 0], [0, 1, 1, 0, 1, 0, 0], [0, 1, 2, 0, 0, 0, 0],
    [0, 2, 0, 0, 0, 0, 1], [0, 2, 0, 0, 0, 1, 0], [0, 2, 0, 1, 0, 0, 0], [0, 2, 1, 0, 0, 0, 0],
    [0, 3, 0, 0, 0, 0, 0], [1, 0, 0, 0, 2, 0, 0], [1, 0, 0, 1, 0, 1, 0], [1, 0, 0, 1, 1, 0, 0],
    [1, 0, 1, 0, 0, 0, 1], [1, 0, 1, 0, 0, 1, 0], [1, 0, 1, 1, 0, 0, 0], [1, 0, 2, 0, 0, 0, 0],
    [1, 1, 0, 0, 0, 0, 1], [1, 1, 0, 0, 1, 0, 0], [1, 1, 0, 1, 0, 0, 0], [1, 1, 1, 0, 0, 0, 0],
    [1, 2, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 1, 0], [2, 0, 0, 0, 1, 0, 0], [2, 0, 0, 1, 0, 0, 0],
    [2, 0, 1, 0, 0, 0, 0], [2, 1, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0],
    [0, 0, 0, 0, 1, 0, 1], [0, 0, 0, 0, 1, 1, 0], [0, 0, 0, 1, 0, 0, 1], [0, 0, 0, 1, 1, 0, 0],
    [0, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0],
    [0, 0, 2, 0, 0, 0, 0], [0, 1, 0, 0, 0, 1, 0], [0, 1, 0, 0, 1, 0, 0], [0, 1, 0, 1, 0, 0, 0],
    [0, 1, 1, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0], [1, 0, 0, 0, 1, 0, 0],
    [1, 0, 0, 1, 0, 0, 0], [1, 0, 1, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1],
    [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, 0, 0]]

set_option maxHeartbeats 8000000 in
/-- `ξ` without the three `A`–`E₀` Newton-tie monomials. -/
def degreeZeroXiNoAE06Polynomial810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
    [
    (1925 / 32768 : k), (385 / 16384 : k), (7245 / 524288 * l : k),
    (-(35 / 1024) : k), (-(105 / 512) : k), (-(315 / 8192 * l) : k),
    (-(35 / 512) : k), (-(525 / 4096) : k), (-(315 / 4096 * l) : k),
    (-(4725 / 262144 * l) : k), (357 / 16384 * beta : k), (9 / 1024 * gamma : k),
    (45 / 512 : k), (55 / 1024 : k), (63 / 2048 * l : k),
    (15 / 256 : k), (165 / 512 : k), (189 / 2048 * l : k),
    (75 / 512 : k), (693 / 8192 * l : k), (-(63 / 2048 * beta) : k),
    (75 / 1024 : k), (75 / 512 : k), (693 / 8192 * l : k),
    (135 / 1024 : k), (315 / 4096 * l : k), (-(189 / 2048 * beta) : k),
    (-(45 / 512 * gamma) : k), (5 / 128 : k), (189 / 8192 * l : k),
    (-(231 / 8192 * beta) : k), (-(15 / 256 * gamma) : k), (-(165 / 2048 * delta) : k),
    (-(3 / 128 * epsilon) : k), (-(15 / 128) : k), (-(15 / 128) : k),
    (-(63 / 1024 * l) : k), (-(25 / 128) : k), (-(27 / 512 * l) : k),
    (-(25 / 128) : k), (-(27 / 256 * l) : k), (7 / 128 * beta : k),
    (-(5 / 64) : k), (-(45 / 1024 * l) : k), (49 / 1024 * beta : k),
    (3 / 32 * gamma : k), (5 / 128 * delta : k), (-(5 / 32) : k),
    (-(45 / 512 * l) : k), (-(5 / 32) : k), (-(45 / 512 * l) : k),
    (49 / 512 * beta : k), (3 / 32 * gamma : k), (-(9 / 128 * l) : k),
    (21 / 256 * beta : k), (21 / 128 * gamma : k), (15 / 64 * delta : k),
    (1 / 8 * epsilon : k), (35 / 1024 * beta : k), (9 / 128 * gamma : k),
    (105 / 1024 * delta : k), (1 / 8 * epsilon : k), (15 / 128 * zeta : k),
    (1 / 32 * eta : k), (5 / 32 : k), (5 / 16 : k),
    (9 / 64 * l : k), (9 / 64 * l : k), (-(7 / 64 * beta) : k),
    (-(3 / 32 * gamma) : k), (-(7 / 64 * beta) : k), (-(3 / 16 * gamma) : k),
    (-(15 / 64 * delta) : k), (-(1 / 8 * epsilon) : k), (-(3 / 32 * gamma) : k),
    (-(5 / 32 * delta) : k), (-(3 / 16 * epsilon) : k), (-(3 / 16 * zeta) : k),
    (-(1 / 16 * eta) : k), (-(5 / 64 * delta) : k), (-(1 / 8 * epsilon) : k),
    (-(9 / 64 * zeta) : k), (-(1 / 8 * eta) : k), (-(1 / 16 * theta) : k),
    (1 / 2 * epsilon : k), (3 / 8 * zeta : k), (1 / 4 * eta : k),
    (1 / 8 * theta : k)]
    [
    [4, 2, 0, 0, 0, 0, 0], [5, 0, 1, 0, 0, 0, 0], [5, 1, 0, 0, 0, 0, 0], [1, 4, 0, 0, 0, 0, 0],
    [2, 2, 1, 0, 0, 0, 0], [2, 3, 0, 0, 0, 0, 0], [3, 0, 2, 0, 0, 0, 0], [3, 1, 0, 1, 0, 0, 0],
    [3, 1, 1, 0, 0, 0, 0], [4, 0, 0, 1, 0, 0, 0], [4, 1, 0, 0, 0, 0, 0], [5, 0, 0, 0, 0, 0, 0],
    [0, 2, 2, 0, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0], [0, 3, 1, 0, 0, 0, 0], [1, 0, 3, 0, 0, 0, 0],
    [1, 1, 1, 1, 0, 0, 0], [1, 1, 2, 0, 0, 0, 0], [1, 2, 0, 0, 1, 0, 0], [1, 2, 0, 1, 0, 0, 0],
    [1, 3, 0, 0, 0, 0, 0], [2, 0, 0, 2, 0, 0, 0], [2, 0, 1, 0, 1, 0, 0], [2, 0, 1, 1, 0, 0, 0],
    [2, 1, 0, 0, 0, 1, 0], [2, 1, 0, 0, 1, 0, 0], [2, 1, 1, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0],
    [3, 0, 0, 0, 0, 0, 1], [3, 0, 0, 0, 0, 1, 0], [3, 0, 0, 1, 0, 0, 0], [3, 0, 1, 0, 0, 0, 0],
    [3, 1, 0, 0, 0, 0, 0], [4, 0, 0, 0, 0, 0, 0], [0, 0, 1, 2, 0, 0, 0], [0, 0, 2, 0, 1, 0, 0],
    [0, 0, 2, 1, 0, 0, 0], [0, 1, 0, 1, 1, 0, 0], [0, 1, 0, 2, 0, 0, 0], [0, 1, 1, 0, 0, 1, 0],
    [0, 1, 1, 0, 1, 0, 0], [0, 1, 2, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 1], [0, 2, 0, 0, 0, 1, 0],
    [0, 2, 0, 1, 0, 0, 0], [0, 2, 1, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0], [1, 0, 0, 1, 0, 1, 0],
    [1, 0, 0, 1, 1, 0, 0], [1, 0, 1, 0, 0, 0, 1], [1, 0, 1, 0, 0, 1, 0], [1, 0, 1, 1, 0, 0, 0],
    [1, 0, 2, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 1], [1, 1, 0, 0, 1, 0, 0], [1, 1, 0, 1, 0, 0, 0],
    [1, 1, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 1, 0], [2, 0, 0, 0, 1, 0, 0],
    [2, 0, 0, 1, 0, 0, 0], [2, 0, 1, 0, 0, 0, 0], [2, 1, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 1, 0, 1], [0, 0, 0, 0, 1, 1, 0], [0, 0, 0, 1, 0, 0, 1],
    [0, 0, 0, 1, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0],
    [0, 0, 1, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0], [0, 1, 0, 0, 0, 1, 0], [0, 1, 0, 0, 1, 0, 0],
    [0, 1, 0, 1, 0, 0, 0], [0, 1, 1, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0],
    [1, 0, 0, 0, 1, 0, 0], [1, 0, 0, 1, 0, 0, 0], [1, 0, 1, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, 0, 0]]

set_option maxHeartbeats 8000000 in
/-- `ξ` without the `A⁷` / `A² D₀²` tie monomials. -/
def degreeZeroXiNoAD05Polynomial810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
    [
    (1925 / 32768 : k), (385 / 16384 : k), (7245 / 524288 * l : k),
    (-(35 / 1024) : k), (-(105 / 512) : k), (-(315 / 8192 * l) : k),
    (-(35 / 512) : k), (-(525 / 4096) : k), (-(315 / 4096 * l) : k),
    (-(245 / 8192) : k), (-(4725 / 262144 * l) : k), (357 / 16384 * beta : k),
    (9 / 1024 * gamma : k), (45 / 512 : k), (55 / 1024 : k),
    (63 / 2048 * l : k), (15 / 256 : k), (165 / 512 : k),
    (189 / 2048 * l : k), (75 / 512 : k), (693 / 8192 * l : k),
    (-(63 / 2048 * beta) : k), (75 / 512 : k), (693 / 8192 * l : k),
    (135 / 1024 : k), (315 / 4096 * l : k), (-(189 / 2048 * beta) : k),
    (-(45 / 512 * gamma) : k), (5 / 128 : k), (189 / 8192 * l : k),
    (-(231 / 8192 * beta) : k), (-(15 / 256 * gamma) : k), (-(165 / 2048 * delta) : k),
    (-(3 / 128 * epsilon) : k), (-(15 / 128) : k), (-(15 / 128) : k),
    (-(63 / 1024 * l) : k), (-(25 / 128) : k), (-(27 / 512 * l) : k),
    (-(25 / 128) : k), (-(27 / 256 * l) : k), (7 / 128 * beta : k),
    (-(5 / 64) : k), (-(45 / 1024 * l) : k), (49 / 1024 * beta : k),
    (3 / 32 * gamma : k), (5 / 128 * delta : k), (-(5 / 64) : k),
    (-(5 / 32) : k), (-(45 / 512 * l) : k), (-(5 / 32) : k),
    (-(45 / 512 * l) : k), (49 / 512 * beta : k), (3 / 32 * gamma : k),
    (-(9 / 128 * l) : k), (21 / 256 * beta : k), (21 / 128 * gamma : k),
    (15 / 64 * delta : k), (1 / 8 * epsilon : k), (35 / 1024 * beta : k),
    (9 / 128 * gamma : k), (105 / 1024 * delta : k), (1 / 8 * epsilon : k),
    (15 / 128 * zeta : k), (1 / 32 * eta : k), (5 / 32 : k),
    (5 / 16 : k), (9 / 64 * l : k), (9 / 64 * l : k),
    (-(7 / 64 * beta) : k), (-(3 / 32 * gamma) : k), (-(7 / 64 * beta) : k),
    (-(3 / 16 * gamma) : k), (-(15 / 64 * delta) : k), (-(1 / 8 * epsilon) : k),
    (-(3 / 32 * gamma) : k), (-(5 / 32 * delta) : k), (-(3 / 16 * epsilon) : k),
    (-(3 / 16 * zeta) : k), (-(1 / 16 * eta) : k), (-(5 / 64 * delta) : k),
    (-(1 / 8 * epsilon) : k), (-(9 / 64 * zeta) : k), (-(1 / 8 * eta) : k),
    (-(1 / 16 * theta) : k), (1 / 2 * epsilon : k), (3 / 8 * zeta : k),
    (1 / 4 * eta : k), (1 / 8 * theta : k)]
    [
    [4, 2, 0, 0, 0, 0, 0], [5, 0, 1, 0, 0, 0, 0], [5, 1, 0, 0, 0, 0, 0], [1, 4, 0, 0, 0, 0, 0],
    [2, 2, 1, 0, 0, 0, 0], [2, 3, 0, 0, 0, 0, 0], [3, 0, 2, 0, 0, 0, 0], [3, 1, 0, 1, 0, 0, 0],
    [3, 1, 1, 0, 0, 0, 0], [4, 0, 0, 0, 1, 0, 0], [4, 0, 0, 1, 0, 0, 0], [4, 1, 0, 0, 0, 0, 0],
    [5, 0, 0, 0, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0], [0, 3, 1, 0, 0, 0, 0],
    [1, 0, 3, 0, 0, 0, 0], [1, 1, 1, 1, 0, 0, 0], [1, 1, 2, 0, 0, 0, 0], [1, 2, 0, 0, 1, 0, 0],
    [1, 2, 0, 1, 0, 0, 0], [1, 3, 0, 0, 0, 0, 0], [2, 0, 1, 0, 1, 0, 0], [2, 0, 1, 1, 0, 0, 0],
    [2, 1, 0, 0, 0, 1, 0], [2, 1, 0, 0, 1, 0, 0], [2, 1, 1, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0],
    [3, 0, 0, 0, 0, 0, 1], [3, 0, 0, 0, 0, 1, 0], [3, 0, 0, 1, 0, 0, 0], [3, 0, 1, 0, 0, 0, 0],
    [3, 1, 0, 0, 0, 0, 0], [4, 0, 0, 0, 0, 0, 0], [0, 0, 1, 2, 0, 0, 0], [0, 0, 2, 0, 1, 0, 0],
    [0, 0, 2, 1, 0, 0, 0], [0, 1, 0, 1, 1, 0, 0], [0, 1, 0, 2, 0, 0, 0], [0, 1, 1, 0, 0, 1, 0],
    [0, 1, 1, 0, 1, 0, 0], [0, 1, 2, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 1], [0, 2, 0, 0, 0, 1, 0],
    [0, 2, 0, 1, 0, 0, 0], [0, 2, 1, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0], [1, 0, 0, 0, 2, 0, 0],
    [1, 0, 0, 1, 0, 1, 0], [1, 0, 0, 1, 1, 0, 0], [1, 0, 1, 0, 0, 0, 1], [1, 0, 1, 0, 0, 1, 0],
    [1, 0, 1, 1, 0, 0, 0], [1, 0, 2, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 1], [1, 1, 0, 0, 1, 0, 0],
    [1, 1, 0, 1, 0, 0, 0], [1, 1, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 1, 0],
    [2, 0, 0, 0, 1, 0, 0], [2, 0, 0, 1, 0, 0, 0], [2, 0, 1, 0, 0, 0, 0], [2, 1, 0, 0, 0, 0, 0],
    [3, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 1, 0, 1], [0, 0, 0, 0, 1, 1, 0],
    [0, 0, 0, 1, 0, 0, 1], [0, 0, 0, 1, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0],
    [0, 0, 1, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0], [0, 1, 0, 0, 0, 1, 0],
    [0, 1, 0, 0, 1, 0, 0], [0, 1, 0, 1, 0, 0, 0], [0, 1, 1, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0],
    [1, 0, 0, 0, 0, 1, 0], [1, 0, 0, 0, 1, 0, 0], [1, 0, 0, 1, 0, 0, 0], [1, 0, 1, 0, 0, 0, 0],
    [1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 1, 0, 0],
    [0, 0, 0, 1, 0, 0, 0]]

set_option maxHeartbeats 8000000 in
/-- `ξ` without the unique `C₀² E₀` monomial. -/
def degreeZeroXiNoC0E0Polynomial810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
    [
    (-(165 / 65536) : k), (1925 / 32768 : k), (385 / 16384 : k),
    (7245 / 524288 * l : k), (-(35 / 1024) : k), (-(105 / 512) : k),
    (-(315 / 8192 * l) : k), (-(35 / 512) : k), (-(525 / 4096) : k),
    (-(315 / 4096 * l) : k), (-(245 / 8192) : k), (-(4725 / 262144 * l) : k),
    (357 / 16384 * beta : k), (9 / 1024 * gamma : k), (45 / 512 : k),
    (55 / 1024 : k), (63 / 2048 * l : k), (15 / 256 : k),
    (165 / 512 : k), (189 / 2048 * l : k), (75 / 512 : k),
    (693 / 8192 * l : k), (-(63 / 2048 * beta) : k), (75 / 1024 : k),
    (75 / 512 : k), (693 / 8192 * l : k), (135 / 1024 : k),
    (315 / 4096 * l : k), (-(189 / 2048 * beta) : k), (-(45 / 512 * gamma) : k),
    (5 / 128 : k), (189 / 8192 * l : k), (-(231 / 8192 * beta) : k),
    (-(15 / 256 * gamma) : k), (-(165 / 2048 * delta) : k), (-(3 / 128 * epsilon) : k),
    (-(15 / 128) : k), (-(63 / 1024 * l) : k), (-(25 / 128) : k),
    (-(27 / 512 * l) : k), (-(25 / 128) : k), (-(27 / 256 * l) : k),
    (7 / 128 * beta : k), (-(5 / 64) : k), (-(45 / 1024 * l) : k),
    (49 / 1024 * beta : k), (3 / 32 * gamma : k), (5 / 128 * delta : k),
    (-(5 / 64) : k), (-(5 / 32) : k), (-(45 / 512 * l) : k),
    (-(5 / 32) : k), (-(45 / 512 * l) : k), (49 / 512 * beta : k),
    (3 / 32 * gamma : k), (-(9 / 128 * l) : k), (21 / 256 * beta : k),
    (21 / 128 * gamma : k), (15 / 64 * delta : k), (1 / 8 * epsilon : k),
    (35 / 1024 * beta : k), (9 / 128 * gamma : k), (105 / 1024 * delta : k),
    (1 / 8 * epsilon : k), (15 / 128 * zeta : k), (1 / 32 * eta : k),
    (5 / 32 : k), (5 / 16 : k), (9 / 64 * l : k),
    (9 / 64 * l : k), (-(7 / 64 * beta) : k), (-(3 / 32 * gamma) : k),
    (-(7 / 64 * beta) : k), (-(3 / 16 * gamma) : k), (-(15 / 64 * delta) : k),
    (-(1 / 8 * epsilon) : k), (-(3 / 32 * gamma) : k), (-(5 / 32 * delta) : k),
    (-(3 / 16 * epsilon) : k), (-(3 / 16 * zeta) : k), (-(1 / 16 * eta) : k),
    (-(5 / 64 * delta) : k), (-(1 / 8 * epsilon) : k), (-(9 / 64 * zeta) : k),
    (-(1 / 8 * eta) : k), (-(1 / 16 * theta) : k), (1 / 2 * epsilon : k),
    (3 / 8 * zeta : k), (1 / 4 * eta : k), (1 / 8 * theta : k)]
    [
    [7, 0, 0, 0, 0, 0, 0], [4, 2, 0, 0, 0, 0, 0], [5, 0, 1, 0, 0, 0, 0], [5, 1, 0, 0, 0, 0, 0],
    [1, 4, 0, 0, 0, 0, 0], [2, 2, 1, 0, 0, 0, 0], [2, 3, 0, 0, 0, 0, 0], [3, 0, 2, 0, 0, 0, 0],
    [3, 1, 0, 1, 0, 0, 0], [3, 1, 1, 0, 0, 0, 0], [4, 0, 0, 0, 1, 0, 0], [4, 0, 0, 1, 0, 0, 0],
    [4, 1, 0, 0, 0, 0, 0], [5, 0, 0, 0, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0],
    [0, 3, 1, 0, 0, 0, 0], [1, 0, 3, 0, 0, 0, 0], [1, 1, 1, 1, 0, 0, 0], [1, 1, 2, 0, 0, 0, 0],
    [1, 2, 0, 0, 1, 0, 0], [1, 2, 0, 1, 0, 0, 0], [1, 3, 0, 0, 0, 0, 0], [2, 0, 0, 2, 0, 0, 0],
    [2, 0, 1, 0, 1, 0, 0], [2, 0, 1, 1, 0, 0, 0], [2, 1, 0, 0, 0, 1, 0], [2, 1, 0, 0, 1, 0, 0],
    [2, 1, 1, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 0, 1], [3, 0, 0, 0, 0, 1, 0],
    [3, 0, 0, 1, 0, 0, 0], [3, 0, 1, 0, 0, 0, 0], [3, 1, 0, 0, 0, 0, 0], [4, 0, 0, 0, 0, 0, 0],
    [0, 0, 1, 2, 0, 0, 0], [0, 0, 2, 1, 0, 0, 0], [0, 1, 0, 1, 1, 0, 0], [0, 1, 0, 2, 0, 0, 0],
    [0, 1, 1, 0, 0, 1, 0], [0, 1, 1, 0, 1, 0, 0], [0, 1, 2, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 1],
    [0, 2, 0, 0, 0, 1, 0], [0, 2, 0, 1, 0, 0, 0], [0, 2, 1, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0],
    [1, 0, 0, 0, 2, 0, 0], [1, 0, 0, 1, 0, 1, 0], [1, 0, 0, 1, 1, 0, 0], [1, 0, 1, 0, 0, 0, 1],
    [1, 0, 1, 0, 0, 1, 0], [1, 0, 1, 1, 0, 0, 0], [1, 0, 2, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 1],
    [1, 1, 0, 0, 1, 0, 0], [1, 1, 0, 1, 0, 0, 0], [1, 1, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0],
    [2, 0, 0, 0, 0, 1, 0], [2, 0, 0, 0, 1, 0, 0], [2, 0, 0, 1, 0, 0, 0], [2, 0, 1, 0, 0, 0, 0],
    [2, 1, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 1, 0, 1],
    [0, 0, 0, 0, 1, 1, 0], [0, 0, 0, 1, 0, 0, 1], [0, 0, 0, 1, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0],
    [0, 0, 1, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0],
    [0, 1, 0, 0, 0, 1, 0], [0, 1, 0, 0, 1, 0, 0], [0, 1, 0, 1, 0, 0, 0], [0, 1, 1, 0, 0, 0, 0],
    [0, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0], [1, 0, 0, 0, 1, 0, 0], [1, 0, 0, 1, 0, 0, 0],
    [1, 0, 1, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0],
    [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, 0, 0]]

set_option maxHeartbeats 8000000 in
/-- `ο` without the three `B`–`E₀` tie monomials. -/
def degreeZeroOmicronNoBE02Polynomial810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
    [
    (-(12705 / 1048576) : k), (-(34155 / 33554432 * l) : k), (3745 / 65536 : k),
    (1365 / 16384 : k), (103005 / 4194304 * l : k), (525 / 32768 : k),
    (19845 / 2097152 * l : k), (-(3927 / 2097152 * beta) : k), (-(105 / 1024) : k),
    (-(945 / 65536 * l) : k), (-(2475 / 16384) : k), (-(2475 / 16384) : k),
    (-(11151 / 131072 * l) : k), (-(795 / 8192) : k), (-(3591 / 131072 * l) : k),
    (-(725 / 8192) : k), (-(3591 / 65536 * l) : k), (4095 / 131072 * beta : k),
    (-(305 / 16384) : k), (-(3087 / 262144 * l) : k), (1953 / 131072 * beta : k),
    (495 / 16384 * gamma : k), (1089 / 131072 * delta : k), (45 / 1024 : k),
    (135 / 1024 : k), (567 / 16384 * l : k), (189 / 8192 * l : k),
    (-(189 / 32768 * beta) : k), (135 / 1024 : k), (189 / 8192 * l : k),
    (135 / 1024 : k), (15 / 64 : k), (567 / 4096 * l : k),
    (105 / 1024 : k), (63 / 1024 * l : k), (-(567 / 8192 * beta) : k),
    (-(45 / 1024 * gamma) : k), (225 / 2048 : k), (135 / 4096 * l : k),
    (195 / 2048 : k), (477 / 8192 * l : k), (-(273 / 8192 * beta) : k),
    (165 / 2048 : k), (207 / 4096 * l : k), (-(273 / 4096 * beta) : k),
    (-(261 / 2048 * gamma) : k), (-(45 / 512 * delta) : k), (99 / 8192 * l : k),
    (-(147 / 8192 * beta) : k), (-(81 / 2048 * gamma) : k), (-(225 / 4096 * delta) : k),
    (-(33 / 512 * epsilon) : k), (-(495 / 32768 * zeta) : k), (-(5 / 128) : k),
    (-(25 / 128) : k), (-(27 / 512 * l) : k), (-(5 / 64) : k),
    (-(45 / 1024 * l) : k), (7 / 512 * beta : k), (-(5 / 32) : k),
    (-(45 / 512 * l) : k), (-(15 / 128) : k), (-(9 / 128 * l) : k),
    (21 / 256 * beta : k), (9 / 128 * gamma : k), (-(27 / 1024 * l) : k),
    (35 / 1024 * beta : k), (9 / 128 * gamma : k), (45 / 512 * delta : k),
    (1 / 32 * epsilon : k), (-(15 / 128) : k), (-(9 / 256 * l) : k),
    (-(15 / 128) : k), (-(9 / 128 * l) : k), (21 / 512 * beta : k),
    (-(27 / 512 * l) : k), (35 / 512 * beta : k), (9 / 64 * gamma : k),
    (45 / 512 * delta : k), (7 / 128 * beta : k), (15 / 128 * gamma : k),
    (45 / 256 * delta : k), (3 / 16 * epsilon : k), (45 / 512 * zeta : k),
    (15 / 512 * gamma : k), (15 / 256 * delta : k), (21 / 256 * epsilon : k),
    (81 / 1024 * zeta : k), (33 / 512 * eta : k), (11 / 1024 * theta : k),
    (5 / 16 : k), (9 / 128 * l : k), (9 / 64 * l : k),
    (-(7 / 128 * beta) : k), (-(7 / 64 * beta) : k), (-(3 / 16 * gamma) : k),
    (-(15 / 128 * delta) : k), (-(3 / 32 * gamma) : k), (-(5 / 32 * delta) : k),
    (-(3 / 16 * epsilon) : k), (-(9 / 128 * zeta) : k), (-(5 / 64 * delta) : k),
    (-(1 / 8 * epsilon) : k), (-(9 / 64 * zeta) : k), (-(3 / 32 * eta) : k),
    (-(3 / 128 * theta) : k), (-(1 / 16 * epsilon) : k), (-(3 / 32 * zeta) : k),
    (-(3 / 32 * eta) : k), (-(3 / 64 * theta) : k), (3 / 8 * zeta : k),
    (1 / 4 * eta : k), (1 / 8 * theta : k)]
    [
    [6, 1, 0, 0, 0, 0, 0], [7, 0, 0, 0, 0, 0, 0], [3, 3, 0, 0, 0, 0, 0], [4, 1, 1, 0, 0, 0, 0],
    [4, 2, 0, 0, 0, 0, 0], [5, 0, 0, 1, 0, 0, 0], [5, 0, 1, 0, 0, 0, 0], [6, 0, 0, 0, 0, 0, 0],
    [1, 3, 1, 0, 0, 0, 0], [1, 4, 0, 0, 0, 0, 0], [2, 1, 2, 0, 0, 0, 0], [2, 2, 0, 1, 0, 0, 0],
    [2, 2, 1, 0, 0, 0, 0], [3, 0, 1, 1, 0, 0, 0], [3, 0, 2, 0, 0, 0, 0], [3, 1, 0, 0, 1, 0, 0],
    [3, 1, 0, 1, 0, 0, 0], [3, 2, 0, 0, 0, 0, 0], [4, 0, 0, 0, 0, 1, 0], [4, 0, 0, 0, 1, 0, 0],
    [4, 0, 1, 0, 0, 0, 0], [4, 1, 0, 0, 0, 0, 0], [5, 0, 0, 0, 0, 0, 0], [0, 1, 3, 0, 0, 0, 0],
    [0, 2, 1, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0],
    [1, 0, 2, 1, 0, 0, 0], [1, 0, 3, 0, 0, 0, 0], [1, 1, 0, 2, 0, 0, 0], [1, 1, 1, 0, 1, 0, 0],
    [1, 1, 1, 1, 0, 0, 0], [1, 2, 0, 0, 0, 1, 0], [1, 2, 0, 0, 1, 0, 0], [1, 2, 1, 0, 0, 0, 0],
    [1, 3, 0, 0, 0, 0, 0], [2, 0, 0, 1, 1, 0, 0], [2, 0, 0, 2, 0, 0, 0], [2, 0, 1, 0, 0, 1, 0],
    [2, 0, 1, 0, 1, 0, 0], [2, 0, 2, 0, 0, 0, 0], [2, 1, 0, 0, 0, 0, 1], [2, 1, 0, 0, 0, 1, 0],
    [2, 1, 0, 1, 0, 0, 0], [2, 1, 1, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 0, 1],
    [3, 0, 0, 0, 1, 0, 0], [3, 0, 0, 1, 0, 0, 0], [3, 0, 1, 0, 0, 0, 0], [3, 1, 0, 0, 0, 0, 0],
    [4, 0, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0], [0, 0, 1, 1, 1, 0, 0], [0, 0, 1, 2, 0, 0, 0],
    [0, 0, 2, 0, 0, 1, 0], [0, 0, 2, 0, 1, 0, 0], [0, 0, 3, 0, 0, 0, 0], [0, 1, 0, 1, 0, 1, 0],
    [0, 1, 0, 1, 1, 0, 0], [0, 1, 1, 0, 0, 0, 1], [0, 1, 1, 0, 0, 1, 0], [0, 1, 1, 1, 0, 0, 0],
    [0, 1, 2, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 1], [0, 2, 0, 0, 1, 0, 0], [0, 2, 0, 1, 0, 0, 0],
    [0, 2, 1, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0], [1, 0, 0, 0, 1, 1, 0], [1, 0, 0, 0, 2, 0, 0],
    [1, 0, 0, 1, 0, 0, 1], [1, 0, 0, 1, 0, 1, 0], [1, 0, 0, 2, 0, 0, 0], [1, 0, 1, 0, 0, 0, 1],
    [1, 0, 1, 0, 1, 0, 0], [1, 0, 1, 1, 0, 0, 0], [1, 0, 2, 0, 0, 0, 0], [1, 1, 0, 0, 0, 1, 0],
    [1, 1, 0, 0, 1, 0, 0], [1, 1, 0, 1, 0, 0, 0], [1, 1, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0],
    [2, 0, 0, 0, 0, 1, 0], [2, 0, 0, 0, 1, 0, 0], [2, 0, 0, 1, 0, 0, 0], [2, 0, 1, 0, 0, 0, 0],
    [2, 1, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 0, 2, 0],
    [0, 0, 0, 0, 1, 0, 1], [0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 1, 1, 0, 0],
    [0, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0],
    [0, 0, 2, 0, 0, 0, 0], [0, 1, 0, 0, 0, 1, 0], [0, 1, 0, 0, 1, 0, 0], [0, 1, 0, 1, 0, 0, 0],
    [0, 1, 1, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0], [1, 0, 0, 0, 1, 0, 0],
    [1, 0, 0, 1, 0, 0, 0], [1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0],
    [0, 0, 0, 0, 1, 0, 0]]

set_option maxHeartbeats 8000000 in
/-- `ο` without the `A⁵ D₀` / `D₀³` tie monomials. -/
def degreeZeroOmicronNoAD05Polynomial810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
    [
    (-(12705 / 1048576) : k), (-(34155 / 33554432 * l) : k), (3745 / 65536 : k),
    (1365 / 16384 : k), (103005 / 4194304 * l : k), (19845 / 2097152 * l : k),
    (-(3927 / 2097152 * beta) : k), (-(21 / 4096) : k), (-(105 / 1024) : k),
    (-(945 / 65536 * l) : k), (-(2475 / 16384) : k), (-(2475 / 16384) : k),
    (-(11151 / 131072 * l) : k), (-(795 / 8192) : k), (-(3591 / 131072 * l) : k),
    (-(725 / 8192) : k), (-(3591 / 65536 * l) : k), (4095 / 131072 * beta : k),
    (-(305 / 16384) : k), (-(3087 / 262144 * l) : k), (1953 / 131072 * beta : k),
    (495 / 16384 * gamma : k), (1089 / 131072 * delta : k), (45 / 1024 : k),
    (135 / 1024 : k), (567 / 16384 * l : k), (5 / 128 : k),
    (189 / 8192 * l : k), (-(189 / 32768 * beta) : k), (135 / 1024 : k),
    (189 / 8192 * l : k), (135 / 1024 : k), (15 / 64 : k),
    (567 / 4096 * l : k), (105 / 1024 : k), (63 / 1024 * l : k),
    (-(567 / 8192 * beta) : k), (-(45 / 1024 * gamma) : k), (225 / 2048 : k),
    (135 / 4096 * l : k), (195 / 2048 : k), (477 / 8192 * l : k),
    (-(273 / 8192 * beta) : k), (165 / 2048 : k), (207 / 4096 * l : k),
    (-(273 / 4096 * beta) : k), (-(261 / 2048 * gamma) : k), (-(45 / 512 * delta) : k),
    (99 / 8192 * l : k), (-(147 / 8192 * beta) : k), (-(81 / 2048 * gamma) : k),
    (-(225 / 4096 * delta) : k), (-(33 / 512 * epsilon) : k), (-(495 / 32768 * zeta) : k),
    (-(25 / 128) : k), (-(27 / 512 * l) : k), (-(5 / 64) : k),
    (-(45 / 1024 * l) : k), (7 / 512 * beta : k), (-(5 / 64) : k),
    (-(5 / 32) : k), (-(45 / 512 * l) : k), (-(15 / 128) : k),
    (-(9 / 128 * l) : k), (21 / 256 * beta : k), (9 / 128 * gamma : k),
    (-(27 / 1024 * l) : k), (35 / 1024 * beta : k), (9 / 128 * gamma : k),
    (45 / 512 * delta : k), (1 / 32 * epsilon : k), (-(15 / 128) : k),
    (-(9 / 256 * l) : k), (-(15 / 128) : k), (-(9 / 128 * l) : k),
    (21 / 512 * beta : k), (-(27 / 512 * l) : k), (35 / 512 * beta : k),
    (9 / 64 * gamma : k), (45 / 512 * delta : k), (7 / 128 * beta : k),
    (15 / 128 * gamma : k), (45 / 256 * delta : k), (3 / 16 * epsilon : k),
    (45 / 512 * zeta : k), (15 / 512 * gamma : k), (15 / 256 * delta : k),
    (21 / 256 * epsilon : k), (81 / 1024 * zeta : k), (33 / 512 * eta : k),
    (11 / 1024 * theta : k), (5 / 16 : k), (9 / 128 * l : k),
    (9 / 64 * l : k), (-(7 / 128 * beta) : k), (-(7 / 64 * beta) : k),
    (-(3 / 16 * gamma) : k), (-(15 / 128 * delta) : k), (-(3 / 32 * gamma) : k),
    (-(5 / 32 * delta) : k), (-(3 / 16 * epsilon) : k), (-(9 / 128 * zeta) : k),
    (-(5 / 64 * delta) : k), (-(1 / 8 * epsilon) : k), (-(9 / 64 * zeta) : k),
    (-(3 / 32 * eta) : k), (-(3 / 128 * theta) : k), (-(1 / 16 * epsilon) : k),
    (-(3 / 32 * zeta) : k), (-(3 / 32 * eta) : k), (-(3 / 64 * theta) : k),
    (3 / 8 * zeta : k), (1 / 4 * eta : k), (1 / 8 * theta : k)]
    [
    [6, 1, 0, 0, 0, 0, 0], [7, 0, 0, 0, 0, 0, 0], [3, 3, 0, 0, 0, 0, 0], [4, 1, 1, 0, 0, 0, 0],
    [4, 2, 0, 0, 0, 0, 0], [5, 0, 1, 0, 0, 0, 0], [6, 0, 0, 0, 0, 0, 0], [0, 5, 0, 0, 0, 0, 0],
    [1, 3, 1, 0, 0, 0, 0], [1, 4, 0, 0, 0, 0, 0], [2, 1, 2, 0, 0, 0, 0], [2, 2, 0, 1, 0, 0, 0],
    [2, 2, 1, 0, 0, 0, 0], [3, 0, 1, 1, 0, 0, 0], [3, 0, 2, 0, 0, 0, 0], [3, 1, 0, 0, 1, 0, 0],
    [3, 1, 0, 1, 0, 0, 0], [3, 2, 0, 0, 0, 0, 0], [4, 0, 0, 0, 0, 1, 0], [4, 0, 0, 0, 1, 0, 0],
    [4, 0, 1, 0, 0, 0, 0], [4, 1, 0, 0, 0, 0, 0], [5, 0, 0, 0, 0, 0, 0], [0, 1, 3, 0, 0, 0, 0],
    [0, 2, 1, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0], [0, 3, 0, 0, 1, 0, 0], [0, 3, 0, 1, 0, 0, 0],
    [0, 4, 0, 0, 0, 0, 0], [1, 0, 2, 1, 0, 0, 0], [1, 0, 3, 0, 0, 0, 0], [1, 1, 0, 2, 0, 0, 0],
    [1, 1, 1, 0, 1, 0, 0], [1, 1, 1, 1, 0, 0, 0], [1, 2, 0, 0, 0, 1, 0], [1, 2, 0, 0, 1, 0, 0],
    [1, 2, 1, 0, 0, 0, 0], [1, 3, 0, 0, 0, 0, 0], [2, 0, 0, 1, 1, 0, 0], [2, 0, 0, 2, 0, 0, 0],
    [2, 0, 1, 0, 0, 1, 0], [2, 0, 1, 0, 1, 0, 0], [2, 0, 2, 0, 0, 0, 0], [2, 1, 0, 0, 0, 0, 1],
    [2, 1, 0, 0, 0, 1, 0], [2, 1, 0, 1, 0, 0, 0], [2, 1, 1, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0],
    [3, 0, 0, 0, 0, 0, 1], [3, 0, 0, 0, 1, 0, 0], [3, 0, 0, 1, 0, 0, 0], [3, 0, 1, 0, 0, 0, 0],
    [3, 1, 0, 0, 0, 0, 0], [4, 0, 0, 0, 0, 0, 0], [0, 0, 1, 1, 1, 0, 0], [0, 0, 1, 2, 0, 0, 0],
    [0, 0, 2, 0, 0, 1, 0], [0, 0, 2, 0, 1, 0, 0], [0, 0, 3, 0, 0, 0, 0], [0, 1, 0, 0, 2, 0, 0],
    [0, 1, 0, 1, 0, 1, 0], [0, 1, 0, 1, 1, 0, 0], [0, 1, 1, 0, 0, 0, 1], [0, 1, 1, 0, 0, 1, 0],
    [0, 1, 1, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 1], [0, 2, 0, 0, 1, 0, 0],
    [0, 2, 0, 1, 0, 0, 0], [0, 2, 1, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0], [1, 0, 0, 0, 1, 1, 0],
    [1, 0, 0, 0, 2, 0, 0], [1, 0, 0, 1, 0, 0, 1], [1, 0, 0, 1, 0, 1, 0], [1, 0, 0, 2, 0, 0, 0],
    [1, 0, 1, 0, 0, 0, 1], [1, 0, 1, 0, 1, 0, 0], [1, 0, 1, 1, 0, 0, 0], [1, 0, 2, 0, 0, 0, 0],
    [1, 1, 0, 0, 0, 1, 0], [1, 1, 0, 0, 1, 0, 0], [1, 1, 0, 1, 0, 0, 0], [1, 1, 1, 0, 0, 0, 0],
    [1, 2, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 1, 0], [2, 0, 0, 0, 1, 0, 0], [2, 0, 0, 1, 0, 0, 0],
    [2, 0, 1, 0, 0, 0, 0], [2, 1, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1],
    [0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 1, 0, 1], [0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 1, 0, 1, 0],
    [0, 0, 0, 1, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0],
    [0, 0, 1, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0], [0, 1, 0, 0, 0, 1, 0], [0, 1, 0, 0, 1, 0, 0],
    [0, 1, 0, 1, 0, 0, 0], [0, 1, 1, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0],
    [1, 0, 0, 0, 1, 0, 0], [1, 0, 0, 1, 0, 0, 0], [1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1],
    [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 1, 0, 0]]

end ExhaustCombined810


/-! ## Rest-degree bounds -/

section ExhaustRests810

variable {k : Type*} [Field k] [CharZero k]

end ExhaustRests810


/-! ## Combined-face degrees from inner forms -/

section ExhaustCombinedDeg810

variable {k : Type*} [Field k] [CharZero k]

end ExhaustCombinedDeg810


/-! ## Unique-face and Groebner-tie impossibilities -/

section ExhaustImpossible810

variable {k : Type*} [Field k] [CharZero k]

end ExhaustImpossible810


/-! ## Affine form of the primitive on unique-`G₀` with `l = 0` -/

section ExhaustG0Affine810

variable {k : Type*} [Field k] [CharZero k]

/-- `G₀`-linear coefficient of `ρ_base` at `l = 0`.  Every remaining
`G₀` monomial is linear, and the quadratic face `G₀² L` has vanished. -/
def rhoBaseG0LinearCoeff810 (A B C0 D0 E0 F0 : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0]
    [
    (-(255 / 2048) : k), (15 / 256 : k), (45 / 128 : k),
    (45 / 256 : k), (-(5 / 16) : k), (-(5 / 16) : k),
    (-(5 / 16) : k)]
    [
    [3, 1, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0], [1, 1, 1, 0, 0, 0], [2, 0, 0, 1, 0, 0],
    [0, 0, 1, 1, 0, 0], [0, 1, 0, 0, 1, 0], [1, 0, 0, 0, 0, 1]]

/-- `G₀`-linear monomials of `ρ_base` at `l = 0`, before factoring `G₀`. -/
def rhoBaseG0LinearTerms810 (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
    [
    (-(255 / 2048) : k), (15 / 256 : k), (45 / 128 : k),
    (45 / 256 : k), (-(5 / 16) : k), (-(5 / 16) : k),
    (-(5 / 16) : k)]
    [
    [3, 1, 0, 0, 0, 0, 1], [0, 3, 0, 0, 0, 0, 1], [1, 1, 1, 0, 0, 0, 1], [2, 0, 0, 1, 0, 0, 1],
    [0, 0, 1, 1, 0, 0, 1], [0, 1, 0, 0, 1, 0, 1], [1, 0, 0, 0, 0, 1, 1]]

end ExhaustG0Affine810


/-! ## Source-facing exhaustion -/

section ExhaustClosed810

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

end ExhaustClosed810



end Max11DegreeRoutes

