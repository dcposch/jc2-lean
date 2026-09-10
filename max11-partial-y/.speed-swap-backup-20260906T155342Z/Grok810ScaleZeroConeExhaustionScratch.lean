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

/-- Groebner membership `C₀⁶ ∈ (μ_inner, ξ_inner)`.  CAS: saturating by
`s` yields `(1)`. -/
theorem mu_xi_AC02_inner_identity (r s : k) :
    (231 * r ^ 6 - 4004 * r ^ 4 * s + 8736 * r ^ 2 * s ^ 2 - 2048 * s ^ 3) *
        muAC02Inner810 r s +
      (-(49 : k) * r * (11 * r ^ 4 - 176 * r ^ 2 * s + 192 * s ^ 2)) *
        xiAC02Inner810 r s =
      (1048576 : k) * s ^ 6 := by
  simp only [muAC02Inner810, xiAC02Inner810]
  ring

theorem mu_xi_AC02_inner_s_pow (r s : k)
    (hmu : muAC02Inner810 r s = 0)
    (hxi : xiAC02Inner810 r s = 0) :
    s ^ 6 = 0 := by
  have hid := mu_xi_AC02_inner_identity (k := k) r s
  have hcomb : (1048576 : k) * s ^ 6 = 0 := by
    rw [← hid, hmu, hxi]
    simp
  have hne : (1048576 : k) ≠ 0 := by norm_num
  exact (mul_eq_zero.mp hcomb).resolve_left hne

/-- Load-free `μ` inner form on `deg E₀ = 3 deg A`. -/
def muAE06Inner810 (r v : k) : k :=
  (77 : k) * r ^ 6 + 896 * r ^ 3 * v + 2048 * v ^ 2

def xiAE06Inner810 (r v : k) : k :=
  r * (r ^ 3 + 8 * v) * (33 * r ^ 3 + 128 * v)

theorem mu_xi_AE06_inner_identity (r v : k) :
    (231 * r ^ 6 + 3668 * r ^ 3 * v + 1248 * v ^ 2) * muAE06Inner810 r v +
      (-(49 : k) * r ^ 2 * (11 * r ^ 3 + 172 * v)) * xiAE06Inner810 r v =
      (2555904 : k) * v ^ 4 := by
  simp only [muAE06Inner810, xiAE06Inner810]
  ring

theorem mu_xi_AE06_inner_v_pow (r v : k)
    (hmu : muAE06Inner810 r v = 0)
    (hxi : xiAE06Inner810 r v = 0) :
    v ^ 4 = 0 := by
  have hid := mu_xi_AE06_inner_identity (k := k) r v
  have hcomb : (2555904 : k) * v ^ 4 = 0 := by
    rw [← hid, hmu, hxi]
    simp
  have hne : (2555904 : k) ≠ 0 := by norm_num
  exact (mul_eq_zero.mp hcomb).resolve_left hne

/-- Load-free `μ` inner form on `deg E₀ = 2 deg B`. -/
def muBE02Inner810 (s w : k) : k :=
  (7 : k) * s ^ 4 - 48 * s ^ 2 * w + 64 * w ^ 2

def omicronBE02Inner810 (s w : k) : k :=
  s * (21 * s ^ 4 - 160 * s ^ 2 * w + 320 * w ^ 2)

theorem mu_omicron_BE02_inner_identity (s w : k) :
    (21 * s ^ 4 - 328 * s ^ 2 * w + 256 * w ^ 2) * muBE02Inner810 s w +
      (-(s : k) * (7 * s ^ 2 - 104 * w)) * omicronBE02Inner810 s w =
      (16384 : k) * w ^ 4 := by
  simp only [muBE02Inner810, omicronBE02Inner810]
  ring

theorem mu_omicron_BE02_inner_w_pow (s w : k)
    (hmu : muBE02Inner810 s w = 0)
    (hom : omicronBE02Inner810 s w = 0) :
    w ^ 4 = 0 := by
  have hid := mu_omicron_BE02_inner_identity (k := k) s w
  have hcomb : (16384 : k) * w ^ 4 = 0 := by
    rw [← hid, hmu, hom]
    simp
  have hne : (16384 : k) ≠ 0 := by norm_num
  exact (mul_eq_zero.mp hcomb).resolve_left hne

/-- Cleared `μ`/`ξ` inner forms on `5 deg A = 2 deg D₀`. -/
def muAD05Inner810 (r d : k) : k :=
  (5 : k) * r * (77 * r ^ 5 - 1536 * d ^ 2)

def xiAD05Inner810 (r d : k) : k :=
  (-(15 : k)) * r ^ 2 * (11 * r ^ 5 - 320 * d ^ 2)

/-- `(r/121) μ_inner + (8/605) ξ_inner = r⁷`. -/
theorem mu_xi_AD05_inner_identity (r d : k) :
    (5 : k) * r ^ 2 * (77 * r ^ 5 - 1536 * d ^ 2) -
        24 * r ^ 2 * (11 * r ^ 5 - 320 * d ^ 2) =
      (121 : k) * r ^ 7 := by
  ring

theorem mu_xi_AD05_inner_r_pow (r d : k)
    (hmu : muAD05Inner810 r d = 0)
    (hxi : xiAD05Inner810 r d = 0) :
    r ^ 7 = 0 := by
  have hid := mu_xi_AD05_inner_identity (k := k) r d
  have h5 : (5 : k) * r * (77 * r ^ 5 - 1536 * d ^ 2) = 0 := hmu
  have h15 : (15 : k) * r ^ 2 * (11 * r ^ 5 - 320 * d ^ 2) = 0 := by
    have := hxi
    simpa [xiAD05Inner810, neg_mul] using this
  have hleft :
      (5 : k) * r ^ 2 * (77 * r ^ 5 - 1536 * d ^ 2) -
          24 * r ^ 2 * (11 * r ^ 5 - 320 * d ^ 2) = 0 := by
    have hr : (5 : k) * r ^ 2 * (77 * r ^ 5 - 1536 * d ^ 2) =
        r * ((5 : k) * r * (77 * r ^ 5 - 1536 * d ^ 2)) := by ring
    have h24 : (24 : k) * r ^ 2 * (11 * r ^ 5 - 320 * d ^ 2) =
        (8 : k) / 5 * ((15 : k) * r ^ 2 * (11 * r ^ 5 - 320 * d ^ 2)) := by
      ring
    simp [hr, h5, h24, h15]
  have h121 : (121 : k) * r ^ 7 = 0 := by
    rw [← hid, hleft]
  have hne : (121 : k) ≠ 0 := by norm_num
  exact (mul_eq_zero.mp h121).resolve_left hne

end ExhaustIdentities810


/-! ## Combined faces and rest polynomials -/

section ExhaustCombined810

variable {k : Type*} [Field k] [CharZero k]

def muA6Face810 (A : k[X]) : k[X] :=
  (385 / 65536 : k) • A ^ 6

def muAC02Combined810 (A C0 : k[X]) : k[X] :=
  (385 / 65536 : k) • A ^ 6 -
    (385 / 8192 : k) • (A ^ 4 * C0) +
    (105 / 1024 : k) • (A ^ 2 * C0 ^ 2) -
    (5 / 128 : k) • C0 ^ 3

def xiAC02Combined810 (A C0 : k[X]) : k[X] :=
  -(165 / 65536 : k) • A ^ 7 +
    (385 / 16384 : k) • (A ^ 5 * C0) -
    (35 / 512 : k) • (A ^ 3 * C0 ^ 2) +
    (15 / 256 : k) • (A * C0 ^ 3)

def muAE06Combined810 (A E0 : k[X]) : k[X] :=
  (385 / 65536 : k) • A ^ 6 +
    (35 / 512 : k) • (A ^ 3 * E0) +
    (5 / 32 : k) • E0 ^ 2

def xiAE06Combined810 (A E0 : k[X]) : k[X] :=
  -(165 / 65536 : k) • A ^ 7 -
    (245 / 8192 : k) • (A ^ 4 * E0) -
    (5 / 64 : k) • (A * E0 ^ 2)

def muBE02Combined810 (B E0 : k[X]) : k[X] :=
  (35 / 2048 : k) • B ^ 4 -
    (15 / 128 : k) • (B ^ 2 * E0) +
    (5 / 32 : k) • E0 ^ 2

def omicronBE02Combined810 (B E0 : k[X]) : k[X] :=
  -(21 / 4096 : k) • B ^ 5 +
    (5 / 128 : k) • (B ^ 3 * E0) -
    (5 / 64 : k) • (B * E0 ^ 2)

def muAD05Combined810 (A D0 : k[X]) : k[X] :=
  (385 / 65536 : k) • A ^ 6 -
    (15 / 128 : k) • (A * D0 ^ 2)

def xiAD05Combined810 (A D0 : k[X]) : k[X] :=
  -(165 / 65536 : k) • A ^ 7 +
    (75 / 1024 : k) • (A ^ 2 * D0 ^ 2)

def xiC0E0Face810 (C0 E0 : k[X]) : k[X] :=
  -(15 / 128 : k) • (C0 ^ 2 * E0)


set_option maxHeartbeats 8000000 in
/-- `μ` with the unique `A⁶` face deleted. -/
def degreeZeroMuNoA6Polynomial810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  - (385 / 4096 : k) • (A ^ 3 * B ^ 2)
    - (385 / 8192 : k) • (A ^ 4 * C0)
    - (7245 / 262144 * l : k) • (A ^ 4 * B)
    + (35 / 2048 : k) • B ^ 4
    + (105 / 512 : k) • (A * B ^ 2 * C0)
    + (315 / 8192 * l : k) • (A * B ^ 3)
    + (105 / 1024 : k) • (A ^ 2 * C0 ^ 2)
    + (105 / 512 : k) • (A ^ 2 * B * D0)
    + (945 / 8192 * l : k) • (A ^ 2 * B * C0)
    + (35 / 512 : k) • (A ^ 3 * E0)
    + (315 / 8192 * l : k) • (A ^ 3 * D0)
    - (357 / 8192 * beta : k) • (A ^ 3 * B)
    - (45 / 2048 * gamma : k) • A ^ 4
    - (5 / 128 : k) • C0 ^ 3
    - (15 / 64 : k) • (B * C0 * D0)
    - (63 / 1024 * l : k) • (B * C0 ^ 2)
    - (15 / 128 : k) • (B ^ 2 * E0)
    - (63 / 1024 * l : k) • (B ^ 2 * D0)
    + (21 / 1024 * beta : k) • B ^ 3
    - (15 / 128 : k) • (A * D0 ^ 2)
    - (15 / 64 : k) • (A * C0 * E0)
    - (63 / 512 * l : k) • (A * C0 * D0)
    - (15 / 64 : k) • (A * B * F0)
    - (63 / 512 * l : k) • (A * B * E0)
    + (63 / 512 * beta : k) • (A * B * C0)
    + (15 / 128 * gamma : k) • (A * B ^ 2)
    - (15 / 128 : k) • (A ^ 2 * G0)
    - (63 / 1024 * l : k) • (A ^ 2 * F0)
    + (63 / 1024 * beta : k) • (A ^ 2 * D0)
    + (15 / 128 * gamma : k) • (A ^ 2 * C0)
    + (165 / 1024 * delta : k) • (A ^ 2 * B)
    + (1 / 16 * epsilon : k) • A ^ 3
    + (5 / 32 : k) • E0 ^ 2
    + (5 / 16 : k) • (D0 * F0)
    + (9 / 64 * l : k) • (D0 * E0)
    + (5 / 16 : k) • (C0 * G0)
    + (9 / 64 * l : k) • (C0 * F0)
    - (7 / 64 * beta : k) • (C0 * D0)
    - (3 / 32 * gamma : k) • C0 ^ 2
    + (9 / 64 * l : k) • (B * G0)
    - (7 / 64 * beta : k) • (B * E0)
    - (3 / 16 * gamma : k) • (B * D0)
    - (15 / 64 * delta : k) • (B * C0)
    - (1 / 8 * epsilon : k) • B ^ 2
    - (7 / 64 * beta : k) • (A * F0)
    - (3 / 16 * gamma : k) • (A * E0)
    - (15 / 64 * delta : k) • (A * D0)
    - (1 / 4 * epsilon : k) • (A * C0)
    - (15 / 64 * zeta : k) • (A * B)
    - (3 / 32 * eta : k) • A ^ 2
    + (3 / 4 * gamma : k) • G0
    + (5 / 8 * delta : k) • F0
    + (1 / 2 * epsilon : k) • E0
    + (3 / 8 * zeta : k) • D0
    + (1 / 4 * eta : k) • C0
    + (1 / 8 * theta : k) • B

set_option maxHeartbeats 8000000 in
/-- `μ` without the four `A`–`C₀` tie monomials. -/
def degreeZeroMuNoAC02Polynomial810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  - (385 / 4096 : k) • (A ^ 3 * B ^ 2)
    - (7245 / 262144 * l : k) • (A ^ 4 * B)
    + (35 / 2048 : k) • B ^ 4
    + (105 / 512 : k) • (A * B ^ 2 * C0)
    + (315 / 8192 * l : k) • (A * B ^ 3)
    + (105 / 512 : k) • (A ^ 2 * B * D0)
    + (945 / 8192 * l : k) • (A ^ 2 * B * C0)
    + (35 / 512 : k) • (A ^ 3 * E0)
    + (315 / 8192 * l : k) • (A ^ 3 * D0)
    - (357 / 8192 * beta : k) • (A ^ 3 * B)
    - (45 / 2048 * gamma : k) • A ^ 4
    - (15 / 64 : k) • (B * C0 * D0)
    - (63 / 1024 * l : k) • (B * C0 ^ 2)
    - (15 / 128 : k) • (B ^ 2 * E0)
    - (63 / 1024 * l : k) • (B ^ 2 * D0)
    + (21 / 1024 * beta : k) • B ^ 3
    - (15 / 128 : k) • (A * D0 ^ 2)
    - (15 / 64 : k) • (A * C0 * E0)
    - (63 / 512 * l : k) • (A * C0 * D0)
    - (15 / 64 : k) • (A * B * F0)
    - (63 / 512 * l : k) • (A * B * E0)
    + (63 / 512 * beta : k) • (A * B * C0)
    + (15 / 128 * gamma : k) • (A * B ^ 2)
    - (15 / 128 : k) • (A ^ 2 * G0)
    - (63 / 1024 * l : k) • (A ^ 2 * F0)
    + (63 / 1024 * beta : k) • (A ^ 2 * D0)
    + (15 / 128 * gamma : k) • (A ^ 2 * C0)
    + (165 / 1024 * delta : k) • (A ^ 2 * B)
    + (1 / 16 * epsilon : k) • A ^ 3
    + (5 / 32 : k) • E0 ^ 2
    + (5 / 16 : k) • (D0 * F0)
    + (9 / 64 * l : k) • (D0 * E0)
    + (5 / 16 : k) • (C0 * G0)
    + (9 / 64 * l : k) • (C0 * F0)
    - (7 / 64 * beta : k) • (C0 * D0)
    - (3 / 32 * gamma : k) • C0 ^ 2
    + (9 / 64 * l : k) • (B * G0)
    - (7 / 64 * beta : k) • (B * E0)
    - (3 / 16 * gamma : k) • (B * D0)
    - (15 / 64 * delta : k) • (B * C0)
    - (1 / 8 * epsilon : k) • B ^ 2
    - (7 / 64 * beta : k) • (A * F0)
    - (3 / 16 * gamma : k) • (A * E0)
    - (15 / 64 * delta : k) • (A * D0)
    - (1 / 4 * epsilon : k) • (A * C0)
    - (15 / 64 * zeta : k) • (A * B)
    - (3 / 32 * eta : k) • A ^ 2
    + (3 / 4 * gamma : k) • G0
    + (5 / 8 * delta : k) • F0
    + (1 / 2 * epsilon : k) • E0
    + (3 / 8 * zeta : k) • D0
    + (1 / 4 * eta : k) • C0
    + (1 / 8 * theta : k) • B

set_option maxHeartbeats 8000000 in
/-- `μ` without the three `A`–`E₀` Newton-tie monomials. -/
def degreeZeroMuNoAE06Polynomial810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  - (385 / 4096 : k) • (A ^ 3 * B ^ 2)
    - (385 / 8192 : k) • (A ^ 4 * C0)
    - (7245 / 262144 * l : k) • (A ^ 4 * B)
    + (35 / 2048 : k) • B ^ 4
    + (105 / 512 : k) • (A * B ^ 2 * C0)
    + (315 / 8192 * l : k) • (A * B ^ 3)
    + (105 / 1024 : k) • (A ^ 2 * C0 ^ 2)
    + (105 / 512 : k) • (A ^ 2 * B * D0)
    + (945 / 8192 * l : k) • (A ^ 2 * B * C0)
    + (315 / 8192 * l : k) • (A ^ 3 * D0)
    - (357 / 8192 * beta : k) • (A ^ 3 * B)
    - (45 / 2048 * gamma : k) • A ^ 4
    - (5 / 128 : k) • C0 ^ 3
    - (15 / 64 : k) • (B * C0 * D0)
    - (63 / 1024 * l : k) • (B * C0 ^ 2)
    - (15 / 128 : k) • (B ^ 2 * E0)
    - (63 / 1024 * l : k) • (B ^ 2 * D0)
    + (21 / 1024 * beta : k) • B ^ 3
    - (15 / 128 : k) • (A * D0 ^ 2)
    - (15 / 64 : k) • (A * C0 * E0)
    - (63 / 512 * l : k) • (A * C0 * D0)
    - (15 / 64 : k) • (A * B * F0)
    - (63 / 512 * l : k) • (A * B * E0)
    + (63 / 512 * beta : k) • (A * B * C0)
    + (15 / 128 * gamma : k) • (A * B ^ 2)
    - (15 / 128 : k) • (A ^ 2 * G0)
    - (63 / 1024 * l : k) • (A ^ 2 * F0)
    + (63 / 1024 * beta : k) • (A ^ 2 * D0)
    + (15 / 128 * gamma : k) • (A ^ 2 * C0)
    + (165 / 1024 * delta : k) • (A ^ 2 * B)
    + (1 / 16 * epsilon : k) • A ^ 3
    + (5 / 16 : k) • (D0 * F0)
    + (9 / 64 * l : k) • (D0 * E0)
    + (5 / 16 : k) • (C0 * G0)
    + (9 / 64 * l : k) • (C0 * F0)
    - (7 / 64 * beta : k) • (C0 * D0)
    - (3 / 32 * gamma : k) • C0 ^ 2
    + (9 / 64 * l : k) • (B * G0)
    - (7 / 64 * beta : k) • (B * E0)
    - (3 / 16 * gamma : k) • (B * D0)
    - (15 / 64 * delta : k) • (B * C0)
    - (1 / 8 * epsilon : k) • B ^ 2
    - (7 / 64 * beta : k) • (A * F0)
    - (3 / 16 * gamma : k) • (A * E0)
    - (15 / 64 * delta : k) • (A * D0)
    - (1 / 4 * epsilon : k) • (A * C0)
    - (15 / 64 * zeta : k) • (A * B)
    - (3 / 32 * eta : k) • A ^ 2
    + (3 / 4 * gamma : k) • G0
    + (5 / 8 * delta : k) • F0
    + (1 / 2 * epsilon : k) • E0
    + (3 / 8 * zeta : k) • D0
    + (1 / 4 * eta : k) • C0
    + (1 / 8 * theta : k) • B

set_option maxHeartbeats 8000000 in
/-- `μ` without the three `B`–`E₀` tie monomials. -/
def degreeZeroMuNoBE02Polynomial810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  (385 / 65536 : k) • A ^ 6
    - (385 / 4096 : k) • (A ^ 3 * B ^ 2)
    - (385 / 8192 : k) • (A ^ 4 * C0)
    - (7245 / 262144 * l : k) • (A ^ 4 * B)
    + (105 / 512 : k) • (A * B ^ 2 * C0)
    + (315 / 8192 * l : k) • (A * B ^ 3)
    + (105 / 1024 : k) • (A ^ 2 * C0 ^ 2)
    + (105 / 512 : k) • (A ^ 2 * B * D0)
    + (945 / 8192 * l : k) • (A ^ 2 * B * C0)
    + (35 / 512 : k) • (A ^ 3 * E0)
    + (315 / 8192 * l : k) • (A ^ 3 * D0)
    - (357 / 8192 * beta : k) • (A ^ 3 * B)
    - (45 / 2048 * gamma : k) • A ^ 4
    - (5 / 128 : k) • C0 ^ 3
    - (15 / 64 : k) • (B * C0 * D0)
    - (63 / 1024 * l : k) • (B * C0 ^ 2)
    - (63 / 1024 * l : k) • (B ^ 2 * D0)
    + (21 / 1024 * beta : k) • B ^ 3
    - (15 / 128 : k) • (A * D0 ^ 2)
    - (15 / 64 : k) • (A * C0 * E0)
    - (63 / 512 * l : k) • (A * C0 * D0)
    - (15 / 64 : k) • (A * B * F0)
    - (63 / 512 * l : k) • (A * B * E0)
    + (63 / 512 * beta : k) • (A * B * C0)
    + (15 / 128 * gamma : k) • (A * B ^ 2)
    - (15 / 128 : k) • (A ^ 2 * G0)
    - (63 / 1024 * l : k) • (A ^ 2 * F0)
    + (63 / 1024 * beta : k) • (A ^ 2 * D0)
    + (15 / 128 * gamma : k) • (A ^ 2 * C0)
    + (165 / 1024 * delta : k) • (A ^ 2 * B)
    + (1 / 16 * epsilon : k) • A ^ 3
    + (5 / 16 : k) • (D0 * F0)
    + (9 / 64 * l : k) • (D0 * E0)
    + (5 / 16 : k) • (C0 * G0)
    + (9 / 64 * l : k) • (C0 * F0)
    - (7 / 64 * beta : k) • (C0 * D0)
    - (3 / 32 * gamma : k) • C0 ^ 2
    + (9 / 64 * l : k) • (B * G0)
    - (7 / 64 * beta : k) • (B * E0)
    - (3 / 16 * gamma : k) • (B * D0)
    - (15 / 64 * delta : k) • (B * C0)
    - (1 / 8 * epsilon : k) • B ^ 2
    - (7 / 64 * beta : k) • (A * F0)
    - (3 / 16 * gamma : k) • (A * E0)
    - (15 / 64 * delta : k) • (A * D0)
    - (1 / 4 * epsilon : k) • (A * C0)
    - (15 / 64 * zeta : k) • (A * B)
    - (3 / 32 * eta : k) • A ^ 2
    + (3 / 4 * gamma : k) • G0
    + (5 / 8 * delta : k) • F0
    + (1 / 2 * epsilon : k) • E0
    + (3 / 8 * zeta : k) • D0
    + (1 / 4 * eta : k) • C0
    + (1 / 8 * theta : k) • B

set_option maxHeartbeats 8000000 in
/-- `μ` without the `A⁶` / `A D₀²` tie monomials. -/
def degreeZeroMuNoAD05Polynomial810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  - (385 / 4096 : k) • (A ^ 3 * B ^ 2)
    - (385 / 8192 : k) • (A ^ 4 * C0)
    - (7245 / 262144 * l : k) • (A ^ 4 * B)
    + (35 / 2048 : k) • B ^ 4
    + (105 / 512 : k) • (A * B ^ 2 * C0)
    + (315 / 8192 * l : k) • (A * B ^ 3)
    + (105 / 1024 : k) • (A ^ 2 * C0 ^ 2)
    + (105 / 512 : k) • (A ^ 2 * B * D0)
    + (945 / 8192 * l : k) • (A ^ 2 * B * C0)
    + (35 / 512 : k) • (A ^ 3 * E0)
    + (315 / 8192 * l : k) • (A ^ 3 * D0)
    - (357 / 8192 * beta : k) • (A ^ 3 * B)
    - (45 / 2048 * gamma : k) • A ^ 4
    - (5 / 128 : k) • C0 ^ 3
    - (15 / 64 : k) • (B * C0 * D0)
    - (63 / 1024 * l : k) • (B * C0 ^ 2)
    - (15 / 128 : k) • (B ^ 2 * E0)
    - (63 / 1024 * l : k) • (B ^ 2 * D0)
    + (21 / 1024 * beta : k) • B ^ 3
    - (15 / 64 : k) • (A * C0 * E0)
    - (63 / 512 * l : k) • (A * C0 * D0)
    - (15 / 64 : k) • (A * B * F0)
    - (63 / 512 * l : k) • (A * B * E0)
    + (63 / 512 * beta : k) • (A * B * C0)
    + (15 / 128 * gamma : k) • (A * B ^ 2)
    - (15 / 128 : k) • (A ^ 2 * G0)
    - (63 / 1024 * l : k) • (A ^ 2 * F0)
    + (63 / 1024 * beta : k) • (A ^ 2 * D0)
    + (15 / 128 * gamma : k) • (A ^ 2 * C0)
    + (165 / 1024 * delta : k) • (A ^ 2 * B)
    + (1 / 16 * epsilon : k) • A ^ 3
    + (5 / 32 : k) • E0 ^ 2
    + (5 / 16 : k) • (D0 * F0)
    + (9 / 64 * l : k) • (D0 * E0)
    + (5 / 16 : k) • (C0 * G0)
    + (9 / 64 * l : k) • (C0 * F0)
    - (7 / 64 * beta : k) • (C0 * D0)
    - (3 / 32 * gamma : k) • C0 ^ 2
    + (9 / 64 * l : k) • (B * G0)
    - (7 / 64 * beta : k) • (B * E0)
    - (3 / 16 * gamma : k) • (B * D0)
    - (15 / 64 * delta : k) • (B * C0)
    - (1 / 8 * epsilon : k) • B ^ 2
    - (7 / 64 * beta : k) • (A * F0)
    - (3 / 16 * gamma : k) • (A * E0)
    - (15 / 64 * delta : k) • (A * D0)
    - (1 / 4 * epsilon : k) • (A * C0)
    - (15 / 64 * zeta : k) • (A * B)
    - (3 / 32 * eta : k) • A ^ 2
    + (3 / 4 * gamma : k) • G0
    + (5 / 8 * delta : k) • F0
    + (1 / 2 * epsilon : k) • E0
    + (3 / 8 * zeta : k) • D0
    + (1 / 4 * eta : k) • C0
    + (1 / 8 * theta : k) • B

set_option maxHeartbeats 8000000 in
/-- `ξ` without the four `A`–`C₀` tie monomials. -/
def degreeZeroXiNoAC02Polynomial810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  (1925 / 32768 : k) • (A ^ 4 * B ^ 2)
    + (7245 / 524288 * l : k) • (A ^ 5 * B)
    - (35 / 1024 : k) • (A * B ^ 4)
    - (105 / 512 : k) • (A ^ 2 * B ^ 2 * C0)
    - (315 / 8192 * l : k) • (A ^ 2 * B ^ 3)
    - (525 / 4096 : k) • (A ^ 3 * B * D0)
    - (315 / 4096 * l : k) • (A ^ 3 * B * C0)
    - (245 / 8192 : k) • (A ^ 4 * E0)
    - (4725 / 262144 * l : k) • (A ^ 4 * D0)
    + (357 / 16384 * beta : k) • (A ^ 4 * B)
    + (9 / 1024 * gamma : k) • A ^ 5
    + (45 / 512 : k) • (B ^ 2 * C0 ^ 2)
    + (55 / 1024 : k) • (B ^ 3 * D0)
    + (63 / 2048 * l : k) • (B ^ 3 * C0)
    + (165 / 512 : k) • (A * B * C0 * D0)
    + (189 / 2048 * l : k) • (A * B * C0 ^ 2)
    + (75 / 512 : k) • (A * B ^ 2 * E0)
    + (693 / 8192 * l : k) • (A * B ^ 2 * D0)
    - (63 / 2048 * beta : k) • (A * B ^ 3)
    + (75 / 1024 : k) • (A ^ 2 * D0 ^ 2)
    + (75 / 512 : k) • (A ^ 2 * C0 * E0)
    + (693 / 8192 * l : k) • (A ^ 2 * C0 * D0)
    + (135 / 1024 : k) • (A ^ 2 * B * F0)
    + (315 / 4096 * l : k) • (A ^ 2 * B * E0)
    - (189 / 2048 * beta : k) • (A ^ 2 * B * C0)
    - (45 / 512 * gamma : k) • (A ^ 2 * B ^ 2)
    + (5 / 128 : k) • (A ^ 3 * G0)
    + (189 / 8192 * l : k) • (A ^ 3 * F0)
    - (231 / 8192 * beta : k) • (A ^ 3 * D0)
    - (15 / 256 * gamma : k) • (A ^ 3 * C0)
    - (165 / 2048 * delta : k) • (A ^ 3 * B)
    - (3 / 128 * epsilon : k) • A ^ 4
    - (15 / 128 : k) • (C0 * D0 ^ 2)
    - (15 / 128 : k) • (C0 ^ 2 * E0)
    - (63 / 1024 * l : k) • (C0 ^ 2 * D0)
    - (25 / 128 : k) • (B * D0 * E0)
    - (27 / 512 * l : k) • (B * D0 ^ 2)
    - (25 / 128 : k) • (B * C0 * F0)
    - (27 / 256 * l : k) • (B * C0 * E0)
    + (7 / 128 * beta : k) • (B * C0 ^ 2)
    - (5 / 64 : k) • (B ^ 2 * G0)
    - (45 / 1024 * l : k) • (B ^ 2 * F0)
    + (49 / 1024 * beta : k) • (B ^ 2 * D0)
    + (3 / 32 * gamma : k) • (B ^ 2 * C0)
    + (5 / 128 * delta : k) • B ^ 3
    - (5 / 64 : k) • (A * E0 ^ 2)
    - (5 / 32 : k) • (A * D0 * F0)
    - (45 / 512 * l : k) • (A * D0 * E0)
    - (5 / 32 : k) • (A * C0 * G0)
    - (45 / 512 * l : k) • (A * C0 * F0)
    + (49 / 512 * beta : k) • (A * C0 * D0)
    + (3 / 32 * gamma : k) • (A * C0 ^ 2)
    - (9 / 128 * l : k) • (A * B * G0)
    + (21 / 256 * beta : k) • (A * B * E0)
    + (21 / 128 * gamma : k) • (A * B * D0)
    + (15 / 64 * delta : k) • (A * B * C0)
    + (1 / 8 * epsilon : k) • (A * B ^ 2)
    + (35 / 1024 * beta : k) • (A ^ 2 * F0)
    + (9 / 128 * gamma : k) • (A ^ 2 * E0)
    + (105 / 1024 * delta : k) • (A ^ 2 * D0)
    + (1 / 8 * epsilon : k) • (A ^ 2 * C0)
    + (15 / 128 * zeta : k) • (A ^ 2 * B)
    + (1 / 32 * eta : k) • A ^ 3
    + (5 / 32 : k) • F0 ^ 2
    + (5 / 16 : k) • (E0 * G0)
    + (9 / 64 * l : k) • (E0 * F0)
    + (9 / 64 * l : k) • (D0 * G0)
    - (7 / 64 * beta : k) • (D0 * E0)
    - (3 / 32 * gamma : k) • D0 ^ 2
    - (7 / 64 * beta : k) • (C0 * F0)
    - (3 / 16 * gamma : k) • (C0 * E0)
    - (15 / 64 * delta : k) • (C0 * D0)
    - (1 / 8 * epsilon : k) • C0 ^ 2
    - (3 / 32 * gamma : k) • (B * F0)
    - (5 / 32 * delta : k) • (B * E0)
    - (3 / 16 * epsilon : k) • (B * D0)
    - (3 / 16 * zeta : k) • (B * C0)
    - (1 / 16 * eta : k) • B ^ 2
    - (5 / 64 * delta : k) • (A * F0)
    - (1 / 8 * epsilon : k) • (A * E0)
    - (9 / 64 * zeta : k) • (A * D0)
    - (1 / 8 * eta : k) • (A * C0)
    - (1 / 16 * theta : k) • (A * B)
    + (1 / 2 * epsilon : k) • G0
    + (3 / 8 * zeta : k) • F0
    + (1 / 4 * eta : k) • E0
    + (1 / 8 * theta : k) • D0

set_option maxHeartbeats 8000000 in
/-- `ξ` without the three `A`–`E₀` Newton-tie monomials. -/
def degreeZeroXiNoAE06Polynomial810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  (1925 / 32768 : k) • (A ^ 4 * B ^ 2)
    + (385 / 16384 : k) • (A ^ 5 * C0)
    + (7245 / 524288 * l : k) • (A ^ 5 * B)
    - (35 / 1024 : k) • (A * B ^ 4)
    - (105 / 512 : k) • (A ^ 2 * B ^ 2 * C0)
    - (315 / 8192 * l : k) • (A ^ 2 * B ^ 3)
    - (35 / 512 : k) • (A ^ 3 * C0 ^ 2)
    - (525 / 4096 : k) • (A ^ 3 * B * D0)
    - (315 / 4096 * l : k) • (A ^ 3 * B * C0)
    - (4725 / 262144 * l : k) • (A ^ 4 * D0)
    + (357 / 16384 * beta : k) • (A ^ 4 * B)
    + (9 / 1024 * gamma : k) • A ^ 5
    + (45 / 512 : k) • (B ^ 2 * C0 ^ 2)
    + (55 / 1024 : k) • (B ^ 3 * D0)
    + (63 / 2048 * l : k) • (B ^ 3 * C0)
    + (15 / 256 : k) • (A * C0 ^ 3)
    + (165 / 512 : k) • (A * B * C0 * D0)
    + (189 / 2048 * l : k) • (A * B * C0 ^ 2)
    + (75 / 512 : k) • (A * B ^ 2 * E0)
    + (693 / 8192 * l : k) • (A * B ^ 2 * D0)
    - (63 / 2048 * beta : k) • (A * B ^ 3)
    + (75 / 1024 : k) • (A ^ 2 * D0 ^ 2)
    + (75 / 512 : k) • (A ^ 2 * C0 * E0)
    + (693 / 8192 * l : k) • (A ^ 2 * C0 * D0)
    + (135 / 1024 : k) • (A ^ 2 * B * F0)
    + (315 / 4096 * l : k) • (A ^ 2 * B * E0)
    - (189 / 2048 * beta : k) • (A ^ 2 * B * C0)
    - (45 / 512 * gamma : k) • (A ^ 2 * B ^ 2)
    + (5 / 128 : k) • (A ^ 3 * G0)
    + (189 / 8192 * l : k) • (A ^ 3 * F0)
    - (231 / 8192 * beta : k) • (A ^ 3 * D0)
    - (15 / 256 * gamma : k) • (A ^ 3 * C0)
    - (165 / 2048 * delta : k) • (A ^ 3 * B)
    - (3 / 128 * epsilon : k) • A ^ 4
    - (15 / 128 : k) • (C0 * D0 ^ 2)
    - (15 / 128 : k) • (C0 ^ 2 * E0)
    - (63 / 1024 * l : k) • (C0 ^ 2 * D0)
    - (25 / 128 : k) • (B * D0 * E0)
    - (27 / 512 * l : k) • (B * D0 ^ 2)
    - (25 / 128 : k) • (B * C0 * F0)
    - (27 / 256 * l : k) • (B * C0 * E0)
    + (7 / 128 * beta : k) • (B * C0 ^ 2)
    - (5 / 64 : k) • (B ^ 2 * G0)
    - (45 / 1024 * l : k) • (B ^ 2 * F0)
    + (49 / 1024 * beta : k) • (B ^ 2 * D0)
    + (3 / 32 * gamma : k) • (B ^ 2 * C0)
    + (5 / 128 * delta : k) • B ^ 3
    - (5 / 32 : k) • (A * D0 * F0)
    - (45 / 512 * l : k) • (A * D0 * E0)
    - (5 / 32 : k) • (A * C0 * G0)
    - (45 / 512 * l : k) • (A * C0 * F0)
    + (49 / 512 * beta : k) • (A * C0 * D0)
    + (3 / 32 * gamma : k) • (A * C0 ^ 2)
    - (9 / 128 * l : k) • (A * B * G0)
    + (21 / 256 * beta : k) • (A * B * E0)
    + (21 / 128 * gamma : k) • (A * B * D0)
    + (15 / 64 * delta : k) • (A * B * C0)
    + (1 / 8 * epsilon : k) • (A * B ^ 2)
    + (35 / 1024 * beta : k) • (A ^ 2 * F0)
    + (9 / 128 * gamma : k) • (A ^ 2 * E0)
    + (105 / 1024 * delta : k) • (A ^ 2 * D0)
    + (1 / 8 * epsilon : k) • (A ^ 2 * C0)
    + (15 / 128 * zeta : k) • (A ^ 2 * B)
    + (1 / 32 * eta : k) • A ^ 3
    + (5 / 32 : k) • F0 ^ 2
    + (5 / 16 : k) • (E0 * G0)
    + (9 / 64 * l : k) • (E0 * F0)
    + (9 / 64 * l : k) • (D0 * G0)
    - (7 / 64 * beta : k) • (D0 * E0)
    - (3 / 32 * gamma : k) • D0 ^ 2
    - (7 / 64 * beta : k) • (C0 * F0)
    - (3 / 16 * gamma : k) • (C0 * E0)
    - (15 / 64 * delta : k) • (C0 * D0)
    - (1 / 8 * epsilon : k) • C0 ^ 2
    - (3 / 32 * gamma : k) • (B * F0)
    - (5 / 32 * delta : k) • (B * E0)
    - (3 / 16 * epsilon : k) • (B * D0)
    - (3 / 16 * zeta : k) • (B * C0)
    - (1 / 16 * eta : k) • B ^ 2
    - (5 / 64 * delta : k) • (A * F0)
    - (1 / 8 * epsilon : k) • (A * E0)
    - (9 / 64 * zeta : k) • (A * D0)
    - (1 / 8 * eta : k) • (A * C0)
    - (1 / 16 * theta : k) • (A * B)
    + (1 / 2 * epsilon : k) • G0
    + (3 / 8 * zeta : k) • F0
    + (1 / 4 * eta : k) • E0
    + (1 / 8 * theta : k) • D0

set_option maxHeartbeats 8000000 in
/-- `ξ` without the `A⁷` / `A² D₀²` tie monomials. -/
def degreeZeroXiNoAD05Polynomial810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  (1925 / 32768 : k) • (A ^ 4 * B ^ 2)
    + (385 / 16384 : k) • (A ^ 5 * C0)
    + (7245 / 524288 * l : k) • (A ^ 5 * B)
    - (35 / 1024 : k) • (A * B ^ 4)
    - (105 / 512 : k) • (A ^ 2 * B ^ 2 * C0)
    - (315 / 8192 * l : k) • (A ^ 2 * B ^ 3)
    - (35 / 512 : k) • (A ^ 3 * C0 ^ 2)
    - (525 / 4096 : k) • (A ^ 3 * B * D0)
    - (315 / 4096 * l : k) • (A ^ 3 * B * C0)
    - (245 / 8192 : k) • (A ^ 4 * E0)
    - (4725 / 262144 * l : k) • (A ^ 4 * D0)
    + (357 / 16384 * beta : k) • (A ^ 4 * B)
    + (9 / 1024 * gamma : k) • A ^ 5
    + (45 / 512 : k) • (B ^ 2 * C0 ^ 2)
    + (55 / 1024 : k) • (B ^ 3 * D0)
    + (63 / 2048 * l : k) • (B ^ 3 * C0)
    + (15 / 256 : k) • (A * C0 ^ 3)
    + (165 / 512 : k) • (A * B * C0 * D0)
    + (189 / 2048 * l : k) • (A * B * C0 ^ 2)
    + (75 / 512 : k) • (A * B ^ 2 * E0)
    + (693 / 8192 * l : k) • (A * B ^ 2 * D0)
    - (63 / 2048 * beta : k) • (A * B ^ 3)
    + (75 / 512 : k) • (A ^ 2 * C0 * E0)
    + (693 / 8192 * l : k) • (A ^ 2 * C0 * D0)
    + (135 / 1024 : k) • (A ^ 2 * B * F0)
    + (315 / 4096 * l : k) • (A ^ 2 * B * E0)
    - (189 / 2048 * beta : k) • (A ^ 2 * B * C0)
    - (45 / 512 * gamma : k) • (A ^ 2 * B ^ 2)
    + (5 / 128 : k) • (A ^ 3 * G0)
    + (189 / 8192 * l : k) • (A ^ 3 * F0)
    - (231 / 8192 * beta : k) • (A ^ 3 * D0)
    - (15 / 256 * gamma : k) • (A ^ 3 * C0)
    - (165 / 2048 * delta : k) • (A ^ 3 * B)
    - (3 / 128 * epsilon : k) • A ^ 4
    - (15 / 128 : k) • (C0 * D0 ^ 2)
    - (15 / 128 : k) • (C0 ^ 2 * E0)
    - (63 / 1024 * l : k) • (C0 ^ 2 * D0)
    - (25 / 128 : k) • (B * D0 * E0)
    - (27 / 512 * l : k) • (B * D0 ^ 2)
    - (25 / 128 : k) • (B * C0 * F0)
    - (27 / 256 * l : k) • (B * C0 * E0)
    + (7 / 128 * beta : k) • (B * C0 ^ 2)
    - (5 / 64 : k) • (B ^ 2 * G0)
    - (45 / 1024 * l : k) • (B ^ 2 * F0)
    + (49 / 1024 * beta : k) • (B ^ 2 * D0)
    + (3 / 32 * gamma : k) • (B ^ 2 * C0)
    + (5 / 128 * delta : k) • B ^ 3
    - (5 / 64 : k) • (A * E0 ^ 2)
    - (5 / 32 : k) • (A * D0 * F0)
    - (45 / 512 * l : k) • (A * D0 * E0)
    - (5 / 32 : k) • (A * C0 * G0)
    - (45 / 512 * l : k) • (A * C0 * F0)
    + (49 / 512 * beta : k) • (A * C0 * D0)
    + (3 / 32 * gamma : k) • (A * C0 ^ 2)
    - (9 / 128 * l : k) • (A * B * G0)
    + (21 / 256 * beta : k) • (A * B * E0)
    + (21 / 128 * gamma : k) • (A * B * D0)
    + (15 / 64 * delta : k) • (A * B * C0)
    + (1 / 8 * epsilon : k) • (A * B ^ 2)
    + (35 / 1024 * beta : k) • (A ^ 2 * F0)
    + (9 / 128 * gamma : k) • (A ^ 2 * E0)
    + (105 / 1024 * delta : k) • (A ^ 2 * D0)
    + (1 / 8 * epsilon : k) • (A ^ 2 * C0)
    + (15 / 128 * zeta : k) • (A ^ 2 * B)
    + (1 / 32 * eta : k) • A ^ 3
    + (5 / 32 : k) • F0 ^ 2
    + (5 / 16 : k) • (E0 * G0)
    + (9 / 64 * l : k) • (E0 * F0)
    + (9 / 64 * l : k) • (D0 * G0)
    - (7 / 64 * beta : k) • (D0 * E0)
    - (3 / 32 * gamma : k) • D0 ^ 2
    - (7 / 64 * beta : k) • (C0 * F0)
    - (3 / 16 * gamma : k) • (C0 * E0)
    - (15 / 64 * delta : k) • (C0 * D0)
    - (1 / 8 * epsilon : k) • C0 ^ 2
    - (3 / 32 * gamma : k) • (B * F0)
    - (5 / 32 * delta : k) • (B * E0)
    - (3 / 16 * epsilon : k) • (B * D0)
    - (3 / 16 * zeta : k) • (B * C0)
    - (1 / 16 * eta : k) • B ^ 2
    - (5 / 64 * delta : k) • (A * F0)
    - (1 / 8 * epsilon : k) • (A * E0)
    - (9 / 64 * zeta : k) • (A * D0)
    - (1 / 8 * eta : k) • (A * C0)
    - (1 / 16 * theta : k) • (A * B)
    + (1 / 2 * epsilon : k) • G0
    + (3 / 8 * zeta : k) • F0
    + (1 / 4 * eta : k) • E0
    + (1 / 8 * theta : k) • D0

set_option maxHeartbeats 8000000 in
/-- `ξ` without the unique `C₀² E₀` monomial. -/
def degreeZeroXiNoC0E0Polynomial810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(165 / 65536 : k) • A ^ 7
    + (1925 / 32768 : k) • (A ^ 4 * B ^ 2)
    + (385 / 16384 : k) • (A ^ 5 * C0)
    + (7245 / 524288 * l : k) • (A ^ 5 * B)
    - (35 / 1024 : k) • (A * B ^ 4)
    - (105 / 512 : k) • (A ^ 2 * B ^ 2 * C0)
    - (315 / 8192 * l : k) • (A ^ 2 * B ^ 3)
    - (35 / 512 : k) • (A ^ 3 * C0 ^ 2)
    - (525 / 4096 : k) • (A ^ 3 * B * D0)
    - (315 / 4096 * l : k) • (A ^ 3 * B * C0)
    - (245 / 8192 : k) • (A ^ 4 * E0)
    - (4725 / 262144 * l : k) • (A ^ 4 * D0)
    + (357 / 16384 * beta : k) • (A ^ 4 * B)
    + (9 / 1024 * gamma : k) • A ^ 5
    + (45 / 512 : k) • (B ^ 2 * C0 ^ 2)
    + (55 / 1024 : k) • (B ^ 3 * D0)
    + (63 / 2048 * l : k) • (B ^ 3 * C0)
    + (15 / 256 : k) • (A * C0 ^ 3)
    + (165 / 512 : k) • (A * B * C0 * D0)
    + (189 / 2048 * l : k) • (A * B * C0 ^ 2)
    + (75 / 512 : k) • (A * B ^ 2 * E0)
    + (693 / 8192 * l : k) • (A * B ^ 2 * D0)
    - (63 / 2048 * beta : k) • (A * B ^ 3)
    + (75 / 1024 : k) • (A ^ 2 * D0 ^ 2)
    + (75 / 512 : k) • (A ^ 2 * C0 * E0)
    + (693 / 8192 * l : k) • (A ^ 2 * C0 * D0)
    + (135 / 1024 : k) • (A ^ 2 * B * F0)
    + (315 / 4096 * l : k) • (A ^ 2 * B * E0)
    - (189 / 2048 * beta : k) • (A ^ 2 * B * C0)
    - (45 / 512 * gamma : k) • (A ^ 2 * B ^ 2)
    + (5 / 128 : k) • (A ^ 3 * G0)
    + (189 / 8192 * l : k) • (A ^ 3 * F0)
    - (231 / 8192 * beta : k) • (A ^ 3 * D0)
    - (15 / 256 * gamma : k) • (A ^ 3 * C0)
    - (165 / 2048 * delta : k) • (A ^ 3 * B)
    - (3 / 128 * epsilon : k) • A ^ 4
    - (15 / 128 : k) • (C0 * D0 ^ 2)
    - (63 / 1024 * l : k) • (C0 ^ 2 * D0)
    - (25 / 128 : k) • (B * D0 * E0)
    - (27 / 512 * l : k) • (B * D0 ^ 2)
    - (25 / 128 : k) • (B * C0 * F0)
    - (27 / 256 * l : k) • (B * C0 * E0)
    + (7 / 128 * beta : k) • (B * C0 ^ 2)
    - (5 / 64 : k) • (B ^ 2 * G0)
    - (45 / 1024 * l : k) • (B ^ 2 * F0)
    + (49 / 1024 * beta : k) • (B ^ 2 * D0)
    + (3 / 32 * gamma : k) • (B ^ 2 * C0)
    + (5 / 128 * delta : k) • B ^ 3
    - (5 / 64 : k) • (A * E0 ^ 2)
    - (5 / 32 : k) • (A * D0 * F0)
    - (45 / 512 * l : k) • (A * D0 * E0)
    - (5 / 32 : k) • (A * C0 * G0)
    - (45 / 512 * l : k) • (A * C0 * F0)
    + (49 / 512 * beta : k) • (A * C0 * D0)
    + (3 / 32 * gamma : k) • (A * C0 ^ 2)
    - (9 / 128 * l : k) • (A * B * G0)
    + (21 / 256 * beta : k) • (A * B * E0)
    + (21 / 128 * gamma : k) • (A * B * D0)
    + (15 / 64 * delta : k) • (A * B * C0)
    + (1 / 8 * epsilon : k) • (A * B ^ 2)
    + (35 / 1024 * beta : k) • (A ^ 2 * F0)
    + (9 / 128 * gamma : k) • (A ^ 2 * E0)
    + (105 / 1024 * delta : k) • (A ^ 2 * D0)
    + (1 / 8 * epsilon : k) • (A ^ 2 * C0)
    + (15 / 128 * zeta : k) • (A ^ 2 * B)
    + (1 / 32 * eta : k) • A ^ 3
    + (5 / 32 : k) • F0 ^ 2
    + (5 / 16 : k) • (E0 * G0)
    + (9 / 64 * l : k) • (E0 * F0)
    + (9 / 64 * l : k) • (D0 * G0)
    - (7 / 64 * beta : k) • (D0 * E0)
    - (3 / 32 * gamma : k) • D0 ^ 2
    - (7 / 64 * beta : k) • (C0 * F0)
    - (3 / 16 * gamma : k) • (C0 * E0)
    - (15 / 64 * delta : k) • (C0 * D0)
    - (1 / 8 * epsilon : k) • C0 ^ 2
    - (3 / 32 * gamma : k) • (B * F0)
    - (5 / 32 * delta : k) • (B * E0)
    - (3 / 16 * epsilon : k) • (B * D0)
    - (3 / 16 * zeta : k) • (B * C0)
    - (1 / 16 * eta : k) • B ^ 2
    - (5 / 64 * delta : k) • (A * F0)
    - (1 / 8 * epsilon : k) • (A * E0)
    - (9 / 64 * zeta : k) • (A * D0)
    - (1 / 8 * eta : k) • (A * C0)
    - (1 / 16 * theta : k) • (A * B)
    + (1 / 2 * epsilon : k) • G0
    + (3 / 8 * zeta : k) • F0
    + (1 / 4 * eta : k) • E0
    + (1 / 8 * theta : k) • D0

set_option maxHeartbeats 8000000 in
/-- `ο` without the three `B`–`E₀` tie monomials. -/
def degreeZeroOmicronNoBE02Polynomial810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(12705 / 1048576 : k) • (A ^ 6 * B)
    - (34155 / 33554432 * l : k) • A ^ 7
    + (3745 / 65536 : k) • (A ^ 3 * B ^ 3)
    + (1365 / 16384 : k) • (A ^ 4 * B * C0)
    + (103005 / 4194304 * l : k) • (A ^ 4 * B ^ 2)
    + (525 / 32768 : k) • (A ^ 5 * D0)
    + (19845 / 2097152 * l : k) • (A ^ 5 * C0)
    - (3927 / 2097152 * beta : k) • A ^ 6
    - (105 / 1024 : k) • (A * B ^ 3 * C0)
    - (945 / 65536 * l : k) • (A * B ^ 4)
    - (2475 / 16384 : k) • (A ^ 2 * B * C0 ^ 2)
    - (2475 / 16384 : k) • (A ^ 2 * B ^ 2 * D0)
    - (11151 / 131072 * l : k) • (A ^ 2 * B ^ 2 * C0)
    - (795 / 8192 : k) • (A ^ 3 * C0 * D0)
    - (3591 / 131072 * l : k) • (A ^ 3 * C0 ^ 2)
    - (725 / 8192 : k) • (A ^ 3 * B * E0)
    - (3591 / 65536 * l : k) • (A ^ 3 * B * D0)
    + (4095 / 131072 * beta : k) • (A ^ 3 * B ^ 2)
    - (305 / 16384 : k) • (A ^ 4 * F0)
    - (3087 / 262144 * l : k) • (A ^ 4 * E0)
    + (1953 / 131072 * beta : k) • (A ^ 4 * C0)
    + (495 / 16384 * gamma : k) • (A ^ 4 * B)
    + (1089 / 131072 * delta : k) • A ^ 5
    + (45 / 1024 : k) • (B * C0 ^ 3)
    + (135 / 1024 : k) • (B ^ 2 * C0 * D0)
    + (567 / 16384 * l : k) • (B ^ 2 * C0 ^ 2)
    + (189 / 8192 * l : k) • (B ^ 3 * D0)
    - (189 / 32768 * beta : k) • B ^ 4
    + (135 / 1024 : k) • (A * C0 ^ 2 * D0)
    + (189 / 8192 * l : k) • (A * C0 ^ 3)
    + (135 / 1024 : k) • (A * B * D0 ^ 2)
    + (15 / 64 : k) • (A * B * C0 * E0)
    + (567 / 4096 * l : k) • (A * B * C0 * D0)
    + (105 / 1024 : k) • (A * B ^ 2 * F0)
    + (63 / 1024 * l : k) • (A * B ^ 2 * E0)
    - (567 / 8192 * beta : k) • (A * B ^ 2 * C0)
    - (45 / 1024 * gamma : k) • (A * B ^ 3)
    + (225 / 2048 : k) • (A ^ 2 * D0 * E0)
    + (135 / 4096 * l : k) • (A ^ 2 * D0 ^ 2)
    + (195 / 2048 : k) • (A ^ 2 * C0 * F0)
    + (477 / 8192 * l : k) • (A ^ 2 * C0 * E0)
    - (273 / 8192 * beta : k) • (A ^ 2 * C0 ^ 2)
    + (165 / 2048 : k) • (A ^ 2 * B * G0)
    + (207 / 4096 * l : k) • (A ^ 2 * B * F0)
    - (273 / 4096 * beta : k) • (A ^ 2 * B * D0)
    - (261 / 2048 * gamma : k) • (A ^ 2 * B * C0)
    - (45 / 512 * delta : k) • (A ^ 2 * B ^ 2)
    + (99 / 8192 * l : k) • (A ^ 3 * G0)
    - (147 / 8192 * beta : k) • (A ^ 3 * E0)
    - (81 / 2048 * gamma : k) • (A ^ 3 * D0)
    - (225 / 4096 * delta : k) • (A ^ 3 * C0)
    - (33 / 512 * epsilon : k) • (A ^ 3 * B)
    - (495 / 32768 * zeta : k) • A ^ 4
    - (5 / 128 : k) • D0 ^ 3
    - (25 / 128 : k) • (C0 * D0 * E0)
    - (27 / 512 * l : k) • (C0 * D0 ^ 2)
    - (5 / 64 : k) • (C0 ^ 2 * F0)
    - (45 / 1024 * l : k) • (C0 ^ 2 * E0)
    + (7 / 512 * beta : k) • C0 ^ 3
    - (5 / 32 : k) • (B * D0 * F0)
    - (45 / 512 * l : k) • (B * D0 * E0)
    - (15 / 128 : k) • (B * C0 * G0)
    - (9 / 128 * l : k) • (B * C0 * F0)
    + (21 / 256 * beta : k) • (B * C0 * D0)
    + (9 / 128 * gamma : k) • (B * C0 ^ 2)
    - (27 / 1024 * l : k) • (B ^ 2 * G0)
    + (35 / 1024 * beta : k) • (B ^ 2 * E0)
    + (9 / 128 * gamma : k) • (B ^ 2 * D0)
    + (45 / 512 * delta : k) • (B ^ 2 * C0)
    + (1 / 32 * epsilon : k) • B ^ 3
    - (15 / 128 : k) • (A * E0 * F0)
    - (9 / 256 * l : k) • (A * E0 ^ 2)
    - (15 / 128 : k) • (A * D0 * G0)
    - (9 / 128 * l : k) • (A * D0 * F0)
    + (21 / 512 * beta : k) • (A * D0 ^ 2)
    - (27 / 512 * l : k) • (A * C0 * G0)
    + (35 / 512 * beta : k) • (A * C0 * E0)
    + (9 / 64 * gamma : k) • (A * C0 * D0)
    + (45 / 512 * delta : k) • (A * C0 ^ 2)
    + (7 / 128 * beta : k) • (A * B * F0)
    + (15 / 128 * gamma : k) • (A * B * E0)
    + (45 / 256 * delta : k) • (A * B * D0)
    + (3 / 16 * epsilon : k) • (A * B * C0)
    + (45 / 512 * zeta : k) • (A * B ^ 2)
    + (15 / 512 * gamma : k) • (A ^ 2 * F0)
    + (15 / 256 * delta : k) • (A ^ 2 * E0)
    + (21 / 256 * epsilon : k) • (A ^ 2 * D0)
    + (81 / 1024 * zeta : k) • (A ^ 2 * C0)
    + (33 / 512 * eta : k) • (A ^ 2 * B)
    + (11 / 1024 * theta : k) • A ^ 3
    + (5 / 16 : k) • (F0 * G0)
    + (9 / 128 * l : k) • F0 ^ 2
    + (9 / 64 * l : k) • (E0 * G0)
    - (7 / 128 * beta : k) • E0 ^ 2
    - (7 / 64 * beta : k) • (D0 * F0)
    - (3 / 16 * gamma : k) • (D0 * E0)
    - (15 / 128 * delta : k) • D0 ^ 2
    - (3 / 32 * gamma : k) • (C0 * F0)
    - (5 / 32 * delta : k) • (C0 * E0)
    - (3 / 16 * epsilon : k) • (C0 * D0)
    - (9 / 128 * zeta : k) • C0 ^ 2
    - (5 / 64 * delta : k) • (B * F0)
    - (1 / 8 * epsilon : k) • (B * E0)
    - (9 / 64 * zeta : k) • (B * D0)
    - (3 / 32 * eta : k) • (B * C0)
    - (3 / 128 * theta : k) • B ^ 2
    - (1 / 16 * epsilon : k) • (A * F0)
    - (3 / 32 * zeta : k) • (A * E0)
    - (3 / 32 * eta : k) • (A * D0)
    - (3 / 64 * theta : k) • (A * C0)
    + (3 / 8 * zeta : k) • G0
    + (1 / 4 * eta : k) • F0
    + (1 / 8 * theta : k) • E0

set_option maxHeartbeats 8000000 in
/-- `ο` without the `A⁵ D₀` / `D₀³` tie monomials. -/
def degreeZeroOmicronNoAD05Polynomial810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(12705 / 1048576 : k) • (A ^ 6 * B)
    - (34155 / 33554432 * l : k) • A ^ 7
    + (3745 / 65536 : k) • (A ^ 3 * B ^ 3)
    + (1365 / 16384 : k) • (A ^ 4 * B * C0)
    + (103005 / 4194304 * l : k) • (A ^ 4 * B ^ 2)
    + (19845 / 2097152 * l : k) • (A ^ 5 * C0)
    - (3927 / 2097152 * beta : k) • A ^ 6
    - (21 / 4096 : k) • B ^ 5
    - (105 / 1024 : k) • (A * B ^ 3 * C0)
    - (945 / 65536 * l : k) • (A * B ^ 4)
    - (2475 / 16384 : k) • (A ^ 2 * B * C0 ^ 2)
    - (2475 / 16384 : k) • (A ^ 2 * B ^ 2 * D0)
    - (11151 / 131072 * l : k) • (A ^ 2 * B ^ 2 * C0)
    - (795 / 8192 : k) • (A ^ 3 * C0 * D0)
    - (3591 / 131072 * l : k) • (A ^ 3 * C0 ^ 2)
    - (725 / 8192 : k) • (A ^ 3 * B * E0)
    - (3591 / 65536 * l : k) • (A ^ 3 * B * D0)
    + (4095 / 131072 * beta : k) • (A ^ 3 * B ^ 2)
    - (305 / 16384 : k) • (A ^ 4 * F0)
    - (3087 / 262144 * l : k) • (A ^ 4 * E0)
    + (1953 / 131072 * beta : k) • (A ^ 4 * C0)
    + (495 / 16384 * gamma : k) • (A ^ 4 * B)
    + (1089 / 131072 * delta : k) • A ^ 5
    + (45 / 1024 : k) • (B * C0 ^ 3)
    + (135 / 1024 : k) • (B ^ 2 * C0 * D0)
    + (567 / 16384 * l : k) • (B ^ 2 * C0 ^ 2)
    + (5 / 128 : k) • (B ^ 3 * E0)
    + (189 / 8192 * l : k) • (B ^ 3 * D0)
    - (189 / 32768 * beta : k) • B ^ 4
    + (135 / 1024 : k) • (A * C0 ^ 2 * D0)
    + (189 / 8192 * l : k) • (A * C0 ^ 3)
    + (135 / 1024 : k) • (A * B * D0 ^ 2)
    + (15 / 64 : k) • (A * B * C0 * E0)
    + (567 / 4096 * l : k) • (A * B * C0 * D0)
    + (105 / 1024 : k) • (A * B ^ 2 * F0)
    + (63 / 1024 * l : k) • (A * B ^ 2 * E0)
    - (567 / 8192 * beta : k) • (A * B ^ 2 * C0)
    - (45 / 1024 * gamma : k) • (A * B ^ 3)
    + (225 / 2048 : k) • (A ^ 2 * D0 * E0)
    + (135 / 4096 * l : k) • (A ^ 2 * D0 ^ 2)
    + (195 / 2048 : k) • (A ^ 2 * C0 * F0)
    + (477 / 8192 * l : k) • (A ^ 2 * C0 * E0)
    - (273 / 8192 * beta : k) • (A ^ 2 * C0 ^ 2)
    + (165 / 2048 : k) • (A ^ 2 * B * G0)
    + (207 / 4096 * l : k) • (A ^ 2 * B * F0)
    - (273 / 4096 * beta : k) • (A ^ 2 * B * D0)
    - (261 / 2048 * gamma : k) • (A ^ 2 * B * C0)
    - (45 / 512 * delta : k) • (A ^ 2 * B ^ 2)
    + (99 / 8192 * l : k) • (A ^ 3 * G0)
    - (147 / 8192 * beta : k) • (A ^ 3 * E0)
    - (81 / 2048 * gamma : k) • (A ^ 3 * D0)
    - (225 / 4096 * delta : k) • (A ^ 3 * C0)
    - (33 / 512 * epsilon : k) • (A ^ 3 * B)
    - (495 / 32768 * zeta : k) • A ^ 4
    - (25 / 128 : k) • (C0 * D0 * E0)
    - (27 / 512 * l : k) • (C0 * D0 ^ 2)
    - (5 / 64 : k) • (C0 ^ 2 * F0)
    - (45 / 1024 * l : k) • (C0 ^ 2 * E0)
    + (7 / 512 * beta : k) • C0 ^ 3
    - (5 / 64 : k) • (B * E0 ^ 2)
    - (5 / 32 : k) • (B * D0 * F0)
    - (45 / 512 * l : k) • (B * D0 * E0)
    - (15 / 128 : k) • (B * C0 * G0)
    - (9 / 128 * l : k) • (B * C0 * F0)
    + (21 / 256 * beta : k) • (B * C0 * D0)
    + (9 / 128 * gamma : k) • (B * C0 ^ 2)
    - (27 / 1024 * l : k) • (B ^ 2 * G0)
    + (35 / 1024 * beta : k) • (B ^ 2 * E0)
    + (9 / 128 * gamma : k) • (B ^ 2 * D0)
    + (45 / 512 * delta : k) • (B ^ 2 * C0)
    + (1 / 32 * epsilon : k) • B ^ 3
    - (15 / 128 : k) • (A * E0 * F0)
    - (9 / 256 * l : k) • (A * E0 ^ 2)
    - (15 / 128 : k) • (A * D0 * G0)
    - (9 / 128 * l : k) • (A * D0 * F0)
    + (21 / 512 * beta : k) • (A * D0 ^ 2)
    - (27 / 512 * l : k) • (A * C0 * G0)
    + (35 / 512 * beta : k) • (A * C0 * E0)
    + (9 / 64 * gamma : k) • (A * C0 * D0)
    + (45 / 512 * delta : k) • (A * C0 ^ 2)
    + (7 / 128 * beta : k) • (A * B * F0)
    + (15 / 128 * gamma : k) • (A * B * E0)
    + (45 / 256 * delta : k) • (A * B * D0)
    + (3 / 16 * epsilon : k) • (A * B * C0)
    + (45 / 512 * zeta : k) • (A * B ^ 2)
    + (15 / 512 * gamma : k) • (A ^ 2 * F0)
    + (15 / 256 * delta : k) • (A ^ 2 * E0)
    + (21 / 256 * epsilon : k) • (A ^ 2 * D0)
    + (81 / 1024 * zeta : k) • (A ^ 2 * C0)
    + (33 / 512 * eta : k) • (A ^ 2 * B)
    + (11 / 1024 * theta : k) • A ^ 3
    + (5 / 16 : k) • (F0 * G0)
    + (9 / 128 * l : k) • F0 ^ 2
    + (9 / 64 * l : k) • (E0 * G0)
    - (7 / 128 * beta : k) • E0 ^ 2
    - (7 / 64 * beta : k) • (D0 * F0)
    - (3 / 16 * gamma : k) • (D0 * E0)
    - (15 / 128 * delta : k) • D0 ^ 2
    - (3 / 32 * gamma : k) • (C0 * F0)
    - (5 / 32 * delta : k) • (C0 * E0)
    - (3 / 16 * epsilon : k) • (C0 * D0)
    - (9 / 128 * zeta : k) • C0 ^ 2
    - (5 / 64 * delta : k) • (B * F0)
    - (1 / 8 * epsilon : k) • (B * E0)
    - (9 / 64 * zeta : k) • (B * D0)
    - (3 / 32 * eta : k) • (B * C0)
    - (3 / 128 * theta : k) • B ^ 2
    - (1 / 16 * epsilon : k) • (A * F0)
    - (3 / 32 * zeta : k) • (A * E0)
    - (3 / 32 * eta : k) • (A * D0)
    - (3 / 64 * theta : k) • (A * C0)
    + (3 / 8 * zeta : k) • G0
    + (1 / 4 * eta : k) • F0
    + (1 / 8 * theta : k) • E0

set_option maxHeartbeats 16000000 in
theorem degreeZeroMuPolynomial810_eq_A6_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0 =
      muA6Face810 A +
        degreeZeroMuNoA6Polynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0 := by
  simp only [degreeZeroMuPolynomial810, muA6Face810,
    degreeZeroMuNoA6Polynomial810]
  module

set_option maxHeartbeats 16000000 in
theorem degreeZeroMuPolynomial810_eq_AC02_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0 =
      muAC02Combined810 A C0 +
        degreeZeroMuNoAC02Polynomial810 l beta gamma delta epsilon zeta
          eta theta A B C0 D0 E0 F0 G0 := by
  simp only [degreeZeroMuPolynomial810, muAC02Combined810,
    degreeZeroMuNoAC02Polynomial810]
  module

set_option maxHeartbeats 16000000 in
theorem degreeZeroXiPolynomial810_eq_AC02_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroXiPolynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0 =
      xiAC02Combined810 A C0 +
        degreeZeroXiNoAC02Polynomial810 l beta gamma delta epsilon zeta
          eta theta A B C0 D0 E0 F0 G0 := by
  simp only [degreeZeroXiPolynomial810, xiAC02Combined810,
    degreeZeroXiNoAC02Polynomial810]
  module

set_option maxHeartbeats 16000000 in
theorem degreeZeroMuPolynomial810_eq_AE06_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0 =
      muAE06Combined810 A E0 +
        degreeZeroMuNoAE06Polynomial810 l beta gamma delta epsilon zeta
          eta theta A B C0 D0 E0 F0 G0 := by
  simp only [degreeZeroMuPolynomial810, muAE06Combined810,
    degreeZeroMuNoAE06Polynomial810]
  module

set_option maxHeartbeats 16000000 in
theorem degreeZeroXiPolynomial810_eq_AE06_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroXiPolynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0 =
      xiAE06Combined810 A E0 +
        degreeZeroXiNoAE06Polynomial810 l beta gamma delta epsilon zeta
          eta theta A B C0 D0 E0 F0 G0 := by
  simp only [degreeZeroXiPolynomial810, xiAE06Combined810,
    degreeZeroXiNoAE06Polynomial810]
  module

set_option maxHeartbeats 16000000 in
theorem degreeZeroMuPolynomial810_eq_BE02_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0 =
      muBE02Combined810 B E0 +
        degreeZeroMuNoBE02Polynomial810 l beta gamma delta epsilon zeta
          eta theta A B C0 D0 E0 F0 G0 := by
  simp only [degreeZeroMuPolynomial810, muBE02Combined810,
    degreeZeroMuNoBE02Polynomial810]
  module

set_option maxHeartbeats 16000000 in
theorem degreeZeroOmicronPolynomial810_eq_BE02_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroOmicronPolynomial810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0 =
      omicronBE02Combined810 B E0 +
        degreeZeroOmicronNoBE02Polynomial810 l beta gamma delta epsilon
          zeta eta theta A B C0 D0 E0 F0 G0 := by
  simp only [degreeZeroOmicronPolynomial810, omicronBE02Combined810,
    degreeZeroOmicronNoBE02Polynomial810]
  module

set_option maxHeartbeats 16000000 in
theorem degreeZeroMuPolynomial810_eq_AD05_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0 =
      muAD05Combined810 A D0 +
        degreeZeroMuNoAD05Polynomial810 l beta gamma delta epsilon zeta
          eta theta A B C0 D0 E0 F0 G0 := by
  simp only [degreeZeroMuPolynomial810, muAD05Combined810,
    degreeZeroMuNoAD05Polynomial810]
  module

set_option maxHeartbeats 16000000 in
theorem degreeZeroXiPolynomial810_eq_AD05_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroXiPolynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0 =
      xiAD05Combined810 A D0 +
        degreeZeroXiNoAD05Polynomial810 l beta gamma delta epsilon zeta
          eta theta A B C0 D0 E0 F0 G0 := by
  simp only [degreeZeroXiPolynomial810, xiAD05Combined810,
    degreeZeroXiNoAD05Polynomial810]
  module

set_option maxHeartbeats 16000000 in
theorem degreeZeroXiPolynomial810_eq_C0E0_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroXiPolynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0 =
      xiC0E0Face810 C0 E0 +
        degreeZeroXiNoC0E0Polynomial810 l beta gamma delta epsilon zeta
          eta theta A B C0 D0 E0 F0 G0 := by
  simp only [degreeZeroXiPolynomial810, xiC0E0Face810,
    degreeZeroXiNoC0E0Polynomial810]
  module

end ExhaustCombined810


/-! ## Rest-degree bounds -/

section ExhaustRests810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000 in
theorem degreeZeroMuNoA6_natDegree_lt_of_mixedB
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : A6LeadsMuMixedBCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoA6Polynomial810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0).natDegree <
      6 * A.natDegree := by
  rcases hcone with ⟨hApos, hBpos, h3, hC, hD, hE, hF, hG⟩
  simp only [degreeZeroMuNoA6Polynomial810, zero_mul, mul_zero, zero_smul,
    smul_zero, zero_pow_two_ex, zero_pow_three_ex, zero_pow_four_ex,
    zero_pow_five_ex, zero_pow_six_ex, zero_pow_seven_ex, hC, hD, hE, hF,
    hG]
  compute_degree
  simp only [hC, hD, hE, hF, hG]
  have h4b : 4 * B.natDegree + 1 ≤ 6 * A.natDegree := by omega
  have h3a2b : 3 * A.natDegree + 2 * B.natDegree + 1 ≤ 6 * A.natDegree := by
    omega
  have h4ab : 4 * A.natDegree + B.natDegree + 1 ≤ 6 * A.natDegree := by omega
  have ha3b : A.natDegree + 3 * B.natDegree + 1 ≤ 6 * A.natDegree := by omega
  have h3b : 3 * B.natDegree + 1 ≤ 6 * A.natDegree := by omega
  have h2a2b : 2 * A.natDegree + 2 * B.natDegree + 1 ≤ 6 * A.natDegree := by
    omega
  omega

set_option maxHeartbeats 16000000 in
theorem degreeZeroMuNoA6_natDegree_lt_of_mixedC0
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : A6LeadsMuMixedC0Cone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoA6Polynomial810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0).natDegree <
      6 * A.natDegree := by
  rcases hcone with ⟨hApos, hCpos, hAC, h2, hB, hD, hE, hF, hG⟩
  simp only [degreeZeroMuNoA6Polynomial810, zero_mul, mul_zero, zero_smul,
    smul_zero, zero_pow_two_ex, zero_pow_three_ex, zero_pow_four_ex,
    zero_pow_five_ex, zero_pow_six_ex, zero_pow_seven_ex, hB, hD, hE, hF,
    hG]
  compute_degree
  simp only [hB, hD, hE, hF, hG]
  have h4ac : 4 * A.natDegree + C0.natDegree + 1 ≤ 6 * A.natDegree := by
    omega
  have h2a2c : 2 * A.natDegree + 2 * C0.natDegree + 1 ≤ 6 * A.natDegree := by
    omega
  have h3c : 3 * C0.natDegree + 1 ≤ 6 * A.natDegree := by omega
  omega

set_option maxHeartbeats 16000000 in
theorem degreeZeroMuNoA6_natDegree_lt_of_mixedD0
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : A6LeadsMuMixedD0Cone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoA6Polynomial810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0).natDegree <
      6 * A.natDegree := by
  rcases hcone with ⟨hApos, hDpos, h5, hB, hC, hE, hF, hG⟩
  simp only [degreeZeroMuNoA6Polynomial810, zero_mul, mul_zero, zero_smul,
    smul_zero, zero_pow_two_ex, zero_pow_three_ex, zero_pow_four_ex,
    zero_pow_five_ex, zero_pow_six_ex, zero_pow_seven_ex, hB, hC, hE, hF,
    hG]
  compute_degree
  simp only [hB, hC, hE, hF, hG]
  have had : A.natDegree + 2 * D0.natDegree + 1 ≤ 6 * A.natDegree := by
    omega
  have h3aD : 3 * A.natDegree + D0.natDegree + 1 ≤ 6 * A.natDegree := by
    omega
  omega

set_option maxHeartbeats 16000000 in
theorem degreeZeroMuNoA6_natDegree_lt_of_AE03
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : AE03RatioTieCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoA6Polynomial810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0).natDegree <
      6 * A.natDegree := by
  rcases hcone with ⟨hApos, hEpos, htie, hB, hC, hD, hF, hG⟩
  simp only [degreeZeroMuNoA6Polynomial810, zero_mul, mul_zero, zero_smul,
    smul_zero, zero_pow_two_ex, zero_pow_three_ex, zero_pow_four_ex,
    zero_pow_five_ex, zero_pow_six_ex, zero_pow_seven_ex, hB, hC, hD, hF,
    hG]
  compute_degree
  simp only [hB, hC, hD, hF, hG, htie]
  have h3ae : 3 * A.natDegree + E0.natDegree + 1 ≤ 6 * A.natDegree := by
    omega
  have h2e : 2 * E0.natDegree + 1 ≤ 6 * A.natDegree := by omega
  omega

set_option maxHeartbeats 16000000 in
theorem degreeZeroMuNoA6_natDegree_lt_of_AF07
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : AF07RatioTieCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoA6Polynomial810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0).natDegree <
      6 * A.natDegree := by
  rcases hcone with ⟨hApos, hFpos, htie, hB, hC, hD, hE, hG⟩
  simp only [degreeZeroMuNoA6Polynomial810, zero_mul, mul_zero, zero_smul,
    smul_zero, zero_pow_two_ex, zero_pow_three_ex, zero_pow_four_ex,
    zero_pow_five_ex, zero_pow_six_ex, zero_pow_seven_ex, hB, hC, hD, hE,
    hG]
  compute_degree
  simp only [hB, hC, hD, hE, hG, htie]
  have h2af : 2 * A.natDegree + F0.natDegree + 1 ≤ 6 * A.natDegree := by
    omega
  have haF : A.natDegree + F0.natDegree + 1 ≤ 6 * A.natDegree := by omega
  omega

set_option maxHeartbeats 16000000 in
theorem degreeZeroMuNoAC02_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : AC02RatioTieCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoAC02Polynomial810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0).natDegree <
      6 * A.natDegree := by
  rcases hcone with ⟨hApos, hCpos, htie, hB, hD, hE, hF, hG⟩
  simp only [degreeZeroMuNoAC02Polynomial810, zero_mul, mul_zero, zero_smul,
    smul_zero, zero_pow_two_ex, zero_pow_three_ex, zero_pow_four_ex,
    zero_pow_five_ex, zero_pow_six_ex, zero_pow_seven_ex, hB, hD, hE, hF,
    hG]
  compute_degree
  simp only [hB, hD, hE, hF, hG, htie]
  omega

set_option maxHeartbeats 16000000 in
theorem degreeZeroXiNoAC02_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : AC02RatioTieCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroXiNoAC02Polynomial810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0).natDegree <
      7 * A.natDegree := by
  rcases hcone with ⟨hApos, hCpos, htie, hB, hD, hE, hF, hG⟩
  simp only [degreeZeroXiNoAC02Polynomial810, zero_mul, mul_zero, zero_smul,
    smul_zero, zero_pow_two_ex, zero_pow_three_ex, zero_pow_four_ex,
    zero_pow_five_ex, zero_pow_six_ex, zero_pow_seven_ex, hB, hD, hE, hF,
    hG]
  compute_degree
  simp only [hB, hD, hE, hF, hG, htie]
  omega

set_option maxHeartbeats 16000000 in
theorem degreeZeroMuNoAC02_natDegree_lt_of_ABC0
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : ABC0RatioTieCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoAC02Polynomial810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0).natDegree <
      6 * A.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, htie, h4b, h5b, hD, hE, hF, hG⟩
  simp only [degreeZeroMuNoAC02Polynomial810, zero_mul, mul_zero, zero_smul,
    smul_zero, zero_pow_two_ex, zero_pow_three_ex, zero_pow_four_ex,
    zero_pow_five_ex, zero_pow_six_ex, zero_pow_seven_ex, hD, hE, hF, hG]
  compute_degree
  simp only [hD, hE, hF, hG, htie, h4b, h5b]
  have h3a2b : 3 * A.natDegree + 2 * B.natDegree + 1 ≤ 6 * A.natDegree := by
    omega
  have h4ab : 4 * A.natDegree + B.natDegree + 1 ≤ 6 * A.natDegree := by omega
  have h4b : 4 * B.natDegree + 1 ≤ 6 * A.natDegree := by omega
  have ha3b : A.natDegree + 3 * B.natDegree + 1 ≤ 6 * A.natDegree := by omega
  have h2a2b : 2 * A.natDegree + 2 * B.natDegree + 1 ≤ 6 * A.natDegree := by
    omega
  have ha2bC : A.natDegree + 2 * B.natDegree + C0.natDegree + 1 ≤
      6 * A.natDegree := by omega
  omega

set_option maxHeartbeats 16000000 in
theorem degreeZeroXiNoAC02_natDegree_lt_of_ABC0
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : ABC0RatioTieCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroXiNoAC02Polynomial810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0).natDegree <
      7 * A.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, htie, h4b, h5b, hD, hE, hF, hG⟩
  simp only [degreeZeroXiNoAC02Polynomial810, zero_mul, mul_zero, zero_smul,
    smul_zero, zero_pow_two_ex, zero_pow_three_ex, zero_pow_four_ex,
    zero_pow_five_ex, zero_pow_six_ex, zero_pow_seven_ex, hD, hE, hF, hG]
  compute_degree
  simp only [hD, hE, hF, hG, htie, h4b, h5b]
  have h4a2b : 4 * A.natDegree + 2 * B.natDegree + 1 ≤ 7 * A.natDegree := by
    omega
  have ha4b : A.natDegree + 4 * B.natDegree + 1 ≤ 7 * A.natDegree := by omega
  omega

set_option maxHeartbeats 16000000 in
theorem degreeZeroMuNoAE06_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : AE06RatioTieCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoAE06Polynomial810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0).natDegree <
      6 * A.natDegree := by
  rcases hcone with ⟨hApos, hEpos, htie, hB, hC, hD, hF, hG⟩
  simp only [degreeZeroMuNoAE06Polynomial810, zero_mul, mul_zero, zero_smul,
    smul_zero, zero_pow_two_ex, zero_pow_three_ex, zero_pow_four_ex,
    zero_pow_five_ex, zero_pow_six_ex, zero_pow_seven_ex, hB, hC, hD, hF,
    hG]
  compute_degree
  simp only [hB, hC, hD, hF, hG, htie]
  omega

set_option maxHeartbeats 16000000 in
theorem degreeZeroXiNoAE06_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : AE06RatioTieCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroXiNoAE06Polynomial810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0).natDegree <
      7 * A.natDegree := by
  rcases hcone with ⟨hApos, hEpos, htie, hB, hC, hD, hF, hG⟩
  simp only [degreeZeroXiNoAE06Polynomial810, zero_mul, mul_zero, zero_smul,
    smul_zero, zero_pow_two_ex, zero_pow_three_ex, zero_pow_four_ex,
    zero_pow_five_ex, zero_pow_six_ex, zero_pow_seven_ex, hB, hC, hD, hF,
    hG]
  compute_degree
  simp only [hB, hC, hD, hF, hG, htie]
  omega

set_option maxHeartbeats 16000000 in
theorem degreeZeroMuNoBE02_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : BE02RatioTieCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoBE02Polynomial810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0).natDegree <
      4 * B.natDegree := by
  rcases hcone with ⟨hBpos, hEpos, htie, hA, hC, hD, hF, hG⟩
  simp only [degreeZeroMuNoBE02Polynomial810, zero_mul, mul_zero, zero_smul,
    smul_zero, zero_pow_two_ex, zero_pow_three_ex, zero_pow_four_ex,
    zero_pow_five_ex, zero_pow_six_ex, zero_pow_seven_ex, hA, hC, hD, hF,
    hG]
  compute_degree
  simp only [hA, hC, hD, hF, hG, htie]
  omega

set_option maxHeartbeats 16000000 in
theorem degreeZeroOmicronNoBE02_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : BE02RatioTieCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroOmicronNoBE02Polynomial810 l beta gamma delta epsilon zeta
        eta theta A B C0 D0 E0 F0 G0).natDegree <
      5 * B.natDegree := by
  rcases hcone with ⟨hBpos, hEpos, htie, hA, hC, hD, hF, hG⟩
  simp only [degreeZeroOmicronNoBE02Polynomial810, zero_mul, mul_zero,
    zero_smul, smul_zero, zero_pow_two_ex, zero_pow_three_ex,
    zero_pow_four_ex, zero_pow_five_ex, zero_pow_six_ex, zero_pow_seven_ex,
    hA, hC, hD, hF, hG]
  compute_degree
  simp only [hA, hC, hD, hF, hG, htie]
  omega

set_option maxHeartbeats 16000000 in
theorem degreeZeroMuNoAD05_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : AD05RatioTieCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoAD05Polynomial810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0).natDegree <
      6 * A.natDegree := by
  rcases hcone with ⟨hApos, hDpos, htie, hB, hC, hE, hF, hG⟩
  simp only [degreeZeroMuNoAD05Polynomial810, zero_mul, mul_zero, zero_smul,
    smul_zero, zero_pow_two_ex, zero_pow_three_ex, zero_pow_four_ex,
    zero_pow_five_ex, zero_pow_six_ex, zero_pow_seven_ex, hB, hC, hE, hF,
    hG]
  compute_degree
  simp only [hB, hC, hE, hF, hG, htie]
  omega

set_option maxHeartbeats 16000000 in
theorem degreeZeroXiNoAD05_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : AD05RatioTieCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroXiNoAD05Polynomial810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0).natDegree <
      7 * A.natDegree := by
  rcases hcone with ⟨hApos, hDpos, htie, hB, hC, hE, hF, hG⟩
  simp only [degreeZeroXiNoAD05Polynomial810, zero_mul, mul_zero, zero_smul,
    smul_zero, zero_pow_two_ex, zero_pow_three_ex, zero_pow_four_ex,
    zero_pow_five_ex, zero_pow_six_ex, zero_pow_seven_ex, hB, hC, hE, hF,
    hG]
  compute_degree
  simp only [hB, hC, hE, hF, hG, htie]
  omega

set_option maxHeartbeats 16000000 in
theorem degreeZeroXiNoC0E0_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : C0E0RatioTieCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroXiNoC0E0Polynomial810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0).natDegree <
      2 * C0.natDegree + E0.natDegree := by
  rcases hcone with ⟨hCpos, hEpos, htie, hA, hB, hD, hF, hG⟩
  simp only [degreeZeroXiNoC0E0Polynomial810, zero_mul, mul_zero, zero_smul,
    smul_zero, zero_pow_two_ex, zero_pow_three_ex, zero_pow_four_ex,
    zero_pow_five_ex, zero_pow_six_ex, zero_pow_seven_ex, hA, hB, hD, hF,
    hG]
  compute_degree
  simp only [hA, hB, hD, hF, hG, htie]
  omega

set_option maxHeartbeats 16000000 in
theorem degreeZeroMuNoC03_natDegree_lt_of_BC03
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : BC03RatioTieCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoC03Polynomial810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0).natDegree <
      3 * C0.natDegree := by
  rcases hcone with ⟨hBpos, hCpos, htie, hA, hD, hE, hF, hG⟩
  simp only [degreeZeroMuNoC03Polynomial810, zero_mul, mul_zero, zero_smul,
    smul_zero, zero_pow_two_ex, zero_pow_three_ex, zero_pow_four_ex,
    zero_pow_five_ex, zero_pow_six_ex, zero_pow_seven_ex, hA, hD, hE, hF,
    hG]
  compute_degree
  simp only [hA, hD, hE, hF, hG, htie]
  omega

set_option maxHeartbeats 16000000 in
theorem degreeZeroMuNoB4_natDegree_lt_of_BD03
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : BD03RatioTieCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoB4Polynomial810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0).natDegree <
      4 * B.natDegree := by
  rcases hcone with ⟨hBpos, hDpos, htie, hA, hC, hE, hF, hG⟩
  simp only [degreeZeroMuNoB4Polynomial810, zero_mul, mul_zero, zero_smul,
    smul_zero, zero_pow_two_ex, zero_pow_three_ex, zero_pow_four_ex,
    zero_pow_five_ex, zero_pow_six_ex, zero_pow_seven_ex, hA, hC, hE, hF,
    hG]
  compute_degree
  simp only [hA, hC, hE, hF, hG, htie]
  omega

end ExhaustRests810


/-! ## Combined-face degrees from inner forms -/

section ExhaustCombinedDeg810

variable {k : Type*} [Field k] [CharZero k]

theorem muA6Face810_natDegree
    {A : k[X]} (hA : A ≠ 0) :
    (muA6Face810 A).natDegree = 6 * A.natDegree := by
  have hc : (385 / 65536 : k) ≠ 0 :=
    div_ne_zero (by norm_num) (by norm_num)
  simp only [muA6Face810]
  rw [natDegree_smul _ hc, natDegree_pow]

theorem muAC02Combined810_coeff (A C0 : k[X]) (n : ℕ) :
    (muAC02Combined810 A C0).coeff n =
      (385 / 65536 : k) * (A ^ 6).coeff n -
        (385 / 8192 : k) * (A ^ 4 * C0).coeff n +
          (105 / 1024 : k) * (A ^ 2 * C0 ^ 2).coeff n -
            (5 / 128 : k) * (C0 ^ 3).coeff n := by
  simp only [muAC02Combined810, coeff_add, coeff_sub, coeff_smul, smul_eq_mul]

theorem muAC02Inner810_smul_eq (r s : k) :
    (385 / 65536 : k) * r ^ 6 -
        (385 / 8192 : k) * r ^ 4 * s +
          (105 / 1024 : k) * r ^ 2 * s ^ 2 -
            (5 / 128 : k) * s ^ 3 =
      (5 / 65536 : k) * muAC02Inner810 r s := by
  simp only [muAC02Inner810]
  ring

theorem xiAC02Combined810_coeff (A C0 : k[X]) (n : ℕ) :
    (xiAC02Combined810 A C0).coeff n =
      (-(165 / 65536 : k)) * (A ^ 7).coeff n +
        (385 / 16384 : k) * (A ^ 5 * C0).coeff n -
          (35 / 512 : k) * (A ^ 3 * C0 ^ 2).coeff n +
            (15 / 256 : k) * (A * C0 ^ 3).coeff n := by
  simp only [xiAC02Combined810, coeff_add, coeff_sub, coeff_neg, coeff_smul,
    smul_eq_mul]

theorem xiAC02Inner810_smul_eq (r s : k) :
    (-(165 / 65536 : k)) * r ^ 7 +
        (385 / 16384 : k) * r ^ 5 * s -
          (35 / 512 : k) * r ^ 3 * s ^ 2 +
            (15 / 256 : k) * r * s ^ 3 =
      (-(5 / 65536 : k)) * xiAC02Inner810 r s := by
  simp only [xiAC02Inner810]
  ring

theorem muAC02_monomial_natDegree_A6 {A : k[X]} :
    (A ^ 6).natDegree = 6 * A.natDegree :=
  natDegree_pow A 6

theorem muAC02_monomial_natDegree_A4C
    {A C0 : k[X]} (hA : A ≠ 0) (hC : C0 ≠ 0)
    (htie : C0.natDegree = 2 * A.natDegree) :
    (A ^ 4 * C0).natDegree = 6 * A.natDegree := by
  rw [natDegree_mul (pow_ne_zero 4 hA) hC, natDegree_pow, htie]
  omega

theorem muAC02_monomial_natDegree_A2C2
    {A C0 : k[X]} (hA : A ≠ 0) (hC : C0 ≠ 0)
    (htie : C0.natDegree = 2 * A.natDegree) :
    (A ^ 2 * C0 ^ 2).natDegree = 6 * A.natDegree := by
  rw [natDegree_mul (pow_ne_zero 2 hA) (pow_ne_zero 2 hC),
    natDegree_pow, natDegree_pow, htie]
  omega

theorem muAC02_monomial_natDegree_C3
    {A C0 : k[X]} (htie : C0.natDegree = 2 * A.natDegree) :
    (C0 ^ 3).natDegree = 6 * A.natDegree := by
  have h1 : (C0 ^ 3).natDegree = 3 * C0.natDegree := natDegree_pow C0 3
  have h2 : 3 * C0.natDegree = 6 * A.natDegree := by omega
  exact h1.trans h2

set_option maxHeartbeats 8000000 in
theorem muAC02Combined810_natDegree_le
    {A C0 : k[X]} (hA : A ≠ 0) (hC : C0 ≠ 0)
    (htie : C0.natDegree = 2 * A.natDegree) :
    (muAC02Combined810 A C0).natDegree ≤ 6 * A.natDegree := by
  have hA6 := muAC02_monomial_natDegree_A6 (A := A)
  have hA4C := muAC02_monomial_natDegree_A4C hA hC htie
  have hA2C2 := muAC02_monomial_natDegree_A2C2 hA hC htie
  have hC3 := muAC02_monomial_natDegree_C3 (A := A) htie
  have hsmul (c : k) {p : k[X]} {n : ℕ} (hp : p.natDegree = n) :
      (c • p).natDegree ≤ n :=
    (natDegree_smul_le810 c p).trans hp.le
  rw [muAC02Combined810]
  -- `((p - q) + r) - s`
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · exact (natDegree_sub_le _ _).trans (max_le (hsmul _ hA6) (hsmul _ hA4C))
    · exact hsmul _ hA2C2
  · exact hsmul _ hC3

set_option maxHeartbeats 8000000 in
theorem muAC02Combined810_coeff_top
    {A C0 : k[X]} (hA : A ≠ 0) (hC : C0 ≠ 0)
    (htie : C0.natDegree = 2 * A.natDegree) :
    (muAC02Combined810 A C0).coeff (6 * A.natDegree) =
      (5 / 65536 : k) *
        muAC02Inner810 A.leadingCoeff C0.leadingCoeff := by
  have hA6 := muAC02_monomial_natDegree_A6 (A := A)
  have hA4C := muAC02_monomial_natDegree_A4C hA hC htie
  have hA2C2 := muAC02_monomial_natDegree_A2C2 hA hC htie
  have hC3 := muAC02_monomial_natDegree_C3 (A := A) htie
  have h1 : (A ^ 6).coeff (6 * A.natDegree) = A.leadingCoeff ^ 6 := by
    rw [← hA6, coeff_natDegree, leadingCoeff_pow]
  have h2 : (A ^ 4 * C0).coeff (6 * A.natDegree) =
      A.leadingCoeff ^ 4 * C0.leadingCoeff := by
    rw [← hA4C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have h3 : (A ^ 2 * C0 ^ 2).coeff (6 * A.natDegree) =
      A.leadingCoeff ^ 2 * C0.leadingCoeff ^ 2 := by
    rw [← hA2C2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow,
      leadingCoeff_pow]
  have h4 : (C0 ^ 3).coeff (6 * A.natDegree) = C0.leadingCoeff ^ 3 := by
    rw [← hC3, coeff_natDegree, leadingCoeff_pow]
  rw [muAC02Combined810_coeff, h1, h2, h3, h4]
  simpa [mul_assoc] using muAC02Inner810_smul_eq A.leadingCoeff C0.leadingCoeff

theorem muAC02Combined810_natDegree_eq_of_coeff_ne
    {A C0 : k[X]}
    (hA : A ≠ 0) (hC : C0 ≠ 0)
    (htie : C0.natDegree = 2 * A.natDegree)
    (hcoeff : muAC02Inner810 A.leadingCoeff C0.leadingCoeff ≠ 0) :
    (muAC02Combined810 A C0).natDegree = 6 * A.natDegree := by
  have h5 : (5 / 65536 : k) ≠ 0 :=
    div_ne_zero (by norm_num) (by norm_num)
  have hle := muAC02Combined810_natDegree_le hA hC htie
  have htop :
      (muAC02Combined810 A C0).coeff (6 * A.natDegree) ≠ 0 := by
    rw [muAC02Combined810_coeff_top hA hC htie]
    exact mul_ne_zero h5 hcoeff
  exact natDegree_eq_of_le_of_coeff_ne_zero hle htop

theorem xiAC02_monomial_natDegree_A7 {A : k[X]} :
    (A ^ 7).natDegree = 7 * A.natDegree :=
  natDegree_pow A 7

theorem xiAC02_monomial_natDegree_A5C
    {A C0 : k[X]} (hA : A ≠ 0) (hC : C0 ≠ 0)
    (htie : C0.natDegree = 2 * A.natDegree) :
    (A ^ 5 * C0).natDegree = 7 * A.natDegree := by
  rw [natDegree_mul (pow_ne_zero 5 hA) hC, natDegree_pow, htie]
  omega

theorem xiAC02_monomial_natDegree_A3C2
    {A C0 : k[X]} (hA : A ≠ 0) (hC : C0 ≠ 0)
    (htie : C0.natDegree = 2 * A.natDegree) :
    (A ^ 3 * C0 ^ 2).natDegree = 7 * A.natDegree := by
  rw [natDegree_mul (pow_ne_zero 3 hA) (pow_ne_zero 2 hC),
    natDegree_pow, natDegree_pow, htie]
  omega

theorem xiAC02_monomial_natDegree_AC3
    {A C0 : k[X]} (hA : A ≠ 0) (hC : C0 ≠ 0)
    (htie : C0.natDegree = 2 * A.natDegree) :
    (A * C0 ^ 3).natDegree = 7 * A.natDegree := by
  rw [natDegree_mul hA (pow_ne_zero 3 hC), natDegree_pow, htie]
  omega

set_option maxHeartbeats 8000000 in
theorem xiAC02Combined810_natDegree_le
    {A C0 : k[X]} (hA : A ≠ 0) (hC : C0 ≠ 0)
    (htie : C0.natDegree = 2 * A.natDegree) :
    (xiAC02Combined810 A C0).natDegree ≤ 7 * A.natDegree := by
  have hA7 := xiAC02_monomial_natDegree_A7 (A := A)
  have hA5C := xiAC02_monomial_natDegree_A5C hA hC htie
  have hA3C2 := xiAC02_monomial_natDegree_A3C2 hA hC htie
  have hAC3 := xiAC02_monomial_natDegree_AC3 hA hC htie
  have hsmul (c : k) {p : k[X]} {n : ℕ} (hp : p.natDegree = n) :
      (c • p).natDegree ≤ n :=
    (natDegree_smul_le810 c p).trans hp.le
  rw [xiAC02Combined810]
  refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
  · refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · exact (natDegree_add_le _ _).trans
        (max_le (hsmul _ hA7) (hsmul _ hA5C))
    · exact hsmul _ hA3C2
  · exact hsmul _ hAC3

set_option maxHeartbeats 8000000 in
theorem xiAC02Combined810_coeff_top
    {A C0 : k[X]} (hA : A ≠ 0) (hC : C0 ≠ 0)
    (htie : C0.natDegree = 2 * A.natDegree) :
    (xiAC02Combined810 A C0).coeff (7 * A.natDegree) =
      (-(5 / 65536 : k)) *
        xiAC02Inner810 A.leadingCoeff C0.leadingCoeff := by
  have hA7 := xiAC02_monomial_natDegree_A7 (A := A)
  have hA5C := xiAC02_monomial_natDegree_A5C hA hC htie
  have hA3C2 := xiAC02_monomial_natDegree_A3C2 hA hC htie
  have hAC3 := xiAC02_monomial_natDegree_AC3 hA hC htie
  have h1 : (A ^ 7).coeff (7 * A.natDegree) = A.leadingCoeff ^ 7 := by
    rw [← hA7, coeff_natDegree, leadingCoeff_pow]
  have h2 : (A ^ 5 * C0).coeff (7 * A.natDegree) =
      A.leadingCoeff ^ 5 * C0.leadingCoeff := by
    rw [← hA5C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have h3 : (A ^ 3 * C0 ^ 2).coeff (7 * A.natDegree) =
      A.leadingCoeff ^ 3 * C0.leadingCoeff ^ 2 := by
    rw [← hA3C2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow,
      leadingCoeff_pow]
  have h4 : (A * C0 ^ 3).coeff (7 * A.natDegree) =
      A.leadingCoeff * C0.leadingCoeff ^ 3 := by
    rw [← hAC3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  rw [xiAC02Combined810_coeff, h1, h2, h3, h4]
  simpa [mul_assoc] using xiAC02Inner810_smul_eq A.leadingCoeff C0.leadingCoeff

theorem xiAC02Combined810_natDegree_eq_of_coeff_ne
    {A C0 : k[X]}
    (hA : A ≠ 0) (hC : C0 ≠ 0)
    (htie : C0.natDegree = 2 * A.natDegree)
    (hcoeff : xiAC02Inner810 A.leadingCoeff C0.leadingCoeff ≠ 0) :
    (xiAC02Combined810 A C0).natDegree = 7 * A.natDegree := by
  have h5 : (-(5 / 65536 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hle := xiAC02Combined810_natDegree_le hA hC htie
  have htop :
      (xiAC02Combined810 A C0).coeff (7 * A.natDegree) ≠ 0 := by
    rw [xiAC02Combined810_coeff_top hA hC htie]
    exact mul_ne_zero h5 hcoeff
  exact natDegree_eq_of_le_of_coeff_ne_zero hle htop

set_option maxHeartbeats 16000000 in
theorem muAE06Combined810_natDegree_eq_of_coeff_ne
    {A E0 : k[X]}
    (hA : A ≠ 0) (hE : E0 ≠ 0)
    (htie : E0.natDegree = 3 * A.natDegree)
    (hcoeff : muAE06Inner810 A.leadingCoeff E0.leadingCoeff ≠ 0) :
    (muAE06Combined810 A E0).natDegree = 6 * A.natDegree := by
  have hA6 : (A ^ 6).natDegree = 6 * A.natDegree := natDegree_pow A 6
  have hA3E :
      (A ^ 3 * E0).natDegree = 6 * A.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hA) hE, natDegree_pow, htie]
    omega
  have hE2 : (E0 ^ 2).natDegree = 6 * A.natDegree := by
    have : (E0 ^ 2).natDegree = 2 * E0.natDegree := natDegree_pow E0 2
    have : 2 * E0.natDegree = 6 * A.natDegree := by omega
    simpa [natDegree_pow] using this
  have hsmul (c : k) {p : k[X]} {n : ℕ} (hp : p.natDegree = n) :
      (c • p).natDegree ≤ n :=
    (natDegree_smul_le810 c p).trans hp.le
  have hle :
      (muAE06Combined810 A E0).natDegree ≤ 6 * A.natDegree := by
    simp only [muAE06Combined810]
    exact (natDegree_add_le _ _).trans
      (max_le ((natDegree_add_le _ _).trans
          (max_le (hsmul _ hA6) (hsmul _ hA3E))) (hsmul _ hE2))
  have h5 : (5 / 65536 : k) ≠ 0 :=
    div_ne_zero (by norm_num) (by norm_num)
  have hscale :
      (muAE06Combined810 A E0).coeff (6 * A.natDegree) =
        (5 / 65536 : k) *
          muAE06Inner810 A.leadingCoeff E0.leadingCoeff := by
    have h1 : (A ^ 6).coeff (6 * A.natDegree) = A.leadingCoeff ^ 6 := by
      rw [← hA6, coeff_natDegree, leadingCoeff_pow]
    have h1' : (A ^ 6).coeff (A.natDegree * 6) = A.leadingCoeff ^ 6 := by
      rw [mul_comm A.natDegree 6]; exact h1
    have h2 : (A ^ 3 * E0).coeff (6 * A.natDegree) =
        A.leadingCoeff ^ 3 * E0.leadingCoeff := by
      rw [← hA3E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
    have h2' : (A ^ 3 * E0).coeff (A.natDegree * 6) =
        A.leadingCoeff ^ 3 * E0.leadingCoeff := by
      rw [mul_comm A.natDegree 6]; exact h2
    have h3 : (E0 ^ 2).coeff (6 * A.natDegree) = E0.leadingCoeff ^ 2 := by
      rw [← hE2, coeff_natDegree, leadingCoeff_pow]
    have h3' : (E0 ^ 2).coeff (A.natDegree * 6) = E0.leadingCoeff ^ 2 := by
      rw [mul_comm A.natDegree 6]; exact h3
    simp only [muAE06Combined810, muAE06Inner810, coeff_add, coeff_smul,
      smul_eq_mul, h1, h1', h2, h2', h3, h3']
    ring
  have htop :
      (muAE06Combined810 A E0).coeff (6 * A.natDegree) ≠ 0 := by
    rw [hscale]
    exact mul_ne_zero h5 hcoeff
  exact natDegree_eq_of_le_of_coeff_ne_zero hle htop

set_option maxHeartbeats 16000000 in
theorem xiAE06Combined810_natDegree_eq_of_coeff_ne
    {A E0 : k[X]}
    (hA : A ≠ 0) (hE : E0 ≠ 0)
    (htie : E0.natDegree = 3 * A.natDegree)
    (hcoeff : xiAE06Inner810 A.leadingCoeff E0.leadingCoeff ≠ 0) :
    (xiAE06Combined810 A E0).natDegree = 7 * A.natDegree := by
  have hA7 : (A ^ 7).natDegree = 7 * A.natDegree := natDegree_pow A 7
  have hA4E :
      (A ^ 4 * E0).natDegree = 7 * A.natDegree := by
    rw [natDegree_mul (pow_ne_zero 4 hA) hE, natDegree_pow, htie]
    omega
  have hAE2 :
      (A * E0 ^ 2).natDegree = 7 * A.natDegree := by
    rw [natDegree_mul hA (pow_ne_zero 2 hE), natDegree_pow, htie]
    omega
  have hsmul (c : k) {p : k[X]} {n : ℕ} (hp : p.natDegree = n) :
      (c • p).natDegree ≤ n :=
    (natDegree_smul_le810 c p).trans hp.le
  have hle :
      (xiAE06Combined810 A E0).natDegree ≤ 7 * A.natDegree := by
    simp only [xiAE06Combined810]
    refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · exact hsmul _ hA7
      · exact hsmul _ hA4E
    · exact hsmul _ hAE2
  have h5 : (-(5 / 65536 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hscale :
      (xiAE06Combined810 A E0).coeff (7 * A.natDegree) =
        (-(5 / 65536 : k)) *
          xiAE06Inner810 A.leadingCoeff E0.leadingCoeff := by
    have h1 : (A ^ 7).coeff (7 * A.natDegree) = A.leadingCoeff ^ 7 := by
      rw [← hA7, coeff_natDegree, leadingCoeff_pow]
    have h1' : (A ^ 7).coeff (A.natDegree * 7) = A.leadingCoeff ^ 7 := by
      rw [mul_comm A.natDegree 7]; exact h1
    have h2 : (A ^ 4 * E0).coeff (7 * A.natDegree) =
        A.leadingCoeff ^ 4 * E0.leadingCoeff := by
      rw [← hA4E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
    have h2' : (A ^ 4 * E0).coeff (A.natDegree * 7) =
        A.leadingCoeff ^ 4 * E0.leadingCoeff := by
      rw [mul_comm A.natDegree 7]; exact h2
    have h3 : (A * E0 ^ 2).coeff (7 * A.natDegree) =
        A.leadingCoeff * E0.leadingCoeff ^ 2 := by
      rw [← hAE2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
    have h3' : (A * E0 ^ 2).coeff (A.natDegree * 7) =
        A.leadingCoeff * E0.leadingCoeff ^ 2 := by
      rw [mul_comm A.natDegree 7]; exact h3
    simp only [xiAE06Combined810, xiAE06Inner810, coeff_add, coeff_sub,
      coeff_smul, smul_eq_mul, h1, h1', h2, h2', h3, h3']
    ring
  have htop :
      (xiAE06Combined810 A E0).coeff (7 * A.natDegree) ≠ 0 := by
    rw [hscale]
    exact mul_ne_zero h5 hcoeff
  exact natDegree_eq_of_le_of_coeff_ne_zero hle htop

set_option maxHeartbeats 16000000 in
theorem muBE02Combined810_natDegree_eq_of_coeff_ne
    {B E0 : k[X]}
    (hB : B ≠ 0) (hE : E0 ≠ 0)
    (htie : E0.natDegree = 2 * B.natDegree)
    (hcoeff : muBE02Inner810 B.leadingCoeff E0.leadingCoeff ≠ 0) :
    (muBE02Combined810 B E0).natDegree = 4 * B.natDegree := by
  have hB4 : (B ^ 4).natDegree = 4 * B.natDegree := natDegree_pow B 4
  have hB2E :
      (B ^ 2 * E0).natDegree = 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hB) hE, natDegree_pow, htie]
    omega
  have hE2 : (E0 ^ 2).natDegree = 4 * B.natDegree := by
    have : (E0 ^ 2).natDegree = 2 * E0.natDegree := natDegree_pow E0 2
    have : 2 * E0.natDegree = 4 * B.natDegree := by omega
    simpa [natDegree_pow] using this
  have hsmul (c : k) {p : k[X]} {n : ℕ} (hp : p.natDegree = n) :
      (c • p).natDegree ≤ n :=
    (natDegree_smul_le810 c p).trans hp.le
  have hle :
      (muBE02Combined810 B E0).natDegree ≤ 4 * B.natDegree := by
    simp only [muBE02Combined810]
    exact (natDegree_add_le _ _).trans
      (max_le ((natDegree_sub_le _ _).trans
          (max_le (hsmul _ hB4) (hsmul _ hB2E))) (hsmul _ hE2))
  have h5 : (5 / 2048 : k) ≠ 0 :=
    div_ne_zero (by norm_num) (by norm_num)
  have hscale :
      (muBE02Combined810 B E0).coeff (4 * B.natDegree) =
        (5 / 2048 : k) *
          muBE02Inner810 B.leadingCoeff E0.leadingCoeff := by
    have h1 : (B ^ 4).coeff (4 * B.natDegree) = B.leadingCoeff ^ 4 := by
      rw [← hB4, coeff_natDegree, leadingCoeff_pow]
    have h1' : (B ^ 4).coeff (B.natDegree * 4) = B.leadingCoeff ^ 4 := by
      rw [mul_comm B.natDegree 4]; exact h1
    have h2 : (B ^ 2 * E0).coeff (4 * B.natDegree) =
        B.leadingCoeff ^ 2 * E0.leadingCoeff := by
      rw [← hB2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
    have h2' : (B ^ 2 * E0).coeff (B.natDegree * 4) =
        B.leadingCoeff ^ 2 * E0.leadingCoeff := by
      rw [mul_comm B.natDegree 4]; exact h2
    have h3 : (E0 ^ 2).coeff (4 * B.natDegree) = E0.leadingCoeff ^ 2 := by
      rw [← hE2, coeff_natDegree, leadingCoeff_pow]
    have h3' : (E0 ^ 2).coeff (B.natDegree * 4) = E0.leadingCoeff ^ 2 := by
      rw [mul_comm B.natDegree 4]; exact h3
    simp only [muBE02Combined810, muBE02Inner810, coeff_add, coeff_sub,
      coeff_smul, smul_eq_mul, h1, h1', h2, h2', h3, h3']
    ring
  have htop :
      (muBE02Combined810 B E0).coeff (4 * B.natDegree) ≠ 0 := by
    rw [hscale]
    exact mul_ne_zero h5 hcoeff
  exact natDegree_eq_of_le_of_coeff_ne_zero hle htop

set_option maxHeartbeats 16000000 in
theorem omicronBE02Combined810_natDegree_eq_of_coeff_ne
    {B E0 : k[X]}
    (hB : B ≠ 0) (hE : E0 ≠ 0)
    (htie : E0.natDegree = 2 * B.natDegree)
    (hcoeff : omicronBE02Inner810 B.leadingCoeff E0.leadingCoeff ≠ 0) :
    (omicronBE02Combined810 B E0).natDegree = 5 * B.natDegree := by
  have hB5 : (B ^ 5).natDegree = 5 * B.natDegree := natDegree_pow B 5
  have hB3E :
      (B ^ 3 * E0).natDegree = 5 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hB) hE, natDegree_pow, htie]
    omega
  have hBE2 :
      (B * E0 ^ 2).natDegree = 5 * B.natDegree := by
    rw [natDegree_mul hB (pow_ne_zero 2 hE), natDegree_pow, htie]
    omega
  have hsmul (c : k) {p : k[X]} {n : ℕ} (hp : p.natDegree = n) :
      (c • p).natDegree ≤ n :=
    (natDegree_smul_le810 c p).trans hp.le
  have hle :
      (omicronBE02Combined810 B E0).natDegree ≤ 5 * B.natDegree := by
    simp only [omicronBE02Combined810]
    refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
      · exact hsmul _ hB5
      · exact hsmul _ hB3E
    · exact hsmul _ hBE2
  have hsc : (-(1 / 4096 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hscale :
      (omicronBE02Combined810 B E0).coeff (5 * B.natDegree) =
        (-(1 / 4096 : k)) *
          omicronBE02Inner810 B.leadingCoeff E0.leadingCoeff := by
    have h1 : (B ^ 5).coeff (5 * B.natDegree) = B.leadingCoeff ^ 5 := by
      rw [← hB5, coeff_natDegree, leadingCoeff_pow]
    have h1' : (B ^ 5).coeff (B.natDegree * 5) = B.leadingCoeff ^ 5 := by
      rw [mul_comm B.natDegree 5]; exact h1
    have h2 : (B ^ 3 * E0).coeff (5 * B.natDegree) =
        B.leadingCoeff ^ 3 * E0.leadingCoeff := by
      rw [← hB3E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
    have h2' : (B ^ 3 * E0).coeff (B.natDegree * 5) =
        B.leadingCoeff ^ 3 * E0.leadingCoeff := by
      rw [mul_comm B.natDegree 5]; exact h2
    have h3 : (B * E0 ^ 2).coeff (5 * B.natDegree) =
        B.leadingCoeff * E0.leadingCoeff ^ 2 := by
      rw [← hBE2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
    have h3' : (B * E0 ^ 2).coeff (B.natDegree * 5) =
        B.leadingCoeff * E0.leadingCoeff ^ 2 := by
      rw [mul_comm B.natDegree 5]; exact h3
    simp only [omicronBE02Combined810, omicronBE02Inner810, coeff_add,
      coeff_sub, coeff_smul, smul_eq_mul, h1, h1', h2, h2', h3, h3']
    ring
  have htop :
      (omicronBE02Combined810 B E0).coeff (5 * B.natDegree) ≠ 0 := by
    rw [hscale]
    exact mul_ne_zero hsc hcoeff
  exact natDegree_eq_of_le_of_coeff_ne_zero hle htop

set_option maxHeartbeats 16000000 in
theorem muAD05Combined810_natDegree_eq_of_coeff_ne
    {A D0 : k[X]}
    (hA : A ≠ 0) (hD : D0 ≠ 0)
    (htie : 5 * A.natDegree = 2 * D0.natDegree)
    (hcoeff : muAD05Inner810 A.leadingCoeff D0.leadingCoeff ≠ 0) :
    (muAD05Combined810 A D0).natDegree = 6 * A.natDegree := by
  have hA6 : (A ^ 6).natDegree = 6 * A.natDegree := natDegree_pow A 6
  have hAD2 :
      (A * D0 ^ 2).natDegree = 6 * A.natDegree := by
    rw [natDegree_mul hA (pow_ne_zero 2 hD), natDegree_pow]
    omega
  have hsmul (c : k) {p : k[X]} {n : ℕ} (hp : p.natDegree = n) :
      (c • p).natDegree ≤ n :=
    (natDegree_smul_le810 c p).trans hp.le
  have hle :
      (muAD05Combined810 A D0).natDegree ≤ 6 * A.natDegree := by
    simp only [muAD05Combined810]
    exact (natDegree_sub_le _ _).trans (max_le (hsmul _ hA6) (hsmul _ hAD2))
  have hsc : (1 / 65536 : k) ≠ 0 :=
    div_ne_zero (by norm_num) (by norm_num)
  have hscale :
      (muAD05Combined810 A D0).coeff (6 * A.natDegree) =
        (1 / 65536 : k) *
          muAD05Inner810 A.leadingCoeff D0.leadingCoeff := by
    have h1 : (A ^ 6).coeff (6 * A.natDegree) = A.leadingCoeff ^ 6 := by
      rw [← hA6, coeff_natDegree, leadingCoeff_pow]
    have h1' : (A ^ 6).coeff (A.natDegree * 6) = A.leadingCoeff ^ 6 := by
      rw [mul_comm A.natDegree 6]; exact h1
    have h2 : (A * D0 ^ 2).coeff (6 * A.natDegree) =
        A.leadingCoeff * D0.leadingCoeff ^ 2 := by
      rw [← hAD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
    have h2' : (A * D0 ^ 2).coeff (A.natDegree * 6) =
        A.leadingCoeff * D0.leadingCoeff ^ 2 := by
      rw [mul_comm A.natDegree 6]; exact h2
    simp only [muAD05Combined810, muAD05Inner810, coeff_sub, coeff_smul,
      smul_eq_mul, h1, h1', h2, h2']
    ring
  have htop :
      (muAD05Combined810 A D0).coeff (6 * A.natDegree) ≠ 0 := by
    rw [hscale]
    exact mul_ne_zero hsc hcoeff
  exact natDegree_eq_of_le_of_coeff_ne_zero hle htop

set_option maxHeartbeats 16000000 in
theorem xiAD05Combined810_natDegree_eq_of_coeff_ne
    {A D0 : k[X]}
    (hA : A ≠ 0) (hD : D0 ≠ 0)
    (htie : 5 * A.natDegree = 2 * D0.natDegree)
    (hcoeff : xiAD05Inner810 A.leadingCoeff D0.leadingCoeff ≠ 0) :
    (xiAD05Combined810 A D0).natDegree = 7 * A.natDegree := by
  have hA7 : (A ^ 7).natDegree = 7 * A.natDegree := natDegree_pow A 7
  have hA2D2 :
      (A ^ 2 * D0 ^ 2).natDegree = 7 * A.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hA) (pow_ne_zero 2 hD),
      natDegree_pow, natDegree_pow]
    omega
  have hsmul (c : k) {p : k[X]} {n : ℕ} (hp : p.natDegree = n) :
      (c • p).natDegree ≤ n :=
    (natDegree_smul_le810 c p).trans hp.le
  have hle :
      (xiAD05Combined810 A D0).natDegree ≤ 7 * A.natDegree := by
    simp only [xiAD05Combined810]
    exact (natDegree_add_le _ _).trans (max_le (hsmul _ hA7) (hsmul _ hA2D2))
  have hsc : (1 / 65536 : k) ≠ 0 :=
    div_ne_zero (by norm_num) (by norm_num)
  have hscale :
      (xiAD05Combined810 A D0).coeff (7 * A.natDegree) =
        (1 / 65536 : k) *
          xiAD05Inner810 A.leadingCoeff D0.leadingCoeff := by
    have h1 : (A ^ 7).coeff (7 * A.natDegree) = A.leadingCoeff ^ 7 := by
      rw [← hA7, coeff_natDegree, leadingCoeff_pow]
    have h1' : (A ^ 7).coeff (A.natDegree * 7) = A.leadingCoeff ^ 7 := by
      rw [mul_comm A.natDegree 7]; exact h1
    have h2 : (A ^ 2 * D0 ^ 2).coeff (7 * A.natDegree) =
        A.leadingCoeff ^ 2 * D0.leadingCoeff ^ 2 := by
      rw [← hA2D2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow,
        leadingCoeff_pow]
    have h2' : (A ^ 2 * D0 ^ 2).coeff (A.natDegree * 7) =
        A.leadingCoeff ^ 2 * D0.leadingCoeff ^ 2 := by
      rw [mul_comm A.natDegree 7]; exact h2
    simp only [xiAD05Combined810, xiAD05Inner810, coeff_add, coeff_smul,
      smul_eq_mul, h1, h1', h2, h2']
    ring
  have htop :
      (xiAD05Combined810 A D0).coeff (7 * A.natDegree) ≠ 0 := by
    rw [hscale]
    exact mul_ne_zero hsc hcoeff
  exact natDegree_eq_of_le_of_coeff_ne_zero hle htop

end ExhaustCombinedDeg810


/-! ## Unique-face and Groebner-tie impossibilities -/

section ExhaustImpossible810

variable {k : Type*} [Field k] [CharZero k]

theorem mu_A6_impossible_of_mixedB
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : A6LeadsMuMixedBCone810 A B C0 D0 E0 F0 G0)
    (hdeg :
      (degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0) :
    False := by
  have hA : A ≠ 0 := by
    intro hA0
    rcases hcone with ⟨hApos, _⟩
    simp [hA0] at hApos
  have hlead := muA6Face810_natDegree hA
  have hrest :=
    degreeZeroMuNoA6_natDegree_lt_of_mixedB l beta gamma delta epsilon
      zeta eta theta A B C0 D0 E0 F0 G0 hcone
  rw [degreeZeroMuPolynomial810_eq_A6_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, _⟩
  omega

theorem mu_A6_impossible_of_A6B
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : A6BLeadsOmicronCone810 A B C0 D0 E0 F0 G0)
    (hdeg :
      (degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0) :
    False := by
  have hA6B :
      A6LeadsMuMixedBCone810 A B C0 D0 E0 F0 G0 := by
    rcases hcone with ⟨hApos, hBpos, _, h3, hC, hD, hE, hF, hG⟩
    exact ⟨hApos, hBpos, h3, hC, hD, hE, hF, hG⟩
  exact mu_A6_impossible_of_mixedB l beta gamma delta epsilon zeta eta
    theta A B C0 D0 E0 F0 G0 hA6B hdeg

theorem mu_A6_impossible_of_mixedC0
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : A6LeadsMuMixedC0Cone810 A B C0 D0 E0 F0 G0)
    (hdeg :
      (degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0) :
    False := by
  have hA : A ≠ 0 := by
    intro hA0
    rcases hcone with ⟨hApos, _⟩
    simp [hA0] at hApos
  have hlead := muA6Face810_natDegree hA
  have hrest :=
    degreeZeroMuNoA6_natDegree_lt_of_mixedC0 l beta gamma delta epsilon
      zeta eta theta A B C0 D0 E0 F0 G0 hcone
  rw [degreeZeroMuPolynomial810_eq_A6_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, _⟩
  omega

theorem mu_A6_impossible_of_mixedD0
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : A6LeadsMuMixedD0Cone810 A B C0 D0 E0 F0 G0)
    (hdeg :
      (degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0) :
    False := by
  have hA : A ≠ 0 := by
    intro hA0
    rcases hcone with ⟨hApos, _⟩
    simp [hA0] at hApos
  have hlead := muA6Face810_natDegree hA
  have hrest :=
    degreeZeroMuNoA6_natDegree_lt_of_mixedD0 l beta gamma delta epsilon
      zeta eta theta A B C0 D0 E0 F0 G0 hcone
  rw [degreeZeroMuPolynomial810_eq_A6_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, _⟩
  omega

theorem mu_A6_impossible_of_AE03
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : AE03RatioTieCone810 A B C0 D0 E0 F0 G0)
    (hdeg :
      (degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0) :
    False := by
  have hA : A ≠ 0 := by
    intro hA0
    rcases hcone with ⟨hApos, _⟩
    simp [hA0] at hApos
  have hlead := muA6Face810_natDegree hA
  have hrest :=
    degreeZeroMuNoA6_natDegree_lt_of_AE03 l beta gamma delta epsilon zeta
      eta theta A B C0 D0 E0 F0 G0 hcone
  rw [degreeZeroMuPolynomial810_eq_A6_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, _⟩
  omega

theorem mu_A6_impossible_of_AF07
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : AF07RatioTieCone810 A B C0 D0 E0 F0 G0)
    (hdeg :
      (degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0) :
    False := by
  have hA : A ≠ 0 := by
    intro hA0
    rcases hcone with ⟨hApos, _⟩
    simp [hA0] at hApos
  have hlead := muA6Face810_natDegree hA
  have hrest :=
    degreeZeroMuNoA6_natDegree_lt_of_AF07 l beta gamma delta epsilon zeta
      eta theta A B C0 D0 E0 F0 G0 hcone
  rw [degreeZeroMuPolynomial810_eq_A6_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, _⟩
  omega

set_option maxHeartbeats 16000000 in
theorem mu_xi_AC02_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : AC02RatioTieCone810 A B C0 D0 E0 F0 G0)
    (hmuDeg :
      (degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0)
    (hxiDeg :
      (degreeZeroXiPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0) :
    False := by
  have hApos : 0 < A.natDegree := hcone.1
  have hCpos : 0 < C0.natDegree := hcone.2.1
  have htie : C0.natDegree = 2 * A.natDegree := hcone.2.2.1
  have hAne : A ≠ 0 := by
    intro hA0
    have : A.natDegree = 0 := by simp [hA0]
    omega
  have hCne : C0 ≠ 0 := by
    intro hC0
    simp [hC0] at hCpos
  have hr : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
  have hs : C0.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  by_cases hmuI : muAC02Inner810 A.leadingCoeff C0.leadingCoeff = 0
  · by_cases hxiI : xiAC02Inner810 A.leadingCoeff C0.leadingCoeff = 0
    · have hs6 :=
        mu_xi_AC02_inner_s_pow A.leadingCoeff C0.leadingCoeff hmuI hxiI
      exact hs ((pow_eq_zero_iff (by decide : (6 : ℕ) ≠ 0)).mp hs6)
    · have hcombdeg :=
        xiAC02Combined810_natDegree_eq_of_coeff_ne hAne hCne htie hxiI
      have hrest :=
        degreeZeroXiNoAC02_natDegree_lt l beta gamma delta epsilon zeta
          eta theta A B C0 D0 E0 F0 G0 hcone
      rw [degreeZeroXiPolynomial810_eq_AC02_add_rest,
        natDegree_add_eq_left_of_natDegree_lt (by rwa [hcombdeg]),
        hcombdeg] at hxiDeg
      omega
  · have hcombdeg :=
      muAC02Combined810_natDegree_eq_of_coeff_ne hAne hCne htie hmuI
    have hrest :=
      degreeZeroMuNoAC02_natDegree_lt l beta gamma delta epsilon zeta
        eta theta A B C0 D0 E0 F0 G0 hcone
    rw [degreeZeroMuPolynomial810_eq_AC02_add_rest,
      natDegree_add_eq_left_of_natDegree_lt (by rwa [hcombdeg]),
      hcombdeg] at hmuDeg
    omega

set_option maxHeartbeats 16000000 in
theorem mu_xi_ABC0_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : ABC0RatioTieCone810 A B C0 D0 E0 F0 G0)
    (hmuDeg :
      (degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0)
    (hxiDeg :
      (degreeZeroXiPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0) :
    False := by
  have hApos : 0 < A.natDegree := hcone.1
  have hCpos : 0 < C0.natDegree := hcone.2.2.1
  have htie : C0.natDegree = 2 * A.natDegree := hcone.2.2.2.1
  have hAne : A ≠ 0 := by
    intro hA0
    have : A.natDegree = 0 := by simp [hA0]
    omega
  have hCne : C0 ≠ 0 := by
    intro hC0
    simp [hC0] at hCpos
  have hs : C0.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  by_cases hmuI : muAC02Inner810 A.leadingCoeff C0.leadingCoeff = 0
  · by_cases hxiI : xiAC02Inner810 A.leadingCoeff C0.leadingCoeff = 0
    · have hs6 :=
        mu_xi_AC02_inner_s_pow A.leadingCoeff C0.leadingCoeff hmuI hxiI
      exact hs ((pow_eq_zero_iff (by decide : (6 : ℕ) ≠ 0)).mp hs6)
    · have hcombdeg :=
        xiAC02Combined810_natDegree_eq_of_coeff_ne hAne hCne htie hxiI
      have hrest :=
        degreeZeroXiNoAC02_natDegree_lt_of_ABC0 l beta gamma delta
          epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone
      rw [degreeZeroXiPolynomial810_eq_AC02_add_rest,
        natDegree_add_eq_left_of_natDegree_lt (by rwa [hcombdeg]),
        hcombdeg] at hxiDeg
      omega
  · have hcombdeg :=
      muAC02Combined810_natDegree_eq_of_coeff_ne hAne hCne htie hmuI
    have hrest :=
      degreeZeroMuNoAC02_natDegree_lt_of_ABC0 l beta gamma delta epsilon
        zeta eta theta A B C0 D0 E0 F0 G0 hcone
    rw [degreeZeroMuPolynomial810_eq_AC02_add_rest,
      natDegree_add_eq_left_of_natDegree_lt (by rwa [hcombdeg]),
      hcombdeg] at hmuDeg
    omega

set_option maxHeartbeats 16000000 in
theorem mu_xi_AE06_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : AE06RatioTieCone810 A B C0 D0 E0 F0 G0)
    (hmuDeg :
      (degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0)
    (hxiDeg :
      (degreeZeroXiPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0) :
    False := by
  have hApos : 0 < A.natDegree := hcone.1
  have hEpos : 0 < E0.natDegree := hcone.2.1
  have htie : E0.natDegree = 3 * A.natDegree := hcone.2.2.1
  have hAne : A ≠ 0 := by
    intro hA0
    have : A.natDegree = 0 := by simp [hA0]
    omega
  have hEne : E0 ≠ 0 := by
    intro hE0
    simp [hE0] at hEpos
  have hv : E0.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hEne
  by_cases hmuI : muAE06Inner810 A.leadingCoeff E0.leadingCoeff = 0
  · by_cases hxiI : xiAE06Inner810 A.leadingCoeff E0.leadingCoeff = 0
    · have hv4 :=
        mu_xi_AE06_inner_v_pow A.leadingCoeff E0.leadingCoeff hmuI hxiI
      exact hv ((pow_eq_zero_iff (by decide : (4 : ℕ) ≠ 0)).mp hv4)
    · have hcombdeg :=
        xiAE06Combined810_natDegree_eq_of_coeff_ne hAne hEne htie hxiI
      have hrest :=
        degreeZeroXiNoAE06_natDegree_lt l beta gamma delta epsilon zeta
          eta theta A B C0 D0 E0 F0 G0 hcone
      rw [degreeZeroXiPolynomial810_eq_AE06_add_rest,
        natDegree_add_eq_left_of_natDegree_lt (by rwa [hcombdeg]),
        hcombdeg] at hxiDeg
      omega
  · have hcombdeg :=
      muAE06Combined810_natDegree_eq_of_coeff_ne hAne hEne htie hmuI
    have hrest :=
      degreeZeroMuNoAE06_natDegree_lt l beta gamma delta epsilon zeta
        eta theta A B C0 D0 E0 F0 G0 hcone
    rw [degreeZeroMuPolynomial810_eq_AE06_add_rest,
      natDegree_add_eq_left_of_natDegree_lt (by rwa [hcombdeg]),
      hcombdeg] at hmuDeg
    omega

set_option maxHeartbeats 16000000 in
theorem mu_omicron_BE02_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : BE02RatioTieCone810 A B C0 D0 E0 F0 G0)
    (hmuDeg :
      (degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0)
    (homDeg :
      (degreeZeroOmicronPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0) :
    False := by
  have hBpos : 0 < B.natDegree := hcone.1
  have hEpos : 0 < E0.natDegree := hcone.2.1
  have htie : E0.natDegree = 2 * B.natDegree := hcone.2.2.1
  have hBne : B ≠ 0 := by
    intro hB0
    simp [hB0] at hBpos
  have hEne : E0 ≠ 0 := by
    intro hE0
    simp [hE0] at hEpos
  have hw : E0.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hEne
  by_cases hmuI : muBE02Inner810 B.leadingCoeff E0.leadingCoeff = 0
  · by_cases homI : omicronBE02Inner810 B.leadingCoeff E0.leadingCoeff = 0
    · have hw4 :=
        mu_omicron_BE02_inner_w_pow B.leadingCoeff E0.leadingCoeff hmuI
          homI
      exact hw ((pow_eq_zero_iff (by decide : (4 : ℕ) ≠ 0)).mp hw4)
    · have hcombdeg :=
        omicronBE02Combined810_natDegree_eq_of_coeff_ne hBne hEne htie
          homI
      have hrest :=
        degreeZeroOmicronNoBE02_natDegree_lt l beta gamma delta epsilon
          zeta eta theta A B C0 D0 E0 F0 G0 hcone
      rw [degreeZeroOmicronPolynomial810_eq_BE02_add_rest,
        natDegree_add_eq_left_of_natDegree_lt (by rwa [hcombdeg]),
        hcombdeg] at homDeg
      omega
  · have hcombdeg :=
      muBE02Combined810_natDegree_eq_of_coeff_ne hBne hEne htie hmuI
    have hrest :=
      degreeZeroMuNoBE02_natDegree_lt l beta gamma delta epsilon zeta
        eta theta A B C0 D0 E0 F0 G0 hcone
    rw [degreeZeroMuPolynomial810_eq_BE02_add_rest,
      natDegree_add_eq_left_of_natDegree_lt (by rwa [hcombdeg]),
      hcombdeg] at hmuDeg
    omega

set_option maxHeartbeats 16000000 in
theorem mu_xi_AD05_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : AD05RatioTieCone810 A B C0 D0 E0 F0 G0)
    (hmuDeg :
      (degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0)
    (hxiDeg :
      (degreeZeroXiPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0) :
    False := by
  have hApos : 0 < A.natDegree := hcone.1
  have hDpos : 0 < D0.natDegree := hcone.2.1
  have htie : 5 * A.natDegree = 2 * D0.natDegree := hcone.2.2.1
  have hAne : A ≠ 0 := by
    intro hA0
    have : A.natDegree = 0 := by simp [hA0]
    omega
  have hDne : D0 ≠ 0 := by
    intro hD0
    simp [hD0] at hDpos
  have hr : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
  by_cases hmuI : muAD05Inner810 A.leadingCoeff D0.leadingCoeff = 0
  · by_cases hxiI : xiAD05Inner810 A.leadingCoeff D0.leadingCoeff = 0
    · have hr7 :=
        mu_xi_AD05_inner_r_pow A.leadingCoeff D0.leadingCoeff hmuI hxiI
      exact hr ((pow_eq_zero_iff (by decide : (7 : ℕ) ≠ 0)).mp hr7)
    · have hcombdeg :=
        xiAD05Combined810_natDegree_eq_of_coeff_ne hAne hDne htie hxiI
      have hrest :=
        degreeZeroXiNoAD05_natDegree_lt l beta gamma delta epsilon zeta
          eta theta A B C0 D0 E0 F0 G0 hcone
      rw [degreeZeroXiPolynomial810_eq_AD05_add_rest,
        natDegree_add_eq_left_of_natDegree_lt (by rwa [hcombdeg]),
        hcombdeg] at hxiDeg
      omega
  · have hcombdeg :=
      muAD05Combined810_natDegree_eq_of_coeff_ne hAne hDne htie hmuI
    have hrest :=
      degreeZeroMuNoAD05_natDegree_lt l beta gamma delta epsilon zeta
        eta theta A B C0 D0 E0 F0 G0 hcone
    rw [degreeZeroMuPolynomial810_eq_AD05_add_rest,
      natDegree_add_eq_left_of_natDegree_lt (by rwa [hcombdeg]),
      hcombdeg] at hmuDeg
    omega

theorem xi_C0E0_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : C0E0RatioTieCone810 A B C0 D0 E0 F0 G0)
    (hdeg :
      (degreeZeroXiPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0) :
    False := by
  have hC : C0 ≠ 0 := by
    intro hC0
    rcases hcone with ⟨hCpos, _⟩
    simp [hC0] at hCpos
  have hE : E0 ≠ 0 := by
    intro hE0
    rcases hcone with ⟨_, hEpos, _⟩
    simp [hE0] at hEpos
  have hc : (-(15 / 128 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead :
      (xiC0E0Face810 C0 E0).natDegree =
        2 * C0.natDegree + E0.natDegree := by
    simp only [xiC0E0Face810]
    rw [natDegree_smul _ hc, natDegree_mul (pow_ne_zero 2 hC) hE,
      natDegree_pow]
  have hrest :=
    degreeZeroXiNoC0E0_natDegree_lt l beta gamma delta epsilon zeta eta
      theta A B C0 D0 E0 F0 G0 hcone
  rw [degreeZeroXiPolynomial810_eq_C0E0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hCpos, hEpos, _⟩
  omega

theorem mu_C03_impossible_of_BC03
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : BC03RatioTieCone810 A B C0 D0 E0 F0 G0)
    (hdeg :
      (degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0) :
    False := by
  have hC : C0 ≠ 0 := by
    intro hC0
    rcases hcone with ⟨_, hCpos, _⟩
    simp [hC0] at hCpos
  have hc : (-(5 / 128 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead :
      ((-(5 / 128 : k)) • C0 ^ 3).natDegree = 3 * C0.natDegree := by
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :=
    degreeZeroMuNoC03_natDegree_lt_of_BC03 l beta gamma delta epsilon
      zeta eta theta A B C0 D0 E0 F0 G0 hcone
  rw [degreeZeroMuPolynomial810_eq_C03_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨_, hCpos, _⟩
  omega

theorem mu_B4_impossible_of_BD03
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : BD03RatioTieCone810 A B C0 D0 E0 F0 G0)
    (hdeg :
      (degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0) :
    False := by
  have hB : B ≠ 0 := by
    intro hB0
    rcases hcone with ⟨hBpos, _⟩
    simp [hB0] at hBpos
  have hc : (35 / 2048 : k) ≠ 0 :=
    div_ne_zero (by norm_num) (by norm_num)
  have hlead :
      ((35 / 2048 : k) • B ^ 4).natDegree = 4 * B.natDegree := by
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :=
    degreeZeroMuNoB4_natDegree_lt_of_BD03 l beta gamma delta epsilon zeta
      eta theta A B C0 D0 E0 F0 G0 hcone
  rw [degreeZeroMuPolynomial810_eq_B4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hBpos, _⟩
  omega

end ExhaustImpossible810


/-! ## Affine form of the primitive on unique-`G₀` with `l = 0` -/

section ExhaustG0Affine810

variable {k : Type*} [Field k] [CharZero k]

/-- `G₀`-linear coefficient of `ρ_base` at `l = 0`.  Every remaining
`G₀` monomial is linear, and the quadratic face `G₀² L` has vanished. -/
def rhoBaseG0LinearCoeff810 (A B C0 D0 E0 F0 : k[X]) : k[X] :=
  -(255 / 2048 : k) • (A ^ 3 * B)
    + (15 / 256 : k) • B ^ 3
    + (45 / 128 : k) • (A * B * C0)
    + (45 / 256 : k) • (A ^ 2 * D0)
    - (5 / 16 : k) • (C0 * D0)
    - (5 / 16 : k) • (B * E0)
    - (5 / 16 : k) • (A * F0)

/-- `G₀`-linear monomials of `ρ_base` at `l = 0`, before factoring `G₀`. -/
def rhoBaseG0LinearTerms810 (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(255 / 2048 : k) • (A ^ 3 * B * G0)
    + (15 / 256 : k) • (B ^ 3 * G0)
    + (45 / 128 : k) • (A * B * C0 * G0)
    + (45 / 256 : k) • (A ^ 2 * D0 * G0)
    - (5 / 16 : k) • (C0 * D0 * G0)
    - (5 / 16 : k) • (B * E0 * G0)
    - (5 / 16 : k) • (A * F0 * G0)

set_option maxHeartbeats 16000000 in
theorem rhoBaseG0LinearTerms810_eq_coeff_mul
    (A B C0 D0 E0 F0 G0 : k[X]) :
    rhoBaseG0LinearTerms810 A B C0 D0 E0 F0 G0 =
      rhoBaseG0LinearCoeff810 A B C0 D0 E0 F0 * G0 := by
  simp only [rhoBaseG0LinearTerms810, rhoBaseG0LinearCoeff810, add_mul,
    sub_mul, neg_mul, ← smul_mul_assoc, mul_assoc]

set_option maxHeartbeats 16000000 in
theorem rhoBaseGroupHighG0Rest810_l0_eq_noG0_add_linearTerms
    (A B C0 D0 E0 F0 G0 : k[X]) :
    rhoBaseGroupHighG0Rest810 0 A B C0 D0 E0 F0 G0 =
      rhoBaseGroupHighG0Rest810 0 A B C0 D0 E0 F0 0 +
        rhoBaseG0LinearTerms810 A B C0 D0 E0 F0 G0 := by
  simp only [rhoBaseGroupHighG0Rest810, rhoBaseG0LinearTerms810, zero_mul,
    mul_zero, zero_smul, smul_zero]
  module

set_option maxHeartbeats 16000000 in
theorem rhoBaseGroupPolynomial810_l0_eq_noG0_add_linear
    (A B C0 D0 E0 F0 G0 : k[X]) :
    rhoBaseGroupPolynomial810 0 A B C0 D0 E0 F0 G0 =
      rhoBaseGroupHighG0Rest810 0 A B C0 D0 E0 F0 0 +
        rhoBaseG0LinearCoeff810 A B C0 D0 E0 F0 * G0 := by
  rw [rhoBaseGroupPolynomial810_eq_G02_add_rest,
    rhoBaseGroupHighG0Rest810_l0_eq_noG0_add_linearTerms,
    rhoBaseG0LinearTerms810_eq_coeff_mul]
  simp only [mul_zero, zero_mul, zero_smul, zero_add]

theorem rhoThetaGroupPolynomial810_eq_noG0_add_G0
    (A B C0 D0 E0 G0 : k[X]) :
    rhoThetaGroupPolynomial810 A B C0 D0 E0 G0 =
      rhoThetaGroupPolynomial810 A B C0 D0 E0 0 + G0 := by
  have h1 : (1 / 1 : k) = 1 := by norm_num
  simp only [rhoThetaGroupPolynomial810, h1, one_smul, zero_mul, mul_zero,
    zero_smul, smul_zero]
  abel

set_option maxHeartbeats 16000000 in
theorem rhoBetaGroupPolynomial810_natDegree_le_zero_of_constants
    {A B C0 D0 E0 F0 : k[X]}
    (hA : A.natDegree = 0) (hB : B.natDegree = 0)
    (hC : C0.natDegree = 0) (hD : D0.natDegree = 0)
    (hE : E0.natDegree = 0) (hF : F0.natDegree = 0) :
    (rhoBetaGroupPolynomial810 A B C0 D0 E0 F0).natDegree ≤ 0 := by
  simp only [rhoBetaGroupPolynomial810]
  compute_degree
  omega

set_option maxHeartbeats 16000000 in
theorem rhoGammaGroupPolynomial810_natDegree_le_zero_of_constants
    {A B C0 D0 E0 F0 : k[X]}
    (hA : A.natDegree = 0) (hB : B.natDegree = 0)
    (hC : C0.natDegree = 0) (hD : D0.natDegree = 0)
    (hE : E0.natDegree = 0) (hF : F0.natDegree = 0) :
    (rhoGammaGroupPolynomial810 A B C0 D0 E0 F0).natDegree ≤ 0 := by
  simp only [rhoGammaGroupPolynomial810]
  compute_degree
  omega

set_option maxHeartbeats 16000000 in
theorem rhoDeltaGroupPolynomial810_natDegree_le_zero_of_constants
    {A B C0 D0 E0 F0 : k[X]}
    (hA : A.natDegree = 0) (hB : B.natDegree = 0)
    (hC : C0.natDegree = 0) (hD : D0.natDegree = 0)
    (hE : E0.natDegree = 0) (hF : F0.natDegree = 0) :
    (rhoDeltaGroupPolynomial810 A B C0 D0 E0 F0).natDegree ≤ 0 := by
  simp only [rhoDeltaGroupPolynomial810]
  compute_degree
  omega

set_option maxHeartbeats 16000000 in
theorem rhoEpsilonGroupPolynomial810_natDegree_le_zero_of_constants
    {A B C0 D0 E0 F0 : k[X]}
    (hA : A.natDegree = 0) (hB : B.natDegree = 0)
    (hC : C0.natDegree = 0) (hD : D0.natDegree = 0)
    (hE : E0.natDegree = 0) (hF : F0.natDegree = 0) :
    (rhoEpsilonGroupPolynomial810 A B C0 D0 E0 F0).natDegree ≤ 0 := by
  simp only [rhoEpsilonGroupPolynomial810]
  compute_degree
  omega

set_option maxHeartbeats 16000000 in
theorem rhoZetaGroupPolynomial810_natDegree_le_zero_of_constants
    {A B C0 D0 E0 F0 : k[X]}
    (hA : A.natDegree = 0) (hB : B.natDegree = 0)
    (hC : C0.natDegree = 0) (hD : D0.natDegree = 0)
    (hE : E0.natDegree = 0) (hF : F0.natDegree = 0) :
    (rhoZetaGroupPolynomial810 A B C0 D0 E0 F0).natDegree ≤ 0 := by
  simp only [rhoZetaGroupPolynomial810]
  compute_degree
  omega

set_option maxHeartbeats 16000000 in
theorem rhoEtaGroupPolynomial810_natDegree_le_zero_of_constants
    {A B C0 D0 E0 F0 : k[X]}
    (hA : A.natDegree = 0) (hB : B.natDegree = 0)
    (hC : C0.natDegree = 0) (hD : D0.natDegree = 0)
    (hE : E0.natDegree = 0) (hF : F0.natDegree = 0) :
    (rhoEtaGroupPolynomial810 A B C0 D0 E0 F0).natDegree ≤ 0 := by
  simp only [rhoEtaGroupPolynomial810]
  compute_degree
  omega

set_option maxHeartbeats 16000000 in
theorem rhoThetaGroupPolynomial810_noG0_natDegree_le_zero_of_constants
    {A B C0 D0 E0 : k[X]}
    (hA : A.natDegree = 0) (hB : B.natDegree = 0)
    (hC : C0.natDegree = 0) (hD : D0.natDegree = 0)
    (hE : E0.natDegree = 0) :
    (rhoThetaGroupPolynomial810 A B C0 D0 E0 0).natDegree ≤ 0 := by
  simp only [rhoThetaGroupPolynomial810, zero_mul, mul_zero, zero_smul,
    smul_zero]
  compute_degree
  omega

set_option maxHeartbeats 16000000 in
theorem rhoBaseGroupHighG0Rest810_noG0_natDegree_le_zero_of_constants
    {A B C0 D0 E0 F0 : k[X]}
    (hA : A.natDegree = 0) (hB : B.natDegree = 0)
    (hC : C0.natDegree = 0) (hD : D0.natDegree = 0)
    (hE : E0.natDegree = 0) (hF : F0.natDegree = 0) :
    (rhoBaseGroupHighG0Rest810 0 A B C0 D0 E0 F0 0).natDegree ≤ 0 := by
  simp only [rhoBaseGroupHighG0Rest810, zero_mul, mul_zero, zero_smul,
    smul_zero]
  compute_degree
  omega

set_option maxHeartbeats 16000000 in
theorem rhoBaseG0LinearCoeff810_natDegree_le_zero_of_constants
    {A B C0 D0 E0 F0 : k[X]}
    (hA : A.natDegree = 0) (hB : B.natDegree = 0)
    (hC : C0.natDegree = 0) (hD : D0.natDegree = 0)
    (hE : E0.natDegree = 0) (hF : F0.natDegree = 0) :
    (rhoBaseG0LinearCoeff810 A B C0 D0 E0 F0).natDegree ≤ 0 := by
  simp only [rhoBaseG0LinearCoeff810]
  compute_degree
  omega

theorem degreeZeroPrimitivePolynomial810_l0_eq_C_add_C_mul_G0
    (beta gamma delta epsilon zeta eta theta : k)
    {A B C0 D0 E0 F0 G0 : k[X]}
    (hA : A.natDegree = 0) (hB : B.natDegree = 0)
    (hC : C0.natDegree = 0) (hD : D0.natDegree = 0)
    (hE : E0.natDegree = 0) (hF : F0.natDegree = 0) :
    ∃ c d : k,
      degreeZeroPrimitivePolynomial810 0 beta gamma delta epsilon zeta
          eta theta A B C0 D0 E0 F0 G0 =
        C c + C d * G0 := by
  have hbeta :=
    rhoBetaGroupPolynomial810_natDegree_le_zero_of_constants hA hB hC hD
      hE hF
  have hgamma :=
    rhoGammaGroupPolynomial810_natDegree_le_zero_of_constants hA hB hC hD
      hE hF
  have hdelta :=
    rhoDeltaGroupPolynomial810_natDegree_le_zero_of_constants hA hB hC hD
      hE hF
  have hepsilon :=
    rhoEpsilonGroupPolynomial810_natDegree_le_zero_of_constants hA hB hC
      hD hE hF
  have hzeta :=
    rhoZetaGroupPolynomial810_natDegree_le_zero_of_constants hA hB hC hD
      hE hF
  have heta :=
    rhoEtaGroupPolynomial810_natDegree_le_zero_of_constants hA hB hC hD
      hE hF
  have htheta0 :=
    rhoThetaGroupPolynomial810_noG0_natDegree_le_zero_of_constants hA hB
      hC hD hE
  have hbase0 :=
    rhoBaseGroupHighG0Rest810_noG0_natDegree_le_zero_of_constants hA hB
      hC hD hE hF
  have hlin0 :=
    rhoBaseG0LinearCoeff810_natDegree_le_zero_of_constants hA hB hC hD hE
      hF
  let pconst : k[X] :=
    rhoBaseGroupHighG0Rest810 0 A B C0 D0 E0 F0 0 +
      beta • rhoBetaGroupPolynomial810 A B C0 D0 E0 F0 +
      gamma • rhoGammaGroupPolynomial810 A B C0 D0 E0 F0 +
      delta • rhoDeltaGroupPolynomial810 A B C0 D0 E0 F0 +
      epsilon • rhoEpsilonGroupPolynomial810 A B C0 D0 E0 F0 +
      zeta • rhoZetaGroupPolynomial810 A B C0 D0 E0 F0 +
      eta • rhoEtaGroupPolynomial810 A B C0 D0 E0 F0 +
      theta • rhoThetaGroupPolynomial810 A B C0 D0 E0 0
  have hpconst :
      pconst.natDegree ≤ 0 := by
    have h1 := hbase0
    have h2 := natDegree_smul_le_of_le810 beta hbeta
    have h3 := natDegree_smul_le_of_le810 gamma hgamma
    have h4 := natDegree_smul_le_of_le810 delta hdelta
    have h5 := natDegree_smul_le_of_le810 epsilon hepsilon
    have h6 := natDegree_smul_le_of_le810 zeta hzeta
    have h7 := natDegree_smul_le_of_le810 eta heta
    have h8 := natDegree_smul_le_of_le810 theta htheta0
    exact natDegree_add8_le810 h1 h2 h3 h4 h5 h6 h7 h8
  have hlinC :
      rhoBaseG0LinearCoeff810 A B C0 D0 E0 F0 =
        C ((rhoBaseG0LinearCoeff810 A B C0 D0 E0 F0).coeff 0) :=
    eq_C_of_natDegree_le_zero hlin0
  have hpC : pconst = C (pconst.coeff 0) :=
    eq_C_of_natDegree_le_zero hpconst
  refine ⟨pconst.coeff 0,
    (rhoBaseG0LinearCoeff810 A B C0 D0 E0 F0).coeff 0 + theta, ?_⟩
  have hprim :
      degreeZeroPrimitivePolynomial810 0 beta gamma delta epsilon zeta
          eta theta A B C0 D0 E0 F0 G0 =
        pconst +
          (rhoBaseG0LinearCoeff810 A B C0 D0 E0 F0 + C theta) * G0 := by
    have hthetaG : theta • G0 = C theta * G0 := by rw [smul_eq_C_mul]
    simp only [degreeZeroPrimitivePolynomial810, pconst]
    rw [rhoBaseGroupPolynomial810_l0_eq_noG0_add_linear,
      rhoThetaGroupPolynomial810_eq_noG0_add_G0, smul_add, hthetaG]
    have hdist :
        (rhoBaseG0LinearCoeff810 A B C0 D0 E0 F0 + C theta) * G0 =
          rhoBaseG0LinearCoeff810 A B C0 D0 E0 F0 * G0 + C theta * G0 :=
      add_mul _ _ _
    rw [hdist]
    abel
  rw [hprim]
  conv_lhs => rw [hpC, hlinC]
  rw [← C_add]

theorem uniqueHighG0DegGtOne_l0_impossible
    (beta gamma delta epsilon zeta eta theta j : k)
    (A B C0 D0 E0 F0 G0 : k[X]) (hj : j ≠ 0)
    (hcone : UniqueHighG0DegGtOneL0Cone810 A B C0 D0 E0 F0 G0)
    (hder :
      derivative
          (degreeZeroPrimitivePolynomial810 0 beta gamma delta epsilon
            zeta eta theta A B C0 D0 E0 F0 G0) =
        C j) :
    False := by
  rcases hcone with ⟨hG, hA, hB, hC, hD, hE, hF⟩
  obtain ⟨c, d, hform⟩ :=
    degreeZeroPrimitivePolynomial810_l0_eq_C_add_C_mul_G0 beta gamma
      delta epsilon zeta eta theta hA hB hC hD hE hF
  have hder' : C d * G0.derivative = C j := by
    have hcongr := congrArg derivative hform
    have : derivative (C c + C d * G0) = C j := hcongr.symm.trans hder
    simpa [derivative_add, derivative_C, derivative_C_mul] using this
  have hdne : d ≠ 0 := by
    intro hd0
    have : C j = 0 := by
      simpa [hd0, zero_mul] using hder'.symm
    exact hj (C_eq_zero.mp this)
  have hGder : G0.derivative = C (j / d) := by
    have hleft : C d⁻¹ * (C d * G0.derivative) = G0.derivative := by
      rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ hdne, C_1, one_mul]
    have hright : C d⁻¹ * C j = C (j / d) := by
      rw [← C_mul, div_eq_inv_mul, mul_comm]
    have hscale := congrArg (fun p : k[X] => C d⁻¹ * p) hder'
    exact hleft.symm.trans (hscale.trans hright)
  have hGdeg :
      G0.natDegree = 1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C810 G0 (j / d)
      (div_ne_zero hj hdne) hGder
  omega

end ExhaustG0Affine810


/-! ## Source-facing exhaustion -/

section ExhaustClosed810

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- Remaining cones after this file's named unique faces and Newton
ties.  Unique-`G₀` of degree greater than one with `l = 0` is empty:
the primitive is affine in `G₀`, so `d ρ = C j` forces `deg G₀ = 1`.
Unique-`G₀` of degree one on a source-mapped core is empty by the
parent `uniqueHighG0DegOne_existsPrimitive_false`.  Named leftover:
unique-`G₀` of degree one on mixed-residual letters whose source maps
were dropped by the parent residual, and mixed supports of three or
more nonconstant letters that are not a named unique face or Newton
tie.  The next unused row is the degree-one Jacobian coefficient
already spent on the mapped unique-`G₀` degree-one chamber.  The
theorems `normalized810ScaleZero_impossible` and
`planeKeller810ScaleZeroExclusion_closed` are not claimed. -/
theorem normalized810ScaleZero_coneExhaustionResidual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    ∃ (t j lambda cleared l beta gamma delta epsilon zeta eta theta
        cXi cMu cOm : k) (A B C0 D0 E0 F0 G0 : k[X]),
      t ≠ 0 ∧
      j ≠ 0 ∧
      j / t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      derivative
          (degreeZeroPrimitivePolynomial810 l beta gamma delta epsilon
            zeta eta theta A B C0 D0 E0 F0 G0) =
        Polynomial.C (j / t) ∧
      (degreeZeroXiPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0 ∧
      (degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0 ∧
      (degreeZeroOmicronPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0 ∧
      ¬ ARatioLeadsXiCone810 A B C0 D0 E0 F0 G0 ∧
      (UniqueHighG0DegOneCone810 A B C0 D0 E0 F0 G0 → l = 0) ∧
      ¬ B5LeadsMixedAPosCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ AB23RatioTieCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ C03LeadsMixedAPosCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ C03LeadsMixedBPosCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ D03LeadsMixedAPosCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ E02LeadsMixedCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ F02LeadsMixedCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ C0D0RatioTieCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ UniqueG0WithBCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ AMaximalCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ BLeadsOmicronCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ C0LeadsMuCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ D0LeadsOmicronCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ E0LeadsMuCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ F0LeadsXiCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ (A.natDegree = 0 ∧ B.natDegree = 0 ∧ C0.natDegree = 0 ∧
          D0.natDegree = 0 ∧ E0.natDegree = 0 ∧ F0.natDegree = 0 ∧
          G0.natDegree = 0) ∧
      ¬ UniqueHighG0DegGtOneL0Cone810 A B C0 D0 E0 F0 G0 ∧
      ¬ A6BLeadsOmicronCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ A6LeadsMuMixedBCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ A6LeadsMuMixedC0Cone810 A B C0 D0 E0 F0 G0 ∧
      ¬ A6LeadsMuMixedD0Cone810 A B C0 D0 E0 F0 G0 ∧
      ¬ AC02RatioTieCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ ABC0RatioTieCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ AE03RatioTieCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ AE06RatioTieCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ BE02RatioTieCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ AD05RatioTieCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ C0E0RatioTieCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ AF07RatioTieCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ BD03RatioTieCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ BC03RatioTieCone810 A B C0 D0 E0 F0 G0 := by
  obtain ⟨t, j, lambda, cleared, l, beta, gamma, delta, epsilon, zeta, eta,
      theta, cXi, cMu, cOm, A, B, C0, D0, E0, F0, G0, ht, hj, hjdiv, hHsq,
      hder, hxi, hmu, hom, hARatio, hG0l, hB5, hAB, hCA, hCB, hDA, hE,
      hF, hCD, hGB⟩ :=
    normalized810ScaleZero_coneMixedResidual hsource
  refine ⟨t, j, lambda, cleared, l, beta, gamma, delta, epsilon, zeta, eta,
    theta, cXi, cMu, cOm, A, B, C0, D0, E0, F0, G0, ht, hj, hjdiv, hHsq,
    hder, hxi, hmu, hom, hARatio, hG0l, hB5, hAB, hCA, hCB, hDA, hE, hF,
    hCD, hGB, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hAmax
    exact xi_A7_impossible_of_A_maximal l beta gamma delta epsilon zeta
      eta theta A B C0 D0 E0 F0 G0 hAmax hxi
  · intro hBleads
    exact omicron_B5_impossible_of_B_leads l beta gamma delta epsilon
      zeta eta theta A B C0 D0 E0 F0 G0 hBleads hom
  · intro hCleads
    exact mu_C03_impossible_of_C0_leads l beta gamma delta epsilon zeta
      eta theta A B C0 D0 E0 F0 G0 hCleads hmu
  · intro hDleads
    exact omicron_D03_impossible_of_D0_leads l beta gamma delta epsilon
      zeta eta theta A B C0 D0 E0 F0 G0 hDleads hom
  · intro hEleads
    exact mu_E02_impossible_of_E0_leads l beta gamma delta epsilon zeta
      eta theta A B C0 D0 E0 F0 G0 hEleads hmu
  · intro hFleads
    exact xi_F02_impossible_of_F0_leads l beta gamma delta epsilon zeta
      eta theta A B C0 D0 E0 F0 G0 hFleads hxi
  · intro hconst
    exact degreeZeroPrimitivePolynomial810_false_of_constant_core l
      beta gamma delta epsilon zeta eta theta (j / t) A B C0 D0 E0 F0
      G0 hjdiv hconst.1 hconst.2.1 hconst.2.2.1 hconst.2.2.2.1
      hconst.2.2.2.2.1 hconst.2.2.2.2.2.1 hconst.2.2.2.2.2.2 hder
  · intro hGgt
    have hl0 : l = 0 := by
      by_contra hlne
      have hGpos : 0 < G0.natDegree := Nat.lt_trans (by decide) hGgt.1
      exact uniqueNonconstantG0_impossible_of_l_ne l beta gamma delta
        epsilon zeta eta theta (j / t) A B C0 D0 E0 F0 G0 hlne hjdiv
        hGgt.2.1 hGgt.2.2.1 hGgt.2.2.2.1 hGgt.2.2.2.2.1
        hGgt.2.2.2.2.2.1 hGgt.2.2.2.2.2.2 hGpos hder
    subst hl0
    exact uniqueHighG0DegGtOne_l0_impossible beta gamma delta epsilon
      zeta eta theta (j / t) A B C0 D0 E0 F0 G0 hjdiv hGgt hder
  · intro hA6B
    exact mu_A6_impossible_of_A6B l beta gamma delta epsilon zeta eta
      theta A B C0 D0 E0 F0 G0 hA6B hmu
  · intro hA6Bm
    exact mu_A6_impossible_of_mixedB l beta gamma delta epsilon zeta
      eta theta A B C0 D0 E0 F0 G0 hA6Bm hmu
  · intro hA6C
    exact mu_A6_impossible_of_mixedC0 l beta gamma delta epsilon zeta
      eta theta A B C0 D0 E0 F0 G0 hA6C hmu
  · intro hA6D
    exact mu_A6_impossible_of_mixedD0 l beta gamma delta epsilon zeta
      eta theta A B C0 D0 E0 F0 G0 hA6D hmu
  · intro hAC02
    exact mu_xi_AC02_impossible l beta gamma delta epsilon zeta eta
      theta A B C0 D0 E0 F0 G0 hAC02 hmu hxi
  · intro hABC0
    exact mu_xi_ABC0_impossible l beta gamma delta epsilon zeta eta
      theta A B C0 D0 E0 F0 G0 hABC0 hmu hxi
  · intro hAE03
    exact mu_A6_impossible_of_AE03 l beta gamma delta epsilon zeta eta
      theta A B C0 D0 E0 F0 G0 hAE03 hmu
  · intro hAE06
    exact mu_xi_AE06_impossible l beta gamma delta epsilon zeta eta
      theta A B C0 D0 E0 F0 G0 hAE06 hmu hxi
  · intro hBE02
    exact mu_omicron_BE02_impossible l beta gamma delta epsilon zeta
      eta theta A B C0 D0 E0 F0 G0 hBE02 hmu hom
  · intro hAD05
    exact mu_xi_AD05_impossible l beta gamma delta epsilon zeta eta
      theta A B C0 D0 E0 F0 G0 hAD05 hmu hxi
  · intro hC0E0
    exact xi_C0E0_impossible l beta gamma delta epsilon zeta eta theta
      A B C0 D0 E0 F0 G0 hC0E0 hxi
  · intro hAF07
    exact mu_A6_impossible_of_AF07 l beta gamma delta epsilon zeta eta
      theta A B C0 D0 E0 F0 G0 hAF07 hmu
  · intro hBD03
    exact mu_B4_impossible_of_BD03 l beta gamma delta epsilon zeta eta
      theta A B C0 D0 E0 F0 G0 hBD03 hmu
  · intro hBC03
    exact mu_C03_impossible_of_BC03 l beta gamma delta epsilon zeta
      eta theta A B C0 D0 E0 F0 G0 hBC03 hmu

theorem normalized810ScaleZero_impossible_of_exhaustionResidual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0)
    (hres :
      (∃ (t j lambda cleared l beta gamma delta epsilon zeta eta theta
          cXi cMu cOm : k) (A B C0 D0 E0 F0 G0 : k[X]),
        t ≠ 0 ∧ j ≠ 0 ∧ j / t ≠ 0 ∧ H = (Polynomial.C t) ^ 2 ∧
          derivative
              (degreeZeroPrimitivePolynomial810 l beta gamma delta
                epsilon zeta eta theta A B C0 D0 E0 F0 G0) =
            Polynomial.C (j / t) ∧
          (degreeZeroXiPolynomial810 l beta gamma delta epsilon zeta eta
              theta A B C0 D0 E0 F0 G0).natDegree =
            0 ∧
          (degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta
              theta A B C0 D0 E0 F0 G0).natDegree =
            0 ∧
          (degreeZeroOmicronPolynomial810 l beta gamma delta epsilon zeta
              eta theta A B C0 D0 E0 F0 G0).natDegree =
            0 ∧
          ¬ ARatioLeadsXiCone810 A B C0 D0 E0 F0 G0 ∧
          (UniqueHighG0DegOneCone810 A B C0 D0 E0 F0 G0 → l = 0) ∧
          ¬ B5LeadsMixedAPosCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ AB23RatioTieCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ C03LeadsMixedAPosCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ C03LeadsMixedBPosCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ D03LeadsMixedAPosCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ E02LeadsMixedCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ F02LeadsMixedCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ C0D0RatioTieCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ UniqueG0WithBCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ AMaximalCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ BLeadsOmicronCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ C0LeadsMuCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ D0LeadsOmicronCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ E0LeadsMuCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ F0LeadsXiCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ (A.natDegree = 0 ∧ B.natDegree = 0 ∧ C0.natDegree = 0 ∧
              D0.natDegree = 0 ∧ E0.natDegree = 0 ∧ F0.natDegree = 0 ∧
              G0.natDegree = 0) ∧
          ¬ UniqueHighG0DegGtOneL0Cone810 A B C0 D0 E0 F0 G0 ∧
          ¬ A6BLeadsOmicronCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ A6LeadsMuMixedBCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ A6LeadsMuMixedC0Cone810 A B C0 D0 E0 F0 G0 ∧
          ¬ A6LeadsMuMixedD0Cone810 A B C0 D0 E0 F0 G0 ∧
          ¬ AC02RatioTieCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ ABC0RatioTieCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ AE03RatioTieCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ AE06RatioTieCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ BE02RatioTieCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ AD05RatioTieCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ C0E0RatioTieCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ AF07RatioTieCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ BD03RatioTieCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ BC03RatioTieCone810 A B C0 D0 E0 F0 G0) →
        False) :
    False :=
  hres (normalized810ScaleZero_coneExhaustionResidual hsource)

end ExhaustClosed810

#print axioms mu_xi_AC02_inner_identity
#print axioms mu_A6_impossible_of_A6B
#print axioms mu_xi_AC02_impossible
#print axioms mu_xi_AE06_impossible
#print axioms mu_omicron_BE02_impossible
#print axioms mu_xi_AD05_impossible
#print axioms uniqueHighG0DegGtOne_l0_impossible
#print axioms muAC02Combined810_natDegree_eq_of_coeff_ne
#print axioms normalized810ScaleZero_coneExhaustionResidual
#print axioms normalized810ScaleZero_impossible_of_exhaustionResidual


end Max11DegreeRoutes
