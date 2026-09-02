import Grok68GammaActiveInventoryScratch

/-! # Loaded uniform row one on the gamma-active `(6,8)` cell

Untracked working note. No tracked file was edited.

The parent inventory
`FiveToSixCuspZetaFirstGammaActiveInventoryResidual68` has exact cusp
edges, `H_(9N-2G-S)=0`, the `Q` leading, and the two-case `F`
profile.  This file consumes the named next unused row: loaded uniform
row one, equally the first coefficient of `Y` against `A F'`.

CAS `derive_68_gamma_active_leadings.py` (row-one extension) records
that compensated I3 remainder
`Rc=-(9/4)ε c+(3/4)γ B²+const` has degree `≤4N-G`, so `A Rc'` and the
`H`-support extra in residual row one sit strictly below both
homogeneous `Y` tops on every gamma-active lattice point, independently
of `(γ,ε)`.  The first coefficient of `Y` against `A F'` is therefore
the `Y` top itself:

* `G<2S`: top `12N-3G` is `AB²c,c³`.  `Y+2c·cusp=8c³=0`, `False`.
* `G>2S`: top `12N-2G-2S` is `Ad²,e²`.  With `H` and the cusp,
  `d²(a b²-3c²)=0` and `a b²-3c²=-6c²`, `False`.
* `G=2S`: all four edges share `12N-6S`.  Cusp, `H`, and `Y` give
  `4 B_D² c_Cc=9 d_V²`, not `e⁴` (that still needs `J=Q-3de`).

The `F` dichotomy does not reach this top.  Both `γ=0` and `γ≠0`
die on `G≠2S` and survive together on `G=2S`.

This file does not claim
`fiveToSix_zetaFirst_gammaActive_false68 : False`.

Exact gain: the two off-wall `Y` chambers are `False`; the `G=2S`
gamma-active cell is replaced by the named residual below.
Next unused row: loaded uniform row two at `11N-2G-2S-1` (on `G=2S`,
the common top of `Q` and `de`).
Residual: `FiveToSixCuspZetaFirstGammaActiveRowOneResidual68`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointGammaActiveRowOne68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

/-! ## Scalar leading-jet identities -/

/-- `Y_AB²c` and the cusp cannot vanish together.  CAS:
`Y_AB2c+2c*cusp=8c³`. -/
theorem fiveToSix_gammaActive_Y_AB2c_leading_false68
    (a b c : k) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hcusp : a * b ^ 2 + (3 : k) * c ^ 2 = 0)
    (hY : -(2 : k) * a * b ^ 2 * c + (2 : k) * c ^ 3 = 0) :
    False := by
  have h8 : (8 : k) * c ^ 3 = 0 := by
    linear_combination hY + (2 : k) * c * hcusp
  have h8ne : (8 : k) ≠ 0 := by norm_num
  exact hc (eq_zero_of_pow_eq_zero ((mul_eq_zero.mp h8).resolve_left h8ne))

/-- `Y_Ade`, the cusp, and `H` cannot vanish together.  CAS:
`d²(ab²-3c²)=3(b²e²-c²d²)` on `ad²=3e²`, and `ab²-3c²=-6c²`. -/
theorem fiveToSix_gammaActive_Y_Ade_leading_false68
    (a b c d e : k)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (hcusp : a * b ^ 2 + (3 : k) * c ^ 2 = 0)
    (hH : b * e + c * d = 0)
    (hY : (3 : k) * a * d ^ 2 - (9 : k) * e ^ 2 = 0) :
    False := by
  have hY' : a * d ^ 2 - (3 : k) * e ^ 2 = 0 := by
    linear_combination (1 / 3 : k) * hY
  have hsq : b ^ 2 * e ^ 2 = c ^ 2 * d ^ 2 := by
    calc
      b ^ 2 * e ^ 2 = (b * e) ^ 2 := by ring
      _ = (-(c * d)) ^ 2 := by rw [add_eq_zero_iff_eq_neg.mp hH]
      _ = (c * d) ^ 2 := by ring
      _ = c ^ 2 * d ^ 2 := by ring
  have hprod : d ^ 2 * (a * b ^ 2 - (3 : k) * c ^ 2) = 0 := by
    calc
      d ^ 2 * (a * b ^ 2 - (3 : k) * c ^ 2) =
          a * d ^ 2 * b ^ 2 - (3 : k) * c ^ 2 * d ^ 2 := by ring
      _ = (3 : k) * e ^ 2 * b ^ 2 - (3 : k) * c ^ 2 * d ^ 2 := by
        rw [eq_of_sub_eq_zero hY']
      _ = (3 : k) * (b ^ 2 * e ^ 2 - c ^ 2 * d ^ 2) := by ring
      _ = 0 := by rw [hsq, sub_self, mul_zero]
  have hdiff : a * b ^ 2 - (3 : k) * c ^ 2 = -((6 : k) * c ^ 2) := by
    linear_combination hcusp
  have h6 : (6 : k) ≠ 0 := by norm_num
  have hd2 : d ^ 2 = 0 := by
    have hne : a * b ^ 2 - (3 : k) * c ^ 2 ≠ 0 := by
      rw [hdiff]
      exact neg_ne_zero.mpr (mul_ne_zero h6 (pow_ne_zero 2 hc))
    exact (mul_eq_zero.mp hprod).resolve_right hne
  exact hd (eq_zero_of_pow_eq_zero hd2)

/-- On `G=2S` the three scalars `cusp`, `H`, `Y` reduce to
`4 b² c=9 d²`.  Not a closure: Groebner does not contain `e⁴`. -/
theorem fiveToSix_gammaActive_Y_G2S_reduced68
    (a b c d e : k)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (hcusp : a * b ^ 2 + (3 : k) * c ^ 2 = 0)
    (hH : b * e + c * d = 0)
    (hY : -(2 : k) * a * b ^ 2 * c + (3 : k) * a * d ^ 2 +
        (2 : k) * c ^ 3 - (9 : k) * e ^ 2 = 0) :
    (4 : k) * b ^ 2 * c - (9 : k) * d ^ 2 = 0 := by
  have hYred : (3 : k) * a * d ^ 2 + (8 : k) * c ^ 3 -
      (9 : k) * e ^ 2 = 0 := by
    linear_combination hY + (2 : k) * c * hcusp
  have hsq : b ^ 2 * e ^ 2 = c ^ 2 * d ^ 2 := by
    calc
      b ^ 2 * e ^ 2 = (b * e) ^ 2 := by ring
      _ = (-(c * d)) ^ 2 := by rw [add_eq_zero_iff_eq_neg.mp hH]
      _ = (c * d) ^ 2 := by ring
      _ = c ^ 2 * d ^ 2 := by ring
  have had : a * d ^ 2 + (3 : k) * e ^ 2 = 0 := by
    have hprod :
        c ^ 2 * d ^ 2 * (a * d ^ 2 + (3 : k) * e ^ 2) = 0 := by
      calc
        c ^ 2 * d ^ 2 * (a * d ^ 2 + (3 : k) * e ^ 2) =
            a * d ^ 2 * (c ^ 2 * d ^ 2) +
              (3 : k) * c ^ 2 * d ^ 2 * e ^ 2 := by ring
        _ = a * d ^ 2 * (b ^ 2 * e ^ 2) +
              (3 : k) * c ^ 2 * d ^ 2 * e ^ 2 := by rw [hsq]
        _ = (a * b ^ 2 + (3 : k) * c ^ 2) * d ^ 2 * e ^ 2 := by ring
        _ = 0 := by rw [hcusp, zero_mul, zero_mul]
    have hcd2 : c ^ 2 * d ^ 2 ≠ 0 :=
      mul_ne_zero (pow_ne_zero 2 hc) (pow_ne_zero 2 hd)
    exact (mul_eq_zero.mp hprod).resolve_left hcd2
  have h8 : (8 : k) * c ^ 3 - (18 : k) * e ^ 2 = 0 := by
    linear_combination hYred - (3 : k) * had
  have h4c3 : (4 : k) * c ^ 3 - (9 : k) * e ^ 2 = 0 := by
    linear_combination (1 / 2 : k) * h8
  have hprod : c ^ 2 * ((4 : k) * b ^ 2 * c - (9 : k) * d ^ 2) = 0 := by
    calc
      c ^ 2 * ((4 : k) * b ^ 2 * c - (9 : k) * d ^ 2) =
          (4 : k) * c ^ 3 * b ^ 2 - (9 : k) * c ^ 2 * d ^ 2 := by ring
      _ = (9 : k) * e ^ 2 * b ^ 2 - (9 : k) * c ^ 2 * d ^ 2 := by
        rw [eq_of_sub_eq_zero h4c3]
      _ = (9 : k) * (b ^ 2 * e ^ 2 - c ^ 2 * d ^ 2) := by ring
      _ = 0 := by rw [hsq, sub_self, mul_zero]
  exact (mul_eq_zero.mp hprod).resolve_left (pow_ne_zero 2 hc)

/-! ## Degree dictionary for row one -/

/-- Remainder of loaded uniform row one versus both homogeneous `Y`
tops.  Window arithmetic forces `A Rc'`, the `H`-support extra, and
every leftover `(γ,ε)` load strictly below `12N-3G-1` and
`12N-2G-2S-1`. -/
theorem fiveToSix_gammaActive_rowOne_degree_arith68
    (N G S : ℕ) (hN : 0 < N) (hgt : 5 * N < 2 * G) (hle : 2 * G ≤ 6 * N)
    (hS : 0 < S) (hSR : S < 7 * N - 2 * G) (hGamma : 4 * N - G ≤ S) :
    let D := 3 * N - G
    let Cc := 4 * N - G
    let V := 5 * N - G - S
    let E := 6 * N - G - S
    let TY0 := 12 * N - 3 * G
    let TY1 := 12 * N - 2 * G - 2 * S
    0 < D ∧ 0 < Cc ∧ 0 < V ∧ 0 < E ∧ S < G ∧ S ≤ G ∧
      2 * D ≤ Cc ∧
      2 * N + Cc - 1 < TY0 - 1 ∧
      2 * D + E - 1 < TY0 - 1 ∧
      2 * D + E - 1 < TY1 - 1 ∧
      2 * Cc - 1 < TY0 - 1 ∧
      2 * Cc - 1 < TY1 - 1 ∧
      D + V - 1 < TY0 - 1 ∧
      D + V - 1 < TY1 - 1 ∧
      2 * N + 2 * D - 1 < TY0 - 1 ∧
      2 * N + 2 * D - 1 < TY1 - 1 ∧
      E - 1 < TY0 - 1 ∧
      E - 1 < TY1 - 1 ∧
      (2 * S ≤ G → 2 * N + Cc - 1 < TY1 - 1) ∧
      12 * N - 2 * G - S - (G - S) - 1 = TY0 - 1 ∧
      12 * N - 2 * G - S - S - 1 = TY1 - 1 ∧
      1 ≤ TY0 ∧ 1 ≤ TY1 ∧ 1 ≤ Cc := by
  omega

/-! ## Degree helpers -/

private theorem natDegree_mul_derivative_le_gammaActive68
    (p q : k[X]) (u v : ℕ)
    (hu : p.natDegree ≤ u) (hv : 0 < v) (hq : q.natDegree ≤ v) :
    (p * derivative q).natDegree ≤ u + v - 1 := by
  have hd : (derivative q).natDegree ≤ v - 1 :=
    (natDegree_derivative_le q).trans (by omega)
  have hmul := natDegree_mul_le.trans (Nat.add_le_add hu hd)
  omega

private theorem natDegree_derivative_mul_le_gammaActive68
    (p q : k[X]) (u v : ℕ)
    (hu : 0 < u) (hp : p.natDegree ≤ u) (hq : q.natDegree ≤ v) :
    (derivative p * q).natDegree ≤ u + v - 1 := by
  have hd : (derivative p).natDegree ≤ u - 1 :=
    (natDegree_derivative_le p).trans (by omega)
  have hmul := natDegree_mul_le.trans (Nat.add_le_add hd hq)
  omega

/-! ## Compensated I3 remainder and residual extra -/

/-- `H`-support extra in residual row one, strictly below both `Y`
tops on a gamma-active cell. -/
def FiveToSixCuspZetaFirstGammaActiveRowOneExtra68
    (A B c d e : k[X]) : k[X] :=
  -(3 : k) • (B ^ 2 * derivative e) +
    (3 : k) • (B * c * derivative d) +
    (3 : k) • (B * derivative c * d) +
    (9 : k) • (derivative B * c * d)

theorem secondaryResidualRowOnePolynomial68_core_extra68
    (A B c d e : k[X]) :
    secondaryResidualRowOnePolynomial68 A B c d e =
      (-4 / 27 : k) •
        (FiveToSixCuspZetaFirstB3EndpointRowOneCore68 A B c d e +
          FiveToSixCuspZetaFirstGammaActiveRowOneExtra68 A B c d e) := by
  unfold secondaryResidualRowOnePolynomial68
    FiveToSixCuspZetaFirstB3EndpointRowOneCore68
    FiveToSixCuspZetaFirstGammaActiveRowOneExtra68
  congr 1
  module

/-- Compensated I3 remainder on a gamma-active cell. -/
theorem fiveToSix_zetaFirst_gammaActive_Rc_polynomial68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hgamma : FiveToSixCuspZetaFirstGammaActiveResidual68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S) :
    ∃ i3 : k,
      (-(A * B * d) + (3 : k) • (c * e) - B ^ 2 * c +
          (3 / 2 : k) • d ^ 2) + (9 / 2 * gamma : k) • e =
        -(9 / 4 * epsilon : k) • c + (3 / 4 * gamma : k) • B ^ 2 +
          (9 / 8 : k) • C i3 := by
  have hs :=
    fiveToSix_zetaFirst_support_of_gammaActive68 alpha gamma epsilon zeta
      eta terminal A B c d e N G S hgamma
  rcases fiveToSix_zetaFirst_B3_compensatedI3_polynomial68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs with
      ⟨i3, hi3⟩
  refine ⟨i3, ?_⟩
  simp only [neg_smul]
  linear_combination hi3

theorem fiveToSix_zetaFirst_gammaActive_rowOne_core_Rc68
    (gamma : k) (A B c d e : k[X]) :
    let F := (-(A * B * d) + (3 : k) • (c * e)) - B ^ 2 * c +
      (3 / 2 : k) • d ^ 2
    let Rc := F + (9 / 2 * gamma : k) • e
    let Y := -(2 : k) • (A * B ^ 2 * c) + (3 : k) • (A * d ^ 2) +
      (2 : k) • c ^ 3 - (9 : k) • e ^ 2
    FiveToSixCuspZetaFirstB3EndpointRowOneCore68 A B c d e -
        (9 * gamma : k) • (A * derivative e) =
      -(2 : k) • (A * derivative Rc) + derivative Y := by
  intro F Rc Y
  have hfactor :=
    fiveToSix_zetaFirst_B3_endpoint_rowOne_core_factor68 (k := k) A B c d e
  rw [hfactor]
  dsimp only [Rc, F]
  simp only [derivative_add, derivative_smul, mul_add, mul_smul_comm,
    smul_mul_assoc, smul_add, smul_sub, smul_smul]
  module

theorem fiveToSix_zetaFirst_gammaActive_rowOne_cancelled68
    (gamma : k) (A B c d e : k[X]) :
    let F := (-(A * B * d) + (3 : k) • (c * e)) - B ^ 2 * c +
      (3 / 2 : k) • d ^ 2
    let Rc := F + (9 / 2 * gamma : k) • e
    let Y := -(2 : k) • (A * B ^ 2 * c) + (3 : k) • (A * d ^ 2) +
      (2 : k) • c ^ 3 - (9 : k) • e ^ 2
    let Extra := FiveToSixCuspZetaFirstGammaActiveRowOneExtra68 A B c d e
    secondaryResidualRowOnePolynomial68 A B c d e +
        (4 / 3 * gamma : k) • (A * derivative e) =
      (-4 / 27 : k) •
        (derivative Y - (2 : k) • (A * derivative Rc) + Extra) := by
  intro F Rc Y Extra
  have hcore :=
    secondaryResidualRowOnePolynomial68_core_extra68 A B c d e
  have hfactor :=
    fiveToSix_zetaFirst_gammaActive_rowOne_core_Rc68 gamma A B c d e
  have hC :
      FiveToSixCuspZetaFirstB3EndpointRowOneCore68 A B c d e =
        -(2 : k) • (A * derivative Rc) + derivative Y +
          (9 * gamma : k) • (A * derivative e) := by
    linear_combination hfactor
  rw [hcore, hC]
  dsimp only [Extra]
  module

/-! ## First coefficient of `Y` -/

/-- Loaded uniform row one at a homogeneous `Y` top kills that
coefficient.  The index is `12N-3G-1` on `G<2S` and `12N-2G-2S-1` on
`G≥2S`. -/
theorem fiveToSix_zetaFirst_gammaActive_rowOne_Y_coeff68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S q m K : ℕ)
    (hgamma : FiveToSixCuspZetaFirstGammaActiveResidual68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hidx : 12 * N - 2 * G - S - (q + m) - 1 = K)
    (hK : K + 1 = 12 * N - 3 * G ∨
      K + 1 = 12 * N - 2 * G - 2 * S ∧ 2 * S ≤ G) :
    let Y := -(2 : k) • (A * B ^ 2 * c) + (3 : k) • (A * d ^ 2) +
      (2 : k) • c ^ 3 - (9 : k) • e ^ 2
    Y.coeff (K + 1) = 0 := by
  let F := (-(A * B * d) + (3 : k) • (c * e)) - B ^ 2 * c +
    (3 / 2 : k) • d ^ 2
  let Rc := F + (9 / 2 * gamma : k) • e
  let Y := -(2 : k) • (A * B ^ 2 * c) + (3 : k) • (A * d ^ 2) +
    (2 : k) • c ^ 3 - (9 : k) • e ^ 2
  let Extra := FiveToSixCuspZetaFirstGammaActiveRowOneExtra68 A B c d e
  let D := 3 * N - G
  let Cc := 4 * N - G
  let V := 5 * N - G - S
  let E := 6 * N - G - S
  have hdeg :=
    fiveToSix_zetaFirst_gammaActive_exact_degrees68 alpha gamma epsilon
      zeta eta terminal A B c d e N G S hgamma
  rcases hdeg with
    ⟨hN, hS, hgt, hle, hSR, hGamma, hDpos, hCpos, hVpos, hEpos, hSltG, _,
      hAdeg, hBdeg, hcdeg, hddeg, hedeg, _, _, _, _, _, _, hs⟩
  have harith :=
    fiveToSix_gammaActive_rowOne_degree_arith68 N G S hN hgt hle hS hSR
      hGamma
  rcases harith with
    ⟨_, _, _, _, _, _, h2DleC, hARc0, hEx0, hEx1, hcc0, hcc1,
      hBd0, hBd1, hAB0, hAB1, he0, he1, hARc1of, _, _, hTY0pos, hTY1pos,
      hCcpos⟩
  have hA' : A.natDegree ≤ 2 * N := hAdeg.le
  have hB' : B.natDegree ≤ D := hBdeg.le
  have hc' : c.natDegree ≤ Cc := hcdeg.le
  have hd' : d.natDegree ≤ V := hddeg.le
  have he' : e.natDegree ≤ E := hedeg.le
  rcases fiveToSix_zetaFirst_gammaActive_Rc_polynomial68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S hgamma with ⟨i3, hRc⟩
  have hRcdeg : Rc.natDegree ≤ Cc := by
    dsimp only [Rc, F]
    rw [hRc]
    compute_degree
    omega
  have hdRc : (derivative Rc).natDegree ≤ Cc - 1 := by
    have := natDegree_derivative_le Rc
    omega
  have hARcdeg : (A * derivative Rc).natDegree ≤ 2 * N + Cc - 1 := by
    have hmul :=
      natDegree_mul_le.trans (Nat.add_le_add hA' hdRc)
    have hsum : 2 * N + (Cc - 1) = 2 * N + Cc - 1 := by omega
    rwa [hsum] at hmul
  have hB2deg : (B ^ 2).natDegree ≤ 2 * D := by
    compute_degree
    omega
  have hBcdeg : (B * c).natDegree ≤ D + Cc :=
    natDegree_mul_le.trans (Nat.add_le_add hB' hc')
  have hEx1deg :
      (B ^ 2 * derivative e).natDegree ≤ 2 * D + E - 1 :=
    natDegree_mul_derivative_le_gammaActive68 (B ^ 2) e (2 * D) E hB2deg
      (by omega) he'
  have hEx2deg :
      (B * c * derivative d).natDegree ≤ D + Cc + V - 1 := by
    have h :=
      natDegree_mul_derivative_le_gammaActive68 (B * c) d (D + Cc) V
        hBcdeg (by omega) hd'
    have hsum : D + Cc + V - 1 = D + Cc + V - 1 := rfl
    simpa [mul_assoc] using h
  have hEx3deg :
      (B * derivative c * d).natDegree ≤ D + Cc + V - 1 := by
    have hBc' :
        (B * derivative c).natDegree ≤ D + Cc - 1 :=
      natDegree_mul_derivative_le_gammaActive68 B c D Cc hB' (by omega) hc'
    have h := natDegree_mul_le.trans (Nat.add_le_add hBc' hd')
    have hsum : D + Cc - 1 + V = D + Cc + V - 1 := by omega
    rwa [hsum] at h
  have hEx4deg :
      (derivative B * c * d).natDegree ≤ D + Cc + V - 1 := by
    have hBc' :
        (derivative B * c).natDegree ≤ D + Cc - 1 :=
      natDegree_derivative_mul_le_gammaActive68 B c D Cc (by omega) hB'
        hc'
    have h := natDegree_mul_le.trans (Nat.add_le_add hBc' hd')
    have hsum : D + Cc - 1 + V = D + Cc + V - 1 := by omega
    rwa [hsum] at h
  have hExdeg : Extra.natDegree ≤ 2 * D + E - 1 := by
    dsimp only [Extra, FiveToSixCuspZetaFirstGammaActiveRowOneExtra68]
    have h1 : 2 * D + E - 1 = 2 * D + E - 1 := rfl
    have h2 : D + Cc + V - 1 = 2 * D + E - 1 := by
      dsimp only [D, Cc, V, E]; omega
    compute_degree
    omega
  have hccdeg : (c * derivative c).natDegree ≤ 2 * Cc - 1 := by
    have h :=
      natDegree_mul_derivative_le_gammaActive68 c c Cc Cc hc' (by omega)
        hc'
    have hsum : Cc + Cc - 1 = 2 * Cc - 1 := by omega
    rwa [hsum] at h
  have hB2deg' : (B ^ 2).natDegree ≤ 2 * D := hB2deg
  have hAB2deg :
      (derivative A * B ^ 2).natDegree ≤ 2 * N + 2 * D - 1 :=
    natDegree_derivative_mul_le_gammaActive68 A (B ^ 2) (2 * N) (2 * D)
      (by omega) hA' hB2deg'
  have hBddeg : (B * derivative d).natDegree ≤ D + V - 1 :=
    natDegree_mul_derivative_le_gammaActive68 B d D V hB' (by omega) hd'
  have hdBdeg : (d * derivative B).natDegree ≤ D + V - 1 := by
    have h :=
      natDegree_derivative_mul_le_gammaActive68 B d D V (by omega) hB' hd'
    simpa [mul_comm] using h
  have hAcdeg : (A * derivative c).natDegree ≤ 2 * N + Cc - 1 :=
    natDegree_mul_derivative_le_gammaActive68 A c (2 * N) Cc hA' (by omega)
      hc'
  have hedeg' : (derivative e).natDegree ≤ E - 1 :=
    (natDegree_derivative_le e).trans (by omega)
  have hARclt : (A * derivative Rc).natDegree < K := by
    rcases hK with h0 | ⟨h1, hleGS⟩
    · omega
    · have := hARc1of hleGS; omega
  have hExlt : Extra.natDegree < K := by
    rcases hK with h0 | ⟨h1, _⟩
    · omega
    · omega
  have hcclt : (c * derivative c).natDegree < K := by
    rcases hK with h0 | ⟨h1, _⟩
    · omega
    · omega
  have hAB2lt : (derivative A * B ^ 2).natDegree < K := by
    rcases hK with h0 | ⟨h1, _⟩
    · omega
    · omega
  have hBdlt : (B * derivative d).natDegree < K := by
    rcases hK with h0 | ⟨h1, _⟩
    · omega
    · omega
  have hdBlt : (d * derivative B).natDegree < K := by
    rcases hK with h0 | ⟨h1, _⟩
    · omega
    · omega
  have hAclt : (A * derivative c).natDegree < K := by
    rcases hK with h0 | ⟨h1, hleGS⟩
    · omega
    · have := hARc1of hleGS; omega
  have helt : (derivative e).natDegree < K := by
    rcases hK with h0 | ⟨h1, _⟩
    · omega
    · omega
  have hrow :=
    fiveToSix_zetaFirst_loaded_uniform_rowOne68 alpha gamma epsilon zeta
      eta terminal A B c d e N G S q m hs
  dsimp only [FiveToSixCuspZetaFirstLoadedUniformRowOneScalar68] at hrow
  rw [hidx] at hrow
  have hcancel :=
    fiveToSix_zetaFirst_gammaActive_rowOne_cancelled68 gamma A B c d e
  have hcancelK :
      (secondaryResidualRowOnePolynomial68 A B c d e +
          (4 / 3 * gamma : k) • (A * derivative e)).coeff K =
        ((-4 / 27 : k) •
          (derivative Y - (2 : k) • (A * derivative Rc) +
            Extra)).coeff K :=
    congrArg (fun p : k[X] => p.coeff K) hcancel
  have hleft :
      (secondaryResidualRowOnePolynomial68 A B c d e +
          (4 / 3 * gamma : k) • (A * derivative e)).coeff K =
        (secondaryResidualRowOnePolynomial68 A B c d e).coeff K +
          (4 / 3 * gamma : k) * (A * derivative e).coeff K := by
    simp only [coeff_add, coeff_smul, smul_eq_mul]
  have hRest0 :
      -(4 / 3 * gamma : k) * (c * derivative c).coeff K +
          (2 / 9 * gamma : k) * (derivative A * B ^ 2).coeff K +
          (2 / 3 * gamma : k) * (B * derivative d).coeff K -
          (2 / 3 * gamma : k) * (d * derivative B).coeff K +
          (2 / 3 * epsilon : k) * (A * derivative c).coeff K +
          (2 * epsilon : k) * (derivative e).coeff K = 0 := by
    simp only [coeff_eq_zero_of_natDegree_lt hcclt,
      coeff_eq_zero_of_natDegree_lt hAB2lt,
      coeff_eq_zero_of_natDegree_lt hBdlt,
      coeff_eq_zero_of_natDegree_lt hdBlt,
      coeff_eq_zero_of_natDegree_lt hAclt,
      coeff_eq_zero_of_natDegree_lt helt, mul_zero, add_zero, sub_zero]
  have hAe :
      (secondaryResidualRowOnePolynomial68 A B c d e).coeff K +
          (4 / 3 * gamma : k) * (A * derivative e).coeff K = 0 := by
    linear_combination hrow - hRest0
  have hYcomb :
      ((-4 / 27 : k) •
          (derivative Y - (2 : k) • (A * derivative Rc) +
            Extra)).coeff K = 0 := by
    rw [← hcancelK, hleft, hAe]
  have hARc0 : (A * derivative Rc).coeff K = 0 :=
    coeff_eq_zero_of_natDegree_lt hARclt
  have hEx0 : Extra.coeff K = 0 :=
    coeff_eq_zero_of_natDegree_lt hExlt
  have hY' : (derivative Y).coeff K = 0 := by
    have hexp :
        ((-4 / 27 : k) •
            (derivative Y - (2 : k) • (A * derivative Rc) +
              Extra)).coeff K =
          (-4 / 27 : k) *
            ((derivative Y).coeff K -
              (2 : k) * (A * derivative Rc).coeff K + Extra.coeff K) := by
      simp only [coeff_add, coeff_sub, coeff_smul, smul_eq_mul]
    rw [hexp, hARc0, hEx0, mul_zero, sub_zero, add_zero] at hYcomb
    have h427 : (-4 / 27 : k) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp hYcomb).resolve_left h427
  have hder : (derivative Y).coeff K = ((K : k) + 1) * Y.coeff (K + 1) := by
    rw [coeff_derivative, mul_comm]
  have hcast : ((K : k) + 1) ≠ 0 := by
    have hk : K + 1 ≠ 0 := by
      rcases hK with h0 | ⟨h1, _⟩ <;> omega
    have hc : ((K + 1 : ℕ) : k) ≠ 0 := by exact_mod_cast hk
    push_cast at hc
    exact hc
  rw [hder] at hY'
  exact (mul_eq_zero.mp hY').resolve_left hcast

theorem fiveToSix_zetaFirst_gammaActive_rowOne_Y_TY0_68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hgamma : FiveToSixCuspZetaFirstGammaActiveResidual68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hBc : G < 2 * S) :
    let Y := -(2 : k) • (A * B ^ 2 * c) + (3 : k) • (A * d ^ 2) +
      (2 : k) • c ^ 3 - (9 : k) • e ^ 2
    Y.coeff (12 * N - 3 * G) = 0 := by
  have hdeg :=
    fiveToSix_zetaFirst_gammaActive_exact_degrees68 alpha gamma epsilon
      zeta eta terminal A B c d e N G S hgamma
  rcases hdeg with
    ⟨hN, hS, hgt, hle, hSR, hGamma, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _⟩
  have harith :=
    fiveToSix_gammaActive_rowOne_degree_arith68 N G S hN hgt hle hS hSR
      hGamma
  have hidx :
      12 * N - 2 * G - S - (G - S + 0) - 1 = 12 * N - 3 * G - 1 := by
    omega
  have hK : (12 * N - 3 * G - 1) + 1 = 12 * N - 3 * G := by omega
  have hY :=
    fiveToSix_zetaFirst_gammaActive_rowOne_Y_coeff68 alpha gamma epsilon
      zeta eta terminal A B c d e N G S (G - S) 0 (12 * N - 3 * G - 1)
      hgamma hidx (Or.inl hK)
  have hK1 : 12 * N - 3 * G - 1 + 1 = 12 * N - 3 * G := by omega
  simpa [hK1] using hY

theorem fiveToSix_zetaFirst_gammaActive_rowOne_Y_TY1_68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hgamma : FiveToSixCuspZetaFirstGammaActiveResidual68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hBc : 2 * S ≤ G) :
    let Y := -(2 : k) • (A * B ^ 2 * c) + (3 : k) • (A * d ^ 2) +
      (2 : k) • c ^ 3 - (9 : k) • e ^ 2
    Y.coeff (12 * N - 2 * G - 2 * S) = 0 := by
  have hdeg :=
    fiveToSix_zetaFirst_gammaActive_exact_degrees68 alpha gamma epsilon
      zeta eta terminal A B c d e N G S hgamma
  rcases hdeg with
    ⟨hN, hS, hgt, hle, hSR, hGamma, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _⟩
  have harith :=
    fiveToSix_gammaActive_rowOne_degree_arith68 N G S hN hgt hle hS hSR
      hGamma
  have hidx :
      12 * N - 2 * G - S - (S + 0) - 1 = 12 * N - 2 * G - 2 * S - 1 := by
    omega
  have hK :
      (12 * N - 2 * G - 2 * S - 1) + 1 = 12 * N - 2 * G - 2 * S := by
    omega
  have hY :=
    fiveToSix_zetaFirst_gammaActive_rowOne_Y_coeff68 alpha gamma epsilon
      zeta eta terminal A B c d e N G S S 0 (12 * N - 2 * G - 2 * S - 1)
      hgamma hidx (Or.inr ⟨hK, hBc⟩)
  have hK1 :
      12 * N - 2 * G - 2 * S - 1 + 1 = 12 * N - 2 * G - 2 * S := by
    omega
  simpa [hK1] using hY

/-! ## Dead chambers -/

/-- `G<2S`, any `γ`.  First `Y` coefficient is `AB²c,c³`. -/
theorem fiveToSix_zetaFirst_gammaActive_rowOne_B3loaded_false68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hgamma : FiveToSixCuspZetaFirstGammaActiveResidual68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hBc : G < 2 * S) :
    False := by
  have hF :=
    fiveToSix_zetaFirst_gammaActive_F_degree_cases68 alpha gamma epsilon
      zeta eta terminal A B c d e N G S hgamma
  have hY0 :=
    fiveToSix_zetaFirst_gammaActive_rowOne_Y_TY0_68 alpha gamma epsilon
      zeta eta terminal A B c d e N G S hgamma hBc
  have hYlead :=
    fiveToSix_zetaFirst_gammaActive_Y_leading_B3loaded68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S hgamma hBc
  have hdeg :=
    fiveToSix_zetaFirst_gammaActive_exact_degrees68 alpha gamma epsilon
      zeta eta terminal A B c d e N G S hgamma
  rcases hdeg with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ha0, hb0, hc0, _,
      _, hcusp0, _⟩
  have hYsc :
      -(2 : k) * A.coeff (2 * N) * B.coeff (3 * N - G) ^ 2 *
            c.coeff (4 * N - G) +
          (2 : k) * c.coeff (4 * N - G) ^ 3 = 0 := by
    rw [← hYlead]
    exact hY0
  rcases hF with _ | _
  · exact
      fiveToSix_gammaActive_Y_AB2c_leading_false68
        (A.coeff (2 * N)) (B.coeff (3 * N - G)) (c.coeff (4 * N - G))
        ha0 hb0 hc0 hcusp0 hYsc
  · exact
      fiveToSix_gammaActive_Y_AB2c_leading_false68
        (A.coeff (2 * N)) (B.coeff (3 * N - G)) (c.coeff (4 * N - G))
        ha0 hb0 hc0 hcusp0 hYsc

theorem fiveToSix_zetaFirst_gammaActive_rowOne_B3loaded_gamma0_false68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hgamma : FiveToSixCuspZetaFirstGammaActiveResidual68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hBc : G < 2 * S) (h0 : gamma = 0) :
    False :=
  fiveToSix_zetaFirst_gammaActive_rowOne_B3loaded_false68 alpha gamma
    epsilon zeta eta terminal A B c d e N G S hgamma hBc

theorem fiveToSix_zetaFirst_gammaActive_rowOne_B3loaded_gammaNe_false68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hgamma : FiveToSixCuspZetaFirstGammaActiveResidual68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hBc : G < 2 * S) (hne : gamma ≠ 0) :
    False :=
  fiveToSix_zetaFirst_gammaActive_rowOne_B3loaded_false68 alpha gamma
    epsilon zeta eta terminal A B c d e N G S hgamma hBc

/-- `G>2S`, any `γ`.  First `Y` coefficient is `Ad²,e²`. -/
theorem fiveToSix_zetaFirst_gammaActive_rowOne_B3absent_false68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hgamma : FiveToSixCuspZetaFirstGammaActiveResidual68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hBc : 2 * S < G) :
    False := by
  have hF :=
    fiveToSix_zetaFirst_gammaActive_F_degree_cases68 alpha gamma epsilon
      zeta eta terminal A B c d e N G S hgamma
  have hY0 :=
    fiveToSix_zetaFirst_gammaActive_rowOne_Y_TY1_68 alpha gamma epsilon
      zeta eta terminal A B c d e N G S hgamma (le_of_lt hBc)
  have hYlead :=
    fiveToSix_zetaFirst_gammaActive_Y_leading_B3absent68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S hgamma hBc
  have hH :=
    fiveToSix_zetaFirst_gammaActive_H_top68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S hgamma
  have hdeg :=
    fiveToSix_zetaFirst_gammaActive_exact_degrees68 alpha gamma epsilon
      zeta eta terminal A B c d e N G S hgamma
  rcases hdeg with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ha0, hb0, hc0,
      hd0, he0, hcusp0, _⟩
  have hYsc :
      (3 : k) * A.coeff (2 * N) * d.coeff (5 * N - G - S) ^ 2 -
          (9 : k) * e.coeff (6 * N - G - S) ^ 2 = 0 := by
    rw [← hYlead]
    exact hY0
  rcases hF with _ | _
  · exact
      fiveToSix_gammaActive_Y_Ade_leading_false68
        (A.coeff (2 * N)) (B.coeff (3 * N - G)) (c.coeff (4 * N - G))
        (d.coeff (5 * N - G - S)) (e.coeff (6 * N - G - S))
        ha0 hb0 hc0 hd0 he0 hcusp0 hH.2.1 hYsc
  · exact
      fiveToSix_gammaActive_Y_Ade_leading_false68
        (A.coeff (2 * N)) (B.coeff (3 * N - G)) (c.coeff (4 * N - G))
        (d.coeff (5 * N - G - S)) (e.coeff (6 * N - G - S))
        ha0 hb0 hc0 hd0 he0 hcusp0 hH.2.1 hYsc

theorem fiveToSix_zetaFirst_gammaActive_rowOne_B3absent_gamma0_false68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hgamma : FiveToSixCuspZetaFirstGammaActiveResidual68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hBc : 2 * S < G) (h0 : gamma = 0) :
    False :=
  fiveToSix_zetaFirst_gammaActive_rowOne_B3absent_false68 alpha gamma
    epsilon zeta eta terminal A B c d e N G S hgamma hBc

theorem fiveToSix_zetaFirst_gammaActive_rowOne_B3absent_gammaNe_false68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hgamma : FiveToSixCuspZetaFirstGammaActiveResidual68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hBc : 2 * S < G) (hne : gamma ≠ 0) :
    False :=
  fiveToSix_zetaFirst_gammaActive_rowOne_B3absent_false68 alpha gamma
    epsilon zeta eta terminal A B c d e N G S hgamma hBc

/-! ## Surviving `G=2S` cell -/

theorem fiveToSix_zetaFirst_gammaActive_rowOne_G2S_Ytop68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hgamma : FiveToSixCuspZetaFirstGammaActiveResidual68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hGS : G = 2 * S) :
    let D := 3 * N - G
    let Cc := 4 * N - G
    let V := 5 * N - G - S
    let E := 6 * N - G - S
    let Y := -(2 : k) • (A * B ^ 2 * c) + (3 : k) • (A * d ^ 2) +
      (2 : k) • c ^ 3 - (9 : k) • e ^ 2
    Y.coeff (12 * N - 6 * S) = 0 ∧
      Y.coeff (12 * N - 6 * S) =
        -(2 : k) * A.coeff (2 * N) * B.coeff D ^ 2 * c.coeff Cc +
          (3 : k) * A.coeff (2 * N) * d.coeff V ^ 2 +
          (2 : k) * c.coeff Cc ^ 3 - (9 : k) * e.coeff E ^ 2 ∧
      (4 : k) * B.coeff D ^ 2 * c.coeff Cc -
        (9 : k) * d.coeff V ^ 2 = 0 := by
  let D := 3 * N - G
  let Cc := 4 * N - G
  let V := 5 * N - G - S
  let E := 6 * N - G - S
  let Y := -(2 : k) • (A * B ^ 2 * c) + (3 : k) • (A * d ^ 2) +
    (2 : k) • c ^ 3 - (9 : k) • e ^ 2
  have hleGS : 2 * S ≤ G := by omega
  have hY0 :=
    fiveToSix_zetaFirst_gammaActive_rowOne_Y_TY1_68 alpha gamma epsilon
      zeta eta terminal A B c d e N G S hgamma hleGS
  have hT : 12 * N - 2 * G - 2 * S = 12 * N - 6 * S := by omega
  have hYlead :=
    fiveToSix_zetaFirst_gammaActive_Y_leading_G2S68 alpha gamma epsilon
      zeta eta terminal A B c d e N G S hgamma hGS
  have hH :=
    fiveToSix_zetaFirst_gammaActive_H_top68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S hgamma
  have hdeg :=
    fiveToSix_zetaFirst_gammaActive_exact_degrees68 alpha gamma epsilon
      zeta eta terminal A B c d e N G S hgamma
  rcases hdeg with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ha0, hb0, hc0,
      hd0, he0, hcusp0, _⟩
  have hYcoeff : Y.coeff (12 * N - 6 * S) = 0 := by
    dsimp only [Y]
    rw [← hT]
    exact hY0
  have hYsc :
      -(2 : k) * A.coeff (2 * N) * B.coeff (3 * N - G) ^ 2 *
            c.coeff (4 * N - G) +
          (3 : k) * A.coeff (2 * N) * d.coeff (5 * N - G - S) ^ 2 +
          (2 : k) * c.coeff (4 * N - G) ^ 3 -
          (9 : k) * e.coeff (6 * N - G - S) ^ 2 = 0 := by
    have hlead := hYlead
    dsimp only at hlead
    rw [← hlead]
    exact hYcoeff
  have hred :=
    fiveToSix_gammaActive_Y_G2S_reduced68
      (A.coeff (2 * N)) (B.coeff (3 * N - G)) (c.coeff (4 * N - G))
      (d.coeff (5 * N - G - S)) (e.coeff (6 * N - G - S))
      ha0 hb0 hc0 hd0 he0 hcusp0 hH.2.1 hYsc
  exact ⟨hYcoeff, hYcoeff.trans hYsc.symm, hred⟩

/-! ## Residual packet -/

/-- Residual after consuming loaded uniform row one.  Not a closure.
Survivors sit on `G=2S` with `Y_(12N-6S)=0` and
`4 B_D² c_Cc=9 d_V²`. -/
def FiveToSixCuspZetaFirstGammaActiveRowOneResidual68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ) : Prop :=
  let D := 3 * N - G
  let Cc := 4 * N - G
  let V := 5 * N - G - S
  let E := 6 * N - G - S
  let Y := -(2 : k) • (A * B ^ 2 * c) + (3 : k) • (A * d ^ 2) +
    (2 : k) • c ^ 3 - (9 : k) • e ^ 2
  FiveToSixCuspZetaFirstGammaActiveInventoryResidual68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S ∧
    G = 2 * S ∧
    Y.coeff (12 * N - 6 * S) = 0 ∧
      -(2 : k) * A.coeff (2 * N) * B.coeff D ^ 2 * c.coeff Cc +
          (3 : k) * A.coeff (2 * N) * d.coeff V ^ 2 +
          (2 : k) * c.coeff Cc ^ 3 - (9 : k) * e.coeff E ^ 2 = 0 ∧
      (4 : k) * B.coeff D ^ 2 * c.coeff Cc -
        (9 : k) * d.coeff V ^ 2 = 0

/-- Source-backed consumption of loaded uniform row one.  Not a
closure. -/
theorem fiveToSix_zetaFirst_gammaActive_rowOne68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hgamma : FiveToSixCuspZetaFirstGammaActiveResidual68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S) :
    FiveToSixCuspZetaFirstGammaActiveRowOneResidual68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S := by
  have hinv :=
    fiveToSix_zetaFirst_gammaActive_inventory68 alpha gamma epsilon zeta
      eta terminal A B c d e N G S hgamma
  rcases lt_trichotomy G (2 * S) with hlt | heq | hgt
  · exact
      (fiveToSix_zetaFirst_gammaActive_rowOne_B3loaded_false68 alpha
        gamma epsilon zeta eta terminal A B c d e N G S hgamma hlt).elim
  · have hY :=
      fiveToSix_zetaFirst_gammaActive_rowOne_G2S_Ytop68 alpha gamma
        epsilon zeta eta terminal A B c d e N G S hgamma heq
    dsimp only [FiveToSixCuspZetaFirstGammaActiveRowOneResidual68]
    exact ⟨hinv, heq, hY.1, hY.2.1.symm.trans hY.1, hY.2.2⟩
  · exact
      (fiveToSix_zetaFirst_gammaActive_rowOne_B3absent_false68 alpha
        gamma epsilon zeta eta terminal A B c d e N G S hgamma hgt).elim

#print axioms fiveToSix_gammaActive_Y_AB2c_leading_false68
#print axioms fiveToSix_gammaActive_Y_Ade_leading_false68
#print axioms fiveToSix_gammaActive_Y_G2S_reduced68
#print axioms fiveToSix_gammaActive_rowOne_degree_arith68
#print axioms secondaryResidualRowOnePolynomial68_core_extra68
#print axioms fiveToSix_zetaFirst_gammaActive_Rc_polynomial68
#print axioms fiveToSix_zetaFirst_gammaActive_rowOne_core_Rc68
#print axioms fiveToSix_zetaFirst_gammaActive_rowOne_cancelled68
#print axioms fiveToSix_zetaFirst_gammaActive_rowOne_Y_coeff68
#print axioms fiveToSix_zetaFirst_gammaActive_rowOne_Y_TY0_68
#print axioms fiveToSix_zetaFirst_gammaActive_rowOne_Y_TY1_68
#print axioms fiveToSix_zetaFirst_gammaActive_rowOne_B3loaded_false68
#print axioms fiveToSix_zetaFirst_gammaActive_rowOne_B3loaded_gamma0_false68
#print axioms fiveToSix_zetaFirst_gammaActive_rowOne_B3loaded_gammaNe_false68
#print axioms fiveToSix_zetaFirst_gammaActive_rowOne_B3absent_false68
#print axioms fiveToSix_zetaFirst_gammaActive_rowOne_B3absent_gamma0_false68
#print axioms fiveToSix_zetaFirst_gammaActive_rowOne_B3absent_gammaNe_false68
#print axioms fiveToSix_zetaFirst_gammaActive_rowOne_G2S_Ytop68
#print axioms fiveToSix_zetaFirst_gammaActive_rowOne68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointGammaActiveRowOne68

end Max11DegreeRoutes
