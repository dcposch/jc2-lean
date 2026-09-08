import Grok68GammaActiveRowOneScratch

/-! # Loaded uniform row two on the gamma-active `(6,8)` `G=2S` cell

Untracked working note. No tracked file was edited.

The parent
`FiveToSixCuspZetaFirstGammaActiveRowOneResidual68` sits on `G=2S`
with exact cusp edges, `H_(9N-2G-S)=0`, the `Q` leading
`-(4/9)A_(2N) B_D³`, `Y_(12N-6S)=0`, and `4 B_D² c_Cc=9 d_V²`.  This
file consumes the named next unused row: loaded uniform row two at
`11N-2G-2S-1`, which on `G=2S` is the common top of `Q` and `de`,
i.e. `J=Q-3de`.

CAS `derive_68_gamma_active_leadings.py` (row-two extension) records
that compensated I4 remainder
`Fc=F+(3/2)γ d=-(3/4)ε B+const` has degree `≤D=3N-G`.  After the
`A d'`/`d A'` gamma pair is absorbed into `Fc`, the `Fc` block,
the `H`-support extra `6 B² d'+12 B B' d`, and every leftover
`(γ,ε)` load sit strictly below `J'` on every `G=2S` gamma-active
lattice point.  (Raw `A d'` reaches the named row, which is why the
absorption is required.)  Loaded uniform row two is therefore the
first coefficient of `J`, forcing `J_(11N-6S)=0`.

Together with the cusp, `H`, and `Y` this is the four-scalar system
whose Groebner basis contains `e⁴`.  The comparison is the same
coefficient identity that closed the `G=2S` wall packets and the
off-wall packet: `3J+(1/3)b·cusp=4bc²-9de` and `Y+2c·cusp=3ad²+8c³-9e²`,
after which `H` and the cusp square force both `4c³+9e²=0` and
`4c³-9e²=0`.  Not a finite-root shortcut.

Exact gain: `FiveToSixCuspZetaFirstGammaActiveResidual68` is `False`.
Next unused row: branchwise among the remaining assembly residual
(NextPacket wall; NextTwo gamma-d wall; constant-`Fce` wall;
support-loaded `q=0` vanishing-A; terminal-zero; large terminal cusp).
Residual: none; the named target
`fiveToSix_zetaFirst_gammaActive_false68` is `False`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointGammaActiveRowTwo68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

/-! ## Scalar leading-jet identity -/

/-- The four leading coefficients of the cusp, of `Be+cd`, of
`Q-3de`, and of `Y` cannot vanish together.  CAS:
`derive_68_gamma_active_leadings.py` records the same multipliers as
the `G=2S` walls: `3*J+(1/3)b*cusp = 4bc²-9de` and
`Y+2c*cusp = 3ad²+8c³-9e²`, after which `H` and the cusp square force
both `4c³+9e²=0` and `4c³-9e²=0`. -/
theorem fiveToSix_gammaActive_leading_jet_false68
    (a b c d e : k)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (hcusp : a * b ^ 2 + (3 : k) * c ^ 2 = 0)
    (hH : b * e + c * d = 0)
    (hJ : b * c ^ 2 - (1 / 9 : k) * a * b ^ 3 - (3 : k) * d * e = 0)
    (hY : -(2 : k) * a * b ^ 2 * c + (3 : k) * a * d ^ 2 +
        (2 : k) * c ^ 3 - (9 : k) * e ^ 2 = 0) :
    False := by
  have hJred : (4 : k) * b * c ^ 2 - (9 : k) * d * e = 0 := by
    linear_combination (3 : k) * hJ + (1 / 3 : k) * b * hcusp
  have hYred : (3 : k) * a * d ^ 2 + (8 : k) * c ^ 3 -
      (9 : k) * e ^ 2 = 0 := by
    linear_combination hY + (2 : k) * c * hcusp
  have hce : (4 : k) * c ^ 3 + (9 : k) * e ^ 2 = 0 := by
    have hprod : d * ((4 : k) * c ^ 3 + (9 : k) * e ^ 2) = 0 := by
      linear_combination (4 : k) * c ^ 2 * hH - e * hJred
    exact (mul_eq_zero.mp hprod).resolve_left hd
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
  have hce' : (4 : k) * c ^ 3 - (9 : k) * e ^ 2 = 0 := by
    have h8 : (8 : k) * c ^ 3 - (18 : k) * e ^ 2 = 0 := by
      linear_combination hYred - (3 : k) * had
    linear_combination (1 / 2 : k) * h8
  have he2 : (18 : k) * e ^ 2 = 0 := by
    linear_combination hce - hce'
  have h18 : (18 : k) ≠ 0 := by norm_num
  have hz : e ^ 2 = 0 := (mul_eq_zero.mp he2).resolve_left h18
  exact he (eq_zero_of_pow_eq_zero hz)

/-! ## Degree dictionary for row two on `G=2S` -/

/-- Remainder of loaded uniform row two versus the common `Q`/`de`
top.  Window arithmetic forces the `Fc` block, the `H`-support extra,
and every leftover `(γ,ε)` load strictly below `11N-6S-1`. -/
theorem fiveToSix_gammaActive_rowTwo_degree_arith68
    (N G S : ℕ) (hN : 0 < N) (hgt : 5 * N < 2 * G) (hle : 2 * G ≤ 6 * N)
    (hS : 0 < S) (hSR : S < 7 * N - 2 * G) (hGamma : 4 * N - G ≤ S)
    (hGS : G = 2 * S) :
    let D := 3 * N - G
    let Cc := 4 * N - G
    let V := 5 * N - G - S
    let E := 6 * N - G - S
    let TJ := 11 * N - 6 * S
    let K := 11 * N - 6 * S - 1
    0 < D ∧ 0 < Cc ∧ 0 < V ∧ 0 < E ∧ S < G ∧ 2 * S < 3 * N ∧
      D < V ∧
      2 * N + D - 1 < K ∧
      2 * D + V - 1 < K ∧
      D + Cc - 1 < K ∧
      V - 1 < K ∧
      2 * N + 3 * D = TJ ∧
      D + 2 * Cc = TJ ∧
      V + E = TJ ∧
      11 * N - 3 * G = TJ ∧
      11 * N - 2 * G - 2 * S - 1 = K ∧
      K + 1 = TJ ∧
      1 ≤ TJ ∧ 1 ≤ D := by
  omega

/-! ## Degree helpers -/

private theorem natDegree_mul_derivative_le_gammaActiveRowTwo68
    (p q : k[X]) (u v : ℕ)
    (hu : p.natDegree ≤ u) (hv : 0 < v) (hq : q.natDegree ≤ v) :
    (p * derivative q).natDegree ≤ u + v - 1 := by
  have hd : (derivative q).natDegree ≤ v - 1 :=
    (natDegree_derivative_le q).trans (by omega)
  have hmul := natDegree_mul_le.trans (Nat.add_le_add hu hd)
  omega

private theorem natDegree_derivative_mul_le_gammaActiveRowTwo68
    (p q : k[X]) (u v : ℕ)
    (hu : 0 < u) (hp : p.natDegree ≤ u) (hq : q.natDegree ≤ v) :
    (derivative p * q).natDegree ≤ u + v - 1 := by
  have hd : (derivative p).natDegree ≤ u - 1 :=
    (natDegree_derivative_le p).trans (by omega)
  have hmul := natDegree_mul_le.trans (Nat.add_le_add hd hq)
  omega

/-! ## `H`-support extra and compensated I4 absorption -/

/-- `H`-support extra in residual row two, strictly below `J'` on a
`G=2S` gamma-active cell. -/
def FiveToSixCuspZetaFirstGammaActiveRowTwoExtra68
    (A B c d e : k[X]) : k[X] :=
  (6 : k) • (B ^ 2 * derivative d) +
    (12 : k) • (B * derivative B * d)

theorem secondaryResidualRowTwoPolynomial68_core_extra68
    (A B c d e : k[X]) :
    secondaryResidualRowTwoPolynomial68 A B c d e =
      (-4 / 27 : k) •
        (FiveToSixCuspZetaFirstB3EndpointRowTwoCore68 A B c d e +
          FiveToSixCuspZetaFirstGammaActiveRowTwoExtra68 A B c d e) := by
  unfold secondaryResidualRowTwoPolynomial68
    FiveToSixCuspZetaFirstB3EndpointRowTwoCore68
    FiveToSixCuspZetaFirstGammaActiveRowTwoExtra68
  congr 1
  module

/-- Absorbing the first `gamma d` load into the compensated I4
remainder. -/
theorem fiveToSix_zetaFirst_gammaActive_rowTwo_load_factor68
    (gamma : k) (A B c d e : k[X]) :
    let F := (B * e + c * d) - (1 / 9 : k) • B ^ 3
    let Fc := F + (3 / 2 * gamma : k) • d
    let J := (B * c ^ 2 - (1 / 9 : k) • (A * B ^ 3)) - (3 : k) • (d * e)
    FiveToSixCuspZetaFirstB3EndpointRowTwoCore68 A B c d e -
        (9 * gamma : k) • (A * derivative d) +
        (9 / 2 * gamma : k) • (d * derivative A) =
      -(6 : k) • (A * derivative Fc) + (3 : k) • (derivative A * Fc) +
        (6 : k) • derivative J := by
  intro F Fc J
  let Q := B * c ^ 2 - (1 / 9 : k) • (A * B ^ 3)
  have hbase :
      FiveToSixCuspZetaFirstB3EndpointRowTwoCore68 A B c d e =
        -(6 : k) • (A * derivative F) + (3 : k) • (derivative A * F) +
          (6 : k) • derivative J := by
    dsimp only [F, Q, J]
    rw [fiveToSix_zetaFirst_B3_endpoint_rowTwo_core_factor68
      (k := k) A B c d e]
    simp only [derivative_sub, derivative_smul, derivative_mul, mul_sub,
      mul_add, add_mul, mul_smul_comm, smul_mul_assoc, smul_sub, smul_add,
      smul_smul, mul_assoc]
    module
  rw [hbase]
  dsimp only [Fc]
  simp only [derivative_add, derivative_smul, mul_add, mul_smul_comm,
    smul_mul_assoc, smul_add, smul_sub, smul_smul]
  rw [show d * derivative A = derivative A * d by ring]
  module

theorem fiveToSix_zetaFirst_gammaActive_rowTwo_cancelled68
    (gamma : k) (A B c d e : k[X]) :
    let F := (B * e + c * d) - (1 / 9 : k) • B ^ 3
    let Fc := F + (3 / 2 * gamma : k) • d
    let J := (B * c ^ 2 - (1 / 9 : k) • (A * B ^ 3)) - (3 : k) • (d * e)
    let Extra := FiveToSixCuspZetaFirstGammaActiveRowTwoExtra68 A B c d e
    secondaryResidualRowTwoPolynomial68 A B c d e +
        (4 / 3 * gamma : k) • (A * derivative d) -
        (2 / 3 * gamma : k) • (d * derivative A) =
      (-4 / 27 : k) •
        (-(6 : k) • (A * derivative Fc) + (3 : k) • (derivative A * Fc) +
          (6 : k) • derivative J + Extra) := by
  intro F Fc J Extra
  have hcore :=
    secondaryResidualRowTwoPolynomial68_core_extra68 A B c d e
  have hfactor :=
    fiveToSix_zetaFirst_gammaActive_rowTwo_load_factor68 gamma A B c d e
  have hC :
      FiveToSixCuspZetaFirstB3EndpointRowTwoCore68 A B c d e =
        -(6 : k) • (A * derivative Fc) + (3 : k) • (derivative A * Fc) +
          (6 : k) • derivative J +
          (9 * gamma : k) • (A * derivative d) -
          (9 / 2 * gamma : k) • (d * derivative A) := by
    dsimp only [F, Fc, J] at hfactor ⊢
    linear_combination hfactor
  rw [hcore, hC]
  dsimp only [Extra]
  module

/-- Compensated I4 remainder has degree at most `deg B`. -/
theorem fiveToSix_zetaFirst_gammaActive_Fc_degree68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hgamma : FiveToSixCuspZetaFirstGammaActiveResidual68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S) :
    let F := (B * e + c * d) - (1 / 9 : k) • B ^ 3
    let Fc := F + (3 / 2 * gamma : k) • d
    let D := 3 * N - G
    Fc.natDegree ≤ D := by
  intro F Fc D
  have hdeg :=
    fiveToSix_zetaFirst_gammaActive_exact_degrees68 alpha gamma epsilon
      zeta eta terminal A B c d e N G S hgamma
  rcases hdeg with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hBdeg, _, _, _, _, _, _, _, _,
      _⟩
  have hB' : B.natDegree ≤ D := hBdeg.le
  rcases fiveToSix_zetaFirst_gammaActive_Fce_constant68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S hgamma with ⟨i4, hFce⟩
  have hFc_eq :
      Fc = (3 / 8 : k) • C i4 - (3 / 4 * epsilon : k) • B := by
    dsimp only [Fc, F]
    linear_combination hFce
  rw [hFc_eq]
  compute_degree
  omega

/-! ## First coefficient of `J` -/

/-- Loaded uniform row two at the common `Q`/`de` top kills that
coefficient.  The index is `11N-6S-1` on `G=2S`. -/
theorem fiveToSix_zetaFirst_gammaActive_rowTwo_J_coeff68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hgamma : FiveToSixCuspZetaFirstGammaActiveResidual68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hGS : G = 2 * S) :
    let J := (B * c ^ 2 - (1 / 9 : k) • (A * B ^ 3)) - (3 : k) • (d * e)
    J.coeff (11 * N - 6 * S) = 0 := by
  let F := (B * e + c * d) - (1 / 9 : k) • B ^ 3
  let Fc := F + (3 / 2 * gamma : k) • d
  let J := (B * c ^ 2 - (1 / 9 : k) • (A * B ^ 3)) - (3 : k) • (d * e)
  let Extra := FiveToSixCuspZetaFirstGammaActiveRowTwoExtra68 A B c d e
  let D := 3 * N - G
  let Cc := 4 * N - G
  let V := 5 * N - G - S
  let K := 11 * N - 6 * S - 1
  have hdeg :=
    fiveToSix_zetaFirst_gammaActive_exact_degrees68 alpha gamma epsilon
      zeta eta terminal A B c d e N G S hgamma
  rcases hdeg with
    ⟨hN, hS, hgt, hle, hSR, hGamma, hDpos, hCpos, hVpos, hEpos, _, _,
      hAdeg, hBdeg, hcdeg, hddeg, hedeg, _, _, _, _, _, _, hs⟩
  have harith :=
    fiveToSix_gammaActive_rowTwo_degree_arith68 N G S hN hgt hle hS hSR
      hGamma hGS
  rcases harith with
    ⟨_, _, _, _, _, _, _, hAFc, hEx, hBc, hdpr, _, _, _, _, hidx, hK1,
      hTJpos, _⟩
  have hA' : A.natDegree ≤ 2 * N := hAdeg.le
  have hB' : B.natDegree ≤ D := hBdeg.le
  have hc' : c.natDegree ≤ Cc := hcdeg.le
  have hd' : d.natDegree ≤ V := hddeg.le
  have hFcdeg : Fc.natDegree ≤ D := by
    dsimp only [Fc, F, D]
    exact fiveToSix_zetaFirst_gammaActive_Fc_degree68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S hgamma
  have hdFc : (derivative Fc).natDegree ≤ D - 1 :=
    (natDegree_derivative_le Fc).trans (by omega)
  have hAFcdeg : (A * derivative Fc).natDegree ≤ 2 * N + D - 1 := by
    have hmul := natDegree_mul_le.trans (Nat.add_le_add hA' hdFc)
    have hsum : 2 * N + (D - 1) = 2 * N + D - 1 := by omega
    rwa [hsum] at hmul
  have hA'Fcdeg :
      (derivative A * Fc).natDegree ≤ 2 * N + D - 1 :=
    natDegree_derivative_mul_le_gammaActiveRowTwo68 A Fc (2 * N) D
      (by omega) hA' hFcdeg
  have hB2deg : (B ^ 2).natDegree ≤ 2 * D := by
    compute_degree
    omega
  have hEx1deg :
      (B ^ 2 * derivative d).natDegree ≤ 2 * D + V - 1 :=
    natDegree_mul_derivative_le_gammaActiveRowTwo68 (B ^ 2) d (2 * D) V
      hB2deg (by omega) hd'
  have hEx2deg :
      (B * derivative B * d).natDegree ≤ 2 * D + V - 1 := by
    have hBB :
        (B * derivative B).natDegree ≤ D + D - 1 :=
      natDegree_mul_derivative_le_gammaActiveRowTwo68 B B D D hB'
        (by omega) hB'
    have h := natDegree_mul_le.trans (Nat.add_le_add hBB hd')
    have hsum : D + D - 1 + V = 2 * D + V - 1 := by omega
    rwa [hsum] at h
  have hExdeg : Extra.natDegree ≤ 2 * D + V - 1 := by
    dsimp only [Extra, FiveToSixCuspZetaFirstGammaActiveRowTwoExtra68]
    compute_degree
    omega
  have hBcdeg : (B * derivative c).natDegree ≤ D + Cc - 1 :=
    natDegree_mul_derivative_le_gammaActiveRowTwo68 B c D Cc hB'
      (by omega) hc'
  have hcBdeg : (c * derivative B).natDegree ≤ D + Cc - 1 := by
    have h :=
      natDegree_derivative_mul_le_gammaActiveRowTwo68 B c D Cc (by omega)
        hB' hc'
    simpa [mul_comm] using h
  have hAB1deg : (derivative A * B).natDegree ≤ 2 * N + D - 1 :=
    natDegree_derivative_mul_le_gammaActiveRowTwo68 A B (2 * N) D
      (by omega) hA' hB'
  have hAB2deg : (A * derivative B).natDegree ≤ 2 * N + D - 1 :=
    natDegree_mul_derivative_le_gammaActiveRowTwo68 A B (2 * N) D hA'
      (by omega) hB'
  have hddeg' : (derivative d).natDegree ≤ V - 1 :=
    (natDegree_derivative_le d).trans (by omega)
  have hAFclt : (A * derivative Fc).natDegree < K := by omega
  have hA'Fclt : (derivative A * Fc).natDegree < K := by omega
  have hExlt : Extra.natDegree < K := by omega
  have hBclt : (B * derivative c).natDegree < K := by omega
  have hcBlt : (c * derivative B).natDegree < K := by omega
  have hAB1lt : (derivative A * B).natDegree < K := by omega
  have hAB2lt : (A * derivative B).natDegree < K := by omega
  have hdlt : (derivative d).natDegree < K := by omega
  have hrow :=
    fiveToSix_zetaFirst_loaded_uniform_rowTwo68 alpha gamma epsilon zeta
      eta terminal A B c d e N G S S 0 hs
  dsimp only [FiveToSixCuspZetaFirstLoadedUniformRowTwoScalar68] at hrow
  have hidx' : 11 * N - 2 * G - S - (S + 0) - 1 = K := by
    dsimp only [K]
    omega
  rw [hidx'] at hrow
  have hcancel :=
    fiveToSix_zetaFirst_gammaActive_rowTwo_cancelled68 gamma A B c d e
  have hcancelK :
      (secondaryResidualRowTwoPolynomial68 A B c d e +
          (4 / 3 * gamma : k) • (A * derivative d) -
          (2 / 3 * gamma : k) • (d * derivative A)).coeff K =
        ((-4 / 27 : k) •
          (-(6 : k) • (A * derivative Fc) +
            (3 : k) • (derivative A * Fc) +
            (6 : k) • derivative J + Extra)).coeff K :=
    congrArg (fun p : k[X] => p.coeff K) hcancel
  have hleft :
      (secondaryResidualRowTwoPolynomial68 A B c d e +
          (4 / 3 * gamma : k) • (A * derivative d) -
          (2 / 3 * gamma : k) • (d * derivative A)).coeff K =
        (secondaryResidualRowTwoPolynomial68 A B c d e).coeff K +
          (4 / 3 * gamma : k) * (A * derivative d).coeff K -
          (2 / 3 * gamma : k) * (d * derivative A).coeff K := by
    simp only [coeff_add, coeff_sub, coeff_smul, smul_eq_mul]
  have hRest0 :
      -(4 / 3 * gamma : k) * (B * derivative c).coeff K -
          (4 / 3 * gamma : k) * (c * derivative B).coeff K -
          (1 / 3 * epsilon : k) * (derivative A * B).coeff K +
          (2 / 3 * epsilon : k) * (A * derivative B).coeff K +
          (2 * epsilon : k) * (derivative d).coeff K = 0 := by
    simp only [coeff_eq_zero_of_natDegree_lt hBclt,
      coeff_eq_zero_of_natDegree_lt hcBlt,
      coeff_eq_zero_of_natDegree_lt hAB1lt,
      coeff_eq_zero_of_natDegree_lt hAB2lt,
      coeff_eq_zero_of_natDegree_lt hdlt, mul_zero, add_zero, sub_zero]
  have hAd :
      (secondaryResidualRowTwoPolynomial68 A B c d e).coeff K +
          (4 / 3 * gamma : k) * (A * derivative d).coeff K -
          (2 / 3 * gamma : k) * (d * derivative A).coeff K = 0 := by
    linear_combination hrow - hRest0
  have hJcomb :
      ((-4 / 27 : k) •
          (-(6 : k) • (A * derivative Fc) +
            (3 : k) • (derivative A * Fc) +
            (6 : k) • derivative J + Extra)).coeff K = 0 := by
    rw [← hcancelK, hleft, hAd]
  have hAFc0 : (A * derivative Fc).coeff K = 0 :=
    coeff_eq_zero_of_natDegree_lt hAFclt
  have hA'Fc0 : (derivative A * Fc).coeff K = 0 :=
    coeff_eq_zero_of_natDegree_lt hA'Fclt
  have hEx0 : Extra.coeff K = 0 :=
    coeff_eq_zero_of_natDegree_lt hExlt
  have hJ' : (derivative J).coeff K = 0 := by
    have hexp :
        ((-4 / 27 : k) •
            (-(6 : k) • (A * derivative Fc) +
              (3 : k) • (derivative A * Fc) +
              (6 : k) • derivative J + Extra)).coeff K =
          (-4 / 27 : k) *
            (-(6 : k) * (A * derivative Fc).coeff K +
              (3 : k) * (derivative A * Fc).coeff K +
              (6 : k) * (derivative J).coeff K + Extra.coeff K) := by
      simp only [coeff_add, coeff_smul, smul_eq_mul]
    have hred :
        (-4 / 27 : k) *
            (-(6 : k) * (A * derivative Fc).coeff K +
              (3 : k) * (derivative A * Fc).coeff K +
              (6 : k) * (derivative J).coeff K + Extra.coeff K) =
          (-4 / 27 : k) * ((6 : k) * (derivative J).coeff K) := by
      rw [hAFc0, hA'Fc0, hEx0]
      ring
    rw [hexp, hred] at hJcomb
    have h427 : (-4 / 27 : k) ≠ 0 := by norm_num
    have h6 : (6 : k) ≠ 0 := by norm_num
    have hJ6 : (6 : k) * (derivative J).coeff K = 0 :=
      (mul_eq_zero.mp hJcomb).resolve_left h427
    exact (mul_eq_zero.mp hJ6).resolve_left h6
  have hder : (derivative J).coeff K = ((K : k) + 1) * J.coeff (K + 1) := by
    rw [coeff_derivative, mul_comm]
  have hcast : ((K : k) + 1) ≠ 0 := by
    have hk : K + 1 ≠ 0 := by omega
    have hc : ((K + 1 : ℕ) : k) ≠ 0 := by exact_mod_cast hk
    push_cast at hc
    exact hc
  rw [hder] at hJ'
  have hJ0 : J.coeff (K + 1) = 0 :=
    (mul_eq_zero.mp hJ').resolve_left hcast
  have hK1' : K + 1 = 11 * N - 6 * S := by
    dsimp only [K]; exact hK1
  rwa [hK1'] at hJ0

theorem fiveToSix_zetaFirst_gammaActive_rowTwo_Jtop68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hgamma : FiveToSixCuspZetaFirstGammaActiveResidual68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hGS : G = 2 * S) :
    let D := 3 * N - G
    let Cc := 4 * N - G
    let V := 5 * N - G - S
    let E := 6 * N - G - S
    let J := (B * c ^ 2 - (1 / 9 : k) • (A * B ^ 3)) - (3 : k) • (d * e)
    J.coeff (11 * N - 6 * S) = 0 ∧
      B.coeff D * c.coeff Cc ^ 2 -
          (1 / 9 : k) * A.coeff (2 * N) * B.coeff D ^ 3 -
          (3 : k) * d.coeff V * e.coeff E = 0 := by
  let D := 3 * N - G
  let Cc := 4 * N - G
  let V := 5 * N - G - S
  let E := 6 * N - G - S
  let TJ := 11 * N - 6 * S
  let Q := B * c ^ 2 - (1 / 9 : k) • (A * B ^ 3)
  let J := Q - (3 : k) • (d * e)
  have hJ0 :=
    fiveToSix_zetaFirst_gammaActive_rowTwo_J_coeff68 alpha gamma epsilon
      zeta eta terminal A B c d e N G S hgamma hGS
  have hdeg :=
    fiveToSix_zetaFirst_gammaActive_exact_degrees68 alpha gamma epsilon
      zeta eta terminal A B c d e N G S hgamma
  rcases hdeg with
    ⟨hN, hS, hgt, hle, hSR, hGamma, _, _, _, _, _, _, hAdeg, hBdeg, hcdeg,
      hddeg, hedeg, _, _, _, _, _, _, _⟩
  have harith :=
    fiveToSix_gammaActive_rowTwo_degree_arith68 N G S hN hgt hle hS hSR
      hGamma hGS
  rcases harith with
    ⟨_, _, _, _, _, _, _, _, _, _, _, hAB3sum, hBc2sum, hdesum, _, _, _,
      _, _⟩
  have hA' : A.natDegree ≤ 2 * N := hAdeg.le
  have hB' : B.natDegree ≤ D := hBdeg.le
  have hc' : c.natDegree ≤ Cc := hcdeg.le
  have hd' : d.natDegree ≤ V := hddeg.le
  have he' : e.natDegree ≤ E := hedeg.le
  have hB3deg : (B ^ 3).natDegree ≤ 3 * D := by
    compute_degree
    omega
  have hc2deg : (c ^ 2).natDegree ≤ 2 * Cc := by
    compute_degree
    omega
  have hB3top : (B ^ 3).coeff (3 * D) = B.coeff D ^ 3 :=
    coeff_pow_at_bound68 B D 3 hB'
  have hc2top : (c ^ 2).coeff (2 * Cc) = c.coeff Cc ^ 2 :=
    coeff_pow_at_bound68 c Cc 2 hc'
  have hBc2 := coeff_mul_at_bounds68 B (c ^ 2) D (2 * Cc) hB' hc2deg
  have hAB3 :=
    coeff_mul_at_bounds68 A (B ^ 3) (2 * N) (3 * D) hA' hB3deg
  have hde := coeff_mul_at_bounds68 d e V E hd' he'
  have hBc2top : (B * c ^ 2).coeff TJ = B.coeff D * c.coeff Cc ^ 2 := by
    have hidx : D + 2 * Cc = TJ := by
      dsimp only [D, Cc, TJ] at hBc2sum ⊢
      exact hBc2sum
    rw [← hidx, hBc2, hc2top]
  have hAB3top : (A * B ^ 3).coeff TJ =
      A.coeff (2 * N) * B.coeff D ^ 3 := by
    have hidx : 2 * N + 3 * D = TJ := by
      dsimp only [D, TJ] at hAB3sum ⊢
      exact hAB3sum
    rw [← hidx, hAB3, hB3top]
  have hdetop : (d * e).coeff TJ = d.coeff V * e.coeff E := by
    have hidx : V + E = TJ := by
      dsimp only [V, E, TJ] at hdesum ⊢
      exact hdesum
    rw [← hidx, hde]
  have hJcoeff : J.coeff TJ = 0 := by
    dsimp only [J, Q, TJ]
    exact hJ0
  have hJlead :
      B.coeff D * c.coeff Cc ^ 2 -
          (1 / 9 : k) * A.coeff (2 * N) * B.coeff D ^ 3 -
          (3 : k) * d.coeff V * e.coeff E = 0 := by
    have hJexp : J.coeff TJ =
        (B * c ^ 2).coeff TJ -
          (1 / 9 : k) * (A * B ^ 3).coeff TJ -
          (3 : k) * (d * e).coeff TJ := by
      dsimp only [J, Q]
      simp only [coeff_sub, coeff_smul, smul_eq_mul]
    rw [hBc2top, hAB3top, hdetop] at hJexp
    convert hJexp.symm.trans hJcoeff using 1
    ring
  exact ⟨hJcoeff, hJlead⟩

/-! ## Closure -/

/-- `G=2S` gamma-active cell: row two kills `J` at `11N-6S`, and the
four leading jets contradict the cusp edges. -/
theorem fiveToSix_zetaFirst_gammaActive_rowTwo_false68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hrow1 : FiveToSixCuspZetaFirstGammaActiveRowOneResidual68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S) :
    False := by
  let D := 3 * N - G
  let Cc := 4 * N - G
  let V := 5 * N - G - S
  let E := 6 * N - G - S
  have hgamma : FiveToSixCuspZetaFirstGammaActiveResidual68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S := hrow1.1.1
  have hGS : G = 2 * S := hrow1.2.1
  have hYsc :
      -(2 : k) * A.coeff (2 * N) * B.coeff D ^ 2 * c.coeff Cc +
          (3 : k) * A.coeff (2 * N) * d.coeff V ^ 2 +
          (2 : k) * c.coeff Cc ^ 3 - (9 : k) * e.coeff E ^ 2 = 0 := by
    simpa [D, Cc, V, E] using hrow1.2.2.2.1
  have hJ :=
    fiveToSix_zetaFirst_gammaActive_rowTwo_Jtop68 alpha gamma epsilon
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
  have hJsc :
      B.coeff D * c.coeff Cc ^ 2 -
          (1 / 9 : k) * A.coeff (2 * N) * B.coeff D ^ 3 -
          (3 : k) * d.coeff V * e.coeff E = 0 := by
    simpa [D, Cc, V, E] using hJ.2
  exact
    fiveToSix_gammaActive_leading_jet_false68
      (A.coeff (2 * N)) (B.coeff D) (c.coeff Cc) (d.coeff V) (e.coeff E)
      ha0 hb0 hc0 hd0 he0 hcusp0 hH.2.1 hJsc hYsc

/-- Exclusion of the gamma-active `(6,8)` scale-zero endpoint cell. -/
theorem fiveToSix_zetaFirst_gammaActive_false68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hgamma : FiveToSixCuspZetaFirstGammaActiveResidual68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S) :
    False :=
  fiveToSix_zetaFirst_gammaActive_rowTwo_false68 alpha gamma epsilon zeta
    eta terminal A B c d e N G S
    (fiveToSix_zetaFirst_gammaActive_rowOne68 alpha gamma epsilon zeta
      eta terminal A B c d e N G S hgamma)

#print axioms fiveToSix_gammaActive_leading_jet_false68
#print axioms fiveToSix_gammaActive_rowTwo_degree_arith68
#print axioms secondaryResidualRowTwoPolynomial68_core_extra68
#print axioms fiveToSix_zetaFirst_gammaActive_rowTwo_load_factor68
#print axioms fiveToSix_zetaFirst_gammaActive_rowTwo_cancelled68
#print axioms fiveToSix_zetaFirst_gammaActive_Fc_degree68
#print axioms fiveToSix_zetaFirst_gammaActive_rowTwo_J_coeff68
#print axioms fiveToSix_zetaFirst_gammaActive_rowTwo_Jtop68
#print axioms fiveToSix_zetaFirst_gammaActive_rowTwo_false68
#print axioms fiveToSix_zetaFirst_gammaActive_false68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointGammaActiveRowTwo68

end Max11DegreeRoutes
