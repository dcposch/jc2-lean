import Grok68VanishingANextRowScratch

/-! # Uniform leading-jet closure of the `q=0` vanishing-A packet

The parent residual
`FiveToSixCuspZetaFirstB3EqualitySupportQZeroVanishingANextRowResidual68`
records remainder degree bounds, the charged `Δ`/`H` profiles, and the
`H_N` identity from `(S)`.  Those relations are not used here.  CAS
`derive_68_vanishing_a_uniform_certificate.py` (`vanishing-a-uniform-certificate`)
on the `m=1` model with every coefficient of `B,c,d,e` symbolic shows
that the four leading edges already generate an ideal containing `e^4`,
the same Groebner basis as the `G=2S` walls, the off-wall support packet,
and the gamma-active cell.  The `H_N` identity is independent of that
leading system.  The degree dictionary on `m=2` is the same four scalars.

On the wall `9N=7S` the four leading edges
`deg A=2N`, `deg B=D=3N-2S`, `deg c=Cc=4N-2S`, `deg d=V=5N-3S`,
`deg e=E=6N-3S` make `Be+cd`, `Q=Bc²-(1/9)AB³`, and
`Y=-2AB²c+3Ad²+2c³-9e²` attain a common top.  Compensated I4 writes
`(Be+cd)_(9N-5S)=0` (`top_resultant68`).  The post-epsilon state writes
`deg J≤2N`, and `2N<11N-6S`, so `J_(11N-6S)=0`.  The terminal `Y` state
in the support-loaded ancestry writes `deg Y≤8N-3S-1`, and
`8N-3S-1<12N-6S`, so `Y_(12N-6S)=0`.  Together with the cusp
`A_(2N) B_D²+3 c_Cc²=0` this is the four-scalar system whose Groebner
basis contains `e^4`.  The comparison is a coefficient at a single
degree, not an evaluation at roots of `B`.

No further loaded-row-one coefficient is consumed: the coefficient at
`12N-7S-1` remains a fresh-jet solve, and the remaining row-one
coefficients are unused.

Exact gain: `fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_impossible68`
is `False`.
Next unused row: branchwise among the remaining assembly residual
(terminal-zero beyond-wall; large terminal cusp).
Residual: none; the named vanishing-A packet is closed.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAUniformCertificate68

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
`derive_68_vanishing_a_uniform_certificate.py` records the same
multipliers as the `G=2S` walls: `3*J+(1/3)b*cusp = 4bc²-9de` and
`Y+2c*cusp = 3ad²+8c³-9e²`, after which `I4` and the cusp square force
both `4c³+9e²=0` and `4c³-9e²=0`. -/
theorem fiveToSix_vanishingA_leading_jet_false68
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

/-! ## Degree dictionary on the wall `9N=7S` -/

/-- Common tops of `Be+cd`, `J`, and `Y` on every `q=0` lattice point,
together with the two strict drops `deg J≤2N` and `deg Y≤8N-3S-1`. -/
theorem fiveToSix_vanishingA_degree_arith68
    (N S : ℕ) (hN : 0 < N) (hS : 0 < S)
    (hEq : 9 * N = 7 * S) (hgt : 5 * N < 4 * S) (hle : 4 * S ≤ 6 * N)
    (hGamma : 3 * S < 4 * N) :
    let D := 3 * N - 2 * S
    let Cc := 4 * N - 2 * S
    let V := 5 * N - 3 * S
    let E := 6 * N - 3 * S
    let TY := 12 * N - 6 * S
    let TJ := 11 * N - 6 * S
    let TH := 9 * N - 5 * S
    0 < D ∧ 0 < Cc ∧ 0 < V ∧ 0 < E ∧
      2 * N + 2 * D + Cc = TY ∧
      2 * N + 2 * V = TY ∧
      3 * Cc = TY ∧
      2 * E = TY ∧
      D + 2 * Cc = TJ ∧
      2 * N + 3 * D = TJ ∧
      V + E = TJ ∧
      D + E = TH ∧
      Cc + V = TH ∧
      2 * N < TJ ∧
      8 * N - 3 * S - 1 < TY ∧
      1 ≤ 8 * N - 3 * S ∧
      12 * N - 6 * S - (4 * N - 3 * S) - 1 = 8 * N - 3 * S - 1 := by
  omega

/-! ## Terminal `Y` state from the support-loaded parent -/

/-- The terminal row-one packet in the support-loaded ancestry has already
dropped `Y` strictly below its four-term top `12N-6S`. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_Y_state68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportLoadedPacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S) :
    let Y := -(2 : k) • (A * B ^ 2 * c) + (3 : k) • (A * d ^ 2) +
      (2 : k) • c ^ 3 - (9 : k) • e ^ 2
    Y.natDegree ≤ 8 * N - 3 * S - 1 := by
  let Y := -(2 : k) • (A * B ^ 2 * c) + (3 : k) • (A * d ^ 2) +
    (2 : k) • c ^ 3 - (9 : k) • e ^ 2
  change Y.natDegree ≤ 8 * N - 3 * S - 1
  rcases fiveToSix_zetaFirst_B3_equality_supportLoaded_source68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs with
      ⟨hGS, hGamma0, hsource⟩
  have hp0 := hsource
  change 0 < S ∧ S < 7 * N - 2 * G ∧ d.natDegree ≤ 5 * N - G - S ∧
      e.natDegree ≤ 6 * N - G - S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp0
  rcases hp0 with ⟨hS, hSR, hd, he, hpacket, hrest⟩
  rcases hpacket with ⟨hN, hgt, hle, hA, hB, hc, hd0, he0, hatop, hcusp, had⟩
  rcases hs with ⟨hsupport, _hrows⟩
  rcases hsupport with ⟨hstop, _hTD⟩
  rcases hstop with ⟨hcur, _ht, _hstate, _hclass, _hrow0, _hrow2⟩
  rcases hcur with ⟨hbase, _hbaseDrop⟩
  rcases hbase with ⟨hterminal, _hJold, _hrowOld0, _hrowOld2⟩
  rcases hterminal with ⟨_hgamma, hY⟩
  dsimp only [FiveToSixCuspZetaFirstB3EqualityYState68] at hY
  change Y.natDegree ≤ 12 * N - 6 * S - (4 * N - 3 * S) - 1 at hY
  have hidx : 12 * N - 6 * S - (4 * N - 3 * S) - 1 =
      8 * N - 3 * S - 1 := by omega
  rw [hidx] at hY
  exact hY

/-! ## The named vanishing-A packet is `False` -/

/-- Support-loaded `q=0` vanishing-A already contradicts the cusp
leading edges. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_impossible68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hterminal : terminal ≠ 0)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0) :
    False := by
  let D := 3 * N - 2 * S
  let Cc := 4 * N - 2 * S
  let V := 5 * N - 3 * S
  let E := 6 * N - 3 * S
  let TY := 12 * N - 6 * S
  let TJ := 11 * N - 6 * S
  let J := (B * c ^ 2 - (1 / 9 : k) • (A * B ^ 3)) - (3 : k) • (d * e)
  let Y := -(2 : k) • (A * B ^ 2 * c) + (3 : k) • (A * d ^ 2) +
    (2 : k) • c ^ 3 - (9 : k) • e ^ 2
  have hwall :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_wall_index68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only at hwall
  rcases hwall with ⟨hEq, hDpos, hDp, hDwin, hpU, hCcU, hKV, hND, hNV,
    hA', hB', hc', hd', he', ha0, hb0, hcusp⟩
  have hloaded := hs.1
  rcases fiveToSix_zetaFirst_B3_equality_supportLoaded_source68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hloaded with
      ⟨hGS, hGamma, hsource⟩
  have hp0 := hsource
  change 0 < S ∧ S < 7 * N - 2 * G ∧ d.natDegree ≤ 5 * N - G - S ∧
      e.natDegree ≤ 6 * N - G - S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp0
  rcases hp0 with ⟨hS, hSR, hd, he, hpacket, hrest⟩
  rcases hpacket with ⟨hN, hgt, hle, hA, hB, hc, hd0, he0, hatop, hcuspP, had⟩
  rcases hcuspP with ⟨hBtop, hctop, hdtop, hetop, hcuspEq⟩
  have hgt' : 5 * N < 4 * S := by omega
  have hle' : 4 * S ≤ 6 * N := by omega
  have hGamma' : 3 * S < 4 * N := by omega
  have harith :=
    fiveToSix_vanishingA_degree_arith68 N S hN hS hEq hgt' hle' hGamma'
  dsimp only [D, Cc, V, E, TY, TJ] at harith
  rcases harith with ⟨_, _, _, _, hAB2csum, hAd2sum, hc3sum, he2sum,
    hBc2sum, hAB3sum, hdesum, hDEsum, hCVsum, hJlt, hYlt, _, _⟩
  have hCidx : Cc = 4 * N - G := by dsimp only [Cc]; omega
  have hVidx : V = 5 * N - G - S := by dsimp only [V]; omega
  have hEidx : E = 6 * N - G - S := by dsimp only [E]; omega
  have hc0 : c.coeff Cc ≠ 0 := by rw [hCidx]; exact hctop
  have hd0c : d.coeff V ≠ 0 := by rw [hVidx]; exact hdtop
  have he0c : e.coeff E ≠ 0 := by rw [hEidx]; exact hetop
  have hres :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_top_resultant68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only at hres
  have hHlead :
      B.coeff D * e.coeff E + c.coeff Cc * d.coeff V = 0 := hres.1
  have hJdeg : J.natDegree ≤ 2 * N := by
    simpa [J] using
      fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_J_degree68
        alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hJcoeff : J.coeff TJ = 0 :=
    coeff_eq_zero_of_natDegree_lt (hJdeg.trans_lt hJlt)
  have hB3deg : (B ^ 3).natDegree ≤ 3 * D := by
    dsimp only [D]
    compute_degree
    omega
  have hc2deg : (c ^ 2).natDegree ≤ 2 * Cc := by
    dsimp only [Cc]
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
    have hidx : D + 2 * Cc = TJ := hBc2sum
    rw [← hidx, hBc2, hc2top]
  have hAB3top : (A * B ^ 3).coeff TJ =
      A.coeff (2 * N) * B.coeff D ^ 3 := by
    have hidx : 2 * N + 3 * D = TJ := hAB3sum
    rw [← hidx, hAB3, hB3top]
  have hdetop : (d * e).coeff TJ = d.coeff V * e.coeff E := by
    have hidx : V + E = TJ := hdesum
    rw [← hidx, hde]
  have hJlead :
      B.coeff D * c.coeff Cc ^ 2 -
        (1 / 9 : k) * A.coeff (2 * N) * B.coeff D ^ 3 -
        (3 : k) * d.coeff V * e.coeff E = 0 := by
    have hJexp : J.coeff TJ =
        (B * c ^ 2).coeff TJ -
          (1 / 9 : k) * (A * B ^ 3).coeff TJ -
          (3 : k) * (d * e).coeff TJ := by
      dsimp only [J]
      simp only [coeff_sub, coeff_smul, smul_eq_mul]
    rw [hBc2top, hAB3top, hdetop] at hJexp
    convert hJexp.symm.trans hJcoeff using 1
    ring
  have hYstate :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_Y_state68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hloaded
  have hYdeg : Y.natDegree ≤ 8 * N - 3 * S - 1 := by
    dsimp only [Y]; exact hYstate
  have hYjet : Y.coeff TY = 0 :=
    coeff_eq_zero_of_natDegree_lt (hYdeg.trans_lt hYlt)
  have hB2deg : (B ^ 2).natDegree ≤ 2 * D := by
    dsimp only [D]
    compute_degree
    omega
  have hB2top : (B ^ 2).coeff (2 * D) = B.coeff D ^ 2 :=
    coeff_pow_at_bound68 B D 2 hB'
  have hAB2c :=
    coeff_mul_mul_at_bounds68 A (B ^ 2) c (2 * N) (2 * D) Cc hA' hB2deg hc'
  rw [hAB2csum, hB2top] at hAB2c
  have hd2deg : (d ^ 2).natDegree ≤ 2 * V := by
    dsimp only [V]
    compute_degree
    omega
  have hd2top : (d ^ 2).coeff (2 * V) = d.coeff V ^ 2 :=
    coeff_pow_at_bound68 d V 2 hd'
  have hAd2 := coeff_mul_at_bounds68 A (d ^ 2) (2 * N) (2 * V) hA' hd2deg
  rw [hAd2sum, hd2top] at hAd2
  have hc3top : (c ^ 3).coeff (3 * Cc) = c.coeff Cc ^ 3 :=
    coeff_pow_at_bound68 c Cc 3 hc'
  rw [hc3sum] at hc3top
  have he2deg : (e ^ 2).natDegree ≤ 2 * E := by
    dsimp only [E]
    compute_degree
    omega
  have he2top : (e ^ 2).coeff (2 * E) = e.coeff E ^ 2 :=
    coeff_pow_at_bound68 e E 2 he'
  rw [he2sum] at he2top
  have hYlead :
      -(2 : k) * A.coeff (2 * N) * B.coeff D ^ 2 * c.coeff Cc +
        (3 : k) * A.coeff (2 * N) * d.coeff V ^ 2 +
        (2 : k) * c.coeff Cc ^ 3 - (9 : k) * e.coeff E ^ 2 = 0 := by
    have hYexp : Y.coeff TY =
        -(2 : k) * (A * B ^ 2 * c).coeff TY +
          (3 : k) * (A * d ^ 2).coeff TY +
          (2 : k) * (c ^ 3).coeff TY - (9 : k) * (e ^ 2).coeff TY := by
      dsimp only [Y]
      simp only [coeff_add, coeff_sub, coeff_neg, coeff_smul, smul_eq_mul]
    rw [hYexp, hAB2c, hAd2, hc3top, he2top] at hYjet
    convert hYjet using 1
    ring
  exact
    fiveToSix_vanishingA_leading_jet_false68
      (A.coeff (2 * N)) (B.coeff D) (c.coeff Cc) (d.coeff V) (e.coeff E)
      ha0 hb0 hc0 hd0c he0c hcusp hHlead hJlead hYlead

#print axioms fiveToSix_vanishingA_leading_jet_false68
#print axioms fiveToSix_vanishingA_degree_arith68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_Y_state68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_impossible68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAUniformCertificate68

end Max11DegreeRoutes
