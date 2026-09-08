import Grok68OffWallSupportScratch

/-! # Closure of the support-loaded off-wall packet `0<q`

`FiveToSixCuspZetaFirstSupportOffWallOpenResidual68` is the conjunction
of `FiveToSixCuspZetaFirstB3EqualitySupportLoadedPacket68` and
`FiveToSixCuspZetaFirstB3EqualitySupportOffWallResidual68`.  The residual
already has exact degrees of `A,B,c,d,e`, constant compensated I4/I3, and
the quadratic `4 B_D^2 c_Cc + 9 d_V^2 = 0`.  This file does not consume
the named next unused row `A_(2N-1)`.

On `G=2S` the four leading edges
`deg A=2N`, `deg B=D=3N-2S`, `deg c=Cc=4N-2S`, `deg d=V=5N-3S`,
`deg e=E=6N-3S` make `Be+cd`, `Q=Bc^{2}-(1/9)AB³`, and
`Y=-2AB²c+3Ad²+2c³-9e²` attain a common top.  Off the wall the I4
identity drops `deg(Be+cd)` to `3D=9N-6S`, so `(Be+cd)` vanishes at
degree `9N-5S`.  The retained `J` state writes `J_(11N-6S)=0`.  The
terminal row-one `Y` state writes `deg Y ≤ 8N-3S-1`, hence
`Y_(12N-6S)=0`.  Together with the cusp `A_(2N) B_D²+3 c_Cc²=0` this is
the same scalar system as the `G=2S` wall: Groebner contains `e^4`.
CAS: `derive_68_offwall_support_leadings.py`.  The extra off-wall
scalars `4 A_(2N) B_D³+27 d_V e_E=0` and `4 B_D² c_Cc+9 d_V²=0` lie in
the ideal of the cusp, of `Be+cd`, and of `J`, and are not needed for
the contradiction.  Without `Y` a nonzero sample exists.

The comparison is a coefficient at a single degree, not an evaluation
at roots of `B`, and not a finite-root shortcut.

This file does not thin
`Grok68ScaleZeroExclusionAssemblyScratch.lean`.

Exact gain: the support-loaded off-wall packet `0<q` is `False`.
Next unused row: branchwise among the remaining residual (gamma pair;
`A_(2N-4)` vanishing-A; terminal-zero beyond-wall; large terminal cusp).
Residual: the off-wall packet is closed; the assembly-facing endpoint
residual is unchanged.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualitySupportOffWallFalse68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Scalar leading-jet identity -/

/-- The four leading coefficients of the cusp, of `Be+cd`, of
`Q-3de`, and of `Y` cannot vanish together.  CAS:
`derive_68_offwall_support_leadings.py` records the same multipliers as
the `G=2S` wall: `3*J+(1/3)b*cusp = 4bc²-9de` and
`Y+2c*cusp = 3ad²+8c³-9e²`, after which `I4` and the cusp square force
both `4c³+9e²=0` and `4c³-9e²=0`. -/
theorem fiveToSix_offWall_support_leading_jet_false68
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

/-! ## Degree dictionary off the wall -/

/-- Common tops of `Y` and the already-killed `J` and `Be+cd` edges. -/
theorem fiveToSix_offWall_support_leading_degree_arith68
    (N S : ℕ) (hN : 0 < N) (hS : 0 < S)
    (hgt : 5 * N < 4 * S) (hle : 4 * S ≤ 6 * N) (hGamma : 3 * S < 4 * N)
    (hq : 0 < 9 * N - 7 * S) :
    let D := 3 * N - 2 * S
    let Cc := 4 * N - 2 * S
    let V := 5 * N - 3 * S
    let E := 6 * N - 3 * S
    let TY := 12 * N - 6 * S
    let TJ := 11 * N - 6 * S
    let TH := 9 * N - 5 * S
    2 * N + 2 * D + Cc = TY ∧
      2 * N + 2 * V = TY ∧
      3 * Cc = TY ∧
      2 * E = TY ∧
      D + 2 * Cc = TJ ∧
      2 * N + 3 * D = TJ ∧
      V + E = TJ ∧
      D + E = TH ∧
      Cc + V = TH ∧
      3 * D < TH ∧
      8 * N - 3 * S - 1 < TY ∧
      1 ≤ 8 * N - 3 * S ∧
      1 ≤ 4 * N - 3 * S ∧
      12 * N - 6 * S - (4 * N - 3 * S) - 1 = 8 * N - 3 * S - 1 := by
  let D := 3 * N - 2 * S
  let Cc := 4 * N - 2 * S
  let V := 5 * N - 3 * S
  let E := 6 * N - 3 * S
  let TY := 12 * N - 6 * S
  let TJ := 11 * N - 6 * S
  let TH := 9 * N - 5 * S
  change 2 * N + 2 * D + Cc = TY ∧
    2 * N + 2 * V = TY ∧
    3 * Cc = TY ∧
    2 * E = TY ∧
    D + 2 * Cc = TJ ∧
    2 * N + 3 * D = TJ ∧
    V + E = TJ ∧
    D + E = TH ∧
    Cc + V = TH ∧
    3 * D < TH ∧
    8 * N - 3 * S - 1 < TY ∧
    1 ≤ 8 * N - 3 * S ∧
    1 ≤ 4 * N - 3 * S ∧
    12 * N - 6 * S - (4 * N - 3 * S) - 1 = 8 * N - 3 * S - 1
  dsimp only [D, Cc, V, E, TY, TJ, TH]
  omega

/-! ## Terminal `Y` state from the support-loaded parent -/

/-- The terminal row-one packet in the support-loaded ancestry has already
dropped `Y` strictly below its four-term top `12N-6S`. -/
theorem fiveToSix_zetaFirst_B3_equality_support_offWall_Y_state68
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

/-! ## The named off-wall packet is `False` -/

/-- Support-loaded and strictly off the wall `0<9N-7S` already contradict
the cusp leading edges. -/
theorem fiveToSix_zetaFirst_B3_equality_support_offWall_false68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportLoadedPacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hr : FiveToSixCuspZetaFirstB3EqualitySupportOffWallResidual68
      gamma epsilon A B c d e N S) :
    False := by
  let D := 3 * N - 2 * S
  let Cc := 4 * N - 2 * S
  let V := 5 * N - 3 * S
  let E := 6 * N - 3 * S
  let TY := 12 * N - 6 * S
  let Y := -(2 : k) • (A * B ^ 2 * c) + (3 : k) • (A * d ^ 2) +
    (2 : k) • c ^ 3 - (9 : k) • e ^ 2
  have hq : 0 < 9 * N - 7 * S := by
    dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportOffWallResidual68]
      at hr
    exact hr.1
  have hrow :=
    fiveToSix_zetaFirst_B3_equality_support_rowOne_packet68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs
  have hdeg :=
    fiveToSix_zetaFirst_B3_equality_support_offWall_exact_degrees68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hrow hq
  rcases hdeg with
    ⟨hGS, hN, hS, hgt, hleN, hGamma, hDpos, hDltV, hVlt3D, hAdeg, hBdeg,
      hcdeg, hddeg, hedeg, hcuspEq, _hsource⟩
  have hAdeg : A.natDegree = 2 * N := hAdeg
  have hBdeg : B.natDegree = D := by dsimp only [D]; exact hBdeg
  have hcdeg : c.natDegree = Cc := by dsimp only [Cc]; exact hcdeg
  have hddeg : d.natDegree = V := by dsimp only [V]; exact hddeg
  have hedeg : e.natDegree = E := by dsimp only [E]; exact hedeg
  have hA : A.natDegree ≤ 2 * N := hAdeg.le
  have hB : B.natDegree ≤ D := hBdeg.le
  have hc : c.natDegree ≤ Cc := hcdeg.le
  have hd : d.natDegree ≤ V := hddeg.le
  have he : e.natDegree ≤ E := hedeg.le
  have ha : A.coeff (2 * N) ≠ 0 := by
    intro h0
    have hlead : A.leadingCoeff = 0 := by rw [leadingCoeff, hAdeg, h0]
    have hA0 : A = 0 := leadingCoeff_eq_zero.mp hlead
    have : 2 * N = 0 := by rw [← hAdeg, hA0, natDegree_zero]
    omega
  have hb : B.coeff D ≠ 0 := by
    intro h0
    have hlead : B.leadingCoeff = 0 := by rw [leadingCoeff, hBdeg, h0]
    have hB0 : B = 0 := leadingCoeff_eq_zero.mp hlead
    have : D = 0 := by rw [← hBdeg, hB0, natDegree_zero]
    dsimp only [D] at this
    omega
  have hc0 : c.coeff Cc ≠ 0 := by
    intro h0
    have hlead : c.leadingCoeff = 0 := by rw [leadingCoeff, hcdeg, h0]
    have hc00 : c = 0 := leadingCoeff_eq_zero.mp hlead
    have : Cc = 0 := by rw [← hcdeg, hc00, natDegree_zero]
    dsimp only [Cc] at this
    omega
  have hd0 : d.coeff V ≠ 0 := by
    intro h0
    have hlead : d.leadingCoeff = 0 := by rw [leadingCoeff, hddeg, h0]
    have hd00 : d = 0 := leadingCoeff_eq_zero.mp hlead
    have : V = 0 := by rw [← hddeg, hd00, natDegree_zero]
    dsimp only [V] at this
    omega
  have he0 : e.coeff E ≠ 0 := by
    intro h0
    have hlead : e.leadingCoeff = 0 := by rw [leadingCoeff, hedeg, h0]
    have he00 : e = 0 := leadingCoeff_eq_zero.mp hlead
    have : E = 0 := by rw [← hedeg, he00, natDegree_zero]
    dsimp only [E] at this
    omega
  have hcusp0 :
      A.coeff (2 * N) * B.coeff D ^ 2 + (3 : k) * c.coeff Cc ^ 2 = 0 := by
    dsimp only [D, Cc]; exact hcuspEq
  have hlead :=
    fiveToSix_zetaFirst_B3_equality_support_offWall_leading68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hrow hq
  have hJtop :
      (4 : k) * A.coeff (2 * N) * B.coeff D ^ 3 +
        (27 : k) * d.coeff V * e.coeff E = 0 := by
    dsimp only [D, V, E]; exact hlead.1
  have hHlead :
      B.coeff D * e.coeff E + c.coeff Cc * d.coeff V = 0 := by
    dsimp only [D, Cc, V, E]; exact hlead.2.2.1
  have hJlead :
      B.coeff D * c.coeff Cc ^ 2 -
        (1 / 9 : k) * A.coeff (2 * N) * B.coeff D ^ 3 -
        (3 : k) * d.coeff V * e.coeff E = 0 := by
    linear_combination (1 / 3 : k) * B.coeff D * hcusp0 -
      (1 / 9 : k) * hJtop
  have hAB2csum : 2 * N + 2 * D + Cc = TY := by
    dsimp only [D, Cc, TY]; omega
  have hAd2sum : 2 * N + 2 * V = TY := by
    dsimp only [V, TY]; omega
  have hc3sum : 3 * Cc = TY := by
    dsimp only [Cc, TY]; omega
  have he2sum : 2 * E = TY := by
    dsimp only [E, TY]; omega
  have hYlt : 8 * N - 3 * S - 1 < TY := by
    dsimp only [TY]; omega
  have hYstate :=
    fiveToSix_zetaFirst_B3_equality_support_offWall_Y_state68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs
  have hYdeg : Y.natDegree ≤ 8 * N - 3 * S - 1 := by
    dsimp only [Y]; exact hYstate
  have hYjet : Y.coeff TY = 0 :=
    coeff_eq_zero_of_natDegree_lt (hYdeg.trans_lt hYlt)
  have hB2deg : (B ^ 2).natDegree ≤ 2 * D := by
    dsimp only [D]
    compute_degree
    omega
  have hB2top : (B ^ 2).coeff (2 * D) = B.coeff D ^ 2 :=
    coeff_pow_at_bound68 B D 2 hB
  have hAB2c :=
    coeff_mul_mul_at_bounds68 A (B ^ 2) c (2 * N) (2 * D) Cc hA hB2deg hc
  rw [hAB2csum, hB2top] at hAB2c
  have hd2deg : (d ^ 2).natDegree ≤ 2 * V := by
    dsimp only [V]
    compute_degree
    omega
  have hd2top : (d ^ 2).coeff (2 * V) = d.coeff V ^ 2 :=
    coeff_pow_at_bound68 d V 2 hd
  have hAd2 := coeff_mul_at_bounds68 A (d ^ 2) (2 * N) (2 * V) hA hd2deg
  rw [hAd2sum, hd2top] at hAd2
  have hc3top : (c ^ 3).coeff (3 * Cc) = c.coeff Cc ^ 3 :=
    coeff_pow_at_bound68 c Cc 3 hc
  rw [hc3sum] at hc3top
  have he2deg : (e ^ 2).natDegree ≤ 2 * E := by
    dsimp only [E]
    compute_degree
    omega
  have he2top : (e ^ 2).coeff (2 * E) = e.coeff E ^ 2 :=
    coeff_pow_at_bound68 e E 2 he
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
    fiveToSix_offWall_support_leading_jet_false68
      (A.coeff (2 * N)) (B.coeff D) (c.coeff Cc) (d.coeff V) (e.coeff E)
      ha hb hc0 hd0 he0 hcusp0 hHlead hJlead hYlead

/-- Same `False` from the support-loaded parent and the chamber
inequality `0<q`. -/
theorem fiveToSix_zetaFirst_B3_equality_supportLoaded_offWall_false68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportLoadedPacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 0 < 9 * N - 7 * S) :
    False :=
  fiveToSix_zetaFirst_B3_equality_support_offWall_false68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs
    (fiveToSix_zetaFirst_B3_equality_supportLoaded_offWall68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq)

#print axioms fiveToSix_offWall_support_leading_jet_false68
#print axioms fiveToSix_offWall_support_leading_degree_arith68
#print axioms fiveToSix_zetaFirst_B3_equality_support_offWall_Y_state68
#print axioms fiveToSix_zetaFirst_B3_equality_support_offWall_false68
#print axioms fiveToSix_zetaFirst_B3_equality_supportLoaded_offWall_false68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualitySupportOffWallFalse68

end Max11DegreeRoutes
