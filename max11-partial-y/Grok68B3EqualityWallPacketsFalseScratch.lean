import Grok68NextTwoAndConstantFceWallsScratch

/-! # Closure of the three remaining G=2S wall packets

`FiveToSixCuspZetaFirstB3EqualityNextPacketWallPacket68`,
`FiveToSixCuspZetaFirstB3EqualityNextTwoGammaWallPacket68`, and
`FiveToSixCuspZetaFirstB3EqualityConstantFceWallPacket68` all sit on
`G=2S` with the B3-equality endpoint jets.  The sibling epsilon-B wall
is already `False` by arithmetic.  These three chambers are `False` by
an exact leading-coefficient comparison, not by a further source row.

On `G=2S` the four leading edges
`deg A=2N`, `deg B=D=3N-2S`, `deg c=Cc=4N-2S`, `deg d=V=5N-3S`,
`deg e=E=6N-3S` make `Be+cd`, `Q=Bc^{2}-(1/9)AB³`, and
`Y=-2AB²c+3Ad²+2c³-9e²` attain a common top.  The endpoint I4 packet
places `deg(Be+cd-(1/9)B³)` strictly below `deg(Be+cd)`, so
`(Be+cd)` vanishes at degree `9N-5S`.  Endpoint row two writes
`Q_(11N-6S)=3 d_V e_E`.  Endpoint row one writes `Y_(12N-6S)=0`.
Together with the cusp `A_(2N) B_D²+3 c_Cc²=0` this is the scalar
system whose Groebner basis contains `e^4`.  The comparison is a
coefficient at a single degree, not an evaluation at roots of `B`.

The next unused loaded row one (`S+1` / `S+2` / `S+3D`) is not
consumed: the endpoint jets already contradict the cusp edges.
This file does not thin
`Grok68ScaleZeroExclusionAssemblyScratch.lean`.

Exact gain: the three named wall packets are `False`.
Next unused row: branchwise among the remaining residual (gamma pair;
`A_(2N-1)` off-wall; `A_(2N-4)` vanishing-A; terminal-zero beyond-wall;
large terminal cusp).
Residual: the three wall packets are closed; the assembly-facing
endpoint residual is unchanged.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityWallPacketsFalse68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Scalar leading-jet identity -/

/-- The four leading coefficients of the cusp, of `Be+cd`, of
`Q-3de`, and of `Y` cannot vanish together.  CAS:
`derive_68_b3_equality_wall_leadings.py` records
`3*J+(1/3)b*cusp = 4bc²-9de` and `Y+2c*cusp = 3ad²+8c³-9e²`,
after which `I4` and the cusp square force both
`4c³+9e²=0` and `4c³-9e²=0`. -/
theorem fiveToSix_b3_equality_leading_jet_false68
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

/-! ## Degree dictionary on `G=2S` -/

/-- Common tops of `Be+cd`, `Q`, and `Y` on every gamma-inactive
equality cell. -/
theorem fiveToSix_b3_equality_G2S_degree_arith68
    (N G S : ℕ) (hN : 0 < N) (hGS : G = 2 * S)
    (hgt : 5 * N < 2 * G) (hle : 2 * G ≤ 6 * N)
    (hGamma : S < 4 * N - G) (hS : 0 < S) :
    0 < 3 * N - 2 * S ∧ 0 < 4 * N - 2 * S ∧
      0 < 5 * N - 3 * S ∧ 0 < 6 * N - 3 * S ∧
      3 * (3 * N - 2 * S) < 9 * N - 5 * S ∧
      9 * N - 6 * S - 1 < 9 * N - 5 * S ∧
      2 * N - 1 < 11 * N - 6 * S := by
  omega

/-! ## Source-facing extraction from the equality cell split -/

/-- Every `G=2S` B3-equality cell split already contradicts the cusp
leading edges. -/
theorem fiveToSix_b3_equality_cellSplit_G2S_false68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hcell : FiveToSixCuspZetaFirstB3EndpointCellSplitPacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hGS : G = 2 * S) :
    False := by
  let D := 3 * N - 2 * S
  let Cc := 4 * N - 2 * S
  let V := 5 * N - 3 * S
  let E := 6 * N - 3 * S
  let TY := 12 * N - 6 * S
  let TJ := 11 * N - 6 * S
  let TH := 9 * N - 5 * S
  let F := (B * e + c * d) - (1 / 9 : k) • B ^ 3
  let Q := B * c ^ 2 - (1 / 9 : k) • (A * B ^ 3)
  let Y := -(2 : k) • (A * B ^ 2 * c) + (3 : k) • (A * d ^ 2) +
    (2 : k) • c ^ 3 - (9 : k) • e ^ 2
  have hbase := hcell.1.1.1
  rcases hbase with ⟨hs, hBc, hGamma, q, hmuq, hqS, hprior, hminimal, hload,
    hi3, hi4, hend⟩
  have hp := hs
  change 0 < S ∧ S < 7 * N - 2 * G ∧ d.natDegree ≤ 5 * N - G - S ∧
      e.natDegree ≤ 6 * N - G - S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  rcases hp with ⟨hS, hSR, hd, he, hpC, hrest⟩
  rcases hpC with ⟨hN, hgt, hle, hA, hB, hc, hd0, he0, hatop, hcusp, had⟩
  rcases hcusp with ⟨hBtop, hctop, hdtop, hetop, hcuspEq⟩
  have harith :=
    fiveToSix_b3_equality_G2S_degree_arith68 N G S hN hGS hgt hle hGamma hS
  rcases harith with ⟨hDpos, hCpos, hVpos, hEpos, h3Dlt', hFlt', hJlt⟩
  have hDidx : D = 3 * N - G := by dsimp only [D]; omega
  have hCidx : Cc = 4 * N - G := by dsimp only [Cc]; omega
  have hVidx : V = 5 * N - G - S := by dsimp only [V]; omega
  have hEidx : E = 6 * N - G - S := by dsimp only [E]; omega
  have hTYg : 12 * N - 3 * G = TY := by dsimp only [TY]; omega
  have hTJg : 11 * N - 3 * G = TJ := by dsimp only [TJ]; omega
  have hAB2csum : 2 * N + 2 * D + Cc = TY := by
    dsimp only [D, Cc, TY]; omega
  have hAd2sum : 2 * N + 2 * V = TY := by dsimp only [V, TY]; omega
  have hc3sum : 3 * Cc = TY := by dsimp only [Cc, TY]; omega
  have he2sum : 2 * E = TY := by dsimp only [E, TY]; omega
  have hBc2sum : D + 2 * Cc = TJ := by dsimp only [D, Cc, TJ]; omega
  have hAB3sum : 2 * N + 3 * D = TJ := by dsimp only [D, TJ]; omega
  have hDEsum : D + E = TH := by dsimp only [D, E, TH]; omega
  have hCVsum : Cc + V = TH := by dsimp only [Cc, V, TH]; omega
  have hFlt : 9 * N - 6 * S - 1 < TH := by dsimp only [TH]; exact hFlt'
  have h3Dlt : 3 * D < TH := by dsimp only [D, TH]; exact h3Dlt'
  have hBdeg : B.natDegree ≤ D := by
    dsimp only [D]
    convert hB using 1 <;> omega
  have hcdeg : c.natDegree ≤ Cc := by
    dsimp only [Cc]
    convert hc using 1 <;> omega
  have hddeg : d.natDegree ≤ V := by
    dsimp only [V]
    convert hd using 1 <;> omega
  have hedeg : e.natDegree ≤ E := by
    dsimp only [E]
    convert he using 1 <;> omega
  have hb : B.coeff D ≠ 0 := by rw [hDidx]; exact hBtop
  have hc0 : c.coeff Cc ≠ 0 := by rw [hCidx]; exact hctop
  have hd0c : d.coeff V ≠ 0 := by rw [hVidx]; exact hdtop
  have he0c : e.coeff E ≠ 0 := by rw [hEidx]; exact hetop
  have hcusp0 :
      A.coeff (2 * N) * B.coeff D ^ 2 + (3 : k) * c.coeff Cc ^ 2 = 0 := by
    rw [hDidx, hCidx]
    exact hcuspEq
  have hYjet := hcell.1.1.2
  dsimp only [FiveToSixCuspZetaFirstB3EndpointRowOneContractedScalar68,
    FixedReflectedJet68] at hYjet
  have ht0 : 2 * S - G = 0 := by omega
  rw [ht0, coeff_reflect, revAt_zero, hTYg] at hYjet
  change Y.coeff TY = 0 at hYjet
  dsimp only [FiveToSixCuspZetaFirstB3EndpointRowTwoContractedScalar68,
    FixedReflectedJet68] at hend
  rw [ht0, coeff_reflect, revAt_zero, hTJg] at hend
  have hQtop : Q.coeff TJ = (3 : k) * d.coeff V * e.coeff E := by
    dsimp only [Q]
    rw [hVidx, hEidx]
    exact hend
  have hJtop : Q.coeff TJ - (3 : k) * d.coeff V * e.coeff E = 0 := by
    rw [hQtop, sub_self]
  have hFdeg : F.natDegree ≤ 9 * N - 6 * S - 1 := by
    dsimp only [FiveToSixCuspZetaFirstEndpointB3I4Packet68] at hi4
    have hFraw := hi4.1
    dsimp only [F]
    convert hFraw using 1 <;> omega
  have hF0 : F.coeff TH = 0 :=
    coeff_eq_zero_of_natDegree_lt (hFdeg.trans_lt hFlt)
  have hB3deg : (B ^ 3).natDegree ≤ 3 * D := by
    dsimp only [D]
    compute_degree
    omega
  have hB30 : (B ^ 3).coeff TH = 0 :=
    coeff_eq_zero_of_natDegree_lt (hB3deg.trans_lt h3Dlt)
  have hHtop : (B * e + c * d).coeff TH = 0 := by
    have hHF : B * e + c * d = F + (1 / 9 : k) • B ^ 3 := by
      dsimp only [F]
      simp only [sub_add_cancel]
    rw [hHF, coeff_add, coeff_smul, smul_eq_mul, hF0, hB30, mul_zero,
      add_zero]
  have hBe := coeff_mul_at_bounds68 B e D E hBdeg hedeg
  have hcd := coeff_mul_at_bounds68 c d Cc V hcdeg hddeg
  have hHlead :
      B.coeff D * e.coeff E + c.coeff Cc * d.coeff V = 0 := by
    have hBe' : (B * e).coeff TH = B.coeff D * e.coeff E := by
      rw [← hDEsum, hBe]
    have hcd' : (c * d).coeff TH = c.coeff Cc * d.coeff V := by
      rw [← hCVsum, hcd]
    have hsum : (B * e + c * d).coeff TH =
        B.coeff D * e.coeff E + c.coeff Cc * d.coeff V := by
      rw [coeff_add, hBe', hcd']
    exact hsum.symm.trans hHtop
  have hB2deg : (B ^ 2).natDegree ≤ 2 * D := by
    dsimp only [D]
    compute_degree
    omega
  have hB2top : (B ^ 2).coeff (2 * D) = B.coeff D ^ 2 :=
    coeff_pow_at_bound68 B D 2 hBdeg
  have hAB2c :=
    coeff_mul_mul_at_bounds68 A (B ^ 2) c (2 * N) (2 * D) Cc hA hB2deg
      hcdeg
  rw [hAB2csum, hB2top] at hAB2c
  have hd2deg : (d ^ 2).natDegree ≤ 2 * V := by
    dsimp only [V]
    compute_degree
    omega
  have hd2top : (d ^ 2).coeff (2 * V) = d.coeff V ^ 2 :=
    coeff_pow_at_bound68 d V 2 hddeg
  have hAd2 := coeff_mul_at_bounds68 A (d ^ 2) (2 * N) (2 * V) hA hd2deg
  rw [hAd2sum, hd2top] at hAd2
  have hc3top : (c ^ 3).coeff (3 * Cc) = c.coeff Cc ^ 3 :=
    coeff_pow_at_bound68 c Cc 3 hcdeg
  rw [hc3sum] at hc3top
  have he2deg : (e ^ 2).natDegree ≤ 2 * E := by
    dsimp only [E]
    compute_degree
    omega
  have he2top : (e ^ 2).coeff (2 * E) = e.coeff E ^ 2 :=
    coeff_pow_at_bound68 e E 2 hedeg
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
  have hB3top : (B ^ 3).coeff (3 * D) = B.coeff D ^ 3 :=
    coeff_pow_at_bound68 B D 3 hBdeg
  have hAB3 :=
    coeff_mul_at_bounds68 A (B ^ 3) (2 * N) (3 * D) hA hB3deg
  rw [hAB3sum, hB3top] at hAB3
  have hc2deg : (c ^ 2).natDegree ≤ 2 * Cc := by
    dsimp only [Cc]
    compute_degree
    omega
  have hc2top : (c ^ 2).coeff (2 * Cc) = c.coeff Cc ^ 2 :=
    coeff_pow_at_bound68 c Cc 2 hcdeg
  have hBc2 := coeff_mul_at_bounds68 B (c ^ 2) D (2 * Cc) hBdeg hc2deg
  rw [hBc2sum, hc2top] at hBc2
  have hJlead :
      B.coeff D * c.coeff Cc ^ 2 -
        (1 / 9 : k) * A.coeff (2 * N) * B.coeff D ^ 3 -
        (3 : k) * d.coeff V * e.coeff E = 0 := by
    dsimp only [Q] at hJtop
    simp only [coeff_sub, coeff_smul, smul_eq_mul] at hJtop
    rw [hBc2, hAB3] at hJtop
    convert hJtop using 1
    ring
  exact
    fiveToSix_b3_equality_leading_jet_false68
      (A.coeff (2 * N)) (B.coeff D) (c.coeff Cc) (d.coeff V) (e.coeff E)
      hatop hb hc0 hd0c he0c hcusp0 hHlead hJlead hYlead

/-! ## The three named packets -/

/-- The `NextPacket` wall `4N-3S=1` is `False`. -/
theorem fiveToSix_zetaFirst_B3_equality_next_wall_false68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hp : FiveToSixCuspZetaFirstB3EqualityNextPacketWallPacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S) :
    False := by
  rcases hp with ⟨hGS, _hwall, hcell, _⟩
  exact
    fiveToSix_b3_equality_cellSplit_G2S_false68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S hcell hGS

/-- The NextTwo gamma-d wall `4N-3S=2` is `False`. -/
theorem fiveToSix_zetaFirst_B3_equality_nextTwo_gamma_wall_false68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hp : FiveToSixCuspZetaFirstB3EqualityNextTwoGammaWallPacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S) :
    False := by
  rcases hp with ⟨hGS, _hwall, hcell, _⟩
  exact
    fiveToSix_b3_equality_cellSplit_G2S_false68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S hcell hGS

/-- The constant-`Fce` wall `D<T` is `False`. -/
theorem fiveToSix_zetaFirst_B3_equality_constantFce_wall_false68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hp : FiveToSixCuspZetaFirstB3EqualityConstantFceWallPacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S) :
    False := by
  rcases hp with ⟨hpC, _⟩
  rcases hpC with ⟨hstop, _hDT, _hdrop⟩
  rcases hstop with ⟨hcur, _ht, _hstate, _hclass, _hrow0, _hrow2⟩
  rcases hcur with ⟨hbase, _hbaseDrop⟩
  rcases hbase with ⟨hterminal, _hJold, _hrowOld0, _hrowOld2⟩
  rcases hterminal with ⟨hgamma, _hY⟩
  rcases hgamma with ⟨hgammaStop, _hcontract⟩
  rcases hgammaStop with ⟨hnext, _ha, _hjet, _hgammaRow0, _hgammaRow2⟩
  rcases hnext.1 with ⟨hGS, hcell, _hprev⟩
  exact
    fiveToSix_b3_equality_cellSplit_G2S_false68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S hcell hGS

#print axioms fiveToSix_b3_equality_leading_jet_false68
#print axioms fiveToSix_b3_equality_G2S_degree_arith68
#print axioms fiveToSix_b3_equality_cellSplit_G2S_false68
#print axioms fiveToSix_zetaFirst_B3_equality_next_wall_false68
#print axioms fiveToSix_zetaFirst_B3_equality_nextTwo_gamma_wall_false68
#print axioms fiveToSix_zetaFirst_B3_equality_constantFce_wall_false68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityWallPacketsFalse68

end Max11DegreeRoutes
