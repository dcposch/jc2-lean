import Sol68FiveToSixCuspFiniteStoppingScratch

/-! # Exact third cusp jet in the five-to-six chamber

The normalized combination `(-9/8) B*I3 + (9/8) c*I4` exposes the
finite invariant directly.  Its leading block is

  `(A*B^2 + 3*c^2) * d`.

At contracted depth two, the old cusp and the homogeneous depth-one
compatibility kill its first two convolution terms.  The only possible
remaining loads are `d^2` when `S=2` and `zeta*A` when
`7N-2G-S=2`.  This file keeps those walls separate and exact.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspThirdJet68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def fiveToSixCuspDiscriminantPolynomial68
    (A B c : k[X]) : k[X] := A * B ^ 2 + (3 : k) • c ^ 2

/-- Exact polynomial factorization behind every homogeneous cusp jet. -/
theorem fiveToSix_firstIntegrals_cuspCombination68
    (gamma epsilon zeta : k) (A B c d e : k[X]) :
    (-9 / 8 : k) •
        (B * cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon zeta
          A B c ((1 / 3 : k) • (A * B) + d) e) +
      (9 / 8 : k) •
        (c * cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon zeta
          A B c ((1 / 3 : k) • (A * B) + d) e) =
      fiveToSixCuspDiscriminantPolynomial68 A B c * d +
        (2 / 3 : k) • (B ^ 3 * c) - (3 / 2 : k) • (B * d ^ 2) +
        (9 / 8 * zeta : k) • (A * c - B ^ 2) +
        (9 / 2 * gamma : k) • (c * d - B * e) +
        (3 / 4 * gamma : k) • B ^ 3 := by
  rw [cubicFirstIntegralThreePolynomial68_fiveToSix_residualCoordinates,
    cubicFirstIntegralFourPolynomial68_fiveToSix_residualCoordinates]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [fiveToSixCuspDiscriminantPolynomial68,
    secondaryResidualInvariantThreePolynomial68,
    secondaryResidualInvariantFourPolynomial68, Polynomial.smul_eq_C_mul,
    map_add, map_sub, map_mul, map_pow, map_neg, map_zero,
    RatFunc.algebraMap_C]
  simp only [map_div₀, map_ofNat, map_one]
  have hneg9 : RatFunc.C (-9 : k) = (-9 : RatFunc k) := by
    rw [show (-9 : k) = -(9 : k) by norm_num, map_neg, map_ofNat]
  have hneg8 : RatFunc.C (-8 : k) = (-8 : RatFunc k) := by
    rw [show (-8 : k) = -(8 : k) by norm_num, map_neg, map_ofNat]
  rw [hneg9, hneg8]
  ring

/-- A coefficient one below two fixed degree bounds. -/
theorem coeff_mul_at_reflect_one_cusp68 (p q : k[X]) (u v : ℕ)
    (hp : p.natDegree ≤ u) (hq : q.natDegree ≤ v)
    (hsum : 1 ≤ u + v) :
    (p * q).coeff (u + v - 1) =
      (p.reflect u).coeff 0 * (q.reflect v).coeff 1 +
        (p.reflect u).coeff 1 * (q.reflect v).coeff 0 := by
  have h := congrArg (fun r : k[X] => r.coeff 1)
    (reflect_mul p q hp hq)
  rw [coeff_reflect, revAt_le hsum, mul_coeff_one] at h
  exact h

/-- Exact depth-two output.  The four implications are, respectively,
the homogeneous case, the `d^2` wall, the `zeta*A` wall, and their
simultaneous intersection. -/
def FiveToSixCuspThirdJetFactor68
    (zeta : k) (A B c d : k[X]) (N G S : ℕ) : Prop :=
  let Delta := fiveToSixCuspDiscriminantPolynomial68 A B c
  let U := 8 * N - 2 * G
  let V := 5 * N - G - S
  let a := A.coeff (2 * N)
  let b := B.coeff (3 * N - G)
  let c0 := c.coeff (4 * N - G)
  let ds := d.coeff V
  let delta2 := (Delta.reflect U).coeff 2
  (Delta.reflect U).coeff 0 = 0 ∧
    (Delta.reflect U).coeff 1 = 0 ∧
    (2 < S → 2 < 7 * N - 2 * G - S → delta2 = 0) ∧
    (S = 2 → 2 < 7 * N - 2 * G - S →
      delta2 * ds - (3 / 2 : k) * b * ds ^ 2 = 0) ∧
    (2 < S → 7 * N - 2 * G - S = 2 →
      delta2 * ds + (9 / 8 : k) * zeta * a * c0 = 0) ∧
    (S = 2 → 7 * N - 2 * G - S = 2 →
      delta2 * ds + (9 / 8 : k) * zeta * a * c0 -
        (3 / 2 : k) * b * ds ^ 2 = 0)

set_option maxHeartbeats 30000000 in
theorem fiveToSix_contractedCusp_thirdJet_factor68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hpacket : FiveToSixContractedCuspPacket68
      alpha gamma epsilon zeta eta terminal A B c d e N G S)
    (hS2 : 2 ≤ S) (hZ2 : 2 ≤ 7 * N - 2 * G - S)
    (hdSharp : d.natDegree ≤ 5 * N - G - S)
    (heSharp : e.natDegree ≤ 6 * N - G - S) :
    FiveToSixCuspThirdJetFactor68 zeta A B c d N G S := by
  rcases hpacket with
    ⟨hN, hgt5, hle6, hA, hB, hc, _hd, _he, _ha, hcusp, hadapter⟩
  rcases hcusp with ⟨hb, hc0, hds, _hes, hcusp0⟩
  rcases hadapter with
    ⟨i4, i3, hi4, hi3, _hrow0, _hrow1, _hrow2, _hrow0pos, _hiff⟩
  let R := 7 * N - 2 * G
  let U := 8 * N - 2 * G
  let V := 5 * N - G - S
  let Delta := fiveToSixCuspDiscriminantPolynomial68 A B c
  have hR : R = 7 * N - 2 * G := rfl
  have hU : U = 8 * N - 2 * G := rfl
  have hV : V = 5 * N - G - S := rfl
  have hDelta : Delta.natDegree ≤ U := by
    dsimp only [Delta, U, fiveToSixCuspDiscriminantPolynomial68]
    compute_degree
    omega
  have hB2 : (B ^ 2).natDegree ≤ 6 * N - 2 * G := by
    compute_degree
    omega
  have hB2top := coeff_mul_at_bounds68 B B (3 * N - G) (3 * N - G)
    hB hB
  rw [← pow_two, show (3 * N - G) + (3 * N - G) = 6 * N - 2 * G
    from by omega] at hB2top
  have hAB2top := coeff_mul_at_bounds68 A (B ^ 2)
    (2 * N) (6 * N - 2 * G) hA hB2
  rw [show 2 * N + (6 * N - 2 * G) = U from by omega, hB2top]
    at hAB2top
  have hc2top := coeff_mul_at_bounds68 c c (4 * N - G) (4 * N - G)
    hc hc
  rw [← pow_two, show (4 * N - G) + (4 * N - G) = U from by omega]
    at hc2top
  have hDeltaTop : Delta.coeff U = 0 := by
    dsimp only [Delta, fiveToSixCuspDiscriminantPolynomial68]
    rw [coeff_add, coeff_smul, smul_eq_mul, hAB2top, hc2top]
    linear_combination hcusp0
  have hDelta0 : (Delta.reflect U).coeff 0 = 0 := by
    simpa only [coeff_reflect, revAt_zero] using hDeltaTop
  have hdsR : (d.reflect V).coeff 0 ≠ 0 := by
    simpa only [coeff_reflect, revAt_zero, V] using hds

  have hidentity := fiveToSix_firstIntegrals_cuspCombination68
    gamma epsilon zeta A B c d e

  have hlow_common (q : ℕ) (hq : q ≤ 2) :
      (B ^ 3 * c).natDegree < 13 * N - 3 * G - S - q ∧
      (B ^ 2).natDegree < 13 * N - 3 * G - S - q ∧
      (c * d - B * e).natDegree < 13 * N - 3 * G - S - q ∧
      (B ^ 3).natDegree < 13 * N - 3 * G - S - q := by
    constructor
    · compute_degree
      omega
    constructor
    · compute_degree
      omega
    constructor
    · compute_degree
      omega
    · compute_degree
      omega
  have hright_common (q : ℕ) (hq : q ≤ 2) :
      B.natDegree < 13 * N - 3 * G - S - q ∧
      c.natDegree < 13 * N - 3 * G - S - q := by
    constructor <;> omega

  have hcombination_coeff (q : ℕ) (hq : 1 ≤ q) (hq2 : q ≤ 2)
      (hqS : q ≤ S) (hqZ : q ≤ R - S) :
      (Delta * d).coeff (U + V - q) +
        (9 / 8 * zeta : k) * (A * c).coeff (U + V - q) -
        (3 / 2 : k) * (B * d ^ 2).coeff (U + V - q) = 0 := by
    have hidx : U + V - q = 13 * N - 3 * G - S - q := by omega
    have hlow := hlow_common q hq2
    have hright := hright_common q hq2
    have hBzero : B.coeff (U + V - q) = 0 :=
      coeff_eq_zero_of_natDegree_lt (by rw [hidx]; exact hright.1)
    have hczero : c.coeff (U + V - q) = 0 :=
      coeff_eq_zero_of_natDegree_lt (by rw [hidx]; exact hright.2)
    have hB3czero : (B ^ 3 * c).coeff (U + V - q) = 0 :=
      coeff_eq_zero_of_natDegree_lt (by rw [hidx]; exact hlow.1)
    have hB2zero : (B ^ 2).coeff (U + V - q) = 0 :=
      coeff_eq_zero_of_natDegree_lt (by rw [hidx]; exact hlow.2.1)
    have hcdzero : (c * d).coeff (U + V - q) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      compute_degree
      omega
    have hBezero : (B * e).coeff (U + V - q) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      compute_degree
      omega
    have hB3zero : (B ^ 3).coeff (U + V - q) = 0 :=
      coeff_eq_zero_of_natDegree_lt (by rw [hidx]; exact hlow.2.2.2)
    have hz := congrArg (fun p : k[X] => p.coeff (U + V - q)) hidentity
    rw [hi3, hi4] at hz
    simp only [coeff_add, coeff_sub, coeff_smul, smul_eq_mul,
      coeff_mul_C, hBzero, hczero, hB3czero, hB2zero, hcdzero, hBezero,
      hB3zero] at hz
    simp only [zero_mul, mul_zero, add_zero, sub_zero] at hz
    change 0 = (Delta * d).coeff (U + V - q) -
      (3 / 2 : k) * (B * d ^ 2).coeff (U + V - q) +
      (9 / 8 : k) * zeta * (A * c).coeff (U + V - q) at hz
    linear_combination -hz

  have hAc1 : (A * c).coeff (U + V - 1) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    compute_degree
    omega
  have hBd1 : (B * d ^ 2).coeff (U + V - 1) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    compute_degree
    omega
  have hprod1raw := hcombination_coeff 1 (by omega) (by omega)
    (by omega) (by omega)
  have hprod1 : (Delta * d).coeff (U + V - 1) = 0 := by
    rw [hAc1, hBd1] at hprod1raw
    linear_combination hprod1raw
  have href1 := coeff_mul_at_reflect_one_cusp68 Delta d U V
    hDelta hdSharp (by omega)
  rw [show U + V - 1 = U + V - 1 from rfl] at href1
  rw [href1, hDelta0, zero_mul, zero_add] at hprod1
  have hDelta1 : (Delta.reflect U).coeff 1 = 0 :=
    (mul_eq_zero.mp hprod1).resolve_right hdsR

  have hprod2 := hcombination_coeff 2 (by omega) (by omega) hS2 hZ2
  have href2 := coeff_mul_at_reflect_two68 Delta d U V
    hDelta hdSharp (by omega)
  rw [href2, hDelta0, hDelta1, zero_mul, zero_add] at hprod2
  have hbase : (Delta.reflect U).coeff 2 * (d.reflect V).coeff 0 +
      (9 / 8 : k) * zeta * (A * c).coeff (U + V - 2) -
      (3 / 2 : k) * (B * d ^ 2).coeff (U + V - 2) = 0 := by
    linear_combination hprod2

  have hActop := coeff_mul_at_bounds68 A c (2 * N) (4 * N - G) hA hc
  have hBtop := hB
  have hd2bound : (d ^ 2).natDegree ≤ 2 * V := by
    dsimp only [V]
    compute_degree
    omega
  have hd2top := coeff_mul_at_bounds68 d d V V hdSharp hdSharp
  rw [← pow_two] at hd2top
  have hd2top' : (d ^ 2).coeff (2 * V) = d.coeff V ^ 2 := by
    rw [show 2 * V = V + V from by omega, hd2top]
    ring
  have hBdtop := coeff_mul_at_bounds68 B (d ^ 2)
    (3 * N - G) (2 * V) hB hd2bound
  rw [hd2top'] at hBdtop
  have hAc_deep (hz : 2 < R - S) :
      (A * c).coeff (U + V - 2) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    compute_degree
    omega
  have hAc_wall (hz : R - S = 2) :
      (A * c).coeff (U + V - 2) =
        A.coeff (2 * N) * c.coeff (4 * N - G) := by
    rw [show U + V - 2 = 2 * N + (4 * N - G) from by omega]
    exact hActop
  have hBd_deep (hs : 2 < S) :
      (B * d ^ 2).coeff (U + V - 2) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    compute_degree
    omega
  have hBd_wall (hs : S = 2) :
      (B * d ^ 2).coeff (U + V - 2) =
        B.coeff (3 * N - G) * d.coeff V ^ 2 := by
    rw [show U + V - 2 = (3 * N - G) + 2 * V from by omega]
    exact hBdtop
  have hds0 : (d.reflect V).coeff 0 = d.coeff V := by
    simp only [coeff_reflect, revAt_zero]
  change (Delta.reflect U).coeff 0 = 0 ∧
    (Delta.reflect U).coeff 1 = 0 ∧ _
  refine ⟨hDelta0, hDelta1, ?_, ?_, ?_, ?_⟩
  · intro hs hz
    rw [hAc_deep hz, hBd_deep hs, hds0] at hbase
    have hfac : (Delta.reflect U).coeff 2 * d.coeff V = 0 := by
      linear_combination hbase
    exact (mul_eq_zero.mp hfac).resolve_right hds
  · intro hs hz
    rw [hAc_deep hz, hBd_wall hs, mul_zero, hds0] at hbase
    linear_combination hbase
  · intro hs hz
    rw [hAc_wall hz, hBd_deep hs, mul_zero, sub_zero, hds0] at hbase
    linear_combination hbase
  · intro hs hz
    rw [hAc_wall hz, hBd_wall hs, hds0] at hbase
    linear_combination hbase

/-- Source data at an earlier cusp either reaches its first load already at
depth one, or carries the exact depth-two factorization above. -/
def FiveToSixContractedEarlierThirdJetAssembly68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e Ae Be ce de ee : k[X]) (n g : ℕ) : Prop :=
  FiveToSixContractedEarlierFiniteStopAssembly68
      alpha gamma epsilon zeta eta terminal
      A B c d e Ae Be ce de ee n g ∧
    ∃ N G S, n = 60 * N ∧ g = 60 * G ∧
      (min S (7 * N - 2 * G - S) = 1 ∨
        FiveToSixCuspThirdJetFactor68 zeta A B c d N G S)

theorem fiveToSix_contractedEarlierFiniteStop_thirdJet68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e Ae Be ce de ee : k[X]) (n g : ℕ)
    (hfinite : FiveToSixContractedEarlierFiniteStopAssembly68
      alpha gamma epsilon zeta eta terminal
      A B c d e Ae Be ce de ee n g) :
    FiveToSixContractedEarlierThirdJetAssembly68
      alpha gamma epsilon zeta eta terminal
      A B c d e Ae Be ce de ee n g := by
  refine ⟨hfinite, ?_⟩
  rcases hfinite.1 with
    ⟨_s, N, G, S, hn, hg, _hs, _hN, hS, hSR,
      hdSharp, heSharp, hpacket, _hsecond⟩
  refine ⟨N, G, S, hn, hg, ?_⟩
  by_cases hmu : min S (7 * N - 2 * G - S) = 1
  · exact Or.inl hmu
  · right
    have hmuPos : 0 < min S (7 * N - 2 * G - S) := by
      rcases le_total S (7 * N - 2 * G - S) with hleft | hright
      · rw [Nat.min_eq_left hleft]
        exact hS
      · rw [Nat.min_eq_right hright]
        omega
    have hmu2 : 2 ≤ min S (7 * N - 2 * G - S) := by omega
    exact fiveToSix_contractedCusp_thirdJet_factor68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hpacket
      (le_trans hmu2 (Nat.min_le_left _ _))
      (le_trans hmu2 (Nat.min_le_right _ _)) hdSharp heSharp

/-- Full source wrapper, preserving both terminal alternatives exactly. -/
theorem integratedPolynomialLowerSystem68_fiveToSix_thirdJet_assembly68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E) :
    let n := weightedRadius68 A B C0 D E
    let Ae := expand k 60 A
    let Be := expand k 60 B
    let Ce := expand k 60 C0
    let ce := cubicCDefectPolynomial68 Ae Ce
    let De := expand k 60 D
    let Ee := expand k 60 E
    let ee := cubicEDefectPolynomial68 Ae Ce Ee
    let g := cubicDefectGap68 n Be ce De ee
    let d := secondaryDDefectPolynomial68 Ae Be De
    FiveToSixTerminalZeroPacket68 zeta d ee n g ∨
      FiveToSixContractedEarlierThirdJetAssembly68
        alpha gamma epsilon zeta eta terminal
        A B (cubicCDefectPolynomial68 A C0)
        (secondaryDDefectPolynomial68 A B D)
        (cubicEDefectPolynomial68 A C0 E)
        Ae Be ce d ee n g ∨
      (120 < n ∧ 60 ∣ n ∧ 60 ∣ g ∧
        d.natDegree ≤ g - 2 * n ∧ ee.natDegree ≤ g - n ∧ zeta = 0 ∧
        FiveToSixCuspEdge68 Ae Be ce d ee n g (7 * n - 2 * g)) := by
  dsimp only
  rcases integratedPolynomialLowerSystem68_fiveToSix_finiteStop_assembly68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys with hzero | hearlier | hterminalCusp
  · exact Or.inl hzero
  · exact Or.inr (Or.inl
      (fiveToSix_contractedEarlierFiniteStop_thirdJet68
        (hfinite := hearlier)))
  · exact Or.inr (Or.inr hterminalCusp)

#print axioms fiveToSix_firstIntegrals_cuspCombination68
#print axioms coeff_mul_at_reflect_one_cusp68
#print axioms fiveToSix_contractedCusp_thirdJet_factor68
#print axioms fiveToSix_contractedEarlierFiniteStop_thirdJet68
#print axioms integratedPolynomialLowerSystem68_fiveToSix_thirdJet_assembly68

end FiveToSixCuspThirdJet68

end Max11DegreeRoutes
