import Sol68FiveToSixCuspThirdJetScratch

/-! # Finite discriminant convolution at an arbitrary cusp depth

The exact first-integral combination from the third-jet file works at every
contracted depth.  Reflection turns its leading term `Delta*d` into an
ordinary coefficient convolution.  Since the edge coefficient of `d` is
nonzero, strong induction kills every `Delta` jet strictly before the first
load `mu = min(S, 7N-2G-S)`.  At `mu` the same convolution leaves exactly
the `d^2`, `zeta*A`, or simultaneous loaded scalar.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspConvolution68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- If every lower coefficient of the left factor vanishes, the coefficient
of a product is its new left coefficient times the constant right edge. -/
theorem mul_coeff_eq_left_edge_of_lower_zero68
    (p q : k[X]) (t : ℕ)
    (hzero : ∀ j, j < t → p.coeff j = 0) :
    (p * q).coeff t = p.coeff t * q.coeff 0 := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [Finset.sum_eq_single t]
  · simp
  · intro j hj hne
    have hjt : j < t := by
      have := Finset.mem_range.mp hj
      omega
    rw [hzero j hjt, zero_mul]
  · intro ht
    exact (ht (Finset.mem_range.mpr (Nat.lt_succ_self t))).elim

/-- Reflected fixed-bound form of the same convolution. -/
theorem coeff_mul_at_reflect_of_left_lower_zero68
    (p q : k[X]) (u v t : ℕ)
    (hp : p.natDegree ≤ u) (hq : q.natDegree ≤ v)
    (ht : t ≤ u + v)
    (hzero : ∀ j, j < t → (p.reflect u).coeff j = 0) :
    (p * q).coeff (u + v - t) =
      (p.reflect u).coeff t * (q.reflect v).coeff 0 := by
  have h := congrArg (fun r : k[X] => r.coeff t)
    (reflect_mul p q hp hq)
  rw [coeff_reflect, revAt_le ht,
    mul_coeff_eq_left_edge_of_lower_zero68 _ _ _ hzero] at h
  exact h

/-- Exact first-load residual after the complete homogeneous induction. -/
def FiveToSixCuspFirstLoadFactor68
    (zeta : k) (A B c d : k[X]) (N G S : ℕ) : Prop :=
  let R := 7 * N - 2 * G
  let mu := min S (R - S)
  let Delta := fiveToSixCuspDiscriminantPolynomial68 A B c
  let U := 8 * N - 2 * G
  let V := 5 * N - G - S
  let a := A.coeff (2 * N)
  let b := B.coeff (3 * N - G)
  let c0 := c.coeff (4 * N - G)
  let ds := d.coeff V
  (∀ q, q < mu → (Delta.reflect U).coeff q = 0) ∧
    ((S < R - S ∧ mu = S ∧
        (Delta.reflect U).coeff mu * ds -
          (3 / 2 : k) * b * ds ^ 2 = 0) ∨
      (R - S < S ∧ mu = R - S ∧
        (Delta.reflect U).coeff mu * ds +
          (9 / 8 : k) * zeta * a * c0 = 0) ∨
      (S = R - S ∧ mu = S ∧ mu = R - S ∧
        (Delta.reflect U).coeff mu * ds +
            (9 / 8 : k) * zeta * a * c0 -
          (3 / 2 : k) * b * ds ^ 2 = 0))

set_option maxHeartbeats 30000000 in
theorem fiveToSix_contractedCusp_firstLoad_convolution68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hpacket : FiveToSixContractedCuspPacket68
      alpha gamma epsilon zeta eta terminal A B c d e N G S)
    (hS : 0 < S) (hSR : S < 7 * N - 2 * G)
    (hdSharp : d.natDegree ≤ 5 * N - G - S)
    (heSharp : e.natDegree ≤ 6 * N - G - S) :
    FiveToSixCuspFirstLoadFactor68 zeta A B c d N G S := by
  rcases hpacket with
    ⟨hN, hgt5, hle6, hA, hB, hc, _hd, _he, _ha, hcusp, hadapter⟩
  rcases hcusp with ⟨_hb, _hc0, hds, _hes, hcusp0⟩
  rcases hadapter with
    ⟨i4, i3, hi4, hi3, _hrow0, _hrow1, _hrow2, _hrow0pos, _hiff⟩
  let R := 7 * N - 2 * G
  let mu := min S (R - S)
  let U := 8 * N - 2 * G
  let V := 5 * N - G - S
  let Delta := fiveToSixCuspDiscriminantPolynomial68 A B c
  have hmuS : mu ≤ S := Nat.min_le_left _ _
  have hmuZ : mu ≤ R - S := Nat.min_le_right _ _
  have hstop := fiveToSix_cuspJet_finiteStop_arithmetic68
    N G S hN ⟨hgt5, hle6⟩ hS hSR
  change 0 < mu ∧ _ ∧ _ ∧ _ at hstop
  have hmuPos := hstop.1
  have hwallCases := hstop.2.2.2
  have hRG : R < G := by omega
  have hmuGamma : mu < 4 * N - G := by
    rcases le_total S (R - S) with hleft | hright
    · have htwice : 2 * S ≤ R := by omega
      omega
    · have htwice : 2 * (R - S) ≤ R := by omega
      omega
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

  have hcombination_coeff (q : ℕ) (hq : q ≤ mu) :
      (Delta * d).coeff (U + V - q) +
        (9 / 8 * zeta : k) * (A * c).coeff (U + V - q) -
        (3 / 2 : k) * (B * d ^ 2).coeff (U + V - q) = 0 := by
    have hidx : U + V - q = 13 * N - 3 * G - S - q := by omega
    have hBzero : B.coeff (U + V - q) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      omega
    have hczero : c.coeff (U + V - q) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      omega
    have hB3czero : (B ^ 3 * c).coeff (U + V - q) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      compute_degree
      omega
    have hB2zero : (B ^ 2).coeff (U + V - q) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      compute_degree
      omega
    have hcdzero : (c * d).coeff (U + V - q) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      compute_degree
      omega
    have hBezero : (B * e).coeff (U + V - q) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      compute_degree
      omega
    have hB3zero : (B ^ 3).coeff (U + V - q) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      compute_degree
      omega
    have hz := congrArg (fun p : k[X] => p.coeff (U + V - q)) hidentity
    rw [hi3, hi4] at hz
    simp only [coeff_add, coeff_sub, coeff_smul, smul_eq_mul,
      coeff_mul_C, hBzero, hczero, hB3czero, hB2zero, hcdzero, hBezero,
      hB3zero, zero_mul, mul_zero, add_zero, sub_zero] at hz
    change 0 = (Delta * d).coeff (U + V - q) -
      (3 / 2 : k) * (B * d ^ 2).coeff (U + V - q) +
      (9 / 8 : k) * zeta * (A * c).coeff (U + V - q) at hz
    linear_combination -hz

  have hvanish : ∀ q, q < mu → (Delta.reflect U).coeff q = 0 := by
    have hall := fiveToSix_cuspJet_zero_before_firstLoad68 mu
      (fun q => (Delta.reflect U).coeff q) hDelta0
      (by
        intro q hq hprev
        let t := q + 1
        have htmu : t < mu := hq
        have htS : t < S := lt_of_lt_of_le htmu hmuS
        have htZ : t < R - S := lt_of_lt_of_le htmu hmuZ
        have hAc : (A * c).coeff (U + V - t) = 0 := by
          apply coeff_eq_zero_of_natDegree_lt
          compute_degree
          omega
        have hBd : (B * d ^ 2).coeff (U + V - t) = 0 := by
          apply coeff_eq_zero_of_natDegree_lt
          compute_degree
          omega
        have hprodRaw := hcombination_coeff t (Nat.le_of_lt htmu)
        have hprod : (Delta * d).coeff (U + V - t) = 0 := by
          rw [hAc, hBd] at hprodRaw
          linear_combination hprodRaw
        have href := coeff_mul_at_reflect_of_left_lower_zero68
          Delta d U V t hDelta hdSharp (by omega)
          (by
            intro j hj
            exact hprev j (by omega))
        rw [href] at hprod
        exact (mul_eq_zero.mp hprod).resolve_right hdsR)
    intro q hq
    exact hall q hq q (by omega)

  have hwallRaw := hcombination_coeff mu (le_refl mu)
  have hrefWall := coeff_mul_at_reflect_of_left_lower_zero68
    Delta d U V mu hDelta hdSharp (by omega) hvanish
  rw [hrefWall] at hwallRaw
  have hds0 : (d.reflect V).coeff 0 = d.coeff V := by
    simp only [coeff_reflect, revAt_zero]
  rw [hds0] at hwallRaw
  have hActop := coeff_mul_at_bounds68 A c (2 * N) (4 * N - G) hA hc
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
  have hAc_before (hq : mu < R - S) :
      (A * c).coeff (U + V - mu) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    compute_degree
    omega
  have hAc_wall (hq : mu = R - S) :
      (A * c).coeff (U + V - mu) =
        A.coeff (2 * N) * c.coeff (4 * N - G) := by
    rw [show U + V - mu = 2 * N + (4 * N - G) from by omega]
    exact hActop
  have hBd_before (hq : mu < S) :
      (B * d ^ 2).coeff (U + V - mu) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    compute_degree
    omega
  have hBd_wall (hq : mu = S) :
      (B * d ^ 2).coeff (U + V - mu) =
        B.coeff (3 * N - G) * d.coeff V ^ 2 := by
    rw [show U + V - mu = (3 * N - G) + 2 * V from by omega]
    exact hBdtop
  change (∀ q, q < mu → (Delta.reflect U).coeff q = 0) ∧ _
  refine ⟨hvanish, ?_⟩
  rcases hwallCases with ⟨hlt, hmuS'⟩ | ⟨hlt, hmuZ'⟩ |
      ⟨heq, hmuS', hmuZ'⟩
  · left
    refine ⟨hlt, hmuS', ?_⟩
    rw [hAc_before (by omega), hBd_wall hmuS', mul_zero] at hwallRaw
    linear_combination hwallRaw
  · right; left
    refine ⟨hlt, hmuZ', ?_⟩
    rw [hAc_wall hmuZ', hBd_before (by omega), mul_zero, sub_zero] at hwallRaw
    linear_combination hwallRaw
  · right; right
    refine ⟨heq, hmuS', hmuZ', ?_⟩
    rw [hAc_wall hmuZ', hBd_wall hmuS'] at hwallRaw
    linear_combination hwallRaw

/-- Existing earlier-cusp source data upgraded with its complete finite
convolution and exact first loaded scalar. -/
def FiveToSixContractedEarlierConvolutionAssembly68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e Ae Be ce de ee : k[X]) (n g : ℕ) : Prop :=
  FiveToSixContractedEarlierFiniteStopAssembly68
      alpha gamma epsilon zeta eta terminal
      A B c d e Ae Be ce de ee n g ∧
    ∃ N G S, n = 60 * N ∧ g = 60 * G ∧
      FiveToSixCuspFirstLoadFactor68 zeta A B c d N G S

theorem fiveToSix_contractedEarlierFiniteStop_convolution68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e Ae Be ce de ee : k[X]) (n g : ℕ)
    (hfinite : FiveToSixContractedEarlierFiniteStopAssembly68
      alpha gamma epsilon zeta eta terminal
      A B c d e Ae Be ce de ee n g) :
    FiveToSixContractedEarlierConvolutionAssembly68
      alpha gamma epsilon zeta eta terminal
      A B c d e Ae Be ce de ee n g := by
  refine ⟨hfinite, ?_⟩
  rcases hfinite.1 with
    ⟨_s, N, G, S, hn, hg, _hs, _hN, hS, hSR,
      hdSharp, heSharp, hpacket, _hsecond⟩
  exact ⟨N, G, S, hn, hg,
    fiveToSix_contractedCusp_firstLoad_convolution68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hpacket
      hS hSR hdSharp heSharp⟩

/-- Full source assembly, with both terminal alternatives unchanged. -/
theorem integratedPolynomialLowerSystem68_fiveToSix_convolution_assembly68
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
      FiveToSixContractedEarlierConvolutionAssembly68
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
      (fiveToSix_contractedEarlierFiniteStop_convolution68
        (hfinite := hearlier)))
  · exact Or.inr (Or.inr hterminalCusp)

#print axioms mul_coeff_eq_left_edge_of_lower_zero68
#print axioms coeff_mul_at_reflect_of_left_lower_zero68
#print axioms fiveToSix_contractedCusp_firstLoad_convolution68
#print axioms fiveToSix_contractedEarlierFiniteStop_convolution68
#print axioms integratedPolynomialLowerSystem68_fiveToSix_convolution_assembly68

end FiveToSixCuspConvolution68

end Max11DegreeRoutes
