import Sol68LaterDeepLowerParentFiveToSixOffsetSixtyRowZeroScratch

/-! # The staggered offset-ninety step in the five-to-six chamber

After a zero offset-`60` edge, expansion support drops both residual defects
to offset `90`.  The unique I4 load wall there is `(n,g)=(90,270)`.
The literal row-zero coefficient deletes that load.  Away from the wall,
I4 and I3 give the ordinary incidence face, whose nonzero alternative is
incompatible with the expansion residue class at displacement `90`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerParentFiveToSixOffsetNinety68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 30000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- On a boundary divisible by `30`, a `60`-expanded polynomial already
bounded at offset `60` drops to offset `90` once its offset-`60` coefficient
vanishes. -/
theorem natDegree_expand_le_sub_ninety_of_boundary_zero_sixty68
    (q : k[X]) (base : ℕ) (hbase : 30 ∣ base) (hbase90 : 90 ≤ base)
    (hdeg : (expand k 60 q).natDegree ≤ base - 60)
    (h60 : (expand k 60 q).coeff (base - 60) = 0) :
    (expand k 60 q).natDegree ≤ base - 90 := by
  by_cases hq : expand k 60 q = 0
  · rw [hq, natDegree_zero]
    omega
  · have hlead : (expand k 60 q).coeff (expand k 60 q).natDegree ≠ 0 := by
      rw [coeff_natDegree, leadingCoeff]
      exact Polynomial.leadingCoeff_ne_zero.mpr hq
    have hdiv : 60 ∣ (expand k 60 q).natDegree :=
      coeff_expand_ne_zero_dvd68 60 (by norm_num) q
        (expand k 60 q).natDegree hlead
    by_contra hnot
    have hlt : base - 90 < (expand k 60 q).natDegree := by omega
    obtain ⟨u, hu⟩ := hbase
    obtain ⟨v, hv⟩ := hdiv
    have heq : (expand k 60 q).natDegree = base - 60 := by omega
    exact hlead (by simpa only [heq] using h60)

/-- If offset `90` vanishes as well, the same support arithmetic supplies
the full next offset-`120` degree bound. -/
theorem natDegree_expand_le_sub_oneTwenty_of_boundary_zero_sixty_ninety68
    (q : k[X]) (base : ℕ) (hbase : 30 ∣ base) (hbase120 : 120 ≤ base)
    (hdeg : (expand k 60 q).natDegree ≤ base - 60)
    (h60 : (expand k 60 q).coeff (base - 60) = 0)
    (h90 : (expand k 60 q).coeff (base - 90) = 0) :
    (expand k 60 q).natDegree ≤ base - 120 := by
  have hdeg90 := natDegree_expand_le_sub_ninety_of_boundary_zero_sixty68
    q base hbase (by omega) hdeg h60
  by_cases hq : expand k 60 q = 0
  · rw [hq, natDegree_zero]
    omega
  · have hlead : (expand k 60 q).coeff (expand k 60 q).natDegree ≠ 0 := by
      rw [coeff_natDegree, leadingCoeff]
      exact Polynomial.leadingCoeff_ne_zero.mpr hq
    have hdiv : 60 ∣ (expand k 60 q).natDegree :=
      coeff_expand_ne_zero_dvd68 60 (by norm_num) q
        (expand k 60 q).natDegree hlead
    by_contra hnot
    have hlt : base - 120 < (expand k 60 q).natDegree := by omega
    obtain ⟨u, hu⟩ := hbase
    obtain ⟨v, hv⟩ := hdiv
    have heq60 : (expand k 60 q).natDegree = base - 60 ∨
        (expand k 60 q).natDegree = base - 90 := by omega
    rcases heq60 with heq | heq
    · exact hlead (by simpa only [heq] using h60)
    · exact hlead (by simpa only [heq] using h90)

/-- Homogeneous I4 at the staggered offset `90`. -/
theorem secondaryResidualInvariantFourPolynomial68_coeff_gap_ninety_fiveToSix
    (B c d e : k[X]) (n g : ℕ) (hn60 : 60 ≤ n)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - g - 90)
    (he : e.natDegree ≤ 6 * n - g - 90) :
    (secondaryResidualInvariantFourPolynomial68 B c d e).coeff
        (9 * n - 2 * g - 90) =
      (8 / 3 : k) *
        (B.coeff (3 * n - g) * e.coeff (6 * n - g - 90) +
          c.coeff (4 * n - g) * d.coeff (5 * n - g - 90)) := by
  have hB3 : (B ^ 3).natDegree < 9 * n - 2 * g - 90 := by
    compute_degree
    omega
  have hBe := coeff_mul_at_bounds68 B e (3 * n - g)
    (6 * n - g - 90) hB he
  have hBei : (3 * n - g) + (6 * n - g - 90) =
      9 * n - 2 * g - 90 := by omega
  rw [hBei] at hBe
  have hcd := coeff_mul_at_bounds68 c d (4 * n - g)
    (5 * n - g - 90) hc hd
  have hcdi : (4 * n - g) + (5 * n - g - 90) =
      9 * n - 2 * g - 90 := by omega
  rw [hcdi] at hcd
  simp only [secondaryResidualInvariantFourPolynomial68, coeff_add,
    coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hB3, hBe, hcd]
  ring

/-- Literal I4 at offset `90`, retaining the only potentially tied
`zeta*A` load. -/
theorem cubicFirstIntegralFourPolynomial68_coeff_gap_ninety_loaded_fiveToSix
    (gamma epsilon zeta : k) (A B c d e : k[X])
    (n g : ℕ) (hn60 : 60 ≤ n)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - g - 90)
    (he : e.natDegree ≤ 6 * n - g - 90) :
    (cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff
        (9 * n - 2 * g - 90) =
      (8 / 3 : k) *
        (B.coeff (3 * n - g) * e.coeff (6 * n - g - 90) +
          c.coeff (4 * n - g) * d.coeff (5 * n - g - 90)) +
        zeta * A.coeff (9 * n - 2 * g - 90) := by
  rw [cubicFirstIntegralFourPolynomial68_fiveToSix_residualCoordinates,
    coeff_add, coeff_add, coeff_add,
    secondaryResidualInvariantFourPolynomial68_coeff_gap_ninety_fiveToSix
      B c d e n g hn60 hwindow hB hc hd he]
  have hloadB : ((2 * epsilon : k) • B).natDegree <
      9 * n - 2 * g - 90 := by compute_degree; omega
  have hloadd : ((4 * gamma : k) • d).natDegree <
      9 * n - 2 * g - 90 := by compute_degree; omega
  rw [coeff_eq_zero_of_natDegree_lt hloadB,
    coeff_eq_zero_of_natDegree_lt hloadd]
  simp only [coeff_smul, smul_eq_mul]
  ring

/-- Homogeneous, and hence literal, I3 at offset `90`. -/
theorem cubicFirstIntegralThreePolynomial68_coeff_gap_ninety_fiveToSix
    (gamma epsilon zeta : k) (A B c d e : k[X])
    (n g : ℕ) (hn60 : 60 ≤ n)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - g - 90)
    (he : e.natDegree ≤ 6 * n - g - 90) :
    (cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff
        (10 * n - 2 * g - 90) =
      (8 / 9 : k) *
        (-(A.coeff (2 * n) * B.coeff (3 * n - g) *
            d.coeff (5 * n - g - 90)) +
          3 * c.coeff (4 * n - g) *
            e.coeff (6 * n - g - 90)) := by
  have hABd := coeff_mul_mul_at_bounds68 A B d (2 * n)
    (3 * n - g) (5 * n - g - 90) hA hB hd
  have hABdi : 2 * n + (3 * n - g) + (5 * n - g - 90) =
      10 * n - 2 * g - 90 := by omega
  rw [hABdi] at hABd
  have hB2c : (B ^ 2 * c).natDegree < 10 * n - 2 * g - 90 := by
    compute_degree
    omega
  have hce := coeff_mul_at_bounds68 c e (4 * n - g)
    (6 * n - g - 90) hc he
  have hcei : (4 * n - g) + (6 * n - g - 90) =
      10 * n - 2 * g - 90 := by omega
  rw [hcei] at hce
  have hd2 : (d ^ 2).natDegree < 10 * n - 2 * g - 90 := by
    compute_degree
    omega
  rw [cubicFirstIntegralThreePolynomial68_fiveToSix_residualCoordinates,
    coeff_sub, coeff_add, coeff_add, coeff_add]
  have hloadB : (zeta • B).natDegree < 10 * n - 2 * g - 90 := by
    compute_degree
    omega
  have hloadc : ((2 * epsilon : k) • c).natDegree <
      10 * n - 2 * g - 90 := by compute_degree; omega
  have hloade : ((4 * gamma : k) • e).natDegree <
      10 * n - 2 * g - 90 := by compute_degree; omega
  have hloadB2 : ((2 / 3 * gamma : k) • B ^ 2).natDegree <
      10 * n - 2 * g - 90 := by compute_degree; omega
  simp only [secondaryResidualInvariantThreePolynomial68, coeff_add,
    coeff_sub, coeff_smul, smul_eq_mul, hABd,
    coeff_eq_zero_of_natDegree_lt hB2c, hce,
    coeff_eq_zero_of_natDegree_lt hd2,
    coeff_eq_zero_of_natDegree_lt hloadB,
    coeff_eq_zero_of_natDegree_lt hloadc,
    coeff_eq_zero_of_natDegree_lt hloade,
    coeff_eq_zero_of_natDegree_lt hloadB2]
  ring

/-- Homogeneous row zero at offset `90`. -/
theorem secondaryResidualRowZeroPolynomial68_coeff_gap_ninety_fiveToSix
    (A B c d e : k[X]) (n g : ℕ) (hn60 : 60 ≤ n)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - g - 90)
    (he : e.natDegree ≤ 6 * n - g - 90) :
    (secondaryResidualRowZeroPolynomial68 A B c d e).coeff
        (13 * n - 2 * g - 91) =
      (-8 / 27 : k) * (n : k) * A.coeff (2 * n) ^ 2 *
        (B.coeff (3 * n - g) * e.coeff (6 * n - g - 90) +
          c.coeff (4 * n - g) * d.coeff (5 * n - g - 90)) := by
  have h1raw := coeff_mul_mul_mul_derivative_at_bounds68 A B e A
    (2 * n) (3 * n - g) (6 * n - g - 90) (2 * n) (by omega)
    hA hB he hA
  have hi1 : 2 * n + (3 * n - g) + (6 * n - g - 90) + 2 * n - 1 =
      13 * n - 2 * g - 91 := by omega
  rw [hi1] at h1raw
  have h1 : (A * derivative A * B * e).coeff
      (13 * n - 2 * g - 91) =
      A.coeff (2 * n) * A.coeff (2 * n) *
        B.coeff (3 * n - g) * e.coeff (6 * n - g - 90) *
          (((2 * n : ℕ) : k)) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h1raw
  have h2raw := coeff_mul_mul_mul_derivative_at_bounds68 A c d A
    (2 * n) (4 * n - g) (5 * n - g - 90) (2 * n) (by omega)
    hA hc hd hA
  have hi2 : 2 * n + (4 * n - g) + (5 * n - g - 90) + 2 * n - 1 =
      13 * n - 2 * g - 91 := by omega
  rw [hi2] at h2raw
  have h2 : (A * derivative A * c * d).coeff
      (13 * n - 2 * g - 91) =
      A.coeff (2 * n) * A.coeff (2 * n) *
        c.coeff (4 * n - g) * d.coeff (5 * n - g - 90) *
          (((2 * n : ℕ) : k)) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h2raw
  have hlow1 : (A * B ^ 2 * derivative d).natDegree <
      13 * n - 2 * g - 91 := by compute_degree; omega
  have hlow2 : (A * B * derivative B * d).natDegree <
      13 * n - 2 * g - 91 := by compute_degree; omega
  have hlow3 : (derivative A * B * c ^ 2).natDegree <
      13 * n - 2 * g - 91 := by compute_degree; omega
  have hlow4 : (derivative A * d * e).natDegree <
      13 * n - 2 * g - 91 := by compute_degree; omega
  have hlow5 : (B * c * derivative e).natDegree <
      13 * n - 2 * g - 91 := by compute_degree; omega
  have hlow6 : (B * d * derivative d).natDegree <
      13 * n - 2 * g - 91 := by compute_degree; omega
  have hlow7 : (derivative B * d ^ 2).natDegree <
      13 * n - 2 * g - 91 := by compute_degree; omega
  have hlow8 : (c * derivative c * d).natDegree <
      13 * n - 2 * g - 91 := by compute_degree; omega
  simp only [secondaryResidualRowZeroPolynomial68, coeff_smul, coeff_add,
    coeff_sub, h1, h2,
    coeff_eq_zero_of_natDegree_lt hlow1,
    coeff_eq_zero_of_natDegree_lt hlow2,
    coeff_eq_zero_of_natDegree_lt hlow3,
    coeff_eq_zero_of_natDegree_lt hlow4,
    coeff_eq_zero_of_natDegree_lt hlow5,
    coeff_eq_zero_of_natDegree_lt hlow6,
    coeff_eq_zero_of_natDegree_lt hlow7,
    coeff_eq_zero_of_natDegree_lt hlow8, smul_eq_mul]
  push_cast
  ring

/-- Exact terminal row-zero load when `B` is constant and the residual
degrees have the `2n,0,n,n,2n` wall chart.  The gamma contributions cancel;
only `(2/9)*n*zeta*a^3` remains. -/
theorem cubicLoadRowZeroPolynomial68_coeff_constantB_chart68
    (alpha gamma epsilon zeta eta : k) (A B c d e : k[X])
    (n : ℕ) (hn : 0 < n)
    (hA : A.natDegree ≤ 2 * n) (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ n) (hd : d.natDegree ≤ n)
    (he : e.natDegree ≤ 2 * n) :
    (cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff (6 * n - 1) =
      (2 / 9 : k) * (n : k) * zeta * A.coeff (2 * n) ^ 3 := by
  let D0 : k[X] := (1 / 3 : k) • (A * B) + d
  let E0 : k[X] :=
    (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
  let Ur : k[X] := (2 / 3 * gamma : k) • B + C zeta
  let W : k[X] :=
    (1 / 9 * gamma : k) • A ^ 2 + (2 / 3 * gamma : k) • c +
      (1 / 3 * epsilon : k) • A + C eta
  have hloadEq :
      cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
        A B c D0 e = Ur * derivative E0 - D0 * derivative W := by
    apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
    simp only [cubicLoadRowZeroPolynomial68, cubicLoadUPolynomial68,
      cubicLoadVPolynomial68, D0, E0, Ur, W,
      zero_mul, zero_smul, smul_zero, add_zero, zero_add, sub_zero,
      derivative_add, derivative_sub, derivative_mul, derivative_pow,
      derivative_smul, derivative_C, one_mul, Polynomial.smul_eq_C_mul,
      map_add, map_sub, map_mul, map_pow, map_neg, map_zero,
      RatFunc.algebraMap_C, map_div₀, map_ofNat, map_natCast, map_one]
    ring
  have hDdeg : D0.natDegree ≤ 2 * n := by
    simp only [D0]
    compute_degree
    omega
  have hEdeg : E0.natDegree ≤ 6 * n := by
    simp only [E0]
    compute_degree
    omega
  have hUrdeg : Ur.natDegree ≤ 0 := by
    simp only [Ur]
    compute_degree
    omega
  have hWdeg : W.natDegree ≤ 4 * n := by
    simp only [W]
    compute_degree
    omega
  have hA3 := coeff_pow_at_bound68 A (2 * n) 3 hA
  have hA3i : 3 * (2 * n) = 6 * n := by omega
  rw [hA3i] at hA3
  have hAclt : (A * c).natDegree < 6 * n := by compute_degree; omega
  have helt : e.natDegree < 6 * n := he.trans_lt (by omega)
  have hEtop : E0.coeff (6 * n) =
      (1 / 27 : k) * A.coeff (2 * n) ^ 3 := by
    simp only [E0, coeff_add, coeff_smul, smul_eq_mul, hA3,
      coeff_eq_zero_of_natDegree_lt hAclt,
      coeff_eq_zero_of_natDegree_lt helt, mul_zero, add_zero]
  have hAB := coeff_mul_at_bounds68 A B (2 * n) 0 hA hB
  have hABi : 2 * n + 0 = 2 * n := by omega
  rw [hABi] at hAB
  have hdlt : d.natDegree < 2 * n := hd.trans_lt (by omega)
  have hDtop : D0.coeff (2 * n) =
      (1 / 3 : k) * A.coeff (2 * n) * B.coeff 0 := by
    simp only [D0, coeff_add, coeff_smul, smul_eq_mul, hAB,
      coeff_eq_zero_of_natDegree_lt hdlt]
    ring
  have hA2 := coeff_pow_at_bound68 A (2 * n) 2 hA
  have hA2i : 2 * (2 * n) = 4 * n := by omega
  rw [hA2i] at hA2
  have hclt : c.natDegree < 4 * n := hc.trans_lt (by omega)
  have hAlt : A.natDegree < 4 * n := hA.trans_lt (by omega)
  have hCeta : (C eta : k[X]).coeff (4 * n) = 0 := by
    simp [coeff_C, show 4 * n ≠ 0 by omega]
  have hWtop : W.coeff (4 * n) =
      (1 / 9 * gamma : k) * A.coeff (2 * n) ^ 2 := by
    simp only [W, coeff_add, coeff_smul, smul_eq_mul, hA2,
      coeff_eq_zero_of_natDegree_lt hclt,
      coeff_eq_zero_of_natDegree_lt hAlt, hCeta, mul_zero, add_zero]
  have hUrtop : Ur.coeff 0 =
      (2 / 3 * gamma : k) * B.coeff 0 + zeta := by
    simp only [Ur, coeff_add, coeff_smul, smul_eq_mul, coeff_C_zero]
  have h1 := coeff_mul_derivative_at_bounds68 Ur E0 0 (6 * n)
    (by omega) hUrdeg hEdeg
  have h1i : 0 + 6 * n - 1 = 6 * n - 1 := by omega
  rw [h1i] at h1
  have h2 := coeff_mul_derivative_at_bounds68 D0 W (2 * n) (4 * n)
    (by omega) hDdeg hWdeg
  have h2i : 2 * n + 4 * n - 1 = 6 * n - 1 := by omega
  rw [h2i] at h2
  change (cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
      A B c D0 e).coeff (6 * n - 1) = _
  rw [hloadEq, coeff_sub, h1, h2, hUrtop, hEtop, hDtop, hWtop]
  push_cast
  ring

set_option maxHeartbeats 40000000 in
/-- Exact source-facing offset-`90` reduction.  A zero offset-`60` pair
drops uniformly through offset `90` and hence to degree offset `120`; the
prospective `(90,270)` load is deleted and forces `zeta=0`.  The old
nonzero discriminant pair is necessarily aligned (`60 | n,g`), so its
offset-`90` coefficients vanish and its first possible new coefficient is
at offset `120`. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepOuter_offsetNinetyPacket68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hlater :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      3 * n ≤ 2 * g) :
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
    ((n = 60 ∧ g = 180 ∧ zeta = 0) ∨ 60 < n) ∧
      ((d.coeff (5 * n - g - 60) = 0 ∧
          ee.coeff (6 * n - g - 60) = 0 ∧
          d.natDegree ≤ 5 * n - g - 120 ∧
          ee.natDegree ≤ 6 * n - g - 120 ∧
          (n = 90 ∧ g = 270 → zeta = 0)) ∨
        (60 ∣ n ∧ 60 ∣ g ∧
          Be.coeff (3 * n - g) ≠ 0 ∧
          ce.coeff (4 * n - g) ≠ 0 ∧
          d.coeff (5 * n - g - 60) ≠ 0 ∧
          ee.coeff (6 * n - g - 60) ≠ 0 ∧
          Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 2 +
            3 * ce.coeff (4 * n - g) ^ 2 = 0 ∧
          d.coeff (5 * n - g - 90) = 0 ∧
          ee.coeff (6 * n - g - 90) = 0)) := by
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
  change 3 * n ≤ 2 * g at hlater
  change ((_ ∧ _ ∧ _) ∨ _) ∧
    ((_ ∧ _ ∧ _ ∧ _ ∧ _) ∨
      (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))
  have hp :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepOuter_offsetSixtyRowZeroPacket68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hlater)
  change ((_ ∧ _ ∧ _) ∨ _) ∧
    ((_ ∧ _) ∨ (_ ∧ _ ∧ _ ∧ _ ∧ _)) at hp
  obtain ⟨hsize, hedge⟩ := hp
  refine ⟨hsize, ?_⟩
  have hparent :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepOuter_forces_fiveToSixStride68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hlater)
  change 5 * n < 2 * g ∧ 2 * g ≤ 6 * n ∧ _ = 0 ∧ _ = 0 ∧
    30 ∣ n ∧ 30 ∣ g ∧ 30 < n ∧ _ ∧
    d.natDegree ≤ 5 * n - g - 60 ∧
    ee.natDegree ≤ 6 * n - g - 60 at hparent
  obtain ⟨hgt5, hle6, _hfourTop, _hthreeTop, hn30, hg30,
    hnBig, _hprevious, hd60, he60⟩ := hparent
  have hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n := ⟨hgt5, hle6⟩
  have hn60 : 60 ≤ n := by
    rcases hsize with hterminal60 | habove60
    · omega
    · omega
  have hdexpand : d = expand k 60 (secondaryDDefectPolynomial68 A B D) := by
    simpa only [d, Ae, Be, De] using
      secondaryDDefectPolynomial68_expand 60 A B D
  have heexpand : ee = expand k 60 (cubicEDefectPolynomial68 A C0 E) := by
    simpa only [ee, Ae, Ce, Ee] using
      expand_cubicEDefectPolynomial68 60 A C0 E
  have hcexpand : ce = expand k 60 (cubicCDefectPolynomial68 A C0) := by
    simpa only [ce, Ae, Ce] using expand_cubicCDefectPolynomial68 60 A C0
  have hbaseD30 : 30 ∣ 5 * n - g := by
    obtain ⟨u, hu⟩ := hn30
    obtain ⟨v, hv⟩ := hg30
    refine ⟨5 * u - v, ?_⟩
    omega
  have hbaseE30 : 30 ∣ 6 * n - g := by
    obtain ⟨u, hu⟩ := hn30
    obtain ⟨v, hv⟩ := hg30
    refine ⟨6 * u - v, ?_⟩
    omega
  have hbaseD120 : 120 ≤ 5 * n - g := by omega
  have hbaseE120 : 120 ≤ 6 * n - g := by omega
  rcases hedge with hzero60 | hnonzero60
  · left
    change d.coeff (5 * n - g - 60) = 0 ∧
      ee.coeff (6 * n - g - 60) = 0 at hzero60
    have hd90deg : d.natDegree ≤ 5 * n - g - 90 := by
      rw [hdexpand]
      exact natDegree_expand_le_sub_ninety_of_boundary_zero_sixty68
        (secondaryDDefectPolynomial68 A B D) (5 * n - g) hbaseD30
        (by omega) (by simpa only [hdexpand] using hd60)
        (by simpa only [hdexpand] using hzero60.1)
    have he90deg : ee.natDegree ≤ 6 * n - g - 90 := by
      rw [heexpand]
      exact natDegree_expand_le_sub_ninety_of_boundary_zero_sixty68
        (cubicEDefectPolynomial68 A C0 E) (6 * n - g) hbaseE30
        (by omega) (by simpa only [heexpand] using he60)
        (by simpa only [heexpand] using hzero60.2)
    have data :=
      maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLoadI4Data68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys
    change LaterDeepLoadI4Data68 l beta gamma delta epsilon zeta
      n g Ae Be ce De ee at data
    have hgt3 : 3 * n < 2 * g := by omega
    have hlbeta :=
      maximalExpandedIntegratedPolynomialLowerSystem_l_beta_eq_zero_of_threeRadius_lt_twoGap68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hgt3)
    have hl : l = 0 := hlbeta.1
    have hbeta : beta = 0 := hlbeta.2
    obtain ⟨i4, hI4raw⟩ := data.invariant
    have hI4 := hI4raw
    rw [hl, hbeta] at hI4
    have hdelta :=
      cubicFirstIntegralFourPolynomial68_forces_delta_eq_zero_of_l_beta
        gamma delta epsilon zeta i4 Ae Be ce De ee n g data.hn data.hg
        hwindow.1 data.hA data.hB data.hc data.hD data.he data.ha hI4
    rw [hdelta] at hI4
    have hDrec : De = (1 / 3 : k) • (Ae * Be) + d := by
      simpa only [d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
    rw [hDrec] at hI4
    have hcoeff4 := congrArg
      (fun p : k[X] => p.coeff (9 * n - 2 * g - 90)) hI4
    rw [cubicFirstIntegralFourPolynomial68_coeff_gap_ninety_loaded_fiveToSix
      gamma epsilon zeta Ae Be ce d ee n g hn60 hwindow data.hA data.hB
      data.hc hd90deg he90deg] at hcoeff4
    have hj4 : 9 * n - 2 * g - 90 ≠ 0 := by omega
    simp only [coeff_C, if_neg hj4] at hcoeff4
    by_cases hwall : n = 90 ∧ g = 270
    · have htarget4 : 9 * n - 2 * g - 90 = 2 * n := by omega
      rw [htarget4] at hcoeff4
      have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
        simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
      have hErec : Ee = (1 / 27 : k) • Ae ^ 3 +
          (1 / 3 : k) • (Ae * ce) + ee := by
        simpa only [ce, ee] using
          cubicEDefectPolynomial68_eq_cubicCoordinates Ae Ce Ee
      have hrowZero : lowerRowZeroPolynomial68
          (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
          (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
            Ae Be Ce De Ee) De Ee =
          C terminal * (60 * (X ^ 59 : k[X])) := by
        simpa only [Ae, Be, Ce, De, Ee] using
          expand_lowerRowZeroPolynomial68_of_system
            l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
      have hzeroCoeff :=
        expand_lowerRowZeroPolynomial68_coeff_eq_zero_of_index_gt
          terminal
          (integratedUPolynomial68 l alpha beta gamma delta zeta
            Ae Be Ce De Ee)
          (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
            Ae Be Ce De Ee) De Ee 539 hrowZero (by norm_num)
      rw [hl, hbeta, hdelta, hCrec, hErec, hDrec,
        cubicRowZeroPolynomial68_offsetSixty_residualSplit, coeff_add]
          at hzeroCoeff
      have hres :=
        secondaryResidualRowZeroPolynomial68_coeff_gap_ninety_fiveToSix
          Ae Be ce d ee n g hn60 hwindow data.hA data.hB data.hc
          hd90deg he90deg
      norm_num [hwall.1, hwall.2] at hres
      have hA180 : Ae.natDegree ≤ 180 := by
        simpa [hwall.1] using data.hA
      have hB0 : Be.natDegree ≤ 0 := by
        simpa [hwall.1, hwall.2] using data.hB
      have hc90 : ce.natDegree ≤ 90 := by
        simpa [hwall.1, hwall.2] using data.hc
      have hd90 : d.natDegree ≤ 90 := by
        simpa [hwall.1, hwall.2] using hd90deg
      have he180 : ee.natDegree ≤ 180 := by
        simpa [hwall.1, hwall.2] using he90deg
      have hload := cubicLoadRowZeroPolynomial68_coeff_constantB_chart68
        alpha gamma epsilon zeta eta Ae Be ce d ee 90 (by norm_num)
        hA180 hB0 hc90 hd90 he180
      norm_num at hload
      rw [hres, hload] at hzeroCoeff
      norm_num [hwall.1, hwall.2] at hcoeff4
      have hzetaCube : zeta * Ae.coeff 180 ^ 3 = 0 := by
        linear_combination (1 / 30 : k) * hzeroCoeff +
          (1 / 3 : k) * Ae.coeff 180 ^ 2 * hcoeff4
      have hzeta : zeta = 0 :=
        (mul_eq_zero.mp hzetaCube).resolve_right
          (pow_ne_zero 3 (by simpa [hwall.1] using data.ha))
      have hcTop0 : ce.coeff (4 * n - g) = 0 := by
        rw [hwall.1, hwall.2, hcexpand]
        rw [coeff_expand (by norm_num : 0 < 60), if_neg]
        norm_num
      have htop :=
        maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_B_or_c_top68
          l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
          hterminal hsys
          (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwindow)
      change Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0 at htop
      have hbTop : Be.coeff (3 * n - g) ≠ 0 :=
        htop.resolve_right (fun h => h hcTop0)
      have hdEdge0 : d.coeff (5 * n - g - 90) = 0 := by
        rw [hwall.1, hwall.2, hdexpand]
        rw [coeff_expand (by norm_num : 0 < 60), if_neg]
        norm_num
      have heEdge0 : ee.coeff (6 * n - g - 90) = 0 := by
        have hcTop0' : ce.coeff 90 = 0 := by
          simpa [hwall.1, hwall.2] using hcTop0
        have hbTop' : Be.coeff 0 ≠ 0 := by
          simpa [hwall.1, hwall.2] using hbTop
        have hdEdge0' : d.coeff 90 = 0 := by
          simpa [hwall.1, hwall.2] using hdEdge0
        rw [hzeta, zero_mul, add_zero, hcTop0', zero_mul, add_zero]
          at hcoeff4
        have hbe : Be.coeff 0 * ee.coeff 180 = 0 :=
          (mul_eq_zero.mp hcoeff4).resolve_left (by norm_num)
        have he' : ee.coeff 180 = 0 :=
          (mul_eq_zero.mp hbe).resolve_left hbTop'
        simpa [hwall.1, hwall.2] using he'
      have hd120 : d.natDegree ≤ 5 * n - g - 120 := by
        rw [hdexpand]
        exact natDegree_expand_le_sub_oneTwenty_of_boundary_zero_sixty_ninety68
          (secondaryDDefectPolynomial68 A B D) (5 * n - g) hbaseD30
          hbaseD120 (by simpa only [hdexpand] using hd60)
          (by simpa only [hdexpand] using hzero60.1)
          (by simpa only [hdexpand] using hdEdge0)
      have he120 : ee.natDegree ≤ 6 * n - g - 120 := by
        rw [heexpand]
        exact natDegree_expand_le_sub_oneTwenty_of_boundary_zero_sixty_ninety68
          (cubicEDefectPolynomial68 A C0 E) (6 * n - g) hbaseE30
          hbaseE120 (by simpa only [heexpand] using he60)
          (by simpa only [heexpand] using hzero60.2)
          (by simpa only [heexpand] using heEdge0)
      exact ⟨hzero60.1, hzero60.2, hd120, he120,
        fun _ => hzeta⟩
    · have hloadA : zeta * Ae.coeff (9 * n - 2 * g - 90) = 0 := by
        rcases hsize with hterminal60 | habove60
        · rw [hterminal60.2.2, zero_mul]
        · have htarget : 2 * n < 9 * n - 2 * g - 90 := by
            obtain ⟨u, hu⟩ := hn30
            obtain ⟨v, hv⟩ := hg30
            omega
          rw [coeff_eq_zero_of_natDegree_lt (data.hA.trans_lt htarget),
            mul_zero]
      rw [hloadA, add_zero] at hcoeff4
      have hfour :
          Be.coeff (3 * n - g) * ee.coeff (6 * n - g - 90) +
            ce.coeff (4 * n - g) * d.coeff (5 * n - g - 90) = 0 :=
        (mul_eq_zero.mp hcoeff4).resolve_left (by norm_num)
      have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
        simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
      have hErec : Ee = (1 / 27 : k) • Ae ^ 3 +
          (1 / 3 : k) • (Ae * ce) + ee := by
        simpa only [ce, ee] using
          cubicEDefectPolynomial68_eq_cubicCoordinates Ae Ce Ee
      obtain ⟨i3, hi3raw⟩ := hsys.firstThree
      have hi3e : firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
          Ae Be Ce De Ee = C i3 := by
        simpa only [Ae, Be, Ce, De, Ee] using
          expand_firstIntegralThreePolynomial68_of_eq
            l beta gamma delta epsilon zeta i3 A B C0 D E hi3raw
      rw [hCrec, hErec, firstIntegralThreePolynomial68_cubicCoordinates,
        hl, hbeta, hdelta, hDrec] at hi3e
      have hcoeff3 := congrArg
        (fun p : k[X] => p.coeff (10 * n - 2 * g - 90)) hi3e
      rw [cubicFirstIntegralThreePolynomial68_coeff_gap_ninety_fiveToSix
        gamma epsilon zeta Ae Be ce d ee n g hn60 hwindow data.hA data.hB
        data.hc hd90deg he90deg] at hcoeff3
      have hj3 : 10 * n - 2 * g - 90 ≠ 0 := by omega
      simp only [coeff_C, if_neg hj3] at hcoeff3
      have hthree :
          -Ae.coeff (2 * n) * Be.coeff (3 * n - g) *
              d.coeff (5 * n - g - 90) +
            3 * ce.coeff (4 * n - g) *
              ee.coeff (6 * n - g - 90) = 0 := by
        have hz := (mul_eq_zero.mp hcoeff3).resolve_left (by norm_num)
        linear_combination hz
      have hface : SecondaryResidualBetweenFace68
          (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
          (ce.coeff (4 * n - g)) (d.coeff (5 * n - g - 90))
          (ee.coeff (6 * n - g - 90)) := ⟨hfour, hthree⟩
      have hmain :=
        maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_mainFamily68
          l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
          hterminal hsys
          (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwindow)
      change ee.coeff (6 * n - g) = 0 ∧
        Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
          3 * De.coeff (5 * n - g) at hmain
      have hsecondary :=
        maximalExpandedIntegratedPolynomialLowerSystem_secondaryRadius68
          l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
          hterminal hsys
      change 0 < g ∧ Be.natDegree ≤ 3 * n - g ∧
        ce.natDegree ≤ 4 * n - g ∧ De.natDegree ≤ 5 * n - g ∧
        ee.natDegree ≤ 6 * n - g ∧
        (Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0 ∨
          De.coeff (5 * n - g) ≠ 0 ∨ ee.coeff (6 * n - g) ≠ 0)
          at hsecondary
      have hold := firstSecondary_mainFamily_attainment_split68
        (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
        (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
        (ee.coeff (6 * n - g)) data.ha hmain hsecondary.2.2.2.2.2
      have hclass := firstSecondary_mainFamily_gapSucc_classify68
        (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
        (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
        (ee.coeff (6 * n - g)) (d.coeff (5 * n - g - 90))
        (ee.coeff (6 * n - g - 90)) data.ha hold hface
      have hzero90 : d.coeff (5 * n - g - 90) = 0 ∧
          ee.coeff (6 * n - g - 90) = 0 := by
        rcases hclass with hz | hdisc
        · exact hz
        · exfalso
          have hs90 : 90 ≤ 5 * n - g := by omega
          have hdiv := expandedSecondaryDActiveEdge_stride_dvd68
            60 (by norm_num) A B D n g 90 (by omega) hs90
            data.ha hdisc.1 hdisc.2.2.1
          norm_num at hdiv
      have hd120 : d.natDegree ≤ 5 * n - g - 120 := by
        rw [hdexpand]
        exact natDegree_expand_le_sub_oneTwenty_of_boundary_zero_sixty_ninety68
          (secondaryDDefectPolynomial68 A B D) (5 * n - g) hbaseD30
          hbaseD120 (by simpa only [hdexpand] using hd60)
          (by simpa only [hdexpand] using hzero60.1)
          (by simpa only [hdexpand] using hzero90.1)
      have he120 : ee.natDegree ≤ 6 * n - g - 120 := by
        rw [heexpand]
        exact natDegree_expand_le_sub_oneTwenty_of_boundary_zero_sixty_ninety68
          (cubicEDefectPolynomial68 A C0 E) (6 * n - g) hbaseE30
          hbaseE120 (by simpa only [heexpand] using he60)
          (by simpa only [heexpand] using hzero60.2)
          (by simpa only [heexpand] using hzero90.2)
      exact ⟨hzero60.1, hzero60.2, hd120, he120,
        fun hw => False.elim (hwall hw)⟩
  · right
    change Be.coeff (3 * n - g) ≠ 0 ∧
      ce.coeff (4 * n - g) ≠ 0 ∧
      d.coeff (5 * n - g - 60) ≠ 0 ∧
      ee.coeff (6 * n - g - 60) ≠ 0 ∧
      Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 2 +
        3 * ce.coeff (4 * n - g) ^ 2 = 0 at hnonzero60
    have hBdiv : 60 ∣ 3 * n - g := by
      have hbexp : (expand k 60 B).coeff (3 * n - g) ≠ 0 := by
        simpa only [Be] using hnonzero60.1
      exact coeff_expand_ne_zero_dvd68 60 (by norm_num) B (3 * n - g)
        hbexp
    have hCdiv : 60 ∣ 4 * n - g := by
      have hcexp : (expand k 60 (cubicCDefectPolynomial68 A C0)).coeff
          (4 * n - g) ≠ 0 := by
        rw [← hcexpand]
        exact hnonzero60.2.1
      exact coeff_expand_ne_zero_dvd68 60 (by norm_num)
        (cubicCDefectPolynomial68 A C0) (4 * n - g) hcexp
    have hnDiv : 60 ∣ n := by
      obtain ⟨u, hu⟩ := hBdiv
      obtain ⟨v, hv⟩ := hCdiv
      refine ⟨v - u, ?_⟩
      omega
    have hgDiv : 60 ∣ g := by
      obtain ⟨u, hu⟩ := hnDiv
      obtain ⟨v, hv⟩ := hBdiv
      refine ⟨3 * u - v, ?_⟩
      omega
    have hd90zero : d.coeff (5 * n - g - 90) = 0 := by
      rw [hdexpand]
      rw [coeff_expand (by norm_num : 0 < 60), if_neg]
      intro hdiv
      obtain ⟨u, hu⟩ := hnDiv
      obtain ⟨v, hv⟩ := hgDiv
      obtain ⟨w, hw⟩ := hdiv
      omega
    have he90zero : ee.coeff (6 * n - g - 90) = 0 := by
      rw [heexpand]
      rw [coeff_expand (by norm_num : 0 < 60), if_neg]
      intro hdiv
      obtain ⟨u, hu⟩ := hnDiv
      obtain ⟨v, hv⟩ := hgDiv
      obtain ⟨w, hw⟩ := hdiv
      omega
    exact ⟨hnDiv, hgDiv, hnonzero60.1, hnonzero60.2.1,
      hnonzero60.2.2.1, hnonzero60.2.2.2.1,
      hnonzero60.2.2.2.2, hd90zero, he90zero⟩

#print axioms natDegree_expand_le_sub_ninety_of_boundary_zero_sixty68
#print axioms natDegree_expand_le_sub_oneTwenty_of_boundary_zero_sixty_ninety68
#print axioms secondaryResidualInvariantFourPolynomial68_coeff_gap_ninety_fiveToSix
#print axioms cubicFirstIntegralFourPolynomial68_coeff_gap_ninety_loaded_fiveToSix
#print axioms cubicFirstIntegralThreePolynomial68_coeff_gap_ninety_fiveToSix
#print axioms secondaryResidualRowZeroPolynomial68_coeff_gap_ninety_fiveToSix
#print axioms cubicLoadRowZeroPolynomial68_coeff_constantB_chart68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepOuter_offsetNinetyPacket68

end LaterDeepLowerParentFiveToSixOffsetNinety68

end Max11DegreeRoutes
