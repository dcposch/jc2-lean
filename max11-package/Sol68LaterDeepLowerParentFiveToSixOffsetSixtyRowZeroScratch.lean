import Sol68LaterDeepLowerParentFiveToSixOffsetSixtyScratch

/-! # The independent row-zero coefficient at the offset-sixty wall

The row-one coefficient at this edge is the I3 incidence equation again.
The first independent lower row is row zero.  Its homogeneous contribution
is the expected `b*e₆₀+c*d₆₀` scalar.  On the unique loaded wall
`(n,g)=(60,180)`, the literal load coefficient is `(40/3)*zeta*a^3`;
together with loaded I4 this forces `zeta=0`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerParentFiveToSixOffsetSixtyRowZero68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 30000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The offset-`60` homogeneous row-zero coefficient.  All terms except the
two linear edge terms lie strictly below this index in the five-to-six
window. -/
theorem secondaryResidualRowZeroPolynomial68_coeff_gap_sixty_fiveToSix
    (A B c d e : k[X]) (n g : ℕ) (hn60 : 60 ≤ n)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - g - 60)
    (he : e.natDegree ≤ 6 * n - g - 60) :
    (secondaryResidualRowZeroPolynomial68 A B c d e).coeff
        (13 * n - 2 * g - 61) =
      (-8 / 27 : k) * (n : k) * A.coeff (2 * n) ^ 2 *
        (B.coeff (3 * n - g) * e.coeff (6 * n - g - 60) +
          c.coeff (4 * n - g) * d.coeff (5 * n - g - 60)) := by
  have h1raw := coeff_mul_mul_mul_derivative_at_bounds68 A B e A
    (2 * n) (3 * n - g) (6 * n - g - 60) (2 * n) (by omega)
    hA hB he hA
  have hi1 : 2 * n + (3 * n - g) + (6 * n - g - 60) + 2 * n - 1 =
      13 * n - 2 * g - 61 := by omega
  rw [hi1] at h1raw
  have h1 : (A * derivative A * B * e).coeff
      (13 * n - 2 * g - 61) =
      A.coeff (2 * n) * A.coeff (2 * n) *
        B.coeff (3 * n - g) * e.coeff (6 * n - g - 60) *
          (((2 * n : ℕ) : k)) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h1raw
  have h2raw := coeff_mul_mul_mul_derivative_at_bounds68 A c d A
    (2 * n) (4 * n - g) (5 * n - g - 60) (2 * n) (by omega)
    hA hc hd hA
  have hi2 : 2 * n + (4 * n - g) + (5 * n - g - 60) + 2 * n - 1 =
      13 * n - 2 * g - 61 := by omega
  rw [hi2] at h2raw
  have h2 : (A * derivative A * c * d).coeff
      (13 * n - 2 * g - 61) =
      A.coeff (2 * n) * A.coeff (2 * n) *
        c.coeff (4 * n - g) * d.coeff (5 * n - g - 60) *
          (((2 * n : ℕ) : k)) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h2raw
  have hlow1 : (A * B ^ 2 * derivative d).natDegree <
      13 * n - 2 * g - 61 := by compute_degree; omega
  have hlow2 : (A * B * derivative B * d).natDegree <
      13 * n - 2 * g - 61 := by compute_degree; omega
  have hlow3 : (derivative A * B * c ^ 2).natDegree <
      13 * n - 2 * g - 61 := by compute_degree; omega
  have hlow4 : (derivative A * d * e).natDegree <
      13 * n - 2 * g - 61 := by compute_degree; omega
  have hlow5 : (B * c * derivative e).natDegree <
      13 * n - 2 * g - 61 := by compute_degree; omega
  have hlow6 : (B * d * derivative d).natDegree <
      13 * n - 2 * g - 61 := by compute_degree; omega
  have hlow7 : (derivative B * d ^ 2).natDegree <
      13 * n - 2 * g - 61 := by compute_degree; omega
  have hlow8 : (c * derivative c * d).natDegree <
      13 * n - 2 * g - 61 := by compute_degree; omega
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

/-- With `l=beta=delta=0`, alpha cancels from row zero.  At the numeric
offset-`60` wall the gamma terms cancel at degree `359`, leaving exactly
the zeta load shown here. -/
theorem cubicLoadRowZeroPolynomial68_coeff_terminal_offset_sixty
    (alpha gamma epsilon zeta eta : k) (A B c d e : k[X])
    (hA : A.natDegree ≤ 120) (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ 60) (hd : d.natDegree ≤ 60)
    (he : e.natDegree ≤ 120) :
    (cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff 359 =
      (40 / 3 : k) * zeta * A.coeff 120 ^ 3 := by
  let D0 : k[X] := (1 / 3 : k) • (A * B) + d
  let E0 : k[X] :=
    (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
  let Ur : k[X] := (2 / 3 * gamma : k) • B + C zeta
  let W : k[X] :=
    (1 / 9 * gamma : k) • A ^ 2 + (2 / 3 * gamma : k) • c +
      (1 / 3 * epsilon : k) • A + C eta
  have hUl : cubicLoadUPolynomial68 0 alpha 0 gamma 0 zeta
      A B c D0 e = alpha • D0 + Ur := by
    simp [D0, Ur, cubicLoadUPolynomial68]
    module
  have hVl : cubicLoadVPolynomial68 0 alpha 0 gamma 0 epsilon eta
      A B c D0 e = alpha • E0 + W := by
    simp only [D0, E0, W, cubicLoadVPolynomial68, zero_mul, zero_smul,
      smul_zero, zero_add, add_zero]
    module
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
  have hDdeg : D0.natDegree ≤ 120 := by
    simp only [D0]
    compute_degree
    omega
  have hEdeg : E0.natDegree ≤ 360 := by
    simp only [E0]
    compute_degree
    omega
  have hUrdeg : Ur.natDegree ≤ 0 := by
    simp only [Ur]
    compute_degree
    omega
  have hWdeg : W.natDegree ≤ 240 := by
    simp only [W]
    compute_degree
    omega
  have hA3 := coeff_pow_at_bound68 A 120 3 hA
  norm_num at hA3
  have hAclt : (A * c).natDegree < 360 := by compute_degree; omega
  have helt : e.natDegree < 360 := he.trans_lt (by omega)
  have hEtop : E0.coeff 360 = (1 / 27 : k) * A.coeff 120 ^ 3 := by
    simp only [E0, coeff_add, coeff_smul, smul_eq_mul, hA3,
      coeff_eq_zero_of_natDegree_lt hAclt,
      coeff_eq_zero_of_natDegree_lt helt, mul_zero, add_zero]
  have hAB := coeff_mul_at_bounds68 A B 120 0 hA hB
  norm_num at hAB
  have hdlt : d.natDegree < 120 := hd.trans_lt (by omega)
  have hDtop : D0.coeff 120 =
      (1 / 3 : k) * A.coeff 120 * B.coeff 0 := by
    simp only [D0, coeff_add, coeff_smul, smul_eq_mul, hAB,
      coeff_eq_zero_of_natDegree_lt hdlt]
    ring
  have hA2 := coeff_pow_at_bound68 A 120 2 hA
  norm_num at hA2
  have hclt : c.natDegree < 240 := hc.trans_lt (by omega)
  have hAlt : A.natDegree < 240 := hA.trans_lt (by omega)
  have hCeta : (C eta : k[X]).coeff 240 = 0 := by simp
  have hWtop : W.coeff 240 =
      (1 / 9 * gamma : k) * A.coeff 120 ^ 2 := by
    simp only [W, coeff_add, coeff_smul, smul_eq_mul, hA2,
      coeff_eq_zero_of_natDegree_lt hclt,
      coeff_eq_zero_of_natDegree_lt hAlt, hCeta, mul_zero, add_zero]
  have hUrtop : Ur.coeff 0 =
      (2 / 3 * gamma : k) * B.coeff 0 + zeta := by
    simp only [Ur, coeff_add, coeff_smul, smul_eq_mul, coeff_C_zero]
  have h1 := coeff_mul_derivative_at_bounds68 Ur E0 0 360
    (by norm_num) hUrdeg hEdeg
  norm_num at h1
  have h2 := coeff_mul_derivative_at_bounds68 D0 W 120 240
    (by norm_num) hDdeg hWdeg
  norm_num at h2
  change (cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
      A B c D0 e).coeff 359 = _
  rw [hloadEq, coeff_sub, h1, h2, hUrtop, hEtop, hDtop, hWtop]
  push_cast
  ring

/-- Row-zero splitting already in the exact residual coordinates used by
the offset descent. -/
theorem cubicRowZeroPolynomial68_offsetSixty_residualSplit
    (alpha gamma epsilon zeta eta : k) (A B c d e : k[X]) :
    lowerRowZeroPolynomial68
      (integratedUPolynomial68 0 alpha 0 gamma 0 zeta A B
        ((1 / 3 : k) • A ^ 2 + c) ((1 / 3 : k) • (A * B) + d)
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      (integratedVPolynomial68 0 alpha 0 gamma 0 epsilon eta A B
        ((1 / 3 : k) • A ^ 2 + c) ((1 / 3 : k) • (A * B) + d)
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      ((1 / 3 : k) • (A * B) + d)
      ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e) =
      secondaryResidualRowZeroPolynomial68 A B c d e +
        cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
          A B c ((1 / 3 : k) • (A * B) + d) e := by
  have hcoords := integratedPolynomial68_cubicCoordinates
    (0 : k) alpha 0 gamma 0 epsilon zeta eta A B c
      ((1 / 3 : k) • (A * B) + d) e
  rw [hcoords.u_eq, hcoords.v_eq, cubicRowZeroPolynomial68_split,
    cubicHomogeneousRowZeroPolynomial68_residualCoordinates]

set_option maxHeartbeats 30000000 in
/-- Exact source backwire at the unique loaded offset-`60` wall.  The
expanded lower-row source has support only at degree `59`, hence its degree
`359` coefficient vanishes.  The literal row-zero load and loaded I4 then
force `zeta=0`. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_terminalOffsetSixty_zeta_zero68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hwall :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      n = 60 ∧ g = 180) :
    zeta = 0 := by
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
  change n = 60 ∧ g = 180 at hwall
  have hlater : 3 * n ≤ 2 * g := by omega
  have hp :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepOuter_offsetSixtyPacket68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hlater)
  change (n = 60 ∧ g = 180 ∧ _ ∧ _) ∨
    (60 < n ∧ ((_ ∧ _) ∨ (_ ∧ _ ∧ _ ∧ _ ∧ _))) at hp
  have hfourLoaded :
      (8 / 3 : k) *
          (Be.coeff (3 * n - g) * ee.coeff (6 * n - g - 60) +
            ce.coeff (4 * n - g) * d.coeff (5 * n - g - 60)) +
        zeta * Ae.coeff (2 * n) = 0 := by
    rcases hp with hloaded | habove
    · exact hloaded.2.2.1
    · omega
  have hparent :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepOuter_forces_fiveToSixStride68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hlater)
  change 5 * n < 2 * g ∧ 2 * g ≤ 6 * n ∧ _ = 0 ∧ _ = 0 ∧
    30 ∣ n ∧ 30 ∣ g ∧ 30 < n ∧ _ ∧
    d.natDegree ≤ 5 * n - g - 60 ∧
    ee.natDegree ≤ 6 * n - g - 60 at hparent
  obtain ⟨hgt5, hle6, _hfourTop, _hthreeTop, _hn30, _hg30,
    _hnBig, _hprevious, hd, he⟩ := hparent
  have hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n :=
    ⟨hgt5, hle6⟩
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
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec : Ee = (1 / 27 : k) • Ae ^ 3 +
      (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using
      cubicEDefectPolynomial68_eq_cubicCoordinates Ae Ce Ee
  have hDrec : De = (1 / 3 : k) • (Ae * Be) + d := by
    simpa only [d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
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
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) De Ee 359 hrowZero (by norm_num)
  rw [hl, hbeta, hdelta, hCrec, hErec, hDrec,
    cubicRowZeroPolynomial68_offsetSixty_residualSplit, coeff_add]
      at hzeroCoeff
  have hA120 : Ae.natDegree ≤ 120 := by
    simpa [hwall.1] using data.hA
  have hB0 : Be.natDegree ≤ 0 := by
    simpa [hwall.1, hwall.2] using data.hB
  have hc60 : ce.natDegree ≤ 60 := by
    simpa [hwall.1, hwall.2] using data.hc
  have hd60 : d.natDegree ≤ 60 := by
    simpa [hwall.1, hwall.2] using hd
  have he120 : ee.natDegree ≤ 120 := by
    simpa [hwall.1, hwall.2] using he
  have hn60 : 60 ≤ n := by omega
  have hres :=
    secondaryResidualRowZeroPolynomial68_coeff_gap_sixty_fiveToSix
      Ae Be ce d ee n g hn60 hwindow data.hA data.hB data.hc hd he
  norm_num [hwall.1, hwall.2] at hres
  have hload :=
    cubicLoadRowZeroPolynomial68_coeff_terminal_offset_sixty
      alpha gamma epsilon zeta eta Ae Be ce d ee
      hA120 hB0 hc60 hd60 he120
  rw [hres, hload] at hzeroCoeff
  norm_num [hwall.1, hwall.2] at hfourLoaded
  have hzetaCube : zeta * Ae.coeff 120 ^ 3 = 0 := by
    linear_combination (1 / 20 : k) * hzeroCoeff +
      (1 / 3 : k) * Ae.coeff 120 ^ 2 * hfourLoaded
  exact (mul_eq_zero.mp hzetaCube).resolve_right
    (pow_ne_zero 3 (by simpa [hwall.1] using data.ha))

set_option maxHeartbeats 30000000 in
/-- Refined offset-`60` packet.  The old load is deleted on its sole wall,
and both the wall and the generic range have the same honest dichotomy:
either the new pair is zero (the offset-`90` descent branch), or all four
directions are nonzero on `a*b^2+3*c^2=0`. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepOuter_offsetSixtyRowZeroPacket68
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
          ee.coeff (6 * n - g - 60) = 0) ∨
        (Be.coeff (3 * n - g) ≠ 0 ∧
          ce.coeff (4 * n - g) ≠ 0 ∧
          d.coeff (5 * n - g - 60) ≠ 0 ∧
          ee.coeff (6 * n - g - 60) ≠ 0 ∧
          Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 2 +
            3 * ce.coeff (4 * n - g) ^ 2 = 0)) := by
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
  change ((_ ∧ _ ∧ _) ∨ _) ∧ ((_ ∧ _) ∨
    (_ ∧ _ ∧ _ ∧ _ ∧ _))
  have hp :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepOuter_offsetSixtyPacket68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hlater)
  change (n = 60 ∧ g = 180 ∧ _ ∧ _) ∨
    (60 < n ∧ ((_ ∧ _) ∨ (_ ∧ _ ∧ _ ∧ _ ∧ _))) at hp
  rcases hp with hwall | habove
  · have hzeta :=
      maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_terminalOffsetSixty_zeta_zero68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
          ⟨hwall.1, hwall.2.1⟩)
    refine ⟨Or.inl ⟨hwall.1, hwall.2.1, hzeta⟩, ?_⟩
    have hfourLoaded := hwall.2.2.1
    rw [hzeta, zero_mul, add_zero] at hfourLoaded
    have hfour :
        Be.coeff (3 * n - g) * ee.coeff (6 * n - g - 60) +
          ce.coeff (4 * n - g) * d.coeff (5 * n - g - 60) = 0 :=
      (mul_eq_zero.mp hfourLoaded).resolve_left (by norm_num)
    have hthree :
        -Ae.coeff (2 * n) * Be.coeff (3 * n - g) *
            d.coeff (5 * n - g - 60) +
          3 * ce.coeff (4 * n - g) * ee.coeff (6 * n - g - 60) = 0 := by
      linear_combination hwall.2.2.2
    have hface : SecondaryResidualBetweenFace68
        (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
        (ce.coeff (4 * n - g)) (d.coeff (5 * n - g - 60))
        (ee.coeff (6 * n - g - 60)) := ⟨hfour, hthree⟩
    have data :=
      maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLoadI4Data68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys
    change LaterDeepLoadI4Data68 l beta gamma delta epsilon zeta
      n g Ae Be ce De ee at data
    have hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n := by omega
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
    exact firstSecondary_mainFamily_gapSucc_classify68
      (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
      (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
      (ee.coeff (6 * n - g)) (d.coeff (5 * n - g - 60))
      (ee.coeff (6 * n - g - 60)) data.ha hold hface
  · exact ⟨Or.inr habove.1, habove.2⟩

#print axioms secondaryResidualRowZeroPolynomial68_coeff_gap_sixty_fiveToSix
#print axioms cubicLoadRowZeroPolynomial68_coeff_terminal_offset_sixty
#print axioms cubicRowZeroPolynomial68_offsetSixty_residualSplit
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_terminalOffsetSixty_zeta_zero68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepOuter_offsetSixtyRowZeroPacket68

end LaterDeepLowerParentFiveToSixOffsetSixtyRowZero68

end Max11DegreeRoutes
