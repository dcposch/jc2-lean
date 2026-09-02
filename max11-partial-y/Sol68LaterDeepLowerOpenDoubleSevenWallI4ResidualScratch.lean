import Sol68LaterDeepLowerOpenDoubleSevenWallNextResidualScratch

/-! # The independent I4 face after the exact-seven row-one packet -/

/-
At coefficient `2n`, strict residual overshoot leaves only `-8b^3/27`
against `zeta*a`, which contradicts both row-one branches.  Thus `h=2g`.
On that equality the `B*e+c*d` face loads exactly and gives the next rigid
edge packet.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerOpenDoubleSevenWallI4Residual68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 30000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option maxHeartbeats 4000000 in
theorem secondaryResidualInvariantFourPolynomial68_coeff_twoRadius_of_doubleRightSevenStrict68
    (B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hwall : 3 * g = 7 * n) (hstrict : 2 * g < h)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (secondaryResidualInvariantFourPolynomial68 B c d e).coeff (2 * n) =
      (-8 / 27 : k) * B.coeff (3 * n - g) ^ 3 := by
  have hB3deg : (B ^ 3).natDegree ≤ 3 * (3 * n - g) := by
    compute_degree
    exact Nat.mul_le_mul_left 3 hB
  have hB3 := coeff_pow_at_bound68 B (3 * n - g) 3 hB
  have hB3i : 3 * (3 * n - g) = 2 * n := by omega
  rw [hB3i] at hB3
  have hBe : (B * e).natDegree < 2 * n := by
    compute_degree
    omega
  have hcd : (c * d).natDegree < 2 * n := by
    compute_degree
    omega
  simp only [secondaryResidualInvariantFourPolynomial68, coeff_add,
    coeff_smul, smul_eq_mul, hB3,
    coeff_eq_zero_of_natDegree_lt hBe,
    coeff_eq_zero_of_natDegree_lt hcd, mul_zero, add_zero]

set_option maxHeartbeats 4000000 in
theorem secondaryResidualInvariantFourPolynomial68_coeff_twoRadius_of_doubleRightSevenEquality68
    (B c d e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hwall : 3 * g = 7 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - 2 * g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (secondaryResidualInvariantFourPolynomial68 B c d e).coeff (2 * n) =
      (-8 / 27 : k) * B.coeff (3 * n - g) ^ 3 +
        (8 / 3 : k) *
          (B.coeff (3 * n - g) * e.coeff (6 * n - 2 * g) +
            c.coeff (4 * n - g) * d.coeff (5 * n - 2 * g)) := by
  have hB3 := coeff_pow_at_bound68 B (3 * n - g) 3 hB
  have hB3i : 3 * (3 * n - g) = 2 * n := by omega
  rw [hB3i] at hB3
  have hBe := coeff_mul_at_bounds68 B e
    (3 * n - g) (6 * n - 2 * g) hB he
  have hBei : (3 * n - g) + (6 * n - 2 * g) = 2 * n := by omega
  rw [hBei] at hBe
  have hcd := coeff_mul_at_bounds68 c d
    (4 * n - g) (5 * n - 2 * g) hc hd
  have hcdi : (4 * n - g) + (5 * n - 2 * g) = 2 * n := by omega
  rw [hcdi] at hcd
  simp only [secondaryResidualInvariantFourPolynomial68, coeff_add,
    coeff_smul, smul_eq_mul, hB3, hBe, hcd]
  ring

theorem laterDeepLowerOpenDoubleRightSeven_strictI4_inconsistent68
    (b zetaA : k) (hb : b ≠ 0)
    (hbranch : zetaA = (-32 / 81 : k) * b ^ 3 ∨
      zetaA = (256 / 81 : k) * b ^ 3)
    (hi4 : (-8 / 27 : k) * b ^ 3 + zetaA = 0) : False := by
  rcases hbranch with hzeta | hzeta
  · rw [hzeta] at hi4
    have hzero : (-56 / 81 : k) * b ^ 3 = 0 := by
      linear_combination hi4
    exact (pow_ne_zero 3 hb)
      ((mul_eq_zero.mp hzero).resolve_left (by norm_num))
  · rw [hzeta] at hi4
    have hzero : (232 / 81 : k) * b ^ 3 = 0 := by
      linear_combination hi4
    exact (pow_ne_zero 3 hb)
      ((mul_eq_zero.mp hzero).resolve_left (by norm_num))

theorem laterDeepLowerOpenDoubleRightSeven_equalityI4_edges68
    (a b c d0 e0 zeta : k) (hb : b ≠ 0)
    (hbranch :
      (c = 0 ∧ zeta * a = (-32 / 81 : k) * b ^ 3) ∨
        (c ≠ 0 ∧ c ^ 2 = a * b ^ 2 ∧
          zeta * a = (256 / 81 : k) * b ^ 3))
    (hi4 : (-8 / 27 : k) * b ^ 3 +
      (8 / 3 : k) * (b * e0 + c * d0) + zeta * a = 0) :
    (c = 0 ∧ zeta * a = (-32 / 81 : k) * b ^ 3 ∧
        e0 = (7 / 27 : k) * b ^ 2) ∨
      (c ≠ 0 ∧ c ^ 2 = a * b ^ 2 ∧
        zeta * a = (256 / 81 : k) * b ^ 3 ∧
        b * e0 + c * d0 = (-29 / 27 : k) * b ^ 3) := by
  rcases hbranch with hzero | htangent
  · left
    refine ⟨hzero.1, hzero.2, ?_⟩
    rw [hzero.1, hzero.2] at hi4
    have hprod : b * (e0 - (7 / 27 : k) * b ^ 2) = 0 := by
      linear_combination (3 / 8 : k) * hi4
    exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left hb)
  · right
    refine ⟨htangent.1, htangent.2.1, htangent.2.2, ?_⟩
    rw [htangent.2.2] at hi4
    linear_combination (3 / 8 : k) * hi4

set_option maxHeartbeats 30000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleStrictHighRightSevenWall_I4Residual68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hopen :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hdouble :
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
      let h := secondaryResidualGap68 n d ee
      2 * g ≤ h)
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
      3 * g = 7 * n) :
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
    let h := secondaryResidualGap68 n d ee
    let a := Ae.coeff (2 * n)
    let b := Be.coeff (3 * n - g)
    let c := ce.coeff (4 * n - g)
    h = 2 * g ∧ delta = 0 ∧ b ≠ 0 ∧
      ((c = 0 ∧ zeta * a = (-32 / 81 : k) * b ^ 3 ∧
          ee.coeff (6 * n - 2 * g) = (7 / 27 : k) * b ^ 2) ∨
        (c ≠ 0 ∧ c ^ 2 = a * b ^ 2 ∧
          zeta * a = (256 / 81 : k) * b ^ 3 ∧
          b * ee.coeff (6 * n - 2 * g) +
            c * d.coeff (5 * n - 2 * g) =
              (-29 / 27 : k) * b ^ 3)) := by
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
  let h := secondaryResidualGap68 n d ee
  let Dtr := (1 / 3 : k) • (Ae * Be) + d
  let a := Ae.coeff (2 * n)
  let b := Be.coeff (3 * n - g)
  let c := ce.coeff (4 * n - g)
  change 3 * n < 2 * g ∧ 2 * g < 5 * n at hopen
  change 2 * g ≤ h at hdouble
  change 3 * g = 7 * n at hwall
  have prior :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleStrictHighRightSevenWall_nextResidual68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hdouble)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
  change delta = 0 ∧ b ≠ 0 ∧
      ((c = 0 ∧ zeta * a = (-32 / 81 : k) * b ^ 3) ∨
        (c ≠ 0 ∧ c ^ 2 = a * b ^ 2 ∧
          zeta * a = (256 / 81 : k) * b ^ 3)) at prior
  have core := maximalExpandedIntegratedPolynomialLowerSystem_cubicCore68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have drop := maximalExpandedIntegratedPolynomialLowerSystem_degreeDrop68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have secondary := maximalExpandedIntegratedPolynomialLowerSystem_secondaryRadius68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  change 0 < g ∧ Be.natDegree ≤ 3 * n - g ∧
    ce.natDegree ≤ 4 * n - g ∧ De.natDegree ≤ 5 * n - g ∧
    ee.natDegree ≤ 6 * n - g ∧ _ at secondary
  have hn : 0 < n := by simpa only [n] using core.1
  have hA : Ae.natDegree ≤ 2 * n := by
    have hAe : Ae.natDegree = 2 * n := by
      simpa only [n, Ae, Be, Ce, De, Ee] using drop.1
    omega
  have drops :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenResidualDrops68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
  change l = 0 ∧ beta = 0 ∧ ee.coeff (6 * n - g) = 0 ∧
      Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
        3 * De.coeff (5 * n - g) ∧
      d.natDegree < 5 * n - g ∧ ee.natDegree < 6 * n - g ∧ g < h
    at drops
  have hdbase : d.natDegree < 5 * n := drops.2.2.2.2.1.trans (by omega)
  have hebase : ee.natDegree < 6 * n := drops.2.2.2.2.2.1.trans (by omega)
  have bounds := secondaryResidualGap68_degreeBounds n d ee hdbase hebase
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec : Ee = (1 / 27 : k) • Ae ^ 3 +
      (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using
      cubicEDefectPolynomial68_eq_cubicCoordinates Ae Ce Ee
  have hDrec : De = Dtr := by
    simpa only [Dtr, d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
  obtain ⟨i4, hi4⟩ := hsys.firstFour
  have hi4c : cubicFirstIntegralFourPolynomial68
      0 0 gamma 0 epsilon zeta Ae Be ce Dtr ee = C i4 := by
    have hi4e : firstIntegralFourPolynomial68
        l beta gamma delta epsilon zeta Ae Be Ce De Ee = C i4 := by
      simpa only [Ae, Be, Ce, De, Ee] using
        expand_firstIntegralFourPolynomial68_of_eq
          l beta gamma delta epsilon zeta i4 A B C0 D E hi4
    rw [hCrec, hErec, firstIntegralFourPolynomial68_cubicCoordinates,
      hDrec, drops.1, drops.2.1, prior.1] at hi4e
    exact hi4e
  have hload :=
    secondaryLoadInvariantFourPolynomial68_coeff_twoRadius_of_delta_zero_seven_sum
      gamma epsilon zeta Ae Be ce d ee n g h hn hopen (by omega)
      hA secondary.2.1 bounds.1
  by_cases heq : h = 2 * g
  · have hd2 : d.natDegree ≤ 5 * n - 2 * g := by
      have ht := bounds.1
      change d.natDegree ≤ 5 * n - h at ht
      rwa [heq] at ht
    have he2 : ee.natDegree ≤ 6 * n - 2 * g := by
      have ht := bounds.2
      change ee.natDegree ≤ 6 * n - h at ht
      rwa [heq] at ht
    have hcoeff := congrArg (fun p : k[X] => p.coeff (2 * n)) hi4c
    rw [cubicFirstIntegralFourPolynomial68_secondaryLoadSplit,
      show cubicFirstIntegralFourPolynomial68 0 0 0 0 0 0 Ae Be ce Dtr ee =
        secondaryResidualInvariantFourPolynomial68 Be ce d ee from
          cubicFirstIntegralFourPolynomial68_residualCoordinates Ae Be ce d ee,
      coeff_add,
      secondaryResidualInvariantFourPolynomial68_coeff_twoRadius_of_doubleRightSevenEquality68
        Be ce d ee n g hn hwall secondary.2.1 secondary.2.2.1 hd2 he2,
      hload] at hcoeff
    have hidx : 2 * n ≠ 0 := by omega
    simp only [coeff_C, if_neg hidx] at hcoeff
    have hi4scalar : (-8 / 27 : k) * b ^ 3 +
        (8 / 3 : k) *
          (b * ee.coeff (6 * n - 2 * g) +
            c * d.coeff (5 * n - 2 * g)) + zeta * a = 0 := by
      simpa only [a, b, c] using hcoeff
    exact ⟨heq, prior.1, prior.2.1,
      laterDeepLowerOpenDoubleRightSeven_equalityI4_edges68
        a b c (d.coeff (5 * n - 2 * g))
          (ee.coeff (6 * n - 2 * g)) zeta prior.2.1 prior.2.2 hi4scalar⟩
  · have hstrict : 2 * g < h := lt_of_le_of_ne hdouble (Ne.symm heq)
    have hcoeff := congrArg (fun p : k[X] => p.coeff (2 * n)) hi4c
    rw [cubicFirstIntegralFourPolynomial68_secondaryLoadSplit,
      show cubicFirstIntegralFourPolynomial68 0 0 0 0 0 0 Ae Be ce Dtr ee =
        secondaryResidualInvariantFourPolynomial68 Be ce d ee from
          cubicFirstIntegralFourPolynomial68_residualCoordinates Ae Be ce d ee,
      coeff_add,
      secondaryResidualInvariantFourPolynomial68_coeff_twoRadius_of_doubleRightSevenStrict68
        Be ce d ee n g h hn hwall hstrict secondary.2.1
          secondary.2.2.1 bounds.1 bounds.2,
      hload] at hcoeff
    have hidx : 2 * n ≠ 0 := by omega
    simp only [coeff_C, if_neg hidx] at hcoeff
    have hi4scalar : (-8 / 27 : k) * b ^ 3 + zeta * a = 0 := by
      simpa only [a, b] using hcoeff
    have hzeta : zeta * a = (-32 / 81 : k) * b ^ 3 ∨
        zeta * a = (256 / 81 : k) * b ^ 3 := by
      rcases prior.2.2 with hzero | htangent
      · exact Or.inl hzero.2
      · exact Or.inr htangent.2.2
    exact False.elim
      (laterDeepLowerOpenDoubleRightSeven_strictI4_inconsistent68
        b (zeta * a) prior.2.1 hzeta hi4scalar)

#print axioms secondaryResidualInvariantFourPolynomial68_coeff_twoRadius_of_doubleRightSevenStrict68
#print axioms secondaryResidualInvariantFourPolynomial68_coeff_twoRadius_of_doubleRightSevenEquality68
#print axioms laterDeepLowerOpenDoubleRightSeven_strictI4_inconsistent68
#print axioms laterDeepLowerOpenDoubleRightSeven_equalityI4_edges68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleStrictHighRightSevenWall_I4Residual68

end LaterDeepLowerOpenDoubleSevenWallI4Residual68

end Max11DegreeRoutes
