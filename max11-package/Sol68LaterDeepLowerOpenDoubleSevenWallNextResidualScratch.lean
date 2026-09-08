import Sol68LaterDeepLowerOpenDoubleExactFiveAssemblyScratch
import LowScale68SecondaryLaterDeepLowerOpenMiddleHighRightSevenRowOne

/-! # The next independent row on the double exact-seven wall

The reduced row-two wall relation is already known.  In the double chamber
the reduced row-one tail is also strictly below `5n-1`; its core gives the
independent factor `c * (c^2-a*b^2)`.  Combining the two equations yields an
exact three-branch packet without dividing by `b` or `c`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerOpenDoubleSevenWallNextResidual68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 30000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option maxHeartbeats 7000000 in
theorem fiveRadiusRightSevenRowOneTail68_degree_lt_of_doubleLaterDeepLowerOpen
    (gamma epsilon zeta : k) (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hdouble : 2 * g ≤ h)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hwall : 3 * g = 7 * n) (habove : 7 * n < 2 * h)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (fiveRadiusRightSevenRowOneTail68
      gamma epsilon zeta A B c d e).natDegree < 5 * n - 1 := by
  let idx := 5 * n - 1
  have hAd2 : (derivative (A * d ^ 2)).natDegree < idx := by
    by_cases hh : h ≤ 5 * n
    · have hp : (A * d ^ 2).natDegree ≤ 12 * n - 2 * h := by
        compute_degree
        omega
      have hder := natDegree_derivative_le (A * d ^ 2)
      dsimp [idx]
      omega
    · have hd0 : d.natDegree ≤ 0 := hd.trans (by omega)
      rw [eq_C_of_natDegree_le_zero hd0]
      simp only [derivative_mul, derivative_C, mul_zero, add_zero]
      dsimp [idx]
      compute_degree
      omega
  have hBcd : (derivative (B * c * d)).natDegree < idx := by
    by_cases hh : h ≤ 5 * n
    · have hp : (B * c * d).natDegree ≤ 12 * n - 2 * g - h := by
        compute_degree
        omega
      have hder := natDegree_derivative_le (B * c * d)
      dsimp [idx]
      omega
    · have hd0 : d.natDegree ≤ 0 := hd.trans (by omega)
      rw [eq_C_of_natDegree_le_zero hd0]
      simp only [derivative_mul, derivative_C, mul_zero, add_zero]
      dsimp [idx]
      compute_degree
      omega
  have hBpcd : (derivative B * c * d).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  have hB2e : (B ^ 2 * derivative e).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  have hee : (e * derivative e).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  have hBd : (B * derivative d).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  have hdB : (d * derivative B).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  have hcc : (c * derivative c).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  have hApB2 : (derivative A * B ^ 2).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  have hABBp : (A * B * derivative B).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  have hep : (derivative e).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  have hApB : (derivative A * B).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  have hdp : (derivative d).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  simp only [fiveRadiusRightSevenRowOneTail68,
    fiveRadiusTerminalEqualityRowOneTail68]
  exact deepGap_natDegree_add_lt
    (deepGap_natDegree_add_lt
      (deepGap_natDegree_add_lt
        (deepGap_natDegree_smul_lt68 (-4 / 27 : k)
          (deepGap_natDegree_add_lt
            (deepGap_natDegree_add_lt
              (deepGap_natDegree_add_lt
                (deepGap_natDegree_add_lt
                  (deepGap_natDegree_smul_lt68 (3 : k) hAd2)
                  (deepGap_natDegree_smul_lt68 (3 : k) hBcd))
                (deepGap_natDegree_smul_lt68 (6 : k) hBpcd))
              (deepGap_natDegree_smul_lt68 (-3 : k) hB2e))
            (deepGap_natDegree_smul_lt68 (-18 : k) hee)))
        (deepGap_natDegree_smul_lt68 gamma
          (deepGap_natDegree_add_lt
            (deepGap_natDegree_add_lt
              (deepGap_natDegree_smul_lt68 (2 / 3 : k)
                (deepGap_natDegree_sub_lt
                  (deepGap_natDegree_sub_lt hBd hdB)
                  (deepGap_natDegree_smul_lt68 (2 : k) hcc)))
              (deepGap_natDegree_smul_lt68 (2 / 9 : k) hApB2))
            (deepGap_natDegree_smul_lt68 (4 / 9 : k) hABBp))))
      (deepGap_natDegree_smul_lt68 (2 * epsilon : k) hep))
    (deepGap_natDegree_smul_lt68 zeta
      (deepGap_natDegree_add_lt
        (deepGap_natDegree_smul_lt68 (1 / 3 : k) hApB) hdp))

set_option maxHeartbeats 9000000 in
theorem fiveRadiusReducedRowOnePolynomial68_doubleRightSeven_factor68
    (alpha gamma epsilon zeta eta i3 : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h)
    (hdouble : 2 * g ≤ h)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hwall : 3 * g = 7 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hi3 : cubicFirstIntegralThreePolynomial68
      0 0 gamma 0 epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i3)
    (hrow : secondaryResidualRowOnePolynomial68 A B c d e +
      cubicLoadRowOnePolynomial68
        0 alpha 0 gamma 0 epsilon zeta eta A B c
          ((1 / 3 : k) • (A * B) + d) e = 0) :
    c.coeff (4 * n - g) *
      (c.coeff (4 * n - g) ^ 2 -
        A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2) = 0 := by
  have hreduced := fiveRadiusReducedRowOnePolynomial68_eq_zero
    alpha gamma epsilon zeta eta i3 A B c d e hi3 hrow
  have habove : 7 * n < 2 * h := by omega
  have htail :=
    fiveRadiusRightSevenRowOneTail68_degree_lt_of_doubleLaterDeepLowerOpen
      gamma epsilon zeta A B c d e n g h hn hg hgh hdouble hopen hwall
      habove hA hB hc hd he
  have hcore := fiveRadiusTerminalEqualityRowOneCore68_coeff_of_rightSeven
    A B c n g hn hg hwall hA hB hc
  have hz := congrArg (fun p : k[X] => p.coeff (5 * n - 1)) hreduced
  rw [fiveRadiusReducedRowOnePolynomial68_rightSevenSplit, coeff_add,
    hcore, coeff_eq_zero_of_natDegree_lt htail, add_zero, coeff_zero] at hz
  have hN : 5 * n = 3 * (4 * n - g) := by omega
  rw [hN] at hz
  push_cast at hz
  have hscaled :
      ((-8 / 9 : k) * (((4 * n - g : ℕ) : k))) *
        (c.coeff (4 * n - g) *
          (c.coeff (4 * n - g) ^ 2 -
            A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2)) = 0 := by
    linear_combination hz
  have hfac : (-8 / 9 : k) * (((4 * n - g : ℕ) : k)) ≠ 0 :=
    mul_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr (by omega))
  exact (mul_eq_zero.mp hscaled).resolve_left hfac

theorem laterDeepLowerOpenDoubleRightSeven_nextResidual_classification68
    (a b c zeta : k) (ha : a ≠ 0)
    (hrow : c * (c ^ 2 - a * b ^ 2) = 0)
    (hwall : (32 / 81 : k) * b * (a * b ^ 2 - 9 * c ^ 2) +
      zeta * a ^ 2 = 0) :
    (b = 0 ∧ c = 0 ∧ zeta = 0) ∨
      (b ≠ 0 ∧
        ((c = 0 ∧ zeta * a = (-32 / 81 : k) * b ^ 3) ∨
          (c ≠ 0 ∧ c ^ 2 = a * b ^ 2 ∧
            zeta * a = (256 / 81 : k) * b ^ 3))) := by
  by_cases hb : b = 0
  · left
    have hc3 : c ^ 3 = 0 := by
      have ht : c * c ^ 2 = 0 := by
        simpa only [hb, zero_pow (by norm_num : 2 ≠ 0), mul_zero,
          sub_zero] using hrow
      simpa only [pow_succ, mul_comm] using ht
    have hc : c = 0 := eq_zero_of_pow_eq_zero hc3
    have hzetaA2 : zeta * a ^ 2 = 0 := by
      simpa only [hb, hc, zero_pow (by norm_num : 2 ≠ 0), mul_zero,
        zero_mul, sub_zero, add_zero, zero_add] using hwall
    have hzeta : zeta = 0 :=
      (mul_eq_zero.mp hzetaA2).resolve_right (pow_ne_zero 2 ha)
    exact ⟨hb, hc, hzeta⟩
  · right
    refine ⟨hb, ?_⟩
    by_cases hc : c = 0
    · left
      refine ⟨hc, ?_⟩
      have ht := hwall
      rw [hc] at ht
      have hfactor : a ≠ 0 := ha
      have hraw : a *
          (zeta * a - (-32 / 81 : k) * b ^ 3) = 0 := by
        linear_combination ht
      exact sub_eq_zero.mp ((mul_eq_zero.mp hraw).resolve_left hfactor)
    · right
      have htangent : c ^ 2 = a * b ^ 2 := by
        exact sub_eq_zero.mp ((mul_eq_zero.mp hrow).resolve_left hc)
      refine ⟨hc, htangent, ?_⟩
      have ht := hwall
      rw [htangent] at ht
      have hraw : a *
          (zeta * a - (256 / 81 : k) * b ^ 3) = 0 := by
        linear_combination ht
      exact sub_eq_zero.mp ((mul_eq_zero.mp hraw).resolve_left ha)

set_option maxHeartbeats 30000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleStrictHighRightSevenWall_nextResidual68
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
    let a := Ae.coeff (2 * n)
    let b := Be.coeff (3 * n - g)
    let c := ce.coeff (4 * n - g)
    delta = 0 ∧ b ≠ 0 ∧
      ((c = 0 ∧ zeta * a = (-32 / 81 : k) * b ^ 3) ∨
        (c ≠ 0 ∧ c ^ 2 = a * b ^ 2 ∧
          zeta * a = (256 / 81 : k) * b ^ 3)) := by
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
  have wallPacket :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleStrictHighRightSevenWall_relation68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hdouble)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
  change delta = 0 ∧
      (8 / 81 : k) * ((4 * n : ℕ) : k) * b *
          (a * b ^ 2 - (9 : k) * c ^ 2) +
        zeta * (n : k) * a ^ 2 = 0 at wallPacket
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
  have hg : 0 < g := secondary.1
  have ha : a ≠ 0 := by
    simpa only [a, n, Ae] using core.2.2.2.2.2
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
  have support : b ≠ 0 ∨ c ≠ 0 := by
    rcases secondary.2.2.2.2.2 with hb | hc | hD | he
    · exact Or.inl hb
    · exact Or.inr hc
    · left
      intro hb0
      change Be.coeff (3 * n - g) = 0 at hb0
      have hab : Ae.coeff (2 * n) * Be.coeff (3 * n - g) = 0 := by
        rw [hb0, mul_zero]
      rw [drops.2.2.2.1] at hab
      exact hD ((mul_eq_zero.mp hab).resolve_left (by norm_num))
    · exact False.elim (he drops.2.2.1)
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
  obtain ⟨i3, hi3⟩ := hsys.firstThree
  have hi3c : cubicFirstIntegralThreePolynomial68
      0 0 gamma 0 epsilon zeta Ae Be ce Dtr ee = C i3 := by
    have hi3e : firstIntegralThreePolynomial68
        l beta gamma delta epsilon zeta Ae Be Ce De Ee = C i3 := by
      simpa only [Ae, Be, Ce, De, Ee] using
        expand_firstIntegralThreePolynomial68_of_eq
          l beta gamma delta epsilon zeta i3 A B C0 D E hi3
    rw [hCrec, hErec, firstIntegralThreePolynomial68_cubicCoordinates,
      hDrec, drops.1, drops.2.1, wallPacket.1] at hi3e
    exact hi3e
  have h1e : lowerRowOnePolynomial68
      (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) Ce De Ee = 0 := by
    dsimp only [Ae, Be, Ce, De, Ee]
    rw [← expand_integratedTPolynomial68, ← expand_integratedUPolynomial68,
      ← expand_integratedVPolynomial68, lowerRowOnePolynomial68_expand,
      hsys.rowOne, map_zero, zero_mul]
  have hrow : secondaryResidualRowOnePolynomial68 Ae Be ce d ee +
      cubicLoadRowOnePolynomial68
        0 alpha 0 gamma 0 epsilon zeta eta Ae Be ce Dtr ee = 0 := by
    have hr := h1e
    rw [hCrec, hDrec, hErec, drops.1, drops.2.1, wallPacket.1] at hr
    exact polynomialSecondaryResidualRowOne68
      0 alpha 0 gamma 0 epsilon zeta eta Ae Be ce d ee hr
  have hrowFactor :=
    fiveRadiusReducedRowOnePolynomial68_doubleRightSeven_factor68
      alpha gamma epsilon zeta eta i3 Ae Be ce d ee n g h hn hg
      drops.2.2.2.2.2.2 hdouble hopen hwall hA secondary.2.1
      secondary.2.2.1 bounds.1 bounds.2 hi3c hrow
  change c * (c ^ 2 - a * b ^ 2) = 0 at hrowFactor
  have hwallNormalized :
      (32 / 81 : k) * b * (a * b ^ 2 - 9 * c ^ 2) +
        zeta * a ^ 2 = 0 := by
    have ht := wallPacket.2
    have hcast : (((4 * n : ℕ) : k)) = 4 * (n : k) := by
      push_cast
      rfl
    rw [hcast] at ht
    have hN : (n : k) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    have hfac : (n : k) *
        ((32 / 81 : k) * b * (a * b ^ 2 - 9 * c ^ 2) +
          zeta * a ^ 2) = 0 := by
      linear_combination ht
    exact (mul_eq_zero.mp hfac).resolve_left hN
  have classification :=
    laterDeepLowerOpenDoubleRightSeven_nextResidual_classification68
      a b c zeta ha hrowFactor hwallNormalized
  rcases classification with hzero | hnonzero
  · exact False.elim (support.elim (fun hb => hb hzero.1)
      (fun hc => hc hzero.2.1))
  · exact ⟨wallPacket.1, hnonzero.1, hnonzero.2⟩

#print axioms fiveRadiusRightSevenRowOneTail68_degree_lt_of_doubleLaterDeepLowerOpen
#print axioms fiveRadiusReducedRowOnePolynomial68_doubleRightSeven_factor68
#print axioms laterDeepLowerOpenDoubleRightSeven_nextResidual_classification68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleStrictHighRightSevenWall_nextResidual68

end LaterDeepLowerOpenDoubleSevenWallNextResidual68

end Max11DegreeRoutes
