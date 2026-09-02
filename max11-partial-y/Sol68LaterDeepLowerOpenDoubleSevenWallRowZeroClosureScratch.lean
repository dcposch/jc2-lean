import Sol68LaterDeepLowerOpenDoubleSevenWallI4ResidualScratch
import LowScale68SecondaryLaterDeepFiveRadiusTerminalRowZeroAlgebra

/-! # Row-zero closure of the double exact-seven equality wall

The independent terminal row at coefficient `6n-1` closes both rigid I4
branches.  On `3g=7n` and `h=2g`, its homogeneous face is

`(8/27)n*a*(-a*b*e0-a*c*d0+b*c^2)`

and the only load at the same height is `(2/9)n*zeta*a^3`.  The remaining
load terms are strictly lower.  Substitution of either exact I4 branch gives
a nonzero multiple of `a*b^3`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerOpenDoubleSevenWallRowZeroClosure68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 30000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option maxHeartbeats 7000000 in
theorem secondaryResidualRowZeroPolynomial68_coeff_sixRadius_of_doubleRightSevenEquality68
    (A B c d e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hwall : 3 * g = 7 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - 2 * g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (secondaryResidualRowZeroPolynomial68 A B c d e).coeff (6 * n - 1) =
      (8 / 27 : k) * (n : k) * A.coeff (2 * n) *
        (-(A.coeff (2 * n) * B.coeff (3 * n - g) *
              e.coeff (6 * n - 2 * g)) -
          A.coeff (2 * n) * c.coeff (4 * n - g) *
              d.coeff (5 * n - 2 * g) +
          B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2) := by
  have h1 := coeff_mul_mul_mul_derivative_at_bounds68 A B e A
    (2 * n) (3 * n - g) (6 * n - 2 * g) (2 * n) (by omega)
    hA hB he hA
  have hi1 : 2 * n + (3 * n - g) + (6 * n - 2 * g) + 2 * n - 1 =
      6 * n - 1 := by omega
  rw [hi1] at h1
  have h1' : (A * derivative A * B * e).coeff (6 * n - 1) =
      A.coeff (2 * n) * A.coeff (2 * n) * B.coeff (3 * n - g) *
        e.coeff (6 * n - 2 * g) * ((2 * n : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h1
  have h2 := coeff_mul_mul_mul_derivative_at_bounds68 A c d A
    (2 * n) (4 * n - g) (5 * n - 2 * g) (2 * n) (by omega)
    hA hc hd hA
  have hi2 : 2 * n + (4 * n - g) + (5 * n - 2 * g) + 2 * n - 1 =
      6 * n - 1 := by omega
  rw [hi2] at h2
  have h2' : (A * derivative A * c * d).coeff (6 * n - 1) =
      A.coeff (2 * n) * A.coeff (2 * n) * c.coeff (4 * n - g) *
        d.coeff (5 * n - 2 * g) * ((2 * n : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h2
  have h3 := coeff_mul_mul_mul_derivative_at_bounds68 B c c A
    (3 * n - g) (4 * n - g) (4 * n - g) (2 * n) (by omega)
    hB hc hc hA
  have hi3 : (3 * n - g) + (4 * n - g) + (4 * n - g) + 2 * n - 1 =
      6 * n - 1 := by omega
  rw [hi3] at h3
  have h3' : (derivative A * B * c ^ 2).coeff (6 * n - 1) =
      A.coeff (2 * n) * B.coeff (3 * n - g) *
        c.coeff (4 * n - g) ^ 2 * ((2 * n : ℕ) : k) := by
    simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using h3
  have hlow1 : (A * B ^ 2 * derivative d).natDegree < 6 * n - 1 := by
    compute_degree
    omega
  have hlow2 : (A * B * derivative B * d).natDegree < 6 * n - 1 := by
    compute_degree
    omega
  have hlow3 : (derivative A * d * e).natDegree < 6 * n - 1 := by
    compute_degree
    omega
  have hlow4 : (B * c * derivative e).natDegree < 6 * n - 1 := by
    compute_degree
    omega
  have hlow5 : (B * d * derivative d).natDegree < 6 * n - 1 := by
    compute_degree
    omega
  have hlow6 : (derivative B * d ^ 2).natDegree < 6 * n - 1 := by
    compute_degree
    omega
  have hlow7 : (c * derivative c * d).natDegree < 6 * n - 1 := by
    compute_degree
    omega
  simp only [secondaryResidualRowZeroPolynomial68, coeff_smul, coeff_add,
    coeff_sub, h1', h2', h3',
    coeff_eq_zero_of_natDegree_lt hlow1,
    coeff_eq_zero_of_natDegree_lt hlow2,
    coeff_eq_zero_of_natDegree_lt hlow3,
    coeff_eq_zero_of_natDegree_lt hlow4,
    coeff_eq_zero_of_natDegree_lt hlow5,
    coeff_eq_zero_of_natDegree_lt hlow6,
    coeff_eq_zero_of_natDegree_lt hlow7, smul_eq_mul]
  push_cast
  ring

set_option maxHeartbeats 5000000 in
theorem cubicLoadRowZeroPolynomial68_deltaZero_split_zeta68
    (alpha gamma epsilon zeta eta : k) (A B c d e : k[X]) :
    cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
        A B c ((1 / 3 : k) • (A * B) + d) e =
      fiveRadiusTerminalRowZeroLoad68 gamma epsilon A B c d e +
        zeta • derivative
          ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e) := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [cubicLoadRowZeroPolynomial68, cubicLoadUPolynomial68,
    cubicLoadVPolynomial68, fiveRadiusTerminalRowZeroLoad68,
    zero_mul, zero_smul, smul_zero, add_zero, zero_add, sub_zero,
    derivative_add, derivative_sub, derivative_mul, derivative_pow,
    derivative_smul, derivative_C, one_mul, Polynomial.smul_eq_C_mul,
    map_add, map_sub, map_mul, map_pow, map_neg, map_zero,
    RatFunc.algebraMap_C, map_div₀, map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 4000000 in
theorem fiveRadiusTerminalRowZeroLoad68_degree_lt_sixRadius_of_rightSevenEquality68
    (gamma epsilon : k) (A B c d e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hwall : 3 * g = 7 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - 2 * g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (fiveRadiusTerminalRowZeroLoad68 gamma epsilon A B c d e).natDegree <
      6 * n - 1 := by
  simp only [fiveRadiusTerminalRowZeroLoad68]
  compute_degree
  omega

set_option maxHeartbeats 6000000 in
theorem cubicLoadRowZeroPolynomial68_coeff_sixRadius_of_doubleRightSevenEquality68
    (alpha gamma epsilon zeta eta : k) (A B c d e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hwall : 3 * g = 7 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - 2 * g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff (6 * n - 1) =
        (2 / 9 : k) * (n : k) * zeta * A.coeff (2 * n) ^ 3 := by
  let E0 := (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
  have hlower :=
    fiveRadiusTerminalRowZeroLoad68_degree_lt_sixRadius_of_rightSevenEquality68
      gamma epsilon A B c d e n g hn hg hwall hA hB hc hd he
  have hA3 := coeff_pow_at_bound68 A (2 * n) 3 hA
  have hA3i : 3 * (2 * n) = 6 * n := by omega
  rw [hA3i] at hA3
  have hAc : (A * c).natDegree < 6 * n := by
    compute_degree
    omega
  have helow : e.natDegree < 6 * n := he.trans_lt (by omega)
  have hEcoeff : E0.coeff (6 * n) =
      (1 / 27 : k) * A.coeff (2 * n) ^ 3 := by
    simp only [E0, coeff_add, coeff_smul, smul_eq_mul, hA3,
      coeff_eq_zero_of_natDegree_lt hAc,
      coeff_eq_zero_of_natDegree_lt helow, mul_zero, add_zero]
  have hEdeg : E0.natDegree ≤ 6 * n := by
    simp only [E0]
    compute_degree
    omega
  have hder := coeff_derivative_at_bound68 E0 (6 * n) (by omega)
  rw [hEcoeff] at hder
  rw [cubicLoadRowZeroPolynomial68_deltaZero_split_zeta68,
    coeff_add, coeff_eq_zero_of_natDegree_lt hlower, zero_add,
    coeff_smul, smul_eq_mul, hder]
  push_cast
  ring

theorem laterDeepLowerOpenDoubleRightSeven_equalityRowZero_inconsistent68
    (a b c d0 e0 zeta : k) (ha : a ≠ 0) (hb : b ≠ 0)
    (hbranch :
      (c = 0 ∧ zeta * a = (-32 / 81 : k) * b ^ 3 ∧
          e0 = (7 / 27 : k) * b ^ 2) ∨
        (c ≠ 0 ∧ c ^ 2 = a * b ^ 2 ∧
          zeta * a = (256 / 81 : k) * b ^ 3 ∧
          b * e0 + c * d0 = (-29 / 27 : k) * b ^ 3))
    (hrow : (4 : k) * (-a * b * e0 - a * c * d0 + b * c ^ 2) +
      (3 : k) * zeta * a ^ 2 = 0) : False := by
  rcases hbranch with hzero | htangent
  · have ht := hrow
    rw [hzero.1, hzero.2.2] at ht
    have hprod : (-20 / 9 : k) * a * b ^ 3 = 0 := by
      linear_combination ht - (3 * a) * hzero.2.1
    exact (mul_ne_zero (mul_ne_zero (by norm_num) ha) (pow_ne_zero 3 hb))
      hprod
  · have ht := hrow
    have hsum := htangent.2.2.2
    have hprod : (160 / 9 : k) * a * b ^ 3 = 0 := by
      linear_combination ht +
        (4 * a) * hsum +
        (-4 * b) * htangent.2.1 -
        (3 * a) * htangent.2.2.1
    exact (mul_ne_zero (mul_ne_zero (by norm_num) ha) (pow_ne_zero 3 hb))
      hprod

set_option maxHeartbeats 30000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleStrictHighRightSevenWall_inconsistent68
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
      3 * g = 7 * n) : False := by
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
  let d0 := d.coeff (5 * n - 2 * g)
  let e0 := ee.coeff (6 * n - 2 * g)
  change 3 * n < 2 * g ∧ 2 * g < 5 * n at hopen
  change 2 * g ≤ h at hdouble
  change 3 * g = 7 * n at hwall
  have prior :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleStrictHighRightSevenWall_I4Residual68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hdouble)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
  change h = 2 * g ∧ delta = 0 ∧ b ≠ 0 ∧
      ((c = 0 ∧ zeta * a = (-32 / 81 : k) * b ^ 3 ∧
          e0 = (7 / 27 : k) * b ^ 2) ∨
        (c ≠ 0 ∧ c ^ 2 = a * b ^ 2 ∧
          zeta * a = (256 / 81 : k) * b ^ 3 ∧
          b * e0 + c * d0 = (-29 / 27 : k) * b ^ 3)) at prior
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
  have hdbase : d.natDegree < 5 * n := drops.2.2.2.2.1.trans (by omega)
  have hebase : ee.natDegree < 6 * n := drops.2.2.2.2.2.1.trans (by omega)
  have bounds := secondaryResidualGap68_degreeBounds n d ee hdbase hebase
  have hd2 : d.natDegree ≤ 5 * n - 2 * g := by
    have ht := bounds.1
    change d.natDegree ≤ 5 * n - h at ht
    rwa [prior.1] at ht
  have he2 : ee.natDegree ≤ 6 * n - 2 * g := by
    have ht := bounds.2
    change ee.natDegree ≤ 6 * n - h at ht
    rwa [prior.1] at ht
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec : Ee = (1 / 27 : k) • Ae ^ 3 +
      (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using
      cubicEDefectPolynomial68_eq_cubicCoordinates Ae Ce Ee
  have hDrec : De = Dtr := by
    simpa only [Dtr, d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
  have h0e : lowerRowZeroPolynomial68
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) De Ee =
      C terminal * (60 * (X ^ 59 : k[X])) := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_lowerRowZeroPolynomial68_of_system
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
  rw [hCrec, hDrec, hErec] at h0e
  have hsplit0 := cubicRowZeroPolynomial68_residualSplit
    l alpha beta gamma delta epsilon zeta eta Ae Be ce d ee
  have hsum0 :
      secondaryResidualRowZeroPolynomial68 Ae Be ce d ee +
        cubicLoadRowZeroPolynomial68 l alpha beta gamma delta epsilon zeta eta
          Ae Be ce Dtr ee = C terminal * (60 * (X ^ 59 : k[X])) := by
    simpa only [Dtr] using hsplit0.symm.trans h0e
  have hidx : 6 * n - 1 ≠ 59 := by omega
  have hterm :
      (C terminal * (60 * (X ^ 59 : k[X]))).coeff (6 * n - 1) = 0 := by
    simp [coeff_C_mul, coeff_X_pow, hidx]
  have hcoeff := congrArg (fun p : k[X] => p.coeff (6 * n - 1)) hsum0
  rw [drops.1, drops.2.1, prior.2.1, coeff_add, hterm,
    secondaryResidualRowZeroPolynomial68_coeff_sixRadius_of_doubleRightSevenEquality68
      Ae Be ce d ee n g hn hg hwall hA secondary.2.1 secondary.2.2.1 hd2 he2,
    cubicLoadRowZeroPolynomial68_coeff_sixRadius_of_doubleRightSevenEquality68
      alpha gamma epsilon zeta eta Ae Be ce d ee n g hn hg hwall hA
        secondary.2.1 secondary.2.2.1 hd2 he2] at hcoeff
  have hrow : (4 : k) * (-a * b * e0 - a * c * d0 + b * c ^ 2) +
      (3 : k) * zeta * a ^ 2 = 0 := by
    have hfactor : (2 / 27 : k) * (n : k) * a ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr hn.ne')) ha
    have hfactored : ((2 / 27 : k) * (n : k) * a) *
        ((4 : k) * (-a * b * e0 - a * c * d0 + b * c ^ 2) +
          (3 : k) * zeta * a ^ 2) = 0 := by
      simpa only [a, b, c, d0, e0] using (by
        linear_combination hcoeff)
    exact (mul_eq_zero.mp hfactored).resolve_left hfactor
  exact laterDeepLowerOpenDoubleRightSeven_equalityRowZero_inconsistent68
    a b c d0 e0 zeta ha prior.2.2.1 prior.2.2.2 hrow

#print axioms secondaryResidualRowZeroPolynomial68_coeff_sixRadius_of_doubleRightSevenEquality68
#print axioms cubicLoadRowZeroPolynomial68_deltaZero_split_zeta68
#print axioms cubicLoadRowZeroPolynomial68_coeff_sixRadius_of_doubleRightSevenEquality68
#print axioms laterDeepLowerOpenDoubleRightSeven_equalityRowZero_inconsistent68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleStrictHighRightSevenWall_inconsistent68

end LaterDeepLowerOpenDoubleSevenWallRowZeroClosure68

end Max11DegreeRoutes
