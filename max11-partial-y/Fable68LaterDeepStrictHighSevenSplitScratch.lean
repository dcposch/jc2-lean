import Fable68LaterDeepStrictHighScratch

/-! # The `3g` versus `7n` split on the double strict-high chamber

On the double child `2g ≤ h` of the strict-open window `3n < 2g < 5n`,
the strict-high face `5n < 3g` forces `delta = 0`
(`Fable68LaterDeepStrictHighScratch`).  The delta-free reduced row two
then carries three scalar faces: the fixed `B,c` cubic face at
`11n - 3g - 1`, the moving `d*e` face at `11n - 2h - 1`, and the `zeta`
face at `4n - 1`.  On the double child the residual pair is pinned by
`2h ≥ 4g > 3g`, so the `d*e` face always sits strictly below the fixed
cubic face, and the middle-child seven-wall tail bound transfers with
`7n ≤ 2h` automatic from `4g ≥ 3g + g`.  The split of `3g` against `7n`
is honest and exact:

* below seven (`3g < 7n`) the fixed cubic face is the unique top face,
  so its raw coefficient dies; it factors as
  `b * (a*b^2 - 9*c4^2) = 0`, an exact balance whose zero branches are
  preserved rather than a contradiction (the middle-child refutation
  needed the ordinary-chamber discriminant, unavailable here);
* on the wall (`3g = 7n`) the cubic face ties the `zeta` face at
  `4n - 1` and the packet records their exact sum;
* above seven (`7n < 3g`) every other face drops below `4n - 1`, the
  `zeta` primitive is isolated, and `zeta = 0`.

No closure is claimed on any branch: the below-seven and wall branches
end in exact relations, and only the above-seven branch forces a scalar.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerOpenDoubleStrictHighSevenSplit68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 24000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## The raw cubic face of the fixed core

The middle-child coefficient lemma
`fiveRadiusRowTwoFixedCore68_coeff_of_laterDeepLowerOpen` presupposes the
ordinary-chamber discriminant relation, which does not transfer to the
double child.  The raw face coefficient needs nothing beyond the open
window and factors through `b * (a*b^2 - 9*c4^2)`. -/

set_option maxHeartbeats 6000000 in
theorem fiveRadiusRowTwoFixedCore68_coeff_cubicFace_of_laterDeepLowerOpen
    (A B c : k[X]) (n g : ℕ) (hn : 0 < n) (hg : 0 < g)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g) :
    (fiveRadiusRowTwoFixedCore68 A B c).coeff (11 * n - 3 * g - 1) =
      (8 / 81 : k) * ((11 * n - 3 * g : ℕ) : k) * B.coeff (3 * n - g) *
        (A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 -
          (9 : k) * c.coeff (4 * n - g) ^ 2) := by
  set idx := 11 * n - 3 * g - 1
  change (fiveRadiusRowTwoFixedCore68 A B c).coeff idx = _
  have hB2deg : (B ^ 2).natDegree ≤ 6 * n - 2 * g := by
    compute_degree
    omega
  have hB2 : (B ^ 2).coeff (6 * n - 2 * g) =
      B.coeff (3 * n - g) ^ 2 := by
    have h := coeff_pow_at_bound68 B (3 * n - g) 2 hB
    have hi : 2 * (3 * n - g) = 6 * n - 2 * g := by omega
    simpa only [hi] using h
  have hAB := coeff_mul_mul_derivative_at_bounds68 A (B ^ 2) B
    (2 * n) (6 * n - 2 * g) (3 * n - g) (by omega) hA hB2deg hB
  have hiAB : 2 * n + (6 * n - 2 * g) + (3 * n - g) - 1 = idx := by
    dsimp [idx]
    omega
  rw [hiAB, hB2] at hAB
  have hABpow : (A * B ^ 2 * derivative B).coeff idx =
      A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 *
        ((3 * n - g : ℕ) : k) := by
    rw [hAB]
    ring
  have hB3deg : (B ^ 3).natDegree ≤ 9 * n - 3 * g := by
    compute_degree
    omega
  have hB3 : (B ^ 3).coeff (9 * n - 3 * g) =
      B.coeff (3 * n - g) ^ 3 := by
    have h := coeff_pow_at_bound68 B (3 * n - g) 3 hB
    have hi : 3 * (3 * n - g) = 9 * n - 3 * g := by omega
    simpa only [hi] using h
  have hA3 := coeff_mul_derivative_at_bounds68 (B ^ 3) A
    (9 * n - 3 * g) (2 * n) (by omega) hB3deg hA
  have hiA3 : (9 * n - 3 * g) + 2 * n - 1 = idx := by
    dsimp [idx]
    omega
  rw [hiA3, hB3] at hA3
  have hA3' : (derivative A * B ^ 3).coeff idx =
      A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 *
        ((2 * n : ℕ) : k) := by
    rw [show (derivative A * B ^ 3).coeff idx =
        (B ^ 3 * derivative A).coeff idx by
      congr 1
      ring]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hA3
  have hc2deg : (c ^ 2).natDegree ≤ 8 * n - 2 * g := by
    compute_degree
    omega
  have hc2 : (c ^ 2).coeff (8 * n - 2 * g) =
      c.coeff (4 * n - g) ^ 2 := by
    have h := coeff_pow_at_bound68 c (4 * n - g) 2 hc
    have hi : 2 * (4 * n - g) = 8 * n - 2 * g := by omega
    simpa only [hi] using h
  have hBccoeff := coeff_mul_at_bounds68 B (c ^ 2)
    (3 * n - g) (8 * n - 2 * g) hB hc2deg
  have hiBc : (3 * n - g) + (8 * n - 2 * g) = 11 * n - 3 * g := by omega
  rw [hiBc, hc2] at hBccoeff
  have hBc := coeff_derivative_at_bound68 (B * c ^ 2)
    (11 * n - 3 * g) (by omega)
  rw [hBccoeff] at hBc
  have hcast3 : (((3 * n - g : ℕ) : k)) =
      (3 : k) * (n : k) - (g : k) := by
    rw [Nat.cast_sub (by omega : g ≤ 3 * n)]
    push_cast
    rfl
  have hcast2 : (((2 * n : ℕ) : k)) = (2 : k) * (n : k) := by
    push_cast
    rfl
  have hcast11 : (((11 * n - 3 * g : ℕ) : k)) =
      (11 : k) * (n : k) - (3 : k) * (g : k) := by
    rw [Nat.cast_sub (by omega : 3 * g ≤ 11 * n)]
    push_cast
    rfl
  simp only [fiveRadiusRowTwoFixedCore68, coeff_smul, coeff_add,
    smul_eq_mul, hABpow, hA3', hBc, hcast3, hcast2, hcast11, idx]
  ring

/-! ## Below seven: the cubic face is alone and dies exactly

For `3g < 7n` the fixed cubic face at `11n - 3g - 1` sits strictly above
the `d*e` face (`3g < 2h` from `2h ≥ 4g`), the tail, and the `zeta` face
at `4n - 1`.  The vanishing row therefore kills the raw face coefficient
and, after removing the nonzero scalar `(8/81) * (11n - 3g)`, leaves the
exact balance `b * (a*b^2 - 9*c4^2) = 0` with both zero branches
preserved.  No contradiction is claimed: the middle-child refutation
used the ordinary discriminant and sharp residual coefficients, neither
of which is available on the double child. -/

set_option maxHeartbeats 5000000 in
theorem fiveRadiusReducedRowTwo_doubleBelowSeven_cubicFace_relation68
    (gamma epsilon zeta i4 : k) (A B c d e : k[X])
    (n g h : ℕ) (hn : 0 < n) (hg : 0 < g) (hgh : g < h)
    (hdouble : 2 * g ≤ h)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hbelow : 3 * g < 7 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hrow : fiveRadiusReducedRowTwoPolynomial68
      gamma epsilon zeta i4 A B c d e = 0) :
    B.coeff (3 * n - g) *
      (A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 -
        (9 : k) * c.coeff (4 * n - g) ^ 2) = 0 := by
  have hfixed := fiveRadiusRowTwoFixedCore68_coeff_cubicFace_of_laterDeepLowerOpen
    A B c n g hn hg hopen hA hB hc
  have hde : ((8 / 3 : k) • derivative (d * e)).natDegree <
      11 * n - 3 * g - 1 := by
    have hp : (d * e).natDegree ≤
        (5 * n - h) + (6 * n - h) := by
      compute_degree
      omega
    have hder := natDegree_derivative_le (d * e)
    apply (natDegree_smul_le _ _).trans_lt
    omega
  have htail : (fiveRadiusRowTwoTail68 gamma epsilon i4 A B c d).natDegree <
      11 * n - 3 * g - 1 := by
    have hBd : (derivative (B ^ 2 * d)).natDegree < 11 * n - 3 * g - 1 := by
      have hp : (B ^ 2 * d).natDegree ≤
          (6 * n - 2 * g) + (5 * n - h) := by
        compute_degree
        omega
      have hder := natDegree_derivative_le (B ^ 2 * d)
      omega
    have hAd : (derivative A).natDegree < 11 * n - 3 * g - 1 := by
      compute_degree
      omega
    have hBc : (derivative (B * c)).natDegree < 11 * n - 3 * g - 1 := by
      have hp : (B * c).natDegree ≤
          (3 * n - g) + (4 * n - g) := by
        compute_degree
        omega
      have hder := natDegree_derivative_le (B * c)
      omega
    have hdd : (derivative d).natDegree < 11 * n - 3 * g - 1 := by
      compute_degree
      omega
    have h1 := deepGap_natDegree_smul_lt68 (-8 / 9 : k) hBd
    have h2 := deepGap_natDegree_smul_lt68 (1 / 6 * i4 : k) hAd
    have h3 := deepGap_natDegree_smul_lt68 (4 / 3 * gamma : k) hBc
    have h4 := deepGap_natDegree_smul_lt68 (2 * epsilon : k) hdd
    simp only [fiveRadiusRowTwoTail68]
    exact deepGap_natDegree_add_lt
      (deepGap_natDegree_sub_lt (deepGap_natDegree_sub_lt h1 h2) h3) h4
  have hz : (zeta • derivative ((1 / 4 : k) • A ^ 2 + c)).natDegree <
      11 * n - 3 * g - 1 := by
    have hp : ((1 / 4 : k) • A ^ 2 + c).natDegree ≤ 4 * n := by
      compute_degree
      omega
    have hder := natDegree_derivative_le ((1 / 4 : k) • A ^ 2 + c)
    apply (natDegree_smul_le _ _).trans_lt
    omega
  have hzrow := congrArg
    (fun p : k[X] => p.coeff (11 * n - 3 * g - 1)) hrow
  rw [fiveRadiusReducedRowTwoPolynomial68_faceSplit,
    coeff_add, coeff_add, coeff_add,
    coeff_eq_zero_of_natDegree_lt hde,
    coeff_eq_zero_of_natDegree_lt htail,
    coeff_eq_zero_of_natDegree_lt hz,
    coeff_zero, hfixed] at hzrow
  simp only [add_zero] at hzrow
  have hkey : ((8 / 81 : k) * ((11 * n - 3 * g : ℕ) : k)) *
      (B.coeff (3 * n - g) *
        (A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 -
          (9 : k) * c.coeff (4 * n - g) ^ 2)) = 0 := by
    linear_combination hzrow
  exact (mul_eq_zero.mp hkey).resolve_left
    (mul_ne_zero (by norm_num)
      (Nat.cast_ne_zero.mpr (by omega : 11 * n - 3 * g ≠ 0)))

/-! ## The exact seven wall: cubic face against the `zeta` face

For `3g = 7n` the fixed cubic face lands exactly on `4n - 1`, where the
`zeta` primitive lives; `2h > 7n` is automatic from `2h ≥ 4g = 7n + g`,
so the `d*e` face and the tail drop out and the wall packet is the exact
sum of the raw cubic face and the `zeta` load. -/

set_option maxHeartbeats 6000000 in
theorem fiveRadiusReducedRowTwo_coeff_doubleRightSevenWall68
    (gamma epsilon zeta i4 : k) (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hdouble : 2 * g ≤ h)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hwall : 3 * g = 7 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (fiveRadiusReducedRowTwoPolynomial68 gamma epsilon zeta i4 A B c d e).coeff
        (4 * n - 1) =
      (8 / 81 : k) * ((4 * n : ℕ) : k) * B.coeff (3 * n - g) *
          (A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 -
            (9 : k) * c.coeff (4 * n - g) ^ 2) +
        zeta * (n : k) * A.coeff (2 * n) ^ 2 := by
  have hfixed := fiveRadiusRowTwoFixedCore68_coeff_cubicFace_of_laterDeepLowerOpen
    A B c n g hn hg hopen hA hB hc
  have hfixedi : 11 * n - 3 * g - 1 = 4 * n - 1 := by omega
  have hfixedN : 11 * n - 3 * g = 4 * n := by omega
  rw [hfixedi, hfixedN] at hfixed
  have hdeprod : (d * e).natDegree ≤
      (5 * n - h) + (6 * n - h) := by
    compute_degree
    omega
  have hdeder := natDegree_derivative_le (d * e)
  have hde : ((8 / 3 : k) • derivative (d * e)).natDegree <
      4 * n - 1 := by
    apply (natDegree_smul_le _ _).trans_lt
    omega
  have hseven : 7 * n ≤ 2 * h ∧ 7 * n ≤ 3 * g := by omega
  have htail := fiveRadiusRowTwoTail68_degree_lt_fourRadius_of_highSeven
    gamma epsilon i4 A B c d n g h hn hg hgh hopen hseven hA hB hc hd
  have hz := derivative_quarterSquare_add_coeff_middleSevenSum68
    A c n g hn hg hA hc
  rw [fiveRadiusReducedRowTwoPolynomial68_faceSplit, coeff_add, coeff_add,
    coeff_add, hfixed, coeff_eq_zero_of_natDegree_lt hde,
    coeff_eq_zero_of_natDegree_lt htail,
    coeff_smul, smul_eq_mul, hz]
  ring

theorem fiveRadiusReducedRowTwo_doubleRightSevenWall_relation68
    (gamma epsilon zeta i4 : k) (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hdouble : 2 * g ≤ h)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hwall : 3 * g = 7 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hrow : fiveRadiusReducedRowTwoPolynomial68
      gamma epsilon zeta i4 A B c d e = 0) :
    (8 / 81 : k) * ((4 * n : ℕ) : k) * B.coeff (3 * n - g) *
        (A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 -
          (9 : k) * c.coeff (4 * n - g) ^ 2) +
      zeta * (n : k) * A.coeff (2 * n) ^ 2 = 0 := by
  have hz := congrArg (fun p : k[X] => p.coeff (4 * n - 1)) hrow
  rw [fiveRadiusReducedRowTwo_coeff_doubleRightSevenWall68
    gamma epsilon zeta i4 A B c d e n g h hn hg hgh hdouble hopen hwall
    hA hB hc hd he, coeff_zero] at hz
  exact hz

/-! ## Above seven: the `zeta` face is isolated

For `7n < 3g` the fixed cubic face drops strictly below `4n - 1`, the
`d*e` face follows from `2h ≥ 4g > 7n`, and the middle-child tail bound
applies with both seven inequalities automatic.  The `zeta` primitive is
then alone on its face and vanishes outright — this is the direct double
analogue of `fiveRadiusReducedRowTwo_forces_zeta_of_highOrdinary68`,
with the `h < 2g` hypothesis replaced by the transfer `2h ≥ 4g`. -/

set_option maxHeartbeats 5000000 in
theorem fiveRadiusReducedRowTwo_forces_zeta_of_doubleStrictHighAboveSeven68
    (gamma epsilon zeta i4 : k) (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hdouble : 2 * g ≤ h)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (habove : 7 * n < 3 * g)
    (ha : A.coeff (2 * n) ≠ 0)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hrow : fiveRadiusReducedRowTwoPolynomial68
      gamma epsilon zeta i4 A B c d e = 0) : zeta = 0 := by
  have hfixedle := fiveRadiusRowTwoFixedCore68_degree_le_of_laterDeepLowerOpen
    A B c n g hn hg hopen hA hB hc
  have hfixed : (fiveRadiusRowTwoFixedCore68 A B c).natDegree <
      4 * n - 1 := by
    omega
  have hdeprod : (d * e).natDegree ≤
      (5 * n - h) + (6 * n - h) := by
    compute_degree
    omega
  have hdeder := natDegree_derivative_le (d * e)
  have hde : ((8 / 3 : k) • derivative (d * e)).natDegree <
      4 * n - 1 := by
    apply (natDegree_smul_le _ _).trans_lt
    omega
  have hseven : 7 * n ≤ 2 * h ∧ 7 * n ≤ 3 * g := by omega
  have htail := fiveRadiusRowTwoTail68_degree_lt_fourRadius_of_highSeven
    gamma epsilon i4 A B c d n g h hn hg hgh hopen hseven hA hB hc hd
  have hcoeff := congrArg (fun p : k[X] => p.coeff (4 * n - 1)) hrow
  rw [fiveRadiusReducedRowTwoPolynomial68_faceSplit,
    coeff_add, coeff_add, coeff_add,
    coeff_eq_zero_of_natDegree_lt hfixed,
    coeff_eq_zero_of_natDegree_lt hde,
    coeff_eq_zero_of_natDegree_lt htail,
    coeff_smul, smul_eq_mul,
    derivative_quarterSquare_add_coeff_middleSevenSum68
      A c n g hn hg hA hc,
    coeff_zero] at hcoeff
  simp only [zero_add] at hcoeff
  exact (mul_eq_zero.mp hcoeff).resolve_right
    (mul_ne_zero (Nat.cast_ne_zero.mpr hn.ne') (pow_ne_zero 2 ha))

/-! ## Source-facing seven split -/

set_option maxHeartbeats 26000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleStrictHighSevenSplit68
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
    (habove :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      5 * n < 3 * g) :
    let n := weightedRadius68 A B C0 D E
    let Ae := expand k 60 A
    let Be := expand k 60 B
    let Ce := expand k 60 C0
    let ce := cubicCDefectPolynomial68 Ae Ce
    let De := expand k 60 D
    let Ee := expand k 60 E
    let ee := cubicEDefectPolynomial68 Ae Ce Ee
    let g := cubicDefectGap68 n Be ce De ee
    delta = 0 ∧
      ((3 * g < 7 * n ∧
          Be.coeff (3 * n - g) *
            (Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 2 -
              (9 : k) * ce.coeff (4 * n - g) ^ 2) = 0) ∨
        (3 * g = 7 * n ∧
          (8 / 81 : k) * ((4 * n : ℕ) : k) * Be.coeff (3 * n - g) *
              (Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 2 -
                (9 : k) * ce.coeff (4 * n - g) ^ 2) +
            zeta * (n : k) * Ae.coeff (2 * n) ^ 2 = 0) ∨
        (7 * n < 3 * g ∧ zeta = 0)) := by
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
  change 3 * n < 2 * g ∧ 2 * g < 5 * n at hopen
  change 2 * g ≤ h at hdouble
  change 5 * n < 3 * g at habove
  have hdelta :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleStrictHigh_forces_delta68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen) (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hdouble) (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using habove)
  have drops :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenResidualDrops68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
  change l = 0 ∧ beta = 0 ∧ ee.coeff (6 * n - g) = 0 ∧
      Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
        3 * De.coeff (5 * n - g) ∧
      d.natDegree < 5 * n - g ∧ ee.natDegree < 6 * n - g ∧ g < h
    at drops
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
  have ha : Ae.coeff (2 * n) ≠ 0 := by
    simpa only [n, Ae] using core.2.2.2.2.2
  have hA : Ae.natDegree ≤ 2 * n := by
    have hAe : Ae.natDegree = 2 * n := by
      simpa only [n, Ae, Be, Ce, De, Ee] using drop.1
    omega
  have hdbase : d.natDegree < 5 * n := drops.2.2.2.2.1.trans (by omega)
  have hebase : ee.natDegree < 6 * n := drops.2.2.2.2.2.1.trans (by omega)
  have bounds := secondaryResidualGap68_degreeBounds n d ee hdbase hebase
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec : Ee = (1 / 27 : k) • Ae ^ 3 +
      (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using
      cubicEDefectPolynomial68_eq_cubicCoordinates Ae Ce Ee
  have hDrec : De = (1 / 3 : k) • (Ae * Be) + d := by
    simpa only [d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
  obtain ⟨i4, hi4⟩ := hsys.firstFour
  have hi4c : cubicFirstIntegralFourPolynomial68
      0 0 gamma 0 epsilon zeta Ae Be ce
        ((1 / 3 : k) • (Ae * Be) + d) ee = C i4 := by
    have hi4e : firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
        Ae Be Ce De Ee = C i4 := by
      simpa only [Ae, Be, Ce, De, Ee] using
        expand_firstIntegralFourPolynomial68_of_eq
          l beta gamma delta epsilon zeta i4 A B C0 D E hi4
    rw [hCrec, hErec, firstIntegralFourPolynomial68_cubicCoordinates,
      hDrec, drops.1, drops.2.1, hdelta] at hi4e
    exact hi4e
  have hrowTwo : lowerRowTwoPolynomial68
      (integratedSPolynomial68 l alpha beta delta Ae Be Ce De)
      (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) Be Ce De Ee = 0 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_lowerRowTwoPolynomial68_of_system
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
  rw [hCrec, hDrec, hErec] at hrowTwo
  have hrow := polynomialSecondaryResidualRowTwo68
    l alpha beta gamma delta epsilon zeta eta Ae Be ce d ee hrowTwo
  rw [drops.1, drops.2.1, hdelta] at hrow
  have hred : fiveRadiusReducedRowTwoPolynomial68
      gamma epsilon zeta i4 Ae Be ce d ee = 0 := by
    have ht := laterDeepFiveSumReducedRowTwoPolynomial68_eq_zero
      alpha gamma 0 epsilon zeta eta i4 Ae Be ce d ee hi4c hrow
    simpa only [laterDeepFiveSumReducedRowTwoPolynomial68, zero_smul, add_zero]
      using ht
  rcases lt_trichotomy (3 * g) (7 * n) with hbelow | hwall | habove7
  · exact ⟨hdelta, Or.inl ⟨hbelow,
      fiveRadiusReducedRowTwo_doubleBelowSeven_cubicFace_relation68
        gamma epsilon zeta i4 Ae Be ce d ee n g h hn hg
        drops.2.2.2.2.2.2 hdouble hopen hbelow hA secondary.2.1
        secondary.2.2.1 bounds.1 bounds.2 hred⟩⟩
  · exact ⟨hdelta, Or.inr (Or.inl ⟨hwall,
      fiveRadiusReducedRowTwo_doubleRightSevenWall_relation68
        gamma epsilon zeta i4 Ae Be ce d ee n g h hn hg
        drops.2.2.2.2.2.2 hdouble hopen hwall hA secondary.2.1
        secondary.2.2.1 bounds.1 bounds.2 hred⟩)⟩
  · exact ⟨hdelta, Or.inr (Or.inr ⟨habove7,
      fiveRadiusReducedRowTwo_forces_zeta_of_doubleStrictHighAboveSeven68
        gamma epsilon zeta i4 Ae Be ce d ee n g h hn hg
        drops.2.2.2.2.2.2 hdouble hopen habove7 ha hA secondary.2.1
        secondary.2.2.1 bounds.1 bounds.2 hred⟩)⟩

/-! ## Per-branch source corollaries -/

set_option maxHeartbeats 20000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleStrictHighBelowSeven_cubicFace68
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
    (habove :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      5 * n < 3 * g)
    (hbelow :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      3 * g < 7 * n) :
    let n := weightedRadius68 A B C0 D E
    let Ae := expand k 60 A
    let Be := expand k 60 B
    let Ce := expand k 60 C0
    let ce := cubicCDefectPolynomial68 Ae Ce
    let De := expand k 60 D
    let Ee := expand k 60 E
    let ee := cubicEDefectPolynomial68 Ae Ce Ee
    let g := cubicDefectGap68 n Be ce De ee
    delta = 0 ∧
      Be.coeff (3 * n - g) *
        (Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 2 -
          (9 : k) * ce.coeff (4 * n - g) ^ 2) = 0 := by
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
  change 3 * n < 2 * g ∧ 2 * g < 5 * n at hopen
  change 2 * g ≤ h at hdouble
  change 5 * n < 3 * g at habove
  change 3 * g < 7 * n at hbelow
  have hsel :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleStrictHighSevenSplit68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen) (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hdouble) (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using habove)
  change delta = 0 ∧
      ((3 * g < 7 * n ∧
          Be.coeff (3 * n - g) *
            (Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 2 -
              (9 : k) * ce.coeff (4 * n - g) ^ 2) = 0) ∨
        (3 * g = 7 * n ∧
          (8 / 81 : k) * ((4 * n : ℕ) : k) * Be.coeff (3 * n - g) *
              (Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 2 -
                (9 : k) * ce.coeff (4 * n - g) ^ 2) +
            zeta * (n : k) * Ae.coeff (2 * n) ^ 2 = 0) ∨
        (7 * n < 3 * g ∧ zeta = 0)) at hsel
  refine ⟨hsel.1, ?_⟩
  rcases hsel.2 with ⟨_, hrel⟩ | ⟨hwall, _⟩ | ⟨hgt, _⟩
  · exact hrel
  · exact absurd hwall (by omega)
  · exact absurd hgt (by omega)

set_option maxHeartbeats 20000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleStrictHighRightSevenWall_relation68
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
    delta = 0 ∧
      (8 / 81 : k) * ((4 * n : ℕ) : k) * Be.coeff (3 * n - g) *
          (Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 2 -
            (9 : k) * ce.coeff (4 * n - g) ^ 2) +
        zeta * (n : k) * Ae.coeff (2 * n) ^ 2 = 0 := by
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
  change 3 * n < 2 * g ∧ 2 * g < 5 * n at hopen
  change 2 * g ≤ h at hdouble
  change 3 * g = 7 * n at hwall
  have core := maximalExpandedIntegratedPolynomialLowerSystem_cubicCore68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have hn : 0 < n := by simpa only [n] using core.1
  have habove : 5 * n < 3 * g := by omega
  have hsel :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleStrictHighSevenSplit68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen) (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hdouble) (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using habove)
  change delta = 0 ∧
      ((3 * g < 7 * n ∧
          Be.coeff (3 * n - g) *
            (Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 2 -
              (9 : k) * ce.coeff (4 * n - g) ^ 2) = 0) ∨
        (3 * g = 7 * n ∧
          (8 / 81 : k) * ((4 * n : ℕ) : k) * Be.coeff (3 * n - g) *
              (Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 2 -
                (9 : k) * ce.coeff (4 * n - g) ^ 2) +
            zeta * (n : k) * Ae.coeff (2 * n) ^ 2 = 0) ∨
        (7 * n < 3 * g ∧ zeta = 0)) at hsel
  refine ⟨hsel.1, ?_⟩
  rcases hsel.2 with ⟨hlt, _⟩ | ⟨_, hrel⟩ | ⟨hgt, _⟩
  · exact absurd hlt (by omega)
  · exact hrel
  · exact absurd hgt (by omega)

set_option maxHeartbeats 20000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleStrictHighAboveSeven_forces_zeta68
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
    (habove :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      7 * n < 3 * g) : delta = 0 ∧ zeta = 0 := by
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
  change 3 * n < 2 * g ∧ 2 * g < 5 * n at hopen
  change 2 * g ≤ h at hdouble
  change 7 * n < 3 * g at habove
  have habove5 : 5 * n < 3 * g := by omega
  have hsel :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleStrictHighSevenSplit68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen) (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hdouble) (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using habove5)
  change delta = 0 ∧
      ((3 * g < 7 * n ∧
          Be.coeff (3 * n - g) *
            (Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 2 -
              (9 : k) * ce.coeff (4 * n - g) ^ 2) = 0) ∨
        (3 * g = 7 * n ∧
          (8 / 81 : k) * ((4 * n : ℕ) : k) * Be.coeff (3 * n - g) *
              (Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 2 -
                (9 : k) * ce.coeff (4 * n - g) ^ 2) +
            zeta * (n : k) * Ae.coeff (2 * n) ^ 2 = 0) ∨
        (7 * n < 3 * g ∧ zeta = 0)) at hsel
  refine ⟨hsel.1, ?_⟩
  rcases hsel.2 with ⟨hlt, _⟩ | ⟨hweq, _⟩ | ⟨_, hzeta⟩
  · exact absurd hlt (by omega)
  · exact absurd hweq (by omega)
  · exact hzeta

#print axioms fiveRadiusRowTwoFixedCore68_coeff_cubicFace_of_laterDeepLowerOpen
#print axioms fiveRadiusReducedRowTwo_doubleBelowSeven_cubicFace_relation68
#print axioms fiveRadiusReducedRowTwo_coeff_doubleRightSevenWall68
#print axioms fiveRadiusReducedRowTwo_doubleRightSevenWall_relation68
#print axioms fiveRadiusReducedRowTwo_forces_zeta_of_doubleStrictHighAboveSeven68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleStrictHighSevenSplit68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleStrictHighBelowSeven_cubicFace68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleStrictHighRightSevenWall_relation68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleStrictHighAboveSeven_forces_zeta68

end LaterDeepLowerOpenDoubleStrictHighSevenSplit68

end Max11DegreeRoutes
