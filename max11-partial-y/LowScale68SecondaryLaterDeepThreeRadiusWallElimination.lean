import LowScale68SecondaryLaterDeepThreeRadiusWallNext

/-! # Elimination on the later-deep wall `2g = 3n`

The mixed I4, row-two, and row-zero equations already force the beta load to
vanish.  The certificate is polynomial: after using `2G = 3N`,

`(24/35) a N^4 I4 + (24/35) N^3 F2 + (512/315) N^4 F0`

is `beta * a^4 * N^4`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepThreeRadiusWallElimination68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 4000000

theorem laterDeepLowerThreeRadiusWall_beta_zero68
    (N G a b c d e beta : k) (hN : N ≠ 0) (ha : a ≠ 0)
    (hwall : 2 * G = 3 * N)
    (hfour :
      (-8 / 9 : k) * firstSecondaryFour68 a b c d e +
        (5 / 72 : k) * beta * a ^ 3 = 0)
    (htwo :
      (8 / 27 : k) * firstSecondaryTwo68 N G a b c d e +
        (5 / 18 : k) * N * beta * a ^ 4 = 0)
    (hzero :
      firstSecondaryZero68 a b c d e +
        (15 / 32 : k) * beta * a ^ 4 = 0) :
    beta = 0 := by
  have hG : G = (3 / 2 : k) * N := by
    linear_combination (1 / 2 : k) * hwall
  rw [hG] at htwo
  simp only [firstSecondaryFour68, firstSecondaryTwo68,
    firstSecondaryZero68] at hfour htwo hzero
  have hproduct : beta * a ^ 4 * N ^ 4 = 0 := by
    linear_combination
      (24 / 35 : k) * a * N ^ 4 * hfour +
      (24 / 35 : k) * N ^ 3 * htwo +
      (512 / 315 : k) * N ^ 4 * hzero
  rcases mul_eq_zero.mp hproduct with hbetaA | hN4
  · exact (mul_eq_zero.mp hbetaA).resolve_right (pow_ne_zero 4 ha)
  · exact False.elim (pow_ne_zero 4 hN hN4)

theorem laterDeepLowerThreeRadiusWall_classify68
    (N G a b c d e beta : k) (hN : N ≠ 0) (ha : a ≠ 0)
    (hwall : 2 * G = 3 * N)
    (hthree : firstSecondaryThree68 a b c d e = 0)
    (hone : firstSecondaryOne68 N G a b c d e = 0)
    (hfour :
      (-8 / 9 : k) * firstSecondaryFour68 a b c d e +
        (5 / 72 : k) * beta * a ^ 3 = 0)
    (htwo :
      (8 / 27 : k) * firstSecondaryTwo68 N G a b c d e +
        (5 / 18 : k) * N * beta * a ^ 4 = 0)
    (hzero :
      firstSecondaryZero68 a b c d e +
        (15 / 32 : k) * beta * a ^ 4 = 0) :
    beta = 0 ∧ e = 0 ∧ a * b = 3 * d := by
  have hbeta := laterDeepLowerThreeRadiusWall_beta_zero68
    N G a b c d e beta hN ha hwall hfour htwo hzero
  have hfour0 : firstSecondaryFour68 a b c d e = 0 := by
    rw [hbeta] at hfour
    norm_num at hfour ⊢
    exact hfour
  have htwo0 : firstSecondaryTwo68 N G a b c d e = 0 := by
    rw [hbeta] at htwo
    norm_num at htwo ⊢
    exact htwo
  have hzero0 : firstSecondaryZero68 a b c d e = 0 := by
    rw [hbeta] at hzero
    norm_num at hzero ⊢
    exact hzero
  have hG : G = (3 / 2 : k) * N := by
    linear_combination (1 / 2 : k) * hwall
  have hgap : G - 6 * N ≠ 0 := by
    rw [hG]
    convert mul_ne_zero (by norm_num : (-9 / 2 : k) ≠ 0) hN using 1 <;>
      ring
  have hface : FirstSecondaryFace68 N G a b c d e :=
    ⟨hfour0, hthree, htwo0, hone, hzero0⟩
  exact ⟨hbeta, firstSecondaryFace68_classify N G a b c d e ha hgap hface⟩

set_option maxHeartbeats 8000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerThreeRadiusWall_classify68
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
      2 * g = 3 * n) :
    let n := weightedRadius68 A B C0 D E
    let Ae := expand k 60 A
    let Be := expand k 60 B
    let Ce := expand k 60 C0
    let ce := cubicCDefectPolynomial68 Ae Ce
    let De := expand k 60 D
    let Ee := expand k 60 E
    let ee := cubicEDefectPolynomial68 Ae Ce Ee
    let g := cubicDefectGap68 n Be ce De ee
    l = 0 ∧ beta = 0 ∧
      ee.coeff (6 * n - g) = 0 ∧
      Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
        3 * De.coeff (5 * n - g) := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  change 2 * g = 3 * n at hwall
  have hnext :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerThreeRadiusWallNext68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
  change l = 0 ∧
      firstSecondaryThree68
        (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
        (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
        (ee.coeff (6 * n - g)) = 0 ∧
      firstSecondaryOne68 (n : k) (g : k)
        (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
        (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
        (ee.coeff (6 * n - g)) = 0 ∧ _ at hnext
  obtain ⟨hl, hthree, hone, hfour, htwo, hzero⟩ := hnext
  have data :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLoadI4Data68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  change LaterDeepLoadI4Data68 l beta gamma delta epsilon zeta
    n g Ae Be ce De ee at data
  have hN : (n : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt data.hn)
  have hwallCast : (2 : k) * (g : k) = 3 * (n : k) := by
    exact_mod_cast hwall
  have hclass := laterDeepLowerThreeRadiusWall_classify68
    (n : k) (g : k) (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
    (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
    (ee.coeff (6 * n - g)) beta hN data.ha hwallCast
    hthree hone hfour htwo hzero
  exact ⟨hl, hclass⟩

#print axioms laterDeepLowerThreeRadiusWall_beta_zero68
#print axioms laterDeepLowerThreeRadiusWall_classify68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerThreeRadiusWall_classify68

end LaterDeepThreeRadiusWallElimination68

end Max11DegreeRoutes
