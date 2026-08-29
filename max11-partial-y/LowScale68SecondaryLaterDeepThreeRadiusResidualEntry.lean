import LowScale68SecondaryLaterDeepThreeRadiusWallElimination

/-! # Residual entry from the later-deep wall `2g = 3n`

After the mixed beta load vanishes, the endpoint has the same strict
translated-defect drops as the open lower chamber.  This module packages the
endpoint directly in the secondary-residual coordinates.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepThreeRadiusResidualEntry68

variable {k : Type*} [Field k] [CharZero k]

theorem laterDeepLowerThreeRadiusWall_e_degree_lt68
    (e : k[X]) (n g : ℕ) (hn : 0 < n)
    (hwall : 2 * g = 3 * n)
    (he : e.natDegree ≤ 6 * n - g)
    (hetop : e.coeff (6 * n - g) = 0) :
    e.natDegree < 6 * n - g := by
  have hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n := by omega
  exact natDegree_lt_of_le_of_coeff_eq_zero68 e (6 * n - g)
    (laterDeepLower_index_pos_six n g hn hwindow) he hetop

set_option maxHeartbeats 8000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerThreeRadiusResidualEntry68
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
    let d := secondaryDDefectPolynomial68 Ae Be De
    l = 0 ∧ beta = 0 ∧ ee.coeff (6 * n - g) = 0 ∧
      Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
        3 * De.coeff (5 * n - g) ∧
      d.natDegree < 5 * n - g ∧ ee.natDegree < 6 * n - g ∧
      g < secondaryResidualGap68 n d ee := by
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
  change 2 * g = 3 * n at hwall
  have hclass :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerThreeRadiusWall_classify68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
  have data :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLoadI4Data68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  change LaterDeepLoadI4Data68 l beta gamma delta epsilon zeta
    n g Ae Be ce De ee at data
  have hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n := by omega
  have hd : d.natDegree < 5 * n - g :=
    secondaryDDefectPolynomial68_degree_lt_of_laterDeepLower
      Ae Be De n g data.hn hwindow data.hA data.hB data.hD hclass.2.2.2
  have he : ee.natDegree < 6 * n - g :=
    laterDeepLowerThreeRadiusWall_e_degree_lt68 ee n g data.hn hwall
      data.he hclass.2.2.1
  exact ⟨hclass.1, hclass.2.1, hclass.2.2.1, hclass.2.2.2,
    hd, he, secondaryResidualGap68_gt_of_strictDrops n g d ee hd he⟩

#print axioms laterDeepLowerThreeRadiusWall_e_degree_lt68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerThreeRadiusResidualEntry68

end LaterDeepThreeRadiusResidualEntry68

end Max11DegreeRoutes
