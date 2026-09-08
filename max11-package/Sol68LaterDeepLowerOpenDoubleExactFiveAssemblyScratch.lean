import Sol68LaterDeepLowerOpenDoubleFiveWallStaggeredStrideInductionClosureSourceScratch
import Fable68LaterDeepStrictHighSevenSplitScratch

/-! # Exhaustive exact-five assembly and the residual strict-high packet

This file wires the nondegenerate, aligned-degenerate, and
staggered-degenerate closures through the immediate exact-five selector.
The existing below-five endgame then leaves precisely the strict-high seven
split as the residual of the later-deep lower-open double chamber.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerOpenDoubleExactFiveAssembly68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 30000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option maxHeartbeats 30000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleFiveWall_impossible68
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
      3 * g = 5 * n) : False := by
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
  let de := d.coeff (5 * n - 2 * g)
  let e := ee.coeff (6 * n - 2 * g)
  let nextRow :=
    (secondaryResidualRowOnePolynomial68 Ae Be ce d ee).coeff
        (12 * n - 3 * g - 61) +
      (cubicLoadRowOnePolynomial68 0 alpha 0 gamma delta epsilon zeta eta
        Ae Be ce Dtr ee).coeff (12 * n - 3 * g - 61)
  change 3 * n < 2 * g ∧ 2 * g < 5 * n at hopen
  change 2 * g ≤ h at hdouble
  change 3 * g = 5 * n at hwall
  have split :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleFiveWallStrideSelector68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hdouble)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
  change nextRow = 0 ∧
      ((c = 0 ∧ b ≠ 0 ∧ de = 0 ∧ e ≠ 0 ∧ 60 < g ∧
          ((¬60 ∣ 4 * n - g) ∨ (¬60 ∣ 5 * n - 2 * g) ∨
            (ce.coeff (4 * n - g - 60) = 0 ∧
              d.coeff (5 * n - 2 * g - 60) = 0))) ∨
        (c ≠ 0 ∧ a * b ^ 2 = c ^ 2 ∧ 60 < g ∧
          60 ∣ 4 * n - g)) at split
  rcases split.2 with hdegenerate | hnondegenerate
  · rcases hdegenerate with ⟨hc, hb, hd, he, hg, hroute⟩
    have hdegenerate' : ce.coeff (4 * n - g) = 0 ∧
        Be.coeff (3 * n - g) ≠ 0 ∧
        d.coeff (5 * n - 2 * g) = 0 ∧
        ee.coeff (6 * n - 2 * g) ≠ 0 := by
      simpa only [c, b, de, e] using And.intro hc ⟨hb, hd, he⟩
    by_cases hmisaligned :
        (¬60 ∣ 4 * n - g) ∨ (¬60 ∣ 5 * n - 2 * g)
    · exact
        maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleFiveWallDegenerateStaggered_inconsistent68
          l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
          hterminal hsys
          (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
          (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hdouble)
          (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
          (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d]
            using hdegenerate')
          (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g]
            using hmisaligned)
    · have hcAlign : 60 ∣ 4 * n - g := by
        by_contra hcNot
        exact hmisaligned (Or.inl hcNot)
      have hdAlign : 60 ∣ 5 * n - 2 * g := by
        by_contra hdNot
        exact hmisaligned (Or.inr hdNot)
      exact
        maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleFiveWallDegenerateAligned_inconsistent68
          l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
          hterminal hsys
          (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
          (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hdouble)
          (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
          (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d]
            using hdegenerate')
          (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g]
            using hcAlign)
          (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g]
            using hdAlign)
  · exact
      maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleFiveWallNondegenerate_inconsistent68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hdouble)
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, c]
          using hnondegenerate.1)

set_option maxHeartbeats 30000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDouble_forces_strictHigh68
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
      2 * g ≤ h) :
    let n := weightedRadius68 A B C0 D E
    let Ae := expand k 60 A
    let Be := expand k 60 B
    let Ce := expand k 60 C0
    let ce := cubicCDefectPolynomial68 Ae Ce
    let De := expand k 60 D
    let Ee := expand k 60 E
    let ee := cubicEDefectPolynomial68 Ae Ce Ee
    let g := cubicDefectGap68 n Be ce De ee
    5 * n < 3 * g := by
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
  rcases lt_trichotomy (3 * g) (5 * n) with hbelow | hwall | habove
  · exact False.elim
      (maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleBelowFive_impossible68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hdouble)
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hbelow))
  · exact False.elim
      (maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleFiveWall_impossible68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hdouble)
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall))
  · exact habove

set_option maxHeartbeats 30000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDouble_strictHighResidual68
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
      2 * g ≤ h) :
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
  have habove :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDouble_forces_strictHigh68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hdouble)
  change 5 * n < 3 * g at habove
  exact
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleStrictHighSevenSplit68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hdouble)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using habove)

#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleFiveWall_impossible68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDouble_forces_strictHigh68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDouble_strictHighResidual68

end LaterDeepLowerOpenDoubleExactFiveAssembly68

end Max11DegreeRoutes
