import Sol68LaterDeepLowerOpenDoubleFiveWallSelectorScratch

/-! # The first lower coefficient on the residual double five-wall packet -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerOpenDoubleFiveWallNextCoefficient68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 30000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The four scalar equations have two honest algebraic branches.  In the
degenerate branch the attained residual edge is necessarily the `e` edge;
in the nondegenerate branch the leading cubic discriminant is zero. -/
theorem laterDeepLowerOpenDoubleFiveWallScalarPacket68_refine
    (N a b c d e delta : k) (ha : a ≠ 0)
    (hsupport : b ≠ 0 ∨ c ≠ 0) (hattained : d ≠ 0 ∨ e ≠ 0)
    (packet : LaterDeepLowerOpenDoubleFiveWallScalarPacket68
      N a b c d e delta) :
    (c = 0 ∧ b ≠ 0 ∧ d = 0 ∧ e ≠ 0) ∨
      (c ≠ 0 ∧ a * b ^ 2 = c ^ 2) := by
  by_cases hc : c = 0
  · left
    have hb : b ≠ 0 := hsupport.resolve_right (fun hcne => hcne hc)
    have hd : d = 0 := by
      have ht := packet.three
      rw [hc] at ht
      have habd : a * (b * d) = 0 := by linear_combination -ht
      have hbd : b * d = 0 := (mul_eq_zero.mp habd).resolve_left ha
      exact (mul_eq_zero.mp hbd).resolve_left hb
    have he : e ≠ 0 := hattained.resolve_left (fun hdne => hdne hd)
    exact ⟨hc, hb, hd, he⟩
  · right
    have hprod : c * (a * b ^ 2 - c ^ 2) = 0 := by
      linear_combination (1 / 7 : k) * packet.rowOne -
        (5 / 7 : k) * a * packet.three
    exact ⟨hc, (sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left hc))⟩

set_option maxHeartbeats 30000000 in
/-- Exact next potentially useful row-one coefficient.  The leading
coefficient is at `12n-3g-1`; source expansion has stride sixty, so after
the scalar face the first full-stride descendant is `12n-3g-61`.  We keep
the load coefficient explicit: this is precisely the datum needed by the
next algebraic elimination. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleFiveWallNextCoefficient68
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
      3 * g = 5 * n) :
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
    h = 2 * g ∧
      (d.coeff (5 * n - 2 * g) ≠ 0 ∨
        ee.coeff (6 * n - 2 * g) ≠ 0) ∧
      LaterDeepLowerOpenDoubleFiveWallScalarPacket68
        (n : k) (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
        (ce.coeff (4 * n - g)) (d.coeff (5 * n - 2 * g))
        (ee.coeff (6 * n - 2 * g)) delta ∧
      ((secondaryResidualRowOnePolynomial68 Ae Be ce d ee).coeff
          (12 * n - 3 * g - 61) +
        (cubicLoadRowOnePolynomial68 0 alpha 0 gamma delta epsilon zeta eta
          Ae Be ce Dtr ee).coeff (12 * n - 3 * g - 61) = 0) := by
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
  change 3 * n < 2 * g ∧ 2 * g < 5 * n at hopen
  change 2 * g ≤ h at hdouble
  change 3 * g = 5 * n at hwall
  have packet :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleFiveWallSelector68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hdouble)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
  change h = 2 * g ∧
      (d.coeff (5 * n - 2 * g) ≠ 0 ∨
        ee.coeff (6 * n - 2 * g) ≠ 0) ∧
      LaterDeepLowerOpenDoubleFiveWallScalarPacket68
        (n : k) (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
        (ce.coeff (4 * n - g)) (d.coeff (5 * n - 2 * g))
        (ee.coeff (6 * n - 2 * g)) delta at packet
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
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec : Ee = (1 / 27 : k) • Ae ^ 3 +
      (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using
      cubicEDefectPolynomial68_eq_cubicCoordinates Ae Ce Ee
  have hDrec : De = Dtr := by
    simpa only [Dtr, d] using
      secondaryDDefectPolynomial68_reconstruct Ae Be De
  have h1e : lowerRowOnePolynomial68
      (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) Ce De Ee = 0 := by
    dsimp only [Ae, Be, Ce, De, Ee]
    rw [← expand_integratedTPolynomial68, ← expand_integratedUPolynomial68,
      ← expand_integratedVPolynomial68, lowerRowOnePolynomial68_expand,
      hsys.rowOne, map_zero, zero_mul]
  have hrowOne : secondaryResidualRowOnePolynomial68 Ae Be ce d ee +
      cubicLoadRowOnePolynomial68 0 alpha 0 gamma delta epsilon zeta eta
        Ae Be ce Dtr ee = 0 := by
    have hr := h1e
    rw [hCrec, hDrec, hErec, drops.1, drops.2.1] at hr
    exact polynomialSecondaryResidualRowOne68
      0 alpha 0 gamma delta epsilon zeta eta Ae Be ce d ee hr
  have hcoeff := congrArg
    (fun p : k[X] => p.coeff (12 * n - 3 * g - 61)) hrowOne
  rw [coeff_add, coeff_zero] at hcoeff
  exact ⟨packet.1, packet.2.1, packet.2.2, hcoeff⟩

#print axioms laterDeepLowerOpenDoubleFiveWallScalarPacket68_refine
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleFiveWallNextCoefficient68

end LaterDeepLowerOpenDoubleFiveWallNextCoefficient68

end Max11DegreeRoutes
