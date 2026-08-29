import LowScale68SecondaryLaterDeepLowerResidual

/-! # Next coefficient on the later-deep wall `2g = 3n`

The residual split
`maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerResidualSplit68`
leaves the endpoint `2g=3n` with `l=0`, ordinary `F3=F1=0`, mixed-`beta`
I4, and mixed-`beta` row-two.  Row-one is already load-free on the whole
later-deep window.  The next independent coefficient is mixed row-zero at
`10n-1`: the load-free face contributes `(8/81) n a F0`, while
`U E'` supplies `(5/108) n beta a^5` and `D V'` lies strictly below.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerThreeRadiusWallNext68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Mixed row-zero load at the wall `2g = 3n` -/

set_option maxHeartbeats 8000000 in
theorem cubicLoadRowZeroPolynomial68_coeff_tenRadius_of_laterDeepLowerThreeWall
    (alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hwall : 2 * g = 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadRowZeroPolynomial68 0 alpha beta gamma delta epsilon zeta eta
      A B c D e).coeff (10 * n - 1) =
      (5 / 108 : k) * (n : k) * beta * A.coeff (2 * n) ^ 5 := by
  let E := (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
  let Ul := cubicLoadUPolynomial68 0 alpha beta gamma delta zeta A B c D e
  let Vl := cubicLoadVPolynomial68 0 alpha beta gamma delta epsilon eta
    A B c D e
  have hgt : n < g := by omega
  have hUldeg : Ul.natDegree ≤ 4 * n := by
    have h := cubicLoadUPolynomial68_degreeBound_of_loadL 0 alpha beta gamma
      delta zeta A B c D e n g rfl hA hB hc hD he
    have hmax : max (4 * n) (5 * n - g) = 4 * n := by omega
    rwa [hmax] at h
  have hVldeg : Vl.natDegree ≤ 6 * n :=
    cubicLoadVPolynomial68_degreeBound_of_loadL 0 alpha beta gamma delta
      epsilon eta A B c D e n g rfl hA hB hc hD he
  have hEdeg : E.natDegree ≤ 6 * n := by
    simp only [E]; compute_degree; omega
  have hA3 := coeff_pow_at_bound68 A (2 * n) 3 hA
  have hA3i : 3 * (2 * n) = 6 * n := by omega
  rw [hA3i] at hA3
  have hAclt : (A * c).natDegree < 6 * n := by compute_degree; omega
  have helt : e.natDegree < 6 * n := he.trans_lt (by omega)
  have hE : E.coeff (6 * n) = (1 / 27 : k) * A.coeff (2 * n) ^ 3 := by
    simp only [E, coeff_add, coeff_smul, smul_eq_mul, hA3,
      coeff_eq_zero_of_natDegree_lt hAclt, coeff_eq_zero_of_natDegree_lt helt,
      mul_zero, add_zero]
  have hUl : Ul.coeff (4 * n) =
      (5 / 24 * beta : k) * A.coeff (2 * n) ^ 2 := by
    simpa only [Ul] using
      cubicLoadUPolynomial68_coeff_fourRadius_of_firstDeep
        (alpha := alpha) (beta := beta) (gamma := gamma) (delta := delta)
        (zeta := zeta) (A := A) (B := B) (c := c) (D := D) (e := e)
        (n := n) (g := g) (hn := hn) (hg := hg) (hgt := hgt)
        (hA := hA) (hB := hB) (hc := hc) (hD := hD)
  have h1 : (Ul * derivative E).coeff (10 * n - 1) =
      Ul.coeff (4 * n) * E.coeff (6 * n) * ((6 * n : ℕ) : k) := by
    have h := coeff_mul_derivative_at_bounds68 Ul E (4 * n) (6 * n)
      (by omega) hUldeg hEdeg
    have hi : 4 * n + 6 * n - 1 = 10 * n - 1 := by omega
    rwa [hi] at h
  have h2deg : (D * derivative Vl).natDegree < 10 * n - 1 := by
    have h := middleBeta_natDegree_mul_derivative_le68 D Vl (5 * n - g)
      (6 * n) hD (by omega) hVldeg
    have hi : 5 * n - g + 6 * n - 1 = 11 * n - g - 1 := by omega
    have hDV : (D * derivative Vl).natDegree ≤ 11 * n - g - 1 := by
      rwa [hi] at h
    exact hDV.trans_lt (by omega)
  have h2 : (D * derivative Vl).coeff (10 * n - 1) = 0 :=
    coeff_eq_zero_of_natDegree_lt h2deg
  have hcast6 : ((6 * n : ℕ) : k) = 6 * (n : k) := by push_cast; rfl
  change (Ul * derivative E - D * derivative Vl).coeff (10 * n - 1) = _
  rw [coeff_sub, h1, h2, hUl, hE, hcast6, sub_zero]
  ring

set_option maxHeartbeats 3000000 in
theorem integratedLowerRowZeroPolynomial68_tenRadius_of_laterDeepLowerThreeWall
    (alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hwall : 2 * g = 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (lowerRowZeroPolynomial68
      (integratedUPolynomial68 0 alpha beta gamma delta zeta A B
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      (integratedVPolynomial68 0 alpha beta gamma delta epsilon eta A B
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      D ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)).coeff
        (10 * n - 1) =
      (8 / 81 : k) * (n : k) * A.coeff (2 * n) *
        firstSecondaryZero68
          (A.coeff (2 * n)) (B.coeff (3 * n - g))
          (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
          (e.coeff (6 * n - g)) +
      (5 / 108 : k) * (n : k) * beta * A.coeff (2 * n) ^ 5 := by
  have hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n := by omega
  have hidx : 13 * n - 2 * g - 1 = 10 * n - 1 := by omega
  have hcoords := integratedPolynomial68_cubicCoordinates
    0 alpha beta gamma delta epsilon zeta eta A B c D e
  rw [hcoords.u_eq, hcoords.v_eq, cubicRowZeroPolynomial68_split, coeff_add]
  rw [← hidx,
    cubicHomogeneousRowZeroPolynomial68_secondaryCoeff_of_laterDeepLower
      A B c D e n g hn hg hwindow hA hB hc hD he, hidx]
  rw [cubicLoadRowZeroPolynomial68_coeff_tenRadius_of_laterDeepLowerThreeWall
      (alpha := alpha) (beta := beta) (gamma := gamma) (delta := delta)
      (epsilon := epsilon) (zeta := zeta) (eta := eta)
      (A := A) (B := B) (c := c) (D := D) (e := e) (n := n) (g := g)
      (hn := hn) (hg := hg) (hwall := hwall)
      (hA := hA) (hB := hB) (hc := hc) (hD := hD) (he := he)]

/-! ## Canonical mixed F0 and the reduced wall packet -/

set_option maxHeartbeats 8000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerThreeRadiusWall_F0mixed68
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
    l = 0 ∧
      (8 / 81 : k) * (n : k) * Ae.coeff (2 * n) *
          firstSecondaryZero68
            (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
            (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
            (ee.coeff (6 * n - g)) +
        (5 / 108 : k) * (n : k) * beta * Ae.coeff (2 * n) ^ 5 = 0 := by
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
  have hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n := by omega
  have hI3 :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLower_I3face68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwindow)
  have hl : l = 0 := hI3.1
  have data :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLoadI4Data68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  change LaterDeepLoadI4Data68 l beta gamma delta epsilon zeta
    n g Ae Be ce De ee at data
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec : Ee = (1 / 27 : k) • Ae ^ 3 +
      (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using cubicEDefectPolynomial68_eq_cubicCoordinates
      Ae Ce Ee
  have h0e : lowerRowZeroPolynomial68
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) De Ee =
      C terminal * (60 * (X ^ 59 : k[X])) := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_lowerRowZeroPolynomial68_of_system
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
  have hnTen : 10 ≤ n := by
    simpa only [n] using weightedRadius68_ge_ten A B C0 D E data.hn
  have hidx : 59 < 10 * n - 1 := by omega
  rw [hl, hCrec, hErec] at h0e
  have hcoeff :=
    expand_lowerRowZeroPolynomial68_coeff_eq_zero_of_index_gt
      terminal
      (integratedUPolynomial68 0 alpha beta gamma delta zeta
        Ae Be ((1 / 3 : k) • Ae ^ 2 + ce) De
        ((1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee))
      (integratedVPolynomial68 0 alpha beta gamma delta epsilon eta
        Ae Be ((1 / 3 : k) • Ae ^ 2 + ce) De
        ((1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee))
      De ((1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee)
      (10 * n - 1) h0e hidx
  rw [integratedLowerRowZeroPolynomial68_tenRadius_of_laterDeepLowerThreeWall
      (alpha := alpha) (beta := beta) (gamma := gamma) (delta := delta)
      (epsilon := epsilon) (zeta := zeta) (eta := eta)
      (A := Ae) (B := Be) (c := ce) (D := De) (e := ee) (n := n) (g := g)
      (hn := data.hn) (hg := data.hg) (hwall := hwall)
      (hA := data.hA) (hB := data.hB) (hc := data.hc)
      (hD := data.hD) (he := data.he)] at hcoeff
  exact ⟨hl, hcoeff⟩

set_option maxHeartbeats 4000000 in
theorem laterDeepLowerThreeRadiusWall_F0scalar68
    (n : ℕ) (a b c d e beta : k) (hn : 0 < n) (ha : a ≠ 0)
    (hmix :
      (8 / 81 : k) * (n : k) * a * firstSecondaryZero68 a b c d e +
        (5 / 108 : k) * (n : k) * beta * a ^ 5 = 0) :
    firstSecondaryZero68 a b c d e +
      (15 / 32 : k) * beta * a ^ 4 = 0 := by
  have hncast : (n : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hfactorn :
      (n : k) *
        ((8 / 81 : k) * a * firstSecondaryZero68 a b c d e +
          (5 / 108 : k) * beta * a ^ 5) = 0 := by
    convert hmix using 1
    ring
  have hmid := (mul_eq_zero.mp hfactorn).resolve_left hncast
  have hfactora :
      a * ((8 / 81 : k) * firstSecondaryZero68 a b c d e +
        (5 / 108 : k) * beta * a ^ 4) = 0 := by
    convert hmid using 1
    ring
  have hface := (mul_eq_zero.mp hfactora).resolve_left ha
  have h32 :
      (32 : k) * firstSecondaryZero68 a b c d e +
        (15 : k) * beta * a ^ 4 =
      (324 : k) *
        ((8 / 81 : k) * firstSecondaryZero68 a b c d e +
          (5 / 108 : k) * beta * a ^ 4) := by
    ring
  rw [hface, mul_zero] at h32
  have hpack :
      (32 : k) *
        (firstSecondaryZero68 a b c d e +
          (15 / 32 : k) * beta * a ^ 4) =
      (32 : k) * firstSecondaryZero68 a b c d e +
        (15 : k) * beta * a ^ 4 := by
    ring
  rw [← hpack] at h32
  exact (mul_eq_zero.mp h32).resolve_left (by norm_num)

set_option maxHeartbeats 8000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerThreeRadiusWallNext68
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
    l = 0 ∧
      firstSecondaryThree68
        (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
        (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
        (ee.coeff (6 * n - g)) = 0 ∧
      firstSecondaryOne68 (n : k) (g : k)
        (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
        (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
        (ee.coeff (6 * n - g)) = 0 ∧
      (-8 / 9 : k) * firstSecondaryFour68
          (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
          (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
          (ee.coeff (6 * n - g)) +
        (5 / 72 * beta : k) * Ae.coeff (2 * n) ^ 3 = 0 ∧
      (8 / 27 : k) * firstSecondaryTwo68 (n : k) (g : k)
          (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
          (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
          (ee.coeff (6 * n - g)) +
        (5 / 18 : k) * (n : k) * beta * Ae.coeff (2 * n) ^ 4 = 0 ∧
      firstSecondaryZero68
          (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
          (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
          (ee.coeff (6 * n - g)) +
        (15 / 32 : k) * beta * Ae.coeff (2 * n) ^ 4 = 0 := by
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
  have hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n := by omega
  have hsplit :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerResidualSplit68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwindow)
  obtain ⟨hl, hthree, hone, hcases⟩ := hsplit
  have hF0 :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerThreeRadiusWall_F0mixed68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
  have data :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLoadI4Data68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  change LaterDeepLoadI4Data68 l beta gamma delta epsilon zeta
    n g Ae Be ce De ee at data
  have hzero := laterDeepLowerThreeRadiusWall_F0scalar68 n
    (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
    (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
    (ee.coeff (6 * n - g)) beta data.hn data.ha hF0.2
  rcases hcases with hwall3 | hopen | hwall5
  · exact ⟨hl, hthree, hone, hwall3.2.1, hwall3.2.2, hzero⟩
  · have hn : 0 < n := data.hn
    have : 3 * n < 2 * g := hopen.1
    omega
  · have hn : 0 < n := data.hn
    have : 2 * g = 5 * n := hwall5.1
    omega

end LaterDeepLowerThreeRadiusWallNext68

#print axioms cubicLoadRowZeroPolynomial68_coeff_tenRadius_of_laterDeepLowerThreeWall
#print axioms integratedLowerRowZeroPolynomial68_tenRadius_of_laterDeepLowerThreeWall
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerThreeRadiusWall_F0mixed68
#print axioms laterDeepLowerThreeRadiusWall_F0scalar68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerThreeRadiusWallNext68

end Max11DegreeRoutes
