import LowScale68SecondaryFirstLoadWallCanonical
import LowScale68SecondaryResidualLoadZeroEndgame

/-! # Residual faces on the first-gap boundary `2g = n`

The tracked classifier
`maximalExpandedIntegratedPolynomialLowerSystem_firstLoadWallClassified68`
already gives `l = 0`, `ee.coeff(6n-g) = 0` and `a*b = 3*D_top` on
`2g = n`.  This module turns those two coefficient cancellations into
strict residual degree drops, selects the residual gap `h > g`, and
extracts the ordinary residual middle invariants throughout `g < h < 2g`.

After `l = 0` the heaviest quartic load is `beta A^3` at `6n`, while the
heaviest residual row-one load is `alpha A^3` against `C0'` at `10n-1`.
Both sit strictly below every displayed residual index on this wall, so
the next exact face is the ordinary middle pair rather than a new mixed
scalar system.  Closing the wall still needs the residual double / row-two
selector and the balanced row-one cubic scalar, supplied by
`LowScale68SecondaryFirstGapBoundary`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FirstGapBoundaryEndgame68

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Residual degree drops after the classified wall -/

theorem firstLoadWall_gap_le_radius (n g : ℕ) (hwall : 2 * g = n) :
    g ≤ n := by
  have : g ≤ 2 * g := Nat.le_mul_of_pos_left g (by omega)
  exact this.trans_eq hwall

theorem firstLoadWall_index_pos (n g : ℕ) (hn : 0 < n)
    (hwall : 2 * g = n) {w : ℕ} (hw : 1 < w) :
    0 < w * n - g := by
  have hg_le : g ≤ n := firstLoadWall_gap_le_radius n g hwall
  have hn_lt : n < w * n :=
    calc
      n = n * 1 := (Nat.mul_one n).symm
      _ < n * w := Nat.mul_lt_mul_of_pos_left hw hn
      _ = w * n := Nat.mul_comm n w
  exact Nat.sub_pos_of_lt (lt_of_le_of_lt hg_le hn_lt)

theorem natDegree_lt_of_le_of_coeff_eq_zero68
    (p : k[X]) (m : ℕ) (hm : 0 < m)
    (hdeg : p.natDegree ≤ m) (hcoeff : p.coeff m = 0) :
    p.natDegree < m := by
  by_cases hp : p = 0
  · simpa [hp, natDegree_zero] using hm
  · have hne : p.natDegree ≠ m := by
      intro h
      have hlead : p.coeff p.natDegree ≠ 0 :=
        leadingCoeff_ne_zero.mpr hp
      rw [h] at hlead
      exact hlead hcoeff
    omega

theorem secondaryDDefectPolynomial68_degree_lt_of_firstLoadWall
    (A B D : k[X]) (n g : ℕ) (hn : 0 < n) (hg : 0 < g)
    (hwall : 2 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (hrel : A.coeff (2 * n) * B.coeff (3 * n - g) =
      3 * D.coeff (5 * n - g)) :
    (secondaryDDefectPolynomial68 A B D).natDegree < 5 * n - g := by
  have hg3 : g ≤ 3 * n :=
    (firstLoadWall_gap_le_radius n g hwall).trans (by omega)
  have hindex : 2 * n + (3 * n - g) = 5 * n - g := by
    rw [← Nat.add_sub_assoc hg3]
    omega
  have hdegree : (secondaryDDefectPolynomial68 A B D).natDegree ≤
      5 * n - g := by
    simp only [secondaryDDefectPolynomial68]
    refine (natDegree_sub_le _ _).trans ?_
    rw [sup_le_iff]
    constructor
    · exact hD
    · have hmul := (natDegree_mul_le (p := A) (q := B)).trans
        (Nat.add_le_add hA hB)
      have hsmul := (natDegree_smul_le (1 / 3 : k) (A * B)).trans hmul
      rwa [hindex] at hsmul
  have hAB := coeff_mul_at_bounds68 A B (2 * n) (3 * n - g) hA hB
  rw [hindex] at hAB
  have hcoeff : (secondaryDDefectPolynomial68 A B D).coeff
      (5 * n - g) = 0 := by
    simp only [secondaryDDefectPolynomial68, coeff_sub, coeff_smul,
      smul_eq_mul]
    rw [hAB]
    linear_combination (-1 / 3 : k) * hrel
  exact natDegree_lt_of_le_of_coeff_eq_zero68 _
    (5 * n - g) (firstLoadWall_index_pos n g hn hwall (by decide))
    hdegree hcoeff

theorem firstSecondaryResidualDegreeDrops68_of_firstLoadWall
    (A B D e : k[X]) (n g : ℕ) (hn : 0 < n) (hg : 0 < g)
    (hwall : 2 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (hrel : A.coeff (2 * n) * B.coeff (3 * n - g) =
      3 * D.coeff (5 * n - g))
    (hetop : e.coeff (6 * n - g) = 0) :
    (secondaryDDefectPolynomial68 A B D).natDegree < 5 * n - g ∧
      e.natDegree < 6 * n - g := by
  refine ⟨secondaryDDefectPolynomial68_degree_lt_of_firstLoadWall A B D n g
    hn hg hwall hA hB hD hrel, ?_⟩
  exact natDegree_lt_of_le_of_coeff_eq_zero68 e (6 * n - g)
    (firstLoadWall_index_pos n g hn hwall (by decide)) he hetop

/-! ## Canonical support, drops, and residual gap -/

/-- The classified first-load wall is genuinely supported by `B` or the
translated even coefficient `c`. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_firstLoadWallBoundary68
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
      2 * g = n) :
    let n := weightedRadius68 A B C0 D E
    let Ae := expand k 60 A
    let Be := expand k 60 B
    let Ce := expand k 60 C0
    let ce := cubicCDefectPolynomial68 Ae Ce
    let De := expand k 60 D
    let Ee := expand k 60 E
    let ee := cubicEDefectPolynomial68 Ae Ce Ee
    let g := cubicDefectGap68 n Be ce De ee
    l = 0 ∧ ee.coeff (6 * n - g) = 0 ∧
      Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
        3 * De.coeff (5 * n - g) ∧
      (Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0) := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  change 2 * g = n at hwall
  change l = 0 ∧ ee.coeff (6 * n - g) = 0 ∧
    Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
      3 * De.coeff (5 * n - g) ∧
    (Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0)
  have hclass :=
    maximalExpandedIntegratedPolynomialLowerSystem_firstLoadWallClassified68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
  change l = 0 ∧ ee.coeff (6 * n - g) = 0 ∧
    Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
      3 * De.coeff (5 * n - g) at hclass
  have hsecondary :=
    maximalExpandedIntegratedPolynomialLowerSystem_secondaryRadius68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  have hattained :
      Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0 ∨
        De.coeff (5 * n - g) ≠ 0 ∨ ee.coeff (6 * n - g) ≠ 0 := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
      hsecondary.2.2.2.2.2
  refine ⟨hclass.1, hclass.2.1, hclass.2.2, ?_⟩
  rcases hattained with hb | hc | hd | he
  · exact Or.inl hb
  · exact Or.inr hc
  · left
    intro hb0
    have hrel := hclass.2.2
    rw [hb0, mul_zero] at hrel
    have hd0 : De.coeff (5 * n - g) = 0 :=
      (mul_eq_zero.mp hrel.symm).resolve_left (by norm_num)
    exact hd hd0
  · exact (he hclass.2.1).elim

/-- The canonical expanded system on `2g = n` has genuine strict degree
drop in both residual coordinates. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_firstLoadWallResidualDrops68
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
      2 * g = n) :
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
      (secondaryDDefectPolynomial68 Ae Be De).natDegree < 5 * n - g ∧
      ee.natDegree < 6 * n - g := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  change 2 * g = n at hwall
  change l = 0 ∧
    (secondaryDDefectPolynomial68 Ae Be De).natDegree < 5 * n - g ∧
    ee.natDegree < 6 * n - g
  have hclass :=
    maximalExpandedIntegratedPolynomialLowerSystem_firstLoadWallClassified68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
  change l = 0 ∧ ee.coeff (6 * n - g) = 0 ∧
    Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
      3 * De.coeff (5 * n - g) at hclass
  have hcore := maximalExpandedIntegratedPolynomialLowerSystem_cubicCore68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have hdrop :=
    maximalExpandedIntegratedPolynomialLowerSystem_degreeDrop68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  have hsecondary :=
    maximalExpandedIntegratedPolynomialLowerSystem_secondaryRadius68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  have hn : 0 < n := by simpa only [n] using hcore.1
  have hg : 0 < g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.1
  have hA : Ae.natDegree ≤ 2 * n := by
    have hAe : Ae.natDegree = 2 * n := by
      simpa only [n, Ae, Be, Ce, De, Ee] using hdrop.1
    omega
  have hB : Be.natDegree ≤ 3 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.2.1
  have hD : De.natDegree ≤ 5 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
      hsecondary.2.2.2.1
  have he : ee.natDegree ≤ 6 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
      hsecondary.2.2.2.2.1
  exact ⟨hclass.1,
    firstSecondaryResidualDegreeDrops68_of_firstLoadWall Ae Be De ee n g
      hn hg hwall hA hB hD he hclass.2.2 hclass.2.1⟩

/-- After the classified wall, the selected residual gap lies strictly
above `g`, and both residual polynomials obey the selected bounds. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_firstLoadWallResidualGap68
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
      2 * g = n) :
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
    l = 0 ∧
      (Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0) ∧
      d.natDegree < 5 * n - g ∧ ee.natDegree < 6 * n - g ∧
      g < h ∧
      d.natDegree ≤ 5 * n - h ∧ ee.natDegree ≤ 6 * n - h := by
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
  change 2 * g = n at hwall
  change l = 0 ∧
    (Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0) ∧
    d.natDegree < 5 * n - g ∧ ee.natDegree < 6 * n - g ∧
    g < h ∧
    d.natDegree ≤ 5 * n - h ∧ ee.natDegree ≤ 6 * n - h
  have hboundary :=
    maximalExpandedIntegratedPolynomialLowerSystem_firstLoadWallBoundary68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
  change l = 0 ∧ ee.coeff (6 * n - g) = 0 ∧
    Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
      3 * De.coeff (5 * n - g) ∧
    (Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0) at hboundary
  have hdrops :=
    maximalExpandedIntegratedPolynomialLowerSystem_firstLoadWallResidualDrops68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
  change l = 0 ∧ d.natDegree < 5 * n - g ∧
    ee.natDegree < 6 * n - g at hdrops
  have hgh : g < h := by
    simpa only [h] using secondaryResidualGap68_gt_of_strictDrops n g d ee
      hdrops.2.1 hdrops.2.2
  have hdbase : d.natDegree < 5 * n := by omega
  have hebase : ee.natDegree < 6 * n := by omega
  have hbounds : d.natDegree ≤ 5 * n - h ∧
      ee.natDegree ≤ 6 * n - h := by
    simpa only [h] using secondaryResidualGap68_degreeBounds n d ee
      hdbase hebase
  exact ⟨hboundary.1, hboundary.2.2.2, hdrops.2.1, hdrops.2.2, hgh,
    hbounds⟩

/-! ## Load cutoffs after `l = 0` on the wall -/

set_option maxHeartbeats 2000000 in
theorem cubicLoadPolynomials68_degreeBounds_of_l_eq_zero_loadWall
    (alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hwall : 2 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadSPolynomial68 0 alpha beta delta A B c).natDegree ≤ 3 * n - g ∧
    (cubicLoadTPolynomial68 0 alpha beta gamma epsilon A B c D).natDegree ≤
      4 * n ∧
    (cubicLoadUPolynomial68 0 alpha beta gamma delta zeta
      A B c D e).natDegree ≤ 5 * n - g ∧
    (cubicLoadVPolynomial68 0 alpha beta gamma delta epsilon eta
      A B c D e).natDegree ≤ 6 * n := by
  simp only [cubicLoadSPolynomial68, cubicLoadTPolynomial68,
    cubicLoadUPolynomial68, cubicLoadVPolynomial68, zero_mul, mul_zero,
    zero_smul, smul_zero, add_zero, sub_zero]
  constructor
  · compute_degree
    omega
  constructor
  · compute_degree
    omega
  constructor <;> compute_degree <;> omega

set_option maxHeartbeats 2000000 in
/-- After `l=0` the heaviest quartic-invariant load is `beta A^3` at `6n`,
strictly below the residual middle index `9n-g-h` on `2g=n`. -/
theorem secondaryLoadInvariantFourPolynomial68_degree_lt_middle_of_firstLoadWall
    (beta gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g h : ℕ) (hg : 0 < g) (hwall : 2 * g = n) (hh : h < 2 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - h) :
    (secondaryLoadInvariantFourPolynomial68
      0 beta gamma delta epsilon zeta A B c D e).natDegree <
        9 * n - g - h := by
  simp only [secondaryLoadInvariantFourPolynomial68, zero_mul, mul_zero,
    zero_smul, smul_zero, add_zero, sub_zero]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
theorem secondaryLoadInvariantFourPolynomial68_degree_lt_double_of_firstLoadWall
    (beta gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g : ℕ) (hg : 0 < g) (hwall : 2 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (secondaryLoadInvariantFourPolynomial68
      0 beta gamma delta epsilon zeta A B c D e).natDegree <
        9 * n - 3 * g := by
  simp only [secondaryLoadInvariantFourPolynomial68, zero_mul, mul_zero,
    zero_smul, smul_zero, add_zero, sub_zero]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
theorem secondaryLoadInvariantThreePolynomial68_degree_lt_middle_of_firstLoadWall
    (l beta gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g h : ℕ) (hg : 0 < g) (hwall : 2 * g = n) (hh : h < 2 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - h) :
    (secondaryLoadInvariantThreePolynomial68
      l beta gamma delta epsilon zeta A B c D e).natDegree <
        10 * n - g - h := by
  simp only [secondaryLoadInvariantThreePolynomial68]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
/-- After `l=0` the heaviest cubic-invariant load sits at `7n-g = 13n/2`,
strictly below the residual double index `10n-3g = 17n/2`.  The `l A^3 B`
term of old weight `9n-g` meets that index and is therefore excluded. -/
theorem secondaryLoadInvariantThreePolynomial68_degree_lt_double_of_firstLoadWall
    (beta gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g : ℕ) (hg : 0 < g) (hwall : 2 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (secondaryLoadInvariantThreePolynomial68
      0 beta gamma delta epsilon zeta A B c D e).natDegree <
        10 * n - 3 * g := by
  have hn : 0 < n :=
    lt_of_lt_of_le hg (firstLoadWall_gap_le_radius n g hwall)
  simp only [secondaryLoadInvariantThreePolynomial68, zero_mul, mul_zero,
    zero_smul, smul_zero, add_zero, sub_zero]
  compute_degree
  omega

set_option maxHeartbeats 6000000 in
theorem cubicLoadRowTwoPolynomial68_degree_lt_cubicFace_of_firstLoadWall
    (alpha beta gamma delta epsilon zeta eta : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hwall : 2 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (cubicLoadRowTwoPolynomial68 0 alpha beta gamma delta epsilon zeta eta
      A B c ((1 / 3 : k) • (A * B) + d) e).natDegree <
        11 * n - 3 * g - 1 := by
  let D := (1 / 3 : k) • (A * B) + d
  let C0 := (1 / 3 : k) • A ^ 2 + c
  let E := (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
  let Sl := cubicLoadSPolynomial68 0 alpha beta delta A B c
  let Tl := cubicLoadTPolynomial68 0 alpha beta gamma epsilon A B c D
  let Ul := cubicLoadUPolynomial68 0 alpha beta gamma delta zeta A B c D e
  let Vl := cubicLoadVPolynomial68 0 alpha beta gamma delta epsilon eta
    A B c D e
  have hn : 0 < n := by omega
  have he' : e.natDegree ≤ 6 * n - g := by omega
  have hD : D.natDegree ≤ 5 * n - g := by
    simp only [D]
    compute_degree
    omega
  have hloads := cubicLoadPolynomials68_degreeBounds_of_l_eq_zero_loadWall
    alpha beta gamma delta epsilon zeta eta A B c D e n g
    hn hg hwall hA hB hc hD he'
  have hSl : Sl.natDegree ≤ 3 * n - g := by simpa only [Sl] using hloads.1
  have hTl : Tl.natDegree ≤ 4 * n := by simpa only [Tl] using hloads.2.1
  have hUl : Ul.natDegree ≤ 5 * n - g := by
    simpa only [Ul] using hloads.2.2.1
  have hVl : Vl.natDegree ≤ 6 * n := by
    simpa only [Vl] using hloads.2.2.2
  have hC0 : C0.natDegree ≤ 4 * n := by
    simp only [C0]
    compute_degree
    omega
  have hE : E.natDegree ≤ 6 * n := by
    simp only [E]
    compute_degree
    omega
  have hUlC : (Ul * derivative C0).natDegree < 11 * n - 3 * g - 1 := by
    compute_degree
    omega
  have hTlD : (Tl * derivative D).natDegree < 11 * n - 3 * g - 1 := by
    compute_degree
    omega
  have hSlE : (Sl * derivative E).natDegree < 11 * n - 3 * g - 1 := by
    compute_degree
    omega
  have hBVl : (B * derivative Vl).natDegree < 11 * n - 3 * g - 1 := by
    compute_degree
    omega
  have hC0Ul : (C0 * derivative Ul).natDegree < 11 * n - 3 * g - 1 := by
    compute_degree
    omega
  have hDTl : (D * derivative Tl).natDegree < 11 * n - 3 * g - 1 := by
    compute_degree
    omega
  change (Ul * derivative C0 + (2 : k) • (Tl * derivative D) +
    (3 : k) • (Sl * derivative E) - (3 : k) • (B * derivative Vl) -
    (2 : k) • (C0 * derivative Ul) - D * derivative Tl).natDegree < _
  compute_degree
  omega

set_option maxHeartbeats 3000000 in
/-- After `l=0` the heaviest row-one load sits at `10n-1`, strictly below
the cubic residual index `12n-3g-1 = 21n/2-1` on the wall. -/
theorem cubicLoadRowOnePolynomial68_degree_lt_cubicFace_of_firstLoadWall
    (alpha beta gamma delta epsilon zeta eta : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hwall : 2 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (cubicLoadRowOnePolynomial68 0 alpha beta gamma delta epsilon zeta eta
      A B c ((1 / 3 : k) • (A * B) + d) e).natDegree <
        12 * n - 3 * g - 1 := by
  let D := (1 / 3 : k) • (A * B) + d
  let C0 := (1 / 3 : k) • A ^ 2 + c
  let E := (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
  let Tl := cubicLoadTPolynomial68 0 alpha beta gamma epsilon A B c D
  let Ul := cubicLoadUPolynomial68 0 alpha beta gamma delta zeta A B c D e
  let Vl := cubicLoadVPolynomial68 0 alpha beta gamma delta epsilon eta
    A B c D e
  have hn : 0 < n := by omega
  have he' : e.natDegree ≤ 6 * n - g := by omega
  have hD : D.natDegree ≤ 5 * n - g := by
    simp only [D]
    compute_degree
    omega
  have hloads := cubicLoadPolynomials68_degreeBounds_of_l_eq_zero_loadWall
    alpha beta gamma delta epsilon zeta eta A B c D e n g
    hn hg hwall hA hB hc hD he'
  have hTl : Tl.natDegree ≤ 4 * n := by
    simpa only [Tl] using hloads.2.1
  have hUl : Ul.natDegree ≤ 5 * n - g := by
    simpa only [Ul] using hloads.2.2.1
  have hVl : Vl.natDegree ≤ 6 * n := by
    simpa only [Vl] using hloads.2.2.2
  have hC0 : C0.natDegree ≤ 4 * n := by
    simp only [C0]
    compute_degree
    omega
  have hE : E.natDegree ≤ 6 * n := by
    simp only [E]
    compute_degree
    omega
  have hUlD : (Ul * derivative D).natDegree < 12 * n - 3 * g - 1 := by
    compute_degree
    omega
  have hTlE : (Tl * derivative E).natDegree < 12 * n - 3 * g - 1 := by
    compute_degree
    omega
  have hC0Vl : (C0 * derivative Vl).natDegree < 12 * n - 3 * g - 1 := by
    compute_degree
    omega
  have hDUl : (D * derivative Ul).natDegree < 12 * n - 3 * g - 1 := by
    compute_degree
    omega
  change (Ul * derivative D + (2 : k) • (Tl * derivative E) -
    (2 : k) • (C0 * derivative Vl) - D * derivative Ul).natDegree < _
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
theorem cubicLoadRowOnePolynomial68_degree_lt_residualDouble_of_firstLoadWall
    (alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hg : 0 < g) (hwall : 2 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (cubicLoadRowOnePolynomial68 0 alpha beta gamma delta epsilon zeta eta
      A B c D e).natDegree < 12 * n - 3 * g - 1 := by
  let C0 := (1 / 3 : k) • A ^ 2 + c
  let E := (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
  let Tl := cubicLoadTPolynomial68 0 alpha beta gamma epsilon A B c D
  let Ul := cubicLoadUPolynomial68 0 alpha beta gamma delta zeta A B c D e
  let Vl := cubicLoadVPolynomial68 0 alpha beta gamma delta epsilon eta
    A B c D e
  have he' : e.natDegree ≤ 6 * n - g := by omega
  have hloads := cubicLoadPolynomials68_degreeBounds_of_l_eq_zero_loadWall
    alpha beta gamma delta epsilon zeta eta A B c D e n g
    (by omega) hg hwall hA hB hc hD he'
  have hTl : Tl.natDegree ≤ 4 * n := by
    simpa only [Tl] using hloads.2.1
  have hUl : Ul.natDegree ≤ 5 * n - g := by
    simpa only [Ul] using hloads.2.2.1
  have hVl : Vl.natDegree ≤ 6 * n := by
    simpa only [Vl] using hloads.2.2.2
  have hC0 : C0.natDegree ≤ 4 * n := by
    simp only [C0]
    compute_degree
    omega
  have hE : E.natDegree ≤ 6 * n := by
    simp only [E]
    compute_degree
    omega
  have hUlD : (Ul * derivative D).natDegree < 12 * n - 3 * g - 1 := by
    compute_degree
    omega
  have hTlE : (Tl * derivative E).natDegree < 12 * n - 3 * g - 1 := by
    compute_degree
    omega
  have hC0Vl : (C0 * derivative Vl).natDegree < 12 * n - 3 * g - 1 := by
    compute_degree
    omega
  have hDUl : (D * derivative Ul).natDegree < 12 * n - 3 * g - 1 := by
    compute_degree
    omega
  change (Ul * derivative D + (2 : k) • (Tl * derivative E) -
    (2 : k) • (C0 * derivative Vl) - D * derivative Ul).natDegree < _
  compute_degree
  omega

/-! ## Homogeneous residual middle coefficients on the wall -/

set_option maxHeartbeats 2000000 in
theorem secondaryResidualInvariantFourPolynomial68_coeff_middle_of_firstLoadWall
    (B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g) (hwall : 2 * g = n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (secondaryResidualInvariantFourPolynomial68 B c d e).coeff
        (9 * n - g - h) =
      (8 / 3 : k) *
        (B.coeff (3 * n - g) * e.coeff (6 * n - h) +
          c.coeff (4 * n - g) * d.coeff (5 * n - h)) := by
  have hB3 : (B ^ 3).natDegree < 9 * n - g - h := by
    compute_degree
    omega
  have hBe := coeff_mul_at_bounds68 B e (3 * n - g) (6 * n - h) hB he
  have hBei : (3 * n - g) + (6 * n - h) = 9 * n - g - h := by omega
  rw [hBei] at hBe
  have hcd := coeff_mul_at_bounds68 c d (4 * n - g) (5 * n - h) hc hd
  have hcdi : (4 * n - g) + (5 * n - h) = 9 * n - g - h := by omega
  rw [hcdi] at hcd
  simp only [secondaryResidualInvariantFourPolynomial68, coeff_add,
    coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hB3, hBe, hcd]
  ring

set_option maxHeartbeats 2000000 in
theorem secondaryResidualInvariantThreePolynomial68_coeff_middle_of_firstLoadWall
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g) (hwall : 2 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (secondaryResidualInvariantThreePolynomial68 A B c d e).coeff
        (10 * n - g - h) =
      (8 / 9 : k) *
        (-(A.coeff (2 * n) * B.coeff (3 * n - g) *
            d.coeff (5 * n - h)) +
          3 * c.coeff (4 * n - g) * e.coeff (6 * n - h)) := by
  have hABd := coeff_mul_mul_at_bounds68 A B d (2 * n)
    (3 * n - g) (5 * n - h) hA hB hd
  have hABdi : 2 * n + (3 * n - g) + (5 * n - h) =
      10 * n - g - h := by omega
  rw [hABdi] at hABd
  have hB2c : (B ^ 2 * c).natDegree < 10 * n - g - h := by
    compute_degree
    omega
  have hce := coeff_mul_at_bounds68 c e (4 * n - g) (6 * n - h) hc he
  have hcei : (4 * n - g) + (6 * n - h) = 10 * n - g - h := by omega
  rw [hcei] at hce
  have hd2 : (d ^ 2).natDegree < 10 * n - g - h := by
    compute_degree
    omega
  simp only [secondaryResidualInvariantThreePolynomial68, coeff_add,
    coeff_sub, coeff_smul, smul_eq_mul, hABd,
    coeff_eq_zero_of_natDegree_lt hB2c, hce,
    coeff_eq_zero_of_natDegree_lt hd2]
  ring

set_option maxHeartbeats 2000000 in
theorem cubicFirstIntegralFourPolynomial68_coeff_residualMiddle_of_firstLoadWall
    (beta gamma delta epsilon zeta : k) (A B c d e : k[X])
    (n g h : ℕ) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hwall : 2 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (cubicFirstIntegralFourPolynomial68 0 beta gamma delta epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff
        (9 * n - g - h) =
      (8 / 3 : k) *
        (B.coeff (3 * n - g) * e.coeff (6 * n - h) +
          c.coeff (4 * n - g) * d.coeff (5 * n - h)) := by
  let D := (1 / 3 : k) • (A * B) + d
  have hD : D.natDegree ≤ 5 * n - g := by
    simp only [D]
    compute_degree
    omega
  have hload :=
    secondaryLoadInvariantFourPolynomial68_degree_lt_middle_of_firstLoadWall
      beta gamma delta epsilon zeta A B c D e n g h hg hwall hh
      hA hB hc hD he
  rw [cubicFirstIntegralFourPolynomial68_secondaryLoadSplit,
    show cubicFirstIntegralFourPolynomial68 0 0 0 0 0 0 A B c D e =
        secondaryResidualInvariantFourPolynomial68 B c d e by
      simpa only [D] using
        cubicFirstIntegralFourPolynomial68_residualCoordinates A B c d e,
    coeff_add,
    secondaryResidualInvariantFourPolynomial68_coeff_middle_of_firstLoadWall
      B c d e n g h hg hgh hh hwall hB hc hd he,
    coeff_eq_zero_of_natDegree_lt hload, add_zero]

set_option maxHeartbeats 2000000 in
theorem cubicFirstIntegralThreePolynomial68_coeff_residualMiddle_of_firstLoadWall
    (l beta gamma delta epsilon zeta : k) (A B c d e : k[X])
    (n g h : ℕ) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hwall : 2 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (cubicFirstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff
        (10 * n - g - h) =
      (8 / 9 : k) *
        (-(A.coeff (2 * n) * B.coeff (3 * n - g) *
            d.coeff (5 * n - h)) +
          3 * c.coeff (4 * n - g) * e.coeff (6 * n - h)) := by
  let D := (1 / 3 : k) • (A * B) + d
  have hD : D.natDegree ≤ 5 * n - g := by
    simp only [D]
    compute_degree
    omega
  have hload :=
    secondaryLoadInvariantThreePolynomial68_degree_lt_middle_of_firstLoadWall
      l beta gamma delta epsilon zeta A B c D e n g h hg hwall hh
      hA hB hc hD he
  rw [cubicFirstIntegralThreePolynomial68_secondaryLoadSplit,
    show cubicFirstIntegralThreePolynomial68 0 0 0 0 0 0 A B c D e =
        secondaryResidualInvariantThreePolynomial68 A B c d e by
      simpa only [D] using
        cubicFirstIntegralThreePolynomial68_residualCoordinates A B c d e,
    coeff_add,
    secondaryResidualInvariantThreePolynomial68_coeff_middle_of_firstLoadWall
      A B c d e n g h hg hgh hh hwall hA hB hc hd he,
    coeff_eq_zero_of_natDegree_lt hload, add_zero]

theorem polynomialSecondaryResidualBetweenFace68_of_firstLoadWall
    (beta gamma delta epsilon zeta i4 i3 : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hwall : 2 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hi4 : cubicFirstIntegralFourPolynomial68
      0 beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hi3 : cubicFirstIntegralThreePolynomial68
      0 beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i3) :
    SecondaryResidualBetweenFace68
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (d.coeff (5 * n - h))
      (e.coeff (6 * n - h)) := by
  constructor
  · have hz := congrArg (fun p : k[X] => p.coeff (9 * n - g - h)) hi4
    rw [cubicFirstIntegralFourPolynomial68_coeff_residualMiddle_of_firstLoadWall
      beta gamma delta epsilon zeta A B c d e n g h hg hgh hh
      hwall hA hB hc hd he] at hz
    have hindex : 9 * n - g - h ≠ 0 := by omega
    simp only [coeff_C, if_neg hindex] at hz
    exact (mul_eq_zero.mp hz).resolve_left (by norm_num)
  · have hz := congrArg (fun p : k[X] => p.coeff (10 * n - g - h)) hi3
    rw [cubicFirstIntegralThreePolynomial68_coeff_residualMiddle_of_firstLoadWall
      0 beta gamma delta epsilon zeta A B c d e n g h hg hgh hh
      hwall hA hB hc hd he] at hz
    have hindex : 10 * n - g - h ≠ 0 := by omega
    simp only [coeff_C, if_neg hindex] at hz
    have hzero := (mul_eq_zero.mp hz).resolve_left (by norm_num)
    linear_combination hzero

/-! ## Homogeneous residual double invariants on the wall -/

set_option maxHeartbeats 2000000 in
theorem secondaryResidualInvariantFourPolynomial68_coeff_double_of_firstLoadWall
    (B c d e : k[X]) (n g : ℕ) (hg : 0 < g) (hwall : 2 * g = n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - 2 * g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (secondaryResidualInvariantFourPolynomial68 B c d e).coeff
        (9 * n - 3 * g) =
      (8 / 27 : k) *
        (-(B.coeff (3 * n - g) ^ 3) +
          9 * B.coeff (3 * n - g) * e.coeff (6 * n - 2 * g) +
          9 * c.coeff (4 * n - g) * d.coeff (5 * n - 2 * g)) := by
  have hB3 := coeff_pow_at_bound68 B (3 * n - g) 3 hB
  have hB3i : 3 * (3 * n - g) = 9 * n - 3 * g := by omega
  rw [hB3i] at hB3
  have hBe := coeff_mul_at_bounds68 B e (3 * n - g)
    (6 * n - 2 * g) hB he
  have hBei : (3 * n - g) + (6 * n - 2 * g) =
      9 * n - 3 * g := by omega
  rw [hBei] at hBe
  have hcd := coeff_mul_at_bounds68 c d (4 * n - g)
    (5 * n - 2 * g) hc hd
  have hcdi : (4 * n - g) + (5 * n - 2 * g) =
      9 * n - 3 * g := by omega
  rw [hcdi] at hcd
  simp only [secondaryResidualInvariantFourPolynomial68, coeff_add,
    coeff_smul, smul_eq_mul, hB3, hBe, hcd]
  ring

set_option maxHeartbeats 2000000 in
theorem secondaryResidualInvariantThreePolynomial68_coeff_double_of_firstLoadWall
    (A B c d e : k[X]) (n g : ℕ) (hg : 0 < g) (hwall : 2 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - 2 * g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (secondaryResidualInvariantThreePolynomial68 A B c d e).coeff
        (10 * n - 3 * g) =
      (8 / 9 : k) *
        (-(A.coeff (2 * n) * B.coeff (3 * n - g) *
            d.coeff (5 * n - 2 * g)) -
          B.coeff (3 * n - g) ^ 2 * c.coeff (4 * n - g) +
          3 * c.coeff (4 * n - g) * e.coeff (6 * n - 2 * g)) := by
  have hABd := coeff_mul_mul_at_bounds68 A B d (2 * n)
    (3 * n - g) (5 * n - 2 * g) hA hB hd
  have hABdi : 2 * n + (3 * n - g) + (5 * n - 2 * g) =
      10 * n - 3 * g := by omega
  rw [hABdi] at hABd
  have hBBc := coeff_mul_mul_at_bounds68 B B c (3 * n - g)
    (3 * n - g) (4 * n - g) hB hB hc
  have hBBci : (3 * n - g) + (3 * n - g) + (4 * n - g) =
      10 * n - 3 * g := by omega
  rw [hBBci] at hBBc
  have hB2c : (B ^ 2 * c).coeff (10 * n - 3 * g) =
      B.coeff (3 * n - g) ^ 2 * c.coeff (4 * n - g) := by
    simpa only [pow_two] using hBBc
  have hce := coeff_mul_at_bounds68 c e (4 * n - g)
    (6 * n - 2 * g) hc he
  have hcei : (4 * n - g) + (6 * n - 2 * g) =
      10 * n - 3 * g := by omega
  rw [hcei] at hce
  have hd2 : (d ^ 2).natDegree < 10 * n - 3 * g := by
    compute_degree
    omega
  simp only [secondaryResidualInvariantThreePolynomial68, coeff_add,
    coeff_sub, coeff_smul, smul_eq_mul, hABd, hB2c, hce,
    coeff_eq_zero_of_natDegree_lt hd2]
  ring

set_option maxHeartbeats 2000000 in
theorem cubicFirstIntegralFourPolynomial68_coeff_residualDouble_of_firstLoadWall
    (beta gamma delta epsilon zeta : k) (A B c d e : k[X])
    (n g : ℕ) (hg : 0 < g) (hwall : 2 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - 2 * g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (cubicFirstIntegralFourPolynomial68 0 beta gamma delta epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff
        (9 * n - 3 * g) =
      (8 / 27 : k) *
        (-(B.coeff (3 * n - g) ^ 3) +
          9 * B.coeff (3 * n - g) * e.coeff (6 * n - 2 * g) +
          9 * c.coeff (4 * n - g) * d.coeff (5 * n - 2 * g)) := by
  let D := (1 / 3 : k) • (A * B) + d
  have hD : D.natDegree ≤ 5 * n - g := by
    simp only [D]
    compute_degree
    omega
  have hload :=
    secondaryLoadInvariantFourPolynomial68_degree_lt_double_of_firstLoadWall
      beta gamma delta epsilon zeta A B c D e n g hg hwall
      hA hB hc hD he
  rw [cubicFirstIntegralFourPolynomial68_secondaryLoadSplit,
    show cubicFirstIntegralFourPolynomial68 0 0 0 0 0 0 A B c D e =
        secondaryResidualInvariantFourPolynomial68 B c d e by
      simpa only [D] using
        cubicFirstIntegralFourPolynomial68_residualCoordinates A B c d e,
    coeff_add,
    secondaryResidualInvariantFourPolynomial68_coeff_double_of_firstLoadWall
      B c d e n g hg hwall hB hc hd he,
    coeff_eq_zero_of_natDegree_lt hload, add_zero]

set_option maxHeartbeats 2000000 in
theorem cubicFirstIntegralThreePolynomial68_coeff_residualDouble_of_firstLoadWall
    (beta gamma delta epsilon zeta : k) (A B c d e : k[X])
    (n g : ℕ) (hg : 0 < g) (hwall : 2 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - 2 * g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (cubicFirstIntegralThreePolynomial68 0 beta gamma delta epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff
        (10 * n - 3 * g) =
      (8 / 9 : k) *
        (-(A.coeff (2 * n) * B.coeff (3 * n - g) *
            d.coeff (5 * n - 2 * g)) -
          B.coeff (3 * n - g) ^ 2 * c.coeff (4 * n - g) +
          3 * c.coeff (4 * n - g) * e.coeff (6 * n - 2 * g)) := by
  let D := (1 / 3 : k) • (A * B) + d
  have hD : D.natDegree ≤ 5 * n - g := by
    simp only [D]
    compute_degree
    omega
  have hload :=
    secondaryLoadInvariantThreePolynomial68_degree_lt_double_of_firstLoadWall
      beta gamma delta epsilon zeta A B c D e n g hg hwall
      hA hB hc hD he
  rw [cubicFirstIntegralThreePolynomial68_secondaryLoadSplit,
    show cubicFirstIntegralThreePolynomial68 0 0 0 0 0 0 A B c D e =
        secondaryResidualInvariantThreePolynomial68 A B c d e by
      simpa only [D] using
        cubicFirstIntegralThreePolynomial68_residualCoordinates A B c d e,
    coeff_add,
    secondaryResidualInvariantThreePolynomial68_coeff_double_of_firstLoadWall
      A B c d e n g hg hwall hA hB hc hd he,
    coeff_eq_zero_of_natDegree_lt hload, add_zero]

theorem polynomialSecondaryResidualDoubleInvariants68_of_firstLoadWall
    (beta gamma delta epsilon zeta i4 i3 : k)
    (A B c d e : k[X]) (n g : ℕ)
    (hg : 0 < g) (hwall : 2 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - 2 * g)
    (he : e.natDegree ≤ 6 * n - 2 * g)
    (hi4 : cubicFirstIntegralFourPolynomial68
      0 beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hi3 : cubicFirstIntegralThreePolynomial68
      0 beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i3) :
    -(B.coeff (3 * n - g) ^ 3) +
        9 * B.coeff (3 * n - g) * e.coeff (6 * n - 2 * g) +
        9 * c.coeff (4 * n - g) * d.coeff (5 * n - 2 * g) = 0 ∧
      -(A.coeff (2 * n) * B.coeff (3 * n - g) *
          d.coeff (5 * n - 2 * g)) -
        B.coeff (3 * n - g) ^ 2 * c.coeff (4 * n - g) +
        3 * c.coeff (4 * n - g) * e.coeff (6 * n - 2 * g) = 0 := by
  constructor
  · have hz := congrArg (fun p : k[X] => p.coeff (9 * n - 3 * g)) hi4
    rw [cubicFirstIntegralFourPolynomial68_coeff_residualDouble_of_firstLoadWall
      beta gamma delta epsilon zeta A B c d e n g hg hwall
      hA hB hc hd he] at hz
    have hindex : 9 * n - 3 * g ≠ 0 := by omega
    simp only [coeff_C, if_neg hindex] at hz
    exact (mul_eq_zero.mp hz).resolve_left (by norm_num)
  · have hz := congrArg (fun p : k[X] => p.coeff (10 * n - 3 * g)) hi3
    rw [cubicFirstIntegralThreePolynomial68_coeff_residualDouble_of_firstLoadWall
      beta gamma delta epsilon zeta A B c d e n g hg hwall
      hA hB hc hd he] at hz
    have hindex : 10 * n - 3 * g ≠ 0 := by omega
    simp only [coeff_C, if_neg hindex] at hz
    have hzero := (mul_eq_zero.mp hz).resolve_left (by norm_num)
    linear_combination hzero

/-! ## Canonical residual middle face on the wall -/

set_option maxHeartbeats 4000000 in
/-- On the canonical expanded system, after the classified wall `2g = n`,
every residual middle window `g < h < 2g` supplies the ordinary two
invariant equations. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_firstLoadWallResidualMiddleFace68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (h : ℕ) (hterminal : terminal ≠ 0)
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
      2 * g = n)
    (hgh :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      g < h)
    (hh :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      h < 2 * g)
    (hmiddle :
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
      d.natDegree ≤ 5 * n - h ∧ ee.natDegree ≤ 6 * n - h) :
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
    l = 0 ∧
      SecondaryResidualBetweenFace68
        (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
        (ce.coeff (4 * n - g)) (d.coeff (5 * n - h))
        (ee.coeff (6 * n - h)) := by
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
  change 2 * g = n at hwall
  change g < h at hgh
  change h < 2 * g at hh
  change d.natDegree ≤ 5 * n - h ∧
    ee.natDegree ≤ 6 * n - h at hmiddle
  change l = 0 ∧
    SecondaryResidualBetweenFace68
      (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
      (ce.coeff (4 * n - g)) (d.coeff (5 * n - h))
      (ee.coeff (6 * n - h))
  have hclass :=
    maximalExpandedIntegratedPolynomialLowerSystem_firstLoadWallClassified68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
  change l = 0 ∧ ee.coeff (6 * n - g) = 0 ∧
    Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
      3 * De.coeff (5 * n - g) at hclass
  have hl : l = 0 := hclass.1
  have hdrop := maximalExpandedIntegratedPolynomialLowerSystem_degreeDrop68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have hsecondary :=
    maximalExpandedIntegratedPolynomialLowerSystem_secondaryRadius68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  have hg : 0 < g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.1
  have hA : Ae.natDegree ≤ 2 * n := by
    have hAe : Ae.natDegree = 2 * n := by
      simpa only [n, Ae, Be, Ce, De, Ee] using hdrop.1
    omega
  have hB : Be.natDegree ≤ 3 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.2.1
  have hc : ce.natDegree ≤ 4 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
      hsecondary.2.2.1
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec :
      Ee = (1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using
      cubicEDefectPolynomial68_eq_cubicCoordinates Ae Ce Ee
  have hDrec : De = (1 / 3 : k) • (Ae * Be) + d := by
    simpa only [d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
  obtain ⟨i4, hi4⟩ := hsys.firstFour
  obtain ⟨i3, hi3⟩ := hsys.firstThree
  have hi4e : firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i4 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_firstIntegralFourPolynomial68_of_eq
        l beta gamma delta epsilon zeta i4 A B C0 D E hi4
  have hi3e : firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i3 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_firstIntegralThreePolynomial68_of_eq
        l beta gamma delta epsilon zeta i3 A B C0 D E hi3
  have hi4c := hi4e
  rw [hCrec, hErec, firstIntegralFourPolynomial68_cubicCoordinates,
    hDrec, hl] at hi4c
  have hi3c := hi3e
  rw [hCrec, hErec, firstIntegralThreePolynomial68_cubicCoordinates,
    hDrec, hl] at hi3c
  exact ⟨hl,
    polynomialSecondaryResidualBetweenFace68_of_firstLoadWall
      beta gamma delta epsilon zeta i4 i3 Ae Be ce d ee n g h
      hg hgh hh hwall hA hB hc hmiddle.1 hmiddle.2 hi4c hi3c⟩

end FirstGapBoundaryEndgame68

#print axioms secondaryDDefectPolynomial68_degree_lt_of_firstLoadWall
#print axioms firstSecondaryResidualDegreeDrops68_of_firstLoadWall
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_firstLoadWallBoundary68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_firstLoadWallResidualDrops68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_firstLoadWallResidualGap68
#print axioms cubicLoadPolynomials68_degreeBounds_of_l_eq_zero_loadWall
#print axioms secondaryLoadInvariantFourPolynomial68_degree_lt_middle_of_firstLoadWall
#print axioms cubicLoadRowTwoPolynomial68_degree_lt_cubicFace_of_firstLoadWall
#print axioms cubicLoadRowOnePolynomial68_degree_lt_cubicFace_of_firstLoadWall
#print axioms polynomialSecondaryResidualBetweenFace68_of_firstLoadWall
#print axioms polynomialSecondaryResidualDoubleInvariants68_of_firstLoadWall
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_firstLoadWallResidualMiddleFace68

end Max11DegreeRoutes
