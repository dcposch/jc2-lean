import LowScale68SecondaryLaterDeepFiveRadiusResidualDescent
import LowScale68SecondaryResidualRowTwoFaces
import LowScale68SecondaryResidualRowTwoSystem

/-! # The `h < 5n` residual endgame on `2g = 5n`

The quartic first integral can be substituted into residual row two.  After
that substitution all `alpha` terms cancel, as do the dangerous `gamma*A*d'`
and `epsilon*A*B'` terms.  The only load above the ordinary residual cubic
face is `zeta * (A^2/4+c)'`.  In particular, on `2h=9n` row two forces
`zeta=0`, so the mixed wall becomes the ordinary nonzero discriminant face.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepFiveRadiusResidualEndgame68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 24000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Row two after using the exact quartic first integral.  The final summand
is the only surviving `zeta` contribution. -/
def fiveRadiusReducedRowTwoPolynomial68
    (gamma epsilon zeta i4 : k) (A B c d e : k[X]) : k[X] :=
  (-4 / 27 : k) •
      ((-2 : k) • (A * B ^ 2 * derivative B) +
        (-2 / 3 : k) • (derivative A * B ^ 3) +
        (6 : k) • derivative (B ^ 2 * d) +
        (6 : k) • derivative (B * c ^ 2) +
        (-18 : k) • derivative (d * e)) -
    (1 / 6 * i4 : k) • derivative A -
    (4 / 3 * gamma : k) • derivative (B * c) +
    (2 * epsilon : k) • derivative d +
    zeta • derivative ((1 / 4 : k) • A ^ 2 + c)

/-- The part of the reduced row strictly below the `zeta` face on
`2h=9n`. -/
def fiveRadiusReducedRowTwoRestPolynomial68
    (gamma epsilon i4 : k) (A B c d e : k[X]) : k[X] :=
  (-4 / 27 : k) •
      ((-2 : k) • (A * B ^ 2 * derivative B) +
        (-2 / 3 : k) • (derivative A * B ^ 3) +
        (6 : k) • derivative (B ^ 2 * d) +
        (6 : k) • derivative (B * c ^ 2) +
        (-18 : k) • derivative (d * e)) -
    (1 / 6 * i4 : k) • derivative A -
    (4 / 3 * gamma : k) • derivative (B * c) +
    (2 * epsilon : k) • derivative d

theorem fiveRadiusReducedRowTwoPolynomial68_eq_rest_add
    (gamma epsilon zeta i4 : k) (A B c d e : k[X]) :
    fiveRadiusReducedRowTwoPolynomial68 gamma epsilon zeta i4 A B c d e =
      fiveRadiusReducedRowTwoRestPolynomial68 gamma epsilon i4 A B c d e +
        zeta • derivative ((1 / 4 : k) • A ^ 2 + c) := by
  rfl

set_option maxHeartbeats 12000000 in
/-- Exact cancellation identity obtained by substituting I4 into row two. -/
theorem polynomialFiveRadiusReducedRowTwo68
    (alpha gamma epsilon zeta eta i4 : k)
    (A B c d e : k[X])
    (hi4 : cubicFirstIntegralFourPolynomial68
      0 0 gamma 0 epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4) :
    secondaryResidualRowTwoPolynomial68 A B c d e +
        cubicLoadRowTwoPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
          A B c ((1 / 3 : k) • (A * B) + d) e =
      fiveRadiusReducedRowTwoPolynomial68 gamma epsilon zeta i4 A B c d e := by
  let Q := residualIncidenceQ68 B c d e
  have hi4' := hi4
  rw [cubicFirstIntegralFourPolynomial68_secondaryLoadSplit,
    cubicFirstIntegralFourPolynomial68_residualCoordinates,
    secondaryResidualInvariantFourPolynomial68_eq_incidenceDefect,
    secondaryLoadInvariantFourPolynomial68_residualCoordinates_of_l_beta_delta]
      at hi4'
  change (8 / 3 : k) • Q +
      (zeta • A + (2 * epsilon : k) • B + (4 * gamma : k) • d) = C i4
      at hi4'
  have hQ : Q = (3 / 8 : k) •
      (C i4 - (zeta • A + (2 * epsilon : k) • B +
        (4 * gamma : k) • d)) := by
    calc
      Q = (3 / 8 : k) • ((8 / 3 : k) • Q) := by
        rw [smul_smul]
        norm_num
      _ = (3 / 8 : k) •
          (C i4 - (zeta • A + (2 * epsilon : k) • B +
            (4 * gamma : k) • d)) := by
        rw [eq_sub_iff_add_eq.mpr hi4']
  rw [residualRowTwo_eq_inner68]
  simp only [residualRowTwoInner68]
  have hQ' : residualIncidenceQ68 B c d e = (3 / 8 : k) •
      (C i4 - (zeta • A + (2 * epsilon : k) • B +
        (4 * gamma : k) • d)) := by
    simpa only [Q] using hQ
  rw [hQ']
  simp only [fiveRadiusReducedRowTwoPolynomial68,
    cubicLoadRowTwoPolynomial68, cubicLoadSPolynomial68,
    cubicLoadTPolynomial68, cubicLoadUPolynomial68,
    cubicLoadVPolynomial68, zero_mul, mul_zero, zero_smul, smul_zero,
    add_zero, zero_add, sub_zero, derivative_add, derivative_sub,
    derivative_mul, derivative_pow, derivative_smul, derivative_C]
  simp only [Polynomial.smul_eq_C_mul]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [map_add, map_sub, map_mul, map_pow, map_neg,
    map_zero, RatFunc.algebraMap_C, map_div₀, map_ofNat, map_natCast,
    map_one, zero_mul, mul_zero, add_zero, zero_add]
  ring

theorem fiveRadiusReducedRowTwoPolynomial68_eq_zero
    (alpha gamma epsilon zeta eta i4 : k)
    (A B c d e : k[X])
    (hi4 : cubicFirstIntegralFourPolynomial68
      0 0 gamma 0 epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hrow : secondaryResidualRowTwoPolynomial68 A B c d e +
        cubicLoadRowTwoPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
          A B c ((1 / 3 : k) • (A * B) + d) e = 0) :
    fiveRadiusReducedRowTwoPolynomial68 gamma epsilon zeta i4 A B c d e = 0 := by
  rw [← polynomialFiveRadiusReducedRowTwo68
    alpha gamma epsilon zeta eta i4 A B c d e hi4]
  exact hrow

set_option maxHeartbeats 4000000 in
theorem fiveRadiusReducedRowTwoRestPolynomial68_degree_lt_zetaWall
    (gamma epsilon i4 : k) (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hwall : 2 * g = 5 * n) (htie : 2 * h = 9 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (fiveRadiusReducedRowTwoRestPolynomial68 gamma epsilon i4 A B c d e).natDegree <
      4 * n - 1 := by
  let bound := 4 * n - 1
  have h1 : (A * B ^ 2 * derivative B).natDegree < bound := by
    dsimp [bound]
    compute_degree
    omega
  have h2 : (derivative A * B ^ 3).natDegree < bound := by
    dsimp [bound]
    compute_degree
    omega
  have h3 : (derivative (B ^ 2 * d)).natDegree < bound := by
    have hp : (B ^ 2 * d).natDegree ≤
        (6 * n - 2 * g) + (5 * n - h) := by
      compute_degree
      omega
    have hder := natDegree_derivative_le (B ^ 2 * d)
    dsimp [bound]
    omega
  have h4 : (derivative (B * c ^ 2)).natDegree < bound := by
    have hp : (B * c ^ 2).natDegree ≤
        (3 * n - g) + (8 * n - 2 * g) := by
      compute_degree
      omega
    have hder := natDegree_derivative_le (B * c ^ 2)
    dsimp [bound]
    omega
  have h5 : (derivative (d * e)).natDegree < bound := by
    have hp : (d * e).natDegree ≤
        (5 * n - h) + (6 * n - h) := by
      compute_degree
      omega
    have hder := natDegree_derivative_le (d * e)
    dsimp [bound]
    omega
  have h6 : (derivative A).natDegree < bound := by
    dsimp [bound]
    compute_degree
    omega
  have h7 : (derivative (B * c)).natDegree < bound := by
    have hp : (B * c).natDegree ≤
        (3 * n - g) + (4 * n - g) := by
      compute_degree
      omega
    have hder := natDegree_derivative_le (B * c)
    dsimp [bound]
    omega
  have h8 : (derivative d).natDegree < bound := by
    dsimp [bound]
    compute_degree
    omega
  have h1s := deepGap_natDegree_smul_lt68 (-2 : k) h1
  have h2s := deepGap_natDegree_smul_lt68 (-2 / 3 : k) h2
  have h3s := deepGap_natDegree_smul_lt68 (6 : k) h3
  have h4s := deepGap_natDegree_smul_lt68 (6 : k) h4
  have h5s := deepGap_natDegree_smul_lt68 (-18 : k) h5
  have hcore := deepGap_natDegree_add_lt
    (deepGap_natDegree_add_lt
      (deepGap_natDegree_add_lt (deepGap_natDegree_add_lt h1s h2s) h3s) h4s) h5s
  have hcores := deepGap_natDegree_smul_lt68 (-4 / 27 : k) hcore
  have h6s := deepGap_natDegree_smul_lt68 (1 / 6 * i4 : k) h6
  have h7s := deepGap_natDegree_smul_lt68 (4 / 3 * gamma : k) h7
  have h8s := deepGap_natDegree_smul_lt68 (2 * epsilon : k) h8
  simp only [fiveRadiusReducedRowTwoRestPolynomial68]
  exact deepGap_natDegree_add_lt
    (deepGap_natDegree_sub_lt (deepGap_natDegree_sub_lt hcores h6s) h7s) h8s

set_option maxHeartbeats 4000000 in
theorem derivative_quarterSquare_add_coeff_zetaWall68
    (A c : k[X]) (n g : ℕ) (hn : 0 < n) (hwall : 2 * g = 5 * n)
    (hA : A.natDegree ≤ 2 * n) (hc : c.natDegree ≤ 4 * n - g) :
    (derivative ((1 / 4 : k) • A ^ 2 + c)).coeff (4 * n - 1) =
      (n : k) * A.coeff (2 * n) ^ 2 := by
  have hA2 := coeff_pow_at_bound68 A (2 * n) 2 hA
  have hiA : 2 * (2 * n) = 4 * n := by omega
  rw [hiA] at hA2
  have hclt : c.natDegree < 4 * n := hc.trans_lt (by omega)
  have htop : (((1 / 4 : k) • A ^ 2 + c).coeff (4 * n)) =
      (1 / 4 : k) * A.coeff (2 * n) ^ 2 := by
    simp only [coeff_add, coeff_smul, smul_eq_mul, hA2,
      coeff_eq_zero_of_natDegree_lt hclt, add_zero]
  have hder := coeff_derivative_at_bound68
    ((1 / 4 : k) • A ^ 2 + c) (4 * n) (by omega)
  rw [htop] at hder
  rw [show 4 * n - 1 = (4 * n) - 1 by rfl, hder]
  push_cast
  ring

set_option maxHeartbeats 4000000 in
/-- On the mixed wall, reduced row two has a unique `zeta` coefficient and
therefore kills `zeta`. -/
theorem fiveRadiusReducedRowTwo_forces_zeta_at_wall68
    (gamma epsilon zeta i4 : k) (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hwall : 2 * g = 5 * n) (htie : 2 * h = 9 * n)
    (ha : A.coeff (2 * n) ≠ 0)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hrow : fiveRadiusReducedRowTwoPolynomial68
      gamma epsilon zeta i4 A B c d e = 0) :
    zeta = 0 := by
  have hcoeff := congrArg (fun p : k[X] => p.coeff (4 * n - 1)) hrow
  rw [fiveRadiusReducedRowTwoPolynomial68_eq_rest_add, coeff_add,
    coeff_eq_zero_of_natDegree_lt
      (fiveRadiusReducedRowTwoRestPolynomial68_degree_lt_zetaWall
        gamma epsilon i4 A B c d e n g h hn hwall htie hA hB hc hd he),
    coeff_smul, smul_eq_mul,
    derivative_quarterSquare_add_coeff_zetaWall68 A c n g hn hwall hA hc,
    coeff_zero, zero_add] at hcoeff
  exact (mul_eq_zero.mp hcoeff).resolve_right
    (mul_ne_zero (Nat.cast_ne_zero.mpr hn.ne') (pow_ne_zero 2 ha))

/-- The exact `zeta` wall is not exceptional after row two: it is the same
ordinary nonzero discriminant packet as the strict cells. -/
theorem fiveRadiusResidualZetaWall_ordinary68
    (gamma epsilon zeta i4 : k) (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hwall : 2 * g = 5 * n) (htie : 2 * h = 9 * n)
    (ha : A.coeff (2 * n) ≠ 0)
    (hsupport : B.coeff (3 * n - g) ≠ 0 ∨ c.coeff (4 * n - g) ≠ 0)
    (hattained : d.coeff (5 * n - h) ≠ 0 ∨ e.coeff (6 * n - h) ≠ 0)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hface : FiveRadiusResidualZetaWallFace68
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (d.coeff (5 * n - h))
      (e.coeff (6 * n - h)) zeta)
    (hrow : fiveRadiusReducedRowTwoPolynomial68
      gamma epsilon zeta i4 A B c d e = 0) :
    zeta = 0 ∧
      B.coeff (3 * n - g) ≠ 0 ∧ c.coeff (4 * n - g) ≠ 0 ∧
      d.coeff (5 * n - h) ≠ 0 ∧ e.coeff (6 * n - h) ≠ 0 ∧
      A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
        3 * c.coeff (4 * n - g) ^ 2 = 0 := by
  have hzeta := fiveRadiusReducedRowTwo_forces_zeta_at_wall68
    gamma epsilon zeta i4 A B c d e n g h hn hwall htie ha
    hA hB hc hd he hrow
  have hordinary : SecondaryResidualBetweenFace68
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (d.coeff (5 * n - h))
      (e.coeff (6 * n - h)) := by
    constructor
    · have h := hface.four
      rw [hzeta, zero_mul, add_zero] at h
      exact (mul_eq_zero.mp h).resolve_left (by norm_num)
    · exact hface.three
  have hclass := secondaryResidualBetweenFace68_classify_of_support
    (A.coeff (2 * n)) (B.coeff (3 * n - g))
    (c.coeff (4 * n - g)) (d.coeff (5 * n - h))
    (e.coeff (6 * n - h)) ha hsupport hattained hordinary
  exact ⟨hzeta, hclass⟩

/-- Uniform finite packet for all three cells below `h=5n`. -/
structure FiveRadiusResidualEndgamePacket68
    (gamma epsilon zeta i4 : k) (A B c d e : k[X])
    (n g h : ℕ) : Prop where
  b_ne : B.coeff (3 * n - g) ≠ 0
  c_ne : c.coeff (4 * n - g) ≠ 0
  d_ne : d.coeff (5 * n - h) ≠ 0
  e_ne : e.coeff (6 * n - h) ≠ 0
  discriminant : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
    3 * c.coeff (4 * n - g) ^ 2 = 0
  row_two : fiveRadiusReducedRowTwoPolynomial68
    gamma epsilon zeta i4 A B c d e = 0
  zeta_cell : 2 * h < 9 * n ∨ (9 * n ≤ 2 * h ∧ zeta = 0)

set_option maxHeartbeats 24000000 in
/-- Source-facing strengthening of the residual descent: the equality wall
is absorbed into the ordinary packet, and every `h<5n` cell carries the
exact reduced row-two equation. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepFiveRadiusResidualEndgame68
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
      2 * g = 5 * n) :
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
    l = 0 ∧ beta = 0 ∧ delta = 0 ∧ g < h ∧
      d.natDegree ≤ 5 * n - h ∧ ee.natDegree ≤ 6 * n - h ∧
      (Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0) ∧
      ((d = 0 ∧ ee = 0) ∨
        (h < 5 * n ∧ ∃ i4 : k,
          FiveRadiusResidualEndgamePacket68 gamma epsilon zeta i4
            Ae Be ce d ee n g h) ∨
        (5 * n ≤ h ∧
          (d.coeff (5 * n - h) ≠ 0 ∨ ee.coeff (6 * n - h) ≠ 0))) := by
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
  have old :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepFiveRadiusResidualDescent68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys hwall
  change l = 0 ∧ beta = 0 ∧ delta = 0 ∧ g < h ∧
      d.natDegree ≤ 5 * n - h ∧ ee.natDegree ≤ 6 * n - h ∧
      (Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0) ∧ _ at old
  refine ⟨old.1, old.2.1, old.2.2.1, old.2.2.2.1,
    old.2.2.2.2.1, old.2.2.2.2.2.1, old.2.2.2.2.2.2.1, ?_⟩
  rcases old.2.2.2.2.2.2.2 with hzero | hlt | hge
  · exact Or.inl hzero
  · right; left
    rcases hlt with ⟨hlt, hcells⟩
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
    have ha : Ae.coeff (2 * n) ≠ 0 := by
      simpa only [n, Ae] using core.2.2.2.2.2
    have hA : Ae.natDegree ≤ 2 * n := by
      have hAe : Ae.natDegree = 2 * n := by
        simpa only [n, Ae, Be, Ce, De, Ee] using drop.1
      omega
    have hB := secondary.2.1
    have hc := secondary.2.2.1
    have hd := old.2.2.2.2.1
    have he := old.2.2.2.2.2.1
    have hsupport := old.2.2.2.2.2.2.1
    have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
      simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
    have hErec : Ee = (1 / 27 : k) • Ae ^ 3 +
        (1 / 3 : k) • (Ae * ce) + ee := by
      simpa only [ce, ee] using
        cubicEDefectPolynomial68_eq_cubicCoordinates Ae Ce Ee
    have hDrec : De = (1 / 3 : k) • (Ae * Be) + d := by
      simpa only [d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
    obtain ⟨i4, hi4⟩ := hsys.firstFour
    have hi4e : firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
        Ae Be Ce De Ee = C i4 := by
      simpa only [Ae, Be, Ce, De, Ee] using
        expand_firstIntegralFourPolynomial68_of_eq
          l beta gamma delta epsilon zeta i4 A B C0 D E hi4
    have hi4c := hi4e
    rw [hCrec, hErec, firstIntegralFourPolynomial68_cubicCoordinates,
      hDrec, old.1, old.2.1, old.2.2.1] at hi4c
    have h2e : lowerRowTwoPolynomial68
        (integratedSPolynomial68 l alpha beta delta Ae Be Ce De)
        (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
        (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
        (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
          Ae Be Ce De Ee) Be Ce De Ee = 0 := by
      simpa only [Ae, Be, Ce, De, Ee] using
        expand_lowerRowTwoPolynomial68_of_system
          l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
    rw [hCrec, hDrec, hErec, old.1, old.2.1, old.2.2.1] at h2e
    have hrow := polynomialSecondaryResidualRowTwo68
      0 alpha 0 gamma 0 epsilon zeta eta Ae Be ce d ee h2e
    have hreduced := fiveRadiusReducedRowTwoPolynomial68_eq_zero
      alpha gamma epsilon zeta eta i4 Ae Be ce d ee hi4c hrow
    refine ⟨hlt, i4, ?_⟩
    rcases hcells with hbelow | htie | habove
    · exact
        { b_ne := hbelow.2.1
          c_ne := hbelow.2.2.1
          d_ne := hbelow.2.2.2.1
          e_ne := hbelow.2.2.2.2.1
          discriminant := hbelow.2.2.2.2.2
          row_two := hreduced
          zeta_cell := Or.inl hbelow.1 }
    · have hordinary := fiveRadiusResidualZetaWall_ordinary68
        gamma epsilon zeta i4 Ae Be ce d ee n g h hn hwall htie.1 ha
        hsupport htie.2.1 hA hB hc hd he htie.2.2 hreduced
      exact
        { b_ne := hordinary.2.1
          c_ne := hordinary.2.2.1
          d_ne := hordinary.2.2.2.1
          e_ne := hordinary.2.2.2.2.1
          discriminant := hordinary.2.2.2.2.2
          row_two := hreduced
          zeta_cell := Or.inr ⟨htie.1.symm.le, hordinary.1⟩ }
    · exact
        { b_ne := habove.2.2.1
          c_ne := habove.2.2.2.1
          d_ne := habove.2.2.2.2.1
          e_ne := habove.2.2.2.2.2.1
          discriminant := habove.2.2.2.2.2.2
          row_two := hreduced
          zeta_cell := Or.inr ⟨habove.1.le, habove.2.1⟩ }
  · exact Or.inr (Or.inr hge)

#print axioms fiveRadiusReducedRowTwoPolynomial68
#print axioms polynomialFiveRadiusReducedRowTwo68
#print axioms fiveRadiusReducedRowTwo_forces_zeta_at_wall68
#print axioms fiveRadiusResidualZetaWall_ordinary68
#print axioms FiveRadiusResidualEndgamePacket68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepFiveRadiusResidualEndgame68

end LaterDeepFiveRadiusResidualEndgame68

end Max11DegreeRoutes
