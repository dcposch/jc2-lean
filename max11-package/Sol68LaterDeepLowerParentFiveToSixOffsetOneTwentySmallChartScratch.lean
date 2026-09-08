import Sol68LaterDeepLowerParentFiveToSixOffsetOneTwentyScratch

/-! # The aligned offset-120 small chart

At `(N,G)=(2,6)`, the second-jet I4 load is exactly `zeta*a` and the
I3 load is zero.  The next independent row-zero coefficient is degree
`11`; it controls the product of the old nonzero edge pair.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerParentFiveToSixOffsetOneTwentySmallChart68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 30000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- First reflected jet of a product of four bounded polynomials. -/
theorem coeff_mul_mul_mul_at_reflect_one68
    (p q r s : k[X]) (u v w z : ℕ)
    (hp : p.natDegree ≤ u) (hq : q.natDegree ≤ v)
    (hr : r.natDegree ≤ w) (hs : s.natDegree ≤ z)
    (hsum : 1 ≤ u + v + w + z) :
    (p * q * r * s).coeff (u + v + w + z - 1) =
      (p.reflect u).coeff 0 * (q.reflect v).coeff 0 *
          (r.reflect w).coeff 0 * (s.reflect z).coeff 1 +
        (p.reflect u).coeff 0 * (q.reflect v).coeff 0 *
          (r.reflect w).coeff 1 * (s.reflect z).coeff 0 +
        (p.reflect u).coeff 0 * (q.reflect v).coeff 1 *
          (r.reflect w).coeff 0 * (s.reflect z).coeff 0 +
        (p.reflect u).coeff 1 * (q.reflect v).coeff 0 *
          (r.reflect w).coeff 0 * (s.reflect z).coeff 0 := by
  have hpq : (p * q).natDegree ≤ u + v :=
    natDegree_mul_le_of_le hp hq
  have hpqr : (p * q * r).natDegree ≤ u + v + w :=
    natDegree_mul_le_of_le hpq hr
  have h := congrArg (fun t : k[X] => t.coeff 1)
    (reflect_mul (p * q * r) s hpqr hs)
  rw [coeff_reflect, revAt_le hsum, mul_coeff_one,
    reflect_mul (p * q) r hpq hr, mul_coeff_zero, mul_coeff_one,
    reflect_mul p q hp hq, mul_coeff_zero, mul_coeff_one] at h
  linear_combination h

/-- Exact homogeneous row-zero coefficient at degree `11` in the small
chart. -/
theorem secondaryResidualRowZeroPolynomial68_coeff_eleven_smallChart68
    (A B c d e : k[X])
    (hA : A.natDegree ≤ 4) (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ 2) (hd : d.natDegree ≤ 3)
    (he : e.natDegree ≤ 5) :
    (secondaryResidualRowZeroPolynomial68 A B c d e).coeff 11 =
      (-4 / 27 : k) * A.coeff 4 *
        (7 * A.coeff 3 * (B.coeff 0 * e.coeff 5 +
            c.coeff 2 * d.coeff 3) +
          4 * A.coeff 4 * (B.coeff 0 * e.coeff 4 +
            c.coeff 1 * d.coeff 3 + c.coeff 2 * d.coeff 2) +
          12 * d.coeff 3 * e.coeff 5) := by
  have hderA : (derivative A).natDegree ≤ 3 := by
    compute_degree
    omega
  have hB1 : B.coeff 1 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hB.trans_lt (by norm_num))
  have h1 := coeff_mul_mul_mul_at_reflect_one68 A (derivative A) B e
    4 3 0 5 hA hderA hB he (by norm_num)
  norm_num [coeff_reflect, coeff_derivative, hB1] at h1
  rw [revAt_eq_self_of_lt (by norm_num : 0 < 1), hB1] at h1
  simp only [mul_zero, zero_mul, add_zero] at h1
  have h1' : (A * derivative A * B * e).coeff 11 =
      4 * A.coeff 4 ^ 2 * B.coeff 0 * e.coeff 4 +
        7 * A.coeff 4 * A.coeff 3 * B.coeff 0 * e.coeff 5 := by
    linear_combination h1
  have h2 := coeff_mul_mul_mul_at_reflect_one68 A (derivative A) c d
    4 3 2 3 hA hderA hc hd (by norm_num)
  norm_num [coeff_reflect, coeff_derivative] at h2
  have h2' : (A * derivative A * c * d).coeff 11 =
      4 * A.coeff 4 ^ 2 * c.coeff 2 * d.coeff 2 +
        4 * A.coeff 4 ^ 2 * c.coeff 1 * d.coeff 3 +
        7 * A.coeff 4 * A.coeff 3 * c.coeff 2 * d.coeff 3 := by
    linear_combination h2
  have h6 := coeff_mul_mul_at_bounds68 (derivative A) d e 3 3 5
    hderA hd he
  norm_num [coeff_derivative] at h6
  have h6' : (derivative A * d * e).coeff 11 =
      4 * A.coeff 4 * d.coeff 3 * e.coeff 5 := by
    linear_combination h6
  have hlow3 : (A * B ^ 2 * derivative d).natDegree < 11 := by
    compute_degree
    omega
  have hlow4 : (A * B * derivative B * d).natDegree < 11 := by
    compute_degree
    omega
  have hlow5 : (derivative A * B * c ^ 2).natDegree < 11 := by
    compute_degree
    omega
  have hlow7 : (B * c * derivative e).natDegree < 11 := by
    compute_degree
    omega
  have hlow8 : (B * d * derivative d).natDegree < 11 := by
    compute_degree
    omega
  have hlow9 : (derivative B * d ^ 2).natDegree < 11 := by
    compute_degree
    omega
  have hlow10 : (c * derivative c * d).natDegree < 11 := by
    compute_degree
    omega
  simp only [secondaryResidualRowZeroPolynomial68, coeff_smul, coeff_add,
    coeff_sub, h1', h2', h6',
    coeff_eq_zero_of_natDegree_lt hlow3,
    coeff_eq_zero_of_natDegree_lt hlow4,
    coeff_eq_zero_of_natDegree_lt hlow5,
    coeff_eq_zero_of_natDegree_lt hlow7,
    coeff_eq_zero_of_natDegree_lt hlow8,
    coeff_eq_zero_of_natDegree_lt hlow9,
    coeff_eq_zero_of_natDegree_lt hlow10, smul_eq_mul]
  ring

/-- The degree-`11` load is exactly `(4/9)*zeta*a^3`; the gamma pieces
cancel before any use of the singular face. -/
theorem cubicLoadRowZeroPolynomial68_coeff_eleven_smallChart68
    (alpha gamma epsilon zeta eta : k) (A B c d e : k[X])
    (hA : A.natDegree ≤ 4) (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ 2) (hd : d.natDegree ≤ 3)
    (he : e.natDegree ≤ 5) :
    (cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff 11 =
      (4 / 9 : k) * zeta * A.coeff 4 ^ 3 := by
  let D0 : k[X] := (1 / 3 : k) • (A * B) + d
  let E0 : k[X] :=
    (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
  let Ur : k[X] := (2 / 3 * gamma : k) • B + C zeta
  let W : k[X] :=
    (1 / 9 * gamma : k) • A ^ 2 + (2 / 3 * gamma : k) • c +
      (1 / 3 * epsilon : k) • A + C eta
  have hloadEq :
      cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
        A B c D0 e = Ur * derivative E0 - D0 * derivative W := by
    apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
    simp only [cubicLoadRowZeroPolynomial68, cubicLoadUPolynomial68,
      cubicLoadVPolynomial68, D0, E0, Ur, W,
      zero_mul, zero_smul, smul_zero, add_zero, zero_add, sub_zero,
      derivative_add, derivative_sub, derivative_mul, derivative_pow,
      derivative_smul, derivative_C, one_mul, Polynomial.smul_eq_C_mul,
      map_add, map_sub, map_mul, map_pow, map_neg, map_zero,
      RatFunc.algebraMap_C, map_div₀, map_ofNat, map_natCast, map_one]
    ring
  have hDdeg : D0.natDegree ≤ 4 := by
    simp only [D0]
    compute_degree
    omega
  have hEdeg : E0.natDegree ≤ 12 := by
    simp only [E0]
    compute_degree
    omega
  have hUrdeg : Ur.natDegree ≤ 0 := by
    simp only [Ur]
    compute_degree
    omega
  have hWdeg : W.natDegree ≤ 8 := by
    simp only [W]
    compute_degree
    omega
  have hA3 := coeff_pow_at_bound68 A 4 3 hA
  norm_num at hA3
  have hAclt : (A * c).natDegree < 12 := by compute_degree; omega
  have helt : e.natDegree < 12 := he.trans_lt (by norm_num)
  have hEtop : E0.coeff 12 = (1 / 27 : k) * A.coeff 4 ^ 3 := by
    simp only [E0, coeff_add, coeff_smul, smul_eq_mul, hA3,
      coeff_eq_zero_of_natDegree_lt hAclt,
      coeff_eq_zero_of_natDegree_lt helt, mul_zero, add_zero]
  have hAB := coeff_mul_at_bounds68 A B 4 0 hA hB
  norm_num at hAB
  have hdlt : d.natDegree < 4 := hd.trans_lt (by norm_num)
  have hDtop : D0.coeff 4 =
      (1 / 3 : k) * A.coeff 4 * B.coeff 0 := by
    simp only [D0, coeff_add, coeff_smul, smul_eq_mul, hAB,
      coeff_eq_zero_of_natDegree_lt hdlt]
    ring
  have hA2 := coeff_pow_at_bound68 A 4 2 hA
  norm_num at hA2
  have hclt : c.natDegree < 8 := hc.trans_lt (by norm_num)
  have hAlt : A.natDegree < 8 := hA.trans_lt (by norm_num)
  have hCeta : (C eta : k[X]).coeff 8 = 0 := by simp [coeff_C]
  have hWtop : W.coeff 8 =
      (1 / 9 * gamma : k) * A.coeff 4 ^ 2 := by
    simp only [W, coeff_add, coeff_smul, smul_eq_mul, hA2,
      coeff_eq_zero_of_natDegree_lt hclt,
      coeff_eq_zero_of_natDegree_lt hAlt, hCeta, mul_zero, add_zero]
  have hUrtop : Ur.coeff 0 =
      (2 / 3 * gamma : k) * B.coeff 0 + zeta := by
    simp only [Ur, coeff_add, coeff_smul, smul_eq_mul, coeff_C_zero]
  have h1 := coeff_mul_derivative_at_bounds68 Ur E0 0 12
    (by norm_num) hUrdeg hEdeg
  norm_num at h1
  have h2 := coeff_mul_derivative_at_bounds68 D0 W 4 8
    (by norm_num) hDdeg hWdeg
  norm_num at h2
  change (cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
      A B c D0 e).coeff 11 = _
  rw [hloadEq, coeff_sub, h1, h2, hUrtop, hEtop, hDtop, hWtop]
  norm_num
  ring

/-- The row-zero jet and second-jet I4 equation eliminate the remaining
load product exactly. -/
theorem fiveToSix_smallChart_rowZero_elimination68
    (a a₁ b c c₁ x y u v zeta : k)
    (ha : a ≠ 0)
    (hface : b * y + c * x = 0)
    (hfour : (8 / 3 : k) * (b * v + c * u + c₁ * x) + zeta * a = 0)
    (hrow : (-4 / 27 : k) * a *
          (7 * a₁ * (b * y + c * x) +
            4 * a * (b * v + c₁ * x + c * u) + 12 * x * y) +
          (4 / 9 : k) * zeta * a ^ 3 = 0) :
    3 * zeta * a ^ 2 = 8 * x * y := by
  have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha
  have hfact : a * (3 * zeta * a ^ 2 - 8 * x * y) = 0 := by
    linear_combination (9 / 2 : k) * hrow +
      a ^ 2 * hfour + (14 / 3 : k) * a * a₁ * hface
  exact sub_eq_zero.mp ((mul_eq_zero.mp hfact).resolve_left ha)

/-- Combining row zero with the singular second-jet compatibility removes
`zeta` and yields the exact remaining first-jet constraint. -/
theorem fiveToSix_smallChart_firstJet_constraint68
    (a a₁ b c c₁ x y zeta : k)
    (ha : a ≠ 0) (hb : b ≠ 0) (hx : x ≠ 0)
    (hface : b * y + c * x = 0)
    (hdisc : a * b ^ 2 + 3 * c ^ 2 = 0)
    (hload : 3 * zeta * a ^ 2 = 8 * x * y)
    (hcompat : 4 * x *
        (3 * b * x - 2 * a₁ * b ^ 2 - 12 * c * c₁) =
          9 * c * (zeta * a)) :
    b * x = 2 * a₁ * b ^ 2 + 12 * c * c₁ := by
  have hbracketProd : 4 * x *
      (a * (3 * b * x - 2 * a₁ * b ^ 2 - 12 * c * c₁) -
        6 * c * y) = 0 := by
    linear_combination a * hcompat + 3 * c * hload
  have hfourx : 4 * x ≠ 0 := mul_ne_zero (by norm_num) hx
  have hbracket :
      a * (3 * b * x - 2 * a₁ * b ^ 2 - 12 * c * c₁) -
        6 * c * y = 0 :=
    (mul_eq_zero.mp hbracketProd).resolve_left hfourx
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  have hscaled : a * b *
      (b * x - 2 * a₁ * b ^ 2 - 12 * c * c₁) = 0 := by
    linear_combination b * hbracket - 2 * x * hdisc + 6 * c * hface
  have hz := (mul_eq_zero.mp hscaled).resolve_left hab
  linear_combination hz

set_option maxHeartbeats 12000000 in
/-- Source-facing closure of the `(N,G)=(2,6)` second jet.  It preserves
the two literal first-integral equations, proves the load is nonzero, and
removes it from the compatibility equation. -/
theorem fiveToSix_aligned_secondJet_smallChart_source_packet68
    (alpha gamma epsilon zeta eta i4 i3 : k) (A B c d e : k[X])
    (hA : A.natDegree ≤ 4) (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ 2) (hd : d.natDegree ≤ 3)
    (he : e.natDegree ≤ 5)
    (ha : A.coeff 4 ≠ 0) (hb : B.coeff 0 ≠ 0)
    (hx : d.coeff 3 ≠ 0) (hy : e.coeff 5 ≠ 0)
    (hface : B.coeff 0 * e.coeff 5 + c.coeff 2 * d.coeff 3 = 0)
    (hdisc : A.coeff 4 * B.coeff 0 ^ 2 + 3 * c.coeff 2 ^ 2 = 0)
    (hi4 : cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon zeta
        A B c ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hi3 : cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon zeta
        A B c ((1 / 3 : k) • (A * B) + d) e = C i3)
    (hrow : (secondaryResidualRowZeroPolynomial68 A B c d e +
        cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
          A B c ((1 / 3 : k) • (A * B) + d) e).coeff 11 = 0) :
    ((8 / 3 : k) *
        (B.coeff 0 * e.coeff 4 + c.coeff 2 * d.coeff 2 +
          c.coeff 1 * d.coeff 3) + zeta * A.coeff 4 = 0) ∧
      (-A.coeff 4 * B.coeff 0 * d.coeff 2 -
          A.coeff 3 * B.coeff 0 * d.coeff 3 +
          3 * c.coeff 2 * e.coeff 4 +
          3 * c.coeff 1 * e.coeff 5 +
          (3 / 2 : k) * d.coeff 3 ^ 2 = 0) ∧
      3 * zeta * A.coeff 4 ^ 2 = 8 * d.coeff 3 * e.coeff 5 ∧
      zeta ≠ 0 ∧
      B.coeff 0 * d.coeff 3 =
        2 * A.coeff 3 * B.coeff 0 ^ 2 +
          12 * c.coeff 2 * c.coeff 1 := by
  have hd4 : d.coeff 4 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hd.trans_lt (by norm_num))
  have he6 : e.coeff 6 = 0 :=
    coeff_eq_zero_of_natDegree_lt (he.trans_lt (by norm_num))
  have hB1 : B.coeff 1 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hB.trans_lt (by norm_num))
  have hB4 : B.coeff 4 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hB.trans_lt (by norm_num))
  have hB6 : B.coeff 6 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hB.trans_lt (by norm_num))
  have hc6 : c.coeff 6 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hc.trans_lt (by norm_num))
  have hB2deg : (B ^ 2).natDegree ≤ 0 := by compute_degree; omega
  have hB2six : (B ^ 2).coeff 6 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hB2deg.trans_lt (by norm_num))
  have hd0 : (d.reflect 4).coeff 0 = 0 := by
    norm_num [coeff_reflect, hd4]
  have he0 : (e.reflect 6).coeff 0 = 0 := by
    norm_num [coeff_reflect, he6]
  have hbr : (B.reflect 0).coeff 0 ≠ 0 := by
    simpa only [coeff_reflect, revAt_zero] using hb
  have hfaceR : (B.reflect 0).coeff 0 * (e.reflect 6).coeff 1 +
      (c.reflect 2).coeff 0 * (d.reflect 4).coeff 1 = 0 := by
    norm_num [coeff_reflect]
    exact hface
  have hdiscR : (A.reflect 4).coeff 0 * (B.reflect 0).coeff 0 ^ 2 +
      3 * (c.reflect 2).coeff 0 ^ 2 = 0 := by
    norm_num [coeff_reflect]
    exact hdisc
  have hp := fiveToSix_aligned_secondJet_source_packet68
    gamma epsilon zeta i4 i3 A B c d e 2 6 (by norm_num) (by norm_num)
    hA hB hc (hd.trans (by norm_num)) (he.trans (by norm_num))
    hd0 he0 hbr hfaceR hdiscR hi4 hi3
  dsimp only at hp
  norm_num [coeff_reflect, hd4, he6, hB4, hB6, hc6, hB2six] at hp
  rw [revAt_eq_self_of_lt (by norm_num : 0 < 1), hB1, zero_mul,
    add_zero] at hp
  obtain ⟨hfour, hthree, hcompat⟩ := hp
  simp only [mul_zero, zero_mul, add_zero, zero_add, sub_zero] at hthree hcompat
  have hthree' :
      -A.coeff 4 * B.coeff 0 * d.coeff 2 -
          A.coeff 3 * B.coeff 0 * d.coeff 3 +
          3 * c.coeff 2 * e.coeff 4 +
          3 * c.coeff 1 * e.coeff 5 +
          (3 / 2 : k) * d.coeff 3 ^ 2 = 0 := by
    linear_combination hthree
  have hres := secondaryResidualRowZeroPolynomial68_coeff_eleven_smallChart68
    A B c d e hA hB hc hd he
  have hload := cubicLoadRowZeroPolynomial68_coeff_eleven_smallChart68
    alpha gamma epsilon zeta eta A B c d e hA hB hc hd he
  rw [coeff_add, hres, hload] at hrow
  have hzetaEdge := fiveToSix_smallChart_rowZero_elimination68
    (A.coeff 4) (A.coeff 3) (B.coeff 0) (c.coeff 2) (c.coeff 1)
    (d.coeff 3) (e.coeff 5) (d.coeff 2) (e.coeff 4) zeta
    ha hface hfour hrow
  have hzeta : zeta ≠ 0 := by
    intro hz
    rw [hz] at hzetaEdge
    simp only [mul_zero, zero_mul] at hzetaEdge
    have h8xy : (8 : k) * (d.coeff 3 * e.coeff 5) = 0 := by
      calc
        (8 : k) * (d.coeff 3 * e.coeff 5) =
            8 * d.coeff 3 * e.coeff 5 := by ring
        _ = 0 := hzetaEdge.symm
    have hxy : d.coeff 3 * e.coeff 5 = 0 := by
      exact (mul_eq_zero.mp h8xy).resolve_left (by norm_num)
    exact (mul_ne_zero hx hy) hxy
  have hjet := fiveToSix_smallChart_firstJet_constraint68
    (A.coeff 4) (A.coeff 3) (B.coeff 0) (c.coeff 2) (c.coeff 1)
    (d.coeff 3) (e.coeff 5) zeta ha hb hx hface hdisc hzetaEdge hcompat
  exact ⟨hfour, hthree', hzetaEdge, hzeta, hjet⟩

#print axioms coeff_mul_mul_mul_at_reflect_one68
#print axioms secondaryResidualRowZeroPolynomial68_coeff_eleven_smallChart68
#print axioms cubicLoadRowZeroPolynomial68_coeff_eleven_smallChart68
#print axioms fiveToSix_smallChart_rowZero_elimination68
#print axioms fiveToSix_smallChart_firstJet_constraint68
#print axioms fiveToSix_aligned_secondJet_smallChart_source_packet68

end LaterDeepLowerParentFiveToSixOffsetOneTwentySmallChart68

end Max11DegreeRoutes
