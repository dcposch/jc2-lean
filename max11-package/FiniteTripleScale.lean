import FiniteDoubleBlowup

/-! # A generic positive common Hahn scale

The first transverse scale is a special case of a construction that
applies to any three regular Hahn series with vanishing residues.  This
file records that generic scale, so later double-root deviations `D`,
`B`, and `C` can be normalized without repeating the order-minimum
argument.
-/

noncomputable section

namespace GCD369CubeHahnRegular

/-- A first nonzero common scale of three regular Hahn series, normalized
by their exact shared positive Hahn order.  At least one of the three
normalized coefficients has nonzero residue. -/
structure TripleScale
    {k : Type*} [Field k] [CharZero k]
    (D B C : GCD369CubeHahnRegular k) where
  mu : ℚ
  hmu : 0 < mu
  Dn : GCD369CubeHahnRegular k
  Bn : GCD369CubeHahnRegular k
  Cn : GCD369CubeHahnRegular k
  hD : D = monomial mu hmu.le * Dn
  hB : B = monomial mu hmu.le * Bn
  hC : C = monomial mu hmu.le * Cn
  hleading :
    constantCoeff Dn ≠ 0 ∨
    constantCoeff Bn ≠ 0 ∨
    constantCoeff Cn ≠ 0

/-- If three regular series have vanishing residues and are not all zero,
they have a canonical first positive common order and a normalized
leading jet. -/
noncomputable def tripleScale
    {k : Type*} [Field k] [CharZero k]
    (D B C : GCD369CubeHahnRegular k)
    (hD0 : constantCoeff D = 0)
    (hB0 : constantCoeff B = 0)
    (hC0 : constantCoeff C = 0)
    (hnonzero : D ≠ 0 ∨ B ≠ 0 ∨ C ≠ 0) :
    TripleScale D B C := by
  let oD : WithTop ℚ := D.1.orderTop
  let oB : WithTop ℚ := B.1.orderTop
  let oC : WithTop ℚ := C.1.orderTop
  let o : WithTop ℚ := min (min oD oB) oC
  have hoD : o ≤ oD := by
    dsimp only [o]
    exact (min_le_left _ _).trans (min_le_left _ _)
  have hoB : o ≤ oB := by
    dsimp only [o]
    exact (min_le_left _ _).trans (min_le_right _ _)
  have hoC : o ≤ oC := by
    dsimp only [o]
    exact min_le_right _ _
  have hone : o ≠ ⊤ := by
    intro htop
    rcases hnonzero with hDz | hBz | hCz
    · have hD' : D.1 ≠ 0 := by
        intro hz
        apply hDz
        exact Subtype.ext hz
      have hoDtop : oD = ⊤ := top_unique (htop ▸ hoD)
      exact (HahnSeries.orderTop_ne_top.mpr hD') hoDtop
    · have hB' : B.1 ≠ 0 := by
        intro hz
        apply hBz
        exact Subtype.ext hz
      have hoBtop : oB = ⊤ := top_unique (htop ▸ hoB)
      exact (HahnSeries.orderTop_ne_top.mpr hB') hoBtop
    · have hC' : C.1 ≠ 0 := by
        intro hz
        apply hCz
        exact Subtype.ext hz
      have hoCtop : oC = ⊤ := top_unique (htop ▸ hoC)
      exact (HahnSeries.orderTop_ne_top.mpr hC') hoCtop
  let mu : ℚ := o.untop hone
  have hmu_coe : (↑mu : WithTop ℚ) = o := by
    exact WithTop.coe_untop o hone
  have hpD : (↑(0 : ℚ) : WithTop ℚ) < oD :=
    orderTop_pos_of_constantCoeff_zero D hD0
  have hpB : (↑(0 : ℚ) : WithTop ℚ) < oB :=
    orderTop_pos_of_constantCoeff_zero B hB0
  have hpC : (↑(0 : ℚ) : WithTop ℚ) < oC :=
    orderTop_pos_of_constantCoeff_zero C hC0
  have hopos : (↑(0 : ℚ) : WithTop ℚ) < o := by
    dsimp only [o]
    exact lt_min (lt_min hpD hpB) hpC
  have hmu_top : (↑(0 : ℚ) : WithTop ℚ) < (↑mu : WithTop ℚ) := by
    rw [hmu_coe]
    exact hopos
  have hmu : 0 < mu := WithTop.coe_lt_coe.mp hmu_top
  have hbD : (↑mu : WithTop ℚ) ≤ D.1.orderTop := by
    change (↑mu : WithTop ℚ) ≤ oD
    rw [hmu_coe]
    exact hoD
  have hbB : (↑mu : WithTop ℚ) ≤ B.1.orderTop := by
    change (↑mu : WithTop ℚ) ≤ oB
    rw [hmu_coe]
    exact hoB
  have hbC : (↑mu : WithTop ℚ) ≤ C.1.orderTop := by
    change (↑mu : WithTop ℚ) ≤ oC
    rw [hmu_coe]
    exact hoC
  let Dn := shift D mu hbD
  let Bn := shift B mu hbB
  let Cn := shift C mu hbC
  refine {
    mu := mu
    hmu := hmu
    Dn := Dn
    Bn := Bn
    Cn := Cn
    hD := ?_
    hB := ?_
    hC := ?_
    hleading := ?_
  }
  · exact (monomial_mul_shift D mu hmu.le hbD).symm
  · exact (monomial_mul_shift B mu hmu.le hbB).symm
  · exact (monomial_mul_shift C mu hmu.le hbC).symm
  · have hchoice : o = oD ∨ o = oB ∨ o = oC := by
      rcases min_choice (min oD oB) oC with hout | hout
      · rcases min_choice oD oB with hin | hin
        · exact Or.inl (by simpa only [o] using hout.trans hin)
        · exact Or.inr (Or.inl (by simpa only [o] using hout.trans hin))
      · exact Or.inr (Or.inr (by simpa only [o] using hout))
    rcases hchoice with hDord | hBord | hCord
    · left
      have horder : D.1.orderTop = (↑mu : WithTop ℚ) := by
        change oD = (↑mu : WithTop ℚ)
        exact (hmu_coe.trans hDord).symm
      simpa only [Dn] using (constantCoeff_shift_ne_zero D mu horder)
    · right; left
      have horder : B.1.orderTop = (↑mu : WithTop ℚ) := by
        change oB = (↑mu : WithTop ℚ)
        exact (hmu_coe.trans hBord).symm
      simpa only [Bn] using (constantCoeff_shift_ne_zero B mu horder)
    · right; right
      have horder : C.1.orderTop = (↑mu : WithTop ℚ) := by
        change oC = (↑mu : WithTop ℚ)
        exact (hmu_coe.trans hCord).symm
      simpa only [Cn] using (constantCoeff_shift_ne_zero C mu horder)

end GCD369CubeHahnRegular

#print axioms GCD369CubeHahnRegular.tripleScale
