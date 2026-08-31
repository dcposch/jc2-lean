import Sol610ScaleTwoDegreeZeroPostCollapseSourceBridgeScratch

/-! # Coordinate bridge for the `(6,10)` degree-zero source primitive

This identifies the compact post-collapse primitive with the literal
coefficients of the normalized depressed sextic/decic.  It is the algebraic
link needed before the simple-pole source theorem can consume the exact
order-`69` head.
-/

noncomputable section

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000

section DegreeZeroPostCollapseCoordinates610

variable {F : Type*} [Field F] [CharZero F]

set_option maxHeartbeats 800000000 in
theorem degreeZeroPostCollapsePrimitive610_eq_depressed
    (h w1 a42 p32 p21 p1 p0 b9 s2 u2 b63 q53 q41 q3 q2 q1 lambda : F)
    (hh : h ≠ 0)
    (hN : 5 * (h ^ 5 * w1) * h ^ 4 - 3 * b9 = lambda * h ^ 9) :
    degreeZeroPostCollapsePrimitive610 h w1 a42 p32 p21 p1 p0 s2 u2
        b63 q53 q41 q3 q2 q1 lambda =
      degreeZeroPrimitive610
        (depressedL610 h (sexticDepressionR610 h (h ^ 5 * w1)) b9)
        (depressedA610 h (sexticDepressionR610 h (h ^ 5 * w1))
          (h ^ 5 * w1) (h ^ 4 * a42))
        (depressedB610 h (sexticDepressionR610 h (h ^ 5 * w1))
          (h ^ 5 * w1) (h ^ 4 * a42) (h ^ 2 * p32))
        (depressedC610 h (sexticDepressionR610 h (h ^ 5 * w1))
          (h ^ 5 * w1) (h ^ 4 * a42) (h ^ 2 * p32) (h * p21))
        (depressedD610 h (sexticDepressionR610 h (h ^ 5 * w1))
          (h ^ 5 * w1) (h ^ 4 * a42) (h ^ 2 * p32) (h * p21) p1)
        (depressedE610 h (sexticDepressionR610 h (h ^ 5 * w1))
          (h ^ 5 * w1) (h ^ 4 * a42) (h ^ 2 * p32) (h * p21) p1 p0)
        (depressedP610 h (sexticDepressionR610 h (h ^ 5 * w1))
          b9 (h ^ 8 * s2))
        (depressedQ610 h (sexticDepressionR610 h (h ^ 5 * w1))
          b9 (h ^ 8 * s2) (h ^ 6 * u2))
        (depressedR610 h (sexticDepressionR610 h (h ^ 5 * w1))
          b9 (h ^ 8 * s2) (h ^ 6 * u2) (h ^ 5 * b63))
        (depressedS610 h (sexticDepressionR610 h (h ^ 5 * w1))
          b9 (h ^ 8 * s2) (h ^ 6 * u2) (h ^ 5 * b63) (h ^ 3 * q53))
        (depressedT610 h (sexticDepressionR610 h (h ^ 5 * w1))
          b9 (h ^ 8 * s2) (h ^ 6 * u2) (h ^ 5 * b63) (h ^ 3 * q53)
          (h * q41))
        (depressedU610 h (sexticDepressionR610 h (h ^ 5 * w1))
          b9 (h ^ 8 * s2) (h ^ 6 * u2) (h ^ 5 * b63) (h ^ 3 * q53)
          (h * q41) q3)
        (depressedV610 h (sexticDepressionR610 h (h ^ 5 * w1))
          b9 (h ^ 8 * s2) (h ^ 6 * u2) (h ^ 5 * b63) (h ^ 3 * q53)
          (h * q41) q3 q2)
        (depressedW610 h (sexticDepressionR610 h (h ^ 5 * w1))
          b9 (h ^ 8 * s2) (h ^ 6 * u2) (h ^ 5 * b63) (h ^ 3 * q53)
          (h * q41) q3 q2 q1) 0 := by
  have hL :
      depressedL610 h (sexticDepressionR610 h (h ^ 5 * w1)) b9 =
        -lambda / 3 :=
    depressedL610_eq_of_ninthPower h (h ^ 5 * w1) b9 lambda hh hN
  have hA :
      depressedA610 h (sexticDepressionR610 h (h ^ 5 * w1))
          (h ^ 5 * w1) (h ^ 4 * a42) =
        postCollapseNuA610 w1 a42 / 12 := by
    rw [depressedA610_eq_cleared]
    field_simp [hh]
    simp only [postCollapseNuA610]
    ring
    exact hh
  have hB :
      depressedB610 h (sexticDepressionR610 h (h ^ 5 * w1))
          (h ^ 5 * w1) (h ^ 4 * a42) (h ^ 2 * p32) =
        postCollapseNuB610 h w1 a42 p32 / (54 * h) := by
    rw [depressedB610_eq_cleared]
    field_simp [hh]
    simp only [postCollapseNuB610]
    ring
    exact hh
  have hC :
      depressedC610 h (sexticDepressionR610 h (h ^ 5 * w1))
          (h ^ 5 * w1) (h ^ 4 * a42) (h ^ 2 * p32) (h * p21) =
        postCollapseNuC610 h w1 a42 p32 p21 / (144 * h) := by
    rw [depressedC610_eq_cleared]
    field_simp [hh]
    simp only [postCollapseNuC610]
    ring
    exact hh
  have hD :
      depressedD610 h (sexticDepressionR610 h (h ^ 5 * w1))
          (h ^ 5 * w1) (h ^ 4 * a42) (h ^ 2 * p32) (h * p21) p1 =
        postCollapseNuD610 h w1 a42 p32 p21 p1 / (324 * h) := by
    rw [depressedD610_eq_cleared]
    field_simp [hh]
    simp only [postCollapseNuD610]
    ring
    exact hh
  have hE :
      depressedE610 h (sexticDepressionR610 h (h ^ 5 * w1))
          (h ^ 5 * w1) (h ^ 4 * a42) (h ^ 2 * p32) (h * p21) p1 p0 =
        postCollapseNuE610 h w1 a42 p32 p21 p1 p0 / (46656 * h) := by
    rw [depressedE610_eq_cleared]
    field_simp [hh]
    simp only [postCollapseNuE610]
    ring
    exact hh
  have hP :
      depressedP610 h (sexticDepressionR610 h (h ^ 5 * w1))
          b9 (h ^ 8 * s2) =
        postCollapseNuP610 w1 s2 lambda / 4 := by
    rw [depressedP610_eq_cleared_ninthPower _ _ _ _ _ hh hN]
    field_simp [hh]
    simp only [postCollapseNuP610]
    ring
  have hQ :
      depressedQ610 h (sexticDepressionR610 h (h ^ 5 * w1))
          b9 (h ^ 8 * s2) (h ^ 6 * u2) =
        postCollapseNuQ610 h w1 s2 u2 lambda / (9 * h) := by
    rw [depressedQ610_eq_cleared _ _ _ _ _ _ hh hN]
    field_simp [hh]
    simp only [postCollapseNuQ610]
    ring
  have hR :
      depressedR610 h (sexticDepressionR610 h (h ^ 5 * w1))
          b9 (h ^ 8 * s2) (h ^ 6 * u2) (h ^ 5 * b63) =
        postCollapseNuR610 h w1 s2 u2 b63 lambda / (432 * h) := by
    rw [depressedR610_eq_cleared _ _ _ _ _ _ _ hh hN]
    field_simp [hh]
    simp only [postCollapseNuR610]
    ring
  have hS :
      depressedS610 h (sexticDepressionR610 h (h ^ 5 * w1))
          b9 (h ^ 8 * s2) (h ^ 6 * u2) (h ^ 5 * b63) (h ^ 3 * q53) =
        postCollapseNuS610 h w1 s2 u2 b63 q53 lambda / (216 * h ^ 2) := by
    rw [depressedS610_eq_cleared _ _ _ _ _ _ _ _ hh hN]
    field_simp [hh]
    simp only [postCollapseNuS610]
    ring
  have hT :
      depressedT610 h (sexticDepressionR610 h (h ^ 5 * w1))
          b9 (h ^ 8 * s2) (h ^ 6 * u2) (h ^ 5 * b63) (h ^ 3 * q53)
          (h * q41) =
        postCollapseNuT610 h w1 s2 u2 b63 q53 q41 lambda /
          (7776 * h ^ 3) := by
    rw [depressedT610_eq_cleared _ _ _ _ _ _ _ _ _ hh hN]
    field_simp [hh]
    simp only [postCollapseNuT610]
    ring
  have hU :
      depressedU610 h (sexticDepressionR610 h (h ^ 5 * w1))
          b9 (h ^ 8 * s2) (h ^ 6 * u2) (h ^ 5 * b63) (h ^ 3 * q53)
          (h * q41) q3 =
        postCollapseNuU610 h w1 s2 u2 b63 q53 q41 q3 lambda /
          (11664 * h ^ 3) := by
    rw [depressedU610_eq_cleared _ _ _ _ _ _ _ _ _ _ hh hN]
    field_simp [hh]
    simp only [postCollapseNuU610]
    ring
  have hV :
      depressedV610 h (sexticDepressionR610 h (h ^ 5 * w1))
          b9 (h ^ 8 * s2) (h ^ 6 * u2) (h ^ 5 * b63) (h ^ 3 * q53)
          (h * q41) q3 q2 =
        postCollapseNuV610 h w1 s2 u2 b63 q53 q41 q3 q2 lambda /
          (186624 * h ^ 3) := by
    rw [depressedV610_eq_cleared _ _ _ _ _ _ _ _ _ _ _ hh hN]
    field_simp [hh]
    simp only [postCollapseNuV610]
    ring
  have hW :
      depressedW610 h (sexticDepressionR610 h (h ^ 5 * w1))
          b9 (h ^ 8 * s2) (h ^ 6 * u2) (h ^ 5 * b63) (h ^ 3 * q53)
          (h * q41) q3 q2 q1 =
        postCollapseNuW610 h w1 s2 u2 b63 q53 q41 q3 q2 q1 lambda /
          (5038848 * h ^ 3) := by
    rw [depressedW610_eq_cleared _ _ _ _ _ _ _ _ _ _ _ _ hh hN]
    field_simp [hh]
    simp only [postCollapseNuW610]
    ring
  rw [hL, hA, hB, hC, hD, hE, hP, hQ, hR, hS, hT, hU, hV, hW]
  rfl

#print axioms degreeZeroPostCollapsePrimitive610_eq_depressed

end DegreeZeroPostCollapseCoordinates610

end Max11DegreeRoutes
