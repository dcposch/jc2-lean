import Grok610ScaleZeroConeCascadePart04Scratch

open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section DegreeLemmas610

variable {k : Type*} [Field k] [CharZero k]

theorem natDegree_add8_le610
    {p1 p2 p3 p4 p5 p6 p7 p8 : k[X]} {d : ℕ}
    (h1 : p1.natDegree ≤ d) (h2 : p2.natDegree ≤ d)
    (h3 : p3.natDegree ≤ d) (h4 : p4.natDegree ≤ d)
    (h5 : p5.natDegree ≤ d) (h6 : p6.natDegree ≤ d)
    (h7 : p7.natDegree ≤ d) (h8 : p8.natDegree ≤ d) :
    (p1 + p2 + p3 + p4 + p5 + p6 + p7 + p8).natDegree ≤ d :=
  natDegree_add_le610
    (natDegree_add_le610
      (natDegree_add_le610
        (natDegree_add_le610
          (natDegree_add_le610
            (natDegree_add_le610 (natDegree_add_le610 h1 h2) h3) h4) h5)
        h6)
      h7)
    h8

end DegreeLemmas610

end Max11DegreeRoutes
