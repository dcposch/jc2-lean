import LowScale46DegreeCones

/-! # Exact common depression for the `(4,6)` source

This module performs the affine coefficient-field change `z=h*y+r` on raw
quartic and sextic polynomials whose leading coefficients are `h^4,h^6`.
For the quartic depression `r=a₃/(4h³)`, it proves the exact depressed forms
and identifies the sextic quintic coefficient with
`-(3*a₃*h²-2*b₅)/(2h⁵)`.  Thus the aligned branch has `L=0`, while
`N=lambda*h⁵` has the constant mismatch `L=-lambda/2`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section Depression

variable {F : Type*} [Field F] [CharZero F]

/-- Substitute `y=(z-r)/h` into a coefficient-field polynomial. -/
def affineDepress46 (h r : F) (p : F[X]) : F[X] :=
  p.comp ((X - C r) * C h⁻¹)

/-- Raw quartic with leading coefficient `h⁴`. -/
def rawQuartic46 (h a3 a2 a1 a0 : F) : F[X] :=
  C (h ^ 4) * X ^ 4 + C a3 * X ^ 3 + C a2 * X ^ 2 +
    C a1 * X + C a0

/-- Raw sextic with leading coefficient `h⁶`. -/
def rawSextic46 (h b5 b4 b3 b2 b1 b0 : F) : F[X] :=
  C (h ^ 6) * X ^ 6 + C b5 * X ^ 5 + C b4 * X ^ 4 +
    C b3 * X ^ 3 + C b2 * X ^ 2 + C b1 * X + C b0

/-- Quartic linear depression parameter. -/
def quarticDepressionR46 (h a3 : F) : F := a3 / (4 * h ^ 3)

def depressedA46 (h r a3 a2 : F) : F :=
  6 * r ^ 2 - 3 * (a3 / h ^ 3) * r + a2 / h ^ 2

def depressedB46 (h r a3 a2 a1 : F) : F :=
  -4 * r ^ 3 + 3 * (a3 / h ^ 3) * r ^ 2 -
    2 * (a2 / h ^ 2) * r + a1 / h

def depressedC46 (h r a3 a2 a1 a0 : F) : F :=
  r ^ 4 - (a3 / h ^ 3) * r ^ 3 + (a2 / h ^ 2) * r ^ 2 -
    (a1 / h) * r + a0

def depressedL46 (h r b5 : F) : F := -6 * r + b5 / h ^ 5

def depressedP46 (h r b5 b4 : F) : F :=
  15 * r ^ 2 - 5 * (b5 / h ^ 5) * r + b4 / h ^ 4

def depressedQ46 (h r b5 b4 b3 : F) : F :=
  -20 * r ^ 3 + 10 * (b5 / h ^ 5) * r ^ 2 -
    4 * (b4 / h ^ 4) * r + b3 / h ^ 3

def depressedR46 (h r b5 b4 b3 b2 : F) : F :=
  15 * r ^ 4 - 10 * (b5 / h ^ 5) * r ^ 3 +
    6 * (b4 / h ^ 4) * r ^ 2 - 3 * (b3 / h ^ 3) * r +
    b2 / h ^ 2

def depressedS46 (h r b5 b4 b3 b2 b1 : F) : F :=
  -6 * r ^ 5 + 5 * (b5 / h ^ 5) * r ^ 4 -
    4 * (b4 / h ^ 4) * r ^ 3 + 3 * (b3 / h ^ 3) * r ^ 2 -
    2 * (b2 / h ^ 2) * r + b1 / h

def depressedT46 (h r b5 b4 b3 b2 b1 b0 : F) : F :=
  r ^ 6 - (b5 / h ^ 5) * r ^ 5 + (b4 / h ^ 4) * r ^ 4 -
    (b3 / h ^ 3) * r ^ 3 + (b2 / h ^ 2) * r ^ 2 -
    (b1 / h) * r + b0

/-- Exact quartic depression. -/
theorem affineDepress_rawQuartic46
    (h r a3 a2 a1 a0 : F) (hh : h ≠ 0)
    (hr : r = quarticDepressionR46 h a3) :
    affineDepress46 h r (rawQuartic46 h a3 a2 a1 a0) =
      depressedQuartic46 (depressedA46 h r a3 a2)
        (depressedB46 h r a3 a2 a1)
        (depressedC46 h r a3 a2 a1 a0) := by
  subst r
  apply Polynomial.funext
  intro z
  simp [affineDepress46, rawQuartic46, depressedQuartic46,
    depressedA46, depressedB46, depressedC46, quarticDepressionR46]
  field_simp [hh]
  ring

/-- Exact sextic expansion under the same affine change. -/
theorem affineDepress_rawSextic46
    (h r b5 b4 b3 b2 b1 b0 : F) (hh : h ≠ 0) :
    affineDepress46 h r (rawSextic46 h b5 b4 b3 b2 b1 b0) =
      depressedSextic46 (depressedL46 h r b5)
        (depressedP46 h r b5 b4) (depressedQ46 h r b5 b4 b3)
        (depressedR46 h r b5 b4 b3 b2)
        (depressedS46 h r b5 b4 b3 b2 b1)
        (depressedT46 h r b5 b4 b3 b2 b1 b0) := by
  apply Polynomial.funext
  intro z
  simp [affineDepress46, rawSextic46, depressedSextic46,
    depressedL46, depressedP46, depressedQ46, depressedR46,
    depressedS46, depressedT46]
  field_simp [hh]
  ring

/-- The quintic mismatch coefficient is the normalized imprimitive
discriminator. -/
theorem depressedL46_eq_discriminator
    (h a3 b5 : F) (hh : h ≠ 0) :
    depressedL46 h (quarticDepressionR46 h a3) b5 =
      -(3 * a3 * h ^ 2 - 2 * b5) / (2 * h ^ 5) := by
  simp only [depressedL46, quarticDepressionR46]
  field_simp [hh]
  ring

/-- In the aligned branch the common depression has `L=0`. -/
theorem depressedL46_eq_zero_of_aligned
    (h a3 b5 : F) (hh : h ≠ 0)
    (haligned : 3 * a3 * h ^ 2 - 2 * b5 = 0) :
    depressedL46 h (quarticDepressionR46 h a3) b5 = 0 := by
  rw [depressedL46_eq_discriminator h a3 b5 hh, haligned]
  simp

/-- In the nonaligned branch `N=lambda*h⁵`, the common depression has the
constant quintic coefficient `L=-lambda/2`. -/
theorem depressedL46_eq_of_mismatch
    (h a3 b5 lambda : F) (hh : h ≠ 0)
    (hmismatch : 3 * a3 * h ^ 2 - 2 * b5 = lambda * h ^ 5) :
    depressedL46 h (quarticDepressionR46 h a3) b5 = -lambda / 2 := by
  rw [depressedL46_eq_discriminator h a3 b5 hh, hmismatch]
  field_simp [hh]

end Depression

end Max11DegreeRoutes
