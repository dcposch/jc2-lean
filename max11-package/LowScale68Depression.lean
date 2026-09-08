import LowScale68Integrated

/-! # Exact common depression for the `(6,8)` source

This module performs the affine coefficient-field change `z=h*y+r` on raw
sextic and octic polynomials whose leading coefficients are `h^6,h^8`.  The
sextic quintic coefficient is killed by `r=a₅/(6h⁵)`, and every resulting
coefficient is identified with the depressed normal form used by the
integrated Faber calculation.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section Depression68

variable {F : Type*} [Field F] [CharZero F]

/-- Substitute `y=(z-r)/h` into a coefficient-field polynomial. -/
def affineDepress68 (h r : F) (p : F[X]) : F[X] :=
  p.comp ((X - C r) * C h⁻¹)

def rawSextic68 (h a5 a4 a3 a2 a1 a0 : F) : F[X] :=
  C (h ^ 6) * X ^ 6 + C a5 * X ^ 5 + C a4 * X ^ 4 +
    C a3 * X ^ 3 + C a2 * X ^ 2 + C a1 * X + C a0

def rawOctic68 (h b7 b6 b5 b4 b3 b2 b1 b0 : F) : F[X] :=
  C (h ^ 8) * X ^ 8 + C b7 * X ^ 7 + C b6 * X ^ 6 +
    C b5 * X ^ 5 + C b4 * X ^ 4 + C b3 * X ^ 3 +
    C b2 * X ^ 2 + C b1 * X + C b0

def sexticDepressionR68 (h a5 : F) : F := a5 / (6 * h ^ 5)

def depressedA68 (h r a5 a4 : F) : F :=
  15 * r ^ 2 - 5 * (a5 / h ^ 5) * r + a4 / h ^ 4

def depressedB68 (h r a5 a4 a3 : F) : F :=
  -20 * r ^ 3 + 10 * (a5 / h ^ 5) * r ^ 2 -
    4 * (a4 / h ^ 4) * r + a3 / h ^ 3

def depressedC68 (h r a5 a4 a3 a2 : F) : F :=
  15 * r ^ 4 - 10 * (a5 / h ^ 5) * r ^ 3 +
    6 * (a4 / h ^ 4) * r ^ 2 - 3 * (a3 / h ^ 3) * r +
    a2 / h ^ 2

def depressedD68 (h r a5 a4 a3 a2 a1 : F) : F :=
  -6 * r ^ 5 + 5 * (a5 / h ^ 5) * r ^ 4 -
    4 * (a4 / h ^ 4) * r ^ 3 + 3 * (a3 / h ^ 3) * r ^ 2 -
    2 * (a2 / h ^ 2) * r + a1 / h

def depressedE68 (h r a5 a4 a3 a2 a1 a0 : F) : F :=
  r ^ 6 - (a5 / h ^ 5) * r ^ 5 + (a4 / h ^ 4) * r ^ 4 -
    (a3 / h ^ 3) * r ^ 3 + (a2 / h ^ 2) * r ^ 2 -
    (a1 / h) * r + a0

def depressedL68 (h r b7 : F) : F := -8 * r + b7 / h ^ 7

def depressedP68 (h r b7 b6 : F) : F :=
  28 * r ^ 2 - 7 * (b7 / h ^ 7) * r + b6 / h ^ 6

def depressedQ68 (h r b7 b6 b5 : F) : F :=
  -56 * r ^ 3 + 21 * (b7 / h ^ 7) * r ^ 2 -
    6 * (b6 / h ^ 6) * r + b5 / h ^ 5

def depressedR68 (h r b7 b6 b5 b4 : F) : F :=
  70 * r ^ 4 - 35 * (b7 / h ^ 7) * r ^ 3 +
    15 * (b6 / h ^ 6) * r ^ 2 - 5 * (b5 / h ^ 5) * r +
    b4 / h ^ 4

def depressedS68 (h r b7 b6 b5 b4 b3 : F) : F :=
  -56 * r ^ 5 + 35 * (b7 / h ^ 7) * r ^ 4 -
    20 * (b6 / h ^ 6) * r ^ 3 + 10 * (b5 / h ^ 5) * r ^ 2 -
    4 * (b4 / h ^ 4) * r + b3 / h ^ 3

def depressedT68 (h r b7 b6 b5 b4 b3 b2 : F) : F :=
  28 * r ^ 6 - 21 * (b7 / h ^ 7) * r ^ 5 +
    15 * (b6 / h ^ 6) * r ^ 4 - 10 * (b5 / h ^ 5) * r ^ 3 +
    6 * (b4 / h ^ 4) * r ^ 2 - 3 * (b3 / h ^ 3) * r +
    b2 / h ^ 2

def depressedU68 (h r b7 b6 b5 b4 b3 b2 b1 : F) : F :=
  -8 * r ^ 7 + 7 * (b7 / h ^ 7) * r ^ 6 -
    6 * (b6 / h ^ 6) * r ^ 5 + 5 * (b5 / h ^ 5) * r ^ 4 -
    4 * (b4 / h ^ 4) * r ^ 3 + 3 * (b3 / h ^ 3) * r ^ 2 -
    2 * (b2 / h ^ 2) * r + b1 / h

def depressedV68 (h r b7 b6 b5 b4 b3 b2 b1 b0 : F) : F :=
  r ^ 8 - (b7 / h ^ 7) * r ^ 7 + (b6 / h ^ 6) * r ^ 6 -
    (b5 / h ^ 5) * r ^ 5 + (b4 / h ^ 4) * r ^ 4 -
    (b3 / h ^ 3) * r ^ 3 + (b2 / h ^ 2) * r ^ 2 -
    (b1 / h) * r + b0

/-- Exact sextic depression under the common affine change. -/
theorem affineDepress_rawSextic68
    (h r a5 a4 a3 a2 a1 a0 : F) (hh : h ≠ 0)
    (hr : r = sexticDepressionR68 h a5) :
    affineDepress68 h r (rawSextic68 h a5 a4 a3 a2 a1 a0) =
      depressedSextic68 (depressedA68 h r a5 a4)
        (depressedB68 h r a5 a4 a3) (depressedC68 h r a5 a4 a3 a2)
        (depressedD68 h r a5 a4 a3 a2 a1)
        (depressedE68 h r a5 a4 a3 a2 a1 a0) := by
  subst r
  apply Polynomial.funext
  intro z
  simp [affineDepress68, rawSextic68, depressedSextic68,
    depressedA68, depressedB68, depressedC68, depressedD68, depressedE68,
    sexticDepressionR68]
  field_simp [hh]
  ring

/-- Exact octic expansion under the same common affine change. -/
theorem affineDepress_rawOctic68
    (h r b7 b6 b5 b4 b3 b2 b1 b0 : F) (hh : h ≠ 0) :
    affineDepress68 h r (rawOctic68 h b7 b6 b5 b4 b3 b2 b1 b0) =
      depressedOctic68 (depressedL68 h r b7) (depressedP68 h r b7 b6)
        (depressedQ68 h r b7 b6 b5) (depressedR68 h r b7 b6 b5 b4)
        (depressedS68 h r b7 b6 b5 b4 b3)
        (depressedT68 h r b7 b6 b5 b4 b3 b2)
        (depressedU68 h r b7 b6 b5 b4 b3 b2 b1)
        (depressedV68 h r b7 b6 b5 b4 b3 b2 b1 b0) := by
  apply Polynomial.funext
  intro z
  simp [affineDepress68, rawOctic68, depressedOctic68, depressedL68,
    depressedP68, depressedQ68, depressedR68, depressedS68, depressedT68,
    depressedU68, depressedV68]
  field_simp [hh]
  ring

/-- The surviving septic coefficient is the normalized first
sextic/octic alignment discriminator. -/
theorem depressedL68_eq_discriminator
    (h a5 b7 : F) (hh : h ≠ 0) :
    depressedL68 h (sexticDepressionR68 h a5) b7 =
      -(4 * a5 * h ^ 2 - 3 * b7) / (3 * h ^ 7) := by
  simp only [depressedL68, sexticDepressionR68]
  field_simp [hh]
  ring

/-- Exact alignment makes the depressed septic coefficient zero. -/
theorem depressedL68_eq_zero_of_aligned
    (h a5 b7 : F) (hh : h ≠ 0)
    (haligned : 4 * a5 * h ^ 2 - 3 * b7 = 0) :
    depressedL68 h (sexticDepressionR68 h a5) b7 = 0 := by
  rw [depressedL68_eq_discriminator h a5 b7 hh, haligned]
  simp

end Depression68

#print axioms affineDepress_rawSextic68
#print axioms affineDepress_rawOctic68
#print axioms depressedL68_eq_discriminator
#print axioms depressedL68_eq_zero_of_aligned

end Max11DegreeRoutes
