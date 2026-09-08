import FiniteDoubleBlowup

/-! # Load annihilation on the common-cubic sheet

The third full Faber row is its zero-high part as soon as every high
parameter annihilates the three normal coordinates.  The first, second,
and fourth rows have the same normal-linear reduction, but they retain an
explicit cubic-sheet remainder in the high parameters.  These identities
are the algebraic source of that comparison, over an arbitrary
commutative ring.
-/

noncomputable section

set_option maxRecDepth 10000 in
/-- In any quotient where every high parameter annihilates all three
normal coordinates, the full first Faber numerator is its zero-high part
plus the displayed cubic-sheet load remainder. -/
theorem GCD369CubeFaberFullN1_eq_zeroHigh_of_load_annihilates_normals
    {R : Type*} [CommRing R]
    (X Y Z U V d c7 c5 c4 c3 c2 c1 : R)
    (hd : d * X = 0 ∧ d * Y = 0 ∧ d * Z = 0)
    (h7 : c7 * X = 0 ∧ c7 * Y = 0 ∧ c7 * Z = 0)
    (h5 : c5 * X = 0 ∧ c5 * Y = 0 ∧ c5 * Z = 0)
    (h4 : c4 * X = 0 ∧ c4 * Y = 0 ∧ c4 * Z = 0)
    (h3 : c3 * X = 0 ∧ c3 * Y = 0 ∧ c3 * Z = 0)
    (h2 : c2 * X = 0 ∧ c2 * Y = 0 ∧ c2 * Z = 0)
    (h1 : c1 * X = 0 ∧ c1 * Y = 0 ∧ c1 * Z = 0) :
    GCD369CubeFaberFullN1
        (V ^ 2 + Z) (2 * U * V + Y) (U ^ 2 + X) (2 * V) (2 * U)
        d c7 c5 c4 c3 c2 c1 =
      729 * GCD369CubeFaberN1
        (V ^ 2 + Z) (2 * U * V + Y) (U ^ 2 + X) (2 * V) (2 * U) +
      (-10240 * U ^ 3 * V + 30720 * V ^ 3) * d +
      (-1792 * U ^ 4 + 32256 * U * V ^ 2) * c7 +
      (-3840 * U ^ 3 + 34560 * V ^ 2) * c5 +
      27648 * U * V * c4 +
      41472 * V * c2 +
      20736 * U * c1 := by
  rcases hd with ⟨hdX, hdY, hdZ⟩
  rcases h7 with ⟨h7X, h7Y, h7Z⟩
  rcases h5 with ⟨h5X, _h5Y, h5Z⟩
  rcases h4 with ⟨_h4X, h4Y, _h4Z⟩
  rcases h3 with ⟨h3X, _h3Y, _h3Z⟩
  rcases h2 with ⟨_h2X, _h2Y, _h2Z⟩
  rcases h1 with ⟨_h1X, _h1Y, _h1Z⟩
  simp only [GCD369CubeFaberN1]
  linear_combination
    (27648 * Y - 18432 * U * V) * hdX -
    9216 * U ^ 2 * hdY +
    55296 * V * hdZ +
    (6048 * X - 8064 * U ^ 2) * h7X +
    24192 * V * h7Y +
    24192 * U * h7Z -
    17280 * U * h5X +
    51840 * h5Z +
    41472 * h4Y +
    31104 * h3X

/-- The primitive first zero-high numerator commutes with ring maps. -/
theorem GCD369CubeFaberN1_map
    {R L : Type*} [CommRing R] [CommRing L] (f : R →+* L)
    (a0 a1 a2 a3 a4 : R) :
    f (GCD369CubeFaberN1 a0 a1 a2 a3 a4) =
      GCD369CubeFaberN1 (f a0) (f a1) (f a2) (f a3) (f a4) := by
  simp only [GCD369CubeFaberN1, map_add, map_sub, map_mul, map_pow,
    map_ofNat]

set_option maxRecDepth 10000 in
/-- In any quotient where every high parameter annihilates all three
normal coordinates, the full second Faber numerator is its zero-high part
plus the displayed cubic-sheet load remainder. -/
theorem GCD369CubeFaberFullN2_eq_zeroHigh_of_load_annihilates_normals
    {R : Type*} [CommRing R]
    (X Y Z U V d c7 c5 c4 c3 c2 c1 : R)
    (hd : d * X = 0 ∧ d * Y = 0 ∧ d * Z = 0)
    (h7 : c7 * X = 0 ∧ c7 * Y = 0 ∧ c7 * Z = 0)
    (h5 : c5 * X = 0 ∧ c5 * Y = 0 ∧ c5 * Z = 0)
    (h4 : c4 * X = 0 ∧ c4 * Y = 0 ∧ c4 * Z = 0)
    (h3 : c3 * X = 0 ∧ c3 * Y = 0 ∧ c3 * Z = 0)
    (h2 : c2 * X = 0 ∧ c2 * Y = 0 ∧ c2 * Z = 0)
    (h1 : c1 * X = 0 ∧ c1 * Y = 0 ∧ c1 * Z = 0) :
    GCD369CubeFaberFullN2
        (V ^ 2 + Z) (2 * U * V + Y) (U ^ 2 + X) (2 * V) (2 * U)
        d c7 c5 c4 c3 c2 c1 =
      2187 * GCD369CubeFaberN2
        (V ^ 2 + Z) (2 * U * V + Y) (U ^ 2 + X) (2 * V) (2 * U) +
      (2048 * U ^ 5 - 46080 * U ^ 2 * V ^ 2) * d +
      (-21504 * U ^ 3 * V + 32256 * V ^ 3) * c7 -
      34560 * U ^ 2 * V * c5 +
      (-9216 * U ^ 3 + 41472 * V ^ 2) * c4 -
      20736 * U ^ 2 * c2 +
      62208 * V * c1 := by
  rcases hd with ⟨hdX, hdY, hdZ⟩
  rcases h7 with ⟨h7X, h7Y, h7Z⟩
  rcases h5 with ⟨h5X, h5Y, _h5Z⟩
  rcases h4 with ⟨h4X, _h4Y, h4Z⟩
  rcases h3 with ⟨_h3X, h3Y, _h3Z⟩
  rcases h2 with ⟨h2X, _h2Y, _h2Z⟩
  rcases h1 with ⟨_h1X, _h1Y, _h1Z⟩
  simp only [GCD369CubeFaberN2]
  linear_combination
    (-55296 * X * U + 82944 * Z + 12288 * U ^ 3 - 27648 * V ^ 2) * hdX +
    (41472 * Y - 55296 * U * V) * hdY -
    27648 * U ^ 2 * hdZ +
    (36288 * Y - 48384 * U * V) * h7X -
    24192 * U ^ 2 * h7Y +
    72576 * V * h7Z -
    51840 * V * h5X -
    51840 * U * h5Y -
    82944 * U * h4X +
    124416 * h4Z +
    93312 * h3Y +
    62208 * h2X

/-- The primitive second zero-high numerator commutes with ring maps. -/
theorem GCD369CubeFaberN2_map
    {R L : Type*} [CommRing R] [CommRing L] (f : R →+* L)
    (a0 a1 a2 a3 a4 : R) :
    f (GCD369CubeFaberN2 a0 a1 a2 a3 a4) =
      GCD369CubeFaberN2 (f a0) (f a1) (f a2) (f a3) (f a4) := by
  simp only [GCD369CubeFaberN2, map_add, map_sub, map_mul, map_pow,
    map_ofNat]

set_option maxRecDepth 10000 in
/-- In any quotient where every high parameter annihilates all three
normal coordinates, the full fourth Faber numerator is its zero-high part
plus the displayed cubic-sheet load remainder. -/
theorem GCD369CubeFaberFullN4_eq_zeroHigh_of_load_annihilates_normals
    {R : Type*} [CommRing R]
    (X Y Z U V d c7 c5 c4 c3 c2 c1 : R)
    (hd : d * X = 0 ∧ d * Y = 0 ∧ d * Z = 0)
    (h7 : c7 * X = 0 ∧ c7 * Y = 0 ∧ c7 * Z = 0)
    (h5 : c5 * X = 0 ∧ c5 * Y = 0 ∧ c5 * Z = 0)
    (h4 : c4 * X = 0 ∧ c4 * Y = 0 ∧ c4 * Z = 0)
    (h3 : c3 * X = 0 ∧ c3 * Y = 0 ∧ c3 * Z = 0)
    (h2 : c2 * X = 0 ∧ c2 * Y = 0 ∧ c2 * Z = 0)
    (h1 : c1 * X = 0 ∧ c1 * Y = 0 ∧ c1 * Z = 0) :
    GCD369CubeFaberFullN4
        (V ^ 2 + Z) (2 * U * V + Y) (U ^ 2 + X) (2 * V) (2 * U)
        d c7 c5 c4 c3 c2 c1 =
      6561 * GCD369CubeFaberN4
        (V ^ 2 + Z) (2 * U * V + Y) (U ^ 2 + X) (2 * V) (2 * U) +
      (5120 * U ^ 6 - 184320 * U ^ 3 * V ^ 2 + 207360 * V ^ 4) * d +
      (-64512 * U ^ 4 * V + 290304 * U * V ^ 3) * c7 +
      (-103680 * U ^ 3 * V + 207360 * V ^ 3) * c5 +
      (-20736 * U ^ 4 + 248832 * U * V ^ 2) * c4 +
      (-41472 * U ^ 3 + 186624 * V ^ 2) * c2 +
      186624 * U * V * c1 := by
  rcases hd with ⟨hdX, hdY, hdZ⟩
  rcases h7 with ⟨h7X, h7Y, h7Z⟩
  rcases h5 with ⟨h5X, _h5Y, _h5Z⟩
  rcases h4 with ⟨h4X, h4Y, _h4Z⟩
  rcases h3 with ⟨h3X, h3Y, _h3Z⟩
  rcases h2 with ⟨h2X, _h2Y, h2Z⟩
  rcases h1 with ⟨_h1X, h1Y, _h1Z⟩
  simp only [GCD369CubeFaberN4]
  linear_combination
    (-82944 * X ^ 2 + 248832 * X * U ^ 2 - 746496 * Y * V -
      497664 * Z * U + 9216 * U ^ 4) * hdX +
    (-248832 * Y * U - 82944 * U ^ 2 * V) * hdY +
    (373248 * Z - 55296 * U ^ 3 + 248832 * V ^ 2) * hdZ +
    (-217728 * X * V - 326592 * Y * U) * h7X +
    (326592 * Z - 24192 * U ^ 3) * h7Y +
    217728 * U * V * h7Z +
    (-233280 * Y + 155520 * U * V) * h5X +
    (-186624 * X + 124416 * U ^ 2) * h4X -
    373248 * V * h4Y -
    559872 * V * h3X -
    279936 * U * h3Y -
    373248 * U * h2X +
    559872 * h2Z +
    279936 * h1Y

#print axioms GCD369CubeFaberFullN1_eq_zeroHigh_of_load_annihilates_normals
#print axioms GCD369CubeFaberN1_map
#print axioms GCD369CubeFaberFullN2_eq_zeroHigh_of_load_annihilates_normals
#print axioms GCD369CubeFaberN2_map
#print axioms GCD369CubeFaberFullN4_eq_zeroHigh_of_load_annihilates_normals
