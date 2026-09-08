import Fable410ScaleTwoAlignedTenthFacePart02Scratch
import Fable410ScaleTwoAlignedFlatDefectPart08Scratch
import Grok810SpeedValLibScratch

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

open private memory410_flatThirdDefect from Fable410ScaleTwoAlignedFlatDefectPart01Scratch in
open private memory410_flatFourthDefect from Fable410ScaleTwoAlignedFlatDefectPart02Scratch in
open private memory410_flatFifthDefect from Fable410ScaleTwoAlignedFlatDefectPart03Scratch in
open private memory410_flatSixthDefect from Fable410ScaleTwoAlignedFlatDefectPart04Scratch in
open private memory410_flatSeventhDefect from Fable410ScaleTwoAlignedFlatDefectPart05Scratch in
open private memory410_flatEighthDefect from Fable410ScaleTwoAlignedFlatDefectPart06Scratch in
open private memory410_flatNinthDefect from Fable410ScaleTwoAlignedFlatDefectPart07Scratch in
open private memory410_flatTenthDefect from Fable410ScaleTwoAlignedFlatDefectPart08Scratch in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 64000000 in
/-- Flat polynomial data for the eleventh defect; each block has at most six monomials. -/
private theorem memory410_flatEleventhDefect {K : Type*} [CommRing K]
    (H a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7 : K[X]) (κ : K) :
    alignedEleventhDefect410 H a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7 κ =
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, b1, b2, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(220200960 : K[X]), (22020096 : K[X]), (44040192 : K[X]), (100663296 : K[X]), (7340032 : K[X]), (67108864 : K[X])]
      [[16, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [15, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1],
        [15, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1],
        [15, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
        [15, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
        [15, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, b1, b2, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(33554432 : K[X]), (330301440 : K[X]), (-110100480 : K[X]), (275251200 : K[X]), (-55050240 : K[X]), (-88080384 : K[X])]
      [[15, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0],
        [14, 2, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
        [14, 1, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
        [14, 1, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [14, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [13, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, b1, b2, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(-60555264 : K[X]), (-150994944 : K[X]), (-60555264 : K[X]), (-125829120 : K[X]), (-100663296 : K[X]), (-60555264 : K[X])]
      [[13, 1, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1],
        [13, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
        [13, 1, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 1],
        [13, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0],
        [13, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0],
        [13, 0, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, b1, b2, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(-62914560 : K[X]), (-20185088 : K[X]), (-100663296 : K[X]), (-75497472 : K[X]), (-37748736 : K[X]), (-50331648 : K[X])]
      [[13, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
        [13, 0, 1, 3, 0, 0, 0, 0, 0, 0, 0, 0, 1],
        [13, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0],
        [13, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0],
        [13, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0],
        [13, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, b1, b2, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(-12582912 : K[X]), (27525120 : K[X]), (-1004666880 : K[X]), (-908328960 : K[X]), (34406400 : K[X]), (-756940800 : K[X])]
      [[13, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0],
        [12, 2, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0],
        [12, 1, 1, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0],
        [12, 1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0],
        [12, 0, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0],
        [12, 0, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, b1, b2, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(-214466560 : K[X]), (308281344 : K[X]), (154140672 : K[X]), (75694080 : K[X]), (264241152 : K[X]), (110100480 : K[X])]
      [[12, 0, 1, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [11, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0],
        [11, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0],
        [11, 1, 0, 1, 3, 0, 0, 0, 0, 0, 0, 0, 1],
        [11, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0],
        [11, 1, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, b1, b2, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(154140672 : K[X]), (37847040 : K[X]), (132120576 : K[X]), (113541120 : K[X]), (132120576 : K[X]), (220200960 : K[X])]
      [[11, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0],
        [11, 0, 2, 0, 3, 0, 0, 0, 0, 0, 0, 0, 1],
        [11, 0, 2, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0],
        [11, 0, 1, 2, 2, 0, 0, 0, 0, 0, 0, 0, 1],
        [11, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0],
        [11, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, b1, b2, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(88080384 : K[X]), (18923520 : K[X]), (36700160 : K[X]), (88080384 : K[X]), (66060288 : K[X]), (14680064 : K[X])]
      [[11, 0, 1, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0],
        [11, 0, 0, 4, 1, 0, 0, 0, 0, 0, 0, 0, 1],
        [11, 0, 0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 0],
        [11, 0, 0, 2, 1, 0, 0, 0, 1, 0, 0, 0, 0],
        [11, 0, 0, 1, 2, 0, 0, 1, 0, 0, 0, 0, 0],
        [11, 0, 0, 0, 3, 0, 1, 0, 0, 0, 0, 0, 0]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, b1, b2, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(-104079360 : K[X]), (1362493440 : K[X]), (605552640 : K[X]), (1873428480 : K[X]), (283852800 : K[X]), (-423886848 : K[X])]
      [[10, 1, 1, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0],
        [10, 1, 0, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0],
        [10, 0, 2, 1, 3, 0, 0, 0, 0, 0, 0, 0, 0],
        [10, 0, 1, 3, 2, 0, 0, 0, 0, 0, 0, 0, 0],
        [10, 0, 0, 5, 1, 0, 0, 0, 0, 0, 0, 0, 0],
        [9, 1, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, b1, b2, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(-17977344 : K[X]), (-121110528 : K[X]), (-211943424 : K[X]), (-423886848 : K[X]), (-89886720 : K[X]), (-363331584 : K[X])]
      [[9, 1, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 1],
        [9, 1, 0, 0, 3, 0, 0, 0, 0, 0, 1, 0, 0],
        [9, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0],
        [9, 0, 1, 2, 1, 0, 0, 0, 0, 0, 0, 1, 0],
        [9, 0, 1, 1, 4, 0, 0, 0, 0, 0, 0, 0, 1],
        [9, 0, 1, 1, 2, 0, 0, 0, 0, 0, 1, 0, 0]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, b1, b2, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(-100925440 : K[X]), (-35323904 : K[X]), (-59924480 : K[X]), (-121110528 : K[X]), (-151388160 : K[X]), (-80740352 : K[X])]
      [[9, 0, 1, 0, 3, 0, 0, 0, 0, 1, 0, 0, 0],
        [9, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 1, 0],
        [9, 0, 0, 3, 3, 0, 0, 0, 0, 0, 0, 0, 1],
        [9, 0, 0, 3, 1, 0, 0, 0, 0, 0, 1, 0, 0],
        [9, 0, 0, 2, 2, 0, 0, 0, 0, 1, 0, 0, 0],
        [9, 0, 0, 1, 3, 0, 0, 0, 1, 0, 0, 0, 0]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, b1, b2, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(-15138816 : K[X]), (-212889600 : K[X]), (73328640 : K[X]), (-1555276800 : K[X]), (-1064448000 : K[X]), (132464640 : K[X])]
      [[9, 0, 0, 0, 4, 0, 0, 1, 0, 0, 0, 0, 0],
        [8, 1, 0, 1, 5, 0, 0, 0, 0, 0, 0, 0, 0],
        [8, 0, 2, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0],
        [8, 0, 1, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0],
        [8, 0, 0, 4, 3, 0, 0, 0, 0, 0, 0, 0, 0],
        [7, 1, 0, 0, 4, 0, 0, 0, 0, 0, 0, 1, 0]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, b1, b2, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(529858560 : K[X]), (17228288 : K[X]), (113541120 : K[X]), (264929280 : K[X]), (51684864 : K[X]), (227082240 : K[X])]
      [[7, 0, 1, 1, 3, 0, 0, 0, 0, 0, 0, 1, 0],
        [7, 0, 1, 0, 6, 0, 0, 0, 0, 0, 0, 0, 1],
        [7, 0, 1, 0, 4, 0, 0, 0, 0, 0, 1, 0, 0],
        [7, 0, 0, 3, 2, 0, 0, 0, 0, 0, 0, 1, 0],
        [7, 0, 0, 2, 5, 0, 0, 0, 0, 0, 0, 0, 1],
        [7, 0, 0, 2, 3, 0, 0, 0, 0, 0, 1, 0, 0]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, b1, b2, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(94617600 : K[X]), (15138816 : K[X]), (-48153600 : K[X]), (159174400 : K[X]), (910103040 : K[X]), (-125841408 : K[X])]
      [[7, 0, 0, 1, 4, 0, 0, 0, 0, 1, 0, 0, 0],
        [7, 0, 0, 0, 5, 0, 0, 0, 1, 0, 0, 0, 0],
        [6, 1, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0],
        [6, 0, 1, 1, 6, 0, 0, 0, 0, 0, 0, 0, 0],
        [6, 0, 0, 3, 5, 0, 0, 0, 0, 0, 0, 0, 0],
        [5, 0, 1, 0, 5, 0, 0, 0, 0, 0, 0, 1, 0]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, b1, b2, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(-314603520 : K[X]), (-16612992 : K[X]), (-107864064 : K[X]), (-14981120 : K[X]), (45570360 : K[X]), (-221506560 : K[X])]
      [[5, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 1, 0],
        [5, 0, 0, 1, 7, 0, 0, 0, 0, 0, 0, 0, 1],
        [5, 0, 0, 1, 5, 0, 0, 0, 0, 0, 1, 0, 0],
        [5, 0, 0, 0, 6, 0, 0, 0, 0, 1, 0, 0, 0],
        [4, 0, 1, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0],
        [4, 0, 0, 2, 7, 0, 0, 0, 0, 0, 0, 0, 0]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, b1, b2, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(120598016 : K[X]), (1788204 : K[X]), (14767104 : K[X]), (-7787340 : K[X]), (-14536368 : K[X]), (5486535 : K[X])]
      [[3, 0, 0, 1, 6, 0, 0, 0, 0, 0, 0, 1, 0],
        [3, 0, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0, 1],
        [3, 0, 0, 0, 7, 0, 0, 0, 0, 0, 1, 0, 0],
        [2, 0, 0, 1, 9, 0, 0, 0, 0, 0, 0, 0, 0],
        [1, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 1, 0],
        [0, 0, 0, 0, 11, 0, 0, 0, 0, 0, 0, 0, 0]] := by
  simp only [alignedEleventhDefect410, memory410_flatThirdDefect, memory410_flatFourthDefect, memory410_flatFifthDefect, memory410_flatSixthDefect, memory410_flatSeventhDefect, memory410_flatEighthDefect, memory410_flatNinthDefect, memory410_flatTenthDefect, Max11ReflectVal.polyR_cons, Max11ReflectVal.polyR_nil_left, Max11ReflectVal.polyR_nil_right, Max11ReflectVal.monoR_cons, Max11ReflectVal.monoR_nil_left, Max11ReflectVal.monoR_nil_right, pow_zero, pow_one, one_mul, mul_one, add_zero]
  ring

#print axioms memory410_flatEleventhDefect

end Max11DegreeRoutes
