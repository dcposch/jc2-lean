import Fable810ScaleTwoNextIntegralBridgeScratch
import Fable810ScaleZeroFourteenthDefectScratch

/-! # Collapsed omicron head on the normalized `(8,10)` nonzero face

This module consumes the literal weight-`105` degree-`2` first-integral
clearing on the exact depth-two right jet produced by the xi bridge.  The
587-term source numerator is factored without reselecting any witness; its
`h^94` quotient has a five-term root head.  No total-degree argument is used.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000

section OmicronCollapsedQuotient810

variable {R : Type*} [CommRing R]

def bridgeOmicronCollapsedQuotient810
    (h t1 v2 u2 a41 a3 a2 a1 a0 s2 w2 b63 b51 b4 b3 b2 b1
      lambda : R) : R :=
    (96757023244288*a41*(-95*a41 ^ 2*u2 + 28*a41 ^ 2*w2 + 60*a41*b51*v2 + 72*a41*b63*u2 + 60*b51*u2 ^ 2))
    + h * (-274877906944*(15360*a3 ^ 2*b51 - 33792*a3*a41 ^ 2*s2 + 100320*a3*a41 ^ 2*v2 + 24576*a3*a41*b4 - 42240*a3*a41*b51*t1 - 50688*a3*a41*b63*v2 + 100320*a3*a41*u2 ^ 2 - 59136*a3*a41*u2*w2 - 42240*a3*b51*u2*v2 - 25344*a3*b63*u2 ^ 2 - 7524*a41 ^ 3*lambda*v2 + 26752*a41 ^ 3*s2*t1 - 75240*a41 ^ 3*t1*v2 - 16896*a41 ^ 2*b4*t1 + 25080*a41 ^ 2*b51*t1 ^ 2 + 60192*a41 ^ 2*b63*t1*v2 - 11286*a41 ^ 2*lambda*u2 ^ 2 + 80256*a41 ^ 2*s2*u2*v2 - 112860*a41 ^ 2*t1*u2 ^ 2 + 70224*a41 ^ 2*t1*u2*w2 - 169290*a41 ^ 2*u2*v2 ^ 2 + 35112*a41 ^ 2*v2 ^ 2*w2 - 33792*a41*b4*u2*v2 + 100320*a41*b51*t1*u2*v2 + 16720*a41*b51*v2 ^ 3 + 60192*a41*b63*t1*u2 ^ 2 + 60192*a41*b63*u2*v2 ^ 2 + 26752*a41*s2*u2 ^ 3 - 112860*a41*u2 ^ 3*v2 + 70224*a41*u2 ^ 2*v2*w2 - 5632*b4*u2 ^ 3 + 16720*b51*t1*u2 ^ 3 + 25080*b51*u2 ^ 2*v2 ^ 2 + 20064*b63*u2 ^ 3*v2 - 5643*u2 ^ 5 + 5852*u2 ^ 4*w2))
    + h ^ 2 * (34359738368*(-245760*a2*a41*b51 + 112640*a3 ^ 3 - 76032*a3 ^ 2*a41*lambda - 422400*a3 ^ 2*a41*t1 + 202752*a3 ^ 2*b63*t1 + 270336*a3 ^ 2*s2*u2 - 802560*a3 ^ 2*u2*v2 + 236544*a3 ^ 2*v2*w2 + 180576*a3*a41 ^ 2*lambda*t1 + 451440*a3*a41 ^ 2*t1 ^ 2 - 481536*a3*a41*b63*t1 ^ 2 + 361152*a3*a41*lambda*u2*v2 - 1284096*a3*a41*s2*t1*u2 - 642048*a3*a41*s2*v2 ^ 2 + 3611520*a3*a41*t1*u2*v2 - 1123584*a3*a41*t1*v2*w2 + 902880*a3*a41*v2 ^ 3 + 270336*a3*b4*t1*u2 + 135168*a3*b4*v2 ^ 2 - 401280*a3*b51*t1 ^ 2*u2 - 401280*a3*b51*t1*v2 ^ 2 - 963072*a3*b63*t1*u2*v2 - 160512*a3*b63*v2 ^ 3 + 60192*a3*lambda*u2 ^ 3 - 642048*a3*s2*u2 ^ 2*v2 + 601920*a3*t1*u2 ^ 3 - 561792*a3*t1*u2 ^ 2*w2 + 1354320*a3*u2 ^ 2*v2 ^ 2 - 561792*a3*u2*v2 ^ 2*w2 - 101574*a41 ^ 3*lambda*t1 ^ 2 - 150480*a41 ^ 3*t1 ^ 3 - 73728*a41 ^ 2*b3 + 270864*a41 ^ 2*b63*t1 ^ 3 - 609444*a41 ^ 2*lambda*t1*u2*v2 - 101574*a41 ^ 2*lambda*v2 ^ 3 + 1083456*a41 ^ 2*s2*t1 ^ 2*u2 + 1083456*a41 ^ 2*s2*t1*v2 ^ 2 - 2877930*a41 ^ 2*t1 ^ 2*u2*v2 + 948024*a41 ^ 2*t1 ^ 2*v2*w2 - 1467180*a41 ^ 2*t1*v2 ^ 3 - 321024*a41*b4*t1 ^ 2*u2 - 321024*a41*b4*t1*v2 ^ 2 + 451440*a41*b51*t1 ^ 3*u2 + 677160*a41*b51*t1 ^ 2*v2 ^ 2 + 1625184*a41*b63*t1 ^ 2*u2*v2 + 541728*a41*b63*t1*v2 ^ 3 - 203148*a41*lambda*t1*u2 ^ 3 - 304722*a41*lambda*u2 ^ 2*v2 ^ 2 + 2166912*a41*s2*t1*u2 ^ 2*v2 + 722304*a41*s2*u2*v2 ^ 3 - 959310*a41*t1 ^ 2*u2 ^ 3 + 948024*a41*t1 ^ 2*u2 ^ 2*w2 - 4401540*a41*t1*u2 ^ 2*v2 ^ 2 + 1896048*a41*t1*u2*v2 ^ 2*w2 - 987525*a41*u2*v2 ^ 4 + 158004*a41*v2 ^ 4*w2 - 321024*b4*t1*u2 ^ 2*v2 - 107008*b4*u2*v2 ^ 3 + 677160*b51*t1 ^ 2*u2 ^ 2*v2 + 451440*b51*t1*u2*v2 ^ 3 + 22572*b51*v2 ^ 5 + 270864*b63*t1 ^ 2*u2 ^ 3 + 812592*b63*t1*u2 ^ 2*v2 ^ 2 + 135432*b63*u2*v2 ^ 4 - 50787*lambda*u2 ^ 4*v2 + 180576*s2*t1*u2 ^ 4 + 361152*s2*u2 ^ 3*v2 ^ 2 - 733590*t1*u2 ^ 4*v2 + 632016*t1*u2 ^ 3*v2*w2 - 658350*u2 ^ 3*v2 ^ 3 + 316008*u2 ^ 2*v2 ^ 3*w2))
    + h ^ 3 * (-2147483648*(-10813440*a2*a3*a41 + 4718592*a2*a3*b63 + 1216512*a2*a41 ^ 2*lambda + 6758400*a2*a41 ^ 2*t1 - 6488064*a2*a41*b63*t1 - 8650752*a2*a41*s2*u2 + 25681920*a2*a41*u2*v2 - 7569408*a2*a41*v2*w2 + 3145728*a2*b4*u2 - 5406720*a2*b51*t1*u2 - 2703360*a2*b51*v2 ^ 2 - 6488064*a2*b63*u2*v2 + 4280320*a2*u2 ^ 3 - 3784704*a2*u2 ^ 2*w2 - 2889216*a3 ^ 2*lambda*t1*u2 - 1444608*a3 ^ 2*lambda*v2 ^ 2 + 10272768*a3 ^ 2*s2*t1*v2 - 7223040*a3 ^ 2*t1 ^ 2*u2 + 4494336*a3 ^ 2*t1 ^ 2*w2 - 14446080*a3 ^ 2*t1*v2 ^ 2 + 9751104*a3*a41*lambda*t1 ^ 2*u2 + 9751104*a3*a41*lambda*t1*v2 ^ 2 - 34670592*a3*a41*s2*t1 ^ 2*v2 + 14446080*a3*a41*t1 ^ 3*u2 - 10112256*a3*a41*t1 ^ 3*w2 + 46046880*a3*a41*t1 ^ 2*v2 ^ 2 + 2359296*a3*b3*u2 + 5136384*a3*b4*t1 ^ 2*v2 - 7223040*a3*b51*t1 ^ 3*v2 - 8667648*a3*b63*t1 ^ 3*u2 - 13001472*a3*b63*t1 ^ 2*v2 ^ 2 + 9751104*a3*lambda*t1*u2 ^ 2*v2 + 3250368*a3*lambda*u2*v2 ^ 3 - 17335296*a3*s2*t1 ^ 2*u2 ^ 2 - 34670592*a3*s2*t1*u2*v2 ^ 2 - 2889216*a3*s2*v2 ^ 4 + 46046880*a3*t1 ^ 2*u2 ^ 2*v2 - 30336768*a3*t1 ^ 2*u2*v2*w2 + 46949760*a3*t1*u2*v2 ^ 3 - 10112256*a3*t1*v2 ^ 3*w2 + 3160080*a3*v2 ^ 5 - 7110180*a41 ^ 2*lambda*t1 ^ 3*u2 - 10665270*a41 ^ 2*lambda*t1 ^ 2*v2 ^ 2 + 25280640*a41 ^ 2*s2*t1 ^ 3*v2 - 6912675*a41 ^ 2*t1 ^ 4*u2 + 5530140*a41 ^ 2*t1 ^ 4*w2 - 31600800*a41 ^ 2*t1 ^ 3*v2 ^ 2 - 3244032*a41*b3*t1*u2 - 1622016*a41*b3*v2 ^ 2 - 5778432*a41*b4*t1 ^ 3*v2 + 7900200*a41*b51*t1 ^ 4*v2 + 9480240*a41*b63*t1 ^ 4*u2 + 18960480*a41*b63*t1 ^ 3*v2 ^ 2 - 21330540*a41*lambda*t1 ^ 2*u2 ^ 2*v2 - 14220360*a41*lambda*t1*u2*v2 ^ 3 - 711018*a41*lambda*v2 ^ 5 + 25280640*a41*s2*t1 ^ 3*u2 ^ 2 + 75841920*a41*s2*t1 ^ 2*u2*v2 ^ 2 + 12640320*a41*s2*t1*v2 ^ 4 - 63201600*a41*t1 ^ 3*u2 ^ 2*v2 + 44241120*a41*t1 ^ 3*u2*v2*w2 - 98752500*a41*t1 ^ 2*u2*v2 ^ 3 + 22120560*a41*t1 ^ 2*v2 ^ 3*w2 - 13430340*a41*t1*v2 ^ 5 - 1622016*b3*u2 ^ 2*v2 - 2889216*b4*t1 ^ 3*u2 ^ 2 - 8667648*b4*t1 ^ 2*u2*v2 ^ 2 - 1444608*b4*t1*v2 ^ 4 + 3950100*b51*t1 ^ 4*u2 ^ 2 + 15800400*b51*t1 ^ 3*u2*v2 ^ 2 + 3950100*b51*t1 ^ 2*v2 ^ 4 + 18960480*b63*t1 ^ 3*u2 ^ 2*v2 + 18960480*b63*t1 ^ 2*u2*v2 ^ 3 + 1896048*b63*t1*v2 ^ 5 - 1777545*lambda*t1 ^ 2*u2 ^ 4 - 7110180*lambda*t1*u2 ^ 3*v2 ^ 2 - 1777545*lambda*u2 ^ 2*v2 ^ 4 + 25280640*s2*t1 ^ 2*u2 ^ 3*v2 + 25280640*s2*t1*u2 ^ 2*v2 ^ 3 + 2528064*s2*u2*v2 ^ 5 - 5266800*t1 ^ 3*u2 ^ 4 + 7373520*t1 ^ 3*u2 ^ 3*w2 - 49376250*t1 ^ 2*u2 ^ 3*v2 ^ 2 + 33180840*t1 ^ 2*u2 ^ 2*v2 ^ 2*w2 - 33575850*t1*u2 ^ 2*v2 ^ 4 + 11060280*t1*u2*v2 ^ 4*w2 - 2830905*u2*v2 ^ 6 + 368676*v2 ^ 6*w2))
    + h ^ 4 * (268435456*(43253760*a1*a41 ^ 2 - 37748736*a1*a41*b63 - 31457280*a1*b51*u2 - 19464192*a2*a3*lambda*u2 + 69206016*a2*a3*s2*v2 - 108134400*a2*a3*t1*u2 + 60555264*a2*a3*t1*w2 - 102727680*a2*a3*v2 ^ 2 + 46227456*a2*a41*lambda*t1*u2 + 23113728*a2*a41*lambda*v2 ^ 2 - 164364288*a2*a41*s2*t1*v2 + 115568640*a2*a41*t1 ^ 2*u2 - 71909376*a2*a41*t1 ^ 2*w2 + 231137280*a2*a41*t1*v2 ^ 2 + 34603008*a2*b4*t1*v2 - 51363840*a2*b51*t1 ^ 2*v2 - 61636608*a2*b63*t1 ^ 2*u2 - 61636608*a2*b63*t1*v2 ^ 2 + 23113728*a2*lambda*u2 ^ 2*v2 - 82182144*a2*s2*t1*u2 ^ 2 - 82182144*a2*s2*u2*v2 ^ 2 + 231137280*a2*t1*u2 ^ 2*v2 - 143818752*a2*t1*u2*v2*w2 + 115568640*a2*u2*v2 ^ 3 - 23969792*a2*v2 ^ 3*w2 - 39004416*a3 ^ 2*lambda*t1 ^ 2*v2 + 46227456*a3 ^ 2*s2*t1 ^ 3 - 57784320*a3 ^ 2*t1 ^ 3*v2 + 113762880*a3*a41*lambda*t1 ^ 3*v2 - 101122560*a3*a41*s2*t1 ^ 4 + 110602800*a3*a41*t1 ^ 4*v2 + 25952256*a3*b3*t1*v2 + 11556864*a3*b4*t1 ^ 4 - 12640320*a3*b51*t1 ^ 5 - 75841920*a3*b63*t1 ^ 4*v2 + 56881440*a3*lambda*t1 ^ 3*u2 ^ 2 + 170644320*a3*lambda*t1 ^ 2*u2*v2 ^ 2 + 28440720*a3*lambda*t1*v2 ^ 4 - 404490240*a3*s2*t1 ^ 3*u2*v2 - 202245120*a3*s2*t1 ^ 2*v2 ^ 3 + 55301400*a3*t1 ^ 4*u2 ^ 2 - 88482240*a3*t1 ^ 4*u2*w2 + 505612800*a3*t1 ^ 3*u2*v2 ^ 2 - 176964480*a3*t1 ^ 3*v2 ^ 2*w2 + 197505000*a3*t1 ^ 2*v2 ^ 4 - 76434435*a41 ^ 2*lambda*t1 ^ 4*v2 + 54353376*a41 ^ 2*s2*t1 ^ 5 - 50956290*a41 ^ 2*t1 ^ 5*v2 - 12582912*a41*b2*u2 - 30818304*a41*b3*t1 ^ 2*v2 - 10112256*a41*b4*t1 ^ 5 + 11323620*a41*b51*t1 ^ 6 + 81530064*a41*b63*t1 ^ 5*v2 - 76434435*a41*lambda*t1 ^ 4*u2 ^ 2 - 305737740*a41*lambda*t1 ^ 3*u2*v2 ^ 2 - 76434435*a41*lambda*t1 ^ 2*v2 ^ 4 + 543533760*a41*s2*t1 ^ 4*u2*v2 + 362355840*a41*s2*t1 ^ 3*v2 ^ 3 - 50956290*a41*t1 ^ 5*u2 ^ 2 + 95118408*a41*t1 ^ 5*u2*w2 - 636953625*a41*t1 ^ 4*u2*v2 ^ 2 + 237796020*a41*t1 ^ 4*v2 ^ 2*w2 - 339708600*a41*t1 ^ 3*v2 ^ 4 - 15409152*b3*t1 ^ 2*u2 ^ 2 - 30818304*b3*t1*u2*v2 ^ 2 - 2568192*b3*v2 ^ 4 - 50561280*b4*t1 ^ 4*u2*v2 - 33707520*b4*t1 ^ 3*v2 ^ 3 + 67941720*b51*t1 ^ 5*u2*v2 + 56618100*b51*t1 ^ 4*v2 ^ 3 + 40765032*b63*t1 ^ 5*u2 ^ 2 + 203825160*b63*t1 ^ 4*u2*v2 ^ 2 + 67941720*b63*t1 ^ 3*v2 ^ 4 - 101912580*lambda*t1 ^ 3*u2 ^ 3*v2 - 152868870*lambda*t1 ^ 2*u2 ^ 2*v2 ^ 3 - 30573774*lambda*t1*u2*v2 ^ 5 - 727947*lambda*v2 ^ 7 + 90588960*s2*t1 ^ 4*u2 ^ 3 + 543533760*s2*t1 ^ 3*u2 ^ 2*v2 ^ 2 + 271766880*s2*t1 ^ 2*u2*v2 ^ 4 + 18117792*s2*t1*v2 ^ 6 - 212317875*t1 ^ 4*u2 ^ 3*v2 + 237796020*t1 ^ 4*u2 ^ 2*v2*w2 - 679417200*t1 ^ 3*u2 ^ 2*v2 ^ 3 + 317061360*t1 ^ 3*u2*v2 ^ 3*w2 - 280259595*t1 ^ 2*u2*v2 ^ 5 + 47559204*t1 ^ 2*v2 ^ 5*w2 - 16985430*t1*v2 ^ 7))
    + h ^ 5 * (-8388608*(-2768240640*a1*a3*u2 + 1409286144*a1*a3*w2 + 622854144*a1*a41*lambda*u2 - 2214592512*a1*a41*s2*v2 + 3460300800*a1*a41*t1*u2 - 1937768448*a1*a41*t1*w2 + 3287285760*a1*a41*v2 ^ 2 + 805306368*a1*b4*v2 - 1384120320*a1*b51*t1*v2 - 1660944384*a1*b63*t1*u2 - 830472192*a1*b63*v2 ^ 2 - 1107296256*a1*s2*u2 ^ 2 + 3287285760*a1*u2 ^ 2*v2 - 1937768448*a1*u2*v2*w2 - 1384120320*a2 ^ 2*u2 + 704643072*a2 ^ 2*w2 - 1479278592*a2*a3*lambda*t1*v2 + 2629828608*a2*a3*s2*t1 ^ 2 - 3698196480*a2*a3*t1 ^ 2*v2 + 2496282624*a2*a41*lambda*t1 ^ 2*v2 - 2958557184*a2*a41*s2*t1 ^ 3 + 3698196480*a2*a41*t1 ^ 3*v2 + 603979776*a2*b3*v2 + 438304768*a2*b4*t1 ^ 3 - 462274560*a2*b51*t1 ^ 4 - 2218917888*a2*b63*t1 ^ 3*v2 + 1248141312*a2*lambda*t1 ^ 2*u2 ^ 2 + 2496282624*a2*lambda*t1*u2*v2 ^ 2 + 208023552*a2*lambda*v2 ^ 4 - 8875671552*a2*s2*t1 ^ 2*u2*v2 - 2958557184*a2*s2*t1*v2 ^ 3 + 1849098240*a2*t1 ^ 3*u2 ^ 2 - 2588737536*a2*t1 ^ 3*u2*w2 + 11788001280*a2*t1 ^ 2*u2*v2 ^ 2 - 3883106304*a2*t1 ^ 2*v2 ^ 2*w2 + 3004784640*a2*t1*v2 ^ 4 - 455051520*a3 ^ 2*lambda*t1 ^ 4 + 101122560*a3 ^ 2*t1 ^ 5 + 978360768*a3*a41*lambda*t1 ^ 5 - 271766880*a3*a41*t1 ^ 6 + 402653184*a3*b2*v2 + 328728576*a3*b3*t1 ^ 3 - 434827008*a3*b63*t1 ^ 6 + 4891803840*a3*lambda*t1 ^ 4*u2*v2 + 3261202560*a3*lambda*t1 ^ 3*v2 ^ 3 - 3478616064*a3*s2*t1 ^ 5*u2 - 8696540160*a3*s2*t1 ^ 4*v2 ^ 2 + 3261202560*a3*t1 ^ 5*u2*v2 - 3043789056*a3*t1 ^ 5*v2*w2 + 6794172000*a3*t1 ^ 4*v2 ^ 3 - 519754158*a41 ^ 2*lambda*t1 ^ 6 + 165001320*a41 ^ 2*t1 ^ 7 - 553648128*a41*b2*t1*v2 - 277364736*a41*b3*t1 ^ 4 + 396003168*a41*b63*t1 ^ 7 - 6237049896*a41*lambda*t1 ^ 5*u2*v2 - 5197541580*a41*lambda*t1 ^ 4*v2 ^ 3 + 3696029568*a41*s2*t1 ^ 6*u2 + 11088088704*a41*s2*t1 ^ 5*v2 ^ 2 - 2887523100*a41*t1 ^ 6*u2*v2 + 3234025872*a41*t1 ^ 6*v2*w2 - 8085064680*a41*t1 ^ 5*v2 ^ 3 - 276824064*b2*t1*u2 ^ 2 - 276824064*b2*u2*v2 ^ 2 - 1109458944*b3*t1 ^ 3*u2*v2 - 554729472*b3*t1 ^ 2*v2 ^ 3 - 289884672*b4*t1 ^ 6*u2 - 869654016*b4*t1 ^ 5*v2 ^ 2 + 330002640*b51*t1 ^ 7*u2 + 1155009240*b51*t1 ^ 6*v2 ^ 2 + 2772022176*b63*t1 ^ 6*u2*v2 + 2772022176*b63*t1 ^ 5*v2 ^ 3 - 1039508316*lambda*t1 ^ 5*u2 ^ 3 - 7796312370*lambda*t1 ^ 4*u2 ^ 2*v2 ^ 2 - 5197541580*lambda*t1 ^ 3*u2*v2 ^ 4 - 519754158*lambda*t1 ^ 2*v2 ^ 6 + 11088088704*s2*t1 ^ 5*u2 ^ 2*v2 + 18480147840*s2*t1 ^ 4*u2*v2 ^ 3 + 3696029568*s2*t1 ^ 3*v2 ^ 5 - 481253850*t1 ^ 6*u2 ^ 3 + 1617012936*t1 ^ 6*u2 ^ 2*w2 - 12127597020*t1 ^ 5*u2 ^ 2*v2 ^ 2 + 9702077616*t1 ^ 5*u2*v2 ^ 2*w2 - 16603257825*t1 ^ 4*u2*v2 ^ 4 + 4042532340*t1 ^ 4*v2 ^ 4*w2 - 3080024640*t1 ^ 3*v2 ^ 6))
    + h ^ 6 * (524288*(44291850240*a0*a41*u2 - 22548578304*a0*a41*w2 - 16106127360*a0*b51*v2 - 19327352832*a0*b63*u2 - 9965666304*a1*a3*lambda*v2 + 35433480192*a1*a3*s2*t1 - 55364812800*a1*a3*t1*v2 + 23668457472*a1*a41*lambda*t1*v2 - 42077257728*a1*a41*s2*t1 ^ 2 + 59171143680*a1*a41*t1 ^ 2*v2 + 8858370048*a1*b4*t1 ^ 2 - 8766095360*a1*b51*t1 ^ 3 - 31557943296*a1*b63*t1 ^ 2*v2 + 11834228736*a1*lambda*t1*u2 ^ 2 + 11834228736*a1*lambda*u2*v2 ^ 2 - 84154515456*a1*s2*t1*u2*v2 - 14025752576*a1*s2*v2 ^ 3 + 29585571840*a1*t1 ^ 2*u2 ^ 2 - 36817600512*a1*t1 ^ 2*u2*w2 + 118342287360*a1*t1*u2*v2 ^ 2 - 36817600512*a1*t1*v2 ^ 2*w2 + 14792785920*a1*v2 ^ 4 - 4982833152*a2 ^ 2*lambda*v2 + 17716740096*a2 ^ 2*s2*t1 - 27682406400*a2 ^ 2*t1*v2 - 13313507328*a2*a3*lambda*t1 ^ 3 + 1849098240*a2*a3*t1 ^ 4 + 14561648640*a2*a41*lambda*t1 ^ 4 - 3235921920*a2*a41*t1 ^ 5 + 6643777536*a2*b3*t1 ^ 2 - 7766212608*a2*b63*t1 ^ 5 + 58246594560*a2*lambda*t1 ^ 3*u2*v2 + 29123297280*a2*lambda*t1 ^ 2*v2 ^ 3 - 51774750720*a2*s2*t1 ^ 4*u2 - 103549501440*a2*s2*t1 ^ 3*v2 ^ 2 + 56628633600*a2*t1 ^ 4*u2*v2 - 45302906880*a2*t1 ^ 4*v2*w2 + 86291251200*a2*t1 ^ 3*v2 ^ 3 + 4429185024*a3*b2*t1 ^ 2 + 16632133056*a3*lambda*t1 ^ 6*u2 + 49896399168*a3*lambda*t1 ^ 5*v2 ^ 2 - 59136473088*a3*s2*t1 ^ 6*v2 - 5280042240*a3*t1 ^ 7*u2 - 7392059136*a3*t1 ^ 7*w2 + 23100184800*a3*t1 ^ 6*v2 ^ 2 - 3221225472*a41*b1*v2 - 3506438144*a41*b2*t1 ^ 3 - 17523140184*a41*lambda*t1 ^ 7*u2 - 61330990644*a41*lambda*t1 ^ 6*v2 ^ 2 + 62304498432*a41*s2*t1 ^ 7*v2 + 6084423675*a41*t1 ^ 8*u2 + 6814554516*a41*t1 ^ 8*w2 - 19470155760*a41*t1 ^ 7*v2 ^ 2 - 1610612736*b1*u2 ^ 2 - 10519314432*b2*t1 ^ 2*u2*v2 - 3506438144*b2*t1*v2 ^ 3 - 3883106304*b3*t1 ^ 5*u2 - 9707765760*b3*t1 ^ 4*v2 ^ 2 - 4224033792*b4*t1 ^ 7*v2 + 4867538940*b51*t1 ^ 8*v2 + 5841046728*b63*t1 ^ 8*u2 + 23364186912*b63*t1 ^ 7*v2 ^ 2 - 61330990644*lambda*t1 ^ 6*u2 ^ 2*v2 - 122661981288*lambda*t1 ^ 5*u2*v2 ^ 3 - 30665495322*lambda*t1 ^ 4*v2 ^ 5 + 31152249216*s2*t1 ^ 7*u2 ^ 2 + 218065744512*s2*t1 ^ 6*u2*v2 ^ 2 + 109032872256*s2*t1 ^ 5*v2 ^ 4 - 19470155760*t1 ^ 7*u2 ^ 2*v2 + 54516436128*t1 ^ 7*u2*v2*w2 - 147648681180*t1 ^ 6*u2*v2 ^ 3 + 63602508816*t1 ^ 6*v2 ^ 3*w2 - 74960099676*t1 ^ 5*v2 ^ 5))
    + h ^ 7 * (-32768*(412316860416*a0*a3*s2 - 708669603840*a0*a3*v2 + 159450660864*a0*a41*lambda*v2 - 566935683072*a0*a41*s2*t1 + 885837004800*a0*a41*t1*v2 + 206158430208*a0*b4*t1 - 177167400960*a0*b51*t1 ^ 2 - 425201762304*a0*b63*t1*v2 + 79725330432*a0*lambda*u2 ^ 2 - 566935683072*a0*s2*u2*v2 + 442918502400*a0*t1*u2 ^ 2 - 496068722688*a0*t1*u2*w2 + 841545154560*a0*u2*v2 ^ 2 - 248034361344*a0*v2 ^ 2*w2 + 412316860416*a1*a2*s2 - 708669603840*a1*a2*v2 - 189347659776*a1*a3*lambda*t1 ^ 2 + 213016117248*a1*a41*lambda*t1 ^ 3 - 29585571840*a1*a41*t1 ^ 4 + 154618822656*a1*b3*t1 - 142010744832*a1*b63*t1 ^ 4 + 639048351744*a1*lambda*t1 ^ 2*u2*v2 + 213016117248*a1*lambda*t1*v2 ^ 3 - 757390639104*a1*s2*t1 ^ 3*u2 - 1136085958656*a1*s2*t1 ^ 2*v2 ^ 2 + 946738298880*a1*t1 ^ 3*u2*v2 - 662716809216*a1*t1 ^ 3*v2*w2 + 1005909442560*a1*t1 ^ 2*v2 ^ 3 - 94673829888*a2 ^ 2*lambda*t1 ^ 2 + 103079215104*a2*b2*t1 + 250460356608*a2*lambda*t1 ^ 5*u2 + 626150891520*a2*lambda*t1 ^ 4*v2 ^ 2 - 890525712384*a2*s2*t1 ^ 5*v2 - 69572321280*a2*t1 ^ 6*u2 - 129868333056*a2*t1 ^ 6*w2 + 417433927680*a2*t1 ^ 5*v2 ^ 2 + 51539607552*a3*b1*t1 + 280370242944*a3*lambda*t1 ^ 7*v2 - 124608996864*a3*s2*t1 ^ 8 - 97350778800*a3*t1 ^ 8*v2 - 35433480192*a41*b1*t1 ^ 2 - 293512598082*a41*lambda*t1 ^ 8*v2 + 115955594304*a41*s2*t1 ^ 9 + 108708369660*a41*t1 ^ 9*v2 - 70866960384*b1*t1*u2*v2 - 11811160064*b1*v2 ^ 3 - 47336914944*b2*t1 ^ 4*u2 - 94673829888*b2*t1 ^ 3*v2 ^ 2 - 55657857024*b3*t1 ^ 6*v2 - 6922722048*b4*t1 ^ 9 + 7247224644*b51*t1 ^ 10 + 86966695728*b63*t1 ^ 9*v2 - 146756299041*lambda*t1 ^ 8*u2 ^ 2 - 1174050392328*lambda*t1 ^ 7*u2*v2 ^ 2 - 684862728858*lambda*t1 ^ 6*v2 ^ 4 + 1043600348736*s2*t1 ^ 8*u2*v2 + 1391467131648*s2*t1 ^ 7*v2 ^ 3 + 54354184830*t1 ^ 9*u2 ^ 2 + 101461145016*t1 ^ 9*u2*w2 - 244593831735*t1 ^ 8*u2*v2 ^ 2 + 456575152572*t1 ^ 8*v2 ^ 2*w2 - 652250217960*t1 ^ 7*v2 ^ 4))
    + h ^ 8 * (4096*(-1275605286912*a0*a3*lambda*t1 - 354334801920*a0*a3*t1 ^ 2 + 1514781278208*a0*a41*lambda*t1 ^ 2 + 3298534883328*a0*b3 - 1346472247296*a0*b63*t1 ^ 3 + 3029562556416*a0*lambda*t1*u2*v2 + 504927092736*a0*lambda*v2 ^ 3 - 5385888989184*a0*s2*t1 ^ 2*u2 - 5385888989184*a0*s2*t1*v2 ^ 2 + 7573906391040*a0*t1 ^ 2*u2*v2 - 4712652865536*a0*t1 ^ 2*v2*w2 + 5049270927360*a0*t1*v2 ^ 3 - 1275605286912*a1*a2*lambda*t1 - 354334801920*a1*a2*t1 ^ 2 + 2199023255552*a1*b2 + 1863891025920*a1*lambda*t1 ^ 4*u2 + 3727782051840*a1*lambda*t1 ^ 3*v2 ^ 2 - 6627168092160*a1*s2*t1 ^ 4*v2 - 414198005760*a1*t1 ^ 5*u2 - 1159754416128*a1*t1 ^ 5*w2 + 3624232550400*a1*t1 ^ 4*v2 ^ 2 + 1099511627776*a2*b1 + 2128913031168*a2*lambda*t1 ^ 6*v2 - 1081352650752*a2*s2*t1 ^ 7 - 675845406720*a2*t1 ^ 7*v2 + 260900087184*a3*lambda*t1 ^ 9 - 217416739320*a3*t1 ^ 10 - 244593831735*a41*lambda*t1 ^ 10 + 197651581200*a41*t1 ^ 11 - 224412041216*b1*t1 ^ 3*u2 - 336618061824*b1*t1 ^ 2*v2 ^ 2 - 331358404608*b2*t1 ^ 5*v2 - 50688405504*b3*t1 ^ 8 + 59295474360*b63*t1 ^ 11 - 2445938317350*lambda*t1 ^ 9*u2*v2 - 3668907476025*lambda*t1 ^ 8*v2 ^ 3 + 869666957280*s2*t1 ^ 10*u2 + 4348334786400*s2*t1 ^ 9*v2 ^ 2 + 951198234525*t1 ^ 10*u2*v2 + 760958587620*t1 ^ 10*v2*w2 - 452951540250*t1 ^ 9*v2 ^ 3))
    + h ^ 9 * (-384*(-9895604649984*a0*a2*lambda - 10995116277760*a0*a2*t1 + 18177375338496*a0*lambda*t1 ^ 3*u2 + 27266063007744*a0*lambda*t1 ^ 2*v2 ^ 2 - 64630667870208*a0*s2*t1 ^ 3*v2 - 2524635463680*a0*t1 ^ 4*u2 - 14137958596608*a0*t1 ^ 4*w2 + 40394167418880*a0*t1 ^ 3*v2 ^ 2 - 4947802324992*a1 ^ 2*lambda - 5497558138880*a1 ^ 2*t1 + 21372617097216*a1*lambda*t1 ^ 5*v2 - 12665254576128*a1*s2*t1 ^ 6 - 5936838082560*a1*t1 ^ 6*v2 + 2990615924736*a2*lambda*t1 ^ 8 - 2584482897920*a2*t1 ^ 9 - 2019708370944*b1*t1 ^ 4*v2 - 452330520576*b2*t1 ^ 7 - 2460762185940*lambda*t1 ^ 11*u2 - 13534192022670*lambda*t1 ^ 10*v2 ^ 2 + 8749376661120*s2*t1 ^ 11*v2 + 1936710979675*t1 ^ 12*u2 + 637975381540*t1 ^ 12*w2 + 5468360413200*t1 ^ 11*v2 ^ 2))
    + h ^ 10 * (48*(-351843720888320*a0*a1 + 159052034211840*a0*lambda*t1 ^ 4*v2 - 113103668772864*a0*s2*t1 ^ 5 - 35344896491520*a0*t1 ^ 5*v2 + 25952463618048*a1*lambda*t1 ^ 7 - 23429307432960*a1*t1 ^ 8 - 2356326432768*b1*t1 ^ 6 - 18660779910045*lambda*t1 ^ 12*v2 + 5103803052320*s2*t1 ^ 13 + 14354446084650*t1 ^ 13*v2))
    + h ^ 11 * (-80883*t1 ^ 6*(16911433728*a0*lambda - 16106127360*a0*t1 - 752987205*lambda*t1 ^ 8 + 780875620*t1 ^ 9))

end OmicronCollapsedQuotient810

section OmicronCollapsedFactor810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 1000000000 in
/-- Exact `h^94` factorization of the literal weight-`105` omicron
numerator on the depth-two right jet of the xi bridge. -/
theorem localClearedFifteenthDefect810_collapsed_factored
    (h t1 v2 u2 a41 a3 a2 a1 a0 s2 w2 b63 b51 b4 b3 b2 b1 : k[X])
    (lambda : k) :
    localClearedFifteenthDefect810 h (h ^ 7 * t1) (h ^ 5 * v2)
        (h ^ 3 * u2) (h * a41) a3 a2 a1 a0 (h ^ 7 * s2)
        (h ^ 5 * w2) (h ^ 3 * b63) (h * b51) b4 b3 b2 b1 lambda =
      h ^ 94 *
        bridgeOmicronCollapsedQuotient810 h t1 v2 u2 a41 a3 a2 a1 a0
          s2 w2 b63 b51 b4 b3 b2 b1 (Polynomial.C lambda) := by
  simp only [localClearedFifteenthDefect810,
    localClearedFifteenthDefectCore810,
    localClearedFifteenthDefectBlock0_810,
    localClearedFifteenthDefectBlock1_810,
    localClearedFifteenthDefectBlock2_810,
    localClearedFifteenthDefectBlock3_810,
    localClearedFifteenthDefectBlock4_810,
    localClearedFifteenthDefectBlock5_810,
    localClearedFifteenthDefectBlock6_810,
    localClearedFifteenthDefectBlock7_810,
    localClearedFifteenthDefectBlock8_810,
    localClearedFifteenthDefectBlock9_810,
    localClearedFifteenthDefectBlock10_810,
    localClearedFifteenthDefectBlock11_810,
    localClearedFifteenthDefectBlock12_810,
    localClearedFifteenthDefectBlock13_810,
    localClearedFifteenthDefectBlock14_810,
    bridgeOmicronCollapsedQuotient810]
  ring

set_option maxHeartbeats 800000000 in
/-- At a root of `h`, evaluation of the quotient is exactly its
five-term omicron head. -/
theorem bridgeOmicronCollapsedQuotient810_eval_root
    (h t1 v2 u2 a41 a3 a2 a1 a0 s2 w2 b63 b51 b4 b3 b2 b1 : k[X])
    (lambda x : k) (hroot : h.eval x = 0) :
    (bridgeOmicronCollapsedQuotient810 h t1 v2 u2 a41 a3 a2 a1 a0
        s2 w2 b63 b51 b4 b3 b2 b1 (Polynomial.C lambda)).eval x =
      (96757023244288 : k) * a41.eval x *
        (-(95 : k) * (a41.eval x) ^ 2 * u2.eval x +
          (28 : k) * (a41.eval x) ^ 2 * w2.eval x +
          (60 : k) * a41.eval x * b51.eval x * v2.eval x +
          (72 : k) * a41.eval x * b63.eval x * u2.eval x +
          (60 : k) * b51.eval x * (u2.eval x) ^ 2) := by
  simp only [bridgeOmicronCollapsedQuotient810, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_ofNat, hroot]
  ring

set_option maxHeartbeats 1000000000 in
/-- Cancelling the exact `h^94` source power and evaluating at the
same root forces the five-term omicron head. -/
theorem bridgeOmicronCollapsed_head_of_power810
    (h t1 v2 u2 a41 a3 a2 a1 a0 s2 w2 b63 b51 b4 b3 b2 b1 : k[X])
    (lambda omicronGround x : k) (hh : h ≠ 0) (hroot : h.eval x = 0)
    (hpow :
      localClearedFifteenthDefect810 h (h ^ 7 * t1) (h ^ 5 * v2)
          (h ^ 3 * u2) (h * a41) a3 a2 a1 a0 (h ^ 7 * s2)
          (h ^ 5 * w2) (h ^ 3 * b63) (h * b51) b4 b3 b2 b1 lambda =
        Polynomial.C omicronGround * h ^ 105) :
    a41.eval x *
        (-(95 : k) * (a41.eval x) ^ 2 * u2.eval x +
          (28 : k) * (a41.eval x) ^ 2 * w2.eval x +
          (60 : k) * a41.eval x * b51.eval x * v2.eval x +
          (72 : k) * a41.eval x * b63.eval x * u2.eval x +
          (60 : k) * b51.eval x * (u2.eval x) ^ 2) = 0 := by
  have h94 : (h : k[X]) ^ 94 ≠ 0 := pow_ne_zero 94 hh
  have hquot :
      bridgeOmicronCollapsedQuotient810 h t1 v2 u2 a41 a3 a2 a1 a0
          s2 w2 b63 b51 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C omicronGround * h ^ 11 := by
    apply mul_left_cancel₀ h94
    rw [← localClearedFifteenthDefect810_collapsed_factored h t1 v2 u2
      a41 a3 a2 a1 a0 s2 w2 b63 b51 b4 b3 b2 b1 lambda]
    rw [hpow]
    ring
  have hev := congrArg (Polynomial.eval x) hquot
  rw [bridgeOmicronCollapsedQuotient810_eval_root h t1 v2 u2 a41 a3 a2
    a1 a0 s2 w2 b63 b51 b4 b3 b2 b1 lambda x hroot] at hev
  have h11 : (0 : k) ^ 11 = 0 := by norm_num
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    hroot, h11, mul_zero] at hev
  exact (mul_eq_zero.mp hev).resolve_left (by norm_num)

variable {F : Type*} [Field F] [CharZero F]

/-- On the q5-deep child the five-term head loses both b51 terms. -/
theorem bridgeOmicronCollapsed_q5Deep810
    (a41 u2 w2 b63 b51 v2 : F)
    (hhead :
      a41 *
          (-(95 : F) * a41 ^ 2 * u2 + (28 : F) * a41 ^ 2 * w2 +
            (60 : F) * a41 * b51 * v2 +
            (72 : F) * a41 * b63 * u2 + (60 : F) * b51 * u2 ^ 2) = 0)
    (hb51 : b51 = 0) :
    a41 *
        (-(95 : F) * a41 ^ 2 * u2 + (28 : F) * a41 ^ 2 * w2 +
          (72 : F) * a41 * b63 * u2) = 0 := by
  simpa only [hb51, mul_zero, zero_mul, add_zero] using hhead

/-- If p4 is not yet one core power deeper, the q5-deep omicron head
becomes the exact three-term transport on `u2,w2,b63`. -/
theorem bridgeOmicronCollapsed_q5Deep_transport810
    (a41 u2 w2 b63 b51 v2 : F)
    (hhead :
      a41 *
          (-(95 : F) * a41 ^ 2 * u2 + (28 : F) * a41 ^ 2 * w2 +
            (60 : F) * a41 * b51 * v2 +
            (72 : F) * a41 * b63 * u2 + (60 : F) * b51 * u2 ^ 2) = 0)
    (hb51 : b51 = 0) (ha41 : a41 ≠ 0) :
    (95 : F) * a41 * u2 =
      (28 : F) * a41 * w2 + (72 : F) * b63 * u2 := by
  have hreduced :=
    bridgeOmicronCollapsed_q5Deep810 a41 u2 w2 b63 b51 v2 hhead hb51
  have ha41sq : a41 ^ 2 ≠ 0 := pow_ne_zero 2 ha41
  apply mul_left_cancel₀ ha41sq
  linear_combination (-1 : F) * hreduced

end OmicronCollapsedFactor810

#print axioms localClearedFifteenthDefect810_collapsed_factored
#print axioms bridgeOmicronCollapsedQuotient810_eval_root
#print axioms bridgeOmicronCollapsed_head_of_power810
#print axioms bridgeOmicronCollapsed_q5Deep810
#print axioms bridgeOmicronCollapsed_q5Deep_transport810

end Max11DegreeRoutes
