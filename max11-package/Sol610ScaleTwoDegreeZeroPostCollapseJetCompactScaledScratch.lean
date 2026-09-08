import Sol610ScaleTwoDegreeZeroCompactSourceScratch

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 100000000

section DegreeZeroPostCollapseJet610

variable {R : Type*} [CommRing R]

set_option maxHeartbeats 400000000 in
/-- Atom-level weight-`69` clearing of the compact source: substituting the
scaled post-collapse atoms into `degreeZeroClearedCompact610` factors through
`h ^ 69` with 103 monomials, before any post-collapse jet numerator is
expanded. -/
private theorem memory610_compactPostCollapseScaled
    (h nA nB nC nD nE nP nQ nR nS nT nU nV nW nl : R) :
    degreeZeroClearedCompact610
        (h ^ 10 * nA)
        (h ^ 14 * nB)
        (h ^ 19 * nC)
        (h ^ 24 * nD)
        (h ^ 29 * nE)
        (h ^ 10 * nP)
        (h ^ 14 * nQ)
        (h ^ 19 * nR)
        (h ^ 23 * nS)
        (h ^ 27 * nT)
        (h ^ 32 * nU)
        (h ^ 37 * nV)
        (h ^ 42 * nW)
        (h ^ 5 * nl) =
      h ^ 69 *
      (- (27909765 : R) * h ^ 6 * nA ^ 7 * nl
      + (144717300 : R) * h ^ 5 * nA ^ 6 * nB
      - (117641160 : R) * h ^ 5 * nA ^ 6 * nQ
      - (403341120 : R) * h ^ 5 * nA ^ 5 * nB * nP
      + (226879380 : R) * h ^ 5 * nA ^ 5 * nC * nl
      - (336117600 : R) * h ^ 5 * nA ^ 5 * nD
      + (968018688 : R) * h ^ 5 * nA ^ 4 * nD * nP
      - (10083528 : R) * h ^ 5 * nA ^ 4 * nE * nl
      + (60501168 : R) * h ^ 4 * nA ^ 5 * nS
      + (336117600 : R) * h ^ 4 * nA ^ 4 * nB ^ 2 * nl
      - (840294000 : R) * h ^ 4 * nA ^ 4 * nB * nC
      + (40334112 : R) * h ^ 4 * nA ^ 4 * nB * nR
      + (847016352 : R) * h ^ 4 * nA ^ 4 * nC * nQ
      + (1936037376 : R) * h ^ 4 * nA ^ 3 * nB * nC * nP
      - (1290691584 : R) * h ^ 4 * nA ^ 3 * nB * nD * nl
      + (29877120 : R) * h ^ 4 * nA ^ 3 * nB * nE
      - (544510512 : R) * h ^ 4 * nA ^ 3 * nC ^ 2 * nl
      + (1613364480 : R) * h ^ 4 * nA ^ 3 * nC * nD
      - (101896704 : R) * h ^ 4 * nA ^ 3 * nD * nR
      - (39626496 : R) * h ^ 4 * nA ^ 3 * nE * nQ
      - (67931136 : R) * h ^ 4 * nA ^ 2 * nB * nE * nP
      - (3668281344 : R) * h ^ 4 * nA ^ 2 * nC * nD * nP
      + (38211264 : R) * h ^ 4 * nA ^ 2 * nC * nE * nl
      + (1222760448 : R) * h ^ 4 * nA ^ 2 * nD ^ 2 * nl
      - (56609280 : R) * h ^ 4 * nA ^ 2 * nD * nE
      + (125411328 : R) * h ^ 4 * nA * nD * nE * nP
      - (653184 : R) * h ^ 4 * nA * nE ^ 2 * nl
      - (12737088 : R) * h ^ 3 * nA ^ 4 * nU
      - (331968000 : R) * h ^ 3 * nA ^ 3 * nB ^ 3
      + (1003871232 : R) * h ^ 3 * nA ^ 3 * nB ^ 2 * nQ
      - (382112640 : R) * h ^ 3 * nA ^ 3 * nC * nS
      + (217728 : R) * h ^ 3 * nA ^ 3 * nW
      + (573640704 : R) * h ^ 3 * nA ^ 2 * nB ^ 3 * nP
      - (968018688 : R) * h ^ 3 * nA ^ 2 * nB ^ 2 * nC * nl
      + (1434101760 : R) * h ^ 3 * nA ^ 2 * nB ^ 2 * nD
      + (1210023360 : R) * h ^ 3 * nA ^ 2 * nB * nC ^ 2
      - (152845056 : R) * h ^ 3 * nA ^ 2 * nB * nC * nR
      - (3804143616 : R) * h ^ 3 * nA ^ 2 * nB * nD * nQ
      - (1604873088 : R) * h ^ 3 * nA ^ 2 * nC ^ 2 * nQ
      + (19595520 : R) * h ^ 3 * nA ^ 2 * nE * nS
      - (2173796352 : R) * h ^ 3 * nA * nB ^ 2 * nD * nP
      + (22643712 : R) * h ^ 3 * nA * nB ^ 2 * nE * nl
      - (1834140672 : R) * h ^ 3 * nA * nB * nC ^ 2 * nP
      + (2445520896 : R) * h ^ 3 * nA * nB * nC * nD * nl
      - (56609280 : R) * h ^ 3 * nA * nB * nC * nE
      - (1811496960 : R) * h ^ 3 * nA * nB * nD ^ 2
      + (5225472 : R) * h ^ 3 * nA * nB * nE * nR
      + (343901376 : R) * h ^ 3 * nA * nC ^ 3 * nl
      - (1528450560 : R) * h ^ 3 * nA * nC ^ 2 * nD
      + (282175488 : R) * h ^ 3 * nA * nC * nD * nR
      + (109734912 : R) * h ^ 3 * nA * nC * nE * nQ
      + (3511517184 : R) * h ^ 3 * nA * nD ^ 2 * nQ
      + (62705664 : R) * h ^ 3 * nB * nC * nE * nP
      + (2006581248 : R) * h ^ 3 * nB * nD ^ 2 * nP
      - (41803776 : R) * h ^ 3 * nB * nD * nE * nl
      + (483840 : R) * h ^ 3 * nB * nE ^ 2
      + (1693052928 : R) * h ^ 3 * nC ^ 2 * nD * nP
      - (17635968 : R) * h ^ 3 * nC ^ 2 * nE * nl
      - (1128701952 : R) * h ^ 3 * nC * nD ^ 2 * nl
      + (52254720 : R) * h ^ 3 * nC * nD * nE
      + (557383680 : R) * h ^ 3 * nD ^ 3
      - (8957952 : R) * h ^ 3 * nD * nE * nR
      - (1741824 : R) * h ^ 3 * nE ^ 2 * nQ
      - (22643712 : R) * h ^ 2 * nA ^ 3 * nB * nT
      - (339655680 : R) * h ^ 2 * nA ^ 2 * nB ^ 2 * nS
      + (7838208 : R) * h ^ 2 * nA ^ 2 * nB * nV
      + (70543872 : R) * h ^ 2 * nA ^ 2 * nC * nU
      + (62705664 : R) * h ^ 2 * nA ^ 2 * nD * nT
      - (95606784 : R) * h ^ 2 * nA * nB ^ 4 * nl
      + (478033920 : R) * h ^ 2 * nA * nB ^ 3 * nC
      - (30191616 : R) * h ^ 2 * nA * nB ^ 3 * nR
      - (1902071808 : R) * h ^ 2 * nA * nB ^ 2 * nC * nQ
      + (1254113280 : R) * h ^ 2 * nA * nB * nD * nS
      + (529079040 : R) * h ^ 2 * nA * nC ^ 2 * nS
      - (1119744 : R) * h ^ 2 * nA * nC * nW
      - (26873856 : R) * h ^ 2 * nA * nD * nV
      - (4478976 : R) * h ^ 2 * nA * nE * nU
      - (362299392 : R) * h ^ 2 * nB ^ 3 * nC * nP
      + (241532928 : R) * h ^ 2 * nB ^ 3 * nD * nl
      - (5591040 : R) * h ^ 2 * nB ^ 3 * nE
      + (305690112 : R) * h ^ 2 * nB ^ 2 * nC ^ 2 * nl
      - (905748480 : R) * h ^ 2 * nB ^ 2 * nC * nD
      + (83607552 : R) * h ^ 2 * nB ^ 2 * nD * nR
      + (32514048 : R) * h ^ 2 * nB ^ 2 * nE * nQ
      - (254741760 : R) * h ^ 2 * nB * nC ^ 3
      + (70543872 : R) * h ^ 2 * nB * nC ^ 2 * nR
      + (3511517184 : R) * h ^ 2 * nB * nC * nD * nQ
      + (493807104 : R) * h ^ 2 * nC ^ 3 * nQ
      - (33592320 : R) * h ^ 2 * nC * nE * nS
      - (1074954240 : R) * h ^ 2 * nD ^ 2 * nS
      + (248832 : R) * h ^ 2 * nE * nW
      + (41803776 : R) * h * nA * nB ^ 2 * nU
      + (62705664 : R) * h * nA * nB * nC * nT
      + (14163968 : R) * h * nB ^ 5
      - (93929472 : R) * h * nB ^ 4 * nQ
      + (313528320 : R) * h * nB ^ 2 * nC * nS
      - (331776 : R) * h * nB ^ 2 * nW
      - (13436928 : R) * h * nB * nC * nV
      - (143327232 : R) * h * nB * nD * nU
      - (1990656 : R) * h * nB * nE * nT
      - (60466176 : R) * h * nC ^ 2 * nU
      - (107495424 : R) * h * nC * nD * nT
      + (6193152 : R) * nB ^ 3 * nT) := by
  unfold degreeZeroClearedCompact610
  ring

end DegreeZeroPostCollapseJet610

end Max11DegreeRoutes
